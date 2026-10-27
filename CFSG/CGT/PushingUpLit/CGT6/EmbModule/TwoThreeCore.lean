module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.TwoThreeBasic
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.GraphLemma
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.NormMap

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoThree

open CFSG.Quasithin CFSG.SL2MinimalFaithful Matrix

namespace NatData

variable {K : Type*} [Field K] {V : Type} [CommGroup V] {G : Subgroup (MulAut V)}
  (D : NatData K G)

@[expose] def T' : Subgroup (MulAut V) := (D.ρ.comp lowerHom).range

theorem mem_T' {g : MulAut V} : g ∈ D.T' ↔ ∃ s : K, D.lo s = g := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.toAdd, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨Multiplicative.ofAdd s, rfl⟩

theorem closure_up_lo :
    Subgroup.closure (D.ρ '' (Set.range (unipotent (F := K)) ∪ Set.range (lowerUni (K := K)))) =
      G := by
  rw [← MonoidHom.map_closure, closure_unipotent_lowerUni, ← MonoidHom.range_eq_map, D.range_eq]

theorem T'_le_G : D.T' ≤ G := by
  intro g hg
  obtain ⟨s, rfl⟩ := D.mem_T'.mp hg
  exact D.lo_mem s

theorem commOn_T_le_U : commOn D.T (commV G) ≤ commV G :=
  (commOn_le_commV _).trans (commV_mono D.T_le_G)

theorem commOn_T'_le_U : commOn D.T' (commV G) ≤ commV G :=
  (commOn_le_commV _).trans (commV_mono D.T'_le_G)

theorem commOn_T_le_P : commOn D.T (commV G) ≤ D.P := by
  unfold commOn
  rw [Subgroup.closure_le]
  rintro _ ⟨g, hg, u, hu, rfl⟩
  obtain ⟨s, rfl⟩ := D.mem_T.mp hg
  exact D.up_comm_mem_P hu s

theorem commOn_T'_le_P' : commOn D.T' (commV G) ≤ D.P' := by
  unfold commOn
  rw [Subgroup.closure_le]
  rintro _ ⟨g, hg, u, hu, rfl⟩
  obtain ⟨s, rfl⟩ := D.mem_T'.mp hg
  exact D.lo_comm_mem_P' hu s

include D in
theorem perfect_G (h4 : ∃ s : Finset K, s.card = 4) : Group.IsPerfect ↥G := by
  have hSL := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  have hsurj : Function.Surjective (D.ρ.codRestrict G D.ρ_mem) := by
    intro g
    have : (g : MulAut V) ∈ D.ρ.range := by rw [D.range_eq]; exact g.2
    obtain ⟨m, hm⟩ := this
    exact ⟨m, Subtype.ext hm⟩
  exact Group.IsPerfect.ofSurjective hsurj

theorem commV_le_commOn_sup (h4 : ∃ s : Finset K, s.card = 4) :
    commV G ≤ commOn D.T (commV G) ⊔ commOn D.T' (commV G) := by
  have := D.perfect_G h4
  refine commV_le_of_generators (X := D.ρ '' (Set.range (unipotent (F := K)) ∪
    Set.range (lowerUni (K := K)))) (sup_le D.commOn_T_le_U D.commOn_T'_le_U) ?_ ?_
    D.closure_up_lo
  · rintro _ ⟨m, -, rfl⟩
    exact D.ρ_mem m
  · rintro _ ⟨m, hm, rfl⟩ u hu
    rcases hm with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure
        ⟨D.up s, D.mem_T.mpr ⟨s, rfl⟩, u, hu, rfl⟩)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure
        ⟨D.lo s, D.mem_T'.mpr ⟨s, rfl⟩, u, hu, rfl⟩)

theorem weyl_conj_commOn {q : V} (hq : q ∈ commOn D.T' (commV G)) :
    D.ρ weylSL⁻¹ q ∈ commOn D.T (commV G) := by
  unfold commOn at hq ⊢
  induction hq using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨g, hg, u, hu, rfl⟩ := hw
    obtain ⟨s, rfl⟩ := D.mem_T'.mp hg
    refine Subgroup.subset_closure ⟨D.up (-s), D.mem_T.mpr ⟨-s, rfl⟩,
      D.ρ weylSL⁻¹ u, D.ρ_mem_commV _ hu, ?_⟩
    have h1 : D.ρ weylSL⁻¹ (D.lo s u) = D.up (-s) (D.ρ weylSL⁻¹ u) := by
      have := congrArg (fun m => D.ρ m u) (weylSL_inv_mul_lowerUni s)
      simpa [lo, up] using this
    have key : D.ρ weylSL⁻¹ (D.lo s u * u⁻¹) =
        D.up (-s) (D.ρ weylSL⁻¹ u) * (D.ρ weylSL⁻¹ u)⁻¹ := by
      rw [map_mul, map_inv (D.ρ weylSL⁻¹) u, h1]
    exact key.symm
  | one => simp [one_mem]
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

theorem A0_le_commOn_T (h4 : ∃ s : Finset K, s.card = 4) :
    commV G ⊓ fixV G ≤ commOn D.T (commV G) := by
  rintro x ⟨hxU, hxf⟩
  obtain ⟨p, hp, p', hp', rfl⟩ := Subgroup.mem_sup.mp (D.commV_le_commOn_sup h4 hxU)
  have hpP := D.commOn_T_le_P hp
  have hp'P := D.commOn_T'_le_P' hp'
  have hpU := D.commOn_T_le_U hp
  have hp'U := D.commOn_T'_le_U hp'
  have h0 : D.coord (p * p') = 0 := (D.coord_eq_zero_iff hxU).mpr hxf
  rw [D.coord_mul hpU hp'U] at h0
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  simp only [Pi.add_apply, Pi.zero_apply] at e0 e1
  have hpz : D.coord p = 0 := by
    ext i
    fin_cases i
    · have := e0
      rw [hp'P.2, add_zero] at this
      simpa using this
    · simpa using hpP.2
  have hp'z : D.coord p' = 0 := by
    ext i
    fin_cases i
    · simpa using hp'P.2
    · have := e1
      rw [hpP.2, zero_add] at this
      simpa using this
  have hpA : p ∈ fixV G := (D.coord_eq_zero_iff hpU).mp hpz
  have hp'A : p' ∈ fixV G := (D.coord_eq_zero_iff hp'U).mp hp'z
  have hw : D.ρ weylSL⁻¹ p' = p' := mem_fixV.mp hp'A _ (D.ρ_mem _)
  have hp'T : p' ∈ commOn D.T (commV G) := hw ▸ D.weyl_conj_commOn hp'
  exact mul_mem hp hp'T

@[expose] def deltaHom (g : MulAut V) : V →* V := g.toMonoidHom * (MonoidHom.id V)⁻¹

@[expose] def Xs (s : K) : Subgroup V := (commV G).map (deltaHom (D.up s))

theorem mem_Xs {s : K} {x : V} : x ∈ D.Xs s ↔ ∃ u ∈ commV G, D.up s u * u⁻¹ = x := by
  unfold Xs
  rw [Subgroup.mem_map]
  rfl

theorem Xs_le_P (s : K) : D.Xs s ≤ D.P := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := D.mem_Xs.mp hx
  exact D.up_comm_mem_P hu s

@[expose] def Tor : Subgroup (MulAut V) := (D.ρ.comp diagHom).range

theorem mem_Tor {g : MulAut V} : g ∈ D.Tor ↔ ∃ l : Kˣ, D.dg l = g := by
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l, rfl⟩
  · rintro ⟨l, rfl⟩
    exact ⟨l, rfl⟩

theorem Tor_le_G : D.Tor ≤ G := by
  intro g hg
  obtain ⟨l, rfl⟩ := D.mem_Tor.mp hg
  exact D.dg_mem l

theorem dg_P {l : Kˣ} {p : V} (hp : p ∈ D.P) : D.dg l p ∈ D.P := by
  refine ⟨D.dg_mem_commV hp.1 l, ?_⟩
  rw [D.coord_dg hp.1]
  simp [hp.2]

theorem Tor_P {g : MulAut V} (hg : g ∈ D.Tor) {p : V} (hp : p ∈ D.P) : g p ∈ D.P := by
  obtain ⟨l, rfl⟩ := D.mem_Tor.mp hg
  exact D.dg_P hp

theorem mem_A0_of_fix_dg {l : Kˣ} (hl : l ≠ 1) {p : V} (hp : p ∈ D.P) (hf : D.dg l p = p) :
    p ∈ commV G ⊓ fixV G := by
  refine ⟨hp.1, (D.coord_eq_zero_iff hp.1).mp ?_⟩
  have h := congrArg D.coord hf
  rw [D.coord_dg hp.1] at h
  have e0 := congrFun h 0
  simp only [Matrix.cons_val_zero] at e0
  have hl' : (l : K) ≠ 1 := fun h' => hl (Units.ext h')
  have hc0 : D.coord p 0 = 0 := by
    by_contra hc
    exact hl' (by simpa [hc] using e0)
  ext i
  fin_cases i
  · simpa using hc0
  · simpa using hp.2

theorem conj_up_apply (l : Kˣ) (s : K) (u : V) :
    D.up ((l : K) ^ 2 * s) u * u⁻¹ =
      D.dg l (D.up s ((D.dg l)⁻¹ u) * ((D.dg l)⁻¹ u)⁻¹) := by
  rw [← D.dg_conj_up l s]
  rw [map_mul, map_inv (D.dg l) _]
  simp [MulAut.mul_apply]

section TorusMain

variable [CharP K 2] [Finite K] [Finite V]

noncomputable instance instFintypeTor : Fintype ↥D.Tor := Fintype.ofFinite _

theorem odd_card_Tor : Odd (Fintype.card ↥D.Tor) := by
  rw [← Nat.card_eq_fintype_card]
  have hdvd : Nat.card ↥D.Tor ∣ Nat.card Kˣ := Subgroup.card_range_dvd (D.ρ.comp diagHom)
  rw [Nat.card_units] at hdvd
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hcard : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hn1 : 1 ≤ (n : ℕ) := n.pos
  have h2 : 2 ∣ Nat.card K := by rw [hcard]; exact dvd_pow_self 2 (by omega)
  have hpos : 0 < Nat.card K := Nat.card_pos
  refine Odd.of_dvd_nat ?_ hdvd
  obtain ⟨m, hm⟩ := h2
  exact ⟨m - 1, by omega⟩

omit [Finite V] [CharP K 2] in
theorem exists_unit_ne_one (h4 : 4 ≤ Nat.card K) : ∃ l : Kˣ, l ≠ 1 := by
  have h1 : 1 < Nat.card Kˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp h1
  exact exists_ne 1

omit [Finite V] in
theorem exists_unit_sq {s₁ s : K} (h1 : s₁ ≠ 0) (hs : s ≠ 0) :
    ∃ l : Kˣ, (l : K) ^ 2 * s₁ = s := by
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (F := K) (ringChar.eq K 2) (s / s₁)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero, div_eq_zero_iff] at hc
    exact hs (hc.resolve_right h1)
  refine ⟨Units.mk0 c hc0, ?_⟩
  simp only [Units.val_mk0]
  rw [sq, ← hc]
  field_simp

omit [CharP K 2] [Finite K] in
theorem normK_mem_P {p : V} (hp : p ∈ D.P) : normK D.Tor p ∈ D.P := by
  rw [normK_apply]
  exact Subgroup.prod_mem _ (fun k _ => D.Tor_P k.2 hp)

omit [CharP K 2] in
theorem normK_mem_A0 (h4 : 4 ≤ Nat.card K) {p : V} (hp : p ∈ D.P) :
    normK D.Tor p ∈ commV G ⊓ fixV G := by
  obtain ⟨l, hl⟩ := exists_unit_ne_one h4
  refine D.mem_A0_of_fix_dg hl (D.normK_mem_P hp) ?_
  exact mem_fixV.mp (normK_mem_fixV D.Tor p) (D.dg l) (D.mem_Tor.mpr ⟨l, rfl⟩)

theorem normK_A0 (hV : ∀ v : V, v ^ 2 = 1) {a : V} (ha : a ∈ commV G ⊓ fixV G) :
    normK D.Tor a = a := by
  have hfix : a ∈ fixV D.Tor := fun g hg => mem_fixV.mp ha.2 g (D.Tor_le_G hg)
  exact normK_of_mem_fixV' D.Tor D.odd_card_Tor hV hfix

theorem pi_Xs_surj (hV : ∀ v : V, v ^ 2 = 1) (h4 : 4 ≤ Nat.card K) {s : K} (hs : s ≠ 0) :
    ∀ a ∈ commV G ⊓ fixV G, ∃ x ∈ D.Xs s, normK D.Tor x = a := by
  have h4' : ∃ s : Finset K, s.card = 4 := CFSG.LinearGroups.exists_finset_card_eq_four h4
  let R : Subgroup V := (D.Xs s).map (normK D.Tor)
  have key : ∀ z ∈ commOn D.T (commV G), normK D.Tor z ∈ R := by
    intro z hz
    unfold commOn at hz
    induction hz using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨g, hg, u, hu, rfl⟩ := hw
      obtain ⟨s', rfl⟩ := D.mem_T.mp hg
      by_cases hs' : s' = 0
      · subst hs'
        rw [D.up_zero]
        simp
      · obtain ⟨l', hl'⟩ := exists_unit_sq hs hs'
        have hu' : (D.dg l')⁻¹ u ∈ commV G := commV_invariant (inv_mem (D.dg_mem l')) hu
        have hxx : D.up s' u * u⁻¹ =
            D.dg l' (D.up s ((D.dg l')⁻¹ u) * ((D.dg l')⁻¹ u)⁻¹) := by
          rw [← hl']
          exact D.conj_up_apply l' s u
        have hx'' : D.up s ((D.dg l')⁻¹ u) * ((D.dg l')⁻¹ u)⁻¹ ∈ D.Xs s :=
          D.mem_Xs.mpr ⟨_, hu', rfl⟩
        rw [hxx, normK_apply_mem D.Tor (D.mem_Tor.mpr ⟨l', rfl⟩)]
        exact Subgroup.mem_map.mpr ⟨_, hx'', rfl⟩
    | one => simp
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
    | inv a _ ha => rw [map_inv]; exact inv_mem ha
  intro a ha
  have h1' := key a (D.A0_le_commOn_T h4' ha)
  rw [D.normK_A0 hV ha] at h1'
  obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp h1'
  exact ⟨x, hx, hxa⟩

theorem pair_A0 (hV : ∀ v : V, v ^ 2 = 1) (h4 : 4 ≤ Nat.card K) {s₁ s₂ : K} (h1 : s₁ ≠ 0)
    (h2 : s₂ ≠ 0) (h12 : s₁ ≠ s₂) :
    ∀ z ∈ commV G ⊓ fixV G, ∃ u ∈ commV G, ∃ u' ∈ commV G,
      z = (D.up s₁ u * u⁻¹) * (D.up s₂ u' * u'⁻¹) := by
  obtain ⟨l, hl⟩ := exists_unit_sq h1 h2
  have hl1 : l ≠ 1 := by
    rintro rfl
    apply h12
    rw [← hl]
    simp
  have hlTor : D.dg l ∈ D.Tor := D.mem_Tor.mpr ⟨l, rfl⟩
  have hinvTor : (D.dg l)⁻¹ ∈ D.Tor := inv_mem hlTor
  have hπX := D.pi_Xs_surj hV h4 h1
  intro z hz
  obtain ⟨x, hx, x', hx', hz'⟩ := graph_lemma hV D.P (commV G ⊓ fixV G) (D.Xs s₁)
    (normK D.Tor) (D.dg l) D.A0_le_P (D.Xs_le_P s₁)
    (fun p hp => D.normK_mem_A0 h4 hp) (fun a ha => D.normK_A0 hV ha)
    (fun p hp => D.Tor_P hinvTor hp)
    (fun p _ => normK_apply_mem D.Tor hlTor p)
    (fun a ha => mem_fixV.mp ha.2 _ (D.dg_mem l))
    (by
      rw [eq_bot_iff]
      rintro x ⟨hxX, hxA⟩
      obtain ⟨u, hu, rfl⟩ := D.mem_Xs.mp hxX
      have h0 := (D.coord_eq_zero_iff hxA.1).mpr hxA.2
      rw [D.coord_up_comm hu] at h0
      have e0 := congrFun h0 0
      simp only [Matrix.cons_val_zero, Pi.zero_apply] at e0
      have hc1 : D.coord u 1 = 0 := (mul_eq_zero.mp e0).resolve_left h1
      have hup : D.up s₁ u = u := D.up_fix_P hV s₁ ⟨hu, hc1⟩
      rw [Subgroup.mem_bot, hup, mul_inv_cancel])
    (fun p hp => by
      obtain ⟨u, hu, ha⟩ := D.exists_comm_mul_A0 h1 hp
      refine ⟨D.up s₁ u * u⁻¹, D.mem_Xs.mpr ⟨u, hu, rfl⟩, p * (D.up s₁ u * u⁻¹)⁻¹,
        ⟨(commV G).mul_mem hp.1 ((commV G).inv_mem
          ((commV G).mul_mem (D.up_mem_commV hu s₁) ((commV G).inv_mem hu))), ha⟩, ?_⟩
      rw [mul_comm p, _root_.mul_inv_cancel_left])
    hπX
    (fun p hp hπ hf => by
      have hpA := D.mem_A0_of_fix_dg hl1 hp hf
      rw [D.normK_A0 hV hpA] at hπ
      exact hπ)
    z hz
  obtain ⟨u, hu, rfl⟩ := D.mem_Xs.mp hx
  obtain ⟨u₂, hu₂, rfl⟩ := D.mem_Xs.mp hx'
  refine ⟨u, hu, D.dg l u₂, D.dg_mem_commV hu₂ l, ?_⟩
  rw [hz']
  congr 1
  rw [← hl, D.conj_up_apply l s₁ (D.dg l u₂)]
  simp

end TorusMain

section Final

variable [CharP K 2] [Finite K] [Finite V]

omit [CharP K 2] in
theorem exists_two_ne_one {H : Type*} [Group H] [Finite H] (h : 3 ≤ Nat.card H) :
    ∃ a b : H, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  by_contra hcon
  push Not at hcon
  by_cases htriv : ∀ a : H, a = 1
  · have hsub : Subsingleton H := ⟨fun a b => by rw [htriv a, htriv b]⟩
    rw [Nat.card_of_subsingleton (1 : H)] at h
    omega
  · push Not at htriv
    obtain ⟨a, ha⟩ := htriv
    have hsurj : Function.Surjective (fun b : Bool => if b then (1 : H) else a) := by
      intro g
      by_cases hg : g = 1
      · exact ⟨true, by simp [hg]⟩
      · exact ⟨false, by simp [hcon a g ha hg]⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    simp at this
    omega

theorem P_le_commV_pair (hV : ∀ v : V, v ^ 2 = 1) (h4 : 4 ≤ Nat.card K) {B : Subgroup (MulAut V)}
    {s₁ s₂ : K} (h1 : s₁ ≠ 0) (h2 : s₂ ≠ 0) (h12 : s₁ ≠ s₂) (hB1 : D.up s₁ ∈ B)
    (hB2 : D.up s₂ ∈ B) : D.P ≤ commV B := by
  have hA : commV G ⊓ fixV G ≤ commV B := by
    intro z hz
    obtain ⟨u, hu, u', hu', rfl⟩ := D.pair_A0 hV h4 h1 h2 h12 z hz
    exact mul_mem (Subgroup.subset_closure ⟨D.up s₁, hB1, u, rfl⟩)
      (Subgroup.subset_closure ⟨D.up s₂, hB2, u', rfl⟩)
  intro p hp
  obtain ⟨u, hu, ha⟩ := D.exists_comm_mul_A0 h1 hp
  have hx : D.up s₁ u * u⁻¹ ∈ commV B := Subgroup.subset_closure ⟨D.up s₁, hB1, u, rfl⟩
  have hxU : D.up s₁ u * u⁻¹ ∈ commV G :=
    (commV G).mul_mem (D.up_mem_commV hu s₁) ((commV G).inv_mem hu)
  have hA' : p * (D.up s₁ u * u⁻¹)⁻¹ ∈ commV B :=
    hA ⟨(commV G).mul_mem hp.1 ((commV G).inv_mem hxU), ha⟩
  have := (commV B).mul_mem hA' hx
  rwa [_root_.inv_mul_cancel_right] at this

omit [Finite K] [CharP K 2] [Finite V] in
theorem card_T : Nat.card D.T = Nat.card K := by
  have hinj : Function.Injective (D.ρ.comp unipotentHom) :=
    D.inj.comp unipotentHom_injective
  exact ((Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm).trans
    (Nat.card_congr Multiplicative.toAdd)

theorem P_le_commV_of_card (hV : ∀ v : V, v ^ 2 = 1) (h4 : 4 ≤ Nat.card K)
    {B : Subgroup (MulAut V)} (hBT : B ≤ D.T) (hB : 3 ≤ Nat.card B) : D.P ≤ commV B := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_two_ne_one hB
  obtain ⟨s₁, hs₁⟩ := D.mem_T.mp (hBT a.2)
  obtain ⟨s₂, hs₂⟩ := D.mem_T.mp (hBT b.2)
  have h1 : s₁ ≠ 0 := by
    rintro rfl
    apply ha
    apply Subtype.ext
    rw [← hs₁, D.up_zero]
    rfl
  have h2 : s₂ ≠ 0 := by
    rintro rfl
    apply hb
    apply Subtype.ext
    rw [← hs₂, D.up_zero]
    rfl
  have h12 : s₁ ≠ s₂ := by
    rintro rfl
    exact hab (Subtype.ext (hs₁.symm.trans hs₂))
  exact D.P_le_commV_pair hV h4 h1 h2 h12 (hs₁ ▸ a.2) (hs₂ ▸ b.2)

theorem sylow_facts (hV : ∀ v : V, v ^ 2 = 1) (h4 : 4 ≤ Nat.card K) :
    IsElemAbelian2 D.T ∧ commV D.T ≤ fixV D.T ∧ commV D.T = commV G ⊓ fixV D.T ∧
      ∀ B : Subgroup (MulAut V), B ≤ D.T → 4 ≤ Nat.card B → commV B = commV D.T := by
  have hT3 : 3 ≤ Nat.card D.T := by rw [D.card_T]; omega
  have hPT : D.P ≤ commV D.T := D.P_le_commV_of_card hV h4 le_rfl hT3
  have hTP : commV D.T ≤ D.P := D.commV_T_le_P hV
  refine ⟨D.isElemAbelian2_T, D.commV_T_le_fixV_T hV, ?_, ?_⟩
  · rw [← D.P_eq_inf_fixV_T hV]
    exact le_antisymm hTP hPT
  · intro B hBT hB
    exact le_antisymm (commV_mono hBT)
      (hTP.trans (D.P_le_commV_of_card hV h4 hBT (by omega)))

end Final

end NatData

end CFSG.CGT.PushingUpLit.CGT6.TwoThree

module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs123b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL34
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input236gt

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts5

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open Equiv Equiv.Perm
open scoped commutatorElement

section PermP

variable {α : Type} [Fintype α] [DecidableEq α]

theorem pow_p_of_mem_uSub {p : ℕ} {σ u : Perm α} (hσ : σ ^ p = 1) (hu : u ∈ Claims126.uSub σ) :
    u ^ p = 1 := by
  ext x
  obtain ⟨k, hk⟩ := hu.2 x
  rw [Claims126.pow_apply_of_mem_uSub hu hk p, pow_mul, hσ, one_pow]

theorem mem_alt_of_pow {p : ℕ} (hp : Odd p) {σ : Perm α} (hσ : σ ^ p = 1) : σ ∈ alternatingGroup α := by
  rw [Perm.mem_alternatingGroup]
  have h := congrArg Perm.sign hσ
  rw [map_pow, map_one] at h
  rcases Int.units_eq_one_or (Perm.sign σ) with h' | h'
  · exact h'
  · rw [h', Odd.neg_one_pow hp] at h
    exact absurd h (by decide)

theorem uSub_le_alt {p : ℕ} (hp : Odd p) {σ : Perm α} (hσ : σ ^ p = 1) :
    Claims126.uSub σ ≤ alternatingGroup α := fun _ hu => mem_alt_of_pow hp (pow_p_of_mem_uSub hσ hu)

end PermP

section Gen

variable {n : ℕ}

theorem eq_one_of_fix_three {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {h : Perm (Fin n)} (hA : h ∈ alternatingGroup (Fin n))
    (hout : ∀ x, x ≠ a → x ≠ b → x ≠ c → h x = x) (ha : h a = a) : h = 1 := by
  have hb : h b = b ∨ h b = c := by
    by_contra hcon
    push Not at hcon
    have hba : h b ≠ a := fun e => hab (h.injective (ha.trans e.symm))
    exact hcon.1 (h.injective (hout (h b) hba hcon.1 hcon.2))
  have hca : h c ≠ a := fun e => hac (h.injective (ha.trans e.symm))
  rcases hb with hb | hb
  · have hc : h c = c := by
      by_contra hne
      have hcb : h c ≠ b := fun e => hbc (h.injective (hb.trans e.symm))
      exact hne (h.injective (hout (h c) hca hcb hne))
    ext x
    by_cases hxa : x = a
    · subst hxa; simp [ha]
    by_cases hxb : x = b
    · subst hxb; simp [hb]
    by_cases hxc : x = c
    · subst hxc; simp [hc]
    simp [hout x hxa hxb hxc]
  · exfalso
    have hc : h c = b := by
      by_contra hne
      have hcc : h c ≠ c := fun e => hbc (h.injective (hb.trans e.symm))
      exact hcc (h.injective (hout (h c) hca hne hcc))
    have hsw : h = swap b c := by
      ext x
      by_cases hxa : x = a
      · subst hxa; simp [ha, swap_apply_of_ne_of_ne hab hac]
      by_cases hxb : x = b
      · subst hxb; simp [hb]
      by_cases hxc : x = c
      · subst hxc; simp [hc]
      simp [hout x hxa hxb hxc, swap_apply_of_ne_of_ne hxb hxc]
    rw [hsw, Perm.mem_alternatingGroup, Perm.sign_swap hbc] at hA
    exact absurd hA (by decide)

theorem altOn_three_le {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {Γ : Subgroup (Perm (Fin n))} (hg : swap a c * swap a b ∈ Γ) :
    GL83.altOn ({a, b, c} : Set (Fin n)) ≤ Γ := by
  intro h hh
  rw [GL83.mem_altOn] at hh
  obtain ⟨hA, hout⟩ := hh
  have hout' : ∀ x, x ≠ a → x ≠ b → x ≠ c → h x = x := fun x h1 h2 h3 =>
    hout x (by simp [h1, h2, h3])
  set g := swap a c * swap a b with hgdef
  have hga : g a = b := by simp [hgdef, swap_apply_of_ne_of_ne hab.symm hbc]
  have hgb : g b = c := by simp [hgdef]
  have hgc : g c = a := by simp [hgdef, swap_apply_of_ne_of_ne hac.symm hbc.symm]
  have hgA : g ∈ alternatingGroup (Fin n) :=
    (isThreeCycle_swap_mul_swap_same hac hab hbc.symm).mem_alternatingGroup
  have hgout : ∀ x, x ≠ a → x ≠ b → x ≠ c → g x = x := fun x h1 h2 h3 => by
    simp [hgdef, swap_apply_of_ne_of_ne h1 h2, swap_apply_of_ne_of_ne h1 h3]
  have hginv : ∀ x, x ≠ a → x ≠ b → x ≠ c → g⁻¹ x = x := fun x h1 h2 h3 => by
    rw [Perm.inv_eq_iff_eq]; exact (hgout x h1 h2 h3).symm
  have hha : h a = a ∨ h a = b ∨ h a = c := by
    by_contra hcon
    push Not at hcon
    exact hcon.1 (h.injective (hout' (h a) hcon.1 hcon.2.1 hcon.2.2))
  rcases hha with h1 | h1 | h1
  · rw [eq_one_of_fix_three hab hac hbc hA hout' h1]
    exact Γ.one_mem
  · have hk : g⁻¹ * h = 1 := by
      refine eq_one_of_fix_three hab hac hbc ((alternatingGroup (Fin n)).mul_mem
        ((alternatingGroup (Fin n)).inv_mem hgA) hA) (fun x h1' h2' h3' => ?_) ?_
      · rw [Perm.mul_apply, hout' x h1' h2' h3', hginv x h1' h2' h3']
      · rw [Perm.mul_apply, h1, Perm.inv_eq_iff_eq, hga]
    have : h = g := (inv_mul_eq_one.1 hk).symm
    rw [this]
    exact hg
  · have hk : (g * g)⁻¹ * h = 1 := by
      have hgg : (g * g) a = c := by rw [Perm.mul_apply, hga, hgb]
      refine eq_one_of_fix_three hab hac hbc ((alternatingGroup (Fin n)).mul_mem
        ((alternatingGroup (Fin n)).inv_mem ((alternatingGroup (Fin n)).mul_mem hgA hgA)) hA)
        (fun x h1' h2' h3' => ?_) ?_
      · rw [Perm.mul_apply, hout' x h1' h2' h3', Perm.inv_eq_iff_eq, Perm.mul_apply,
          hgout x h1' h2' h3', hgout x h1' h2' h3']
      · rw [Perm.mul_apply, h1, Perm.inv_eq_iff_eq, hgg]
    have : h = g * g := (inv_mul_eq_one.1 hk).symm
    rw [this]
    exact Γ.mul_mem hg hg

theorem altOn_image_le {Γ : Subgroup (Perm (Fin n))} {U : Set (Fin n)} (hU : GL83.altOn U ≤ Γ)
    {v : Perm (Fin n)} (hv : v ∈ Γ) : GL83.altOn (v '' U) ≤ Γ := by
  intro h hh
  rw [GL83.mem_altOn] at hh
  have hmem : v⁻¹ * h * v ∈ GL83.altOn U := by
    rw [GL83.mem_altOn]
    refine ⟨?_, fun x hx => ?_⟩
    · have := (alternatingGroup.normal (α := Fin n)).conj_mem h hh.1 v⁻¹
      simpa using this
    · have hvx : v x ∉ v '' U := fun ⟨y, hy, hyx⟩ => hx (v.injective hyx ▸ hy)
      rw [Perm.mul_apply, Perm.mul_apply, hh.2 _ hvx]
      exact Perm.inv_eq_iff_eq.2 rfl
  have := Γ.mul_mem (Γ.mul_mem hv (hU hmem)) (Γ.inv_mem hv)
  simpa [mul_assoc] using this

theorem gl83_altOn_le (β : Perm (Fin n)) :
    GL83.altOn ((β.supportᶜ : Finset (Fin n)) : Set (Fin n)) ≤ Claims126.altOn β.supportᶜ := by
  intro g hg
  rw [GL83.mem_altOn] at hg
  refine Claims126.mem_altOn.2 ⟨hg.1, fun x hx => ?_⟩
  by_contra hxs
  exact (Perm.mem_support.1 hx) (hg.2 x (by simpa using hxs))

theorem exists_two_of_card_four {s₀ : Finset (Fin n)} (h4 : s₀.card = 4) {x y : Fin n} (hx : x ∈ s₀)
    (hy : y ∈ s₀) (hxy : x ≠ y) :
    ∃ a b : Fin n, a ∈ s₀ ∧ b ∈ s₀ ∧ a ≠ b ∧ x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b ∧
      ∀ z ∈ s₀, z = x ∨ z = y ∨ z = a ∨ z = b := by
  have h2 : ((s₀.erase x).erase y).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hxy.symm, hy⟩), Finset.card_erase_of_mem hx, h4]
  obtain ⟨a, b, hab, hab'⟩ := Finset.card_eq_two.1 h2
  have ha : a ∈ (s₀.erase x).erase y := by rw [hab']; simp
  have hb : b ∈ (s₀.erase x).erase y := by rw [hab']; simp
  simp only [Finset.mem_erase] at ha hb
  refine ⟨a, b, ha.2.2, hb.2.2, hab, Ne.symm ha.2.1, Ne.symm hb.2.1, Ne.symm ha.1, Ne.symm hb.1,
    fun z hz => ?_⟩
  by_cases hzx : z = x
  · exact Or.inl hzx
  by_cases hzy : z = y
  · exact Or.inr (Or.inl hzy)
  have : z ∈ (s₀.erase x).erase y := by simp [hzx, hzy, hz]
  rw [hab'] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  tauto

theorem fix_of_comm {p : ℕ} (hp : Odd p) {β β' : Perm (Fin n)} (hcomm : β * β' = β' * β)
    (hβ'p : β' ^ p = 1) (h4 : β.supportᶜ.card = 4) {x y : Fin n} (hxy : x ≠ y) (hx : β x = x)
    (hy : β y = y) (hx' : β' x = x) (hy' : β' y = y) : ∀ w, β w = w → β' w = w := by
  have hmem : ∀ z, z ∈ β.supportᶜ ↔ β z = z := fun z => by
    rw [Finset.mem_compl, Perm.mem_support, not_not]
  have hinv : ∀ z, β z = z → β (β' z) = β' z := fun z hz => by
    rw [← Perm.mul_apply, hcomm, Perm.mul_apply, hz]
  intro w hw
  by_contra hne
  have hwx : w ≠ x := fun h => hne (h ▸ hx')
  have hwy : w ≠ y := fun h => hne (h ▸ hy')
  have hw'x : β' w ≠ x := fun h => hwx (β'.injective (h.trans hx'.symm))
  have hw'y : β' w ≠ y := fun h => hwy (β'.injective (h.trans hy'.symm))
  have h1 : β' (β' w) ≠ x := fun h => hw'x (β'.injective (h.trans hx'.symm))
  have h2 : β' (β' w) ≠ y := fun h => hw'y (β'.injective (h.trans hy'.symm))
  have h3 : β' (β' w) ≠ β' w := fun h => hne (β'.injective h)
  obtain ⟨a, b, ha, hb, hab, hxa, hxb, hya, hyb, hall⟩ :=
    exists_two_of_card_four h4 ((hmem x).2 hx) ((hmem y).2 hy) hxy
  have hw2 : β' (β' w) = w := by
    have e1 := hall w ((hmem w).2 hw)
    have e2 := hall (β' w) ((hmem _).2 (hinv w hw))
    have e3 := hall (β' (β' w)) ((hmem _).2 (hinv _ (hinv w hw)))
    rcases e1 with e1 | e1 | e1 | e1
    · exact absurd e1 hwx
    · exact absurd e1 hwy
    · rcases e2 with e2 | e2 | e2 | e2
      · exact absurd e2 hw'x
      · exact absurd e2 hw'y
      · exact absurd (e2.trans e1.symm) hne
      · rcases e3 with e3 | e3 | e3 | e3
        · exact absurd e3 h1
        · exact absurd e3 h2
        · rw [e3, e1]
        · exact absurd (e3.trans e2.symm) h3
    · rcases e2 with e2 | e2 | e2 | e2
      · exact absurd e2 hw'x
      · exact absurd e2 hw'y
      · rcases e3 with e3 | e3 | e3 | e3
        · exact absurd e3 h1
        · exact absurd e3 h2
        · exact absurd (e3.trans e2.symm) h3
        · rw [e3, e1]
      · exact absurd (e2.trans e1.symm) hne
  obtain ⟨k, hk⟩ := hp
  have hsq : (β' ^ 2) (β' w) = β' w := by
    rw [sq, Perm.mul_apply, hw2]
  have hpw : (β' ^ p) w = β' w := by
    rw [hk, pow_succ, Perm.mul_apply, pow_mul]
    exact Perm.pow_apply_eq_self_of_apply_eq_self hsq k
  rw [hβ'p, Perm.one_apply] at hpw
  exact hne hpw.symm

theorem alt_le_of_fix' {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hpn : ¬ p ∣ n) (h5 : 5 ≤ n)
    {T Γ : Subgroup (Perm (Fin n))} (hT : IsElemAbelian p T)
    (hreg : ∀ i, ∃ β ∈ T, β ≠ 1 ∧ β i = i)
    (halt : ∀ β ∈ T, β ≠ 1 → 5 ≤ β.supportᶜ.card → Claims126.altOn β.supportᶜ ≤ Γ)
    (hkl : ∀ β ∈ T, β ≠ 1 → β.supportᶜ.card = 4 → Claims126.kleinOn β.supportᶜ ≤ Γ) :
    alternatingGroup (Fin n) ≤ Γ := by
  classical
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  have hTp : IsPGroup p T := fun g => ⟨1, Subtype.ext (by simpa using hT.2 g g.2)⟩
  have hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hT.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hmem : ∀ (β : Perm (Fin n)) z, z ∈ β.supportᶜ ↔ β z = z := fun β z => by
    rw [Finset.mem_compl, Perm.mem_support, not_not]
  set F₀ : Finset (Fin n) := Finset.univ.filter (fun i => ∀ β ∈ T, β i = i) with hF₀
  have hF₀mod : F₀.card ≡ n [MOD p] := by
    have h := AltFacts3.card_fixedPoints_modEq hTp T.subtype
    have e : Nat.card {i : Fin n // ∀ q : ↥T, T.subtype q i = i} = F₀.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hF₀]
      congr 1
      ext i
      simp
    rwa [e] at h
  have hF₀pos : 0 < F₀.card := by
    by_contra h0
    have h00 : F₀.card = 0 := by omega
    rw [h00] at hF₀mod
    exact hpn (Nat.modEq_zero_iff_dvd.1 hF₀mod.symm)
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.1 hF₀pos
  have hx₀' : ∀ β ∈ T, β x₀ = x₀ := (Finset.mem_filter.1 hx₀).2
  have hβmod : ∀ β ∈ T, β.supportᶜ.card ≡ n [MOD p] := fun β hβ => by
    have := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) (σ := β)
      (by rw [pow_one]; exact hT.2 β hβ)
    rwa [Fintype.card_fin] at this
  have hF₀sub : ∀ β ∈ T, F₀ ⊆ β.supportᶜ := fun β hβ i hi =>
    (hmem β i).2 ((Finset.mem_filter.1 hi).2 β hβ)
  have hbig : ∀ β ∈ T, ∀ i, β i = i → i ∉ F₀ → F₀.card + p ≤ β.supportᶜ.card := by
    intro β hβ i hi hiF
    have hlt : F₀.card < β.supportᶜ.card :=
      Finset.card_lt_card ((Finset.ssubset_iff_of_subset (hF₀sub β hβ)).2 ⟨i, (hmem β i).2 hi, hiF⟩)
    have hmod : F₀.card ≡ β.supportᶜ.card [MOD p] := hF₀mod.trans (hβmod β hβ).symm
    obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hlt.le).1 hmod
    have hk0 : k ≠ 0 := by
      rintro rfl
      omega
    have : p ≤ p * k := Nat.le_mul_of_pos_right p (Nat.pos_of_ne_zero hk0)
    omega
  obtain ⟨β₁, hβ₁, hβ₁1, -⟩ := hreg x₀
  by_cases hA : ∃ β₀ ∈ T, β₀ ≠ 1 ∧ 5 ≤ β₀.supportᶜ.card
  ·
    obtain ⟨β₀, hβ₀, hβ₀1, hβ₀5⟩ := hA
    set U₀ : Set (Fin n) := ((β₀.supportᶜ : Finset (Fin n)) : Set (Fin n)) with hU₀
    have hU₀Γ : GL83.altOn U₀ ≤ Γ := (gl83_altOn_le β₀).trans (halt β₀ hβ₀ hβ₀1 hβ₀5)
    have hU₀card : 5 ≤ U₀.ncard := by rw [hU₀, Set.ncard_coe_finset]; exact hβ₀5
    have hU₀mem : ∀ z, z ∈ U₀ ↔ β₀ z = z := fun z => by
      rw [hU₀, Finset.mem_coe, hmem]
    have hx₀U : x₀ ∈ U₀ := (hU₀mem x₀).2 (hx₀' β₀ hβ₀)
    have hW : ∀ s : Fin n, ∃ W : Set (Fin n), s ∈ W ∧ 3 ≤ W.ncard ∧ GL83.altOn W ≤ Γ ∧
        (W ∩ U₀).Nonempty := by
      intro s
      by_cases hs : β₀ s = s
      · exact ⟨U₀, (hU₀mem s).2 hs, by omega, hU₀Γ, ⟨x₀, hx₀U, hx₀U⟩⟩
      · have hsF : s ∉ F₀ := fun h => hs ((Finset.mem_filter.1 h).2 β₀ hβ₀)
        obtain ⟨β, hβ, hβ1, hβs⟩ := hreg s
        have h4 : 4 ≤ β.supportᶜ.card := by have := hbig β hβ s hβs hsF; omega
        rcases (show 5 ≤ β.supportᶜ.card ∨ β.supportᶜ.card = 4 by omega) with h5' | h4'
        · refine ⟨((β.supportᶜ : Finset (Fin n)) : Set (Fin n)), by simpa [hmem] using hβs, ?_,
            (gl83_altOn_le β).trans (halt β hβ hβ1 h5'), ⟨x₀, by simpa [hmem] using hx₀' β hβ, hx₀U⟩⟩
          rw [Set.ncard_coe_finset]
          omega
        · have hx₀s : x₀ ≠ s := fun h => hs (h ▸ hx₀' β₀ hβ₀)
          obtain ⟨a, b, ha, hb, hab, hxa, hxb, hsa, hsb, hall⟩ :=
            exists_two_of_card_four h4' ((hmem β x₀).2 (hx₀' β hβ)) ((hmem β s).2 hβs) hx₀s
          set v : Perm (Fin n) := swap x₀ s * swap a b with hv
          have hvΓ : v ∈ Γ := hkl β hβ hβ1 h4' (Claims126.swap_mul_swap_mem_kleinOn h4'
            (by simp [hx₀s, hxa, hxb, hsa, hsb, hab]) ((hmem β x₀).2 (hx₀' β hβ))
            ((hmem β s).2 hβs) ha hb)
          refine ⟨v '' U₀, ⟨x₀, hx₀U, ?_⟩, ?_, altOn_image_le hU₀Γ hvΓ, ?_⟩
          · rw [hv, Perm.mul_apply, swap_apply_of_ne_of_ne hxa hxb, swap_apply_left]
          · rw [Set.ncard_image_of_injective _ v.injective]
            omega
          · obtain ⟨u, hu, hu'⟩ : ∃ u ∈ β₀.supportᶜ, u ∉ β.supportᶜ := by
              by_contra hcon
              push Not at hcon
              have := Finset.card_le_card (show β₀.supportᶜ ⊆ β.supportᶜ from hcon)
              omega
            have hux : u ≠ x₀ := fun e => hu' (e ▸ (hmem β x₀).2 (hx₀' β hβ))
            have hus : u ≠ s := fun e => hu' (e ▸ (hmem β s).2 hβs)
            have hua : u ≠ a := fun e => hu' (e ▸ ha)
            have hub : u ≠ b := fun e => hu' (e ▸ hb)
            have hvu : v u = u := by
              rw [hv, Perm.mul_apply, swap_apply_of_ne_of_ne hua hub, swap_apply_of_ne_of_ne hux hus]
            have huU : u ∈ U₀ := by rw [hU₀, Finset.mem_coe]; exact hu
            exact ⟨u, ⟨u, huU, hvu⟩, huU⟩
    choose W hWs hW3 hWΓ hWU using hW
    let S : Option (Fin n) → Set (Fin n) := fun o => o.elim U₀ W
    have hcover : (⋃ o, S o) = Set.univ :=
      Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨some x, hWs x⟩
    have hS3 : ∀ o, 3 ≤ (S o).ncard := by
      rintro (_ | s)
      · exact (by omega : 3 ≤ 5).trans hU₀card
      · exact hW3 s
    have hadj : ∀ o, (S o ∩ U₀).Nonempty := by
      rintro (_ | s)
      · exact ⟨x₀, hx₀U, hx₀U⟩
      · exact hWU s
    have hconn : ∀ i j, Relation.ReflTransGen (fun a b => (S a ∩ S b).Nonempty) i j := by
      intro i j
      have h1 : Relation.ReflTransGen (fun a b => (S a ∩ S b).Nonempty) i none :=
        Relation.ReflTransGen.single (hadj i)
      have h2 : Relation.ReflTransGen (fun a b => (S a ∩ S b).Nonempty) none j :=
        Relation.ReflTransGen.single (by rw [Set.inter_comm]; exact hadj j)
      exact h1.trans h2
    haveI : Nonempty (Fin n) := ⟨x₀⟩
    rw [← GL83.iSup_altOn_eq_alternatingGroup hS3 hcover hconn]
    refine iSup_le fun o => ?_
    rcases o with _ | s
    · exact hU₀Γ
    · exact hWΓ s
  ·
    push Not at hA
    have hF₀1 : F₀.card = 1 := by
      obtain ⟨i, hi⟩ : ∃ i, β₁ i ≠ i := by
        by_contra h
        push Not at h
        exact hβ₁1 (Perm.ext h)
      have hiF : i ∉ F₀ := fun h => hi ((Finset.mem_filter.1 h).2 β₁ hβ₁)
      obtain ⟨β, hβ, hβ1, hβi⟩ := hreg i
      have := hbig β hβ i hβi hiF
      have := hA β hβ hβ1
      omega
    have hsF : ∀ s, s ≠ x₀ → s ∉ F₀ := fun s hs h =>
      hs (Finset.card_le_one.1 (by omega) s h x₀ hx₀)
    have hW : ∀ s : Fin n, s ≠ x₀ → ∃ t : Fin n, t ≠ x₀ ∧ t ≠ s ∧ swap x₀ t * swap x₀ s ∈ Γ := by
      intro s hs
      obtain ⟨β, hβ, hβ1, hβs⟩ := hreg s
      have h4 : β.supportᶜ.card = 4 := by
        have := hbig β hβ s hβs (hsF s hs)
        have := hA β hβ hβ1
        omega
      obtain ⟨a, b, ha, hb, hab, hxa, hxb, hsa, hsb, hall⟩ :=
        exists_two_of_card_four h4 ((hmem β x₀).2 (hx₀' β hβ)) ((hmem β s).2 hβs) (Ne.symm hs)
      obtain ⟨t, ht⟩ : ∃ t, t ∉ β.supportᶜ := by
        by_contra h
        push Not at h
        have : β.supportᶜ = Finset.univ := Finset.eq_univ_of_forall h
        rw [this, Finset.card_univ, Fintype.card_fin] at h4
        omega
      have htβ : β t ≠ t := fun e => ht ((hmem β t).2 e)
      have htx : t ≠ x₀ := fun e => htβ (e ▸ hx₀' β hβ)
      obtain ⟨β', hβ', hβ'1, hβ't⟩ := hreg t
      have h4' : β'.supportᶜ.card = 4 := by
        have := hbig β' hβ' t hβ't (hsF t htx)
        have := hA β' hβ' hβ'1
        omega
      obtain ⟨c, d, hc, hd, hcd, hxc, hxd, htc, htd, hall'⟩ :=
        exists_two_of_card_four h4' ((hmem β' x₀).2 (hx₀' β' hβ')) ((hmem β' t).2 hβ't) (Ne.symm htx)
      have hdisj : ∀ y, β y = y → β' y = y → y = x₀ := by
        intro y hy hy'
        by_contra hyx
        have hfix := fix_of_comm hpodd (hcomm β hβ β' hβ') (hT.2 β' hβ') h4 (Ne.symm hyx)
          (hx₀' β hβ) hy (hx₀' β' hβ') hy'
        exact htβ (by
          have hsub : β.supportᶜ ⊆ β'.supportᶜ := fun w hw => (hmem β' w).2 (hfix w ((hmem β w).1 hw))
          have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
          have : t ∈ β.supportᶜ := heq ▸ (hmem β' t).2 hβ't
          exact absurd this ht)
      have hfβ : ∀ z ∈ β.supportᶜ, β z = z := fun z hz => (hmem β z).1 hz
      have hfβ' : ∀ z ∈ β'.supportᶜ, β' z = z := fun z hz => (hmem β' z).1 hz
      have hne : ∀ u ∈ β.supportᶜ, ∀ w ∈ β'.supportᶜ, u ≠ x₀ → u ≠ w := fun u hu w hw hux e =>
        hux (hdisj u (hfβ u hu) (e ▸ hfβ' w hw))
      have h1 : swap x₀ s * swap a b ∈ Γ := hkl β hβ hβ1 h4 (Claims126.swap_mul_swap_mem_kleinOn h4
        (by simp [Ne.symm hs, hxa, hxb, hsa, hsb, hab]) ((hmem β x₀).2 (hx₀' β hβ))
        ((hmem β s).2 hβs) ha hb)
      have h2 : swap x₀ t * swap c d ∈ Γ := hkl β' hβ' hβ'1 h4' (Claims126.swap_mul_swap_mem_kleinOn h4'
        (by simp [Ne.symm htx, hxc, hxd, htc, htd, hcd]) ((hmem β' x₀).2 (hx₀' β' hβ'))
        ((hmem β' t).2 hβ't) hc hd)
      have hsβ : s ∈ β.supportᶜ := (hmem β s).2 hβs
      have htβ' : t ∈ β'.supportᶜ := (hmem β' t).2 hβ't
      have hax : a ≠ x₀ := Ne.symm hxa
      have hbx : b ≠ x₀ := Ne.symm hxb
      have h3 := Γ.pow_mem (Γ.mul_mem h1 h2) 2
      rw [InputsL34.sq_swaps (Ne.symm hs) hxa hxb (Ne.symm htx) hxc hxd hsa hsb
        (hne s hsβ t htβ' hs) (hne s hsβ c hc hs) (hne s hsβ d hd hs) hab
        (hne a ha t htβ' hax) (hne a ha c hc hax) (hne a ha d hd hax)
        (hne b hb t htβ' hbx) (hne b hb c hc hbx) (hne b hb d hd hbx) htc htd hcd] at h3
      exact ⟨t, htx, Ne.symm (hne s hsβ t htβ' hs), h3⟩
    obtain ⟨s₁, hs₁⟩ : ∃ s₁ : Fin n, s₁ ≠ x₀ := by
      by_contra h
      push Not at h
      have : Fintype.card (Fin n) ≤ 1 := Fintype.card_le_one_iff.2 fun a b => (h a).trans (h b).symm
      rw [Fintype.card_fin] at this
      omega
    have hW' : ∀ s : Fin n, ∃ W : Set (Fin n), s ∈ W ∧ x₀ ∈ W ∧ 3 ≤ W.ncard ∧ GL83.altOn W ≤ Γ := by
      have key : ∀ s : Fin n, s ≠ x₀ →
          ∃ W : Set (Fin n), s ∈ W ∧ x₀ ∈ W ∧ 3 ≤ W.ncard ∧ GL83.altOn W ≤ Γ := by
        intro s hs
        obtain ⟨t, htx, hts, hΓ⟩ := hW s hs
        refine ⟨{x₀, s, t}, by simp, by simp, ?_, altOn_three_le (Ne.symm hs) (Ne.symm htx)
          (Ne.symm hts) hΓ⟩
        rw [Set.ncard_eq_three.2 ⟨x₀, s, t, Ne.symm hs, Ne.symm htx, Ne.symm hts, rfl⟩]
      intro s
      by_cases hs : s = x₀
      · obtain ⟨W, -, hx, h3, hΓ⟩ := key s₁ hs₁
        exact ⟨W, hs ▸ hx, hx, h3, hΓ⟩
      · exact key s hs
    choose W hWs hWx hW3 hWΓ using hW'
    have hcover : (⋃ s, W s) = Set.univ :=
      Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, hWs x⟩
    have hconn : ∀ i j, Relation.ReflTransGen (fun a b => (W a ∩ W b).Nonempty) i j := fun i j =>
      Relation.ReflTransGen.single ⟨x₀, hWx i, hWx j⟩
    haveI : Nonempty (Fin n) := ⟨x₀⟩
    rw [← GL83.iSup_altOn_eq_alternatingGroup hW3 hcover hconn]
    exact iSup_le hWΓ

theorem exists_fix_of_card_le {p : ℕ} [hp : Fact p.Prime] (hpn : ¬ p ∣ n) {T : Subgroup (Perm (Fin n))}
    (hT : IsElemAbelian p T) (hTn : n ≤ Nat.card T) (h2 : 2 ≤ n) : ∀ i, ∃ β ∈ T, β ≠ 1 ∧ β i = i := by
  classical
  have hTp : IsPGroup p T := fun g => ⟨1, Subtype.ext (by simpa using hT.2 g g.2)⟩
  have hF₀mod := AltFacts3.card_fixedPoints_modEq hTp T.subtype
  obtain ⟨⟨x₀, hx₀⟩⟩ : Nonempty {i : Fin n // ∀ q : ↥T, T.subtype q i = i} := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Nat.card_of_isEmpty] at hF₀mod
    exact hpn (Nat.modEq_zero_iff_dvd.1 hF₀mod.symm)
  have hx₀' : ∀ β ∈ T, β x₀ = x₀ := fun β hβ => hx₀ ⟨β, hβ⟩
  obtain ⟨β₁, hβ₁, hβ₁1⟩ : ∃ β ∈ T, β ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : T = ⊥ := (Subgroup.eq_bot_iff_forall T).2 hcon
    rw [hbot, Subgroup.card_bot] at hTn
    omega
  intro i
  by_contra hcon
  push Not at hcon
  have hix : i ≠ x₀ := fun h => hcon β₁ hβ₁ hβ₁1 (h ▸ hx₀' β₁ hβ₁)
  let φ : ↥T → Fin n := fun β => (β : Perm (Fin n)) i
  have hφ : Function.Injective φ := by
    intro β γ h
    have h1 : (β : Perm (Fin n)) i = (γ : Perm (Fin n)) i := h
    by_contra hne
    have hne' : (γ : Perm (Fin n))⁻¹ * β ≠ 1 := fun e =>
      hne (Subtype.ext (inv_mul_eq_one.1 e).symm)
    exact hcon _ (T.mul_mem (T.inv_mem γ.2) β.2) hne' (by
      rw [Perm.mul_apply, h1]
      exact Perm.inv_eq_iff_eq.2 rfl)
  have hx₀φ : x₀ ∉ Set.range φ := by
    rintro ⟨β, hβ⟩
    apply hix
    have h1 : (β : Perm (Fin n)) i = x₀ := hβ
    have h2 : (β : Perm (Fin n)) x₀ = x₀ := hx₀' β β.2
    exact (β : Perm (Fin n)).injective (h1.trans h2.symm)
  have hlt := Fintype.card_lt_of_injective_of_notMem φ hφ hx₀φ
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card] at hlt
  omega

theorem alt_le_of_fix {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hpn : ¬ p ∣ n) (h5 : 5 ≤ n)
    {T Γ : Subgroup (Perm (Fin n))} (hT : IsElemAbelian p T) (hTn : n ≤ Nat.card T)
    (halt : ∀ β ∈ T, β ≠ 1 → 5 ≤ β.supportᶜ.card → Claims126.altOn β.supportᶜ ≤ Γ)
    (hkl : ∀ β ∈ T, β ≠ 1 → β.supportᶜ.card = 4 → Claims126.kleinOn β.supportᶜ ≤ Γ) :
    alternatingGroup (Fin n) ≤ Γ :=
  alt_le_of_fix' hp2 hpn h5 hT (exists_fix_of_card_le hpn hT hTn (by omega)) halt hkl

theorem regular_of_maximal {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hpn : ¬ p ∣ n)
    {T : Subgroup (Perm (Fin n))} (hT : IsElemAbelian p T)
    (hmax : ∀ σ ∈ alternatingGroup (Fin n), σ ^ p = 1 → (∀ t ∈ T, σ * t = t * σ) → σ ∈ T)
    {i : Fin n} (hi : ∀ t ∈ T, t ≠ 1 → t i ≠ i) (hTne : ∃ t ∈ T, t ≠ 1) :
    ∃ δ, 1 ≤ δ ∧ δ < p ∧ n = Nat.card T + δ ∧ ∀ t ∈ T, t ≠ 1 → t.support.card = Nat.card T := by
  classical
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  have hTp : IsPGroup p T := fun g => ⟨1, Subtype.ext (by simpa using hT.2 g g.2)⟩
  have hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hT.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have heven : ∀ σ : Perm (Fin n), σ ^ p = 1 → σ ∈ alternatingGroup (Fin n) := fun σ hσ =>
    mem_alt_of_pow hpodd hσ
  set F : Finset (Fin n) := Finset.univ.filter (fun j => ∀ t ∈ T, t j = j) with hF
  have hFmem : ∀ j, j ∈ F ↔ ∀ t ∈ T, t j = j := fun j => by simp [hF]
  obtain ⟨t₀, ht₀, ht₀1⟩ := hTne
  have hiF : i ∉ F := fun h => hi t₀ ht₀ ht₀1 ((hFmem i).1 h t₀ ht₀)
  have hfree : ∀ t ∈ T, t ≠ 1 → ∀ j, (∃ u ∈ T, u i = j) → t j ≠ j := by
    rintro t ht ht1 _ ⟨u, hu, rfl⟩ h
    apply hi t ht ht1
    apply u.injective
    rw [← Perm.mul_apply, hcomm u hu t ht, Perm.mul_apply]
    exact h
  have hFp : F.card < p := by
    by_contra hge
    push Not at hge
    have h2 : 2 ≤ F.card := by have := hp.out.two_le; omega
    have hdvd : p ∣ Nat.card ↥(Claims126.altOn F) := by
      rw [Claims126.card_altOn h2]
      exact Claims126.dvd_factorial_div_two ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2)
        hp.out.one_lt.le hge h2
    obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Claims126.altOn F)) p hdvd
    obtain ⟨hσA, hσs⟩ := Claims126.mem_altOn.1 σ.2
    have hσp : (σ : Perm (Fin n)) ^ p = 1 := by
      have h := pow_orderOf_eq_one σ
      rw [hσ] at h
      simpa using congrArg Subtype.val h
    have hσ1 : (σ : Perm (Fin n)) ≠ 1 := fun h =>
      hp.out.one_lt.ne' (by rw [← hσ, show σ = 1 from Subtype.ext h, orderOf_one])
    have hσT : (σ : Perm (Fin n)) ∈ T := hmax _ hσA hσp fun t ht => by
      have hd : Perm.Disjoint (σ : Perm (Fin n)) t := by
        intro x
        by_cases hx : x ∈ F
        · exact Or.inr ((hFmem x).1 hx t ht)
        · left
          by_contra hσx
          exact hx (hσs (Perm.mem_support.2 hσx))
      exact hd.commute.eq
    apply hi _ hσT hσ1
    by_contra hσi
    exact hiF (hσs (Perm.mem_support.2 hσi))
  have hFq : ∀ j, j ∉ F → ∃ u ∈ T, u i = j := by
    intro j hjF
    by_contra hjq
    obtain ⟨t, ht, htj⟩ : ∃ t ∈ T, t j ≠ j := by
      by_contra h
      push Not at h
      exact hjF ((hFmem j).2 h)
    set r : Fin n → Prop := fun x => ∃ u ∈ T, u j = x with hr
    have hrt : ∀ x, r (t x) ↔ r x := by
      intro x
      constructor
      · rintro ⟨u, hu, hux⟩
        refine ⟨t⁻¹ * u, T.mul_mem (T.inv_mem ht) hu, ?_⟩
        rw [Perm.mul_apply, hux]
        exact Perm.inv_eq_iff_eq.2 rfl
      · rintro ⟨u, hu, rfl⟩
        exact ⟨t * u, T.mul_mem ht hu, rfl⟩
    set σ : Perm (Fin n) := Perm.ofSubtype (t.subtypePerm hrt : Perm (Subtype r)) with hσ
    have hσr : ∀ x, r x → σ x = t x := fun x hx => by
      rw [hσ, Perm.ofSubtype_apply_of_mem _ hx]
      rfl
    have hσnr : ∀ x, ¬ r x → σ x = x := fun x hx => Perm.ofSubtype_apply_of_not_mem _ hx
    have hσp : σ ^ p = 1 := by
      ext x
      by_cases hx : r x
      · rw [hσ, ← map_pow, Perm.ofSubtype_apply_of_mem _ hx, Equiv.Perm.subtypePerm_pow]
        simp [hT.2 t ht]
      · rw [hσ, ← map_pow, Perm.ofSubtype_apply_of_not_mem _ hx]
        rfl
    have hσc : ∀ u ∈ T, σ * u = u * σ := by
      intro u hu
      ext x
      simp only [Perm.mul_apply]
      by_cases hx : r x
      · have hux : r (u x) := by
          obtain ⟨v, hv, rfl⟩ := hx
          exact ⟨u * v, T.mul_mem hu hv, rfl⟩
        rw [hσr _ hux, hσr _ hx, ← Perm.mul_apply, ← Perm.mul_apply, hcomm t ht u hu]
      · have hux : ¬ r (u x) := by
          rintro ⟨v, hv, hvx⟩
          refine hx ⟨u⁻¹ * v, T.mul_mem (T.inv_mem hu) hv, ?_⟩
          rw [Perm.mul_apply, hvx]
          exact Perm.inv_eq_iff_eq.2 rfl
        rw [hσnr _ hux, hσnr _ hx]
    have hσT := hmax σ (heven σ hσp) hσp hσc
    have hσ1 : σ ≠ 1 := fun h => htj (by rw [← hσr j ⟨1, T.one_mem, rfl⟩, h]; rfl)
    apply hi σ hσT hσ1
    apply hσnr
    rintro ⟨u, hu, hui⟩
    exact hjq ⟨u⁻¹, T.inv_mem hu, Perm.inv_eq_iff_eq.2 hui.symm⟩
  set O : Finset (Fin n) := Finset.univ.filter (fun j => ∃ u ∈ T, u i = j) with hO
  have hOmem : ∀ j, j ∈ O ↔ ∃ u ∈ T, u i = j := fun j => by simp [hO]
  have hOcard : O.card = Nat.card T := by
    have hbij : Function.Bijective
        (fun u : ↥T => (⟨(u : Perm (Fin n)) i, (hOmem _).2 ⟨u, u.2, rfl⟩⟩ : ↥O)) := by
      constructor
      · intro u v h
        have h1 : (u : Perm (Fin n)) i = (v : Perm (Fin n)) i := congrArg Subtype.val h
        by_contra hne
        have hne' : (v : Perm (Fin n))⁻¹ * u ≠ 1 := fun e =>
          hne (Subtype.ext (inv_mul_eq_one.1 e).symm)
        exact hi _ (T.mul_mem (T.inv_mem v.2) u.2) hne' (by
          rw [Perm.mul_apply, h1]
          exact Perm.inv_eq_iff_eq.2 rfl)
      · rintro ⟨j, hj⟩
        obtain ⟨u, hu, rfl⟩ := (hOmem j).1 hj
        exact ⟨⟨u, hu⟩, rfl⟩
    rw [← Fintype.card_coe O, ← Nat.card_eq_fintype_card]
    exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
  have hn : n = O.card + F.card := by
    have hdisj : Disjoint O F := Finset.disjoint_left.2 fun j hjO hjF =>
      hfree t₀ ht₀ ht₀1 j ((hOmem j).1 hjO) ((hFmem j).1 hjF t₀ ht₀)
    have hcov : O ∪ F = Finset.univ := Finset.eq_univ_of_forall fun j => by
      by_cases hjF : j ∈ F
      · exact Finset.mem_union_right _ hjF
      · exact Finset.mem_union_left _ ((hOmem j).2 (hFq j hjF))
    have := Finset.card_union_of_disjoint hdisj
    rw [hcov, Finset.card_univ, Fintype.card_fin] at this
    exact this
  have hF1 : 1 ≤ F.card := by
    have h := AltFacts3.card_fixedPoints_modEq hTp T.subtype
    have e : Nat.card {i : Fin n // ∀ q : ↥T, T.subtype q i = i} = F.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hF]
      congr 1
      ext j
      simp
    rw [e] at h
    by_contra h0
    have h00 : F.card = 0 := by omega
    rw [h00] at h
    exact hpn (Nat.modEq_zero_iff_dvd.1 h.symm)
  refine ⟨F.card, hF1, hFp, by omega, fun t ht ht1 => ?_⟩
  rw [← hOcard]
  congr 1
  ext j
  rw [Perm.mem_support, hOmem]
  constructor
  · intro htj
    by_contra hjq
    exact htj ((hFmem j).1 (by by_contra hjF; exact hjq (hFq j hjF)) t ht)
  · exact hfree t ht ht1 j

end Gen

section Rep

variable {Y : Type} [Group Y] {n : ℕ}

structure IsAltRep (ρ : Y →* Perm (Fin n)) : Prop where
  mem : ∀ y, ρ y ∈ alternatingGroup (Fin n)
  surj : ∀ σ ∈ alternatingGroup (Fin n), ∃ y, ρ y = σ
  ker : ∀ y, ρ y = 1 ↔ y ∈ Subgroup.center Y

theorem isAltRep_of_equiv (f : Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin n)) :
    IsAltRep ((alternatingGroup (Fin n)).subtype.comp
      (f.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y)))) where
  mem y := (f _).2
  surj σ hσ := by
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (f.symm ⟨σ, hσ⟩)
    refine ⟨y, ?_⟩
    show ((f (QuotientGroup.mk y) : alternatingGroup (Fin n)) : Perm (Fin n)) = σ
    rw [hy, MulEquiv.apply_symm_apply]
  ker y := by
    show ((f (QuotientGroup.mk y) : alternatingGroup (Fin n)) : Perm (Fin n)) = 1 ↔ _
    constructor
    · intro h
      have h1 : f (QuotientGroup.mk y) = 1 := Subtype.ext h
      rw [MulEquiv.map_eq_one_iff] at h1
      exact (QuotientGroup.eq_one_iff y).1 h1
    · intro h
      have h1 : (QuotientGroup.mk y : Y ⧸ Subgroup.center Y) = 1 := (QuotientGroup.eq_one_iff y).2 h
      rw [h1, map_one]
      rfl

variable {ρ : Y →* Perm (Fin n)}

theorem inv_mul_mem_center (hρ : IsAltRep ρ) {α : MulAut Y} {τ : Perm (Fin n)}
    (hτ : ∀ y, ρ (α y) = τ * ρ y * τ⁻¹) {y : Y} (hy : ρ y * τ = τ * ρ y) :
    y⁻¹ * α y ∈ Subgroup.center Y := by
  rw [← hρ.ker, map_mul, map_inv, hτ, ← hy]
  group

theorem comm_of_mem_fixSub {α : MulAut Y} {τ : Perm (Fin n)} (hτ : ∀ y, ρ (α y) = τ * ρ y * τ⁻¹)
    {c : Y} (hc : c ∈ fixSub α) : ρ c * τ = τ * ρ c := by
  have h := hτ c
  rw [(mem_fixSub.1 hc : α c = c)] at h
  calc ρ c * τ = (τ * ρ c * τ⁻¹) * τ := by rw [← h]
    _ = τ * ρ c := by group

theorem top_le_of_alt_le_map (hρ : IsAltRep ρ) (hperf : commutator Y = ⊤) {H : Subgroup Y}
    (hgen : alternatingGroup (Fin n) ≤ H.map ρ) : (⊤ : Subgroup Y) ≤ H := by
  have hdec : ∀ y : Y, ∃ h ∈ H, ∃ z ∈ Subgroup.center Y, y = h * z := by
    intro y
    obtain ⟨h, hh, hhy⟩ := hgen (hρ.mem y)
    exact ⟨h, hh, h⁻¹ * y, (hρ.ker _).1 (by rw [map_mul, map_inv, hhy, inv_mul_cancel]), by group⟩
  rw [← hperf, commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨h, hh, z, hz, rfl⟩ := hdec x
  obtain ⟨h', hh', w, hw, rfl⟩ := hdec y
  rw [commutatorElement_def, commutator_mul_central hz hw]
  exact H.mul_mem (H.mul_mem (H.mul_mem hh hh') (H.inv_mem hh)) (H.inv_mem hh')

theorem isQuasisimple_of_surj_central {N S : Type*} [Group N] [Group S] (hperf : commutator N = ⊤)
    (f : N →* S) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center N)
    (hS : IsSimpleGroup S) (hnc : ∃ x y : S, x * y ≠ y * x) : CFSG.Open.IsQuasisimple N := by
  have hZS : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      have hx : x ∈ Subgroup.center S := h ▸ Subgroup.mem_top x
      exact hxy ((Subgroup.mem_center_iff.1 hx y).symm)
  have hZ : Subgroup.center N = f.ker := by
    refine le_antisymm (fun z hz => ?_) hker
    have hfz : f z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨m, rfl⟩ := hf s
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz m]
    rw [hZS, Subgroup.mem_bot] at hfz
    exact hfz
  exact ⟨hperf, ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)).isSimpleGroup_congr.2 hS⟩

end Rep

section Lift

variable {Y : Type} [Group Y] [Finite Y] {n p : ℕ} {ρ : Y →* Perm (Fin n)}

theorem altOn_le_map (hρ : IsAltRep ρ) {α : MulAut Y} {τ : Perm (Fin n)}
    (hτ : ∀ y, ρ (α y) = τ * ρ y * τ⁻¹) (h5 : 5 ≤ τ.supportᶜ.card) :
    Claims126.altOn τ.supportᶜ ≤
      (GLAPPrimeCoreOf p (fixSub α) ⊔ GLAPLayer p (fixSub α)).map ρ := by
  classical
  set A₀ := Claims126.altOn τ.supportᶜ with hA₀
  set C : Subgroup Y := fixSub α with hC
  have hA₀s : IsSimpleGroup ↥A₀ := Claims126.isSimpleGroup_altOn h5
  have hA₀nc := Claims126.altOn_noncomm h5
  have hA₀q : CFSG.Open.IsQuasisimple ↥A₀ := Claims126.isQuasisimple_of_simple hA₀s hA₀nc
  have hA₀c : ∀ g ∈ A₀, g * τ = τ * g := fun g hg =>
    (Claims126.mem_cA.1 (Claims126.altOn_le_cA τ hg)).2
  have hA₀alt : A₀ ≤ alternatingGroup (Fin n) := fun g hg => (Claims126.mem_altOn.1 hg).1
  set P : Subgroup Y := A₀.comap ρ with hP
  have hPz : ∀ x ∈ P, ∃ z ∈ Subgroup.center Y, α x = x * z := fun x hx =>
    ⟨x⁻¹ * α x, inv_mul_mem_center hρ hτ (hA₀c _ hx), by group⟩
  set N : Subgroup Y := ⁅P, P⁆ with hN
  have hNC : N ≤ C := by
    rw [hN, Subgroup.commutator_le]
    intro x hx y hy
    show α ⁅x, y⁆ = ⁅x, y⁆
    obtain ⟨z, hz, hzx⟩ := hPz x hx
    obtain ⟨w, hw, hwy⟩ := hPz y hy
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hzx, hwy]
    exact commutator_mul_central hz hw
  have hPmap : P.map ρ = A₀ := by
    rw [hP, Subgroup.map_comap_eq]
    refine inf_eq_right.2 (hA₀alt.trans fun σ hσ => ?_)
    obtain ⟨y, hy⟩ := hρ.surj σ hσ
    exact ⟨y, hy⟩
  have hA₀perf : ⁅A₀, A₀⁆ = A₀ := Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hA₀q.1)
  have hNmap : N.map ρ = A₀ := by rw [hN, Subgroup.map_commutator, hPmap, hA₀perf]
  have hPconj : ∀ c ∈ C, ∀ x ∈ P, c * x * c⁻¹ ∈ P := by
    intro c hc x hx
    have hcτ := comm_of_mem_fixSub hτ hc
    have h1 := (Claims126.altOn_normal_cA τ).conj_mem ⟨ρ x, Claims126.altOn_le_cA τ hx⟩
      (Subgroup.mem_subgroupOf.2 hx) ⟨ρ c, Claims126.mem_cA.2 ⟨hρ.mem c, hcτ⟩⟩
    rw [Subgroup.mem_subgroupOf] at h1
    show ρ (c * x * c⁻¹) ∈ A₀
    simpa [map_mul, map_inv] using h1
  have hPc : ∀ c ∈ C, P.map (MulAut.conj c).toMonoidHom = P := by
    intro c hc
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hPconj c hc y hy
    · intro y hy
      refine ⟨c⁻¹ * y * c⁻¹⁻¹, hPconj c⁻¹ (C.inv_mem hc) y hy, ?_⟩
      simp [mul_assoc]
  have hNnorm : (N.subgroupOf C).Normal := by
    refine ⟨fun x hx c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have h1 : N.map (MulAut.conj (c : Y)).toMonoidHom = N := by
      rw [hN, Subgroup.map_commutator, hPc c c.2]
    have h2 : (MulAut.conj (c : Y)).toMonoidHom (x : Y) ∈ N.map (MulAut.conj (c : Y)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [h1] at h2
    simpa using h2
  have hlift : ∀ x ∈ P, ∃ x' ∈ N, ∃ z ∈ Subgroup.center Y, x = x' * z := by
    intro x hx
    have : ρ x ∈ N.map ρ := by rw [hNmap]; exact hx
    obtain ⟨x', hx', hxx⟩ := this
    exact ⟨x', hx', x'⁻¹ * x, (hρ.ker _).1 (by rw [map_mul, map_inv, hxx, inv_mul_cancel]),
      by group⟩
  have hNperf : ⁅N, N⁆ = N := by
    refine le_antisymm (commutator_le_of_le' le_rfl le_rfl) ?_
    show ⁅P, P⁆ ≤ ⁅N, N⁆
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨x', hx', z, hz, rfl⟩ := hlift x hx
    obtain ⟨y', hy', w, hw, rfl⟩ := hlift y hy
    rw [commutatorElement_def, commutator_mul_central hz hw, ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator hx' hy'
  have hNq : CFSG.Open.IsQuasisimple ↥N := by
    let ρN : ↥N →* ↥A₀ := (ρ.comp N.subtype).codRestrict A₀ (fun x => by
      rw [← hNmap]
      exact ⟨x, x.2, rfl⟩)
    have hρNs : Function.Surjective ρN := by
      rintro ⟨g, hg⟩
      rw [← hNmap] at hg
      obtain ⟨x, hx, rfl⟩ := hg
      exact ⟨⟨x, hx⟩, rfl⟩
    have hker : ρN.ker ≤ Subgroup.center ↥N := by
      intro x hx
      have h1 : ρ (x : Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      have h2 := (hρ.ker _).1 h1
      rw [Subgroup.mem_center_iff] at h2 ⊢
      intro g
      exact Subtype.ext (h2 g)
    exact isQuasisimple_of_surj_central (Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hNperf))
      ρN hρNs hker hA₀s hA₀nc
  have hNle : N ≤ GLAPPrimeCoreOf p C ⊔ GLAPLayer p C := by
    by_cases hbot : barX p C N = ⊥
    · intro x hx
      have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hNC hx⟩ ∈ barX p C N :=
        ⟨⟨x, hNC hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact Subgroup.mem_sup_left ⟨_, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
    · haveI : Nontrivial ↥(barX p C N) := (Subgroup.nontrivial_iff_ne_bot _).2 hbot
      have hq : CFSG.Open.IsQuasisimple ↥(barX p C N) :=
        CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.isQuasisimple_of_surjective_of_nontrivial
          hNq (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barXHom p hNC)
          (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barXHom_surjective p hNC)
      have hcomp : IsComponentOf (barX p C N) ⊤ := by
        refine ⟨le_top, ?_, hq⟩
        haveI : (barX p C N).Normal := hNnorm.map _ (QuotientGroup.mk'_surjective _)
        exact IsSubnormal.step le_top (Subgroup.Normal.subgroupOf inferInstance _) (IsSubnormal.refl _)
      obtain ⟨L, hL, hLN⟩ := exists_glaPComponent_barX_eq (p := p) C hcomp
      intro x hx
      obtain ⟨l, hl, hlx⟩ := exists_of_barX_le (le_of_eq hLN.symm) hx (hNC hx)
      have hLle : L ≤ GLAPLayer p C := le_sSup hL
      have hlL : l ∈ GLAPLayer p C := hLle hl
      have e : x = l * (l⁻¹ * x) := by group
      rw [e, sup_comm]
      exact Subgroup.mul_mem_sup hlL hlx
  rw [← hNmap]
  exact Subgroup.map_mono hNle

theorem kleinOn_le_map (hp : p.Prime) (hp2 : p ≠ 2) (hρ : IsAltRep ρ)
    (hZ : IsPGroup p ↥(Subgroup.center Y)) {α : MulAut Y} {τ : Perm (Fin n)}
    (hτ : ∀ y, ρ (α y) = τ * ρ y * τ⁻¹) (h4 : τ.supportᶜ.card = 4) :
    Claims126.kleinOn τ.supportᶜ ≤ (GLAPPrimeCoreOf p (fixSub α)).map ρ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set V := Claims126.kleinOn τ.supportᶜ with hV
  set C : Subgroup Y := fixSub α with hC
  have hValt : ∀ v ∈ V, v ∈ Claims126.altOn τ.supportᶜ := fun v hv =>
    ((Claims126.mem_kleinOn h4).1 hv).1
  have hVc : ∀ v ∈ V, v * τ = τ * v := fun v hv =>
    (Claims126.mem_cA.1 (Claims126.altOn_le_cA τ (hValt v hv))).2
  have hVsq : ∀ v ∈ V, v * v = 1 := by
    intro v hv
    rcases ((Claims126.mem_kleinOn h4).1 hv).2 with h | h
    · rw [h, mul_one]
    · have h2 : orderOf v = 2 := by
        rw [← Equiv.Perm.lcm_cycleType, h]
        rfl
      rw [← sq, ← h2, pow_orderOf_eq_one]
  have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := by
    intro v hv w hw
    have h1 := hVsq _ (V.mul_mem hv hw)
    have h2 : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hVsq v hv)
    have h3 : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hVsq w hw)
    calc v * w = (v * w)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = w * v := by rw [mul_inv_rev, h2, h3]
  have hz2 : ∀ z ∈ Subgroup.center Y, z * z = 1 → z = 1 := by
    intro z hz hzz
    obtain ⟨k, hk⟩ := hZ ⟨z, hz⟩
    have h1 : z ^ (p ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h2 : z ^ 2 = 1 := by rw [sq]; exact hzz
    have hcop : Nat.Coprime 2 (p ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
    have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1)
    rw [Nat.Coprime.gcd_eq_one hcop] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  let S : Subgroup Y :=
    { carrier := {y | α y = y ∧ ρ y ∈ V ∧ y * y = 1}
      mul_mem' := by
        rintro y y' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
        have hc : y * y' = y' * y := by
          set z := y * y' * y⁻¹ * y'⁻¹ with hzdef
          have hz : z ∈ Subgroup.center Y := (hρ.ker z).1 (by
            rw [hzdef, map_mul, map_mul, map_mul, map_inv, map_inv, hVcomm _ h2 _ h2']
            group)
          have hzc := Subgroup.mem_center_iff.1 hz
          have hzz : z * z = 1 := by
            have e1 : y * y' * y⁻¹ = z * y' := by rw [hzdef]; group
            have e2 : (y * y' * y⁻¹) * (y * y' * y⁻¹) = 1 := by
              calc (y * y' * y⁻¹) * (y * y' * y⁻¹) = y * (y' * y') * y⁻¹ := by group
                _ = 1 := by rw [h3', mul_one, mul_inv_cancel]
            rw [e1] at e2
            calc z * z = z * z * (y' * y') := by rw [h3', mul_one]
              _ = z * (z * y') * y' := by group
              _ = z * (y' * z) * y' := by rw [hzc y']
              _ = z * y' * (z * y') := by group
              _ = 1 := e2
          have h0 := hz2 z hz hzz
          rw [hzdef] at h0
          calc y * y' = y * y' * y⁻¹ * y'⁻¹ * (y' * y) := by group
            _ = y' * y := by rw [h0, one_mul]
        refine ⟨by rw [map_mul, h1, h1'], by rw [map_mul]; exact V.mul_mem h2 h2', ?_⟩
        calc y * y' * (y * y') = y * (y' * y) * y' := by group
          _ = y * (y * y') * y' := by rw [hc]
          _ = (y * y) * (y' * y') := by group
          _ = 1 := by rw [h3, h3', one_mul]
      one_mem' := ⟨map_one α, by rw [map_one]; exact V.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro y ⟨h1, h2, h3⟩
        refine ⟨by rw [map_inv, h1], by rw [map_inv]; exact V.inv_mem h2, ?_⟩
        rw [← mul_inv_rev, h3, inv_one] }
  have hSmem : ∀ y, y ∈ S ↔ α y = y ∧ ρ y ∈ V ∧ y * y = 1 := fun y => Iff.rfl
  have hSC : S ≤ C := fun y hy => ((hSmem y).1 hy).1
  have hSn : (S.subgroupOf C).Normal := by
    refine ⟨fun x hx c => ?_⟩
    rw [Subgroup.mem_subgroupOf, hSmem] at hx ⊢
    obtain ⟨h1, h2, h3⟩ := hx
    have hc : α c = c := c.2
    have hcτ := comm_of_mem_fixSub hτ c.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨by rw [map_mul, map_mul, map_inv, hc, h1], ?_, ?_⟩
    · have := (Claims126.kleinOn_normal_cA τ h4).conj_mem
        ⟨ρ x, Claims126.altOn_le_cA τ (hValt _ h2)⟩ (Subgroup.mem_subgroupOf.2 h2)
        ⟨ρ c, Claims126.mem_cA.2 ⟨hρ.mem c, hcτ⟩⟩
      rw [Subgroup.mem_subgroupOf] at this
      simpa [map_mul, map_inv] using this
    · calc (c : Y) * x * (c : Y)⁻¹ * ((c : Y) * x * (c : Y)⁻¹) = c * (x * x) * (c : Y)⁻¹ := by group
        _ = 1 := by rw [h3, mul_one, mul_inv_cancel]
  have hS2 : IsPGroup 2 ↥S := fun g => ⟨1, Subtype.ext (by
    show (g : Y) ^ 2 ^ 1 = 1
    rw [pow_one, sq]
    exact ((hSmem _).1 g.2).2.2)⟩
  have hScop : Nat.Coprime p (Nat.card ↥S) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hSO : S ≤ GLAPPrimeCoreOf p C :=
    Prop95Parts.Input18.le_glaPPrimeCoreOf_of_coprime hp
      (IsSubnormal.step hSC hSn (IsSubnormal.refl C)) hScop
  intro v hv
  obtain ⟨x, hx⟩ := hρ.surj v (Claims126.mem_altOn.1 (hValt v hv)).1
  set m := Nat.card ↥(Subgroup.center Y) with hm
  have hmodd : Odd m := by
    obtain ⟨k, hk⟩ := hZ.exists_card_eq
    rw [hm, hk]
    exact (hp.odd_of_ne_two hp2).pow
  have hxx : x * x ∈ Subgroup.center Y := (hρ.ker _).1 (by rw [map_mul, hx, hVsq v hv])
  set y := x ^ m with hy
  have hyv : ρ y = v := by
    rw [hy, map_pow, hx]
    obtain ⟨k, hk⟩ := hmodd
    rw [hk, pow_succ, pow_mul, sq, hVsq v hv, one_pow, one_mul]
  have hyy : y * y = 1 := by
    have h1 : (x * x) ^ m = 1 := by
      have h0 : (⟨x * x, hxx⟩ : ↥(Subgroup.center Y)) ^ m = 1 := pow_card_eq_one'
      have h0' := congrArg Subtype.val h0
      rwa [SubgroupClass.coe_pow] at h0'
    rw [hy, ← pow_add, ← two_mul, pow_mul, sq]
    exact h1
  have hyα : α y = y := by
    have hyτ : ρ y * τ = τ * ρ y := by rw [hyv]; exact hVc v hv
    have hz := inv_mul_mem_center hρ hτ hyτ
    have hzc := Subgroup.mem_center_iff.1 hz
    have hαy : α y = y * (y⁻¹ * α y) := by group
    have hzz : (y⁻¹ * α y) * (y⁻¹ * α y) = 1 := by
      have h1 : α y * α y = 1 := by rw [← map_mul, hyy, map_one]
      calc (y⁻¹ * α y) * (y⁻¹ * α y) = y * y * ((y⁻¹ * α y) * (y⁻¹ * α y)) := by
            rw [hyy, one_mul]
        _ = y * (y * (y⁻¹ * α y)) * (y⁻¹ * α y) := by group
        _ = y * ((y⁻¹ * α y) * y) * (y⁻¹ * α y) := by rw [hzc y]
        _ = α y * α y := by group
        _ = 1 := h1
    rw [hαy, hz2 _ hz hzz, mul_one]
  exact ⟨y, hSO ((hSmem y).2 ⟨hyα, by rw [hyv]; exact hv, hyy⟩), hyv⟩

end Lift

section Comp

variable {Y : Type} [Group Y] [Finite Y] {n p : ℕ} {ρ : Y →* Perm (Fin n)}

theorem component_alt (hp : p.Prime) (hp2 : p ≠ 2) (hρ : IsAltRep ρ)
    (hZ : IsPGroup p ↥(Subgroup.center Y)) {α : MulAut Y} {τ : Perm (Fin n)}
    (hτ : ∀ y, ρ (α y) = τ * ρ y * τ⁻¹) (hτp : τ ^ p = 1) {J : Subgroup Y}
    (hJ : GLAPComponent p (fixSub α) J) :
    5 ≤ τ.supportᶜ.card ∧
      Nonempty (barOf p J ⧸ Subgroup.center (barOf p J) ≃* alternatingGroup (Fin τ.supportᶜ.card)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  set C : Subgroup Y := fixSub α with hC
  set D : Subgroup Y := (Claims126.cA τ).comap ρ with hD
  have hDmem : ∀ y, y ∈ D ↔ ρ y * τ = τ * ρ y := fun y => by
    rw [hD, Subgroup.mem_comap, Claims126.mem_cA]
    exact ⟨fun h => h.2, fun h => ⟨hρ.mem y, h⟩⟩
  have hCD : C ≤ D := fun c hc => (hDmem c).2 (comm_of_mem_fixSub hτ hc)
  have hCn : (C.subgroupOf D).Normal := by
    refine ⟨fun x hx d => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hx' : α x = x := hx
    obtain ⟨z, hz, hzd⟩ : ∃ z ∈ Subgroup.center Y, α d = d * z :=
      ⟨(d : Y)⁻¹ * α d, inv_mul_mem_center hρ hτ ((hDmem d).1 d.2), by group⟩
    have hzc := Subgroup.mem_center_iff.1 hz
    show α ((d : Y) * x * (d : Y)⁻¹) = (d : Y) * x * (d : Y)⁻¹
    rw [map_mul, map_mul, map_inv, hzd, hx']
    calc (d : Y) * z * x * ((d : Y) * z)⁻¹ = d * (z * x) * z⁻¹ * (d : Y)⁻¹ := by group
      _ = d * (x * z) * z⁻¹ * (d : Y)⁻¹ := by rw [← hzc x]
      _ = d * x * (d : Y)⁻¹ := by group
  have hJD : GLAPComponent p D J :=
    l119_glaPComponent_of_isSubnormal hp (IsSubnormal.step hCD hCn (IsSubnormal.refl D)) hJ
  set U : Subgroup Y := (Claims126.uSub τ).comap ρ with hU
  have hUD : U ≤ D := fun u hu => (hDmem u).2 hu.1
  have hUp : IsPGroup p ↥U := by
    intro u
    have h1 : ρ ((u : Y) ^ p) = 1 := by rw [map_pow]; exact pow_p_of_mem_uSub hτp u.2
    obtain ⟨k, hk⟩ := hZ ⟨_, (hρ.ker _).1 h1⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have h2 := congrArg Subtype.val hk
    rw [SubgroupClass.coe_pow] at h2
    rw [SubgroupClass.coe_pow, pow_succ', pow_mul]
    exact h2
  have hUn : (U.subgroupOf D).Normal := by
    refine ⟨fun x hx d => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    show ρ ((d : Y) * x * (d : Y)⁻¹) ∈ Claims126.uSub τ
    rw [map_mul, map_mul, map_inv]
    exact Claims126.conj_mem_uSub ((hDmem d).1 d.2) hx
  have hJU : ∀ j ∈ J, ∀ u ∈ U, j * u = u * j := by
    have hUbn : (barX p D U).Normal := hUn.map _ (QuotientGroup.mk'_surjective _)
    have hcomp := (CFSG.Adapters.isComponentOf_top_iff _).1 hJD.2.2.1
    rcases CFSG.GorensteinWalter.component_le_or_commutator_eq_bot_of_normal hcomp hUbn with
      hle | hbot
    · exfalso
      have hpU : IsPGroup p ↥(barX p D U) := by
        have h1 : IsPGroup p ↥(U.subgroupOf D) :=
          hUp.of_equiv (Subgroup.subgroupOfEquivOfLe hUD).symm
        exact h1.map _
      exact Claims126.not_isPGroup_of_isQuasisimple hp hJD.2.2.1.2.2 (hpU.to_le hle)
    · intro j hj u hu
      have hjD := hJD.1 hj
      have huD := hUD hu
      have hmem : ⁅QuotientGroup.mk' (GLAPPrimeCore p ↥D) ⟨j, hjD⟩,
          QuotientGroup.mk' (GLAPPrimeCore p ↥D) ⟨u, huD⟩⁆ ∈ ⁅barX p D J, barX p D U⁆ :=
        Subgroup.commutator_mem_commutator ⟨⟨j, hjD⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩
          ⟨⟨u, huD⟩, Subgroup.mem_subgroupOf.2 hu, rfl⟩
      have hbot' : ⁅barX p D J, barX p D U⁆ = ⊥ := hbot
      rw [hbot', Subgroup.mem_bot, ← map_commutatorElement] at hmem
      set c : ↥D := ⁅(⟨j, hjD⟩ : ↥D), ⟨u, huD⟩⁆ with hcdef
      have h1 : c ∈ GLAPPrimeCore p ↥D := (QuotientGroup.eq_one_iff _).1 hmem
      have hcY : (c : Y) = ⁅j, u⁆ := rfl
      have h3 : ⁅j, u⁆ ∈ U := by
        rw [commutatorElement_def]
        have := hUn.conj_mem ⟨u, huD⟩ (Subgroup.mem_subgroupOf.2 hu) ⟨j, hjD⟩
        rw [Subgroup.mem_subgroupOf] at this
        exact U.mul_mem this (U.inv_mem hu)
      obtain ⟨k, hk⟩ := hUp ⟨_, h3⟩
      have hk' : c ^ p ^ k = 1 := by
        apply Subtype.ext
        have h4 := congrArg Subtype.val hk
        rw [SubgroupClass.coe_pow] at h4 ⊢
        rw [hcY]
        exact h4
      have hd1 : orderOf c ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
      have hd2 : orderOf c ∣ Nat.card ↥(GLAPPrimeCore p ↥D) := Subgroup.orderOf_dvd_natCard _ h1
      have hcop : Nat.Coprime (p ^ k) (Nat.card ↥(GLAPPrimeCore p ↥D)) :=
        Nat.Coprime.pow_left k CFSG.pPrimeCore_coprime_card
      have h4 := Nat.dvd_gcd hd1 hd2
      rw [Nat.Coprime.gcd_eq_one hcop] at h4
      have hc1 : c = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
      have h5 : ⁅j, u⁆ = 1 := by rw [← hcY, hc1]; rfl
      exact commutatorElement_eq_one_iff_mul_comm.1 h5
  set R : Subgroup (Perm (Fin n)) := J.map ρ with hR
  have hRc : ∀ g ∈ R, ∀ w ∈ Claims126.uSub τ, g * w = w * g := by
    rintro _ ⟨j, hj, rfl⟩ w hw
    obtain ⟨u, rfl⟩ := hρ.surj w (uSub_le_alt hpodd hτp hw)
    rw [← map_mul, ← map_mul, hJU j hj u hw]
  have hRτ : ∀ g ∈ R, g * τ = τ * g := by
    rintro _ ⟨j, hj, rfl⟩
    exact (hDmem j).1 (hJD.1 hj)
  have he : ∀ g ∈ R, ∀ y, τ y ≠ y → ∃ k : ℕ, g y = (τ ^ k) y := fun g hg y hy =>
    Claims126.exists_pow_of_comm_uSub (hRτ g hg) (hRc g hg) hy
  have hJperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hRperf : ⁅R, R⁆ = R := by rw [hR, ← Subgroup.map_commutator, hJperf]
  have hRalt : R ≤ Claims126.altOn τ.supportᶜ := by
    rw [← hRperf, Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    refine Claims126.mem_altOn.2 ⟨?_, ?_⟩
    · obtain ⟨j₁, -, rfl⟩ := h₁
      obtain ⟨j₂, -, rfl⟩ := h₂
      rw [← map_commutatorElement]
      exact hρ.mem _
    · intro y hy
      rw [Finset.mem_compl, Perm.mem_support, not_not]
      by_contra hτy
      rw [Perm.mem_support] at hy
      exact hy (Claims126.commutator_apply_eq_of_pow (hRτ g₁ h₁) (hRτ g₂ h₂) (he g₁ h₁)
        (he g₂ h₂) hτy)
  have hRne : R ≠ ⊥ := by
    intro hR0
    have hJZ : J ≤ Subgroup.center Y := fun j hj => (hρ.ker j).1 (by
      have : ρ j ∈ R := ⟨j, hj, rfl⟩
      rw [hR0, Subgroup.mem_bot] at this
      exact this)
    have hJ0 : J = ⊥ := by
      rw [← hJperf, eq_bot_iff, Subgroup.commutator_le]
      intro x _ y hy
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_center_iff.1 (hJZ hy) x
    have h := (Subgroup.nontrivial_iff_ne_bot _).1
      (Claims126.nontrivial_of_isQuasisimple hJ.2.2.1.2.2)
    apply h
    rw [hJ0, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  have h5 : 5 ≤ τ.supportᶜ.card := by
    by_contra h
    exact hRne (Claims126.eq_bot_of_perfect_of_le_solvable hRperf hRalt
      (Claims126.isSolvable_altOn (by omega)))
  have hAD : Claims126.altOn τ.supportᶜ ≤ D.map ρ := by
    intro g hg
    obtain ⟨y, rfl⟩ := hρ.surj g (Claims126.mem_altOn.1 hg).1
    exact ⟨y, (hDmem y).2 (Claims126.mem_cA.1 (Claims126.altOn_le_cA τ hg)).2, rfl⟩
  have hReq : R = Claims126.altOn τ.supportᶜ := by
    have hsn : IsSubnormal R (Claims126.altOn τ.supportᶜ) :=
      isSubnormal_of_le_of_le (isSubnormal_map' ρ hJD.2.1) hRalt hAD
    rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsn
      (Claims126.isSimpleGroup_altOn h5) with h | h
    · exact absurd h hRne
    · exact h
  refine ⟨h5, ?_⟩
  set A₀ := Claims126.altOn τ.supportᶜ with hA₀
  haveI hA₀s : IsSimpleGroup ↥A₀ := Claims126.isSimpleGroup_altOn h5
  let ρJ : ↥J →* ↥A₀ := (ρ.comp J.subtype).codRestrict A₀ (fun j => by
    rw [← hReq]
    exact ⟨j, j.2, rfl⟩)
  have hρJs : Function.Surjective ρJ := by
    rintro ⟨g, hg⟩
    rw [← hReq] at hg
    obtain ⟨j, hj, rfl⟩ := hg
    exact ⟨⟨j, hj⟩, rfl⟩
  have hkerZ : ρJ.ker ≤ Subgroup.center ↥J := by
    intro x hx
    have h1 : ρ (x : Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have h2 := (hρ.ker _).1 h1
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro g
    exact Subtype.ext (h2 g)
  have hJq : commutator ↥J = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hJperf)
  have hOker : GLAPPrimeCore p ↥J ≤ ρJ.ker := by
    haveI hn : ((GLAPPrimeCore p ↥J).map ρJ).Normal := (GLAPPrimeCore.normal p ↥J).map ρJ hρJs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((GLAPPrimeCore p ↥J).map ρJ) with h | h
    · exact (Subgroup.map_eq_bot_iff _).1 h
    · exfalso
      have hall : ∀ j : ↥J, ∃ o ∈ GLAPPrimeCore p ↥J, ∃ z ∈ Subgroup.center ↥J, j = o * z := by
        intro j
        have : ρJ j ∈ (GLAPPrimeCore p ↥J).map ρJ := by rw [h]; exact Subgroup.mem_top _
        obtain ⟨o, ho, hoj⟩ := this
        exact ⟨o, ho, o⁻¹ * j, hkerZ (by rw [MonoidHom.mem_ker, map_mul, map_inv, hoj, inv_mul_cancel]),
          by group⟩
      have hle : commutator ↥J ≤ GLAPPrimeCore p ↥J := by
        rw [commutator_def, Subgroup.commutator_le]
        intro x _ y _
        obtain ⟨o, ho, z, hz, rfl⟩ := hall x
        obtain ⟨o', ho', w, hw, rfl⟩ := hall y
        rw [commutatorElement_def, commutator_mul_central hz hw]
        exact (GLAPPrimeCore p ↥J).mul_mem ((GLAPPrimeCore p ↥J).mul_mem
          ((GLAPPrimeCore p ↥J).mul_mem ho ho') ((GLAPPrimeCore p ↥J).inv_mem ho))
          ((GLAPPrimeCore p ↥J).inv_mem ho')
      rw [hJq] at hle
      have hq : CFSG.Open.IsQuasisimple (barOf p J) :=
        (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.isQuasisimple_barX_iff hp hJ.2.1).1
          hJ.2.2.1.2.2
      haveI := Claims126.nontrivial_of_isQuasisimple hq
      obtain ⟨u, hu⟩ := exists_ne (1 : barOf p J)
      apply hu
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
      exact (QuotientGroup.eq_one_iff x).2 (hle (Subgroup.mem_top x))
  have hZker : Subgroup.center ↥J = ρJ.ker := by
    refine le_antisymm (fun z hz => ?_) hkerZ
    have hfz : ρJ z ∈ Subgroup.center ↥A₀ := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨m, rfl⟩ := hρJs s
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz m]
    have hZA : Subgroup.center ↥A₀ = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥A₀) with h | h
      · exact h
      · exfalso
        obtain ⟨x, y, hxy⟩ := Claims126.altOn_noncomm h5
        have hx : x ∈ Subgroup.center ↥A₀ := h ▸ Subgroup.mem_top x
        exact hxy ((Subgroup.mem_center_iff.1 hx y).symm)
    rw [hZA, Subgroup.mem_bot] at hfz
    exact hfz
  obtain ⟨e1⟩ := Claims126.nonempty_quot_center_quot hJq (GLAPPrimeCore p ↥J) (hOker.trans hkerZ)
  exact ⟨e1.trans ((QuotientGroup.quotientMulEquivOfEq hZker).trans
    ((QuotientGroup.quotientKerEquivOfSurjective ρJ hρJs).trans (Claims126.altOnEquiv _)))⟩

end Comp

section Tau

theorem mem_range_conjNormal {n p : ℕ} (hp : Odd p) (h5 : 5 ≤ n)
    (φ : MulAut ↥(alternatingGroup (Fin n))) (hφ : φ ^ p = 1) :
    φ ∈ (MulAut.conjNormal (H := alternatingGroup (Fin n)) :
      Perm (Fin n) →* MulAut ↥(alternatingGroup (Fin n))).range := by
  by_cases hn6 : n = 6
  · subst hn6
    set H := (MulAut.conjNormal (H := alternatingGroup (Fin 6)) :
      Perm (Fin 6) →* MulAut ↥(alternatingGroup (Fin 6))).range with hH
    have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num)
    haveI := Input236gt.finite_mulAut (alternatingGroup (Fin 6))
    have hHcard : Nat.card H = 720 := by
      rw [hH, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_perm,
        Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have hle :=
      CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.automorphism_card_le
    have hidx := H.index_mul_card
    rw [hHcard] at hidx
    have hpos : 0 < Nat.card (MulAut ↥(alternatingGroup (Fin 6))) := Nat.card_pos
    have h12 : H.index = 1 ∨ H.index = 2 := by
      rcases Nat.lt_or_ge H.index 3 with h | h
      · omega
      · exfalso
        have : 3 * 720 ≤ H.index * 720 := Nat.mul_le_mul_right 720 h
        omega
    rcases h12 with h | h
    · rw [Subgroup.index_eq_one] at h
      rw [h]
      exact Subgroup.mem_top φ
    · obtain ⟨k, hk⟩ := hp
      have hφeq : φ = (φ ^ 2) ^ (k + 1) := by
        rw [← pow_mul, show 2 * (k + 1) = p + 1 by omega, pow_succ, hφ, one_mul]
      rw [hφeq]
      exact H.pow_mem (Subgroup.sq_mem_of_index_two h φ) _
  · exact (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n h5 hn6).2 φ

theorem exists_perm_hom {p n : ℕ} (hp : Odd p) (h5 : 5 ≤ n) {S : Type*} [Group S]
    (φ : S →* MulAut ↥(alternatingGroup (Fin n))) (hφ : ∀ s, φ s ^ p = 1) :
    ∃ τ : S →* Perm (Fin n), ∀ s, MulAut.conjNormal (τ s) = φ s := by
  set c : Perm (Fin n) →* MulAut ↥(alternatingGroup (Fin n)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin n)) with hc
  have hcinj : Function.Injective c :=
    CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega)
  set e := MonoidHom.ofInjective hcinj with he
  have hce : ∀ x : ↥c.range, c (e.symm x) = x := fun x => by
    rw [← MonoidHom.ofInjective_apply hcinj, ← he, MulEquiv.apply_symm_apply]
  exact ⟨e.symm.toMonoidHom.comp (φ.codRestrict c.range fun s => mem_range_conjNormal hp h5 _ (hφ s)),
    fun s => hce _⟩

theorem eq_one_of_comm_alt {n : ℕ} (h4 : 4 ≤ n) {σ : Perm (Fin n)}
    (h : ∀ g ∈ alternatingGroup (Fin n), σ * g = g * σ) : σ = 1 := by
  apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n h4
  rw [map_one]
  ext ⟨g, hg⟩
  simp [MulAut.conjNormal_apply, h g hg]

theorem exists_tau {p n : ℕ} (hp : Odd p) (h5 : 5 ≤ n) {Y : Type} [Group Y]
    (hperf : commutator Y = ⊤) (f : Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin n))
    {A : Subgroup (MulAut Y)} (hA : ∀ a ∈ A, a ^ p = 1) :
    ∃ τ : ↥A →* Perm (Fin n), Function.Injective τ ∧
      ∀ (a : ↥A) (y : Y), ((f (QuotientGroup.mk ((a : MulAut Y) y)) : alternatingGroup (Fin n)) :
        Perm (Fin n)) = τ a * (f (QuotientGroup.mk y) : Perm (Fin n)) * (τ a)⁻¹ := by
  set ψ : ↥A →* MulAut ↥(alternatingGroup (Fin n)) :=
    (MulAut.congr f).toMonoidHom.comp ((quotientCenterAut' Y).comp A.subtype) with hψ
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : quotientCenterAut' Y a = quotientCenterAut' Y b := (MulAut.congr f).injective hab
    exact Subtype.ext (quotientCenterAut'_injective hperf h1)
  obtain ⟨τ, hτ⟩ := exists_perm_hom hp h5 ψ fun a => by
    rw [← map_pow, show a ^ p = 1 from Subtype.ext (by simpa using hA a a.2), map_one]
  refine ⟨τ, fun a b hab => hψinj (by rw [← hτ a, ← hτ b, hab]), fun a y => ?_⟩
  have h2 := congrArg (fun φ : MulAut ↥(alternatingGroup (Fin n)) =>
    ((φ (f (QuotientGroup.mk y)) : ↥(alternatingGroup (Fin n))) : Perm (Fin n))) (hτ a)
  simp only [MulAut.conjNormal_apply] at h2
  have h3 : ψ a (f (QuotientGroup.mk y)) = f (QuotientGroup.mk ((a : MulAut Y) y)) := by
    show f (quotientCenterAut' Y a (f.symm (f (QuotientGroup.mk y)))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  rw [h3] at h2
  exact h2.symm

theorem exists_perm_action {X : Type*} [Group X] {p n : ℕ} (hp : Odd p) (h5 : 5 ≤ n) {K S : Subgroup X}
    (ψ : ↥K ≃* alternatingGroup (Fin n)) (hSN : S ≤ Subgroup.normalizer (K : Set X))
    (hSp : ∀ s ∈ S, s ^ p = 1) :
    ∃ τ : ↥S →* Perm (Fin n), ∀ (s : ↥S) (x : ↥K),
      ((ψ (K.normalizerMonoidHom ⟨s, hSN s.2⟩ x) : alternatingGroup (Fin n)) : Perm (Fin n)) =
        τ s * (ψ x : Perm (Fin n)) * (τ s)⁻¹ := by
  set φ : ↥S →* MulAut ↥(alternatingGroup (Fin n)) :=
    (MulAut.congr ψ).toMonoidHom.comp (K.normalizerMonoidHom.comp (Subgroup.inclusion hSN)) with hφ
  obtain ⟨τ, hτ⟩ := exists_perm_hom hp h5 φ fun s => by
    rw [← map_pow, show s ^ p = 1 from Subtype.ext (by simpa using hSp s s.2), map_one]
  refine ⟨τ, fun s x => ?_⟩
  have h1 := congrArg (fun φ' : MulAut ↥(alternatingGroup (Fin n)) =>
    ((φ' (ψ x) : ↥(alternatingGroup (Fin n))) : Perm (Fin n))) (hτ s)
  simp only [MulAut.conjNormal_apply] at h1
  rw [h1]
  show ((ψ (K.normalizerMonoidHom ⟨s, hSN s.2⟩ x) : alternatingGroup (Fin n)) : Perm (Fin n)) =
    ((ψ (K.normalizerMonoidHom ⟨s, hSN s.2⟩ (ψ.symm (ψ x))) : alternatingGroup (Fin n)) :
      Perm (Fin n))
  rw [MulEquiv.symm_apply_apply]

theorem comm_iff_of_action {X : Type*} [Group X] {n : ℕ} {K S : Subgroup X}
    (ψ : ↥K ≃* alternatingGroup (Fin n)) (hSN : S ≤ Subgroup.normalizer (K : Set X))
    {τ : ↥S →* Perm (Fin n)}
    (hτ : ∀ (s : ↥S) (x : ↥K),
      ((ψ (K.normalizerMonoidHom ⟨s, hSN s.2⟩ x) : alternatingGroup (Fin n)) : Perm (Fin n)) =
        τ s * (ψ x : Perm (Fin n)) * (τ s)⁻¹)
    (s : ↥S) (x : ↥K) :
    (s : X) * x = x * s ↔ τ s * (ψ x : Perm (Fin n)) = (ψ x : Perm (Fin n)) * τ s := by
  have hco : ((K.normalizerMonoidHom ⟨s, hSN s.2⟩ x : ↥K) : X) = (s : X) * x * (s : X)⁻¹ :=
    K.normalizerMonoidHom_apply_apply_coe _ x
  constructor
  · intro h
    have h1 : K.normalizerMonoidHom ⟨s, hSN s.2⟩ x = x :=
      Subtype.ext (by rw [hco, h, mul_inv_cancel_right])
    have h2 := hτ s x
    rw [h1] at h2
    calc τ s * (ψ x : Perm (Fin n)) = (τ s * (ψ x : Perm (Fin n)) * (τ s)⁻¹) * τ s := by group
      _ = (ψ x : Perm (Fin n)) * τ s := by rw [← h2]
  · intro h
    have h1 : ((ψ (K.normalizerMonoidHom ⟨s, hSN s.2⟩ x) : alternatingGroup (Fin n)) :
        Perm (Fin n)) = ψ x := by
      rw [hτ, h, mul_inv_cancel_right]
    have h2 : K.normalizerMonoidHom ⟨s, hSN s.2⟩ x = x := ψ.injective (Subtype.ext h1)
    have h3 := congrArg Subtype.val h2
    rw [hco] at h3
    calc (s : X) * x = (s : X) * x * (s : X)⁻¹ * s := by group
      _ = x * s := by rw [h3]

end Tau

theorem input23_4Q_holds : Inputs123b.Input23_4Q := by
  intro p hp hp2 Y _ _ hq hO n hn5 hAlt hpn A hAel hAne
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨f⟩ := hAlt
  have hZ : IsPGroup p ↥(Subgroup.center Y) := AltFacts2.isPGroup_center_of_core_eq_bot hp hO
  set ρ : Y →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp
    (f.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))) with hρdef
  have hρ : IsAltRep ρ := isAltRep_of_equiv f
  have hAp : ∀ a ∈ A, a ^ p = 1 := fun a ha => hAel.2 a ha
  obtain ⟨τ, hτinj, hτ⟩ := exists_tau hpodd hn5 hq.1 f hAp
  have hτ' : ∀ (a : ↥A) (y : Y), ρ ((a : MulAut Y) y) = τ a * ρ y * (τ a)⁻¹ := hτ
  have hτp : ∀ a : ↥A, τ a ^ p = 1 := fun a => by
    rw [← map_pow, show a ^ p = 1 from Subtype.ext (by simpa using hAp a a.2), map_one]
  have hτ1 : ∀ a : ↥A, (a : MulAut Y) ≠ 1 → τ a ≠ 1 := fun a ha h =>
    ha (congrArg Subtype.val (hτinj (h.trans (map_one τ).symm)))
  have hne1 : ∀ a : ↥A, τ a ≠ 1 → (a : MulAut Y) ≠ 1 := fun a ha h => ha (by
    rw [show a = 1 from Subtype.ext h, map_one])
  refine ⟨?_, ?_⟩
  · by_cases hlt : Nat.card A < n
    · exact Or.inr hlt
    left
    set T : Subgroup (Perm (Fin n)) := τ.range with hT
    have hTel : IsElemAbelian p T := by
      refine ⟨⟨⟨fun u v => ?_⟩⟩, fun y hy => ?_⟩
      · rcases u with ⟨_, a, rfl⟩
        rcases v with ⟨_, b, rfl⟩
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [← map_mul, ← map_mul, show a * b = b * a from Subtype.ext
          (congrArg Subtype.val (hAel.1.is_comm.comm ⟨a, a.2⟩ ⟨b, b.2⟩))]
      · obtain ⟨a, rfl⟩ := hy
        exact hτp a
    have hTn : n ≤ Nat.card T := by
      rw [hT, ← Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv]
      omega
    set H : Subgroup Y := ⨆ (α : MulAut Y) (_ : α ∈ A) (_ : α ≠ 1),
      (GLAPPrimeCoreOf p (fixSub α) ⊔ GLAPLayer p (fixSub α)) with hH
    have hle : ∀ α ∈ A, α ≠ 1 → GLAPPrimeCoreOf p (fixSub α) ⊔ GLAPLayer p (fixSub α) ≤ H :=
      fun α hα hα1 => le_iSup_of_le α (le_iSup_of_le hα (le_iSup_of_le hα1 le_rfl))
    have hgen : alternatingGroup (Fin n) ≤ H.map ρ := by
      refine alt_le_of_fix hp2 hpn hn5 hTel hTn ?_ ?_
      · rintro _ ⟨a, rfl⟩ hβ1 h5
        exact (altOn_le_map hρ (hτ' a) h5).trans (Subgroup.map_mono (hle a a.2 (hne1 a hβ1)))
      · rintro _ ⟨a, rfl⟩ hβ1 h4
        exact (kleinOn_le_map hp hp2 hρ hZ (hτ' a) h4).trans
          (Subgroup.map_mono (le_sup_left.trans (hle a a.2 (hne1 a hβ1))))
    exact top_le_of_alt_le_map hρ hq.1 hgen
  · intro α hα hα1 J hJ
    obtain ⟨h5, ⟨e⟩⟩ := component_alt hp hp2 hρ hZ (hτ' ⟨α, hα⟩) (hτp ⟨α, hα⟩) hJ
    refine ⟨_, h5, ?_, ?_, ⟨e⟩⟩
    · have hne : τ ⟨α, hα⟩ ≠ 1 := hτ1 ⟨α, hα⟩ hα1
      have hsupp : (τ ⟨α, hα⟩).support.Nonempty :=
        Finset.nonempty_iff_ne_empty.2 (fun h => hne (Perm.support_eq_empty_iff.1 h))
      have := (Finset.card_compl_lt_iff_nonempty _).2 hsupp
      rwa [Fintype.card_fin] at this
    · have := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) (σ := τ ⟨α, hα⟩)
        (by rw [pow_one]; exact hτp _)
      rwa [Fintype.card_fin] at this

section AltDown

theorem isElemAbelian_zpowers {X : Type*} [Group X] {p : ℕ} {a : X} (hap : a ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers a) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 x.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 y.2
    show (x : X) * y = y * x
    rw [← hi, ← hj]
    exact (Commute.zpow_zpow_self a i j).eq
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap, one_zpow]

theorem input14_4_AltDown_of_eqv (h183 : Inputs123b.Input18_3_eqv) :
    Prop1116Design.Input14_4_AltDown := by
  intro G _ _ p hp hp2 e a J0 J1 hae hap hJ1 hJ0 hKx n hn
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  set Js : Subgroup G := ⨆ g ∈ Subgroup.zpowers a, GLBConj g J1 with hJs
  rw [hKx] at hJ0
  have hcomp : ∀ g ∈ Subgroup.zpowers a, GLAPComponent p (Cg e) (GLBConj g J1) := by
    intro g hg
    have hge : g * e = e * g := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      exact (Commute.zpow_left hae k).eq
    have := glaPComponent_gLBConj hJ1 g
    rwa [Prop1116Design.gLBConj_cg_eq hge] at this
  have hJsn : IsSubnormal Js (Cg e) := by
    have hJs' : Js = sSup ((fun g => GLBConj g J1) '' (Subgroup.zpowers a : Set G)) := by
      rw [hJs, sSup_image]
      rfl
    rw [hJs']
    exact CFSG.LocalAnalysis.GLTheoremA.isSubnormal_sSup_glaPComponent hp _
      (by rintro L ⟨g, hg, rfl⟩; exact hcomp g hg)
  have hlayer : IsSubnormal (GLAPLayer p (Js ⊓ Cg a)) (Js ⊓ Cg a) :=
    CFSG.LocalAnalysis.GLTheoremA.isSubnormal_sSup_glaPComponent hp
      {L | GLAPComponent p (Js ⊓ Cg a) L} fun _ h => h
  have hJ0a : GLAPComponent p (Js ⊓ Cg a) J0 := l119_glaPComponent_of_isSubnormal hp hlayer hJ0
  have hJ0' : GLAPComponent p (Cg e ⊓ Subgroup.centralizer ({a} : Set G)) J0 :=
    l119_glaPComponent_of_isSubnormal hp (isSubnormal_inf hJsn (Cg a)) hJ0a
  have hq1 : CFSG.Open.IsQuasisimple (barOf p J1) :=
    (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.isQuasisimple_barX_iff hp hJ1.2.1).1
      hJ1.2.2.1.2.2
  obtain ⟨f⟩ := hn
  have h5 : 5 ≤ n := SchurFacts.five_le_of_isAltType hq1 ⟨f⟩
  by_cases haN : a ∈ Subgroup.normalizer (J1 : Set G)
  ·
    have hJsJ : Js = J1 := by
      refine le_antisymm (iSup₂_le fun g hg => ?_) (le_iSup₂_of_le 1 (Subgroup.one_mem _) (by
        rw [gLBConj_one]))
      have hgN : g ∈ Subgroup.normalizer (J1 : Set G) :=
        (Subgroup.zpowers_le.2 haN) hg
      exact (mem_normalizer_iff_gLBConj_eq.1 hgN).le
    have hJ0'' : GLAPComponent p (J1 ⊓ Subgroup.centralizer ({a} : Set G)) J0 := by
      rw [← hJsJ]
      exact hJ0a
    obtain ⟨Q, hQ, ⟨eQ⟩⟩ := Inputs123b.exists_component_image hp haN hap hJ0''
    have hO : GLAPPrimeCore p (barOf p J1) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
    have hZ : IsPGroup p ↥(Subgroup.center (barOf p J1)) :=
      AltFacts2.isPGroup_center_of_core_eq_bot hp hO
    set α := CFSG.HardMathSupport.Solomon.LocalBalance.barAut p J1 ⟨a, haN⟩ with hα
    have hαp : α ^ p = 1 := by
      rw [hα, ← map_pow]
      have : (⟨a, haN⟩ : ↥(Subgroup.normalizer (J1 : Set G))) ^ p = 1 :=
        Subtype.ext (by simpa using hap)
      rw [this, map_one]
    have hAp : ∀ β ∈ Subgroup.zpowers α, β ^ p = 1 := by
      intro β hβ
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hβ
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hαp, one_zpow]
    obtain ⟨τ, -, hτ⟩ := exists_tau hpodd h5 hq1.1 f hAp
    set α' : ↥(Subgroup.zpowers α) := ⟨α, Subgroup.mem_zpowers α⟩ with hα'
    have hτp : τ α' ^ p = 1 := by
      rw [← map_pow, show α' ^ p = 1 from Subtype.ext (by simpa using hαp), map_one]
    obtain ⟨h5', ⟨eA⟩⟩ := component_alt hp hp2 (isAltRep_of_equiv f) hZ (hτ α') hτp hQ
    refine ⟨_, h5', Inputs123b.isAltType_center_congr eQ ⟨eA⟩, ?_⟩
    have := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) (σ := τ α')
      (by rw [pow_one]; exact hτp)
    rwa [Fintype.card_fin] at this
  ·
    have ha1 : a ≠ 1 := fun h => haN (h ▸ (Subgroup.normalizer (J1 : Set G)).one_mem)
    have haC : a ∈ Cg e := Subgroup.mem_centralizer_singleton_iff.2 hae
    have hle : barX p (Cg e) J0 ≤ barX p (Cg e) Js := barX_mono (hJ0a.1.trans inf_le_left)
    obtain ⟨π, hπs, hπk, -⟩ := h183 G p hp hp2 (Cg e) J1 (Subgroup.zpowers a) hJ1
      (isElemAbelian_zpowers hap) (Subgroup.zpowers_le.2 haC) a (Subgroup.mem_zpowers a) ha1 haC
      (Or.inl haN) J0 hJ0' hle
    obtain ⟨e1⟩ := Claims126.nonempty_quot_center_quot hq1.1 π.ker hπk
    exact ⟨n, h5, Inputs123b.isAltType_center_congr
      (QuotientGroup.quotientKerEquivOfSurjective π hπs).symm ⟨e1.trans f⟩, rfl⟩

end AltDown

section I236

variable {X : Type} [Group X] [Finite X]

theorem mem_of_isSCp {p : ℕ} {B : Subgroup X} (hB : IsSCp p ⊤ B) {z : X} (hzp : z ^ p = 1)
    (hz : ∀ b ∈ B, b * z = z * b) : z ∈ B := by
  have hc : B ≤ Subgroup.centralizer (Subgroup.zpowers z : Set X) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_right (hz b hb) k).eq.symm
  have h := hB.2.2 (B ⊔ Subgroup.zpowers z) le_top
    (isElemAbelian_sup_of_commute hB.2.1 (isElemAbelian_zpowers hzp) hc) le_sup_left
  rw [← h]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

theorem mem_glbCore_of_comm {p : ℕ} (hp : p.Prime) {B B₀ : Subgroup X} (hBel : IsElemAbelian p B)
    (hB₀B : B₀ ≤ B) {b₀ c x : X} (hb₀ : b₀ ∈ B₀) (hb₀1 : b₀ ≠ 1) (hcB : c ∈ B) (hcB₀ : c ∉ B₀)
    (hxb₀ : x * b₀ = b₀ * x) (hxc : x * c = c * x) : x ∈ CFSG.Open.GLBCore p 2 B := by
  have hb₀p : b₀ ^ p = 1 := hBel.2 b₀ (hB₀B hb₀)
  have hcp : c ^ p = 1 := hBel.2 c hcB
  have hc1 : c ≠ 1 := fun h => hcB₀ (h ▸ B₀.one_mem)
  have hD : Subgroup.closure ({b₀, c} : Set X) ≤ B := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with h | h
    · rw [h]
      exact hB₀B hb₀
    · rw [h]
      exact hcB
  have hDr : 2 ≤ CFSG.Open.pRank p (Subgroup.closure ({b₀, c} : Set X)) := by
    refine Lemma116.two_le_pRank_pair hp (elemAbelian_comm hBel (hB₀B hb₀) hcB) hb₀p hcp hb₀1 hc1 ?_
    intro i j hij
    by_contra hne
    have hcj : c ^ (j % p) = c ^ j := by
      conv_rhs => rw [← Nat.div_add_mod j p, pow_add, pow_mul, hcp, one_pow, one_mul]
    have hj0 : j % p ≠ 0 := by
      intro h0
      apply hne
      rw [hij, ← hcj, h0, pow_zero]
    apply hcB₀
    refine Input236gt.mem_of_pow_mem hp hcp (Nat.pos_of_ne_zero hj0) (Nat.mod_lt _ hp.pos) ?_
    rw [hcj, ← hij]
    exact B₀.pow_mem hb₀ i
  refine MovingAround.normalizer_le_glbCore hD hDr
    (Lemma116.mem_normalizer_closure_of_comm _ _ fun t ht => ?_)
  rcases ht with h | h
  · rw [h]
    exact hxb₀
  · rw [h]
    exact hxc

@[expose] def tl (b k : X) (m : ℕ) : X :=
  ((List.range m).map fun i => (b ^ (i + 1))⁻¹ * k * b ^ (i + 1)).prod

theorem tl_succ (b k : X) (m : ℕ) :
    tl b k (m + 1) = tl b k m * ((b ^ (m + 1))⁻¹ * k * b ^ (m + 1)) := by
  simp [tl, List.range_succ]

theorem tl_succ' (b k : X) (m : ℕ) :
    tl b k (m + 1) = (b⁻¹ * k * b) *
      ((List.range m).map fun i => (b ^ (i + 2))⁻¹ * k * b ^ (i + 2)).prod := by
  rw [tl, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
  simp only [zero_add, pow_one]
  rfl

theorem conj_tl (b k : X) (m : ℕ) :
    b⁻¹ * tl b k m * b = ((List.range m).map fun i => (b ^ (i + 2))⁻¹ * k * b ^ (i + 2)).prod := by
  have h : b⁻¹ * tl b k m * b = MulAut.conj b⁻¹ (tl b k m) := by rw [MulAut.conj_apply, inv_inv]
  rw [h, tl, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, MulAut.conj_apply, inv_inv]
  group

theorem commute_dg {b k : X} {m : ℕ} (hb : b ^ (m + 1) = 1) (hk : Commute k (tl b k m)) :
    Commute b (k * tl b k m) := by
  have h1 : b⁻¹ * (k * tl b k m) * b = k * tl b k m := by
    calc b⁻¹ * (k * tl b k m) * b = (b⁻¹ * k * b) * (b⁻¹ * tl b k m * b) := by group
      _ = tl b k (m + 1) := by rw [conj_tl, tl_succ']
      _ = tl b k m * k := by rw [tl_succ, hb]; simp
      _ = k * tl b k m := hk.eq.symm
  show b * (k * tl b k m) = (k * tl b k m) * b
  calc b * (k * tl b k m) = b * (b⁻¹ * (k * tl b k m) * b) := by rw [h1]
    _ = (k * tl b k m) * b := by group

theorem commute_tl_of_commute {s b k : X} (hb : Commute s b) (hk : Commute s k) (m : ℕ) :
    Commute s (tl b k m) := by
  apply Commute.list_prod_right
  intro y hy
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
  exact ((hb.pow_right (i + 1)).inv_right.mul_right hk).mul_right (hb.pow_right (i + 1))

theorem commute_tl_of {K : Subgroup X} {b k w : X} (hk : k ∈ K) {m : ℕ}
    (h : ∀ i, 0 < i → i ≤ m → ∀ y ∈ GLBConj (b ^ i) K, Commute y w) : Commute (tl b k m) w := by
  apply Commute.list_prod_left
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
  rw [List.mem_range] at hi
  refine h (i + 1) (by omega) (by omega) _ ?_
  rw [mem_gLBConj]
  simpa [mul_assoc] using hk

theorem input23_6_holds : Lemma116.Input23_6 := by
  intro X _ _ p n hp hp2 hpn hpdvd B K hB hB3 hK he hB0ne
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨ψ⟩ := he
  have h5 : 5 ≤ n := Input236gt.five_le_of_isQuasisimple hK.2.2 ψ
  have hBel : IsElemAbelian p B := hB.2.1
  have hBp : ∀ b ∈ B, b ^ p = 1 := fun b hb => hBel.2 b hb
  set Ks : Subgroup X := ⨆ g ∈ B, GLBConj g K with hKs
  set B₀ : Subgroup X := B ⊓ Subgroup.centralizer (Ks : Set X) with hB₀
  set Γ : Subgroup X := CFSG.Open.GLBCore p 2 B with hΓ
  have hB₀B : B₀ ≤ B := inf_le_left
  have hKKs : K ≤ Ks := le_iSup₂_of_le 1 B.one_mem (by rw [gLBConj_one])
  have hB₀K : ∀ b ∈ B₀, ∀ x ∈ K, x * b = b * x := fun b hb x hx =>
    Subgroup.mem_centralizer_iff.1 hb.2 x (hKKs hx)
  by_cases hB₀2 : 2 ≤ CFSG.Open.pRank p B₀
  · left
    intro k hk
    refine MovingAround.normalizer_le_glbCore hB₀B hB₀2 ?_
    have h := Lemma116.mem_normalizer_closure_of_comm (B₀ : Set X) k fun s hs => hB₀K s hs k hk
    rwa [Subgroup.closure_eq] at h
  have hB₀el : IsElemAbelian p B₀ := CFSG.Open.IsElemAbelian.mono hBel hB₀B
  have hB₀card : Nat.card B₀ = p := by
    have h1 := Lemma116.card_eq_pow_pRank hp hB₀el
    have h2 : CFSG.Open.pRank p B₀ ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at h1
      exact hB0ne (Subgroup.eq_bot_of_card_eq B₀ h1)
    have h3 : CFSG.Open.pRank p B₀ = 1 := by omega
    rw [h1, h3, pow_one]
  obtain ⟨b₀, hb₀, hb₀1⟩ : ∃ b₀ ∈ B₀, b₀ ≠ 1 := by
    obtain ⟨⟨s, hs⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB0ne
    exact ⟨s, hs, fun h => hs1 (Subtype.ext h)⟩
  have hΓmem : ∀ c ∈ B, c ∉ B₀ → ∀ x, x * b₀ = b₀ * x → x * c = c * x → x ∈ Γ :=
    fun c hc hcB₀ x h1 h2 => mem_glbCore_of_comm hp hBel hB₀B hb₀ hb₀1 hc hcB₀ h1 h2
  have hKb₀ : ∀ x ∈ K, x * b₀ = b₀ * x := fun x hx => hB₀K b₀ hb₀ x hx
  have hB₀N : ∀ b ∈ B₀, b ∈ Subgroup.normalizer (K : Set X) := fun b hb =>
    Subgroup.centralizer_le_normalizer (K : Set X) (Subgroup.centralizer_le (fun x hx => hKKs hx) hb.2)
  haveI hKsimp : IsSimpleGroup ↥K := ψ.isSimpleGroup_congr.2 (AltFacts3.isSimple_alt h5)
  by_cases hN : ∀ b ∈ B, b ∈ Subgroup.normalizer (K : Set X)
  swap
  ·
    left
    push Not at hN
    obtain ⟨b₁, hb₁B, hb₁N⟩ := hN
    obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    have hKc : ∀ g : X, IsComponentOf (GLBConj g K) ⊤ := Input236gt.isComponentOf_glbConj hK
    have hKne : ∀ b ∈ B, b ∉ Subgroup.normalizer (K : Set X) → ∀ i, 0 < i → i < p →
        GLBConj (b ^ i) K ≠ K := fun b hb hbN i hi0 hi h =>
      hbN (Input236gt.mem_of_pow_mem hp (hBp b hb) hi0 hi (mem_normalizer_iff_gLBConj_eq.2 h))
    have htlK : ∀ b ∈ B, b ∉ Subgroup.normalizer (K : Set X) → ∀ k ∈ K, ∀ y ∈ K,
        Commute (tl b k m) y := fun b hb hbN k hk y hy =>
      commute_tl_of hk fun i hi0 him z hz =>
        Input236gt.commute_of_mem_ne (hKc _) hK (hKne b hb hbN i hi0 (by omega)) hz hy
    have hdg : ∀ b ∈ B, b ∉ Subgroup.normalizer (K : Set X) → ∀ k ∈ K, k * tl b k m ∈ Γ := by
      intro b hb hbN k hk
      have hbB₀ : b ∉ B₀ := fun h => hbN (hB₀N b h)
      have hb₀b : Commute b₀ b := elemAbelian_comm hBel (hB₀B hb₀) hb
      have hb₀k : Commute b₀ k := (hKb₀ k hk).symm
      refine hΓmem b hb hbB₀ _ (hb₀k.mul_right (commute_tl_of_commute hb₀b hb₀k m)).eq.symm ?_
      have hbp : b ^ (m + 1) = 1 := by rw [← hm]; exact hBp b hb
      exact (commute_dg hbp (htlK b hb hbN k hk k hk).symm).eq.symm
    by_cases h3a : ∃ c ∈ B, c ∉ B₀ ∧ c ∈ Subgroup.normalizer (K : Set X)
    ·
      obtain ⟨c, hcB, hcB₀, hcN⟩ := h3a
      obtain ⟨w, hwK, hw1, hwc⟩ : ∃ w ∈ K, w ≠ 1 ∧ w * c = c * w := by
        have hcS : c ∈ Subgroup.zpowers c := Subgroup.mem_zpowers c
        obtain ⟨τc, hτc⟩ := exists_perm_action hpodd h5 ψ (S := Subgroup.zpowers c)
          (Subgroup.zpowers_le.2 hcN) fun s hs => by
            obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
            rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hBp c hcB, one_zpow]
        set σ := τc ⟨c, hcS⟩ with hσ
        have hσp : σ ^ p = 1 := by
          rw [hσ, ← map_pow, show (⟨c, hcS⟩ : ↥(Subgroup.zpowers c)) ^ p = 1 from
            Subtype.ext (by simpa using hBp c hcB), map_one]
        obtain ⟨w₀, hw₀1, hw₀σ⟩ : ∃ w₀ : ↥K, w₀ ≠ 1 ∧
            σ * (ψ w₀ : Perm (Fin n)) = (ψ w₀ : Perm (Fin n)) * σ := by
          by_cases hσ1 : σ = 1
          · haveI := Claims126.nontrivial_of_isQuasisimple hK.2.2
            obtain ⟨w₀, hw₀⟩ := exists_ne (1 : ↥K)
            exact ⟨w₀, hw₀, by rw [hσ1, one_mul, mul_one]⟩
          · have hσA : σ ∈ alternatingGroup (Fin n) := mem_alt_of_pow hpodd hσp
            refine ⟨ψ.symm ⟨σ, hσA⟩, fun h => hσ1 ?_, by rw [MulEquiv.apply_symm_apply]⟩
            have := congrArg (fun x => ((ψ x : alternatingGroup (Fin n)) : Perm (Fin n))) h
            simpa using this
        exact ⟨w₀, w₀.2, fun h => hw₀1 (Subtype.ext h),
          ((comm_iff_of_action ψ _ hτc ⟨c, hcS⟩ w₀).2 hw₀σ).symm⟩
      have hconj : ∀ k ∈ K, ∀ y ∈ K, y * c = c * y → k * y * k⁻¹ ∈ Γ := by
        intro k hk y hy hyc
        have hyΓ : y ∈ Γ := hΓmem c hcB hcB₀ y (hKb₀ y hy) hyc
        have hd := hdg b₁ hb₁B hb₁N k hk
        have hc := htlK b₁ hb₁B hb₁N k hk y hy
        have e : (k * tl b₁ k m) * y * (k * tl b₁ k m)⁻¹ = k * y * k⁻¹ := by
          calc (k * tl b₁ k m) * y * (k * tl b₁ k m)⁻¹
              = k * (tl b₁ k m * y) * (tl b₁ k m)⁻¹ * k⁻¹ := by group
            _ = k * (y * tl b₁ k m) * (tl b₁ k m)⁻¹ * k⁻¹ := by rw [hc.eq]
            _ = k * y * k⁻¹ := by group
        rw [← e]
        exact Γ.mul_mem (Γ.mul_mem hd hyΓ) (Γ.inv_mem hd)
      set S : Set ↥K := {x | ∃ g y : ↥K, (y : X) * c = c * y ∧ x = g * y * g⁻¹} with hS
      have hMn : (Subgroup.closure S).Normal := by
        refine ⟨fun x hx g => ?_⟩
        refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ Subgroup.closure S)
          ?_ ?_ ?_ ?_ hx
        · rintro _ ⟨g', y, hy, rfl⟩
          exact Subgroup.subset_closure ⟨g * g', y, hy, by group⟩
        · rw [mul_one, mul_inv_cancel]
          exact (Subgroup.closure S).one_mem
        · intro a b _ _ ha hb
          have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
          rw [e]
          exact (Subgroup.closure S).mul_mem ha hb
        · intro a _ ha
          have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
          rw [e]
          exact (Subgroup.closure S).inv_mem ha
      have hMtop : Subgroup.closure S = ⊤ := by
        rcases hMn.eq_bot_or_eq_top with h | h
        · exfalso
          have : (⟨w, hwK⟩ : ↥K) ∈ Subgroup.closure S :=
            Subgroup.subset_closure ⟨1, ⟨w, hwK⟩, hwc, by group⟩
          rw [h, Subgroup.mem_bot] at this
          exact hw1 (congrArg Subtype.val this)
        · exact h
      have hMΓ : Subgroup.closure S ≤ Γ.comap K.subtype := by
        rw [Subgroup.closure_le]
        rintro _ ⟨g, y, hy, rfl⟩
        exact hconj g g.2 y y.2 hy
      intro k hk
      exact hMΓ (hMtop ▸ Subgroup.mem_top (⟨k, hk⟩ : ↥K))
    ·
      push Not at h3a
      have hNB : ∀ c ∈ B, c ∈ Subgroup.normalizer (K : Set X) → c ∈ B₀ := fun c hc hcN => by
        by_contra h
        exact h3a c hc h hcN
      have hBcard : p ^ 3 ≤ Nat.card B := by
        rw [Lemma116.card_eq_pow_pRank hp hBel]
        exact Nat.pow_le_pow_right hp.pos hB3
      obtain ⟨b1, hb1B, b2, hb2B, hind⟩ := Input236gt.exists_indep hp hBel hB₀B hB₀card hBcard
      have hpow1 : ∀ i, 0 < i → i < p → b1 ^ i ∉ B₀ := fun i hi0 hi hmem =>
        absurd (hind i 0 hi (by omega) (by simpa using hmem)).1 (by omega)
      have hpow2 : ∀ j, 0 < j → j < p → b2 ^ j ∉ B₀ := fun j hj0 hj hmem =>
        absurd (hind 0 j (by omega) hj (by simpa using hmem)).2 (by omega)
      have hb1N : b1 ∉ Subgroup.normalizer (K : Set X) := fun h =>
        hpow1 1 (by omega) hp.one_lt (by rw [pow_one]; exact hNB b1 hb1B h)
      have hb2N : b2 ∉ Subgroup.normalizer (K : Set X) := fun h =>
        hpow2 1 (by omega) hp.one_lt (by rw [pow_one]; exact hNB b2 hb2B h)
      have hKne12 : ∀ i j, 0 < i → i < p → 0 < j → j < p →
          GLBConj (b1 ^ i) K ≠ GLBConj (b2 ^ j) K := by
        intro i j hi0 hi hj0 hj h
        have h1 := hNB _ (B.mul_mem (B.pow_mem hb2B j) (B.inv_mem (B.pow_mem hb1B i)))
          (mem_normalizer_iff_gLBConj_eq.2 (Input236gt.glbConj_eq_of_eq h))
        have h2 : b2 ^ j * (b1 ^ i)⁻¹ = b1 ^ (p - i) * b2 ^ j := by
          have hinv : (b1 ^ i)⁻¹ = b1 ^ (p - i) := by
            rw [inv_eq_iff_mul_eq_one, ← pow_add, Nat.add_sub_of_le hi.le, hBp b1 hb1B]
          rw [hinv]
          exact elemAbelian_comm hBel (B.pow_mem hb2B j) (B.pow_mem hb1B _)
        rw [h2] at h1
        exact absurd (hind (p - i) j (by omega) hj h1).2 (by omega)
      have hcomm12 : ∀ k ∈ K, ∀ k' ∈ K, Commute (tl b1 k m) (tl b2 k' m) := by
        intro k hk k' hk'
        refine commute_tl_of hk fun i hi0 him y hy => ?_
        refine (commute_tl_of hk' fun j hj0 hjm z hz => ?_).symm
        exact (Input236gt.commute_of_mem_ne (hKc _) (hKc _)
          (hKne12 i j hi0 (by omega) hj0 (by omega)) hy hz).symm
      have hΓ' : ∀ k ∈ K, ∀ k' ∈ K, ⁅k, k'⁆ ∈ Γ := by
        intro k hk k' hk'
        have h1 := hdg b1 hb1B hb1N k hk
        have h2 := hdg b2 hb2B hb2N k' hk'
        have hc : ⁅k * tl b1 k m, k' * tl b2 k' m⁆ = ⁅k, k'⁆ :=
          Input236gt.commutatorElement_mul_mul (htlK b1 hb1B hb1N k hk k' hk') (hcomm12 k hk k' hk')
            (htlK b2 hb2B hb2N k' hk' k hk)
        rw [← hc, commutatorElement_def]
        exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem h1 h2) (Γ.inv_mem h1)) (Γ.inv_mem h2)
      exact Input236gt.le_of_commutators hK.2.2.1 hΓ'
  have hBN : B ≤ Subgroup.normalizer (K : Set X) := fun b hb => hN b hb
  have hKsK : Ks = K :=
    le_antisymm (iSup₂_le fun g hg => (mem_normalizer_iff_gLBConj_eq.1 (hN g hg)).le) hKKs
  obtain ⟨τ, hτ⟩ := exists_perm_action hpodd h5 ψ hBN hBp
  have hcomm' := comm_iff_of_action ψ hBN hτ
  have hτp : ∀ b : ↥B, τ b ^ p = 1 := fun b => by
    rw [← map_pow, show b ^ p = 1 from Subtype.ext (by simpa using hBp b b.2), map_one]
  have hτA : ∀ b : ↥B, τ b ∈ alternatingGroup (Fin n) := fun b => mem_alt_of_pow hpodd (hτp b)
  have hBc : ∀ b b' : ↥B, τ b * τ b' = τ b' * τ b := fun b b' => by
    rw [← map_mul, ← map_mul, show b * b' = b' * b from Subtype.ext (elemAbelian_comm hBel b.2 b'.2)]
  have hmaxK : ∀ σ (hσ : σ ∈ alternatingGroup (Fin n)), σ ^ p = 1 → (∀ b : ↥B, σ * τ b = τ b * σ) →
      ((ψ.symm ⟨σ, hσ⟩ : ↥K) : X) ∈ B := by
    intro σ hσ hσp hσc
    have hψk : ((ψ (ψ.symm ⟨σ, hσ⟩) : alternatingGroup (Fin n)) : Perm (Fin n)) = σ := by
      rw [MulEquiv.apply_symm_apply]
    refine mem_of_isSCp hB ?_ fun b hb => (hcomm' ⟨b, hb⟩ _).2 (by rw [hψk]; exact (hσc ⟨b, hb⟩).symm)
    have h1 : ψ (ψ.symm ⟨σ, hσ⟩ ^ p) = 1 := by
      apply Subtype.ext
      rw [map_pow, SubgroupClass.coe_pow, hψk, hσp]
      rfl
    have h2 : ψ.symm ⟨σ, hσ⟩ ^ p = 1 := (MulEquiv.map_eq_one_iff ψ).1 h1
    have h3 := congrArg Subtype.val h2
    rwa [SubgroupClass.coe_pow] at h3
  have hτK : ∀ (t : ↥K) (ht : (t : X) ∈ B),
      τ ⟨t, ht⟩ = ((ψ t : alternatingGroup (Fin n)) : Perm (Fin n)) := by
    intro t ht
    have h : ((ψ t : alternatingGroup (Fin n)) : Perm (Fin n))⁻¹ * τ ⟨t, ht⟩ = 1 := by
      refine eq_one_of_comm_alt (by omega) fun g hg => ?_
      have h1 := hτ ⟨t, ht⟩ (ψ.symm ⟨g, hg⟩)
      have h2 : K.normalizerMonoidHom ⟨((⟨t, ht⟩ : ↥B) : X), hBN ht⟩ (ψ.symm ⟨g, hg⟩) =
          t * ψ.symm ⟨g, hg⟩ * t⁻¹ := Subtype.ext (K.normalizerMonoidHom_apply_apply_coe _ _)
      rw [h2, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      set u := ((ψ t : alternatingGroup (Fin n)) : Perm (Fin n))
      have h3 : τ ⟨t, ht⟩ * g = u * g * u⁻¹ * τ ⟨t, ht⟩ := by
        calc τ ⟨t, ht⟩ * g = (τ ⟨t, ht⟩ * g * (τ ⟨t, ht⟩)⁻¹) * τ ⟨t, ht⟩ := by group
          _ = u * g * u⁻¹ * τ ⟨t, ht⟩ := by rw [← h1]
      calc u⁻¹ * τ ⟨t, ht⟩ * g = u⁻¹ * (τ ⟨t, ht⟩ * g) := by group
        _ = u⁻¹ * (u * g * u⁻¹ * τ ⟨t, ht⟩) := by rw [h3]
        _ = g * (u⁻¹ * τ ⟨t, ht⟩) := by group
    exact (inv_mul_eq_one.1 h).symm
  have hker : ∀ b : ↥B, τ b = 1 ↔ (b : X) ∈ B₀ := by
    intro b
    constructor
    · intro h1
      refine ⟨b.2, ?_⟩
      show (b : X) ∈ Subgroup.centralizer (Ks : Set X)
      rw [hKsK, Subgroup.mem_centralizer_iff]
      intro x hx
      exact ((hcomm' b ⟨x, hx⟩).2 (by rw [h1, one_mul, mul_one])).symm
    · intro hb
      refine eq_one_of_comm_alt (by omega) fun g hg => ?_
      have h1 := (hcomm' b (ψ.symm ⟨g, hg⟩)).1 (hB₀K b hb _ (ψ.symm ⟨g, hg⟩).2).symm
      rwa [MulEquiv.apply_symm_apply] at h1
  set T' : Subgroup (Perm (Fin n)) := τ.range with hT'
  have hT'el : IsElemAbelian p T' := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun y hy => ?_⟩
    · rcases u with ⟨_, a, rfl⟩
      rcases v with ⟨_, b, rfl⟩
      exact Subtype.ext (hBc a b)
    · obtain ⟨a, rfl⟩ := hy
      exact hτp a
  have hcardB : Nat.card B = p * Nat.card T' := by
    have h1 : Nat.card B = Nat.card τ.ker * Nat.card τ.range := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup τ.ker, mul_comm,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange τ).toEquiv]
    have h2 : Nat.card τ.ker = p := by
      rw [← hB₀card]
      have : τ.ker.map B.subtype = B₀ := by
        ext x
        constructor
        · rintro ⟨b, hb, rfl⟩
          exact (hker b).1 hb
        · intro hx
          exact ⟨⟨x, hB₀B hx⟩, (hker _).2 hx, rfl⟩
      rw [← this, Subgroup.card_map_of_injective B.subtype_injective]
    rw [h1, h2]
  have hmax : ∀ σ ∈ alternatingGroup (Fin n), σ ^ p = 1 → (∀ t ∈ T', σ * t = t * σ) → σ ∈ T' := by
    intro σ hσ hσp hσc
    have hkB := hmaxK σ hσ hσp fun b => hσc _ ⟨b, rfl⟩
    refine ⟨⟨_, hkB⟩, ?_⟩
    rw [hτK _ hkB, MulEquiv.apply_symm_apply]
  by_cases hreg : ∀ i, ∃ t ∈ T', t ≠ 1 ∧ t i = i
  ·
    left
    set Γ' : Subgroup (Perm (Fin n)) :=
      (Γ.comap K.subtype).map ((alternatingGroup (Fin n)).subtype.comp ψ.toMonoidHom) with hΓ'
    have hcent : ∀ t ∈ T', t ≠ 1 → Claims126.cA t ≤ Γ' := by
      rintro _ ⟨b, rfl⟩ hb1 g hg
      obtain ⟨hgA, hgc⟩ := Claims126.mem_cA.1 hg
      refine ⟨ψ.symm ⟨g, hgA⟩, ?_, by simp⟩
      show ((ψ.symm ⟨g, hgA⟩ : ↥K) : X) ∈ Γ
      have hbB₀ : (b : X) ∉ B₀ := fun h => hb1 ((hker b).2 h)
      refine hΓmem b b.2 hbB₀ _ (hKb₀ _ (ψ.symm ⟨g, hgA⟩).2) ?_
      exact ((hcomm' b (ψ.symm ⟨g, hgA⟩)).2 (by rw [MulEquiv.apply_symm_apply]; exact hgc.symm)).symm
    intro k hk
    have hA := alt_le_of_fix' hp2 hpdvd h5 hT'el hreg
      (fun t ht ht1 _ => (Claims126.altOn_le_cA t).trans (hcent t ht ht1))
      (fun t ht ht1 h4 g hg =>
        hcent t ht ht1 (Claims126.altOn_le_cA t ((Claims126.mem_kleinOn h4).1 hg).1))
    obtain ⟨x, hx, hxk⟩ := hA (ψ ⟨k, hk⟩).2
    have hxk' : x = ⟨k, hk⟩ := ψ.injective (Subtype.ext hxk)
    rw [hxk'] at hx
    exact hx
  ·
    right
    push Not at hreg
    obtain ⟨i, hi⟩ := hreg
    set r := CFSG.Open.pRank p B - 1 with hr
    have hrB : CFSG.Open.pRank p B = r + 1 := by omega
    have hT'card : Nat.card T' = p ^ r := by
      have h1 := Lemma116.card_eq_pow_pRank hp hBel
      rw [hcardB, hrB, pow_succ, mul_comm] at h1
      exact Nat.eq_of_mul_eq_mul_right hp.pos h1
    have hT'ne : ∃ t ∈ T', t ≠ 1 := by
      by_contra h
      push Not at h
      have hbot : T' = ⊥ := (Subgroup.eq_bot_iff_forall T').2 h
      rw [hbot, Subgroup.card_bot] at hT'card
      have h1 : p ^ 2 ≤ p ^ r := Nat.pow_le_pow_right hp.pos (by omega)
      have h2 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    obtain ⟨δ, hδ1, hδp, hnδ, hsupp⟩ := regular_of_maximal hp2 hpdvd hT'el hmax hi hT'ne
    obtain ⟨_, ⟨b, rfl⟩, hb1⟩ := hT'ne
    have hkB := hmaxK (τ b) (hτA b) (hτp b) fun b' => hBc b b'
    refine ⟨r, δ, by omega, hδ1, hδp, by omega, hrB, ?_, ψ.symm ⟨τ b, hτA b⟩, hkB, ?_, ψ, ?_⟩
    · rw [eq_bot_iff]
      rintro x ⟨⟨-, hxK⟩, hxB₀⟩
      rw [Subgroup.mem_bot]
      have h1 : ((ψ ⟨x, hxK⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) = 1 := by
        refine eq_one_of_comm_alt (by omega) fun g hg => ?_
        have hc : ((ψ.symm ⟨g, hg⟩ : ↥K) : X) * x = x * (ψ.symm ⟨g, hg⟩ : ↥K) :=
          Subgroup.mem_centralizer_iff.1 hxB₀.2 _ (hKKs (ψ.symm ⟨g, hg⟩).2)
        have h2 : ψ ⟨x, hxK⟩ * ψ (ψ.symm ⟨g, hg⟩) = ψ (ψ.symm ⟨g, hg⟩) * ψ ⟨x, hxK⟩ := by
          rw [← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext hc.symm
        rw [MulEquiv.apply_symm_apply] at h2
        exact congrArg Subtype.val h2
      have h2 : ψ ⟨x, hxK⟩ = 1 := Subtype.ext h1
      exact congrArg Subtype.val ((MulEquiv.map_eq_one_iff ψ).1 h2)
    · intro h
      apply hb1
      have := congrArg (fun x => ((ψ x : alternatingGroup (Fin n)) : Perm (Fin n))) h
      simpa using this
    · rw [MulEquiv.apply_symm_apply]
      show (τ b).cycleType = _
      have hct := Equiv.Perm.cycleType_of_pow_prime_eq_one (hτp b)
      have hsum := Equiv.Perm.sum_cycleType (τ b)
      rw [hct, Multiset.sum_replicate, smul_eq_mul, hsupp _ ⟨b, rfl⟩ hb1, hT'card] at hsum
      have hc : (τ b).cycleType.card = p ^ (r - 1) := by
        have : p ^ r = p ^ (r - 1) * p := by
          rw [← pow_succ]
          congr 1
          omega
        rw [this] at hsum
        exact Nat.eq_of_mul_eq_mul_right hp.pos hsum
      rw [hct, hc]

end I236

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts5

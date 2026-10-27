module

public import CFSG.LargeExtraspecial.A2ModFrFLevi

public section

namespace CFSG.LargeExtraspecial.A2Mod.FrF

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.ExclNS
open scoped commutatorElement Pointwise

abbrev a2v : Fin 4 → ℤ := ![0, 0, 1, 0]
abbrev s12 : Fin 4 → ℤ := ![0, 1, 1, 0]

theorem a2v_mem_roots (hA : TauCeti.IsFiniteType f4M) : a2v ∈ roots hA ∅ := by
  have h := (RootSystem.ofCartan hA ∅).single_mem (2 : Fin 4)
  rwa [show (Pi.single 2 1 : Fin 4 → ℤ) = a2v by decide] at h

theorem s12_mem_roots (hA : TauCeti.IsFiniteType f4M) : s12 ∈ roots hA ∅ :=
  mem_roots_of_eq hA ((coxeterMatrix hA).toCoxeterSystem.simple 1) 2
    (by rw [weylAction_simple_eq]; decide)

namespace F4Frame

variable {G : Type} [Group G] {R : Set (Subgroup G)} {F : F4Frame G R}

theorem rootGroup_s12 : F.X s12 = conjSub (F.X a2v) (F.n 1) := by
  have h := (actsAs_n (D := F.D) F.hct 1) a2v (a2v_mem_roots F.hA)
  rw [show weylAction F.hA ((coxeterMatrix F.hA).toCoxeterSystem.simple 1) a2v = s12 by
    rw [weylAction_simple_eq]; decide] at h
  exact h.symm

theorem finite_rootGroup [Finite G] {γ : Fin 4 → ℤ} (hγ : γ ∈ roots F.hA ∅) : Finite (F.X γ) :=
  Finite.of_injective (fun x : F.X γ => F.Ψ x) fun x y h =>
    Subtype.ext (eq_of_map_eq hγ x.2 y.2 h)

theorem commuting_neg_r2_a2v : Commuting (F.X (-r2)) (F.X a2v) :=
  commuting_of_form (isLong_r2 (F := F)).neg.mem_roots (a2v_mem_roots F.hA) (by decide) (by decide)
    (by rw [form_apply]; decide) (by rw [form_apply]; decide) (by rw [form_apply]; decide)
    (by simp only [form_apply]; decide)

theorem commuting_neg_r1_a2v : Commuting (F.X (-r1)) (F.X a2v) :=
  commuting_of_form (isLong_r1 (F := F)).neg.mem_roots (a2v_mem_roots F.hA) (by decide) (by decide)
    (by rw [form_apply]; decide) (by rw [form_apply]; decide) (by rw [form_apply]; decide)
    (by simp only [form_apply]; decide)

theorem commuting_r3_a2v : Commuting (F.X r3) (F.X a2v) :=
  commuting_of_form (isLong_r3 (F := F)).mem_roots (a2v_mem_roots F.hA) (by decide) (by decide)
    (by rw [form_apply]; decide) (by rw [form_apply]; decide) (by rw [form_apply]; decide)
    (by simp only [form_apply]; decide)

theorem commuting_r3_s12 : Commuting (F.X r3) (F.X s12) :=
  commuting_of_form (isLong_r3 (F := F)).mem_roots (s12_mem_roots F.hA) (by decide) (by decide)
    (by rw [form_apply]; decide) (by rw [form_apply]; decide) (by rw [form_apply]; decide)
    (by simp only [form_apply]; decide)

theorem commuting_r3_r2 : Commuting (F.X r3) (F.X r2) :=
  commuting_long (isLong_r3 (F := F)) isLong_r2 (by rw [form_apply]; decide) (by decide)

theorem commuting_r3_neg_r2 : Commuting (F.X r3) (F.X (-r2)) :=
  commuting_long (isLong_r3 (F := F)) isLong_r2.neg (by rw [form_apply]; decide) (by decide)

theorem commutator_mem_sup {c x : F.K} (hc : c ∈ F.X a2v) (hx : x ∈ F.X r2) :
    ⁅c, x⁆ ∈ F.X s12 ⊔ F.X r3 := by
  have h2 := (isLong_r2 (F := F)).mem_roots
  have hind : LinIndepPair a2v r2 :=
    linIndepPair_of_ne F.hA (a2v_mem_roots F.hA) h2 (by decide) (by decide)
  refine (iSup₂_le fun ε hε => ?_ :
    (⨆ ε ∈ openCone F.D.roots a2v r2, F.D.rootGroup ε) ≤ F.X s12 ⊔ F.X r3)
    (F.hext.commutator_mem a2v (a2v_mem_roots F.hA) r2 h2 hind c hc x hx)
  rcases eq_of_mem_openCone_shortLong F.hA (by rw [form_apply]; decide)
    (by rw [form_apply]; decide) (by rw [form_apply]; decide) hε with h | h
  · rw [h, show a2v + r2 = s12 by decide]
    exact le_sup_left
  · rw [h, show 2 • a2v + r2 = r3 by decide]
    exact le_sup_right

theorem ht_r2_pos : 0 < ht r2 := by decide

theorem eq_one_of_conj_mem_posUnipotent {g : F.K} {w : (coxeterMatrix F.hA).Group}
    (hg : ActsAs F.D g w) {γ : Fin 4 → ℤ} (hγ : γ ∈ roots F.hA ∅) {y : F.K} (hy : y ∈ F.X γ)
    (hneg : ht (weylAction F.hA w γ) < 0) (hpos : g * y * g⁻¹ ∈ posUnipotent F.D) : y = 1 := by
  have hneg' : g * y * g⁻¹ ∈ negUnipotent F.D :=
    rootGroup_le_negUnipotent (weylAction_mem_roots _ w hγ) hneg (hg.conj_mem hγ hy)
  have h1 : g * y * g⁻¹ ∈ posUnipotent F.D ⊓ negUnipotent F.D := Subgroup.mem_inf.mpr ⟨hpos, hneg'⟩
  rw [posUnipotent_inf_negUnipotent F.hext, Subgroup.mem_bot, conj_eq_one_iff] at h1
  exact h1

section Nondeg

variable {D : Set G} (hR : IsRootClass R) (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d)
include hR hRD

theorem eq_one_of_commutator_mem {c : F.K} (hc : c ∈ F.X a2v) (h : ⁅c, F.xL r2⁆ ∈ F.X r3) :
    c = 1 := by
  have hr2 := isLong_r2 (F := F)
  have hr3 := isLong_r3 (F := F)
  let S : Subgroup F.K :=
    { carrier := {g | (∀ z ∈ F.X r3, Commute g z) ∧ ⁅c, g⁆ ∈ F.X r3}
      mul_mem' := by
        rintro g g' ⟨hg1, hg2⟩ ⟨hg1', hg2'⟩
        refine ⟨fun z hz => (hg1 z hz).mul_left (hg1' z hz), ?_⟩
        have e : ⁅c, g * g'⁆ = ⁅c, g⁆ * (g * ⁅c, g'⁆ * g⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e, (hg1 _ hg2').eq, mul_inv_cancel_right]
        exact mul_mem hg2 hg2'
      one_mem' := ⟨fun z _ => Commute.one_left z, by
        rw [commutatorElement_one_right]
        exact one_mem _⟩
      inv_mem' := by
        rintro g ⟨hg1, hg2⟩
        refine ⟨fun z hz => (hg1 z hz).inv_left, ?_⟩
        have e : ⁅c, g⁻¹⁆ = g⁻¹ * ⁅c, g⁆⁻¹ * g := by
          simp only [commutatorElement_def]
          group
        rw [e, mul_assoc, ← (hg1 _ (inv_mem hg2)).eq, inv_mul_cancel_left]
        exact inv_mem hg2 }
  have hS : CFSG.LieType.CurtisTits.rankOne F.X 1 ≤ S := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · rw [show (Pi.single 1 1 : Fin 4 → ℤ) = r2 by decide] at hg
      rcases (mem_rootGroup_iff hR hRD hr2).1 hg with rfl | rfl
      · exact S.one_mem
      · exact ⟨fun z hz => (commuting_r3_r2 z hz _ hg).symm, h⟩
    · rw [show (-Pi.single 1 1 : Fin 4 → ℤ) = -r2 by decide] at hg
      refine ⟨fun z hz => (commuting_r3_neg_r2 z hz _ hg).symm, ?_⟩
      rw [commutatorElement_eq_one_iff_commute.2 (commuting_neg_r2_a2v _ hg _ hc).symm]
      exact one_mem _
  obtain ⟨-, hz₀⟩ : F.n 1 ∈ S := hS (F.hct.n_mem 1)
  have he : F.n 1 * c * (F.n 1)⁻¹ ∈ F.X s12 := by
    rw [rootGroup_s12]
    exact conj_mem_map_conj hc
  have he' : F.n 1 * c * (F.n 1)⁻¹ = ⁅c, F.n 1⁆⁻¹ * c := by
    simp only [commutatorElement_def]
    group
  have hm := actsAs_nrep (F := F) (F.s 2 * F.s 1)
  have hw1 : weylAction F.hA (F.s 2 * F.s 1) s12 = -a2v := by
    rw [weylAction_mul_apply, weylAction_simple_eq, weylAction_simple_eq]; decide
  have hw2 : weylAction F.hA (F.s 2 * F.s 1) r3 = r2 := by
    rw [weylAction_mul_apply, weylAction_simple_eq, weylAction_simple_eq]; decide
  have hw3 : weylAction F.hA (F.s 2 * F.s 1) a2v = s12 := by
    rw [weylAction_mul_apply, weylAction_simple_eq, weylAction_simple_eq]; decide
  have h1 : F.n 1 * c * (F.n 1)⁻¹ = 1 := by
    refine eq_one_of_conj_mem_posUnipotent hm (s12_mem_roots F.hA) he
      (by rw [hw1]; exact (by decide : ht (-a2v : Fin 4 → ℤ) < 0)) ?_
    rw [he']
    set m := nrep F.hct (F.s 2 * F.s 1)
    have e : m * (⁅c, F.n 1⁆⁻¹ * c) * m⁻¹ = (m * ⁅c, F.n 1⁆⁻¹ * m⁻¹) * (m * c * m⁻¹) := by
      group
    rw [e]
    have hz := hm.conj_mem hr3.mem_roots (inv_mem hz₀)
    have hc' := hm.conj_mem (a2v_mem_roots F.hA) hc
    rw [hw2] at hz
    rw [hw3] at hc'
    exact mul_mem (rootGroup_le_posUnipotent hr2.mem_roots ht_r2_pos hz)
      (rootGroup_le_posUnipotent (s12_mem_roots F.hA) (by decide : 0 < ht s12) hc')
  have hcz : c ∈ F.X r3 := by
    rw [he', inv_mul_eq_one] at h1
    rw [← h1]
    exact hz₀
  have hn2 := actsAs_n (D := F.D) F.hct 2
  refine eq_one_of_conj_mem_posUnipotent hn2 (a2v_mem_roots F.hA) hc
    (by rw [weylAction_simple_eq]; exact (by decide : ht (reflF f4M 2 a2v) < 0)) ?_
  have hz := hn2.conj_mem hr3.mem_roots hcz
  rw [weylAction_simple_eq, show reflF f4M 2 r3 = r2 by decide] at hz
  exact rootGroup_le_posUnipotent hr2.mem_roots ht_r2_pos hz

end Nondeg

theorem commutatorElement_inv_mul_eq {K : Type*} [Group K] {c c' x z z' : K}
    (h : ⁅c, x⁆ * z = ⁅c', x⁆ * z') (hxw : x * (z' * z⁻¹) = z' * z⁻¹ * x)
    (hcw : c' * (z' * z⁻¹) = z' * z⁻¹ * c') : ⁅c'⁻¹ * c, x⁆ = z' * z⁻¹ := by
  set w := z' * z⁻¹
  have h' : c * x * c⁻¹ * x⁻¹ * z = c' * x * c'⁻¹ * x⁻¹ * z' := by
    simpa only [commutatorElement_def] using h
  have hcx : c * x * c⁻¹ = c' * x * c'⁻¹ * w := by
    calc c * x * c⁻¹ = (c * x * c⁻¹ * x⁻¹ * z) * z⁻¹ * x := by group
      _ = (c' * x * c'⁻¹ * x⁻¹ * z') * z⁻¹ * x := by rw [h']
      _ = c' * x * c'⁻¹ * x⁻¹ * (w * x) := by simp only [w]; group
      _ = c' * x * c'⁻¹ * w := by rw [← hxw]; group
  calc ⁅c'⁻¹ * c, x⁆ = c'⁻¹ * (c * x * c⁻¹) * c' * x⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = x * (c'⁻¹ * w * c') * x⁻¹ := by rw [hcx]; group
    _ = x * w * x⁻¹ := by rw [mul_assoc c'⁻¹, ← hcw, inv_mul_cancel_left]
    _ = w := by rw [hxw, mul_inv_cancel_right]

section Generation

variable {D : Set G} (hR : IsRootClass R) (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d)
include hR hRD

theorem rootGroup_s12_le [Finite G] {P : Subgroup F.K} (hPx : F.xL r2 ∈ P)
    (hPZ : F.X r3 ≤ P) (hPc : ∀ c ∈ F.X a2v, c * F.xL r2 * c⁻¹ ∈ P) : F.X s12 ≤ P := by
  have hr2 := isLong_r2 (F := F)
  have hr3 := isLong_r3 (F := F)
  have := finite_rootGroup (F := F) (s12_mem_roots F.hA)
  have := finite_rootGroup (F := F) hr3.mem_roots
  have := finite_rootGroup (F := F) (a2v_mem_roots F.hA)
  have hCA : Nat.card (F.X a2v) = Nat.card (F.X s12) := by
    rw [rootGroup_s12]
    exact (Subgroup.card_map_of_injective (MulAut.conj (F.n 1)).injective).symm
  have hAZ : ((F.X s12 ⊔ F.X r3 : Subgroup F.K) : Set F.K) =
      (F.X s12 : Set F.K) * (F.X r3 : Set F.K) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (le_normalizer_of_commuting' commuting_r3_s12)
  have : Finite (F.X s12 ⊔ F.X r3 : Subgroup F.K) := by
    have hfin : ((F.X s12 : Set F.K) * (F.X r3 : Set F.K)).Finite :=
      (Set.toFinite _).mul (Set.toFinite _)
    rw [← hAZ] at hfin
    exact hfin.to_subtype
  have hcardAZ : Nat.card (F.X s12 ⊔ F.X r3 : Subgroup F.K) ≤
      Nat.card (F.X s12) * Nat.card (F.X r3) := by
    have h := Set.natCard_mul_le (s := (F.X s12 : Set F.K)) (t := (F.X r3 : Set F.K))
    rw [← hAZ] at h
    exact h
  have hmem : ∀ c ∈ F.X a2v, ∀ z ∈ F.X r3,
      ⁅c, F.xL r2⁆ * z ∈ P ⊓ (F.X s12 ⊔ F.X r3) := fun c hc z hz => by
    refine Subgroup.mem_inf.mpr ⟨mul_mem ?_ (hPZ hz), mul_mem (commutator_mem_sup hc
      (xL_mem hr2.mem_roots)) (Subgroup.mem_sup_right hz)⟩
    rw [commutatorElement_def]
    exact mul_mem (hPc c hc) (inv_mem hPx)
  let f : F.X a2v × F.X r3 → ↥(P ⊓ (F.X s12 ⊔ F.X r3)) := fun p =>
    ⟨⁅(p.1 : F.K), F.xL r2⁆ * p.2, hmem _ p.1.2 _ p.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨c, hc⟩, ⟨z, hz⟩⟩ ⟨⟨c', hc'⟩, ⟨z', hz'⟩⟩ h
    have h' : ⁅c, F.xL r2⁆ * z = ⁅c', F.xL r2⁆ * z' := congrArg Subtype.val h
    have hw : z' * z⁻¹ ∈ F.X r3 := mul_mem hz' (inv_mem hz)
    have hcc : ⁅c'⁻¹ * c, F.xL r2⁆ = z' * z⁻¹ :=
      commutatorElement_inv_mul_eq h' (commuting_r3_r2 _ hw _ (xL_mem hr2.mem_roots)).symm.eq
        (commuting_r3_a2v _ hw _ hc').symm.eq
    have h1 := eq_one_of_commutator_mem hR hRD (mul_mem (inv_mem hc') hc) (hcc ▸ hw)
    rw [inv_mul_eq_one] at h1
    subst h1
    have h2 : z = z' := mul_left_cancel h'
    subst h2
    rfl
  have : Finite ↥(P ⊓ (F.X s12 ⊔ F.X r3)) :=
    Finite.of_injective (Subgroup.inclusion inf_le_right) (Subgroup.inclusion_injective _)
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, hCA] at h1
  have hS : P ⊓ (F.X s12 ⊔ F.X r3) = F.X s12 ⊔ F.X r3 :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (hcardAZ.trans h1)
  exact le_sup_left.trans (hS ▸ inf_le_left)

end Generation

end F4Frame

end CFSG.LargeExtraspecial.A2Mod.FrF

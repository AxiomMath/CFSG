module

public import CFSG.GH74.Generic.S1.TInvThree
public import CFSG.Walter.ReeOrder.JT.Section7E
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2

public section

open CFSG CFSG.ClassicalInvolution.WeakCT Subgroup
open scoped MatrixGroups
open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

namespace CFSG.GH74.Generic.S1

theorem isQuasisimple_range_of_ker {Q X : Type*} [Group Q] [Group X] (hQ : IsQuasisimple Q)
    (θ : Q →* X) (hker : θ.ker ≤ Subgroup.center Q) : IsQuasisimple θ.range := by
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hQ
    (θ.rangeRestrict_surjective) ?_
  by_contra hcon
  push Not at hcon
  have hall : ∀ k : Q, k ∈ Subgroup.center Q := fun k => hker (by
    rw [MonoidHom.mem_ker]
    have := hcon k
    exact congrArg Subtype.val this)
  obtain ⟨a, b, hab⟩ := hQ.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact (Subgroup.mem_center_iff.1 (hall a') b').symm

theorem quasisimple_range_center_odd {Q X : Type} [Group Q] [Finite Q] [Group X] (hQ : IsQuasisimple Q)
    (hodd : Odd (Nat.card (Subgroup.center Q))) (θ : Q →* X) (hker : θ.ker ≤ Subgroup.center Q) :
    IsQuasisimple θ.range ∧ ∀ z ∈ θ.range, (∀ w ∈ θ.range, z * w = w * z) → Odd (orderOf z) := by
  refine ⟨isQuasisimple_range_of_ker hQ θ hker, fun z hz hzc => ?_⟩
  have hcen : (⟨z, hz⟩ : ↥θ.range) ∈ Subgroup.center ↥θ.range := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g g.2).symm
  rw [CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hQ θ.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hker)] at hcen
  obtain ⟨a, ha, haz⟩ := hcen
  have hθa : θ a = z := congrArg Subtype.val haz
  have h1 : orderOf z ∣ orderOf a := hθa ▸ orderOf_map_dvd θ a
  have h2 : orderOf a ∣ Nat.card (Subgroup.center Q) := Subgroup.orderOf_dvd_natCard _ ha
  exact Odd.of_dvd_nat hodd (h1.trans h2)

section Lin

variable {F : Type} [Field F] [Finite F]

theorem lin_pair_W_facts {X : Type} [Group X] {W U V : Subgroup X}
    (hP : LinearBlockStandardPair F W U V) :
    IsQuasisimple W ∧ ∀ z ∈ W, (∀ w ∈ W, z * w = w * z) → Odd (orderOf z) := by
  obtain ⟨θ, c, hrange, hker, -⟩ := hP
  subst hrange
  exact quasisimple_range_center_odd
    (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 F
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))) odd_card_center_lin3 θ hker

omit [Finite F] in
theorem lin_pair_block {X : Type} [Group X] (θ : SL(3, F) →* X) (hker : θ.ker ≤ Subgroup.center SL(3, F))
    (c : SL(3, F)) {i : ℕ} (hi : i + 2 ≤ 3) :
    ∃ f : SL(2, F) →* X,
      f.range = ((blockSL F 3 2 i hi).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ ∧
        f.ker ≤ Subgroup.center SL(2, F) := by
  refine ⟨θ.comp ((MulAut.conj c⁻¹).toMonoidHom.comp (blockSL F 3 2 i hi)), ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_comp]
  · intro A hA
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply] at hA
    have h1 : (MulAut.conj c⁻¹).toMonoidHom (blockSL F 3 2 i hi A) ∈ Subgroup.center SL(3, F) :=
      hker (MonoidHom.mem_ker.2 hA)
    have h2 : blockSL F 3 2 i hi A ∈ Subgroup.center SL(3, F) := by
      set x := blockSL F 3 2 i hi A with hx
      set y := (MulAut.conj c⁻¹).toMonoidHom x with hy
      have hy' : y = c⁻¹ * x * c := by simp [y]
      have hcy : c * y = y * c := Subgroup.mem_center_iff.1 h1 c
      have hxy : x = y := by
        calc x = c * y * c⁻¹ := by rw [hy']; group
          _ = y * c * c⁻¹ := by rw [hcy]
          _ = y := by group
      rw [hxy]
      exact h1
    rw [Subgroup.mem_center_iff]
    intro A'
    apply blockSL_injective (K := F) hi
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 h2 (blockSL F 3 2 i hi A')

theorem lin_pair_UV_quasisimple (h4 : 3 < Nat.card F) {X : Type} [Group X] {W U V : Subgroup X}
    (hP : LinearBlockStandardPair F W U V) : IsQuasisimple U ∧ IsQuasisimple V := by
  obtain ⟨θ, c, hrange, hker, hcases⟩ := hP
  have hSL2 : IsQuasisimple SL(2, F) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2 F le_rfl
      (Or.inr (by omega)) (Or.inr (by omega))
  have hq : ∀ {i : ℕ} (hi : i + 2 ≤ 3) (T : Subgroup X),
      ((blockSL F 3 2 i hi).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ = T → IsQuasisimple T := by
    intro i hi T hT
    obtain ⟨f, hf, hfk⟩ := lin_pair_block θ hker c hi
    rw [← hT, ← hf]
    exact isQuasisimple_range_of_ker hSL2 f hfk
  have h12 : CFSG.ClassicalInvolution.WeakCT.B12 F = (blockSL F 3 2 0 (by omega)).range := rfl
  have h23 : CFSG.ClassicalInvolution.WeakCT.B23 F = (blockSL F 3 2 1 (by omega)).range := rfl
  rcases hcases with ⟨hU, hV⟩ | ⟨hV, hU⟩
  · rw [h12] at hU
    rw [h23] at hV
    exact ⟨hq _ U hU, hq _ V hV⟩
  · rw [h12] at hV
    rw [h23] at hU
    exact ⟨hq _ U hU, hq _ V hV⟩

theorem lin_pair_UV_solvable (h3 : Nat.card F = 3) {X : Type} [Group X] {W U V : Subgroup X}
    (hP : LinearBlockStandardPair F W U V) : Group.IsSolvable U ∧ Group.IsSolvable V := by
  obtain ⟨θ, c, hrange, hker, hcases⟩ := hP
  have hcard : Nat.card SL(2, F) = 2 ^ 3 * 3 ^ 1 := by
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear F 2 (by norm_num), h3]
    decide
  have hSL2 : Group.IsSolvable SL(2, F) :=
    CFSG.Walter.JT.isSolvable_of_card_eq_two_pow_mul_three_pow hcard
  have hq : ∀ {i : ℕ} (hi : i + 2 ≤ 3) (T : Subgroup X),
      ((blockSL F 3 2 i hi).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ = T →
        Group.IsSolvable T := by
    intro i hi T hT
    obtain ⟨f, hf, hfk⟩ := lin_pair_block θ hker c hi
    rw [← hT, ← hf]
    exact Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have h12 : CFSG.ClassicalInvolution.WeakCT.B12 F = (blockSL F 3 2 0 (by omega)).range := rfl
  have h23 : CFSG.ClassicalInvolution.WeakCT.B23 F = (blockSL F 3 2 1 (by omega)).range := rfl
  rcases hcases with ⟨hU, hV⟩ | ⟨hV, hU⟩
  · rw [h12] at hU
    rw [h23] at hV
    exact ⟨hq _ U hU, hq _ V hV⟩
  · rw [h12] at hV
    rw [h23] at hU
    exact ⟨hq _ U hU, hq _ V hV⟩

end Lin

section Uni

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem uni_pair_W_facts (hF : Nat.card F = (p ^ f) ^ 2) (hq : Odd (p ^ f)) {X : Type} [Group X]
    {W U V : Subgroup X} (hP : UnitaryBlockStandardPair F p f W U V) :
    IsQuasisimple W ∧ ∀ z ∈ W, (∀ w ∈ W, z * w = w * z) → Odd (orderOf z) := by
  obtain ⟨θ, c, hrange, hker, -⟩ := hP
  subst hrange
  have hnq : ((3 : ℕ), p ^ f) ≠ (3, 2) := by
    intro h'
    have : p ^ f = 2 := (Prod.mk.inj h').2
    rw [this] at hq
    exact absurd hq (by decide)
  have hodd : Odd (Nat.card (Subgroup.center (Su F p f 3))) := by
    rw [Nat.card_congr (Subgroup.centerCongr (CFSG.GH74.L5U5.suEquiv hF 3)).toEquiv]
    exact odd_card_center_uni3 hF hq
  exact quasisimple_range_center_odd (CFSG.GH74.L5U5.isQuasisimple_su hF (by norm_num) hnq) hodd θ
    hker

omit [Finite F] in
theorem isQuasisimple_su2_of_five_le [Finite F] (hF : Nat.card F = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    IsQuasisimple (Su F p f 2) := by
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.Models.nonempty_sl2_mulEquiv_su_two (K := F) (p := p)
    (f := f) hF
  have hc : Nat.card (CFSG.LieType.Steinberg.fixedSubfield F p f) = p ^ f :=
    CFSG.LieType.Steinberg.card_fixedSubfield hF
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e
    (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2 _ le_rfl
      (Or.inr (by omega)) (Or.inr (by omega)))

omit [Finite F] in
theorem uni_pair_block [Finite F] {X : Type} [Group X] (θ : Su F p f 3 →* X)
    (hker : θ.ker ≤ Subgroup.center (Su F p f 3)) (c : Su F p f 3) (i : Fin 3) :
    ∃ g : Su F p f 2 →* X,
      g.range = (((embSUid (unitaryInvolution F p f) i).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ) ∧
        g.ker ≤ Subgroup.center (Su F p f 2) := by
  refine ⟨θ.comp ((MulAut.conj c⁻¹).toMonoidHom.comp (embSUid (unitaryInvolution F p f) i)), ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_comp]
  · intro A hA
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply] at hA
    have h1 : (MulAut.conj c⁻¹).toMonoidHom (embSUid (unitaryInvolution F p f) i A) ∈
        Subgroup.center (Su F p f 3) := hker (MonoidHom.mem_ker.2 hA)
    have h2 : embSUid (unitaryInvolution F p f) i A ∈ Subgroup.center (Su F p f 3) := by
      set x := embSUid (unitaryInvolution F p f) i A with hx
      set y := (MulAut.conj c⁻¹).toMonoidHom x with hy
      have hy' : y = c⁻¹ * x * c := by simp [y]
      have hcy : c * y = y * c := Subgroup.mem_center_iff.1 h1 c
      have hxy : x = y := by
        calc x = c * y * c⁻¹ := by rw [hy']; group
          _ = y * c * c⁻¹ := by rw [hcy]
          _ = y := by group
      rw [hxy]
      exact h1
    rw [Subgroup.mem_center_iff]
    intro A'
    apply embSUid_injective (unitaryInvolution F p f) i
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 h2 (embSUid (unitaryInvolution F p f) i A')

theorem uni_pair_UV_quasisimple (hF : Nat.card F = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) {X : Type} [Group X]
    {W U V : Subgroup X} (hP : UnitaryBlockStandardPair F p f W U V) :
    IsQuasisimple U ∧ IsQuasisimple V := by
  obtain ⟨θ, c, hrange, hker, hcases⟩ := hP
  have hSu2 : IsQuasisimple (Su F p f 2) := isQuasisimple_su2_of_five_le hF hq
  have hq' : ∀ (i : Fin 3) (T : Subgroup X),
      (((embSUid (unitaryInvolution F p f) i).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ) = T →
        IsQuasisimple T := by
    intro i T hT
    obtain ⟨g, hg, hgk⟩ := uni_pair_block θ hker c i
    rw [← hT, ← hg]
    exact isQuasisimple_range_of_ker hSu2 g hgk
  have h12 : CFSG.ClassicalInvolution.Phan.B12 F p f = (embSUid (unitaryInvolution F p f) 2).range := rfl
  have h23 : CFSG.ClassicalInvolution.Phan.B23 F p f = (embSUid (unitaryInvolution F p f) 0).range := rfl
  rcases hcases with ⟨hU, hV⟩ | ⟨hV, hU⟩
  · rw [h12] at hU
    rw [h23] at hV
    exact ⟨hq' _ U hU, hq' _ V hV⟩
  · rw [h12] at hV
    rw [h23] at hU
    exact ⟨hq' _ U hU, hq' _ V hV⟩

end Uni

end CFSG.GH74.Generic.S1

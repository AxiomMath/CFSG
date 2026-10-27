module

public import CFSG.LocalAnalysis.EvenBN.U5.ModelThree
public import CFSG.LocalAnalysis.EvenBN.U5.PrelimModules
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M2

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

omit [Finite G] in
theorem lins2a_map_conj_inv_le {A B : Subgroup G} {x : G}
    (hAB : A ≤ B.map (MulAut.conj x).toMonoidHom) :
    A.map (MulAut.conj x⁻¹).toMonoidHom ≤ B := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, hb, hba⟩ := hAB ha
  rw [← hba]
  show x⁻¹ * (x * b * x⁻¹) * x⁻¹⁻¹ ∈ B
  rw [show x⁻¹ * (x * b * x⁻¹) * x⁻¹⁻¹ = b by group]
  exact hb

omit [Finite G] in
theorem lins2a_card_map_conj (A : Subgroup G) (x : G) :
    Nat.card (A.map (MulAut.conj x).toMonoidHom) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj x).injective

omit [Finite G] in
theorem lins2a_map_conj_sq {A : Subgroup G} (hA : ∀ a ∈ A, a * a = 1) (x : G) :
    ∀ y ∈ A.map (MulAut.conj x).toMonoidHom, y * y = 1 := by
  rintro _ ⟨a, ha, rfl⟩
  have h2 := hA a ha
  show x * a * x⁻¹ * (x * a * x⁻¹) = 1
  calc x * a * x⁻¹ * (x * a * x⁻¹) = x * (a * a) * x⁻¹ := by group
    _ = 1 := by rw [h2]; group

theorem lins2a_lt_pow_three {q : ℕ} (hq : 1 < q) : q < q ^ 3 :=
  calc q = q ^ 1 := (pow_one q).symm
    _ < q ^ 3 := Nat.pow_lt_pow_right hq (by norm_num)

theorem lin_exists_z₂ (hd : d.Hyp) :
    ∃ z : G, z ∈ d.N₂ ∧ z ∈ d.P ∧ z ∈ d.A₃ ∧ z * z ≠ 1 := by
  have hcard : Nat.card d.CPI₂ = (2 ^ f) ^ 3 :=
    (d.card_pull (patSub_le_U sI₂ isPattern_sI₂)).trans card_patSub_sI₂
  have h4 := hd.four_le
  by_contra hne
  have hall : ∀ z, z ∈ d.N₂ → z ∈ d.P → z ∈ d.A₃ → z * z = 1 := fun z h1 h2 h3 =>
    Classical.byContradiction fun hz => hne ⟨z, h1, h2, h3, hz⟩
  have hsq : ∀ z ∈ d.CPI₂, z * z = 1 := fun z hz =>
    hall z (d.pull_mono patSub_sI₂_le_N₂sub hz) (d.pull_mono (patSub_le_U _ _) hz)
      (d.pull_mono patSub_I₂_le_Ssub hz)
  have hsub : d.CPI₂ ≤ Subgroup.closure {x | x ∈ d.CPI₂ ∧ x * x = 1} := by
    intro z hz
    exact Subgroup.subset_closure ⟨hz, hsq z hz⟩
  have hle := Subgroup.card_le_of_le (hsub.trans d.closure_involutions_CPI₂.1.le)
  rw [hcard, d.card_CPI₆] at hle
  exact absurd hle (not_le.2 (lins2a_lt_pow_three (lt_of_lt_of_le (by norm_num) h4)))

theorem lin_card_le_of_sq_N₂ (hd : d.Hyp) {X : Subgroup G} (hX : X ≤ d.N₂)
    (hX2 : ∀ x ∈ X, x * x = 1) : Nat.card X ≤ 2 ^ f := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 X := isPGroup_iff_pow_pow_eq_one.2 fun g => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (hX2 _ g.2)⟩
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := d.N₂)).exists_le_sylow
  have hT : IsSylowOf 2 ((Q : Subgroup d.N₂).map d.N₂.subtype) d.N₂ := ⟨Q, rfl⟩
  have hXT : X ≤ (Q : Subgroup d.N₂).map d.N₂.subtype :=
    fun x hx => ⟨⟨x, hX hx⟩, hQ hx, rfl⟩
  obtain ⟨g, -, hg⟩ := CFSG.LocalAnalysis.EvenBN.U5.Prelim.exists_conj_of_isSylowOf
    d.isSylowOf_N₂_inf_P.2 hT
  have hX' : X ≤ d.CPI₂.map (MulAut.conj g).toMonoidHom := hXT.trans hg.le
  have hle : X.map (MulAut.conj g⁻¹).toMonoidHom ≤ d.CPI₂ := lins2a_map_conj_inv_le hX'
  have hle6 : X.map (MulAut.conj g⁻¹).toMonoidHom ≤ d.CPI₆ := by
    rw [← d.closure_involutions_CPI₂.1]
    intro y hy
    exact Subgroup.subset_closure ⟨hle hy, lins2a_map_conj_sq hX2 g⁻¹ y hy⟩
  calc Nat.card X = Nat.card (X.map (MulAut.conj g⁻¹).toMonoidHom) :=
        (lins2a_card_map_conj X g⁻¹).symm
    _ ≤ Nat.card d.CPI₆ := Subgroup.card_le_of_le hle6
    _ = 2 ^ f := d.card_CPI₆

theorem lin_exists_z₅ (hd : d.Hyp) :
    ∃ z : G, z ∈ d.N₅ ∧ z ∈ d.A₂ ∧ z ∈ d.A₃ ∧ z ∈ centralizer (d.I₅ : Set G) ∧ z * z ≠ 1 := by
  have hmem : ∀ z ∈ d.P ⊓ centralizer (d.I₅ : Set G), z ∈ d.N₅ ∧ z ∈ d.A₂ ∧ z ∈ d.A₃ ∧
      z ∈ centralizer (d.I₅ : Set G) := by
    intro z hz
    have hz' : z ∈ d.pull (patSub h sI₅ isPattern_sI₅) := hd.P_inf_centralizer_I₅ ▸ hz
    exact ⟨d.C₅_le_N₅ hz', d.pull_mono (patSub_I₅_le_A₂sub_inf_Ssub.trans inf_le_left) hz',
      d.pull_mono (patSub_I₅_le_A₂sub_inf_Ssub.trans inf_le_right) hz', hz.2⟩
  have hcard := hd.card_C₅
  have h4 := hd.four_le
  by_contra hne
  have hsq : ∀ z ∈ d.P ⊓ centralizer (d.I₅ : Set G), z * z = 1 := fun z hz =>
    Classical.byContradiction fun h5 =>
      hne ⟨z, (hmem z hz).1, (hmem z hz).2.1, (hmem z hz).2.2.1, (hmem z hz).2.2.2, h5⟩
  have hC5 : d.P ⊓ centralizer (d.I₅ : Set G) ≤ d.N₂.map (MulAut.conj d.r).toMonoidHom :=
    fun z hz => by
      have hzN := (hmem z hz).1
      rwa [d.N₅_eq] at hzN
  have hle := lin_card_le_of_sq_N₂ hd (lins2a_map_conj_inv_le hC5)
    (lins2a_map_conj_sq hsq d.r⁻¹)
  rw [lins2a_card_map_conj, hcard] at hle
  exact absurd hle (not_le.2 (lins2a_lt_pow_three (lt_of_lt_of_le (by norm_num) h4)))

end Data

end CFSG.LocalAnalysis.EvenBN.U5

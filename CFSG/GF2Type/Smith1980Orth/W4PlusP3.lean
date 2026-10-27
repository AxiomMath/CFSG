module

public import CFSG.GF2Type.Smith1980Orth.S2Seven
public import CFSG.GF2Type.Smith1980Orth.OEight

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G] {S : Setting G}

section Linear

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem two_le_finrank_of_ne {U : Submodule (ZMod 2) V} {a b : V} (ha : a ∈ U)
    (hb : b ∈ U) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b) : 2 ≤ finrank (ZMod 2) U := by
  by_contra h
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp (by omega : finrank (ZMod 2) U ≤ 1)
  obtain ⟨c₁, h₁⟩ := hv ⟨a, ha⟩
  obtain ⟨c₂, h₂⟩ := hv ⟨b, hb⟩
  have key : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases key c₁ with rfl | rfl
  · exact ha0 (by simpa using (congrArg Subtype.val h₁).symm)
  rcases key c₂ with rfl | rfl
  · exact hb0 (by simpa using (congrArg Subtype.val h₂).symm)
  exact hab (by simpa using (congrArg Subtype.val h₁).symm.trans (congrArg Subtype.val h₂))

end Linear

namespace S2Data

variable {M1 : Subgroup S.O} (D : S2Data S M1)

include D in
private theorem two_le_finrank_of_section {N : Submodule (ZMod 2) S.Qt} {σ₁ σ₂ : Vt S D.g D.t}
    (ι : Vt S D.g D.t → S.Qt) (π : S.Qt →ₗ[ZMod 2] Vt S D.g D.t) (hπ : ∀ u, π (ι u) = u)
    (hN : ∀ u, D.betaV σ₁ u = 0 → D.betaV σ₂ u = 0 → ι u ∈ N) :
    2 ≤ finrank (ZMod 2) N := by
  obtain ⟨f, hf⟩ : ∃ f : Vt S D.g D.t →ₗ[ZMod 2] ZMod 2 × ZMod 2,
      f = (D.betaV σ₁).prod (D.betaV σ₂) := ⟨_, rfl⟩
  have h1 : finrank (ZMod 2) (LinearMap.range f) ≤ 2 := by
    calc finrank (ZMod 2) (LinearMap.range f) ≤ finrank (ZMod 2) (ZMod 2 × ZMod 2) :=
        Submodule.finrank_le _
      _ = 2 := by simp
  have h2 := f.finrank_range_add_finrank_ker
  have h3 := D.finrank_Vt
  have h4 := D.four_le
  have hK : LinearMap.ker f ≤ N.map π := by
    intro u hu
    have h := LinearMap.mem_ker.mp hu
    rw [hf, LinearMap.prod_apply, Prod.mk_eq_zero] at h
    exact ⟨ι u, hN u h.1 h.2, hπ u⟩
  calc 2 ≤ finrank (ZMod 2) (LinearMap.ker f) := by omega
    _ ≤ finrank (ZMod 2) (N.map π) := Submodule.finrank_mono hK
    _ ≤ finrank (ZMod 2) N := Submodule.finrank_map_le π N

include D in
private theorem two_le_finrank_Pfst_inf_Pfst (σ₁ σ₂ : Vt S D.g D.t) :
    2 ≤ finrank (ZMod 2) (D.Pfst σ₁ ⊓ D.Pfst σ₂ : Submodule (ZMod 2) S.Qt) := by
  refine D.two_le_finrank_of_section (σ₁ := σ₁) (σ₂ := σ₂) (fun u => D.coord (u, 0))
    ((LinearMap.fst (ZMod 2) (Vt S D.g D.t) (Vt S D.g D.t)).comp D.coord.symm.toLinearMap)
    (fun u => by simp) ?_
  intro u h1 h2
  exact ⟨D.mem_Pfst_iff.mpr ⟨u, 0, h1, by rw [zero_smul]⟩,
    D.mem_Pfst_iff.mpr ⟨u, 0, h2, by rw [zero_smul]⟩⟩

include D in
private theorem two_le_finrank_Psnd_inf_Psnd (σ₁ σ₂ : Vt S D.g D.t) :
    2 ≤ finrank (ZMod 2) (D.Psnd σ₁ ⊓ D.Psnd σ₂ : Submodule (ZMod 2) S.Qt) := by
  refine D.two_le_finrank_of_section (σ₁ := σ₁) (σ₂ := σ₂) (fun u => D.coord (0, u))
    ((LinearMap.snd (ZMod 2) (Vt S D.g D.t) (Vt S D.g D.t)).comp D.coord.symm.toLinearMap)
    (fun u => by simp) ?_
  intro u h1 h2
  exact ⟨D.mem_Psnd_iff.mpr ⟨u, 0, h1, by rw [zero_smul, add_zero]⟩,
    D.mem_Psnd_iff.mpr ⟨u, 0, h2, by rw [zero_smul, add_zero]⟩⟩

include D in
private theorem two_le_finrank_Pdiag_inf_Pdiag (σ₁ σ₂ : Vt S D.g D.t) :
    2 ≤ finrank (ZMod 2) (D.Pdiag σ₁ ⊓ D.Pdiag σ₂ : Submodule (ZMod 2) S.Qt) := by
  refine D.two_le_finrank_of_section (σ₁ := σ₁) (σ₂ := σ₂) (fun u => D.coord (u, u))
    ((LinearMap.fst (ZMod 2) (Vt S D.g D.t) (Vt S D.g D.t)).comp D.coord.symm.toLinearMap)
    (fun u => by simp) ?_
  intro u h1 h2
  exact ⟨D.mem_Pdiag_iff.mpr ⟨u, 0, h1, by rw [zero_smul, add_zero]⟩,
    D.mem_Pdiag_iff.mpr ⟨u, 0, h2, by rw [zero_smul, add_zero]⟩⟩

include D in
private theorem two_le_finrank_Pfst_inf_Psnd {σ₁ σ₂ : Vt S D.g D.t} (h₁ : σ₁ ≠ 0) (h₂ : σ₂ ≠ 0)
    (hβ : D.betaV σ₁ σ₂ = 0) :
    2 ≤ finrank (ZMod 2) (D.Pfst σ₁ ⊓ D.Psnd σ₂ : Submodule (ZMod 2) S.Qt) := by
  have hβ' : D.betaV σ₂ σ₁ = 0 := by rw [D.betaV_symm]; exact hβ
  refine two_le_finrank_of_ne (a := D.coord (σ₂, 0)) (b := D.coord (0, σ₁)) ?_ ?_ ?_ ?_ ?_
  · exact ⟨D.mem_Pfst_iff.mpr ⟨σ₂, 0, hβ, by rw [zero_smul]⟩,
      D.mem_Psnd_iff.mpr ⟨σ₂, 1, D.betaV_isAlt σ₂, by rw [one_smul, OrthoF2.vec_add_self]⟩⟩
  · exact ⟨D.mem_Pfst_iff.mpr ⟨0, 1, map_zero _, by rw [one_smul]⟩,
      D.mem_Psnd_iff.mpr ⟨σ₁, 0, hβ', by rw [zero_smul, add_zero]⟩⟩
  · exact fun h => h₂ (congrArg Prod.fst ((D.coord.map_eq_zero_iff).mp h))
  · exact fun h => h₁ (congrArg Prod.snd ((D.coord.map_eq_zero_iff).mp h))
  · exact fun h => h₂ (congrArg Prod.fst (D.coord.injective h))

include D in
private theorem two_le_finrank_Pfst_inf_Pdiag {σ₁ σ₂ : Vt S D.g D.t} (h₁ : σ₁ ≠ 0) (h₂ : σ₂ ≠ 0)
    (hβ : D.betaV σ₁ σ₂ = 0) :
    2 ≤ finrank (ZMod 2) (D.Pfst σ₁ ⊓ D.Pdiag σ₂ : Submodule (ZMod 2) S.Qt) := by
  have hβ' : D.betaV σ₂ σ₁ = 0 := by rw [D.betaV_symm]; exact hβ
  refine two_le_finrank_of_ne (a := D.coord (σ₂, 0)) (b := D.coord (σ₁, σ₁)) ?_ ?_ ?_ ?_ ?_
  · exact ⟨D.mem_Pfst_iff.mpr ⟨σ₂, 0, hβ, by rw [zero_smul]⟩,
      D.mem_Pdiag_iff.mpr ⟨0, 1, map_zero _, by rw [one_smul, zero_add]⟩⟩
  · exact ⟨D.mem_Pfst_iff.mpr ⟨σ₁, 1, D.betaV_isAlt σ₁, by rw [one_smul]⟩,
      D.mem_Pdiag_iff.mpr ⟨σ₁, 0, hβ', by rw [zero_smul, add_zero]⟩⟩
  · exact fun h => h₂ (congrArg Prod.fst ((D.coord.map_eq_zero_iff).mp h))
  · exact fun h => h₁ (congrArg Prod.fst ((D.coord.map_eq_zero_iff).mp h))
  · exact fun h => h₁ (congrArg Prod.snd (D.coord.injective h)).symm

include D in
private theorem two_le_finrank_Psnd_inf_Pdiag {σ₁ σ₂ : Vt S D.g D.t} (h₁ : σ₁ ≠ 0) (h₂ : σ₂ ≠ 0)
    (hβ : D.betaV σ₁ σ₂ = 0) :
    2 ≤ finrank (ZMod 2) (D.Psnd σ₁ ⊓ D.Pdiag σ₂ : Submodule (ZMod 2) S.Qt) := by
  have hβ' : D.betaV σ₂ σ₁ = 0 := by rw [D.betaV_symm]; exact hβ
  refine two_le_finrank_of_ne (a := D.coord (0, σ₂)) (b := D.coord (σ₁, σ₁)) ?_ ?_ ?_ ?_ ?_
  · exact ⟨D.mem_Psnd_iff.mpr ⟨σ₂, 0, hβ, by rw [zero_smul, add_zero]⟩,
      D.mem_Pdiag_iff.mpr ⟨σ₂, 1, D.betaV_isAlt σ₂, by rw [one_smul, OrthoF2.vec_add_self]⟩⟩
  · exact ⟨D.mem_Psnd_iff.mpr ⟨0, 1, map_zero _, by rw [one_smul, zero_add]⟩,
      D.mem_Pdiag_iff.mpr ⟨σ₁, 0, hβ', by rw [zero_smul, add_zero]⟩⟩
  · exact fun h => h₂ (congrArg Prod.snd ((D.coord.map_eq_zero_iff).mp h))
  · exact fun h => h₁ (congrArg Prod.fst ((D.coord.map_eq_zero_iff).mp h))
  · exact fun h => h₁ (congrArg Prod.fst (D.coord.injective h)).symm

include D in
private theorem two_le_finrank_inf_clSub {h₁ h₂ : G} (hQ₁ : h₁ * S.z * h₁⁻¹ ∈ S.QG)
    (hne₁ : h₁ * S.z * h₁⁻¹ ≠ S.z) (hQ₂ : h₂ * S.z * h₂⁻¹ ∈ S.QG)
    (hne₂ : h₂ * S.z * h₂⁻¹ ≠ S.z)
    (hcomm : h₁ * S.z * h₁⁻¹ * (h₂ * S.z * h₂⁻¹) = h₂ * S.z * h₂⁻¹ * (h₁ * S.z * h₁⁻¹)) :
    2 ≤ finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa h₁) ⊓ S.clSub (S.QG ⊓ S.Qa h₂) :
      Submodule (ZMod 2) S.Qt) := by
  obtain ⟨σ₁, hσ₁, -, hc₁⟩ := (D.isConj_z_iff_coord hQ₁ hne₁).mp (isConj_iff.mpr ⟨h₁, rfl⟩)
  obtain ⟨σ₂, hσ₂, -, hc₂⟩ := (D.isConj_z_iff_coord hQ₂ hne₂).mp (isConj_iff.mpr ⟨h₂, rfl⟩)
  rcases hc₁ with hc₁ | hc₁ | hc₁ <;> rcases hc₂ with hc₂ | hc₂ | hc₂
  ·
    rw [D.clSub_QG_inf_Qa_eq_Pfst hQ₁ hne₁ hc₁, D.clSub_QG_inf_Qa_eq_Pfst hQ₂ hne₂ hc₂]
    exact D.two_le_finrank_Pfst_inf_Pfst σ₁ σ₂
  ·
    have hβ : D.betaV σ₁ σ₂ = 0 := by
      simpa using (D.commute_iff_coord hQ₁ hQ₂ hc₁ hc₂).mp hcomm
    rw [D.clSub_QG_inf_Qa_eq_Pfst hQ₁ hne₁ hc₁, D.clSub_QG_inf_Qa_eq_Psnd hQ₂ hne₂ hc₂]
    exact D.two_le_finrank_Pfst_inf_Psnd hσ₁ hσ₂ hβ
  ·
    have hβ : D.betaV σ₁ σ₂ = 0 := by
      simpa using (D.commute_iff_coord hQ₁ hQ₂ hc₁ hc₂).mp hcomm
    rw [D.clSub_QG_inf_Qa_eq_Pfst hQ₁ hne₁ hc₁, D.clSub_QG_inf_Qa_eq_Pdiag hQ₂ hne₂ hc₂]
    exact D.two_le_finrank_Pfst_inf_Pdiag hσ₁ hσ₂ hβ
  ·
    have hβ : D.betaV σ₂ σ₁ = 0 := by
      rw [D.betaV_symm]
      simpa using (D.commute_iff_coord hQ₁ hQ₂ hc₁ hc₂).mp hcomm
    rw [D.clSub_QG_inf_Qa_eq_Psnd hQ₁ hne₁ hc₁, D.clSub_QG_inf_Qa_eq_Pfst hQ₂ hne₂ hc₂, inf_comm]
    exact D.two_le_finrank_Pfst_inf_Psnd hσ₂ hσ₁ hβ
  ·
    rw [D.clSub_QG_inf_Qa_eq_Psnd hQ₁ hne₁ hc₁, D.clSub_QG_inf_Qa_eq_Psnd hQ₂ hne₂ hc₂]
    exact D.two_le_finrank_Psnd_inf_Psnd σ₁ σ₂
  ·
    have hβ : D.betaV σ₁ σ₂ = 0 := by
      simpa using (D.commute_iff_coord hQ₁ hQ₂ hc₁ hc₂).mp hcomm
    rw [D.clSub_QG_inf_Qa_eq_Psnd hQ₁ hne₁ hc₁, D.clSub_QG_inf_Qa_eq_Pdiag hQ₂ hne₂ hc₂]
    exact D.two_le_finrank_Psnd_inf_Pdiag hσ₁ hσ₂ hβ
  ·
    have hβ : D.betaV σ₂ σ₁ = 0 := by
      rw [D.betaV_symm]
      simpa using (D.commute_iff_coord hQ₁ hQ₂ hc₁ hc₂).mp hcomm
    rw [D.clSub_QG_inf_Qa_eq_Pdiag hQ₁ hne₁ hc₁, D.clSub_QG_inf_Qa_eq_Pfst hQ₂ hne₂ hc₂, inf_comm]
    exact D.two_le_finrank_Pfst_inf_Pdiag hσ₂ hσ₁ hβ
  ·
    have hβ : D.betaV σ₂ σ₁ = 0 := by
      rw [D.betaV_symm]
      simpa using (D.commute_iff_coord hQ₁ hQ₂ hc₁ hc₂).mp hcomm
    rw [D.clSub_QG_inf_Qa_eq_Pdiag hQ₁ hne₁ hc₁, D.clSub_QG_inf_Qa_eq_Psnd hQ₂ hne₂ hc₂, inf_comm]
    exact D.two_le_finrank_Psnd_inf_Pdiag hσ₂ hσ₁ hβ
  ·
    rw [D.clSub_QG_inf_Qa_eq_Pdiag hQ₁ hne₁ hc₁, D.clSub_QG_inf_Qa_eq_Pdiag hQ₂ hne₂ hc₂]
    exact D.two_le_finrank_Pdiag_inf_Pdiag σ₁ σ₂

include D in
private theorem eight_le_card_Qa_inf_Qa {h₁ h₂ : G} (hQ₁ : h₁ * S.z * h₁⁻¹ ∈ S.QG)
    (hne₁ : h₁ * S.z * h₁⁻¹ ≠ S.z) (hQ₂ : h₂ * S.z * h₂⁻¹ ∈ S.QG)
    (hne₂ : h₂ * S.z * h₂⁻¹ ≠ S.z)
    (hcomm : h₁ * S.z * h₁⁻¹ * (h₂ * S.z * h₂⁻¹) = h₂ * S.z * h₂⁻¹ * (h₁ * S.z * h₁⁻¹)) :
    8 ≤ Nat.card (S.Qa h₁ ⊓ S.Qa h₂ : Subgroup G) := by
  obtain ⟨W, hW⟩ : ∃ W : Submodule (ZMod 2) S.Qt,
      W = S.clSub (S.QG ⊓ S.Qa h₁) ⊓ S.clSub (S.QG ⊓ S.Qa h₂) := ⟨_, rfl⟩
  have hfin : 2 ≤ finrank (ZMod 2) W := by
    rw [hW]
    exact D.two_le_finrank_inf_clSub hQ₁ hne₁ hQ₂ hne₂ hcomm
  have hz₁ : S.z ∈ S.QG ⊓ S.Qa h₁ := ⟨S.z_mem_QG, S.z_mem_Qa hQ₁ hne₁⟩
  have hz₂ : S.z ∈ S.QG ⊓ S.Qa h₂ := ⟨S.z_mem_QG, S.z_mem_Qa hQ₂ hne₂⟩
  have hle : S.clPre W ≤ S.Qa h₁ ⊓ S.Qa h₂ := by
    intro y hy
    rw [hW] at hy
    have e₁ : y ∈ S.clPre (S.clSub (S.QG ⊓ S.Qa h₁)) := S.clPre_mono inf_le_left hy
    have e₂ : y ∈ S.clPre (S.clSub (S.QG ⊓ S.Qa h₂)) := S.clPre_mono inf_le_right hy
    rw [S.clPre_clSub inf_le_left hz₁] at e₁
    rw [S.clPre_clSub inf_le_left hz₂] at e₂
    exact ⟨e₁.2, e₂.2⟩
  calc 8 = 2 * 2 ^ 2 := by norm_num
    _ ≤ 2 * 2 ^ finrank (ZMod 2) W :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) hfin)
    _ = 2 * Nat.card W := by rw [S.card_submodule]
    _ = Nat.card (S.clPre W) := (S.card_clPre W).symm
    _ ≤ Nat.card (S.Qa h₁ ⊓ S.Qa h₂ : Subgroup G) := Subgroup.card_le_of_le hle

include D in
theorem oEight : OEight S :=
  fun h₁ h₂ hQ₁ hne₁ hQ₂ hne₂ hcomm =>
    D.eight_le_card_Qa_inf_Qa hQ₁ hne₁ hQ₂ hne₂ hcomm

end S2Data

theorem eight_le_card_QG_inf_Qa {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (DT : S2Data (S.conjBy g)) {k : G}
    (hxM : k * S.z * k⁻¹ ∈ S.M) (hxQ : k * S.z * k⁻¹ ∉ S.QG) (hxa : k * S.z * k⁻¹ ∈ S.Qa g) :
    8 ≤ Nat.card (S.QG ⊓ S.Qa k : Subgroup G) := by
  have e₁ : g⁻¹ * (S.conjBy g).z * g⁻¹⁻¹ = S.z := by rw [S.conjBy_z]; group
  have e₂ : k * g⁻¹ * (S.conjBy g).z * (k * g⁻¹)⁻¹ = k * S.z * k⁻¹ := by
    rw [S.conjBy_z]; group
  have hz : S.z ∈ (S.conjBy g).QG := S.z_mem_Qa haQ hne
  have hne₂ : k * S.z * k⁻¹ ≠ (S.conjBy g).z := fun h => hxQ (by
    have h' : k * S.z * k⁻¹ = g * S.z * g⁻¹ := h
    rw [h']
    exact haQ)
  have := DT.eight_le_card_Qa_inf_Qa (h₁ := g⁻¹) (h₂ := k * g⁻¹) (by rw [e₁]; exact hz)
    (by rw [e₁]; exact fun h => hne h.symm) (by rw [e₂]; exact hxa) (by rw [e₂]; exact hne₂)
    (by rw [e₁, e₂]; exact (S.mem_M_iff.mp hxM).symm)
  rwa [S.Qa_conjBy, S.Qa_conjBy, inv_mul_cancel, S.Qa_one, inv_mul_cancel_right] at this

end CFSG.GF2Type.Smith1980Orth

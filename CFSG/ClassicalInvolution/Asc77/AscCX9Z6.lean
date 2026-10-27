module

public import CFSG.ClassicalInvolution.Asc77.AscCX9Z5
public import CFSG.ClassicalInvolution.Asc77.AscCX9Z0

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2U

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Steinberg
  CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77.CX.MF2L (spForm famT om5Data_of_cover)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

namespace DescData

section Hom

variable {F : Type} [Field F] (D : DescData (unitaryInvolution K p f) F) {Y : Type} [Group Y]
  (θ : Su K p f 4 →* Y) (T : Subgroup Y) (hT : T = (spU (spForm D.m D.n)).map θ)

@[expose] def homTU : StatedSp 2 F →* ↥T :=
  (θ.comp D.kU).codRestrict T fun x => by
    rw [hT]
    exact Subgroup.mem_map_of_mem θ (D.kU_mem_spU x)

theorem subtype_comp_homTU : T.subtype.comp (D.homTU θ T hT) = θ.comp D.kU := rfl

theorem homTU_surjective : Function.Surjective (D.homTU θ T hT) := by
  rintro ⟨y, hy⟩
  rw [hT] at hy
  obtain ⟨s, hs, rfl⟩ := hy
  rw [← D.range_kU] at hs
  obtain ⟨x, rfl⟩ := hs
  exact ⟨x, rfl⟩

theorem ker_homTU_le_center (hker : θ.ker ≤ Subgroup.center (Su K p f 4)) :
    (D.homTU θ T hT).ker ≤ Subgroup.center (StatedSp 2 F) := by
  intro x hx
  have hx' : D.kU x ∈ θ.ker := by
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val hx
  have hc := hker hx'
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  apply D.kU_injective
  rw [map_mul, map_mul, hc (D.kU y)]

theorem block0_le (hK : Nat.card K = (p ^ f) ^ 2) :
    (blockEmb K p f 4 2 0 (by norm_num)).range ≤ spU (spForm D.m D.n) := by
  rw [← D.map_kU_longRoot0 hK, ← D.range_kU, MonoidHom.range_eq_map]
  exact Subgroup.map_mono le_top

theorem block2_le (hK : Nat.card K = (p ^ f) ^ 2) :
    (blockEmb K p f 4 2 2 (by norm_num)).range ≤ spU (spForm D.m D.n) := by
  rw [← D.map_kU_longRoot1 hK, ← D.range_kU, MonoidHom.range_eq_map]
  exact Subgroup.map_mono le_top

include hT in
theorem block0_le_T (hK : Nat.card K = (p ^ f) ^ 2) :
    (blockEmb K p f 4 2 0 (by norm_num)).range.map θ ≤ T := by
  rw [hT]
  exact Subgroup.map_mono (D.block0_le hK)

include hT in
theorem block2_le_T (hK : Nat.card K = (p ^ f) ^ 2) :
    (blockEmb K p f 4 2 2 (by norm_num)).range.map θ ≤ T := by
  rw [hT]
  exact Subgroup.map_mono (D.block2_le hK)

end Hom

section Lie


variable (D : DescData (unitaryInvolution K p f) (GaloisField p f))

theorem om5Data_T (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Y : Type}
    [Group Y] [Finite Y] (θ : Su K p f 4 →* Y) (hker : θ.ker ≤ Subgroup.center (Su K p f 4))
    (T : Subgroup Y) (hT : T = (spU (spForm D.m D.n)).map θ) {Φ : Set (Subgroup Y)}
    {z' a₀ b₀ : Y}
    (htw : TwinSect0 Φ ((blockEmb K p f 4 2 0 (by norm_num)).range.map θ)
      ((blockEmb K p f 4 2 2 (by norm_num)).range.map θ) z' a₀ b₀)
    (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) :
    C5O.Om5Data p f ↥T (famT (D.homTU θ T hT))
      (((blockEmb K p f 4 2 0 (by norm_num)).range.map θ).subgroupOf T)
      (((blockEmb K p f 4 2 2 (by norm_num)).range.map θ).subgroupOf T)
      ⟨z', D.block0_le_T θ T hT hK htw.hzA.mem⟩ ⟨a₀, D.block0_le_T θ T hT hK htw.ha₀⟩
      ⟨b₀, D.block2_le_T θ T hT hK htw.hb₀⟩ :=
  om5Data_of_cover hp2 hq T (D.homTU θ T hT) (D.homTU_surjective θ T hT)
    (D.ker_homTU_le_center θ T hT hker) (D.block0_le_T θ T hT hK) (D.block2_le_T θ T hT hK)
    (by rw [subtype_comp_homTU, ← Subgroup.map_map, D.map_kU_longRoot0 hK])
    (by rw [subtype_comp_homTU, ← Subgroup.map_map, D.map_kU_longRoot1 hK]) htw hconj

end Lie

end DescData

end CFSG.ClassicalInvolution.Asc77.CX.MF2U

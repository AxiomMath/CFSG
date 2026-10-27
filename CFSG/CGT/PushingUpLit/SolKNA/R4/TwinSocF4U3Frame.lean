module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.ClassicalInvolution.Q3.TL4MF163U3A
public import CFSG.ClassicalInvolution.Q3.TL4MF163U3F
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.U3

open CFSG CFSG.Open CFSG.ClassicalInvolution Matrix
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2 CFSG.ClassicalInvolution.Q3.TA3.Q5U3
open CFSG.ClassicalInvolution.Q3.TL4.MF163.U3
open CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK.Proofs2 CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

theorem eq_one_of_central_psu {A P : Type} [Group A] [Group P] {T : Subgroup A} [T.Normal]
    [IsSimpleGroup ↥T] (hC : Subgroup.centralizer (T : Set A) = ⊥) (E : ↥T ≃* P) {y : P}
    (hy : ∀ w : P, w * y = y * w) : y = 1 := by
  have hZT : Subgroup.center ↥T = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥T) with h0 | h0
    · exact h0
    · exfalso
      have hT1 : ∀ t : A, t ∈ T → t = 1 := fun t ht => by
        have htC : t ∈ Subgroup.centralizer (T : Set A) := by
          rw [Subgroup.mem_centralizer_iff]
          intro n hn
          have htc : (⟨t, ht⟩ : ↥T) ∈ Subgroup.center ↥T := by
            rw [h0]
            exact Subgroup.mem_top _
          exact congrArg Subtype.val (Subgroup.mem_center_iff.mp htc ⟨n, hn⟩)
        rw [hC, Subgroup.mem_bot] at htC
        exact htC
      obtain ⟨x, hx⟩ := exists_ne (1 : ↥T)
      exact hx (Subtype.ext (hT1 x.1 x.2))
  have hEy : E.symm y ∈ Subgroup.center ↥T := Subgroup.mem_center_iff.mpr fun w => by
    apply E.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy (E w)
  rw [hZT, Subgroup.mem_bot] at hEy
  rw [← E.apply_symm_apply y, hEy, map_one]

structure U3Frame {A : Type} [Group A] (T : Subgroup A) (z : A) (p f : ℕ) {K : Type} [Field K]
    (h : UnitaryFieldData p f K) where
  E : ↥T ≃* unitaryPSU h 3
  π : ↥(GU2Stated (p ^ f) K) →* A
  hrange : π.range = T ⊓ Subgroup.centralizer ({z} : Set A)
  hk : CubeKer π
  hπ1 : π ⟨-1, neg_one_mem_GU2 h⟩ = z
  hπE : ∀ (B : ↥(GU2Stated (p ^ f) K)) (hB : π B ∈ T),
    E ⟨π B, hB⟩ = ((Lemma41aU3.blkU h B : unitarySU p f K 3) : unitaryPSU h 3)

namespace U3Frame

variable {A : Type} [Group A] {T : Subgroup A} {z : A} {p f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData p f K} (F : U3Frame T z p f h)

theorem π_mem (B : ↥(GU2Stated (p ^ f) K)) : F.π B ∈ T := by
  have hB : F.π B ∈ F.π.range := ⟨B, rfl⟩
  rw [F.hrange] at hB
  exact hB.1

@[expose] def J : Subgroup A := (slPart (GU2Stated (p ^ f) K)).map F.π

end U3Frame

theorem exists_u3Frame {A : Type} [Group A] {T : Subgroup A} {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (e : ↥T ≃* StatedProj (StatedSU 3 (p ^ f) K))
    {z : A} (hzT : z ∈ T) (hz : orderOf z = 2) : Nonempty (U3Frame T z p f h) := by
  obtain ⟨c, π, hrange, hk, hπ1, hπ⟩ := exists_frame_formula h hp2 e hzT hz
  obtain ⟨E, hE⟩ := exists_std_equiv h e c hπ
  exact ⟨⟨E, π, hrange, hk, hπ1, hE⟩⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.U3

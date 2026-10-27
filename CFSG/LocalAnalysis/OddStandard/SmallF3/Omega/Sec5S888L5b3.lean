module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L5b1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L5b2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

theorem lemma54_ctx (h514 : Asc82Lemma514) (h516a : Asc82Lemma516a) (h52a : Asc82Lemma52a)
    (h37 : Asc82Lemma37) (hF3 : Asc82FactOm6CentD) (hF6 : Asc82FactOm6NRank)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {U : Subgroup G}
    (hU : U ≤ normalizer (Qsub K₁ K₂ h : Set G) ⊓ centralizer ({t} : Set G))
    (hab : IsElemAbelianModSub
      (centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h)) U) :
    (centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h)).relIndex U ≤ 8 := by
  classical
  let C := centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h)
  let C6 := Sec5C6 L K₁ K₂
  have hCU : C ⊓ U ≤ C6 ⊓ U := by
    intro x hx
    exact ⟨centralizerMod_inf_centralizer_le_C6 h514 h516a h52a hF3 c ⟨hx.1, (hU hx.2).2⟩,
      hx.2⟩
  have h_inf_eq : C ⊓ U = C ⊓ (C6 ⊓ U) := by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1, hCU hx⟩
    · intro x hx
      exact ⟨hx.1, hx.2.2⟩
  have htower := Subgroup.relIndex_mul_relIndex (H := C ⊓ U) (K := C6 ⊓ U) (L := U)
    hCU inf_le_right
  have h_eq : C.relIndex U = C.relIndex (C6 ⊓ U) * C6.relIndex U := by
    rw [← Subgroup.inf_relIndex_right C U, htower.symm, h_inf_eq,
      Subgroup.inf_relIndex_right C (C6 ⊓ U), Subgroup.inf_relIndex_right C6 U]
  calc C.relIndex U = C.relIndex (C6 ⊓ U) * C6.relIndex U := h_eq
    _ ≤ 2 * 4 := Nat.mul_le_mul
      (relIndex_inf_C6_le_two h514 h52a h37 hF3 c hU hab)
      (relIndex_C6_le_four h514 h516a h52a hF3 hF6 c hU hab)
    _ = 8 := by norm_num

end CFSG.OddStandard.SmallF3.Omega

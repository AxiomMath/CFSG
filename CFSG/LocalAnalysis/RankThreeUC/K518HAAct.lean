module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbSimpleBQAct
public import CFSG.LocalAnalysis.GLTheoremB.AutL34Bound
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open CFSG.AGLEmbeddingD2.Tits.GN516.SimpleBQ
open CFSG.LocalAnalysis.GLTheoremB (quotientCenterAut' quotientCenterAut'_injective)

variable {Y : Type} [Group Y]

@[expose] noncomputable def actQ (L : Subgroup Y) :
    ↥(Subgroup.normalizer (L : Set Y)) →* MulAut (↥L ⧸ Subgroup.center ↥L) :=
  (quotientCenterAut' ↥L).comp (actHom (le_refl (Subgroup.normalizer (L : Set Y))))

theorem actQ_mk (L : Subgroup Y) (g : ↥(Subgroup.normalizer (L : Set Y))) (x : ↥L) :
    actQ L g (QuotientGroup.mk x) =
      QuotientGroup.mk (conjAut L (g : Y) g.2 x) := by
  simp [actQ, quotientCenterAut', QuotientGroup.congr_mk, actHom]

theorem actQ_of_mem (L : Subgroup Y) (x : ↥L) :
    actQ L ⟨(x : Y), Subgroup.le_normalizer x.2⟩ = MulAut.conj (QuotientGroup.mk x) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H y =>
    rw [actQ_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subtype.ext rfl)

theorem actQ_eq_one_iff (L : Subgroup Y) (hperf : commutator ↥L = ⊤)
    (g : ↥(Subgroup.normalizer (L : Set Y))) :
    actQ L g = 1 ↔ (g : Y) ∈ Subgroup.centralizer (L : Set Y) := by
  constructor
  · intro h
    have h1 : (actHom (le_refl (Subgroup.normalizer (L : Set Y))) g : MulAut ↥L) = 1 :=
      quotientCenterAut'_injective hperf (h.trans (map_one (quotientCenterAut' ↥L)).symm)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h2 := congrArg (fun φ : MulAut ↥L => ((φ ⟨k, hk⟩ : ↥L) : Y)) h1
    simp only [coe_actHom, MulAut.one_apply] at h2
    calc k * (g : Y) = ((g : Y) * k * (g : Y)⁻¹) * (g : Y) := by rw [h2]
      _ = (g : Y) * k := by group
  · intro hg
    have h1 : (actHom (le_refl (Subgroup.normalizer (L : Set Y))) g : MulAut ↥L) = 1 := by
      ext k
      simp only [coe_actHom, MulAut.one_apply]
      have := Subgroup.mem_centralizer_iff.mp hg k k.2
      rw [← this]
      group
    show quotientCenterAut' ↥L (actHom (le_refl (Subgroup.normalizer (L : Set Y))) g) = 1
    rw [h1, map_one]

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

end

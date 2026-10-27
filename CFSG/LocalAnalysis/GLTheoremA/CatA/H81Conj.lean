module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremB.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_glaPPrimeCoreOf_iff' {p : ℕ} {J : Subgroup G} {g : G} :
    g ∈ GLAPPrimeCoreOf p J ↔ ∃ h ∈ GLAPPrimeCore p ↥J, (h : G) = g := by
  unfold GLAPPrimeCoreOf
  simp [Subgroup.mem_map]

@[expose] def conjLE (L : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)) : ↥L ≃* ↥L where
  toFun k := ⟨g * k * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg (k : G)).1 k.2⟩
  invFun k := ⟨g⁻¹ * k * g, (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * k * g)).2 (by
    simpa [mul_assoc] using k.2)⟩
  left_inv k := Subtype.ext (by simp [mul_assoc])
  right_inv k := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

@[simp] theorem conjLE_coe (L : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G))
    (k : ↥L) : ((conjLE L g hg k : ↥L) : G) = g * k * g⁻¹ := rfl

@[expose] noncomputable def alphaPQ (p : ℕ) (L : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    PQuot p L ≃* PQuot p L :=
  QuotientGroup.congr (GLAPPrimeCore p ↥L) (GLAPPrimeCore p ↥L) (conjLE L g hg)
    (pPrimeCore_map_iso p (conjLE L g hg))

theorem alphaPQ_mk (p : ℕ) (L : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G))
    (k : ↥L) :
    alphaPQ p L g hg (QuotientGroup.mk k) = QuotientGroup.mk (conjLE L g hg k) :=
  QuotientGroup.congr_mk _ _ _ _ _

theorem alphaPQ_one (p : ℕ) (L : Subgroup G) :
    alphaPQ p L 1 (Subgroup.one_mem _) = MulEquiv.refl _ := by
  refine MulEquiv.ext fun q => ?_
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  rw [alphaPQ_mk]
  congr 1
  exact Subtype.ext (by simp)

theorem alphaPQ_mul (p : ℕ) (L : Subgroup G) (g h : G) (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hh : h ∈ Subgroup.normalizer (L : Set G)) :
    alphaPQ p L (g * h) (Subgroup.mul_mem _ hg hh) = alphaPQ p L g hg * alphaPQ p L h hh := by
  refine MulEquiv.ext fun q => ?_
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  rw [alphaPQ_mk, MulAut.mul_def, MulEquiv.trans_apply, alphaPQ_mk, alphaPQ_mk]
  congr 1
  exact Subtype.ext (by simp [mul_assoc])

@[expose] noncomputable def alphaHom (p : ℕ) (L : Subgroup G) :
    ↥(Subgroup.normalizer (L : Set G)) →* MulAut (PQuot p L) where
  toFun g := alphaPQ p L g.1 g.2
  map_one' := alphaPQ_one p L
  map_mul' a b := alphaPQ_mul p L a.1 b.1 a.2 b.2

end CFSG.LocalAnalysis.GLTheoremA.H81

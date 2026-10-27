module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Basic
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Inputs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bAction
public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutB
public import CFSG.Quasithin.Recognition.St84.WeissB
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Uniq
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitNormalFour
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.LocalAnalysis.SignalizerFunctor

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] {𝕊 : Type} [Group 𝕊]

@[expose] noncomputable def act (A : Subgroup G) (ε : A ⧸ pPrimeCore 2 A ≃* 𝕊) :
    ↥(normalizer (A : Set G)) →* MulAut 𝕊 :=
  (MulAut.congr ε).toMonoidHom.comp (GSThmB.oddBarConj A)

@[expose] noncomputable def psi (A : Subgroup G) (ε : A ⧸ pPrimeCore 2 A ≃* 𝕊) : ↥A →* 𝕊 :=
  ε.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 A))

variable {A : Subgroup G} (ε : A ⧸ pPrimeCore 2 A ≃* 𝕊)

theorem psi_surjective : Function.Surjective (psi A ε) :=
  ε.surjective.comp (QuotientGroup.mk'_surjective _)

theorem psi_eq_one_iff (a : ↥A) : psi A ε a = 1 ↔ (a : G) ∈ oddCoreIn A := by
  rw [psi, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _ ε.injective,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pPrimeCore_iff_mem_oddCoreIn]

theorem act_psi (x : ↥(normalizer (A : Set G))) (a : ↥A) :
    act A ε x (psi A ε a) =
      psi A ε ⟨(x : G) * a * (x : G)⁻¹, (mem_normalizer_iff.mp x.2 a).mp a.2⟩ := by
  rw [act, psi, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [QuotientGroup.mk'_apply, GSThmB.oddBarConj_apply_mk]
  rfl

omit [Group 𝕊] in
theorem oddBarConj_eq_one {x : ↥(normalizer (A : Set G))} (hx : (x : G) ∈ coreActionKernel A) :
    GSThmB.oddBarConj A x = 1 := by
  ext y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [GSThmB.oddBarConj_apply_mk, MulAut.one_apply, QuotientGroup.eq]
  have h1 := (inv_mem hx : (x : G)⁻¹ ∈ coreActionKernel A).2 _ y.2
  rw [inv_inv] at h1
  obtain ⟨w, hw, hwe⟩ := mem_map.mp (inv_mem h1)
  convert hw using 1
  apply Subtype.ext
  rw [subtype_apply] at hwe
  rw [hwe]
  simp only [coe_mul, coe_inv]
  group

theorem act_eq_one_iff (x : ↥(normalizer (A : Set G))) :
    act A ε x = 1 ↔ (x : G) ∈ coreActionKernel A := by
  constructor
  · intro hx
    apply GSThmB.mem_coreActionKernel_of_oddBarConj_eq_one
    have h1 : (MulAut.congr ε) (GSThmB.oddBarConj A x) = 1 := hx
    rwa [map_eq_one_iff _ (MulAut.congr ε).injective] at h1
  · intro hx
    rw [act, MonoidHom.comp_apply, oddBarConj_eq_one hx, map_one]

theorem act_of_mem (a : ↥A) (ha : (a : G) ∈ normalizer (A : Set G)) :
    act A ε ⟨a, ha⟩ = MulAut.conj (psi A ε a) := by
  ext s
  obtain ⟨b, rfl⟩ := psi_surjective ε s
  rw [act_psi, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

variable [Finite G]

@[expose] noncomputable def sylowImage {R : Subgroup G} (hR : IsSylowOf 2 R A) : Sylow 2 𝕊 :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (Classical.choose hR.exists_sylow_eq_subgroupOf).mapSurjective (psi_surjective ε)

theorem coe_sylowImage {R : Subgroup G} (hR : IsSylowOf 2 R A) :
    ((sylowImage ε hR : Sylow 2 𝕊) : Subgroup 𝕊) = (R.subgroupOf A).map (psi A ε) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [sylowImage, Sylow.coe_mapSurjective, Classical.choose_spec hR.exists_sylow_eq_subgroupOf]

theorem mem_sylowImage {R : Subgroup G} (hR : IsSylowOf 2 R A) {s : 𝕊} :
    s ∈ (sylowImage ε hR : Subgroup 𝕊) ↔ ∃ r : ↥A, (r : G) ∈ R ∧ psi A ε r = s := by
  rw [coe_sylowImage, mem_map]
  exact ⟨fun ⟨r, hr, hrs⟩ => ⟨r, mem_subgroupOf.mp hr, hrs⟩,
    fun ⟨r, hr, hrs⟩ => ⟨r, mem_subgroupOf.mpr hr, hrs⟩⟩

end CFSG.ComponentClassification.Foote5

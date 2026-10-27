module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShDescent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeWSetup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.HardMathSupport.Dickson.I271.Support.OuterTransport
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.SimpleTrick

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.T171Sh CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalCores CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

theorem PreSetup.toWSetup {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G}
    {d b : G} (hpre : PreSetup p L J A d b) :
    WSetup p L J (Subgroup.zpowers d ⊔ Subgroup.zpowers b) d b := by
  have hle : Subgroup.zpowers d ⊔ Subgroup.zpowers b ≤ A :=
    sup_le (Subgroup.zpowers_le.2 hpre.d_mem) (Subgroup.zpowers_le.2 hpre.b_mem)
  have hfaithful : (Subgroup.zpowers d ⊔ Subgroup.zpowers b) ⊓
      Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff]
    exact (le_inf (inf_le_left.trans hle) inf_le_right).trans_eq hpre.faithful
  exact
    { prime := hpre.prime
      odd := hpre.odd
      qs := hpre.qs
      chev2 := hpre.chev2
      elem := hpre.elem.mono hle
      idiag := hpre.idiag₂
      faithful := hfaithful
      d_mem := Subgroup.mem_sup_left (Subgroup.mem_zpowers d)
      d_ne := hpre.d_ne
      b_mem := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
      pcomp := hpre.pcomp
      b_norm := hpre.b_norm }

theorem isComponentOf_of_isComponentOf_map_piCenterQuot {G : Type} [Group G] [Finite G]
    {p : ℕ} {L X J : Subgroup G} (hXL : X ≤ L)
    {R : Type} [Group R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {φ : MulAut R}
    (hJ : GLAPComponent p X J)
    (hT : CFSG.Open.IsComponentOf ((J.subgroupOf L).map (piCenterQuot θ))
      (fixSubgroup φ)) :
    CFSG.Open.IsComponentOf J X := by
  have hJL : J ≤ L := hJ.1.trans hXL
  let T : Subgroup R := (J.subgroupOf L).map (piCenterQuot θ)
  have hperf : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.2 (glaPComponent_perfect hJ)
  obtain ⟨f', hf'surj, hf'ker, -⟩ :=
    exists_centralSurjection hJL θ (MonoidHom.id R) (fun _ _ h => h)
      (K := T) (by rw [Subgroup.map_id])
  have hTq : CFSG.IsQuasisimple ↥T :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff ↥T).2.2.1).mpr hT.2.2
  have hJq : CFSG.IsQuasisimple ↥J :=
    (isQuasisimple_iff_of_surjective hperf f' hf'surj hf'ker).mpr hTq
  refine ⟨hJ.1, hJ.2.1, ?_⟩
  exact ((CFSG.Foundations.SteinbergCA.quasisimple_iff ↥J).2.2.1).mp hJq

theorem eq_of_isComponentOf_map_piCenterQuot_eq {G : Type} [Group G] [Finite G]
    {L X J K : Subgroup G} (hXL : X ≤ L)
    {R : Type} [Group R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    (hK : CFSG.Open.IsComponentOf K X) (hJ : CFSG.Open.IsComponentOf J X)
    (h : (K.subgroupOf L).map (piCenterQuot θ) = (J.subgroupOf L).map (piCenterQuot θ)) :
    K = J := by
  have hKL : K ≤ L := hK.1.trans hXL
  have hJL : J ≤ L := hJ.1.trans hXL
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 ⟨hK.2.2.1⟩
  have hJperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.1 ⟨hJ.2.2.1⟩
  refine le_antisymm (le_of_map_piCenterQuot_le hJL hKL hKperf θ (le_of_eq h)) ?_
  exact le_of_map_piCenterQuot_le hKL hJL hJperf θ (le_of_eq h.symm)

theorem glaLayer_eq_of_forall_map_eq {G : Type} [Group G] [Finite G]
    {L X J : Subgroup G} (hXL : X ≤ L)
    {R : Type} [Group R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    (hJ : CFSG.Open.IsComponentOf J X)
    (h : ∀ K : Subgroup G, CFSG.Open.IsComponentOf K X →
      (K.subgroupOf L).map (piCenterQuot θ) = (J.subgroupOf L).map (piCenterQuot θ)) :
    GLALayer X = J := by
  have hall : ∀ K : Subgroup G, CFSG.Open.IsComponentOf K X → K = J :=
    fun K hK => eq_of_isComponentOf_map_piCenterQuot_eq hXL θ hK hJ (h K hK)
  rw [show GLALayer X = sSup {K : Subgroup G | CFSG.Open.IsComponentOf K X} from rfl]
  refine le_antisymm (sSup_le ?_) (le_sSup hJ)
  intro K hK
  rw [hall K hK]

theorem nonempty_pSimple_equiv_of_central_surjective {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {L X J : Subgroup G} (hXL : X ≤ L)
    {R : Type} [Group R] [Finite R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {φ : MulAut R}
    (hJ : GLAPComponent p X J)
    (hJT : GLAPComponent p (fixSubgroup φ) ((J.subgroupOf L).map (piCenterQuot θ)))
    (hT : CFSG.Open.IsComponentOf ((J.subgroupOf L).map (piCenterQuot θ)) (fixSubgroup φ))
    {S : Type} [Group S]
    (g : S →* ↥((J.subgroupOf L).map (piCenterQuot θ)))
    (hg : Function.Surjective g) (hker : g.ker ≤ Subgroup.center S)
    (hS : IsSimpleGroup (S ⧸ Subgroup.center S)) :
    Nonempty (PSimple p J ≃* S ⧸ Subgroup.center S) := by
  have hJL : J ≤ L := hJ.1.trans hXL
  have hJsub : GLAPComponent p (X.subgroupOf L) (J.subgroupOf L) := by
    refine (Y10F.glaPComponent_map_iff (p := p) hp (Subgroup.subtype_injective L)).mp ?_
    rwa [Subgroup.map_subgroupOf_eq_of_le hXL, Subgroup.map_subgroupOf_eq_of_le hJL]
  obtain ⟨e1⟩ : Nonempty (PSimple p J ≃* PSimple p (J.subgroupOf L)) :=
    ⟨CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv p
      (L := J) (L' := J.subgroupOf L) (Subgroup.subgroupOfEquivOfLe hJL).symm⟩
  obtain ⟨e2⟩ : Nonempty (PSimple p (J.subgroupOf L) ≃*
      PSimple p ((J.subgroupOf L).map (piCenterQuot θ))) :=
    CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_map hp (piCenterQuot θ)
      (X := X.subgroupOf L) (Y := fixSubgroup φ) (J := J.subgroupOf L) hJsub hJT
  obtain ⟨e3⟩ : Nonempty (PSimple p ((J.subgroupOf L).map (piCenterQuot θ)) ≃*
      (↥((J.subgroupOf L).map (piCenterQuot θ)) ⧸
        Subgroup.center ↥((J.subgroupOf L).map (piCenterQuot θ)))) :=
    CFSG.LocalAnalysis.GLTheoremA.S9.nonempty_pSimple_equiv hp hJT hT.2.2
  let f : S →* (↥((J.subgroupOf L).map (piCenterQuot θ)) ⧸
      Subgroup.center ↥((J.subgroupOf L).map (piCenterQuot θ))) :=
    (QuotientGroup.mk' (Subgroup.center _)).comp g
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp hg
  have hZ : Subgroup.center S ≤ f.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff (g z)).2
      (Subgroup.map_center_le_center hg (Subgroup.mem_map_of_mem g hz))
  let φ' : (S ⧸ Subgroup.center S) →* (↥((J.subgroupOf L).map (piCenterQuot θ)) ⧸
      Subgroup.center ↥((J.subgroupOf L).map (piCenterQuot θ))) :=
    QuotientGroup.lift (Subgroup.center S) f hZ
  have hφ'surj : Function.Surjective φ' :=
    QuotientGroup.lift_surjective_of_surjective _ f hf hZ
  haveI : IsSimpleGroup (↥((J.subgroupOf L).map (piCenterQuot θ)) ⧸
      Subgroup.center ↥((J.subgroupOf L).map (piCenterQuot θ))) := hT.2.2.2
  have hφ'inj : Function.Injective φ' :=
    CFSG.QuasithinUnique.SQTK.injective_of_isSimpleGroup_of_surjective φ' hφ'surj
  obtain ⟨e4⟩ : Nonempty ((S ⧸ Subgroup.center S) ≃*
      (↥((J.subgroupOf L).map (piCenterQuot θ)) ⧸
        Subgroup.center ↥((J.subgroupOf L).map (piCenterQuot θ)))) :=
    ⟨MulEquiv.ofBijective φ' ⟨hφ'inj, hφ'surj⟩⟩
  exact ⟨e1.trans (e2.trans (e3.trans e4.symm))⟩

end CFSG.LocalAnalysis.GLTheoremA.T158

end

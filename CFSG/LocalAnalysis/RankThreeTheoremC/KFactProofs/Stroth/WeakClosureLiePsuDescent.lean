module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTwistFrame
public import CFSG.GroupTheory.WeirSylow.UnitaryBridge
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieFormDet
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieGUDet
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.GroupTheory.WeirSylow.GL
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.CoFiberGraphPi
public import CFSG.Monster.B.TwoA.Base.GeomNative
public import CFSG.Monster.B.TwoA.Sp8.GenActionBase
public import CFSG.Monster.B.TwoA.Sp8.NormalizerBase
public import CFSG.Monster.B.TwoA.Sp8.Orth8Base
public import CFSG.Monster.B.TwoA.Sp8.SubgeomBuildingBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFive
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFiveBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomIsoBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomStdBase
public import CFSG.Monster.B.TwoA.Unitary.Twenty
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate43
public import Certificates.Certificate9124
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.GroupTheory.WeirSylow Module
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Quasithin (StatedGU)

private noncomputable def suFrame_negIsom {p₀ f : ℕ} {L : Type} [Field L]
    {h : UnitaryFieldData p₀ f L} {S₀ : FormSpace L L} (hS₀ : IsHermitianSpace h S₀) : S₀.isom :=
  ⟨LinearEquiv.neg L, mem_formIsometryGroup.2 fun x y => by
    obtain ⟨B, hBF, -, -⟩ := hS₀
    simp only [LinearEquiv.neg_apply, hBF, map_neg, LinearMap.neg_apply, neg_neg]⟩

private theorem suFrame_negIsom_comm {p₀ f : ℕ} {L : Type} [Field L]
    {h : UnitaryFieldData p₀ f L} {S₀ : FormSpace L L} (hS₀ : IsHermitianSpace h S₀)
    (g : S₀.isom) : suFrame_negIsom hS₀ * g * (suFrame_negIsom hS₀)⁻¹ = g := by
  have hcomm : suFrame_negIsom hS₀ * g = g * suFrame_negIsom hS₀ := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    simp [suFrame_negIsom]
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

private theorem suFrame_det_negIsom {p₀ f : ℕ} {L : Type} [Field L]
    {h : UnitaryFieldData p₀ f L} {S₀ : FormSpace L L} (hS₀ : IsHermitianSpace h S₀) :
    LinearMap.det (((suFrame_negIsom hS₀ : S₀.isom) : S₀.V ≃ₗ[L] S₀.V) : S₀.V →ₗ[L] S₀.V) =
      (-1) ^ finrank L S₀.V := by
  have h1 : (((suFrame_negIsom hS₀ : S₀.isom) : S₀.V ≃ₗ[L] S₀.V) : S₀.V →ₗ[L] S₀.V) =
      (-1 : L) • (LinearMap.id : S₀.V →ₗ[L] S₀.V) := by
    ext v
    simp [suFrame_negIsom]
  rw [h1, LinearMap.det_smul, LinearMap.det_id, mul_one]

private theorem suFrame_det_piDiagIsom_mulSingle {L : Type} [Field L] {S₀ : FormSpace L L}
    {r : ℕ} (i : Fin r) (g : S₀.isom) :
    LinearMap.det ((piDiagIsom S₀ r (Pi.mulSingle i g) : (Fin r → S₀.V) ≃ₗ[L] (Fin r → S₀.V)) :
      (Fin r → S₀.V) →ₗ[L] (Fin r → S₀.V)) =
      LinearMap.det ((g : S₀.V ≃ₗ[L] S₀.V) : S₀.V →ₗ[L] S₀.V) := by
  rw [det_piDiagIsom, Fintype.prod_eq_single i]
  · rw [Pi.mulSingle_eq_same]
  · intro k hk
    rw [Pi.mulSingle_eq_of_ne hk]
    simp

private theorem suFrame_piDiagIsom_mulSingle_conj {L : Type} [Field L] {S₀ : FormSpace L L}
    {r : ℕ} (m : S₀.isom) (hm : ∀ g : S₀.isom, m * g * m⁻¹ = g) (i : Fin r)
    (Z : Fin r → S₀.isom) :
    piDiagIsom S₀ r (Pi.mulSingle i m) * piDiagIsom S₀ r Z *
      (piDiagIsom S₀ r (Pi.mulSingle i m))⁻¹ = piDiagIsom S₀ r Z := by
  rw [← map_inv, ← map_mul, ← map_mul]
  refine congrArg (piDiagIsom S₀ r) ?_
  funext k
  by_cases hk : k = i
  · subst hk
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same]
    exact hm _
  · simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_of_ne hk, one_mul, mul_one, inv_one]

private theorem suFrame_exists_Phi {p₀ f : ℕ} {L : Type} [Field L] [Finite L]
    {h : UnitaryFieldData p₀ f L} {q : ℕ} (hqf : q = p₀ ^ f) {S₀ : FormSpace L L}
    (hS₀ : IsHermitianSpace h S₀) {r n : ℕ} (hn : r * finrank L S₀.V ≤ n) :
    ∃ Φ : (FormSpace.pi fun _ : Fin r => S₀).isom →* GL (Fin n) L,
      Function.Injective Φ ∧ (∀ x, Φ x ∈ StatedGU n q L) ∧
      ∀ x : (FormSpace.pi fun _ : Fin r => S₀).isom,
        ((Φ x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det =
          LinearMap.det ((x : (Fin r → S₀.V) ≃ₗ[L] (Fin r → S₀.V)) :
            (Fin r → S₀.V) →ₗ[L] (Fin r → S₀.V)) := by
  have hPherm : IsHermitianSpace h (FormSpace.pi fun _ : Fin r => S₀) :=
    isHermitianSpace_pi (fun _ : Fin r => S₀) fun _ => hS₀
  have hT₀herm : IsHermitianSpace h (stdHermSpace h (n - r * finrank L S₀.V)) :=
    isHermitianSpace_stdHermSpace _
  have hSherm : IsHermitianSpace h (FormSpace.prod (FormSpace.pi fun _ : Fin r => S₀)
      (stdHermSpace h (n - r * finrank L S₀.V))) :=
    isHermitianSpace_prod _ _ hPherm hT₀herm
  have hPdim : finrank L (FormSpace.pi fun _ : Fin r => S₀).V = r * finrank L S₀.V := by
    rw [FormSpace.finrank_pi]
    simp
  have hSdim : finrank L (FormSpace.prod (FormSpace.pi fun _ : Fin r => S₀)
      (stdHermSpace h (n - r * finrank L S₀.V))).V = n := by
    rw [FormSpace.finrank_prod, hPdim, finrank_stdHermSpace]
    exact Nat.add_sub_of_le hn
  obtain ⟨ψ, hψinj, hψdet⟩ := exists_injective_isom_statedGU_det hqf _ hSherm hSdim
  refine ⟨(StatedGU n q L).subtype.comp (ψ.comp (prodLeftIsom _ _)), ?_, ?_, ?_⟩
  · exact Subtype.val_injective.comp (hψinj.comp (prodLeftIsom_injective _ _))
  · intro x
    exact (ψ _).2
  · intro x
    have hx := hψdet (prodLeftIsom _ _ x)
    rw [det_prodLeftIsom] at hx
    exact hx

theorem nonempty_suFrame_of_block {p₀ f : ℕ} {L : Type} [Field L] [Finite L]
    {h : UnitaryFieldData p₀ f L} {q : ℕ} (hqf : q = p₀ ^ f) {p : ℕ} [Fact p.Prime]
    (hpq1 : ¬ p ∣ q + 1) {a : ℕ} (S₀ : FormSpace L L) (hS₀ : IsHermitianSpace h S₀)
    (ρ : Multiplicative (ZMod (p ^ a)) →* S₀.isom) (hρ : Function.Injective ρ) {μ : ℤ}
    (φ : S₀.isom) (hφ : ∀ c, φ * ρ c * φ⁻¹ = ρ (c ^ μ))
    (hφdet : LinearMap.det ((φ : S₀.V ≃ₗ[L] S₀.V) : S₀.V →ₗ[L] S₀.V) = 1) {r n : ℕ}
    (hn : r * finrank L S₀.V ≤ n) :
    Nonempty (TwistFrame (Multiplicative (ZMod (p ^ a))) r (StatedSU n q L) μ) := by
  obtain ⟨Φ, hΦinj, hΦGU, hΦdet⟩ := suFrame_exists_Phi hqf hS₀ hn
  have hdetmul : ∀ x y : (FormSpace.pi fun _ : Fin r => S₀).isom,
      LinearMap.det (((x * y : (FormSpace.pi fun _ : Fin r => S₀).isom) :
        (Fin r → S₀.V) ≃ₗ[L] (Fin r → S₀.V)) : (Fin r → S₀.V) →ₗ[L] (Fin r → S₀.V)) =
      LinearMap.det ((x : (Fin r → S₀.V) ≃ₗ[L] (Fin r → S₀.V)) :
        (Fin r → S₀.V) →ₗ[L] (Fin r → S₀.V)) *
      LinearMap.det ((y : (Fin r → S₀.V) ≃ₗ[L] (Fin r → S₀.V)) :
        (Fin r → S₀.V) →ₗ[L] (Fin r → S₀.V)) := by
    intro x y
    rw [← hΦdet, ← hΦdet, ← hΦdet, map_mul, Units.val_mul, Matrix.det_mul]
  have hΦSU : ∀ x : (FormSpace.pi fun _ : Fin r => S₀).isom,
      LinearMap.det ((x : (Fin r → S₀.V) ≃ₗ[L] (Fin r → S₀.V)) :
        (Fin r → S₀.V) →ₗ[L] (Fin r → S₀.V)) = 1 → Φ x ∈ StatedSU n q L :=
    fun x hx => mem_statedSU_of_mem_statedGU h hqf (hΦGU x) ((hΦdet x).trans hx)
  let Δ : (Fin r → Multiplicative (ZMod (p ^ a))) →* GL (Fin n) L :=
    Φ.comp ((piDiagIsom S₀ r).comp (MonoidHom.piMap fun _ : Fin r => ρ))
  have hC : ∀ x : Multiplicative (ZMod (p ^ a)), x ^ (p ^ a) = 1 := by
    intro x
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hcpow : ∀ c : Fin r → Multiplicative (ZMod (p ^ a)), c ^ (p ^ a) = 1 :=
    fun c => funext fun i => hC (c i)
  have hΔpow : ∀ c, Δ c ^ (p ^ a) = 1 := fun c => by
    rw [← map_pow, hcpow c, map_one]
  have hΔGU : ∀ c, Δ c ∈ StatedGU n q L := fun c => hΦGU _
  have hcop : Nat.Coprime (p ^ a) (q + 1) :=
    Nat.Coprime.pow_left a ((Fact.out : p.Prime).coprime_iff_not_dvd.2 hpq1)
  have hΔdet : ∀ c, ((Δ c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det = 1 := by
    intro c
    have h1 : ((Δ c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det ^ (p ^ a) = 1 := by
      rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, hΔpow c, Units.val_one, Matrix.det_one]
    have h2 := det_pow_card_add_one_of_mem_statedGU h hqf (hΔGU c)
    exact (pow_eq_one_iff_of_coprime hcop).1 ⟨h1, h2⟩
  have hΔSU : ∀ c, Δ c ∈ StatedSU n q L := fun c =>
    mem_statedSU_of_mem_statedGU h hqf (hΔGU c) (hΔdet c)
  let A0 : alternatingGroup (Fin r) →* GL (Fin n) L :=
    Φ.comp ((piPermIsom S₀ r).comp (alternatingGroup (Fin r)).subtype)
  have hA0SU : ∀ σ : alternatingGroup (Fin r), A0 σ ∈ StatedSU n q L := by
    intro σ
    refine hΦSU (piPermIsom S₀ r (σ : Equiv.Perm (Fin r))) ?_
    rw [det_piPermIsom, Equiv.Perm.mem_alternatingGroup.1 σ.2, one_pow, Units.val_one,
      Int.cast_one]
  let T : (Fin r → Multiplicative (ZMod (p ^ a))) →* StatedSU n q L :=
    MonoidHom.codRestrict Δ (StatedSU n q L) hΔSU
  let A : alternatingGroup (Fin r) →* StatedSU n q L :=
    MonoidHom.codRestrict A0 (StatedSU n q L) hA0SU
  have hΔinj : Function.Injective Δ := by
    intro c c' hcc
    have hcc' : Φ (piDiagIsom S₀ r (fun k => ρ (c k))) =
        Φ (piDiagIsom S₀ r (fun k => ρ (c' k))) := hcc
    have h1 := piDiagIsom_injective S₀ r (hΦinj hcc')
    funext k
    exact hρ (congrFun h1 k)
  have hTinj : Function.Injective T := fun c c' hcc =>
    hΔinj (show Δ c = Δ c' from congrArg Subtype.val hcc)
  have hAconj : ∀ (σ : alternatingGroup (Fin r)) (c : Fin r → Multiplicative (ZMod (p ^ a))),
      A σ * T c * (A σ)⁻¹ = T (c ∘ ⇑((σ : Equiv.Perm (Fin r))⁻¹)) := by
    intro σ c
    apply Subtype.ext
    show Φ (piPermIsom S₀ r (σ : Equiv.Perm (Fin r))) *
        Φ (piDiagIsom S₀ r (fun k => ρ (c k))) *
        (Φ (piPermIsom S₀ r (σ : Equiv.Perm (Fin r))))⁻¹ =
      Φ (piDiagIsom S₀ r (fun k => ρ ((c ∘ ⇑((σ : Equiv.Perm (Fin r))⁻¹)) k)))
    rw [← map_inv, ← map_mul, ← map_mul, piPermIsom_conj]
    rfl
  have hswap : ∀ i j : Fin r, ∃ g : StatedSU n q L,
      ∀ c : Fin r → Multiplicative (ZMod (p ^ a)), g * T c * g⁻¹ = T (c ∘ Equiv.swap i j) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact ⟨1, fun c => by simp [Equiv.swap_self]⟩
    · obtain ⟨x, hx⟩ : ∃ x : (FormSpace.pi fun _ : Fin r => S₀).isom,
          x = piPermIsom S₀ r (Equiv.swap i j) *
            piDiagIsom S₀ r (Pi.mulSingle i (suFrame_negIsom hS₀)) := ⟨_, rfl⟩
      have hxdet : LinearMap.det ((x : (Fin r → S₀.V) ≃ₗ[L] (Fin r → S₀.V)) :
          (Fin r → S₀.V) →ₗ[L] (Fin r → S₀.V)) = 1 := by
        rw [hx, hdetmul, det_piPermIsom, Equiv.Perm.sign_swap hij,
          suFrame_det_piDiagIsom_mulSingle, suFrame_det_negIsom]
        simp [← mul_pow]
      refine ⟨⟨Φ x, hΦSU x hxdet⟩, fun c => Subtype.ext ?_⟩
      show Φ x * Φ (piDiagIsom S₀ r (fun k => ρ (c k))) * (Φ x)⁻¹ =
        Φ (piDiagIsom S₀ r (fun k => ρ ((c ∘ ⇑(Equiv.swap i j)) k)))
      rw [← map_inv, ← map_mul, ← map_mul]
      refine congrArg Φ ?_
      have hconj : x * piDiagIsom S₀ r (fun k => ρ (c k)) * x⁻¹ =
          piPermIsom S₀ r (Equiv.swap i j) *
            (piDiagIsom S₀ r (Pi.mulSingle i (suFrame_negIsom hS₀)) *
              piDiagIsom S₀ r (fun k => ρ (c k)) *
              (piDiagIsom S₀ r (Pi.mulSingle i (suFrame_negIsom hS₀)))⁻¹) *
            (piPermIsom S₀ r (Equiv.swap i j))⁻¹ := by
        rw [hx]
        group
      rw [hconj, suFrame_piDiagIsom_mulSingle_conj (suFrame_negIsom hS₀)
        (suFrame_negIsom_comm hS₀) i _, piPermIsom_conj, Equiv.swap_inv]
      rfl
  have htwist : ∀ i : Fin r, ∃ g : StatedSU n q L,
      ∀ c : Fin r → Multiplicative (ZMod (p ^ a)),
        g * T c * g⁻¹ = T (Function.update c i (c i ^ μ)) := by
    intro i
    have hMdet : LinearMap.det ((piDiagIsom S₀ r (Pi.mulSingle i φ) :
        (Fin r → S₀.V) ≃ₗ[L] (Fin r → S₀.V)) : (Fin r → S₀.V) →ₗ[L] (Fin r → S₀.V)) = 1 := by
      rw [suFrame_det_piDiagIsom_mulSingle]
      exact hφdet
    refine ⟨⟨Φ (piDiagIsom S₀ r (Pi.mulSingle i φ)), hΦSU _ hMdet⟩, fun c => Subtype.ext ?_⟩
    show Φ (piDiagIsom S₀ r (Pi.mulSingle i φ)) * Φ (piDiagIsom S₀ r (fun k => ρ (c k))) *
        (Φ (piDiagIsom S₀ r (Pi.mulSingle i φ)))⁻¹ =
      Φ (piDiagIsom S₀ r (fun k => ρ (Function.update c i (c i ^ μ) k)))
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
    refine congrArg Φ (congrArg (piDiagIsom S₀ r) ?_)
    funext k
    by_cases hk : k = i
    · subst hk
      simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same, Function.update_self]
      exact hφ (c k)
    · simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_of_ne hk,
        Function.update_of_ne hk, one_mul, mul_one, inv_one]
  exact ⟨⟨T, A, hTinj, hAconj, hswap, htwist⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

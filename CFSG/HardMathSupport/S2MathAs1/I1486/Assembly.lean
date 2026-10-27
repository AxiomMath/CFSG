module

public import CFSG.LocalAnalysis.StandardType.GGKGAF4CoreDefs
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoLang
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyTw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLeviToral
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTReeF4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoModel
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.S12.Sec137
public import CFSG.RankThree.PartOne.S12.Sec15FA
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.M24
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import Certificates.Certificate10050
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate16005
public import Certificates.Certificate16041
public import Certificates.Certificate17002
public import Certificates.Certificate17951
public import Certificates.Certificate2098
public import Certificates.Certificate2103
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2323
public import Certificates.Certificate3044
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8117
public import Certificates.Certificate9124

public section

namespace CFSG.HardMathSupport.S2MathAs1.I1486

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.StandardType CFSG.StandardType.KGA

@[expose] def GGF4AdjointCoreAt (p f : ℕ) (K : Type) [Field K] [Finite K] : Prop :=
  GGF4CoreAt p f (adjointGroup .F4 K)

@[expose] def GGF4AdjointCoreInput : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ f : ℕ, 1 ≤ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f → GGF4AdjointCoreAt p f K

@[expose] def GGF4RecipeCoreInput : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ f : ℕ, 1 ≤ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
      GGF4CoreAt p f (TableBF4.RecipeGroup K)

@[expose] def GGF4GeomCoreAt
    (p₀ p f : ℕ) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2]
    (S : LangSetup Tag.F4 L p₀) (a : Fin Tag.F4.rank → Lˣ) : Prop :=
  S.D.q = 2 ^ f →
  rootDiagUnit Tag.F4 a ∈ S.D.torus →
  (∀ j, a j ^ p = 1) →
  rootDiagUnit Tag.F4 a ≠ 1 →
  (∀ i : KernelComponent (rootCharHom a),
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
      Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i)) →
  ∀ i : KernelComponent (rootCharHom a),
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    GGHasLabel ⟨.C, 3, f⟩
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) →
    ∀ y ∈ S.Γ ⊓ Subgroup.centralizer ({rootDiagUnit Tag.F4 a} : Set (ModGL Tag.F4 L)),
      ∃ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
        ∀ z ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
          y * z * y⁻¹ = x * z * x⁻¹

@[expose] def GGF4GeomCoreInput
    : Prop :=
  ∀ (p₀ p f : ℕ) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2]
    (S : LangSetup Tag.F4 L p₀) (a : Fin Tag.F4.rank → Lˣ),
    p.Prime → p ≠ 2 → GGF4GeomCoreAt p₀ p f L S a

theorem ggF4CoreAt_of_mulEquiv {p f : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGF4CoreAt p f R') : GGF4CoreAt p f R := by
  intro s hs hs1 S hS hlab g hg
  have hs' : (e s) ^ p = 1 := by rw [← map_pow, hs, map_one]
  have hs1' : e s ≠ 1 := fun h' => hs1 (e.injective (by rw [h', map_one]))
  have hS' : IsComponentOf (S.map e.toMonoidHom)
      (Subgroup.centralizer ({e s} : Set R')) := by
    have h1 := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hS
      e.toMonoidHom e.injective
    rwa [CFSG.StandardType.TableBSymp.map_centralizer_singleton e s] at h1
  have hlab' : GGHasLabel ⟨.C, 3, f⟩
      (↥(S.map e.toMonoidHom) ⧸ Subgroup.center ↥(S.map e.toMonoidHom)) := by
    let eS : ↥S ≃* ↥(S.map e.toMonoidHom) := S.equivMapOfInjective e.toMonoidHom e.injective
    let eSQ : ↥S ⧸ Subgroup.center ↥S ≃*
        ↥(S.map e.toMonoidHom) ⧸ Subgroup.center ↥(S.map e.toMonoidHom) :=
      QuotientGroup.congr _ _ eS (Subgroup.map_center_eq eS)
    exact largeEvenRawDatum_mono (fun _ _ _ _ ⟨e0⟩ => ⟨eSQ.symm.trans e0⟩) hlab
  have hg' : e g ∈ Subgroup.centralizer ({e s} : Set R') := by
    rw [← CFSG.StandardType.TableBSymp.map_centralizer_singleton e s]
    exact ⟨g, hg, rfl⟩
  obtain ⟨x', hx', hxconj⟩ := h (e s) hs' hs1' (S.map e.toMonoidHom) hS' hlab' (e g) hg'
  obtain ⟨x, hxS, hx⟩ := Subgroup.mem_map.1 hx'
  refine ⟨x, hxS, fun y hy => ?_⟩
  have hy' : e y ∈ S.map e.toMonoidHom := ⟨y, hy, rfl⟩
  have h := hxconj (e y) hy'
  apply e.injective
  simp only [map_mul, map_inv]
  have hxe : e x = x' := hx
  rw [← hxe] at h
  exact h

theorem ggF4CoreInput_of_recipe (h : GGF4RecipeCoreInput) : GGF4CoreInput := by
  intro p hp hp2 f hf Q hQ
  obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
  exact ⟨K, hField, hFinite, hK, hQ', h p hp hp2 f hf K hK⟩

theorem ggF4RecipeCoreInput_of_adjoint
    (h : GGF4AdjointCoreInput) : GGF4RecipeCoreInput := by
  intro p hp hp2 f hf K hField hFinite hK
  exact ggF4CoreAt_of_mulEquiv (TableBF4.recipeEquiv K) (h p hp hp2 f hf K hK)

theorem ggF4AdjointCoreInput_of_geom
    (hgeo : GGF4GeomCoreInput) : GGF4AdjointCoreInput := by
  intro p hp hp2 f hf K hField hFinite hK
  intro s hs hs1 S0 hS0 hlab g hg
  classical
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  obtain ⟨p₀, hp₀, hp₀2, hq₀⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_setup_prime
      (ℓ := 2) (f := f) Nat.prime_two hf hp hp2 hp2
  have hp₀K : ¬ p₀ ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hp₀2 ((Nat.prime_dvd_prime_iff_eq hp₀ Nat.prime_two).1 (hp₀.dvd_of_dvd_pow h))
  have hq₀' : 5 ≤ p₀ ∨ 4 ≤ Nat.card K := by rw [hK]; exact hq₀
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt .F4 p :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_exc
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E6_five
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E7_five
      (by simp) hp hp2
  have hperf : commutator ↥(adjointGroup .F4 K) = ⊤ :=
    CFSG.LieType.Chevalley.single_edge_perfect .F4 K (by simp)
  obtain ⟨S, a, ι, hSq, hT, hap, h1, hinj, hrange, hιs, hconj⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.exists_langSetup_of_inner_untw_of_prime_eq
      (Or.inr (Or.inl rfl)) hp hpK hp₀ hp₀K hq₀' hmon hperf s hs hs1
  have hL2 : ringChar (AlgebraicClosure K) = 2 := by
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ringChar_algebraicClosure' K,
      ringChar.eq K 2]
  haveI : CharP (AlgebraicClosure K) 2 := ringChar.of_eq hL2
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.natCast_ne_zero_algebraicClosure_of_ne
      (ℓ := 2) (f := f) (m := 1) Nat.prime_two hp (by simpa using hK) hp2
  have hTame :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime S hp hpL
      (fun h => absurd h (by decide)) hT hap h1
  have hfix : fixSubgroup (MulAut.conj s) =
      Subgroup.centralizer ({s} : Set ↥(adjointGroup .F4 K)) := by
    ext x
    rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      rw [MulAut.conj_apply] at hx
      calc x * s = s * x * s⁻¹ * s := by rw [hx]
        _ = s * x := by group
    · intro hx
      rw [MulAut.conj_apply]
      calc s * x * s⁻¹ = x * s * s⁻¹ := by rw [← hx]
        _ = x := by group
  have hcomp : CFSG.Open.IsComponentOf S0 (fixSubgroup (MulAut.conj s)) := by
    rw [hfix]
    exact CFSG.Assembly.isComponentOf_iff_open.1 hS0
  obtain ⟨i, hqs, hmap⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup S hp ι hinj hrange
      (MulAut.conj s) hconj hT hap h1 hTame hcomp
  let R := rationalComponent S.ρ S.Γ (rootCharHom a) i
  let eS : ↥S0 ≃* ↥R := (S0.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hmap)
  let eSQ : ↥S0 ⧸ Subgroup.center ↥S0 ≃* ↥R ⧸ Subgroup.center ↥R :=
    QuotientGroup.congr _ _ eS (Subgroup.map_center_eq eS)
  have hlabR : GGHasLabel ⟨.C, 3, f⟩ (↥R ⧸ Subgroup.center ↥R) :=
    largeEvenRawDatum_mono (fun _ _ _ _ ⟨e0⟩ => ⟨eSQ.symm.trans e0⟩) hlab
  have hgcent : ι g ∈ S.Γ ⊓
      Subgroup.centralizer ({rootDiagUnit Tag.F4 a} :
        Set (ModGL Tag.F4 (AlgebraicClosure K))) := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [← hrange]; exact MonoidHom.mem_range.2 ⟨g, rfl⟩
    · have hcomm : g * s = s * g := Subgroup.mem_centralizer_singleton_iff.1 hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc ι g * rootDiagUnit Tag.F4 a = ι g * ι s := by rw [hιs]
        _ = ι (g * s) := (map_mul ι g s).symm
        _ = ι (s * g) := by rw [hcomm]
        _ = ι s * ι g := map_mul ι s g
        _ = rootDiagUnit Tag.F4 a * ι g := by rw [hιs]
  obtain ⟨x, hxR, hxconj⟩ :=
    hgeo p₀ p f (AlgebraicClosure K) S a hp hp2 (hSq.trans hK) hT hap h1 hTame i hqs hlabR (ι g) hgcent
  obtain ⟨ξ, hξS, hξx⟩ := Subgroup.mem_map.1 (by rw [hmap]; exact hxR)
  refine ⟨ξ, hξS, fun y hy => ?_⟩
  have hyR : ι y ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rw [← hmap]; exact ⟨y, hy, rfl⟩
  have heq := hxconj (ι y) hyR
  apply hinj
  simp only [map_mul, map_inv]
  rw [← hξx] at heq
  exact heq

theorem ggF4CoreInput_of_geom
    (hgeo : GGF4GeomCoreInput) : GGF4CoreInput :=
  ggF4CoreInput_of_recipe (ggF4RecipeCoreInput_of_adjoint (ggF4AdjointCoreInput_of_geom hgeo))

end CFSG.HardMathSupport.S2MathAs1.I1486

end


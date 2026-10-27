module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Plane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2SpComm
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthFixed
public import CFSG.RankThree.PartOne.F106.OddRadOrthInner
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticFamily
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock
public import CFSG.RankThree.PartOne.S11d.LieCentralizerOrth
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import Certificates.Certificate116
public import Certificates.Certificate119
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Polynomial Module
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.RankThree.Classical

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [Finite K] in
theorem ringChar_eq_two_of_card (hK : Nat.card K = 2) : ringChar K = 2 := by
  have := charP_two_of_card hK
  exact ringChar.eq K 2

omit [Finite K] [FiniteDimensional K V] in
theorem conj_mem_orthDerived {G : V ≃ₗ[K] V} (hG : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {y : V ≃ₗ[K] V} (hy : y ∈ orthDerived Q) : G * y * G⁻¹ ∈ orthDerived Q := by
  have hle : (TauCeti.QuadraticMap.orthogonalGroup Q).map (MulAut.conj G).toMonoidHom ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨a, ha, rfl⟩
    exact mul_mem (mul_mem hG ha) (inv_mem hG)
  have h1 : (MulAut.conj G).toMonoidHom y ∈ (orthDerived Q).map (MulAut.conj G).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hy
  rw [orthDerived, Subgroup.map_commutator] at h1
  exact Subgroup.commutator_mono hle hle h1

theorem orth2_mem_supportedFixedDerived (hK : Nat.card K = 2) {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2)
    (h6 : 6 ≤ finrank K (fixedSpace x)) {g : V ≃ₗ[K] V} (hg : g ∈ supportedBlock Q x (X - 1))
    (hgp : g ^ p = 1) : g ∈ supportedFixedDerived Q x := by
  have := charP_two_of_card hK
  refine mem_supportedFixedDerived.mpr ⟨hg, ?_⟩
  have h1 : (restrictFixed Q x ⟨g, hg⟩) ^ p = 1 := by
    rw [← map_pow]
    have : (⟨g, hg⟩ : ↥(supportedBlock Q x (X - 1))) ^ p = 1 := Subtype.ext hgp
    rw [this, map_one]
  have hodd : Odd (orderOf (restrictFixed Q x ⟨g, hg⟩)) :=
    Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one h1)
  exact (CFSG.AGLEmbedding.ToralCensus.perfect_and_odd_orthDerived_of_card_two hK
    hx.polarBilin_fixed_nondegenerate h6).2 _ (restrictFixed_mem_orthogonalGroup _) hodd

variable (hK : Nat.card K = 2) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
  (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)

include hK hQ hT in
theorem orth2_fixedComponentImage_le_fixSub (hinj : Function.Injective
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)))
    {H E : Subgroup (MulAut (ProjOrthDerived Q))}
    (hH : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ H)
    {g : MulAut (ProjOrthDerived Q)} (hg : g ∈ localDeltaIn 3 H E)
    (x : orthDerived Q) (hxp : orderOf x = 3)
    (he : MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q) ∈ E)
    {w : V ≃ₗ[K] V} (hw : w ∈ supportedBlock Q (x : V ≃ₗ[K] V) (X - 1)) (hwp : w ^ 3 = 1)
    (hw1 : w ≠ 1) (h6 : 6 ≤ finrank K (fixedSpace (x : V ≃ₗ[K] V))) :
    fixedComponentImage Q (x : V ≃ₗ[K] V) ≤ fixSub g := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hpl : (3 : ℕ) ≠ ringChar K := by rw [ringChar_eq_two_of_card hK]; norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  have ha := orth3_orderOf_mk_projOrth hQ hT hp hp2 hxp
  have ha1 : (QuotientGroup.mk x : ProjOrthDerived Q) ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at ha
    omega
  have he1 : MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q) ≠ 1 :=
    fun h1 => ha1 (hinj (by rw [h1, map_one]))
  have hlist : FixedLayerListed Q (x : V ≃ₗ[K] V) :=
    ⟨by omega, by rintro (⟨h, -⟩ | ⟨⟨h, -⟩, -⟩) <;> omega⟩
  have hs4 : ¬ (finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4 ∧
      ∃ S : Submodule K (fixedSpace (x : V ≃ₗ[K] V)), finrank K S = 2 ∧
        ∀ s ∈ S, (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) s = 0) := by
    rintro ⟨h, -⟩
    omega
  have hwS : w ∈ supportedFixedDerived Q (x : V ≃ₗ[K] V) :=
    orth2_mem_supportedFixedDerived hK hx hp hp2 h6 hw hwp
  have hwΩ := hx.supportedFixedDerived_le_orthDerived hwS
  set w' : orthDerived Q := ⟨w, hwΩ⟩ with hw'
  have hw'p : orderOf w' = 3 := orderOf_eq_prime (Subtype.ext hwp)
    (fun h1 => hw1 (congrArg Subtype.val h1))
  have hρw := orth3_orderOf_mk_projOrth hQ hT hp hp2 hw'p
  have hmemF : (QuotientGroup.mk w' : ProjOrthDerived Q) ∈
      fixedComponentImage Q (x : V ≃ₗ[K] V) :=
    ⟨w', Subgroup.mem_subgroupOf.mpr hwS, rfl⟩
  obtain ⟨-, -, hle, -, hcomp⟩ := orth3_unsplit_fixed_layer hQ hT hp hp2 hpl
    H hH _ ha1 x rfl hxp hlist hs4
  refine le_fixSub_of_component hp hinj hg he he1 ?_ hcomp
    (not_coprime_card_of_orderOf_orth hp hmemF hρw)
  rintro _ ⟨t, ht, rfl⟩
  refine Subgroup.mem_inf.2 ⟨hH ⟨t, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 (hle ht)]

include hK hQ in
theorem orth2_fixes_fixedSpace {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x)
    (h6 : 6 ≤ finrank K (fixedSpace x)) {G : V ≃ₗ[K] V}
    (hGO : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hGx : G * x = x * G)
    (hcomm : ∀ f ∈ supportedFixedDerived Q x, G * f = f * G) :
    ∀ w ∈ fixedSpace x, G w = w := by
  have := charP_two_of_card hK
  have hnexc : ¬ SmallFixedException (Q.comp (fixedSpace x).subtype) := by
    rintro (⟨h, -⟩ | ⟨⟨h, -⟩, -⟩) <;> omega
  have hGM : G ∈ isometryCentralizer Q x := by
    rw [mem_isometryCentralizer]
    refine ⟨fun v => (TauCeti.QuadraticMap.mem_orthogonalGroup_iff).1 hGO v, fun v => ?_⟩
    have := congrArg (fun e : V ≃ₗ[K] V => e v) hGx
    simpa using this
  exact F106.OddRadOrth.fixes_of_commute_listed hx hQ (by omega) hnexc hGM fun f hf v => by
    have := congrArg (fun e : V ≃ₗ[K] V => e v) (hcomm f hf)
    simpa using this

end CFSG.HardMathSupport.Timmesfeld.CrossChar

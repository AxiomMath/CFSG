module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Simple59
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Commute
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma551
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Cover59
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Pump

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem eq_of_isPComponent_of_le {C P P' K : Subgroup G} (hPC : P ≤ C) (hP'C : P' ≤ C)
    (hP : IsPComponent 2 (P.subgroupOf C)) (hP' : IsPComponent 2 (P'.subgroupOf C))
    (hKP : K ≤ P) (hKP' : K ≤ P') (hKperf : ⁅K, K⁆ = K) (hK2 : 2 ∣ Nat.card K) : P = P' := by
  by_contra hne
  have h1 := commutator_le_inf_oddIn hPC hP'C hP hP' hne
  have hKO : K ≤ oddIn P := by
    rw [← hKperf]
    exact (commutator_mono hKP hKP').trans (h1.trans inf_le_left)
  have hodd : Odd (Nat.card (oddIn P)) := by
    rw [oddIn, card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  exact (Nat.not_even_iff_odd.mpr hodd)
    (even_iff_two_dvd.mpr (hK2.trans (Subgroup.card_dvd_of_le hKO)))

theorem commutator_eq_self_of_isPComponent' {C K : Subgroup G} (hKC : K ≤ C)
    (hK : IsPComponent 2 (K.subgroupOf C)) : ⁅K, K⁆ = K := by
  have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hK
  have h2 : Group.IsPerfect ↥K :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKC).toMonoidHom)
      (subgroupOfEquivOfLe hKC).surjective
  exact (Subgroup.isPerfect_iff (H := K)).mp h2

theorem mem_coreActionKernel_of_commute_pumpUp {a t : G} {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJp : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G)))) (hat : a * t = t * a)
    (hJt : J ≤ centralizer ({t} : Set G))
    (hPp : IsPComponent 2 ((pumpUp J t).subgroupOf (centralizer ({t} : Set G))))
    (hsup : J ⊔ oddIn (pumpUp J t) = pumpUp J t) : a ∈ coreActionKernel (pumpUp J t) := by
  set C := centralizer ({t} : Set G) with hC
  set P := pumpUp J t with hP
  have hPC : P ≤ C := pumpUp_le_centralizer J t
  have haC : a ∈ C := mem_centralizer_singleton_iff.mpr hat
  have hgs := gsFixedLayer_eq_of_le hJa hJp hJt
  have hJP : J ≤ P := le_pumpUp hgs
  obtain ⟨hPaC, hPap⟩ := GSThmB.Six.isPComponent_conjugate hPC hPp a
  have hCa : conjugate C a = C := conjugate_eq_of_mem_normalizer (le_normalizer haC)
  rw [hCa] at hPaC hPap
  have haJ : a ∈ normalizer (J : Set G) :=
    mem_normalizer_of_commute fun j hj => (mem_centralizer_singleton_iff.mp (hJa hj)).symm
  have hJPa : J ≤ conjugate P a := by
    have h1 := map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hJP
    have h2 : conjugate J a = J := conjugate_eq_of_mem_normalizer haJ
    exact h2.symm.le.trans h1
  have hPa : conjugate P a = P := eq_of_isPComponent_of_le hPaC hPC hPap hPp hJPa hJP
    (commutator_eq_self_of_isPComponent' hJa hJp) (two_dvd_card_of_isPComponent hJa hJp)
  have haN : a ∈ normalizer (P : Set G) := mem_normalizer_of_conjugate_eq hPa
  refine GSThmB.mem_coreActionKernel_of_sup hJP hsup haN fun y hy => ?_
  rw [show y⁻¹ * a⁻¹ * y * a = 1 by
    rw [show y⁻¹ * a⁻¹ * y * a = y⁻¹ * a⁻¹ * (y * a) by group,
      (mem_centralizer_singleton_iff.mp (hJa hy)), show y⁻¹ * a⁻¹ * (a * y) = 1 by group]]
  exact one_mem _

theorem l34Lemma59TripleStep_of_inputs
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
      L34Sec5Setting G L t S T → S ⊓ coreActionKernel L = zpowers t →
      ∃ x : G, GSUnbalancingTriple t x L := by
  intro G _ _ L t S T hset hQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  obtain ⟨-, ⟨⟨a, x, J, hT, htype, hto, ⟨-, hat, hJt⟩, hL⟩, htypeL, -⟩, -, hSyl, -, -, -⟩ := hset
  subst hL
  have hJa := hT.2.2.2.1
  have hJp := hT.2.2.2.2.1
  have hgs := gsFixedLayer_eq_of_le hJa hJp hJt
  have hsup : J ⊔ oddIn (pumpUp J t) = pumpUp J t :=
    sup_oddIn_eq_of_le_of_isL34Type (le_pumpUp hgs) htype htypeL
      (commutator_eq_self_of_isPComponent' hLt hLpt)
  have hPp := hLpt
  set P := pumpUp J t with hP
  have hPC : P ≤ centralizer ({t} : Set G) := pumpUp_le_centralizer J t
  have haK := mem_coreActionKernel_of_commute_pumpUp hJa hJp hat hJt hPp hsup
  have ha2 : IsPGroup 2 (zpowers a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hT.1, pow_one])
  obtain ⟨n, hnN, hn⟩ := exists_conjugate_le_of_isSylowTwoIn hSyl
    (zpowers_le.mpr (mem_coreActionKernel.mp haK).1) ha2
  have hanS : n⁻¹ * a * n ∈ S := hn ⟨a, mem_zpowers a, by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have hanK : n⁻¹ * a * n ∈ coreActionKernel P := by
    have h1 := (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel P (inv_mem hnN))
      a).mp haK
    rwa [inv_inv] at h1
  have hanQ : n⁻¹ * a * n ∈ zpowers t := by
    rw [← hQ]
    exact mem_inf.mpr ⟨hanS, hanK⟩
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have han : n⁻¹ * a * n = t := by
    rcases eq_one_or_eq_of_mem_zpowers' ht2 hanQ with h | h
    · exfalso
      have ha1 : a = 1 := by
        calc a = n * (n⁻¹ * a * n) * n⁻¹ := by group
          _ = 1 := by rw [h, mul_one, mul_inv_cancel]
      have h2 := hT.1
      rw [ha1, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    · exact h
  have hT' := gsUnbalancingTriple_conjugate hT n
  rw [han] at hT'
  have hPn : conjugate P n = P := conjugate_eq_of_mem_normalizer hnN
  have hJP : J ≤ P := le_pumpUp hgs
  have hJnP : conjugate J n ≤ P := by
    rw [← hPn]
    exact map_mono hJP
  have hJnC := hT'.2.2.2.1
  have hJnp := hT'.2.2.2.2.1
  have heq : conjugate J n = P := eq_of_isPComponent_of_le hJnC hPC hJnp hPp le_rfl hJnP
    (commutator_eq_self_of_isPComponent' hJnC hJnp) (two_dvd_card_of_isPComponent hJnC hJnp)
  refine ⟨n⁻¹ * x * n, ?_⟩
  rw [← heq]
  exact hT'

end CFSG.ComponentClassification.GrSLit.GrS5

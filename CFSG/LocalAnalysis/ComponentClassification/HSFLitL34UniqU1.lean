module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvL2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Tools59
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma414Tools
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvTools

public section

namespace CFSG.ComponentClassification.HSFLit.L34Uniq

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
  CFSG.ComponentClassification.HSFLit.L34Inv
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoIn_centralizers
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) {L : Subgroup G} {t : G} {S T : Subgroup G}
    (hset : L34Sec5Setting G L t S T) {u : G} (huc : ∀ s ∈ S, s * u = u * s) :
    IsSylowTwoIn S (centralizer ({u} : Set G) ⊓ centralizer ({t} : Set G)) := by
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hCN := centralizer_le_normalizer_of_setting hS hU hheld hSol hGW hMax hset
  obtain ⟨-, -, -, hSyl, -, -, -⟩ := hset
  exact isSylowTwoIn_of_le_of_le hSyl
    (le_inf (fun s hs => mem_centralizer_singleton_iff.mpr (huc s hs))
      fun s hs => mem_centralizer_singleton_iff.mpr (hZS s hs)) (inf_le_right.trans hCN)

theorem isSylowTwoIn_inf_component
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) {L : Subgroup G} {t : G} {S T : Subgroup G}
    (hset : L34Sec5Setting G L t S T) {u : G} (huc : ∀ s ∈ S, s * u = u * s) {K : Subgroup G}
    (hKu : K ≤ centralizer ({u} : Set G))
    (hKp : IsPComponent 2 (K.subgroupOf (centralizer ({u} : Set G)))) :
    IsSylowTwoIn (S ⊓ K) (K ⊓ centralizer ({t} : Set G)) := by
  set H := centralizer ({u} : Set G) ⊓ centralizer ({t} : Set G) with hH
  have hSH := isSylowTwoIn_centralizers hS hU hheld hSol hGW hMax hset huc
  have hsub : (K.subgroupOf (centralizer ({u} : Set G))).IsSubnormal := by
    obtain ⟨_, _, h, _, _⟩ := hKp
    exact h
  have hsub' := isSubnormal_inf_subgroupOf (inf_le_left : H ≤ centralizer ({u} : Set G)) hsub
  have h1 := isSylowTwoIn_inf_of_isSubnormal hSH inf_le_right hsub'
  have e1 : S ⊓ (K ⊓ H) = S ⊓ K := by
    apply le_antisymm (inf_le_inf_left _ inf_le_left)
    exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hSH.1))
  have e2 : K ⊓ H = K ⊓ centralizer ({t} : Set G) := by
    apply le_antisymm (inf_le_inf_left _ inf_le_right)
    exact le_inf inf_le_left (le_inf (inf_le_left.trans hKu) inf_le_right)
  rw [e1, e2] at h1
  exact h1

theorem card_inf_component
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) {L : Subgroup G} {t : G} {S T : Subgroup G}
    (hset : L34Sec5Setting G L t S T) {u : G} (hu : u ∈ L34UnbalancingSet L t S)
    (huc : ∀ s ∈ S, s * u = u * s) {K : Subgroup G} (hKu : K ≤ centralizer ({u} : Set G))
    (hKp : IsPComponent 2 (K.subgroupOf (centralizer ({u} : Set G))))
    (hKn : ¬ ⁅K, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K)
    (htype : IsL2Type 5 (K ⧸ pPrimeCore 2 K) ∨ IsL2Type 7 (K ⧸ pPrimeCore 2 K)) :
    Nat.card ↥(S ⊓ K) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, hSyl, htS, -, -⟩ := hset'
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  obtain ⟨huS₀, hu2, -⟩ := hu
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S) huS₀
  have htu : t * u = u * t := (hZS u huS).symm
  have hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_right _ (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  have hT := gsUnbalancingTriple_of_not_le hSol hto hu2 htu hKu hKp hYD hKn
  have hS2 : IsPGroup 2 S := GrS5.IsSylowTwoIn.isPGroup hSyl
  have hSK := isSylowTwoIn_inf_component hS hU hheld hSol hGW hMax hset huc hKu hKp
  have hle : Nat.card ↥(S ⊓ K) ≤ 2 :=
    (AutL2.l2UnbalancingAutFact G u t K (S ⊓ K) hT htype (hS2.to_le inf_le_left)).2
      (le_inf inf_le_right fun s hs => mem_centralizer_singleton_iff.mpr (hZS s (mem_inf.mp hs).1))
  have htN : t ∈ normalizer (K : Set G) := by
    obtain ⟨-, h⟩ := (solomon_involutions hSol hto hu2 htu).2 K hKu hKp
    refine (h fun hle' => hKn (le_trans (commutator_mono le_rfl hYD) hle')).1
  have hKe : 2 ∣ Nat.card K := by
    have hq : Nat.card (K ⧸ pPrimeCore 2 K) = 60 ∨ Nat.card (K ⧸ pPrimeCore 2 K) = 168 := by
      rcases htype with h | h
      · left; rw [GSThmB.card_of_lieModel_psl_two (by norm_num) h]; decide
      · right; rw [GSThmB.card_of_lieModel_psl_two (by norm_num) h]; decide
    have hdvd : Nat.card (K ⧸ pPrimeCore 2 K) ∣ Nat.card K := by
      rw [← Subgroup.index]; exact Subgroup.index_dvd_card _
    rcases hq with h | h <;> rw [h] at hdvd <;> exact (by norm_num : (2 : ℕ) ∣ _).trans hdvd
  obtain ⟨P, hP, hPt, -⟩ := exists_isSylowTwoIn_normalized (isPGroup_zpowers_of_mul_self ht2)
    (zpowers_le.mpr htN)
  have hP2 : IsPGroup 2 P := GrS5.IsSylowTwoIn.isPGroup hP
  have hP1 : P ≠ ⊥ := by
    intro hPb
    obtain ⟨hPK, P₀, hP₀⟩ := hP
    have h1 := Sylow.card_eq_multiplicity P₀
    have h2 : Nat.card ↥(P₀ : Subgroup ↥K) = 1 := by
      rw [hP₀, hPb]
      simp
    have h3 : 0 < (Nat.card ↥K).factorization 2 :=
      Nat.prime_two.factorization_pos_of_dvd Nat.card_pos.ne' hKe
    rw [h2] at h1
    have h4 : 2 ≤ 2 ^ (Nat.card ↥K).factorization 2 :=
      le_self_pow₀ (by norm_num) h3.ne'
    omega
  set R := P ⊔ zpowers t with hR
  have hR2 : IsPGroup 2 R :=
    hP2.to_sup_of_normal_left' (isPGroup_zpowers_of_mul_self ht2) (zpowers_le.mpr (hPt
      (mem_zpowers t)))
  have hRN : R ≤ normalizer (P : Set G) := sup_le le_normalizer (zpowers_le.mpr (hPt
    (mem_zpowers t)))
  obtain ⟨x, hxP, hx2, hxR⟩ := FooteLit.exists_involution_inf_center hR2 le_sup_left hRN hP1
  have hxt : x * t = t * x := (hxR t (mem_sup_right (mem_zpowers t))).symm
  have hxC : x ∈ K ⊓ centralizer ({t} : Set G) :=
    mem_inf.mpr ⟨hP.1 hxP, mem_centralizer_singleton_iff.mpr hxt⟩
  have hge : 2 ≤ Nat.card ↥(S ⊓ K) := by
    have hx' : IsPGroup 2 (zpowers x) := isPGroup_zpowers_of_mul_self (by
      rw [← pow_two, ← hx2, pow_orderOf_eq_one])
    have h1 := card_le_of_isSylowTwoIn hSK (zpowers_le.mpr hxC) hx'
    rw [Nat.card_zpowers, hx2] at h1
    exact h1
  omega

end CFSG.ComponentClassification.HSFLit.L34Uniq

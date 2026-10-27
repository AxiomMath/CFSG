module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitBridge
public import CFSG.LocalAnalysis.ComponentClassification.Sol78PSp4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Core

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem le_of_le_sup_of_odd {P O' L : Subgroup G} (hP : Group.IsPerfect P)
    (hO' : Odd (Nat.card O')) (hO'L : O' ≤ normalizer (L : Set G))
    (hPL : P ≤ normalizer (L : Set G)) (hle : P ≤ O' ⊔ L) : P ≤ L := by
  set N := normalizer (L : Set G) with hN
  have hLN : L ≤ N := le_normalizer
  set L' := L.subgroupOf N with hL'
  have : L'.Normal := normal_in_normalizer
  set π := QuotientGroup.mk' L' with hπ
  set P' := P.subgroupOf N with hP'
  set O'' := O'.subgroupOf N with hO''
  have hle' : P' ≤ O'' ⊔ L' := by
    rw [hP', hO'', hL', ← subgroupOf_sup hO'L hLN]
    intro x hx
    exact hle hx
  have hmap : P'.map π ≤ O''.map π := by
    refine (map_mono hle').trans ?_
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  have hodd : Odd (Nat.card (P'.map π)) := by
    have h1 : Nat.card (O''.map π) ∣ Nat.card O'' := card_map_dvd O'' π
    have h2 : Nat.card O'' = Nat.card O' := Nat.card_congr (subgroupOfEquivOfLe hO'L).toEquiv
    exact (hO'.of_dvd_nat (h2 ▸ h1)).of_dvd_nat (card_dvd_of_le hmap)
  have hperf : _root_.commutator ↥(P'.map π) = ⊤ := by
    have h1 : Group.IsPerfect P' := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hPL).symm.toMonoidHom) (subgroupOfEquivOfLe hPL).symm.surjective
    have h2 : Group.IsPerfect ↥(P'.map π) :=
      Group.IsPerfect.ofSurjective (f := π.subgroupMap P') (π.subgroupMap_surjective P')
    exact h2.commutator_eq_top
  have hbot := ClassicalInvolution.Balance.eq_bot_of_perfect_of_odd hperf hodd
  intro p hp
  have hpN : p ∈ N := hPL hp
  have h1 : π ⟨p, hpN⟩ ∈ P'.map π := ⟨⟨p, hpN⟩, hp, rfl⟩
  rw [hbot, mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem two_le_pRank_of_four {H W : Subgroup G} (hWH : W ≤ H) (hW : IsElemTwo W)
    (hW4 : Nat.card W = 4) : 2 ≤ pRank 2 ↥H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B : Subgroup ↥H := W.subgroupOf H with hB
  have hBc : Nat.card B = 2 ^ 2 := by
    rw [hB, Nat.card_congr (subgroupOfEquivOfLe hWH).toEquiv, hW4]
    norm_num
  have hBe : IsElementaryAbelian 2 ↥B :=
    { is_comm := ⟨fun x y => Subtype.ext (Subtype.ext (hW.1 _ (mem_subgroupOf.mp x.2) _
        (mem_subgroupOf.mp y.2)))⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun y =>
        Subtype.ext (Subtype.ext (by
          show (((y : B) : H) : G) ^ 2 = 1
          rw [pow_two]
          exact hW.2 _ (mem_subgroupOf.mp y.2))) }
  have hbdd : BddAbove
      {r : ℕ | ∃ A : Subgroup ↥H, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} := by
    refine ⟨Nat.card H, ?_⟩
    rintro k ⟨A, -, hA⟩
    calc k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
      _ = Nat.card A := hA.symm
      _ ≤ Nat.card H := card_le_card_group A
  exact le_csSup hbdd ⟨B, hBe, hBc⟩

theorem centralizer_le_normalizer_of_setting
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) {L : Subgroup G} {t : G} {S T : Subgroup G}
    (hset : L34Sec5Setting G L t S T) : centralizer ({t} : Set G) ≤ normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  obtain ⟨hbase, hfam, -, -, -, -, -⟩ := hset
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := id hbase
  obtain ⟨⟨-, -, -, -, -, hto, -, -⟩, htype, hmax, -, -⟩ := hfam
  have : IsSimpleGroup G := hsimple
  have htop : GeneralizedFitting.subgroup G = ⊤ := GSLit.generalizedFitting_eq_top_of_simple
  let eF : GeneralizedFitting.subgroup G ≃* G :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hsF : IsSimpleGroup (GeneralizedFitting.subgroup G) := eF.isSimpleGroup
  have hnF : ∃ u v : GeneralizedFitting.subgroup G, u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := hnab
    exact ⟨eF.symm u, eF.symm v, fun h => huv (eF.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hoF : ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup G) := fun h => hUo (Or.inl h)
  obtain ⟨W, hWL, hWe, hW4, -⟩ := exists_four_inf_centralizer htype
  have h2L : 2 ≤ pRank 2 ↥L := two_le_pRank_of_four hWL hWe hW4
  obtain ⟨hcon, -⟩ := hMax G hsF hnF hoF hK L hmax h2L
    (Sol78.not_psp4_of_l34 htype) (Or.inl ⟨htype, hbase⟩) t hto hLt
  intro c hc
  have hLc : conjugate L c ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨l, hl, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact mul_mem (mul_mem (inv_mem hc) (hLt hl)) hc
  have hle : conjugate L c ≤ (pPrimeCore 2 (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype ⊔ L := (le_iSup₂_of_le c hLc le_rfl).trans hcon
  have hON : (pPrimeCore 2 (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype ≤
      normalizer (L : Set G) := by
    rintro _ ⟨o, ho, rfl⟩
    have h1 := pPrimeCore_le_normalizer hLpt ho
    rw [mem_normalizer_iff] at h1 ⊢
    intro y
    constructor
    · intro hy
      have hyC : y ∈ centralizer ({t} : Set G) := hLt hy
      have := mem_subgroupOf.mp ((h1 ⟨y, hyC⟩).mp (mem_subgroupOf.mpr hy))
      simpa using this
    · intro hy
      have hyC : y ∈ centralizer ({t} : Set G) := by
        have h2 : (o : G) * y * (o : G)⁻¹ ∈ centralizer ({t} : Set G) := hLt hy
        have := mul_mem (mul_mem (inv_mem o.2) h2) o.2
        simpa [mul_assoc] using this
      have := (h1 ⟨y, hyC⟩).mpr (by simpa using mem_subgroupOf.mpr hy)
      exact mem_subgroupOf.mp this
  have hodd : Odd (Nat.card ((pPrimeCore 2 (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype)) := by
    rw [card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hperf : Group.IsPerfect L := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hLpt
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hLt).toMonoidHom)
      (subgroupOfEquivOfLe hLt).surjective
  have hperfc : Group.IsPerfect (conjugate L c) :=
    Group.IsPerfect.ofSurjective (f := (L.equivMapOfInjective _ (MulAut.conj c⁻¹).injective
      ).toMonoidHom) (MulEquiv.surjective _)
  have hcN : conjugate L c ≤ normalizer (L : Set G) := hle.trans (sup_le hON le_normalizer)
  have hsub := le_of_le_sup_of_odd hperfc hodd hON hcN hle
  have hceq : conjugate L c = L := by
    apply eq_of_le_of_card_ge hsub
    rw [conjugate, card_map_of_injective (MulAut.conj c⁻¹).injective]
  exact mem_normalizer_of_conjugate_eq hceq

end CFSG.ComponentClassification.GrSLit.GrS5

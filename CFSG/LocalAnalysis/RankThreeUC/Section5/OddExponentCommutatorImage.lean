module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.ActionVocabulary
public import CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary.FaithfulPImageVocabulary
public import CFSG.LocalAnalysis.RankThreeUC.Section5.OpenPCoreEq

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.OddExponentCommutatorImage

open CFSG.LocalAnalysis.RankThreeUC.Section5

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_sup_eq {p : ℕ} {P T B : Subgroup G} {e : ℕ} (h51 : OddPrimeClassTwoAction G p P T B e)
    (he : Odd e) : CFSG.Open.pCoreOf 2 (B ⊔ T) = T := by
  have hset := h51.setting
  have hBT : B ≤ Subgroup.normalizer (T : Set G) := h51.normalizes he
  have hM : B ⊔ T ≤ Subgroup.normalizer (T : Set G) :=
    sup_le hBT (fun t ht => Subgroup.le_normalizer ht)
  have hBM : B ≤ B ⊔ T := le_sup_left
  have hTM : T ≤ B ⊔ T := le_sup_right
  set M : Subgroup G := B ⊔ T with hMdef
  have hTn : (T.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTM).mpr hM
  haveI : (T.subgroupOf M).Normal := hTn
  have hT : IsPGroup 2 (T.subgroupOf M) :=
    hset.twoGroup.comap_of_injective M.subtype Subtype.coe_injective
  have hBodd : Odd (Nat.card (B.subgroupOf M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv]; exact hset.oddOrder
  have hperm : ((B.subgroupOf M : Subgroup M) : Set M) * ((T.subgroupOf M : Subgroup M) : Set M) =
      ((T.subgroupOf M : Subgroup M) : Set M) * ((B.subgroupOf M : Subgroup M) : Set M) := by
    have hp := hset.prod_comm
    ext x
    constructor
    · rintro ⟨b, hb, t, ht, rfl⟩
      have : (b : G) * t ∈ (T : Set G) * B := by
        rw [hp]; exact ⟨b, hb, t, ht, rfl⟩
      obtain ⟨t', ht', b', hb', e⟩ := this
      exact ⟨⟨t', hTM ht'⟩, ht', ⟨b', hBM hb'⟩, hb', Subtype.ext e⟩
    · rintro ⟨t, ht, b, hb, rfl⟩
      have : (t : G) * b ∈ (B : Set G) * T := by
        rw [← hp]; exact ⟨t, ht, b, hb, rfl⟩
      obtain ⟨b', hb', t', ht', e⟩ := this
      exact ⟨⟨b', hBM hb'⟩, hb', ⟨t', hTM ht'⟩, ht', Subtype.ext e⟩
  have hsup : B.subgroupOf M ⊔ T.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hBM hTM, ← hMdef, Subgroup.subgroupOf_self]
  have hcop0 : Nat.Coprime (Nat.card (B.subgroupOf M)) (Nat.card (T.subgroupOf M)) := by
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    rw [hk]; exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hBodd)
  have hdisj : B.subgroupOf M ⊓ T.subgroupOf M = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop0
  have hmul : ((B.subgroupOf M : Subgroup M) : Set M) * ((T.subgroupOf M : Subgroup M) : Set M)
      = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ B.subgroupOf M ⊔ T.subgroupOf M := by rw [hsup]; trivial
    obtain ⟨b, hb, t, ht, rfl⟩ := OddActorSylowFactorization.mem_sup_mul hperm hx
    exact Set.mem_mul.mpr ⟨b, hb, t, ht, rfl⟩
  have hcompl : Subgroup.IsComplement' (B.subgroupOf M) (T.subgroupOf M) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hdisj) hmul
  have hcard : Nat.card (B.subgroupOf M) * Nat.card (T.subgroupOf M) = Nat.card M :=
    hcompl.card_mul_card
  haveI : (CFSG.pCore 2 M).Normal := CFSG.pCore_normal
  have hNT : CFSG.pCore 2 M ≤ T.subgroupOf M :=
    OddActorSylowFactorization.normal_two_le (CFSG.pCore_isPGroup) hBodd hT hcard
  have hTle : T.subgroupOf M ≤ CFSG.pCore 2 M := fun x hx =>
    Subgroup.mem_sSup_of_mem (show T.subgroupOf M ∈ CFSG.normalPSubgroups 2 M from ⟨hTn, hT⟩) hx
  unfold CFSG.Open.pCoreOf
  rw [OddActorSylowFactorization.openPCore_eq]
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mpr hNT
  · intro t ht
    exact Subgroup.mem_map.mpr ⟨⟨t, hTM ht⟩, hTle (show (⟨t, hTM ht⟩ : M) ∈ T.subgroupOf M from ht), rfl⟩

theorem xs_eq {p : ℕ} {P T B : Subgroup G} {e : ℕ} (h51 : OddPrimeClassTwoAction G p P T B e) (he : Odd e) :
    twoCoreCommutator T B = ⁅T, B⁆ := by
  unfold twoCoreCommutator
  rw [pCoreOf_sup_eq h51 he]

theorem xs_le {p : ℕ} {P T B : Subgroup G} {e : ℕ} (h51 : OddPrimeClassTwoAction G p P T B e) (he : Odd e) :
    twoCoreCommutator T B ≤ T := by
  rw [xs_eq h51 he, Subgroup.commutator_le]
  intro t ht b hb
  have hb' := (Subgroup.mem_normalizer_iff.mp (h51.normalizes he hb) t⁻¹).mp (T.inv_mem ht)
  rw [commutatorElement_def, show t * b * t⁻¹ * b⁻¹ = t * (b * t⁻¹ * b⁻¹) by group]
  exact T.mul_mem ht hb'

theorem commutator_image {p : ℕ} {P T B : Subgroup G} {e : ℕ} (h51 : OddPrimeClassTwoAction G p P T B e)
    (hP : P.Normal) (he : Odd e) :
    Sstar P T B =
      ⁅T.map (FaithfulPImageVocabulary.conjOnP P hP), Bstar P B⁆ := by
  have hS : Sstar P T B = (twoCoreCommutator T B).map (FaithfulPImageVocabulary.conjOnP P hP) :=
    (FaithfulPImageVocabulary.image_eq P hP (twoCoreCommutator T B)).symm
  have hB : Bstar P B = B.map (FaithfulPImageVocabulary.conjOnP P hP) :=
    (FaithfulPImageVocabulary.image_eq P hP B).symm
  rw [hS, hB, xs_eq h51 he, Subgroup.map_commutator]

end CFSG.LocalAnalysis.RankThreeUC.Section5.OddExponentCommutatorImage

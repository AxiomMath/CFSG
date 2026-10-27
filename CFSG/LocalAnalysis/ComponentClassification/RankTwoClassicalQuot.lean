module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicOddCore
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCore
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma22Basic
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.LocalAnalysis.ComponentClassification.AS76bExistBasic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bHypII

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ABGLocalTools

variable {Q : Type} [Group Q] [Finite Q]

local notation "O" => standardComponentOddCore Q
local notation "π" => QuotientGroup.mk' (standardComponentOddCore Q)

omit [Finite Q] in
theorem rightConjugate_map_mk' (H : Subgroup Q) (q : Q) :
    rightConjugate (H.map π) (π q) = (rightConjugate H q).map π := by
  ext y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective O y
  rw [mem_rightConjugate_iff, mem_map, mem_map]
  constructor
  · rintro ⟨h, hh, he⟩
    refine ⟨q⁻¹ * h * q, (mem_rightConjugate_iff H q _).mpr (by simpa [mul_assoc] using hh), ?_⟩
    rw [map_mul, map_mul, map_inv, he]
    group
  · rintro ⟨h, hh, he⟩
    refine ⟨q * h * q⁻¹, (mem_rightConjugate_iff H q h).mp hh, ?_⟩
    rw [map_mul, map_mul, map_inv, he]

omit [Finite Q] in
theorem mem_of_mem_sup {M N : Subgroup Q} [N.Normal] (hodd : Odd (Nat.card N))
    (hNM : N ≤ centralizer (M : Set Q)) {x : Q} (hx : x ∈ M ⊔ N) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    x ∈ M := by
  obtain ⟨m, hm, n, hn, rfl⟩ := mem_sup_of_normal_right.mp hx
  have hc : Commute m n := (mem_centralizer_iff.mp (hNM hn)) m hm
  have h1 : n ^ 2 ^ k = (m ^ 2 ^ k)⁻¹ := by
    rw [hc.mul_pow] at hk
    exact eq_inv_of_mul_eq_one_right hk
  have hcop : Nat.Coprime (2 ^ k) (orderOf n) := by
    refine Nat.Coprime.pow_left k (Nat.prime_two.coprime_iff_not_dvd.mpr fun h2 => ?_)
    have : Odd (orderOf n) := by
      have h := Subgroup.orderOf_dvd_natCard N hn
      exact hodd.of_dvd_nat h
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h2)
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  have hnM : n ∈ M := by
    rw [← hj, h1]
    exact pow_mem (inv_mem (pow_mem hm _)) j
  exact mul_mem hm hnM

theorem inf_eq_bot_of_two {P N : Subgroup Q} (hP : IsPGroup 2 P) (hodd : Odd (Nat.card N)) :
    P ⊓ N = ⊥ :=
  AschbacherTightEmbedding.two_subgroup_of_odd_eq_bot _ N hP.to_inf_left hodd inf_le_right

theorem mk'_injOn_of_two {P : Subgroup Q} (hP : IsPGroup 2 P) {x y : Q} (hx : x ∈ P) (hy : y ∈ P)
    (h : π x = π y) : x = y := by
  have h1 : x⁻¹ * y ∈ P ⊓ O := by
    rw [mem_inf]
    refine ⟨mul_mem (inv_mem hx) hy, ?_⟩
    rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [inf_eq_bot_of_two hP RankTwoSporadic.odd_card_standardComponentOddCore, mem_bot,
    inv_mul_eq_one] at h1
  exact h1

theorem card_map_mk'_of_two {P : Subgroup Q} (hP : IsPGroup 2 P) :
    Nat.card (P.map π) = Nat.card P :=
  (Nat.card_congr (Equiv.ofBijective ((QuotientGroup.mk' O).subgroupMap P)
    ⟨fun x y hxy => Subtype.ext (mk'_injOn_of_two hP x.2 y.2 (congrArg Subtype.val hxy)),
      (QuotientGroup.mk' O).subgroupMap_surjective P⟩)).symm

theorem oddCore_le_of_rankTwoHyp {M : Subgroup Q} (hH : RankTwoHyp Q M) :
    O ≤ centralizer (M : Set Q) :=
  standardComponentOddCore_le_centralizer hH.standard hH.rank

section Standard

variable {M : Subgroup Q} (hH : RankTwoHyp Q M)
include hH

theorem rankTwoHyp_map : RankTwoHyp (Q ⧸ O) (M.map π) := by
  have hodd := odd_card_standardComponentOddCore (G := Q)
  have hNA := (oddCore_le_of_rankTwoHyp hH)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact CatalogueKProperOver.kProper_quotient (fun e h => SectionRank.catalog_of_mulEquiv e h)
      hH.kProper _
  · exact standard_map hH.standard hodd hNA
  · intro hn
    apply hH.not_normal
    have h1 : (M ⊔ O).Normal := by
      have := hn.comap (QuotientGroup.mk' O)
      rwa [comap_map_eq, QuotientGroup.ker_mk'] at this
    rw [← normalizer_eq_top_iff, ← normalizer_sup_eq hodd hNA hH.standard.1.1]
    exact normalizer_eq_top_iff.mpr h1
  · exact two_le_pRank_map hodd hNA hH.standard.1.1 hH.rank

noncomputable def quotCenterMap : rankTwoQuot M ≃* rankTwoQuot (M.map π) :=
  quotCenterEquivMap (oddCore_le_of_rankTwoHyp hH) hH.standard.1.1

theorem odd_card_center_map (hZ : Odd (Nat.card (center ↥M))) :
    Odd (Nat.card (center ↥(M.map π))) := by
  set f := (QuotientGroup.mk' O).subgroupMap M
  have hle : center ↥(M.map π) ≤ (center ↥M).map f := by
    intro z hz
    obtain ⟨m, rfl⟩ := (QuotientGroup.mk' O).subgroupMap_surjective M z
    refine ⟨m, ?_, rfl⟩
    change m ∈ center ↥M
    rw [← ker_quotCenter_map (oddCore_le_of_rankTwoHyp hH) hH.standard.1.1, MonoidHom.mem_ker,
      MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hz
  exact hZ.of_dvd_nat ((card_dvd_of_le hle).trans (card_map_dvd _ _))

theorem isSylowOf_map {R : Subgroup Q} (hR : IsSylowOf 2 R (centralizer (M : Set Q))) :
    IsSylowOf 2 (R.map π) (centralizer ((M.map π : Subgroup (Q ⧸ O)) : Set (Q ⧸ O))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [centralizer_map_eq odd_card_standardComponentOddCore (oddCore_le_of_rankTwoHyp hH)
    hH.standard.1.1]
  exact RankTwoSporadic.IsSylowOf.map hR π

theorem not_conj_le_map {R : Subgroup Q} (hR : IsPGroup 2 R)
    (hno : ∀ x : Q, ¬ rightConjugate R x ≤ M) (h : Q ⧸ O) :
    ¬ rightConjugate (R.map π) h ≤ M.map π := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective O h
  rw [rightConjugate_map_mk']
  intro hle
  apply hno q
  intro x hx
  have hxMO : x ∈ M ⊔ O := by
    have : x ∈ (M.map π).comap π := hle ⟨x, hx, rfl⟩
    rwa [comap_map_eq, QuotientGroup.ker_mk'] at this
  have hRq : IsPGroup 2 (rightConjugate R q) := hR.map _
  obtain ⟨k, hk⟩ := hRq ⟨x, hx⟩
  exact mem_of_mem_sup odd_card_standardComponentOddCore (oddCore_le_of_rankTwoHyp hH) hxMO
    (by simpa using congrArg Subtype.val hk)

theorem exists_lift {R : Subgroup Q} (hR : IsPGroup 2 R) {t : Q ⧸ O} (ht : t ^ 2 = 1)
    (htM : t ∈ normalizer ((M.map π : Subgroup (Q ⧸ O)) : Set (Q ⧸ O)))
    (htR : t ∈ normalizer ((R.map π : Subgroup (Q ⧸ O)) : Set (Q ⧸ O))) :
    ∃ b : Q, b ^ 2 = 1 ∧ π b = t ∧ b ∈ normalizer (M : Set Q) ∧
      b ∈ normalizer (R : Set Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := odd_card_standardComponentOddCore (G := Q)
  set Rb := R.map π with hRb
  set Tb := Rb ⊔ zpowers t with hTb
  have hz : IsPGroup 2 (zpowers t) := by
    have ht' : t ^ 2 ^ 1 = 1 := by rwa [pow_one]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one ht')
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hTb2 : IsPGroup 2 Tb :=
    IsPGroup.to_sup_of_normal_left' (hR.map π) hz (zpowers_le.mpr htR)
  set X := Tb.comap π with hX
  have hRX : R ≤ X := fun r hr => mem_sup_left ⟨r, hr, rfl⟩
  obtain ⟨S, hS, hRS⟩ : ∃ S : Subgroup Q, IsSylowOf 2 S X ∧ R ≤ S := by
    have hR' : IsPGroup 2 (R.subgroupOf X) := hR.comap_subtype
    obtain ⟨P, hP⟩ := hR'.exists_le_sylow
    refine ⟨(P : Subgroup X).map X.subtype, ⟨P, rfl⟩, fun x hx => ?_⟩
    exact ⟨⟨x, hRX hx⟩, hP (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hS2 := hS.isPGroup
  have hXmap : X.map π = Tb := map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O) _
  have hSmap : S.map π = Tb := by
    have h1 := RankTwoSporadic.IsSylowOf.map hS π
    rw [hXmap] at h1
    exact (h1.eq_of_le h1.le le_rfl hTb2).symm
  obtain ⟨b, hbS, hbt⟩ : ∃ b ∈ S, π b = t := by
    have : t ∈ S.map π := by
      rw [hSmap]
      exact mem_sup_right (mem_zpowers t)
    obtain ⟨b, hb, hbt⟩ := this
    exact ⟨b, hb, hbt⟩
  refine ⟨b, ?_, hbt, ?_, ?_⟩
  ·
    refine mk'_injOn_of_two hS2 (pow_mem hbS 2) (one_mem S) ?_
    rw [map_pow, hbt, ht, map_one]
  ·
    rw [← normalizer_sup_eq hodd (oddCore_le_of_rankTwoHyp hH) hH.standard.1.1, mem_normalizer_iff]
    intro y
    have hiff : ∀ z : Q, z ∈ M ⊔ O ↔ π z ∈ M.map π := by
      intro z
      rw [← mem_comap, comap_map_eq, QuotientGroup.ker_mk']
    rw [hiff, hiff, map_mul, map_mul, map_inv, hbt]
    exact mem_normalizer_iff.mp htM (π y)
  ·
    have hRle : R ≤ S ⊓ Rb.comap π := by
      refine le_inf hRS fun r hr => ?_
      rw [mem_comap]
      exact mem_map_of_mem (QuotientGroup.mk' O) hr
    have hReq : R = S ⊓ Rb.comap π := by
      refine Subgroup.eq_of_le_of_card_ge hRle ?_
      have h2 : IsPGroup 2 ↥(S ⊓ Rb.comap π) := hS2.to_inf_left
      rw [← card_map_mk'_of_two h2, ← card_map_mk'_of_two hR]
      exact card_le_of_le (map_le_iff_le_comap.mpr inf_le_right)
    rw [hReq, mem_normalizer_iff]
    intro y
    rw [mem_inf, mem_inf, mem_comap, mem_comap, map_mul, map_mul, map_inv, hbt,
      ← mem_normalizer_iff.mp htR (π y), ← mem_normalizer_iff.mp (le_normalizer hbS) y]

end Standard

section Equiv

variable {H H' : Type*} [Group H] [Group H'] (e : H ≃* H')

omit [Finite Q] in
theorem centralizer_map_equiv (S : Subgroup H) :
    centralizer ((S.map e.toMonoidHom : Subgroup H') : Set H') =
      (centralizer (S : Set H)).map e.toMonoidHom := by
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [mem_map_equiv, MulEquiv.symm_apply_apply, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h s hs
    apply e.injective
    rw [map_mul, map_mul]
    exact h (e s) ⟨s, hs, rfl⟩
  · rintro h _ ⟨s, hs, rfl⟩
    change e s * e y = e y * e s
    rw [← map_mul, ← map_mul, h s hs]

omit [Finite Q] in
theorem map_conj_map_equiv (K : Subgroup H) (g : H) :
    (K.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom =
      (K.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp

omit [Finite Q] in
theorem standardComponentIsStandard_map_equiv {M : Subgroup H}
    (hM : standardComponentIsStandard M) : standardComponentIsStandard (M.map e.toMonoidHom) :=
  CFSG.Open.standardComponentIsStandard.map_mulEquiv e hM

end Equiv

theorem centralizer_normalClosure_eq_bot {M : Subgroup Q} (hH : RankTwoHyp Q M)
    (hO : O = ⊥) : centralizer (normalClosure (M : Set Q) : Set Q) = ⊥ := by
  set N := centralizer (normalClosure (M : Set Q) : Set Q) with hNdef
  have hNn : N.Normal := normal_centralizer
  have hNK : N ≤ centralizer (M : Set Q) := centralizer_le subset_normalClosure
  obtain ⟨g, hg⟩ : ∃ g : Q, g ∉ normalizer (centralizer (M : Set Q) : Set Q) := by
    by_contra h
    push Not at h
    apply hH.not_normal
    rw [← normalizer_eq_top_iff, ← hH.standard.2.2.2.1, eq_top_iff]
    exact fun x _ => h x
  have hodd := hH.standard.2.2.1 g hg
  have hle : N ≤ centralizer (M : Set Q) ⊓
      (centralizer (M : Set Q)).map (MulAut.conj g).toMonoidHom := by
    refine le_inf hNK fun n hn => ⟨g⁻¹ * n * g, hNK (hNn.conj_mem' _ hn g), ?_⟩
    simp [mul_assoc]
  rw [eq_bot_iff, ← hO]
  exact le_standardComponentOddCore hNn (hodd.of_dvd_nat (card_dvd_of_le hle))

end CFSG.ComponentClassification.RankTwoClassical

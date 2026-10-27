module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Fixed
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTypeRank
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedL34
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitReduction
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2022
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_modCentralizer (C H : Subgroup G) :
    ∃ P : Subgroup G, ∀ c, c ∈ P ↔ c ∈ C ∧ ∀ y ∈ H, c * y * c⁻¹ * y⁻¹ ∈ oddIn C := by
  have hconj : ∀ c ∈ C, ∀ o ∈ oddIn C, c * o * c⁻¹ ∈ oddIn C := fun c hc o ho =>
    (mem_normalizer_iff.mp (normalizer_le_normalizer_oddIn C (le_normalizer hc)) o).mp ho
  let P : Subgroup G :=
    { carrier := {c | c ∈ C ∧ ∀ y ∈ H, c * y * c⁻¹ * y⁻¹ ∈ oddIn C}
      one_mem' := ⟨one_mem _, fun y _ => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun y hy => by
        have e : a * b * y * (a * b)⁻¹ * y⁻¹ =
            a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ * (a * y * a⁻¹ * y⁻¹) := by group
        rw [e]
        exact mul_mem (hconj a ha.1 _ (hb.2 y hy)) (ha.2 y hy)⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun y hy => by
        have e : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = a⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact hconj a⁻¹ (inv_mem ha.1) _ (inv_mem (ha.2 y hy))⟩ }
  exact ⟨P, fun c => Iff.rfl⟩

theorem commute_mod_of_ne {C K M : Subgroup G} (hKC : K ≤ C) (hMC : M ≤ C)
    (hK : IsPComponent 2 (K.subgroupOf C)) (hM : IsPComponent 2 (M.subgroupOf C)) (hne : K ≠ M) :
    ∀ k ∈ K, ∀ m ∈ M, k * m * k⁻¹ * m⁻¹ ∈ oddIn C := by
  intro k hk m hm
  have h := (commutator_le_of_ne hKC hMC hK hM hne).1 (commutator_mem_commutator hk hm)
  rwa [commutatorElement_def] at h

theorem not_commute_mod_of_not_mem_zStarIn {C K : Subgroup G} (hKC : K ≤ C) {k : G}
    (hkK : k ∈ K) (hkZ : k ∉ zStarIn K) : ¬ ∀ x ∈ K, k * x * k⁻¹ * x⁻¹ ∈ oddIn C := by
  intro h
  apply hkZ
  refine ⟨⟨k, hkK⟩, GSThmB.OddQuot.mem_fusionZStar_iff.mpr fun m => ?_, rfl⟩
  have h1 : k * m * k⁻¹ * (m : G)⁻¹ ∈ oddIn C ⊓ K :=
    mem_inf.mpr ⟨h m m.2, mul_mem (mul_mem (mul_mem hkK m.2) (inv_mem hkK)) (inv_mem m.2)⟩
  obtain ⟨y, hy, hyeq⟩ := inf_oddIn_le_oddIn hKC h1
  have e : ⁅(⟨k, hkK⟩ : ↥K), m⁆ = y := by
    apply Subtype.ext
    rw [show ((y : ↥K) : G) = k * m * k⁻¹ * (m : G)⁻¹ from hyeq, commutatorElement_def]
    simp
  rw [e]
  exact hy

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers' {x y : G} (hx : x * x = 1) (hy : y ∈ zpowers x) :
    y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hx, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hx, one_zpow, one_mul, zpow_one]

theorem exists_involution_of_swap {C K : Subgroup G} {t z k : G} (hKC : K ≤ C)
    (hK : IsPComponent 2 (K.subgroupOf C)) (hK'C : conjugate K t ≤ C)
    (hK' : IsPComponent 2 ((conjugate K t).subgroupOf C)) (hne : K ≠ conjugate K t)
    (ht : t * t = 1) (htC : t ∈ C) (hz : z * z = 1) (hzC' : z ∈ C)
    (hzC : ∀ c ∈ C, z * c = c * z)
    (hkK : k ∈ K) (hk : k * k = 1) (hkZ : k ∉ zStarIn K) :
    ∃ w ∈ K ⊔ conjugate K t, w * w = 1 ∧ w * t = t * w ∧ w ∉ zpowers t ⊔ zpowers z := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hkinv : k⁻¹ = k := inv_eq_of_mul_eq_one_right hk
  set K' := conjugate K t with hK'def
  set k' := t * k * t⁻¹ with hk'
  have hk'K' : k' ∈ K' := ⟨k, hkK, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hk', htinv]⟩
  have hk'inv : k'⁻¹ = k' := by
    rw [hk', mul_inv_rev, mul_inv_rev, inv_inv, hkinv, htinv, mul_assoc]
  have hcomm := commute_mod_of_ne hKC hK'C hK hK' hne
  have hcomm' := commute_mod_of_ne hK'C hKC hK' hK (Ne.symm hne)
  obtain ⟨P, hP⟩ := exists_modCentralizer C K
  have hkP : k ∉ P := fun h => not_commute_mod_of_not_mem_zStarIn hKC hkK hkZ ((hP k).mp h).2
  have hk'P : k' ∈ P := (hP k').mpr ⟨hK'C hk'K', fun x hx => hcomm' k' hk'K' x hx⟩
  have hOP : ∀ o ∈ oddIn C, o ∈ P := by
    intro o ho
    refine (hP o).mpr ⟨map_subtype_le _ ho, fun x hx => ?_⟩
    have hxN : x ∈ normalizer (oddIn C : Set G) :=
      normalizer_le_normalizer_oddIn C (le_normalizer (hKC hx))
    have h1 := (mem_normalizer_iff.mp hxN o⁻¹).mp (inv_mem ho)
    rw [show o * x * o⁻¹ * x⁻¹ = o * (x * o⁻¹ * x⁻¹) by group]
    exact mul_mem ho h1
  have hzP : z ∈ P := by
    refine (hP z).mpr ⟨hzC', fun x hx => ?_⟩
    rw [hzC x (hKC hx), mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  set r := k * k' with hr
  have hrP : r ∈ P → False := by
    intro h
    apply hkP
    have : k = r * k'⁻¹ := by rw [hr, mul_inv_cancel_right]
    rw [this]
    exact mul_mem h (inv_mem hk'P)
  have hr2 : r * r ∈ oddIn C := by
    have h := hcomm k hkK k' hk'K'
    rwa [hkinv, hk'inv, show k * k' * k * k' = r * r by rw [hr]; group] at h
  have hoddC : Odd (Nat.card (oddIn C)) := by
    rw [oddIn, card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hr2odd : Odd (orderOf (r * r)) :=
    hoddC.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hr2)
  have htr : t * r * t⁻¹ = r⁻¹ := by
    rw [hr, mul_inv_rev, hk'inv, hkinv, hk', htinv]
    calc t * (k * (t * k * t)) * t = t * k * t * k * (t * t) := by group
      _ = t * k * t * k := by rw [ht, mul_one]
  rcases Nat.even_or_odd (orderOf r) with ⟨m, hm⟩ | ⟨m, hm⟩
  ·
    have hm0 : 0 < m := by
      have := orderOf_pos r
      omega
    have hmo : orderOf (r * r) = m := by
      rw [← pow_two, orderOf_pow_of_dvd (by norm_num) (by rw [hm]; exact ⟨m, by ring⟩), hm]
      omega
    rw [hmo] at hr2odd
    obtain ⟨j, hj⟩ := hr2odd
    refine ⟨r ^ m, pow_mem (mul_mem (mem_sup_left hkK) (mem_sup_right hk'K')) m, ?_, ?_, ?_⟩
    · rw [← pow_add, ← hm, pow_orderOf_eq_one]
    · have h1 : t * r ^ m * t⁻¹ = (r ^ m)⁻¹ := by
        rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, htr, inv_pow]
      have h2 : (r ^ m)⁻¹ = r ^ m := inv_eq_of_mul_eq_one_right (by
        rw [← pow_add, ← hm, pow_orderOf_eq_one])
      calc r ^ m * t = (t * r ^ m * t⁻¹) * t := by rw [h1, h2]
        _ = t * r ^ m := by group
    · intro hw
      obtain ⟨i, h, hh, hwh⟩ := mem_zpowers_sup (fun y hy => by
        obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp hy
        exact (Commute.zpow_right (show Commute t z from (hzC t htC).symm) l).eq) hw
      rcases eq_one_or_eq_of_mem_zpowers' ht (zpow_mem (mem_zpowers t) i) with h1 | h1
      ·
        rw [h1, one_mul] at hwh
        apply hrP
        have hrm : r = r ^ m * (r * r)⁻¹ ^ j := by
          rw [hj]
          group
        rw [hrm]
        refine mul_mem ?_ (pow_mem (inv_mem (hOP _ hr2)) j)
        rcases eq_one_or_eq_of_mem_zpowers' hz hh with h2 | h2
        · rw [hwh, h2]
          exact one_mem _
        · rw [hwh, h2]
          exact hzP
      ·
        rw [h1] at hwh
        apply hne
        have hK'N := (commutator_le_of_ne hKC hK'C hK hK' hne).2
        have hzN : z ∈ normalizer (K : Set G) :=
          mem_normalizer_of_commute fun y hy => hzC y (hKC hy)
        have hrN : r ^ m ∈ normalizer (K : Set G) :=
          pow_mem (mul_mem (le_normalizer hkK) (hK'N hk'K')) m
        have htN : t ∈ normalizer (K : Set G) := by
          have : t = r ^ m * h⁻¹ := by rw [hwh]; group
          rw [this]
          exact mul_mem hrN (inv_mem ((zpowers_le.mpr hzN) hh))
        exact (conjugate_eq_self htN).symm
  ·
    exfalso
    apply hrP
    have hrr : r = (r * r) ^ (m + 1) := by
      rw [← pow_two, ← pow_mul, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, ← hm,
        pow_orderOf_eq_one, one_mul]
    rw [hrr]
    exact hOP _ (pow_mem hr2 _)

omit [Finite G] in
theorem mem_four_of_mem_sup {t z x : G} (ht : t * t = 1) (hz : z * z = 1) (htz : t * z = z * t)
    (hx : x ∈ zpowers t ⊔ zpowers z) : x = 1 ∨ x = t ∨ x = z ∨ x = t * z := by
  obtain ⟨i, h, hh, rfl⟩ := mem_zpowers_sup (fun y hy => by
    obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute t z from htz) l).eq) hx
  rcases eq_one_or_eq_of_mem_zpowers' ht (zpow_mem (mem_zpowers t) i) with h1 | h1 <;>
    rcases eq_one_or_eq_of_mem_zpowers' hz hh with h2 | h2 <;> rw [h1, h2] <;> simp

theorem exists_four_le_of_two_le_pRank {K : Subgroup G} (h : 2 ≤ pRank 2 ↥K) :
    ∃ W ≤ K, IsElemTwo W ∧ Nat.card W = 4 := by
  obtain ⟨A, hA, h4⟩ := LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank h
  refine ⟨A.map K.subtype, map_subtype_le _, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  · rintro _ ⟨a, ha, rfl⟩
    have h1 := hA.2 a ha
    rw [pow_two] at h1
    exact congrArg Subtype.val h1
  · rw [card_map_of_injective (subtype_injective K), h4]

theorem l2_type_facts {C K : Subgroup G} (hKC : K ≤ C) (hK : IsPComponent 2 (K.subgroupOf C))
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 2 p f) :
    (∀ x ∈ K, x * x = 1 → x ∈ zStarIn K → x = 1) ∧ pRank 2 ↥K = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (K ⧸ pPrimeCore 2 K) := isSimpleGroup_of_lieModel_psl_two h
  obtain ⟨-, -, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K C hKC).mp hK
  obtain ⟨-, -, a, b, hab⟩ := id hq
  have hnab : ∃ x y : K ⧸ pPrimeCore 2 K, x * y ≠ y * x := by
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h' => hab (by rw [← QuotientGroup.mk_mul, h', QuotientGroup.mk_mul])⟩
  have hcen : center (K ⧸ pPrimeCore 2 K) = ⊥ := by
    rcases (inferInstance : (center (K ⧸ pPrimeCore 2 K)).Normal).eq_bot_or_eq_top with h1 | h1
    · exact h1
    · obtain ⟨x, y, hxy⟩ := hnab
      exact absurd ((mem_center_iff.mp (h1 ▸ mem_top x)) y).symm hxy
  refine ⟨fun x hxK hx2 hxZ => ?_, ?_⟩
  · obtain ⟨x', hx', rfl⟩ := hxZ
    rw [Sol78.fusionZStar_eq_comap, SetLike.mem_coe, mem_comap, hcen, mem_bot,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
    have hodd : Odd (orderOf x') :=
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat
        (Subgroup.orderOf_dvd_natCard _ hx')
    have h2 : orderOf x' ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [pow_two]
      exact Subtype.ext hx2)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h3 | h3
    · rw [orderOf_eq_one_iff] at h3
      rw [h3]
      rfl
    · rw [h3] at hodd
      exact absurd hodd (by decide)
  · have hodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥K) := by
      intro hd
      exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
        (even_iff_two_dvd.mpr hd)
    rw [← GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hodd]
    refine le_antisymm ?_
      (LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hq
        (by rw [hcen, card_bot]; exact odd_one))
    obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := FooteLit.statedClassicalModel_of_lieModel_psl_two h
    have hdih : GorensteinWalter.HasDihedralSylowTwo
        (Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSL 2 F)) :=
      OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv
        (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
        (GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F
          ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hcard⟩)
    exact FooteLit.pRank_le_two_of_hasDihedralSylowTwo
      (OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv e hdih)

theorem exists_involution_of_two_le_pRank {K : Subgroup G} {t z : G} (ht : t * t = 1)
    (hz : z * z = 1) (htz : t * z = z * t) (htN : t ∈ normalizer (K : Set G)) (hzK : z ∉ K)
    (hzc : ∀ k ∈ K, z * k = k * z) (h2 : 2 ≤ pRank 2 ↥K) :
    ∃ w ∈ K, w * w = 1 ∧ w * t = t * w ∧ w ∉ zpowers t ⊔ zpowers z := by
  obtain ⟨W, hWK, hW, hW4⟩ := exists_four_le_of_two_le_pRank h2
  obtain ⟨k, hkW, hk1⟩ : ∃ k ∈ W, k ≠ 1 := by
    by_contra hall
    push Not at hall
    have : W = ⊥ := eq_bot_iff.mpr fun x hx => mem_bot.mpr (hall x hx)
    rw [this, card_bot] at hW4
    omega
  obtain ⟨w₀, hw₀K, hw₀2, hw₀1, hw₀t⟩ :=
    exists_involution_commute_of_mem ht htN (hWK hkW) (hW.2 k hkW) hk1
  by_cases hw₀ : w₀ ∈ zpowers t ⊔ zpowers z
  ·
    have htw₀ : t = w₀ ∨ t = w₀ * z := by
      rcases mem_four_of_mem_sup ht hz htz hw₀ with h | h | h | h
      · exact absurd h hw₀1
      · exact Or.inl h.symm
      · exact absurd (h ▸ hw₀K) hzK
      · right
        rw [h, mul_assoc, hz, mul_one]
    obtain ⟨w', hw'2, hw'1, hw'ne, hw'c⟩ := exists_involution_commute_ne h2
      (k := (⟨w₀, hw₀K⟩ : ↥K)) (Subtype.ext hw₀2) (fun h => hw₀1 (congrArg Subtype.val h))
    have hw'c' : (w' : G) * w₀ = w₀ * w' := congrArg Subtype.val hw'c
    have hw'z : (w' : G) * z = z * w' := (hzc _ w'.2).symm
    refine ⟨w', w'.2, congrArg Subtype.val hw'2, ?_, fun hw' => ?_⟩
    · rcases htw₀ with rfl | rfl
      · exact hw'c'
      · rw [← mul_assoc, hw'c', mul_assoc, hw'z, mul_assoc]
    · rcases mem_four_of_mem_sup ht hz htz hw' with h | h | h | h
      · exact hw'1 (Subtype.ext h)
      · rcases htw₀ with h' | h'
        · exact hw'ne (Subtype.ext (h.trans h'))
        · apply hzK
          have : z = w₀⁻¹ * w' := by rw [h, h']; group
          rw [this]
          exact mul_mem (inv_mem hw₀K) w'.2
      · exact hzK (h ▸ w'.2)
      · rcases htw₀ with h' | h'
        · apply hzK
          have : z = w₀⁻¹ * w' := by rw [h, h']; group
          rw [this]
          exact mul_mem (inv_mem hw₀K) w'.2
        · apply hw'ne
          apply Subtype.ext
          rw [h, h', mul_assoc, hz, mul_one]
  · exact ⟨w₀, hw₀K, hw₀2, hw₀t, hw₀⟩

omit [Finite G] in
theorem conjugate_conjugate_self {K : Subgroup G} {t : G} (ht : t * t = 1) :
    conjugate (conjugate K t) t = K := by
  rw [conjugate_conjugate'', ht]
  ext y
  simp [conjugate]

omit [Finite G] in
theorem mem_coreActionKernel_of_commute {L : Subgroup G} {c : G} (h : ∀ l ∈ L, c * l = l * c) :
    c ∈ coreActionKernel L := by
  refine mem_coreActionKernel.mpr ⟨mem_normalizer_of_commute h, fun j hj => ?_⟩
  rw [show j⁻¹ * c⁻¹ * j * c = j⁻¹ * c⁻¹ * (j * c) by group, ← h j hj]
  rw [show j⁻¹ * c⁻¹ * (c * j) = 1 by group]
  exact one_mem _

theorem false_of_ne_of_setting (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {z : G}
    (hzQ : z ∈ S ⊓ coreActionKernel L) (hz : orderOf z = 2) {M : Subgroup G}
    (hMz : M ≤ centralizer ({z} : Set G))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({z} : Set G))))
    (hTM : gsFixedLayer L z ≤ M) {K : Subgroup G} (hKz : K ≤ centralizer ({z} : Set G))
    (hKp : IsPComponent 2 (K.subgroupOf (centralizer ({z} : Set G))))
    (htype : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
        Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 2 p f) ∨
      IsL34Type (K ⧸ Open.fusionZStar K))
    (hKM : K ≠ M) (hMt : conjugate M t = M) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hCN := centralizer_le_normalizer_of_setting hS hU hheld hSol hGW hMax hset
  have hE8 : ∀ E : Subgroup G, IsEightGroup E → E ≤ coreActionKernel L → False :=
    fun E hE hEK => false_of_eightGroup_le_coreActionKernel hS hU hheld hSol hGW hset hE hEK
  obtain ⟨hbase, hfam, -, -, -, -, -⟩ := hset
  obtain ⟨hsimple, hnonab, hK, -, -, -, -, -⟩ := hbase
  obtain ⟨⟨-, -, -, -, -, hto, -, -⟩, -, -, -, -⟩ := hfam
  have : IsSimpleGroup G := hsimple
  obtain ⟨hzS, hzK⟩ := mem_inf.mp hzQ
  have htz : t * z = z * t := (hZS z hzS).symm
  have hz1 : z ≠ 1 := by rintro rfl; simp at hz
  have ht1 : t ≠ 1 := by rintro rfl; simp at hto
  have hz2 : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have hzZ : z ∉ center G := not_mem_center_of_ne_one hnonab hz1
  obtain ⟨hTtz, -, -, hTset, -, -⟩ := gsFixedLayer_facts hS hK hto hz htz hzZ hLt hLpt hzK
  obtain ⟨hTL, -⟩ := gsFixedLayer_sup_oddIn hTset
  have hTz : gsFixedLayer L z ≤ centralizer ({z} : Set G) := hTtz.trans inf_le_right
  have htK : t ∈ coreActionKernel L := mem_coreActionKernel_of_commute fun l hl =>
    (mem_centralizer_singleton_iff.mp (hLt hl)).symm
  set C := centralizer ({z} : Set G) with hC
  have htC : t ∈ C := mem_centralizer_singleton_iff.mpr htz
  have hzC' : z ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hzC : ∀ c ∈ C, z * c = c * z := fun c hc => (mem_centralizer_singleton_iff.mp hc).symm
  obtain ⟨hK'z, hK'p⟩ := UGSChain.conjugate_isPComponent_centralizer htz hKz hKp
  have hK'M : conjugate K t ≠ M := by
    intro h
    apply hKM
    rw [← conjugate_conjugate_self (K := K) ht2, h, hMt]
  obtain ⟨P, hP⟩ := exists_modCentralizer C M
  have hKP : K ⊔ conjugate K t ≤ P := sup_le
    (fun k hk => (hP k).mpr ⟨hKz hk, commute_mod_of_ne hKz hMz hKp hMp hKM k hk⟩)
    (fun k hk => (hP k).mpr ⟨hK'z hk, commute_mod_of_ne hK'z hMz hK'p hMp hK'M k hk⟩)
  have hker : ∀ c ∈ K ⊔ conjugate K t, c * t = t * c → c ∈ coreActionKernel L := by
    intro c hc hct
    exact mem_coreActionKernel_of_fixedLayer hTL hTz hTset
      (hCN (mem_centralizer_singleton_iff.mpr hct)) fun y hy => ((hP c).mp (hKP hc)).2 y (hTM hy)
  have hfin : z ≠ t → ∀ w ∈ K ⊔ conjugate K t, w * w = 1 → w * t = t * w →
      w ∉ zpowers t ⊔ zpowers z → False := by
    intro hzt w hw hw2 hwt hwn
    have htn : t ∉ zpowers z := by
      intro h
      rcases eq_one_or_eq_of_mem_zpowers' hz2 h with h1 | h1
      · exact ht1 h1
      · exact hzt h1.symm
    obtain ⟨hB, hBc⟩ := elemTwo_zpowers_sup ht2 (isElemTwo_zpowers hz2) (fun y hy => by
      obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (show Commute t z from htz) l).eq) htn
    have hwz : w * z = z * w :=
      (hzC w (sup_le hKz hK'z hw)).symm
    obtain ⟨hE, hEc⟩ := elemTwo_zpowers_sup hw2 hB (fun y hy => by
      have hle : zpowers t ⊔ zpowers z ≤ centralizer ({w} : Set G) := sup_le
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hwt.symm))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hwz.symm))
      exact (mem_centralizer_singleton_iff.mp (hle hy)).symm) hwn
    refine hE8 _ ⟨hE, by rw [hEc, hBc, Nat.card_zpowers, hz]⟩ (sup_le ?_ (sup_le ?_ ?_))
    · exact zpowers_le.mpr (hker w hw hwt)
    · exact zpowers_le.mpr htK
    · exact zpowers_le.mpr hzK
  have hperf : ⁅K, K⁆ = K := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hKp
    have h2 : Group.IsPerfect K := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hKz).toMonoidHom) (subgroupOfEquivOfLe hKz).surjective
    exact (Subgroup.isPerfect_iff (H := K)).mp h2
  have hzcK : ∀ k ∈ K, z * k = k * z := fun k hk => hzC k (hKz hk)
  have hzZK : z ∈ K → z ∈ zStarIn K := fun h =>
    inf_centralizer_le_zStarIn' K (mem_inf.mpr ⟨h, mem_centralizer_iff.mpr fun k hk =>
      (hzcK k hk).symm⟩)
  by_cases hzt : z = t
  ·
    have hKt : ∀ k ∈ K, k * t = t * k := fun k hk => by
      rw [← hzt]
      exact mem_centralizer_singleton_iff.mp (hKz hk)
    have hKker : K ≤ coreActionKernel L := fun k hk => hker k (mem_sup_left hk) (hKt k hk)
    rcases htype with ⟨p, f, hp, hp2, hf, hL⟩ | hL
    · obtain ⟨hinv, hrank⟩ := l2_type_facts hKz hKp hp hp2 hf hL
      obtain ⟨W, hWK, hW, hW4⟩ := exists_four_le_of_two_le_pRank hrank.ge
      have htW : t ∉ W := by
        intro h
        apply ht1
        apply hinv t (hWK h) ht2
        rw [← hzt]
        exact hzZK (hzt ▸ hWK h)
      obtain ⟨hE, hEc⟩ := elemTwo_zpowers_sup ht2 hW (fun y hy => (hKt y (hWK hy)).symm) htW
      exact hE8 _ ⟨hE, by rw [hEc, hW4]⟩
        (sup_le (zpowers_le.mpr htK) (hWK.trans hKker))
    · obtain ⟨E, hEK, hE⟩ := exists_eightGroup_of_three_le_pRank (Q := K)
        (three_le_pRank_of_l34 hL)
      exact hE8 E hE (hEK.trans hKker)
  by_cases hKt : conjugate K t = K
  ·
    have htN : t ∈ normalizer (K : Set G) := mem_normalizer_of_conjugate_eq hKt
    rcases htype with ⟨p, f, hp, hp2, hf, hL⟩ | hL
    · obtain ⟨hinv, hrank⟩ := l2_type_facts hKz hKp hp hp2 hf hL
      have hzK' : z ∉ K := fun h => hz1 (hinv z h hz2 (hzZK h))
      obtain ⟨w, hwK, hw2, hwt, hwn⟩ :=
        exists_involution_of_two_le_pRank ht2 hz2 htz htN hzK' hzcK hrank.ge
      exact hfin hzt w (mem_sup_left hwK) hw2 hwt hwn
    · obtain ⟨w, hwK, hw2, hwt, hwZ, hwk⟩ := hL34 G K t hperf hL ht2 htN
      refine hfin hzt w (mem_sup_left hwK) hw2 hwt fun hw => ?_
      have hzk : z ∈ coreActionKernel K := mem_coreActionKernel_of_commute hzcK
      rcases mem_four_of_mem_sup ht2 hz2 htz hw with h | h | h | h
      · exact hwZ (h ▸ one_mem _)
      · exact hwk (by rw [h, inv_mul_cancel]; exact one_mem _)
      · exact hwZ (h ▸ hzZK (h ▸ hwK))
      · exact hwk (by rw [h, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]; exact inv_mem hzk)
  ·
    obtain ⟨k, hkK, hk2, hkZ⟩ : ∃ k ∈ K, k * k = 1 ∧ k ∉ zStarIn K := by
      rcases htype with ⟨p, f, hp, hp2, hf, hL⟩ | hL
      · obtain ⟨hinv, hrank⟩ := l2_type_facts hKz hKp hp hp2 hf hL
        obtain ⟨W, hWK, hW, hW4⟩ := exists_four_le_of_two_le_pRank hrank.ge
        obtain ⟨k, hkW, hk1⟩ : ∃ k ∈ W, k ≠ 1 := by
          by_contra hall
          push Not at hall
          have : W = ⊥ := eq_bot_iff.mpr fun x hx => mem_bot.mpr (hall x hx)
          rw [this, card_bot] at hW4
          omega
        exact ⟨k, hWK hkW, hW.2 k hkW, fun h => hk1 (hinv k (hWK hkW) (hW.2 k hkW) h)⟩
      · exact exists_involution_not_mem_zStarIn hL
    obtain ⟨w, hw, hw2, hwt, hwn⟩ := exists_involution_of_swap hKz hKp hK'z hK'p
      (fun h => hKt h.symm) ht2 htC hz2 hzC' hzC hkK hk2 hkZ
    exact hfin hzt w hw hw2 hwt hwn

theorem isPComponent_eq_of_setting (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {z : G}
    (hzQ : z ∈ S ⊓ coreActionKernel L) (hz : orderOf z = 2) {K : Subgroup G}
    (hKz : K ≤ centralizer ({z} : Set G))
    (hKp : IsPComponent 2 (K.subgroupOf (centralizer ({z} : Set G))))
    (htype : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
        Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 2 p f) ∨
      IsL34Type (K ⧸ Open.fusionZStar K)) :
    gsFixedLayer L z ≤ K ∧ gsFixedLayer L z ⊔ oddIn K = K ∧
      (∀ g ∈ centralizer ({z} : Set G), conjugate K g = K) ∧
      K = (⨆ (g : G) (_ : g ∈ centralizer ({z} : Set G)), conjugate (gsFixedLayer L z) g) ∧
      IsL34Type (K ⧸ Open.fusionZStar K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset' := hset
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  obtain ⟨hbase, hfam, -, -, -, -, -⟩ := hset
  obtain ⟨hsimple, hnonab, hK, -, -, -, -, -⟩ := hbase
  obtain ⟨⟨-, -, -, -, -, hto, -, -⟩, htypeL, -, -, -⟩ := hfam
  have : IsSimpleGroup G := hsimple
  obtain ⟨hzS, hzK⟩ := mem_inf.mp hzQ
  have htz : t * z = z * t := (hZS z hzS).symm
  have hz1 : z ≠ 1 := by rintro rfl; simp at hz
  have hzZ : z ∉ center G := not_mem_center_of_ne_one hnonab hz1
  obtain ⟨hTtz, hTpc, hTE, hTset, -, ⟨φ⟩⟩ := gsFixedLayer_facts hS hK hto hz htz hzZ hLt hLpt hzK
  set T₀ := gsFixedLayer L z with hT₀
  obtain ⟨eT⟩ := nonempty_fusionZStar_equiv_of_quotient_equiv φ
  have htypeT : IsL34Type (T₀ ⧸ Open.fusionZStar T₀) :=
    LieType.CurtisTits.lieModel_of_mulEquiv eT.symm htypeL
  obtain ⟨M, hMz, hMp, hTMM, hTMpc⟩ :=
    UGSChain.exists_orbit_component_of_le_pLayer hto htz hTtz hTpc hTE
  have hTK : T₀ ≤ (M ⊔ conjugate M t) ⊓ centralizer ({t} : Set G) :=
    le_inf hTMM (hTtz.trans inf_le_left)
  have hMt : conjugate M t = M :=
    conjugate_eq_of_fixedLayer hS hU hheld hSol hGW hMax hset' hz htz hzK hMz hMp hTK hTMpc
  have hTM : T₀ ≤ M := by
    rw [hMt, sup_idem] at hTMM
    exact hTMM
  have hKM : K = M := by
    by_contra hne
    exact false_of_ne_of_setting hS hU hheld hSol hGW hMax hL34 hset' hzQ hz hMz hMp hTM hKz hKp
      htype hne hMt
  have hTK' : T₀ ≤ K := hKM ▸ hTM
  have hKt : conjugate K t = K := hKM ▸ hMt
  have htypeK : IsL34Type (K ⧸ Open.fusionZStar K) := by
    rcases htype with ⟨p, f, hp, hp2, hf, hL⟩ | hL
    · exfalso
      obtain ⟨-, hrank⟩ := l2_type_facts hKz hKp hp hp2 hf hL
      have h3 := three_le_pRank_of_l34 htypeT
      have h4 := pRank_le_of_le hTK'
      omega
    · exact hL
  have hTKK : T₀ ≤ (K ⊔ conjugate K t) ⊓ centralizer ({t} : Set G) := by
    rw [hKt, sup_idem]
    exact le_inf hTK' (hTtz.trans inf_le_left)
  have hTKpc : IsPComponent 2 (T₀.subgroupOf ((K ⊔ conjugate K t) ⊓
      centralizer ({t} : Set G))) := hKM ▸ hTMpc
  obtain ⟨hidxle, -, heqc⟩ := UGSChain.orbit_fixed_component_comparison hto htz hKz hKp hTKK hTKpc
  have hTO : T₀ ⊔ oddIn K = K := by
    by_cases hidx : (pPrimeCore 2 T₀).index = (pPrimeCore 2 K).index
    · exact (heqc hidx).2 hKt.symm
    · exfalso
      have hTK2 : T₀ ≤ K ⊓ centralizer ({t} : Set G) := le_inf hTK' (hTtz.trans inf_le_left)
      have hTpc2 : IsPComponent 2 (T₀.subgroupOf (K ⊓ centralizer ({t} : Set G))) := by
        rw [hKt, sup_idem] at hTKpc
        exact hTKpc
      have c2 := GSThmB.card_of_lieModel_L34 htypeT
      rcases l34FixedInput G t z K T₀ hto hz htz hKz hKp hKt hTK2 hTpc2
          (lt_of_le_of_ne hidxle hidx) htypeK with h5 | h7
      · have c1 := GSThmB.card_of_lieModel_psl_two (by norm_num) h5
        have : Open.ordA 1 (5 ^ 1) = 60 := by decide
        omega
      · have c1 := GSThmB.card_of_lieModel_psl_two (by norm_num) h7
        have : Open.ordA 1 (7 ^ 1) = 168 := by decide
        omega
  have hKnorm : ∀ g ∈ centralizer ({z} : Set G), conjugate K g = K := by
    intro g hg
    by_contra hne
    obtain ⟨hKgz, hKgp⟩ := GSThmB.isPComponent_conjugate_centralizer_singleton hKz hKp hg
    have e : K ≃* conjugate K g := K.equivMapOfInjective _ (MulAut.conj g⁻¹).injective
    obtain ⟨e'⟩ := nonempty_fusionZStar_equiv_of_mulEquiv' e
    have htypeKg : IsL34Type (conjugate K g ⧸ Open.fusionZStar (conjugate K g)) :=
      LieType.CurtisTits.lieModel_of_mulEquiv e' htypeK
    exact false_of_ne_of_setting hS hU hheld hSol hGW hMax hL34 hset' hzQ hz hKz hKp hTK' hKgz
      hKgp (Or.inr htypeKg) hne hKt
  set N₀ := ⨆ (g : G) (_ : g ∈ centralizer ({z} : Set G)), conjugate T₀ g with hN₀
  have hN₀K : N₀ ≤ K := iSup_le fun g => iSup_le fun hg =>
    (map_mono hTK').trans (le_of_eq (hKnorm g hg))
  have hTN₀ : T₀ ≤ N₀ := le_iSup_of_le 1 (le_iSup_of_le (one_mem _) (by
    intro x hx
    exact ⟨x, hx, by simp⟩))
  have hCN₀ : ∀ c ∈ centralizer ({z} : Set G), conjugate N₀ c ≤ N₀ := by
    intro c hc
    rw [hN₀, conjugate, Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hg => le_iSup_of_le (g * c) (le_iSup_of_le (mul_mem hg hc) ?_)
    show conjugate (conjugate T₀ g) c ≤ conjugate T₀ (g * c)
    rw [conjugate_conjugate'']
  have hN₀N : ∀ c ∈ centralizer ({z} : Set G), c ∈ normalizer (N₀ : Set G) := by
    intro c hc
    apply mem_normalizer_of_conjugate_eq
    refine le_antisymm (hCN₀ c hc) ?_
    calc N₀ = conjugate (conjugate N₀ c⁻¹) c := by
          rw [conjugate_conjugate'', inv_mul_cancel]
          ext y
          simp [conjugate]
      _ ≤ conjugate N₀ c := map_mono (hCN₀ c⁻¹ (inv_mem hc))
  have hperfK : Group.IsPerfect K := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hKp
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKz).toMonoidHom)
      (subgroupOfEquivOfLe hKz).surjective
  have hoddK : Odd (Nat.card (oddIn K)) := by
    rw [oddIn, card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hKN₀ : K ≤ N₀ := by
    refine le_of_le_sup_of_odd hperfK hoddK (fun x hx => hN₀N x (hKz (map_subtype_le _ hx)))
      (fun x hx => hN₀N x (hKz hx)) ?_
    calc K = T₀ ⊔ oddIn K := hTO.symm
      _ ≤ oddIn K ⊔ N₀ := sup_le (hTN₀.trans le_sup_right) le_sup_left
  exact ⟨hTK', hTO, hKnorm, le_antisymm hKN₀ hN₀K, htypeK⟩

end CFSG.ComponentClassification.GrSLit.GrS5

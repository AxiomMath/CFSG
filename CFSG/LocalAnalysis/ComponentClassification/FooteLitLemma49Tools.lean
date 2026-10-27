module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitElemAb

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup
open scoped commutatorElement

section Generic

variable {B : Type*} [Group B]

theorem exists_pow_mul_eq {Y : Subgroup B} {o : B} (ho : o ∈ normalizer (Y : Set B)) {y : B}
    (hy : y ∈ Y) (n : ℕ) : ∃ y' ∈ Y, (o * y) ^ n = y' * o ^ n := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨y', hy', he⟩ := ih
    refine ⟨y' * (o ^ (n + 1) * y * (o ^ (n + 1))⁻¹), mul_mem hy' ?_, ?_⟩
    · exact (mem_normalizer_iff.mp (pow_mem ho (n + 1)) y).mp hy
    · rw [pow_succ, he]
      group

theorem isQuasisimple_of_isSimpleGroup' [hs : IsSimpleGroup B] (hna : ∃ a b : B, a * b ≠ b * a) :
    CFSG.IsQuasisimple B := by
  obtain ⟨a, b, hab⟩ := hna
  have hcen : center B = ⊥ := by
    rcases (center B).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      apply hab
      have hb : b ∈ center B := h ▸ mem_top b
      exact mem_center_iff.mp hb a
  have hperf : commutator B = ⊤ := by
    rcases (commutator_normal (⊤ : Subgroup B) ⊤).eq_bot_or_eq_top with h | h
    · exfalso
      apply hab
      have h1 : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup B), ⊤⁆ :=
        commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    · rw [commutator_def]
      exact h
  have e : B ⧸ center B ≃* B := (QuotientGroup.quotientMulEquivOfEq hcen).trans
    QuotientGroup.quotientBot
  refine ⟨⟨hperf⟩, e.isSimpleGroup_congr.mpr hs, ⟨e.symm a, e.symm b, fun h => hab ?_⟩⟩
  apply e.symm.injective
  rw [map_mul, map_mul, h]

variable [Finite B]

omit [Finite B] in
theorem mem_of_mem_sup_of_le_normalizer {Y O : Subgroup B} (hYO : O ≤ normalizer (Y : Set B))
    (hO : Odd (Nat.card O)) {x : B} (hx : x ∈ Y ⊔ O) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x ∈ Y := by
  have hx' : x ∈ ((O ⊔ Y : Subgroup B) : Set B) := by
    rw [sup_comm]
    exact hx
  rw [coe_mul_of_left_le_normalizer_right O Y hYO] at hx'
  obtain ⟨o, ho, y, hy, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨y', hy', he⟩ := exists_pow_mul_eq (hYO ho) hy (2 ^ k)
  rw [hk] at he
  have hoY : o ^ 2 ^ k ∈ Y := by
    rw [eq_inv_of_mul_eq_one_right he.symm]
    exact inv_mem hy'
  have hodd : Odd (orderOf o) := Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard O ho)
  have hcop : Nat.Coprime (2 ^ k) (orderOf o) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  have hoY' : o ∈ Y := by
    rw [← hj]
    exact pow_mem hoY j
  exact mul_mem hoY' hy

theorem eq_of_commute_of_pRank_eq_one {C : Subgroup B} (hC : CFSG.pRank 2 ↥C = 1) {t u : B}
    (htC : t ∈ C) (huC : u ∈ C) (ht : orderOf t = 2) (hu : orderOf u = 2)
    (htu : t * u = u * t) : u = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hu2 : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; omega
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu; omega
  have hV := isKleinFour_sup_zpowers ht2 hu2 ht1 hu1 hne htu
  set V := zpowers t ⊔ zpowers u with hVdef
  have hVC : V ≤ C := sup_le (zpowers_le.mpr htC) (zpowers_le.mpr huC)
  have hel : Open.IsElemAbelian 2 (V.subgroupOf C) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext ?_⟩
    · exact commute_of_sq_eq_one (fun x hx => sq_eq_one_of_isKleinFour hV hx) a.2 b.2
    · rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact sq_eq_one_of_isKleinFour hV ha
  have hcard : Nat.card (V.subgroupOf C) = 2 ^ 2 := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hVC).symm.toEquiv, hV.card_four]
    norm_num
  have h2 := SectionRank.le_pRank one_lt_two (le_top : V.subgroupOf C ≤ ⊤) hel hcard
  rw [← SectionRank.pRank_eq_open_pRank_top] at h2
  omega

theorem eq_of_isComponent_le {K L : Subgroup B} (hK : CFSG.IsComponent K)
    (hL : CFSG.IsQuasisimple ↥L) (hKL : K ≤ L) : K = L := by
  have hLc : CFSG.IsComponent (⊤ : Subgroup ↥L) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.topEquiv (G := ↥L)).symm hL,
      Subgroup.IsSubnormal.top⟩
  have hU : (K.subgroupOf L).IsSubnormal := hK.2.comap L.subtype
  rcases CFSG.LocalCores.component_subnormal_subgroup hLc hU with h | h
  · refine le_antisymm hKL fun x hx => ?_
    have : (⟨x, hx⟩ : ↥L) ∈ K.subgroupOf L := h (mem_top _)
    exact this
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hK.1
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hc : (⟨a, hKL a.2⟩ : ↥L) * ⟨b, hKL b.2⟩ = ⟨b, hKL b.2⟩ * ⟨a, hKL a.2⟩ := by
      have h1 : ⁅(⟨a, hKL a.2⟩ : ↥L), (⟨b, hKL b.2⟩ : ↥L)⁆ ∈ ⁅(⊤ : Subgroup ↥L), K.subgroupOf L⁆ :=
        commutator_mem_commutator (mem_top _) (show (⟨b, hKL b.2⟩ : ↥L) ∈ K.subgroupOf L from b.2)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hab' : a * b = b * a := by
      apply Subtype.ext
      have := congrArg Subtype.val hc
      simpa using this
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hab']

end Generic

section Components

variable {B : Type*} [Group B] [Finite B]

theorem nonempty_quotientEquivMap {K : Subgroup B} (hK : IsPComponent 2 K) :
    Nonempty (K ⧸ pPrimeCore 2 K ≃* K.map (QuotientGroup.mk' (pPrimeCore 2 B))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hsub, -, -⟩ := hK
  set φ : K →* B ⧸ pPrimeCore 2 B := (QuotientGroup.mk' (pPrimeCore 2 B)).comp K.subtype with hφ
  have hrange : φ.range = K.map (QuotientGroup.mk' (pPrimeCore 2 B)) := by
    rw [hφ, MonoidHom.range_comp, range_subtype]
  have hker : pPrimeCore 2 K = φ.ker := by
    have h1 := UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hsub
    ext x
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      have : (x : B) ∈ (pPrimeCore 2 K).map K.subtype := ⟨x, hx, rfl⟩
      rw [h1] at this
      exact this.2
    · intro hx
      have : (x : B) ∈ K ⊓ pPrimeCore 2 B := ⟨x.2, hx⟩
      rw [← h1] at this
      obtain ⟨y, hy, hyx⟩ := this
      rw [← Subtype.ext hyx]
      exact hy
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))⟩

theorem odd_card_pPrimeCore_two (B : Type*) [Group B] [Finite B] :
    Odd (Nat.card (pPrimeCore 2 B)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := B))

theorem mem_of_mk_mem_map {Y : Subgroup B} (hY : pPrimeCore 2 B ≤ normalizer (Y : Set B))
    {x : B} {k : ℕ} (hk : x ^ 2 ^ k = 1)
    (hx : QuotientGroup.mk' (pPrimeCore 2 B) x ∈ Y.map (QuotientGroup.mk' (pPrimeCore 2 B))) :
    x ∈ Y := by
  obtain ⟨y, hy, hyx⟩ := mem_map.mp hx
  have ho : y⁻¹ * x ∈ pPrimeCore 2 B := by
    rw [← QuotientGroup.eq]
    exact hyx
  refine mem_of_mem_sup_of_le_normalizer hY (odd_card_pPrimeCore_two B) ?_ hk
  rw [show x = y * (y⁻¹ * x) by group]
  exact mul_mem (mem_sup_left hy) (mem_sup_right ho)

theorem pPrimeCore_le_normalizer_sup {K : Subgroup B} (hK : IsPComponent 2 K) {t : B}
    (htZ : t ∈ center B) :
    pPrimeCore 2 B ≤ normalizer ((K ⊔ zpowers t : Subgroup B) : Set B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (zpowers t).Normal := normal_of_le_center (zpowers_le.mpr htZ)
  refine le_trans (le_inf (UnbalancedLayer.pPrimeCore_le_normalizer hK) ?_)
    (inf_normalizer_le_normalizer_sup K (zpowers t))
  rw [normalizer_eq_top]
  exact le_top

end Components

end CFSG.ComponentClassification.FooteLit

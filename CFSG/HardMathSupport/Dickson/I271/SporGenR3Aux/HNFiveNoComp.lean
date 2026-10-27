module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNFiveSolv
import CFSG.RankThree.PartOne.S11c.HNCoverAbstract
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open

section Dichotomy

variable {M : Type} [Group M] [Finite M]

theorem hnComp_le_or_commute {B H K : Subgroup M} (hB : CFSG.Assembly.IsComponentOf B H)
    (hKH : K ≤ H) (hK : H ≤ Subgroup.normalizer (K : Set M)) : B ≤ K ∨ ⁅B, K⁆ = ⊥ := by
  have hBH := hB.1
  have hc := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hBH).1 hB
  have hKn : (K.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hK
  rcases CFSG.LocalCores.component_normal_subgroup hc hKn with h | h
  · left
    intro x hx
    have hx' : (⟨x, hBH hx⟩ : H) ∈ B.subgroupOf H := Subgroup.mem_subgroupOf.2 hx
    exact Subgroup.mem_subgroupOf.1 (h hx')
  · right
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    have hx' : (⟨x, hBH hx⟩ : H) ∈ B.subgroupOf H := Subgroup.mem_subgroupOf.2 hx
    have h1 := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h) hx'
    rw [Subgroup.mem_centralizer_iff] at h1
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (⟨y, hKH hy⟩ : H) ∈ K.subgroupOf H := Subgroup.mem_subgroupOf.2 hy
    exact congrArg Subtype.val (h1 ⟨y, hKH hy⟩ hy')

end Dichotomy

section NoComp

variable {G : Type} [Group G] [Finite G]

theorem hnNoComp_of_normal_solvable {C Q : Subgroup G} (hQC : Q ≤ C)
    (hQn : (Q.subgroupOf C).Normal) (hQs : Group.IsSolvable ↥Q) (hO : GLAPPrimeCoreOf 5 C = ⊥)
    {a b : ℕ}
    (hcard : Nat.card ↥C ∣ 2 ^ a * 3 * 5 ^ b)
    (hmov : ∀ s ∈ C, orderOf s = 3 → ∃ q ∈ Q, s * q ≠ q * s) (J : Subgroup G) :
    ¬ GLAPComponent 5 C J := by
  intro hJ
  have hJC : J ≤ C := hJ.1
  have hJq : CFSG.Open.IsQuasisimple ↥J :=
    CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_of_glaPComponent_of_comm
      Nat.prime_five hJ
      (fun g _ o ho => by
        rw [hO, Subgroup.mem_bot] at ho
        rw [ho, one_mul, mul_one])
  have hcomp : CFSG.Assembly.IsComponentOf J C :=
    CFSG.Assembly.isComponentOf_iff_open.2 ⟨hJC, hJ.2.1, hJq⟩
  haveI : Group.IsPerfect ↥J := ⟨hJq.1⟩
  haveI : Nontrivial ↥J := CFSG.ComponentClassification.Quasisimple.nontrivial hJq
  have hNQ : C ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQC).1 hQn
  rcases hnComp_le_or_commute hcomp hQC hNQ with h | h
  ·
    haveI := hQs
    haveI : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h)
    exact Group.IsPerfect.not_isSolvable (↥J) inferInstance
  ·
    have hJcard : Nat.card ↥J ∣ 2 ^ a * 3 * 5 ^ b :=
      (Subgroup.card_dvd_of_le hJC).trans hcard
    have h3 : 3 ∣ Nat.card ↥J := by
      by_contra h3
      have hcop : Nat.Coprime (Nat.card ↥J) 3 :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3 |>.symm
      have e : 2 ^ a * 3 * 5 ^ b = 3 * (2 ^ a * 5 ^ b) := by ring
      rw [e] at hJcard
      have hd : Nat.card ↥J ∣ 2 ^ a * 5 ^ b := hcop.dvd_of_dvd_mul_left hJcard
      exact Group.IsPerfect.not_isSolvable (↥J) (isSolvable_of_card_dvd_two_five hd)
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 3 h3
    have hso : orderOf (s : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hs
    obtain ⟨q, hq, hne⟩ := hmov (s : G) (hJC s.2) hso
    have hcen := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h) s.2
    exact hne ((Subgroup.mem_centralizer_iff.1 hcen q hq).symm)

theorem hnMoved_of_sylow {C Q : Subgroup G} (hQC : Q ≤ C) (hQn : (Q.subgroupOf C).Normal)
    (h9 : ¬ 3 ^ 2 ∣ Nat.card ↥C) {s₀ : G} (hs₀C : s₀ ∈ C) (hs₀ : orderOf s₀ = 3)
    (hmov : ∃ q ∈ Q, s₀ * q ≠ q * s₀) :
    ∀ s ∈ C, orderOf s = 3 → ∃ q ∈ Q, s * q ≠ q * s := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro s hsC hso
  by_contra hcon
  push Not at hcon
  have hs'o : orderOf (⟨s, hsC⟩ : ↥C) = 3 := by rw [Subgroup.orderOf_mk]; exact hso
  have hs₀'o : orderOf (⟨s₀, hs₀C⟩ : ↥C) = 3 := by rw [Subgroup.orderOf_mk]; exact hs₀
  obtain ⟨c, k, hc⟩ := CFSG.RankThree.PartOne.HNRed.exists_conj_pow_of_orderOf_prime (p := 3)
    (G := ↥C) h9 hs₀'o hs'o
  have hck : (c : G) * s * (c : G)⁻¹ = s₀ ^ k := by
    have := congrArg Subtype.val hc
    simpa using this
  have hcenk : ∀ q ∈ Q, s₀ ^ k * q = q * s₀ ^ k := by
    intro q hq
    have hqC : q ∈ C := hQC hq
    have hq' : (⟨q, hqC⟩ : ↥C) ∈ Q.subgroupOf C := Subgroup.mem_subgroupOf.2 hq
    have hconj := hQn.conj_mem _ hq' c⁻¹
    have hqm : (c : G)⁻¹ * q * (c : G) ∈ Q := by
      have := Subgroup.mem_subgroupOf.1 hconj
      simpa using this
    have hcomm := hcon _ hqm
    rw [← hck]
    calc (c : G) * s * (c : G)⁻¹ * q = (c : G) * (s * ((c : G)⁻¹ * q * (c : G))) * (c : G)⁻¹ := by
          group
      _ = (c : G) * (((c : G)⁻¹ * q * (c : G)) * s) * (c : G)⁻¹ := by rw [hcomm]
      _ = q * ((c : G) * s * (c : G)⁻¹) := by group
  have hs₀3 : s₀ ^ 3 = 1 := hs₀ ▸ pow_orderOf_eq_one s₀
  have hk3 : k % 3 ≠ 0 := by
    intro h0
    have h1 : s₀ ^ k = 1 := by
      rw [pow_eq_pow_mod k hs₀3, h0, pow_zero]
    rw [← hck] at h1
    have h2 : s = 1 := by
      calc s = (c : G)⁻¹ * ((c : G) * s * (c : G)⁻¹) * (c : G) := by group
        _ = 1 := by rw [h1]; group
    rw [h2, orderOf_one] at hso
    omega
  obtain ⟨q, hq, hne⟩ := hmov
  apply hne
  have hr : k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with hr | hr
  · have := hcenk q hq
    rw [pow_eq_pow_mod k hs₀3, hr, pow_one] at this
    exact this
  · have := hcenk q hq
    rw [pow_eq_pow_mod k hs₀3, hr] at this
    have hinv : s₀ ^ 2 = s₀⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ]
      exact hs₀3
    rw [hinv] at this
    calc s₀ * q = s₀ * (q * s₀⁻¹ * s₀) := by group
      _ = s₀ * (s₀⁻¹ * q * s₀) := by rw [show q * s₀⁻¹ = s₀⁻¹ * q from this.symm]
      _ = q * s₀ := by group

end NoComp

end CFSG.HardMathSupport.Dickson.I271

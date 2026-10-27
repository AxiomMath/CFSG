module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma23Proof
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Case1
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface2

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_eq_bot_of_isMaxBInvariantTwo (hC : IsCharTwoType G) {B T : Subgroup G}
    (hB3 : IsElemAbelian 3 B) (hT : IsMaxBInvariantTwo B T) (hT1 : T ≠ ⊥) :
    B ⊓ Subgroup.centralizer (T : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := Subgroup.normalizer (T : Set G) with hH
  have hloc : IsTwoLocal H := ⟨T, hT1, hT.1, rfl⟩
  have hP := hC H hloc
  have hTP : T ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hT.1
  have hBH : B ≤ H := hT.2.1
  have hPT : pCoreOf 2 H = T :=
    hT.2.2 _ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
      (hBH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)) hTP
  rw [eq_bot_iff]
  intro b hb
  rw [Subgroup.mem_inf] at hb
  have hbc : b ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := by rw [hPT]; exact hb.2
  have hbT : b ∈ T := by
    have := hP (Subgroup.mem_inf.2 ⟨hBH hb.1, hbc⟩)
    rwa [hPT] at this
  have hb3 : b ^ 3 = 1 := hB3.2 b hb.1
  obtain ⟨k, hk⟩ := hT.1 ⟨b, hbT⟩
  have hk' : b ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdiv : orderOf b ∣ 3 := orderOf_dvd_of_pow_eq_one hb3
  have hdiv2 : orderOf b ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have : orderOf b ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd hdiv hdiv2
  have hcop : Nat.gcd 3 (2 ^ k) = 1 :=
    Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
  rw [hcop] at this
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 this))

theorem le_normalizer_component_of_input11_6 (i : Input11_6) (hS : GLStanding G 4 3)
    {B : Subgroup G} (hB : IsBOneMax 3 B) {N : Subgroup G} (hN : N ≠ ⊤) (hBN : B ≤ N)
    {Y : Subgroup G} (hYN : Y ≤ N) (hBY : B ≤ Subgroup.normalizer (Y : Set G))
    (hY3 : ¬ 3 ∣ Nat.card Y) {L : Subgroup G} (hL : GLAPComponent 3 N L) :
    Y ≤ Subgroup.normalizer (L : Set G) := by
  have hK : CFSG.Open.IsKGroup ↥N := isKGroup_of_isKProper hS.kProper hN
  have hSC : IsSCp 3 ⊤ (B.subgroupOf N) :=
    isSCp_subgroupOf (lemma23_proved G 4 3 hS B hB) hBN
  have hcardB : Nat.card (B.subgroupOf N) = 3 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv, card_eq_81 hS hB]
    norm_num
  have hrank : GLATwoLocalRank 3 ↥N ≤ CFSG.Open.pRank 3 (B.subgroupOf N) := by
    have h1 := glaTwoLocalRank_subgroup_le (by norm_num : 1 < 3) N
    rw [hS.rank_eq] at h1
    exact h1.trans (CFSG.SectionRank.le_pRank (by norm_num) le_rfl
      (isElemAbelian_subgroupOf (hB.1.1) N) hcardB)
  have hYcard : Nat.Coprime 3 (Nat.card (Y.subgroupOf N)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYN).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hY3
  have hnorm : B.subgroupOf N ≤ Subgroup.normalizer ((Y.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
    rw [normalizer_subgroupOf_eq hYN]
    intro x hx
    exact hBY hx
  have key := i ↥N hK 3 Nat.prime_three (by norm_num) _ hSC hrank _ hYcard hnorm _
    (glaPComponent_top hL)
  intro y hy
  have hy' : (⟨y, hYN hy⟩ : ↥N) ∈ Y.subgroupOf N := hy
  have := key hy'
  rw [normalizer_subgroupOf_eq (hL.1)] at this
  exact this

omit [Finite G] in
private theorem mem_barX_iff {p : ℕ} {X K : Subgroup G} {z : ↥X ⧸ GLAPPrimeCore p ↥X} :
    z ∈ barX p X K ↔ ∃ x : ↥X, (x : G) ∈ K ∧ (x : ↥X ⧸ GLAPPrimeCore p ↥X) = z := by
  simp [barX, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem le_normalizer_of_barX_eq {B N I K : Subgroup G} (hBN : B ≤ N) (hKN : K ≤ N)
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hI : GLAPComponent 3 N I)
    (hbar : barX 3 N I = barX 3 N K) : B ≤ Subgroup.normalizer (I : Set G) := by
  have _ := hKN
  intro b hb
  have hbN : b ∈ N := hBN hb
  set u : ↥N := ⟨b, hbN⟩ with hu
  have hū : (u : ↥N ⧸ GLAPPrimeCore 3 ↥N) ∈
      Subgroup.normalizer (barX 3 N I : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) := by
    rw [hbar]
    exact barX_le_normalizer hBK (mem_barX_iff.2 ⟨u, hb, rfl⟩)
  have hū' := Subgroup.mem_normalizer_iff.1 hū
  have hEq : barX 3 N (GLBConj b I) = barX 3 N I := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := mem_barX_iff.1 hz
      rw [mem_gLBConj] at hx
      refine (hū' _).2 (mem_barX_iff.2 ⟨⟨b * x * b⁻¹, ?_⟩, hx, ?_⟩)
      · exact N.mul_mem (N.mul_mem hbN x.2) (N.inv_mem hbN)
      · rfl
    · intro hz
      obtain ⟨x'', hx'', hxx⟩ := mem_barX_iff.1 ((hū' _).1 hz)
      refine mem_barX_iff.2 ⟨u⁻¹ * x'' * u, ?_, ?_⟩
      · rw [Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv, mem_gLBConj]
        simpa [hu, mul_assoc] using hx''
      · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hxx]
        group
  have hc := glaPComponent_gLBConj hI b
  rw [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hbN)] at hc
  exact mem_normalizer_iff_gLBConj_eq.2 (glaPComponent_unique hc hI hEq)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal

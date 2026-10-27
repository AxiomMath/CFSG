module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser.MainCase
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser

@[expose] def QStmt (k : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsPGroup 3 G → ∀ M : Subgroup G, M.Normal →
    (∃ E : Subgroup G, E ≤ M ∧ IsEA3 E ∧ Nat.card E = 3 ^ k) →
    ∃ N : Subgroup G, N ≤ M ∧ N.Normal ∧ IsEA3 N ∧ Nat.card N = 3 ^ k

theorem qstmt_one : QStmt 1 := by
  intro G _ _ hG M hM ⟨E, hEM, hE, hEc⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbot : (⊥ : Subgroup G) < M := by
    refine bot_lt_iff_ne_bot.mpr (fun h => ?_)
    have := Subgroup.card_le_of_le (h ▸ hEM : E ≤ ⊥)
    rw [Subgroup.card_bot, hEc] at this
    norm_num at this
  obtain ⟨x, hxM, hx1, hxc⟩ := exists_mem_central_mod hG hbot
  have hx1' : x ≠ 1 := fun h => hx1 (h ▸ Subgroup.one_mem _)
  have hxcomm : ∀ g : G, g * x * g⁻¹ = x := fun g => by
    have := hxc g
    rw [Subgroup.mem_bot] at this
    calc g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
      _ = x := by rw [this]; simp
  obtain ⟨t, ht⟩ := (IsPGroup.iff_orderOf.mp hG) x
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hx1' (orderOf_eq_one_iff.mp (by simpa using ht))
  have h3dvd : 3 ∣ orderOf x := by
    rw [ht]; exact dvd_pow_self 3 ht0
  have hordpos : orderOf x ≠ 0 := by rw [ht]; positivity
  set y := x ^ (orderOf x / 3) with hy
  have hyord : orderOf y = 3 := orderOf_pow_orderOf_div hordpos h3dvd
  have hyM : y ∈ M := M.pow_mem hxM _
  have hyc : ∀ g : G, g * y * g⁻¹ = y := fun g => by
    rw [hy, ← conj_pow, hxcomm]
  refine ⟨Subgroup.zpowers y, Subgroup.zpowers_le.mpr hyM, ?_, ?_, ?_⟩
  · refine ⟨fun n hn g => ?_⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← conj_zpow, hyc]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) i
  · refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow_self y i k).eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hyord,
        pow_orderOf_eq_one, one_zpow]
  · rw [Nat.card_zpowers, hyord]; norm_num


theorem exists_sub_ea {G : Type} [Group G] [Finite G] {E : Subgroup G} (hE : IsEA3 E) {j : ℕ}
    (hc : Nat.card E = 3 ^ (j + 1)) :
    ∃ K : Subgroup G, K ≤ E ∧ IsEA3 K ∧ Nat.card K = 3 ^ j := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 3
    (n := j) (by rw [hc]; exact pow_dvd_pow 3 (Nat.le_succ j))
  refine ⟨K'.map E.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
      exact hE.1 _ x.2 _ y.2
    · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      exact hE.2 _ x.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hK']

theorem qstmt_succ (j : ℕ) (hj1 : 1 ≤ j) (hj3 : j ≤ 3) (hprev : QStmt j) : QStmt (j + 1) := by
  have key : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → IsPGroup 3 G →
      ∀ (m : ℕ) (M : Subgroup G), Nat.card M = m → M.Normal →
      (∃ E : Subgroup G, E ≤ M ∧ IsEA3 E ∧ Nat.card E = 3 ^ (j + 1)) →
      ∃ N : Subgroup G, N ≤ M ∧ N.Normal ∧ IsEA3 N ∧ Nat.card N = 3 ^ (j + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihG =>
    intro G _ _ hn hG m
    induction m using Nat.strong_induction_on with
    | _ m ihM =>
    intro M hm hMn ⟨E, hEM, hE, hEc⟩
    by_contra hcon
    have hno : ∀ Y : Subgroup G, Y ≤ M → Y.Normal → IsEA3 Y → Nat.card Y ≠ 3 ^ (j + 1) :=
      fun Y hY hYn hYe hYc => hcon ⟨Y, hY, hYn, hYe, hYc⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hnil : Group.IsNilpotent G := hG.isNilpotent
    by_cases hMtop : M = ⊤
    ·
      rcases IsCoatomic.eq_top_or_exists_le_coatom E with hEtop | ⟨M', hco, hEM'⟩
      · exact hno E (by rw [hMtop]; exact le_top) (by subst hEtop; infer_instance) hE hEc
      · have hM'n : M'.Normal := Subgroup.NormalizerCondition.normal_of_coatom M'
          (Group.normalizerCondition_of_isNilpotent (G := G)) hco
        have hlt : Nat.card M' < m := by
          rw [← hm, hMtop, Subgroup.card_top]
          refine lt_of_le_of_ne (Subgroup.card_le_card_group M') (fun h => hco.1 ?_)
          exact (Subgroup.card_eq_iff_eq_top M').mp h
        obtain ⟨N, hNM', hNn, hNe, hNc⟩ := ihM _ hlt M' rfl hM'n ⟨E, hEM', hE, hEc⟩
        exact hno N (hNM'.trans (hMtop ▸ le_top)) hNn hNe hNc
    ·
      have hMlt : Nat.card M < n := by
        rw [← hn]
        refine lt_of_le_of_ne (Subgroup.card_le_card_group M) (fun h => hMtop ?_)
        exact (Subgroup.card_eq_iff_eq_top M).mp h
      have hGM : IsPGroup 3 M := hG.to_subgroup M
      have hE' : ∃ E' : Subgroup M, E' ≤ ⊤ ∧ IsEA3 E' ∧ Nat.card E' = 3 ^ (j + 1) := by
        refine ⟨E.subgroupOf M, le_top, ⟨fun a ha b hb => ?_, fun a ha => ?_⟩, ?_⟩
        · exact Subtype.ext (hE.1 _ ha _ hb)
        · exact Subtype.ext (hE.2 _ ha)
        · rw [← hEc]
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv
      obtain ⟨S', -, hS'n, hS'e, hS'c⟩ := ihG (Nat.card M) hMlt M rfl hGM (Nat.card (⊤ : Subgroup M))
        ⊤ rfl inferInstance hE'
      set S : Subgroup G := S'.map M.subtype with hS
      have hSM : S ≤ M := Subgroup.map_subtype_le _
      have hSe : IsEA3 S := by
        refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
        · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
          obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
          exact congrArg Subtype.val (hS'e.1 x hx y hy)
        · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
          exact congrArg Subtype.val (hS'e.2 x hx)
      have hSc : Nat.card S = 3 ^ (j + 1) := by
        rw [hS, Subgroup.card_map_of_injective M.subtype_injective, hS'c]
      have hSn : ∀ m ∈ M, ∀ s ∈ S, m * s * m⁻¹ ∈ S := by
        intro m hm s hs
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hs
        exact ⟨⟨m, hm⟩ * x * ⟨m, hm⟩⁻¹, hS'n.conj_mem x hx ⟨m, hm⟩, rfl⟩
      obtain ⟨K, hKS, hKe, hKc⟩ := exists_sub_ea hSe hSc
      obtain ⟨N, hNM, hNn, hNe, hNc⟩ := hprev G hG M hMn ⟨K, hKS.trans hSM, hKe, hKc⟩
      have hmin : ∀ T : Subgroup G, T ≤ M → T.Normal → S ≤ T → T = M := by
        intro T hTM hTn hST
        by_contra hTne
        have hlt : Nat.card T < m := by
          rw [← hm]
          refine lt_of_le_of_ne (Subgroup.card_le_of_le hTM) (fun h => hTne ?_)
          exact Subgroup.eq_of_le_of_card_ge hTM h.ge
        obtain ⟨N', hN'T, hN'n, hN'e, hN'c⟩ := ihM _ hlt T rfl hTn ⟨S, hST, hSe, hSc⟩
        exact hno N' (hN'T.trans hTM) hN'n hN'e hN'c
      let c : Cfg G j :=
        { hG := hG, M := M, N := N, S := S, hMn := hMn, hNn := hNn, hNM := hNM, hSM := hSM,
          hN := hNe, hS := hSe, hSn := hSn, hNc := hNc, hSc := hSc, hno := hno, hmin := hmin }
      obtain ⟨hj, hJ9, n₀, hn₀N, hn₀J, hgen, hsurj, hcs⟩ := c.main_case hj1 hj3
      exact MainData.false_main (c := c)
        ⟨hj, hJ9, n₀, hn₀N, hn₀J, hgen, hsurj, hcs⟩
  intro G _ _ hG M hM hE
  exact key _ G rfl hG _ M rfl hM hE

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser

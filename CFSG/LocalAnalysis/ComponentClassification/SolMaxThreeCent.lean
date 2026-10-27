module

public import Certificates.Certificate22259
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixGenBase
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

namespace ThreeCent

open SixGen

theorem threeCentSupp_eq {t : Tab} {g : Perm (Fin 9)} (ht : TabRep t g) :
    threeCentSupp t = g.support.card := by
  classical
  rw [threeCentSupp, countBelow_eq]
  have h1 : (Finset.range 9).filter (fun k => (t[k]! != k) = true) =
      g.support.map Fin.valEmbedding := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Perm.mem_support,
      Fin.valEmbedding_apply, bne_iff_ne, ne_eq]
    constructor
    · rintro ⟨hk, hne⟩
      refine ⟨⟨k, hk⟩, fun h => hne ?_, rfl⟩
      rw [ht.apply ⟨k, hk⟩, h]
    · rintro ⟨i, hi, rfl⟩
      refine ⟨i.2, fun h => hi (Fin.ext ?_)⟩
      rw [← ht.apply i, h]
  rw [h1, Finset.card_map]

theorem threeCentCaseOK_spec {c : Swaps × List Swaps × Nat}
    (hcard : Nat.card (centralizer {permOf c.1}) = c.2.2) (h : threeCentCaseOK c = true) :
    (∀ y ∈ centralizer {permOf c.1}, y * y ≠ 1 → y * y * (y * y) = 1 →
      y.support.card < 6 ∨ (y * y).support.card < 6) ∧
    ∀ a ∈ centralizer {permOf c.1}, ∀ b ∈ centralizer {permOf c.1}, a * a = 1 → b * b = 1 →
      a ≠ 1 → b ≠ 1 → 6 ≤ a.support.card → 6 ≤ b.support.card → a ≠ b → a * b = b * a →
      (a * b).support.card < 6 := by
  classical
  simp only [threeCentCaseOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hcg, hok⟩, hsz⟩, hZ4⟩, hV4⟩ := h
  have hEC := enumerates_of_list hok
  have hCle : closure {a | ∃ l ∈ c.2.1, a = permOf l} ≤ centralizer {permOf c.1} := by
    rw [closure_le]
    rintro a ⟨l, hl, rfl⟩
    rw [List.all_toArray, List.all_eq_true] at hcg
    have h1 := hcg (tabOf (permOf l)) (List.mem_map.mpr ⟨l, hl, rfl⟩)
    exact mem_centralizer_singleton_iff.mpr (commute_of_commutes h1)
  have hCeq : closure {a | ∃ l ∈ c.2.1, a = permOf l} = centralizer {permOf c.1} := by
    refine Subgroup.eq_of_le_of_card_ge hCle ?_
    rw [hcard, hEC.card, Array.length_toList]
    rw [beq_iff_eq] at hsz
    rw [hsz]
  have htab : ∀ y ∈ centralizer {permOf c.1}, ∃ t ∈ (enumBFS 9
      (c.2.1.map fun l => tabOf (permOf l)).toArray c.2.2).tabs.toList, TabRep t y := by
    intro y hy
    rw [← hCeq] at hy
    exact hEC.complete y hy
  refine ⟨fun y hy hy2 hy4 => ?_, fun a ha b hb ha2 hb2 ha1 hb1 ha6 hb6 hab hcomm => ?_⟩
  · obtain ⟨t, ht, hty⟩ := htab y hy
    rw [Array.all_eq_true'] at hZ4
    have h1 := hZ4 t (Array.mem_toList_iff.mp ht)
    have hty2 : TabRep (comp 9 t t) (y * y) := hty.comp hty
    have hty4 : TabRep (comp 9 (comp 9 t t) (comp 9 t t)) (y * y * (y * y)) :=
      hty2.comp hty2
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    rcases h1 with ((h1 | h1) | h1) | h1
    · exact absurd ((hty2.beq_iff TabRep.idTab).mp h1) hy2
    · exact absurd ((hty4.beq_iff TabRep.idTab).mpr hy4) (by rw [h1]; simp)
    · left
      rwa [← threeCentSupp_eq hty]
    · right
      rwa [← threeCentSupp_eq hty2]
  · obtain ⟨ta, hta, hrepa⟩ := htab a ha
    obtain ⟨tb, htb, hrepb⟩ := htab b hb
    have hbig : ∀ (t : Tab) (x : Perm (Fin 9)), t ∈ (enumBFS 9
        (c.2.1.map fun l => tabOf (permOf l)).toArray c.2.2).tabs.toList → TabRep t x →
        x * x = 1 → x ≠ 1 → 6 ≤ x.support.card →
        t ∈ ((enumBFS 9 (c.2.1.map fun l => tabOf (permOf l)).toArray c.2.2).tabs.filter
          fun a => comp 9 a a == idTab 9 && !(a == idTab 9) && 6 ≤ threeCentSupp a) := by
      intro t x ht hrep hx2 hx1 hx6
      rw [Array.mem_filter]
      refine ⟨Array.mem_toList_iff.mp ht, ?_⟩
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
      refine ⟨⟨((hrep.comp hrep).beq_iff TabRep.idTab).mpr hx2, ?_⟩, ?_⟩
      · rw [Bool.eq_false_iff]
        intro h2
        exact hx1 ((hrep.beq_iff TabRep.idTab).mp h2)
      · rwa [threeCentSupp_eq hrep]
    rw [Array.all_eq_true'] at hV4
    have h1 := hV4 ta (hbig ta a hta hrepa ha2 ha1 ha6)
    rw [Array.all_eq_true'] at h1
    have h2 := h1 tb (hbig tb b htb hrepb hb2 hb1 hb6)
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h2
    rcases h2 with (h2 | h2) | h2
    · exact absurd ((hrepa.beq_iff hrepb).mp h2) hab
    · exfalso
      have h3 : commutes ta tb = true := by
        rw [commutes, beq_iff_eq]
        exact (hrepa.comp hrepb).tab_eq (by rw [hcomm]; exact hrepb.comp hrepa)
      rw [h3] at h2
      exact Bool.false_ne_true h2.symm
    · rwa [← threeCentSupp_eq (hrepa.comp hrepb)]

theorem cycleType_fin_nine_of_pow_three {w : Perm (Fin 9)} {k : ℕ} (h3 : w ^ 3 = 1) (h1 : w ≠ 1)
    (hs : w.support.card = 3 * k) : w.cycleType = Multiset.replicate k 3 := by
  have hw : orderOf w = 3 := orderOf_eq_prime h3 h1
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (σ := w) (by rw [hw]; norm_num)
  rw [hw] at hn
  have hsum : w.support.card = 3 * (n + 1) := by
    rw [← Perm.sum_cycleType, hn, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  rw [hn]
  congr 1
  omega

end ThreeCent

open ThreeCent SixGen

theorem card_le_two_of_centralizer_three {u : Perm (Fin 9)}
    (hu : orderOf u = 3) {Y : Subgroup (Perm (Fin 9))} (hYu : Y ≤ centralizer {u})
    (hY2 : IsPGroup 2 Y) (hY6 : ∀ y ∈ Y, y ≠ 1 → 6 ≤ y.support.card) : Nat.card Y ≤ 2 := by
  classical
  have hc := Certificates.certificate22259
  rw [threeCentCheck, List.all_eq_true] at hc
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (σ := u) (by rw [hu]; norm_num)
  rw [hu] at hn
  have hsum : u.support.card = 3 * (n + 1) := by
    rw [← Perm.sum_cycleType, hn, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hle : u.support.card ≤ 9 := by
    have := Finset.card_le_univ u.support
    rwa [Fintype.card_fin] at this
  obtain ⟨c, hcmem, hct, hcard⟩ : ∃ c ∈ threeCentCases, (permOf c.1).cycleType = u.cycleType ∧
      Nat.card (centralizer {permOf c.1}) = c.2.2 := by
    have hn2 : n ≤ 2 := by omega
    interval_cases n
    · have hct : (permOf threeCentCases[0].1).cycleType = Multiset.replicate 1 3 :=
        cycleType_fin_nine_of_pow_three (by decide) (by decide) (by decide)
      refine ⟨threeCentCases[0], by simp [threeCentCases], by rw [hct, hn], ?_⟩
      rw [Perm.nat_card_centralizer, hct]
      simp
      decide
    · have hct : (permOf threeCentCases[1].1).cycleType = Multiset.replicate 2 3 :=
        cycleType_fin_nine_of_pow_three (by decide) (by decide) (by decide)
      refine ⟨threeCentCases[1], by simp [threeCentCases], by rw [hct, hn], ?_⟩
      rw [Perm.nat_card_centralizer, hct]
      simp
      decide
    · have hct : (permOf threeCentCases[2].1).cycleType = Multiset.replicate 3 3 :=
        cycleType_fin_nine_of_pow_three (by decide) (by decide) (by decide)
      refine ⟨threeCentCases[2], by simp [threeCentCases], by rw [hct, hn], ?_⟩
      rw [Perm.nat_card_centralizer, hct]
      simp
      decide
  obtain ⟨hZ4, hV4⟩ := threeCentCaseOK_spec hcard (hc c hcmem)
  obtain ⟨π, hπ⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr hct.symm)
  have hconjC : ∀ y ∈ Y, π * y * π⁻¹ ∈ centralizer {permOf c.1} := by
    intro y hy
    rw [mem_centralizer_singleton_iff, ← hπ]
    have h1 := mem_centralizer_singleton_iff.mp (hYu hy)
    calc π * y * π⁻¹ * (π * u * π⁻¹) = π * (y * u) * π⁻¹ := by group
      _ = π * (u * y) * π⁻¹ := by rw [h1]
      _ = π * u * π⁻¹ * (π * y * π⁻¹) := by group
  have hsupp : ∀ y : Perm (Fin 9), (π * y * π⁻¹).support.card = y.support.card :=
    fun y => Perm.card_support_conj
  have hconj_ne : ∀ y : Perm (Fin 9), y ≠ 1 → π * y * π⁻¹ ≠ 1 := fun y hy h => hy (by
    have := congrArg (fun z => π⁻¹ * z * π) h
    simpa [mul_assoc] using this)
  have hconj_mul : ∀ y z : Perm (Fin 9), π * y * π⁻¹ * (π * z * π⁻¹) = π * (y * z) * π⁻¹ :=
    fun y z => by group
  by_contra hY
  push Not at hY
  by_cases hexp : ∃ y ∈ Y, y * y ≠ 1
  · obtain ⟨y, hyY, hy2⟩ := hexp
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hY2) ⟨y, hyY⟩
    rw [Subgroup.orderOf_mk] at hj
    have hj2 : 2 ≤ j := by
      by_contra h2
      push Not at h2
      apply hy2
      rw [← sq]
      have h3 : orderOf y ∣ 2 := by
        rw [hj]
        interval_cases j <;> norm_num
      exact orderOf_dvd_iff_pow_eq_one.mp h3
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
    set z := y ^ 2 ^ i with hzdef
    have hzY : z ∈ Y := Y.pow_mem hyY _
    have hzo : orderOf z = 4 := by
      rw [hzdef, orderOf_pow_of_dvd (by positivity) (by rw [hj]; exact pow_dvd_pow 2 (by omega)),
        hj, pow_add, Nat.mul_div_cancel_left _ (by positivity)]
      norm_num
    have hz4 : z * z * (z * z) = 1 := by
      rw [← sq, ← sq, ← pow_mul, show 2 * 2 = orderOf z by rw [hzo], pow_orderOf_eq_one]
    have hz2 : z * z ≠ 1 := by
      intro h
      have h1 : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [sq]; exact h)
      rw [hzo] at h1
      exact absurd (Nat.le_of_dvd (by norm_num) h1) (by norm_num)
    have hz1 : z ≠ 1 := fun h => hz2 (by rw [h, mul_one])
    rcases hZ4 _ (hconjC z hzY) (by rw [hconj_mul]; exact hconj_ne _ hz2)
        (by rw [hconj_mul, hconj_mul, hz4, mul_one, mul_inv_cancel]) with h1 | h1
    · rw [hsupp] at h1
      exact absurd (hY6 z hzY hz1) (by omega)
    · rw [hconj_mul, hsupp] at h1
      exact absurd (hY6 _ (Y.mul_mem hzY hzY) hz2) (by omega)
  · push Not at hexp
    have hnt : ∃ a ∈ Y, a ≠ 1 := by
      by_contra h
      push Not at h
      have : Y = ⊥ := (Subgroup.eq_bot_iff_forall Y).mpr h
      rw [this, Subgroup.card_bot] at hY
      omega
    obtain ⟨a, haY, ha1⟩ := hnt
    have hnt2 : ∃ b ∈ Y, b ≠ 1 ∧ b ≠ a := by
      by_contra h
      push Not at h
      have hsub : (Y : Set (Perm (Fin 9))) ⊆ {1, a} := fun b hb => by
        by_cases hb1 : b = 1
        · exact Or.inl hb1
        · exact Or.inr (h b hb hb1)
      have h1 : Nat.card Y ≤ 2 := by
        rw [← SetLike.coe_sort_coe, Nat.card_eq_card_toFinset]
        calc (Y : Set (Perm (Fin 9))).toFinset.card ≤ ({1, a} : Finset (Perm (Fin 9))).card :=
              Finset.card_le_card (by
                intro x hx
                simpa using hsub (Set.mem_toFinset.mp hx))
          _ ≤ 2 := Finset.card_le_two
      omega
    obtain ⟨b, hbY, hb1, hba⟩ := hnt2
    have hab : a * b = b * a := by
      have ha2 := hexp a haY
      have hb2 := hexp b hbY
      calc a * b = a * b * (b * a) * (b * a) := by
            rw [mul_assoc (a * b), show b * a * (b * a) = 1 from hexp _ (Y.mul_mem hbY haY),
              mul_one]
        _ = a * (b * b) * a * (b * a) := by group
        _ = b * a := by rw [hb2, mul_one, ha2, one_mul]
    have hab1 : a * b ≠ 1 := fun h => hba (by
      have := congrArg (· * b) h
      simp only [one_mul] at this
      rw [mul_assoc, hexp b hbY, mul_one] at this
      exact this.symm)
    have h1 := hV4 _ (hconjC a haY) _ (hconjC b hbY)
      (by rw [hconj_mul, hexp a haY]; group) (by rw [hconj_mul, hexp b hbY]; group)
      (hconj_ne a ha1) (hconj_ne b hb1) (by rw [hsupp]; exact hY6 a haY ha1)
      (by rw [hsupp]; exact hY6 b hbY hb1)
      (fun h => hba (by
        have := congrArg (fun z => π⁻¹ * z * π) h
        simpa [mul_assoc] using this.symm))
      (by rw [hconj_mul, hconj_mul, hab])
    rw [hconj_mul, hsupp] at h1
    exact absurd (hY6 _ (Y.mul_mem haY hbY) hab1) (by omega)

end CFSG.ComponentClassification.SolMax

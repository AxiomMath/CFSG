module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Datum
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsGroup
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin A6Facts QuaternionGroup

theorem classify_rank_one_in_P0 {Y : Type} [Group Y] [Finite Y] (ι : Y →* P10)
    (hinj : Function.Injective ι) (hP : ∀ y, ι y ∈ P0) (hrank : CFSG.pRank 2 Y ≤ 1)
    (hfr : frattini Y ≠ ⊥) :
    Nonempty (Y ≃* Multiplicative (ZMod 4)) ∨ Nonempty (Y ≃* Multiplicative (ZMod 8)) ∨
      Nonempty (Y ≃* QuaternionGroup 2) := by
  have h8 : ∀ y : Y, y ^ 8 = 1 := fun y =>
    hinj (by rw [map_pow, map_one]; exact P0_pow_eight (hP y))
  have h2 : IsPGroup 2 Y := fun y => ⟨3, by simpa using h8 y⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 Y) := ⟨h2⟩
  rcases (CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification Nat.prime_two h2).1
    hrank with hcyc | ⟨-, n, hn, ⟨e⟩⟩
  ·
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hcard : Nat.card Y = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
    have hdvd : Nat.card Y ∣ 8 := by rw [hcard]; exact orderOf_dvd_of_pow_eq_one (h8 g)
    have hcomm : ∀ a b : Y, a * b = b * a := by
      intro a b
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
      exact (Commute.zpow_zpow_self g i j).eq
    have hbig : 4 ≤ Nat.card Y := by
      by_contra hlt
      push Not at hlt
      apply hfr
      apply frattini_eq_bot_of_exponent_two hcomm
      intro y
      have h1 := pow_card_eq_one' (G := Y) (x := y)
      have hpos := Nat.card_pos (α := Y)
      interval_cases hc : Nat.card Y
      · rw [pow_one] at h1
        rw [h1, one_pow]
      · exact h1
      · exfalso
        have : 3 ∣ 8 := hdvd
        omega
    obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card Y ∣ 2 ^ 3 from hdvd)
    have e := zmodCyclicMulEquiv hcyc
    interval_cases i
    · omega
    · omega
    · left
      rw [hci] at e
      exact ⟨e.symm⟩
    · right; left
      rw [hci] at e
      exact ⟨e.symm⟩
  ·
    set m : ℕ := 2 ^ (n - 2) with hm
    by_cases hm2 : m = 2
    · right; right
      rw [hm2] at e
      exact ⟨e⟩
    · exfalso
      have h2le : 2 ≤ n - 2 := by
        by_contra hlt
        have : n - 2 = 1 := by omega
        exact hm2 (by rw [hm, this]; norm_num)
      have hm4 : 4 ∣ m := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ∣ 2 ^ (n - 2) := pow_dvd_pow 2 h2le
      have hmpos : 0 < m := pow_pos (by norm_num) _
      have : NeZero m := ⟨hmpos.ne'⟩
      set α : QuaternionGroup m := (a 1) ^ (m / 4) with hα
      set β : QuaternionGroup m := xa 0 with hβ
      have hα4 : α ^ 4 = a (m : ZMod (2 * m)) := by
        rw [hα, ← pow_mul, Nat.div_mul_cancel hm4, a_one_pow]
      have hα4ne : α ^ 4 ≠ 1 := by
        rw [hα4, one_def]
        intro h
        have h1 : (m : ZMod (2 * m)) = 0 := by injection h
        rw [ZMod.natCast_eq_zero_iff] at h1
        have := Nat.le_of_dvd hmpos h1
        omega
      have hββ : β * β = α ^ 4 := by
        rw [hα4, hβ, xa_mul_xa]
        simp
      have hαβα : α * β * α = β := by
        have : α = a ((m / 4 : ℕ) : ZMod (2 * m)) := by rw [hα, a_one_pow]
        rw [this, hβ, a_mul_xa, xa_mul_a]
        simp
      set aY : Y := e.symm α with haY
      set bY : Y := e.symm β with hbY
      have h4 : aY ^ 4 ≠ 1 := by
        rw [haY, ← map_pow]
        intro h
        exact hα4ne (e.symm.injective (by rw [h, map_one]))
      have hb2 : bY * bY = aY ^ 4 := by
        rw [haY, hbY, ← map_pow, ← map_mul, hββ]
      have hab : aY * bY * aY = bY := by
        rw [haY, hbY, ← map_mul, ← map_mul, hαβα]
      refine P0_not_Q16 (hP aY) (hP bY) ?_ ?_ ?_
      · rw [← map_pow]
        intro h
        exact h4 (hinj (by rw [h, map_one]))
      · rw [← map_mul, ← map_pow, hb2]
      · rw [← map_mul, ← map_mul, hab]

theorem lemma2527 : Lemma2527 := by
  intro G _ _ T M hs N t zK h
  have hK0 : N.K0 = N.K := h.concl2520
  have hKH : N.H ≤ Subgroup.normalizer (N.K : Set G) := by
    rw [← hK0]; exact N.H_le_normalizer_K0
  obtain ⟨D⟩ := exists_a6Datum N hKH h.facts258 h.concl2521
  have hconj : ∀ a ∈ N.SC, N.x⁻¹ * a * N.x ∈ N.S := by
    intro a ha
    have : N.x⁻¹ * a * N.x ∈ CFSG.conjugate N.SC N.x := by
      rw [mem_conjugate_iff]
      have e : N.x * (N.x⁻¹ * a * N.x) * N.x⁻¹ = a := by group
      rw [e]; exact ha
    exact h.concl255.2.1 this
  let ι : ↥N.SC →* P10 :=
    { toFun := fun a => D.Φ (N.x⁻¹ * (a : G) * N.x)
      map_one' := by simpa using D.Φ_one
      map_mul' := fun a b => by
        have e : N.x⁻¹ * ((a * b : ↥N.SC) : G) * N.x =
            (N.x⁻¹ * (a : G) * N.x) * (N.x⁻¹ * (b : G) * N.x) := by
          simp only [Subgroup.coe_mul]; group
        simp only [e]
        exact D.mul _ (N.S_le_H (hconj a a.2)) _ (N.S_le_H (hconj b b.2)) }
  have hinj : Function.Injective ι := by
    intro a b hab
    have hx1 : N.x⁻¹ * (a : G) * N.x ∈ N.S := hconj a a.2
    have hx2 : N.x⁻¹ * (b : G) * N.x ∈ N.S := hconj b b.2
    have h1 := D.inv_mul_mem_SC hK0 hx1 hx2 hab
    have hmem2 : (N.x⁻¹ * (a : G) * N.x)⁻¹ * (N.x⁻¹ * (b : G) * N.x) ∈
        CFSG.conjugate N.SC N.x := by
      rw [mem_conjugate_iff]
      have e : N.x * ((N.x⁻¹ * (a : G) * N.x)⁻¹ * (N.x⁻¹ * (b : G) * N.x)) * N.x⁻¹ =
          (a : G)⁻¹ * b := by group
      rw [e]
      exact N.SC.mul_mem (N.SC.inv_mem a.2) b.2
    have h3 : (N.x⁻¹ * (a : G) * N.x)⁻¹ * (N.x⁻¹ * (b : G) * N.x) ∈
        N.SC ⊓ CFSG.conjugate N.SC N.x := ⟨h1, hmem2⟩
    rw [h.concl255.1, Subgroup.mem_bot] at h3
    have h4 : N.x⁻¹ * (a : G) * N.x = N.x⁻¹ * (b : G) * N.x := inv_mul_eq_one.mp h3
    apply Subtype.ext
    calc (a : G) = N.x * (N.x⁻¹ * (a : G) * N.x) * N.x⁻¹ := by group
      _ = N.x * (N.x⁻¹ * (b : G) * N.x) * N.x⁻¹ := by rw [h4]
      _ = b := by group
  have hP : ∀ a : ↥N.SC, ι a ∈ P0 := fun a => D.S_mem _ (hconj a a.2)
  have hrank : CFSG.pRank 2 ↥N.SC ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 2) N.SC]
    exact h.concl2526.le
  exact classify_rank_one_in_P0 ι hinj hP hrank h.concl2524

end CFSG.QuasithinUnique

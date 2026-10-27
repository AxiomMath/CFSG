module

public import CFSG.GH74.Uniqueness.SU.SU1ClassBound

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

open Subgroup

theorem exists_orderOf_four {P : Type*} [Group P] [Finite P] (h8 : Nat.card P = 8)
    (hnc : ¬ IsMulCommutative P) : ∃ g : P, orderOf g = 4 := by
  by_contra hcon
  push Not at hcon
  have hord : ∀ g : P, orderOf g = 1 ∨ orderOf g = 2 := by
    intro g
    have hdvd : orderOf g ∣ 2 ^ 3 := by
      have := orderOf_dvd_natCard g
      rwa [h8] at this
    obtain ⟨k, hk, hgk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases k
    · left; simpa using hgk
    · right; simpa using hgk
    · exact absurd hgk (hcon g)
    · exfalso
      have : orderOf g = Nat.card P := by rw [hgk, h8]; norm_num
      have hcyc : IsCyclic P := isCyclic_of_orderOf_eq_card g this
      exact hnc (inferInstance)
  apply hnc
  refine ⟨⟨fun a b => ?_⟩⟩
  have hsq : ∀ g : P, g * g = 1 := by
    intro g
    rcases hord g with h | h
    · rw [orderOf_eq_one_iff.mp h, one_mul]
    · rw [← pow_two, ← h]
      exact pow_orderOf_eq_one g
  have h1 := hsq (a * b)
  have h2 := hsq a
  have h3 := hsq b
  calc a * b = a * b * (a * b * (b * a)) := by
        have : a * b * (b * a) = 1 := by
          calc a * b * (b * a) = a * (b * b) * a := by group
            _ = 1 := by rw [h3, mul_one, h2]
        rw [this, mul_one]
    _ = (a * b * (a * b)) * (b * a) := by group
    _ = b * a := by rw [h1, one_mul]

theorem false_of_noncyclic_preimage {P : Type*} [Group P] [Finite P] {k : ℕ} (hk : 2 ≤ k)
    (hZ : Nat.card (center P) = 2) (M : Subgroup P) [M.Normal] (x : P) (hxM : x ∈ M)
    (hMdec : ∀ m ∈ M, ∃ (i : ℤ) (c : P), c ∈ center P ∧ m = x ^ i * c)
    (hord : orderOf (QuotientGroup.mk x : P ⧸ center P) = 2 ^ k) (hnc : ¬ IsCyclic M) :
    False := by
  have hcsq : ∀ c ∈ center P, c * c = 1 := by
    intro c hc
    have h1 : (⟨c, hc⟩ : center P) ^ Nat.card (center P) = 1 := pow_card_eq_one'
    rw [hZ] at h1
    have h2 := congrArg Subtype.val h1
    simpa [pow_two] using h2
  set T : Subgroup P := zpowers x with hT
  have hZT : center P ⊓ T = ⊥ := by
    by_contra hne
    have hdvd : Nat.card ↥(center P ⊓ T) ∣ 2 := hZ ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact hne (Subgroup.eq_bot_of_card_eq _ h1)
    · have hZle : center P ≤ T := by
        have : center P ⊓ T = center P :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h2, hZ])
        rw [← this]
        exact inf_le_right
      apply hnc
      have hMT : M = T := by
        refine le_antisymm (fun m hm => ?_) (Subgroup.zpowers_le.mpr hxM)
        obtain ⟨i, c, hc, rfl⟩ := hMdec m hm
        exact T.mul_mem (zpow_mem (Subgroup.mem_zpowers x) i) (hZle hc)
      rw [hMT]
      infer_instance
  have hpowZ : x ^ (2 ^ k) ∈ center P := by
    have h1 : (QuotientGroup.mk (x ^ (2 ^ k)) : P ⧸ center P) = 1 := by
      rw [QuotientGroup.mk_pow, ← hord]
      exact pow_orderOf_eq_one _
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hxk : x ^ (2 ^ k) = 1 := by
    have : x ^ (2 ^ k) ∈ center P ⊓ T := ⟨hpowZ, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _⟩
    rw [hZT] at this
    exact Subgroup.mem_bot.mp this
  have hox : orderOf x = 2 ^ k := by
    apply Nat.dvd_antisymm
    · exact orderOf_dvd_of_pow_eq_one hxk
    · rw [← hord]
      exact orderOf_map_dvd (QuotientGroup.mk' (center P)) x
  set w : P := x ^ (2 ^ (k - 1)) with hw
  have hk1 : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hww : w * w = 1 := by
    rw [hw, ← pow_add, ← two_mul, ← hk1]
    exact hxk
  have hw1 : w ≠ 1 := by
    intro h
    have : orderOf x ∣ 2 ^ (k - 1) := orderOf_dvd_of_pow_eq_one h
    rw [hox] at this
    have := Nat.le_of_dvd (pow_pos two_pos _) this
    have h2 : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hwcent : ∀ g : P, g * w * g⁻¹ = w := by
    intro g
    have hk2 : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
      rw [← pow_succ']
      congr 1
      omega
    have hxm : x ^ (2 ^ (k - 2)) ∈ M := Subgroup.pow_mem _ hxM _
    have hcM : g * x ^ (2 ^ (k - 2)) * g⁻¹ ∈ M := by
      have := (inferInstance : M.Normal).conj_mem _ hxm g
      exact this
    obtain ⟨i, d, hd, hcd⟩ := hMdec _ hcM
    have hsq : g * w * g⁻¹ = x ^ (i + i) := by
      have e1 : g * w * g⁻¹ = (g * x ^ (2 ^ (k - 2)) * g⁻¹) * (g * x ^ (2 ^ (k - 2)) * g⁻¹) := by
        have : w = x ^ (2 ^ (k - 2)) * x ^ (2 ^ (k - 2)) := by
          rw [hw, hk2, ← pow_add, ← two_mul, mul_comm]
        rw [this]
        group
      rw [e1, hcd]
      have hdc : x ^ i * d * (x ^ i * d) = x ^ i * x ^ i * (d * d) := by
        have := Subgroup.mem_center_iff.mp hd (x ^ i)
        calc x ^ i * d * (x ^ i * d) = x ^ i * (d * x ^ i) * d := by group
          _ = x ^ i * (x ^ i * d) * d := by rw [← this]
          _ = x ^ i * x ^ i * (d * d) := by group
      rw [hdc, hcsq d hd, mul_one, ← zpow_add]
    set u : P := g * w * g⁻¹ with hu
    have huu : u * u = 1 := by
      rw [hu]
      calc g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
        _ = 1 := by rw [hww]; group
    have hu1 : u ≠ 1 := by
      intro h
      apply hw1
      have : w = g⁻¹ * u * g := by rw [hu]; group
      rw [this, h]
      group
    have hx4 : x ^ (i + i + (i + i)) = 1 := by
      rw [zpow_add, ← hsq, huu]
    have hdvd : ((2 ^ k : ℕ) : ℤ) ∣ i + i + (i + i) := by
      rw [← hox]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hx4
    have hdvd2 : ((2 ^ (k - 2) : ℕ) : ℤ) ∣ i := by
      have h4 : (2 ^ k : ℕ) = 2 ^ (k - 2) * 4 := by
        have : k = (k - 2) + 2 := by omega
        conv_lhs => rw [this]
        rw [pow_add]
        norm_num
      have hdvd' : (((2 ^ (k - 2) : ℕ) : ℤ) * 4) ∣ i * 4 := by
        have h5 : i + i + (i + i) = i * 4 := by ring
        rw [h5, h4] at hdvd
        simpa [Nat.cast_mul] using hdvd
      exact (Int.mul_dvd_mul_iff_right (by norm_num : (4 : ℤ) ≠ 0)).mp hdvd'
    obtain ⟨t, ht⟩ := hdvd2
    have hut : u = w ^ t := by
      have h6 : i + i = ((2 ^ (k - 1) : ℕ) : ℤ) * t := by
        rw [hk2, ht]
        push_cast
        ring
      rw [hsq, h6, zpow_mul, zpow_natCast, hw]
    have hw2 : w ^ (2 : ℤ) = 1 := by rw [zpow_two, hww]
    rcases Int.even_or_odd' t with ⟨s, hs | hs⟩
    · exfalso
      apply hu1
      rw [hut, hs, zpow_mul, hw2, one_zpow]
    · rw [hut, hs, zpow_add, zpow_mul, hw2, one_zpow, one_mul, zpow_one]
  have hwZ : w ∈ center P := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := hwcent g
    calc g * w = g * w * g⁻¹ * g := by group
      _ = w * g := by rw [this]
  have hwT : w ∈ T := Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _
  have : w ∈ center P ⊓ T := ⟨hwZ, hwT⟩
  rw [hZT] at this
  exact hw1 (Subgroup.mem_bot.mp this)

theorem exists_cyclic_index_two :
    ∀ n : ℕ, 3 ≤ n → ∀ (P : Type) [Group P] [Finite P], Nat.card P = 2 ^ n →
      n - 1 ≤ Group.nilpotencyClass P → ∃ M : Subgroup P, M.index = 2 ∧ IsCyclic M := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro P _ _ hP hcl
    have hPp : IsPGroup 2 P := IsPGroup.of_card hP
    have hnil : Group.IsNilpotent P := hPp.isNilpotent
    have hnc : ¬ IsMulCommutative P := by
      intro hcomm
      have := (Group.IsNilpotent.nilpotencyClass_le_one_iff).mpr hcomm
      omega
    obtain ⟨g, hg⟩ := exists_orderOf_four (by simpa using hP) hnc
    refine ⟨zpowers g, ?_, inferInstance⟩
    have h1 := Subgroup.card_mul_index (zpowers g)
    rw [Nat.card_zpowers, hg, hP] at h1
    omega
  | succ n hn ih =>
    intro P _ _ hP hcl
    have hPp : IsPGroup 2 P := IsPGroup.of_card hP
    have hnil : Group.IsNilpotent P := hPp.isNilpotent
    have hZc : Nat.card (center P) = 2 :=
      card_center_of_maxClass Nat.prime_two (n := n + 1) (by omega) hP (by omega)
    have hQcard : Nat.card (P ⧸ center P) = 2 ^ n := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center P)
      rw [hZc, hP, pow_succ] at h1
      exact (Nat.eq_of_mul_eq_mul_right two_pos h1).symm
    have hQcl : n - 1 ≤ Group.nilpotencyClass (P ⧸ center P) := by
      rw [Group.nilpotencyClass_quotient_center]
      omega
    obtain ⟨M', hM'idx, hM'cyc⟩ := ih (P ⧸ center P) hQcard hQcl
    set f : P →* P ⧸ center P := QuotientGroup.mk' (center P) with hf
    have hfs : Function.Surjective f := QuotientGroup.mk'_surjective _
    set M : Subgroup P := M'.comap f with hM
    have hMidx : M.index = 2 := by
      rw [hM, Subgroup.index_comap_of_surjective M' hfs, hM'idx]
    have hMn : M.Normal := Subgroup.normal_of_index_eq_two hMidx
    by_cases hMcyc : IsCyclic M
    · exact ⟨M, hMidx, hMcyc⟩
    exfalso
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := M')
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (g : P ⧸ center P)
    have hxM : x ∈ M := by
      rw [hM, Subgroup.mem_comap]
      change (x : P ⧸ center P) ∈ M'
      rw [hx]
      exact g.2
    have hMdec : ∀ m ∈ M, ∃ (i : ℤ) (c : P), c ∈ center P ∧ m = x ^ i * c := by
      intro m hm
      have hm' : f m ∈ M' := hm
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨f m, hm'⟩)
      have hi' : (g : P ⧸ center P) ^ i = f m := congrArg Subtype.val hi
      refine ⟨i, (x ^ i)⁻¹ * m, ?_, by group⟩
      rw [← QuotientGroup.eq_one_iff]
      change f ((x ^ i)⁻¹ * m) = 1
      rw [map_mul, map_inv, map_zpow]
      have : f x = (g : P ⧸ center P) := hx
      rw [this, hi']
      group
    have hord : orderOf (QuotientGroup.mk x : P ⧸ center P) = 2 ^ (n - 1) := by
      have h1 : orderOf (g : P ⧸ center P) = Nat.card M' := by
        rw [Subgroup.orderOf_coe]
        exact orderOf_eq_card_of_forall_mem_zpowers hg
      have h2 : Nat.card M' = 2 ^ (n - 1) := by
        have h3 := Subgroup.card_mul_index M'
        rw [hM'idx, hQcard] at h3
        have : 2 ^ n = 2 ^ (n - 1) * 2 := by
          rw [← pow_succ]
          congr 1
          omega
        rw [this] at h3
        exact Nat.eq_of_mul_eq_mul_right two_pos h3
      rw [← hx] at h1
      exact h1.trans h2
    exact false_of_noncyclic_preimage (k := n - 1) (by omega) hZc M x hxM hMdec hord hMcyc

theorem card_le_four_of_cyclic_index_two {P : Type*} [Group P] [Finite P] {M : Subgroup P}
    (hM : M.index = 2) [IsCyclic M] {E : Subgroup P} (hE : ∀ y ∈ E, y * y = 1) :
    Nat.card E ≤ 4 := by
  have hS : Nat.card ↥(M ⊓ E) ≤ 2 := by
    set S : Subgroup M := (M ⊓ E).subgroupOf M with hSdef
    have hcard : Nat.card ↥(M ⊓ E) = Nat.card S :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : M ⊓ E ≤ M)).toEquiv).symm
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := S)
    have hog : orderOf g = Nat.card S := orderOf_eq_card_of_forall_mem_zpowers hg
    have hg2 : g * g = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact hE _ (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp g.2)).2
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    rw [hcard, ← hog]
    exact Nat.le_of_dvd two_pos hdvd
  have h1 := Subgroup.relIndex_mul_card (H := M) (K := E)
  have hne : M.relIndex ⊤ ≠ 0 := Subgroup.FiniteIndex.index_ne_zero (H := M.subgroupOf ⊤)
  have h2 : M.relIndex E ≤ 2 := by
    calc M.relIndex E ≤ M.relIndex ⊤ := Subgroup.relIndex_le_of_le_right le_top hne
      _ = 2 := by rw [Subgroup.relIndex_top_right, hM]
  rw [← h1]
  calc M.relIndex E * Nat.card ↥(M ⊓ E) ≤ 2 * 2 := Nat.mul_le_mul h2 hS
    _ = 4 := by norm_num

end CFSG.GH74.Uniqueness.SU.SU1

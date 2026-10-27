module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.ClassicalInvolution.Q3.SP3

universe u

section Aux

variable {T : Type u} [Group T]

theorem eq_one_or_eq_of_mem_zpowers {n w : T} (hn : n * n = 1) (hw : w ∈ Subgroup.zpowers n) :
    w = 1 ∨ w = n := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have h2 : n ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hn
  have : n ^ k = n ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left; rw [this, h0]; simp
  · right; rw [this, h1]; simp

theorem mem_of_pow_three_mem {c : T} {S : Subgroup T} (hT : IsPGroup 2 T) (h : c ^ 3 ∈ S) :
    c ∈ S := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hT c
  have hcop : Nat.Coprime 3 (orderOf c) := by
    rw [hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact S.pow_mem h m

end Aux

section Main

theorem inv_mul_map_mem_aux (m : ℕ) : ∀ (T : Type u) [Group T] [Finite T], Nat.card T = m →
    IsPGroup 2 T → ∀ (g : T →* T), (∀ x, g (g (g x)) = x) → ∀ (Q : Subgroup T) (z : T),
    z ∈ Q → z * z = 1 → (∀ x ∈ Q, x * x = 1 → x = 1 ∨ x = z) → g z = z →
    Q ≤ Subgroup.closure {y | ∃ x ∈ Q, y = x⁻¹ * g x} →
    (∀ x : T, x * z = z * x → x⁻¹ * g x ∈ Q) → ∀ x : T, x⁻¹ * g x ∈ Q := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro T _ _ hm hT g hg Q z hzQ hz2 hQ2 hgz hQg H1
  by_cases hzc : z ∈ Subgroup.center T
  · intro x
    exact H1 x (Subgroup.mem_center_iff.mp hzc x)
  have hz1 : z ≠ 1 := fun h => hzc (h ▸ one_mem _)
  have hQz : ∀ q ∈ Q, q * z = z * q := by
    intro q hq
    have hmem : q * z * q⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hq hzQ) (Q.inv_mem hq)
    have hsq : q * z * q⁻¹ * (q * z * q⁻¹) = 1 := by
      calc q * z * q⁻¹ * (q * z * q⁻¹) = q * (z * z) * q⁻¹ := by group
        _ = 1 := by rw [hz2]; group
    rcases hQ2 _ hmem hsq with h | h
    · exfalso
      apply hz1
      calc z = q⁻¹ * (q * z * q⁻¹) * q := by group
        _ = 1 := by rw [h]; group
    · calc q * z = (q * z * q⁻¹) * q := by group
        _ = z * q := by rw [h]
  have hQg' : ∀ q ∈ Q, g q ∈ Q := fun q hq => by
    have h1 := H1 q (hQz q hq)
    have h2 : g q = q * (q⁻¹ * g q) := by group
    rw [h2]
    exact Q.mul_mem hq h1
  have hgC : ∀ c, c * z = z * c → g c * z = z * g c := fun c hc => by
    have := congrArg g hc
    rwa [map_mul, map_mul, hgz] at this
  have hnorm : ∀ c, c * z = z * c → ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := by
    set S : Set T := {y | ∃ x, x * z = z * x ∧ y = x⁻¹ * g x} with hS
    have hDQ : Subgroup.closure S ≤ Q := by
      rw [Subgroup.closure_le]
      rintro y ⟨x, hx, rfl⟩
      exact H1 x hx
    have hQD : Q ≤ Subgroup.closure S :=
      hQg.trans (Subgroup.closure_mono fun y ⟨x, hxQ, hy⟩ => ⟨x, hQz x hxQ, hy⟩)
    intro c hc q hq
    have hcinv : c⁻¹ * z = z * c⁻¹ := (Commute.inv_left (show Commute c z from hc)).eq
    have hgen : ∀ y ∈ S, c * y * c⁻¹ ∈ Subgroup.closure S := by
      rintro y ⟨x, hx, rfl⟩
      have hxc : (x * c⁻¹) * z = z * (x * c⁻¹) :=
        (Commute.mul_left (show Commute x z from hx) (show Commute c⁻¹ z from hcinv)).eq
      have h1 : (x * c⁻¹)⁻¹ * g (x * c⁻¹) ∈ Subgroup.closure S :=
        Subgroup.subset_closure ⟨x * c⁻¹, hxc, rfl⟩
      have h2 : ((c⁻¹)⁻¹ * g c⁻¹)⁻¹ ∈ Subgroup.closure S :=
        Subgroup.inv_mem _ (Subgroup.subset_closure ⟨c⁻¹, hcinv, rfl⟩)
      have e : c * (x⁻¹ * g x) * c⁻¹ = (x * c⁻¹)⁻¹ * g (x * c⁻¹) * ((c⁻¹)⁻¹ * g c⁻¹)⁻¹ := by
        simp only [map_mul, map_inv, inv_inv, mul_inv_rev]
        group
      rw [e]
      exact Subgroup.mul_mem _ h1 h2
    have hqD : c * q * c⁻¹ ∈ Subgroup.closure S := by
      refine Subgroup.closure_induction (p := fun q _ => c * q * c⁻¹ ∈ Subgroup.closure S)
        (fun y hy => hgen y hy) (by simp) (fun a b _ _ ha hb => ?_) (fun a _ ha => ?_)
        (hQD hq)
      · have : c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
        rw [this]
        exact Subgroup.mul_mem _ ha hb
      · have : c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ := by group
        rw [this]
        exact Subgroup.inv_mem _ ha
    exact hDQ hqD
  have hc3 : ∀ c, c * z = z * c → c * g c * g (g c) = 1 → c ∈ Q := by
    intro c hc h1
    have hq1 : c⁻¹ * g c ∈ Q := H1 c hc
    have hq2 : (g c)⁻¹ * g (g c) ∈ Q := H1 (g c) (hgC c hc)
    have hcinv : c⁻¹ * z = z * c⁻¹ := (Commute.inv_left (show Commute c z from hc)).eq
    have hq1' : c⁻¹ * (c⁻¹ * g c) * c⁻¹⁻¹ ∈ Q := hnorm c⁻¹ hcinv _ hq1
    have key : c ^ 3 = ((c⁻¹ * (c⁻¹ * g c) * c⁻¹⁻¹) * (c⁻¹ * g c) * ((g c)⁻¹ * g (g c)))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc c ^ 3 * (c⁻¹ * (c⁻¹ * g c) * c⁻¹⁻¹ * (c⁻¹ * g c) * ((g c)⁻¹ * g (g c)))
          = c * g c * g (g c) := by group
        _ = 1 := h1
    have hmem : c ^ 3 ∈ Q := by
      rw [key]
      exact Q.inv_mem (Q.mul_mem (Q.mul_mem hq1' hq1) hq2)
    exact mem_of_pow_three_mem hT hmem
  have : Nontrivial T := ⟨⟨z, 1, hz1⟩⟩
  obtain ⟨n, hnc, hn2, hn1⟩ : ∃ n : T, n ∈ Subgroup.center T ∧ n * n = 1 ∧ n ≠ 1 := by
    have : Nontrivial (Subgroup.center T) := hT.center_nontrivial
    have hZ2 : IsPGroup 2 (Subgroup.center T) := hT.to_subgroup _
    obtain ⟨k, hk⟩ := hZ2.exists_card_eq
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hk
      have := Finite.one_lt_card (α := Subgroup.center T)
      omega
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center T) 2
      (by rw [hk]; exact dvd_pow_self 2 hk0)
    refine ⟨x, x.2, ?_, ?_⟩
    · have h := pow_orderOf_eq_one x
      rw [hx] at h
      have := congrArg Subtype.val h
      simpa [sq] using this
    · intro h
      have : x = 1 := Subtype.ext h
      rw [this, orderOf_one] at hx
      omega
  have hnc' : ∀ y, n * y = y * n := fun y => (Subgroup.mem_center_iff.mp hnc y).symm
  have hgnc : ∀ y, g n * y = y * g n := by
    intro y
    calc g n * y = g n * g (g (g y)) := by rw [hg y]
      _ = g (n * g (g y)) := by rw [map_mul]
      _ = g (g (g y) * n) := by rw [hnc']
      _ = y * g n := by rw [map_mul, hg y]
  have hgnmem : g n ∈ Subgroup.center T := Subgroup.mem_center_iff.mpr fun y => (hgnc y).symm
  have hgn : g n = n := by
    have hgnq : n⁻¹ * g n ∈ Q := H1 n (hnc' z)
    have hsq : (n⁻¹ * g n) * (n⁻¹ * g n) = 1 := by
      have hu : ∀ y, n⁻¹ * y = y * n⁻¹ := fun y =>
        (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hnc) y).symm
      calc (n⁻¹ * g n) * (n⁻¹ * g n) = n⁻¹ * (g n * n⁻¹) * g n := by group
        _ = n⁻¹ * (n⁻¹ * g n) * g n := by rw [hgnc n⁻¹, hu]
        _ = (n * n)⁻¹ * (g n * g n) := by
          have : n⁻¹ * (n⁻¹ * g n) * g n = n⁻¹ * n⁻¹ * (g n * g n) := by group
          rw [this, mul_inv_rev]
        _ = 1 := by rw [hn2, ← map_mul, hn2, map_one]; group
    rcases hQ2 _ hgnq hsq with h | h
    · calc g n = n * (n⁻¹ * g n) := by group
        _ = n := by rw [h, mul_one]
    · exfalso
      apply hzc
      rw [← h]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hnc) hgnmem
  have hnQ : n ∉ Q := fun h => by
    rcases hQ2 n h hn2 with h1 | h1
    · exact hn1 h1
    · exact hzc (h1 ▸ hnc)
  set N : Subgroup T := Subgroup.zpowers n with hNdef
  have hNle : N ≤ Subgroup.center T := Subgroup.zpowers_le.mpr hnc
  have hNn : N.Normal := Subgroup.normal_of_le_center hNle
  have hNeq : ∀ w ∈ N, w = 1 ∨ w = n := fun w hw => eq_one_or_eq_of_mem_zpowers hn2 hw
  have hgN : ∀ w ∈ N, g w = w := by
    intro w hw
    rcases hNeq w hw with rfl | rfl
    · exact map_one g
    · exact hgn
  have hNcom : ∀ w ∈ N, ∀ y, w * y = y * w := fun w hw y =>
    (Subgroup.mem_center_iff.mp (hNle hw) y).symm
  let gb : T ⧸ N →* T ⧸ N :=
    QuotientGroup.map N N g (fun w hw => by rw [Subgroup.mem_comap, hgN w hw]; exact hw)
  have hgb : ∀ x : T, gb (x : T ⧸ N) = ((g x : T) : T ⧸ N) := fun x =>
    QuotientGroup.map_mk N N g _ x
  have hcardlt : Nat.card (T ⧸ N) < m := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have h2 : 1 < Nat.card N := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      intro hb
      have : n ∈ N := Subgroup.mem_zpowers n
      rw [hb, Subgroup.mem_bot] at this
      exact hn1 this
    have h3 : 0 < Nat.card (T ⧸ N) := Nat.card_pos
    rw [← hm]
    calc Nat.card (T ⧸ N) < Nat.card (T ⧸ N) * Nat.card N := lt_mul_of_one_lt_right h3 h2
      _ = Nat.card T := h1.symm
  have hTq : IsPGroup 2 (T ⧸ N) := hT.to_quotient N
  have hgb3 : ∀ x : T ⧸ N, gb (gb (gb x)) = x := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H x => rw [hgb, hgb, hgb, hg]
  have hz'Q : (z : T ⧸ N) ∈ Q.map (QuotientGroup.mk' N) := ⟨z, hzQ, rfl⟩
  have hz'2 : (z : T ⧸ N) * (z : T ⧸ N) = 1 := by rw [← QuotientGroup.mk_mul, hz2]; rfl
  have hQ'2 : ∀ x ∈ Q.map (QuotientGroup.mk' N), x * x = 1 → x = 1 ∨ x = (z : T ⧸ N) := by
    rintro _ ⟨q, hq, rfl⟩ hsq
    have hsq' : ((q * q : T) : T ⧸ N) = 1 := by rw [QuotientGroup.mk_mul]; exact hsq
    have hqqN : q * q ∈ N := (QuotientGroup.eq_one_iff _).mp hsq'
    have hqq : q * q = 1 := by
      rcases hNeq _ hqqN with h | h
      · exact h
      · exfalso
        apply hnQ
        rw [← h]
        exact Q.mul_mem hq hq
    rcases hQ2 q hq hqq with h | h
    · left; rw [h]; rfl
    · right; rw [h]; rfl
  have hgbz : gb (z : T ⧸ N) = (z : T ⧸ N) := by rw [hgb, hgz]
  have hQ'g : Q.map (QuotientGroup.mk' N) ≤
      Subgroup.closure {y | ∃ x ∈ Q.map (QuotientGroup.mk' N), y = x⁻¹ * gb x} := by
    have h1 := Subgroup.map_mono (f := QuotientGroup.mk' N) hQg
    rw [MonoidHom.map_closure] at h1
    refine h1.trans (Subgroup.closure_mono ?_)
    rintro _ ⟨y, ⟨x, hxQ, rfl⟩, rfl⟩
    refine ⟨(x : T ⧸ N), ⟨x, hxQ, rfl⟩, ?_⟩
    simp [hgb]
  have hH1' : ∀ x : T ⧸ N, x * (z : T ⧸ N) = (z : T ⧸ N) * x →
      x⁻¹ * gb x ∈ Q.map (QuotientGroup.mk' N) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
    intro hx
    have hν : x * z * x⁻¹ * z⁻¹ ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hx]
      group
    have hgν := hgN _ hν
    simp only [map_mul, map_inv, hgz] at hgν
    have hcz : (x⁻¹ * g x) * z = z * (x⁻¹ * g x) := by
      have h1 : g x * z * (g x)⁻¹ = x * z * x⁻¹ := by
        have := congrArg (fun w => w * z) hgν
        simpa [mul_assoc] using this
      calc (x⁻¹ * g x) * z = x⁻¹ * (g x * z * (g x)⁻¹) * g x := by group
        _ = x⁻¹ * (x * z * x⁻¹) * g x := by rw [h1]
        _ = z * (x⁻¹ * g x) := by group
    have hprod : (x⁻¹ * g x) * g (x⁻¹ * g x) * g (g (x⁻¹ * g x)) = 1 := by
      simp only [map_mul, map_inv, hg x]
      group
    have hcQ := hc3 _ hcz hprod
    rw [hgb]
    exact ⟨x⁻¹ * g x, hcQ, by simp⟩
  have IHres := ih (Nat.card (T ⧸ N)) hcardlt (T ⧸ N) rfl hTq gb hgb3
    (Q.map (QuotientGroup.mk' N)) (z : T ⧸ N) hz'Q hz'2 hQ'2 hgbz hQ'g hH1'
  intro x
  have h := IHres (x : T ⧸ N)
  rw [hgb] at h
  obtain ⟨q, hq, hqe⟩ := h
  have hνN : q⁻¹ * (x⁻¹ * g x) ∈ N := QuotientGroup.eq.mp (by simpa using hqe)
  have hc : x⁻¹ * g x = q * (q⁻¹ * (x⁻¹ * g x)) := by group
  have hcz : (x⁻¹ * g x) * z = z * (x⁻¹ * g x) := by
    set ν := q⁻¹ * (x⁻¹ * g x) with hν
    rw [hc]
    calc (q * ν) * z = q * (ν * z) := mul_assoc _ _ _
      _ = q * (z * ν) := by rw [hNcom ν hνN z]
      _ = (q * z) * ν := (mul_assoc _ _ _).symm
      _ = (z * q) * ν := by rw [hQz q hq]
      _ = z * (q * ν) := mul_assoc _ _ _
  have hprod : (x⁻¹ * g x) * g (x⁻¹ * g x) * g (g (x⁻¹ * g x)) = 1 := by
    simp only [map_mul, map_inv, hg x]
    group
  exact hc3 _ hcz hprod

theorem inv_mul_map_mem_of_centralizer {T : Type u} [Group T] [Finite T] (hT : IsPGroup 2 T)
    (g : T →* T) (hg : ∀ x, g (g (g x)) = x) (Q : Subgroup T) (z : T) (hzQ : z ∈ Q)
    (hz2 : z * z = 1) (hQ2 : ∀ x ∈ Q, x * x = 1 → x = 1 ∨ x = z) (hgz : g z = z)
    (hQg : Q ≤ Subgroup.closure {y | ∃ x ∈ Q, y = x⁻¹ * g x})
    (H1 : ∀ x : T, x * z = z * x → x⁻¹ * g x ∈ Q) : ∀ x : T, x⁻¹ * g x ∈ Q :=
  inv_mul_map_mem_aux (Nat.card T) T rfl hT g hg Q z hzQ hz2 hQ2 hgz hQg H1

end Main

end CFSG.ClassicalInvolution.Q3.SP3

module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.AlphaCore

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census423Three

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res423Two
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

@[expose] def Rank2 (X : Type) [Group X] : Prop :=
  ∀ E : Subgroup X, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
    Nat.card E ≤ 9

omit [Finite X] in
theorem qRes_normalized {d c : X} (hc : c ∈ Subgroup.centralizer ({d} : Set X)) {y : X}
    (hy : y ∈ qRes d) : c * y * c⁻¹ ∈ qRes d := by
  have hcd : (MulAut.conj c : MulAut X) d = d := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    simp only [MulAut.conj_apply]
    calc c * d * c⁻¹ = d * c * c⁻¹ := by rw [this]
      _ = d := by group
  have h := map_qRes (MulAut.conj c) hcd
  rw [← h]
  exact ⟨y, hy, rfl⟩

omit [Finite X] in
theorem qRes_conj {d : X} (g : X) {y : X} (hy : y ∈ qRes d) : g * y * g⁻¹ ∈ qRes (g * d * g⁻¹) := by
  have h : (qRes d).map (MulAut.conj g).toMonoidHom = qRes (g * d * g⁻¹) := by
    unfold qRes
    rw [map_inSubgroup_perfectResidual (MulAut.conj g), map_centralizer_singleton]
    rfl
  rw [← h]
  exact ⟨y, hy, rfl⟩

theorem card_pow_three {E : Subgroup X} (hE : ∀ x ∈ E, x ^ 3 = 1) : ∃ n : ℕ, Nat.card E = 3 ^ n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := fun g => ⟨1, by simpa using Subtype.ext (hE g g.2)⟩
  exact IsPGroup.iff_card.mp hp

theorem not_rank2_of_three (hR : Rank2 X) {a b c : X} (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1) (ha1 : a ≠ 1)
    (hb' : b ∉ Subgroup.zpowers a) (hc' : c ∉ Subgroup.closure {a, b}) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S : Set X := {a, b, c} with hS
  have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | rfl | assumption | exact (‹_ = _›).symm
  have hcl : Subgroup.closure S ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro x hx
    exact fun y hy => (hSc x hx y hy).symm
  have hEc : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx y hy
    have h1 := Subgroup.closure_le_centralizer_centralizer S hx
    exact (Subgroup.mem_centralizer_iff.mp h1 y (hcl hy)).symm
  have hEe : ∀ x ∈ Subgroup.closure S, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    | one => exact one_pow 3
    | mul x y hx hy hx3 hy3 =>
      have hcomm : Commute x y := hEc x hx y hy
      rw [hcomm.mul_pow, hx3, hy3, one_mul]
    | inv x hx hx3 => rw [inv_pow, hx3, inv_one]
  have hle1 : Subgroup.zpowers a ≤ Subgroup.closure {a, b} := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  have hle2 : Subgroup.closure {a, b} ≤ Subgroup.closure S := by
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hbmem : b ∈ Subgroup.closure {a, b} := Subgroup.subset_closure (by simp)
  have hcmem : c ∈ Subgroup.closure S := Subgroup.subset_closure (by simp [hS])
  have hlt1 : Subgroup.zpowers a < Subgroup.closure {a, b} :=
    lt_of_le_of_ne hle1 (fun h => hb' (h ▸ hbmem))
  have hlt2 : Subgroup.closure {a, b} < Subgroup.closure S :=
    lt_of_le_of_ne hle2 (fun h => hc' (h ▸ hcmem))
  have hE2e : ∀ x ∈ Subgroup.closure {a, b}, x ^ 3 = 1 := fun x hx => hEe x (hle2 hx)
  obtain ⟨n₂, hn₂⟩ := card_pow_three hE2e
  obtain ⟨n₃, hn₃⟩ := card_pow_three hEe
  have hc1 : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha ha1]
  have h12 := Subgroup.card_lt_of_lt hlt1
  have h23 := Subgroup.card_lt_of_lt hlt2
  rw [hc1, hn₂] at h12
  rw [hn₂, hn₃] at h23
  have hn₂' : 2 ≤ n₂ := by
    by_contra h
    push Not at h
    interval_cases n₂ <;> simp at h12
  have hn₃' : 3 ≤ n₃ := by
    by_contra h
    push Not at h
    have : n₃ ≤ n₂ := by omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp h23
    omega
  have hbig : 27 ≤ Nat.card (Subgroup.closure S) := by
    rw [hn₃]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ n₃ := Nat.pow_le_pow_right (by norm_num) hn₃'
  have := hR _ hEc hEe
  omega

theorem sup_zpowers_eq {D : Subgroup X} (hDexp : ∀ x ∈ D, x ^ 3 = 1) (hD9 : Nat.card D = 9)
    {d e : X} (hd : d ∈ D) (hd1 : d ≠ 1) (he : e ∈ D) (hed : e ∉ Subgroup.zpowers d) :
    Subgroup.zpowers d ⊔ Subgroup.zpowers e = D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P : Subgroup X := Subgroup.zpowers d ⊔ Subgroup.zpowers e with hP
  have hle : P ≤ D :=
    sup_le ((Subgroup.zpowers_le).mpr hd) ((Subgroup.zpowers_le).mpr he)
  have hcd : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hDexp d hd) hd1]
  have hdvd : 3 ∣ Nat.card P := by
    rw [← hcd]
    exact Subgroup.card_dvd_of_le (le_sup_left : Subgroup.zpowers d ≤ P)
  have heP : e ∈ P := Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have hne : Subgroup.zpowers d ≠ P := by
    intro h
    apply hed
    rwa [← h] at heP
  have hlt : Subgroup.zpowers d < P := lt_of_le_of_ne le_sup_left hne
  have h3 := Subgroup.card_lt_of_lt hlt
  rw [hcd] at h3
  have hdiv : Nat.card P ∣ 9 := by
    rw [← hD9]
    exact Subgroup.card_dvd_of_le hle
  have h9 : Nat.card P = 9 := by
    obtain ⟨k, hk⟩ := hdvd
    have hk9 : k ∣ 3 := by
      have : 3 * k ∣ 3 * 3 := hk ▸ hdiv
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) this
    rcases (Nat.dvd_prime Nat.prime_three).mp hk9 with h | h
    · rw [h] at hk; omega
    · rw [h] at hk; omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h9, hD9])

end CFSG.AGLEmbeddingD2.Wilson.Census423Three

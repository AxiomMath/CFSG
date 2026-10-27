module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Open.Defs

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def projSub (N₁ N₂ A : Subgroup G) (hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x) :
    Subgroup G where
  carrier := {n | n ∈ N₁ ∧ ∃ m ∈ N₂, n * m ∈ A}
  mul_mem' := by
    rintro a b ⟨ha, m, hm, ham⟩ ⟨hb, m', hm', hbm'⟩
    refine ⟨N₁.mul_mem ha hb, m * m', N₂.mul_mem hm hm', ?_⟩
    have h := hcomm b hb m hm
    have : a * b * (m * m') = (a * m) * (b * m') := by
      calc a * b * (m * m') = a * (b * m) * m' := by group
        _ = a * (m * b) * m' := by rw [h]
        _ = (a * m) * (b * m') := by group
    rw [this]
    exact A.mul_mem ham hbm'
  one_mem' := ⟨N₁.one_mem, 1, N₂.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, m, hm, ham⟩
    refine ⟨N₁.inv_mem ha, m⁻¹, N₂.inv_mem hm, ?_⟩
    have h := hcomm a⁻¹ (N₁.inv_mem ha) m⁻¹ (N₂.inv_mem hm)
    have : a⁻¹ * m⁻¹ = (a * m)⁻¹ := by rw [h]; group
    rw [this]
    exact A.inv_mem ham

theorem mem_projSub {N₁ N₂ A : Subgroup G} {hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x} {n : G} :
    n ∈ projSub N₁ N₂ A hcomm ↔ n ∈ N₁ ∧ ∃ m ∈ N₂, n * m ∈ A :=
  Iff.rfl

theorem projSub_le {N₁ N₂ A : Subgroup G} {hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x} :
    projSub N₁ N₂ A hcomm ≤ N₁ := fun _ h => h.1

@[expose] def mulSub (H₁ H₂ : Subgroup G) (hcomm : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x) :
    Subgroup G where
  carrier := {a | ∃ c ∈ H₁, ∃ d ∈ H₂, a = c * d}
  mul_mem' := by
    rintro a b ⟨c, hc, d, hd, rfl⟩ ⟨c', hc', d', hd', rfl⟩
    refine ⟨c * c', H₁.mul_mem hc hc', d * d', H₂.mul_mem hd hd', ?_⟩
    have h := hcomm c' hc' d hd
    calc c * d * (c' * d') = c * (d * c') * d' := by group
      _ = c * (c' * d) * d' := by rw [h]
      _ = c * c' * (d * d') := by group
  one_mem' := ⟨1, H₁.one_mem, 1, H₂.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨c, hc, d, hd, rfl⟩
    refine ⟨c⁻¹, H₁.inv_mem hc, d⁻¹, H₂.inv_mem hd, ?_⟩
    have h := hcomm c⁻¹ (H₁.inv_mem hc) d⁻¹ (H₂.inv_mem hd)
    rw [h]
    group

theorem mem_mulSub {H₁ H₂ : Subgroup G} {hcomm : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x} {a : G} :
    a ∈ mulSub H₁ H₂ hcomm ↔ ∃ c ∈ H₁, ∃ d ∈ H₂, a = c * d :=
  Iff.rfl

theorem commutatorElement_mul_mul {N₁ N₂ : Subgroup G}
    (hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x) {n n' m m' : G} (hn : n ∈ N₁) (hn' : n' ∈ N₁)
    (hm : m ∈ N₂) (hm' : m' ∈ N₂) : ⁅n * m, n' * m'⁆ = ⁅n, n'⁆ * ⁅m, m'⁆ := by
  let φ : N₁ × N₂ →* G := MonoidHom.noncommCoprod N₁.subtype N₂.subtype
    (fun a b => hcomm a a.2 b b.2)
  have h := map_commutatorElement φ (⟨n, hn⟩, ⟨m, hm⟩) (⟨n', hn'⟩, ⟨m', hm'⟩)
  have h1 : φ (⟨n, hn⟩, ⟨m, hm⟩) = n * m := rfl
  have h2 : φ (⟨n', hn'⟩, ⟨m', hm'⟩) = n' * m' := rfl
  rw [h1, h2] at h
  have h3 : ⁅((⟨n, hn⟩ : N₁), (⟨m, hm⟩ : N₂)), ((⟨n', hn'⟩ : N₁), (⟨m', hm'⟩ : N₂))⁆ =
      (⁅(⟨n, hn⟩ : N₁), ⟨n', hn'⟩⁆, ⁅(⟨m, hm⟩ : N₂), ⟨m', hm'⟩⁆) := by
    simp [commutatorElement_def]
  rw [← h, h3]
  rfl

section Aux

variable {T N₁ N₂ A : Subgroup G}

theorem exists_mul_commutator_projSub (hperf : ⁅A, A⁆ = A)
    (hdec : ∀ a ∈ A, ∃ n ∈ N₁, ∃ m ∈ N₂, a = n * m) (hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x)
    (hcomm' : ∀ x ∈ N₂, ∀ y ∈ N₁, x * y = y * x) :
    ∀ a ∈ A, ∃ c ∈ ⁅projSub N₁ N₂ A hcomm, projSub N₁ N₂ A hcomm⁆,
      ∃ d ∈ ⁅projSub N₂ N₁ A hcomm', projSub N₂ N₁ A hcomm'⁆, a = c * d := by
  have hcomm'' : ∀ x ∈ ⁅projSub N₁ N₂ A hcomm, projSub N₁ N₂ A hcomm⁆,
      ∀ y ∈ ⁅projSub N₂ N₁ A hcomm', projSub N₂ N₁ A hcomm'⁆, x * y = y * x := by
    intro x hx y hy
    have hx' : x ∈ N₁ := projSub_le (Subgroup.commutator_le_of_le (le_refl _) (le_refl _) hx)
    have hy' : y ∈ N₂ := projSub_le (Subgroup.commutator_le_of_le (le_refl _) (le_refl _) hy)
    exact hcomm x hx' y hy'
  have hle : ⁅A, A⁆ ≤ mulSub _ _ hcomm'' := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    obtain ⟨n, hn, m, hm, rfl⟩ := hdec a ha
    obtain ⟨n', hn', m', hm', rfl⟩ := hdec b hb
    refine ⟨⁅n, n'⁆, ?_, ⁅m, m'⁆, ?_, commutatorElement_mul_mul hcomm hn hn' hm hm'⟩
    · exact Subgroup.commutator_mem_commutator ⟨hn, m, hm, ha⟩ ⟨hn', m', hm', hb⟩
    · refine Subgroup.commutator_mem_commutator ⟨hm, n, hn, ?_⟩ ⟨hm', n', hn', ?_⟩
      · rw [← hcomm n hn m hm]; exact ha
      · rw [← hcomm n' hn' m' hm']; exact hb
  intro a ha
  exact hle (by rw [hperf]; exact ha)

theorem exists_eq_mul_of_mem_projSub (hperf : ⁅A, A⁆ = A)
    (hdec : ∀ a ∈ A, ∃ n ∈ N₁, ∃ m ∈ N₂, a = n * m) (hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x)
    (hcomm' : ∀ x ∈ N₂, ∀ y ∈ N₁, x * y = y * x) {x : G} (hx : x ∈ projSub N₁ N₂ A hcomm) :
    ∃ c ∈ ⁅projSub N₁ N₂ A hcomm, projSub N₁ N₂ A hcomm⁆, ∃ z ∈ N₁ ⊓ N₂, x = c * z := by
  obtain ⟨hxN, m, hm, hxm⟩ := hx
  obtain ⟨c, hc, d, hd, hcd⟩ := exists_mul_commutator_projSub hperf hdec hcomm hcomm' (x * m) hxm
  have hcN : c ∈ N₁ := projSub_le (Subgroup.commutator_le_of_le (le_refl _) (le_refl _) hc)
  have hdN : d ∈ N₂ := projSub_le (Subgroup.commutator_le_of_le (le_refl _) (le_refl _) hd)
  have hz : c⁻¹ * x = d * m⁻¹ := by
    calc c⁻¹ * x = c⁻¹ * (x * m) * m⁻¹ := by group
      _ = c⁻¹ * (c * d) * m⁻¹ := by rw [hcd]
      _ = d * m⁻¹ := by group
  refine ⟨c, hc, c⁻¹ * x, ⟨N₁.mul_mem (N₁.inv_mem hcN) hxN, ?_⟩, by group⟩
  rw [hz]
  exact N₂.mul_mem hdN (N₂.inv_mem hm)

theorem commutator_projSub_le_commutator (hperf : ⁅A, A⁆ = A)
    (hdec : ∀ a ∈ A, ∃ n ∈ N₁, ∃ m ∈ N₂, a = n * m) (hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x)
    (hcomm' : ∀ x ∈ N₂, ∀ y ∈ N₁, x * y = y * x) :
    ⁅projSub N₁ N₂ A hcomm, projSub N₁ N₂ A hcomm⁆ ≤
      ⁅⁅projSub N₁ N₂ A hcomm, projSub N₁ N₂ A hcomm⁆,
        ⁅projSub N₁ N₂ A hcomm, projSub N₁ N₂ A hcomm⁆⁆ := by
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  obtain ⟨c₁, hc₁, z₁, hz₁, rfl⟩ := exists_eq_mul_of_mem_projSub hperf hdec hcomm hcomm' hx
  obtain ⟨c₂, hc₂, z₂, hz₂, rfl⟩ := exists_eq_mul_of_mem_projSub hperf hdec hcomm hcomm' hy
  have hc₁N : c₁ ∈ N₁ := projSub_le (Subgroup.commutator_le_of_le (le_refl _) (le_refl _) hc₁)
  have hc₂N : c₂ ∈ N₁ := projSub_le (Subgroup.commutator_le_of_le (le_refl _) (le_refl _) hc₂)
  rw [commutatorElement_mul_mul hcomm hc₁N hc₂N hz₁.2 hz₂.2,
    commutatorElement_eq_one_iff_commute.mpr (hcomm z₁ hz₁.1 z₂ hz₂.2), mul_one]
  exact Subgroup.commutator_mem_commutator hc₁ hc₂

theorem commutator_projSub_le_of_isSubnormal (hN₁ : N₁ ≤ T)
    (hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x)
    (hX : ⁅projSub N₁ N₂ A hcomm, projSub N₁ N₂ A hcomm⁆ ≤
      ⁅⁅projSub N₁ N₂ A hcomm, projSub N₁ N₂ A hcomm⁆,
        ⁅projSub N₁ N₂ A hcomm, projSub N₁ N₂ A hcomm⁆⁆)
    {K : Subgroup G} (hK : IsSubnormal K T) (hAK : A ≤ K) :
    ⁅projSub N₁ N₂ A hcomm, projSub N₁ N₂ A hcomm⁆ ≤ K := by
  induction hK with
  | refl H =>
    exact (Subgroup.commutator_le_of_le (le_refl _) (le_refl _)).trans (projSub_le.trans hN₁)
  | @step H M K' hHM hN hMK ih =>
    have hX0M := ih hN₁ (hAK.trans hHM)
    refine hX.trans ?_
    refine (Subgroup.commutator_mono_left
      (Subgroup.commutator_le_of_le (le_refl _) (le_refl _))).trans ?_
    refine Subgroup.commutator_le.mpr fun n hn x hx => ?_
    obtain ⟨hnN, m, hm, hnm⟩ := hn
    have hxN : x ∈ N₁ := projSub_le (Subgroup.commutator_le_of_le (le_refl _) (le_refl _) hx)
    have hxM : x ∈ M := hX0M hx
    have hnmH : n * m ∈ H := hAK hnm
    have hconj : x * (n * m)⁻¹ * x⁻¹ ∈ H := by
      have := (Subgroup.normal_subgroupOf_iff hHM).mp hN ((n * m)⁻¹) x (H.inv_mem hnmH) hxM
      exact this
    have hmx := hcomm x hxN m hm
    have hcom : ⁅n * m, x⁆ = ⁅n, x⁆ := by
      simp only [commutatorElement_def]
      calc n * m * x * (n * m)⁻¹ * x⁻¹ = n * (m * x) * m⁻¹ * n⁻¹ * x⁻¹ := by group
        _ = n * (x * m) * m⁻¹ * n⁻¹ * x⁻¹ := by rw [← hmx]
        _ = n * x * n⁻¹ * x⁻¹ := by group
    rw [← hcom, commutatorElement_def]
    have : n * m * x * (n * m)⁻¹ * x⁻¹ = (n * m) * (x * (n * m)⁻¹ * x⁻¹) := by group
    rw [this]
    exact H.mul_mem hnmH hconj

theorem exists_perfect_mul_of_isSubnormal_perfect (hN₁ : N₁ ≤ T) (hN₂ : N₂ ≤ T)
    (hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x) (hperf : ⁅A, A⁆ = A)
    (hsub : IsSubnormal A T) (hdec : ∀ a ∈ A, ∃ n ∈ N₁, ∃ m ∈ N₂, a = n * m) :
    ∃ B₁ B₂ : Subgroup G, B₁ ≤ A ⊓ N₁ ∧ B₂ ≤ A ⊓ N₂ ∧ ⁅B₁, B₁⁆ = B₁ ∧ ⁅B₂, B₂⁆ = B₂ ∧
      ∀ a ∈ A, ∃ c ∈ B₁, ∃ d ∈ B₂, a = c * d := by
  have hcomm' : ∀ x ∈ N₂, ∀ y ∈ N₁, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have hdec' : ∀ a ∈ A, ∃ n ∈ N₂, ∃ m ∈ N₁, a = n * m := fun a ha => by
    obtain ⟨n, hn, m, hm, rfl⟩ := hdec a ha
    exact ⟨m, hm, n, hn, hcomm n hn m hm⟩
  have hX₁ := commutator_projSub_le_commutator hperf hdec hcomm hcomm'
  have hX₂ := commutator_projSub_le_commutator hperf hdec' hcomm' hcomm
  have h1 := commutator_projSub_le_of_isSubnormal (T := T) (N₂ := N₂) (A := A) hN₁ hcomm hX₁
    hsub le_rfl
  have h2 := commutator_projSub_le_of_isSubnormal (T := T) (N₁ := N₂) (N₂ := N₁) (A := A) hN₂
    hcomm' hX₂ hsub le_rfl
  refine ⟨⁅projSub N₁ N₂ A hcomm, projSub N₁ N₂ A hcomm⁆,
    ⁅projSub N₂ N₁ A hcomm', projSub N₂ N₁ A hcomm'⁆, ?_, ?_, ?_, ?_,
    exists_mul_commutator_projSub hperf hdec hcomm hcomm'⟩
  · exact fun x hx => ⟨h1 hx, projSub_le (Subgroup.commutator_le_of_le le_rfl le_rfl hx)⟩
  · exact fun x hx => ⟨h2 hx, projSub_le (Subgroup.commutator_le_of_le le_rfl le_rfl hx)⟩
  · exact le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) hX₁
  · exact le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) hX₂

end Aux

theorem exists_orderOf_eq_two_of_isPerfect {B : Type*} [Group B] [Finite B] [Nontrivial B]
    (h : Group.IsPerfect B) : ∃ b : B, orderOf b = 2 := by
  by_cases hev : 2 ∣ Nat.card B
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 2 hev
    exact ⟨b, hb⟩
  · exfalso
    have hodd : Odd (Nat.card B) := Nat.odd_iff.mpr (by omega)
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    exact Group.IsPerfect.not_isSolvable B hsolv

theorem le_of_isSubnormal_perfect_of_uniqueInvolution [Finite G] {T N₁ N₂ A : Subgroup G}
    (hN₁ : N₁ ≤ T) (hN₂ : N₂ ≤ T) (hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x)
    (hdisj : ∀ x ∈ N₁, x ∈ N₂ → x = 1) (hperf : ⁅A, A⁆ = A) (hsub : IsSubnormal A T)
    (hdec : ∀ a ∈ A, ∃ n ∈ N₁, ∃ m ∈ N₂, a = n * m)
    (huniq : ∀ a ∈ A, ∀ b ∈ A, orderOf a = 2 → orderOf b = 2 → a * b = b * a → a = b) {i : G}
    (hiA : i ∈ A) (hi2 : orderOf i = 2) (hi' : ∀ n ∈ N₁, ∀ m ∈ N₂, i = n * m → n = 1) :
    A ≤ N₂ := by
  obtain ⟨B₁, B₂, hB₁, hB₂, hB₁p, hB₂p, hAB⟩ :=
    exists_perfect_mul_of_isSubnormal_perfect hN₁ hN₂ hcomm hperf hsub hdec
  have hiN : i ∈ N₂ := by
    obtain ⟨c, hc, d, hd, hcd⟩ := hAB i hiA
    have hc1 : c = 1 := hi' c (hB₁ hc).2 d (hB₂ hd).2 hcd
    rw [hcd, hc1, one_mul]
    exact (hB₂ hd).2
  have hB₁triv : B₁ = ⊥ := by
    by_contra hne
    have : Nontrivial B₁ := (Subgroup.nontrivial_iff_ne_bot B₁).mpr hne
    have : Group.IsPerfect B₁ := Subgroup.isPerfect_iff.mpr hB₁p
    obtain ⟨b, hb⟩ := exists_orderOf_eq_two_of_isPerfect (B := B₁) inferInstance
    have hbA : (b : G) ∈ A := (hB₁ b.2).1
    have hbN : (b : G) ∈ N₁ := (hB₁ b.2).2
    have hb2 : orderOf (b : G) = 2 := (Subgroup.orderOf_coe b).trans hb
    have hcb : (b : G) * i = i * (b : G) := hcomm _ hbN i hiN
    have hne' : (b : G) ≠ i := by
      intro h
      have h1 : (b : G) = 1 := hdisj _ hbN (h ▸ hiN)
      rw [h1] at hb2
      simp at hb2
    exact hne' (huniq _ hbA i hiA hb2 hi2 hcb)
  intro a ha
  obtain ⟨c, hc, d, hd, rfl⟩ := hAB a ha
  rw [hB₁triv, Subgroup.mem_bot] at hc
  rw [hc, one_mul]
  exact hB₂.trans inf_le_right hd

end CFSG.ClassicalInvolution.ModelFacts

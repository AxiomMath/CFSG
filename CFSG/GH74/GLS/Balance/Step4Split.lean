module

public import CFSG.GH74.GLS.Balance.Step4Basic
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

namespace Step4

variable {X : Type} [Group X]

@[expose] def partSub (A₁ B₁ P : Subgroup X) (hc : ∀ a ∈ A₁, ∀ b ∈ B₁, a * b = b * a) :
    Subgroup X where
  carrier := {a | a ∈ A₁ ∧ ∃ b ∈ B₁, a * b ∈ P}
  mul_mem' := by
    rintro a a' ⟨ha, b, hb, hab⟩ ⟨ha', b', hb', hab'⟩
    refine ⟨mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
    have : a * a' * (b * b') = (a * b) * (a' * b') := by
      calc a * a' * (b * b') = a * (a' * b) * b' := by group
        _ = a * (b * a') * b' := by rw [hc a' ha' b hb]
        _ = (a * b) * (a' * b') := by group
    rw [this]
    exact mul_mem hab hab'
  one_mem' := ⟨one_mem _, 1, one_mem _, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, b, hb, hab⟩
    refine ⟨inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
    have : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
      rw [hc a ha b hb, mul_inv_rev]
    rw [this]
    exact inv_mem hab

variable {x : X} {V : Subgroup X}

structure SplitHyp (A : SolvAPI x V) (A₁ B₁ Z : Subgroup X) : Prop where
  comm : ∀ a ∈ A₁, ∀ b ∈ B₁, a * b = b * a
  inf_le : A₁ ⊓ B₁ ≤ Z
  wA : A.w ∈ normalizer (A₁ : Set X)
  wB : A.w ∈ normalizer (B₁ : Set X)
  xA : x ∈ normalizer (A₁ : Set X)
  xB : x ∈ normalizer (B₁ : Set X)
  P_le : A.P ≤ A₁ ⊔ B₁
  Z_two : IsPGroup 2 Z
  Z_w : ⁅Z, zpowers A.w⁆ = ⊥

namespace SplitHyp

variable {A : SolvAPI x V} {A₁ B₁ Z : Subgroup X}

theorem symm (H : SplitHyp A A₁ B₁ Z) : SplitHyp A B₁ A₁ Z where
  comm b hb a ha := (H.comm a ha b hb).symm
  inf_le := by rw [inf_comm]; exact H.inf_le
  wA := H.wB
  wB := H.wA
  xA := H.xB
  xB := H.xA
  P_le := by rw [sup_comm]; exact H.P_le
  Z_two := H.Z_two
  Z_w := H.Z_w

@[expose] def part (H : SplitHyp A A₁ B₁ Z) : Subgroup X := partSub A₁ B₁ A.P H.comm

theorem part_le (H : SplitHyp A A₁ B₁ Z) : H.part ≤ A₁ := fun _ ha => ha.1

theorem part_isPGroup (H : SplitHyp A A₁ B₁ Z) : IsPGroup 2 H.part := by
  refine isPGroup_of_forall_mem fun a ha => ?_
  obtain ⟨haA, b, hb, hab⟩ := ha
  obtain ⟨m, hm⟩ := exists_pow_eq_one_of_mem A.P_two hab
  have hc : Commute a b := H.comm a haA b hb
  rw [hc.mul_pow] at hm
  have h1 : a ^ (2 ^ m) ∈ A₁ ⊓ B₁ := by
    refine ⟨A₁.pow_mem haA _, ?_⟩
    have : a ^ (2 ^ m) = (b ^ (2 ^ m))⁻¹ := eq_inv_of_mul_eq_one_left hm
    rw [this]
    exact B₁.inv_mem (B₁.pow_mem hb _)
  obtain ⟨j, hj⟩ := exists_pow_eq_one_of_mem H.Z_two (H.inf_le h1)
  exact ⟨m + j, by rw [pow_add, pow_mul]; exact hj⟩

theorem part_conj_mem (H : SplitHyp A A₁ B₁ Z) {g : X} (hgA : g ∈ normalizer (A₁ : Set X))
    (hgB : g ∈ normalizer (B₁ : Set X)) (hgP : g ∈ normalizer (A.P : Set X)) {a : X}
    (ha : a ∈ H.part) : g * a * g⁻¹ ∈ H.part := by
  obtain ⟨haA, b, hb, hab⟩ := ha
  refine ⟨(mem_normalizer_iff.mp hgA a).mp haA, g * b * g⁻¹,
    (mem_normalizer_iff.mp hgB b).mp hb, ?_⟩
  have : g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
  rw [this]
  exact (mem_normalizer_iff.mp hgP _).mp hab

theorem w_mem_normalizer_part (H : SplitHyp A A₁ B₁ Z) : A.w ∈ normalizer (H.part : Set X) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · exact fun hh => H.part_conj_mem H.wA H.wB A.w_norm hh
  · intro hh
    have := H.part_conj_mem (inv_mem H.wA) (inv_mem H.wB) (inv_mem A.w_norm) hh
    simpa [mul_assoc] using this

theorem commutator_mem (H : SplitHyp A A₁ B₁ Z) {g : X} (hg : g ∈ zpowers x) {a : X}
    (ha : a ∈ H.part) : ⁅g, a⁆ ∈ Z := by
  obtain ⟨haA, b, hb, hab⟩ := ha
  have hgA : g ∈ normalizer (A₁ : Set X) := Subgroup.zpowers_le.mpr H.xA hg
  have hgB : g ∈ normalizer (B₁ : Set X) := Subgroup.zpowers_le.mpr H.xB hg
  have hgP : g ∈ centralizer (A.P : Set X) := Subgroup.zpowers_le.mpr A.x_mem_centralizer_P hg
  have hg' : Commute g (a * b) := (mem_centralizer_iff.mp hgP _ hab).symm
  have hy : b * (g * b⁻¹ * g⁻¹) ∈ B₁ :=
    mul_mem hb ((mem_normalizer_iff.mp hgB b⁻¹).mp (inv_mem hb))
  have hay : Commute a (b * (g * b⁻¹ * g⁻¹)) := H.comm a haA _ hy
  have e1 : g * a * g⁻¹ = a * b * (g * b⁻¹ * g⁻¹) := by
    calc g * a * g⁻¹ = (g * (a * b) * g⁻¹) * (g * b⁻¹ * g⁻¹) := by group
      _ = a * b * (g * b⁻¹ * g⁻¹) := by rw [hg'.mul_inv_cancel]
  have e2 : ⁅g, a⁆ = b * (g * b⁻¹ * g⁻¹) := by
    rw [commutatorElement_def]
    calc g * a * g⁻¹ * a⁻¹ = (a * (b * (g * b⁻¹ * g⁻¹)) * a⁻¹) := by rw [e1]; group
      _ = b * (g * b⁻¹ * g⁻¹) := hay.mul_inv_cancel
  have h1 : ⁅g, a⁆ ∈ A₁ := by
    rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.mp hgA a).mp haA) (inv_mem haA)
  have h2 : ⁅g, a⁆ ∈ B₁ := by rw [e2]; exact hy
  exact H.inf_le ⟨h1, h2⟩

theorem commutator_zpowers_eq_bot {a b : X} (h : a * b = b * a) :
    ⁅zpowers a, zpowers b⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le, mem_centralizer_iff]
  intro g hg
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  exact ((show Commute a b from h).zpow_right n).symm.eq

theorem part_commutator_x (H : SplitHyp A A₁ B₁ Z) :
    ⁅⁅H.part, zpowers A.w⁆, zpowers x⁆ = ⊥ := by
  apply Subgroup.commutator_commutator_eq_bot_of_rotate
  · rw [commutator_zpowers_eq_bot A.w_mul_x, Subgroup.commutator_bot_left]
  · refine le_bot_iff.mp ?_
    calc ⁅⁅zpowers x, H.part⁆, zpowers A.w⁆ ≤ ⁅Z, zpowers A.w⁆ :=
          Subgroup.commutator_mono (Subgroup.commutator_le.mpr fun g hg a ha =>
            H.commutator_mem hg ha) le_rfl
      _ = ⊥ := H.Z_w

theorem U_le_part (H : SplitHyp A A₁ B₁ Z) : ⁅H.part, zpowers A.w⁆ ≤ H.part :=
  commutator_le_of_le_normalizer (Subgroup.zpowers_le.mpr H.w_mem_normalizer_part)

theorem U_le_centralizer (H : SplitHyp A A₁ B₁ Z) :
    ⁅H.part, zpowers A.w⁆ ≤ centralizer ({x} : Set X) := by
  have h := H.part_commutator_x
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  exact h.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers x)))

theorem U_isPGroup (H : SplitHyp A A₁ B₁ Z) : IsPGroup 2 (⁅H.part, zpowers A.w⁆ : Subgroup X) :=
  isPGroup_of_forall_mem fun _ hg => exists_pow_eq_one_of_mem H.part_isPGroup (H.U_le_part hg)

theorem w_mem_normalizer_U (H : SplitHyp A A₁ B₁ Z) :
    A.w ∈ normalizer ((⁅H.part, zpowers A.w⁆ : Subgroup X) : Set X) :=
  SignalizerFunctor.Helpers.normalized_commutator_normalized (zpowers A.w) H.part
    (Subgroup.zpowers_le.mpr H.w_mem_normalizer_part) (Subgroup.mem_zpowers A.w)

theorem U_idempotent [Finite X] (H : SplitHyp A A₁ B₁ Z) :
    ⁅⁅H.part, zpowers A.w⁆, zpowers A.w⁆ = ⁅H.part, zpowers A.w⁆ := by
  obtain ⟨k, hk⟩ := A.w_three
  have hp3 : IsPGroup 3 (zpowers A.w) := IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := H.part_isPGroup.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card H.part) := by
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  exact SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 3 Nat.prime_three
    (zpowers A.w) H.part hp3 (Subgroup.zpowers_le.mpr H.w_mem_normalizer_part) hcop

theorem P_le_of_U_eq_bot (H : SplitHyp A A₁ B₁ Z) (h : ⁅H.part, zpowers A.w⁆ = ⊥) :
    A.P ≤ B₁ := by
  rw [← A.P_comm, Subgroup.commutator_le]
  intro p hp g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute H.comm (H.P_le hp)
  have hap : a ∈ H.part := ⟨ha, b, hb, hp⟩
  have hag : Commute a g :=
    (mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hap) g hg).symm
  have hab : Commute a b := H.comm a ha b hb
  have hgB : g ∈ normalizer (B₁ : Set X) := Subgroup.zpowers_le.mpr H.wB hg
  have hcz : Commute a (b * g * b⁻¹) := (hab.mul_right hag).mul_right hab.inv_right
  have e : ⁅a * b, g⁆ = b * (g * b⁻¹ * g⁻¹) := by
    rw [commutatorElement_def]
    calc a * b * g * (a * b)⁻¹ * g⁻¹ = (a * (b * g * b⁻¹) * a⁻¹) * g⁻¹ := by group
      _ = b * (g * b⁻¹ * g⁻¹) := by rw [hcz.mul_inv_cancel]; group
  rw [e]
  exact mul_mem hb ((mem_normalizer_iff.mp hgB b⁻¹).mp (inv_mem hb))

theorem U_ne_bot (H : SplitHyp A A₁ B₁ Z) [Finite X] (h : ⁅H.part, zpowers A.w⁆ ≠ ⊥) :
    ⁅H.part, zpowers A.w⁆ ≤ V ∧ Nat.card (⁅H.part, zpowers A.w⁆ : Subgroup X) = Nat.card A.P ∧
      ∃ a ∈ ⁅H.part, zpowers A.w⁆, ∃ b ∈ ⁅H.part, zpowers A.w⁆, a * b ≠ b * a :=
  A.T_le _ H.U_le_centralizer H.U_isPGroup H.w_mem_normalizer_U H.U_idempotent h

end SplitHyp

theorem split_lemma [Finite X] {A : SolvAPI x V} {A₁ B₁ Z : Subgroup X} (H : SplitHyp A A₁ B₁ Z)
    (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) : A.P ≤ A₁ ∨ A.P ≤ B₁ := by
  by_contra hcon
  obtain ⟨hPA, hPB⟩ := not_or.mp hcon
  have hUA : ⁅H.part, zpowers A.w⁆ ≠ ⊥ := fun h => hPB (H.P_le_of_U_eq_bot h)
  have hUB : ⁅H.symm.part, zpowers A.w⁆ ≠ ⊥ := fun h => hPA (H.symm.P_le_of_U_eq_bot h)
  obtain ⟨hAV, hAcard, -⟩ := H.U_ne_bot hUA
  obtain ⟨hBV, -, a₀, ha₀, b₀, hb₀, hnc⟩ := H.symm.U_ne_bot hUB
  have hUAle : ⁅H.part, zpowers A.w⁆ ≤ A₁ := H.U_le_part.trans H.part_le
  have hUBle : ⁅H.symm.part, zpowers A.w⁆ ≤ B₁ := H.symm.U_le_part.trans H.symm.part_le
  have hcomm : ∀ a ∈ ⁅H.part, zpowers A.w⁆, ∀ b ∈ ⁅H.symm.part, zpowers A.w⁆, a * b = b * a :=
    fun a ha b hb => H.comm a (hUAle ha) b (hUBle hb)
  have hsup2 : IsPGroup 2 (⁅H.part, zpowers A.w⁆ ⊔ ⁅H.symm.part, zpowers A.w⁆ : Subgroup X) := by
    refine isPGroup_of_forall_mem fun g hg => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hcomm hg
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem H.U_isPGroup ha
    obtain ⟨l, hl⟩ := exists_pow_eq_one_of_mem H.symm.U_isPGroup hb
    refine ⟨k + l, ?_⟩
    have hx' : a ^ (2 ^ (k + l)) = 1 := by rw [pow_add, pow_mul, hk, one_pow]
    have hy' : b ^ (2 ^ (k + l)) = 1 := by rw [pow_add, mul_comm, pow_mul, hl, one_pow]
    rw [(show Commute a b from hcomm a ha b hb).mul_pow, hx', hy', one_mul]
  have hle : Nat.card (⁅H.part, zpowers A.w⁆ ⊔ ⁅H.symm.part, zpowers A.w⁆ : Subgroup X) ≤
      Nat.card A.P := A.P_sylow _ (sup_le hAV hBV) hsup2
  have heq : ⁅H.part, zpowers A.w⁆ = ⁅H.part, zpowers A.w⁆ ⊔ ⁅H.symm.part, zpowers A.w⁆ :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (hAcard ▸ hle)
  have hBA : ⁅H.symm.part, zpowers A.w⁆ ≤ ⁅H.part, zpowers A.w⁆ := heq ▸ le_sup_right
  have hBZ : ⁅H.symm.part, zpowers A.w⁆ ≤ Z := fun g hg => H.inf_le ⟨hUAle (hBA hg), hUBle hg⟩
  exact hnc (hZc a₀ (hBZ ha₀) b₀ (hBZ hb₀))

end Step4

end CFSG.GH74.GLS.Balance

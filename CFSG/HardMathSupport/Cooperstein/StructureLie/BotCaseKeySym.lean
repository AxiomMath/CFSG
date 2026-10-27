module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLHeart
import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesSym
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
public import Std.Tactic.BVDecide.Normalize.Prop

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.ComponentClassification.OutcomeLocal Module Equiv

namespace BotCaseKeySym

theorem exists_pair_of_mem {α : Type*} [DecidableEq α] {s : Finset α} (hs : s.card = 2) {a : α}
    (ha : a ∈ s) : ∃ b, b ≠ a ∧ s = {a, b} := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact ⟨y, hxy.symm, rfl⟩
  · exact ⟨x, hxy, Finset.pair_comm _ _⟩

theorem exists_common_point {α : Type*} [DecidableEq α] (T : Finset (Finset α))
    (h2 : ∀ s ∈ T, s.card = 2) (hmeet : ∀ s ∈ T, ∀ t ∈ T, (s ∩ t).Nonempty)
    (hcard : 4 ≤ T.card) : ∃ v, ∀ s ∈ T, v ∈ s := by
  obtain ⟨A, hA⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨B, hB, hAB⟩ : ∃ B ∈ T, B ≠ A := by
    by_contra! h
    have h1 : T ⊆ {A} := fun s hs => by simpa using h s hs
    have := Finset.card_le_card h1
    simp only [Finset.card_singleton] at this
    omega
  obtain ⟨a, ha⟩ := hmeet A hA B hB
  rw [Finset.mem_inter] at ha
  obtain ⟨b, hba, rfl⟩ := exists_pair_of_mem (h2 A hA) ha.1
  obtain ⟨c, hca, rfl⟩ := exists_pair_of_mem (h2 B hB) ha.2
  have hbc : b ≠ c := by rintro rfl; exact hAB rfl
  have claim1 : ∀ D ∈ T, D ≠ {a, b} → D ≠ {a, c} → a ∈ D ∨ D = {b, c} := by
    intro D hD hDA hDB
    by_cases haD : a ∈ D
    · exact Or.inl haD
    right
    obtain ⟨x, hx⟩ := hmeet D hD _ hB
    obtain ⟨y, hy⟩ := hmeet D hD _ hA
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx hy
    have hcD : c ∈ D := by
      obtain ⟨hxD, h | h⟩ := hx
      · rw [h] at hxD; exact absurd hxD haD
      · rw [h] at hxD; exact hxD
    have hbD : b ∈ D := by
      obtain ⟨hyD, h | h⟩ := hy
      · rw [h] at hyD; exact absurd hyD haD
      · rw [h] at hyD; exact hyD
    refine (Finset.eq_of_subset_of_card_le (s := {b, c}) (t := D) ?_ ?_).symm
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · rw [Finset.card_pair hbc, h2 D hD]
  obtain ⟨D0, hD0, hD0A, hD0B, hD0C⟩ : ∃ D ∈ T, D ≠ {a, b} ∧ D ≠ {a, c} ∧ D ≠ {b, c} := by
    by_contra! h
    have h1 : T ⊆ {{a, b}, {a, c}, {b, c}} := by
      intro D hD
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hn
      simp only [not_or] at hn
      exact hn.2.2 (h D hD hn.1 hn.2.1)
    have := Finset.card_le_card h1
    have h3 : ({{a, b}, {a, c}, {b, c}} : Finset (Finset α)).card ≤ 3 := Finset.card_le_three
    omega
  rcases claim1 D0 hD0 hD0A hD0B with haD0 | h
  swap
  · exact absurd h hD0C
  obtain ⟨d, hda, rfl⟩ := exists_pair_of_mem (h2 D0 hD0) haD0
  refine ⟨a, fun E hE => ?_⟩
  by_contra haE
  have hEA : E ≠ {a, b} := by rintro rfl; exact haE (by simp)
  have hEB : E ≠ {a, c} := by rintro rfl; exact haE (by simp)
  rcases claim1 E hE hEA hEB with h | h
  · exact haE h
  obtain ⟨z, hz⟩ := hmeet E hE _ hD0
  rw [h] at hz
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hz
  obtain ⟨hz1, hz2⟩ := hz
  rcases hz2 with rfl | rfl
  · rcases hz1 with rfl | rfl
    · exact hba rfl
    · exact hca rfl
  · rcases hz1 with rfl | rfl
    · exact hD0A rfl
    · exact hD0B rfl

theorem whitney_core {m : ℕ} (hm : 5 ≤ m) (ψ : Fin m → Fin m → Finset (Fin m))
    (hcard : ∀ i j, i ≠ j → (ψ i j).card = 2)
    (hsymm : ∀ i j, ψ i j = ψ j i)
    (hinj : ∀ i j k l, i ≠ j → k ≠ l → ψ i j = ψ k l → (i = k ∧ j = l) ∨ (i = l ∧ j = k))
    (hmeet : ∀ i j k l, i ≠ j → k ≠ l →
      ((∃ v, (v = i ∨ v = j) ∧ (v = k ∨ v = l)) ↔ (ψ i j ∩ ψ k l).Nonempty)) :
    ∃ σ : Equiv.Perm (Fin m), ∀ i j, i ≠ j → ψ i j = {σ i, σ j} := by
  have hstar : ∀ i, ∃ v, ∀ j, j ≠ i → v ∈ ψ i j := by
    intro i
    have hinjOn : Set.InjOn (ψ i) (Finset.univ.erase i : Finset (Fin m)) := by
      intro j hj k hk hjk
      simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
        Set.mem_singleton_iff, true_and] at hj hk
      rcases hinj i j i k (Ne.symm hj) (Ne.symm hk) hjk with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h.symm hk
    obtain ⟨v, hv⟩ := exists_common_point ((Finset.univ.erase i).image (ψ i))
      (by
        intro s hs
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
        exact hcard i j (Ne.symm (Finset.ne_of_mem_erase hj)))
      (by
        intro s hs t ht
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
        exact (hmeet i j i k (Ne.symm (Finset.ne_of_mem_erase hj))
          (Ne.symm (Finset.ne_of_mem_erase hk))).mp ⟨i, Or.inl rfl, Or.inl rfl⟩)
      (by
        rw [Finset.card_image_of_injOn hinjOn, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, Fintype.card_fin]
        omega)
    exact ⟨v, fun j hj => hv _ (Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩, rfl⟩)⟩
  choose σ hσ using hstar
  have hσinj : Function.Injective σ := by
    intro i j hij
    by_contra hne
    have hcard' : ({i, j} : Finset (Fin m)).card < m := by
      refine lt_of_le_of_lt Finset.card_le_two (by omega)
    obtain ⟨k, hk⟩ : ∃ k, k ∉ ({i, j} : Finset (Fin m)) := by
      obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({i, j} : Finset (Fin m)))
        (t := Finset.univ) (by rwa [Finset.card_univ, Fintype.card_fin])
      exact ⟨l, hl⟩
    obtain ⟨l, hl⟩ : ∃ l, l ∉ ({i, j, k} : Finset (Fin m)) := by
      obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := ({i, j, k} : Finset (Fin m))) (t := Finset.univ)
        (by rw [Finset.card_univ, Fintype.card_fin]; exact lt_of_le_of_lt Finset.card_le_three (by omega))
      exact ⟨l, hl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk hl
    obtain ⟨hki, hkj⟩ := hk
    obtain ⟨hli, hlj, hlk⟩ := hl
    have h1 : σ i ∈ ψ i k := hσ i k hki
    have h2 : σ j ∈ ψ j l := hσ j l hlj
    have hdisj : ¬ ∃ v, (v = i ∨ v = k) ∧ (v = j ∨ v = l) := by
      rintro ⟨v, hv1, hv2⟩
      rcases hv1 with rfl | rfl <;> rcases hv2 with rfl | rfl
      · exact hne rfl
      · exact hli rfl
      · exact hkj rfl
      · exact hlk rfl
    apply hdisj
    rw [hmeet i k j l (Ne.symm hki) (Ne.symm hlj)]
    exact ⟨σ i, Finset.mem_inter.mpr ⟨h1, by rw [hij]; exact h2⟩⟩
  refine ⟨Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hσinj), fun i j hij => ?_⟩
  have h1 : σ i ∈ ψ i j := hσ i j (Ne.symm hij)
  have h2 : σ j ∈ ψ i j := by rw [hsymm]; exact hσ j i hij
  have hne : σ i ≠ σ j := fun h => hij (hσinj h)
  refine (Finset.eq_of_subset_of_card_le (s := {σ i, σ j}) (t := ψ i j) ?_ ?_).symm
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  · rw [Finset.card_pair hne, hcard i j hij]

theorem swap_eq_swap_iff' {α : Type*} [DecidableEq α] {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    swap a b = swap c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have h1 := congrArg (fun e : Perm α => e a) h
    simp only [swap_apply_left] at h1
    by_cases hac : a = c
    · subst hac
      rw [swap_apply_left] at h1
      exact Or.inl ⟨rfl, h1⟩
    by_cases had : a = d
    · subst had
      rw [swap_apply_right] at h1
      exact Or.inr ⟨rfl, h1⟩
    rw [swap_apply_of_ne_of_ne hac had] at h1
    exact absurd h1.symm hab
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact swap_comm _ _

theorem not_commute_swap_swap {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : ¬ Commute (swap a b) (swap a c) := by
  intro h
  have h1 := congrArg (fun e : Perm α => e a) h.eq
  simp only [Perm.mul_apply, swap_apply_left] at h1
  rw [swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)] at h1
  rw [swap_apply_of_ne_of_ne (Ne.symm hab) hbc] at h1
  exact hbc h1.symm

theorem commute_swap_swap_of_disjoint {α : Type*} [DecidableEq α] {a b c d : α}
    (h : ¬ ∃ v, (v = a ∨ v = b) ∧ (v = c ∨ v = d)) : Commute (swap a b) (swap c d) := by
  refine Perm.Disjoint.commute fun x => ?_
  by_cases hx : x = a ∨ x = b
  · right
    refine swap_apply_of_ne_of_ne ?_ ?_
    · rintro rfl; exact h ⟨x, hx, Or.inl rfl⟩
    · rintro rfl; exact h ⟨x, hx, Or.inr rfl⟩
  · left
    push Not at hx
    exact swap_apply_of_ne_of_ne hx.1 hx.2

theorem meet_iff_swap {α : Type*} [DecidableEq α] {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    (∃ v, (v = a ∨ v = b) ∧ (v = c ∨ v = d)) ↔
      (swap a b = swap c d ∨ ¬ Commute (swap a b) (swap c d)) := by
  constructor
  · intro ⟨v, hv1, hv2⟩
    by_cases heq : swap a b = swap c d
    · exact Or.inl heq
    right
    intro hcomm
    rcases hv1 with h1 | h1 <;> rcases hv2 with h2 | h2
    · have hac : a = c := h1.symm.trans h2
      subst hac
      exact not_commute_swap_swap hab hcd (fun h => heq ((swap_eq_swap_iff' hab hcd).mpr (Or.inl ⟨rfl, h⟩))) hcomm
    · have had : a = d := h1.symm.trans h2
      subst had
      rw [swap_comm c a] at hcomm
      exact not_commute_swap_swap hab hcd.symm
        (fun h => heq ((swap_eq_swap_iff' hab hcd).mpr (Or.inr ⟨rfl, h⟩))) hcomm
    · have hbc : b = c := h1.symm.trans h2
      subst hbc
      rw [swap_comm a b] at hcomm
      exact not_commute_swap_swap hab.symm hcd
        (fun h => heq ((swap_eq_swap_iff' hab hcd).mpr (Or.inr ⟨h, rfl⟩))) hcomm
    · have hbd : b = d := h1.symm.trans h2
      subst hbd
      rw [swap_comm a b, swap_comm c b] at hcomm
      exact not_commute_swap_swap hab.symm hcd.symm
        (fun h => heq ((swap_eq_swap_iff' hab hcd).mpr (Or.inl ⟨h, rfl⟩))) hcomm
  · intro h
    by_contra hn
    rcases h with h | h
    · rw [swap_eq_swap_iff' hab hcd] at h
      rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hn ⟨a, Or.inl rfl, Or.inl rfl⟩
      · exact hn ⟨a, Or.inl rfl, Or.inr rfl⟩
    · exact h (commute_swap_swap_of_disjoint hn)

theorem finset_pair_eq_pair_iff {α : Type*} [DecidableEq α] {x y z w : α} :
    ({x, y} : Finset α) = {z, w} ↔ (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  rw [← Finset.coe_inj]
  simp [Set.pair_eq_pair_iff]

section
variable {m : ℕ}
theorem mem_sum_pairVec (i₀ : Fin m) (x : sumZero m) :
    x = ∑ i, (x : Fin m → ZMod 2) i • pairVec i i₀ := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  funext p
  simp only [Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coe_pairVec,
    Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  have h1 : ∑ l, (x : Fin m → ZMod 2) l = 0 := x.2
  rw [h1, zero_mul, add_zero]
  simp [Pi.single_apply]
end

section
variable {m : ℕ}

def dvec (π : Perm (Fin m)) (i : Fin m) : Fin m → ZMod 2 := Pi.single i 1 + Pi.single (π i) 1

theorem dvec_apply (π : Perm (Fin m)) (i l : Fin m) :
    dvec π i l = (if l = i then 1 else 0) + (if l = π i then 1 else 0) := by
  simp [dvec, Pi.single_apply]

theorem dvec_self_of_moved {π : Perm (Fin m)} {i : Fin m} (h : π i ≠ i) : dvec π i i = 1 := by
  rw [dvec_apply]; simp [Ne.symm h]

theorem dvec_fixed {π : Perm (Fin m)} {k : Fin m} (h : π k = k) : dvec π k = 0 := by
  funext l
  rw [dvec_apply, h]
  simp only [Pi.zero_apply]
  split_ifs <;> decide

theorem dvec_ne_of_moved {π : Perm (Fin m)} {i l : Fin m} (hl : π l ≠ l) (hli : l ≠ i)
    (hlπ : l ≠ π i) : dvec π l ≠ dvec π i := by
  intro h
  have h1 := congrFun h l
  rw [dvec_self_of_moved hl, dvec_apply] at h1
  simp [hli, hlπ] at h1

theorem exists_notMem_card_lt (s : Finset (Fin m)) (hs : s.card < m) : ∃ l, l ∉ s := by
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := s) (t := Finset.univ)
    (by rwa [Finset.card_univ, Fintype.card_fin])
  exact ⟨l, hl⟩

theorem exists_three_dvec (hm : 5 ≤ m) (π : Perm (Fin m)) (h1 : π ≠ 1) (h2 : ¬ π.IsSwap) :
    ∃ i j k, dvec π i ≠ dvec π j ∧ dvec π i ≠ dvec π k ∧ dvec π j ≠ dvec π k := by
  by_cases hfix : ∃ k, π k = k
  · obtain ⟨k, hk⟩ := hfix
    have hsup : 3 ≤ π.support.card := by
      have a1 := Equiv.Perm.card_support_ne_one π
      have a2 : π.support.card ≠ 2 := fun h => h2 (Equiv.Perm.card_support_eq_two.mp h)
      have a3 : π.support.card ≠ 0 := fun h => h1 (Equiv.Perm.support_eq_empty_iff.mp
        (Finset.card_eq_zero.mp h))
      omega
    obtain ⟨i, hi⟩ : π.support.Nonempty := Finset.card_pos.mp (by omega)
    rw [Equiv.Perm.mem_support] at hi
    obtain ⟨j, hj, hjn⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({i, π i} : Finset (Fin m))) (t := π.support)
      (lt_of_le_of_lt Finset.card_le_two (by omega))
    rw [Equiv.Perm.mem_support] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hjn
    refine ⟨i, j, k, (dvec_ne_of_moved hj hjn.1 hjn.2).symm, ?_, ?_⟩
    · rw [dvec_fixed hk]
      intro h
      have := congrFun h i
      rw [dvec_self_of_moved hi] at this
      exact one_ne_zero this
    · rw [dvec_fixed hk]
      intro h
      have := congrFun h j
      rw [dvec_self_of_moved hj] at this
      exact one_ne_zero this
  · push Not at hfix
    obtain ⟨i⟩ : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    obtain ⟨j, hj⟩ := exists_notMem_card_lt ({i, π i} : Finset (Fin m))
      (lt_of_le_of_lt Finset.card_le_two (by omega))
    obtain ⟨k, hk⟩ := exists_notMem_card_lt ({i, π i, j, π j} : Finset (Fin m))
      (lt_of_le_of_lt Finset.card_le_four (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj hk
    exact ⟨i, j, k, (dvec_ne_of_moved (hfix j) hj.1 hj.2).symm,
      (dvec_ne_of_moved (hfix k) hk.1 hk.2.1).symm,
      (dvec_ne_of_moved (hfix k) hk.2.2.1 hk.2.2.2).symm⟩

theorem dvec_eq_of_const (hm : 5 ≤ m) (π : Perm (Fin m)) (x y : Fin m)
    (h : ∃ c : ZMod 2, dvec π x + dvec π y = fun _ => c) : dvec π x = dvec π y := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨l, hl⟩ := exists_notMem_card_lt ({x, π x, y, π y} : Finset (Fin m))
    (lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
  have h0 : c = 0 := by
    have := congrFun hc l
    simp only [Pi.add_apply, dvec_apply] at this
    simp [hl.1, hl.2.1, hl.2.2.1, hl.2.2.2] at this
    exact this.symm
  subst h0
  funext l'
  have := congrFun hc l'
  simp only [Pi.add_apply] at this
  generalize dvec π x l' = a at this ⊢
  generalize dvec π y l' = b at this ⊢
  revert a b; decide
end

structure SymHeartData (m : ℕ) (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] where
  q : sumZero m →ₗ[ZMod 2] V
  ρ : Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) V
  q_surj : Function.Surjective q
  ρ_q : ∀ (σ : Perm (Fin m)) (x : sumZero m),
    (ρ σ : V →ₗ[ZMod 2] V) (q x) = q (sumZeroEquiv σ x)
  ker_q : ∀ x, q x = 0 → ∃ c : ZMod 2, (x : Fin m → ZMod 2) = fun _ => c

namespace SymHeartData

variable {m : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (D : SymHeartData m V)

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by revert c; decide

theorem zmod2_aux1 : ∀ a b c d : ZMod 2, c + d - (a + b) = a + c + (b + d) := by decide

theorem zmod2_aux2 : ∀ a b c : ZMod 2, a + c = a + b + (b + c) := by decide

theorem permCoord_single (π : Perm (Fin m)) (x : Fin m) :
    permCoord π (Pi.single x (1 : ZMod 2)) = Pi.single (π x) 1 := by
  funext l
  rw [permCoord_apply, Pi.single_apply, Pi.single_apply]
  simp [Equiv.symm_apply_eq]

theorem coe_uu (π : Perm (Fin m)) (x y : Fin m) :
    ((sumZeroEquiv π (pairVec x y) - pairVec x y : sumZero m) : Fin m → ZMod 2) =
      dvec π x + dvec π y := by
  rw [Submodule.coe_sub, coe_sumZeroEquiv, coe_pairVec, map_add, permCoord_single,
    permCoord_single]
  funext l
  simp only [dvec, Pi.sub_apply, Pi.add_apply]
  generalize (Pi.single x (1 : ZMod 2) : Fin m → ZMod 2) l = a
  generalize (Pi.single y (1 : ZMod 2) : Fin m → ZMod 2) l = b
  generalize (Pi.single (π x) (1 : ZMod 2) : Fin m → ZMod 2) l = c
  generalize (Pi.single (π y) (1 : ZMod 2) : Fin m → ZMod 2) l = d
  exact zmod2_aux1 a b c d

theorem pairVec_add (i j k : Fin m) : pairVec i k = pairVec i j + pairVec j k := by
  apply Subtype.ext
  funext l
  simp only [coe_pairVec, Submodule.coe_add, Pi.add_apply]
  generalize (Pi.single i (1 : ZMod 2) : Fin m → ZMod 2) l = a
  generalize (Pi.single j (1 : ZMod 2) : Fin m → ZMod 2) l = b
  generalize (Pi.single k (1 : ZMod 2) : Fin m → ZMod 2) l = c
  exact zmod2_aux2 a b c

theorem ρ_swap_apply (i j : Fin m) (x : sumZero m) :
    (D.ρ (swap i j) : V →ₗ[ZMod 2] V) (D.q x) =
      D.q x + ((x : Fin m → ZMod 2) i + (x : Fin m → ZMod 2) j) • D.q (pairVec i j) := by
  rw [D.ρ_q, ← map_smul, ← map_add]
  congr 1
  apply Subtype.ext
  rw [coe_sumZeroEquiv, permCoord_swap]
  rfl

theorem ρ_injective (hm : 5 ≤ m) : Function.Injective D.ρ := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  by_contra hne
  obtain ⟨i, k, hik⟩ := CFSG.HardMathSupport.Solomon.Coordinator.mclt_permCoord_pairVec_sub_ne_const hm hne
  obtain ⟨c, hc⟩ := D.ker_q (sumZeroEquiv σ (pairVec i k) - pairVec i k) (by
    rw [map_sub, ← D.ρ_q, hσ]
    simp)
  rw [Submodule.coe_sub, coe_sumZeroEquiv] at hc
  exact hik c hc

theorem isSwap_of_tv (hm : 5 ≤ m) (π : Perm (Fin m)) (h1 : π ≠ 1)
    (a : V) (ha : ∀ x : V, ∃ c : ZMod 2, (D.ρ π : V →ₗ[ZMod 2] V) x = x + c • a) :
    π.IsSwap := by
  by_contra hs
  obtain ⟨i, j, k, hij, hik, hjk⟩ := exists_three_dvec hm π h1 hs
  have key : ∀ x y : Fin m, dvec π x ≠ dvec π y →
      D.q (sumZeroEquiv π (pairVec x y) - pairVec x y) = a ∧
        D.q (sumZeroEquiv π (pairVec x y) - pairVec x y) ≠ 0 := by
    intro x y hxy
    obtain ⟨c, hc⟩ := ha (D.q (pairVec x y))
    rw [D.ρ_q] at hc
    have h2 : D.q (sumZeroEquiv π (pairVec x y) - pairVec x y) = c • a := by
      rw [map_sub, hc]; abel
    have hne : D.q (sumZeroEquiv π (pairVec x y) - pairVec x y) ≠ 0 := by
      intro h0
      apply hxy
      apply dvec_eq_of_const hm π x y
      obtain ⟨c', hc'⟩ := D.ker_q _ h0
      rw [coe_uu] at hc'
      exact ⟨c', hc'⟩
    refine ⟨?_, hne⟩
    rw [h2] at hne ⊢
    rcases zmod2_cases c with rfl | rfl
    · exact absurd (zero_smul _ _) hne
    · exact one_smul _ _
  obtain ⟨e1, n1⟩ := key i j hij
  obtain ⟨e2, -⟩ := key j k hjk
  obtain ⟨e3, -⟩ := key i k hik
  have hsum : sumZeroEquiv π (pairVec i k) - pairVec i k =
      (sumZeroEquiv π (pairVec i j) - pairVec i j) + (sumZeroEquiv π (pairVec j k) - pairVec j k) := by
    rw [pairVec_add i j k, map_add]; abel
  rw [hsum, map_add, e1, e2] at e3
  have h11 : (1 + 1 : ZMod 2) = 0 := by decide
  have : a + a = 0 := by
    calc a + a = (1 : ZMod 2) • a + (1 : ZMod 2) • a := by rw [one_smul]
      _ = ((1 : ZMod 2) + 1) • a := (add_smul _ _ _).symm
      _ = 0 := by rw [h11, zero_smul]
  have ha0 : a = 0 := by rw [this] at e3; exact e3.symm
  exact n1 (e1.trans ha0)

theorem pairVec_self (i : Fin m) : pairVec i i = 0 := by
  apply Subtype.ext
  funext l
  rw [coe_pairVec, Pi.add_apply]
  exact add_self_zmod2 _

theorem sum_pairVec_apply (i₀ : Fin m) (x : sumZero m) :
    D.q x = ∑ i, (x : Fin m → ZMod 2) i • D.q (pairVec i i₀) := by
  conv_lhs => rw [mem_sum_pairVec i₀ x, map_sum]
  simp only [map_smul]

theorem gl_inv_apply (g : LinearMap.GeneralLinearGroup (ZMod 2) V) (x : V) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) ((g : V →ₗ[ZMod 2] V) x) = x := by
  have := congrArg (fun u : V →ₗ[ZMod 2] V => u x) (Units.inv_mul g)
  exact this

theorem gl_apply_inv (g : LinearMap.GeneralLinearGroup (ZMod 2) V) (x : V) :
    (g : V →ₗ[ZMod 2] V) (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) x) = x := by
  have := congrArg (fun u : V →ₗ[ZMod 2] V => u x) (Units.mul_inv g)
  exact this

theorem gl_apply_injective (g : LinearMap.GeneralLinearGroup (ZMod 2) V) {x y : V}
    (h : (g : V →ₗ[ZMod 2] V) x = (g : V →ₗ[ZMod 2] V) y) : x = y := by
  rw [← gl_inv_apply g x, h, gl_inv_apply]

theorem conj_swap_tv (g : LinearMap.GeneralLinearGroup (ZMod 2) V) (i j : Fin m) (x : V) :
    ∃ c : ZMod 2, ((g * D.ρ (swap i j) * g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) x = x + c • (g : V →ₗ[ZMod 2] V) (D.q (pairVec i j)) := by
  obtain ⟨y, hy⟩ := D.q_surj (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) x)
  refine ⟨(y : Fin m → ZMod 2) i + (y : Fin m → ZMod 2) j, ?_⟩
  have h1 := D.ρ_swap_apply i j y
  rw [hy] at h1
  change (g : V →ₗ[ZMod 2] V) ((D.ρ (swap i j) : V →ₗ[ZMod 2] V)
    (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) x)) = _
  rw [h1, map_add, map_smul, gl_apply_inv]

theorem not_commute_iff_ne_one_aux {G : Type*} [Group G] {g a b : G} :
    g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹) ↔ a * b = b * a := by
  constructor
  · intro h
    have : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      simpa [mul_assoc] using h
    simpa using this
  · intro h
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [h]
      _ = _ := by group

theorem fix_of_commute (hm : 5 ≤ m) (h : LinearMap.GeneralLinearGroup (ZMod 2) V) (i j : Fin m)
    (hij : i ≠ j) (hc : h * D.ρ (swap i j) = D.ρ (swap i j) * h) :
    (h : V →ₗ[ZMod 2] V) (D.q (pairVec i j)) = D.q (pairVec i j) := by
  have hρ := D.ρ_injective hm
  obtain ⟨x, hx⟩ : ∃ x : sumZero m, (D.ρ (swap i j) : V →ₗ[ZMod 2] V) (D.q x) ≠ D.q x := by
    by_contra hcon
    push Not at hcon
    apply swap_eq_one_iff.not.mpr hij
    apply hρ
    rw [map_one]
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨y, rfl⟩ := D.q_surj v
    exact hcon y
  have hx' := D.ρ_swap_apply i j x
  set c : ZMod 2 := (x : Fin m → ZMod 2) i + (x : Fin m → ZMod 2) j with hcdef
  have hca : c • D.q (pairVec i j) ≠ 0 := by
    intro h0
    apply hx
    rw [hx', h0, add_zero]
  have hc1 : c = 1 := by
    rcases zmod2_cases c with h0 | h1
    · exact absurd (by rw [h0, zero_smul]) hca
    · exact h1
  rw [hc1, one_smul] at hx'
  have ha0 : D.q (pairVec i j) ≠ 0 := fun h0 => hca (by rw [h0, smul_zero])
  have hcomm : ∀ y : V, (h : V →ₗ[ZMod 2] V) ((D.ρ (swap i j) : V →ₗ[ZMod 2] V) y) =
      (D.ρ (swap i j) : V →ₗ[ZMod 2] V) ((h : V →ₗ[ZMod 2] V) y) := fun y =>
    congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod 2) V => (u : V →ₗ[ZMod 2] V) y) hc
  have e1 := hcomm (D.q x)
  rw [hx', map_add] at e1
  obtain ⟨x', hx''⟩ := D.q_surj ((h : V →ₗ[ZMod 2] V) (D.q x))
  have e2 := D.ρ_swap_apply i j x'
  rw [hx''] at e2
  rw [e2] at e1
  have e3 : (h : V →ₗ[ZMod 2] V) (D.q (pairVec i j)) =
      ((x' : Fin m → ZMod 2) i + (x' : Fin m → ZMod 2) j) • D.q (pairVec i j) := by
    have := e1
    rw [add_comm] at this
    exact add_left_cancel (a := (h : V →ₗ[ZMod 2] V) (D.q x)) (by rw [add_comm]; exact this)
  set c' : ZMod 2 := (x' : Fin m → ZMod 2) i + (x' : Fin m → ZMod 2) j
  rcases zmod2_cases c' with h0 | h1
  · exfalso
    rw [h0, zero_smul] at e3
    apply ha0
    apply gl_apply_injective h
    rw [e3, map_zero]
  · rw [e3, h1, one_smul]

theorem mem_range_of_normalizes (hm : 5 ≤ m) (g : LinearMap.GeneralLinearGroup (ZMod 2) V)
    (hg : ∀ π : Perm (Fin m), g * D.ρ π * g⁻¹ ∈ D.ρ.range) : g ∈ D.ρ.range := by
  classical
  have hρ := D.ρ_injective hm
  have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  choose α hα using hg
  have hαinj : ∀ π π', α π = α π' → π = π' := by
    intro π π' h
    apply hρ
    have := congrArg D.ρ h
    rw [hα, hα] at this
    simpa using this
  have e1 : ∀ x y : Perm (Fin m), x * y = y * x ↔ D.ρ x * D.ρ y = D.ρ y * D.ρ x := fun x y => by
    rw [← map_mul, ← map_mul, hρ.eq_iff]
  have hαcomm : ∀ π π', Commute (α π) (α π') ↔ Commute π π' := by
    intro π π'
    rw [commute_iff_eq, commute_iff_eq, e1, e1 π, hα, hα, not_commute_iff_ne_one_aux]
  have hsw : ∀ i j : Fin m, i ≠ j → ∃ a b : Fin m, a ≠ b ∧ α (swap i j) = swap a b := by
    intro i j hij
    have hne : α (swap i j) ≠ 1 := by
      intro h1
      apply swap_eq_one_iff.not.mpr hij
      apply hρ
      have := hα (swap i j)
      rw [h1, map_one] at this
      rw [map_one]
      simpa using this.symm
    obtain ⟨a, b, hab, h⟩ := D.isSwap_of_tv hm (α (swap i j)) hne
      ((g : V →ₗ[ZMod 2] V) (D.q (pairVec i j))) (fun x => by
        obtain ⟨c, hc⟩ := D.conj_swap_tv g i j x
        rw [← hα] at hc
        exact ⟨c, hc⟩)
    exact ⟨a, b, hab, h⟩
  choose! A B hAB hαAB using hsw
  have hψ := whitney_core (m := m) hm (fun i j => {A i j, B i j})
    (fun i j hij => Finset.card_pair (hAB i j hij))
    (by
      intro i j
      by_cases hij : i = j
      · subst hij; rfl
      · have h1 := hαAB i j hij
        have h2 := hαAB j i (Ne.symm hij)
        rw [swap_comm j i, h1] at h2
        exact finset_pair_eq_pair_iff.mpr
          ((swap_eq_swap_iff' (hAB i j hij) (hAB j i (Ne.symm hij))).mp h2))
    (by
      intro i j k l hij hkl h
      have h1 : swap (A i j) (B i j) = swap (A k l) (B k l) :=
        (swap_eq_swap_iff' (hAB i j hij) (hAB k l hkl)).mpr (finset_pair_eq_pair_iff.mp h)
      rw [← hαAB i j hij, ← hαAB k l hkl] at h1
      exact (swap_eq_swap_iff' hij hkl).mp (hαinj _ _ h1))
    (by
      intro i j k l hij hkl
      rw [meet_iff_swap hij hkl]
      have h1 : (({A i j, B i j} : Finset (Fin m)) ∩ {A k l, B k l}).Nonempty ↔
          ∃ v, (v = A i j ∨ v = B i j) ∧ (v = A k l ∨ v = B k l) := by
        simp [Finset.Nonempty]
      rw [h1, meet_iff_swap (hAB i j hij) (hAB k l hkl), ← hαAB i j hij, ← hαAB k l hkl,
        hαcomm]
      constructor
      · rintro (h | h)
        · exact Or.inl (h ▸ rfl)
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl (hαinj _ _ h)
        · exact Or.inr h)
  obtain ⟨σ, hσ⟩ := hψ
  have hασ : ∀ i j : Fin m, i ≠ j → α (swap i j) = swap (σ i) (σ j) := by
    intro i j hij
    rw [hαAB i j hij]
    have := hσ i j hij
    rcases finset_pair_eq_pair_iff.mp this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, swap_comm]
  have hcomm : ∀ i j : Fin m, i ≠ j →
      ((D.ρ σ)⁻¹ * g) * D.ρ (swap i j) = D.ρ (swap i j) * ((D.ρ σ)⁻¹ * g) := by
    intro i j hij
    have e := hα (swap i j)
    rw [hασ i j hij, swap_apply_apply σ i j, map_mul, map_mul, map_inv] at e
    have e' : g * D.ρ (swap i j) = D.ρ σ * D.ρ (swap i j) * (D.ρ σ)⁻¹ * g := by
      rw [e]; group
    rw [mul_assoc, e']
    group
  have hone : (D.ρ σ)⁻¹ * g = 1 := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨x, rfl⟩ := D.q_surj v
    set h := (D.ρ σ)⁻¹ * g
    have hfix : ∀ i j : Fin m, i ≠ j →
        (h : V →ₗ[ZMod 2] V) (D.q (pairVec i j)) = D.q (pairVec i j) := fun i j hij =>
      D.fix_of_commute hm h i j hij (hcomm i j hij)
    let i₀ : Fin m := ⟨0, by omega⟩
    rw [D.sum_pairVec_apply i₀ x, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul]
    by_cases hl : l = i₀
    · simp [hl, pairVec_self]
    · rw [hfix l i₀ hl]
  have : D.ρ σ = g := inv_mul_eq_one.mp hone
  exact ⟨σ, this⟩

end SymHeartData

section Final

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem SymHeartData.mem_of_normalizer {m : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (D : SymHeartData m V) (hm : 5 ≤ m) (β : W ≃ₗ[ZMod 2] V)
    (H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W))
    (hH : H.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom = D.ρ.range)
    (g : LinearMap.GeneralLinearGroup (ZMod 2) W)
    (hg : g ∈ Subgroup.normalizer (H : Set (LinearMap.GeneralLinearGroup (ZMod 2) W))) :
    g ∈ H := by
  set e := LinearMap.GeneralLinearGroup.congrLinearEquiv β with he
  have h1 : e g ∈ D.ρ.range := by
    refine D.mem_range_of_normalizes hm (e g) fun π => ?_
    have hπ : D.ρ π ∈ H.map e.toMonoidHom := by rw [hH]; exact ⟨π, rfl⟩
    obtain ⟨h, hh, hπh⟩ := hπ
    rw [← hH]
    refine ⟨g * h * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg h).mp hh, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom] at hπh ⊢
    rw [← hπh]
    simp
  rw [← hH] at h1
  obtain ⟨h, hh, hhe⟩ := h1
  have : h = g := e.injective hhe
  rwa [← this]

end Final

noncomputable def sumZeroData (m : ℕ) : SymHeartData m (sumZero m) where
  q := LinearMap.id
  ρ := sumZeroRep m
  q_surj := Function.surjective_id
  ρ_q _ _ := rfl
  ker_q x hx := ⟨0, by rw [LinearMap.id_apply] at hx; rw [hx]; rfl⟩

noncomputable def heartData (m : ℕ) : SymHeartData m (sumZero m ⧸ onesLine m) where
  q := (onesLine m).mkQ
  ρ := heartRep m
  q_surj := Submodule.mkQ_surjective _
  ρ_q σ x := heartRep_apply_mk σ x
  ker_q _ hx := mem_onesLine.mp ((Submodule.Quotient.mk_eq_zero _).mp hx)

end BotCaseKeySym

open BotCaseKeySym in
theorem mem_of_mem_normalizer_sym {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (h4 : 4 ≤ Module.finrank (ZMod 2) W)
    (H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W))
    (hH : (∃ β : W ≃ₗ[ZMod 2] sumZero (Module.finrank (ZMod 2) W + 1),
              H.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
                (sumZeroRep (Module.finrank (ZMod 2) W + 1)).range) ∨
          ∃ β : W ≃ₗ[ZMod 2] sumZero (Module.finrank (ZMod 2) W + 2) ⧸
              onesLine (Module.finrank (ZMod 2) W + 2),
              H.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
                (heartRep (Module.finrank (ZMod 2) W + 2)).range)
    (g : LinearMap.GeneralLinearGroup (ZMod 2) W)
    (hg : g ∈ Subgroup.normalizer (H : Set (LinearMap.GeneralLinearGroup (ZMod 2) W))) :
    g ∈ H := by
  rcases hH with ⟨β, hβ⟩ | ⟨β, hβ⟩
  · exact (sumZeroData (Module.finrank (ZMod 2) W + 1)).mem_of_normalizer (by omega) β H hβ g hg
  · exact (heartData (Module.finrank (ZMod 2) W + 2)).mem_of_normalizer (by omega) β H hβ g hg

end CFSG.HardMathSupport.Cooperstein.StructureLie

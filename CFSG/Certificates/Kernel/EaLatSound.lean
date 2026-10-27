module

public import CFSG.Quasithin.Background.B3Basic
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.EaLat

variable {G : Type*} [Group G] [DecidableEq G]

structure Uni (n : ℕ) (v : ℕ → G) (pr : ℕ → ℕ → ℕ) : Prop where
  inj : ∀ i < n, ∀ j < n, v i = v j → i = j
  ne_one : ∀ i < n, v i ≠ 1
  sq : ∀ i < n, v i * v i = 1
  prod : ∀ i < n, ∀ j < n, i ≠ j → v i * v j = v j * v i → pr i j < n ∧ v (pr i j) = v i * v j

structure Recs (n NF : ℕ) (v : ℕ → G) (pr : ℕ → ℕ → ℕ) (S Cc : ℕ → Finset ℕ)
    (P K Z : ℕ → ℕ) : Prop where
  S0 : S 0 = ∅
  Cc0 : Cc 0 = Finset.range n
  Z0 : Z 0 = 0
  P_lt : ∀ f, 0 < f → f < NF → P f < f
  K_lt : ∀ f, 0 < f → f < NF → K f < n
  K_nmem : ∀ f, 0 < f → f < NF → K f ∉ S (P f)
  K_mem : ∀ f, 0 < f → f < NF → K f ∈ Cc (P f)
  S_eq : ∀ f, 0 < f → f < NF →
    S f = insert (K f) (S (P f) ∪ (S (P f)).image (pr (K f)))
  Cc_eq : ∀ f, 0 < f → f < NF →
    Cc f = (Cc (P f)).filter fun j => v j * v (K f) = v (K f) * v j
  Z_eq : ∀ f, 0 < f → f < NF → Z f = 2 * Z (P f) + 1
  cover : ∀ f < NF, ∀ i ∈ Cc f, i ∉ S f →
    ∃ c < NF, S f ⊆ S c ∧ Z c = 2 * Z f + 1 ∧ i ∈ S c

@[expose] def aSet (v : ℕ → G) (S : Finset ℕ) : Finset G := insert 1 (S.image v)

theorem mem_aSet {v : ℕ → G} {S : Finset ℕ} {x : G} :
    x ∈ aSet v S ↔ x = 1 ∨ ∃ i ∈ S, v i = x := by
  simp [aSet, eq_comm]

structure RecInv (n : ℕ) (v : ℕ → G) (S Cc : Finset ℕ) (z : ℕ) : Prop where
  lt : ∀ i ∈ S, i < n
  mul : ∀ x ∈ aSet v S, ∀ y ∈ aSet v S, x * y ∈ aSet v S
  comm : ∀ x ∈ aSet v S, ∀ y ∈ aSet v S, x * y = y * x
  cc : ∀ j, j ∈ Cc ↔ j < n ∧ ∀ x ∈ aSet v S, v j * x = x * v j
  card : S.card = z

variable {n NF : ℕ} {v : ℕ → G} {pr : ℕ → ℕ → ℕ} {S Cc : ℕ → Finset ℕ} {P K Z : ℕ → ℕ}

theorem sq_of_mem (hu : Uni n v pr) {T : Finset ℕ} (hT : ∀ i ∈ T, i < n) {x : G}
    (hx : x ∈ aSet v T) : x * x = 1 := by
  rcases mem_aSet.1 hx with rfl | ⟨i, hi, rfl⟩
  · exact mul_one 1
  · exact hu.sq i (hT i hi)

theorem recInv_step (hu : Uni n v pr) {Sp Ccp Sf Ccf : Finset ℕ} {zp zf k : ℕ}
    (hp : RecInv n v Sp Ccp zp) (hk : k < n) (hkS : k ∉ Sp) (hkC : k ∈ Ccp)
    (hS : Sf = insert k (Sp ∪ Sp.image (pr k)))
    (hC : Ccf = Ccp.filter fun j => v j * v k = v k * v j) (hz : zf = 2 * zp + 1) :
    RecInv n v Sf Ccf zf := by
  have hcomK : ∀ x ∈ aSet v Sp, v k * x = x * v k := ((hp.cc k).1 hkC).2
  have hpr : ∀ a ∈ Sp, pr k a < n ∧ v (pr k a) = v k * v a := by
    intro a ha
    have han := hp.lt a ha
    refine hu.prod k hk a han (fun h => hkS (h ▸ ha)) ?_
    exact hcomK _ (mem_aSet.2 (Or.inr ⟨a, ha, rfl⟩))
  have hA : ∀ x, x ∈ aSet v Sf ↔ x ∈ aSet v Sp ∨ ∃ y ∈ aSet v Sp, x = v k * y := by
    intro x
    rw [hS, mem_aSet, mem_aSet]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact Or.inl (Or.inl rfl)
      · rcases Finset.mem_insert.1 hi with rfl | hi
        · exact Or.inr ⟨1, mem_aSet.2 (Or.inl rfl), (mul_one _).symm⟩
        rcases Finset.mem_union.1 hi with hi | hi
        · exact Or.inl (Or.inr ⟨i, hi, rfl⟩)
        · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hi
          exact Or.inr ⟨v a, mem_aSet.2 (Or.inr ⟨a, ha, rfl⟩), (hpr a ha).2⟩
    · rintro ((rfl | ⟨i, hi, rfl⟩) | ⟨y, hy, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨i, Finset.mem_insert_of_mem (Finset.mem_union_left _ hi), rfl⟩
      · rcases mem_aSet.1 hy with rfl | ⟨a, ha, rfl⟩
        · exact Or.inr ⟨k, Finset.mem_insert_self _ _, (mul_one _).symm⟩
        · exact Or.inr ⟨pr k a, Finset.mem_insert_of_mem (Finset.mem_union_right _
            (Finset.mem_image_of_mem _ ha)), (hpr a ha).2⟩
  have hkk : v k * v k = 1 := hu.sq k hk
  have hmem1 : ∀ y ∈ aSet v Sp, y ∈ aSet v Sf := fun y hy => (hA y).2 (Or.inl hy)
  have hmem2 : ∀ y ∈ aSet v Sp, v k * y ∈ aSet v Sf := fun y hy => (hA _).2 (Or.inr ⟨y, hy, rfl⟩)
  have hsplit : ∀ a ∈ aSet v Sp, ∀ b, v k * a * (v k * b) = a * b := by
    intro a ha b
    simp only [mul_assoc]
    rw [← mul_assoc a (v k) b, ← hcomK a ha, mul_assoc, ← mul_assoc (v k) (v k), hkk, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hS] at hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hk
    rcases Finset.mem_union.1 hi with hi | hi
    · exact hp.lt i hi
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hi
      exact (hpr a ha).1
  · intro x hx y hy
    rcases (hA x).1 hx with hx | ⟨x', hx', rfl⟩ <;> rcases (hA y).1 hy with hy | ⟨y', hy', rfl⟩
    · exact hmem1 _ (hp.mul _ hx _ hy)
    · rw [← mul_assoc, ← hcomK x hx, mul_assoc]
      exact hmem2 _ (hp.mul _ hx _ hy')
    · rw [mul_assoc]
      exact hmem2 _ (hp.mul _ hx' _ hy)
    · rw [hsplit x' hx' y']
      exact hmem1 _ (hp.mul _ hx' _ hy')
  · intro x hx y hy
    rcases (hA x).1 hx with hx | ⟨x', hx', rfl⟩ <;> rcases (hA y).1 hy with hy | ⟨y', hy', rfl⟩
    · exact hp.comm _ hx _ hy
    · rw [← mul_assoc, ← hcomK x hx, mul_assoc, hp.comm x hx y' hy', mul_assoc]
    · rw [mul_assoc, hp.comm x' hx' y hy, ← mul_assoc, hcomK y hy, mul_assoc]
    · rw [hsplit x' hx' y', hsplit y' hy' x', hp.comm x' hx' y' hy']
  · intro j
    rw [hC, Finset.mem_filter, hp.cc j]
    constructor
    · rintro ⟨⟨hj, hc⟩, hjk⟩
      refine ⟨hj, fun x hx => ?_⟩
      rcases (hA x).1 hx with hx | ⟨y, hy, rfl⟩
      · exact hc x hx
      · rw [← mul_assoc, hjk, mul_assoc, hc y hy, mul_assoc]
    · rintro ⟨hj, hc⟩
      exact ⟨⟨hj, fun x hx => hc x (hmem1 x hx)⟩,
        by simpa using hc (v k * 1) (hmem2 1 (mem_aSet.2 (Or.inl rfl)))⟩
  ·
    have hv1 : ∀ i ∈ Sp, v i ≠ 1 := fun i hi => hu.ne_one i (hp.lt i hi)
    have hkp : ∀ a ∈ Sp, pr k a ∉ Sp := by
      intro a ha hb
      have hmem : v k * v a ∈ aSet v Sp := by
        rw [← (hpr a ha).2]
        exact mem_aSet.2 (Or.inr ⟨_, hb, rfl⟩)
      have hk' : v k ∈ aSet v Sp := by
        have := hp.mul _ hmem _ (mem_aSet.2 (Or.inr ⟨a, ha, rfl⟩))
        rwa [mul_assoc, hu.sq a (hp.lt a ha), mul_one] at this
      rcases mem_aSet.1 hk' with h | ⟨i, hi, hik⟩
      · exact hu.ne_one k hk h
      · exact hkS (hu.inj i (hp.lt i hi) k hk hik ▸ hi)
    have hinj : Set.InjOn (pr k) Sp := by
      intro a ha b hb hab
      have e : v k * v a = v k * v b := by rw [← (hpr a ha).2, ← (hpr b hb).2, hab]
      exact hu.inj a (hp.lt a ha) b (hp.lt b hb) (mul_left_cancel e)
    have hknot : k ∉ Sp ∪ Sp.image (pr k) := by
      rw [Finset.mem_union, Finset.mem_image]
      rintro (h | ⟨a, ha, he⟩)
      · exact hkS h
      · have e : v k * v a = v k := by rw [← (hpr a ha).2, he]
        exact hv1 a ha (by simpa using e)
    have hdisj : Disjoint Sp (Sp.image (pr k)) := by
      rw [Finset.disjoint_right]
      intro x hx hxS
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      exact hkp a ha hxS
    rw [hS, Finset.card_insert_of_notMem hknot, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injOn hinj, hp.card, hz]
    ring

theorem recs_inv (hu : Uni n v pr) (hr : Recs n NF v pr S Cc P K Z) :
    ∀ f < NF, RecInv n v (S f) (Cc f) (Z f) := by
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro hf
    rcases Nat.eq_zero_or_pos f with rfl | hf0
    · have h1 : aSet v (S 0) = {1} := by simp [aSet, hr.S0]
      refine ⟨by simp [hr.S0], ?_, ?_, ?_, by simp [hr.S0, hr.Z0]⟩
      · intro x hx y hy
        rw [h1, Finset.mem_singleton] at hx hy ⊢
        rw [hx, hy, mul_one]
      · intro x hx y hy
        rw [h1, Finset.mem_singleton] at hx hy
        rw [hx, hy]
      · intro j
        rw [hr.Cc0, Finset.mem_range]
        refine ⟨fun h => ⟨h, fun x hx => ?_⟩, fun h => h.1⟩
        rw [h1, Finset.mem_singleton] at hx
        rw [hx, mul_one, one_mul]
    · have hp := hr.P_lt f hf0 hf
      exact recInv_step hu (ih _ hp (hp.trans hf)) (hr.K_lt f hf0 hf) (hr.K_nmem f hf0 hf)
        (hr.K_mem f hf0 hf) (hr.S_eq f hf0 hf) (hr.Cc_eq f hf0 hf) (hr.Z_eq f hf0 hf)

theorem card_aSet {T : Finset ℕ} (hu : Uni n v pr) (hT : ∀ i ∈ T, i < n) :
    (aSet v T).card = T.card + 1 := by
  have h1 : (1 : G) ∉ T.image v := by
    rw [Finset.mem_image]
    rintro ⟨i, hi, he⟩
    exact hu.ne_one i (hT i hi) he
  rw [aSet, Finset.card_insert_of_notMem h1, Finset.card_image_of_injOn
    (fun a ha b hb h => hu.inj a (hT a ha) b (hT b hb) h)]

theorem ea_complete [Finite G] (hu : Uni n v pr) (hr : Recs n NF v pr S Cc P K Z) (hNF : 0 < NF)
    (T : Subgroup G) (hT : ∀ s ∈ T, s * s = 1 → s ≠ 1 → ∃ i < n, v i = s)
    (E : Subgroup G) (hET : E ≤ T) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hsq : ∀ x ∈ E, x * x = 1) :
    ∃ f < NF, ∀ x, x ∈ E ↔ x = 1 ∨ ∃ i ∈ S f, v i = x := by
  have hinv := recs_inv hu hr
  let D : List (Finset G) := (List.range NF).map fun f => aSet v (S f)
  have hD : ∀ A ∈ D, ∃ f < NF, A = aSet v (S f) := by
    intro A hA
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hA
    exact ⟨f, List.mem_range.1 hf, rfl⟩
  have hmemD : ∀ f < NF, aSet v (S f) ∈ D := fun f hf =>
    List.mem_map.2 ⟨f, List.mem_range.2 hf, rfl⟩
  have h1 : ({1} : Finset G) ∈ D := by
    have := hmemD 0 hNF
    rwa [hr.S0, aSet, Finset.image_empty] at this
  have hext : ∀ A ∈ D, ∀ s : G, s ∈ T → s * s = 1 → s ∉ A → (∀ a ∈ A, a * s = s * a) →
      (A ∪ A.image (· * s)) ∈ D := by
    rintro _ hA s hsT hss hsA hcA
    obtain ⟨f, hf, rfl⟩ := hD _ hA
    have hI := hinv f hf
    have hs1 : s ≠ 1 := fun h => hsA (h ▸ Finset.mem_insert_self _ _)
    obtain ⟨i, hi, rfl⟩ := hT s hsT hss hs1
    have hiC : i ∈ Cc f := (hI.cc i).2 ⟨hi, fun x hx => (hcA x hx).symm⟩
    have hiS : i ∉ S f := fun h => hsA (mem_aSet.2 (Or.inr ⟨i, h, rfl⟩))
    obtain ⟨c, hc, hsub, hz, hic⟩ := hr.cover f hf i hiC hiS
    have hJ := hinv c hc
    have hsubA : aSet v (S f) ⊆ aSet v (S c) := Finset.insert_subset_insert _
      (Finset.image_subset_image hsub)
    have hvi : v i ∈ aSet v (S c) := mem_aSet.2 (Or.inr ⟨i, hic, rfl⟩)
    suffices e : aSet v (S f) ∪ (aSet v (S f)).image (· * v i) = aSet v (S c) by
      rw [e]
      exact hmemD c hc
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · refine Finset.union_subset hsubA ?_
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      exact hJ.mul _ (hsubA ha) _ hvi
    · have hdisj : Disjoint (aSet v (S f)) ((aSet v (S f)).image (· * v i)) := by
        rw [Finset.disjoint_right]
        intro x hx hxA
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
        apply hsA
        have h := hI.mul a ha (a * v i) hxA
        have haa : a * a = 1 := sq_of_mem hu hI.lt ha
        rwa [← mul_assoc, haa, one_mul] at h
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _
        (mul_left_injective _), card_aSet hu hI.lt, card_aSet hu hJ.lt, hJ.card, hI.card, hz]
      omega
  obtain ⟨A, hA, hAE⟩ := CFSG.Quasithin.B3.exists_mem_of_isEA_le T D h1 hext E hET hcomm hsq
  obtain ⟨f, hf, rfl⟩ := hD A hA
  exact ⟨f, hf, fun x => by rw [← hAE x, mem_aSet]⟩

end CFSG.KC.EaLat

end

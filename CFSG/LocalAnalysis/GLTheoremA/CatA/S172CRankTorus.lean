module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCFrame

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

open CFSG.Open

variable {G : Type*} [Group G]

private theorem card_closure_range_eq_pow_aux1 {m : ℕ} {e : Fin (m + 1) → G}
    (hc : ∀ i j, Commute (e i) (e j)) :
    Subgroup.closure (Set.range (fun i : Fin m => e i.succ)) ≤
      Subgroup.centralizer ({e 0} : Set G) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩ x hx
  rw [Set.mem_singleton_iff.1 hx]
  exact (hc 0 i.succ).eq

private theorem card_closure_range_eq_pow_aux2 {A : Subgroup G} {g : G}
    (h : A ≤ Subgroup.centralizer ({g} : Set G)) :
    Subgroup.zpowers g ≤ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.zpowers_le]
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact ((Subgroup.mem_centralizer_iff.1 (h ha)) g rfl).symm

private theorem card_closure_range_eq_pow_aux3 {p : ℕ} (hp : p.Prime) {A : Subgroup G} {g : G}
    (hg : g ∉ A) (hcard : Nat.card (Subgroup.zpowers g) = p) :
    Nat.card (A ⊓ Subgroup.zpowers g : Subgroup G) = 1 := by
  haveI : Finite ↥(Subgroup.zpowers g) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have hdvd : Nat.card (A ⊓ Subgroup.zpowers g : Subgroup G) ∣ p := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le inf_le_right
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | hp'
  · exact h1
  · exfalso
    have heq : A ⊓ Subgroup.zpowers g = Subgroup.zpowers g :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hp', hcard])
    have : g ∈ A ⊓ Subgroup.zpowers g := by rw [heq]; exact Subgroup.mem_zpowers g
    exact hg this.1

private theorem card_closure_range_eq_pow_aux4 {p : ℕ} [Fact p.Prime] {m : ℕ}
    (ih : ∀ (e : Fin m → G), (∀ i j, Commute (e i) (e j)) → (∀ i, orderOf (e i) = p) →
      (∀ i, e i ∉ Subgroup.closure (e '' {j | j ≠ i})) →
      Nat.card (Subgroup.closure (Set.range e)) = p ^ m)
    (e : Fin (m + 1) → G) (hc : ∀ i j, Commute (e i) (e j)) (ho : ∀ i, orderOf (e i) = p)
    (hi : ∀ i, e i ∉ Subgroup.closure (e '' {j | j ≠ i})) :
    Nat.card (Subgroup.closure (Set.range e)) = p ^ (m + 1) := by
  set e' : Fin m → G := fun i => e i.succ with he'
  have hsub : Set.range e' ⊆ e '' {j | j ≠ 0} := by
    rintro _ ⟨i, rfl⟩
    exact ⟨i.succ, Fin.succ_ne_zero i, rfl⟩
  set A := Subgroup.closure (Set.range e') with hA
  set B := Subgroup.zpowers (e 0) with hB
  have hcardA : Nat.card A = p ^ m := by
    refine ih e' (fun i j => hc _ _) (fun i => ho _) fun i => fun hmem => hi i.succ ?_
    refine Subgroup.closure_mono ?_ hmem
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨j.succ, fun h => hj (Fin.succ_injective _ h), rfl⟩
  have hcardB : Nat.card B = p := by rw [hB, Nat.card_zpowers, ho 0]
  haveI : Finite B :=
    Nat.finite_of_card_ne_zero (by rw [hcardB]; exact (Fact.out : p.Prime).ne_zero)
  have hrange : Set.range e = insert (e 0) (Set.range e') := by
    rw [← Fin.cons_self_tail e, Fin.range_cons]
    rfl
  have hsup : Subgroup.closure (Set.range e) = A ⊔ B := by
    rw [hrange, ← Set.singleton_union, Subgroup.closure_union, sup_comm, hA, hB,
      Subgroup.zpowers_eq_closure]
  have hcentr : A ≤ Subgroup.centralizer ({e 0} : Set G) := by
    rw [hA]
    exact card_closure_range_eq_pow_aux1 hc
  have hBnorm : B ≤ Subgroup.normalizer (A : Set G) := by
    rw [hB]
    exact card_closure_range_eq_pow_aux2 hcentr
  have hnot : e 0 ∉ A := fun hmem => hi 0 (Subgroup.closure_mono hsub hmem)
  have hinf : Nat.card (A ⊓ B : Subgroup G) = 1 := by
    rw [hB]
    exact card_closure_range_eq_pow_aux3 (Fact.out : p.Prime) hnot hcardB
  have h := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC.card_sup_mul_card_inf_of_le_normalizer'
    hBnorm
  rw [hinf, hcardB, mul_one, hcardA] at h
  rw [hsup, h, pow_succ]

theorem card_closure_range_eq_pow {p : ℕ} [Fact p.Prime] :
    ∀ {m : ℕ} (e : Fin m → G), (∀ i j, Commute (e i) (e j)) → (∀ i, orderOf (e i) = p) →
      (∀ i, e i ∉ Subgroup.closure (e '' {j | j ≠ i})) →
      Nat.card (Subgroup.closure (Set.range e)) = p ^ m := by
  intro m
  induction m with
  | zero =>
    intro e _ _ _
    rw [Set.range_eq_empty, Subgroup.closure_empty]
    simp
  | succ m ih =>
    intro e hc ho hi
    exact card_closure_range_eq_pow_aux4 ih e hc ho hi

theorem isElemAbelian_closure_range {p : ℕ} {m : ℕ} (e : Fin m → G)
    (hcomm : ∀ i j, Commute (e i) (e j)) (hp : ∀ i, e i ^ p = 1) :
    IsElemAbelian p (Subgroup.closure (Set.range e)) := by
  have hC : IsMulCommutative (Subgroup.closure (Set.range e)) :=
    Subgroup.isMulCommutative_closure (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact hcomm i j)
  refine ⟨hC, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hp i
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y :=
      congrArg Subtype.val (hC.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem isElemAbelian_card_closure_range {p : ℕ} [Fact p.Prime] {m : ℕ} (e : Fin m → G)
    (hcomm : ∀ i j, Commute (e i) (e j)) (hord : ∀ i, orderOf (e i) = p)
    (hindep : ∀ i, e i ∉ Subgroup.closure (e '' {j | j ≠ i})) :
    IsElemAbelian p (Subgroup.closure (Set.range e)) ∧
      Nat.card (Subgroup.closure (Set.range e)) = p ^ m :=
  ⟨isElemAbelian_closure_range e hcomm fun i => by rw [← hord i]; exact pow_orderOf_eq_one _,
    card_closure_range_eq_pow e hcomm hord hindep⟩

theorem not_mem_closure_image_of_smul_ne {H X : Type*} [Group H] [MulAction H X] (φ : G →* H) {m : ℕ}
    (e : Fin m → G) (x : Fin m → X) (hmove : ∀ i, φ (e i) • x i ≠ x i)
    (hfix : ∀ i j, i ≠ j → φ (e j) • x i = x i) (i : Fin m) :
    e i ∉ Subgroup.closure (e '' {j | j ≠ i}) := by
  intro hi
  have hle : Subgroup.closure (e '' {j | j ≠ i}) ≤ (MulAction.stabilizer H (x i)).comap φ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact hfix i j (Ne.symm hj)
  exact hmove i (hle hi)

end CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

end

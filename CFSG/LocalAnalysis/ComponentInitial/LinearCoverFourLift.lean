module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverHigherRoots
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearCover

open Subgroup
open scoped commutatorElement Pointwise

variable {K G E : Type*} [Field K] [Group G] [Group E]

theorem eq_one_of_map_add_of_map_mul {c : K → E} (hadd : ∀ a b, c (a + b) = c a * c b)
    {r : K} (hr : r ≠ 1) (hinv : ∀ a, c (r * a) = c a) (a : K) : c a = 1 := by
  have hr' : r - 1 ≠ 0 := sub_ne_zero.mpr hr
  have h := hinv ((r - 1)⁻¹ * a)
  rw [show r * ((r - 1)⁻¹ * a) = a + (r - 1)⁻¹ * a by field_simp; ring, hadd] at h
  exact mul_eq_right.mp h

section Lifts

variable (η : E →* G) (hker : ∀ z, η z = 1 → z ∈ center E)
include hker

theorem lift_mul_comm_of_torus (hη : Function.Surjective η) {x y : K → G}
    (hx : ∀ a b, x (a + b) = x a * x b) (hxy : ∀ a b, x a * y b = y b * x a) {t : G} {r : K}
    (hr : r ≠ 1) (htx : ∀ a, t * x a * t⁻¹ = x (r * a)) (hty : ∀ b, t * y b * t⁻¹ = y b)
    {e e' : E} {a b : K} (he : η e = x a) (he' : η e' = y b) : e * e' = e' * e := by
  have comm_eq : ∀ {p p' q q' : E}, η p = η p' → η q = η q' → ⁅p, q⁆ = ⁅p', q'⁆ :=
    fun hp hq => HeisenbergRoots.commutatorElement_eq_of_map_eq η hker hp hq
  choose lx hlx using fun a => hη (x a)
  obtain ⟨g, hg⟩ := hη t
  have hcen : ∀ a, ⁅lx a, e'⁆ ∈ center E := fun a => hker _ (by
    rw [map_commutatorElement, hlx, he', commutatorElement_eq_one_iff_mul_comm]
    exact hxy a b)
  have hadd : ∀ a a', ⁅lx (a + a'), e'⁆ = ⁅lx a, e'⁆ * ⁅lx a', e'⁆ := fun a a' => by
    rw [comm_eq (p' := lx a * lx a') (by rw [hlx, map_mul, hlx, hlx, hx]) rfl,
      commutatorElement_mul_left_of_mem_center (hcen a')]
  have hinv : ∀ a, ⁅lx (r * a), e'⁆ = ⁅lx a, e'⁆ := fun a => by
    have h1 : g * ⁅lx a, e'⁆ * g⁻¹ = ⁅lx a, e'⁆ := by
      rw [mem_center_iff.mp (hcen a) g, mul_inv_cancel_right]
    rw [← h1, conj_commutatorElement_eq]
    exact comm_eq (by rw [hlx, map_mul, map_mul, map_inv, hg, hlx, htx])
      (by rw [map_mul, map_mul, map_inv, hg, he', hty])
  have h : ⁅lx a, e'⁆ = 1 :=
    eq_one_of_map_add_of_map_mul (c := fun a => ⁅lx a, e'⁆) hadd hr hinv a
  exact commutatorElement_eq_one_iff_mul_comm.mp ((comm_eq (by rw [he, hlx]) rfl).trans h)

theorem exists_torus_lift (hη : Function.Surjective η) {x : K → G}
    (hx : ∀ a b, x (a + b) = x a * x b)
    (hxx : ∀ (e e' : E) (a b : K), η e = x a → η e' = x b → e * e' = e' * e) {t₀ : G}
    {r₀ : K} (hr₀ : r₀ ≠ 1) (ht₀ : ∀ a, t₀ * x a * t₀⁻¹ = x (r₀ * a)) :
    ∃ xl : K → E, (∀ a, η (xl a) = x a) ∧ (∀ a b, xl (a + b) = xl a * xl b) ∧
      ∀ (g : E) (ρ : K), η g * t₀ = t₀ * η g → (∀ a, η g * x a * (η g)⁻¹ = x (ρ * a)) →
        ∀ a, g * xl a * g⁻¹ = xl (ρ * a) := by
  have comm_eq : ∀ {p p' q q' : E}, η p = η p' → η q = η q' → ⁅p, q⁆ = ⁅p', q'⁆ :=
    fun hp hq => HeisenbergRoots.commutatorElement_eq_of_map_eq η hker hp hq
  choose lx hlx using fun a => hη (x a)
  obtain ⟨g₀, hg₀⟩ := hη t₀
  have hr : r₀ - 1 ≠ 0 := sub_ne_zero.mpr hr₀
  have himg : ∀ s, η ⁅g₀, lx s⁆ = x ((r₀ - 1) * s) := fun s => by
    rw [map_commutatorElement, hg₀, hlx, commutatorElement_def, ht₀, mul_inv_eq_iff_eq_mul,
      ← hx]
    congr 1
    ring
  refine ⟨fun a => ⁅g₀, lx ((r₀ - 1)⁻¹ * a)⁆, fun a => ?_, fun a b => ?_,
    fun g ρ hgt hgx a => ?_⟩
  · change η ⁅g₀, lx ((r₀ - 1)⁻¹ * a)⁆ = x a
    rw [himg, ← mul_assoc, mul_inv_cancel₀ hr, one_mul]
  · change ⁅g₀, lx ((r₀ - 1)⁻¹ * (a + b))⁆ =
      ⁅g₀, lx ((r₀ - 1)⁻¹ * a)⁆ * ⁅g₀, lx ((r₀ - 1)⁻¹ * b)⁆
    rw [comm_eq (q' := lx ((r₀ - 1)⁻¹ * a) * lx ((r₀ - 1)⁻¹ * b)) rfl
      (by rw [hlx, map_mul, hlx, hlx, ← hx, mul_add]), commutatorElement_mul_right_eq,
      hxx _ _ _ _ (hlx ((r₀ - 1)⁻¹ * a)) (himg ((r₀ - 1)⁻¹ * b)), mul_inv_cancel_right]
  · change g * ⁅g₀, lx ((r₀ - 1)⁻¹ * a)⁆ * g⁻¹ = ⁅g₀, lx ((r₀ - 1)⁻¹ * (ρ * a))⁆
    rw [conj_commutatorElement_eq]
    refine comm_eq ?_ ?_
    · rw [map_mul, map_mul, map_inv, hg₀, hgt, mul_inv_cancel_right]
    · rw [map_mul, map_mul, map_inv, hlx, hgx, hlx]
      congr 1
      ring

theorem eq_of_conj_eq_smul {p q : K → E} (hp : ∀ a b, p (a + b) = p a * p b)
    (hq : ∀ a b, q (a + b) = q a * q b) (hpq : ∀ a, η (p a) = η (q a)) {g : E} {r : K}
    (hr : r ≠ 1) (hgp : ∀ a, g * p a * g⁻¹ = p (r * a)) (hgq : ∀ a, g * q a * g⁻¹ = q (r * a))
    (a : K) : p a = q a := by
  have hcen : ∀ a, (q a)⁻¹ * p a ∈ center E := fun a => hker _ (by
    rw [map_mul, map_inv, hpq, inv_mul_cancel])
  have hadd : ∀ a b, (q (a + b))⁻¹ * p (a + b) = (q a)⁻¹ * p a * ((q b)⁻¹ * p b) :=
    fun a b => by
      rw [hp, hq, mul_inv_rev]
      calc (q b)⁻¹ * (q a)⁻¹ * (p a * p b) = (q b)⁻¹ * ((q a)⁻¹ * p a) * p b := by group
        _ = (q a)⁻¹ * p a * (q b)⁻¹ * p b := by rw [mem_center_iff.mp (hcen a) (q b)⁻¹]
        _ = (q a)⁻¹ * p a * ((q b)⁻¹ * p b) := by group
  have hinv : ∀ a, (q (r * a))⁻¹ * p (r * a) = (q a)⁻¹ * p a := fun a => by
    rw [← hgp, ← hgq]
    calc (g * q a * g⁻¹)⁻¹ * (g * p a * g⁻¹) = g * ((q a)⁻¹ * p a) * g⁻¹ := by group
      _ = (q a)⁻¹ * p a := by rw [mem_center_iff.mp (hcen a) g, mul_inv_cancel_right]
  have h : (q a)⁻¹ * p a = 1 :=
    eq_one_of_map_add_of_map_mul (c := fun a => (q a)⁻¹ * p a) hadd hr hinv a
  exact (inv_mul_eq_one.mp h).symm

theorem commutatorElement_lift_eq_of_torus {x y z : K → G} {xl yl zl : K → E}
    (hxl : ∀ a, η (xl a) = x a) (hyl : ∀ b, η (yl b) = y b) (hzl : ∀ c, η (zl c) = z c)
    (hxadd : ∀ a a', xl (a + a') = xl a * xl a') (hzadd : ∀ c c', zl (c + c') = zl c * zl c')
    (hxyz : ∀ a b, ⁅x a, y b⁆ = z (a * b))
    (hxz : ∀ (a : K) (e : E) (c : K), η e = z c → xl a * e = e * xl a)
    (hzz : ∀ (e e' : E) (c c' : K), η e = z c → η e' = z c' → e * e' = e' * e)
    {g : E} {r : K} (hr : r ≠ 1) (hgx : ∀ a, g * xl a * g⁻¹ = xl (r * a))
    (hgy : ∀ b, g * yl b * g⁻¹ = yl b) (hgz : ∀ c, g * zl c * g⁻¹ = zl (r * c)) (a b : K) :
    ⁅xl a, yl b⁆ = zl (a * b) := by
  have hcz : ∀ a, η ⁅xl a, yl b⁆ = z (a * b) := fun a => by
    rw [map_commutatorElement, hxl, hyl, hxyz]
  refine eq_of_conj_eq_smul η hker (p := fun a => ⁅xl a, yl b⁆) (q := fun a => zl (a * b))
    (g := g) (fun a a' => ?_) (fun a a' => ?_) (fun a => ?_) hr (fun a => ?_) (fun a => ?_) a
  · rw [hxadd, commutatorElement_mul_left_eq, hxz a _ _ (hcz a'), mul_inv_cancel_right]
    exact hzz _ _ _ _ (hcz a') (hcz a)
  · rw [add_mul, hzadd]
  · rw [hcz, hzl]
  · rw [conj_commutatorElement_eq, hgx, hgy]
  · rw [hgz, mul_assoc]

end Lifts

section Counting

theorem conj_mem_closure {X : Set E} {x : E} (hX : ∀ s ∈ X, x * s * x⁻¹ ∈ closure X) {h : E}
    (hh : h ∈ closure X) : x * h * x⁻¹ ∈ closure X := by
  induction hh using closure_induction with
  | mem s hs => exact hX s hs
  | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
  | mul a b _ _ ha hb =>
    rw [show x * (a * b) * x⁻¹ = x * a * x⁻¹ * (x * b * x⁻¹) by group]
    exact mul_mem ha hb
  | inv a _ ha =>
    rw [show x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ by group]
    exact inv_mem ha

theorem card_sup_le_of_conj_mem [Finite E] {M H : Subgroup E} {q : ℕ} (hM : Nat.card M ≤ q)
    (hnorm : ∀ x ∈ M, ∀ h ∈ H, x * h * x⁻¹ ∈ H) :
    Nat.card (M ⊔ H : Subgroup E) ≤ q * Nat.card H := by
  have hle : M ≤ normalizer (H : Set E) := fun x hx => mem_normalizer_iff.mpr fun h =>
    ⟨fun hh => hnorm x hx h hh, fun hh => by
      have h' := hnorm x⁻¹ (inv_mem hx) _ hh
      rwa [inv_inv, show x⁻¹ * (x * h * x⁻¹) * x = h by group] at h'⟩
  have hcoe := coe_mul_of_left_le_normalizer_right M H hle
  calc Nat.card (M ⊔ H : Subgroup E) = Nat.card ((M : Set E) * (H : Set E) : Set E) := by
        rw [← hcoe]
        rfl
    _ ≤ Nat.card (M : Set E) * Nat.card (H : Set E) := Set.natCard_mul_le
    _ ≤ q * Nat.card H := Nat.mul_le_mul_right _ hM

theorem card_closure_le_of_root_subgroups [Finite E] {n q : ℕ} (M : Fin n → Fin n → Subgroup E)
    (hM : ∀ i j, i < j → Nat.card (M i j) ≤ q)
    (hcomm : ∀ i j k l, i < j → k < l → j ≠ k → i ≠ l → (i, j) ≠ (k, l) →
      ∀ x ∈ M i j, ∀ y ∈ M k l, x * y = y * x)
    (hrel : ∀ i j l, i < j → j < l → ∀ x ∈ M i j, ∀ y ∈ M j l, ⁅x, y⁆ ∈ M i l) :
    Nat.card (closure {g | ∃ i j, i < j ∧ g ∈ M i j}) ≤ q ^ (n * (n - 1) / 2) := by
  classical
  have key : ∀ T : Finset (Fin n × Fin n), (∀ r ∈ T, r.1 < r.2) →
      (∀ i j l, (i, j) ∈ T → (j, l) ∈ T → (i, l) ∈ T) →
      Nat.card (closure {g | ∃ r ∈ T, g ∈ M r.1 r.2}) ≤ q ^ T.card := by
    intro T
    induction T using Finset.induction_on_min_value (fun r : Fin n × Fin n => r.2) with
    | empty =>
      intro _ _
      simp
    | insert a s has hmin ih =>
      intro hpos hcl
      obtain ⟨i₀, j₀⟩ := a
      have ha : i₀ < j₀ := hpos _ (Finset.mem_insert_self _ _)
      have hpos_s : ∀ r ∈ s, r.1 < r.2 := fun r hr => hpos r (Finset.mem_insert_of_mem hr)
      have hcl_s : ∀ i j l, (i, j) ∈ s → (j, l) ∈ s → (i, l) ∈ s := by
        intro i j l hij hjl
        rcases Finset.mem_insert.mp (hcl i j l (Finset.mem_insert_of_mem hij)
          (Finset.mem_insert_of_mem hjl)) with h | h
        · have h1 : j₀ ≤ j := hmin _ hij
          have h2 : j < l := hpos_s _ hjl
          rw [Prod.mk.injEq] at h
          exact absurd (h.2 ▸ h2) (not_lt.mpr h1)
        · exact h
      have ih' := ih hpos_s hcl_s
      have hset : {g | ∃ r ∈ insert (i₀, j₀) s, g ∈ M r.1 r.2} =
          (M i₀ j₀ : Set E) ∪ {g | ∃ r ∈ s, g ∈ M r.1 r.2} := by
        ext g
        constructor
        · rintro ⟨r, hr, hg⟩
          rcases Finset.mem_insert.mp hr with rfl | hr
          · exact Or.inl hg
          · exact Or.inr ⟨r, hr, hg⟩
        · rintro (hg | ⟨r, hr, hg⟩)
          · exact ⟨(i₀, j₀), Finset.mem_insert_self _ _, hg⟩
          · exact ⟨r, Finset.mem_insert_of_mem hr, hg⟩
      rw [hset, Subgroup.closure_union, closure_eq, Finset.card_insert_of_notMem has, pow_succ']
      refine (card_sup_le_of_conj_mem (hM i₀ j₀ ha) fun x hx h hh => ?_).trans
        (Nat.mul_le_mul_left q ih')
      refine conj_mem_closure (fun g hg => ?_) hh
      obtain ⟨⟨i, j⟩, hr, hg⟩ := hg
      have hij : i < j := hpos_s _ hr
      have hj : j₀ ≤ j := hmin _ hr
      by_cases hi : i = j₀
      · subst hi
        have hmem : (i₀, j) ∈ s := by
          rcases Finset.mem_insert.mp (hcl i₀ i j (Finset.mem_insert_self _ _)
            (Finset.mem_insert_of_mem hr)) with h | h
          · rw [Prod.mk.injEq] at h
            exact absurd h.2 hij.ne'
          · exact h
        rw [show x * g * x⁻¹ = ⁅x, g⁆ * g by simp only [commutatorElement_def]; group]
        exact mul_mem (subset_closure ⟨_, hmem, hrel i₀ i j ha hij x hx g hg⟩)
          (subset_closure ⟨_, hr, hg⟩)
      · rw [hcomm i₀ j₀ i j ha hij (Ne.symm hi) (ha.trans_le hj).ne
          (fun h => has (h ▸ hr)) x hx g hg, mul_inv_cancel_right]
        exact subset_closure ⟨_, hr, hg⟩
  set T : Finset (Fin n × Fin n) := Finset.univ.filter fun r => r.1 < r.2 with hTdef
  have hT := key T (fun r hr => (Finset.mem_filter.mp hr).2) (fun i j l hij hjl =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hij).2.trans (Finset.mem_filter.mp hjl).2⟩)
  have hset : {g | ∃ r ∈ T, g ∈ M r.1 r.2} = {g | ∃ i j, i < j ∧ g ∈ M i j} := by
    ext g
    constructor
    · rintro ⟨⟨i, j⟩, hr, hg⟩
      exact ⟨i, j, (Finset.mem_filter.mp hr).2, hg⟩
    · rintro ⟨i, j, hij, hg⟩
      exact ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, hg⟩
  rw [hset, hTdef, Fintype.card_product_filter_lt, Fintype.card_fin, Nat.choose_two_right] at hT
  exact hT

end Counting

end LinearCover

end CFSG.LocalAnalysis.ComponentInitial

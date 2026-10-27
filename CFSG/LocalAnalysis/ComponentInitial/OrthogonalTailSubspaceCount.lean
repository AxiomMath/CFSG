module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSubspaceCount
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWittFlags

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module Submodule
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (finrank_span_image_lt)

variable {K : Type*} [Field K]

section Model

variable {B : Type*} [AddCommGroup B] [Module K B]

theorem card_dotProduct_eq [Finite K] {n : ℕ} {x : Fin n → K} (hx : x ≠ 0) (c : K) :
    Nat.card {y : Fin n → K // ∑ i, x i * y i = c} = Nat.card K ^ (n - 1) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  set y₀ : Fin n → K := Pi.single i (c / x i) with hy₀
  have hxy₀ : ∑ k, x k * y₀ k = c := by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [hy₀, hk]) (by simp), hy₀,
      Pi.single_eq_same, mul_div_cancel₀ _ (show x i ≠ 0 from hi)]
  rw [← card_dotProduct_ne_zero K hx]
  refine Nat.card_congr
    { toFun := fun y => ⟨y.1 - y₀, by
        simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, y.2, hxy₀, sub_self]⟩
      invFun := fun y => ⟨y.1 + y₀, by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, y.2, hxy₀, zero_add]⟩
      left_inv := fun y => Subtype.ext (sub_add_cancel _ _)
      right_inv := fun y => Subtype.ext (add_sub_cancel_right _ _) }

theorem card_quadTail_eq_zero [Finite K] [FiniteDimensional K B] {qB : QuadraticForm K B}
    (hani : qB.Anisotropic) (n : ℕ) :
    Nat.card {v : (Fin n ⊕ Fin n → K) × B // quadTail n qB v = 0} =
      Nat.card K ^ n +
        (Nat.card K ^ n - 1) * (Nat.card K ^ finrank K B * Nat.card K ^ (n - 1)) := by
  classical
  have : Finite B := Module.finite_of_finite K
  let _ := Fintype.ofFinite K
  let _ := Fintype.ofFinite B
  let e : {v : (Fin n ⊕ Fin n → K) × B // quadTail n qB v = 0} ≃
      Σ x : Fin n → K, Σ b : B, {y : Fin n → K // ∑ i, x i * y i = -qB b} :=
    { toFun := fun v => ⟨fun i => v.1.1 (.inl i), v.1.2, fun i => v.1.1 (.inr i), by
        have h := v.2
        rw [quadTail_apply, quadPlus_apply] at h
        exact eq_neg_of_add_eq_zero_left h⟩
      invFun := fun p => ⟨(Sum.elim p.1 p.2.2.1, p.2.1), by
        rw [quadTail_apply, quadPlus_apply]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [p.2.2.2, neg_add_cancel]⟩
      left_inv := fun v => Subtype.ext (Prod.ext (funext fun s => by cases s <;> rfl) rfl)
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  simp only [Nat.card_sigma]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ 0)]
  have h0 : ∑ b : B, Nat.card {y : Fin n → K // ∑ i, (0 : Fin n → K) i * y i = -qB b} =
      Nat.card K ^ n := by
    rw [Finset.sum_eq_single 0]
    · rw [QuadraticMap.map_zero, neg_zero]
      exact card_dotProduct_zero K n
    · intro b _ hb
      rw [Nat.card_eq_zero]
      left
      refine ⟨fun y => hb (hani b ?_)⟩
      have hy := y.2
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hy
      exact neg_eq_zero.1 hy.symm
    · simp
  have h1 : ∀ x ∈ Finset.univ.erase (0 : Fin n → K),
      ∑ b : B, Nat.card {y : Fin n → K // ∑ i, x i * y i = -qB b} =
        Nat.card K ^ finrank K B * Nat.card K ^ (n - 1) := by
    intro x hx
    rw [Finset.sum_congr rfl fun b _ => card_dotProduct_eq (Finset.ne_of_mem_erase hx) _,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := K)]
  rw [h0, Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, smul_eq_mul, Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card]

theorem card_quadTail_nonzero_singular [Finite K] [FiniteDimensional K B]
    {qB : QuadraticForm K B} (hani : qB.Anisotropic) (n : ℕ) :
    Nat.card {v : (Fin n ⊕ Fin n → K) × B // v ≠ 0 ∧ quadTail n qB v = 0} =
      (Nat.card K ^ n - 1) * (Nat.card K ^ (n + finrank K B - 1) + 1) := by
  have : Finite B := Module.finite_of_finite K
  have hN : Nat.card {v : (Fin n ⊕ Fin n → K) × B | v ≠ 0 ∧ quadTail n qB v = 0} + 1 =
      Nat.card {v : (Fin n ⊕ Fin n → K) × B // quadTail n qB v = 0} := by
    have hset : {v : (Fin n ⊕ Fin n → K) × B | v ≠ 0 ∧ quadTail n qB v = 0} =
        {v | quadTail n qB v = 0} \ {0} := by
      ext v
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [hset, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_add_one
      (show (0 : (Fin n ⊕ Fin n → K) × B) ∈ {v | quadTail n qB v = 0} from
        QuadraticMap.map_zero _)]
    exact (Nat.card_coe_set_eq _).symm
  rw [card_quadTail_eq_zero hani] at hN
  have hset' : Nat.card {v : (Fin n ⊕ Fin n → K) × B // v ≠ 0 ∧ quadTail n qB v = 0} =
      Nat.card {v : (Fin n ⊕ Fin n → K) × B | v ≠ 0 ∧ quadTail n qB v = 0} := rfl
  rw [hset']
  have hq : 1 < Nat.card K := Finite.one_lt_card
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero, Nat.sub_self, zero_mul, add_zero] at hN ⊢
    omega
  · have hpow : Nat.card K ^ finrank K B * Nat.card K ^ (n - 1) =
        Nat.card K ^ (n + finrank K B - 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow] at hN
    have h1 : 1 ≤ Nat.card K ^ n := Nat.one_le_pow _ _ (by omega)
    obtain ⟨a, ha⟩ : ∃ a, a = Nat.card K ^ n - 1 := ⟨_, rfl⟩
    rw [← ha] at hN ⊢
    have h2 : Nat.card K ^ n = a + 1 := by omega
    rw [h2] at hN
    nlinarith

@[expose] def hiPart {r j : ℕ} (hj : j ≤ r) (v : Fin r ⊕ Fin r → K) :
    Fin (r - j) ⊕ Fin (r - j) → K :=
  Sum.elim (fun t => v (Sum.inl (splitIdx hj (Sum.inr t))))
    (fun t => v (Sum.inr (splitIdx hj (Sum.inr t))))

@[expose] def joinHi {r j : ℕ} (hj : j ≤ r) (a : Fin j → K) (u : Fin (r - j) ⊕ Fin (r - j) → K) :
    Fin r ⊕ Fin r → K :=
  Sum.elim (fun p => Sum.elim a (fun t => u (Sum.inl t)) ((splitIdx hj).symm p))
    (fun p => Sum.elim (fun _ => (0 : K)) (fun t => u (Sum.inr t)) ((splitIdx hj).symm p))

theorem hiPart_joinHi {r j : ℕ} (hj : j ≤ r) (a : Fin j → K) (u : Fin (r - j) ⊕ Fin (r - j) → K) :
    hiPart hj (joinHi hj a u) = u := by
  funext s
  rcases s with t | t <;> simp [hiPart, joinHi]

theorem joinHi_low_e {r j : ℕ} (hj : j ≤ r) (a : Fin j → K) (u : Fin (r - j) ⊕ Fin (r - j) → K)
    (i : Fin j) : joinHi hj a u (Sum.inl (splitIdx hj (Sum.inl i))) = a i := by
  simp [joinHi]

theorem joinHi_low_f {r j : ℕ} (hj : j ≤ r) (a : Fin j → K) (u : Fin (r - j) ⊕ Fin (r - j) → K)
    (i : Fin j) : joinHi hj a u (Sum.inr (splitIdx hj (Sum.inl i))) = 0 := by
  simp [joinHi]

theorem joinHi_hiPart {r j : ℕ} (hj : j ≤ r) {v : Fin r ⊕ Fin r → K}
    (hv : ∀ i : Fin j, v (Sum.inr (splitIdx hj (Sum.inl i))) = 0) :
    joinHi hj (fun i => v (Sum.inl (splitIdx hj (Sum.inl i)))) (hiPart hj v) = v := by
  funext c
  rcases c with p | p <;> obtain ⟨s, rfl⟩ := (splitIdx hj).surjective p <;>
    rcases s with i | t <;> simp [joinHi, hiPart, hv]

theorem quadPlus_eq_add_hiPart {r j : ℕ} (hj : j ≤ r) (v : Fin r ⊕ Fin r → K) :
    quadPlus r K v = ∑ i : Fin j, v (Sum.inl (splitIdx hj (Sum.inl i))) *
        v (Sum.inr (splitIdx hj (Sum.inl i))) + quadPlus (r - j) K (hiPart hj v) := by
  rw [quadPlus_apply, quadPlus_apply, ← Equiv.sum_comp (splitIdx hj), Fintype.sum_sum_type]
  rfl

theorem mem_flag_iff_hiPart {r j : ℕ} (hj : j ≤ r) {v : Fin r ⊕ Fin r → K}
    (hv : ∀ i : Fin j, v (Sum.inr (splitIdx hj (Sum.inl i))) = 0) :
    v ∈ flag r K j ↔ hiPart hj v = 0 := by
  rw [mem_flag]
  constructor
  · rintro ⟨h1, h2⟩
    funext s
    rcases s with t | t
    · exact h2 _ (by rw [splitIdx_inr]; omega)
    · exact h1 _
  · intro h
    refine ⟨fun p => ?_, fun p hp => ?_⟩
    · obtain ⟨s, rfl⟩ := (splitIdx hj).surjective p
      rcases s with i | t
      · exact hv i
      · exact congrFun h (Sum.inr t)
    · obtain ⟨s, rfl⟩ := (splitIdx hj).surjective p
      rcases s with i | t
      · rw [splitIdx_inl] at hp
        exact absurd i.isLt (by omega)
      · exact congrFun h (Sum.inl t)

theorem mem_tailFlag_iff {r j : ℕ} {v : (Fin r ⊕ Fin r → K) × B} :
    v ∈ tailFlag K B r j ↔ v.1 ∈ flag r K j ∧ v.2 = 0 := by
  rw [tailFlag_eq_map, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨v.1, h1, Prod.ext rfl h2.symm⟩

theorem polar_tailFlag_eq_zero_iff {qB : QuadraticForm K B} {r j : ℕ} (hj : j ≤ r)
    {v : (Fin r ⊕ Fin r → K) × B} :
    (∀ w ∈ tailFlag K B r j, polar (quadTail r qB) v w = 0) ↔
      ∀ i : Fin j, v.1 (Sum.inr (splitIdx hj (Sum.inl i))) = 0 := by
  rw [← polar_flag_eq_zero_iff' hj]
  constructor
  · intro h w hw
    have := h (w, 0) (mem_tailFlag_iff.2 ⟨hw, rfl⟩)
    rwa [polar_quadTail, polar_zero_right, add_zero] at this
  · intro h w hw
    obtain ⟨h1, h2⟩ := mem_tailFlag_iff.1 hw
    rw [polar_quadTail, h2, polar_zero_right, add_zero]
    exact h w.1 h1

theorem quadTail_eq_add_highPart {qB : QuadraticForm K B} {r j : ℕ} (hj : j ≤ r)
    (v : (Fin r ⊕ Fin r → K) × B) :
    quadTail r qB v = ∑ i : Fin j, v.1 (Sum.inl (splitIdx hj (Sum.inl i))) *
        v.1 (Sum.inr (splitIdx hj (Sum.inl i))) + quadTail (r - j) qB (hiPart hj v.1, v.2) := by
  rw [quadTail_apply, quadTail_apply, quadPlus_eq_add_hiPart hj, add_assoc]

theorem card_singularOrthOutside_tailFlag {qB : QuadraticForm K B} {r j : ℕ} (hj : j ≤ r) :
    Nat.card (singularOrthOutside (quadTail r qB) (tailFlag K B r j)) =
      Nat.card (Fin j → K) * Nat.card {u : (Fin (r - j) ⊕ Fin (r - j) → K) × B //
        u ≠ 0 ∧ quadTail (r - j) qB u = 0} := by
  rw [← Nat.card_prod]
  have hlow : ∀ x ∈ singularOrthOutside (quadTail r qB) (tailFlag K B r j),
      ∀ i : Fin j, x.1 (Sum.inr (splitIdx hj (Sum.inl i))) = 0 :=
    fun x hx => (polar_tailFlag_eq_zero_iff hj).1 hx.2.2
  have hQ : ∀ x ∈ singularOrthOutside (quadTail r qB) (tailFlag K B r j),
      quadTail (r - j) qB (hiPart hj x.1, x.2) = 0 := fun x hx => by
    have h := quadTail_eq_add_highPart (qB := qB) hj x
    rw [hx.2.1, Finset.sum_eq_zero fun i _ => by rw [hlow x hx i, mul_zero], zero_add] at h
    exact h.symm
  have hmem : ∀ x : (Fin r ⊕ Fin r → K) × B,
      (∀ i : Fin j, x.1 (Sum.inr (splitIdx hj (Sum.inl i))) = 0) →
      (x ∈ tailFlag K B r j ↔
        ((hiPart hj x.1, x.2) : (Fin (r - j) ⊕ Fin (r - j) → K) × B) = 0) := by
    intro x hx
    rw [mem_tailFlag_iff, mem_flag_iff_hiPart hj hx, Prod.mk_eq_zero]
  refine Nat.card_congr
    { toFun := fun x =>
        (fun i => (x : (Fin r ⊕ Fin r → K) × B).1 (Sum.inl (splitIdx hj (Sum.inl i))),
          ⟨(hiPart hj x.1.1, x.1.2), fun h0 => x.2.1 ((hmem x.1 (hlow x x.2)).2 h0), hQ x x.2⟩)
      invFun := fun p => ⟨(joinHi hj p.1 p.2.1.1, p.2.1.2), ?_, ?_, ?_⟩
      left_inv := fun x => ?_
      right_inv := fun p => ?_ }
  · rw [hmem (joinHi hj p.1 p.2.1.1, p.2.1.2) (joinHi_low_f hj p.1 p.2.1.1)]
    dsimp only
    rw [hiPart_joinHi]
    exact p.2.2.1
  · rw [quadTail_eq_add_highPart hj]
    dsimp only
    rw [hiPart_joinHi, Finset.sum_eq_zero fun i _ => by rw [joinHi_low_f, mul_zero], zero_add]
    exact p.2.2.2
  · rw [polar_tailFlag_eq_zero_iff hj]
    exact joinHi_low_f hj p.1 p.2.1.1
  · exact Subtype.ext (Prod.ext (joinHi_hiPart hj (hlow x.1 x.2)) rfl)
  · exact Prod.ext (funext fun i => joinHi_low_e hj _ _ i)
      (Subtype.ext (Prod.ext (hiPart_joinHi hj _ _) rfl))

end Model

section Frame

variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {r : ℕ}

@[expose] noncomputable def frameMap (P : Fin r → HypPair Q) :
    ((Fin r ⊕ Fin r → K) × pairsPerp P) →ₗ[K] V :=
  (Fintype.linearCombination K (Sum.elim (fun i => (P i).e) (fun i => (P i).f))).comp
      (LinearMap.fst K _ _) + (pairsPerp P).subtype.comp (LinearMap.snd K _ _)

theorem frameMap_apply (P : Fin r → HypPair Q) (x : (Fin r ⊕ Fin r → K) × pairsPerp P) :
    frameMap P x =
      ∑ i, x.1 (.inl i) • (P i).e + ∑ i, x.1 (.inr i) • (P i).f + (x.2 : V) := by
  simp only [frameMap, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, Fintype.linearCombination_apply, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Submodule.subtype_apply]

theorem frameMap_hypVec (P : Fin r → HypPair Q) (i : Fin r) :
    frameMap P (hypVec K (pairsPerp P) (.inl i)) = (P i).e := by
  rw [frameMap_apply, hypVec]
  simp [Pi.single_apply]

variable {P : Fin r → HypPair Q} (hP : ∀ i j, i ≠ j → (P i).Orth (P j))
include hP

omit hP in
theorem mem_pairsSpan_sum (x y : Fin r → K) :
    ∑ i, x i • (P i).e + ∑ i, y i • (P i).f ∈ pairsSpan P :=
  add_mem (sum_mem fun i _ => smul_mem _ _ (subset_span (Or.inl ⟨i, rfl⟩)))
    (sum_mem fun i _ => smul_mem _ _ (subset_span (Or.inr ⟨i, rfl⟩)))

theorem quad_sum_pairs (x y : Fin r → K) :
    Q (∑ i, x i • (P i).e + ∑ i, y i • (P i).f) = ∑ i, x i * y i := by
  obtain ⟨hef, hfe, hee, hff⟩ := polar_pairs hP
  have hX : Q (∑ i, x i • (P i).e) = 0 :=
    map_eq_zero_of_mem_span (S := Set.range fun i => (P i).e)
      (by rintro _ ⟨i, rfl⟩; exact (P i).Q_e) (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hee i j)
      (sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩))
  have hY : Q (∑ i, y i • (P i).f) = 0 :=
    map_eq_zero_of_mem_span (S := Set.range fun i => (P i).f)
      (by rintro _ ⟨i, rfl⟩; exact (P i).Q_f) (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hff i j)
      (sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩))
  rw [QuadraticMap.map_add Q, hX, hY, zero_add, zero_add, polar_sum_smul_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [polar_sum_smul_right]
  simp [hef]

theorem quad_frameMap (x : (Fin r ⊕ Fin r → K) × pairsPerp P) :
    Q (frameMap P x) = quadTail r (Q.comp (pairsPerp P).subtype) x := by
  rw [frameMap_apply, QuadraticMap.map_add Q, quad_sum_pairs hP,
    polar_pairsSpan_pairsPerp P (mem_pairsSpan_sum (P := P) _ _) x.2.2, add_zero, quadTail_apply,
    quadPlus_apply, QuadraticMap.comp_apply, Submodule.subtype_apply]

variable (hQ : (polarBilin Q).Nondegenerate)
include hQ

theorem frameMap_bijective : Function.Bijective (frameMap P) := by
  have hli := linearIndependent_pairs hP
  refine ⟨fun x y hxy => ?_, fun v => ?_⟩
  ·
    have hsum : ∀ z : (Fin r ⊕ Fin r → K) × pairsPerp P,
        frameMap P z = Fintype.linearCombination K (Sum.elim (fun i => (P i).e)
          (fun i => (P i).f)) z.1 + (z.2 : V) := fun z => rfl
    rw [hsum, hsum] at hxy
    have hs : Fintype.linearCombination K (Sum.elim (fun i => (P i).e) (fun i => (P i).f))
        (x.1 - y.1) = ((y.2 : V) - x.2) := by
      rw [map_sub]
      linear_combination (norm := module) hxy
    have hmemS : ((y.2 : V) - x.2) ∈ pairsSpan P := by
      rw [← hs, Fintype.linearCombination_apply, pairsSpan, ← Set.Sum.elim_range]
      exact sum_mem fun c _ => smul_mem _ _ (subset_span ⟨c, rfl⟩)
    have hmemP : ((y.2 : V) - x.2) ∈ pairsPerp P := sub_mem y.2.2 x.2.2
    have h0 : ((y.2 : V) - x.2) = 0 := by
      have := (pairsSpan_inf_pairsPerp hP hQ).le ⟨hmemS, hmemP⟩
      rwa [mem_bot] at this
    rw [h0] at hs
    have h1 : x.1 - y.1 = 0 := by
      rw [Fintype.linearCombination_apply] at hs
      exact funext (Fintype.linearIndependent_iff.1 hli _ hs)
    exact Prod.ext (sub_eq_zero.1 h1) (Subtype.ext (sub_eq_zero.1 h0).symm)
  ·
    have hv : v ∈ pairsSpan P ⊔ pairsPerp P := by
      rw [pairsSpan_sup_pairsPerp hP]
      exact mem_top
    obtain ⟨s, hs, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
    rw [pairsSpan, ← Set.Sum.elim_range] at hs
    obtain ⟨w, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hs
    exact ⟨(w, ⟨c, hc⟩), by rw [← Fintype.linearCombination_apply]; rfl⟩

@[expose] noncomputable def frameEquiv : ((Fin r ⊕ Fin r → K) × pairsPerp P) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (frameMap P) (frameMap_bijective hP hQ)

theorem coe_frameEquiv : ((frameEquiv hP hQ : _ ≃ₗ[K] V) : _ →ₗ[K] V) = frameMap P :=
  rfl

theorem map_tailFlag_frameEquiv (j : ℕ) :
    (tailFlag K (pairsPerp P) r j).map ((frameEquiv hP hQ : _ ≃ₗ[K] V) : _ →ₗ[K] V) =
      span K ((fun i => (P i).e) '' {i : Fin r | (i : ℕ) < j}) := by
  rw [coe_frameEquiv, tailFlag, Submodule.map_span, ← Set.image_comp]
  congr 1
  refine Set.image_congr fun i _ => ?_
  exact frameMap_hypVec P i

end Frame

theorem card_singularOrthOutside_map₂ {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁]
    [AddCommGroup V₂] [Module K V₂] {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (φ : V₁ ≃ₗ[K] V₂) (hφ : ∀ x, Q₂ (φ x) = Q₁ x) (U : Submodule K V₁) :
    Nat.card (singularOrthOutside Q₂ (U.map (φ : V₁ →ₗ[K] V₂))) =
      Nat.card (singularOrthOutside Q₁ U) := by
  have hpolar : ∀ x y, polar Q₂ (φ x) (φ y) = polar Q₁ x y := fun x y => by
    simp only [QuadraticMap.polar, ← map_add, hφ]
  have hmem : ∀ x, φ x ∈ U.map (φ : V₁ →ₗ[K] V₂) ↔ x ∈ U := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => by rwa [φ.injective hyx] at hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hiff : ∀ x, x ∈ singularOrthOutside Q₁ U ↔
      φ x ∈ singularOrthOutside Q₂ (U.map (φ : V₁ →ₗ[K] V₂)) := by
    intro x
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by rwa [hmem], by rw [hφ]; exact h2, ?_⟩
      rintro _ ⟨w, hw, rfl⟩
      rw [LinearEquiv.coe_coe, hpolar]
      exact h3 w hw
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by rwa [hmem] at h1, by rwa [hφ] at h2, fun w hw => ?_⟩
      have := h3 (φ w) ⟨w, hw, rfl⟩
      rwa [hpolar] at this
  exact (Nat.card_congr (φ.toEquiv.subtypeEquiv hiff)).symm

section Tail

variable {A : Type*} [AddCommGroup A] [Module K A] [FiniteDimensional K A] {r : ℕ}
  {qA : QuadraticForm K A} (hani : qA.Anisotropic) (hreg : (polarBilin qA).Nondegenerate)
include hani hreg

theorem exists_tail_pairs_of_totSing {U : Submodule K ((Fin r ⊕ Fin r → K) × A)}
    (hU : ∀ v ∈ U, quadTail r qA v = 0) :
    ∃ P : Fin r → HypPair (quadTail r qA), (∀ i j, i ≠ j → (P i).Orth (P j)) ∧
      finrank K (pairsPerp P) = finrank K A ∧
      (∀ x ∈ pairsPerp P, quadTail r qA x = 0 → x = 0) ∧
      U = span K ((fun j => (P j).e) '' {j : Fin r | (j : ℕ) < finrank K U}) := by
  set k := finrank K U with hkdef
  have hk : k ≤ r := finrank_le_of_totSing_tail hani hU
  set u := Module.finBasis K U
  set Wf : ℕ → Submodule K ((Fin r ⊕ Fin r → K) × A) :=
    fun i => span K ((fun j : Fin k => (u j : (Fin r ⊕ Fin r → K) × A)) '' {j | (j : ℕ) < i})
    with hWf
  have hli : LinearIndependent K (fun j : Fin k => (u j : (Fin r ⊕ Fin r → K) × A)) :=
    u.linearIndependent.map' U.subtype (ker_subtype U)
  have hWd : ∀ i ≤ k, finrank K (Wf i) = i := fun i hi => finrank_span_image_lt hli hi
  have hWm : ∀ i < k, Wf i ≤ Wf (i + 1) := fun i _ =>
    span_mono (Set.image_mono fun j (hj : (j : ℕ) < i) => Nat.lt_succ_of_lt hj)
  have hWt : Wf k ≤ U := span_le.2 (by rintro _ ⟨j, -, rfl⟩; exact (u j).2)
  obtain ⟨P, hPo, -, hd, -, ha, hPW⟩ := exists_tail_pairs_of_flag hani hreg hk hWd hWm
    (fun x hx => hU x (hWt hx))
  refine ⟨P, hPo, hd, ha, ?_⟩
  rw [← hPW k le_rfl]
  exact (eq_of_le_of_finrank_eq hWt (by rw [hWd k le_rfl])).symm

theorem card_singularOrthOutside_tail [Finite K] {j : ℕ} (hj : j ≤ r)
    {U : Submodule K ((Fin r ⊕ Fin r → K) × A)} (hU : U ∈ singularSubspaces (quadTail r qA) j) :
    Nat.card (singularOrthOutside (quadTail r qA) U) =
      Nat.card K ^ j *
        ((Nat.card K ^ (r - j) - 1) * (Nat.card K ^ (r - j + finrank K A - 1) + 1)) := by
  obtain ⟨P, hPo, hdim, hanis, hUP⟩ := exists_tail_pairs_of_totSing hani hreg hU.2
  rw [hU.1] at hUP
  have hQ := nondegenerate_polarBilin_quadTail (r := r) hreg
  have hU' : U = (tailFlag K (pairsPerp P) r j).map
      ((frameEquiv hPo hQ : _ ≃ₗ[K] _) : _ →ₗ[K] (Fin r ⊕ Fin r → K) × A) := by
    rw [map_tailFlag_frameEquiv, hUP]
  have hani' : ((quadTail r qA).comp (pairsPerp P).subtype).Anisotropic := fun x hx =>
    Subtype.ext (hanis x x.2 hx)
  rw [hU', card_singularOrthOutside_map₂ (frameEquiv hPo hQ) (fun x => quad_frameMap hPo x),
    card_singularOrthOutside_tailFlag hj, card_quadTail_nonzero_singular hani', hdim,
    Nat.card_fun, Nat.card_fin]

theorem card_extensionsWith_singular_tail [Finite K] {j : ℕ} (hj : j ≤ r)
    {U : Submodule K ((Fin r ⊕ Fin r → K) × A)} (hU : U ∈ singularSubspaces (quadTail r qA) j) :
    (Nat.card (extensionsWith (fun X => ∀ x ∈ X, quadTail r qA x = 0) U j) : ℚ) =
      ((Nat.card K : ℚ) ^ (r - j) - 1) * ((Nat.card K : ℚ) ^ (r - j + finrank K A - 1) + 1) /
        ((Nat.card K : ℚ) - 1) := by
  obtain ⟨hUd, hUs⟩ := hU
  have hS := card_vectors_eq_mul_card_extensions (W := U)
    (S := singularOrthOutside (quadTail r qA) U) (fun x hx => hx.1) fun c w x hc hw hx => by
      refine ⟨fun h => hx.1 ?_, ?_, fun w' hw' => ?_⟩
      · simpa [smul_smul, inv_mul_cancel₀ hc] using U.smul_mem c⁻¹ (U.sub_mem h hw)
      · rw [QuadraticMap.map_add (quadTail r qA), map_smul_eq_sq, hx.2.1, hUs w hw,
          polar_smul_left_eq, hx.2.2 w hw]
        ring
      · rw [polar_add_left, polar_smul_left_eq, hx.2.2 w' hw',
          polar_eq_zero_of_singular hUs hw hw', mul_zero, add_zero]
  have hext : extensionsIn U (singularOrthOutside (quadTail r qA) U) =
      extensionsWith (fun X => ∀ x ∈ X, quadTail r qA x = 0) U j := by
    ext W'
    constructor
    · rintro ⟨hUW', hd, hW'⟩
      refine ⟨hUW', by rw [hd, hUd], fun x hx => ?_⟩
      by_cases hxU : x ∈ U
      · exact hUs x hxU
      · exact (hW' x hx hxU).2.1
    · rintro ⟨hUW', hd, hW's⟩
      refine ⟨hUW', by rw [hd, hUd], fun x hx hxU => ⟨hxU, hW's x hx, fun w hw => ?_⟩⟩
      exact polar_eq_zero_of_singular hW's hx (hUW' hw)
  rw [hext, card_singularOrthOutside_tail hani hreg hj ⟨hUd, hUs⟩, hUd] at hS
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hq1 : 1 ≤ Nat.card K := hq.le
  have hpos := pow_succ_sub_pow_pos (K := K) j
  have h1 : 1 ≤ Nat.card K ^ (r - j) := Nat.one_le_pow _ _ (by omega)
  have hle' : Nat.card K ^ j ≤ Nat.card K ^ (j + 1) := Nat.pow_le_pow_right hq1 (by omega)
  have hS' := congrArg (Nat.cast : ℕ → ℚ) hS
  push_cast [Nat.cast_sub h1, Nat.cast_sub hle'] at hS'
  have hqQ : (1 : ℚ) < Nat.card K := by exact_mod_cast hq
  have hden : (Nat.card K : ℚ) - 1 ≠ 0 := by linarith
  have hqj : (Nat.card K : ℚ) ^ j ≠ 0 := pow_ne_zero _ (by linarith)
  rw [eq_div_iff hden]
  have hfac : (Nat.card K : ℚ) ^ (j + 1) - (Nat.card K : ℚ) ^ j =
      (Nat.card K : ℚ) ^ j * ((Nat.card K : ℚ) - 1) := by ring
  rw [hfac] at hS'
  have := hS'.symm
  apply mul_left_cancel₀ hqj
  linear_combination this

omit hani hreg [FiniteDimensional K A] in
theorem singular_natFlag_tail {k : ℕ} {W : Fin k → Submodule K ((Fin r ⊕ Fin r → K) × A)}
    (hW : ∀ i, ∀ x ∈ W i, quadTail r qA x = 0) : ∀ x ∈ natFlag W k, quadTail r qA x = 0 := by
  intro x hx
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [natFlag_of_not_pos W (by omega), mem_bot] at hx
    rw [hx, QuadraticMap.map_zero]
  · rw [natFlag_of_pos W hk le_rfl] at hx
    exact hW _ x hx

theorem card_singularFlags_tail [Finite K] {k : ℕ} (hk : k ≤ r) :
    (Nat.card (singularFlags (quadTail r qA) k) : ℚ) =
      ∏ j ∈ Finset.range k, (((Nat.card K : ℚ) ^ (r - j) - 1) *
        ((Nat.card K : ℚ) ^ (r + finrank K A - j - 1) + 1) / ((Nat.card K : ℚ) - 1)) := by
  change (Nat.card (flagsWith (fun X => ∀ x ∈ X, quadTail r qA x = 0) k) : ℚ) = _
  apply card_flagsWith
  intro j hj W hW
  rw [card_extensionsWith_singular_tail hani hreg (by omega)
    ⟨finrank_natFlag hW.1, singular_natFlag_tail hW.2.2⟩,
    show r - j + finrank K A - 1 = r + finrank K A - j - 1 by omega]

omit hani hreg in
theorem card_singularFlags_eq_mul_tail [Finite K] {k : ℕ} (hk : 0 < k) :
    (Nat.card (singularFlags (quadTail r qA) k) : ℚ) =
      Nat.card (singularSubspaces (quadTail r qA) k) *
        ∏ j ∈ Finset.range k, (((Nat.card K : ℚ) ^ k - (Nat.card K : ℚ) ^ j) /
          ((Nat.card K : ℚ) ^ (j + 1) - (Nat.card K : ℚ) ^ j)) := by
  classical
  have : Finite ((Fin r ⊕ Fin r → K) × A) := Module.finite_of_finite K
  have : Finite (Submodule K ((Fin r ⊕ Fin r → K) × A)) :=
    Finite.of_injective _ SetLike.coe_injective
  let _ := Fintype.ofFinite (singularSubspaces (quadTail r qA) k)
  let top : singularFlags (quadTail r qA) k → singularSubspaces (quadTail r qA) k := fun W =>
    ⟨W.1 ⟨k - 1, by omega⟩, by rw [W.2.1]; simp only; omega, W.2.2.2 _⟩
  have hfib : ∀ X : singularSubspaces (quadTail r qA) k,
      Nat.card {W // top W = X} = Nat.card (flagsWith (· ≤ X.1) k) := by
    intro X
    refine Nat.card_congr
      { toFun := fun W => ⟨W.1.1, W.1.2.1, W.1.2.2.1, fun i => ?_⟩
        invFun := fun F => ⟨⟨F.1, F.2.1, F.2.2.1, fun i x hx => X.2.2 x (F.2.2.2 i hx)⟩, ?_⟩
        left_inv := fun W => rfl
        right_inv := fun F => rfl }
    · have h : (W.1.1 ⟨k - 1, by omega⟩ : Submodule K ((Fin r ⊕ Fin r → K) × A)) = X.1 :=
        congrArg Subtype.val W.2
      rw [← h]
      exact W.1.2.2.1 (Fin.le_def.2 (by simp only; omega))
    · apply Subtype.ext
      exact eq_of_le_of_finrank_eq (F.2.2.2 _) (by rw [F.2.1, X.2.1]; simp only; omega)
  have hF : ∀ X : singularSubspaces (quadTail r qA) k,
      (Nat.card (flagsWith (· ≤ X.1) k) : ℚ) =
        ∏ j ∈ Finset.range k, (((Nat.card K : ℚ) ^ k - (Nat.card K : ℚ) ^ j) /
          ((Nat.card K : ℚ) ^ (j + 1) - (Nat.card K : ℚ) ^ j)) := by
    intro X
    have h := card_flagsWith_le X.1
    rw [X.2.1] at h
    exact h
  have hsig := Nat.card_congr (Equiv.sigmaFiberEquiv top)
  rw [Nat.card_sigma] at hsig
  rw [← hsig, Nat.cast_sum, Finset.sum_congr rfl fun X _ =>
    show ((Nat.card {W // top W = X} : ℕ) : ℚ) = ∏ j ∈ Finset.range k,
      (((Nat.card K : ℚ) ^ k - (Nat.card K : ℚ) ^ j) /
        ((Nat.card K : ℚ) ^ (j + 1) - (Nat.card K : ℚ) ^ j)) by rw [hfib X]; exact hF X,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]

omit hani hreg in
theorem card_singularSubspaces_zero_tail :
    Nat.card (singularSubspaces (quadTail r qA) 0) = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨⊥, finrank_bot K _, fun x hx => by rw [(mem_bot K).1 hx, QuadraticMap.map_zero]⟩, ?_⟩
  rintro ⟨X, hX, -⟩
  exact Subtype.ext (Submodule.finrank_eq_zero.1 hX)

theorem card_singularSubspaces_tail [Finite K] {k : ℕ} (hk : k ≤ r) :
    (Nat.card (singularSubspaces (quadTail r qA) k) : ℚ) =
      (∏ j ∈ Finset.range k, (((Nat.card K : ℚ) ^ (r - j) - 1) *
        ((Nat.card K : ℚ) ^ (r + finrank K A - j - 1) + 1))) /
        ∏ i ∈ Finset.Icc 1 k, ((Nat.card K : ℚ) ^ i - 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [card_singularSubspaces_zero_tail, Finset.prod_range_zero, Finset.Icc_eq_empty (by omega),
      Finset.prod_empty, Nat.cast_one, div_one]
  set q : ℚ := (Nat.card K : ℚ) with hqdef
  have hq : 1 < q := by rw [hqdef]; exact_mod_cast Finite.one_lt_card
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q - 1 ≠ 0 := by linarith
  have hFk : ∏ j ∈ Finset.range k, ((q ^ k - q ^ j) / (q ^ (j + 1) - q ^ j)) =
      ∏ j ∈ Finset.range k, ((q ^ (k - j) - 1) / (q - 1)) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [show q ^ k = q ^ j * q ^ (k - j) by rw [← pow_add]; congr 1; omega, pow_succ]
    rw [show q ^ j * q ^ (k - j) - q ^ j = q ^ j * (q ^ (k - j) - 1) by ring,
      show q ^ j * q - q ^ j = q ^ j * (q - 1) by ring, mul_div_mul_left _ _ (pow_ne_zero _ hq0)]
  have hpos : ∀ m, 1 ≤ m → (0 : ℚ) < q ^ m - 1 := fun m hm => by
    have := one_lt_pow₀ hq (by omega : m ≠ 0)
    linarith
  have hFne : ∏ j ∈ Finset.range k, ((q ^ (k - j) - 1) / (q - 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j hj => by
      rw [Finset.mem_range] at hj
      exact div_ne_zero (hpos _ (by omega)).ne' hq1
  have h := card_singularFlags_eq_mul_tail (K := K) (r := r) (qA := qA) hk0
  rw [card_singularFlags_tail hani hreg hk, ← hqdef, hFk] at h
  rw [eq_div_iff hFne |>.mpr h.symm, ← Finset.prod_div_distrib]
  rw [Finset.prod_congr rfl fun j _ => div_div_div_cancel_right₀ hq1 _ _, Finset.prod_div_distrib,
    prod_range_pow_sub_one]

end Tail


theorem orthogonal_geometry_tail_singular_subspace_count {K : Type*} [Field K] [Finite K]
    {A : Type*} [AddCommGroup A] [Module K A] [FiniteDimensional K A] {r : ℕ} (hr : 1 ≤ r)
    {qA : QuadraticForm K A} (hani : qA.Anisotropic) (hreg : (polarBilin qA).Nondegenerate)
    {k : ℕ} (hk : k ≤ r) :
    (Nat.card (singularSubspaces (quadTail r qA) k) : ℚ) =
        (∏ j ∈ Finset.range k, (((Nat.card K : ℚ) ^ (r - j) - 1) *
          ((Nat.card K : ℚ) ^ (r + finrank K A - j - 1) + 1))) /
          ∏ i ∈ Finset.Icc 1 k, ((Nat.card K : ℚ) ^ i - 1) ∧
      (Nat.card (singularFlags (quadTail r qA) k) : ℚ) =
        ∏ j ∈ Finset.range k, (((Nat.card K : ℚ) ^ (r - j) - 1) *
          ((Nat.card K : ℚ) ^ (r + finrank K A - j - 1) + 1) / ((Nat.card K : ℚ) - 1)) ∧
      (Nat.card (singularSubspaces (quadTail r qA) 1) : ℚ) =
        (∑ i ∈ Finset.range r, (Nat.card K : ℚ) ^ i) *
          ((Nat.card K : ℚ) ^ (r + finrank K A - 1) + 1) ∧
      (Nat.card (singularSubspaces (quadTail r qA) r) : ℚ) =
        ∏ i ∈ Finset.Icc (finrank K A) (r + finrank K A - 1), ((Nat.card K : ℚ) ^ i + 1) := by
  have hq : (1 : ℚ) < Nat.card K := by exact_mod_cast Finite.one_lt_card
  refine ⟨card_singularSubspaces_tail hani hreg hk, card_singularFlags_tail hani hreg hk, ?_, ?_⟩
  ·
    rw [card_singularSubspaces_tail hani hreg hr, Finset.prod_range_one, Finset.Icc_self,
      Finset.prod_singleton, pow_one, Nat.sub_zero, Nat.sub_zero, geom_sum_eq hq.ne' r]
    have hq1 : (Nat.card K : ℚ) - 1 ≠ 0 := by linarith
    field_simp
  ·
    have hne : ∏ i ∈ Finset.Icc 1 r, ((Nat.card K : ℚ) ^ i - 1) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i hi => by
        have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
        have := one_lt_pow₀ hq (by omega : i ≠ 0)
        linarith
    rw [card_singularSubspaces_tail hani hreg le_rfl, Finset.prod_mul_distrib,
      prod_range_pow_sub_one, mul_div_cancel_left₀ _ hne]
    have hrefl : ∏ j ∈ Finset.range r, ((Nat.card K : ℚ) ^ (r + finrank K A - j - 1) + 1) =
        ∏ j ∈ Finset.range r, ((Nat.card K : ℚ) ^ (finrank K A + j) + 1) := by
      rw [← Finset.prod_range_reflect (fun j => (Nat.card K : ℚ) ^ (finrank K A + j) + 1) r]
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      congr 2
      omega
    have hIco : ∏ i ∈ Finset.Ico (finrank K A) (finrank K A + r), ((Nat.card K : ℚ) ^ i + 1) =
        ∏ j ∈ Finset.range r, ((Nat.card K : ℚ) ^ (finrank K A + j) + 1) := by
      rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel_left]
    rw [hrefl, ← hIco]
    congr 1
    ext i
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

module

public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex
import TauCeti.Algebra.Group.Units.Basic
public import CFSG.ClassicalGroups.Orthogonal.Models

public section

namespace CFSG.ClassicalInvolution

open TauCeti QuadraticMap CliffordAlgebra CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin

section Generic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem prod_map_reflect_apply_of_forall_polar_eq_zero {l : List V} {x : V}
    (h : ∀ u ∈ l, polar Q u x = 0) : (l.map (reflect Q)).prod x = x := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    rw [List.map_cons, List.prod_cons, LinearEquiv.mul_apply,
      ih (fun u hu => h u (List.mem_cons_of_mem _ hu)),
      reflect_apply_of_polar_eq_zero (h w List.mem_cons_self)]

theorem prod_map_reflect_apply_of_mem {l : List V} (hl0 : ∀ a ∈ l, Q a ≠ 0)
    (hpair : l.Pairwise (fun u v => polar Q u v = 0)) {v : V} (hv : v ∈ l) :
    (l.map (reflect Q)).prod v = -v := by
  induction l with
  | nil => simp at hv
  | cons w l ih =>
    rw [List.pairwise_cons] at hpair
    obtain ⟨hw, hpair'⟩ := hpair
    rw [List.map_cons, List.prod_cons, LinearEquiv.mul_apply]
    rcases List.mem_cons.1 hv with rfl | hvl
    · rw [prod_map_reflect_apply_of_forall_polar_eq_zero
        (fun u hu => by rw [polar_comm]; exact hw u hu),
        reflect_apply (hl0 _ List.mem_cons_self), polar_self_eq_two_mul,
        mul_div_cancel_right₀ _ (hl0 _ List.mem_cons_self)]
      module
    · rw [ih (fun a ha => hl0 a (List.mem_cons_of_mem _ ha)) hpair' hvl, map_neg,
        reflect_apply_of_polar_eq_zero (hw v hvl)]

theorem span_eq_top_of_pairwise_polar [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) {l : List V}
    (hl0 : ∀ a ∈ l, Q a ≠ 0) (hpair : l.Pairwise (fun u v => polar Q u v = 0))
    (hlen : l.length = Module.finrank K V) : Submodule.span K {v | v ∈ l} = ⊤ := by
  have hortho : LinearMap.BilinForm.iIsOrtho (polarBilin Q) l.get := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact (List.pairwise_iff_get.1 hpair i j h)
    · change polar Q (l.get i) (l.get j) = 0
      rw [polar_comm]
      exact (List.pairwise_iff_get.1 hpair j i h)
  have hli : LinearIndependent K l.get := by
    refine LinearMap.BilinForm.linearIndependent_of_iIsOrtho hortho fun i => ?_
    change polar Q (l.get i) (l.get i) ≠ 0
    rw [polar_self_eq_two_mul]
    exact mul_ne_zero h2 (hl0 _ (List.get_mem l i))
  have := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hlen])
  rw [← this]
  congr 1
  ext v
  simp [List.mem_iff_get]

theorem prod_map_reflect_eq_neg {l : List V} (hl0 : ∀ a ∈ l, Q a ≠ 0)
    (hpair : l.Pairwise (fun u v => polar Q u v = 0)) (hspan : Submodule.span K {v | v ∈ l} = ⊤) :
    (l.map (reflect Q)).prod = LinearEquiv.neg K := by
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext_on hspan (fun v hv => ?_)
  exact prod_map_reflect_apply_of_mem hl0 hpair hv

end Generic

section Scalars

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eq_one_or_eq_neg_of_mem_scalars {g : V ≃ₗ[K] V} (hg : g ∈ scalars K V)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hv : ∃ v, Q v ≠ 0) :
    g = 1 ∨ g = LinearEquiv.neg K := by
  obtain ⟨c, hc⟩ := mem_scalars.1 hg
  obtain ⟨v, hv⟩ := hv
  have h1 : Q (c • v) = Q v := by rw [← hc v]; exact map_of_mem hgO v
  rw [map_smul_eq_sq] at h1
  have hc2 : c * c = 1 := mul_right_cancel₀ hv (by linear_combination h1)
  rcases mul_self_eq_one_iff.1 hc2 with rfl | rfl
  · left
    ext w
    simp [hc]
  · right
    ext w
    simp [hc]

theorem eq_one_or_eq_neg_of_mem_scalars_subgroupOf {g : elementaryGroup Q}
    (hg : g ∈ (scalars K V).subgroupOf (elementaryGroup Q)) (hv : ∃ v, Q v ≠ 0) :
    (g : V ≃ₗ[K] V) = 1 ∨ (g : V ≃ₗ[K] V) = LinearEquiv.neg K :=
  eq_one_or_eq_neg_of_mem_scalars (Subgroup.mem_subgroupOf.1 hg)
    (elementaryGroup_le_orthogonalGroup Q g.2) hv

theorem card_scalars_subgroupOf_elementaryGroup_of_neg_mem (h2 : (2 : K) ≠ 0)
    (hv : ∃ v, Q v ≠ 0) (hneg : (LinearEquiv.neg K : V ≃ₗ[K] V) ∈ elementaryGroup Q) :
    Nat.card ((scalars K V).subgroupOf (elementaryGroup Q)) = 2 := by
  have hnegS : (LinearEquiv.neg K : V ≃ₗ[K] V) ∈ scalars K V :=
    mem_scalars.2 ⟨-1, fun w => by simp⟩
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨⟨LinearEquiv.neg K, hneg⟩, Subgroup.mem_subgroupOf.2 hnegS⟩, ?_, ?_⟩
  · intro h
    obtain ⟨v, hv⟩ := hv
    have hv0 : v ≠ 0 := fun h0 => hv (by rw [h0, QuadraticMap.map_zero])
    have := congrArg (fun x : (scalars K V).subgroupOf (elementaryGroup Q) =>
      ((x : elementaryGroup Q) : V ≃ₗ[K] V) v) h
    simp only at this
    have h' : v = -v := by simpa using this
    apply hv0
    have h3 : (2 : K) • v = 0 := by rw [two_smul]; nth_rewrite 1 [h']; exact neg_add_cancel v
    exact (smul_eq_zero.1 h3).resolve_left h2
  · ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases eq_one_or_eq_neg_of_mem_scalars_subgroupOf g.2 hv with h | h
    · left
      exact Subtype.ext (Subtype.ext h)
    · right
      exact Subtype.ext (Subtype.ext h)

theorem card_scalars_subgroupOf_elementaryGroup_of_neg_not_mem (hv : ∃ v, Q v ≠ 0)
    (hneg : (LinearEquiv.neg K : V ≃ₗ[K] V) ∉ elementaryGroup Q) :
    Nat.card ((scalars K V).subgroupOf (elementaryGroup Q)) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  have hone : ∀ x : (scalars K V).subgroupOf (elementaryGroup Q), x = 1 := fun x => by
    rcases eq_one_or_eq_neg_of_mem_scalars_subgroupOf x.2 hv with h | h
    · exact Subtype.ext (Subtype.ext h)
    · exact absurd (h ▸ (x : elementaryGroup Q).2) hneg
  exact ⟨⟨fun x y => by rw [hone x, hone y]⟩, ⟨1⟩⟩

end Scalars

section Neg

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} [Finite K] [Invertible (2 : K)]

theorem neg_mem_elementaryGroup_iff (hQ : (polarBilin Q).Nondegenerate) {P₁ P₂ P₃ : HypPair Q}
    (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) {l : List V}
    (hl0 : ∀ a ∈ l, Q a ≠ 0) (hpair : l.Pairwise (fun u v => polar Q u v = 0))
    (hspan : Submodule.span K {v | v ∈ l} = ⊤) (hev : Even l.length) :
    (LinearEquiv.neg K : V ≃ₗ[K] V) ∈ elementaryGroup Q ↔ IsSquare (l.map Q).prod := by
  classical
  have hprod := prod_map_reflect_eq_neg hl0 hpair hspan
  constructor
  · intro hneg
    have hQ' : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
    have hnegO : (LinearEquiv.neg K : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      QuadraticMap.neg_mem_orthogonalGroup Q
    obtain ⟨-, hiff⟩ := orthogonalGroup_index_four hQ h₁₂ h₁₃ h₂₃
    have hΦ := (hiff ⟨_, hnegO⟩).1 hneg
    rw [detSpinorNorm_apply] at hΦ
    have hθ1 : orthogonalSpinorNorm Q hQ' ⟨LinearEquiv.neg K, hnegO⟩ = 1 :=
      congrArg Prod.snd hΦ
    let reflO : V → TauCeti.QuadraticMap.orthogonalGroup Q :=
      fun v => ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩
    let unitQ : V → Kˣ := fun v => if h : Q v = 0 then 1 else Units.mk0 (Q v) h
    have hgprod : (⟨LinearEquiv.neg K, hnegO⟩ : TauCeti.QuadraticMap.orthogonalGroup Q) =
        (l.map reflO).prod := by
      apply Subtype.ext
      rw [Subgroup.val_list_prod, List.map_map]
      exact hprod.symm
    have hfactor : ∀ v ∈ l, orthogonalSpinorNorm Q hQ' (reflO v) = squareClassHom (unitQ v) := by
      intro v hv
      have hv0 : Q v ≠ 0 := hl0 v hv
      let _ : Invertible (Q v) := invertibleOfNonzero hv0
      have hr : reflO v = TauCeti.QuadraticMap.reflectionOrthogonal Q v :=
        Subtype.ext (coe_reflectionOrthogonal_eq_reflect v).symm
      rw [hr, orthogonalSpinorNorm_reflectionOrthogonal]
      congr 1
      apply Units.ext
      simp [unitQ, hv0]
    have hθ : orthogonalSpinorNorm Q hQ' (l.map reflO).prod =
        squareClassHom (l.map unitQ).prod := by
      rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
      congr 1
      exact List.map_congr_left fun v hv => hfactor v hv
    rw [hgprod, hθ] at hθ1
    have hker : (l.map unitQ).prod ∈ (squareClassHom (K := K)).ker := hθ1
    rw [ker_squareClassHom, Subgroup.mem_square, ← isSquare_units_val_iff] at hker
    have hval : (((l.map unitQ).prod : Kˣ) : K) = (l.map Q).prod := by
      have := map_list_prod (Units.coeHom K) (l.map unitQ)
      rw [List.map_map] at this
      change (((l.map unitQ).prod : Kˣ) : K) = _ at this
      rw [this]
      congr 1
      refine List.map_congr_left fun v hv => ?_
      simp [unitQ, hl0 v hv]
    rwa [hval] at hker
  · intro hsq
    rw [← hprod]
    exact prod_map_reflect_mem_elementaryGroup hQ h₁₂ hl0 hev hsq

end Neg

section HypList

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_hyp_hyp_of_orth {P P' : HypPair Q} (h : P.Orth P') (ε δ : K) :
    polar Q (P.e + ε • P.f) (P'.e + δ • P'.f) = 0 := by
  simp [polar_add_left, polar_add_right, h.ee, h.ef, h.fe, h.ff]

theorem polar_hyp_add_hyp_sub (P : HypPair Q) :
    polar Q (P.e + (1 : K) • P.f) (P.e + (-1 : K) • P.f) = 0 := by
  simp [polar_add_left, polar_add_right, P.polar_ee, P.polar_ef, P.polar_fe, P.polar_ff]

def hypList {m : ℕ} (P : Fin m → HypPair Q) : List V :=
  (List.finRange m).map (fun i => (P i).e + (1 : K) • (P i).f) ++
    (List.finRange m).map (fun i => (P i).e + (-1 : K) • (P i).f)

variable {m : ℕ} {P : Fin m → HypPair Q}

theorem hypList_map_ne_zero (a : V) (ha : a ∈ hypList P) : Q a ≠ 0 := by
  simp only [hypList, List.mem_append, List.mem_map] at ha
  rcases ha with ⟨i, -, rfl⟩ | ⟨i, -, rfl⟩
  · rw [map_hypPair_add_smul]; exact one_ne_zero
  · rw [map_hypPair_add_smul]; exact neg_ne_zero.2 one_ne_zero

theorem hypList_pairwise (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    (hypList P).Pairwise (fun u v => polar Q u v = 0) := by
  have hf : ∀ ε δ : K, ∀ i j : Fin m, i ≠ j →
      polar Q ((P i).e + ε • (P i).f) ((P j).e + δ • (P j).f) = 0 := fun ε δ i j hij =>
    polar_hyp_hyp_of_orth (hP i j hij) ε δ
  rw [hypList, List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · refine List.pairwise_map.2 (List.Nodup.pairwise_of_forall_ne (List.nodup_finRange m) ?_)
    intro i _ j _ hij
    exact hf 1 1 i j hij
  · refine List.pairwise_map.2 (List.Nodup.pairwise_of_forall_ne (List.nodup_finRange m) ?_)
    intro i _ j _ hij
    exact hf (-1) (-1) i j hij
  · intro x hx y hy
    simp only [List.mem_map] at hx hy
    obtain ⟨i, -, rfl⟩ := hx
    obtain ⟨j, -, rfl⟩ := hy
    by_cases hij : i = j
    · subst hij
      exact polar_hyp_add_hyp_sub (P i)
    · exact hf 1 (-1) i j hij

theorem hypList_length : (hypList P).length = 2 * m := by
  simp [hypList, two_mul]

theorem hypList_prod_map : ((hypList P).map Q).prod = (-1) ^ m := by
  rw [hypList, List.map_append, List.prod_append, List.map_map, List.map_map]
  have h1 : (List.map (⇑Q ∘ fun i => (P i).e + (1 : K) • (P i).f) (List.finRange m)).prod = 1 := by
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact map_hypPair_add_smul (P i) 1
  have h2 : (List.map (⇑Q ∘ fun i => (P i).e + (-1 : K) • (P i).f) (List.finRange m)).prod =
      (-1) ^ m := by
    have : List.map (⇑Q ∘ fun i => (P i).e + (-1 : K) • (P i).f) (List.finRange m) =
        List.replicate m (-1 : K) := by
      refine List.eq_replicate_iff.2 ⟨by simp, fun x hx => ?_⟩
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact map_hypPair_add_smul (P i) (-1)
    rw [this, List.prod_replicate]
  rw [h1, h2, one_mul]

end HypList

section Models

open CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K]

theorem neg_mem_elementaryGroup_quadPlus_iff (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 3 ≤ n) :
    (LinearEquiv.neg K : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) ∈
        elementaryGroup (quadPlus n K) ↔ IsSquare ((-1 : K) ^ n) := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hP : ∀ i j : Fin n, i ≠ j → (plusPair K i).Orth (plusPair K j) := fun i j hij =>
    plusPair_orth hij
  have hlen : (hypList (plusPair K : Fin n → HypPair (quadPlus n K))).length =
      Module.finrank K (Fin n ⊕ Fin n → K) := by
    rw [hypList_length, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin,
      two_mul]
  have hspan := span_eq_top_of_pairwise_polar h2
    (hypList_map_ne_zero (P := (plusPair K : Fin n → HypPair (quadPlus n K))))
    (hypList_pairwise hP) hlen
  have := neg_mem_elementaryGroup_iff (nondegenerate_polarBilin_quadPlus n K)
    (P₁ := plusPair K ⟨0, by omega⟩) (P₂ := plusPair K ⟨1, by omega⟩)
    (P₃ := plusPair K ⟨2, by omega⟩) (plusPair_orth (by simp [Fin.ext_iff]))
    (plusPair_orth (by simp [Fin.ext_iff])) (plusPair_orth (by simp [Fin.ext_iff]))
    (hypList_map_ne_zero (P := (plusPair K : Fin n → HypPair (quadPlus n K))))
    (hypList_pairwise hP) hspan (by rw [hypList_length]; exact even_two_mul n)
  rw [this, hypList_prod_map]

section Minus

variable {b c : K}

def planeVec₀ (n : ℕ) (K : Type) [Field K] : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K :=
  Pi.single (Sum.inr (Sum.inr 0)) 1

def planeVec₁ (n : ℕ) (b : K) : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K :=
  (-b) • Pi.single (Sum.inr (Sum.inr 0)) 1 + (2 : K) • Pi.single (Sum.inr (Sum.inr 1)) 1

omit [Finite K] in
theorem quadMinus_planeVec₀ (n : ℕ) : quadMinus n K b c (planeVec₀ n K) = 1 := by
  simp [quadMinus_apply, planeVec₀]

omit [Finite K] in
theorem quadMinus_planeVec₁ (n : ℕ) : quadMinus n K b c (planeVec₁ n b) = 4 * c - b ^ 2 := by
  simp [quadMinus_apply, planeVec₁]
  ring

omit [Finite K] in
theorem polar_planeVec₀_planeVec₁ (n : ℕ) :
    polar (quadMinus n K b c) (planeVec₀ n K) (planeVec₁ n b) = 0 := by
  simp [polar, quadMinus_apply, planeVec₀, planeVec₁]
  ring

omit [Finite K] in
theorem polar_hypList_of_plane (n : ℕ) {y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K}
    (hy1 : ∀ i, y (Sum.inl i) = 0) (hy2 : ∀ i, y (Sum.inr (Sum.inl i)) = 0)
    {x : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K}
    (hx : x ∈ hypList (minusPair K b c : Fin (n - 1) → HypPair (quadMinus n K b c))) :
    polar (quadMinus n K b c) x y = 0 := by
  simp only [hypList, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨i, -, rfl⟩ | ⟨i, -, rfl⟩ <;>
    simp [polar_add_left, minusPair_e, minusPair_f, polar_single_inl_quadMinus,
      polar_single_inr_quadMinus, hy1, hy2]

theorem neg_mem_elementaryGroup_quadMinus_iff (h2 : (2 : K) ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hn : 4 ≤ n) :
    (LinearEquiv.neg K : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ≃ₗ[K]
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)) ∈ elementaryGroup (quadMinus n K b c) ↔
      IsSquare ((-1 : K) ^ (n - 1) * (4 * c - b ^ 2)) := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hP : ∀ i j : Fin (n - 1), i ≠ j →
      (minusPair K b c i).Orth (minusPair K b c j) := fun i j hij => minusPair_orth hij
  have h4c : 4 * c - b ^ 2 ≠ 0 := by
    intro h
    apply hirr (-b / 2)
    field_simp
    linear_combination h
  set P : Fin (n - 1) → HypPair (quadMinus n K b c) := minusPair K b c with hPdef
  set l : List (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :=
    hypList P ++ [planeVec₀ n K, planeVec₁ n b] with hl
  have hpv0 : ∀ i, planeVec₀ n K (Sum.inl i) = 0 := fun i => by simp [planeVec₀]
  have hpv0' : ∀ i, planeVec₀ n K (Sum.inr (Sum.inl i)) = 0 := fun i => by simp [planeVec₀]
  have hpv1 : ∀ i, planeVec₁ n b (Sum.inl i) = 0 := fun i => by simp [planeVec₁]
  have hpv1' : ∀ i, planeVec₁ n b (Sum.inr (Sum.inl i)) = 0 := fun i => by simp [planeVec₁]
  have hl0 : ∀ a ∈ l, quadMinus n K b c a ≠ 0 := by
    intro a ha
    rw [hl, List.mem_append] at ha
    rcases ha with ha | ha
    · exact hypList_map_ne_zero a ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · rw [quadMinus_planeVec₀]; exact one_ne_zero
      · rw [quadMinus_planeVec₁]; exact h4c
  have hpair : l.Pairwise (fun u v => polar (quadMinus n K b c) u v = 0) := by
    rw [hl, List.pairwise_append]
    refine ⟨hypList_pairwise hP, ?_, ?_⟩
    · simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]
      exact polar_planeVec₀_planeVec₁ n
    · intro x hx y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact polar_hypList_of_plane n hpv0 hpv0' hx
      · exact polar_hypList_of_plane n hpv1 hpv1' hx
  have hlen : l.length = Module.finrank K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) := by
    rw [hl, List.length_append, hypList_length, Module.finrank_fintype_fun_eq_card,
      Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    simp
    omega
  have hspan := span_eq_top_of_pairwise_polar h2 hl0 hpair hlen
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  have := neg_mem_elementaryGroup_iff hnd
    (P₁ := minusPair K b c ⟨0, by omega⟩) (P₂ := minusPair K b c ⟨1, by omega⟩)
    (P₃ := minusPair K b c ⟨2, by omega⟩) (minusPair_orth (by simp [Fin.ext_iff]))
    (minusPair_orth (by simp [Fin.ext_iff])) (minusPair_orth (by simp [Fin.ext_iff]))
    hl0 hpair hspan (by
      rw [hl, List.length_append, hypList_length]
      exact ⟨n - 1 + 1, by simp; omega⟩)
  rw [this, hl, List.map_append, List.prod_append, hypList_prod_map]
  simp [quadMinus_planeVec₀, quadMinus_planeVec₁]


end Minus

section Odd

omit [Finite K] in
theorem det_neg_eq {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    LinearMap.det (LinearEquiv.neg K : V ≃ₗ[K] V).toLinearMap = (-1 : K) ^ Module.finrank K V := by
  have : (LinearEquiv.neg K : V ≃ₗ[K] V).toLinearMap = (-1 : K) • LinearMap.id := by
    ext v
    simp
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]

theorem neg_not_mem_elementaryGroup_quadOdd (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 3 ≤ n) :
    (LinearEquiv.neg K : (Fin n ⊕ Fin n ⊕ Unit → K) ≃ₗ[K] (Fin n ⊕ Fin n ⊕ Unit → K)) ∉
      elementaryGroup (quadOdd n K) := by
  intro hneg
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hnegO : (LinearEquiv.neg K : (Fin n ⊕ Fin n ⊕ Unit → K) ≃ₗ[K] (Fin n ⊕ Fin n ⊕ Unit → K)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadOdd n K) :=
    QuadraticMap.neg_mem_orthogonalGroup _
  obtain ⟨-, hiff⟩ := orthogonalGroup_index_four (nondegenerate_polarBilin_quadOdd n K h2)
    (P₁ := oddPair K ⟨0, by omega⟩) (P₂ := oddPair K ⟨1, by omega⟩)
    (P₃ := oddPair K ⟨2, by omega⟩) (oddPair_orth (by simp [Fin.ext_iff]))
    (oddPair_orth (by simp [Fin.ext_iff])) (oddPair_orth (by simp [Fin.ext_iff]))
  have hΦ := (hiff ⟨_, hnegO⟩).1 hneg
  rw [detSpinorNorm_apply] at hΦ
  have hdet := congrArg Prod.fst hΦ
  have hdet' : LinearEquiv.det (LinearEquiv.neg K : (Fin n ⊕ Fin n ⊕ Unit → K) ≃ₗ[K]
      (Fin n ⊕ Fin n ⊕ Unit → K)) = 1 := by
    simpa [QuadraticMap.orthogonalDet_apply] using hdet
  have h1 := congrArg (fun u : Kˣ => (u : K)) hdet'
  simp only [LinearEquiv.coe_det, Units.val_one] at h1
  rw [det_neg_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_unit] at h1
  have hodd : Odd (n + (n + 1)) := ⟨n, by omega⟩
  rw [hodd.neg_one_pow] at h1
  apply h2
  linear_combination -h1

end Odd

end Models

end CFSG.ClassicalInvolution

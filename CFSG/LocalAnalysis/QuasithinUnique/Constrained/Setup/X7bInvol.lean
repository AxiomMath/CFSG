module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bTensor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Iso

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7
open CFSG.QuasithinUnique.Setup.X7a (kron kron_apply kron_mul kron_one kron_transpose)

section Jordan

open Module

theorem exists_perm_basis {k V : Type*} [Field k] [CharP k 2] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V] (T : V →ₗ[k] V) (hT : ∀ v, T (T v) = v) :
    ∃ (X : Type) (_ : Fintype X) (b : Module.Basis X k V) (σ : Equiv.Perm X),
      σ * σ = 1 ∧ ∀ x, T (b x) = b (σ x) := by
  classical
  have h2 : ∀ v : V, v + v = 0 := by
    intro v
    have : (2 : k) • v = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
    rwa [two_smul] at this
  let N : V →ₗ[k] V := T - LinearMap.id
  have hN : ∀ v, N v = T v - v := fun v => rfl
  have hTN : ∀ v, T v = v + N v := fun v => by rw [hN]; abel
  have hNN : ∀ v, N (N v) = 0 := by
    intro v
    rw [hN, hN, map_sub, hT]
    have h3 := h2 v
    have h4 := h2 (T v)
    calc v - T v - (T v - v) = (v + v) - (T v + T v) := by abel
      _ = 0 := by rw [h3, h4, sub_zero]
  set K := LinearMap.ker N with hK
  set B := LinearMap.range N with hB
  have hBK : B ≤ K := by
    rintro _ ⟨v, rfl⟩
    exact LinearMap.mem_ker.mpr (hNN v)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl K
  have hinjC : Function.Injective (N.domRestrict C) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hc' : (c : V) ∈ K ⊓ C := ⟨LinearMap.mem_ker.mpr hc, c.2⟩
    rw [hC.inf_eq_bot] at hc'
    exact Subtype.ext ((Submodule.mem_bot k).mp hc')
  obtain ⟨D', hD'⟩ := Submodule.exists_isCompl (B.comap K.subtype)
  set r := Module.finrank k C with hr
  set t := Module.finrank k D' with ht
  let bC : Module.Basis (Fin r) k C := Module.finBasis k C
  let bD : Module.Basis (Fin t) k D' := Module.finBasis k D'
  have d1 : Module.finrank k B + Module.finrank k K = Module.finrank k V :=
    LinearMap.finrank_range_add_finrank_ker N
  have d2 : Module.finrank k K + Module.finrank k C = Module.finrank k V :=
    Submodule.finrank_add_eq_of_isCompl hC
  have d3 : Module.finrank k (B.comap K.subtype) = Module.finrank k B :=
    (Submodule.comapSubtypeEquivOfLe hBK).finrank_eq
  have d4 : Module.finrank k (B.comap K.subtype) + Module.finrank k D' = Module.finrank k K :=
    Submodule.finrank_add_eq_of_isCompl hD'
  have hcardX : Fintype.card ((Fin r × Bool) ⊕ Fin t) = Module.finrank k V := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega
  let c : Fin r → V := fun j => (bC j : V)
  let f : Fin t → V := fun l => ((bD l : D') : K)
  let e : ((Fin r × Bool) ⊕ Fin t) → V :=
    Sum.elim (fun p => if p.2 then c p.1 else T (c p.1)) f
  have hNf : ∀ l, N (f l) = 0 := fun l => LinearMap.mem_ker.mp ((bD l : D') : K).2
  have hNc : LinearIndependent k (fun j => N (c j)) := by
    have := bC.linearIndependent.map' (N.domRestrict C) (LinearMap.ker_eq_bot.mpr hinjC)
    exact this
  have hf : LinearIndependent k f := by
    have hinj : Function.Injective (K.subtype ∘ₗ D'.subtype) :=
      Subtype.val_injective.comp Subtype.val_injective
    exact bD.linearIndependent.map' (K.subtype ∘ₗ D'.subtype) (LinearMap.ker_eq_bot.mpr hinj)
  have hdisj : ∀ y ∈ B, ∀ (w : V), w ∈ Submodule.span k (Set.range f) → y + w = 0 → y = 0 := by
    intro y hy w hw hyw
    have hspan : Submodule.span k (Set.range f) ≤ D'.map K.subtype := by
      rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact ⟨(bD l : D'), (bD l).2, rfl⟩
    have hyD : y ∈ D'.map K.subtype := by
      have : y = -w := eq_neg_of_add_eq_zero_left hyw
      rw [this]
      exact neg_mem (hspan hw)
    obtain ⟨d', hd', hdy⟩ := hyD
    have hyB' : K.subtype d' ∈ B := hdy ▸ hy
    have hd'K : d' ∈ (B.comap K.subtype) ⊓ D' := ⟨hyB', hd'⟩
    rw [hD'.inf_eq_bot] at hd'K
    have : d' = 0 := (Submodule.mem_bot k).mp hd'K
    rw [← hdy, this]
    rfl
  have hli : LinearIndependent k e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at hg
    simp only [Fintype.sum_bool, e, Sum.elim_inl, Sum.elim_inr, ite_true, Bool.false_eq_true,
      ite_false] at hg
    have hNT : ∀ j, N (T (c j)) = N (c j) := fun j => by
      rw [hTN (c j), map_add, hNN, add_zero]
    have hA := congrArg N hg
    simp only [map_add, map_sum, map_smul, hNT, hNf, smul_zero, Finset.sum_const_zero,
      add_zero, map_zero] at hA
    have hA' : ∑ j, (g (Sum.inl (j, true)) + g (Sum.inl (j, false))) • N (c j) = 0 := by
      rw [← hA]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [add_smul]
    have hcoef := Fintype.linearIndependent_iff.mp hNc _ hA'
    have hB' : ∑ j, g (Sum.inl (j, false)) • N (c j) +
        ∑ l, g (Sum.inr l) • f l = 0 := by
      rw [← hg]
      have : ∀ j, g (Sum.inl (j, true)) • c j + g (Sum.inl (j, false)) • T (c j) =
          g (Sum.inl (j, false)) • N (c j) := by
        intro j
        have h0 := hcoef j
        rw [hTN (c j), smul_add, ← add_assoc, ← add_smul, h0, zero_smul, zero_add]
      simp only [this]
    have hyB : ∑ j, g (Sum.inl (j, false)) • N (c j) ∈ B :=
      ⟨∑ j, g (Sum.inl (j, false)) • c j, by simp [map_sum, map_smul]⟩
    have hwS : ∑ l, g (Sum.inr l) • f l ∈ Submodule.span k (Set.range f) :=
      Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    have hy0 := hdisj _ hyB _ hwS hB'
    have hg0 := Fintype.linearIndependent_iff.mp hNc _ hy0
    have hw0 : ∑ l, g (Sum.inr l) • f l = 0 := by
      rw [hy0, zero_add] at hB'
      exact hB'
    have hγ := Fintype.linearIndependent_iff.mp hf _ hw0
    rintro (⟨j, _ | _⟩ | l)
    · exact hg0 j
    · have := hcoef j
      rw [hg0 j] at this
      simpa using this
    · exact hγ l
  have hne : Nonempty ((Fin r × Bool) ⊕ Fin t) := by
    have : 0 < Module.finrank k V := Module.finrank_pos
    rw [← hcardX] at this
    exact Fintype.card_pos_iff.mp this
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcardX
  have hb : ∀ x, b x = e x := fun x => by simp [b]
  let σ : Equiv.Perm ((Fin r × Bool) ⊕ Fin t) :=
    { toFun := Sum.map (fun p => (p.1, !p.2)) id
      invFun := Sum.map (fun p => (p.1, !p.2)) id
      left_inv := by rintro (⟨j, s⟩ | l) <;> simp
      right_inv := by rintro (⟨j, s⟩ | l) <;> simp }
  refine ⟨(Fin r × Bool) ⊕ Fin t, inferInstance, b, σ, ?_, ?_⟩
  · ext x
    rcases x with ⟨j, s⟩ | l <;> simp [σ, Equiv.Perm.mul_apply]
  · intro x
    rw [hb, hb]
    rcases x with ⟨j, _ | _⟩ | l
    · show T (T (c j)) = c j
      exact hT _
    · rfl
    · show T (f l) = f l
      rw [hTN, hNf, add_zero]

end Jordan

section Perm

variable {k : Type*} [Field k] {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem rank_permMat_sub_one (σ : Equiv.Perm κ) (hσ : σ * σ = 1) :
    (permMat k σ - 1 : Matrix κ κ k).rank * 2 + Fintype.card {x // σ x = x} = Fintype.card κ := by
  classical
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun p : Equiv.Perm κ => p x) hσ
    simpa [Equiv.Perm.mul_apply] using this
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  set S : Finset κ := Finset.univ.filter fun x => e x < e (σ x) with hS
  set S' : Finset κ := Finset.univ.filter fun x => e (σ x) < e x with hS'
  set F0 : Finset κ := Finset.univ.filter fun x => σ x = x with hF0
  let A : Matrix κ κ k := permMat k σ - 1
  have hcol : ∀ x y, A.col x y = (if y = σ x then 1 else 0) - (if y = x then 1 else 0) := by
    intro x y
    simp [A, permMat, Matrix.sub_apply, Matrix.one_apply, Matrix.col_apply, eq_comm]
  let cols : S → (κ → k) := fun x => A.col x
  have hspan : Submodule.span k (Set.range A.col) = Submodule.span k (Set.range cols) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rcases lt_trichotomy (e x) (e (σ x)) with h | h | h
      · exact Submodule.subset_span ⟨⟨x, by simp [hS, h]⟩, rfl⟩
      · have hx : σ x = x := (e.injective h).symm
        have : A.col x = 0 := by
          funext y
          rw [hcol, hx]
          simp
        rw [this]
        exact Submodule.zero_mem _
      · have hmem : σ x ∈ S := by simp [hS, hσσ, h]
        have : A.col x = -(A.col (σ x)) := by
          funext y
          simp only [Pi.neg_apply, hcol, hσσ]
          ring
        rw [this]
        exact Submodule.neg_mem _ (Submodule.subset_span ⟨⟨σ x, hmem⟩, rfl⟩)
    · exact Submodule.span_mono (by rintro _ ⟨x, rfl⟩; exact ⟨x, rfl⟩)
  have hli : LinearIndependent k cols := by
    rw [Fintype.linearIndependent_iff]
    intro c hc y
    have hcy := congrFun hc (y : κ)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcy
    have hyS : (y : κ) ∈ S := y.2
    have hterm : ∀ x : S, c x * cols x (y : κ) = if x = y then -c y else 0 := by
      intro x
      have hxS : (x : κ) ∈ S := x.2
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hxS hyS
      show c x * A.col x y = _
      rw [hcol]
      by_cases hxy : x = y
      · subst hxy
        have : (x : κ) ≠ σ x := fun h => by
          rw [← h] at hxS
          exact lt_irrefl _ hxS
        simp [this]
      · have h1 : (y : κ) ≠ x := fun h => hxy (Subtype.ext h.symm)
        have h2 : (y : κ) ≠ σ x := fun h => by
          have h3 : σ y = x := by rw [h, hσσ]
          rw [h3] at hyS
          rw [h] at hyS
          exact lt_asymm hxS hyS
        simp [h1, h2, hxy]
    rw [Finset.sum_congr rfl fun x _ => hterm x] at hcy
    simpa using hcy
  have hrank : A.rank = S.card := by
    rw [Matrix.rank, Matrix.range_mulVecLin, hspan, finrank_span_eq_card hli, Fintype.card_coe]
  have hcardS' : S'.card = S.card := by
    refine Finset.card_bij (fun x _ => σ x) ?_ ?_ ?_
    · intro x hx
      simp only [hS, hS', Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [hσσ]
      exact hx
    · intro x _ y _ h
      have := congrArg σ h
      rwa [hσσ, hσσ] at this
    · intro y hy
      refine ⟨σ y, ?_, hσσ y⟩
      simp only [hS, hS', Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [hσσ]
      exact hy
  have hpart : (Finset.univ : Finset κ) = S ∪ S' ∪ F0 := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_union, hS, hS', hF0, Finset.mem_filter, true_and,
      true_iff]
    rcases lt_trichotomy (e x) (e (σ x)) with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (e.injective h).symm
    · exact Or.inl (Or.inr h)
  have hd1 : Disjoint S S' := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [hS, hS', Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    exact lt_asymm hx hx'
  have hd2 : Disjoint (S ∪ S') F0 := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [hF0, Finset.mem_filter, Finset.mem_univ, true_and] at hx'
    rcases Finset.mem_union.mp hx with h | h
    · simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at h
      rw [hx'] at h
      exact lt_irrefl _ h
    · simp only [hS', Finset.mem_filter, Finset.mem_univ, true_and] at h
      rw [hx'] at h
      exact lt_irrefl _ h
  have hcard : Fintype.card κ = S.card + S'.card + F0.card := by
    rw [← Finset.card_univ, hpart, Finset.card_union_of_disjoint hd2,
      Finset.card_union_of_disjoint hd1]
  have hfix : Fintype.card {x // σ x = x} = F0.card := by
    rw [Fintype.card_subtype]
  rw [hrank, hfix, hcard, hcardS']
  ring


end Perm

section KronRank

variable {k : Type*} [Field k] {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem rank_conj_eq {κ' : Type*} [Fintype κ'] (M : Matrix κ κ k) (P : Matrix κ' κ k)
    (Q : Matrix κ κ' k) (hQP : Q * P = 1) : (P * M * Q).rank = M.rank := by
  refine le_antisymm ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)) ?_
  have : M = Q * (P * M * Q) * P := by
    calc M = (Q * P) * M * (Q * P) := by rw [hQP, Matrix.one_mul, Matrix.mul_one]
      _ = Q * (P * M * Q) * P := by simp only [Matrix.mul_assoc]
  calc M.rank = (Q * (P * M * Q) * P).rank := by rw [← this]
    _ ≤ (Q * (P * M * Q)).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (P * M * Q).rank := Matrix.rank_mul_le_right _ _

theorem exists_perm_conj [CharP k 2] [Nonempty κ] {z : Matrix κ κ k} (hz : z * z = 1) :
    ∃ (σ : Equiv.Perm κ) (P Q : Matrix κ κ k), σ * σ = 1 ∧ P * Q = 1 ∧ Q * P = 1 ∧
      z * P = P * permMat k σ := by
  classical
  let T : (κ → k) →ₗ[k] (κ → k) := Matrix.mulVecLin z
  have hT : ∀ v, T (T v) = v := fun v => by
    simp only [T, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hz, Matrix.one_mulVec]
  obtain ⟨X, _, b, σX, hσX, hTb⟩ := exists_perm_basis T hT
  have hcard : Fintype.card X = Fintype.card κ := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card]
  let eqv : X ≃ κ := Fintype.equivOfCardEq hcard
  let b' : Module.Basis κ k (κ → k) := b.reindex eqv
  let σ : Equiv.Perm κ := (eqv.symm.trans σX).trans eqv
  have hb' : ∀ y, b' y = b (eqv.symm y) := fun y => by simp [b']
  have hσy : ∀ y, eqv.symm (σ y) = σX (eqv.symm y) := fun y => by simp [σ]
  refine ⟨σ, (Pi.basisFun k κ).toMatrix b', b'.toMatrix (Pi.basisFun k κ), ?_,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _, ?_⟩
  · ext y
    have h1 := congrArg (fun p : Equiv.Perm X => p (eqv.symm y)) hσX
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h1 ⊢
    simp [σ, h1]
  · ext i y
    have h1 : T (b' y) = b' (σ y) := by rw [hb', hb', hTb, hσy]
    have h2 : (z * (Pi.basisFun k κ).toMatrix b') i y = T (b' y) i := by
      simp [Matrix.mul_apply, Module.Basis.toMatrix_apply, T, Matrix.mulVec, dotProduct]
    rw [h2, h1]
    simp [Matrix.mul_apply, permMat, Module.Basis.toMatrix_apply]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype κ] [DecidableEq ι] in
theorem kron_permMat (σ : ι → Equiv.Perm κ) :
    kron (fun i => permMat k (σ i)) = permMat k (Equiv.piCongrRight σ) := by
  ext y x
  rw [kron_apply]
  simp only [permMat, Matrix.of_apply]
  rw [Finset.prod_boole]
  simp [funext_iff]

theorem rank_kron_sub_one [CharP k 2] [Nonempty κ] (z : ι → Matrix κ κ k) (hz : ∀ i, z i * z i = 1) :
    (kron z - 1).rank * 2 + ∏ i, (Fintype.card κ - 2 * (z i - 1).rank) =
      Fintype.card κ ^ Fintype.card ι := by
  classical
  choose σ P Q hσ hPQ hQP hzP using fun i => exists_perm_conj (hz i)
  have hz' : ∀ i, z i - 1 = P i * (permMat k (σ i) - 1) * Q i := fun i => by
    have h1 : z i = P i * permMat k (σ i) * Q i := by
      calc z i = z i * (P i * Q i) := by rw [hPQ, Matrix.mul_one]
        _ = (z i * P i) * Q i := by rw [Matrix.mul_assoc]
        _ = P i * permMat k (σ i) * Q i := by rw [hzP]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ, ← h1]
  have hfix : ∀ i, Fintype.card {y // σ i y = y} = Fintype.card κ - 2 * (z i - 1).rank := fun i => by
    have h1 := rank_permMat_sub_one (k := k) (σ i) (hσ i)
    rw [hz' i, rank_conj_eq _ _ _ (hQP i)]
    omega
  have hPk : kron P * kron Q = 1 := by rw [← kron_mul]; simp only [hPQ]; exact kron_one
  have hQk : kron Q * kron P = 1 := by rw [← kron_mul]; simp only [hQP]; exact kron_one
  have hzk : kron z * kron P = kron P * permMat k (Equiv.piCongrRight σ) := by
    rw [← kron_permMat, ← kron_mul, ← kron_mul]
    congr 1
    funext i
    exact hzP i
  have hz'' : kron z - 1 = kron P * (permMat k (Equiv.piCongrRight σ) - 1) * kron Q := by
    have h1 : kron z = kron P * permMat k (Equiv.piCongrRight σ) * kron Q := by
      calc kron z = kron z * (kron P * kron Q) := by rw [hPk, Matrix.mul_one]
        _ = (kron z * kron P) * kron Q := by rw [Matrix.mul_assoc]
        _ = kron P * permMat k (Equiv.piCongrRight σ) * kron Q := by rw [hzk]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPk, ← h1]
  have hσk : Equiv.piCongrRight σ * Equiv.piCongrRight σ = 1 := by
    ext x i
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, Equiv.piCongrRight_apply]
    have := congrArg (fun p : Equiv.Perm κ => p (x i)) (hσ i)
    simpa [Equiv.Perm.mul_apply] using this
  have h2 := rank_permMat_sub_one (k := k) (Equiv.piCongrRight σ) hσk
  rw [hz'', rank_conj_eq _ _ _ hQk]
  have hcardfix : Fintype.card {x : ι → κ // Equiv.piCongrRight σ x = x} =
      ∏ i, Fintype.card {y // σ i y = y} := by
    rw [← Fintype.card_pi]
    refine Fintype.card_congr ?_
    refine (Equiv.subtypeEquivRight fun x => ?_).trans (Equiv.subtypePiEquivPi (p := fun i y => σ i y = y))
    simp [funext_iff]
  rw [hcardfix] at h2
  simp only [hfix] at h2
  simpa [Fintype.card_pi] using h2

theorem one_le_rank_of_ne_zero {m : Type*} [Fintype m] {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix m n k) (hN : N ≠ 0) : 1 ≤ N.rank := by
  rw [Matrix.rank_eq_finrank_span_cols]
  obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hN (by ext i j; exact h i j)
  have hcol : N.col j ≠ 0 := fun h => hij (congrFun h i)
  have hmem : N.col j ∈ Submodule.span k (Set.range N.col) := Submodule.subset_span ⟨j, rfl⟩
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨N.col j, hmem⟩, fun h => hcol (congrArg Subtype.val h)⟩

theorem two_mul_rank_le [CharP k 2] [Nonempty κ] (w : Matrix κ κ k) (hw : w * w = 1) :
    2 * (w - 1).rank ≤ Fintype.card κ := by
  obtain ⟨σ, P, Q, hσ, hPQ, hQP, hwP⟩ := exists_perm_conj hw
  have h1 := rank_permMat_sub_one (k := k) σ hσ
  have h2 : w - 1 = P * (permMat k σ - 1) * Q := by
    have h3 : w = P * permMat k σ * Q := by
      calc w = w * (P * Q) := by rw [hPQ, Matrix.mul_one]
        _ = (w * P) * Q := by rw [Matrix.mul_assoc]
        _ = P * permMat k σ * Q := by rw [hwP]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ, ← h3]
  rw [h2, rank_conj_eq _ _ _ hQP]
  omega

end KronRank

section Apply

variable {F : Type} [Field F] [CharP F 2] [Fintype F] (k : Type*) [Field k] [Algebra F k] [CharP k 2]

omit [CharP k 2] in
theorem natRepS_mul_self {z : antiSp F} (hz : z * z = 1) (i : ℕ) :
    natRepS k i z * natRepS k i z = 1 := by
  rw [← map_mul, hz, map_one]

theorem rank_tensorRepS_sub_one (A : Finset ℕ) {z : antiSp F} (hz : z * z = 1) :
    (tensorRepS k A z - 1).rank * 2 +
        ∏ i : A, (4 - 2 * (natRepS k (i : ℕ) z - 1).rank) = 4 ^ A.card := by
  have := rank_kron_sub_one (k := k) (ι := A) (κ := Fin 4)
    (fun i : A => natRepS k (i : ℕ) z) (fun i => natRepS_mul_self k hz i)
  have e : tensorRepS k A z = kron (fun i : A => natRepS k (i : ℕ) z) := rfl
  rw [e]
  simpa using this

omit [CharP k 2] in
theorem natRepS_ne_one {z : antiSp F} (hz : z ≠ 1) (i : ℕ) : natRepS k i z ≠ 1 := by
  intro h
  apply hz
  have h1 : (minorAut F ^ i) z = 1 := by
    have h2 : (glMat (((minorAut F ^ i) z : antiSp F) : GL (Fin 4) F)).map (algebraMap F k) =
        (1 : Matrix (Fin 4) (Fin 4) F).map (algebraMap F k) := by
      rw [← natRepS_apply, h]
      ext a b
      simp [Matrix.one_apply, apply_ite (algebraMap F k)]
    have h3 := Matrix.map_injective (algebraMap F k).injective h2
    exact Subtype.ext (Units.ext h3)
  have := (minorAut F ^ i).injective (h1.trans (map_one (minorAut F ^ i)).symm)
  exact this

omit [CharP k 2] in
theorem one_le_rank_natRepS_sub_one {z : antiSp F} (hz : z ≠ 1) (i : ℕ) :
    1 ≤ (natRepS k i z - 1).rank :=
  one_le_rank_of_ne_zero _ (sub_ne_zero.mpr (natRepS_ne_one k hz i))

theorem rank_natRepS_sub_one_le {z : antiSp F} (hz : z * z = 1) (i : ℕ) :
    2 * (natRepS k i z - 1).rank ≤ 4 := by
  have := two_mul_rank_le (k := k) (κ := Fin 4) (natRepS k i z) (natRepS_mul_self k hz i)
  simpa using this

theorem rank_tensorRepS_sub_one_ge (A : Finset ℕ) {z : antiSp F} (hz : z * z = 1) (hz1 : z ≠ 1) :
    (4 ^ A.card - 2 ^ A.card) / 2 ≤ (tensorRepS k A z - 1).rank := by
  have h1 := rank_tensorRepS_sub_one k A hz
  have h2 : ∏ i : A, (4 - 2 * (natRepS k (i : ℕ) z - 1).rank) ≤ 2 ^ A.card := by
    have := Finset.prod_le_pow_card (Finset.univ : Finset A)
      (fun i : A => 4 - 2 * (natRepS k (i : ℕ) z - 1).rank) 2
      (fun i _ => by have := one_le_rank_natRepS_sub_one k hz1 i; omega)
    simpa using this
  omega

theorem rank_tensorRepS_sub_one_of_rank_two (A : Finset ℕ) {z : antiSp F} (hz : z * z = 1)
    {i : ℕ} (hiA : i ∈ A) (hi2 : (natRepS k i z - 1).rank = 2) :
    (tensorRepS k A z - 1).rank = 4 ^ A.card / 2 := by
  have h1 := rank_tensorRepS_sub_one k A hz
  have h2 : ∏ i : A, (4 - 2 * (natRepS k (i : ℕ) z - 1).rank) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ (⟨i, hiA⟩ : A)) (by simp [hi2])
  omega

end Apply

section RankE

@[expose] def mE03 (k : Type*) [Field k] : Matrix (Fin 4) (Fin 4) k := !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

@[expose] def mE0213 (k : Type*) [Field k] : Matrix (Fin 4) (Fin 4) k :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0]

theorem rank_mE03 (k : Type*) [Field k] : (mE03 k).rank = 1 := by
  classical
  have h : (mE03 k : Matrix (Fin 4) (Fin 4) k) =
      Matrix.diagonal ![1, 0, 0, 0] * permMat k (Equiv.swap (0 : Fin 4) 3) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [mE03, permMat, Matrix.mul_apply, Matrix.diagonal_apply, Equiv.swap_apply_def]
  rw [h, Matrix.rank_mul_eq_left_of_isUnit_det _ _
    (Matrix.isUnit_det_of_right_inverse (permMat_mul_permMat (k := k) (Equiv.swap (0 : Fin 4) 3))),
    Matrix.rank_diagonal]
  simp [Fintype.card_subtype, Finset.card_filter, Fin.sum_univ_four]

theorem rank_mE0213 (k : Type*) [Field k] : (mE0213 k).rank = 2 := by
  classical
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
  have h : (mE0213 k : Matrix (Fin 4) (Fin 4) k) =
      Matrix.diagonal ![1, 1, 0, 0] * permMat k σ := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [mE0213, permMat, σ, Matrix.mul_apply, Matrix.diagonal_apply, Equiv.swap_apply_def]
  rw [h, Matrix.rank_mul_eq_left_of_isUnit_det _ _
    (Matrix.isUnit_det_of_right_inverse (permMat_mul_permMat (k := k) σ)),
    Matrix.rank_diagonal]
  simp [Fintype.card_subtype, Finset.card_filter, Fin.sum_univ_four]

end RankE

section Specific

variable {F : Type} [Field F] [CharP F 2] [Fintype F] (k : Type*) [Field k] [Algebra F k] [CharP k 2]

variable (F) in
@[expose] noncomputable def invX : antiSp F := uElt 0 0 1 0

variable (F) in
@[expose] noncomputable def invY : antiSp F := uElt 0 1 0 0

omit [Fintype F] in
theorem invX_mul_self : invX F * invX F = 1 := by
  have h := uElt_mul_self (K := F) 0 0 1 0
  rw [invX]
  simpa [uElt_zero_eq_one] using h

omit [Fintype F] in
theorem invY_mul_self : invY F * invY F = 1 := by
  have h := uElt_mul_self (K := F) 0 1 0 0
  rw [invY]
  simpa [uElt_zero_eq_one] using h

omit [Fintype F] in
theorem invX_ne_one : invX F ≠ 1 := by
  intro h
  have h1 : uElt (0 : F) 0 1 0 = uElt 0 0 0 0 := by rw [uElt_zero_eq_one]; exact h
  have := (uElt_inj h1).2.2.1
  exact one_ne_zero this

omit [Fintype F] in
theorem invY_ne_one : invY F ≠ 1 := by
  intro h
  have h1 : uElt (0 : F) 1 0 0 = uElt 0 0 0 0 := by rw [uElt_zero_eq_one]; exact h
  have := (uElt_inj h1).2.1
  exact one_ne_zero this

omit [Fintype F] in
theorem minorMap_uMat_x : minorMap (uMat (0 : F) 0 1 0) = uMat 0 1 0 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three, uMat,
      CharTwo.sub_eq_add]

omit [Fintype F] in
theorem minorMap_uMat_y : minorMap (uMat (0 : F) 1 0 0) = uMat 0 0 1 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three, uMat,
      CharTwo.sub_eq_add]

omit [Fintype F] in
theorem minorHom_invX : minorHom F (invX F) = invY F :=
  Subtype.ext (Units.ext (by
    show minorMap (uMat (0 : F) 0 1 0) = uMat 0 1 0 0
    exact minorMap_uMat_x))

omit [Fintype F] in
theorem minorHom_invY : minorHom F (invY F) = invX F :=
  Subtype.ext (Units.ext (by
    show minorMap (uMat (0 : F) 1 0 0) = uMat 0 0 1 0
    exact minorMap_uMat_y))

theorem minorAut_pow_inv (i : ℕ) :
    (minorAut F ^ i) (invX F) = (if i % 2 = 0 then invX F else invY F) ∧
      (minorAut F ^ i) (invY F) = (if i % 2 = 0 then invY F else invX F) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [minorAut_pow_succ, minorAut_pow_succ, minorHom_invX, minorHom_invY, ih.1, ih.2]
    by_cases h : i % 2 = 0
    · have h' : ¬ (i + 1) % 2 = 0 := by omega
      simp [h, h']
    · have h' : (i + 1) % 2 = 0 := by omega
      simp [h, h']

omit [CharP k 2] in
theorem natRepS_invX_sub_one (i : ℕ) :
    natRepS k i (invX F) - 1 = if i % 2 = 0 then mE03 k else mE0213 k := by
  rw [natRepS_apply, (minorAut_pow_inv i).1]
  by_cases h : i % 2 = 0
  · simp only [h, ite_true]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [invX, glMat_uElt, uMat, mE03, Matrix.sub_apply, Matrix.map_apply]
  · simp only [h, ite_false]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [invY, glMat_uElt, uMat, mE0213, Matrix.sub_apply, Matrix.map_apply]

omit [CharP k 2] in
theorem natRepS_invY_sub_one (i : ℕ) :
    natRepS k i (invY F) - 1 = if i % 2 = 0 then mE0213 k else mE03 k := by
  rw [natRepS_apply, (minorAut_pow_inv i).2]
  by_cases h : i % 2 = 0
  · simp only [h, ite_true]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [invY, glMat_uElt, uMat, mE0213, Matrix.sub_apply, Matrix.map_apply]
  · simp only [h, ite_false]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [invX, glMat_uElt, uMat, mE03, Matrix.sub_apply, Matrix.map_apply]

omit [CharP k 2] in
theorem rank_natRepS_invX (i : ℕ) :
    (natRepS k i (invX F) - 1).rank = if i % 2 = 0 then 1 else 2 := by
  rw [natRepS_invX_sub_one]
  split_ifs
  · exact rank_mE03 k
  · exact rank_mE0213 k

omit [CharP k 2] in
theorem rank_natRepS_invY (i : ℕ) :
    (natRepS k i (invY F) - 1).rank = if i % 2 = 0 then 2 else 1 := by
  rw [natRepS_invY_sub_one]
  split_ifs
  · exact rank_mE0213 k
  · exact rank_mE03 k

theorem rank_tensorRepS_invX (A : Finset ℕ) :
    (tensorRepS k A (invX F) - 1).rank =
      if ∀ i ∈ A, i % 2 = 0 then (4 ^ A.card - 2 ^ A.card) / 2 else 4 ^ A.card / 2 := by
  have h1 := rank_tensorRepS_sub_one k A (invX_mul_self (F := F))
  have h2 : ∏ i : A, (4 - 2 * (natRepS k (i : ℕ) (invX F) - 1).rank) =
      if ∀ i ∈ A, i % 2 = 0 then 2 ^ A.card else 0 := by
    have e : ∀ i : A, 4 - 2 * (natRepS k (i : ℕ) (invX F) - 1).rank =
        if (i : ℕ) % 2 = 0 then 2 else 0 := fun i => by
      rw [rank_natRepS_invX]
      split_ifs <;> rfl
    simp_rw [e]
    rw [Finset.prod_ite_zero]
    simp
  rw [h2] at h1
  split_ifs at h1 ⊢ <;> omega

theorem rank_tensorRepS_invY (A : Finset ℕ) :
    (tensorRepS k A (invY F) - 1).rank =
      if ∀ i ∈ A, i % 2 = 1 then (4 ^ A.card - 2 ^ A.card) / 2 else 4 ^ A.card / 2 := by
  have h1 := rank_tensorRepS_sub_one k A (invY_mul_self (F := F))
  have h2 : ∏ i : A, (4 - 2 * (natRepS k (i : ℕ) (invY F) - 1).rank) =
      if ∀ i ∈ A, i % 2 = 1 then 2 ^ A.card else 0 := by
    have e : ∀ i : A, 4 - 2 * (natRepS k (i : ℕ) (invY F) - 1).rank =
        if (i : ℕ) % 2 = 1 then 2 else 0 := fun i => by
      rw [rank_natRepS_invY]
      by_cases h : (i : ℕ) % 2 = 0
      · simp [h]
      · have h' : (i : ℕ) % 2 = 1 := by omega
        simp [h']
    simp_rw [e]
    rw [Finset.prod_ite_zero]
    simp
  rw [h2] at h1
  split_ifs at h1 ⊢ <;> omega

theorem fundamental_tensor_involution_ranks (A : Finset ℕ) :
    (invX F * invX F = 1 ∧ invY F * invY F = 1 ∧ minorHom F (invX F) = invY F ∧
      minorHom F (invY F) = invX F) ∧
    (tensorRepS k A (invX F) - 1).rank =
      (if ∀ i ∈ A, i % 2 = 0 then (4 ^ A.card - 2 ^ A.card) / 2 else 4 ^ A.card / 2) ∧
    (tensorRepS k A (invY F) - 1).rank =
      (if ∀ i ∈ A, i % 2 = 1 then (4 ^ A.card - 2 ^ A.card) / 2 else 4 ^ A.card / 2) ∧
    (∀ z : antiSp F, z * z = 1 → (tensorRepS k A z - 1).rank =
      (4 ^ A.card - ∏ i : A, (4 - 2 * (natRepS k (i : ℕ) z - 1).rank)) / 2) ∧
    (∀ z : antiSp F, z * z = 1 → z ≠ 1 →
      (4 ^ A.card - 2 ^ A.card) / 2 ≤ (tensorRepS k A z - 1).rank) ∧
    (∀ z : antiSp F, z * z = 1 → ∀ i ∈ A, (natRepS k i z - 1).rank = 2 →
      (tensorRepS k A z - 1).rank = 4 ^ A.card / 2) :=
  ⟨⟨invX_mul_self, invY_mul_self, minorHom_invX, minorHom_invY⟩, rank_tensorRepS_invX k A,
    rank_tensorRepS_invY k A,
    fun z hz => by
      have := rank_tensorRepS_sub_one k A hz
      omega,
    fun z hz hz1 => rank_tensorRepS_sub_one_ge k A hz hz1,
    fun z hz i hi h2 => rank_tensorRepS_sub_one_of_rank_two k A hz hi h2⟩

end Specific

end CFSG.QuasithinUnique.Setup.X7b

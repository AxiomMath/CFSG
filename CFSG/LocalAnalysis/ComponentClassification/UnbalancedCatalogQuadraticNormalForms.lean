module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalWittFlags
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial Module
  Submodule

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem polar_self_charTwo [CharP k 2] (Q : QuadraticForm k V) (x : V) : polar Q x x = 0 := by
  rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]

theorem even_finrank_of_charTwo [CharP k 2] [FiniteDimensional k V] (Q : QuadraticForm k V)
    (hQ : (polarBilin Q).Nondegenerate) : Even (finrank k V) :=
  LinearMap.BilinForm.IsAlt.even_finrank (fun x => by
    rw [polarBilin_apply_apply]
    exact polar_self_charTwo Q x) hQ

theorem nondegenerate_polarBilin_comp_subtype {Q : QuadraticForm k V} {S : Submodule k V}
    (hS : PolarNondegOn Q S) : (polarBilin (Q.comp S.subtype)).Nondegenerate := by
  refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun x hx => ?_
  have h := hS x x.2 fun y hy => by
    have := hx ⟨y, hy⟩
    simpa [polar] using this
  exact Subtype.ext h

theorem exists_mem_orth_two [FiniteDimensional k V] (Q : QuadraticForm k V)
    {S : Submodule k V} (h3 : 3 ≤ finrank k S) (a b : V) :
    ∃ c ∈ S, c ≠ 0 ∧ polar Q a c = 0 ∧ polar Q b c = 0 := by
  let φ : V →ₗ[k] k × k := (polarBilin Q a).prod (polarBilin Q b)
  have hker : 1 ≤ finrank k (S ⊓ LinearMap.ker φ : Submodule k V) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq S (LinearMap.ker φ)
    have h2 := Submodule.finrank_le (S ⊔ LinearMap.ker φ)
    have h3' := LinearMap.finrank_range_add_finrank_ker φ
    have h4 : finrank k (LinearMap.range φ) ≤ 2 := by
      have := Submodule.finrank_le (LinearMap.range φ)
      rwa [Module.finrank_prod, Module.finrank_self] at this
    omega
  obtain ⟨c, hc, hc0⟩ := exists_ne_zero_of_one_le_finrank hker
  have hφ : φ c = 0 := hc.2
  have h1 : polarBilin Q a c = 0 := congrArg Prod.fst hφ
  have h2 : polarBilin Q b c = 0 := congrArg Prod.snd hφ
  rw [polarBilin_apply_apply] at h1 h2
  exact ⟨c, hc.1, hc0, h1, h2⟩

theorem exists_singular_of_three_le [Finite k] [CharP k 2] [FiniteDimensional k V]
    {Q : QuadraticForm k V} {S : Submodule k V} (hS : PolarNondegOn Q S)
    (h3 : 3 ≤ finrank k S) : ∃ x ∈ S, x ≠ 0 ∧ Q x = 0 := by
  obtain ⟨a, haS, ha0⟩ := exists_ne_zero_of_one_le_finrank (T := S) (by omega)
  by_cases hQa : Q a = 0
  · exact ⟨a, haS, ha0, hQa⟩
  obtain ⟨b, -, hab⟩ := hS.exists_polar_ne_zero haS ha0
  obtain ⟨c, hcS, hc0, hac, hbc⟩ := exists_mem_orth_two Q h3 a b
  by_cases hQc : Q c = 0
  · exact ⟨c, hcS, hc0, hQc⟩
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' (Q a)
  obtain ⟨t, ht⟩ := isSquare_of_charTwo' (Q c)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hQc (by rw [ht, mul_zero])
  refine ⟨t • a + s • c, S.add_mem (S.smul_mem _ haS) (S.smul_mem _ hcS), fun h => ?_, ?_⟩
  · have h1 := congrArg (fun x => polar Q x b) h
    simp only [polar_add_left, polar_smul_left_eq, polar_zero_left] at h1
    rw [polar_comm Q c b, hbc, mul_zero, add_zero] at h1
    exact mul_ne_zero ht0 hab h1
  · rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, polar_smul_left_eq,
      polar_smul_right_eq, hac, hs, ht]
    linear_combination (s ^ 2 * t ^ 2) * (CharTwo.two_eq_zero : (2 : k) = 0)

section Splitting

variable {Q : QuadraticForm k V}

theorem orth_cons {m : ℕ} {P₀ : HypPair Q} {P' : Fin m → HypPair Q}
    (h0 : ∀ j, P₀.Orth (P' j)) (h : ∀ i j, i ≠ j → (P' i).Orth (P' j)) :
    ∀ i j : Fin (m + 1), i ≠ j →
      ((Fin.cons P₀ P' : Fin (m + 1) → HypPair Q) i).Orth
        ((Fin.cons P₀ P' : Fin (m + 1) → HypPair Q) j) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact absurd rfl hij
    | succ j => exact h0 j
  | succ i =>
    induction j using Fin.cases with
    | zero => exact (h0 i).symm
    | succ j => exact h i j fun h' => hij (by rw [h'])

theorem exists_hypPairs_normal [Finite k] [CharP k 2] [FiniteDimensional k V] :
    ∀ (n : ℕ) (S : Submodule k V), PolarNondegOn Q S → finrank k S = 2 * n →
      (∃ P : Fin n → HypPair Q, (∀ i, (P i).e ∈ S ∧ (P i).f ∈ S) ∧
        ∀ i j, i ≠ j → (P i).Orth (P j)) ∨
      ∃ m, m + 1 = n ∧ ∃ (P : Fin m → HypPair Q) (u v : V), (∀ i, (P i).e ∈ S ∧ (P i).f ∈ S) ∧
        (∀ i j, i ≠ j → (P i).Orth (P j)) ∧ u ∈ S ∧ v ∈ S ∧
        (∀ i, u ∈ (P i).perp ∧ v ∈ (P i).perp) ∧ Q u = 1 ∧ polar Q u v ≠ 0 ∧
        ∀ s : k, s ^ 2 + polar Q u v * s + Q v ≠ 0 := by
  intro n
  induction n with
  | zero =>
    intro S _ _
    exact Or.inl ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro S hS hSn
    rcases Nat.eq_zero_or_pos n with rfl | hn
    ·
      by_cases hiso : ∃ x ∈ S, x ≠ 0 ∧ Q x = 0
      · obtain ⟨e, heS, he0, he⟩ := hiso
        obtain ⟨f, hfS, hf, hef⟩ := exists_partner_of_polarNondegOn hS heS he he0
        refine Or.inl ⟨fun _ => ⟨e, f, he, hf, hef⟩, fun _ => ⟨heS, hfS⟩, fun i j hij => ?_⟩
        have hi := i.isLt
        have hj := j.isLt
        exact absurd (Fin.ext (by omega)) hij
      · push Not at hiso
        obtain ⟨u₀, hu₀S, hu₀⟩ := exists_ne_zero_of_one_le_finrank (T := S) (by omega)
        obtain ⟨s, hs⟩ := isSquare_of_charTwo' (Q u₀)
        have hs0 : s ≠ 0 := by
          rintro rfl
          exact hiso u₀ hu₀S hu₀ (by rw [hs, mul_zero])
        have huS : s⁻¹ • u₀ ∈ S := S.smul_mem _ hu₀S
        have hu : Q (s⁻¹ • u₀) = 1 := by
          rw [map_smul_eq_sq, hs]
          field_simp
        have hu0 : s⁻¹ • u₀ ≠ 0 := smul_ne_zero (inv_ne_zero hs0) hu₀
        obtain ⟨v, hvS, huv⟩ := hS.exists_polar_ne_zero huS hu0
        refine Or.inr ⟨0, rfl, Fin.elim0, s⁻¹ • u₀, v, fun i => i.elim0, fun i => i.elim0, huS,
          hvS, fun i => i.elim0, hu, huv, fun t ht => ?_⟩
        have hQ' : Q (t • (s⁻¹ • u₀) + v) = t ^ 2 + polar Q (s⁻¹ • u₀) v * t + Q v := by
          rw [QuadraticMap.map_add Q, map_smul_eq_sq, hu, polar_smul_left_eq]
          ring
        have hz : t • (s⁻¹ • u₀) + v = 0 := by
          by_contra hne
          exact hiso _ (S.add_mem (S.smul_mem _ huS) hvS) hne (by rw [hQ', ht])
        apply huv
        rw [show v = -(t • (s⁻¹ • u₀)) from eq_neg_of_add_eq_zero_right hz, polar_neg_right,
          polar_smul_right_eq, polar_self_charTwo, mul_zero, neg_zero]
    ·
      obtain ⟨e, heS, he0, he⟩ := exists_singular_of_three_le hS (by omega)
      obtain ⟨f, hfS, hf, hef⟩ := exists_partner_of_polarNondegOn hS heS he he0
      let P₀ : HypPair Q := ⟨e, f, he, hf, hef⟩
      have hS' : PolarNondegOn Q (S ⊓ P₀.perp) := hS.inf_perp P₀ heS hfS
      have hS'n : finrank k (S ⊓ P₀.perp : Submodule k V) = 2 * n := by
        have := finrank_inf_perp_add_two P₀ heS hfS
        omega
      rcases ih (S ⊓ P₀.perp) hS' hS'n with ⟨P', hP'S, hP'o⟩ |
          ⟨m, hm, P', u, v, hP'S, hP'o, huS, hvS, huv, hu, hβ, hroot⟩
      · have h0 : ∀ j, P₀.Orth (P' j) := fun j =>
          HypPair.orth_of_mem_perp (hP'S j).1.2 (hP'S j).2.2
        refine Or.inl ⟨Fin.cons P₀ P', fun i => ?_, orth_cons h0 hP'o⟩
        induction i using Fin.cases with
        | zero => exact ⟨heS, hfS⟩
        | succ j => exact ⟨(hP'S j).1.1, (hP'S j).2.1⟩
      · have h0 : ∀ j, P₀.Orth (P' j) := fun j =>
          HypPair.orth_of_mem_perp (hP'S j).1.2 (hP'S j).2.2
        refine Or.inr ⟨m + 1, by omega, Fin.cons P₀ P', u, v, fun i => ?_, orth_cons h0 hP'o,
          huS.1, hvS.1, fun i => ?_, hu, hβ, hroot⟩
        · induction i using Fin.cases with
          | zero => exact ⟨heS, hfS⟩
          | succ j => exact ⟨(hP'S j).1.1, (hP'S j).2.1⟩
        · induction i using Fin.cases with
          | zero => exact ⟨huS.2, hvS.2⟩
          | succ j => exact huv j

end Splitting

section Coordinates

variable {Q : QuadraticForm k V} {m : ℕ} {P : Fin m → HypPair Q}

theorem polar_e_f_of_orth (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (i j : Fin m) :
    polar Q (P i).e (P j).f = if i = j then 1 else 0 := by
  split_ifs with h
  · subst h
    exact (P i).polar_ef
  · exact (hP i j h).ef

theorem polar_f_e_of_orth (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (i j : Fin m) :
    polar Q (P i).f (P j).e = if i = j then 1 else 0 := by
  rw [polar_comm, polar_e_f_of_orth hP j i]
  simp only [eq_comm]

theorem polar_e_e_of_orth (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (i j : Fin m) :
    polar Q (P i).e (P j).e = 0 := by
  by_cases h : i = j
  · subst h
    exact (P i).polar_ee
  · exact (hP i j h).ee

theorem polar_f_f_of_orth (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (i j : Fin m) :
    polar Q (P i).f (P j).f = 0 := by
  by_cases h : i = j
  · subst h
    exact (P i).polar_ff
  · exact (hP i j h).ff

theorem polar_sum_add_f (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (a b : Fin m → k) {w : V}
    (hw : ∀ i, w ∈ (P i).perp) (j : Fin m) :
    polar Q (∑ i, a i • (P i).e + ∑ i, b i • (P i).f + w) (P j).f = a j := by
  have hwj : polar Q w (P j).f = 0 := by
    rw [polar_comm]
    exact (HypPair.mem_perp.1 (hw j)).2
  simp [polar_add_left, polar_sum_smul_left, polar_e_f_of_orth hP, polar_f_f_of_orth hP, hwj]

theorem polar_sum_add_e (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (a b : Fin m → k) {w : V}
    (hw : ∀ i, w ∈ (P i).perp) (j : Fin m) :
    polar Q (∑ i, a i • (P i).e + ∑ i, b i • (P i).f + w) (P j).e = b j := by
  have hwj : polar Q w (P j).e = 0 := by
    rw [polar_comm]
    exact (HypPair.mem_perp.1 (hw j)).1
  simp [polar_add_left, polar_sum_smul_left, polar_e_e_of_orth hP, polar_f_e_of_orth hP, hwj]

theorem polar_sum_f (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (a b : Fin m → k) (j : Fin m) :
    polar Q (∑ i, a i • (P i).e + ∑ i, b i • (P i).f) (P j).f = a j := by
  have h := polar_sum_add_f hP a b (w := 0) (fun i => zero_mem _) j
  rwa [add_zero] at h

theorem polar_sum_e (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (a b : Fin m → k) (j : Fin m) :
    polar Q (∑ i, a i • (P i).e + ∑ i, b i • (P i).f) (P j).e = b j := by
  have h := polar_sum_add_e hP a b (w := 0) (fun i => zero_mem _) j
  rwa [add_zero] at h

theorem map_sum_hyp (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (x y : Fin m → k) :
    Q (∑ i, x i • (P i).e + ∑ i, y i • (P i).f) = ∑ i, x i * y i := by
  have hX : Q (∑ i, x i • (P i).e) = 0 :=
    map_eq_zero_of_mem_span (S := Set.range fun i => (P i).e)
      (by rintro _ ⟨i, rfl⟩; exact (P i).Q_e)
      (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact polar_e_e_of_orth hP i j)
      (sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩))
  have hY : Q (∑ i, y i • (P i).f) = 0 :=
    map_eq_zero_of_mem_span (S := Set.range fun i => (P i).f)
      (by rintro _ ⟨i, rfl⟩; exact (P i).Q_f)
      (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact polar_f_f_of_orth hP i j)
      (sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩))
  rw [QuadraticMap.map_add Q, hX, hY, zero_add, zero_add, polar_sum_smul_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := polar_sum_add_f hP x 0 (w := 0) (fun i => zero_mem _) j
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at h
  rw [h, mul_comm]

theorem polar_sum_hyp_eq_zero (x y : Fin m → k) {w : V} (hw : ∀ i, w ∈ (P i).perp) :
    polar Q (∑ i, x i • (P i).e + ∑ i, y i • (P i).f) w = 0 := by
  simp only [polar_add_left, polar_sum_smul_left]
  simp [(HypPair.mem_perp.1 (hw _)).1, (HypPair.mem_perp.1 (hw _)).2]

theorem exists_basis_of_hypPairs [FiniteDimensional k V] (hV : finrank k V = 2 * m)
    (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    ∃ b : Basis (Fin m ⊕ Fin m) k V, (∀ i, b (.inl i) = (P i).e ∧ b (.inr i) = (P i).f) ∧
      ∀ x y : Fin m → k, Q (∑ i, x i • b (.inl i) + ∑ i, y i • b (.inr i)) = ∑ i, x i * y i := by
  set v : Fin m ⊕ Fin m → V := Sum.elim (fun i => (P i).e) (fun i => (P i).f) with hv
  have hli : LinearIndependent k v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [hv, Sum.elim_inl, Sum.elim_inr] at hg
    have hg' : ∑ i, g (.inl i) • (P i).e + ∑ i, g (.inr i) • (P i).f + 0 = 0 := by
      rw [add_zero, hg]
    rintro (j | j)
    · have := polar_sum_add_f hP (fun i => g (.inl i)) (fun i => g (.inr i))
        (fun i => zero_mem _) j
      rwa [hg', polar_zero_left, eq_comm] at this
    · have := polar_sum_add_e hP (fun i => g (.inl i)) (fun i => g (.inr i))
        (fun i => zero_mem _) j
      rwa [hg', polar_zero_left, eq_comm] at this
  have hsp : ⊤ ≤ span k (Set.range v) := by
    rw [top_le_iff]
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_eq_card hli, Fintype.card_sum, Fintype.card_fin, hV]
    ring
  refine ⟨Basis.mk hli hsp, fun i => ⟨by rw [Basis.mk_apply]; rfl, by rw [Basis.mk_apply]; rfl⟩,
    fun x y => ?_⟩
  simp only [Basis.mk_apply, hv, Sum.elim_inl, Sum.elim_inr]
  exact map_sum_hyp hP x y

theorem exists_basis_of_hypPairs_plane [CharP k 2] [FiniteDimensional k V]
    (hV : finrank k V = 2 * (m + 1)) (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) {u v : V}
    (huv : ∀ i, u ∈ (P i).perp ∧ v ∈ (P i).perp) (hu : Q u = 1) (hβ : polar Q u v ≠ 0) :
    ∃ b : Basis (Fin m ⊕ Fin m ⊕ Fin 2) k V,
      (∀ i, b (.inl i) = (P i).e ∧ b (.inr (.inl i)) = (P i).f) ∧ b (.inr (.inr 0)) = u ∧
      b (.inr (.inr 1)) = v ∧
      ∀ (x y : Fin m → k) (s t : k),
        Q (∑ i, x i • b (.inl i) + ∑ i, y i • b (.inr (.inl i)) + s • b (.inr (.inr 0)) +
          t • b (.inr (.inr 1))) =
          ∑ i, x i * y i + s ^ 2 + polar Q u v * s * t + Q v * t ^ 2 := by
  have hst : ∀ s t : k, ∀ i, s • u + t • v ∈ (P i).perp := fun s t i =>
    add_mem (smul_mem _ _ (huv i).1) (smul_mem _ _ (huv i).2)
  set w : Fin m ⊕ Fin m ⊕ Fin 2 → V :=
    Sum.elim (fun i => (P i).e) (Sum.elim (fun i => (P i).f) ![u, v]) with hw
  have hli : LinearIndependent k w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_two] at hg
    simp only [hw, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
    have hg' : ∑ i, g (.inl i) • (P i).e + ∑ i, g (.inr (.inl i)) • (P i).f +
        (g (.inr (.inr 0)) • u + g (.inr (.inr 1)) • v) = 0 := by
      rw [← hg]
      abel
    have hx : ∀ j, g (.inl j) = 0 := fun j => by
      have := polar_sum_add_f hP (fun i => g (.inl i)) (fun i => g (.inr (.inl i)))
        (hst (g (.inr (.inr 0))) (g (.inr (.inr 1)))) j
      rwa [hg', polar_zero_left, eq_comm] at this
    have hy : ∀ j, g (.inr (.inl j)) = 0 := fun j => by
      have := polar_sum_add_e hP (fun i => g (.inl i)) (fun i => g (.inr (.inl i)))
        (hst (g (.inr (.inr 0))) (g (.inr (.inr 1)))) j
      rwa [hg', polar_zero_left, eq_comm] at this
    simp only [hx, hy, zero_smul, Finset.sum_const_zero, zero_add] at hg'
    have hvu : polar Q v u ≠ 0 := by rwa [polar_comm]
    have h1 := congrArg (fun z => polar Q z u) hg'
    have h2 := congrArg (fun z => polar Q z v) hg'
    simp only [polar_add_left, polar_smul_left_eq, polar_self_charTwo, polar_zero_left,
      mul_zero, zero_add, add_zero] at h1 h2
    have g1 : g (.inr (.inr 1)) = 0 := (mul_eq_zero.1 h1).resolve_right hvu
    have g0 : g (.inr (.inr 0)) = 0 := (mul_eq_zero.1 h2).resolve_right hβ
    rintro (j | j | j)
    · exact hx j
    · exact hy j
    · fin_cases j
      · exact g0
      · exact g1
  have hsp : ⊤ ≤ span k (Set.range w) := by
    rw [top_le_iff]
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_eq_card hli, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin, hV]
    ring
  refine ⟨Basis.mk hli hsp, fun i => ⟨by rw [Basis.mk_apply]; rfl, by rw [Basis.mk_apply]; rfl⟩,
    by rw [Basis.mk_apply]; rfl, by rw [Basis.mk_apply]; rfl, fun x y s t => ?_⟩
  simp only [Basis.mk_apply, hw, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have hvv : polar Q v v = 0 := polar_self_charTwo Q v
  rw [add_assoc, QuadraticMap.map_add Q, map_sum_hyp hP x y, polar_sum_hyp_eq_zero x y (hst s t),
    QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, polar_smul_left_eq,
    polar_smul_right_eq, hu]
  ring

end Coordinates

section Remainder

variable {Q : QuadraticForm k V} {m : ℕ} {P : Fin m → HypPair Q}

theorem sub_sum_mem_perp (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (x : V) (j : Fin m) :
    x - (∑ i, polar Q x (P i).f • (P i).e + ∑ i, polar Q x (P i).e • (P i).f) ∈ (P j).perp := by
  have he := polar_sum_e hP (fun i => polar Q x (P i).f) (fun i => polar Q x (P i).e) j
  have hf := polar_sum_f hP (fun i => polar Q x (P i).f) (fun i => polar Q x (P i).e) j
  beta_reduce at he hf
  rw [HypPair.mem_perp]
  constructor
  · rw [polar_sub_right, polar_comm Q (P j).e (_ + _), he, polar_comm, sub_self]
  · rw [polar_sub_right, polar_comm Q (P j).f (_ + _), hf, polar_comm, sub_self]

theorem polarNondegOn_iInf_perp (hQ : (polarBilin Q).Nondegenerate)
    (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) : PolarNondegOn Q (⨅ i, (P i).perp) := by
  intro x hx hxW
  rw [Submodule.mem_iInf] at hx
  apply eq_zero_of_polar_eq_zero hQ
  intro z
  have hz : z - (∑ i, polar Q z (P i).f • (P i).e + ∑ i, polar Q z (P i).e • (P i).f) ∈
      ⨅ i, (P i).perp := Submodule.mem_iInf _ |>.2 (sub_sum_mem_perp hP z)
  have h1 := hxW _ hz
  rw [polar_sub_right, polar_comm Q x (_ + _),
    polar_sum_hyp_eq_zero (Q := Q) (P := P) _ _ hx, sub_zero] at h1
  exact h1

theorem finrank_iInf_perp_of_anisotropic [Finite k] [CharP k 2] [FiniteDimensional k V]
    (hQ : (polarBilin Q).Nondegenerate) (hP : ∀ i j, i ≠ j → (P i).Orth (P j))
    (han : ∀ w : V, (∀ i, w ∈ (P i).perp) → Q w = 0 → w = 0) :
    finrank k (⨅ i, (P i).perp : Submodule k V) = 0 ∨
      finrank k (⨅ i, (P i).perp : Submodule k V) = 2 := by
  have hW := polarNondegOn_iInf_perp hQ hP
  have hle : finrank k (⨅ i, (P i).perp : Submodule k V) ≤ 2 := by
    by_contra h
    obtain ⟨x, hxW, hx0, hx⟩ := exists_singular_of_three_le hW (by omega)
    exact hx0 (han x (Submodule.mem_iInf _ |>.1 hxW) hx)
  obtain ⟨d, hd⟩ := even_finrank_of_charTwo _ (nondegenerate_polarBilin_comp_subtype hW)
  omega

end Remainder

theorem finite_even_regular_quadratic_normal_forms [Finite k] [CharP k 2] [FiniteDimensional k V]
    (Q : QuadraticForm k V) (hQ : (polarBilin Q).Nondegenerate) :
    (∃ n, finrank k V = 2 * n) ∧
    (finrank k V = 0 → ∀ v : V, v = 0) ∧
    (∀ n, 1 ≤ n → finrank k V = 2 * n →
      (∃ b : Basis (Fin n ⊕ Fin n) k V, ∀ x y : Fin n → k,
        Q (∑ i, x i • b (.inl i) + ∑ i, y i • b (.inr i)) = ∑ i, x i * y i) ∨
      ∃ β γ : k, β ≠ 0 ∧ (∀ s : k, s ^ 2 + β * s + γ ≠ 0) ∧
        ∃ b : Basis (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) k V,
          ∀ (x y : Fin (n - 1) → k) (s t : k),
            Q (∑ i, x i • b (.inl i) + ∑ i, y i • b (.inr (.inl i)) + s • b (.inr (.inr 0)) +
              t • b (.inr (.inr 1))) = ∑ i, x i * y i + s ^ 2 + β * s * t + γ * t ^ 2) ∧
    (∃ (m : ℕ) (P : Fin m → HypPair Q), (∀ i j, i ≠ j → (P i).Orth (P j)) ∧
      ∀ w : V, (∀ i, w ∈ (P i).perp) → Q w = 0 → w = 0) ∧
    (∀ (m : ℕ) (P : Fin m → HypPair Q), (∀ i j, i ≠ j → (P i).Orth (P j)) →
      (∀ w : V, (∀ i, w ∈ (P i).perp) → Q w = 0 → w = 0) →
      finrank k (⨅ i, (P i).perp : Submodule k V) = 0 ∨
        finrank k (⨅ i, (P i).perp : Submodule k V) = 2) ∧
    (∀ n, finrank k V = 2 * n → 4 ≤ n →
      ∃ P₁ P₂ P₃ : HypPair Q, P₁.Orth P₂ ∧ P₁.Orth P₃ ∧ P₂.Orth P₃) := by
  obtain ⟨n₀, hn₀⟩ := even_finrank_of_charTwo Q hQ
  have hV₀ : finrank k V = 2 * n₀ := by omega
  have htop : finrank k (⊤ : Submodule k V) = 2 * n₀ := by rw [finrank_top, hV₀]
  have hnf := exists_hypPairs_normal (Q := Q) n₀ ⊤ (polarNondegOn_top hQ) htop
  have hexists : ∃ (m : ℕ) (P : Fin m → HypPair Q), (∀ i j, i ≠ j → (P i).Orth (P j)) ∧
      ∀ w : V, (∀ i, w ∈ (P i).perp) → Q w = 0 → w = 0 := by
    rcases hnf with ⟨P, -, hPo⟩ | ⟨m, hm, P, u, v, -, hPo, -, -, huv, hu, hβ, hroot⟩
    · refine ⟨n₀, P, hPo, fun w hw _ => ?_⟩
      obtain ⟨b, hb, -⟩ := exists_basis_of_hypPairs hV₀ hPo
      have hw' : ∑ i, b.repr w (.inl i) • (P i).e + ∑ i, b.repr w (.inr i) • (P i).f = w := by
        have h := b.sum_repr w
        rw [Fintype.sum_sum_type] at h
        simpa only [(hb _).1, (hb _).2] using h
      have hx : ∀ j, b.repr w (.inl j) = 0 := fun j => by
        have h := polar_sum_f hPo (fun i => b.repr w (.inl i)) (fun i => b.repr w (.inr i)) j
        beta_reduce at h
        rw [hw', polar_comm] at h
        rw [← h]
        exact (HypPair.mem_perp.1 (hw j)).2
      have hy : ∀ j, b.repr w (.inr j) = 0 := fun j => by
        have h := polar_sum_e hPo (fun i => b.repr w (.inl i)) (fun i => b.repr w (.inr i)) j
        beta_reduce at h
        rw [hw', polar_comm] at h
        rw [← h]
        exact (HypPair.mem_perp.1 (hw j)).1
      rw [← hw']
      simp [hx, hy]
    · subst hm
      refine ⟨m, P, hPo, fun w hw hw0 => ?_⟩
      obtain ⟨b, hb, hb0, hb1, -⟩ := exists_basis_of_hypPairs_plane hV₀ hPo huv hu hβ
      have hw' := b.sum_repr w
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_two] at hw'
      simp only [(hb _).1, (hb _).2, hb0, hb1] at hw'
      have hst : ∀ s t : k, ∀ i, s • u + t • v ∈ (P i).perp := fun s t i =>
        add_mem (smul_mem _ _ (huv i).1) (smul_mem _ _ (huv i).2)
      have hw'' : ∑ i, b.repr w (.inl i) • (P i).e + ∑ i, b.repr w (.inr (.inl i)) • (P i).f +
          (b.repr w (.inr (.inr 0)) • u + b.repr w (.inr (.inr 1)) • v) = w := by
        refine Eq.trans ?_ hw'
        abel
      have hx : ∀ j, b.repr w (.inl j) = 0 := fun j => by
        have h := polar_sum_add_f hPo (fun i => b.repr w (.inl i))
          (fun i => b.repr w (.inr (.inl i))) (hst (b.repr w (.inr (.inr 0)))
            (b.repr w (.inr (.inr 1)))) j
        beta_reduce at h
        rw [hw'', polar_comm] at h
        rw [← h]
        exact (HypPair.mem_perp.1 (hw j)).2
      have hy : ∀ j, b.repr w (.inr (.inl j)) = 0 := fun j => by
        have h := polar_sum_add_e hPo (fun i => b.repr w (.inl i))
          (fun i => b.repr w (.inr (.inl i))) (hst (b.repr w (.inr (.inr 0)))
            (b.repr w (.inr (.inr 1)))) j
        beta_reduce at h
        rw [hw'', polar_comm] at h
        rw [← h]
        exact (HypPair.mem_perp.1 (hw j)).1
      simp only [hx, hy, zero_smul, Finset.sum_const_zero, zero_add] at hw''
      set s := b.repr w (.inr (.inr 0))
      set t := b.repr w (.inr (.inr 1))
      have hQw : s ^ 2 + polar Q u v * s * t + Q v * t ^ 2 = 0 := by
        rw [← hw0, ← hw'', QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq,
          polar_smul_left_eq, polar_smul_right_eq, hu]
        ring
      have ht : t = 0 := by
        by_contra ht
        apply hroot (s / t)
        field_simp
        linear_combination hQw
      have hs : s = 0 := by
        rw [ht] at hQw
        simpa using hQw
      rw [← hw'', hs, ht, zero_smul, zero_smul, add_zero]
  refine ⟨⟨n₀, hV₀⟩, fun h => (finrank_zero_iff_forall_zero).1 h, fun n hn hV => ?_, hexists,
    fun m P hPo han => finrank_iInf_perp_of_anisotropic hQ hPo han, fun n hV hn => ?_⟩
  · have hnn : n = n₀ := by omega
    subst hnn
    rcases hnf with ⟨P, -, hPo⟩ | ⟨m, hm, P, u, v, -, hPo, -, -, huv, hu, hβ, hroot⟩
    · obtain ⟨b, -, hb⟩ := exists_basis_of_hypPairs hV hPo
      exact Or.inl ⟨b, hb⟩
    · subst hm
      obtain ⟨b, -, -, -, hb⟩ := exists_basis_of_hypPairs_plane hV hPo huv hu hβ
      exact Or.inr ⟨polar Q u v, Q v, hβ, hroot, b, hb⟩
  · have hnn : n = n₀ := by omega
    subst hnn
    rcases hnf with ⟨P, -, hPo⟩ | ⟨m, hm, P, -, -, -, hPo, -⟩
    · exact ⟨P ⟨0, by omega⟩, P ⟨1, by omega⟩, P ⟨2, by omega⟩, hPo _ _ (by simp),
        hPo _ _ (by simp), hPo _ _ (by simp)⟩
    · exact ⟨P ⟨0, by omega⟩, P ⟨1, by omega⟩, P ⟨2, by omega⟩, hPo _ _ (by simp),
        hPo _ _ (by simp), hPo _ _ (by simp)⟩

end CFSG.ComponentClassification.UnbalancedCatalog

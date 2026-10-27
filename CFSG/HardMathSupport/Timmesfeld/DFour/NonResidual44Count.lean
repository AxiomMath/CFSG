module

public import CFSG.Timmesfeld.Orders.ClassicalOrthogonal
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaThreeFamily

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open QuadraticMap Module CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.Timmesfeld.ClassicalOrders
open CFSG.ComponentClassification.UnbalancedCatalog.ThreeFamily (card_invariant_singular_congr)

section General

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem quad_smul_sub_smul {u w : V} (hQu : Q u = 0) (huw : polar Q u w = 0) (s t : K) :
    Q (s • w - t • u) = s ^ 2 * Q w := by
  rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hQu,
    polar_smul_left_eq, polar_smul_right_eq, polar_comm, huw]
  ring

theorem polar_isometry {V' : Type*} [AddCommGroup V'] [Module K V'] {Q' : QuadraticForm K V'}
    (r : V ≃ₗ[K] V') (hr : ∀ x, Q' (r x) = Q x) (x y : V) :
    polar Q' (r x) (r y) = polar Q x y := by
  rw [polar, polar, ← map_add, hr, hr, hr]

theorem mem_of_map_eq_of_eichler [FiniteDimensional K V] (hnd : (polarBilin Q).Nondegenerate)
    {u w : V} (hQu : Q u = 0) (huw : polar Q u w = 0) (hQw : Q w ≠ 0) {A : V ≃ₗ[K] V}
    (hA : ∀ x, A x = x + polar Q x u • w - (polar Q x w + Q w * polar Q x u) • u)
    {M : Submodule K V} (hMs : ∀ x ∈ M, Q x = 0) (hdim : finrank K V = 2 * finrank K M)
    (hMA : M.map (A : V →ₗ[K] V) = M) : u ∈ M := by
  have hperp : ∀ m ∈ M, polar Q m u = 0 := by
    intro m hm
    have hAm : A m ∈ M := by
      rw [← hMA]
      exact ⟨m, hm, rfl⟩
    have hd' : A m - m = polar Q m u • w - (polar Q m w + Q w * polar Q m u) • u := by
      rw [hA]
      abel
    have h0 := hMs _ (M.sub_mem hAm hm)
    rw [hd', quad_smul_sub_smul hQu huw] at h0
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 h0).resolve_right hQw)
  have hle : M ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) M := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    change polar Q y x = 0
    rw [polar, hMs _ (M.add_mem hy hx), hMs y hy, hMs x hx, sub_zero, sub_zero]
  have heq : LinearMap.BilinForm.orthogonal (polarBilin Q) M = M := by
    refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
    rw [LinearMap.BilinForm.finrank_orthogonal hnd]
    omega
  rw [← heq, LinearMap.BilinForm.mem_orthogonal_iff]
  exact fun y hy => hperp y hy

theorem eichler_transport {V' : Type*} [AddCommGroup V'] [Module K V'] {Q' : QuadraticForm K V'}
    (r : V ≃ₗ[K] V') (hr : ∀ x, Q' (r x) = Q x) {u w : V} {A : V ≃ₗ[K] V}
    (hA : ∀ x, A x = x + polar Q x u • w - (polar Q x w + Q w * polar Q x u) • u) (y : V') :
    (r.symm.trans (A.trans r)) y =
      y + polar Q' y (r u) • r w - (polar Q' y (r w) + Q' (r w) * polar Q' y (r u)) • r u := by
  have hy : y = r (r.symm y) := (r.apply_symm_apply y).symm
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hA, map_sub, map_add, map_smul, map_smul,
    r.apply_symm_apply, hr]
  conv_rhs => rw [hy, polar_isometry r hr, polar_isometry r hr]
  rw [r.apply_symm_apply]

end General

section Split

variable {K : Type*} [Field K]

theorem polar_hypSum_e (x : (K × K) × (Fin 3 ⊕ Fin 3 → K)) :
    polar (hypSum (quadPlus 3 K)) x ((1, 0), 0) = x.1.2 := by
  rw [polar_hypSum]
  simp

theorem hypSum_e : hypSum (quadPlus 3 K) ((1, 0), 0) = 0 := by
  simp [hypSum_apply]

theorem nondegenerate_hypSum_three :
    (polarBilin (hypSum (quadPlus 3 K))).Nondegenerate :=
  nondegenerate_polarBilin_hypSum (nondegenerate_polarBilin_quadPlus 3 K)

theorem finrank_hypSum_three : finrank K ((K × K) × (Fin 3 ⊕ Fin 3 → K)) = 8 := by
  simp

theorem eq_span_sup_map_inr {M : Submodule K ((K × K) × (Fin 3 ⊕ Fin 3 → K))}
    (hMs : ∀ x ∈ M, hypSum (quadPlus 3 K) x = 0) (he : ((1, 0), 0) ∈ M) :
    M = (K ∙ (((1, 0), 0) : (K × K) × (Fin 3 ⊕ Fin 3 → K))) ⊔
      (M.comap (LinearMap.inr K (K × K) (Fin 3 ⊕ Fin 3 → K))).map
        (LinearMap.inr K (K × K) (Fin 3 ⊕ Fin 3 → K)) := by
  refine le_antisymm (fun x hx => ?_) (sup_le ?_ (Submodule.map_comap_le _ _))
  · have hx12 : x.1.2 = 0 := by
      rw [← polar_hypSum_e, polar, hMs _ (M.add_mem hx he), hMs x hx, hMs _ he, sub_zero,
        sub_zero]
    have hdec : x = x.1.1 • ((1, 0), 0) + ((0, 0), x.2) := by
      ext <;> simp [hx12]
    have hin : ((0, 0), x.2) ∈ M := by
      have h := M.sub_mem hx (M.smul_mem x.1.1 he)
      have e : x - x.1.1 • (((1, 0), 0) : (K × K) × (Fin 3 ⊕ Fin 3 → K)) = ((0, 0), x.2) := by
        ext <;> simp [hx12]
      rwa [e] at h
    rw [hdec]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
      ⟨x.2, hin, rfl⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact he

theorem comap_inr_mem_singularSubspaces {M : Submodule K ((K × K) × (Fin 3 ⊕ Fin 3 → K))}
    (hM : M ∈ singularSubspaces (hypSum (quadPlus 3 K)) 4) (he : ((1, 0), 0) ∈ M) :
    M.comap (LinearMap.inr K (K × K) (Fin 3 ⊕ Fin 3 → K)) ∈
      singularSubspaces (quadPlus 3 K) 3 := by
  set ι := LinearMap.inr K (K × K) (Fin 3 ⊕ Fin 3 → K)
  refine ⟨?_, fun v hv => ?_⟩
  · have hdec := eq_span_sup_map_inr hM.2 he
    have hdisj : (K ∙ (((1, 0), 0) : (K × K) × (Fin 3 ⊕ Fin 3 → K))) ⊓ (M.comap ι).map ι = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro x ⟨hx1, ⟨v, -, rfl⟩⟩
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hx1
      have h1 : a = 0 := by
        have := congrArg (fun y : (K × K) × (Fin 3 ⊕ Fin 3 → K) => y.1.1) ha
        simpa [ι] using this
      rw [← ha, h1, zero_smul]
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq
      (K ∙ (((1, 0), 0) : (K × K) × (Fin 3 ⊕ Fin 3 → K))) ((M.comap ι).map ι)
    rw [← hdec, hdisj, finrank_bot, add_zero, hM.1,
      finrank_span_singleton (by simp : (((1, 0), 0) : (K × K) × (Fin 3 ⊕ Fin 3 → K)) ≠ 0),
      ← (Submodule.equivMapOfInjective ι (LinearMap.inr_injective) _).finrank_eq] at hsum
    omega
  · have h := hM.2 _ hv
    simpa [hypSum_apply, ι] using h

variable [Finite K]

theorem card_fixed_maximal_le_split {w' : (K × K) × (Fin 3 ⊕ Fin 3 → K)}
    (hwe : polar (hypSum (quadPlus 3 K)) ((1, 0), 0) w' = 0) (hw' : hypSum (quadPlus 3 K) w' ≠ 0)
    {A : ((K × K) × (Fin 3 ⊕ Fin 3 → K)) ≃ₗ[K] ((K × K) × (Fin 3 ⊕ Fin 3 → K))}
    (hA : ∀ x, A x = x + polar (hypSum (quadPlus 3 K)) x ((1, 0), 0) • w' -
      (polar (hypSum (quadPlus 3 K)) x w' +
        hypSum (quadPlus 3 K) w' * polar (hypSum (quadPlus 3 K)) x ((1, 0), 0)) • ((1, 0), 0)) :
    Nat.card {M // M ∈ singularSubspaces (hypSum (quadPlus 3 K)) 4 ∧
        M.map (A : _ →ₗ[K] _) = M} ≤
      Nat.card (singularSubspaces (quadPlus 3 K) 3) := by
  have hmem : ∀ M : {M // M ∈ singularSubspaces (hypSum (quadPlus 3 K)) 4 ∧
      M.map (A : _ →ₗ[K] _) = M}, ((1, 0), 0) ∈ M.1 := fun M =>
    mem_of_map_eq_of_eichler nondegenerate_hypSum_three hypSum_e hwe hw' hA M.2.1.2
      (by rw [finrank_hypSum_three, M.2.1.1]) M.2.2
  refine Nat.card_le_card_of_injective
    (fun M => ⟨M.1.comap (LinearMap.inr K (K × K) (Fin 3 ⊕ Fin 3 → K)),
      comap_inr_mem_singularSubspaces M.2.1 (hmem M)⟩) fun M M' h => ?_
  have h' := congrArg Subtype.val h
  simp only at h'
  apply Subtype.ext
  rw [eq_span_sup_map_inr M.2.1.2 (hmem M), eq_span_sup_map_inr M'.2.1.2 (hmem M'), h']

theorem card_le_card_fixed_lines_split {w' : (K × K) × (Fin 3 ⊕ Fin 3 → K)}
    (hwe : polar (hypSum (quadPlus 3 K)) ((1, 0), 0) w' = 0)
    {A : ((K × K) × (Fin 3 ⊕ Fin 3 → K)) ≃ₗ[K] ((K × K) × (Fin 3 ⊕ Fin 3 → K))}
    (hA : ∀ x, A x = x + polar (hypSum (quadPlus 3 K)) x ((1, 0), 0) • w' -
      (polar (hypSum (quadPlus 3 K)) x w' +
        hypSum (quadPlus 3 K) w' * polar (hypSum (quadPlus 3 K)) x ((1, 0), 0)) • ((1, 0), 0)) :
    Nat.card {v : Fin 3 ⊕ Fin 3 → K // polar (quadPlus 3 K) v w'.2 = 0 ∧ quadPlus 3 K v = 0} ≤
      Nat.card {L // L ∈ singularSubspaces (hypSum (quadPlus 3 K)) 1 ∧
        L.map (A : _ →ₗ[K] _) = L} := by
  have hw12 : w'.1.2 = 0 := by
    have h := hwe
    rw [polar_comm, polar_hypSum_e] at h
    exact h
  have : Finite (Submodule K ((K × K) × (Fin 3 ⊕ Fin 3 → K))) :=
    Finite.of_injective (fun L : Submodule K ((K × K) × (Fin 3 ⊕ Fin 3 → K)) =>
      (L : Set ((K × K) × (Fin 3 ⊕ Fin 3 → K)))) SetLike.coe_injective
  have hp0 : ∀ v : Fin 3 ⊕ Fin 3 → K, (((1, 0), v) : (K × K) × (Fin 3 ⊕ Fin 3 → K)) ≠ 0 :=
    fun v h => by
      have := congrArg (fun y : (K × K) × (Fin 3 ⊕ Fin 3 → K) => y.1.1) h
      simp at this
  have hfix : ∀ v : Fin 3 ⊕ Fin 3 → K, polar (quadPlus 3 K) v w'.2 = 0 →
      A ((1, 0), v) = ((1, 0), v) := by
    intro v hv
    rw [hA, polar_hypSum_e, polar_hypSum]
    simp [hw12, hv]
  refine Nat.card_le_card_of_injective (fun v => ⟨K ∙ ((1, 0), v.1),
    ⟨finrank_span_singleton (hp0 v.1), fun x hx => ?_⟩, ?_⟩) fun v v' h => ?_
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul_eq_sq, hypSum_apply]
    simp [v.2.2]
  · rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, hfix v.1 v.2.1]
  · have h' := congrArg Subtype.val h
    simp only at h'
    have hmem : ((1, 0), v'.1) ∈ K ∙ (((1, 0), v.1) : (K × K) × (Fin 3 ⊕ Fin 3 → K)) := by
      rw [h']
      exact Submodule.mem_span_singleton_self _
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
    have h1 : a = 1 := by
      have := congrArg (fun y : (K × K) × (Fin 3 ⊕ Fin 3 → K) => y.1.1) ha
      simpa using this
    have h2 := congrArg (fun y : (K × K) × (Fin 3 ⊕ Fin 3 → K) => y.2) ha
    simp only [h1, one_smul] at h2
    exact Subtype.ext h2

omit [Finite K] in
theorem polar_std (c : K) (v : Fin 3 ⊕ Fin 3 → K) :
    polar (quadPlus 3 K) v (Pi.single (Sum.inl 0) 1 + c • Pi.single (Sum.inr 0) 1) =
      v (Sum.inr 0) + c * v (Sum.inl 0) := by
  rw [polar_add_right, polar_smul_right, polar_quadPlus_single_inl, polar_quadPlus_single_inr,
    smul_eq_mul]

omit [Finite K] in
theorem quadPlus_std (c : K) :
    quadPlus 3 K (Pi.single (Sum.inl 0) 1 + c • Pi.single (Sum.inr 0) 1) = c := by
  rw [quadPlus_apply, Fin.sum_univ_three]
  simp

theorem card_perp_singular_std {c : K} (hc : c ≠ 0) :
    Nat.card {v : Fin 3 ⊕ Fin 3 → K //
      polar (quadPlus 3 K) v (Pi.single (Sum.inl 0) 1 + c • Pi.single (Sum.inr 0) 1) = 0 ∧
        quadPlus 3 K v = 0} = Nat.card K ^ 4 := by
  let Q₁ : QuadraticForm K K := (-c) • QuadraticMap.sq
  have hQ₁ : ∀ x, Q₁ x = -c * (x * x) := fun x => rfl
  let e : {v : Fin 3 ⊕ Fin 3 → K //
      polar (quadPlus 3 K) v (Pi.single (Sum.inl 0) 1 + c • Pi.single (Sum.inr 0) 1) = 0 ∧
        quadPlus 3 K v = 0} ≃ {p : (K × K) × ((K × K) × K) // hypSum (hypSum Q₁) p = 0} :=
    { toFun := fun v => ⟨((v.1 (.inl 1), v.1 (.inr 1)), ((v.1 (.inl 2), v.1 (.inr 2)),
        v.1 (.inl 0))), by
          have h1 := v.2.1
          have h2 := v.2.2
          rw [polar_std] at h1
          rw [quadPlus_apply, Fin.sum_univ_three] at h2
          simp only [hypSum_apply, hQ₁]
          linear_combination h2 - v.1 (.inl 0) * h1⟩
      invFun := fun p => ⟨Sum.elim ![p.1.2.2, p.1.1.1, p.1.2.1.1]
        ![-c * p.1.2.2, p.1.1.2, p.1.2.1.2], by
          have h := p.2
          simp only [hypSum_apply, hQ₁] at h
          refine ⟨?_, ?_⟩
          · rw [polar_std]
            simp
          · rw [quadPlus_apply, Fin.sum_univ_three]
            simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
            linear_combination h⟩
      left_inv := fun v => by
        apply Subtype.ext
        have h1 := v.2.1
        rw [polar_std] at h1
        funext s
        rcases s with i | i <;> fin_cases i <;> simp
        linear_combination -h1
      right_inv := fun p => by
        apply Subtype.ext
        simp }
  have hq : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
  have h0 : Nat.card {x : K // Q₁ x = 0} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨0, by simp [hQ₁]⟩⟩⟩
    have hx := x.2
    have hy := y.2
    rw [hQ₁] at hx hy
    have hx' : (x : K) = 0 := by simpa [hc] using hx
    have hy' : (y : K) = 0 := by simpa [hc] using hy
    rw [hx', hy']
  rw [Nat.card_congr e, card_singular_hypSum, card_singular_hypSum, h0, Nat.card_prod,
    Nat.card_prod]
  obtain ⟨n, hn⟩ : ∃ n, Nat.card K = n + 1 := ⟨Nat.card K - 1, by omega⟩
  rw [hn, Nat.add_sub_cancel]
  ring

theorem card_perp_singular {w : Fin 3 ⊕ Fin 3 → K} (hw : quadPlus 3 K w ≠ 0) :
    Nat.card {v : Fin 3 ⊕ Fin 3 → K // polar (quadPlus 3 K) v w = 0 ∧ quadPlus 3 K v = 0} =
      Nat.card K ^ 4 := by
  have hw₀ := quadPlus_std (quadPlus 3 K w)
  have hw0 : w ≠ 0 := fun h => hw (by rw [h, map_zero])
  have hw₀0 : (Pi.single (Sum.inl 0) 1 + quadPlus 3 K w • Pi.single (Sum.inr 0) 1 :
      Fin 3 ⊕ Fin 3 → K) ≠ 0 := fun h => hw (by rw [← hw₀, h, map_zero])
  obtain ⟨g, hg, hgw⟩ := (orthogonal_norm_shell_transitive (nondegenerate_polarBilin_quadPlus 3 K)
    ⟨flag 3 K 2, finrank_flag_of_le (by norm_num), flag_singular 2⟩).1 w _ hw0 hw₀0 hw₀.symm
  have hO := orthElementaryGroup_le _ hg
  rw [← card_perp_singular_std hw]
  refine Nat.card_congr
    { toFun := fun v => ⟨g v.1, ?_, ?_⟩
      invFun := fun v => ⟨g.symm v.1, ?_, ?_⟩
      left_inv := fun v => Subtype.ext (g.symm_apply_apply v.1)
      right_inv := fun v => Subtype.ext (g.apply_symm_apply v.1) }
  · rw [← hgw, polar_map_of_mem hO]
    exact v.2.1
  · rw [map_of_mem hO]
    exact v.2.2
  · rw [← polar_map_of_mem hO, g.apply_symm_apply, hgw]
    exact v.2.1
  · rw [← map_of_mem hO, g.apply_symm_apply]
    exact v.2.2

theorem card_singular_three_three' :
    Nat.card (singularSubspaces (quadPlus 3 K) 3) =
      2 * (Nat.card K + 1) * (Nat.card K ^ 2 + 1) := by
  have h := card_singularSubspaces_top (K := K) (r := 3) (by norm_num)
  rw [show Finset.Icc 1 (3 - 1) = {1, 2} by decide, Finset.prod_pair (by norm_num), pow_one] at h
  have h' : ((Nat.card (singularSubspaces (quadPlus 3 K) 3) : ℕ) : ℚ) =
      ((2 * (Nat.card K + 1) * (Nat.card K ^ 2 + 1) : ℕ) : ℚ) := by
    rw [h]
    push_cast
    ring
  exact_mod_cast h'

theorem card_fixed_maximal_lt_split (h3 : 3 ≤ Nat.card K) {w' : (K × K) × (Fin 3 ⊕ Fin 3 → K)}
    (hwe : polar (hypSum (quadPlus 3 K)) ((1, 0), 0) w' = 0) (hw' : hypSum (quadPlus 3 K) w' ≠ 0)
    {A : ((K × K) × (Fin 3 ⊕ Fin 3 → K)) ≃ₗ[K] ((K × K) × (Fin 3 ⊕ Fin 3 → K))}
    (hA : ∀ x, A x = x + polar (hypSum (quadPlus 3 K)) x ((1, 0), 0) • w' -
      (polar (hypSum (quadPlus 3 K)) x w' +
        hypSum (quadPlus 3 K) w' * polar (hypSum (quadPlus 3 K)) x ((1, 0), 0)) • ((1, 0), 0)) :
    Nat.card {M // M ∈ singularSubspaces (hypSum (quadPlus 3 K)) 4 ∧
        M.map (A : _ →ₗ[K] _) = M} <
      Nat.card {L // L ∈ singularSubspaces (hypSum (quadPlus 3 K)) 1 ∧
        L.map (A : _ →ₗ[K] _) = L} := by
  have hw12 : w'.1.2 = 0 := by
    have h := hwe
    rw [polar_comm, polar_hypSum_e] at h
    exact h
  have hQ3 : quadPlus 3 K w'.2 ≠ 0 := by
    rw [hypSum_apply, hw12, mul_zero, zero_add] at hw'
    exact hw'
  have h1 := card_fixed_maximal_le_split hwe hw' hA
  have h2 := card_le_card_fixed_lines_split hwe hA
  rw [card_perp_singular hQ3] at h2
  rw [card_singular_three_three'] at h1
  have hlt : 2 * (Nat.card K + 1) * (Nat.card K ^ 2 + 1) < Nat.card K ^ 4 := by
    nlinarith
  omega

end Split

section Plus

variable {K : Type*} [Field K] [Finite K]

theorem card_fixed_maximal_lt_card_fixed_lines (h3 : 3 ≤ Nat.card K) {u w : Fin 4 ⊕ Fin 4 → K}
    (hu0 : u ≠ 0) (hQu : quadPlus 4 K u = 0) (huw : polar (quadPlus 4 K) u w = 0)
    (hQw : quadPlus 4 K w ≠ 0) {A : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (hA : ∀ x, A x = x + polar (quadPlus 4 K) x u • w -
      (polar (quadPlus 4 K) x w + quadPlus 4 K w * polar (quadPlus 4 K) x u) • u) :
    Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ M.map (A : _ →ₗ[K] _) = M} <
      Nat.card {L // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧ L.map (A : _ →ₗ[K] _) = L} := by
  have he₁ : quadPlus 4 K (Pi.single (Sum.inl 0) 1) = 0 := by
    rw [quadPlus_apply]
    simp
  have he₁0 : (Pi.single (Sum.inl 0) 1 : Fin 4 ⊕ Fin 4 → K) ≠ 0 := fun h =>
    (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrFun h (Sum.inl 0))
  obtain ⟨g, hg, hgu⟩ := (orthogonal_norm_shell_transitive (nondegenerate_polarBilin_quadPlus 4 K)
    ⟨flag 4 K 2, finrank_flag_of_le (by norm_num), flag_singular 2⟩).1 u _ hu0 he₁0
      (by rw [hQu, he₁])
  have hO := orthElementaryGroup_le _ hg
  let r : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (K × K) × (Fin 3 ⊕ Fin 3 → K) :=
    g.trans (plusIsometry K 3).toLinearEquiv
  have hr : ∀ x, hypSum (quadPlus 3 K) (r x) = quadPlus 4 K x := fun x => by
    change hypSum (quadPlus 3 K) (plusIsometry K 3 (g x)) = _
    rw [(plusIsometry K 3).map_app, map_of_mem hO]
  have hru : r u = ((1, 0), 0) := by
    change plusSplit K 3 (g u) = _
    rw [hgu]
    refine Prod.ext (Prod.ext ?_ ?_) (funext fun s => ?_)
    · simp [plusSplit]
    · simp [plusSplit]
    · rcases s with i | i <;> simp [plusSplit]
  let A' := r.symm.trans (A.trans r)
  have hA' := eichler_transport r hr hA
  rw [hru] at hA'
  have hcard : ∀ k, Nat.card {L // L ∈ singularSubspaces (hypSum (quadPlus 3 K)) k ∧
      L.map (A' : _ →ₗ[K] _) = L} =
        Nat.card {L // L ∈ singularSubspaces (quadPlus 4 K) k ∧ L.map (A : _ →ₗ[K] _) = L} :=
    fun k => card_invariant_singular_congr r hr (fun x => by simp [A']) k
  rw [← hcard 4, ← hcard 1]
  refine card_fixed_maximal_lt_split h3 (w' := r w) ?_ ?_ hA'
  · rw [← hru, polar_isometry r hr, huw]
  · rw [hr]
    exact hQw

end Plus

end CFSG.HardMathSupport.Timmesfeld.DFour

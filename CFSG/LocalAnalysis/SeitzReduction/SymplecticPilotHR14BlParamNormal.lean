module

public import CFSG.RankThree.PartOne.KC.AlternatingSymplecticBasis
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpALevi

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Module Matrix
open LinearMap (BilinForm)
open CFSG.RankThree.PartOne.KCAlternating (IsSymplecticBasis IsSymplecticBasis.apply_inr_inl
  exists_isSymplecticBasis)

variable {K : Type} [Field K] {U : Type*} [AddCommGroup U] [Module K U] {ω : BilinForm K U}

theorem linearIndependent_of_symplecticGram (hω : ω.IsAlt) {m : ℕ} {v : Fin m ⊕ Fin m → U}
    (h1 : ∀ i i', ω (v (Sum.inl i)) (v (Sum.inl i')) = 0)
    (h2 : ∀ i i', ω (v (Sum.inr i)) (v (Sum.inr i')) = 0)
    (h3 : ∀ i i', ω (v (Sum.inl i)) (v (Sum.inr i')) = if i = i' then 1 else 0) :
    LinearIndependent K v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg z
  have hpair : ∀ y, ∑ x, g x * ω (v x) (v y) = 0 := by
    intro y
    have := congrArg (fun u => ω u (v y)) hg
    simpa only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, map_zero, LinearMap.zero_apply] using this
  rcases z with i | i
  · have h := hpair (Sum.inr i)
    rw [Fintype.sum_sum_type] at h
    simp only [h3, h2, mul_zero, Finset.sum_const_zero, add_zero, mul_ite, mul_one,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
    exact h
  · have h := hpair (Sum.inl i)
    rw [Fintype.sum_sum_type] at h
    have h4 : ∀ i', ω (v (Sum.inr i')) (v (Sum.inl i)) = if i' = i then -1 else 0 := by
      intro i'
      rw [← hω.neg_eq, h3]
      split_ifs with h5 h6 h6
      · rfl
      · exact absurd h5.symm h6
      · exact absurd h6.symm h5
      · rw [neg_zero]
    simp only [h1, h4, mul_zero, Finset.sum_const_zero, zero_add, mul_ite, mul_neg, mul_one,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, neg_eq_zero] at h
    exact h

theorem exists_basis_of_symplecticGram [FiniteDimensional K U] (hω : ω.IsAlt) {m : ℕ}
    (hU : finrank K U = 2 * m) (v : Fin m ⊕ Fin m → U)
    (h1 : ∀ i i', ω (v (Sum.inl i)) (v (Sum.inl i')) = 0)
    (h2 : ∀ i i', ω (v (Sum.inr i)) (v (Sum.inr i')) = 0)
    (h3 : ∀ i i', ω (v (Sum.inl i)) (v (Sum.inr i')) = if i = i' then 1 else 0) :
    ∃ b : Basis (Fin m ⊕ Fin m) K U, ⇑b = v ∧ IsSymplecticBasis ω b := by
  have hli := linearIndependent_of_symplecticGram hω h1 h2 h3
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by
    rw [Fintype.card_sum, Fintype.card_fin, hU, two_mul])
  refine ⟨Basis.mk hli hsp.ge, Basis.coe_mk hli hsp.ge, ?_⟩
  refine ⟨fun i i' => ?_, fun i i' => ?_, fun i i' => ?_⟩ <;> rw [Basis.coe_mk]
  · exact h1 i i'
  · exact h2 i i'
  · exact h3 i i'

section Nil

variable [CharP K 2]

theorem nf_nil_nil {x : U →ₗ[K] U} (hxx : ∀ u, x (x u) = u) (u : U) :
    (x - LinearMap.id : U →ₗ[K] U) ((x - LinearMap.id : U →ₗ[K] U) u) = 0 := by
  have h2 : ∀ y : U, y + y = 0 := fun y => by
    rw [← two_smul K y, CharTwo.two_eq_zero, zero_smul]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hxx]
  rw [show u - x u - (x u - u) = (u + u) - (x u + x u) by abel, h2, h2, sub_zero]

end Nil

theorem nf_nil_adj {x : U →ₗ[K] U} (hx : ∀ u v, ω (x u) (x v) = ω u v)
    (hxx : ∀ u, x (x u) = u) (u v : U) :
    ω ((x - LinearMap.id : U →ₗ[K] U) u) v = ω u ((x - LinearMap.id : U →ₗ[K] U) v) := by
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, LinearMap.sub_apply]
  have h : ω (x u) v = ω u (x v) := by
    rw [← hx u (x v), hxx]
  rw [h]

theorem nf_nil_alt (hω : ω.IsAlt) {x : U →ₗ[K] U} (ha : ∀ u, ω u (x u) = 0) (u : U) :
    ω u ((x - LinearMap.id : U →ₗ[K] U) u) = 0 := by
  rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub, ha, hω u, sub_zero]

theorem nf_exists_betaBasis [CharP K 2] [FiniteDimensional K U] (hω : ω.IsAlt)
    (hωn : ω.Nondegenerate) {N : U →ₗ[K] U} (hNadj : ∀ u v, ω (N u) v = ω u (N v))
    (hNalt : ∀ u, ω u (N u) = 0) {j : ℕ} (hrank : finrank K (LinearMap.range N) = 2 * j) :
    ∃ c : Fin j ⊕ Fin j → U,
      (∀ r s, ω (N (c r)) (c s) = if s = r.swap then 1 else 0) ∧
      ∀ u, ∃ a : Fin j ⊕ Fin j → K, N u = ∑ r, a r • N (c r) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker N)
  set β : BilinForm K U := ω.comp N LinearMap.id with hβ
  have hβapp : ∀ u v, β u v = ω (N u) v := fun u v => rfl
  have hβsymm : ∀ u v, β u v = β v u := by
    intro u v
    rw [hβapp, hβapp, hNadj, ← hω.neg_eq, CharTwo.neg_eq]
  have hdec : ∀ u : U, ∃ k c, N k = 0 ∧ c ∈ C ∧ u = k + c := by
    intro u
    have hu : u ∈ LinearMap.ker N ⊔ C := by
      rw [hC.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨k, hk, c, hc, rfl⟩ := Submodule.mem_sup.1 hu
    exact ⟨k, c, hk, hc, rfl⟩
  set β' := β.restrict C with hβ'
  have hβ'alt : β'.IsAlt := fun c => by
    change ω (N c) c = 0
    rw [hNadj]
    exact hNalt c
  have hleft : ∀ c : C, (∀ c' : C, β' c c' = 0) → c = 0 := by
    intro c hc
    have hNc : N c = 0 := by
      apply hωn.1
      intro u
      obtain ⟨k, c', hk, hc', rfl⟩ := hdec u
      have h1 : ω (N c) c' = 0 := hc ⟨c', hc'⟩
      rw [map_add, hNadj c k, hk, map_zero, zero_add]
      exact h1
    have hcC := c.2
    have h0 : (c : U) = 0 :=
      (Submodule.disjoint_def.1 hC.disjoint) _ (LinearMap.mem_ker.2 hNc) hcC
    exact Subtype.ext h0
  have hβ'nd : β'.Nondegenerate := by
    refine ⟨hleft, fun c' hc' => hleft c' fun c => ?_⟩
    have h1 := hc' c
    change β c' c = 0
    rw [hβsymm]
    exact h1
  have hCdim : finrank K C = 2 * j := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hC
    have h2 := LinearMap.finrank_range_add_finrank_ker N
    omega
  obtain ⟨m, b, hm, hb⟩ := exists_isSymplecticBasis hβ'alt hβ'nd
  obtain rfl : m = j := by omega
  refine ⟨fun r => (b r : U), fun r s => ?_, fun u => ?_⟩
  · change β' (b r) (b s) = _
    rcases r with i | i <;> rcases s with i' | i'
    · rw [hb.1 i i']
      simp
    · rw [hb.2.2 i i']
      simp [eq_comm]
    · rw [hb.apply_inr_inl hβ'alt i i']
      simp [eq_comm, CharTwo.neg_eq]
    · rw [hb.2.1 i i']
      simp
  · obtain ⟨k, c, hk, hc, rfl⟩ := hdec u
    refine ⟨fun r => b.repr ⟨c, hc⟩ r, ?_⟩
    have hsum := congrArg Subtype.val (b.sum_repr ⟨c, hc⟩)
    rw [Submodule.coe_sum] at hsum
    simp only [Submodule.coe_smul] at hsum
    rw [map_add, hk, zero_add]
    calc N c = N (∑ x, (b.repr ⟨c, hc⟩) x • (b x : U)) := by rw [hsum]
      _ = _ := by
        rw [map_sum]
        simp only [map_smul]

theorem nf_exists_gramSchmidt [CharP K 2] (hω : ω.IsAlt) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {idx : ι → ℕ} (hidx : Function.Injective idx) {e f : ι → U}
    (hef : ∀ r s, ω (e r) (f s) = if r = s then 1 else 0) (hee : ∀ r s, ω (e r) (e s) = 0) :
    ∃ f' : ι → U, (∀ r s, ω (e r) (f' s) = if r = s then 1 else 0) ∧
      (∀ r s, ω (f' r) (f' s) = 0) ∧ ∀ r, ∃ a : ι → K, f' r = f r + ∑ s, a s • e s := by
  set m : ι → ι → K := fun r s => if idx r < idx s then ω (f r) (f s) else 0 with hm
  have hfe : ∀ r s, ω (f r) (e s) = if s = r then 1 else 0 := by
    intro r s
    rw [← hω.neg_eq, hef, CharTwo.neg_eq]
  have hffs : ∀ r s, ω (f s) (f r) = ω (f r) (f s) := by
    intro r s
    rw [← hω.neg_eq, CharTwo.neg_eq]
  refine ⟨fun r => f r + ∑ s, m r s • e s, fun r s => ?_, fun r s => ?_, fun r => ⟨m r, rfl⟩⟩
  · simp only [map_add, map_sum, map_smul, hee, smul_eq_mul, mul_zero, Finset.sum_const_zero,
      add_zero, hef]
  · simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, hee, hef, hfe, mul_zero, Finset.sum_const_zero, add_zero,
      mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have h2 : ∀ a : K, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
    rcases lt_trichotomy (idx r) (idx s) with h | h | h
    · simp only [hm, ite_eq_left h, ite_eq_right (lt_asymm h)]
      rw [add_zero, h2]
    · obtain rfl := hidx h
      simp only [hm, lt_irrefl, ite_false, add_zero]
      exact hω (f r)
    · simp only [hm, ite_eq_right (lt_asymm h), ite_eq_left h]
      rw [add_zero, hffs, h2]

theorem nf_exists_complement [CharP K 2] [FiniteDimensional K U] (hω : ω.IsAlt)
    (hωn : ω.Nondegenerate) {ι : Type*} [Fintype ι] [DecidableEq ι] {e f : ι → U}
    (hef : ∀ r s, ω (e r) (f s) = if r = s then 1 else 0) (hee : ∀ r s, ω (e r) (e s) = 0)
    (hff : ∀ r s, ω (f r) (f s) = 0) :
    ∃ (m : ℕ) (d : Fin m ⊕ Fin m → U), 2 * m + 2 * Fintype.card ι = finrank K U ∧
      (∀ z r, ω (e r) (d z) = 0 ∧ ω (f r) (d z) = 0) ∧
      (∀ i i', ω (d (Sum.inl i)) (d (Sum.inl i')) = 0) ∧
      (∀ i i', ω (d (Sum.inr i)) (d (Sum.inr i')) = 0) ∧
      (∀ i i', ω (d (Sum.inl i)) (d (Sum.inr i')) = if i = i' then 1 else 0) := by
  have hfe : ∀ r s, ω (f r) (e s) = if s = r then 1 else 0 := by
    intro r s
    rw [← hω.neg_eq, hef, CharTwo.neg_eq]
  have hswap : ∀ u v, ω v u = ω u v := by
    intro u v
    rw [← hω.neg_eq, CharTwo.neg_eq]
  set Φ : U →ₗ[K] (ι ⊕ ι → K) :=
    LinearMap.pi (fun z => Sum.elim (fun r => ω (e r)) (fun r => ω (f r)) z) with hΦ
  have hΦapp : ∀ u z, Φ u z = Sum.elim (fun r => ω (e r) u) (fun r => ω (f r) u) z := by
    intro u z
    rcases z with r | r <;> rfl
  set W := LinearMap.ker Φ with hW
  have hmemW : ∀ u, u ∈ W ↔ (∀ r, ω (e r) u = 0) ∧ ∀ r, ω (f r) u = 0 := by
    intro u
    rw [hW, LinearMap.mem_ker, funext_iff]
    simp only [hΦapp, Pi.zero_apply, Sum.forall, Sum.elim_inl, Sum.elim_inr]
  have hΦsurj : LinearMap.range Φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro g
    refine ⟨∑ r, g (Sum.inl r) • f r + ∑ r, g (Sum.inr r) • e r, ?_⟩
    funext z
    rw [hΦapp]
    rcases z with r | r
    · simp only [Sum.elim_inl, map_add, map_sum, map_smul, hef, hee, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const_zero,
        add_zero]
    · simp only [Sum.elim_inr, map_add, map_sum, map_smul, hff, hfe, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero,
        zero_add]
  have hWdim : finrank K W + 2 * Fintype.card ι = finrank K U := by
    have h := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hΦsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_sum] at h
    rw [← hW] at h
    omega
  have hproj : ∀ u, u - ∑ r, (ω (e r) u • f r + ω (f r) u • e r) ∈ W := by
    intro u
    rw [hmemW]
    have h2 : ∀ a : K, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
    refine ⟨fun s => ?_, fun s => ?_⟩
    · simp only [map_sub, map_sum, map_add, map_smul, hef, hee, smul_eq_mul, mul_ite, mul_one,
        mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        Finset.sum_const_zero, add_zero, sub_self]
    · simp only [map_sub, map_sum, map_add, map_smul, hff, hfe, smul_eq_mul, mul_ite, mul_one,
        mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        Finset.sum_const_zero, zero_add]
      rw [sub_eq_add_neg, CharTwo.neg_eq, h2]
  have hleft : ∀ w : W, (∀ w' : W, ω.restrict W w w' = 0) → w = 0 := by
    intro w hw
    have hwW := (hmemW w).1 w.2
    apply Subtype.ext
    apply hωn.1
    intro u
    have h1 : ω w (u - ∑ r, (ω (e r) u • f r + ω (f r) u • e r)) = 0 := hw ⟨_, hproj u⟩
    have h3 : ω w (∑ r, (ω (e r) u • f r + ω (f r) u • e r)) = 0 := by
      simp only [map_sum, map_add, map_smul, smul_eq_mul]
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [hswap (f r) (w : U), hswap (e r) (w : U), hwW.1 r, hwW.2 r, mul_zero, mul_zero,
        add_zero]
    rw [map_sub, h3, sub_zero] at h1
    exact h1
  have hWalt : (ω.restrict W).IsAlt := fun w => hω w
  have hWnd : (ω.restrict W).Nondegenerate := by
    refine ⟨hleft, fun w' hw' => hleft w' fun w => ?_⟩
    have h1 := hw' w
    change ω w' w = 0
    rw [hswap]
    exact h1
  obtain ⟨m, d, hm, hd⟩ := exists_isSymplecticBasis hWalt hWnd
  refine ⟨m, fun z => (d z : U), by omega, fun z r => ?_, hd.1, hd.2.1, hd.2.2⟩
  have := (hmemW _).1 (d z).2
  exact ⟨this.1 r, this.2 r⟩

open CFSG.ClassicalInvolution.Models.SymplecticPairs (par sgn) in
theorem exists_isSymplecticBasis_toMatrix_eq_spARep [CharP K 2] [FiniteDimensional K U]
    (hω : ω.IsAlt) (hωn : ω.Nondegenerate) {n j : ℕ} (hU : finrank K U = 2 * n)
    {x : U →ₗ[K] U} (hx : ∀ u v, ω (x u) (x v) = ω u v) (hxx : ∀ u, x (x u) = u)
    (ha : ∀ u, ω u (x u) = 0)
    (hrank : finrank K (LinearMap.range (x - LinearMap.id : U →ₗ[K] U)) = 2 * j) :
    ∃ b : Basis (Fin n ⊕ Fin n) K U, IsSymplecticBasis ω b ∧
      LinearMap.toMatrix b b x = fromBlocks 1 (spARepMat n j) 0 1 := by
  set N : U →ₗ[K] U := x - LinearMap.id with hN
  have hNN : ∀ u, N (N u) = 0 := nf_nil_nil hxx
  have hNadj : ∀ u v, ω (N u) v = ω u (N v) := nf_nil_adj hx hxx
  have hNalt : ∀ u, ω u (N u) = 0 := nf_nil_alt hω ha
  have hxN : ∀ u, x u = u + N u := fun u => by
    rw [hN, LinearMap.sub_apply, LinearMap.id_apply]
    abel
  have hswap : ∀ u v, ω v u = ω u v := fun u v => by rw [← hω.neg_eq, CharTwo.neg_eq]
  obtain ⟨c, hc, hspan⟩ := nf_exists_betaBasis hω hωn hNadj hNalt hrank
  set e : Fin j ⊕ Fin j → U := fun r => N (c r.swap) with he
  have hNc : ∀ r, N (c r) = e r.swap := fun r => by
    change N (c r) = N (c r.swap.swap)
    rw [Sum.swap_swap]
  have hef : ∀ r s, ω (e r) (c s) = if r = s then 1 else 0 := by
    intro r s
    rw [he]
    dsimp only
    rw [hc, Sum.swap_swap]
    by_cases h : r = s
    · rw [ite_eq_left h.symm, ite_eq_left h]
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h]
  have hee : ∀ r s, ω (e r) (e s) = 0 := by
    intro r s
    rw [he]
    dsimp only
    rw [hNadj, hNN, map_zero]
  have hNe : ∀ r, N (e r) = 0 := fun r => hNN _
  set idx : Fin j ⊕ Fin j → ℕ := Sum.elim (fun i => i.val) (fun i => j + i.val) with hidxdef
  have hidx : Function.Injective idx := by
    intro a b h
    rcases a with i | i <;> rcases b with i' | i' <;>
      simp only [hidxdef, Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (Fin.ext h)
    · exact absurd h (by have := i.isLt; omega)
    · exact absurd h (by have := i'.isLt; omega)
    · exact congrArg Sum.inr (Fin.ext (by omega))
  obtain ⟨f', hef', hff', hf'⟩ := nf_exists_gramSchmidt hω hidx hef hee
  have hNf' : ∀ r, N (f' r) = e r.swap := by
    intro r
    obtain ⟨a, har⟩ := hf' r
    rw [har, map_add, map_sum, hNc]
    simp only [map_smul, hNe, smul_zero, Finset.sum_const_zero, add_zero]
  obtain ⟨m, d, hdim, hdW, hd1, hd2, hd3⟩ := nf_exists_complement hω hωn hef' hee hff'
  have hcard : Fintype.card (Fin j ⊕ Fin j) = 2 * j := by simp [two_mul]
  rw [hcard, hU] at hdim
  have hjn : 2 * j ≤ n := by omega
  obtain rfl : m = n - 2 * j := by omega
  have hNd : ∀ z, N (d z) = 0 := by
    intro z
    apply hωn.1
    intro u
    rw [hNadj]
    obtain ⟨a, hu⟩ := hspan u
    rw [hu, map_sum]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [map_smul, smul_eq_mul, hNc, hswap (e r.swap) (d z), (hdW z r.swap).1, mul_zero]
  set σ := spAIndexEquiv (n := n) (j := j) hjn with hσ
  set vE : (Fin j ⊕ Fin j) ⊕ Fin (n - 2 * j) → U := Sum.elim e (fun i => d (Sum.inl i))
    with hvE
  set vF : (Fin j ⊕ Fin j) ⊕ Fin (n - 2 * j) → U := Sum.elim f' (fun i => d (Sum.inr i))
    with hvF
  have hEE : ∀ a a', ω (vE a) (vE a') = 0 := by
    rintro (r | i) (r' | i')
    · exact hee r r'
    · exact (hdW _ r).1
    · change ω (d (Sum.inl i)) (e r') = 0
      rw [hswap (e r') (d (Sum.inl i))]
      exact (hdW _ r').1
    · exact hd1 i i'
  have hFF : ∀ a a', ω (vF a) (vF a') = 0 := by
    rintro (r | i) (r' | i')
    · exact hff' r r'
    · exact (hdW _ r).2
    · change ω (d (Sum.inr i)) (f' r') = 0
      rw [hswap (f' r') (d (Sum.inr i))]
      exact (hdW _ r').2
    · exact hd2 i i'
  have hEF : ∀ a a', ω (vE a) (vF a') = if a = a' then 1 else 0 := by
    rintro (r | i) (r' | i')
    · change ω (e r) (f' r') = _
      rw [hef' r r']
      simp only [Sum.inl.injEq]
    · change ω (e r) (d (Sum.inr i')) = _
      rw [(hdW _ r).1]
      simp
    · change ω (d (Sum.inl i)) (f' r') = _
      rw [hswap (f' r') (d (Sum.inl i)), (hdW _ r').2]
      simp
    · change ω (d (Sum.inl i)) (d (Sum.inr i')) = _
      rw [hd3 i i']
      simp only [Sum.inr.injEq]
  set v : Fin n ⊕ Fin n → U := Sum.elim (fun k => vE (σ.symm k)) (fun k => vF (σ.symm k))
    with hv
  obtain ⟨b, hbv, hb⟩ := exists_basis_of_symplecticGram hω hU v
    (fun k k' => hEE _ _) (fun k k' => hFF _ _) (fun k k' => by
      change ω (vE (σ.symm k)) (vF (σ.symm k')) = _
      rw [hEF]
      by_cases h : k = k'
      · rw [ite_eq_left (congrArg σ.symm h), ite_eq_left h]
      · rw [ite_eq_right (fun h' => h (σ.symm.injective h')), ite_eq_right h])
  refine ⟨b, hb, ?_⟩
  have hNvE : ∀ a, N (vE a) = 0 := by
    rintro (r | i)
    · exact hNe r
    · exact hNd _
  have hsgn : ∀ a : Fin j ⊕ Fin j, sgn K a = 1 := by
    rintro (i | i)
    · rfl
    · change -1 = (1 : K)
      rw [CharTwo.neg_eq]
  have hNvF : ∀ a, N (vF a) = ∑ a', (fromBlocks
      (CFSG.ClassicalInvolution.Models.SymplecticPairs.gram K j) 0 0 0) a' a • vE a' := by
    rintro (r | i)
    · rw [Fintype.sum_sum_type]
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.zero_apply, zero_smul,
        Finset.sum_const_zero, add_zero,
        CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply]
      change N (f' r) = _
      rw [hNf', Finset.sum_eq_single r.swap]
      · have hpar : par r.swap = r := Sum.swap_swap r
        rw [ite_eq_left hpar.symm, hsgn, one_smul]
        rfl
      · intro r' _ hr'
        have : r ≠ par r' := fun h => hr' (by rw [h]; exact (Sum.swap_swap r').symm)
        rw [ite_eq_right this, zero_smul]
      · simp
    · rw [Fintype.sum_sum_type]
      simp only [fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply, zero_smul,
        Finset.sum_const_zero, add_zero]
      exact hNd _
  have hxv : x = Matrix.toLin b b (fromBlocks 1 (spARepMat n j) 0 1) := by
    apply b.ext
    intro col
    rw [Matrix.toLin_self, hbv, Fintype.sum_sum_type]
    rcases col with k | k
    · simp only [hv, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₂₁,
        Matrix.zero_apply, zero_smul, Finset.sum_const_zero, add_zero, Matrix.one_apply,
        ite_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [hxN, hNvE, add_zero]
    · simp only [hv, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₂, fromBlocks_apply₂₂,
        Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
      rw [hxN, hNvF, add_comm, spARepMat_eq_submatrix hjn]
      congr 1
      simp only [Matrix.submatrix_apply]
      exact (σ.symm.sum_comp (fun a' => (fromBlocks
        (CFSG.ClassicalInvolution.Models.SymplecticPairs.gram K j) 0 0 0) a' (σ.symm k) •
          vE a')).symm
  rw [hxv, LinearMap.toMatrix_toLin]

end CFSG.SeitzReduction.SymplecticPilot

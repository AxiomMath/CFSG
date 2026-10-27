module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public section

namespace CFSG.GroupTheory.SteinbergBK

open Module

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem semilinear_iterate_smul (σ : k ≃+* k) (a : V ≃+ V)
    (ha : ∀ (c : k) (v : V), a (c • v) = σ c • a v)
    (l : ℕ) (c : k) (v : V) : (⇑a)^[l] (c • v) = (σ ^ l) c • (⇑a)^[l] v := by
  induction l generalizing c v with
  | zero => simp
  | succ l ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ha, ih, pow_succ]
    rfl

theorem semilinear_iterate_sum (a : V ≃+ V) (l : ℕ) {ι : Type*} (s : Finset ι) (f : ι → V) :
    (⇑a)^[l] (∑ j ∈ s, f j) = ∑ j ∈ s, (⇑a)^[l] (f j) := by
  induction l with
  | zero => simp
  | succ l ih =>
    simp_rw [Function.iterate_succ_apply', ih, map_sum]

theorem dedekind_powers (σ : k ≃+* k) {h : ℕ} (hσ : orderOf σ = h) (lam : Fin h → k)
    (hlam : ∀ x : k, ∑ l : Fin h, lam l * (σ ^ (l : ℕ)) x = 0) : lam = 0 := by
  let f : Fin h → (k →* k) := fun l => (σ ^ (l : ℕ)).toMonoidHom
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : σ ^ (i : ℕ) = σ ^ (j : ℕ) := by
      ext x
      exact DFunLike.congr_fun hij x
    exact Fin.ext (pow_injOn_Iio_orderOf (hσ ▸ i.2) (hσ ▸ j.2) h1)
  have hli := (linearIndependent_monoidHom k k).comp f hf
  rw [Fintype.linearIndependent_iff] at hli
  funext l
  refine hli lam (funext fun x => ?_) l
  simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  exact hlam x

theorem exists_powers_dual_family [Fintype k] (σ : k ≃+* k) {h : ℕ} (hσ : orderOf σ = h) :
    ∃ c : k → k, ∀ l : Fin h, ∑ d : k, c d * (σ ^ (l : ℕ)) d = if (l : ℕ) = 0 then 1 else 0 := by
  set W := Submodule.span k (Set.range (fun d : k => fun l : Fin h => (σ ^ (l : ℕ)) d)) with hW
  have htop : W = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hWf⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.mpr hne)
    have hlam : (fun l : Fin h => f (Pi.single l 1)) = 0 := by
      refine dedekind_powers σ hσ _ fun x => ?_
      have hx : (fun l : Fin h => (σ ^ (l : ℕ)) x) ∈ W := Submodule.subset_span ⟨x, rfl⟩
      have h0 := hWf hx
      rw [LinearMap.mem_ker] at h0
      rw [← h0]
      conv_rhs => rw [← Finset.univ_sum_single (fun l : Fin h => (σ ^ (l : ℕ)) x)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [show Pi.single l ((σ ^ (l : ℕ)) x) = ((σ ^ (l : ℕ)) x) • (Pi.single l (1 : k) : Fin h → k)
        by rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]
    apply hf0
    refine LinearMap.pi_ext' fun l => LinearMap.ext_ring ?_
    simpa using congrFun hlam l
  have hmem : (fun l : Fin h => if (l : ℕ) = 0 then (1 : k) else 0) ∈ W := htop ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hmem
  refine ⟨c, fun l => ?_⟩
  have := congrFun hc l
  simpa [Finset.sum_apply, mul_comm] using this

abbrev semilinearFixedSubfield (σ : k ≃+* k) : Subfield k :=
  RingHom.eqLocusField (σ : k →+* k) (RingHom.id k)

@[expose] def semilinearFixedSubmodule (σ : k ≃+* k) (a : V ≃+ V)
    (ha : ∀ (c : k) (v : V), a (c • v) = σ c • a v) :
    Submodule (semilinearFixedSubfield σ) V where
  carrier := {v | a v = v}
  add_mem' := fun {v w} hv hw => by
    change a v = v at hv
    change a w = w at hw
    change a (v + w) = v + w
    rw [map_add, hv, hw]
  zero_mem' := map_zero a
  smul_mem' := fun c v hv => by
    change a v = v at hv
    change a (c • v) = c • v
    rw [Subfield.smul_def, ha, hv]
    congr 1
    exact (RingHom.mem_eqLocusField.mp c.2)

@[expose] def semilinearAvg (a : V ≃+ V) (h : ℕ) (v : V) : V := ∑ l ∈ Finset.range h, (⇑a)^[l] v

theorem apply_semilinearAvg (a : V ≃+ V) {h : ℕ} (hah : ∀ v, (⇑a)^[h] v = v) (v : V) :
    a (semilinearAvg a h v) = semilinearAvg a h v := by
  unfold semilinearAvg
  rw [map_sum]
  have hs : ∀ l, a ((⇑a)^[l] v) = (⇑a)^[l + 1] v := fun l =>
    (Function.iterate_succ_apply' (⇑a) l v).symm
  simp_rw [hs]
  cases h with
  | zero => simp
  | succ n =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ', hah, Function.iterate_zero, id]

theorem exists_semilinear_fixed_basis [Finite k] {h : ℕ} (σ : k ≃+* k) (hσ : orderOf σ = h)
    (hh : 0 < h)
    [FiniteDimensional k V] (a : V ≃+ V) (ha : ∀ (c : k) (v : V), a (c • v) = σ c • a v)
    (hah : ∀ v, (⇑a)^[h] v = v) :
    ∃ (n : ℕ) (b : Basis (Fin n) k V) (b₀ : Basis (Fin n) (semilinearFixedSubfield σ)
      (semilinearFixedSubmodule σ a ha)), ∀ i, (b₀ i : V) = b i := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have : Finite V := Module.finite_of_finite k
  set k₀ := semilinearFixedSubfield σ
  set C := semilinearFixedSubmodule σ a ha
  have : Module.Finite k₀ C := Module.Finite.of_finite
  set B₀ := Module.finBasis k₀ C
  set v : Fin (finrank k₀ C) → V := fun i => (B₀ i : V) with hv
  have hσh : σ ^ h = 1 := hσ ▸ pow_orderOf_eq_one σ
  have htrfix : ∀ x : k, σ (∑ l ∈ Finset.range h, (σ ^ l) x) = ∑ l ∈ Finset.range h, (σ ^ l) x := by
    intro x
    rw [map_sum]
    have hs : ∀ l, σ ((σ ^ l) x) = (σ ^ (l + 1)) x := fun l => by rw [pow_succ']; rfl
    simp_rw [hs]
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh.ne'
    rw [Finset.sum_range_succ, Finset.sum_range_succ', hσh, pow_zero]
  have havg_fixed : ∀ (x : k) (u : V), a u = u →
      semilinearAvg a h (x • u) = (∑ l ∈ Finset.range h, (σ ^ l) x) • u := by
    intro x u hu
    have hiter : ∀ l, (⇑a)^[l] u = u := fun l => Function.iterate_fixed hu l
    unfold semilinearAvg
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [semilinear_iterate_smul σ a ha, hiter]
  have havgsum : ∀ (f : Fin (finrank k₀ C) → V),
      semilinearAvg a h (∑ j, f j) = ∑ j, semilinearAvg a h (f j) := by
    intro f
    unfold semilinearAvg
    simp_rw [semilinear_iterate_sum]
    rw [Finset.sum_comm]
  have hli : LinearIndependent k v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have htr : ∀ y : k, ∀ j, ∑ l ∈ Finset.range h, (σ ^ l) (y * g j) = 0 := by
      intro y
      have h1 : ∑ j, (y * g j) • v j = 0 := by
        rw [← smul_zero y, ← hg, Finset.smul_sum]
        simp_rw [smul_smul]
      have h2 := congrArg (semilinearAvg a h) h1
      rw [havgsum, show semilinearAvg a h 0 = 0 by simp [semilinearAvg]] at h2
      simp_rw [hv, havg_fixed _ _ (B₀ _).2] at h2
      have hfix : ∀ j, (∑ l ∈ Finset.range h, (σ ^ l) (y * g j)) ∈ k₀ := fun j =>
        RingHom.mem_eqLocusField.mpr (htrfix _)
      have h3 : ∑ j, (⟨_, hfix j⟩ : k₀) • B₀ j = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum, Submodule.coe_zero]
        simpa only [Submodule.coe_smul_of_tower, Subfield.smul_def] using h2
      have h4 := (Fintype.linearIndependent_iff.mp B₀.linearIndependent) _ h3
      intro j
      exact congrArg Subtype.val (h4 j)
    have hlam : (fun l : Fin h => (σ ^ (l : ℕ)) (g i)) = 0 := by
      refine dedekind_powers σ hσ _ fun x => ?_
      have := htr x i
      rw [Finset.sum_range] at this
      rw [← this]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, mul_comm]
    have := congrFun hlam ⟨0, hh⟩
    simpa using this
  obtain ⟨c, hc⟩ := exists_powers_dual_family σ hσ
  have hsp : ⊤ ≤ Submodule.span k (Set.range v) := by
    intro w _
    have hw : w = ∑ d : k, c d • semilinearAvg a h (d • w) := by
      unfold semilinearAvg
      simp_rw [semilinear_iterate_smul σ a ha, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      rw [Finset.sum_range]
      rw [Finset.sum_eq_single (⟨0, hh⟩ : Fin h)]
      · rw [hc]
        simp
      · intro l _ hl
        rw [hc, ite_eq_right_iff.mpr (fun h0 => absurd (Fin.ext h0) hl), zero_smul]
      · intro h0
        exact absurd (Finset.mem_univ _) h0
    rw [hw]
    refine Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ ?_
    have hmemC : semilinearAvg a h (d • w) ∈ C := apply_semilinearAvg a hah _
    rw [show semilinearAvg a h (d • w) = ((⟨_, hmemC⟩ : C) : V) from rfl, ← B₀.sum_repr ⟨_, hmemC⟩,
      Submodule.coe_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Submodule.coe_smul_of_tower, Subfield.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  exact ⟨_, Basis.mk hli hsp, B₀, fun i => (Basis.mk_apply hli hsp i).symm⟩

theorem coprime_finite_field_semilinear_fixed_basis {p e h m : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    {k : Type*} [Field k] (hk : Nat.card k = p ^ e) (σ : k ≃+* k) (hσ : orderOf σ = h)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (hm : finrank k V = m)
    (a : V ≃+ V) (ha : ∀ (c : k) (v : V), a (c • v) = σ c • a v)
    (hah : ∀ v : V, (⇑a)^[h] v = v) :
    h ∣ e ∧ Nat.card (semilinearFixedSubfield σ) = p ^ (e / h) ∧
      ∃ (b : Basis (Fin m) k V)
        (b₀ : Basis (Fin m) (semilinearFixedSubfield σ) (semilinearFixedSubmodule σ a ha)),
        (∀ i, a (b i) = b i) ∧ (∀ i, (b₀ i : V) = b i) ∧
        finrank (semilinearFixedSubfield σ) (semilinearFixedSubmodule σ a ha) = m ∧
        Nat.card (semilinearFixedSubmodule σ a ha) = p ^ (e * m / h) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hp.pos e).ne')
  obtain ⟨-, -, -, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp he hk
  obtain ⟨hdvd, S, hS, hScard⟩ := hA (Subgroup.zpowers σ)
  rw [Nat.card_zpowers, hσ] at hdvd hScard
  have hh : 0 < h := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hdvd
    omega
  have hk₀S : semilinearFixedSubfield σ = S := by
    apply SetLike.ext'
    rw [hS]
    ext x
    constructor
    · intro hx τ hτ
      have hx' : σ x = x := RingHom.mem_eqLocusField.mp hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
      have hstab : Subgroup.zpowers σ ≤ MulAction.stabilizer (k ≃+* k) x :=
        (Subgroup.zpowers_le (H := MulAction.stabilizer (k ≃+* k) x)).mpr hx'
      exact hstab (Subgroup.zpow_mem_zpowers σ n)
    · intro hx
      exact RingHom.mem_eqLocusField.mpr (hx σ (Subgroup.mem_zpowers σ))
  have hk₀card : Nat.card (semilinearFixedSubfield σ) = p ^ (e / h) := by rw [hk₀S, hScard]
  obtain ⟨n, b, b₀, hbb₀⟩ := exists_semilinear_fixed_basis σ hσ hh a ha hah
  have hn : n = m := by rw [← hm, finrank_eq_card_basis b, Fintype.card_fin]
  subst hn
  have : Finite V := Module.finite_of_finite k
  have : Module.Finite (semilinearFixedSubfield σ) (semilinearFixedSubmodule σ a ha) :=
    Module.Finite.of_finite
  have hfr : finrank (semilinearFixedSubfield σ) (semilinearFixedSubmodule σ a ha) = n := by
    rw [finrank_eq_card_basis b₀, Fintype.card_fin]
  refine ⟨hdvd, hk₀card, b, b₀, fun i => ?_, hbb₀, hfr, ?_⟩
  · rw [← hbb₀]
    exact (b₀ i).2
  · rw [Module.natCard_eq_pow_finrank (K := semilinearFixedSubfield σ), hk₀card, hfr, ← pow_mul,
      Nat.div_mul_right_comm hdvd]

end CFSG.GroupTheory.SteinbergBK

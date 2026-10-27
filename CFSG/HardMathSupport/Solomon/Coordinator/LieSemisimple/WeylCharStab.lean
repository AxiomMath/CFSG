module

public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
import CFSG.LieType.Chevalley.LangWeylChamberStabilizers

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable {τ : Tag} {K : Type} [Field K]

open Matrix in
private theorem exists_rootSpace_inner_eq (f : (Fin τ.rank → ℤ) →+ ℤ) :
    ∃ ν : RootSpace τ, ∀ v : Fin τ.rank → ℤ,
      inner ℝ (RootSpace.ofLattice v) ν = (f v : ℝ) := by
  have hdet : IsUnit (formMatrix τ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (posDef_formMatrix τ).isUnit
  refine ⟨RootSpace.ofPi ((formMatrix τ)⁻¹ *ᵥ fun j => (f (Pi.single j 1) : ℝ)), fun v => ?_⟩
  rw [RootSpace.inner_def, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec]
  have hv : v = ∑ j, v j • (Pi.single j 1 : Fin τ.rank → ℤ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hfv : f v = ∑ j, v j * f (Pi.single j 1) := by
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, smul_eq_mul]
  rw [hfv]
  simp [dotProduct, RootSpace.ofLattice]

private theorem weylAct_eq_of_forall_apply_eq {ν : RootSpace τ} {f : (Fin τ.rank → ℤ) →+ ℤ}
    (hν : ∀ v : Fin τ.rank → ℤ, inner ℝ (RootSpace.ofLattice v) ν = (f v : ℝ))
    {w : WeylGroup τ} (hw : ∀ v, f (w • v) = f v) : weylAct τ w ν = ν := by
  refine InnerProductSpace.ext_inner_left_basis (RootSpace.basis τ) fun i => ?_
  rw [RootSpace.basis_apply, hν, real_inner_comm, inner_weylAct_left, weylAct_ofLattice,
    real_inner_comm, hν]
  have := hw (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ))
  rw [smul_inv_smul] at this
  exact_mod_cast this.symm

theorem mem_stab_closure_of_invariant (f : (Fin τ.rank → ℤ) →+ ℤ) {w : WeylGroup τ}
    (hw : ∀ v, f (w • v) = f v) :
    w ∈ Subgroup.closure {r | ∃ (u : WeylGroup τ) (i : Fin τ.rank),
      f (u • (Pi.single i 1 : Fin τ.rank → ℤ)) = 0 ∧ r = u * simple τ i * u⁻¹} := by
  obtain ⟨ν, hν⟩ := exists_rootSpace_inner_eq f
  have hmem : w ∈ weylStabilizer τ ν := mem_weylStabilizer.2 (weylAct_eq_of_forall_apply_eq hν hw)
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.2.2.2.2 ν] at hmem
  refine Subgroup.closure_mono ?_ hmem
  rintro _ ⟨α, hα, hαν, rfl⟩
  obtain ⟨u, i, hu⟩ := isRoot_iff_exists_smul_single.1 hα
  refine ⟨u, i, ?_, rootReflection_eq_conj hu⟩
  have h := hν α
  rw [hαν, ← hu] at h
  exact_mod_cast h.symm

private theorem prod_zpow_eq_zpow_sum {G : Type*} [CommGroup G] {ι : Type*} (s : Finset ι)
    (g : G) (n : ι → ℤ) : ∏ i ∈ s, g ^ n i = g ^ ∑ i ∈ s, n i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, zpow_add, ih]

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
private theorem exists_zpow_form {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i ^ p = 1) :
    ∃ (g : Kˣ) (f₀ : (Fin τ.rank → ℤ) →+ ℤ), g ^ p = 1 ∧ ∀ v, rootChar a v = g ^ f₀ v := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity p K)
  have hc : ∀ i, ∃ c : ℤ, (g : Kˣ) ^ c = a i := fun i => by
    obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨a i, (mem_rootsOfUnity p (a i)).2 (ha i)⟩)
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩
  choose c hc using hc
  refine ⟨g, AddMonoidHom.mk' (fun v => ∑ i, c i * v i) fun x y => by
      simp [mul_add, Finset.sum_add_distrib], (mem_rootsOfUnity p (g : Kˣ)).1 g.2, fun v => ?_⟩
  simp only [rootChar, AddMonoidHom.mk'_apply, ← hc, ← zpow_mul, prod_zpow_eq_zpow_sum]

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
private theorem exists_invariant_form_of_coprime {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i ^ p = 1) {w : WeylGroup τ} (hw : w ∈ rootCharStabilizerSubgroup a)
    (hcop : Nat.Coprime (orderOf w) p) :
    ∃ f : (Fin τ.rank → ℤ) →+ ℤ, (∀ v, f (w • v) = f v) ∧ ∀ v, f v = 0 → rootChar a v = 1 := by
  obtain ⟨g, f₀, hgp, hχ⟩ := exists_zpow_form (K := K) hp ha
  set r := orderOf w
  set q := orderOf g
  have hqp : q ∣ p := orderOf_dvd_of_pow_eq_one hgp
  have hcop' : Nat.Coprime r q := Nat.Coprime.coprime_dvd_right hqp hcop
  obtain ⟨u, s, hus⟩ : IsCoprime (r : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 hcop'
  refine ⟨AddMonoidHom.mk' (fun v => u * ∑ j ∈ Finset.range r, f₀ ((w ^ j) • v)) fun x y => by
      simp [smul_add, Finset.sum_add_distrib, mul_add], ?_, ?_⟩
  · intro v
    simp only [AddMonoidHom.mk'_apply]
    congr 1
    have e : ∀ j : ℕ, f₀ (w ^ j • w • v) = f₀ (w ^ (j + 1) • v) := fun j => by
      rw [← mul_smul, ← pow_succ]
    simp only [e]
    have h1 := Finset.sum_range_succ (fun j => f₀ (w ^ j • v)) r
    have h2 := Finset.sum_range_succ' (fun j => f₀ (w ^ j • v)) r
    have h3 : w ^ r = 1 := pow_orderOf_eq_one w
    simp only [h3, one_smul, pow_zero] at h1 h2
    linarith
  · intro v hv
    simp only [AddMonoidHom.mk'_apply] at hv
    have hwv : ∀ (j : ℕ) (x : Fin τ.rank → ℤ), rootChar a ((w ^ j) • x) = rootChar a x :=
      fun j x => (Subgroup.pow_mem _ hw j : w ^ j ∈ rootCharStabilizerSubgroup a) x
    have hdvd : ∀ j : ℕ, (q : ℤ) ∣ f₀ v - f₀ ((w ^ j) • v) := fun j => by
      have h := hwv j v
      rw [hχ, hχ] at h
      exact Int.modEq_iff_dvd.1 (zpow_eq_zpow_iff_modEq.1 h)
    set S := ∑ j ∈ Finset.range r, f₀ ((w ^ j) • v)
    have hD : (q : ℤ) ∣ (r : ℤ) * f₀ v - S := by
      have h : (q : ℤ) ∣ ∑ j ∈ Finset.range r, (f₀ v - f₀ ((w ^ j) • v)) :=
        Finset.dvd_sum fun j _ => hdvd j
      rwa [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    have hdv : (q : ℤ) ∣ f₀ v := by
      have e : f₀ v = u * ((r : ℤ) * f₀ v - S) + (q : ℤ) * (s * f₀ v) := by
        linear_combination (-(f₀ v)) * hus + hv
      rw [e]
      exact dvd_add (Dvd.dvd.mul_left hD u) (dvd_mul_right _ _)
    rw [hχ]
    exact orderOf_dvd_iff_zpow_eq_one.1 hdv

theorem mem_kernelReflectionGroup_of_coprime {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i ^ p = 1) {w : WeylGroup τ} (hw : w ∈ rootCharStabilizerSubgroup a)
    (hcop : Nat.Coprime (orderOf w) p) : w ∈ kernelReflectionGroup a := by
  obtain ⟨f, hfw, hfker⟩ := exists_invariant_form_of_coprime hp ha hw hcop
  refine (Subgroup.closure_le (kernelReflectionGroup a)).2 ?_ (mem_stab_closure_of_invariant f hfw)
  rintro _ ⟨u, i, hui, rfl⟩
  exact Subgroup.subset_closure ⟨u, i, ⟨IsRoot.smul (isRoot_single τ i) u, hfker _ hui⟩, rfl⟩

theorem isPGroup_quotient {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Kˣ} (ha : ∀ i, a i ^ p = 1) :
    IsPGroup p (↥(rootCharStabilizerSubgroup a) ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) := by
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (orderOf_pos (y : WeylGroup τ)).ne' p hp.ne_one
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    Subgroup.coe_pow]
  have hcop : Nat.Coprime (orderOf ((y : WeylGroup τ) ^ p ^ k)) p := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (hord ▸ dvd_mul_right _ _), hord,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
  exact mem_kernelReflectionGroup_of_coprime hp ha (Subgroup.pow_mem _ y.2 _) hcop

theorem isSolvable_quotient {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i ^ p = 1) :
    Group.IsSolvable (↥(rootCharStabilizerSubgroup a) ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := (isPGroup_quotient hp ha).isNilpotent
  infer_instance

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

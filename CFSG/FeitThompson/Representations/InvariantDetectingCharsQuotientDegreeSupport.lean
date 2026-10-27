module

public import CFSG.FeitThompson.Representations.CyclicTILinearCharIntegralCoprime
public import CFSG.FeitThompson.Representations.ScalarCoordinateDegreeDivisibility
public import CFSG.FeitThompson.Representations.CoprimeInvariantCharacterInductionSupport

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexOrder

theorem mem_Irr_units_coe {G : Type*} [Group G] (w : G →* ℂˣ) :
    (fun x => ((w x : ℂˣ) : ℂ)) ∈ Irr G := by
  have h := linearCharClassFun_mem_Irr w
  rwa [coe_linearCharClassFun] at h

theorem mem_classFun_units_coe {G : Type*} [Group G] (w : G →* ℂˣ) :
    (fun x => ((w x : ℂˣ) : ℂ)) ∈ classFun G :=
  Irr_subset_classFun (mem_Irr_units_coe w)

def mulAutSubgroupRestrict {K : Type*} [Group K] (b : MulAut K) (N : Subgroup K) (h : ∀ x ∈ N, b x ∈ N)
    (h' : ∀ x ∈ N, b.symm x ∈ N) : MulAut N where
  toFun x := ⟨b (x : K), h _ x.2⟩
  invFun x := ⟨b.symm (x : K), h' _ x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by push_cast; rw [map_mul])

@[simp] theorem coe_mulAutSubgroupRestrict {K : Type*} [Group K] {b : MulAut K} {N : Subgroup K} {h h'}
    (x : N) : ((mulAutSubgroupRestrict b N h h' x : N) : K) = b (x : K) := (rfl)

theorem coe_mulAutSubgroupRestrict_pow {K : Type*} [Group K] {b : MulAut K} {N : Subgroup K} {h h'} (n : ℕ)
    (x : N) : (((mulAutSubgroupRestrict b N h h') ^ n) x : K) = (b ^ n) (x : K) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', MulAut.mul_apply, coe_mulAutSubgroupRestrict, ih, pow_succ', MulAut.mul_apply]

theorem mulAutSubgroupRestrict_pow_eq_one {K : Type*} [Group K] {b : MulAut K} {N : Subgroup K} {h h'} {n : ℕ}
    (hb : b ^ n = 1) : (mulAutSubgroupRestrict b N h h') ^ n = 1 := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [coe_mulAutSubgroupRestrict_pow, hb]
  rfl

theorem inertiaGroup_le_inertiaGroup_of_le {L : Type*} [Group L] {N M : Subgroup L} [N.Normal]
    [M.Normal] (hNM : N ≤ M) (f : M → ℂ) :
    inertiaGroup M f ≤ inertiaGroup N (fun x : N => f ⟨(x : L), hNM x.2⟩) := by
  intro g hg
  have h := mem_inertiaGroup.1 hg
  refine mem_inertiaGroup.2 (funext fun x => ?_)
  rw [NormalInduction.conjClassFun_apply]
  have h2 := congrFun h ⟨(x : L), hNM x.2⟩
  rw [NormalInduction.conjClassFun_apply] at h2
  exact h2

theorem exists_comp_eq_mem_resConstituents {K : Type*} [Group K] [Finite K] {N : Subgroup K}
    [N.Normal] [Fintype N] {q : ℕ} (hq : q.Prime) (hqK : ¬ q ∣ Nat.card K) (e : MulAut N)
    (heq : e ^ q = 1) {θ : K → ℂ} (hθ : θ ∈ Irr K) (hinv : ∀ x : N, θ (e x : K) = θ (x : K)) :
    ∃ lam ∈ resConstituents N θ, lam ∘ e = lam := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hres : resClassFun N θ ∘ (e : N → N) = resClassFun N θ := by
    funext x
    rw [Function.comp_apply, resClassFun_apply, resClassFun_apply, hinv]
  have hstab : ∀ f : N → ℂ, f ∈ resConstituents N θ → f ∘ (e : N → N) ∈ resConstituents N θ := by
    intro f hf
    rw [mem_resConstituents] at hf ⊢
    refine ⟨mem_Irr_comp_mulAut hf.1 e, ?_⟩
    have h1 : cfInner (resClassFun N θ ∘ (e : N → N)) (f ∘ (e : N → N))
        = cfInner (resClassFun N θ) f := cfInner_comp_equiv e.toEquiv _ _
    rw [hres] at h1
    rw [h1]
    exact hf.2
  set T := resConstituents N θ with hT
  set F : {f : N → ℂ // f ∈ T} → {f : N → ℂ // f ∈ T} :=
    fun x => ⟨x.1 ∘ (e : N → N), hstab _ x.2⟩ with hF
  have hFval : ∀ x, (F x).1 = x.1 ∘ (e : N → N) := fun _ => rfl
  have hFinj : Function.Injective F := by
    intro x y hxy
    have h : x.1 ∘ (e : N → N) = y.1 ∘ (e : N → N) := by
      rw [← hFval x, ← hFval y, hxy]
    refine Subtype.ext (funext fun z => ?_)
    have h2 := congrFun h (e.symm z)
    simpa using h2
  set σ : Equiv.Perm {f : N → ℂ // f ∈ T} :=
    Equiv.ofBijective F (Finite.injective_iff_bijective.1 hFinj) with hσ
  have hσapply : ∀ x, σ x = F x := fun _ => rfl
  have hσpow : ∀ (n : ℕ) (x : {f : N → ℂ // f ∈ T}),
      ((σ ^ n) x).1 = x.1 ∘ ((e ^ n : MulAut N) : N → N) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih (σ x), hσapply, hFval]
      funext z
      simp only [Function.comp_apply]
      rw [pow_succ', MulAut.mul_apply]
  have hσq : σ ^ q ^ 1 = 1 := by
    rw [pow_one]
    refine Equiv.ext fun x => Subtype.ext ?_
    rw [hσpow q x, heq]
    rfl
  have hcard : ¬ q ∣ Fintype.card {f : N → ℂ // f ∈ T} := by
    rw [Fintype.card_coe]
    obtain ⟨lam, hlam⟩ := resConstituents_nonempty (N := N) hθ
    have h1 : Nat.card (K ⧸ inertiaGroup N lam) = T.card :=
      ScalarCoordinateSystem.natCard_quotient_inertiaGroup_eq_card hθ hlam
    intro hdvd
    refine hqK (hdvd.trans ?_)
    rw [← h1, ← Subgroup.index_eq_card]
    exact Subgroup.index_dvd_card _
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσq
  exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

end CFSG.FeitThompson

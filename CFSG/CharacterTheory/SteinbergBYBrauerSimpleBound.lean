module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.CharP.Algebra
public import CFSG.ThirdParty.BrauerInduction.Background.Group.PRegularClass

public section

namespace CFSG.CharacterTheory.SteinbergBY

open Module

section Density

variable {k A : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
  [∀ i, Module A (V i)] [∀ i, Module k (V i)] [∀ i, IsScalarTower k A (V i)]
  [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]

theorem exists_scalar_of_end_pi (hne : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))
    (φ : (∀ i, V i) →ₗ[A] (∀ i, V i)) : ∃ c : ι → k, ∀ m i, φ m i = c i • m i := by
  have hdiag : ∀ i, ∃ c : k, ∀ v : V i, φ (Pi.single i v) i = c • v := by
    intro i
    set ψ : V i →ₗ[A] V i := (LinearMap.proj i).comp (φ.comp (LinearMap.single A V i)) with hψ
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k
      (A := A) (V := V i)).2 ψ
    refine ⟨c, fun v => ?_⟩
    have h := congrArg (fun F : Module.End A (V i) => F v) hc
    simp only [hψ, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
      Function.eval, LinearMap.coe_single] at h
    rw [← h]
    rfl
  have hoff : ∀ i j, i ≠ j → ∀ v : V j, φ (Pi.single j v) i = 0 := by
    intro i j hij v
    set ψ : V j →ₗ[A] V i := (LinearMap.proj i).comp (φ.comp (LinearMap.single A V j)) with hψ
    have hψ0 : ψ = 0 := by
      rcases LinearMap.bijective_or_eq_zero ψ with h | h
      · exact ((hne j i (Ne.symm hij)).false (LinearEquiv.ofBijective ψ h)).elim
      · exact h
    have h := congrArg (fun F : V j →ₗ[A] V i => F v) hψ0
    simpa [hψ] using h
  choose c hc using hdiag
  refine ⟨c, fun m i => ?_⟩
  have hm : m = ∑ j, Pi.single j (m j) := (Finset.univ_sum_single m).symm
  conv_lhs => rw [hm]
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i (fun j _ hji => hoff i j hji.symm _)
    (fun h => absurd (Finset.mem_univ i) h), hc]

theorem exists_smul_eq_of_simple (hne : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))
    (f : ∀ i, V i →ₗ[k] V i) : ∃ a : A, ∀ i (v : V i), a • v = f i v := by
  classical
  set M := ∀ i, V i
  have : IsSemisimpleModule A M := inferInstance
  set F : Module.End (Module.End A M) M :=
    { toFun := fun m i => f i (m i)
      map_add' := fun m n => funext fun i => map_add (f i) (m i) (n i)
      map_smul' := fun φ m => by
        obtain ⟨c, hc⟩ := exists_scalar_of_end_pi (k := k) hne φ
        funext i
        change f i ((φ m) i) = φ (fun i => f i (m i)) i
        rw [hc, hc, map_smul] } with hFdef
  set b := Module.finBasis k M with hbdef
  obtain ⟨a, ha⟩ := jacobson_density F (Finset.univ.image b)
  have hall : ∀ m : M, F m = a • m := by
    intro m
    have hm := b.sum_repr m
    rw [← hm]
    have hFk : ∀ (c : k) (x : M), F (c • x) = c • F x := fun c x => by
      funext i
      change f i ((c • x) i) = (c • F x) i
      rw [Pi.smul_apply, map_smul]
      rfl
    have hFadd : ∀ x y : M, F (x + y) = F x + F y := fun x y => F.map_add x y
    have hsum : ∀ (s : Finset (Fin (Module.finrank k M))) (c : Fin (Module.finrank k M) → k),
        F (∑ j ∈ s, c j • b j) = ∑ j ∈ s, c j • F (b j) := by
      intro s c
      induction s using Finset.induction_on with
      | empty => simp
      | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, hFadd, ih, hFk]
    rw [hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ha (b j) (Finset.mem_image_of_mem b (Finset.mem_univ j)), smul_comm]
  refine ⟨a, fun i v => ?_⟩
  have h := congrFun (hall (Pi.single i v)) i
  rw [Pi.smul_apply, Pi.single_eq_same] at h
  rw [← h]
  change f i (Pi.single i v i) = f i v
  rw [Pi.single_eq_same]

end Density

section Characters

variable {k G : Type*} [Field k] [Group G]

theorem trace_asAlgebraHom {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (a : MonoidAlgebra k G) :
    LinearMap.trace k V (ρ.asAlgebraHom a) =
      ∑ g ∈ a.coeff.support, a.coeff g * LinearMap.trace k V (ρ g) := by
  classical
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single a]
  rw [Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Representation.asAlgebraHom_single, map_smul, smul_eq_mul]

theorem exists_endomorphism_trace_eq_one {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V] : ∃ P : V →ₗ[k] V, LinearMap.trace k V P = 1 := by
  classical
  set b := Module.finBasis k V with hb
  have hpos : 0 < Module.finrank k V := Module.finrank_pos
  set i₀ : Fin (Module.finrank k V) := ⟨0, hpos⟩
  refine ⟨(b.coord i₀).smulRight (b i₀), ?_⟩
  rw [LinearMap.trace_smulRight, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same]

theorem linearIndependent_trace_of_irreducible [IsAlgClosed k] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, FiniteDimensional k (V i)] (ρ : ∀ i, Representation k G (V i))
    [∀ i, (ρ i).IsIrreducible] (hne : ∀ i j, i ≠ j → IsEmpty ((ρ i).Equiv (ρ j))) :
    LinearIndependent k fun i (g : G) => LinearMap.trace k (V i) (ρ i g) := by
  classical
  have hne' : ∀ i j, i ≠ j →
      IsEmpty ((ρ i).asModule ≃ₗ[MonoidAlgebra k G] (ρ j).asModule) := by
    intro i j hij
    refine ⟨fun e => (hne i j hij).false ?_⟩
    exact ((Representation.IntertwiningMap.equivLinearMapAsModule (ρ i) (ρ j)).symm
      e.toLinearMap).ofBijective e.bijective
  have hnt : ∀ i, Nontrivial (V i) := fun i =>
    IsSimpleModule.nontrivial (MonoidAlgebra k G) (ρ i).asModule
  choose P hP using fun i => @exists_endomorphism_trace_eq_one k _ (V i) _ _ _ (hnt i)
  have hsel : ∀ j, ∃ a : MonoidAlgebra k G, ∀ i,
      LinearMap.trace k (V i) ((ρ i).asAlgebraHom a) = if i = j then 1 else 0 := by
    intro j
    obtain ⟨a, ha⟩ := exists_smul_eq_of_simple (k := k) (A := MonoidAlgebra k G)
      (V := fun i => (ρ i).asModule) hne' fun i => (if i = j then (1 : k) else 0) • P i
    refine ⟨a, fun i => ?_⟩
    have hlin : (ρ i).asAlgebraHom a = (if i = j then (1 : k) else 0) • P i := by
      ext v
      exact ha i v
    rw [hlin, map_smul, hP, smul_eq_mul, mul_one]
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  obtain ⟨a, ha⟩ := hsel j
  have h := congrArg (fun F : G → k => ∑ g ∈ a.coeff.support, a.coeff g * F g) hc
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero] at h
  have h2 : ∑ g ∈ a.coeff.support, a.coeff g * ∑ i, c i * LinearMap.trace k (V i) (ρ i g) =
      ∑ i, c i * LinearMap.trace k (V i) ((ρ i).asAlgebraHom a) := by
    simp_rw [trace_asAlgebraHom, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun g _ => ?_
    ring
  rw [h2] at h
  simp only [ha, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  exact h

end Characters

section Brauer

variable {k G : Type*} [Field k] [Group G]

theorem trace_rep_eq_trace_pRegular [Finite G] (p : ℕ) [Fact p.Prime] [CharP k p] {V : Type*}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) (g : G) :
    LinearMap.trace k V (ρ g) = LinearMap.trace k V (ρ (Group.pRegular p g)) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · have h0 : ∀ f : V →ₗ[k] V, f = 0 := fun f => LinearMap.ext fun v => Subsingleton.elim _ _
    rw [h0 (ρ g), h0 (ρ (Group.pRegular p g))]
  have hinj : Function.Injective (algebraMap k (Module.End k V)) := by
    intro c d h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h1 := congrArg (fun f : Module.End k V => f v) h
    simp only [Module.algebraMap_end_apply] at h1
    exact smul_left_injective k hv h1
  have : CharP (Module.End k V) p := charP_of_injective_algebraMap hinj p
  set r := Group.pRegular p g with hr
  set s := Group.pSingular p g with hs
  have hg : g = r * s := (Group.pDecomp' p (isOfFinOrder_of_finite g)).symm
  have hcomm : Commute r s := (Group.pDecomp_commute p g).symm
  obtain ⟨n, hn⟩ := Group.isPSingular_pSingular (p := p) g
  have hsn : s ^ p ^ n = 1 := by
    rw [← hn]
    exact pow_orderOf_eq_one s
  set N : Module.End k V := ρ s - 1 with hN
  have hNcomm : Commute (ρ r) N := by
    refine Commute.sub_right ?_ (Commute.one_right _)
    have h := congrArg ρ hcomm.eq
    rw [map_mul, map_mul] at h
    exact h
  have hNp : N ^ p ^ n = 0 := by
    rw [hN, sub_pow_char_pow_of_commute p n (Commute.one_right _), one_pow, ← map_pow, hsn,
      map_one, sub_self]
  have hnil : IsNilpotent (ρ r * N) := ⟨p ^ n, by rw [hNcomm.mul_pow, hNp, mul_zero]⟩
  have htr : LinearMap.trace k V (ρ r * N) = 0 :=
    (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  have hρg : ρ g = ρ r + ρ r * N := by
    rw [hN, mul_sub, mul_one, add_sub_cancel, hg, map_mul]
  rw [hρg, map_add, htr, add_zero]

theorem trace_rep_conj {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (g h : G) :
    LinearMap.trace k V (ρ (h * g * h⁻¹)) = LinearMap.trace k V (ρ g) := by
  rw [ρ.map_mul, ρ.map_mul, LinearMap.trace_mul_comm, ← mul_assoc, ← ρ.map_mul, ← ρ.map_mul,
    inv_mul_cancel, one_mul]

theorem card_le_card_pRegularClass [IsAlgClosed k] [Finite G] (p : ℕ) [Fact p.Prime] [CharP k p]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (ρ : ∀ i, Representation k G (V i))
    [∀ i, (ρ i).IsIrreducible] (hne : ∀ i j, i ≠ j → IsEmpty ((ρ i).Equiv (ρ j))) :
    Fintype.card ι ≤ Fintype.card (PRegularClass p G) := by
  classical
  set χ : ι → G → k := fun i g => LinearMap.trace k (V i) (ρ i g) with hχ
  have hli : LinearIndependent k χ := linearIndependent_trace_of_irreducible ρ hne
  set Res : (G → k) →ₗ[k] (PRegularClass p G → k) := LinearMap.funLeft k k PRegularClass.repr
    with hRes
  have hprop : ∀ f ∈ Submodule.span k (Set.range χ),
      (∀ g h : G, f (h * g * h⁻¹) = f g) ∧ ∀ g : G, f g = f (Group.pRegular p g) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨fun g h => trace_rep_conj (ρ i) g h, fun g => trace_rep_eq_trace_pRegular p (ρ i) g⟩
    | zero => exact ⟨fun _ _ => rfl, fun _ => rfl⟩
    | add x y _ _ hx hy =>
      exact ⟨fun g h => by simp only [Pi.add_apply, hx.1, hy.1],
        fun g => by simp only [Pi.add_apply, ← hx.2, ← hy.2]⟩
    | smul c x _ hx =>
      exact ⟨fun g h => by simp only [Pi.smul_apply, hx.1],
        fun g => by simp only [Pi.smul_apply, ← hx.2]⟩
  have hdisj : Disjoint (Submodule.span k (Set.range χ)) (LinearMap.ker Res) := by
    rw [Submodule.disjoint_def]
    intro f hf hker
    obtain ⟨hcl, hreg⟩ := hprop f hf
    funext g
    have hgreg : IsPRegular p (Group.pRegular p g) :=
      Group.isPRegular_pRegular p (isOfFinOrder_of_finite g)
    obtain ⟨C, hC, -⟩ := PRegularClass.unique_of_isPRegular (p := p) _ hgreg
    obtain ⟨c, hc⟩ := isConj_iff.mp hC
    have h0 : Res f C = 0 := by
      rw [LinearMap.mem_ker.mp hker]
      rfl
    rw [Pi.zero_apply, hreg g, ← hc, hcl]
    exact h0
  have hli' : LinearIndependent k (Res ∘ χ) := hli.map hdisj
  have h := hli'.fintype_card_le_finrank
  rwa [Module.finrank_fintype_fun_eq_card] at h

end Brauer

end CFSG.CharacterTheory.SteinbergBY

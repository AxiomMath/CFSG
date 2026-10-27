module

public import CFSG.LinearAlgebra.OddSolvableUnitary.HomologyMonomial

public section

namespace CFSG.OddSolvableUnitary

open Module Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover
  CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement Matrix

variable {f : ℕ} {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section Coordinates

variable (hK : UnitaryFieldData 2 f K) {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  (e : Basis (Fin 3) K V) (he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0)
include hK he

theorem repr_eq_apply_of_orthonormal (v : V) (i : Fin 3) : e.repr v i = B (e i) v := by
  have h := congrArg (B (e i)) (e.sum_repr v)
  simp only [map_sum, map_smul, he, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
  exact h

theorem apply_eq_sum_of_orthonormal (x y : V) :
    B x y = ∑ i, hK.bar (e.repr x i) * e.repr y i := by
  conv_lhs => rw [← e.sum_repr x]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, ← repr_eq_apply_of_orthonormal hK e he]

theorem apply_eq_gramForm (x y : V) :
    B x y = gramForm hK (1 : Matrix (Fin 3) (Fin 3) K) (e.equivFun x) (e.equivFun y) := by
  rw [apply_eq_sum_of_orthonormal hK e he, gramForm_apply, Matrix.one_mulVec]
  simp [dotProduct, Basis.equivFun_apply]

theorem mem_sesqSpecialUnitaryGroup_iff_glMatrix_mem {g : LinearMap.GeneralLinearGroup K V} :
    g ∈ sesqSpecialUnitaryGroup B ↔ glMatrix e g ∈ unitarySU 2 f K 3 := by
  rw [mem_sesqSpecialUnitaryGroup, mem_sesqUnitaryGroup, mem_unitarySU_iff hK, coe_glMatrix,
    LinearMap.det_toMatrix, and_comm]
  refine and_congr_right fun _ => ?_
  set M := LinearMap.toMatrix e e (g : V →ₗ[K] V)
  have hrepr : ∀ x, e.equivFun ((g : V →ₗ[K] V) x) = M *ᵥ e.equivFun x := fun x => by
    rw [Basis.equivFun_apply, Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
  rw [← Matrix.mul_one (M.map hK.bar)ᵀ, ← gramForm_isometry_iff]
  constructor
  · intro h X Y
    obtain ⟨x, rfl⟩ := e.equivFun.surjective X
    obtain ⟨y, rfl⟩ := e.equivFun.surjective Y
    rw [← hrepr, ← hrepr, ← apply_eq_gramForm hK e he, ← apply_eq_gramForm hK e he, h]
  · intro h x y
    rw [apply_eq_gramForm hK e he, apply_eq_gramForm hK e he, hrepr, hrepr, h]

theorem map_glMatrix_eq_unitarySU :
    (sesqSpecialUnitaryGroup B).map
      (glMatrix e : LinearMap.GeneralLinearGroup K V →* GL (Fin 3) K) = unitarySU 2 f K 3 := by
  ext A
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_sesqSpecialUnitaryGroup_iff_glMatrix_mem hK e he).1 hg
  · intro hA
    refine ⟨(glMatrix e).symm A, (mem_sesqSpecialUnitaryGroup_iff_glMatrix_mem hK e he).2 ?_, ?_⟩
    · rwa [MulEquiv.apply_symm_apply]
    · exact MulEquiv.apply_symm_apply _ _

@[expose] noncomputable def unitaryEquiv : sesqSpecialUnitaryGroup B ≃* unitarySU 2 f K 3 :=
  ((glMatrix e).subgroupMap (sesqSpecialUnitaryGroup B)).trans
    (MulEquiv.subgroupCongr (map_glMatrix_eq_unitarySU hK e he))

theorem coe_unitaryEquiv (g : sesqSpecialUnitaryGroup B) :
    ((unitaryEquiv hK e he g : unitarySU 2 f K 3) : GL (Fin 3) K) = glMatrix e g :=
  rfl

end Coordinates

section Diagonal

variable (e : Basis (Fin 3) K V)

theorem coe_glMatrix_eq_diagonal_of_apply {g : LinearMap.GeneralLinearGroup K V} (d : Fin 3 → K)
    (hd : ∀ j, (g : V →ₗ[K] V) (e j) = d j • e j) :
    ((glMatrix e g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal d := by
  ext i j
  rw [coe_glMatrix, LinearMap.toMatrix_apply, hd, map_smul, e.repr_self, Matrix.diagonal_apply]
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs with h1 h2 h2
  · rw [h2]
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

theorem apply_eq_smul_of_coe_glMatrix_eq_diagonal {g : LinearMap.GeneralLinearGroup K V}
    (d : Fin 3 → K)
    (hd : ((glMatrix e g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal d)
    (j : Fin 3) : (g : V →ₗ[K] V) (e j) = d j • e j := by
  rw [← e.sum_repr ((g : V →ₗ[K] V) (e j))]
  have h : ∀ i, e.repr ((g : V →ₗ[K] V) (e j)) i = Matrix.diagonal d i j := fun i => by
    rw [← hd, coe_glMatrix, LinearMap.toMatrix_apply]
  simp only [h, Matrix.diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

end Diagonal

section HomologyTorus

variable {hK : UnitaryFieldData 2 f K} (B : V →ₛₗ[hK.bar] V →ₗ[K] K)

@[expose] noncomputable def homologySubgroup (e : Basis (Fin 3) K V) :
    Subgroup (sesqSpecialUnitaryGroup B) :=
  (homologyTorus (normOne K (2 ^ f))).comap
    ((glMatrix e : LinearMap.GeneralLinearGroup K V →* GL (Fin 3) K).comp
      (sesqSpecialUnitaryGroup B).subtype)

theorem mem_homologySubgroup {e : Basis (Fin 3) K V} {g : sesqSpecialUnitaryGroup B} :
    g ∈ homologySubgroup B e ↔
      glMatrix e (g : LinearMap.GeneralLinearGroup K V) ∈ homologyTorus (normOne K (2 ^ f)) :=
  Iff.rfl

variable {B}

include hK in
theorem mem_homologySubgroup_of_span_eq {e e' : Basis (Fin 3) K V}
    (he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0)
    (he' : ∀ i j, B (e' i) (e' j) = if i = j then 1 else 0) (hspan : K ∙ e 2 = K ∙ e' 2)
    {g : sesqSpecialUnitaryGroup B} (hg : g ∈ homologySubgroup B e) :
    g ∈ homologySubgroup B e' := by
  obtain ⟨a, ha⟩ := hg
  set d : Fin 3 → K := fun j => ((![(a : Kˣ), (a : Kˣ), ((a : Kˣ) * a)⁻¹] : Fin 3 → Kˣ) j : K)
  have hd : ((glMatrix e (g : LinearMap.GeneralLinearGroup K V) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal d := by
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) ha
    simp only [homologyHom_apply, coe_diagHom] at this
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype] at this
    exact this.symm
  have hge := apply_eq_smul_of_coe_glMatrix_eq_diagonal e d hd
  have hd01 : d 0 = d 1 := rfl
  have h2mem : e 2 ∈ K ∙ e' 2 := hspan ▸ Submodule.mem_span_singleton_self _
  obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.1 h2mem
  have he'2 : e' 2 ∈ K ∙ e 2 := hspan ▸ Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 he'2
  have hg' : ∀ j, ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (e' j) = d j • e' j := by
    intro j
    by_cases hj : j = 2
    · subst hj
      rw [← hc, map_smul, hge 2, smul_comm]
    · have h2 : e.repr (e' j) 2 = 0 := by
        rw [repr_eq_apply_of_orthonormal hK e he, ← hc', map_smulₛₗ, LinearMap.smul_apply,
          he' 2 j, ite_eq_right (Ne.symm hj), smul_zero]
      have hdj : d j = d 0 := by fin_cases j <;> first | rfl | exact absurd rfl hj
      have hsum : e' j = (e.repr (e' j)) 0 • e 0 + (e.repr (e' j)) 1 • e 1 := by
        conv_lhs => rw [← e.sum_repr (e' j)]
        rw [Fin.sum_univ_three, h2, zero_smul, add_zero]
      rw [hdj, hsum, map_add, map_smul, map_smul, hge, hge, ← hd01, smul_add,
        smul_comm (d 0), smul_comm (d 0)]
  refine ⟨a, Units.ext ?_⟩
  change ((homologyHom _ a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    ((glMatrix e' (g : LinearMap.GeneralLinearGroup K V) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)
  rw [coe_glMatrix_eq_diagonal_of_apply e' d hg', homologyHom_apply, coe_diagHom]

omit hK in
theorem eigenspace_of_coe_glMatrix_eq_diagonal (e : Basis (Fin 3) K V)
    {w : LinearMap.GeneralLinearGroup K V} {b c : K} (hbc : b ≠ c)
    (hw : ((glMatrix e w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![b, b, c]) :
    Module.End.eigenspace (w : Module.End K V) c = K ∙ e 2 ∧
      finrank K (Module.End.eigenspace (w : Module.End K V) b) = 2 ∧
      finrank K (Module.End.eigenspace (w : Module.End K V) c) = 1 := by
  have : Module.Finite K V := Module.Finite.of_basis e
  have hV : finrank K V = 3 := by rw [Module.finrank_eq_card_basis e, Fintype.card_fin]
  have hge := apply_eq_smul_of_coe_glMatrix_eq_diagonal e ![b, b, c] hw
  have hrep : ∀ x : V, ∀ k, e.repr ((w : V →ₗ[K] V) x) k = ![b, b, c] k * e.repr x k := by
    intro x k
    rw [← LinearMap.toMatrix_mulVec_repr e e, ← coe_glMatrix e w, hw, Matrix.mulVec_diagonal]
  have hEc : Module.End.eigenspace (w : Module.End K V) c = K ∙ e 2 := by
    ext x
    rw [Module.End.mem_eigenspace_iff, Submodule.mem_span_singleton]
    constructor
    · intro hx
      have h0 : ∀ k : Fin 3, k ≠ 2 → e.repr x k = 0 := by
        intro k hk
        have h := hrep x k
        rw [hx, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
        have hk' : ![b, b, c] k = b := by fin_cases k <;> first | rfl | exact absurd rfl hk
        rw [hk'] at h
        have h' : (b - c) * e.repr x k = 0 := by linear_combination -h
        exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hbc)
      refine ⟨e.repr x 2, ?_⟩
      conv_rhs => rw [← e.sum_repr x]
      rw [Fin.sum_univ_three, h0 0 (by decide), h0 1 (by decide), zero_smul, zero_smul,
        zero_add, zero_add]
    · rintro ⟨a, rfl⟩
      rw [map_smul, hge 2]
      exact smul_comm a c (e 2)
  have hfc : finrank K (Module.End.eigenspace (w : Module.End K V) c) = 1 := by
    rw [hEc, finrank_span_singleton (e.ne_zero 2)]
  refine ⟨hEc, ?_, hfc⟩
  have hle : Submodule.span K (Set.range ![e 0, e 1]) ≤
      Module.End.eigenspace (w : Module.End K V) b := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · exact Module.End.mem_eigenspace_iff.2 (hge 0)
    · exact Module.End.mem_eigenspace_iff.2 (hge 1)
  have hli : LinearIndependent K ![e 0, e 1] := by
    have := e.linearIndependent.comp ![0, 1] (by decide)
    convert this using 1
    ext k
    fin_cases k <;> rfl
  have hge2 := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hli, Fintype.card_fin] at hge2
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (Module.End.eigenspace (w : Module.End K V) b) (Module.End.eigenspace (w : Module.End K V) c)
  rw [eigenspace_inf_eigenspace _ hbc, finrank_bot, hfc] at hsum
  have := Submodule.finrank_le (Module.End.eigenspace (w : Module.End K V) b ⊔
    Module.End.eigenspace (w : Module.End K V) c)
  omega

end HomologyTorus

theorem diagHom_mul_cycGL_mul_inv_mul_inv {d : Fin 3 → Kˣ} (hd : d 0 * d 1 * d 2 = 1) :
    diagHom 3 d * cycGL * (diagHom 3 d)⁻¹ * cycGL⁻¹ =
      diagHom 3 ![d 0, (d 0 * d 0)⁻¹, d 0] *
        diagHom 3 ![d 0 * d 1, d 0 * d 1, (d 0 * d 1 * (d 0 * d 1))⁻¹] := by
  have hd2 : d 2 = (d 0 * d 1)⁻¹ := eq_inv_of_mul_eq_one_right hd
  rw [mul_assoc (diagHom 3 d * cycGL), ← map_inv, mul_assoc, ← mul_assoc cycGL,
    cycGL_conj_diagHom, ← map_mul, ← map_mul]
  congr 1
  funext i
  fin_cases i <;> simp [hd2, mul_comm, mul_left_comm, mul_assoc]
  exact mul_comm _ _

section Groups

variable {G : Type*} [Group G]

theorem odd_card_sup_of_le_normalizer [Finite G] {H N : Subgroup G}
    (hHN : H ≤ normalizer (N : Set G)) (hH : Odd (Nat.card H)) (hN : Odd (Nat.card N)) :
    Odd (Nat.card (H ⊔ N : Subgroup G)) := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv]
  exact (Odd.of_dvd_nat hH (Subgroup.card_quotient_dvd_card _)).mul hN

theorem eq_one_of_sq_eq_one_of_odd {c : G} (hc : Odd (orderOf c)) (h : c ^ 2 = 1) : c = 1 := by
  have h2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one h
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h1 | h1
  · exact orderOf_eq_one_iff.1 h1
  · rw [h1] at hc
    exact absurd hc (by decide)

theorem smul_eq_self_of_odd {Ω : Type*} [MulAction G Ω] {g : G} (hg : Odd (orderOf g))
    {α β : Ω} (hαβ : α ≠ β) (hα : g • α = α ∨ g • α = β) (hβ : g • β = α ∨ g • β = β) :
    g • α = α ∧ g • β = β := by
  have hfix : ∀ ω : Ω, (g ^ 2) • ω = ω → g • ω = ω := by
    intro ω h
    obtain ⟨k, hk⟩ := hg
    have hpow : ∀ n : ℕ, (g ^ (2 * n)) • ω = ω := by
      intro n
      induction n with
      | zero => rw [mul_zero, pow_zero, one_smul]
      | succ n ih => rw [mul_add, mul_one, pow_add, mul_smul, h, ih]
    calc g • ω = g • (g ^ (2 * k)) • ω := by rw [hpow k]
      _ = (g ^ orderOf g) • ω := by rw [← mul_smul, ← pow_succ', hk]
      _ = ω := by rw [pow_orderOf_eq_one, one_smul]
  have hα' : g • α = α := by
    rcases hα with h | h
    · exact h
    · exfalso
      have hβ' : g • β = α := by
        rcases hβ with h' | h'
        · exact h'
        · exact absurd (MulAction.injective g (h.trans h'.symm)) hαβ
      have := hfix α (by rw [sq, mul_smul, h, hβ'])
      exact hαβ (this.symm.trans h)
  refine ⟨hα', ?_⟩
  rcases hβ with h | h
  · exact absurd (MulAction.injective g (h.trans hα'.symm)) (Ne.symm hαβ)
  · exact h

end Groups

theorem unitary_homology_subgroup_saturates_from_pair_fixed_set
    (hK : UnitaryFieldData 2 f K) [FiniteDimensional K V] (hV : finrank K V = 3)
    {B : V →ₛₗ[hK.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (Z₀ : Subgroup (sesqSpecialUnitaryGroup B)) [Z₀.Normal]
    (hZ₀ : ∀ z ∈ Z₀, ∃ c : K, ((z : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = c • 1)
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] {α β : Ω} (hαβ : α ≠ β)
    (ι : sesqSpecialUnitaryGroup B ⧸ Z₀ →* G) (hι : Function.Injective ι)
    {t : G} (htL : t ∈ ι.range) (ht2 : orderOf t = 2) (htα : t • α = β) (htβ : t • β = α)
    {D I W H : Subgroup G} (hD : D = MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)
    (hID : I ≤ D) (hIn : D ≤ normalizer (I : Set G)) (hIodd : Odd (Nat.card I))
    (hDt : ∀ d ∈ D, ⁅d, t⁆ ∈ I)
    (e₀ : Basis (Fin 3) K V) (he₀ : ∀ i j, B (e₀ i) (e₀ j) = if i = j then 1 else 0)
    (hW : W = (homologySubgroup B e₀).map (ι.comp (QuotientGroup.mk' Z₀))) (hWD : W ≤ D)
    (hWt : ∀ w ∈ W, ⁅w, t⁆ = 1) (hH : H = (W ⊔ I) ⊓ ι.range) (hsolv : Group.IsSolvable H)
    (hWH : ⁅W, H⁆ ≠ ⊥) (hfix : {ω : Ω | ∀ h ∈ H, h • ω = ω} = {α, β}) :
    ∃ e : Basis (Fin 3) K V, (∀ i j, B (e i) (e j) = if i = j then 1 else 0) ∧
      (H.comap (ι.comp (QuotientGroup.mk' Z₀))).map
          ((glMatrix e : LinearMap.GeneralLinearGroup K V →* GL (Fin 3) K).comp
            (sesqSpecialUnitaryGroup B).subtype) = monomialX (normOne K (2 ^ f)) ∧
      (∃! r : sesqSpecialUnitaryGroup B, ι (QuotientGroup.mk' Z₀ r) = t ∧ r ^ 2 = 1) ∧
      (∀ r : sesqSpecialUnitaryGroup B, ι (QuotientGroup.mk' Z₀ r) = t → r ^ 2 = 1 →
        glMatrix e (r : LinearMap.GeneralLinearGroup K V) = s01GL) ∧
      H = I ⊓ ι.range ∧ ⁅H, zpowers t⁆ = H ∧
      {y | ∃ x ∈ H, x * t * x⁻¹ = y}.ncard = 3 * (2 ^ f + 1) := by
  classical
  have := hK.finite
  have : CharP K 2 := hK.charP
  set ψ : sesqSpecialUnitaryGroup B →* G := ι.comp (QuotientGroup.mk' Z₀) with hψdef
  have hψker : ψ.ker = Z₀ := by
    ext x
    rw [MonoidHom.mem_ker, hψdef, MonoidHom.comp_apply, ← map_one ι, hι.eq_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hψrange : ψ.range = ι.range := by
    rw [hψdef, MonoidHom.range_comp, QuotientGroup.range_mk', MonoidHom.range_eq_map]
  have hFinS : Finite (sesqSpecialUnitaryGroup B) :=
    Finite.of_equiv _ (unitaryEquiv hK e₀ he₀).symm.toEquiv
  have hZcen : Z₀ ≤ center (sesqSpecialUnitaryGroup B) := by
    intro z hz
    obtain ⟨c, hc⟩ := hZ₀ z hz
    refine mem_center_iff.2 fun y => Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul, hc, smul_mul_assoc, one_mul, mul_smul_comm,
      mul_one]
  have hZ₀3 : ∀ z ∈ Z₀, z ^ 3 = 1 := by
    intro z hz
    obtain ⟨c, hc⟩ := hZ₀ z hz
    have hdet := (mem_sesqSpecialUnitaryGroup.1 z.2).2
    rw [hc, LinearMap.det_smul, hV, Module.End.one_eq_id, LinearMap.det_id, mul_one] at hdet
    refine Subtype.ext (Units.ext ?_)
    rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, hc, smul_pow, one_pow, hdet, one_smul]
    rfl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ₀odd : Odd (Nat.card Z₀) := by
    have hp : IsPGroup 3 Z₀ := fun z => ⟨1, Subtype.ext (by rw [pow_one]; exact hZ₀3 z z.2)⟩
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact Odd.pow (by decide)
  have hoddZ : ∀ c ∈ Z₀, Odd (orderOf c) := fun c hc => by
    have := orderOf_dvd_natCard (⟨c, hc⟩ : Z₀)
    rw [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hZ₀odd this
  obtain ⟨x, hx⟩ := htL
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective Z₀ x
  have hψx₀ : ψ x₀ = t := hx
  have ht2' : t ^ 2 = 1 := by rw [← ht2, pow_orderOf_eq_one]
  have hx₀sq : x₀ ^ 2 ∈ Z₀ := by rw [← hψker, MonoidHom.mem_ker, map_pow, hψx₀, ht2']
  obtain ⟨z, hz⟩ := exists_sq_eq_of_odd hZ₀odd ⟨(x₀ ^ 2)⁻¹, Z₀.inv_mem hx₀sq⟩
  have hz2 : (z : sesqSpecialUnitaryGroup B) ^ 2 = (x₀ ^ 2)⁻¹ := congrArg Subtype.val hz
  have hzc : ∀ y : sesqSpecialUnitaryGroup B, Commute (z : sesqSpecialUnitaryGroup B) y :=
    fun y => (mem_center_iff.1 (hZcen z.2) y).symm
  set r : sesqSpecialUnitaryGroup B := x₀ * (z : sesqSpecialUnitaryGroup B) with hrdef
  have hr2 : r ^ 2 = 1 := by
    rw [hrdef, ((hzc x₀).symm).mul_pow, hz2, mul_inv_cancel]
  have hψz : ψ (z : sesqSpecialUnitaryGroup B) = 1 := by rw [← MonoidHom.mem_ker, hψker]; exact z.2
  have hψr : ψ r = t := by rw [hrdef, map_mul, hψx₀, hψz, mul_one]
  have huniq : ∀ r' : sesqSpecialUnitaryGroup B, ψ r' = t → r' ^ 2 = 1 → r' = r := by
    intro r' hr' hr'2
    have hc : r⁻¹ * r' ∈ Z₀ := by
      rw [← hψker, MonoidHom.mem_ker, map_mul, map_inv, hψr, hr', inv_mul_cancel]
    have hcomm : Commute r (r⁻¹ * r') := (mem_center_iff.1 (hZcen hc) r)
    have hcc : (r⁻¹ * r') ^ 2 = 1 := by
      have h1 : r' ^ 2 = r ^ 2 * (r⁻¹ * r') ^ 2 := by
        rw [← hcomm.mul_pow, mul_inv_cancel_left]
      rw [hr'2, hr2, one_mul] at h1
      exact h1.symm
    have := eq_one_of_sq_eq_one_of_odd (hoddZ _ hc) hcc
    calc r' = r * (r⁻¹ * r') := by group
      _ = r := by rw [this, mul_one]
  have htL : t ∈ ι.range := by rw [← hψrange, ← hψr]; exact ⟨r, rfl⟩
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← sq, ht2']
  set A := homologySubgroup B e₀ with hAdef
  have hq1 : Odd (2 ^ f + 1) := by
    have : Even (2 ^ f) := (Nat.even_pow' (by have := hK.one_le; omega)).2 even_two
    exact this.add_one
  have hAodd : Odd (Nat.card A) := by
    let φ : A →* homologyTorus (normOne K (2 ^ f)) :=
      (((glMatrix e₀ : LinearMap.GeneralLinearGroup K V →* GL (Fin 3) K).comp
        (sesqSpecialUnitaryGroup B).subtype).comp A.subtype).codRestrict _ fun a => a.2
    have hφ : Function.Injective φ := by
      intro a a' h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext ((glMatrix e₀).injective h'))
    have hdvd := Subgroup.card_dvd_of_injective φ hφ
    rw [card_homologyTorus, card_normOne_eq hK] at hdvd
    exact Odd.of_dvd_nat hq1 hdvd
  have hWodd : Odd (Nat.card W) := by
    rw [hW]
    exact Odd.of_dvd_nat hAodd (Subgroup.card_map_dvd A ψ)
  have hWIodd : Odd (Nat.card (W ⊔ I : Subgroup G)) :=
    odd_card_sup_of_le_normalizer (hWD.trans hIn) hWodd hIodd
  have hHle : H ≤ W ⊔ I := hH ▸ inf_le_left
  have hHL : H ≤ ι.range := hH ▸ inf_le_right
  have hHodd : Odd (Nat.card H) := Odd.of_dvd_nat hWIodd (Subgroup.card_dvd_of_le hHle)
  have hWL : W ≤ ι.range := by
    rw [hW, ← hψrange]
    exact map_le_range ψ A
  have hWH' : W ≤ H := hH ▸ le_inf le_sup_left hWL
  have hHD : H ≤ D := hHle.trans (sup_le hWD hID)
  set Ht := H.comap ψ with hHtdef
  have hZHt : Z₀ ≤ Ht := hψker ▸ MonoidHom.ker_le_comap ψ H
  have hmapHt : Ht.map ψ = H := by
    rw [Subgroup.map_comap_eq, hψrange, inf_of_le_right hHL]
  have hHtcard : Nat.card Ht = Nat.card H * Nat.card Z₀ := by
    have h := card_map_mul_card_ker ψ (K := Ht) (by rw [hψker]; exact hZHt)
    rw [hmapHt, hψker] at h
    exact h.symm
  have hHtodd : Odd (Nat.card Ht) := hHtcard ▸ hHodd.mul hZ₀odd
  have hHtsolv : Group.IsSolvable Ht := by
    let g : Ht →* H := (ψ.comp Ht.subtype).codRestrict H fun x => x.2
    let f' : Z₀.subgroupOf Ht →* Ht := (Z₀.subgroupOf Ht).subtype
    have hcomm : Group.IsSolvable (Z₀.subgroupOf Ht) := Group.isSolvable_of_comm fun a b => by
      have ha : ((a : Ht) : sesqSpecialUnitaryGroup B) ∈ Z₀ := Subgroup.mem_subgroupOf.1 a.2
      have h := mem_center_iff.1 (hZcen ha) ((b : Ht) : sesqSpecialUnitaryGroup B)
      exact Subtype.ext (Subtype.ext h.symm)
    exact Group.isSolvable_of_ker_le_range f' g fun x hx => ⟨⟨x, by
      rw [Subgroup.mem_subgroupOf, ← hψker, MonoidHom.mem_ker]
      exact congrArg Subtype.val (MonoidHom.mem_ker.1 hx)⟩, rfl⟩
  have htD : ∀ d ∈ D, t * d * t⁻¹ ∈ D := by
    intro d hd
    rw [hD] at hd ⊢
    obtain ⟨hdα, hdβ⟩ := Subgroup.mem_inf.1 hd
    rw [MulAction.mem_stabilizer_iff] at hdα hdβ
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩ <;> rw [MulAction.mem_stabilizer_iff, htinv, mul_smul,
      mul_smul]
    · rw [htα, hdβ, htβ]
    · rw [htβ, hdα, htα]
  have htI : ∀ i ∈ I, t * i * t⁻¹ ∈ I := by
    intro i hi
    have h1 := hDt i (hID hi)
    have e : t * i * t⁻¹ = (i⁻¹ * ⁅i, t⁆)⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact I.inv_mem (I.mul_mem (I.inv_mem hi) h1)
  have htW : ∀ w ∈ W, t * w * t⁻¹ = w := by
    intro w hw
    have h := commutatorElement_eq_one_iff_mul_comm.1 (hWt w hw)
    rw [← h]
    group
  have htH : ∀ h ∈ H, t * h * t⁻¹ ∈ H := by
    intro h hh
    rw [hH] at hh ⊢
    obtain ⟨hh1, hh2⟩ := Subgroup.mem_inf.1 hh
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem htL hh2) (inv_mem htL)⟩
    have hle : W ⊔ I ≤ (W ⊔ I).comap (MulAut.conj t).toMonoidHom := by
      refine sup_le (fun w hw => ?_) (fun i hi => ?_)
      · change (MulAut.conj t) w ∈ W ⊔ I
        rw [MulAut.conj_apply, htW w hw]
        exact mem_sup_left hw
      · change (MulAut.conj t) i ∈ W ⊔ I
        rw [MulAut.conj_apply]
        exact mem_sup_right (htI i hi)
    have := hle hh1
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  obtain ⟨a₀, ha₀A, h₀, hh₀, hne⟩ : ∃ a ∈ A, ∃ h ∈ Ht, ⁅a, h⁆ ≠ 1 := by
    by_contra! hall
    apply hWH
    rw [eq_bot_iff, commutator_le]
    intro w hw h hh
    rw [hW] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    rw [← hmapHt] at hh
    obtain ⟨h', hh', rfl⟩ := hh
    rw [← map_commutatorElement, hall a ha h' hh', map_one]
    exact one_mem _
  have ha₀A' : a₀ ∈ A := ha₀A
  obtain ⟨b, hb⟩ := ha₀A
  have hdiag₀ : ((glMatrix e₀ (a₀ : LinearMap.GeneralLinearGroup K V) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) =
        Matrix.diagonal ![((b : Kˣ) : K), ((b : Kˣ) : K), ((((b : Kˣ) * b)⁻¹ : Kˣ) : K)] := by
    have h := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hb
    simp only [homologyHom_apply, coe_diagHom, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype] at h
    refine h.symm.trans ?_
    congr 1
    funext i
    fin_cases i <;> rfl
  have hscal : ∀ c : K, ((a₀ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = c • 1 →
      a₀ ∈ center (sesqSpecialUnitaryGroup B) := by
    intro c hc
    refine mem_center_iff.2 fun y => Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul, hc, smul_mul_assoc, one_mul, mul_smul_comm,
      mul_one]
  have hb3 : ((b : Kˣ) : K) ≠ ((((b : Kˣ) * b)⁻¹ : Kˣ) : K) := by
    intro hbe
    apply hne
    have hsc : ∀ j, ((a₀ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (e₀ j) =
        ((b : Kˣ) : K) • e₀ j := by
      intro j
      rw [apply_eq_smul_of_coe_glMatrix_eq_diagonal e₀ _ hdiag₀ j]
      fin_cases j
      · rfl
      · rfl
      · exact congrArg (· • e₀ 2) hbe.symm
    have hsc' : ((a₀ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = ((b : Kˣ) : K) • 1 :=
      e₀.ext fun j => by rw [hsc]; rfl
    exact commutatorElement_eq_one_iff_mul_comm.2 (mem_center_iff.1 (hscal _ hsc') h₀).symm
  obtain ⟨hEc, hfb, hfc⟩ := eigenspace_of_coe_glMatrix_eq_diagonal e₀ hb3 hdiag₀
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hr2)
  have hrA : ∀ a ∈ A, r * a = a * r := by
    intro a ha
    have hwa : ψ a ∈ W := hW ▸ ⟨a, ha, rfl⟩
    set c := r * a * r⁻¹ * a⁻¹ with hcdef
    have hc : c ∈ Z₀ := by
      rw [← hψker, MonoidHom.mem_ker, hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, hψr,
        htW _ hwa, mul_inv_cancel]
    have hcr : r * c = c * r := (mem_center_iff.1 (hZcen hc) r)
    have e1 : r * a * r⁻¹ = c * a := by rw [hcdef]; group
    have e2 : r * (r * a * r⁻¹) * r⁻¹ = a := by
      rw [hrinv]
      calc r * (r * a * r) * r = (r * r) * a * (r * r) := by group
        _ = a := by rw [← sq, hr2, one_mul, mul_one]
    have e3 : r * (c * a) * r⁻¹ = c * (r * a * r⁻¹) := by
      rw [← mul_assoc r c a, hcr]
      group
    rw [e1, e3, e1] at e2
    have hc2 : c ^ 2 = 1 := by
      have : c * c * a = 1 * a := by rw [one_mul, mul_assoc]; exact e2
      rw [sq]
      exact mul_right_cancel this
    have hc1 := eq_one_of_sq_eq_one_of_odd (hoddZ c hc) hc2
    calc r * a = r * a * r⁻¹ * r := by group
      _ = c * a * r := by rw [e1]
      _ = a * r := by rw [hc1, one_mul]
  have hrHt : ∀ h ∈ Ht, r * h * r⁻¹ ∈ Ht := fun h hh => by
    change ψ (r * h * r⁻¹) ∈ H
    rw [map_mul, map_mul, map_inv, hψr]
    exact htH _ hh
  set H' := Ht.map (sesqSpecialUnitaryGroup B).subtype with hH'def
  have hH'S : H' ≤ sesqSpecialUnitaryGroup B := map_subtype_le _
  have hH'odd : Odd (Nat.card H') := by
    rw [hH'def, card_map_of_injective (Subgroup.subtype_injective _)]
    exact hHtodd
  have hH'solv : Group.IsSolvable H' :=
    Group.isSolvable_of_surjective ((sesqSpecialUnitaryGroup B).subtype.subgroupMap_surjective Ht)
  have ha₀Ht : a₀ ∈ Ht := by
    change ψ a₀ ∈ H
    exact hWH' (hW ▸ ⟨a₀, ha₀A', rfl⟩)
  have hw₀H' : (a₀ : LinearMap.GeneralLinearGroup K V) ∈ H' := ⟨a₀, ha₀Ht, rfl⟩
  have hwZ : ∃ g ∈ H', g * (a₀ : LinearMap.GeneralLinearGroup K V) ≠
      (a₀ : LinearMap.GeneralLinearGroup K V) * g := by
    refine ⟨h₀, ⟨h₀, hh₀, rfl⟩, fun h => hne ?_⟩
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext h.symm
  have hμnorm : hK.norm ((((b : Kˣ) * b)⁻¹ : Kˣ) : K) = 1 :=
    (mem_normOne_iff_norm hK).1 (inv_mem (mul_mem b.2 b.2))
  have hr1 : r ≠ 1 := fun h => by
    rw [h, map_one] at hψr
    rw [← hψr, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hrord : orderOf (r : LinearMap.GeneralLinearGroup K V) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hr2 hr1
  have hrN : (r : LinearMap.GeneralLinearGroup K V) ∈
      normalizer (H' : Set (LinearMap.GeneralLinearGroup K V)) := by
    rw [mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨r * h * r⁻¹, hrHt h hh, by simp⟩
    · rintro ⟨h, hh, hgh⟩
      refine ⟨r⁻¹ * h * r, ?_, ?_⟩
      · have := hrHt h hh
        rw [hrinv] at this ⊢
        exact this
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype] at hgh ⊢
        rw [hgh]
        group
  have hrw : (r : LinearMap.GeneralLinearGroup K V) * (a₀ : LinearMap.GeneralLinearGroup K V) =
      (a₀ : LinearMap.GeneralLinearGroup K V) * (r : LinearMap.GeneralLinearGroup K V) :=
    congrArg Subtype.val (hrA a₀ ha₀A')
  obtain ⟨-, hpart2⟩ := odd_solvable_unitary_homology_forces_orthogonal_monomial_action hK hV hB
    hBl hH'S hH'odd hH'solv hw₀H' hwZ hb3 hμnorm hfb hfc
  obtain ⟨e, he, heX, ⟨g₁, hg₁, d₁, hd₁, hgd₁⟩, he2, her⟩ :=
    hpart2 (r : LinearMap.GeneralLinearGroup K V) r.2 hrord hrN hrw
  have hspan : K ∙ e₀ 2 = K ∙ e 2 := by rw [he2, hEc]
  have hAe : ∀ g, g ∈ A ↔ g ∈ homologySubgroup B e := fun g =>
    ⟨mem_homologySubgroup_of_span_eq he₀ he hspan,
      mem_homologySubgroup_of_span_eq he he₀ hspan.symm⟩
  set Φ := unitaryEquiv hK e he with hΦdef
  have hΦsymm : ∀ d : GL (Fin 3) K, ∀ hd : d ∈ unitarySU 2 f K 3,
      glMatrix e ((Φ.symm ⟨d, hd⟩ : sesqSpecialUnitaryGroup B) : LinearMap.GeneralLinearGroup K V)
        = d := fun d hd => by
    rw [← coe_unitaryEquiv hK e he, ← hΦdef, MulEquiv.apply_symm_apply]
  set 𝓗 := H'.map (glMatrix e : LinearMap.GeneralLinearGroup K V →* GL (Fin 3) K) with h𝓗def
  have hmem𝓗 : ∀ g : sesqSpecialUnitaryGroup B,
      glMatrix e (g : LinearMap.GeneralLinearGroup K V) ∈ 𝓗 ↔ g ∈ Ht := by
    intro g
    constructor
    · rintro ⟨x, ⟨y, hy, rfl⟩, hxy⟩
      have h1 : ((y : sesqSpecialUnitaryGroup B) : LinearMap.GeneralLinearGroup K V) =
          (g : LinearMap.GeneralLinearGroup K V) := (glMatrix e).injective hxy
      rw [← Subtype.ext h1]
      exact hy
    · intro hg
      exact ⟨g, ⟨g, hg, rfl⟩, rfl⟩
  have h𝓗X : 𝓗 ≤ monomialX (normOne K (2 ^ f)) := by
    rintro _ ⟨g, hg, rfl⟩
    exact heX g hg
  have hXSU := monomialX_le_unitarySU hK
  have hlift : ∀ d ∈ monomialX (normOne K (2 ^ f)), ∃ g : sesqSpecialUnitaryGroup B,
      glMatrix e (g : LinearMap.GeneralLinearGroup K V) = d := fun d hd =>
    ⟨Φ.symm ⟨d, hXSU hd⟩, hΦsymm d (hXSU hd)⟩
  have hmemX : ∀ d ∈ monomialX (normOne K (2 ^ f)),
      (∀ g : sesqSpecialUnitaryGroup B, glMatrix e (g : LinearMap.GeneralLinearGroup K V) = d →
        g ∈ Ht) → d ∈ 𝓗 := by
    intro d hd h
    obtain ⟨g, hg⟩ := hlift d hd
    rw [← hg]
    exact (hmem𝓗 g).2 (h g hg)
  have hA3 : homologyTorus (normOne K (2 ^ f)) ≤ 𝓗 := by
    intro d hd
    refine hmemX d (mem_sup_left (homologyTorus_le_torus3 _ hd)) fun g hg => ?_
    have hgA : g ∈ A := (hAe g).2 (by rw [mem_homologySubgroup, hg]; exact hd)
    change ψ g ∈ H
    exact hWH' (hW ▸ ⟨g, hgA, rfl⟩)
  have hk : d₁ * cycGL ∈ 𝓗 := by rw [← hgd₁]; exact ⟨g₁, hg₁, rfl⟩
  have hTcomm : ∀ x ∈ torus3 (normOne K (2 ^ f)), ∀ y ∈ torus3 (normOne K (2 ^ f)),
      x * y = y * x := fun x hx y hy => torus3_comm _ hx hy
  have hconjk : ∀ x ∈ torus3 (normOne K (2 ^ f)),
      (d₁ * cycGL) * x * (d₁ * cycGL)⁻¹ = cycGL * x * cycGL⁻¹ := by
    intro x hx
    have hcx := cycGL_conj_mem_torus3 _ hx
    calc d₁ * cycGL * x * (d₁ * cycGL)⁻¹ = d₁ * (cycGL * x * cycGL⁻¹) * d₁⁻¹ := by group
      _ = (cycGL * x * cycGL⁻¹) * d₁ * d₁⁻¹ := by rw [hTcomm _ hd₁ _ hcx]
      _ = cycGL * x * cycGL⁻¹ := by group
  have hconj𝓗 : ∀ x ∈ 𝓗, ∀ y ∈ 𝓗, x * y * x⁻¹ ∈ 𝓗 := fun x hx y hy =>
    mul_mem (mul_mem hx hy) (inv_mem hx)
  have hA1 : ∀ a : normOne K (2 ^ f), cycGL * homologyHom _ a * cycGL⁻¹ ∈ 𝓗 := by
    intro a
    rw [← hconjk _ (homologyTorus_le_torus3 _ ⟨a, rfl⟩)]
    exact hconj𝓗 _ hk _ (hA3 ⟨a, rfl⟩)
  have hA2 : ∀ a : normOne K (2 ^ f),
      cycGL * (cycGL * homologyHom _ a * cycGL⁻¹) * cycGL⁻¹ ∈ 𝓗 := by
    intro a
    have hx : cycGL * homologyHom _ a * cycGL⁻¹ ∈ torus3 (normOne K (2 ^ f)) :=
      cycGL_conj_mem_torus3 _ (homologyTorus_le_torus3 _ ⟨a, rfl⟩)
    rw [← hconjk _ hx]
    exact hconj𝓗 _ hk _ (hA1 a)
  have hc1 : ∀ σ ∈ torus3 (normOne K (2 ^ f)), σ * cycGL * σ⁻¹ * cycGL⁻¹ ∈ 𝓗 := by
    intro σ hσ
    obtain ⟨d, hdM, hd, rfl⟩ := (mem_torus3 _).1 hσ
    rw [diagHom_mul_cycGL_mul_inv_mul_inv hd]
    refine mul_mem ?_ (hA3 ⟨⟨d 0 * d 1, mul_mem (hdM 0) (hdM 1)⟩, rfl⟩)
    have h := hA2 ⟨d 0, hdM 0⟩
    rw [homologyHom_apply, cycGL_conj_diagHom, cycGL_conj_diagHom] at h
    exact h
  have hcj : ∀ σ ∈ torus3 (normOne K (2 ^ f)), ∀ j : ℕ,
      σ * cycGL ^ j * σ⁻¹ * (cycGL ^ j)⁻¹ ∈ 𝓗 ∧
        σ * cycGL ^ j * σ⁻¹ * (cycGL ^ j)⁻¹ ∈ torus3 (normOne K (2 ^ f)) := by
    intro σ hσ j
    induction j with
    | zero =>
      rw [pow_zero, mul_one, mul_inv_cancel, inv_one, mul_one]
      exact ⟨one_mem _, one_mem _⟩
    | succ j ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have heq : σ * cycGL ^ (j + 1) * σ⁻¹ * (cycGL ^ (j + 1))⁻¹ =
          (σ * cycGL * σ⁻¹ * cycGL⁻¹) *
            (cycGL * (σ * cycGL ^ j * σ⁻¹ * (cycGL ^ j)⁻¹) * cycGL⁻¹) := by
        rw [pow_succ']
        group
      have hc1T : σ * cycGL * σ⁻¹ * cycGL⁻¹ ∈ torus3 (normOne K (2 ^ f)) := by
        have heq' : σ * cycGL * σ⁻¹ * cycGL⁻¹ = σ * (cycGL * σ⁻¹ * cycGL⁻¹) := by group
        rw [heq']
        exact mul_mem hσ (cycGL_conj_mem_torus3 _ (inv_mem hσ))
      rw [heq]
      refine ⟨mul_mem (hc1 σ hσ) ?_, mul_mem hc1T (cycGL_conj_mem_torus3 _ ih2)⟩
      rw [← hconjk _ ih2]
      exact hconj𝓗 _ hk _ ih1
  have hTN : ∀ σ ∈ torus3 (normOne K (2 ^ f)), ∀ x ∈ 𝓗, σ * x * σ⁻¹ ∈ 𝓗 := by
    intro σ hσ x hx
    obtain ⟨d, hd, j, -, rfl⟩ := exists_mem_torus3_mul_cyc _ (h𝓗X hx)
    have h1 : σ * d = d * σ := hTcomm _ hσ _ hd
    have h2 : d * (σ * cycGL ^ j * σ⁻¹ * (cycGL ^ j)⁻¹) =
        (σ * cycGL ^ j * σ⁻¹ * (cycGL ^ j)⁻¹) * d := hTcomm _ hd _ (hcj σ hσ j).2
    have heq : σ * (d * cycGL ^ j) * σ⁻¹ =
        (σ * cycGL ^ j * σ⁻¹ * (cycGL ^ j)⁻¹) * (d * cycGL ^ j) := by
      calc σ * (d * cycGL ^ j) * σ⁻¹ = (σ * d) * cycGL ^ j * σ⁻¹ := by group
        _ = d * (σ * cycGL ^ j * σ⁻¹ * (cycGL ^ j)⁻¹) * cycGL ^ j := by rw [h1]; group
        _ = (σ * cycGL ^ j * σ⁻¹ * (cycGL ^ j)⁻¹) * (d * cycGL ^ j) := by rw [h2]; group
    rw [heq]
    exact mul_mem (hcj σ hσ j).1 hx
  have hφinj : Function.Injective
      ((glMatrix e : LinearMap.GeneralLinearGroup K V →* GL (Fin 3) K).comp
        (sesqSpecialUnitaryGroup B).subtype) :=
    (glMatrix e).injective.comp (Subgroup.subtype_injective _)
  have hILH : I ⊓ ι.range ≤ H := by
    rw [hH]
    exact inf_le_inf_right _ le_sup_right
  have hTodd : Odd (Nat.card (torus3 (normOne K (2 ^ f)))) := by
    rw [card_torus3, card_normOne_eq hK]
    exact hq1.pow
  have hTr : ∀ σ ∈ torus3 (normOne K (2 ^ f)), ⁅σ, (s01GL : GL (Fin 3) K)⁆ ∈ 𝓗 := by
    intro σ hσ
    obtain ⟨τ, hτ⟩ := hlift σ (mem_sup_left hσ)
    have hτHt : ∀ h ∈ Ht, τ * h * τ⁻¹ ∈ Ht ∧ τ⁻¹ * h * τ ∈ Ht := by
      intro h hh
      have hx := (hmem𝓗 h).2 hh
      refine ⟨(hmem𝓗 _).1 ?_, (hmem𝓗 _).1 ?_⟩
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hτ]
        exact hTN σ hσ _ hx
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hτ]
        have := hTN σ⁻¹ (inv_mem hσ) _ hx
        rwa [inv_inv] at this
    have hgH : ∀ h ∈ H, (ψ τ)⁻¹ * h * ψ τ ∈ H := by
      intro h hh
      rw [← hmapHt] at hh ⊢
      obtain ⟨h', hh', rfl⟩ := hh
      exact ⟨_, (hτHt h' hh').2, by rw [map_mul, map_mul, map_inv]⟩
    have hgfix : ∀ ω ∈ ({α, β} : Set Ω), ψ τ • ω ∈ ({α, β} : Set Ω) := by
      intro ω hω
      rw [← hfix] at hω ⊢
      intro h hh
      calc h • ψ τ • ω = ψ τ • (((ψ τ)⁻¹ * h * ψ τ) • ω) := by
            rw [smul_smul, smul_smul]
            congr 1
            group
        _ = ψ τ • ω := by rw [hω _ (hgH h hh)]
    have hgodd : Odd (orderOf (ψ τ)) := by
      have h1 : orderOf τ = orderOf σ := by
        rw [← hτ]
        exact (orderOf_injective _ hφinj τ).symm
      have h2 : Odd (orderOf σ) := by
        have := orderOf_dvd_natCard (⟨σ, hσ⟩ : torus3 (normOne K (2 ^ f)))
        rw [Subgroup.orderOf_mk] at this
        exact Odd.of_dvd_nat hTodd this
      exact Odd.of_dvd_nat (h1 ▸ h2) (orderOf_map_dvd ψ τ)
    have hgα := hgfix α (Set.mem_insert _ _)
    have hgβ := hgfix β (Set.mem_insert_of_mem _ rfl)
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hgα hgβ
    obtain ⟨hgα', hgβ'⟩ := smul_eq_self_of_odd hgodd hαβ hgα hgβ
    have hgD : ψ τ ∈ D := by
      rw [hD]
      exact Subgroup.mem_inf.2 ⟨hgα', hgβ'⟩
    have hcHt : ⁅τ, r⁆ ∈ Ht := by
      change ψ ⁅τ, r⁆ ∈ H
      rw [map_commutatorElement, hψr]
      refine hILH ⟨hDt _ hgD, ?_⟩
      rw [← hψrange, ← hψr, ← map_commutatorElement]
      exact ⟨_, rfl⟩
    have h := (hmem𝓗 _).2 hcHt
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hτ,
      her] at h
    rw [commutatorElement_def]
    exact h
  have hq1M : Odd (Nat.card (normOne K (2 ^ f))) := odd_card_normOne hK
  have hA12 : ∀ a ∈ normOne K (2 ^ f), diagHom 3 ![a, a⁻¹, 1] ∈ 𝓗 := by
    intro a ha
    obtain ⟨b, hb⟩ := exists_sq_eq_of_odd hq1M ⟨a, ha⟩
    have hbT : diagHom 3 ![(b : Kˣ), (b : Kˣ)⁻¹, 1] ∈ torus3 (normOne K (2 ^ f)) := by
      refine (mem_torus3 _).2 ⟨_, fun i => ?_, by simp, rfl⟩
      fin_cases i
      · exact b.2
      · exact inv_mem b.2
      · exact one_mem _
    have h := hTr _ hbT
    rw [commutatorElement_diagHom_s01GL] at h
    have hb' : (b : Kˣ) * (b : Kˣ) = a := by rw [← sq]; exact congrArg Subtype.val hb
    convert h using 2
    funext i
    fin_cases i
    · simp [← hb']
    · simp [← hb']
    · rfl
  have hA23 : ∀ a ∈ normOne K (2 ^ f), diagHom 3 ![1, a, a⁻¹] ∈ 𝓗 := by
    intro a ha
    have hx : diagHom 3 ![a, a⁻¹, 1] ∈ torus3 (normOne K (2 ^ f)) := by
      refine (mem_torus3 _).2 ⟨_, fun i => ?_, by simp, rfl⟩
      fin_cases i
      · exact ha
      · exact inv_mem ha
      · exact one_mem _
    have h := hconj𝓗 _ hk _ (hA12 a ha)
    rw [hconjk _ hx, cycGL_conj_diagHom] at h
    exact h
  have hT𝓗 : torus3 (normOne K (2 ^ f)) ≤ 𝓗 := by
    intro x hx
    obtain ⟨d, hdM, hd, rfl⟩ := (mem_torus3 _).1 hx
    have hd1 : d 1 = (d 0)⁻¹ * (d 2)⁻¹ := by
      calc d 1 = (d 0)⁻¹ * (d 0 * d 1 * d 2) * (d 2)⁻¹ := by group
        _ = (d 0)⁻¹ * (d 2)⁻¹ := by rw [hd]; group
    have heq : diagHom 3 d =
        diagHom 3 ![d 0, (d 0)⁻¹, 1] * diagHom 3 ![1, (d 2)⁻¹, (d 2)⁻¹⁻¹] := by
      rw [← map_mul]
      congr 1
      funext i
      fin_cases i
      · simp
      · simp [hd1]
      · simp
    rw [heq]
    exact mul_mem (hA12 _ (hdM 0)) (hA23 _ (inv_mem (hdM 2)))
  have hs𝓗 : (cycGL : GL (Fin 3) K) ∈ 𝓗 := by
    have heq : (cycGL : GL (Fin 3) K) = d₁⁻¹ * (d₁ * cycGL) := by group
    rw [heq]
    exact mul_mem (inv_mem (hT𝓗 hd₁)) hk
  have h𝓗eq : 𝓗 = monomialX (normOne K (2 ^ f)) :=
    le_antisymm h𝓗X (sup_le hT𝓗 (zpowers_le.2 hs𝓗))
  have hΦapp : ∀ g : sesqSpecialUnitaryGroup B,
      ((Φ g : unitarySU 2 f K 3) : GL (Fin 3) K) =
        glMatrix e (g : LinearMap.GeneralLinearGroup K V) :=
    fun g => coe_unitaryEquiv hK e he g
  set ψ' : unitarySU 2 f K 3 →* G := ψ.comp Φ.symm.toMonoidHom with hψ'def
  have hψ' : ψ'.ker ≤ unitaryScalars hK 3 := by
    intro u hu
    have hu' : Φ.symm u ∈ Z₀ := by rw [← hψker]; exact hu
    obtain ⟨c, hc⟩ := hZ₀ _ hu'
    have hdet := (mem_sesqSpecialUnitaryGroup.1 (Φ.symm u).2).2
    rw [hc, LinearMap.det_smul, hV, Module.End.one_eq_id, LinearMap.det_id, mul_one] at hdet
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hdet
      exact zero_ne_one hdet
    rw [unitaryScalars_eq hK (by norm_num), mem_subgroupOf]
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    rw [← MulEquiv.apply_symm_apply Φ u, hΦapp, Matrix.GeneralLinearGroup.coe_scalar,
      coe_glMatrix, hc, map_smul, LinearMap.toMatrix_one, Units.val_mk0, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have hΦr : Φ r = transpositionSU hK := Subtype.ext ((hΦapp r).trans her)
  have hψ't : ψ' (transpositionSU hK) = t := by
    rw [← hΦr, hψ'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, hψr]
  have hmemSU : ∀ u : unitarySU 2 f K 3, u ∈ monomialSU ↔ Φ.symm u ∈ Ht := by
    intro u
    rw [← hmem𝓗, h𝓗eq, mem_subgroupOf, ← hΦapp, MulEquiv.apply_symm_apply]
  have hmapX : monomialSU.map ψ' = H := by
    rw [← hmapHt]
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨Φ.symm u, (hmemSU u).1 hu, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      refine ⟨Φ g, (hmemSU _).2 (by rwa [MulEquiv.symm_apply_apply]), ?_⟩
      change ψ (Φ.symm (Φ g)) = ψ g
      rw [MulEquiv.symm_apply_apply]
  have hcomm := commutator_map_monomialSU hK ψ'
  rw [hmapX, hψ't] at hcomm
  have hncard := ncard_conj_map_transpositionSU hK ψ' hψ'
  rw [hmapX, hψ't] at hncard
  have hHI : H ≤ I := by
    refine hcomm.symm.le.trans ((commutator_le).2 fun h hh y hy => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    have hk := zpow_mod_orderOf t k
    simp only [ht2, Nat.cast_ofNat] at hk
    rw [← hk]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero, commutatorElement_one_right]
      exact one_mem _
    · rw [h1, zpow_one]
      exact hDt h (hHD hh)
  refine ⟨e, he, (Subgroup.map_map _ _ _).symm.trans h𝓗eq,
    ⟨r, ⟨hψr, hr2⟩, fun r' hr' => huniq r' hr'.1 hr'.2⟩,
    fun r' h1 h2 => by rw [huniq r' h1 h2]; exact her,
    le_antisymm (le_inf hHI hHL) hILH, hcomm, hncard⟩

end CFSG.OddSolvableUnitary

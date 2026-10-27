module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Uni5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.ClassicalGroups.UnitaryFlag.PointStabilizerRank
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedAKit

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

open CFSG.LieType.SeitzGeneration HyperBlocks CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

section Orthonormal

variable {m : ℕ} {b : Module.Basis (Fin m) K V}

theorem sesq_sum_smul {n : ℕ} {h : UnitaryFieldData 2 n K} {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (horth : ∀ i j, B (b i) (b j) = if i = j then 1 else 0) (u v : Fin m → K) :
    B (∑ i, u i • b i) (∑ j, v j • b j) = ∑ i, h.bar (u i) * v i := by
  classical
  have h1 : ∀ i, B (b i) (∑ j, v j • b j) = v i := by
    intro i
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, horth]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have h2 : ∀ y : V, B (∑ i, u i • b i) y = ∑ i, h.bar (u i) * B (b i) y := by
    intro y
    have hsplit : B (∑ i, u i • b i) = ∑ i, B (u i • b i) :=
      map_sum (B : V →ₛₗ[h.bar] (V →ₗ[K] K)) (fun i => u i • b i) Finset.univ
    rw [hsplit, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  calc B (∑ i, u i • b i) (∑ j, v j • b j)
      = ∑ i, h.bar (u i) * B (b i) (∑ j, v j • b j) := h2 _
    _ = ∑ i, h.bar (u i) * v i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [h1 i]

theorem sesq_eq_sum_repr {n : ℕ} {h : UnitaryFieldData 2 n K} {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (horth : ∀ i j, B (b i) (b j) = if i = j then 1 else 0) (x y : V) :
    B x y = ∑ i, h.bar (b.repr x i) * (b.repr y i) := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  rw [sesq_sum_smul horth]

end Orthonormal

section Diagonal

variable [FiniteDimensional K V] {m : ℕ} (b : Module.Basis (Fin m) K V)

private noncomputable def diagLin (c : Fin m → Kˣ) : V →ₗ[K] V :=
  Module.Basis.constr (M' := V) b K (fun i => (c i : K) • b i)

private theorem diagLin_basis (c : Fin m → Kˣ) (i : Fin m) :
    diagLin b c (b i) = (c i : K) • b i :=
  Module.Basis.constr_basis b K (fun i => (c i : K) • b i) i

private theorem diagLin_sum_repr (c : Fin m → Kˣ) (x : V) :
    diagLin b c x = ∑ j, (b.repr x j * (c j : K)) • b j := by
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, diagLin_basis, smul_smul]

private theorem diagLin_comp (c c' : Fin m → Kˣ) :
    (diagLin b c).comp (diagLin b c') = diagLin b (c * c') := by
  refine b.ext fun i => ?_
  simp only [LinearMap.comp_apply, diagLin_basis, map_smul, smul_smul, Pi.mul_apply,
    Units.val_mul]
  congr 1
  ring

private theorem diagLin_one : diagLin b (1 : Fin m → Kˣ) = LinearMap.id := by
  refine b.ext fun i => ?_
  rw [diagLin_basis]
  simp

private noncomputable def diagEquiv (c : Fin m → Kˣ) : V ≃ₗ[K] V where
  toFun := diagLin b c
  map_add' := (diagLin b c).map_add
  map_smul' := (diagLin b c).map_smul
  invFun := diagLin b fun i => (c i)⁻¹
  left_inv x := by
    have h : (diagLin b (fun i => (c i)⁻¹)).comp (diagLin b c) = LinearMap.id := by
      rw [diagLin_comp]
      have : (fun i => (c i)⁻¹) * c = 1 := by
        ext i
        simp [Pi.mul_apply]
      rw [this, diagLin_one]
    exact LinearMap.congr_fun h x
  right_inv x := by
    have h : (diagLin b c).comp (diagLin b fun i => (c i)⁻¹) = LinearMap.id := by
      rw [diagLin_comp]
      have : c * (fun i => (c i)⁻¹) = 1 := by
        ext i
        simp [Pi.mul_apply]
      rw [this, diagLin_one]
    exact LinearMap.congr_fun h x

private theorem diagEquiv_mul (c c' : Fin m → Kˣ) :
    diagEquiv b c * diagEquiv b c' = diagEquiv b (c * c') := by
  refine LinearEquiv.ext fun x => ?_
  show diagLin b c (diagLin b c' x) = diagLin b (c * c') x
  rw [← LinearMap.comp_apply, diagLin_comp]

private noncomputable def diagHom : (Fin m → Kˣ) →* (V ≃ₗ[K] V) where
  toFun c := diagEquiv b c
  map_one' := by
    refine LinearEquiv.ext fun x => ?_
    show diagLin b 1 x = x
    rw [diagLin_one]
    rfl
  map_mul' c c' := (diagEquiv_mul b c c').symm

private theorem diagEquiv_isometry {n : ℕ} {h : UnitaryFieldData 2 n K}
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (horth : ∀ i j, B (b i) (b j) = if i = j then 1 else 0)
    {c : Fin m → Kˣ} (hμ : ∀ i, h.bar (c i : K) * (c i : K) = 1) (x y : V) :
    B (diagEquiv b c x) (diagEquiv b c y) = B x y := by
  rw [show (diagEquiv b c x : V) = diagLin b c x from rfl,
    show (diagEquiv b c y : V) = diagLin b c y from rfl,
    diagLin_sum_repr, diagLin_sum_repr, sesq_sum_smul horth,
    sesq_eq_sum_repr horth x y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  linear_combination (h.bar (b.repr x i) * b.repr y i) * hμ i

private theorem toMatrix_diagEquiv (c : Fin m → Kˣ) :
    LinearMap.toMatrix b b ((diagEquiv b c : V ≃ₗ[K] V) : V →ₗ[K] V) =
      Matrix.diagonal (fun i : Fin m => (c i : K)) := by
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
  show b.repr (diagLin b c (b j)) i = if i = j then (c i : K) else 0
  rw [diagLin_basis, map_smul, Module.Basis.repr_self]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    simp
  · rw [if_neg hij]
    simp [Finsupp.single_apply, hij]

private theorem det_diagEquiv (c : Fin m → Kˣ) :
    LinearMap.det ((diagEquiv b c : V ≃ₗ[K] V) : V →ₗ[K] V) = ∏ i, (c i : K) := by
  rw [← LinearMap.det_toMatrix b, toMatrix_diagEquiv, Matrix.det_diagonal]

end Diagonal

section QTorsion

variable {n p q : ℕ} {h : UnitaryFieldData 2 n K} {B : V →ₛₗ[h.bar] V →ₗ[K] K}

private def qCoord0 (μ : Subgroup Kˣ) (p : ↥μ × ↥μ × ↥μ) : ↥μ :=
  ⟨(p.1 : Kˣ) * (p.2.1 : Kˣ) * (p.2.2 : Kˣ), mul_mem (mul_mem p.1.2 p.2.1.2) p.2.2.2⟩

private def qCoord1 (μ : Subgroup Kˣ) (p : ↥μ × ↥μ × ↥μ) : ↥μ :=
  ⟨((p.1 : Kˣ))⁻¹, inv_mem p.1.2⟩

private def qCoord2 (μ : Subgroup Kˣ) (p : ↥μ × ↥μ × ↥μ) : ↥μ :=
  ⟨((p.2.1 : Kˣ))⁻¹, inv_mem p.2.1.2⟩

private def qCoord3 (μ : Subgroup Kˣ) (p : ↥μ × ↥μ × ↥μ) : ↥μ :=
  ⟨((p.2.2 : Kˣ))⁻¹, inv_mem p.2.2.2⟩

private theorem exists_qtorsion_scalarTuple {n m : ℕ} {h : UnitaryFieldData 2 n K}
    {μ : Subgroup Kˣ} (hm : 4 ≤ m)
    (hμbar : ∀ x : ↥μ, h.bar ((x : Kˣ) : K) * ((x : Kˣ) : K) = 1) :
    ∃ γK : (↥μ × ↥μ × ↥μ) →* (Fin m → Kˣ), Function.Injective γK ∧
      (∀ p : ↥μ × ↥μ × ↥μ, ∏ i, γK p i = 1) ∧
      (∀ (p : ↥μ × ↥μ × ↥μ) (i : Fin m),
        h.bar ((γK p i : Kˣ) : K) * ((γK p i : Kˣ) : K) = 1) := by
  let ee : Fin m ≃ Fin 4 ⊕ Fin (m - 4) :=
    (finCongr (Nat.add_sub_of_le hm)).symm.trans finSumFinEquiv.symm
  let γfun : ↥μ × ↥μ × ↥μ → (Fin m → ↥μ) := fun p i =>
    Sum.elim (fun j : Fin 4 => ![qCoord0 μ p, qCoord1 μ p, qCoord2 μ p, qCoord3 μ p] j)
      (fun _ => 1) (ee i)
  have hγone : γfun 1 = 1 := by
    funext i
    rcases hij : ee i with j | k
    · fin_cases j <;> simp [γfun, hij, qCoord0, qCoord1, qCoord2, qCoord3]
    · simp [γfun, hij]
  have hγmul : ∀ a b, γfun (a * b) = γfun a * γfun b := by
    intro a b
    funext i
    rcases hij : ee i with j | k
    · fin_cases j <;> apply Subtype.ext <;>
        simp [γfun, hij, qCoord0, qCoord1, qCoord2, qCoord3, Pi.mul_apply, mul_comm,
          mul_left_comm, mul_assoc]
    · simp [γfun, hij]
  let γK : ↥μ × ↥μ × ↥μ →* (Fin m → Kˣ) :=
    { toFun := fun p i => ((γfun p i : ↥μ) : Kˣ)
      map_one' := by funext i; simp [hγone]
      map_mul' := by intro a b; funext i; simp [hγmul, Pi.mul_apply] }
  have hprod : ∀ p : ↥μ × ↥μ × ↥μ, ∏ i, γK p i = 1 := by
    intro p
    rw [Fintype.prod_equiv ee (fun i => γK p i)
      (fun j => Sum.elim (fun j : Fin 4 => γK p (ee.symm (Sum.inl j))) (fun _ => 1) j)
      (fun i => by
        rcases hij : ee i with j | k
        · have h : ee.symm (Sum.inl j) = i := by rw [← hij, Equiv.symm_apply_apply]
          rw [Sum.elim_inl, h]
        · simp [γK, γfun, hij])]
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, Finset.prod_const_one, mul_one]
    have h0 : γK p (ee.symm (Sum.inl 0)) = (p.1 : Kˣ) * (p.2.1 : Kˣ) * (p.2.2 : Kˣ) := by
      simp [γK, γfun, Equiv.apply_symm_apply, qCoord0]
    have h1 : γK p (ee.symm (Sum.inl 1)) = ((p.1 : Kˣ))⁻¹ := by
      simp [γK, γfun, Equiv.apply_symm_apply, qCoord1]
    have h2 : γK p (ee.symm (Sum.inl 2)) = ((p.2.1 : Kˣ))⁻¹ := by
      simp [γK, γfun, Equiv.apply_symm_apply, qCoord2]
    have h3 : γK p (ee.symm (Sum.inl 3)) = ((p.2.2 : Kˣ))⁻¹ := by
      simp [γK, γfun, Equiv.apply_symm_apply, qCoord3]
    rw [h0, h1, h2, h3]
    have hx : (p.1 : Kˣ) * (p.2.1 : Kˣ) * (p.2.2 : Kˣ) * (p.1 : Kˣ)⁻¹ * (p.2.1 : Kˣ)⁻¹ *
        (p.2.2 : Kˣ)⁻¹ = ((p.1 : Kˣ) * (p.1 : Kˣ)⁻¹) * ((p.2.1 : Kˣ) * (p.2.1 : Kˣ)⁻¹) *
          ((p.2.2 : Kˣ) * (p.2.2 : Kˣ)⁻¹) := by ac_rfl
    rw [hx]; simp
  have hγinj : Function.Injective γfun := by
    intro p q hpq
    have h0 := congrFun hpq (ee.symm (Sum.inl 0))
    have h1 := congrFun hpq (ee.symm (Sum.inl 1))
    have h2 := congrFun hpq (ee.symm (Sum.inl 2))
    simp only [γfun, Equiv.apply_symm_apply, Sum.elim_inl] at h0 h1 h2
    have e1 : (p.1 : Kˣ) = (q.1 : Kˣ) := by
      have h := congrArg (fun z : ↥μ => ((z : Kˣ))) h1
      simp only [qCoord1] at h
      exact inv_injective h
    have e2 : (p.2.1 : Kˣ) = (q.2.1 : Kˣ) := by
      have h := congrArg (fun z : ↥μ => ((z : Kˣ))) h2
      simp only [qCoord2] at h
      exact inv_injective h
    have e3 : (p.2.2 : Kˣ) = (q.2.2 : Kˣ) := by
      have h : (p.1 : Kˣ) * (p.2.1 : Kˣ) * (p.2.2 : Kˣ) =
          (q.1 : Kˣ) * (q.2.1 : Kˣ) * (q.2.2 : Kˣ) := by
        have h' := congrArg (fun z : ↥μ => ((z : Kˣ))) h0
        simpa [qCoord0] using h'
      rw [e1, e2] at h
      exact mul_left_cancel h
    exact Prod.ext (Subtype.ext e1) (Prod.ext (Subtype.ext e2) (Subtype.ext e3))
  have hγKinj : Function.Injective γK := fun a b hab =>
    hγinj (funext fun i => Subtype.ext (congrFun hab i))
  exact ⟨γK, hγKinj, hprod, fun p i => hμbar (γfun p i)⟩

private theorem diagHom_injective [FiniteDimensional K V] {m : ℕ}
    (b : Module.Basis (Fin m) K V) :
    Function.Injective (diagHom b) := by
  intro c c' hcc'
  funext i
  have hb : (diagEquiv b c (b i) : V) = (diagEquiv b c' (b i) : V) := by
    rw [show diagEquiv b c = diagEquiv b c' from hcc']
  rw [show (diagEquiv b c (b i) : V) = diagLin b c (b i) from rfl,
    show (diagEquiv b c' (b i) : V) = diagLin b c' (b i) from rfl,
    diagLin_basis, diagLin_basis] at hb
  have h1 : ((c i : K) - (c' i : K)) • b i = 0 := by
    rw [sub_smul, hb, sub_self]
  rcases smul_eq_zero.mp h1 with h2 | h2
  · exact Units.ext (sub_eq_zero.mp h2)
  · exact absurd h2 (b.ne_zero i)

private theorem exists_elemAbelian_range_of_injective {q : ℕ} {M : Type} [Group M] [Finite M]
    (hq : q.Prime) {μ : Subgroup Kˣ} (hμcard : Nat.card μ = q)
    (hμexp : ∀ x : ↥μ, x ^ q = 1) (Φ : (↥μ × ↥μ × ↥μ) →* M) (hΦinj : Function.Injective Φ) :
    ∃ F : Subgroup M, IsElemAbelian q F ∧ 3 ≤ CFSG.Open.pRank q F := by
  have htop : IsElemAbelian q (⊤ : Subgroup (↥μ × ↥μ × ↥μ)) :=
    ⟨⟨⟨fun a b => mul_comm' a b⟩⟩, fun a _ => Prod.ext (hμexp a.1) (Prod.ext (hμexp a.2.1)
      (hμexp a.2.2))⟩
  have hcard : Nat.card (↥μ × ↥μ × ↥μ) = q ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod, hμcard]
    ring
  refine ⟨Φ.range, ?_, ?_⟩
  · have h := CFSG.SectionRank.isElemAbelian_map htop Φ
    rwa [Subgroup.map_top] at h
  · exact CFSG.SectionRank.le_pRank_of_injective (p := q) hq.one_lt
      (fun a b : ↥μ × ↥μ × ↥μ => mul_comm' a b)
      (fun a => Prod.ext (hμexp a.1) (Prod.ext (hμexp a.2.1) (hμexp a.2.2)))
      hcard Φ hΦinj le_rfl

theorem exists_elemAbelian_qtorsion_pointwiseStab_blockSpace [Finite K] [FiniteDimensional K V]
    (A : Subgroup (V ≃ₗ[K] V)) [Fintype A]
    (hp : p.Prime) (hpK : (p : K) ≠ 0) (hA : IsElemAbelian p A) (hB : InvariantSesq A B)
    (hBsym : B.IsSymm) (hBn : B.SeparatingLeft) (D : Hyperplane A p)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqd : q ∣ 2 ^ n + 1)
    (hm : 4 ≤ Module.finrank K (Submodule.orthogonalBilin B (blockSpace A D.1))) :
    ∃ F : Subgroup ↥(pointwiseStab (sesqSpecialUnitaryGroupLE B) (blockSpace A D.1)),
      IsElemAbelian q F ∧ 3 ≤ CFSG.Open.pRank q F := by
  classical
  haveI : Finite K := h.finite
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := finite_linearEquiv_self
  haveI : Finite ↥(sesqSpecialUnitaryGroupLE B) := Subtype.finite
  haveI : Finite ↥(pointwiseStab (sesqSpecialUnitaryGroupLE B) (blockSpace A D.1)) :=
    Subtype.finite
  have hrefl : B.IsRefl := hBsym.isRefl
  have hc := isCompl_blockSpace_orthogonalBilin A hp hpK hA hB hrefl hBn D
  let W : Submodule K V := Submodule.orthogonalBilin B (blockSpace A D.1)
  have hWsym : (B.domRestrict₁₂ W W).IsSymm := hBsym.domRestrict W
  have hWsep : (B.domRestrict₁₂ W W).SeparatingLeft :=
    separatingLeft_domRestrict_orthogonalBilin hrefl hBn hc
  haveI : FiniteDimensional K W :=
    FiniteDimensional.of_injective (Submodule.subtype W) Subtype.val_injective
  obtain ⟨b, horth⟩ := h.exists_orthonormal_basis hWsym hWsep
  obtain ⟨μ, hμcard, hμexp, hμbar⟩ :=
    CFSG.ClassicalGroups.UnitaryFlag.exists_pthRoots_subgroup h hq hqd
  obtain ⟨γK, hγKinj, hprod, hnorm⟩ := exists_qtorsion_scalarTuple hm hμbar
  let Φ : ↥μ × ↥μ × ↥μ →* (W ≃ₗ[K] W) := (diagHom b).comp γK
  have hΦcoe : ∀ p, (Φ p : W ≃ₗ[K] W) = diagEquiv b (γK p) := fun p => rfl
  have hΦmem : ∀ p, Φ p ∈ sesqSpecialUnitaryGroupLE (B.domRestrict₁₂ W W) := by
    intro p
    refine mem_sesqSpecialUnitaryGroupLE.mpr ⟨?_, ?_⟩
    · rw [hΦcoe]
      exact diagEquiv_isometry b horth (hnorm p)
    · rw [hΦcoe, det_diagEquiv, ← Units.coe_prod, hprod, Units.val_one]
  have hΦinj : Function.Injective Φ := (diagHom_injective b).comp hγKinj
  obtain ⟨e⟩ := pointwiseStab_blockSpace_mulEquiv (A := A) (B := B) hp hpK hA hB hrefl hBn D
  let Ψ : ↥μ × ↥μ × ↥μ →* ↥(pointwiseStab (sesqSpecialUnitaryGroupLE B) (blockSpace A D.1)) :=
    { toFun := fun p => e.symm ⟨Φ p, hΦmem p⟩
      map_one' := by
        show e.symm ⟨Φ 1, hΦmem 1⟩ = 1
        have h1 : (⟨Φ 1, hΦmem 1⟩ : ↥(sesqSpecialUnitaryGroupLE (B.domRestrict₁₂ W W))) = 1 :=
          Subtype.ext (map_one Φ)
        rw [h1, map_one e.symm]
      map_mul' := by
        intro a b
        have h : (⟨Φ (a * b), hΦmem (a * b)⟩ :
            ↥(sesqSpecialUnitaryGroupLE (B.domRestrict₁₂ W W))) =
            ⟨Φ a, hΦmem a⟩ * ⟨Φ b, hΦmem b⟩ := by
          apply Subtype.ext
          show Φ (a * b) = Φ a * Φ b
          exact map_mul Φ a b
        rw [h, map_mul] }
  have hΨinj : Function.Injective Ψ := by
    intro a b hab
    have h1 : (⟨Φ a, hΦmem a⟩ : ↥(sesqSpecialUnitaryGroupLE (B.domRestrict₁₂ W W))) =
        ⟨Φ b, hΦmem b⟩ := e.symm.injective hab
    exact hΦinj (Subtype.ext_iff.mp h1)
  exact exists_elemAbelian_range_of_injective hq hμcard hμexp Ψ hΨinj

end QTorsion

end CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

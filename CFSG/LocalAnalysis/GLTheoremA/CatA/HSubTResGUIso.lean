module

public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.SemisimpleCentralizers.Held Matrix

variable {E : Type} [Field E]

@[expose] noncomputable def resTau (hE : UnitaryFieldData 2 1 E) : E ≃+* E :=
  RingEquiv.ofBijective hE.bar (Function.Involutive.bijective hE.bar_bar)

theorem resTau_apply (hE : UnitaryFieldData 2 1 E) (x : E) : resTau hE x = x ^ 2 := by
  show hE.bar x = x ^ 2
  rw [UnitaryFieldData.bar_apply, pow_one]

theorem resTau_invol (hE : UnitaryFieldData 2 1 E) : ∀ x, resTau hE (resTau hE x) = x :=
  hE.bar_bar

theorem resTau_coe (hE : UnitaryFieldData 2 1 E) : ⇑(resTau hE) = ⇑hE.bar :=
  rfl

theorem sesq_eq_gramForm_of_basis {p f : ℕ} {K : Type} [Field K] {W : Type} [AddCommGroup W]
    [Module K W] (h : UnitaryFieldData p f K) {Hf : W →ₛₗ[h.bar] W →ₗ[K] K} {n : ℕ}
    (e : Module.Basis (Fin n) K W) (he : ∀ i j, Hf (e i) (e j) = if i = j then 1 else 0)
    (x y : W) :
    Hf x y = gramForm h (1 : Matrix (Fin n) (Fin n) K) (e.equivFun x) (e.equivFun y) := by
  have hx : Hf x y = Hf (∑ i, e.equivFun x i • e i) (∑ j, e.equivFun y j • e j) := by
    rw [e.sum_equivFun, e.sum_equivFun]
  rw [hx]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, he,
    smul_eq_mul]
  simp [gramForm_apply, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem resGU_coord_iff {W : Type} [AddCommGroup W] [Module E W] {n : ℕ}
    (hE : UnitaryFieldData 2 1 E) {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E}
    (e : Module.Basis (Fin n) E W) (he : ∀ i j, Hf (e i) (e j) = if i = j then 1 else 0)
    (g : LinearMap.GeneralLinearGroup E W) :
    (∀ x y : W, Hf ((g : W →ₗ[E] W) x) ((g : W →ₗ[E] W) y) = Hf x y) ↔
      ((LinearMap.toMatrix e e (g : W →ₗ[E] W)).map (resTau hE))ᵀ *
        LinearMap.toMatrix e e (g : W →ₗ[E] W) = 1 := by
  have hHc := sesq_eq_gramForm_of_basis hE e he
  have hTg : ∀ x : W, e.equivFun ((g : W →ₗ[E] W) x) =
      LinearMap.toMatrix e e (g : W →ₗ[E] W) *ᵥ e.equivFun x := fun x => by
    rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
  have hG : ∀ x y : W, Hf ((g : W →ₗ[E] W) x) ((g : W →ₗ[E] W) y) =
      gramForm hE 1 (LinearMap.toMatrix e e (g : W →ₗ[E] W) *ᵥ e.equivFun x)
        (LinearMap.toMatrix e e (g : W →ₗ[E] W) *ᵥ e.equivFun y) := fun x y => by
    rw [hHc, hTg, hTg]
  have h1 : (∀ x y : W, Hf ((g : W →ₗ[E] W) x) ((g : W →ₗ[E] W) y) = Hf x y) ↔
      ∀ u v : Fin n → E, gramForm hE 1 (LinearMap.toMatrix e e (g : W →ₗ[E] W) *ᵥ u)
        (LinearMap.toMatrix e e (g : W →ₗ[E] W) *ᵥ v) = gramForm hE 1 u v := by
    constructor
    · intro h u v
      obtain ⟨x, rfl⟩ : ∃ x : W, e.equivFun x = u :=
        ⟨e.equivFun.symm u, e.equivFun.apply_symm_apply u⟩
      obtain ⟨y, rfl⟩ : ∃ y : W, e.equivFun y = v :=
        ⟨e.equivFun.symm v, e.equivFun.apply_symm_apply v⟩
      have hxy := h x y
      rw [hG x y, hHc x y] at hxy
      exact hxy
    · intro h x y
      rw [hG x y, hHc x y]
      exact h _ _
  exact h1.trans ((gramForm_isometry_iff hE (1 : Matrix (Fin n) (Fin n) E) _).trans
    (by rw [Matrix.mul_one]; exact Iff.rfl))

theorem resGU_mulEquiv_of_basis {W : Type} [AddCommGroup W] [Module E W] {n : ℕ}
    (hE : UnitaryFieldData 2 1 E) {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E}
    (e : Module.Basis (Fin n) E W) (he : ∀ i j, Hf (e i) (e j) = if i = j then 1 else 0) :
    Nonempty (sesqUnitaryGroup Hf ≃* heldGU n E (resTau hE) (resTau_invol hE)) := by
  let ψ : LinearMap.GeneralLinearGroup E W ≃* GL (Fin n) E :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv e).toRingEquiv.toMulEquiv
  have hψ : ∀ g : LinearMap.GeneralLinearGroup E W,
      ((ψ g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
        LinearMap.toMatrix e e (g : W →ₗ[E] W) :=
    fun g => rfl
  have hkey : ∀ g : LinearMap.GeneralLinearGroup E W, g ∈ sesqUnitaryGroup Hf ↔
      (((ψ g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (resTau hE))ᵀ *
        ((ψ g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 := fun g => by
    rw [hψ, mem_sesqUnitaryGroup]
    exact resGU_coord_iff hE e he g
  have hmap : (sesqUnitaryGroup Hf).map (ψ : LinearMap.GeneralLinearGroup E W →* GL (Fin n) E) =
      heldGU n E (resTau hE) (resTau_invol hE) := by
    ext y
    refine (Subgroup.mem_map_equiv (f := ψ)).trans ?_
    rw [hkey, MulEquiv.apply_symm_apply, mem_heldGU]
  exact ⟨(MulEquiv.subgroupMap ψ (sesqUnitaryGroup Hf)).trans (MulEquiv.subgroupCongr hmap)⟩

theorem resGU_mulEquiv {W : Type} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (hE : UnitaryFieldData 2 1 E) (Hf : W →ₛₗ[hE.bar] W →ₗ[E] E) (hHs : Hf.IsSymm)
    (hHl : Hf.SeparatingLeft) :
    Nonempty (sesqUnitaryGroup Hf ≃*
      heldGU (Module.finrank E W) E (resTau hE) (resTau_invol hE)) := by
  obtain ⟨e, he⟩ := hE.exists_orthonormal_basis hHs hHl
  exact resGU_mulEquiv_of_basis hE e he

theorem resGU_isSolvable_of_resSU {n : ℕ} {τ : E ≃+* E} {hτ : ∀ x, τ (τ x) = x}
    (hSU : Group.IsSolvable ↥(heldSU n E τ hτ)) : Group.IsSolvable ↥(heldGU n E τ hτ) := by
  haveI := hSU
  haveI : Group.IsSolvable Eˣ := Group.isSolvable_of_comm fun a b => mul_comm a b
  have hle : heldSU n E τ hτ ≤ heldGU n E τ hτ := inf_le_left
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hle)
    ((Matrix.GeneralLinearGroup.det : GL (Fin n) E →* Eˣ).comp (heldGU n E τ hτ).subtype) ?_
  intro x hx
  have hdet : ((x : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).det = 1 := by
    have h : Matrix.GeneralLinearGroup.det (x : GL (Fin n) E) = 1 := hx
    have h' := congrArg Units.val h
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h'
  exact MonoidHom.mem_range.mpr
    ⟨⟨(x : GL (Fin n) E), Subgroup.mem_inf.mpr ⟨x.2, mem_statedSL_of_det hdet⟩⟩, Subtype.ext rfl⟩

theorem resGU_solvable (hE : UnitaryFieldData 2 1 E) :
    ∀ n, n ≤ 3 → Group.IsSolvable ↥(heldGU n E (resTau hE) (resTau_invol hE)) := by
  intro n hn
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · exact Group.isSolvable_of_comm fun a b =>
      Subtype.ext (mul_comm_GL_of_le_one (a := n) (by omega) a.1 b.1)
  · haveI : Finite E := hE.finite
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP E 2 := hE.charP
    have hK : Nat.card E = (2 ^ 1) ^ 2 := by
      rw [hE.card] <;> norm_num
    apply resGU_isSolvable_of_resSU
    interval_cases n
    · rw [hct_heldSU_eq_statedSU (resTau_apply hE)]
      have hc := CFSG.RankThree.SubgroupLists.card_statedSU_two (K := E) (r := 2) (f := 1) hK
      norm_num at hc
      exact hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two
        Nat.prime_three (by norm_num) (by rw [hc] <;> norm_num)
    · rw [hct_heldSU_eq_statedSU (resTau_apply hE)]
      have hc :=
        CFSG.RankThree.PartTwo.Sec8.Item87Proof.card_statedSU_three_two (F := E) (f := 1) hK
      norm_num at hc
      exact hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 3) (b := 3) Nat.prime_two
        Nat.prime_three (by norm_num) (by rw [hc] <;> norm_num)

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end

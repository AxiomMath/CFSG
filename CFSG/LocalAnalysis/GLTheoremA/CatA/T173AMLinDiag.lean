module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173
open scoped commutatorElement MatrixGroups

private theorem permMatrix_inv {d : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin d)) :
    (σ.permMatrix F)⁻¹ = σ⁻¹.permMatrix F :=
  Matrix.inv_eq_right_inv (by
    have h := Matrix.permMatrix_mul (σ := σ⁻¹) (τ := σ) (R := F)
    simpa using h.symm)

private theorem permMatrix_mul_diagonal_mul {d : ℕ} {F : Type} [Field F]
    (τ : Equiv.Perm (Fin d)) (v : Fin d → F) :
    (τ.permMatrix F) * (Matrix.diagonal v * (τ⁻¹.permMatrix F)) =
      Matrix.diagonal (fun i => v (τ i)) := by
  rw [← mul_assoc]
  ext i l
  rw [Matrix.mul_apply, Finset.sum_eq_single (τ i)]
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Matrix.mul_diagonal, Matrix.diagonal_apply]
  · intro k _ hk
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Matrix.mul_diagonal, Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem diagonal_inv {d : ℕ} {F : Type} [Field F] (v : Fin d → F)
    (hv : ∀ i, v i ≠ 0) :
    (Matrix.diagonal v)⁻¹ = Matrix.diagonal (fun i => (v i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal,
    show (fun i => v i * (v i)⁻¹) = (fun _ => 1) from
      funext fun i => mul_inv_cancel₀ (hv i),
    Matrix.diagonal_one]

private theorem diagonal_mul_single {d : ℕ} {F : Type} [Field F] (v : Fin d → F)
    (i j : Fin d) (b : F) :
    Matrix.diagonal v * Matrix.single i j b = Matrix.single i j (v i * b) := by
  ext k l
  rw [Matrix.diagonal_mul, Matrix.single_apply, Matrix.single_apply]
  by_cases h : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h, if_neg h, mul_zero]

private theorem single_mul_diagonal {d : ℕ} {F : Type} [Field F] (i j : Fin d) (a : F)
    (v : Fin d → F) :
    Matrix.single i j a * Matrix.diagonal v = Matrix.single i j (a * v j) := by
  ext k l
  rw [Matrix.mul_diagonal, Matrix.single_apply, Matrix.single_apply]
  by_cases h : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h, if_neg h, zero_mul]

private theorem diagonal_transvection_conj {d : ℕ} {F : Type} [Field F]
    (v : Fin d → F) (hv : ∀ k, v k ≠ 0) {i j : Fin d} (hij : i ≠ j) (b : F) :
    Matrix.diagonal v *
        (Matrix.SpecialLinearGroup.transvection hij b : Matrix (Fin d) (Fin d) F) *
        (Matrix.diagonal v)⁻¹ =
      (Matrix.SpecialLinearGroup.transvection hij (v i * b * (v j)⁻¹) :
        Matrix (Fin d) (Fin d) F) := by
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
    diagonal_inv v hv, Matrix.mul_add, Matrix.add_mul, mul_one, diagonal_mul_single,
    Matrix.diagonal_mul_diagonal, single_mul_diagonal,
    show (fun k => v k * (v k)⁻¹) = (fun _ => 1) from
      funext fun k => mul_inv_cancel₀ (hv k),
    Matrix.diagonal_one]

private theorem diagonal_entries_ne_zero {d : ℕ} {F : Type} [Field F] {D : GL (Fin d) F}
    {v : Fin d → F} (hD : (D : Matrix (Fin d) (Fin d) F) = Matrix.diagonal v) :
    ∀ k, v k ≠ 0 := by
  have hdet : Matrix.det (Matrix.diagonal v) ≠ 0 := by
    rw [← hD, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  rw [Matrix.det_diagonal] at hdet
  intro k
  exact (Finset.prod_ne_zero_iff.mp hdet) k (Finset.mem_univ k)

private theorem det_conj_eq_one {d : ℕ} {F : Type} [Field F] (A g : GL (Fin d) F)
    (hg : Matrix.GeneralLinearGroup.det g = 1) :
    Matrix.GeneralLinearGroup.det (A * g * A⁻¹) = 1 := by
  rw [map_mul, map_mul, map_inv, hg, mul_one]
  group

private theorem det_coe_eq_one {d : ℕ} {F : Type} [Field F]
    (u : ↥(LargeEvenSLGroup (Fin d) F)) :
    Matrix.GeneralLinearGroup.det (u : GL (Fin d) F) = 1 :=
  MonoidHom.mem_ker.mp (show (u : GL (Fin d) F) ∈
    (Matrix.GeneralLinearGroup.det (n := Fin d) (R := F)).ker from u.2)

private noncomputable def linRootHom {d : ℕ} {F : Type} [Field F] (i j : Fin d) (hij : i ≠ j) :
    Multiplicative F →* GL (Fin d) F :=
  (Matrix.SpecialLinearGroup.toGL (n := Fin d) (R := F)).comp
    { toFun := fun c => Matrix.SpecialLinearGroup.transvection hij c.toAdd
      map_one' := by
        simpa using Matrix.SpecialLinearGroup.transvection_coeff_zero hij
      map_mul' := fun a b => by
        rw [show (a * b).toAdd = a.toAdd + b.toAdd from rfl]
        exact Matrix.SpecialLinearGroup.transvection_add hij _ _ }

private noncomputable def linRoot {d : ℕ} {F : Type} [Field F] (i j : Fin d) (hij : i ≠ j) :
    Subgroup (GL (Fin d) F) := (linRootHom i j hij).range

private theorem linRootHom_apply {d : ℕ} {F : Type} [Field F] {i j : Fin d} (hij : i ≠ j)
    (c : Multiplicative F) :
    linRootHom i j hij c =
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij c.toAdd) :=
  rfl

private theorem linRoot_le_SL {d : ℕ} {F : Type} [Field F] {i j : Fin d} (hij : i ≠ j) :
    linRoot i j hij ≤ LargeEvenSLGroup (Fin d) F := by
  intro g hg
  rw [linRoot] at hg
  obtain ⟨c, rfl⟩ := hg
  rw [linRootHom_apply]
  have h : Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij c.toAdd) ∈
      (Matrix.SpecialLinearGroup.toGL (n := Fin d) (R := F)).range := ⟨_, rfl⟩
  rwa [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det] at h

private theorem diagonal_conj_mem_linRoot {d : ℕ} {F : Type} [Field F]
    {i j : Fin d} (hij : i ≠ j) (D : GL (Fin d) F) (v : Fin d → F)
    (hD : (D : Matrix (Fin d) (Fin d) F) = Matrix.diagonal v) (hv : ∀ k, v k ≠ 0)
    {g : GL (Fin d) F} (hg : g ∈ linRoot i j hij) :
    D * g * D⁻¹ ∈ linRoot i j hij := by
  rw [linRoot] at hg
  obtain ⟨c, rfl⟩ := hg
  refine ⟨Multiplicative.ofAdd (v i * c.toAdd * (v j)⁻¹), ?_⟩
  apply Units.ext
  change (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij
      (v i * c.toAdd * (v j)⁻¹)) : Matrix (Fin d) (Fin d) F) =
    ((D * Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij c.toAdd) *
      D⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hD,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  exact (diagonal_transvection_conj v hv hij c.toAdd).symm

private theorem diagonal_mul_diagonal_comm {d : ℕ} {F : Type} [Field F] (u v : Fin d → F) :
    Matrix.diagonal u * Matrix.diagonal v = Matrix.diagonal v * Matrix.diagonal u := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

private theorem toMonoidHom_conj_apply {G : Type*} [Group G] (g x : G) :
    (MulEquiv.toMonoidHom (MulAut.conj g)) x = g * x * g⁻¹ := rfl

private theorem conj_mem_Root_of_diag {d : ℕ} {F : Type} [Field F] {i j : Fin d} (hij : i ≠ j)
    (P A : GL (Fin d) F) (v : Fin d → F)
    (hA : ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = Matrix.diagonal v)
    (hv : ∀ k, v k ≠ 0)
    {y : GL (Fin d) F} (hy : y ∈ (linRoot i j hij).map (MulAut.conj P⁻¹).toMonoidHom) :
    A * y * A⁻¹ ∈ (linRoot i j hij).map (MulAut.conj P⁻¹).toMonoidHom := by
  obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp hy
  rw [← hgy, toMonoidHom_conj_apply]
  have hmem : (MulEquiv.toMonoidHom (MulAut.conj P⁻¹))
      ((P * A * P⁻¹) * g * (P * A * P⁻¹)⁻¹) ∈
      (linRoot i j hij).map (MulAut.conj P⁻¹).toMonoidHom :=
    Subgroup.mem_map_of_mem _
      (diagonal_conj_mem_linRoot hij (P * A * P⁻¹) v hA hv hg)
  convert hmem using 1
  rw [toMonoidHom_conj_apply]
  group

private theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (h' : ∀ x ∈ H, g⁻¹ * x * g ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => h x hx, fun hx => by
    have := h' (g * x * g⁻¹) hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this⟩

theorem lin_ES_le {p n d : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω}
    {x : Ω} (hcfg : Cfg173 p S B N D K x) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (hd : 3 ≤ d) (hpd : p ∣ d) (hpF : p ∣ 2 ^ n - 1)
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F))
    (ψ : ↥(LargeEvenSLGroup (Fin d) F) →* ↥S) (hψ : GLifts θ ψ) (P : GL (Fin d) F)
    (hB : ∀ b ∈ B, GDiagAct p ψ P b) {t : GL (Fin d) F} (ht : t ∈ LinDiagTors p d F)
    {u : ↥(LargeEvenSLGroup (Fin d) F)} (hu : (u : GL (Fin d) F) = P⁻¹ * t * P) :
    (ψ u : Ω) ∈ B := by
  classical
  have hBelem : IsElemAbelian p B := hcfg.bmax.1
  have hker : ∀ u : ↥(LargeEvenSLGroup (Fin d) F), ψ u = 1 →
      (u : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := by
    intro u hu
    have h := hψ u
    rw [hu] at h
    simp only [QuotientGroup.mk_one, map_one] at h
    have h1 : LargeEvenProjMk (LargeEvenSLGroup (Fin d) F) u = 1 := h.symm
    have h2 : u ∈ (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)).ker :=
      MonoidHom.mem_ker.mpr h1
    rw [LargeEvenProjMk, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at h2
    exact h2
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have : (i : ℕ) = (j : ℕ) := congrArg Fin.val h
    simp [i, j] at this
  let Root : Subgroup (GL (Fin d) F) := (linRoot i j hij).map (MulAut.conj P⁻¹).toMonoidHom
  have hRootSL : Root ≤ LargeEvenSLGroup (Fin d) F := by
    rintro _ ⟨g, hg, rfl⟩
    rw [toMonoidHom_conj_apply]
    exact det_conj_eq_one P⁻¹ g (MonoidHom.mem_ker.mp (linRoot_le_SL hij hg))
  let RootU : Subgroup ↥(LargeEvenSLGroup (Fin d) F) := Root.subgroupOf _
  let RootS : Subgroup ↥S := RootU.map ψ
  let RootΩ : Subgroup Ω := RootS.map S.subtype
  have hRootΩ2 : IsPGroup 2 RootΩ := by
    have hAdd : IsPGroup 2 (Multiplicative F) :=
      IsPGroup.of_card (n := n) (by rw [Nat.card_congr Multiplicative.toAdd, hF])
    have hRoot2Base : IsPGroup 2 (linRoot (F := F) i j hij) := by
      rw [linRoot, ← Subgroup.map_top]
      exact IsPGroup.map (H := ⊤) (hAdd.of_equiv Subgroup.topEquiv.symm)
        (linRootHom (F := F) i j hij)
    have hRoot2 : IsPGroup 2 Root :=
      hRoot2Base.of_equiv (MulEquiv.subgroupMap (MulAut.conj P⁻¹ : GL (Fin d) F ≃* GL (Fin d) F)
        (linRoot i j hij))
    have hRootU2 : IsPGroup 2 RootU :=
      hRoot2.of_equiv (Subgroup.subgroupOfEquivOfLe hRootSL).symm
    exact (hRootU2.map ψ).map S.subtype
  have hRootΩne : RootΩ ≠ ⊥ := by
    let g0 : GL (Fin d) F :=
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij 1)
    have hg0root : g0 ∈ linRoot i j hij := by
      rw [linRoot]
      exact ⟨Multiplicative.ofAdd 1, rfl⟩
    have hg0ns : g0 ∉ LargeEvenScalars (Fin d) F := by
      intro h
      obtain ⟨a, ha⟩ := h
      have hzero : (Matrix.GeneralLinearGroup.scalar (Fin d) a :
          Matrix (Fin d) (Fin d) F) i j = 0 := by
        rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          Matrix.diagonal_apply_ne _ hij]
      have hone : (g0 : Matrix (Fin d) (Fin d) F) i j = 1 := by
        dsimp only [g0]
        rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
          Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply,
          Matrix.one_apply_ne hij, Matrix.single_apply_same, zero_add]
      rw [ha] at hzero
      rw [hzero] at hone
      exact one_ne_zero hone.symm
    let g1 : GL (Fin d) F := (MulEquiv.toMonoidHom (MulAut.conj P⁻¹)) g0
    have hg1Root : g1 ∈ Root := by
      dsimp only [g1]
      exact Subgroup.mem_map_of_mem _ hg0root
    have hg1ns : g1 ∉ LargeEvenScalars (Fin d) F := by
      intro h
      apply hg0ns
      have hconj : P * g1 * P⁻¹ = g0 := by
        dsimp only [g1]
        rw [toMonoidHom_conj_apply]
        group
      rw [← hconj]
      exact (inferInstance : (LargeEvenScalars (Fin d) F).Normal).conj_mem g1 h P
    have hg1U : g1 ∈ LargeEvenSLGroup (Fin d) F := hRootSL hg1Root
    let u1 : ↥(LargeEvenSLGroup (Fin d) F) := ⟨g1, hg1U⟩
    have hpsi1 : ψ u1 ≠ 1 := fun h => hg1ns (hker u1 h)
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨(ψ u1 : Ω), ?_⟩, ?_⟩
    · exact Subgroup.mem_map_of_mem S.subtype
        (Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr hg1Root))
    · intro h
      apply hpsi1
      exact Subtype.ext (by simpa using congrArg Subtype.val h)
  set w : Ω := (ψ u : Ω) with hwdef
  have ht_diag : (t : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal (fun k => (t : Matrix (Fin d) (Fin d) F) k k) := by
    ext k l
    by_cases hkl : k = l
    · subst hkl; rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hkl, ht.2.1 k l hkl]
  have ht_pow : t ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_one]
    have hmat : (t : Matrix (Fin d) (Fin d) F) ^ p = 1 := by
      rw [ht_diag, Matrix.diagonal_pow]
      ext k l
      by_cases hkl : k = l
      · subst hkl
        rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
        simpa using ht.2.2 k
      · rw [Matrix.diagonal_apply_ne _ hkl, Matrix.one_apply_ne hkl]
    exact hmat
  have hu_pow : u ^ p = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [hu]
    have hconjpow : (P⁻¹ * t * P) ^ p = P⁻¹ * t ^ p * P := by
      rw [show P⁻¹ * t * P = (MulAut.conj P⁻¹) t from (MulAut.conj_apply P⁻¹ t).symm,
        ← map_pow, MulAut.conj_apply]
      group
    rw [hconjpow, ht_pow]
    group
  have hwp : w ^ p = 1 := by
    have h1 : (ψ (u ^ p) : Ω) = w ^ p := by
      rw [hwdef, map_pow, Subgroup.coe_pow]
    rw [← h1, hu_pow, map_one]
    rfl
  let E : Subgroup Ω := B ⊔ Subgroup.zpowers w
  have hEelem : IsElemAbelian p E := by
    refine IsElemAbelian.sup_of_commute hBelem (isElemAbelian_zpowers hwp) ?_
    intro b hb z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hbw : b * w = w * b := by
      obtain ⟨A, hActs, _hAp, hdiag⟩ := hB b hb
      obtain ⟨dvec, hdvec⟩ := hdiag
      have hv : ∀ k, dvec k ≠ 0 := diagonal_entries_ne_zero hdvec
      have hPuP : P * (u : GL (Fin d) F) * P⁻¹ = t := by rw [hu]; group
      have hDcomm : (P * A * P⁻¹) * t = t * (P * A * P⁻¹) := by
        apply Units.ext
        show ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
            ((t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
          ((t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
            ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
        rw [hdvec, ht_diag]
        exact diagonal_mul_diagonal_comm _ _
      have hDcomm' : (P * A * P⁻¹) * (P * (u : GL (Fin d) F) * P⁻¹) =
          (P * (u : GL (Fin d) F) * P⁻¹) * (P * A * P⁻¹) := by
        rw [hPuP]; exact hDcomm
      have hAu' : A * (u : GL (Fin d) F) = (u : GL (Fin d) F) * A := by
        have hcongr := congrArg (fun x : GL (Fin d) F => P⁻¹ * x * P) hDcomm'
        convert hcongr using 1 <;> group
      have hAu : A * (u : GL (Fin d) F) * A⁻¹ = (u : GL (Fin d) F) := by
        rw [hAu']; group
      have h := hActs u u hAu.symm
      rw [← hwdef] at h
      calc b * w = b * (b⁻¹ * w * b) := congrArg (fun x => b * x) h
        _ = w * b := by group
    exact (show Commute b w from hbw).zpow_right k |>.eq
  have hBnorm : B ≤ Subgroup.normalizer (RootΩ : Set Ω) := by
    intro b hb
    apply mem_normalizer_of_conj_mem
    · intro x hx
      obtain ⟨s, hs, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hs
      obtain ⟨A', hActs', _hAp', hdiag'⟩ := hB b⁻¹ (B.inv_mem hb)
      obtain ⟨evec, hevec⟩ := hdiag'
      have hev : ∀ k, evec k ≠ 0 := diagonal_entries_ne_zero hevec
      have hyR : (y : GL (Fin d) F) ∈ Root := Subgroup.mem_subgroupOf.mp hy
      have hy' : A' * (y : GL (Fin d) F) * A'⁻¹ ∈ Root :=
        conj_mem_Root_of_diag hij P A' evec hevec hev hyR
      let y' : ↥(LargeEvenSLGroup (Fin d) F) := ⟨A' * (y : GL (Fin d) F) * A'⁻¹, hRootSL hy'⟩
      have hActs'y : (ψ y' : Ω) = (b⁻¹)⁻¹ * (ψ y : Ω) * b⁻¹ := hActs' y y' rfl
      have hb' : b * (ψ y : Ω) * b⁻¹ = (ψ y' : Ω) := by
        rw [hActs'y]; group
      change b * (ψ y : Ω) * b⁻¹ ∈ RootΩ
      rw [hb']
      exact Subgroup.mem_map_of_mem S.subtype
        (Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr hy'))
    · intro x hx
      obtain ⟨s, hs, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hs
      obtain ⟨A, hActs, _hAp, hdiag⟩ := hB b hb
      obtain ⟨dvec, hdvec⟩ := hdiag
      have hv : ∀ k, dvec k ≠ 0 := diagonal_entries_ne_zero hdvec
      have hyR : (y : GL (Fin d) F) ∈ Root := Subgroup.mem_subgroupOf.mp hy
      have hy' : A * (y : GL (Fin d) F) * A⁻¹ ∈ Root :=
        conj_mem_Root_of_diag hij P A dvec hdvec hv hyR
      let y' : ↥(LargeEvenSLGroup (Fin d) F) := ⟨A * (y : GL (Fin d) F) * A⁻¹, hRootSL hy'⟩
      have hActs_y : (ψ y' : Ω) = b⁻¹ * (ψ y : Ω) * b := hActs y y' rfl
      change b⁻¹ * (ψ y : Ω) * b ∈ RootΩ
      rw [← hActs_y]
      exact Subgroup.mem_map_of_mem S.subtype
        (Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr hy'))
  have hwN : w ∈ Subgroup.normalizer (RootΩ : Set Ω) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨s, hs, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hs
      have hyR : (y : GL (Fin d) F) ∈ Root := Subgroup.mem_subgroupOf.mp hy
      have hPuP : P * (u : GL (Fin d) F) * P⁻¹ = t := by rw [hu]; group
      have hAw : ((P * (u : GL (Fin d) F) * P⁻¹ : GL (Fin d) F) :
          Matrix (Fin d) (Fin d) F) =
          Matrix.diagonal (fun k => (t : Matrix (Fin d) (Fin d) F) k k) := by
        rw [hPuP]; exact ht_diag
      have htv : ∀ k, (t : Matrix (Fin d) (Fin d) F) k k ≠ 0 :=
        diagonal_entries_ne_zero ht_diag
      have hy' : u * (y : GL (Fin d) F) * u⁻¹ ∈ Root :=
        conj_mem_Root_of_diag hij P u (fun k => (t : Matrix (Fin d) (Fin d) F) k k) hAw htv hyR
      let y' : ↥(LargeEvenSLGroup (Fin d) F) := ⟨u * (y : GL (Fin d) F) * u⁻¹, hRootSL hy'⟩
      have h1 : (ψ y' : Ω) = (ψ u : Ω) * (ψ y : Ω) * (ψ u : Ω)⁻¹ := by
        show (ψ (u * y * u⁻¹) : Ω) = (ψ u : Ω) * (ψ y : Ω) * (ψ u : Ω)⁻¹
        rw [map_mul, map_mul, map_inv]
        rfl
      change w * (ψ y : Ω) * w⁻¹ ∈ RootΩ
      rw [hwdef, ← h1]
      exact Subgroup.mem_map_of_mem S.subtype
        (Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr hy'))
    · exact le_of_eq (Subgroup.card_map_of_injective (K := RootΩ) (MulAut.conj w).injective).symm
  have hEnorm : E ≤ Subgroup.normalizer (RootΩ : Set Ω) :=
    sup_le hBnorm (Subgroup.zpowers_le.mpr hwN)
  have hEB : E = B :=
    GLAIsBmax.eq_of_le hcfg.prime hcfg.bmax le_sup_left hEelem hRootΩne hRootΩ2 hEnorm
  have hwB : w ∈ B := hEB ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  simpa [hwdef] using hwB

theorem lin_perm_mem_N {p n d : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω}
    {x : Ω} (hcfg : Cfg173 p S B N D K x) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (hd : 3 ≤ d) (hpd : p ∣ d) (hpF : p ∣ 2 ^ n - 1)
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F))
    (ψ : ↥(LargeEvenSLGroup (Fin d) F) →* ↥S) (hψ : GLifts θ ψ) (P : GL (Fin d) F)
    (hB : ∀ b ∈ B, GDiagAct p ψ P b)
    (hES : ∀ (t : GL (Fin d) F) (u : ↥(LargeEvenSLGroup (Fin d) F)), t ∈ LinDiagTors p d F →
      (u : GL (Fin d) F) = P⁻¹ * t * P → (ψ u : Ω) ∈ B)
    (σ : Equiv.Perm (Fin d)) (Pσ : GL (Fin d) F)
    (hPσ : (Pσ : Matrix (Fin d) (Fin d) F) = σ.permMatrix F)
    {u : ↥(LargeEvenSLGroup (Fin d) F)} (hu : (u : GL (Fin d) F) = P⁻¹ * Pσ * P) :
    (ψ u : Ω) ∈ N := by
  classical
  have hxcent : x ∈ Subgroup.centralizer (S : Set Ω) :=
    (hcfg.cent x hcfg.mem).mpr (Subgroup.mem_zpowers x)
  set w : Ω := (ψ u : Ω) with hwdef
  have hPuP : P * (u : GL (Fin d) F) * P⁻¹ = Pσ := by
    rw [hu]; group
  have hwN : w ∈ Subgroup.normalizer (B : Set Ω) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨A, hActs, hAp, hdiag⟩ := hB z hz
      obtain ⟨dvec, hdvec⟩ := hdiag
      have hv : ∀ k, dvec k ≠ 0 := diagonal_entries_ne_zero hdvec
      let AuA : ↥(LargeEvenSLGroup (Fin d) F) :=
        ⟨A * (u : GL (Fin d) F) * A⁻¹, by
          show A * (u : GL (Fin d) F) * A⁻¹ ∈
            (Matrix.GeneralLinearGroup.det (n := Fin d) (R := F)).ker
          rw [MonoidHom.mem_ker]
          exact det_conj_eq_one A (u : GL (Fin d) F) (det_coe_eq_one u)⟩
      have hActsA : (ψ AuA : Ω) = z⁻¹ * w * z := by
        simpa [hwdef] using hActs u AuA rfl
      let vU : ↥(LargeEvenSLGroup (Fin d) F) := AuA * u⁻¹
      have hvUcoe : (vU : GL (Fin d) F) =
          A * (u : GL (Fin d) F) * A⁻¹ * (u : GL (Fin d) F)⁻¹ := by
        simp [vU, AuA, Subgroup.coe_mul, Subgroup.coe_inv]
      let t : GL (Fin d) F := (P * A * P⁻¹) * Pσ * (P * A * P⁻¹)⁻¹ * Pσ⁻¹
      have ht_matrix : (t : Matrix (Fin d) (Fin d) F) =
          Matrix.diagonal (fun i => dvec i * (dvec (σ i))⁻¹) := by
        dsimp only [t]
        rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
          Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv,
          Matrix.GeneralLinearGroup.coe_inv, hdvec, hPσ,
          diagonal_inv dvec hv, permMatrix_inv, mul_assoc, mul_assoc,
          permMatrix_mul_diagonal_mul, Matrix.diagonal_mul_diagonal]
      have ht_mem : t ∈ LinDiagTors p d F := by
        refine ⟨?_, ?_, ?_⟩
        · show t ∈ (Matrix.GeneralLinearGroup.det (n := Fin d) (R := F)).ker
          rw [MonoidHom.mem_ker]
          apply Units.ext
          rw [Matrix.GeneralLinearGroup.val_det_apply, ht_matrix, Matrix.det_diagonal,
            Units.val_one]
          rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Equiv.prod_comp σ dvec]
          exact mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr fun i _ => hv i)
        · intro i j hij
          rw [ht_matrix, Matrix.diagonal_apply_ne _ hij]
        · intro i
          rw [ht_matrix, Matrix.diagonal_apply_eq]
          obtain ⟨a, ha⟩ := hAp
          have hconjpow : (P * A * P⁻¹) ^ p = P * A ^ p * P⁻¹ := by
            rw [show P * A * P⁻¹ = (MulAut.conj P) A from (MulAut.conj_apply P A).symm,
              ← map_pow, MulAut.conj_apply]
          have hDpow : (P * A * P⁻¹) ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) a := by
            rw [hconjpow, ← ha, (Matrix.GeneralLinearGroup.scalar_commute a P).symm]
            group
          have hDpow_mat : (Matrix.diagonal dvec) ^ p =
              Matrix.diagonal (fun _ : Fin d => (a : F)) := by
            have h1 : ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) ^ p =
                (Matrix.GeneralLinearGroup.scalar (Fin d) a : Matrix (Fin d) (Fin d) F) := by
              simpa only [Units.val_pow_eq_pow_val] using
                congrArg (fun g : GL (Fin d) F => (g : Matrix (Fin d) (Fin d) F)) hDpow
            rwa [hdvec, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h1
          have hpi_a : ∀ k, dvec k ^ p = (a : F) := by
            have h2 : Matrix.diagonal (dvec ^ p) =
                Matrix.diagonal (fun _ : Fin d => (a : F)) := by
              simpa only [Matrix.diagonal_pow] using hDpow_mat
            intro k
            have := congrFun (Matrix.diagonal_injective h2) k
            simpa using this
          have hpi : dvec i ^ p = dvec (σ i) ^ p := by rw [hpi_a i, hpi_a (σ i)]
          rw [mul_pow, inv_pow, hpi]
          exact mul_inv_cancel₀ (pow_ne_zero p (hv (σ i)))
      have hconj : (P * A * P⁻¹) * (P * (u : GL (Fin d) F) * P⁻¹) *
            (P * A * P⁻¹)⁻¹ * (P * (u : GL (Fin d) F) * P⁻¹)⁻¹ =
          P * (A * (u : GL (Fin d) F) * A⁻¹ * (u : GL (Fin d) F)⁻¹) * P⁻¹ := by
        group
      have ht_eq : t = P * (vU : GL (Fin d) F) * P⁻¹ := by
        dsimp only [t]
        rw [← hPuP, hconj, ← hvUcoe]
      have hvU : (vU : GL (Fin d) F) = P⁻¹ * t * P := by
        rw [ht_eq]; group
      have hpsi : (ψ vU : Ω) ∈ B := hES t vU ht_mem hvU
      have hwz : w * z * w⁻¹ = z * (ψ vU : Ω) := by
        have h1 : (ψ vU : Ω) = (ψ AuA : Ω) * w⁻¹ := by
          have h2 : (ψ vU : Ω) = (ψ AuA : Ω) * (ψ u : Ω)⁻¹ := by
            show (ψ (AuA * u⁻¹) : Ω) = (ψ AuA : Ω) * (ψ u : Ω)⁻¹
            rw [map_mul, map_inv]
            rfl
          rwa [← hwdef] at h2
        rw [h1, hActsA]
        group
      change w * z * w⁻¹ ∈ B
      rw [hwz]
      exact B.mul_mem hz hpsi
    · exact le_of_eq (Subgroup.card_map_of_injective (K := B) (MulAut.conj w).injective).symm
  have hwC : w ∈ Subgroup.centralizer ({x} : Set Ω) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hxcent) (ψ u : Ω) (ψ u).2
  rw [hcfg.hN]
  exact ⟨hwN, hwC⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end

module

public import CFSG.GroupTheory.WeirSylow.UnitaryBridge
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GroupTheory.WeirSylow.GL
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.GroupTheory.WeirSylow Module
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Quasithin (StatedGU)
open scoped Matrix

variable {p₀ f : ℕ} {L : Type} [Field L] {h : UnitaryFieldData p₀ f L}

private theorem gu_det_pow_of_unitary (h : UnitaryFieldData p₀ f L) {q : ℕ} (hq : q = p₀ ^ f)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) L) (hA : (A.map (· ^ q))ᵀ * A = 1) :
    A.det ^ (q + 1) = 1 := by
  have hfun : (fun x : L => x ^ q) = ⇑h.bar := funext fun x => (unitaryBar_eq_pow h hq x).symm
  have hdet : (A.map ⇑h.bar).det = A.det ^ q := by
    have := RingHom.map_det h.bar A
    rw [unitaryBar_eq_pow h hq] at this
    exact this.symm
  rw [hfun] at hA
  have h1 := congrArg Matrix.det hA
  rw [Matrix.det_mul, Matrix.det_transpose, hdet, Matrix.det_one] at h1
  rw [pow_succ]
  exact h1

private theorem gu_unitary_mul (h : UnitaryFieldData p₀ f L) {q : ℕ} (hq : q = p₀ ^ f) {n : ℕ}
    {X Y : Matrix (Fin n) (Fin n) L} (hX : (X.map (· ^ q))ᵀ * X = 1)
    (hY : (Y.map (· ^ q))ᵀ * Y = 1) : ((X * Y).map (· ^ q))ᵀ * (X * Y) = 1 := by
  have hfun : (fun x : L => x ^ q) = ⇑h.bar := funext fun x => (unitaryBar_eq_pow h hq x).symm
  rw [hfun] at hX hY ⊢
  rw [Matrix.map_mul, Matrix.transpose_mul]
  calc (Y.map ⇑h.bar)ᵀ * (X.map ⇑h.bar)ᵀ * (X * Y)
      = (Y.map ⇑h.bar)ᵀ * (((X.map ⇑h.bar)ᵀ * X) * Y) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hX, Matrix.one_mul, hY]

private theorem gu_unitary_inv (h : UnitaryFieldData p₀ f L) {q : ℕ} (hq : q = p₀ ^ f) {n : ℕ}
    {X : GL (Fin n) L}
    (hX : ((X : Matrix (Fin n) (Fin n) L).map (· ^ q))ᵀ * (X : Matrix (Fin n) (Fin n) L) = 1) :
    (((X⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (· ^ q))ᵀ *
      ((X⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
  have hfun : (fun x : L => x ^ q) = ⇑h.bar := funext fun x => (unitaryBar_eq_pow h hq x).symm
  have hXY : (X : Matrix (Fin n) (Fin n) L) * ((X⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      1 :=
    Units.mul_inv X
  rw [hfun] at hX ⊢
  have hMT : ((X : Matrix (Fin n) (Fin n) L).map ⇑h.bar)ᵀ =
      ((X⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    calc ((X : Matrix (Fin n) (Fin n) L).map ⇑h.bar)ᵀ
        = ((X : Matrix (Fin n) (Fin n) L).map ⇑h.bar)ᵀ *
            ((X : Matrix (Fin n) (Fin n) L) * ((X⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
          rw [hXY, Matrix.mul_one]
      _ = (((X : Matrix (Fin n) (Fin n) L).map ⇑h.bar)ᵀ * (X : Matrix (Fin n) (Fin n) L)) *
            ((X⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
          rw [Matrix.mul_assoc]
      _ = ((X⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
          rw [hX, Matrix.one_mul]
  have h3 : (X : Matrix (Fin n) (Fin n) L).map ⇑h.bar *
      ((X⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map ⇑h.bar = 1 := by
    rw [← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]
  calc (((X⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map ⇑h.bar)ᵀ *
        ((X⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
      = (((X⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map ⇑h.bar)ᵀ *
        ((X : Matrix (Fin n) (Fin n) L).map ⇑h.bar)ᵀ := by
          rw [hMT]
    _ = ((X : Matrix (Fin n) (Fin n) L).map ⇑h.bar *
        ((X⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map ⇑h.bar)ᵀ := by
          rw [Matrix.transpose_mul]
    _ = 1 := by rw [h3, Matrix.transpose_one]

private theorem gu_unitary_of_mem_statedGU (h : UnitaryFieldData p₀ f L) {q : ℕ}
    (hq : q = p₀ ^ f) {n : ℕ} {g : GL (Fin n) L} (hg : g ∈ StatedGU n q L) :
    ((g : Matrix (Fin n) (Fin n) L).map (· ^ q))ᵀ * (g : Matrix (Fin n) (Fin n) L) = 1 := by
  unfold StatedGU at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    have hfun : (fun x : L => x ^ q) = ⇑h.bar := funext fun x => (unitaryBar_eq_pow h hq x).symm
    rw [hfun, Units.val_one, Matrix.map_one _ (map_zero h.bar) (map_one h.bar),
      Matrix.transpose_one, Matrix.one_mul]
  | mul x y _ _ hx hy =>
    rw [Units.val_mul]
    exact gu_unitary_mul h hq hx hy
  | inv x _ hx => exact gu_unitary_inv h hq hx

theorem exists_injective_isom_statedGU_det {q : ℕ} (hq : q = p₀ ^ f) [Finite L]
    (S : FormSpace L L) (hS : IsHermitianSpace h S) {n : ℕ} (hdim : finrank L S.V = n) :
    ∃ ψ : S.isom →* StatedGU n q L, Function.Injective ψ ∧
      ∀ g : S.isom, ((ψ g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det =
        LinearMap.det ((g : S.V ≃ₗ[L] S.V) : S.V →ₗ[L] S.V) := by
  obtain ⟨B, hBF, hBs, hBn⟩ := hS
  obtain ⟨e₀, he₀⟩ := h.exists_orthonormal_basis hBs hBn
  let e := e₀.reindex (finCongr hdim)
  have he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0 := fun i j => by
    simp only [e, Module.Basis.reindex_apply, he₀, (finCongr hdim).symm.injective.eq_iff]
  have hι : ∀ x y, stdHerm h n (e.equivFun x) (e.equivFun y) = B x y := by
    have := LinearMap.ext_basis e e
      (B := ((stdHerm h n).comp e.equivFun.toLinearMap).compl₂ e.equivFun.toLinearMap) (B' := B)
      fun i j => by
        simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, Module.Basis.repr_self,
          Module.Basis.repr_self, Finsupp.single_eq_pi_single, Finsupp.single_eq_pi_single,
          stdHerm_single, he]
    intro x y
    have h' := congrArg (fun C : S.V →ₛₗ[h.bar] S.V →ₗ[L] L => C x y) this
    simpa using h'
  let e₁ : S.isom ≃* stdHermIsom h n :=
    formIsometryGroupCongr e.equivFun fun x y => by rw [hBF]; exact hι x y
  have hmem : ∀ g : stdHermIsom h n, matrixEquiv g.1 ∈ StatedGU n q L := fun g => by
    rw [← map_stdHermIsom_eq_statedGU (h := h) hq]
    exact Subgroup.mem_map_of_mem _ g.2
  let ψ₀ : stdHermIsom h n →* StatedGU n q L :=
    { toFun := fun g => ⟨matrixEquiv g.1, hmem g⟩
      map_one' := Subtype.ext (map_one matrixEquiv)
      map_mul' := fun g g' => Subtype.ext (map_mul matrixEquiv g.1 g'.1) }
  refine ⟨ψ₀.comp e₁.toMonoidHom, fun g g' hgg => e₁.injective (Subtype.ext ?_), fun g => ?_⟩
  · exact matrixEquiv.injective (congrArg Subtype.val hgg)
  ·
    have hconj : (e₁ g).1.toLinearMap =
        e.equivFun.toLinearMap.comp (g.1.toLinearMap.comp e.equivFun.symm.toLinearMap) :=
      LinearMap.ext fun x => formIsometryGroupCongr_apply e.equivFun _ g x
    show ((matrixEquiv (e₁ g).1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det = _
    rw [matrixEquiv_val, LinearMap.det_toMatrix', hconj, LinearMap.det_conj]

variable (h) in
include h in
theorem det_pow_card_add_one_of_mem_statedGU {q : ℕ} (hq : q = p₀ ^ f) {n : ℕ}
    {g : GL (Fin n) L} (hg : g ∈ StatedGU n q L) :
    ((g : Matrix (Fin n) (Fin n) L).det) ^ (q + 1) = 1 :=
  gu_det_pow_of_unitary h hq _ (gu_unitary_of_mem_statedGU h hq hg)

variable (h) in
include h in
theorem mem_statedSU_of_mem_statedGU {q : ℕ} (hq : q = p₀ ^ f) {n : ℕ} {g : GL (Fin n) L}
    (hg : g ∈ StatedGU n q L) (hdet : (g : Matrix (Fin n) (Fin n) L).det = 1) :
    g ∈ StatedSU n q L := by
  have hU := gu_unitary_of_mem_statedGU h hq hg
  unfold StatedSU
  exact Subgroup.subset_closure ⟨hdet, hU⟩

theorem statedSU_le_statedGU {q n : ℕ} : StatedSU n q L ≤ StatedGU n q L := by
  unfold StatedSU StatedGU
  exact (Subgroup.closure_le _).2 fun A hA => Subgroup.subset_closure hA.2

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

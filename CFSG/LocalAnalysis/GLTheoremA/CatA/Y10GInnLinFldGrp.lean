module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangU64
public import CFSG.Adapters.StatedSLPerfect
public import CFSG.Models.PGLSimple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld

open CFSG.Open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.HeldLang
open scoped commutatorElement

variable {K : Type} [Field K]

theorem hom_eq_one_of_perfect {G A : Type*} [Group G] [Group.IsPerfect G] [CommGroup A]
    (φ : G →* A) (g : G) : φ g = 1 := by
  have hcomm : commutator G ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have htop : commutator G = ⊤ := Group.isPerfect_def.1 inferInstance
  have hg : g ∈ commutator G := by
    rw [htop]
    exact Subgroup.mem_top g
  exact MonoidHom.mem_ker.1 (hcomm hg)

@[expose] noncomputable def quotientCongrSubgroup {G : Type*} [Group G] {H H' : Subgroup G} (hH : H = H')
    {Z Z' : Subgroup G} [Z.Normal] [Z'.Normal] (hZ : Z = Z') :
    ↥H ⧸ Z.subgroupOf H ≃* ↥H' ⧸ Z'.subgroupOf H' := by
  subst hH
  subst hZ
  exact MulEquiv.refl _

theorem center_eq_largeEvenScalars (d : ℕ) :
    Subgroup.center (GL (Fin d) K) = LargeEvenScalars (Fin d) K := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  rfl

@[expose] noncomputable def pslEquivLarge (d : ℕ) :
    PSL (Fin d) K ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K) :=
  quotientCongrSubgroup (H := slGL (Fin d) K) (H' := LargeEvenSLGroup (Fin d) K) rfl
    (center_eq_largeEvenScalars d)

theorem quotientCongrSubgroup_mk {G : Type*} [Group G] {H H' : Subgroup G} (hH : H = H')
    {Z Z' : Subgroup G} [Z.Normal] [Z'.Normal] (hZ : Z = Z') (x : ↥H) :
    quotientCongrSubgroup hH hZ (QuotientGroup.mk x) = QuotientGroup.mk ⟨x.1, hH ▸ x.2⟩ := by
  subst hH
  subst hZ
  rfl

theorem pslEquivLarge_mk {d : ℕ} (g : ↥(slGL (Fin d) K)) :
    pslEquivLarge d (QuotientGroup.mk g) = QuotientGroup.mk ⟨g.1, g.2⟩ :=
  quotientCongrSubgroup_mk rfl (center_eq_largeEvenScalars d) g

theorem nonempty_psl_equiv_statedProj (d : ℕ) (F : Type) [Field F] :
    Nonempty (PSL (Fin d) F ≃* StatedProj (StatedSL d F)) := by
  have hH : slGL (Fin d) F = StatedSL d F := (CFSG.Open.StatedAPI.statedSL_eq_ker_det d F).symm
  have hZ : Subgroup.center (GL (Fin d) F) = StatedScalars (Fin d) F := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    rfl
  exact ⟨quotientCongrSubgroup hH hZ⟩

theorem isSimpleGroup_statedProj_of_three_le {d : ℕ} (hd : 3 ≤ d) (F : Type) [Field F] :
    IsSimpleGroup (StatedProj (StatedSL d F)) :=
  CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL F (by omega) (Or.inl (by omega))
    (Or.inl (by omega))

theorem isPerfect_statedProj_of_three_le {d : ℕ} (hd : 3 ≤ d) (F : Type) [Field F] :
    Group.IsPerfect (StatedProj (StatedSL d F)) := by
  haveI : Group.IsPerfect (StatedSL d F) := CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le hd F
  exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)

theorem nonempty_quotCenter_equiv {X Q : Type*} [Group X] [Group Q] [IsSimpleGroup X] [Group.IsPerfect X]
    (e : X ≃* Q) : Nonempty (X ⧸ Subgroup.center X ≃* Q) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple_perfect (inferInstance : Group.IsPerfect X))).trans
    (QuotientGroup.quotientBot.trans e)⟩

theorem scalar_eq_of_mul_eq {d : ℕ} (i : Fin d) {a b : Kˣ} {g : GL (Fin d) K}
    (h : Matrix.GeneralLinearGroup.scalar (Fin d) a * g = Matrix.GeneralLinearGroup.scalar (Fin d) b * g) :
    a = b := by
  have h' : Matrix.GeneralLinearGroup.scalar (Fin d) a = Matrix.GeneralLinearGroup.scalar (Fin d) b :=
    mul_right_cancel h
  apply Units.ext
  have h0 := congrArg (fun z : GL (Fin d) K => ((z : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i) h'
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply] using h0

theorem scalar_mul_mul_scalar_mul {d : ℕ} (s t : Kˣ) (g k : GL (Fin d) K) :
    (Matrix.GeneralLinearGroup.scalar (Fin d) s * g) * (Matrix.GeneralLinearGroup.scalar (Fin d) t * k) =
      (Matrix.GeneralLinearGroup.scalar (Fin d) s * Matrix.GeneralLinearGroup.scalar (Fin d) t) * (g * k) := by
  calc (Matrix.GeneralLinearGroup.scalar (Fin d) s * g) * (Matrix.GeneralLinearGroup.scalar (Fin d) t * k)
      = Matrix.GeneralLinearGroup.scalar (Fin d) s * (g * Matrix.GeneralLinearGroup.scalar (Fin d) t) * k := by
        group
    _ = Matrix.GeneralLinearGroup.scalar (Fin d) s * (Matrix.GeneralLinearGroup.scalar (Fin d) t * g) * k := by
        rw [scalar_mul_comm t g]
    _ = (Matrix.GeneralLinearGroup.scalar (Fin d) s * Matrix.GeneralLinearGroup.scalar (Fin d) t) * (g * k) := by
        group

theorem exists_scalar_of_conj_mod_scalar {d : ℕ} (hd : 3 ≤ d) (N : GL (Fin d) K)
    (h : ∀ x ∈ slGL (Fin d) K, ∃ c : Kˣ, N * x * N⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) c * x) :
    ∃ c : Kˣ, N = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
  classical
  have i0 : Fin d := ⟨0, by omega⟩
  choose! ψ hψ using h
  have hmul : ∀ x ∈ slGL (Fin d) K, ∀ y ∈ slGL (Fin d) K, ψ (x * y) = ψ x * ψ y := by
    intro x hx y hy
    have hxy : x * y ∈ slGL (Fin d) K := (slGL (Fin d) K).mul_mem hx hy
    apply scalar_eq_of_mul_eq i0 (g := x * y)
    rw [← hψ _ hxy]
    calc N * (x * y) * N⁻¹ = (N * x * N⁻¹) * (N * y * N⁻¹) := by group
      _ = (Matrix.GeneralLinearGroup.scalar (Fin d) (ψ x) * x) *
            (Matrix.GeneralLinearGroup.scalar (Fin d) (ψ y) * y) := by
          rw [hψ x hx, hψ y hy]
      _ = (Matrix.GeneralLinearGroup.scalar (Fin d) (ψ x) * Matrix.GeneralLinearGroup.scalar (Fin d) (ψ y)) *
            (x * y) := scalar_mul_mul_scalar_mul _ _ _ _
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) (ψ x * ψ y) * (x * y) := by rw [map_mul]
  let Φ : slGL (Fin d) K →* Kˣ :=
    MonoidHom.mk' (fun x => ψ x) (fun x y => hmul x x.2 y y.2)
  haveI hperf : Group.IsPerfect ↥(slGL (Fin d) K) := by
    haveI : Group.IsPerfect ↥(StatedSL d K) := CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le hd K
    have hS : slGL (Fin d) K = StatedSL d K := (CFSG.Open.StatedAPI.statedSL_eq_ker_det d K).symm
    exact Group.IsPerfect.ofSurjective (f := (MulEquiv.subgroupCongr hS).symm.toMonoidHom)
      (MulEquiv.subgroupCongr hS).symm.surjective
  refine exists_scalar_of_commute_slGL N (fun x hx => ?_)
  have h1 : ψ x = 1 := hom_eq_one_of_perfect Φ ⟨x, hx⟩
  have h2 := hψ x hx
  rw [h1, map_one, one_mul] at h2
  exact h2

theorem mk_eq_scalar {d : ℕ} (x y : ↥(slGL (Fin d) K))
    (h : LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x = LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) y) :
    ∃ c : Kˣ, (y : GL (Fin d) K) = Matrix.GeneralLinearGroup.scalar (Fin d) c * (x : GL (Fin d) K) := by
  have h1 := QuotientGroup.eq.1 h
  rw [Subgroup.mem_subgroupOf] at h1
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 h1
  refine ⟨c, ?_⟩
  have hc' : Matrix.GeneralLinearGroup.scalar (Fin d) c = (x : GL (Fin d) K)⁻¹ * (y : GL (Fin d) K) := hc
  calc (y : GL (Fin d) K) = (x : GL (Fin d) K) * ((x : GL (Fin d) K)⁻¹ * (y : GL (Fin d) K)) := by group
    _ = (x : GL (Fin d) K) * Matrix.GeneralLinearGroup.scalar (Fin d) c := by rw [hc']
    _ = Matrix.GeneralLinearGroup.scalar (Fin d) c * (x : GL (Fin d) K) := (scalar_mul_comm c _).symm

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld

end

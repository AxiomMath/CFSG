module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthFamWitt
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorBridge
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7Rank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCOrthComm
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.Open

@[expose] def SigmaEquivariant {K : Type} [Field K] {d : ℕ} (σ : K ≃+* K)
    (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) : Prop :=
  ∀ v, g (coordinateFieldMap d σ v) = coordinateFieldMap d σ (g v)

section Descent

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

noncomputable def descentIncl (hext : IsExtension k Q₀ Q) : ↥(orthDerived Q₀) →* ↥(orthDerived Q) :=
  (matrixDerivedEquiv Q).toMonoidHom.comp
    ((inclHom k hext).comp (matrixDerivedEquiv Q₀).symm.toMonoidHom)

theorem descentIncl_injective (hext : IsExtension k Q₀ Q) : Function.Injective (descentIncl hext) := by
  have hincl : Function.Injective (inclHom k hext) := by
    intro x y hxy
    have hgl : glIncl k (x : GL (Fin d) k) = glIncl k (y : GL (Fin d) k) := by
      have h := congrArg Subtype.val hxy
      simpa only [inclHom_val] using h
    have hmat : (x : GL (Fin d) k).val = (y : GL (Fin d) k).val :=
      Matrix.map_injective (f := k.subtype) k.subtype_injective
        (by simpa only [glIncl_val] using congrArg (fun A : GL (Fin d) K => A.val) hgl)
    exact Subtype.ext (Units.ext hmat)
  intro a b hab
  change matrixDerivedEquiv Q (inclHom k hext ((matrixDerivedEquiv Q₀).symm a)) =
    matrixDerivedEquiv Q (inclHom k hext ((matrixDerivedEquiv Q₀).symm b)) at hab
  exact (matrixDerivedEquiv Q₀).symm.injective (hincl ((matrixDerivedEquiv Q).injective hab))

theorem descentIncl_equivariant (hσk : ∀ x, x ∈ k ↔ σ x = x) (hext : IsExtension k Q₀ Q)
    (a₀ : ↥(orthDerived Q₀)) :
    SigmaEquivariant σ ((descentIncl hext a₀ : ↥(orthDerived Q)) : (Fin d → K) ≃ₗ[K] (Fin d → K)) := by
  intro v
  set x : matrixDerived Q₀ := (matrixDerivedEquiv Q₀).symm a₀ with hx
  have hd : ((descentIncl hext a₀ : ↥(orthDerived Q)) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
      matrixLinearEquiv (glIncl k (x : GL (Fin d) k)) := by
    have h : descentIncl hext a₀ = matrixDerivedEquiv Q (inclHom k hext x) := by
      change matrixDerivedEquiv Q (inclHom k hext ((matrixDerivedEquiv Q₀).symm a₀)) =
        matrixDerivedEquiv Q (inclHom k hext x)
      rw [← hx]
    rw [h, coe_matrixDerivedEquiv, inclHom_val]
  rw [hd]
  have key := coordinateFieldMap_matrix (d := d) σ (glIncl k (x : GL (Fin d) k)) v
  rw [glFieldAut_glIncl k hσk] at key
  exact key.symm

private theorem i167COrth_descent_rat_aux1 (k : Subfield K) {d : ℕ} :
    Function.Injective (glIncl (d := d) k) := by
  intro A B hAB
  refine Units.ext (Matrix.map_injective (f := k.subtype) k.subtype_injective ?_)
  simpa only [glIncl_val] using congrArg (fun u : GL (Fin d) K => u.val) hAB

private theorem i167COrth_descent_rat_aux2 {σ : K ≃+* K} {g : GL (Fin d) K}
    (hg : ∀ v, matrixLinearEquiv g (coordinateFieldMap d σ v) =
      coordinateFieldMap d σ (matrixLinearEquiv g v)) :
    CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin d) K σ g = g := by
  let G : GL (Fin d) K →* GL (Fin d) K :=
    CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin d) K σ
  change G g = g
  have h1 : ∀ v, matrixLinearEquiv g (coordinateFieldMap d σ v) =
      matrixLinearEquiv (G g) (coordinateFieldMap d σ v) := fun v => by
    show matrixLinearEquiv g (coordinateFieldMap d σ v) =
      matrixLinearEquiv (CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin d) K σ g)
        (coordinateFieldMap d σ v)
    exact (hg v).trans (coordinateFieldMap_matrix σ g v)
  have h2 : matrixLinearEquiv g = matrixLinearEquiv (G g) :=
    LinearEquiv.ext fun w => by
      obtain ⟨v, rfl⟩ := (coordinateFieldMap d σ).surjective w
      exact h1 v
  exact (Units.ext (Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← matrixLinearEquiv_apply, ← matrixLinearEquiv_apply]
    exact congrArg (fun e : (Fin d → K) ≃ₗ[K] (Fin d → K) => e v) h2)).symm

theorem i167COrth_descent_rat (SS : SubfieldSetup k Q₀ Q σ p) {a : ↥(orthDerived Q)}
    (ha : SigmaEquivariant σ (a : (Fin d → K) ≃ₗ[K] (Fin d → K))) (hap : a ^ p = 1) :
    ∃ a₀ : ↥(orthDerived Q₀), descentIncl SS.hext a₀ = a := by
  classical
  let y : matrixDerived Q := (matrixDerivedEquiv Q).symm a
  have hya : matrixDerivedEquiv Q y = a := MulEquiv.apply_symm_apply _ _
  have hacoe : (a : (Fin d → K) ≃ₗ[K] (Fin d → K)) = matrixLinearEquiv y.1 := by
    simpa [hya] using coe_matrixDerivedEquiv Q y
  have hfix : CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin d) K σ y.1 = y.1 :=
    i167COrth_descent_rat_aux2 fun v => by simpa [hacoe] using ha v
  obtain ⟨x, hx⟩ := exists_glIncl_of_fixed k SS.hσk hfix
  have hiso : x ∈ matrixIsometries Q₀ :=
    mem_isometries_of_glIncl k SS.hext (hx ▸ matrixDerived_le_isometries Q y.2)
  have hy_pow : y ^ p = 1 := by
    apply (matrixDerivedEquiv Q).injective
    rw [map_pow, hya, hap, map_one]
  have hxp : x ^ p = 1 := by
    apply i167COrth_descent_rat_aux1 k
    rw [map_pow, hx]
    have := congrArg (fun z : matrixDerived Q => (z : GL (Fin d) K)) hy_pow
    simpa using this
  have hx2 : x * x ∈ matrixDerived Q₀ := sq_mem_matrixDerived k SS.hnd₀ SS.hT₀ hiso
  have hxmem : x ∈ matrixDerived Q₀ := by
    have hxeq : x = (x * x) ^ ((p + 1) / 2) := by
      obtain ⟨m, hm⟩ := SS.odd
      have hp1 : (p + 1) / 2 = m + 1 := by omega
      rw [hp1, ← pow_two, ← pow_mul, show 2 * (m + 1) = p + 1 by omega, pow_succ, hxp, one_mul]
    rw [hxeq]
    exact pow_mem hx2 _
  refine ⟨matrixDerivedEquiv Q₀ ⟨x, hxmem⟩, ?_⟩
  have hz : inclHom k SS.hext ⟨x, hxmem⟩ = y := by
    apply Subtype.ext
    simpa only [inclHom_val] using hx
  rw [show descentIncl SS.hext (matrixDerivedEquiv Q₀ ⟨x, hxmem⟩) =
      matrixDerivedEquiv Q (inclHom k SS.hext ((matrixDerivedEquiv Q₀).symm
        (matrixDerivedEquiv Q₀ ⟨x, hxmem⟩))) from rfl,
    MulEquiv.symm_apply_apply, hz, hya]

private theorem i167COrth_descent_fixed_finrank_aux1 {F : Type} [Field F] {d : ℕ}
    (A : GL (Fin d) F) :
    Module.finrank F (fixedSpace (matrixLinearEquiv A)) + (A.val - 1).rank = d := by
  have hto : (matrixLinearEquiv A).toLinearMap - 1 = (A.val - 1).mulVecLin := by
    ext v
    simp [matrixLinearEquiv_apply, Matrix.sub_mulVec]
  have hfs : fixedSpace (matrixLinearEquiv A) = LinearMap.ker ((A.val - 1).mulVecLin) := by
    rw [fixedSpace, hto]
  rw [hfs]
  have hrn := LinearMap.finrank_range_add_finrank_ker ((A.val - 1).mulVecLin)
  have hrank : (A.val - 1).rank = Module.finrank F (LinearMap.range (A.val - 1).mulVecLin) :=
    rfl
  rw [Module.finrank_fin_fun] at hrn
  omega

theorem i167COrth_descent_fixed_finrank (hext : IsExtension k Q₀ Q) (a₀ : ↥(orthDerived Q₀)) :
    Module.finrank K
        (fixedSpace ((descentIncl hext a₀ : ↥(orthDerived Q)) : (Fin d → K) ≃ₗ[K] (Fin d → K))) =
      Module.finrank k (fixedSpace (a₀ : (Fin d → k) ≃ₗ[k] (Fin d → k))) := by
  set x : matrixDerived Q₀ := (matrixDerivedEquiv Q₀).symm a₀ with hx
  have hdesc : ((descentIncl hext a₀ : ↥(orthDerived Q)) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
      matrixLinearEquiv (glIncl k (x : GL (Fin d) k)) := by
    have h : descentIncl hext a₀ = matrixDerivedEquiv Q (inclHom k hext x) := by
      change matrixDerivedEquiv Q (inclHom k hext ((matrixDerivedEquiv Q₀).symm a₀)) =
        matrixDerivedEquiv Q (inclHom k hext x)
      rw [← hx]
    rw [h, coe_matrixDerivedEquiv, inclHom_val]
  have ha₀ : (a₀ : (Fin d → k) ≃ₗ[k] (Fin d → k)) = matrixLinearEquiv (x : GL (Fin d) k) := by
    have h : matrixDerivedEquiv Q₀ x = a₀ := by rw [hx, MulEquiv.apply_symm_apply]
    rw [← h, coe_matrixDerivedEquiv]
  rw [hdesc, ha₀]
  have hK := i167COrth_descent_fixed_finrank_aux1 (glIncl k (x : GL (Fin d) k))
  have hk := i167COrth_descent_fixed_finrank_aux1 (x : GL (Fin d) k)
  have hrank : ((glIncl k (x : GL (Fin d) k)).val - 1).rank =
      ((x : GL (Fin d) k).val - 1).rank := by
    have hmap : (glIncl k (x : GL (Fin d) k)).val - 1 =
        ((x : GL (Fin d) k).val - 1).map k.subtype := by
      rw [glIncl_val, Matrix.map_sub k.subtype (fun a b => RingHom.map_sub k.subtype a b),
        Matrix.map_one k.subtype (map_zero k.subtype) (map_one k.subtype)]
    rw [hmap]
    exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.rank_map_field k.subtype _
  omega

private theorem i167COrth_descent_fixed_trivial_aux1 {k : Type} [Field k] {d : ℕ}
    {M N : Matrix (Fin d) (Fin d) k}
    (h : LinearMap.ker M.mulVecLin ≤ LinearMap.ker N.mulVecLin) :
    ∃ R : Matrix (Fin d) (Fin d) k, N = R * M := by
  classical
  set φ : LinearMap.range M.mulVecLin →ₗ[k] (Fin d → k) :=
    (Submodule.liftQ (LinearMap.ker M.mulVecLin) N.mulVecLin h).comp
      M.mulVecLin.quotKerEquivRange.symm.toLinearMap with hφ
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend φ
  refine ⟨LinearMap.toMatrix' ψ, ?_⟩
  have hcomp : N.mulVecLin = ψ.comp M.mulVecLin := by
    apply LinearMap.ext
    intro v
    have hv : M.mulVecLin v ∈ LinearMap.range M.mulVecLin := ⟨v, rfl⟩
    have h1 : ψ (M.mulVecLin v) = φ ⟨M.mulVecLin v, hv⟩ := by
      have := congrArg (fun F : LinearMap.range M.mulVecLin →ₗ[k] (Fin d → k) =>
        F ⟨M.mulVecLin v, hv⟩) hψ
      simpa [LinearMap.comp_apply] using this
    rw [LinearMap.comp_apply, h1]
    rw [hφ, LinearMap.comp_apply]
    rw [LinearEquiv.coe_toLinearMap, LinearMap.quotKerEquivRange_symm_apply_image,
      Submodule.mkQ_apply, Submodule.liftQ_apply]
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_apply',
    Matrix.toLin'_apply']
  exact hcomp

private theorem i167COrth_descent_fixed_trivial_aux2 (hext : IsExtension k Q₀ Q)
    (x : matrixDerived Q₀) :
    ((descentIncl hext (matrixDerivedEquiv Q₀ x) : ↥(orthDerived Q)) :
        (Fin d → K) ≃ₗ[K] (Fin d → K)) = matrixLinearEquiv (glIncl k x.1) := by
  unfold descentIncl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
    coe_matrixDerivedEquiv, inclHom_val]

private theorem i167COrth_descent_fixed_trivial_aux3 {k L : Type} [Field k] [Field L] {d : ℕ}
    (f : k →+* L) (A : Matrix (Fin d) (Fin d) k) : (A - 1).map f = A.map f - 1 := by
  ext i j
  simp [Matrix.map_apply, Matrix.one_apply]

private theorem i167COrth_descent_fixed_trivial_aux4 (a b : (Fin d → k) ≃ₗ[k] (Fin d → k))
    (A B : GL (Fin d) k) (ha : a = matrixLinearEquiv A) (hb : b = matrixLinearEquiv B)
    (h : ∀ w ∈ fixedSpace a, b w = w) :
    LinearMap.ker (A.val - 1).mulVecLin ≤ LinearMap.ker (B.val - 1).mulVecLin := by
  intro v hv
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  have hA0 : a v = v ↔ Matrix.mulVec (A.val - 1) v = 0 := by
    rw [ha, matrixLinearEquiv_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  have hB0 : b v = v ↔ Matrix.mulVec (B.val - 1) v = 0 := by
    rw [hb, matrixLinearEquiv_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  exact hB0.mp (h v (by rw [mem_fixedSpace]; exact hA0.mpr hv))

theorem i167COrth_descent_fixed_trivial (hext : IsExtension k Q₀ Q) (a₀ b₀ : ↥(orthDerived Q₀))
    (h : ∀ w ∈ fixedSpace (a₀ : (Fin d → k) ≃ₗ[k] (Fin d → k)),
      (b₀ : (Fin d → k) ≃ₗ[k] (Fin d → k)) w = w) :
    ∀ w ∈ fixedSpace ((descentIncl hext a₀ : ↥(orthDerived Q)) : (Fin d → K) ≃ₗ[K] (Fin d → K)),
      ((descentIncl hext b₀ : ↥(orthDerived Q)) : (Fin d → K) ≃ₗ[K] (Fin d → K)) w = w := by
  classical
  set x : matrixDerived Q₀ := (matrixDerivedEquiv Q₀).symm a₀ with hx
  set y : matrixDerived Q₀ := (matrixDerivedEquiv Q₀).symm b₀ with hy
  have hxa : matrixDerivedEquiv Q₀ x = a₀ := by rw [hx, MulEquiv.apply_symm_apply]
  have hyb : matrixDerivedEquiv Q₀ y = b₀ := by rw [hy, MulEquiv.apply_symm_apply]
  have hA : (a₀ : (Fin d → k) ≃ₗ[k] (Fin d → k)) = matrixLinearEquiv x.1 := by
    rw [← hxa, coe_matrixDerivedEquiv]
  have hB : (b₀ : (Fin d → k) ≃ₗ[k] (Fin d → k)) = matrixLinearEquiv y.1 := by
    rw [← hyb, coe_matrixDerivedEquiv]
  have hA' : ((descentIncl hext a₀ : ↥(orthDerived Q)) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
      matrixLinearEquiv (glIncl k x.1) := by
    rw [← hxa]
    exact i167COrth_descent_fixed_trivial_aux2 hext x
  have hB' : ((descentIncl hext b₀ : ↥(orthDerived Q)) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
      matrixLinearEquiv (glIncl k y.1) := by
    rw [← hyb]
    exact i167COrth_descent_fixed_trivial_aux2 hext y
  have hker : LinearMap.ker (x.1.val - 1).mulVecLin ≤
      LinearMap.ker (y.1.val - 1).mulVecLin :=
    i167COrth_descent_fixed_trivial_aux4 (a₀ : (Fin d → k) ≃ₗ[k] (Fin d → k))
      (b₀ : (Fin d → k) ≃ₗ[k] (Fin d → k)) x.1 y.1 hA hB h
  obtain ⟨R, hR⟩ := i167COrth_descent_fixed_trivial_aux1 hker
  have hRmap : (y.1.val - 1).map k.subtype =
      R.map k.subtype * (x.1.val - 1).map k.subtype := by
    rw [hR, Matrix.map_mul]
  intro w hw
  have hw' : Matrix.mulVec (x.1.val.map k.subtype) w = w := by
    rw [mem_fixedSpace, hA', matrixLinearEquiv_apply, glIncl_val] at hw
    exact hw
  have hxw : Matrix.mulVec ((x.1.val - 1).map k.subtype) w = 0 := by
    rw [i167COrth_descent_fixed_trivial_aux3 k.subtype x.1.val, Matrix.sub_mulVec,
      Matrix.one_mulVec, hw', sub_self]
  have hyw : Matrix.mulVec ((y.1.val - 1).map k.subtype) w = 0 := by
    rw [hRmap, ← Matrix.mulVec_mulVec, hxw, Matrix.mulVec_zero]
  rw [← hyb, i167COrth_descent_fixed_trivial_aux2 hext y, matrixLinearEquiv_apply, glIncl_val]
  rw [i167COrth_descent_fixed_trivial_aux3 k.subtype y.1.val, Matrix.sub_mulVec,
    Matrix.one_mulVec, sub_eq_zero] at hyw
  exact hyw

private theorem i167COrth_descent_dim_aux1 (SS : SubfieldSetup k Q₀ Q σ p)
    {A : Subgroup ↥(orthDerived Q)} (hA : IsElemAbelian p A)
    (hrat : ∀ a ∈ A, SigmaEquivariant σ (a : (Fin d → K) ≃ₗ[K] (Fin d → K)))
    (hmax : ∀ s : ↥(orthDerived Q), SigmaEquivariant σ (s : (Fin d → K) ≃ₗ[K] (Fin d → K)) →
      s ^ p = 1 → (∀ a ∈ A, a * s = s * a) → s ∈ A) :
    IsElemAbelian p (A.comap (descentIncl SS.hext)) ∧
      (∀ E : Subgroup ↥(orthDerived Q₀), IsElemAbelian p E →
        A.comap (descentIncl SS.hext) ≤ E → E = A.comap (descentIncl SS.hext)) := by
  classical
  have hιinj : Function.Injective (descentIncl SS.hext) := descentIncl_injective SS.hext
  have hA₀ : IsElemAbelian p (A.comap (descentIncl SS.hext)) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hιinj ?_)⟩⟩, fun x hx => hιinj ?_⟩
    · show descentIncl SS.hext (a.1 * b.1) = descentIncl SS.hext (b.1 * a.1)
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hA.1.is_comm.comm
        ⟨descentIncl SS.hext a.1, Subgroup.mem_comap.mp a.2⟩
        ⟨descentIncl SS.hext b.1, Subgroup.mem_comap.mp b.2⟩)
    · show descentIncl SS.hext (x ^ p) = descentIncl SS.hext 1
      rw [map_pow, hA.2 (descentIncl SS.hext x) (Subgroup.mem_comap.mp hx), map_one]
  refine ⟨hA₀, fun E hE hA₀E => le_antisymm (fun s hs => ?_) hA₀E⟩
  have hsι : descentIncl SS.hext s ∈ A := by
    refine hmax (descentIncl SS.hext s) (descentIncl_equivariant SS.hσk SS.hext s) ?_ ?_
    · rw [← map_pow, hE.2 s hs, map_one]
    · intro a ha
      obtain ⟨a₀', ha₀'⟩ := i167COrth_descent_rat SS (hrat a ha) (hA.2 a ha)
      have ha₀'A : a₀' ∈ A.comap (descentIncl SS.hext) := by
        rw [Subgroup.mem_comap, ha₀']; exact ha
      have hcommE : a₀' * s = s * a₀' :=
        congrArg Subtype.val (hE.1.is_comm.comm ⟨a₀', hA₀E ha₀'A⟩ ⟨s, hs⟩)
      have h1 := congrArg (descentIncl SS.hext) hcommE
      rw [map_mul, map_mul] at h1
      rw [← ha₀']; exact h1
  exact Subgroup.mem_comap.mpr hsι

private theorem i167COrth_descent_dim_aux2 (SS : SubfieldSetup k Q₀ Q σ p)
    {A : Subgroup ↥(orthDerived Q)} {g : ↥(orthDerived Q)}
    {g₀ : ↥(orthDerived Q₀)} (hg₀ : descentIncl SS.hext g₀ = g)
    (hCA : ∀ a ∈ A, (∀ w ∈ fixedSpace (g : (Fin d → K) ≃ₗ[K] (Fin d → K)),
      (a : (Fin d → K) ≃ₗ[K] (Fin d → K)) w = w) → a ∈ Subgroup.zpowers g) :
    ∀ a₀ ∈ A.comap (descentIncl SS.hext),
      (∀ w ∈ fixedSpace (g₀ : (Fin d → k) ≃ₗ[k] (Fin d → k)),
        (a₀ : (Fin d → k) ≃ₗ[k] (Fin d → k)) w = w) → a₀ ∈ Subgroup.zpowers g₀ := by
  have hιinj : Function.Injective (descentIncl SS.hext) := descentIncl_injective SS.hext
  intro a₀ ha₀ hfix
  have hfixK : ∀ w ∈ fixedSpace (g : (Fin d → K) ≃ₗ[K] (Fin d → K)),
      (descentIncl SS.hext a₀ : (Fin d → K) ≃ₗ[K] (Fin d → K)) w = w := by
    have h := i167COrth_descent_fixed_trivial SS.hext g₀ a₀ hfix
    rwa [hg₀] at h
  have hmem : descentIncl SS.hext a₀ ∈
      Subgroup.map (descentIncl SS.hext) (Subgroup.zpowers g₀) := by
    rw [MonoidHom.map_zpowers (descentIncl SS.hext) g₀, hg₀]
    exact hCA (descentIncl SS.hext a₀) (Subgroup.mem_comap.mp ha₀) hfixK
  obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp hmem
  simpa [hιinj hbeq] using hb
theorem i167COrth_descent_dim (SS : SubfieldSetup k Q₀ Q σ p) {N : ℕ} (hd : d = 2 * N) (hN : 4 ≤ N)
    (hpk : p ∣ Nat.card k + 1) {A : Subgroup ↥(orthDerived Q)} (hA : IsElemAbelian p A)
    (hrat : ∀ a ∈ A, SigmaEquivariant σ (a : (Fin d → K) ≃ₗ[K] (Fin d → K)))
    (hmax : ∀ s : ↥(orthDerived Q), SigmaEquivariant σ (s : (Fin d → K) ≃ₗ[K] (Fin d → K)) →
      s ^ p = 1 → (∀ a ∈ A, a * s = s * a) → s ∈ A)
    {g : ↥(orthDerived Q)} (hgA : g ∈ A) (hg : orderOf g = p)
    (hCA : ∀ a ∈ A, (∀ w ∈ fixedSpace (g : (Fin d → K) ≃ₗ[K] (Fin d → K)),
      (a : (Fin d → K) ≃ₗ[K] (Fin d → K)) w = w) → a ∈ Subgroup.zpowers g) :
    Module.finrank K (Fin d → K) =
      Module.finrank K (fixedSpace (g : (Fin d → K) ≃ₗ[K] (Fin d → K))) + 2 := by
  classical
  have hιinj : Function.Injective (descentIncl SS.hext) := descentIncl_injective SS.hext
  have hgpow : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  obtain ⟨g₀, hg₀⟩ := i167COrth_descent_rat SS (hrat g hgA) hgpow
  have hord₀ : orderOf g₀ = p := by
    have h := orderOf_injective (descentIncl SS.hext) hιinj g₀
    rw [hg₀, hg] at h
    exact h.symm
  have hg₀A : g₀ ∈ A.comap (descentIncl SS.hext) := by
    rw [Subgroup.mem_comap, hg₀]; exact hgA
  obtain ⟨hA₀, hmax₀⟩ := i167COrth_descent_dim_aux1 SS hA hrat hmax
  have hCA₀ := i167COrth_descent_dim_aux2 SS (g := g) (g₀ := g₀) hg₀ hCA
  have hwitt := i167COrth_witt_triv (F := k) (V := Fin d → k) (Q := Q₀) (p := p) (m := N)
    SS.hnd₀ SS.hp SS.hp2 hpk (by rw [Module.finrank_fin_fun, hd]) hN hA₀ hmax₀ hg₀A hord₀ hCA₀
  have hfin : Module.finrank K (fixedSpace (g : (Fin d → K) ≃ₗ[K] (Fin d → K))) =
      Module.finrank k (fixedSpace (g₀ : (Fin d → k) ≃ₗ[k] (Fin d → k))) := by
    have h := i167COrth_descent_fixed_finrank SS.hext g₀
    rwa [hg₀] at h
  rw [Module.finrank_fin_fun, hfin, ← hwitt.1, Module.finrank_fin_fun]

end Descent

end CFSG.LocalAnalysis.GLTheoremA.I167

end

module

public import CFSG.CGT.Harada80.OmegaCodes
public import CFSG.CGT.Harada80.Setting
public import CFSG.ClassicalGroups.Orthogonal.ReflectPairs
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.LieType.Universal.Spin.Forms

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Harada80

open CFSG.ClassicalGroups.Orthogonal
open CFSG.Quasithin.SteinbergCB.G2Two
open CFSG.RankThree.PartTwo
open Matrix
open scoped commutatorElement

noncomputable abbrev quadQ (m : ℕ) :
    QuadraticForm (ZMod 2) (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) :=
  CFSG.LieType.Universal.Spin.quadMinus (m + 1) (ZMod 2) 1 1

theorem coe_quadQ (m : ℕ) : ⇑(quadQ m) = CFSG.PGLModel.minusQuadForm m (1 : ZMod 2) 1 := by
  funext v
  show CFSG.LieType.Universal.Spin.quadMinus (m + 1) (ZMod 2) 1 1 v =
    CFSG.PGLModel.minusQuadForm m (1 : ZMod 2) 1 v
  rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
  rfl

theorem nondegenerate_quadQ (m : ℕ) :
    (QuadraticMap.polarBilin (quadQ m)).Nondegenerate :=
  CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (m + 1) (ZMod 2)
    (by decide)

theorem polar_vec (m x u : ℕ) :
    QuadraticMap.polar (quadQ m) (vec m x) (vec m u) = polarCode m x u := by
  simp only [QuadraticMap.polar, polarCode, coe_quadQ]

theorem reflect_vec {m u : ℕ}
    (hu : CFSG.PGLModel.minusQuadForm m (1 : ZMod 2) 1 (vec m u) ≠ 0) (x : ℕ) :
    reflect (quadQ m) (vec m u) (vec m x) = vec m (reflCode m u x) := by
  have hu1 : quadQ m (vec m u) = 1 := by
    apply CFSG.ClassicalGroups.Orthogonal.zmod_two_eq_one_of_ne_zero
    rwa [coe_quadQ]
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_map_eq_one hu1, polar_vec,
    ← vec_reflCode]

noncomputable def reflProd (m : ℕ) (cs : List ℕ) :
    (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) :=
  (cs.map fun c => reflect (quadQ m) (vec m c)).prod

theorem reflProd_mem (m : ℕ) (cs : List ℕ) :
    reflProd m cs ∈ TauCeti.QuadraticMap.orthogonalGroup (quadQ m) := by
  induction cs with
  | nil => exact Subgroup.one_mem _
  | cons c cs ih =>
    rw [reflProd, List.map_cons, List.prod_cons]
    exact Subgroup.mul_mem _ (reflect_mem_orthogonalGroup (quadQ m) (vec m c)) ih

theorem reflProd_vec {m : ℕ} {cs : List ℕ}
    (hcs : ∀ c ∈ cs, CFSG.PGLModel.minusQuadForm m (1 : ZMod 2) 1 (vec m c) ≠ 0) (x : ℕ) :
    reflProd m cs (vec m x) = vec m (reflChain m cs x) := by
  induction cs generalizing x with
  | nil => rfl
  | cons c cs ih =>
    show (reflect (quadQ m) (vec m c) * reflProd m cs) (vec m x) =
      vec m (reflCode m c (reflChain m cs x))
    rw [LinearEquiv.mul_apply, ih (fun d hd => hcs d (List.mem_cons_of_mem c hd)) x,
      reflect_vec (hcs c (List.mem_cons_self ..)) (reflChain m cs x)]

theorem reflProd_append (m : ℕ) (X Y : List ℕ) :
    reflProd m (X ++ Y) = reflProd m X * reflProd m Y := by
  simp only [reflProd, List.map_append, List.prod_append]

theorem reflProd_reverse (m : ℕ) (X : List ℕ) :
    reflProd m X.reverse = (reflProd m X)⁻¹ := by
  unfold reflProd
  have h : X.map ((fun x => x⁻¹) ∘ fun c => reflect (quadQ m) (vec m c)) =
      X.map fun c => reflect (quadQ m) (vec m c) :=
    List.map_congr_left fun c _ => reflect_inv (quadQ m) (vec m c)
  rw [List.map_reverse, List.prod_inv_reverse, List.map_map, h]

noncomputable def commGL (m : ℕ) (X Y : List ℕ) :
    GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2) :=
  (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)).symm
    ⁅reflProd m X, reflProd m Y⁆

theorem omegaMinusTwo_eq_comap (m : ℕ) :
    omegaMinusTwo m =
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadQ m),
        TauCeti.QuadraticMap.orthogonalGroup (quadQ m)⁆.comap
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv
          (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)).toMonoidHom := by
  rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.omegaMinusTwo_eq_statedOmega,
    CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
      (CFSG.LieType.Universal.Spin.coe_quadMinus (m + 1) (ZMod 2) 1 1)]
  rfl

theorem commGL_mem (m : ℕ) (X Y : List ℕ) : commGL m X Y ∈ omegaMinusTwo m := by
  rw [omegaMinusTwo_eq_comap, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, commGL,
    MulEquiv.apply_symm_apply]
  exact Subgroup.commutator_mem_commutator (reflProd_mem m X) (reflProd_mem m Y)

theorem commGL_vec {m : ℕ} {X Y : List ℕ}
    (hX : ∀ c ∈ X, CFSG.PGLModel.minusQuadForm m (1 : ZMod 2) 1 (vec m c) ≠ 0)
    (hY : ∀ c ∈ Y, CFSG.PGLModel.minusQuadForm m (1 : ZMod 2) 1 (vec m c) ≠ 0) (x : ℕ) :
    ((commGL m X Y : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ vec m x =
      vec m (reflChain m (X ++ Y ++ X.reverse ++ Y.reverse) x) := by
  have hprod : reflProd m (X ++ Y ++ X.reverse ++ Y.reverse) =
      reflProd m X * reflProd m Y * (reflProd m X)⁻¹ * (reflProd m Y)⁻¹ := by
    rw [reflProd_append, reflProd_append, reflProd_append, reflProd_reverse, reflProd_reverse]
  have hcs : ∀ c ∈ X ++ Y ++ X.reverse ++ Y.reverse,
      CFSG.PGLModel.minusQuadForm m (1 : ZMod 2) 1 (vec m c) ≠ 0 := by
    intro c hc
    simp only [List.mem_append, List.mem_reverse] at hc
    rcases hc with ((hc | hc) | hc) | hc
    · exact hX c hc
    · exact hY c hc
    · exact hX c hc
    · exact hY c hc
  calc
    ((commGL m X Y : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ vec m x
        = CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)
            (commGL m X Y) (vec m x) :=
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply _ _).symm
    _ = ⁅reflProd m X, reflProd m Y⁆ (vec m x) := by
          rw [commGL, MulEquiv.apply_symm_apply]
    _ = (reflProd m X * reflProd m Y * (reflProd m X)⁻¹ * (reflProd m Y)⁻¹) (vec m x) := by
          rw [commutatorElement_def]
    _ = reflProd m (X ++ Y ++ X.reverse ++ Y.reverse) (vec m x) := by
          rw [hprod]
    _ = vec m (reflChain m (X ++ Y ++ X.reverse ++ Y.reverse) x) :=
          reflProd_vec hcs x

theorem wordEval_vec {m k : ℕ} {gens : Fin k → GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)}
    {cols : List (List ℕ)}
    (hcols : ∀ i : Fin k, ∀ c ∈ cols.getD i [], c < 2 ^ (m + (m + 2)))
    (hgen : ∀ i : Fin k, ∀ x < 2 ^ (m + (m + 2)),
      ((gens i : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ vec m x =
        vec m (mApp (cols.getD i []) x))
    (w : List (Fin k)) {x : ℕ} (hx : x < 2 ^ (m + (m + 2))) :
    ((CFSG.Quasithin.JonesParshall.wordEval gens w :
        GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ vec m x =
      vec m (mApp (wordCols (m + (m + 2)) cols w) x) := by
  induction w generalizing x with
  | nil =>
    change (1 : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ vec m x =
      vec m (mApp ((List.range (m + (m + 2))).map (2 ^ ·)) x)
    rw [Matrix.one_mulVec, mApp_range_pow hx]
  | cons i w ih =>
    have hlt : mApp (wordCols (m + (m + 2)) cols w) x < 2 ^ (m + (m + 2)) :=
      CFSG.Quasithin.SteinbergCB.I16.mApp_lt_pow _ (wordCols_lt hcols w) x
    change ((gens i * CFSG.Quasithin.JonesParshall.wordEval gens w :
        GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ vec m x =
      vec m (mApp (wordCols (m + (m + 2)) cols (i :: w)) x)
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ih hx, hgen i _ hlt, mApp_wordCols_cons]

theorem omegaMinusTwo_le_closure {m k : ℕ} (hm : 2 ≤ m)
    {gens : Fin k → GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)} {cols : List (List ℕ)}
    (hcols : ∀ i : Fin k, ∀ c ∈ cols.getD i [], c < 2 ^ (m + (m + 2)))
    (hgen : ∀ i : Fin k, ∀ x < 2 ^ (m + (m + 2)),
      ((gens i : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ vec m x =
        vec m (mApp (cols.getD i []) x))
    {v₀ : ℕ} (hv₀ : CFSG.PGLModel.minusQuadForm m (1 : ZMod 2) 1 (vec m v₀) ≠ 0)
    (hword : ∀ u < 2 ^ (m + (m + 2)),
      CFSG.PGLModel.minusQuadForm m (1 : ZMod 2) 1 (vec m u) ≠ 0 →
      ∃ w : List (Fin k), ∀ x < 2 ^ (m + (m + 2)),
        mApp (wordCols (m + (m + 2)) cols w) x = reflCode m u (reflCode m v₀ x)) :
    omegaMinusTwo m ≤ Subgroup.closure (Set.range gens) := by
  have h5 : 5 ≤ Module.finrank (ZMod 2) (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) := by
    rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.finrank_minus]
    omega
  have hv₀' : quadQ m (vec m v₀) ≠ 0 := by
    rwa [coe_quadQ]
  have hT : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadQ m),
      TauCeti.QuadraticMap.orthogonalGroup (quadQ m)⁆ ≤
      Subgroup.closure {g | ∃ v : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2,
        quadQ m v ≠ 0 ∧ g = reflect (quadQ m) v * reflect (quadQ m) (vec m v₀)} :=
    CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_le_closure_reflect_mul
      (nondegenerate_quadQ m) h5 hv₀'
  have hTle : Subgroup.closure {g | ∃ v : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2,
      quadQ m v ≠ 0 ∧ g = reflect (quadQ m) v * reflect (quadQ m) (vec m v₀)} ≤
      (Subgroup.closure (Set.range gens)).map
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv
          (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro g ⟨v, hv, rfl⟩
    have hvec : vec m (code v) = v := vec_code v
    have hu_lt : code v < 2 ^ (m + (m + 2)) := code_lt v
    have hu_ne : CFSG.PGLModel.minusQuadForm m (1 : ZMod 2) 1 (vec m (code v)) ≠ 0 := by
      rw [hvec]
      intro h0
      exact hv (by rw [coe_quadQ]; exact h0)
    obtain ⟨w, hw⟩ := hword (code v) hu_lt hu_ne
    refine Subgroup.mem_map.2 ⟨CFSG.Quasithin.JonesParshall.wordEval gens w,
      CFSG.Quasithin.SteinbergCB.I16.wordEval_mem_closure_range gens w, ?_⟩
    refine LinearEquiv.ext fun y => ?_
    have hy : y = vec m (code y) := (vec_code y).symm
    rw [hy, MulEquiv.coe_toMonoidHom, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
      wordEval_vec hcols hgen w (code_lt y), hw (code y) (code_lt y),
      LinearEquiv.mul_apply,
      ← reflect_vec (m := m) (u := code v) hu_ne, hvec,
      ← reflect_vec (m := m) (u := v₀) hv₀]
  rw [omegaMinusTwo_eq_comap]
  intro g hg
  rw [Subgroup.mem_comap] at hg
  have hge : (CFSG.ClassicalGroups.Orthogonal.toLinEquiv
      (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)).toMonoidHom g ∈
      (Subgroup.closure (Set.range gens)).map
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv
          (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)).toMonoidHom :=
    (hT.trans hTle) hg
  obtain ⟨k, hk, hke⟩ := Subgroup.mem_map.mp hge
  have hkg : k = g :=
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)).injective hke
  rwa [hkg] at hk

noncomputable def codeAddEquiv (m : ℕ) :
    (Fin (m + (m + 2)) → ZMod 2) ≃+ (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) where
  toFun v := v ∘ codeIdx m
  invFun w := w ∘ (codeIdx m).symm
  left_inv v := by funext j; simp
  right_inv w := by funext i; simp
  map_add' v w := by funext i; simp

noncomputable def codeMu (m : ℕ) :
    GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2) →*
      AddMonoid.End (Fin (m + (m + 2)) → ZMod 2) where
  toFun g :=
    { toFun := fun v => (codeAddEquiv m).symm
        ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2) g)
          ((codeAddEquiv m) v))
      map_zero' := by
        change (codeAddEquiv m).symm
          ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2) g)
            ((codeAddEquiv m) 0)) = 0
        rw [map_zero, map_zero, map_zero]
      map_add' v w := by
        change (codeAddEquiv m).symm
          ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2) g)
            ((codeAddEquiv m) (v + w))) =
          (codeAddEquiv m).symm
            ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2) g)
              ((codeAddEquiv m) v)) +
          (codeAddEquiv m).symm
            ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2) g)
              ((codeAddEquiv m) w))
        rw [map_add, map_add, map_add] }
  map_one' := AddMonoid.End.ext _ fun v => by
    change (codeAddEquiv m).symm
      ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2) 1)
        ((codeAddEquiv m) v)) = v
    rw [map_one]
    change (codeAddEquiv m).symm ((codeAddEquiv m) v) = v
    exact AddEquiv.symm_apply_apply _ _
  map_mul' g h := AddMonoid.End.ext _ fun v => by
    change (codeAddEquiv m).symm
      ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2) (g * h))
        ((codeAddEquiv m) v)) =
      (codeAddEquiv m).symm
        ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2) g)
          ((codeAddEquiv m) ((codeAddEquiv m).symm
            ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv
              (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2) h) ((codeAddEquiv m) v)))))
    rw [map_mul, LinearEquiv.mul_apply, AddEquiv.apply_symm_apply]

noncomputable def omegaAction (m : ℕ) :
    ↥(omegaMinusTwo m) →* AddMonoid.End (Fin (m + (m + 2)) → ZMod 2) :=
  (codeMu m).comp (omegaMinusTwo m).subtype

theorem codeMu_apply (m : ℕ) (g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2))
    (v : Fin (m + (m + 2)) → ZMod 2) :
    codeMu m g v =
      (((g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ
        (v ∘ codeIdx m)) ∘ (codeIdx m).symm := by
  change (codeAddEquiv m).symm
    ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2) g)
      ((codeAddEquiv m) v)) = _
  rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
  rfl

theorem codeAddEquiv_codeMu (m : ℕ) (g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2))
    (v : Fin (m + (m + 2)) → ZMod 2) :
    codeAddEquiv m (codeMu m g v) =
      ((g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ
        codeAddEquiv m v := by
  rw [codeMu_apply]
  funext i
  simp [codeAddEquiv]

theorem codeAddEquiv_omegaAction (m : ℕ) (g : ↥(omegaMinusTwo m))
    (v : Fin (m + (m + 2)) → ZMod 2) :
    codeAddEquiv m (omegaAction m g v) =
      (((g : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ
        codeAddEquiv m v := by
  change codeAddEquiv m (codeMu m ((g : ↥(omegaMinusTwo m)) : GL _ (ZMod 2)) v) = _
  rw [codeAddEquiv_codeMu]

theorem omegaAction_apply (m : ℕ) (g : ↥(omegaMinusTwo m))
    (v : Fin (m + (m + 2)) → ZMod 2) :
    omegaAction m g v =
      ((((g : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ
        (v ∘ codeIdx m)) ∘ (codeIdx m).symm := by
  change codeMu m ((g : ↥(omegaMinusTwo m)) : GL _ (ZMod 2)) v = _
  rw [codeMu_apply]

theorem h1Natural_of_checks {m : ℕ} {gens : Fin 2 → ↥(omegaMinusTwo m)}
    (hgen : Subgroup.closure (Set.range gens) = ⊤) {cols : List (List ℕ)}
    (hcols : ∀ i : Fin 2, ∀ c ∈ cols.getD i [], c < 2 ^ (m + (m + 2)))
    (hact : ∀ i : Fin 2, ∀ x < 2 ^ (m + (m + 2)),
      (((gens i : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ vec m x =
        vec m (mApp (cols.getD i []) x))
    {rels : List (List (Fin 2))}
    (hrels : ∀ r ∈ rels, CFSG.Quasithin.JonesParshall.wordEval gens r = 1)
    (hclass : ∀ v₀ < 2 ^ (m + (m + 2)), ∀ v₁ < 2 ^ (m + (m + 2)),
      (∀ r ∈ rels, CFSG.Quasithin.SteinbergCB.I16.foxCode cols [v₀, v₁] r = 0) →
      ∃ x < 2 ^ (m + (m + 2)), ∃ ε < 2,
        v₀ = mApp (cols.getD 0 []) x ^^^ x ^^^ ε * [0, 0].getD 0 0 ∧
        v₁ = mApp (cols.getD 1 []) x ^^^ x ^^^ ε * [0, 0].getD 1 0) :
    H1Natural m := by
  unfold H1Natural
  intro F hF
  let f : ↥(omegaMinusTwo m) → (Fin (m + (m + 2)) → ZMod 2) :=
    fun g => F g ∘ (codeIdx m).symm
  have hμ : ∀ i : Fin 2, ∀ x < 2 ^ (m + (m + 2)),
      omegaAction m (gens i) (toV (m + (m + 2)) x) =
        toV (m + (m + 2)) (mApp (cols.getD i []) x) := by
    intro i x hx
    rw [omegaAction_apply]
    have hv : (toV (m + (m + 2)) x ∘ codeIdx m) = vec m x := rfl
    rw [hv, hact i x hx]
    funext j
    simp [vec]
  have hf : f ∈ CFSG.Quasithin.JonesParshall.Z1A (omegaAction m) := by
    intro g h
    funext i
    have h1 := congrFun (hF g h) ((codeIdx m).symm i)
    have hv : (F h ∘ (codeIdx m).symm) ∘ (codeIdx m) = F h := by
      funext j
      simp
    simp only [f, Pi.add_apply, Function.comp_apply] at h1 ⊢
    rw [h1, omegaAction_apply, hv]
    rfl
  have hclass' : ∀ f ∈ CFSG.Quasithin.JonesParshall.Z1A (omegaAction m),
      f ∈ CFSG.Quasithin.JonesParshall.B1A (omegaAction m) ∨
        f - 0 ∈ CFSG.Quasithin.JonesParshall.B1A (omegaAction m) :=
    CFSG.Quasithin.SteinbergCB.I16.classify_Z1A (G := ↥(omegaMinusTwo m))
      (m := m + (m + 2)) (μ := omegaAction m) (gens := gens) hgen hcols hμ hrels
      (zero_mem _) (c := [0, 0]) (by
        intro i
        fin_cases i <;> exact (toV_zero (m + (m + 2))).symm)
      (by
        intro v₀ hv₀ v₁ hv₁ hfox
        exact hclass v₀ hv₀ v₁ hv₁ hfox)
  have key : f ∈ CFSG.Quasithin.JonesParshall.B1A (omegaAction m) →
      ∃ a' : (Fin m ⊕ Fin m ⊕ Fin 2) → ZMod 2, ∀ g : ↥(omegaMinusTwo m),
        F g = (((g : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ a' - a' := by
    intro hb
    obtain ⟨a, ha⟩ := hb
    refine ⟨codeAddEquiv m a, fun g => ?_⟩
    have h1 : codeAddEquiv m (f g) = F g := by
      funext i
      simp [f, codeAddEquiv]
    have h2 : codeAddEquiv m
        (CFSG.Quasithin.JonesParshall.coboundaryA (omegaAction m) a g) =
        (((g : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ
          codeAddEquiv m a - codeAddEquiv m a := by
      rw [CFSG.Quasithin.JonesParshall.coboundaryA_apply, map_sub,
        codeAddEquiv_omegaAction]
    calc F g = codeAddEquiv m (f g) := h1.symm
      _ = codeAddEquiv m
            (CFSG.Quasithin.JonesParshall.coboundaryA (omegaAction m) a g) := by rw [ha]
      _ = _ := h2
  rcases hclass' f hf with h | h
  · exact key h
  · rw [sub_zero] at h
    exact key h

end CFSG.CGT.Harada80

module

public import CFSG.LieType.Chevalley.C2E6UnitaryFourEquivariance
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Overlap

open Module Matrix CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

instance : RingHomSurjective barHom := ⟨fun a => ⟨bar a, bar_bar a⟩⟩

@[expose] def frobV : V →ₛₗ[barHom] V where
  toFun v i := bar (v i)
  map_add' _ _ := funext fun _ => bar_add _ _
  map_smul' _ _ := funext fun _ => bar_mul _ _

@[expose] def frobW : W →ₛₗ[barHom] W where
  toFun x p := bar (x p)
  map_add' _ _ := funext fun _ => bar_add _ _
  map_smul' _ _ := funext fun _ => bar_mul _ _

theorem frobV_apply (v : V) (i : Fin 4) : frobV v i = bar (v i) := rfl

theorem frobW_apply (x : W) (p : Fin 6) : frobW x p = bar (x p) := rfl

theorem bar_sub (a b : K) : bar (a - b) = bar a - bar b := by revert a b; decide

theorem frobW_wedge (u v : V) : frobW (wedge u v) = wedge (frobV u) (frobV v) := by
  funext p
  fin_cases p <;> simp [frobW_apply, frobV_apply, wedge, bar_sub, bar_mul]

theorem T_frobW (x : W) : T (frobW x) = frobW (T x) := by
  funext p
  fin_cases p <;> rfl

theorem herm_frobV (x v : V) : herm (frobV x) (frobV v) = bar (herm x v) := by
  simp only [herm, frobV_apply, bar_add, bar_mul]

theorem frobV_frobV (v : V) : frobV (frobV v) = v := funext fun i => bar_bar (v i)

theorem frobW_frobW (x : W) : frobW (frobW x) = x := funext fun p => bar_bar (x p)

theorem Pf_frobW (x : W) : Pf (frobW x) = bar (Pf x) := by
  simp only [Pf, frobW_apply, bar_add, bar_mul]

@[expose] def frobLinW : W →ₗ[ZMod 2] W where
  toFun := frobW
  map_add' := map_add frobW
  map_smul' c x := by
    rw [← algebraMap_smul K c x, map_smulₛₗ, barHom_apply, bar_coe, algebraMap_smul]
    rfl

theorem frobLinW_apply (x : W) : frobLinW x = frobW x := rfl

theorem frobLinW_injective : Function.Injective frobLinW := fun x y h => by
  rw [← frobW_frobW x, ← frobW_frobW y]
  exact congrArg frobW h

theorem Pf_frobLinW {w : W} (hw : w ∈ W₀) : Pf (frobLinW w) = Pf w := by
  rw [frobLinW_apply, Pf_frobW, Pf_eq_Q hw, bar_coe]

@[expose] def frobIso : QuadraticMap.IsometryEquiv Q Q :=
  isoOfCommute frobLinW frobLinW_injective (fun x => T_frobW x) fun _ hw => Pf_frobLinW hw

theorem frobIso_apply_aux : ∀ a b c d e f : ZMod 2,
    psiLin (frobW (param ![a, b, c, d, e, f])) = ![a, b, c, d, e + f, f] := by
  decide

theorem frobIso_apply (x : X) : frobIso x = ![x 0, x 1, x 2, x 3, x 4 + x 5, x 5] := by
  change psiLin (frobW (param x)) = _
  rw [eta_X x]
  exact frobIso_apply_aux _ _ _ _ _ _

theorem frobIso_psiLin {w : W} (hw : w ∈ W₀) : frobIso (psiLin w) = psiLin (frobW w) :=
  isoOfCommute_psiLin _ _ _ _ hw

theorem L_map_frob (P : Submodule K V) : L (P.map frobV) = (L P).map frobW := by
  rw [L, L, Submodule.map_span]
  congr 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_image, Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨wedge x y, ⟨x, hx, y, hy, rfl⟩, frobW_wedge x y⟩
  · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, frobW_wedge x y⟩

theorem perp_map_frob (ℓ : Submodule K V) : perp (ℓ.map frobV) = (perp ℓ).map frobV := by
  ext v
  simp only [mem_perp, Submodule.mem_map]
  constructor
  · intro h
    refine ⟨frobV v, fun x hx => ?_, frobV_frobV v⟩
    rw [← bar_eq_zero_iff, ← herm_frobV, frobV_frobV]
    exact h _ ⟨x, hx, rfl⟩
  · rintro ⟨v', hv', rfl⟩ _ ⟨x, hx, rfl⟩
    rw [herm_frobV, hv' x hx, bar_zero]

theorem M_map_frob (ℓ : Submodule K V) : M (ℓ.map frobV) = (M ℓ).map frobW := by
  rw [M, M, Submodule.map_span, perp_map_frob]
  congr 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_image, Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨wedge x y, ⟨x, hx, y, hy, rfl⟩, frobW_wedge x y⟩
  · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, frobW_wedge x y⟩

theorem pointMap_map_frob (P : Submodule K V) :
    pointMap (P.map frobV) = (pointMap P).map (frobIso.toLinearEquiv : X →ₗ[ZMod 2] X) := by
  refine map_fixed_iso _ _ _ _ ?_
  rw [L_map_frob, Submodule.map_coe]
  rfl

theorem lineMap_map_frob (ℓ : Submodule K V) :
    lineMap (ℓ.map frobV) = (lineMap ℓ).map (frobIso.toLinearEquiv : X →ₗ[ZMod 2] X) := by
  refine map_fixed_iso _ _ _ _ ?_
  rw [M_map_frob, Submodule.map_coe]
  rfl

end CFSG.LieType.Chevalley.C2E6Overlap

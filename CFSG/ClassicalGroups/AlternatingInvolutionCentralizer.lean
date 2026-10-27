module
public import CFSG.ClassicalGroups.PCoreSection
public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import CFSG.RankThree.GF2n.Stroth80.Sec7IsometryFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveIsometry

public section

namespace CFSG.ClassicalGroups.AlternatingCentralizer

theorem range_eq_of_stable_of_transvections
    {F M G : Type} [Field F] [AddCommGroup M] [Module F M] [Group G]
    (rep : G →* Module.End F M) (N : Module.End F M)
    (B : M →ₗ[F] M →ₗ[F] F)
    (hB : ∀ w : M, w ≠ 0 → ∃ a : M, B w a ≠ 0)
    (S : Subgroup G)
    (hTrans : ∀ a : M, ∃ g ∈ S, ∀ x ∈ LinearMap.range N,
      rep g x = x + B x a • N a)
    {W : Submodule F M} (hWU : W ≤ LinearMap.range N)
    (hStable : ∀ g ∈ S, ∀ x ∈ W, rep g x ∈ W) :
    W = ⊥ ∨ W = LinearMap.range N := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W).mp hW
  have hmem (a : M) (ha : B w a ≠ 0) : N a ∈ W := by
    obtain ⟨g, hg, hAct⟩ := hTrans a
    have hd := W.sub_mem (hStable g hg w hw) hw
    rw [hAct w (hWU hw), add_sub_cancel_left] at hd
    have h := W.smul_mem (B w a)⁻¹ hd
    simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using h
  obtain ⟨a₀, ha₀⟩ := hB w hw0
  refine Or.inr (le_antisymm hWU ?_)
  intro v hv
  obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hv
  by_cases ha : B w a = 0
  · have haa : B w (a + a₀) ≠ 0 := by
      simpa only [map_add, ha, zero_add] using ha₀
    have heq : N a = N (a + a₀) - N a₀ := by rw [map_add]; abel
    rw [heq]
    exact W.sub_mem (hmem (a + a₀) haa) (hmem a₀ ha₀)
  · exact hmem a ha

theorem pCoreOf_fixes_range_of_transvections
    {F M G : Type} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup M] [Module F M] [Finite M] [Group G]
    (rep : G →* Module.End F M) (N : Module.End F M)
    (B : M →ₗ[F] M →ₗ[F] F)
    (hB : ∀ w : M, w ≠ 0 → ∃ a : M, B w a ≠ 0)
    (S : Subgroup G)
    (hRange : ∀ g ∈ S, ∀ x ∈ LinearMap.range N, rep g x ∈ LinearMap.range N)
    (hTrans : ∀ a : M, ∃ g ∈ S, ∀ x ∈ LinearMap.range N,
      rep g x = x + B x a • N a) :
    ∀ g ∈ CFSG.Open.pCoreOf 2 S, ∀ x ∈ LinearMap.range N, rep g x = x := by
  have hAct : CFSG.ClassicalGroups.PCoreSection.IsLinearAction F (fun g x => rep g x) :=
    { one := fun x => by rw [map_one]; rfl
      mul := fun g h x => by rw [map_mul]; rfl
      add := fun g x y => map_add (rep g) x y
      smul := fun g c x => (rep g).map_smul c x }
  have h := CFSG.ClassicalGroups.PCoreSection.apply_sub_mem_of_isPGroup hAct
    (CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 S)
    (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 S)
    (fun g hg t ht => CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hg ht)
    (L := ⊥) (P := LinearMap.range N) bot_le hRange
    (by intro g hg x hx; simp only [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero])
    (fun W _ hWU hInv => range_eq_of_stable_of_transvections rep N B hB S hTrans hWU hInv)
  intro g hg x hx
  exact sub_eq_zero.mp ((Submodule.mem_bot F).mp (h g hg x hx))

section Symplectic

variable {F M : Type} [Field F] [AddCommGroup M] [Module F M]

include F in
private theorem vec_neg [CharP F 2] (x : M) : -x = x := by
  rw [← neg_one_smul F x, CharTwo.neg_eq, one_smul]

private theorem isAlt_symm [CharP F 2] {B : LinearMap.BilinForm F M}
    (hB : B.IsAlt) (x y : M) : B x y = B y x := by
  rw [← hB.neg_eq, CharTwo.neg_eq]

private noncomputable abbrev sympTransvection (B : LinearMap.BilinForm F M) (hB : B.IsAlt) (a : M) : M ≃ₗ[F] M :=
  LinearEquiv.transvection (f := B.flip a) (v := a) (hB.self_eq_zero a)

private theorem sympTransvection_apply (B : LinearMap.BilinForm F M) (hB : B.IsAlt) (a x : M) :
    sympTransvection B hB a x = x + B x a • a := by
  exact LinearEquiv.transvection.apply (f := B.flip a) (v := a) (hB.self_eq_zero a) x

private theorem sympTransvection_mem (B : LinearMap.BilinForm F M) (hB : B.IsAlt) (a : M) :
    sympTransvection B hB a ∈ TauCeti.BilinForm.isometryGroup B := by
  rw [TauCeti.BilinForm.mem_isometryGroup_iff]
  intro x y
  simp only [sympTransvection_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hB.self_eq_zero, mul_zero, add_zero, ← hB.neg_eq y a]
  ring

@[expose] def isometryRep (B : LinearMap.BilinForm F M) :
    TauCeti.BilinForm.isometryGroup B →* Module.End F M :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (TauCeti.BilinForm.isometryGroup B).subtype

variable [CharP F 2]

theorem paired_transvection_action
    (B : LinearMap.BilinForm F M) (hB : B.IsAlt)
    (r : TauCeti.BilinForm.isometryGroup B) (hr : r ^ 2 = 1)
    (hAlt : ∀ a : M, B a (r.1 a - a) = 0) :
    ∀ a : M, ∃ g ∈ Subgroup.centralizer ({r} : Set (TauCeti.BilinForm.isometryGroup B)),
      ∀ x ∈ LinearMap.range (isometryRep B r - 1),
        isometryRep B g x = x + B x a • (isometryRep B r - 1) a := by
  have hRR (x : M) : r.1 (r.1 x) = x := by
    have h := congrArg (fun g : TauCeti.BilinForm.isometryGroup B => g.1 x) hr
    change r.1 (r.1 x) = x at h
    exact h
  have hPres (x y : M) : B (r.1 x) (r.1 y) = B x y :=
    TauCeti.BilinForm.mem_isometryGroup_iff.mp r.2 x y
  have hAdj (x y : M) : B (r.1 x) y = B x (r.1 y) := by
    calc
      B (r.1 x) y = B (r.1 x) (r.1 (r.1 y)) := by rw [hRR]
      _ = B x (r.1 y) := hPres x (r.1 y)
  have hRangeFix {x : M} (hx : x ∈ LinearMap.range (isometryRep B r - 1)) : r.1 x = x := by
    obtain ⟨b, rfl⟩ := LinearMap.mem_range.mp hx
    change r.1 (r.1 b - b) = r.1 b - b
    rw [map_sub, hRR]
    simp only [sub_eq_add_neg, vec_neg (F := F)]
    exact add_comm _ _
  intro a
  have hOrth : B a (r.1 a) = 0 := by
    have hmap := map_sub (B a) (r.1 a) a
    rw [hB.self_eq_zero] at hmap
    exact (_root_.sub_zero (B a (r.1 a))).symm.trans (hmap.symm.trans (hAlt a))
  have hOrth' : B (r.1 a) a = 0 := (isAlt_symm hB _ _).trans hOrth
  let ta : TauCeti.BilinForm.isometryGroup B :=
    ⟨sympTransvection B hB a, sympTransvection_mem B hB a⟩
  let tr : TauCeti.BilinForm.isometryGroup B :=
    ⟨sympTransvection B hB (r.1 a), sympTransvection_mem B hB (r.1 a)⟩
  let g : TauCeti.BilinForm.isometryGroup B := ta * tr
  have hApply (x : M) : g.1 x = x + B x a • a + B x (r.1 a) • r.1 a := by
    change sympTransvection B hB a (sympTransvection B hB (r.1 a) x) = _
    simp only [sympTransvection_apply, map_add, map_smul, hOrth', add_zero, zero_smul]
  have hComm : r * g = g * r := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change r.1 (g.1 x) = g.1 (r.1 x)
    rw [hApply, hApply, map_add, map_add, map_smul, map_smul, hRR]
    simp only [hAdj, hRR]
    abel
  refine ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr hComm.symm, ?_⟩
  intro x hx
  have hba : B x (r.1 a) = B x a := by
    rw [← hAdj, hRangeFix hx]
  change g.1 x = x + B x a • (r.1 a - a)
  rw [hApply, hba]
  simp only [sub_eq_add_neg, vec_neg (F := F), smul_add]
  abel

variable [Finite F]

theorem pCoreOf_centralizer_fixes_displacement [Finite M]
    (B : LinearMap.BilinForm F M) (hB : B.IsAlt)
    (hNondeg : ∀ w : M, w ≠ 0 → ∃ a : M, B w a ≠ 0)
    (r : TauCeti.BilinForm.isometryGroup B) (hr : r ^ 2 = 1)
    (hAlt : ∀ a : M, B a (r.1 a - a) = 0) :
    ∀ g ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({r} : Set (TauCeti.BilinForm.isometryGroup B))),
      ∀ x ∈ LinearMap.range (isometryRep B r - 1), g.1 x = x := by
  apply pCoreOf_fixes_range_of_transvections (isometryRep B) (isometryRep B r - 1)
    B hNondeg (Subgroup.centralizer ({r} : Set (TauCeti.BilinForm.isometryGroup B)))
  · intro g hg x hx
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hx
    have hComm : r * g = g * r := (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
    have hVec := congrArg (fun k : TauCeti.BilinForm.isometryGroup B => k.1 a) hComm
    change r.1 (g.1 a) = g.1 (r.1 a) at hVec
    refine LinearMap.mem_range.mpr ⟨g.1 a, ?_⟩
    change r.1 (g.1 a) - g.1 a = g.1 (r.1 a - a)
    rw [map_sub, hVec]
  · exact paired_transvection_action B hB r hr hAlt

theorem pCoreOf_centralizer_le_centralizer_of_fix_kernel [Finite M]
    (B : LinearMap.BilinForm F M) (hB : B.IsAlt)
    (hNondeg : ∀ w : M, w ≠ 0 → ∃ a : M, B w a ≠ 0)
    (r : TauCeti.BilinForm.isometryGroup B) (hr : r ^ 2 = 1)
    (hAlt : ∀ a : M, B a (r.1 a - a) = 0)
    (V : Subgroup (TauCeti.BilinForm.isometryGroup B))
    (hFix : ∀ v ∈ V, ∀ x ∈ LinearMap.ker (isometryRep B r - 1), v.1 x = x) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({r} : Set (TauCeti.BilinForm.isometryGroup B))) ≤
      Subgroup.centralizer (V : Set (TauCeti.BilinForm.isometryGroup B)) := by
  have : FiniteDimensional F M := Module.Finite.of_finite
  have hn : B.Nondegenerate := by
    constructor
    · intro x hx
      by_contra hx0
      obtain ⟨a, ha⟩ := hNondeg x hx0
      exact ha (hx a)
    · intro x hx
      by_contra hx0
      obtain ⟨a, ha⟩ := hNondeg x hx0
      exact ha ((isAlt_symm hB _ _).trans (hx a))
  have hrefl : B.IsRefl := by
    intro x y hxy
    rw [← isAlt_symm hB x y, hxy]
  have hker : LinearMap.ker (isometryRep B r - 1) =
      B.orthogonal (LinearMap.range (isometryRep B r - 1)) :=
    CFSG.RankThree.GF2n.Stroth80.sec7_ker_sub_one_eq_perp_range B hn hrefl r.1
      (TauCeti.BilinForm.mem_isometryGroup_iff.mp r.2)
  intro g hg
  apply Subgroup.mem_centralizer_iff.mpr
  intro v hv
  have hrange : LinearMap.range (CFSG.RankThree.GF2n.Stroth80.opm v.1) ≤
      LinearMap.range (isometryRep B r - 1) := by
    intro z hz
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hz
    rw [CFSG.RankThree.GF2n.Stroth80.opm_apply]
    have h := CFSG.RankThree.GF2n.Stroth80.sub_mem_orthogonal_of_fixes B v.1
      (TauCeti.BilinForm.mem_isometryGroup_iff.mp v.2)
      (LinearMap.ker (isometryRep B r - 1)) (hFix v hv) x
    rwa [hker, B.orthogonal_orthogonal hn hrefl] at h
  have hk : B.orthogonal (LinearMap.range (isometryRep B r - 1)) ≤
      LinearMap.ker (CFSG.RankThree.GF2n.Stroth80.opm v.1) := by
    intro x hx
    rw [← hker] at hx
    rw [LinearMap.mem_ker, CFSG.RankThree.GF2n.Stroth80.opm_apply, hFix v hv x hx, sub_self]
  have h := CFSG.RankThree.GF2n.Stroth80.mul_comm_of_fixes B g.1 v.1
    (TauCeti.BilinForm.mem_isometryGroup_iff.mp g.2)
    (LinearMap.range (isometryRep B r - 1))
    (fun x hx => pCoreOf_centralizer_fixes_displacement B hB hNondeg r hr hAlt g hg x hx)
    hrange hk
  have hgv : g * v = v * g := Subtype.ext h
  first | exact hgv | exact hgv.symm

end Symplectic

end CFSG.ClassicalGroups.AlternatingCentralizer

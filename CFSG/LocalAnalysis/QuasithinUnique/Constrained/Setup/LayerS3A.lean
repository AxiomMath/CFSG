module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerS3Fix

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem conjR_sup (x : V ≃ₗ[k] V) (X Y : Subgroup (V ≃ₗ[k] V)) :
    conjR x (X ⊔ Y) = conjR x X ⊔ conjR x Y :=
  (conjSub x⁻¹).map_sup X Y

theorem natS_eq (N A : Subgroup (V ≃ₗ[k] V)) {ι : Type*} (g : ι → V ≃ₗ[k] V) (i : ι) :
    natS N A g i = conjR (g i) (⁅N, A⁆ ⊔ A) :=
  (conjR_sup _ _ _).symm

theorem conjSub_le_of_mem {G X : Subgroup (V ≃ₗ[k] V)} {x : V ≃ₗ[k] V} (hx : x ∈ G)
    (hX : X ≤ G) : conjSub x X ≤ G := by
  intro y hy
  rw [mem_conjSub] at hy
  have h1 := hX hy
  have h2 : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
  rw [h2]
  exact G.mul_mem (G.mul_mem hx h1) (G.inv_mem hx)

theorem conjSub_conjR_eq {a x y : V ≃ₗ[k] V} {X : Subgroup (V ≃ₗ[k] V)}
    (hxy : a * y⁻¹ = x) : conjSub y (conjR a X) = conjR x X := by
  rw [conjSub_conjR, hxy]

namespace OddAbelianSetting

variable [CharP k 2] [Finite V] {G N A : Subgroup (V ≃ₗ[k] V)} {ι : Type*}
  {g : ι → V ≃ₗ[k] V} [Fintype ι] (h : OddAbelianSetting G N A) (F : ConjFamily G N A g)

include h F

omit [Fintype ι] F in
theorem pd_conjR {x : V ≃ₗ[k] V} (hx : x ∈ G) {i : ι}
    (hxi : conjR x ⁅N, A⁆ = natL N A g i) :
    PlaneData G N (conjR x A) (natL N A g i) (natI N A g i) := by
  have pd := h.planeData_conj (G.inv_mem hx)
  have e : conjSub x⁻¹ ⁅N, A⁆ = natL N A g i := hxi
  rw [e] at pd
  exact pd

theorem S_choice {x : V ≃ₗ[k] V} (hx : x ∈ G) {i : ι}
    (hxi : conjR x ⁅N, A⁆ = natL N A g i) :
    conjR x (⁅N, A⁆ ⊔ A) = natS N A g i := by
  have fd := h.famData F
  have pd1 := h.pd_conjR hx hxi
  have pd2 := h.planeData_family F i
  have e1 : conjR x (⁅N, A⁆ ⊔ A) = natL N A g i ⊔ conjR x A := by
    rw [conjR_sup, hxi]
  rw [e1]
  exact fd.sup_eq_of_planeData pd1 pd2

theorem S_perm {x : V ≃ₗ[k] V} (hx : x ∈ G) (i : ι) :
    ∃ j, conjSub x (natS N A g i) = natS N A g j ∧ conjSub x (natL N A g i) = natL N A g j ∧
      (natI N A g i).map (x : V →ₗ[k] V) = natI N A g j := by
  have hy : g i * x⁻¹ ∈ G := G.mul_mem (F.mem i) (G.inv_mem hx)
  obtain ⟨j, hj⟩ := F.all _ hy
  refine ⟨j, ?_, ?_, ?_⟩
  · rw [natS_eq, conjSub_conjR_eq (a := g i) (x := g i * x⁻¹) (y := x) rfl]
    exact h.S_choice F hy hj
  · have : conjSub x (natL N A g i) = conjR (g i * x⁻¹) ⁅N, A⁆ :=
      conjSub_conjR_eq (a := g i) (x := g i * x⁻¹) (y := x) rfl
    rw [this, hj]
  · have : conjSub x (natL N A g i) = natL N A g j := by
      have e : conjSub x (natL N A g i) = conjR (g i * x⁻¹) ⁅N, A⁆ :=
        conjSub_conjR_eq (a := g i) (x := g i * x⁻¹) (y := x) rfl
      rw [e, hj]
    have e2 := commGL_conjSub x (natL N A g i)
    rw [this] at e2
    exact e2.symm

omit [CharP k 2] [Finite V] [Fintype ι] h in
theorem S_trans (i j : ι) :
    ∃ x ∈ G, conjSub x (natS N A g i) = natS N A g j ∧ conjSub x (natL N A g i) = natL N A g j ∧
      (natI N A g i).map (x : V →ₗ[k] V) = natI N A g j := by
  refine ⟨(g j)⁻¹ * g i, G.mul_mem (G.inv_mem (F.mem j)) (F.mem i), ?_⟩
  have hxy : g i * ((g j)⁻¹ * g i)⁻¹ = g j := by group
  have hL : conjSub ((g j)⁻¹ * g i) (natL N A g i) = natL N A g j := by
    have e : conjSub ((g j)⁻¹ * g i) (natL N A g i) = conjR (g j) ⁅N, A⁆ :=
      conjSub_conjR_eq (a := g i) (x := g j) (y := (g j)⁻¹ * g i) hxy
    exact e
  refine ⟨?_, hL, ?_⟩
  · rw [natS_eq, natS_eq, conjSub_conjR_eq (a := g i) (x := g j) (y := (g j)⁻¹ * g i) hxy]
  · have e2 := commGL_conjSub ((g j)⁻¹ * g i) (natL N A g i)
    rw [hL] at e2
    exact e2.symm

theorem B_eq : natB G N A = ⨆ i, natS N A g i := by
  apply le_antisymm
  · refine iSup₂_le fun x hx => ?_
    obtain ⟨i, hi⟩ := F.all x hx
    rw [h.S_choice F hx hi]
    exact le_iSup (natS N A g) i
  · refine iSup_le fun i => ?_
    rw [natS_eq]
    exact le_iSup₂_of_le (g i) (F.mem i) le_rfl

omit [CharP k 2] [Finite V] [Fintype ι] F in
theorem natB_le : natB G N A ≤ G := by
  refine iSup₂_le fun x hx => ?_
  exact conjSub_le_of_mem (G.inv_mem hx) (sup_le (h.L_le_N.trans h.N_le) h.A_le)

omit [CharP k 2] [Finite V] [Fintype ι] h F in
theorem conjSub_natB_le {y : V ≃ₗ[k] V} (hy : y ∈ G) : conjSub y (natB G N A) ≤ natB G N A := by
  have e : conjSub y (natB G N A) = ⨆ x ∈ G, conjSub y (conjR x (⁅N, A⁆ ⊔ A)) := by
    simp only [natB, OrderIso.map_iSup]
  rw [e]
  refine iSup₂_le fun x hx => ?_
  rw [conjSub_conjR]
  exact le_iSup₂_of_le (x * y⁻¹) (G.mul_mem hx (G.inv_mem hy)) le_rfl

omit [CharP k 2] [Finite V] [Fintype ι] F in
theorem natB_normal : ((natB G N A).subgroupOf G).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer h.natB_le]
  intro y hy
  exact mem_normalizer_of_conjSub_le (conjSub_natB_le hy) (conjSub_natB_le (G.inv_mem hy))

omit [CharP k 2] [Finite V] [Fintype ι] h F in
theorem LA_le_B : ⁅N, A⁆ ⊔ A ≤ natB G N A := by
  have := le_iSup₂_of_le (f := fun x (_ : x ∈ G) => conjR x (⁅N, A⁆ ⊔ A)) (1 : V ≃ₗ[k] V)
    G.one_mem (conjR_one (⁅N, A⁆ ⊔ A)).ge
  exact this

theorem D_normal_aux {y : V ≃ₗ[k] V} (hy : y ∈ G) :
    conjSub y (natD N A g) ≤ natD N A g := by
  have e : conjSub y (natD N A g) = ⨆ i, conjSub y (natL N A g i) := by
    simp only [natD, OrderIso.map_iSup]
  rw [e]
  refine iSup_le fun i => ?_
  obtain ⟨j, -, hj, -⟩ := h.S_perm F hy i
  rw [hj]
  exact le_iSup (natL N A g) j

end OddAbelianSetting

end CFSG.QuasithinUnique.Setup.Layer

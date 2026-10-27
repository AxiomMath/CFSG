module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G]

theorem lbUp_layer_le_self (p : ℕ) (N : Subgroup G) : GLAPLayer p N ≤ N :=
  sSup_le fun _ hL => hL.1

theorem lbUp_inf_ker_subtype_eq_bot (X : Subgroup G) (A : Subgroup X) :
    A ⊓ X.subtype.ker = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  have h1 : X.subtype x = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hx).2
  exact Subgroup.mem_bot.2 (Subtype.ext h1)

theorem lbUp_component_top_map [Finite G] {p : ℕ} (hp : p.Prime) (X : Subgroup G)
    {J : Subgroup X} (hJ : GLAPComponent p ⊤ J) : GLAPComponent p X (J.map X.subtype) := by
  have hker : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup X) ⊓ X.subtype.ker)) := by
    rw [lbUp_inf_ker_subtype_eq_bot, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have h := glaPComponent_map hp X.subtype hker hJ
  have htop : (⊤ : Subgroup X).map X.subtype = X :=
    le_antisymm (by rintro _ ⟨y, -, rfl⟩; exact y.2) fun y hy => ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩
  rwa [htop] at h

theorem lbUp_layer_top_le_comap [Finite G] {p : ℕ} (hp : p.Prime) (X : Subgroup G) :
    GLAPLayer p (⊤ : Subgroup X) ≤ (GLAPLayer p X).comap X.subtype := by
  unfold GLAPLayer
  refine sSup_le fun J hJ => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (lbUp_component_top_map hp X hJ)

theorem lbUp_subgroupOf_inf_centralizer (X E : Subgroup G) (hEX : E ≤ X) :
    (X ⊓ Subgroup.centralizer (E : Set G)).subgroupOf X =
      Subgroup.centralizer (((E.subgroupOf X : Subgroup X)) : Set X) := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    refine Subgroup.mem_centralizer_iff.2 fun h hh => Subtype.ext ?_
    have hc : (x : G) ∈ Subgroup.centralizer (E : Set G) := (Subgroup.mem_inf.1 hx).2
    have h' := Subgroup.mem_centralizer_iff.1 hc (h : G) (Subgroup.mem_subgroupOf.1 hh)
    simpa using h'
  · intro hx
    refine Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
    have h := congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.1 hx ⟨e, hEX he⟩ (Subgroup.mem_subgroupOf.2 he))
    simpa using h

theorem glaPLayer_inf_centralizer_le_of_input18_2One (i2 : LocalBalance.Input18_2One)
    [Finite G] {X E : Subgroup G} (hK : CFSG.Open.IsKGroup ↥X) {p : ℕ} (hp : p.Prime)
    (hEX : E ≤ X) (hE : IsElemAbelian p E) :
    GLAPLayer p (X ⊓ Subgroup.centralizer (E : Set G)) ≤ GLAPLayer p X := by
  set M : Subgroup G := X ⊓ Subgroup.centralizer (E : Set G) with hM
  have hMX : M ≤ X := inf_le_left
  set E' : Subgroup X := E.subgroupOf X with hE'
  have hE'p : IsPGroup p E' := fun z =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hE.2 ((z : X) : G) (Subgroup.mem_subgroupOf.1 z.2)))⟩
  have hkey : GLAPLayer p (Subgroup.centralizer (E' : Set X)) ≤ GLAPLayer p (⊤ : Subgroup X) := by
    have h2 := i2 X hK p hp E' hE'p
    exact (le_of_eq h2.symm).trans ((lbUp_layer_le_self p _).trans inf_le_left)
  unfold GLAPLayer
  refine sSup_le fun K hKM => ?_
  have hKM' : GLAPComponent p M K := hKM
  have hMap : (M.subgroupOf X).map X.subtype = M := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hMX]
  have hcomp : GLAPComponent p ((M.subgroupOf X).map X.subtype) K := by
    rw [hMap]; exact hKM'
  have hker : Nat.Coprime p (Nat.card ↥((M.subgroupOf X) ⊓ X.subtype.ker)) := by
    rw [lbUp_inf_ker_subtype_eq_bot, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  obtain ⟨K₀, hK₀, hK₀map⟩ := exists_glaPComponent_map_eq hp X.subtype hker hcomp
  have hK₀A : K₀ ≤ GLAPLayer p (M.subgroupOf X) := le_sSup hK₀
  have hK₀C : K₀ ≤ GLAPLayer p (Subgroup.centralizer (E' : Set X)) := by
    rw [← lbUp_subgroupOf_inf_centralizer X E hEX]
    exact hK₀A
  have hK₀top : K₀ ≤ GLAPLayer p (⊤ : Subgroup X) := hK₀C.trans hkey
  rw [← hK₀map]
  exact Subgroup.map_le_iff_le_comap.2 (hK₀top.trans (lbUp_layer_top_le_comap hp X))

end CFSG.HardMathSupport.Solomon.Proving

end

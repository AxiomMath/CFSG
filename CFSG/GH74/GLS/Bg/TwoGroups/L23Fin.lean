module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23Ext
public import CFSG.GH74.GLS.Bg.TwoGroups.A44Data

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L23

open A44

@[expose] def actHom (M : M4) : Vec →+ Vec where
  toFun := M.act
  map_zero' := by simp [M4.act]
  map_add' := M4.act_add M

@[expose] def Pm : M4 := ⟨1, 2, 2, 1⟩

@[expose] def Qm : M4 := ⟨3, 0, 2, 3⟩

@[expose] def PP : Vec →+ Vec := actHom Pm

@[expose] def QQ : Vec →+ Vec := actHom Qm

theorem hdistPQ : ∀ i j i' j' : Bool, (∀ w, Mop PP QQ i j w = Mop PP QQ i' j' w) →
    i = i' ∧ j = j' := by decide +kernel

@[expose] def gp : Vec × Bool × Bool := (0, true, false)

@[expose] def gq : Vec × Bool × Bool := (0, false, true)

@[expose] def Assoc8 (α β γ : Vec) : Prop :=
  ∀ a ∈ [gp, gq], ∀ b ∈ [gp, gq], ∀ c ∈ [gp, gq],
    mulC PP QQ α β γ (mulC PP QQ α β γ a b) c = mulC PP QQ α β γ a (mulC PP QQ α β γ b c)

instance (α β γ : Vec) : Decidable (Assoc8 α β γ) := by unfold Assoc8; infer_instance

instance instDecEqVec : DecidableEq Vec := inferInstance

instance instDecEqCoords : DecidableEq (Vec × Bool × Bool) := inferInstance

instance instDecEqParams : DecidableEq (Vec × Vec × Vec) := inferInstance

@[expose] def allVec : List Vec :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3),
   (2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3)]

theorem mem_allVec (v : Vec) : v ∈ allVec := by
  obtain ⟨a, b⟩ := v
  revert a b
  decide

@[expose] def assoc8B (α β γ : Vec) : Bool :=
  [gp, gq].all fun a => [gp, gq].all fun b => [gp, gq].all fun c =>
    decide (mulC PP QQ α β γ (mulC PP QQ α β γ a b) c =
      mulC PP QQ α β γ a (mulC PP QQ α β γ b c))

theorem assoc8B_iff (α β γ : Vec) : assoc8B α β γ = true ↔ Assoc8 α β γ := by
  simp [assoc8B, Assoc8]

@[expose] def valid64 : List (Vec × Vec × Vec) :=
  [((0, 0), (0, 0), (0, 0)),
   ((0, 0), (0, 0), (0, 2)),
   ((0, 0), (0, 0), (2, 0)),
   ((0, 0), (0, 0), (2, 2)),
   ((0, 0), (0, 2), (0, 0)),
   ((0, 0), (0, 2), (0, 2)),
   ((0, 0), (0, 2), (2, 0)),
   ((0, 0), (0, 2), (2, 2)),
   ((0, 0), (2, 0), (0, 0)),
   ((0, 0), (2, 0), (0, 2)),
   ((0, 0), (2, 0), (2, 0)),
   ((0, 0), (2, 0), (2, 2)),
   ((0, 0), (2, 2), (0, 0)),
   ((0, 0), (2, 2), (0, 2)),
   ((0, 0), (2, 2), (2, 0)),
   ((0, 0), (2, 2), (2, 2)),
   ((0, 2), (0, 0), (0, 0)),
   ((0, 2), (0, 0), (0, 2)),
   ((0, 2), (0, 0), (2, 0)),
   ((0, 2), (0, 0), (2, 2)),
   ((0, 2), (0, 2), (0, 0)),
   ((0, 2), (0, 2), (0, 2)),
   ((0, 2), (0, 2), (2, 0)),
   ((0, 2), (0, 2), (2, 2)),
   ((0, 2), (2, 0), (0, 0)),
   ((0, 2), (2, 0), (0, 2)),
   ((0, 2), (2, 0), (2, 0)),
   ((0, 2), (2, 0), (2, 2)),
   ((0, 2), (2, 2), (0, 0)),
   ((0, 2), (2, 2), (0, 2)),
   ((0, 2), (2, 2), (2, 0)),
   ((0, 2), (2, 2), (2, 2)),
   ((2, 0), (0, 0), (0, 0)),
   ((2, 0), (0, 0), (0, 2)),
   ((2, 0), (0, 0), (2, 0)),
   ((2, 0), (0, 0), (2, 2)),
   ((2, 0), (0, 2), (0, 0)),
   ((2, 0), (0, 2), (0, 2)),
   ((2, 0), (0, 2), (2, 0)),
   ((2, 0), (0, 2), (2, 2)),
   ((2, 0), (2, 0), (0, 0)),
   ((2, 0), (2, 0), (0, 2)),
   ((2, 0), (2, 0), (2, 0)),
   ((2, 0), (2, 0), (2, 2)),
   ((2, 0), (2, 2), (0, 0)),
   ((2, 0), (2, 2), (0, 2)),
   ((2, 0), (2, 2), (2, 0)),
   ((2, 0), (2, 2), (2, 2)),
   ((2, 2), (0, 0), (0, 0)),
   ((2, 2), (0, 0), (0, 2)),
   ((2, 2), (0, 0), (2, 0)),
   ((2, 2), (0, 0), (2, 2)),
   ((2, 2), (0, 2), (0, 0)),
   ((2, 2), (0, 2), (0, 2)),
   ((2, 2), (0, 2), (2, 0)),
   ((2, 2), (0, 2), (2, 2)),
   ((2, 2), (2, 0), (0, 0)),
   ((2, 2), (2, 0), (0, 2)),
   ((2, 2), (2, 0), (2, 0)),
   ((2, 2), (2, 0), (2, 2)),
   ((2, 2), (2, 2), (0, 0)),
   ((2, 2), (2, 2), (0, 2)),
   ((2, 2), (2, 2), (2, 0)),
   ((2, 2), (2, 2), (2, 2))]

@[expose] def S16 : List (Vec × Vec × Vec) :=
  [((0, 0), (0, 0), (0, 0)),
   ((0, 0), (0, 0), (2, 0)),
   ((0, 0), (0, 2), (0, 2)),
   ((0, 0), (0, 2), (2, 2)),
   ((0, 2), (2, 0), (0, 0)),
   ((0, 2), (2, 0), (2, 0)),
   ((0, 2), (2, 2), (0, 2)),
   ((0, 2), (2, 2), (2, 2)),
   ((2, 0), (2, 0), (0, 2)),
   ((2, 0), (2, 0), (2, 2)),
   ((2, 0), (2, 2), (0, 0)),
   ((2, 0), (2, 2), (2, 0)),
   ((2, 2), (0, 0), (0, 2)),
   ((2, 2), (0, 0), (2, 2)),
   ((2, 2), (0, 2), (0, 0)),
   ((2, 2), (0, 2), (2, 0))]

theorem assoc8_validB : (allVec.all fun α => allVec.all fun β => allVec.all fun γ =>
    !assoc8B α β γ || valid64.contains (α, β, γ)) = true := by
  decide +kernel

theorem assoc8_valid (α β γ : Vec) (h : Assoc8 α β γ) : (α, β, γ) ∈ valid64 := by
  have h1 := assoc8_validB
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h1
  have h2 := h1 α (mem_allVec α) β (mem_allVec β) γ (mem_allVec γ)
  rcases h2 with h2 | h2
  · exact absurd ((assoc8B_iff α β γ).mpr h) (by simp [h2])
  · simpa using h2

@[expose] def ActP (ξ : M4) (i j : Bool) : Prop :=
  ∀ w, Mop PP QQ i j (ξ.act w) = ξ.act (Pm.act w)

@[expose] def ActQ (ξ : M4) (i j : Bool) : Prop :=
  ∀ w, Mop PP QQ i j (ξ.act w) = ξ.act (Qm.act w)

@[expose] def SqEq (π : Vec × Vec × Vec) (u : Vec × Bool × Bool) (t : Vec) : Prop :=
  mulC PP QQ π.1 π.2.1 π.2.2 u u = (t, false, false)

@[expose] def CommEq (π : Vec × Vec × Vec) (u₁ u₂ : Vec × Bool × Bool) (t : Vec) : Prop :=
  mulC PP QQ π.1 π.2.1 π.2.2 u₂ u₁ =
    mulC PP QQ π.1 π.2.1 π.2.2 (mulC PP QQ π.1 π.2.1 π.2.2 u₁ u₂) (t, false, false)

@[expose] def actPB (ξ : M4) (i j : Bool) : Bool :=
  allVec.all fun w => decide (Mop PP QQ i j (ξ.act w) = ξ.act (Pm.act w))

@[expose] def actQB (ξ : M4) (i j : Bool) : Bool :=
  allVec.all fun w => decide (Mop PP QQ i j (ξ.act w) = ξ.act (Qm.act w))

@[expose] def sqEqB (π : Vec × Vec × Vec) (u : Vec × Bool × Bool) (t : Vec) : Bool :=
  decide (mulC PP QQ π.1 π.2.1 π.2.2 u u = (t, false, false))

@[expose] def commEqB (π : Vec × Vec × Vec) (u₁ u₂ : Vec × Bool × Bool) (t : Vec) : Bool :=
  decide (mulC PP QQ π.1 π.2.1 π.2.2 u₂ u₁ =
    mulC PP QQ π.1 π.2.1 π.2.2 (mulC PP QQ π.1 π.2.1 π.2.2 u₁ u₂) (t, false, false))

theorem actPB_iff (ξ : M4) (i j : Bool) : actPB ξ i j = true ↔ ActP ξ i j := by
  simp [actPB, ActP, List.all_eq_true, mem_allVec]

theorem actQB_iff (ξ : M4) (i j : Bool) : actQB ξ i j = true ↔ ActQ ξ i j := by
  simp [actQB, ActQ, List.all_eq_true, mem_allVec]

theorem sqEqB_iff (π : Vec × Vec × Vec) (u : Vec × Bool × Bool) (t : Vec) :
    sqEqB π u t = true ↔ SqEq π u t := by
  simp [sqEqB, SqEq]

theorem commEqB_iff (π : Vec × Vec × Vec) (u₁ u₂ : Vec × Bool × Bool) (t : Vec) :
    commEqB π u₁ u₂ t = true ↔ CommEq π u₁ u₂ t := by
  simp [commEqB, CommEq]

theorem x_classifyB : (valid64.all fun π => ord3list.all fun ξ =>
    [false, true].all fun i₁ => [false, true].all fun j₁ =>
    !actPB ξ i₁ j₁ || allVec.all fun a₁ =>
    !sqEqB π (a₁, i₁, j₁) (ξ.act π.1) || [false, true].all fun i₂ => [false, true].all fun j₂ =>
    !actQB ξ i₂ j₂ || allVec.all fun a₂ =>
    !sqEqB π (a₂, i₂, j₂) (ξ.act π.2.1) || !commEqB π (a₁, i₁, j₁) (a₂, i₂, j₂) (ξ.act π.2.2) ||
      S16.contains π) = true := by
  decide +kernel

theorem x_classify (π : Vec × Vec × Vec) (hπ : π ∈ valid64) (ξ : M4) (hξ : ξ ∈ ord3list)
    (i₁ j₁ : Bool) (h1 : ActP ξ i₁ j₁) (a₁ : Vec) (h2 : SqEq π (a₁, i₁, j₁) (ξ.act π.1))
    (i₂ j₂ : Bool) (h3 : ActQ ξ i₂ j₂) (a₂ : Vec) (h4 : SqEq π (a₂, i₂, j₂) (ξ.act π.2.1))
    (h5 : CommEq π (a₁, i₁, j₁) (a₂, i₂, j₂) (ξ.act π.2.2)) : π ∈ S16 := by
  have h := x_classifyB
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  have hb : ∀ b : Bool, b ∈ [false, true] := by decide
  have := h π hπ ξ hξ i₁ (hb i₁) j₁ (hb j₁)
  rcases this with this | this
  · exact absurd ((actPB_iff ξ i₁ j₁).mpr h1) (by simp [this])
  have := this a₁ (mem_allVec a₁)
  rcases this with this | this
  · exact absurd ((sqEqB_iff _ _ _).mpr h2) (by simp [this])
  have := this i₂ (hb i₂) j₂ (hb j₂)
  rcases this with this | this
  · exact absurd ((actQB_iff ξ i₂ j₂).mpr h3) (by simp [this])
  have := this a₂ (mem_allVec a₂)
  rcases this with (this | this) | this
  · exact absurd ((sqEqB_iff _ _ _).mpr h4) (by simp [this])
  · exact absurd ((commEqB_iff _ _ _ _).mpr h5) (by simp [this])
  · simpa using this

end L23

end CFSG.GH74.GLS.Bg.TwoGroups

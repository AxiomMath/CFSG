module

public import CFSG.ClassicalInvolution.Q3.TL4OddProp
public import CFSG.ClassicalInvolution.Asc77.AscT8T1
public import CFSG.ClassicalInvolution.Q3.TL4OddDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Balance.Bootstrap (ShareFour)
open CFSG.ClassicalInvolution.Asc77.T8T (TriFrame)

section Family

variable {G : Type} [Group G]

@[expose] def triFrameSet (Ω : Set (Subgroup G)) : Set (Subgroup G) :=
  {B | ∃ (M : Fin 3 → Subgroup G) (x : Fin 3 → G) (P : Fin 3 → Subgroup G),
    TriFrame Ω M x P ∧ x 2 ∉ Subgroup.closure ({x 0, x 1} : Set G) ∧
      B = Subgroup.closure ({x 0, x 1, x 2} : Set G)}

@[expose] def memberInvSet (Ω : Set (Subgroup G)) : Set G :=
  {a | ∃ M ∈ Ω, IsUniqueInvolution M a}

theorem triFrame_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {M : Fin 3 → Subgroup G}
    {x : Fin 3 → G} {P : Fin 3 → Subgroup G} (hF : TriFrame Ω M x P) (g : G) :
    TriFrame Ω (fun i => conjSub g (M i)) (fun i => g * x i * g⁻¹)
      (fun i => conjSub g (P i)) where
  mem i := hΩ g _ (hF.mem i)
  inv i := (hF.inv i).conj g
  nbr i j hij := omegaNbr_conj hΩ (hF.nbr i j hij) g
  syl i := (hF.syl i).conj g
  cent i j := by
    intro y hy
    rw [mem_conjSub_iff] at hy
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hF.cent i j hy)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * (g * x j * g⁻¹) = g * ((g⁻¹ * y * g) * x j) * g⁻¹ := by group
      _ = g * (x j * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * x j * g⁻¹ * y := by group

theorem map_conj_closure_three (g a b c : G) :
    (Subgroup.closure ({a, b, c} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.closure ({g * a * g⁻¹, g * b * g⁻¹, g * c * g⁻¹} : Set G) := by
  rw [MonoidHom.map_closure]
  congr 1
  simp [Set.image_insert_eq, Set.image_singleton]

theorem map_conj_closure_two (g a b : G) :
    (Subgroup.closure ({a, b} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.closure ({g * a * g⁻¹, g * b * g⁻¹} : Set G) := by
  rw [MonoidHom.map_closure]
  congr 1
  simp [Set.image_insert_eq, Set.image_singleton]

theorem triFrameSet_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {B : Subgroup G}
    (hB : B ∈ triFrameSet Ω) (g : G) : B.map (MulAut.conj g).toMonoidHom ∈ triFrameSet Ω := by
  obtain ⟨M, x, P, hF, hx2, rfl⟩ := hB
  refine ⟨_, _, _, triFrame_conj hΩ hF g, fun h => hx2 ?_, map_conj_closure_three g _ _ _⟩
  have h' : g * x 2 * g⁻¹ ∈
      (Subgroup.closure ({x 0, x 1} : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [map_conj_closure_two]
    exact h
  obtain ⟨y, hy, hyx⟩ := h'
  have hyx' : y = x 2 := by
    have h1 : g * y * g⁻¹ = g * x 2 * g⁻¹ := hyx
    simpa using h1
  rwa [← hyx']

theorem mem_triFrame_closure {x : Fin 3 → G} (i : Fin 3) :
    x i ∈ Subgroup.closure ({x 0, x 1, x 2} : Set G) :=
  Subgroup.subset_closure (by fin_cases i <;> simp)

end Family

section Graph

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {𝒯 : Set (Subgroup G)}

theorem mem_of_reflTransGen_dAdj {M N : Subgroup G} (hM : M ∈ Ω)
    (h : Relation.ReflTransGen (fun X Y : Subgroup G => Y ∈ Ω ∧ Disconnected.dAdj Ω X Y) M N) :
    N ∈ Ω := by
  induction h with
  | refl => exact hM
  | tail _ hstep _ => exact hstep.1

end Graph

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem alphaOf_eq_bot_of_frames (hL : TightLargeHypR r n Y R S t) {𝒯 : Set (Subgroup Y)}
    (ha : FramesAtEdges (CoreAssembly.conjClass (tightCore R)) (tightCore R) t 𝒯)
    (hb : FramesHyp51 𝒯) (hc : FramesConnected 𝒯) :
    ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
      IsUniqueInvolution J u → alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥ := by
  intro J hJ u hu
  obtain ⟨hinv, hconn⟩ := hc
  obtain ⟨B, hB, hle⟩ := ha J hJ u hu
  have hbal : ∀ A ∈ 𝒯, Bootstrap.RankThreeBalance A := fun A hA => lemma52 Y A (hb A hA)
  have hO : componentClassificationOddCore Y = ⊥ := hL.cls.2.2
  have hF : Subgroup.closure ({t, u} : Set Y) ∈ signalizerFunctorEk 2 2 B :=
    ⟨hle, by rw [card_closure_edge_eq_four hL.datum hJ hu]; norm_num⟩
  exact alphaOf_eq_bot_of_alphaCore_eq_bot
    (Theorem5.alphaCore_eq_bot_of_connected_frames hO hinv hbal hconn B hB _ hF)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4

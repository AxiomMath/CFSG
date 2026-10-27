module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.RankThree.PartOne.CTP.FusionSound

public section

namespace CFSG.AGLEmbedding.MonsterThree

open CFSG.Open CFSG.RankThree.PartOne.CTP.Fus

structure Datum (X : Type*) [Group X] (ι : Type*) where
  y : ι → X
  q : Fin 3 → X
  w : Fin 3 → X
  gen : Subgroup.closure (Set.range y) = ⊤
  comm : ∀ i j, Commute (q i) (q j)
  ord : ∀ j, orderOf (q j) = 3
  inv : ∀ j, w j * q j * (w j)⁻¹ = (q j)⁻¹
  fix : ∀ i j, i ≠ j → w i * q j * (w i)⁻¹ = q j
  act : ∀ i, ∃ m : Fin 3, ∀ j, j ≠ m →
    y i * q j * (y i)⁻¹ = q j ∨ y i * q j * (y i)⁻¹ = (q j)⁻¹

namespace Datum

variable {X : Type*} [Group X] {ι : Type*}

private def E (D : Datum X ι) : Subgroup X := Subgroup.closure (Set.range D.q)

private def pair (D : Datum X ι) (m : Fin 3) : Subgroup X :=
  Subgroup.closure (Set.range (D.q ∘ m.succAbove))

private theorem q_mem (D : Datum X ι) (j : Fin 3) : D.q j ∈ D.E := Subgroup.subset_closure ⟨j, rfl⟩

private theorem q_ne_one (D : Datum X ι) (j : Fin 3) : D.q j ≠ 1 := fun h => by
  have := D.ord j
  rw [h, orderOf_one] at this
  omega

private theorem pair_le (D : Datum X ι) (m : Fin 3) : D.pair m ≤ D.E :=
  Subgroup.closure_mono (by rintro _ ⟨a, rfl⟩; exact ⟨m.succAbove a, rfl⟩)

private theorem torus (D : Datum X ι) :
    IsElemAbelian 3 D.E ∧ Nat.card D.E = 3 ^ 3 ∧ LiftsComm D.E := by
  have h := liftsComm_of_inverters D.q D.w D.comm D.ord D.inv D.fix
  rw [Fintype.card_fin] at h
  exact h

private theorem card_pair (D : Datum X ι) (m : Fin 3) : Nat.card (D.pair m) = 3 ^ 2 := by
  have := (liftsComm_of_inverters (L := X) (ι := Fin 2) (D.q ∘ m.succAbove)
    (D.w ∘ m.succAbove) (fun a b => D.comm _ _) (fun a => D.ord _) (fun a => D.inv _)
    (fun a b hab => D.fix _ _ (fun h => hab (Fin.succAbove_right_injective h)))).2.1
  rw [Fintype.card_fin] at this
  exact this

private theorem inv_conj_cases {y t : X} (h : y * t * y⁻¹ = t ∨ y * t * y⁻¹ = t⁻¹) :
    y⁻¹ * t * y = t ∨ y⁻¹ * t * y = t⁻¹ := by
  rcases h with h | h
  · left
    calc y⁻¹ * t * y = y⁻¹ * (y * t * y⁻¹) * y := by rw [h]
      _ = t := by group
  · right
    have h1 : y⁻¹ * t⁻¹ * y = t := by
      calc y⁻¹ * t⁻¹ * y = y⁻¹ * (y * t * y⁻¹) * y := by rw [h]
        _ = t := by group
    calc y⁻¹ * t * y = (y⁻¹ * t⁻¹ * y)⁻¹ := by group
      _ = t⁻¹ := by rw [h1]

private theorem mem_normalizer_pair (D : Datum X ι) {g : X} {m : Fin 3}
    (hg : ∀ j, j ≠ m → g * D.q j * g⁻¹ = D.q j ∨ g * D.q j * g⁻¹ = (D.q j)⁻¹) :
    g ∈ Subgroup.normalizer (D.pair m : Set X) := by
  have key : ∀ a : Fin 2, ∀ u : X, (u = D.q (m.succAbove a) ∨ u = (D.q (m.succAbove a))⁻¹) →
      u ∈ D.pair m := by
    intro a u hu
    have hmem : D.q (m.succAbove a) ∈ D.pair m := Subgroup.subset_closure ⟨a, rfl⟩
    rcases hu with rfl | rfl
    · exact hmem
    · exact Subgroup.inv_mem _ hmem
  refine mem_normalizer_closure_of_conj_mem_inv ?_ ?_
  · rintro _ ⟨a, rfl⟩
    exact key a _ (hg _ (Fin.succAbove_ne m a))
  · rintro _ ⟨a, rfl⟩
    exact key a _ (inv_conj_cases (hg _ (Fin.succAbove_ne m a)))

theorem liftableNormalizerGen (D : Datum X ι) : LiftableNormalizerGen X := by
  obtain ⟨hEab, hEcard, hElift⟩ := D.torus
  refine ⟨D.E, {F | ∃ m, F = D.pair m}, hEab.2, ?_, ⟨_, 0, rfl⟩, ?_, hElift, ?_⟩
  · rw [hEcard]
  · rintro F ⟨m, rfl⟩
    exact ⟨D.pair_le m, (D.card_pair m).ge⟩
  · refine le_trans (le_of_eq D.gen.symm) ?_
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨m, hm⟩ := D.act i
    exact (le_iSup₂ (f := fun F (_ : F ∈ {F | ∃ m, F = D.pair m}) =>
      Subgroup.normalizer (F : Set X)) (D.pair m) ⟨m, rfl⟩) (D.mem_normalizer_pair hm)

theorem fusionGenerationOf (D : Datum X ι) : FusionGenerationOf X 3 := by
  obtain ⟨hEab, -, -⟩ := D.torus
  refine ⟨D.E, Set.range D.y, fun g => ⟨1, Subtype.ext (by simpa using hEab.2 g g.2)⟩, ?_,
    D.gen, ?_⟩
  · intro h
    have h0 := D.q_mem 0
    rw [h, Subgroup.mem_bot] at h0
    exact D.q_ne_one 0 h0
  · rintro _ ⟨i, rfl⟩
    obtain ⟨m, hm⟩ := D.act i
    refine ⟨D.q (m.succAbove 0), D.q_mem _, D.q_ne_one _, ?_⟩
    rcases hm _ (Fin.succAbove_ne m 0) with h | h
    · rw [h]
      exact D.q_mem _
    · rw [h]
      exact Subgroup.inv_mem _ (D.q_mem _)

end Datum

end CFSG.AGLEmbedding.MonsterThree

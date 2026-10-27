module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.OddLift
public import CFSG.RankThree.PartOne.CTP.FusionDefs

public section

namespace CFSG.AGLEmbedding.Norton.MON5_7

open CFSG.Open CFSG.RankThree.PartOne.CTP.Fus CFSG.RankThree.Classical2 CFSG.RankThree.CentralCover
  CFSG.AGLEmbedding

structure TorusDatumP (p : ℕ) (X : Type*) [Group X] (ι : Type*) where
  y : ι → X
  q : Fin 3 → X
  w : Fin 3 → X
  gen : Subgroup.closure (Set.range y) = ⊤
  comm : ∀ i j, Commute (q i) (q j)
  ord : ∀ j, orderOf (q j) = p
  inv : ∀ j, w j * q j * (w j)⁻¹ = (q j)⁻¹
  fix : ∀ i j, i ≠ j → w i * q j * (w i)⁻¹ = q j
  act : ∀ i, ∃ m : Fin 3, ∀ j, j ≠ m →
    y i * q j * (y i)⁻¹ = q j ∨ y i * q j * (y i)⁻¹ = (q j)⁻¹

namespace TorusDatumP

variable {p : ℕ} {X : Type} [Group X] {ι : Type*}

private def E (D : TorusDatumP p X ι) : Subgroup X := Subgroup.closure (Set.range D.q)

private def pair (D : TorusDatumP p X ι) (m : Fin 3) : Subgroup X :=
  Subgroup.closure (Set.range (D.q ∘ m.succAbove))

private theorem q_mem (D : TorusDatumP p X ι) (j : Fin 3) : D.q j ∈ D.E :=
  Subgroup.subset_closure ⟨j, rfl⟩

private theorem pair_le (D : TorusDatumP p X ι) (m : Fin 3) : D.pair m ≤ D.E :=
  Subgroup.closure_mono (by rintro _ ⟨a, rfl⟩; exact ⟨m.succAbove a, rfl⟩)

private theorem torus (D : TorusDatumP p X ι) (hp : p.Prime) (hp2 : p ≠ 2) :
    IsElemAbelian p D.E ∧ Nat.card D.E = p ^ 3 ∧ LiftsComm D.E := by
  have h := liftsComm_of_invertersP hp hp2 D.q D.w D.comm D.ord D.inv D.fix
  rw [Fintype.card_fin] at h
  exact h

private theorem pair_elem (D : TorusDatumP p X ι) (hp : p.Prime) (hp2 : p ≠ 2) (m : Fin 3) :
    IsElemAbelian p (D.pair m) ∧ Nat.card (D.pair m) = p ^ 2 := by
  have h := liftsComm_of_invertersP (L := X) (ι := Fin 2) hp hp2 (D.q ∘ m.succAbove)
    (D.w ∘ m.succAbove) (fun a b => D.comm _ _) (fun a => D.ord _) (fun a => D.inv _)
    (fun a b hab => D.fix _ _ (fun h => hab (Fin.succAbove_right_injective h)))
  rw [Fintype.card_fin] at h
  exact ⟨h.1, h.2.1⟩

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

private theorem mem_normalizer_pair (D : TorusDatumP p X ι) {g : X} {m : Fin 3}
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

private theorem E_le_pair_sup (D : TorusDatumP p X ι) (m : Fin 3) :
    D.E ≤ D.pair m ⊔ (D.E ⊓ Subgroup.centralizer (D.pair m : Set X)) := by
  have hpc : ∀ y ∈ D.pair m, y * D.q m = D.q m * y := by
    intro y hy
    have hle : D.pair m ≤ Subgroup.centralizer {D.q m} :=
      (Subgroup.closure_le _).2 fun z hz => by
        obtain ⟨a, rfl⟩ := hz
        exact Subgroup.mem_centralizer_singleton_iff.2 (D.comm _ _).eq
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
  have hqm : D.q m ∈ Subgroup.centralizer (D.pair m : Set X) :=
    Subgroup.mem_centralizer_iff.2 fun y hy => (hpc y hy)
  unfold E
  rw [Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  by_cases hjm : j = m
  · rw [hjm]
    exact Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨D.q_mem m, hqm⟩)
  · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hjm
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨a, rfl⟩)

theorem liftableNormalizerGenP (D : TorusDatumP p X ι) (hp : p.Prime) (hp2 : p ≠ 2) :
    LiftableNormalizerGenP p X := by
  obtain ⟨hEab, hEcard, hElift⟩ := D.torus hp hp2
  refine ⟨D.E, {F | ∃ m, F = D.pair m}, hEab.2, ?_, ⟨_, 0, rfl⟩, ?_, hElift, ?_⟩
  · rw [hEcard]
  · rintro F ⟨m, rfl⟩
    exact ⟨D.pair_le m, (D.pair_elem hp hp2 m).2.ge⟩
  · refine le_trans (le_of_eq D.gen.symm) ?_
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨m, hm⟩ := D.act i
    exact (le_iSup₂ (f := fun F (_ : F ∈ {F | ∃ m, F = D.pair m}) =>
      Subgroup.normalizer (F : Set X)) (D.pair m) ⟨m, rfl⟩) (D.mem_normalizer_pair hm)

theorem tcGenDatum [Finite X] (D : TorusDatumP p X ι) (hp : p.Prime) (hp2 : p ≠ 2) :
    TCGenDatum X p := by
  obtain ⟨hEab, hEcard, -⟩ := D.torus hp hp2
  refine ⟨3, fun m => D.pair m, D.E, Set.range D.y, ?_, fun m => D.pair_le m, fun m => ?_,
    D.gen, ?_⟩
  · exact fun g => ⟨1, Subtype.ext (by simpa using hEab.2 g g.2)⟩
  · obtain ⟨hab, hcard⟩ := D.pair_elem hp hp2 m
    exact ⟨SectionRank.le_pRank hp.one_lt (le_refl _) hab hcard,
      SectionRank.le_pRank hp.one_lt (D.E_le_pair_sup m) hEab hEcard⟩
  · rintro _ ⟨i, rfl⟩
    obtain ⟨m, hm⟩ := D.act i
    exact ⟨m, D.mem_normalizer_pair hm⟩

def ofMulEquiv {X' : Type*} [Group X'] (e : X ≃* X') (D : TorusDatumP p X ι) :
    TorusDatumP p X' ι where
  y := fun i => e (D.y i)
  q := fun j => e (D.q j)
  w := fun j => e (D.w j)
  gen := by
    have h1 : Set.range (fun i => e (D.y i)) = e.toMonoidHom '' Set.range D.y := by
      rw [← Set.range_comp]
      rfl
    rw [h1, ← MonoidHom.map_closure, D.gen]
    exact Subgroup.map_top_of_surjective e.toMonoidHom e.surjective
  comm := fun i j => (D.comm i j).map e
  ord := fun j => (orderOf_injective e.toMonoidHom e.injective _).trans (D.ord j)
  inv := fun j => by simpa only [map_mul, map_inv] using congrArg e (D.inv j)
  fix := fun i j hij => by simpa only [map_mul, map_inv] using congrArg e (D.fix i j hij)
  act := fun i => by
    obtain ⟨m, hm⟩ := D.act i
    refine ⟨m, fun j hj => ?_⟩
    rcases hm j hj with h | h
    · exact Or.inl (by simpa only [map_mul, map_inv] using congrArg e h)
    · exact Or.inr (by simpa only [map_mul, map_inv] using congrArg e h)

end TorusDatumP

end CFSG.AGLEmbedding.Norton.MON5_7

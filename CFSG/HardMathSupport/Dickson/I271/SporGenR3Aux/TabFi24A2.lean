module

public import Certificates.Certificate17352
public import CFSG.ClassicalInvolution.Q3.Q3ZMat
public import CFSG.ClassicalInvolution.WeakCT.Standard
public import CFSG.GH74.Generic.S1.KL3SL3

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.CosetTable CFSG.ClassicalInvolution.Q3.Q3Z CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

theorem b12_eq_closure_a2 :
    B12 (ZMod 3) = Subgroup.closure ({a2Mat 0, a2Mat 1} : Set SL(3, ZMod 3)) := by
  unfold B12
  rw [MonoidHom.range_eq_map, ← closure_xp_xm, MonoidHom.map_closure, Set.image_pair]
  rfl

theorem b23_eq_closure_a2 :
    B23 (ZMod 3) = Subgroup.closure ({a2Mat 4, a2Mat 5} : Set SL(3, ZMod 3)) := by
  unfold B23
  rw [MonoidHom.range_eq_map, ← closure_xp_xm, MonoidHom.map_closure, Set.image_pair]
  rfl

theorem a2_closure_eq_top : Subgroup.closure (Set.range a2Mat) = ⊤ := by
  rw [eq_top_iff, ← B12_sup_B23 (K := ZMod 3), b12_eq_closure_a2, b23_eq_closure_a2]
  refine sup_le (Subgroup.closure_mono ?_) (Subgroup.closure_mono ?_)
  · rintro _ (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · rintro _ (rfl | rfl)
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩

theorem pg_a2_card_le :
    Finite (PG 6 a2Words) ∧ Nat.card (PG 6 a2Words) ≤ 5616 :=
  Certificates.certificate17352

theorem exists_mulEquiv_a2 :
    ∃ e : PG 6 a2Words ≃* SL(3, ZMod 3), ∀ i, e (PresentedGroup.of i) = a2Mat i := by
  obtain ⟨φ, hφ⟩ := exists_hom_of_relsHold a2Words a2Mat a2_relsHold
  obtain ⟨hfin, hcard⟩ := pg_a2_card_le
  haveI := hfin
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← a2_closure_eq_top, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, hφ i⟩
  have hSL : Nat.card SL(3, ZMod 3) = 5616 :=
    CFSG.GH74.Generic.S1.kl3_card_sl3 (F := ZMod 3) (by simp)
  have hbij : Function.Bijective φ := hsurj.bijective_of_nat_card_le (by rw [hSL]; exact hcard)
  exact ⟨MulEquiv.ofBijective φ hbij, hφ⟩

theorem a2_universal {G : Type*} [Group G] (g : Fin 6 → G)
    (hg : RelsHold g a2Words) : ∃ ψ : SL(3, ZMod 3) →* G, ∀ i, ψ (a2Mat i) = g i := by
  obtain ⟨e, he⟩ := exists_mulEquiv_a2
  obtain ⟨f, hf⟩ := exists_hom_of_relsHold a2Words g hg
  refine ⟨f.comp e.symm.toMonoidHom, fun i => ?_⟩
  rw [MonoidHom.comp_apply]
  have : e.symm (a2Mat i) = PresentedGroup.of i := by rw [← he i]; exact e.symm_apply_apply _
  change f (e.symm (a2Mat i)) = g i
  rw [this, hf]

theorem linearBlockStandardPair_of_relsHold {X : Type}
    [Group X] (g : Fin 6 → X) (hg : RelsHold g a2Words) (hne : g 0 ≠ 1) :
    LinearBlockStandardPair (ZMod 3) (Subgroup.closure (Set.range g))
      (Subgroup.closure {g 0, g 1}) (Subgroup.closure {g 4, g 5}) := by
  obtain ⟨ψ, hψ⟩ := a2_universal g hg
  have hid : (MulAut.conj ((1 : SL(3, ZMod 3))⁻¹)).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  have hmap : ∀ s : Set SL(3, ZMod 3), Subgroup.map ψ (Subgroup.closure s) =
      Subgroup.closure (ψ '' s) := fun s => MonoidHom.map_closure ψ s
  refine ⟨ψ, 1, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
  · have himg : ψ '' Set.range a2Mat = Set.range g := by
      rw [← Set.range_comp]
      congr 1
      funext i
      exact hψ i
    rw [MonoidHom.range_eq_map, ← a2_closure_eq_top, hmap, himg]
  · have hnt : ψ.ker ≠ ⊤ := by
      intro h
      apply hne
      rw [← hψ 0]
      exact MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top (a2Mat 0))
    haveI := CFSG.GH74.Generic.S1.kl3_isSimple_sl3 (F := ZMod 3) (by simp)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · rw [h]; exact bot_le
    · exact absurd h hnt
  · rw [hid, Subgroup.map_id, b12_eq_closure_a2, hmap, Set.image_pair, hψ, hψ]
  · rw [hid, Subgroup.map_id, b23_eq_closure_a2, hmap, Set.image_pair, hψ, hψ]

@[expose] def edgeSix {X : Type*} [Group X] (x y x' y' : X) : Fin 6 → X :=
  ![x, y, x⁻¹ * x'⁻¹ * x * x', (y⁻¹ * y'⁻¹ * y * y')⁻¹, x', y']

end CFSG.HardMathSupport.Dickson.I271

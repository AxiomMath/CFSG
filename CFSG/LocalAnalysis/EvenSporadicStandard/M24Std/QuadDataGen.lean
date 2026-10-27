module

public import Certificates.Certificate24847

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

variable {G : Type} [Group G] {L A : Subgroup G}

theorem qdIota_elt_mem (ι : S24 →* G) (K : Subgroup G) (B : List S24)
    (hB : ∀ j, ι (B.getD j 1) ∈ K) (n : ℕ) : ι (m24Elt B n) ∈ K := by
  unfold m24Elt
  suffices H : ∀ (l : List ℕ) (acc : S24), ι acc ∈ K →
      ι (l.foldl (fun acc k => if n.testBit k then acc * B.getD k 1 else acc) acc) ∈ K from
    H _ 1 (by rw [map_one]; exact K.one_mem)
  intro l
  induction l with
  | nil => intro acc h; simpa using h
  | cons k l ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    split_ifs
    · rw [map_mul]
      exact K.mul_mem h (hB k)
    · exact h

theorem gen45W_of_type (h : SextetType L A) :
    ∃ a₁ ∈ A, a₁ ≠ 1 ∧
      Subgroup.closure {x : G | x ∈ A ∧ x ∈ egOrb L A a₁ ∧ a₁ * x ∈ egOrb L A a₁} = A := by
  obtain ⟨hAL, e, he⟩ := h
  obtain ⟨hgs, hA1, hA1l, hX, hcov⟩ := Certificates.certificate24847
  have hnorm : ∀ g ∈ qdGens, QdNorm g := fun g hg => (hgs g hg).norm
  have horb : ∀ y ∈ qdReach qdGens qdA1 qdDepth, qdIota e y ∈ egOrb L A (qdIota e qdA1) := by
    intro y hy
    obtain ⟨m, hm, hma⟩ := exists_norm_of_mem_qdReach hnorm hy
    exact ⟨qdIota e m, qdIota_mem_egNL e hAL he hm, by rw [qdIota_conj, hma]⟩
  refine ⟨qdIota e qdA1, (qdIota_mem_A e he qdA1).2 hA1l, fun h1 => hA1 ?_, ?_⟩
  · exact qdIota_injective e (by rw [h1, map_one])
  · apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      exact hx.1
    · intro y hy
      obtain ⟨s, hs, rfl⟩ := (qdMem_A_iff e hAL he y).1 hy
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 (hcov s hs)
      refine qdIota_elt_mem (qdIota e) _ qdX45 (fun j => ?_) k
      by_cases hj : j < qdX45.length
      · have hx : qdX45.getD j 1 ∈ qdX45 := by
          rw [List.getD_eq_getElem _ _ hj]
          exact List.getElem_mem hj
        obtain ⟨hxl, hx1, hx2⟩ := hX _ hx
        refine Subgroup.subset_closure ⟨(qdIota_mem_A e he _).2 hxl, horb _ hx1, ?_⟩
        rw [← map_mul]
        exact horb _ hx2
      · rw [List.getD_eq_default _ _ (not_lt.1 hj), map_one]
        exact one_mem _

end CFSG.EvenSporadicStandard.M24Std

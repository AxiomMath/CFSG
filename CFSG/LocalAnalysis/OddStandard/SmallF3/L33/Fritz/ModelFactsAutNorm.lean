module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsAutElems
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsNorm

public section

namespace CFSG.OddStandard.SmallF3.L33

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Sporadic.Schreier CFSG.Blueprint

namespace IsL33Model

variable {L : Type} [Group L] {M : AutModel L (Equiv.Perm (Fin 26))}

private theorem conj_mem_closure_of_le (S : Set (MulAut L)) (K : Subgroup (Equiv.Perm (Fin 26)))
    (hK : ∀ g ∈ S, M.ι g ∈ K) {n : MulAut L}
    (hn : n ∈ Subgroup.normalizer (Subgroup.closure S)) {g : MulAut L}
    (hg : g ∈ Subgroup.closure S) :
    M.ι n * M.ι g * (M.ι n)⁻¹ ∈ K := by
  have hle : Subgroup.closure S ≤ K.comap M.ι :=
    (Subgroup.closure_le (K.comap M.ι)).2 fun g hgS => hK g hgS
  have h1 : n * g * n⁻¹ ∈ Subgroup.closure S :=
    (Subgroup.mem_normalizer_iff.1 hn g).1 hg
  have h2 : M.ι (n * g * n⁻¹) ∈ K := hle h1
  simpa only [map_mul, map_inv] using h2

variable (h : IsL33Model M)

theorem elK_fixed : ∀ n ∈ Subgroup.normalizer
    (Subgroup.closure ({MulAut.conj (h.elX ^ 4), MulAut.conj h.elY, h.elK} : Set (MulAut L)) :
      Set (MulAut L)), n * h.elK * n⁻¹ = h.elK := by
  intro n hn
  have hιZ : M.ι (MulAut.conj (h.elX ^ 4)) = modelZ := by
    simp only [map_pow, h.ι_conj, h.e_elX, modelZ]
  have hιY : M.ι (MulAut.conj h.elY) = modelY := by
    simp only [h.ι_conj, h.e_elY]
  have hιK : M.ι h.elK = modelK := h.ι_elK
  have hK : ∀ g ∈ ({MulAut.conj (h.elX ^ 4), MulAut.conj h.elY, h.elK} : Set (MulAut L)),
      M.ι g ∈ Subgroup.closure ({modelZ, modelY, modelK} : Set (Equiv.Perm (Fin 26))) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · rw [hιZ]; exact Subgroup.subset_closure (Set.mem_insert_iff.2 (Or.inl rfl))
    · rw [hιY]
      exact Subgroup.subset_closure
        (Set.mem_insert_iff.2 (Or.inr (Set.mem_insert_iff.2 (Or.inl rfl))))
    · rw [hιK]
      exact Subgroup.subset_closure
        (Set.mem_insert_iff.2 (Or.inr (Set.mem_insert_iff.2
          (Or.inr (Set.mem_singleton_iff.2 rfl)))))
  have hz : M.ι n * modelZ * (M.ι n)⁻¹ ∈
      Subgroup.closure ({modelZ, modelY, modelK} : Set (Equiv.Perm (Fin 26))) := by
    simpa only [hιZ] using conj_mem_closure_of_le
      (S := ({MulAut.conj (h.elX ^ 4), MulAut.conj h.elY, h.elK} : Set (MulAut L)))
      (K := Subgroup.closure ({modelZ, modelY, modelK} : Set (Equiv.Perm (Fin 26))))
      hK hn (g := MulAut.conj (h.elX ^ 4))
      (Subgroup.subset_closure (Set.mem_insert_iff.2 (Or.inl rfl)))
  have hy : M.ι n * modelY * (M.ι n)⁻¹ ∈
      Subgroup.closure ({modelZ, modelY, modelK} : Set (Equiv.Perm (Fin 26))) := by
    simpa only [hιY] using conj_mem_closure_of_le
      (S := ({MulAut.conj (h.elX ^ 4), MulAut.conj h.elY, h.elK} : Set (MulAut L)))
      (K := Subgroup.closure ({modelZ, modelY, modelK} : Set (Equiv.Perm (Fin 26))))
      hK hn (g := MulAut.conj h.elY)
      (Subgroup.subset_closure
        (Set.mem_insert_iff.2 (Or.inr (Set.mem_insert_iff.2 (Or.inl rfl)))))
  have hk : M.ι n * modelK * (M.ι n)⁻¹ ∈
      Subgroup.closure ({modelZ, modelY, modelK} : Set (Equiv.Perm (Fin 26))) := by
    simpa only [hιK] using conj_mem_closure_of_le
      (S := ({MulAut.conj (h.elX ^ 4), MulAut.conj h.elY, h.elK} : Set (MulAut L)))
      (K := Subgroup.closure ({modelZ, modelY, modelK} : Set (Equiv.Perm (Fin 26))))
      hK hn (g := h.elK)
      (Subgroup.subset_closure (Set.mem_insert_iff.2 (Or.inr (Set.mem_insert_iff.2
        (Or.inr (Set.mem_singleton_iff.2 rfl))))))
  have hres : M.ι n * modelK * (M.ι n)⁻¹ = modelK :=
    model_norm_one (n := M.ι n) (h.A_eq ▸ M.ι_mem n) hz hy hk
  apply M.ι_injective
  simp only [map_mul, map_inv, hιK]
  exact hres

theorem elZK_fixed : ∀ n ∈ Subgroup.normalizer
    (Subgroup.closure
      ({MulAut.conj (h.elX ^ 4), MulAut.conj (h.elX ^ 2 * h.elY), h.elK} : Set (MulAut L)) :
      Set (MulAut L)), n * (MulAut.conj (h.elX ^ 4) * h.elK) * n⁻¹ =
        MulAut.conj (h.elX ^ 4) * h.elK := by
  intro n hn
  have hιZ : M.ι (MulAut.conj (h.elX ^ 4)) = modelZ := by
    simp only [map_pow, h.ι_conj, h.e_elX, modelZ]
  have hιW : M.ι (MulAut.conj (h.elX ^ 2 * h.elY)) = modelX ^ 2 * modelY := by
    simp only [map_mul, map_pow, h.ι_conj, h.e_elX, h.e_elY]
  have hιK : M.ι h.elK = modelK := h.ι_elK
  have hK : ∀ g ∈
      ({MulAut.conj (h.elX ^ 4), MulAut.conj (h.elX ^ 2 * h.elY), h.elK} : Set (MulAut L)),
      M.ι g ∈ Subgroup.closure
        ({modelZ, modelX ^ 2 * modelY, modelK} : Set (Equiv.Perm (Fin 26))) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · rw [hιZ]; exact Subgroup.subset_closure (Set.mem_insert_iff.2 (Or.inl rfl))
    · rw [hιW]
      exact Subgroup.subset_closure
        (Set.mem_insert_iff.2 (Or.inr (Set.mem_insert_iff.2 (Or.inl rfl))))
    · rw [hιK]
      exact Subgroup.subset_closure
        (Set.mem_insert_iff.2 (Or.inr (Set.mem_insert_iff.2
          (Or.inr (Set.mem_singleton_iff.2 rfl)))))
  have hz : M.ι n * modelZ * (M.ι n)⁻¹ ∈
      Subgroup.closure
        ({modelZ, modelX ^ 2 * modelY, modelK} : Set (Equiv.Perm (Fin 26))) := by
    simpa only [hιZ] using conj_mem_closure_of_le
      (S := ({MulAut.conj (h.elX ^ 4), MulAut.conj (h.elX ^ 2 * h.elY), h.elK} :
        Set (MulAut L)))
      (K := Subgroup.closure
        ({modelZ, modelX ^ 2 * modelY, modelK} : Set (Equiv.Perm (Fin 26))))
      hK hn (g := MulAut.conj (h.elX ^ 4))
      (Subgroup.subset_closure (Set.mem_insert_iff.2 (Or.inl rfl)))
  have hw : M.ι n * (modelX ^ 2 * modelY) * (M.ι n)⁻¹ ∈
      Subgroup.closure
        ({modelZ, modelX ^ 2 * modelY, modelK} : Set (Equiv.Perm (Fin 26))) := by
    simpa only [hιW] using conj_mem_closure_of_le
      (S := ({MulAut.conj (h.elX ^ 4), MulAut.conj (h.elX ^ 2 * h.elY), h.elK} :
        Set (MulAut L)))
      (K := Subgroup.closure
        ({modelZ, modelX ^ 2 * modelY, modelK} : Set (Equiv.Perm (Fin 26))))
      hK hn (g := MulAut.conj (h.elX ^ 2 * h.elY))
      (Subgroup.subset_closure
        (Set.mem_insert_iff.2 (Or.inr (Set.mem_insert_iff.2 (Or.inl rfl)))))
  have hk : M.ι n * modelK * (M.ι n)⁻¹ ∈
      Subgroup.closure
        ({modelZ, modelX ^ 2 * modelY, modelK} : Set (Equiv.Perm (Fin 26))) := by
    simpa only [hιK] using conj_mem_closure_of_le
      (S := ({MulAut.conj (h.elX ^ 4), MulAut.conj (h.elX ^ 2 * h.elY), h.elK} :
        Set (MulAut L)))
      (K := Subgroup.closure
        ({modelZ, modelX ^ 2 * modelY, modelK} : Set (Equiv.Perm (Fin 26))))
      hK hn (g := h.elK)
      (Subgroup.subset_closure (Set.mem_insert_iff.2 (Or.inr (Set.mem_insert_iff.2
        (Or.inr (Set.mem_singleton_iff.2 rfl))))))
  have hres : M.ι n * (modelZ * modelK) * (M.ι n)⁻¹ = modelZ * modelK :=
    model_norm_two (n := M.ι n) (h.A_eq ▸ M.ι_mem n) hz hw hk
  apply M.ι_injective
  simp only [map_mul, map_inv, hιZ, hιK]
  exact hres

end IsL33Model

end CFSG.OddStandard.SmallF3.L33

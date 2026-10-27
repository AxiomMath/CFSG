module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSign

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec128_closure_odd_alt5 :
    Subgroup.closure {a : ↥(alternatingGroup (Fin 5)) | Odd (orderOf a)} = ⊤ := by
  set S : Subgroup ↥(alternatingGroup (Fin 5)) :=
    Subgroup.closure {a : ↥(alternatingGroup (Fin 5)) | Odd (orderOf a)} with hS
  have h3 : ∀ σ : Equiv.Perm (Fin 5), σ.IsThreeCycle →
      σ ∈ S.map (alternatingGroup (Fin 5)).subtype := by
    intro σ hσ
    have hmem : σ ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.mpr hσ.sign
    refine Subgroup.mem_map.mpr ⟨⟨σ, hmem⟩, Subgroup.subset_closure ?_, rfl⟩
    show Odd (orderOf (⟨σ, hmem⟩ : ↥(alternatingGroup (Fin 5))))
    rw [← Subgroup.orderOf_coe]
    simp only [hσ.orderOf]
    decide
  have hle : alternatingGroup (Fin 5) ≤ S.map (alternatingGroup (Fin 5)).subtype := by
    have hc : Subgroup.closure {σ : Equiv.Perm (Fin 5) | σ.IsThreeCycle} ≤
        S.map (alternatingGroup (Fin 5)).subtype :=
      (Subgroup.closure_le _).mpr (fun σ hσ => h3 σ hσ)
    rwa [Equiv.Perm.closure_three_cycles_eq_alternating] at hc
  rw [eq_top_iff]
  intro a _
  obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp (hle a.2)
  have : b = a := Subtype.ext hba
  rw [← this]
  exact hb

theorem sec128_closure_odd_of_alt5 {Y : Type} [Group Y] {X : Subgroup Y}
    (hX : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) :
    Subgroup.closure {x : Y | x ∈ X ∧ Odd (orderOf x)} = X := by
  obtain ⟨e⟩ := hX
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  · intro x hx
    have h1 : e ⟨x, hx⟩ ∈ Subgroup.closure {a : ↥(alternatingGroup (Fin 5)) | Odd (orderOf a)} := by
      rw [sec128_closure_odd_alt5]
      trivial
    have h2 : (⟨x, hx⟩ : ↥X) ∈
        (Subgroup.closure {a : ↥(alternatingGroup (Fin 5)) | Odd (orderOf a)}).map
          e.symm.toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨e ⟨x, hx⟩, h1, ?_⟩
      simp
    have h3 : (Subgroup.closure {a : ↥(alternatingGroup (Fin 5)) | Odd (orderOf a)}).map
        e.symm.toMonoidHom = Subgroup.closure {y : ↥X | Odd (orderOf y)} := by
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      simp only [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨a, ha, rfl⟩
        have : orderOf (e.symm.toMonoidHom a) = orderOf a :=
          MulEquiv.orderOf_eq e.symm a
        rw [this]
        exact ha
      · intro hy
        refine ⟨e y, ?_, by simp⟩
        rw [MulEquiv.orderOf_eq e y]
        exact hy
    rw [h3] at h2
    have h4 : x ∈ (Subgroup.closure {y : ↥X | Odd (orderOf y)}).map X.subtype :=
      Subgroup.mem_map.mpr ⟨⟨x, hx⟩, h2, rfl⟩
    rw [MonoidHom.map_closure] at h4
    refine (Subgroup.closure_mono ?_) h4
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    change Odd (orderOf (y : Y))
    rw [Subgroup.orderOf_coe]
    exact hy

end CFSG.OddStandard.SmallF3.Omega

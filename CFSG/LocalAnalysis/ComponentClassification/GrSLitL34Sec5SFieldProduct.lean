module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {X : Type} [Group X] [Finite X]

theorem exists_mulEquiv_pi_normalClosure {L : Subgroup X} (hL : IsComponent L)
    (hZ : center ↥L = ⊥) :
    ∃ k : ℕ, 1 ≤ k ∧ Nonempty (↥(normalClosure (L : Set X)) ≃* (Fin k → ↥L)) := by
  classical
  let ι : Type := {K : Subgroup X // ∃ g : X, K = L.map (MulAut.conj g).toMonoidHom}
  have : Fintype ι := Fintype.ofFinite _
  have hclosure : normalClosure (L : Set X) = ⨆ i : ι, i.1 := by
    apply le_antisymm
    · have hN : (⨆ i : ι, i.1).Normal := by
        refine ⟨fun n hn g => ?_⟩
        have key : ∀ i : ι, i.1.map (MulAut.conj g).toMonoidHom ≤ ⨆ i : ι, i.1 := by
          rintro ⟨K, h, rfl⟩
          refine le_trans ?_ (le_iSup (fun i : ι => i.1)
            ⟨L.map (MulAut.conj (g * h)).toMonoidHom, g * h, rfl⟩)
          rw [Subgroup.map_map]
          apply le_of_eq
          congr 1
          ext x
          simp [mul_assoc]
        have hmap : (⨆ i : ι, i.1).map (MulAut.conj g).toMonoidHom ≤ ⨆ i : ι, i.1 := by
          rw [Subgroup.map_iSup]
          exact iSup_le key
        exact hmap ⟨n, hn, rfl⟩
      have hL' : (L : Set X) ⊆ (⨆ i : ι, i.1 : Subgroup X) := by
        intro x hx
        refine le_iSup (fun i : ι => i.1) ⟨L, 1, ?_⟩ hx
        ext y
        simp
      exact normalClosure_le_normal hL'
    · refine iSup_le ?_
      rintro ⟨K, g, rfl⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (normalClosure_normal).conj_mem x (subset_normalClosure hx) g
  have hcomp : ∀ i : ι, IsComponent i.1 := by
    rintro ⟨K, g, rfl⟩
    exact CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hL
  let e : ∀ i : ι, ↥L ≃* ↥i.1 := fun i =>
    (L.equivMapOfInjective (MulAut.conj i.2.choose).toMonoidHom
      (MulAut.conj i.2.choose).injective).trans (MulEquiv.subgroupCongr i.2.choose_spec.symm)
  have hZi : ∀ i : ι, ∀ x ∈ i.1, (∀ y ∈ i.1, y * x = x * y) → x = 1 := by
    intro i x hx hc
    have hz : (e i).symm ⟨x, hx⟩ ∈ center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply (e i).injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext (hc _ (e i y).2)
    rw [hZ, Subgroup.mem_bot, MulEquiv.symm_apply_eq, map_one] at hz
    exact congrArg Subtype.val hz
  have hcomm : Pairwise fun i j : ι => ∀ x y : X, x ∈ i.1 → y ∈ j.1 → Commute x y := by
    intro i j hij x y hx hy
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    have h := (CFSG.LocalCores.distinct_components_commute (hcomp i) (hcomp j)).resolve_left hne
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hx) y hy).symm
  have hind : iSupIndep fun i : ι => i.1 := by
    rw [iSupIndep_def]
    intro i
    rw [Subgroup.disjoint_def]
    intro x hx hx'
    have hle : (⨆ (j : ι) (_ : j ≠ i), j.1) ≤ centralizer (i.1 : Set X) := by
      refine iSup₂_le fun j hji => ?_
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (hcomm hji y z hy hz).symm
    exact hZi i x hx fun y hy => Subgroup.mem_centralizer_iff.mp (hle hx') y hy
  set φ := Subgroup.noncommPiCoprod hcomm with hφ
  have hinj : Function.Injective φ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hrange : φ.range = normalClosure (L : Set X) := by
    rw [hφ, Subgroup.noncommPiCoprod_range, hclosure]
  have : Nonempty ι := ⟨⟨L, 1, by ext y; simp⟩⟩
  have hk : 1 ≤ Nat.card ι := Nat.card_pos
  refine ⟨Nat.card ι, hk, ⟨?_⟩⟩
  exact ((MulEquiv.subgroupCongr hrange).symm.trans (MonoidHom.ofInjective hinj).symm).trans
    ((MulEquiv.piCongrRight fun i => (e i).symm).trans
      (MulEquiv.arrowCongr (Finite.equivFin ι) (MulEquiv.refl ↥L)))

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end

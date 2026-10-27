module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.S8Concrete

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

open CFSG.GH74.Uniqueness.SU.SU5

theorem IsA8Type.nonempty_mulEquiv_S8 {P : Type*} [Group P] (h : IsA8Type P) :
    Nonempty (P ≃* S8) := by
  obtain ⟨Q, ⟨e⟩⟩ := h
  exact ⟨e.trans (Sylow.equiv Q J2Syl.sylA8)⟩

theorem IsA8Type.card_eq {P : Type*} [Group P] (h : IsA8Type P) : Nat.card P = 64 := by
  obtain ⟨φ⟩ := IsA8Type.nonempty_mulEquiv_S8 h
  have hS8 : Nat.card S8 = 64 := by
    have hcoe : (J2Syl.sylA8 : Subgroup (alternatingGroup (Fin 8))) = J2Syl.imgA8 :=
      Sylow.coe_ofCard _ _
    show Nat.card ↥(J2Syl.sylA8 : Subgroup (alternatingGroup (Fin 8))) = 64
    rw [hcoe]
    have h := J2Syl.card_imgA8
    rw [J2Syl.card_A8_factorization] at h
    norm_num at h
    exact h
  calc Nat.card P = Nat.card S8 := Nat.card_congr φ.toEquiv
    _ = 64 := hS8

theorem IsA8Type.pow_four {P : Type*} [Group P] (h : IsA8Type P) (x : P) : x ^ 4 = 1 := by
  obtain ⟨φ⟩ := IsA8Type.nonempty_mulEquiv_S8 h
  apply φ.injective
  rw [map_pow, S8_pow_four, map_one]

theorem IsA8Type.card_center {P : Type*} [Group P] (h : IsA8Type P) :
    Nat.card (Subgroup.center P) = 2 := by
  obtain ⟨φ⟩ := IsA8Type.nonempty_mulEquiv_S8 h
  calc Nat.card (Subgroup.center P) = Nat.card (Subgroup.center S8) :=
        Nat.card_congr (Subgroup.centerCongr φ).toEquiv
    _ = 2 := S8_card_center

theorem IsA8Type.exists_e16 {P : Type*} [Group P] (h : IsA8Type P) :
    ∃ E : Subgroup P, Nat.card E = 16 ∧ ∀ x ∈ E, x ^ 2 = 1 := by
  obtain ⟨φ⟩ := IsA8Type.nonempty_mulEquiv_S8 h
  obtain ⟨E, hcard, hsq⟩ := S8_exists_e16
  refine ⟨E.map φ.symm.toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective φ.symm.injective]; exact hcard
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_pow, hsq y hy, map_one]

theorem IsA8Type.exists_noncomm_involutions {P : Type*} [Group P] (h : IsA8Type P) :
    ∃ a b : P, a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a * b ≠ b * a := by
  obtain ⟨φ⟩ := IsA8Type.nonempty_mulEquiv_S8 h
  obtain ⟨a, b, ha, hb, hne⟩ := S8_exists_noncomm_involutions
  refine ⟨φ.symm a, φ.symm b, ?_, ?_, ?_⟩
  · rw [← map_pow, ha, map_one]
  · rw [← map_pow, hb, map_one]
  · intro h
    apply hne
    calc a * b = φ (φ.symm a * φ.symm b) := by
          rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      _ = φ (φ.symm b * φ.symm a) := by rw [h]
      _ = b * a := by
          rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem IsA8Type.gen_four {P : Type*} [Group P] (h : IsA8Type P) (R : Subgroup P) :
    ∃ s : Finset P, s.card ≤ 4 ∧ Subgroup.closure (s : Set P) = R := by
  classical
  obtain ⟨φ⟩ := IsA8Type.nonempty_mulEquiv_S8 h
  obtain ⟨s, hcard, hs⟩ := S8_gen_four (R.map φ.toMonoidHom)
  refine ⟨s.image φ.symm, ?_, ?_⟩
  · exact le_trans Finset.card_image_le hcard
  · apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    rw [MonoidHom.map_closure]
    have himg : φ.toMonoidHom '' (↑(s.image φ.symm) : Set P) = (↑s : Set S8) := by
      rw [Finset.coe_image, Set.image_image]
      simp
    rw [himg, hs]

end CFSG.EvenSporadicStandard.HNRecog.GH73

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDBase

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {H : Type*} [Group H]

private theorem s8d_conj_inl (a b : ↥(alternatingGroup (Fin 5))) :
    ((b * a * b⁻¹, 1) : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5))) =
      (b, b) * (a, 1) * (b, b)⁻¹ := by
  ext <;> simp

private theorem s8d_split_pair (a b : ↥(alternatingGroup (Fin 5))) :
    ((a, b) : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5))) =
      (a * b⁻¹, 1) * (b, b) := by
  ext <;> simp

theorem s8d_range_le_of_diag (ι : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)) →* H)
    (R : Subgroup H) (hd : ∀ b, ι (b, b) ∈ R) {g : ↥(alternatingGroup (Fin 5))} (hg : g ≠ 1)
    (hgR : ι (g, 1) ∈ R) : ∀ x, ι x ∈ R := by
  let E : Subgroup ↥(alternatingGroup (Fin 5)) :=
    R.comap (ι.comp (MonoidHom.inl ↥(alternatingGroup (Fin 5)) ↥(alternatingGroup (Fin 5))))
  have hE : ∀ a, a ∈ E ↔ ι (a, 1) ∈ R := fun a => Iff.rfl
  have hEn : E.Normal := by
    refine ⟨fun a ha b => ?_⟩
    rw [hE] at ha ⊢
    rw [s8d_conj_inl, map_mul, map_mul, map_inv]
    exact R.mul_mem (R.mul_mem (hd b) ha) (R.inv_mem (hd b))
  have hEtop : E = ⊤ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ E hEn with h | h
    · exfalso
      have : g ∈ E := (hE g).mpr hgR
      rw [h, Subgroup.mem_bot] at this
      exact hg this
    · exact h
  rintro ⟨a, b⟩
  rw [s8d_split_pair, map_mul]
  have ha : a * b⁻¹ ∈ E := by rw [hEtop]; exact Subgroup.mem_top _
  exact R.mul_mem ((hE _).mp ha) (hd b)

theorem s8d_hom_eq_of_diag (ι χ : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)) →* H)
    (hd : ∀ b, ι (b, b) = χ (b, b)) {g : ↥(alternatingGroup (Fin 5))} (hg : g ≠ 1)
    (hgi : ι (g, 1) = χ (g, 1)) : ι = χ := by
  let E : Subgroup ↥(alternatingGroup (Fin 5)) :=
    MonoidHom.eqLocus (ι.comp (MonoidHom.inl _ _)) (χ.comp (MonoidHom.inl _ _))
  have hE : ∀ a, a ∈ E ↔ ι (a, 1) = χ (a, 1) := fun a => Iff.rfl
  have hEn : E.Normal := by
    refine ⟨fun a ha b => ?_⟩
    rw [hE] at ha ⊢
    rw [s8d_conj_inl, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, ha, hd b]
  have hEtop : E = ⊤ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ E hEn with h | h
    · exfalso
      have : g ∈ E := (hE g).mpr hgi
      rw [h, Subgroup.mem_bot] at this
      exact hg this
    · exact h
  refine MonoidHom.ext fun ⟨a, b⟩ => ?_
  have ha : a * b⁻¹ ∈ E := by rw [hEtop]; exact Subgroup.mem_top _
  rw [s8d_split_pair, map_mul, map_mul, (hE _).mp ha, hd b]

theorem s8dG_ne_one : s8dG ≠ 1 := by
  intro h
  have h1 := congrArg Subtype.val h
  exact absurd h1 (by decide)

theorem s8d_shapeS {Z : Subgroup S8A}
    (θ' : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)) ≃* ↥Z)
    (hθ : ∀ a : ↥(alternatingGroup (Fin 5)), (θ' (a, a) : S8A) = s8dDiag a)
    (T : (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ) (hT : (θ' (s8dG, 1) : S8A) = s8dSplit T) :
    ∀ x : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)),
      (θ' x : S8A) = s8dTheta T * s8dProdA x * (s8dTheta T)⁻¹ := by
  let ι : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)) →* S8A :=
    Z.subtype.comp θ'.toMonoidHom
  let χ : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)) →* S8A :=
    (MulAut.conj (s8dTheta T)).toMonoidHom.comp s8dProdA
  have hχ : ∀ x, χ x = s8dTheta T * s8dProdA x * (s8dTheta T)⁻¹ := fun _ => rfl
  have hd : ∀ b, ι (b, b) = χ (b, b) := by
    intro b
    rw [hχ]
    show (θ' (b, b) : S8A) = _
    rw [hθ b, s8dProdA_eq, ← s8dDiag_eq, s8dTheta_comm_diag, mul_inv_cancel_right]
  have hgi : ι (s8dG, 1) = χ (s8dG, 1) := by
    rw [hχ]
    exact hT
  intro x
  exact (congrArg (fun φ => φ x) (s8d_hom_eq_of_diag ι χ hd s8dG_ne_one hgi) :)

end CFSG.OddStandard.SmallF3.Omega

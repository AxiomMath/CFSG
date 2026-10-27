module

public import CFSG.LieType.ChevTwo.OppCl.Defs
public import CFSG.LieType.BorelTits.Symplectic

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

variable (r : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]

theorem ea_Sp_aux :
    EA0 (spForm r F) (fun _ => True) (natRep (StatedSp r F)) ∧
    EA1 (spForm r F) (fun _ => True) (natRep (StatedSp r F)) ∧
    EA2 (spForm r F) (fun _ => True) (natRep (StatedSp r F)) := by
  have hσ : (spForm r F).σ = RingEquiv.refl F := rfl
  have hs : ∀ (a : F) (w w' : Fin r ⊕ Fin r → F),
      (spForm r F).β (a • w) w' = a * (spForm r F).β w w' := fun a w w' => by
    rw [(spForm r F).smul_left, hσ]
    rfl
  have hneg : ∀ (a : F) (w : Fin r ⊕ Fin r → F), -(a • w) = a • w := fun a w => by
    rw [← neg_smul, CharTwo.neg_eq]
  have hsub : ∀ (u w : Fin r ⊕ Fin r → F) (a : F), u - a • w = u + a • w := fun u w a => by
    rw [sub_eq_add_neg, hneg]
  have hSiegel : ∀ x y : Fin r ⊕ Fin r → F, (spForm r F).β x y = 0 →
      ∃ g : StatedSp r F, ∀ v : Fin r ⊕ Fin r → F, natRep (StatedSp r F) g v =
        v + (spForm r F).β x v • y + (spForm r F).β y v • x := by
    intro x y hxy
    refine exists_natRep_eq_of_isometry r F
      { toFun := fun v => v + (spForm r F).β x v • y + (spForm r F).β y v • x
        map_add' := fun u v => by
          simp only [(spForm r F).add_right, add_smul]
          abel
        map_smul' := fun a v => by
          simp only [RingHom.id_apply, (spForm r F).smul_right, smul_add, smul_smul] }
      ((spForm r F).β_siegel hσ (spForm_self r F) hxy)
  have hT : ∀ (x : Fin r ⊕ Fin r → F) (c : F), ∃ g : StatedSp r F, ∀ v : Fin r ⊕ Fin r → F,
      natRep (StatedSp r F) g v = v + (c * (spForm r F).β x v) • x := by
    intro x c
    obtain ⟨d, rfl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c
    obtain ⟨g, hg⟩ := exists_natRep_eq_of_isometry r F
      { toFun := fun v => v + (spForm r F).β (d • x) v • (d • x)
        map_add' := fun u v => by
          simp only [(spForm r F).add_right, add_smul]
          abel
        map_smul' := fun a v => by
          simp only [RingHom.id_apply, (spForm r F).smul_right, smul_add, smul_smul, mul_assoc] }
      ((spForm r F).β_transvection hσ (spForm_self r F) (d • x))
    refine ⟨g, fun v => ?_⟩
    rw [hg v]
    show v + (spForm r F).β (d • x) v • (d • x) = v + (d * d * (spForm r F).β x v) • x
    rw [hs, smul_smul, show d * (spForm r F).β x v * d = d * d * (spForm r F).β x v by ring]
  refine ⟨?_, ?_, ?_⟩
  · intro x y _ _ hxy
    obtain ⟨g, hg⟩ := hSiegel x y hxy
    exact ⟨g, fun v => by rw [hg v, hsub]⟩
  · intro x y _ hxy
    obtain ⟨g, hg⟩ := hSiegel x y hxy
    exact ⟨0, g, fun v => by rw [hg v, zero_smul, add_zero, hsub]⟩
  · intro x c _ _
    exact hT x c

end CFSG.LieType.ChevTwo.OppCl

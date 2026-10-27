module

public import CFSG.ClassicalInvolution.Q3.TL4ExitDichA
public import CFSG.ClassicalInvolution.Q3.TL4MF163M12O
public import CFSG.ClassicalInvolution.Q3.TL4MFMuZ2Cl

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint CFSG.Sporadic.Schreier
  CFSG.Sporadic.Mathieu
open CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.OuterAutomorphisms

namespace MF163

variable {X : Type} [Group X] [Finite X]

theorem concl163Syl_m12
    {R : Subgroup X} {S : Sylow 2 R} {z : X}
    (hm : EdgelessMember3 R S z) (hX : NativeSporadic.IsSporadic X .M12) :
    Concl163Syl R S z := by
  intro β hβ2 hβS
  obtain ⟨e⟩ := hX
  obtain ⟨ι, hι, hιS, hιz⟩ := exists_quat_of_member_syl hm
  let e' : X ≃* NativeSporadic.M12 := e
  have hfix : ∀ g, MulAut.congr e' β ((e'.toMonoidHom.comp ι) g) = (e'.toMonoidHom.comp ι) g :=
    fun g => by simp [MulAut.congr_apply, hβS _ (hιS g)]
  rcases eq_one_or_conj_of_quat_m12 (e'.toMonoidHom.comp ι) (e'.injective.comp hι)
    (MulAut.congr e' β) (by rw [← map_mul, hβ2, map_one]) hfix with h | h
  · exact Or.inl ((MulAut.congr e').injective (h.trans (map_one _).symm))
  · right
    apply (MulAut.congr e').injective
    rw [h, congr_conj]
    simp [hιz]

omit [Finite X] in
theorem fstar_nonabelian (h : ∃ a b : FStarQuot X, a * b ≠ b * a) :
    ∃ a b : genFittingFStar X, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩

theorem center_eq_bot_of_fstar [IsSimpleGroup ↥(genFittingFStar X)]
    (hnab : ∃ a b : genFittingFStar X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff, ← centralizer_genFittingFStar_eq_bot hnab]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y _
  exact Subgroup.mem_center_iff.mp hx y

theorem isSporadic_of_center_quot [IsSimpleGroup ↥(genFittingFStar X)]
    (hnab : ∃ a b : genFittingFStar X, a * b ≠ b * a)
    (h : Nonempty (X ⧸ Subgroup.center X ≃* NativeSporadic.Carrier .M12)) :
    NativeSporadic.IsSporadic X .M12 := by
  obtain ⟨e⟩ := h
  have hZ := center_eq_bot_of_fstar hnab
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e⟩

theorem index_le_two_of_m12
    [IsSimpleGroup ↥(genFittingFStar X)]
    (h : NativeSporadic.IsSporadic (FStarQuot X) .M12) : (genFittingFStar X).index ≤ 2 := by
  obtain ⟨e⟩ := h
  have e₁ : FStarQuot X ≃* ↥NativeSporadic.M12 := e
  have hnab : ∃ a b : genFittingFStar X, a * b ≠ b * a :=
    fstar_nonabelian ⟨e₁.symm m12a, e₁.symm m12b, fun h => m12_gens_not_comm (by
      simpa using congrArg e₁ h)⟩
  obtain ⟨eF⟩ := MFMuZ2.nonempty_fstar_equiv (MFMuZ2.center_fstar_eq_bot hnab)
  let E : ↥(genFittingFStar X) ≃* ↥NativeSporadic.M12 := eF.trans e₁
  have hC := centralizer_genFittingFStar_eq_bot hnab
  have : (genFittingFStar X).Normal := genFittingFStar_normal X
  have hinj : Function.Injective (MulAut.conjNormal (G := X) (H := genFittingFStar X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [← hC, Subgroup.mem_centralizer_iff]
    intro n hn
    have h1 := congrArg (fun φ : MulAut ↥(genFittingFStar X) =>
      ((φ ⟨n, hn⟩ : ↥(genFittingFStar X)) : X)) hx
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc n * x = x * n * x⁻¹ * x := by rw [h1]
      _ = x * n := by group
  have : Finite (MulAut ↥(genFittingFStar X)) :=
    Finite.of_injective (fun β : MulAut ↥(genFittingFStar X) =>
      (β : ↥(genFittingFStar X) → ↥(genFittingFStar X))) fun β γ h => MulEquiv.ext (congrFun h)
  have h1 : Nat.card X ≤ Nat.card (MulAut ↥(genFittingFStar X)) :=
    Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card (MulAut ↥(genFittingFStar X)) = Nat.card (MulAut ↥NativeSporadic.M12) :=
    Nat.card_congr (MulAut.congr E).toEquiv
  have h3 := m12_mulAut_card
  have h4 : Nat.card ↥NativeSporadic.M12 = Nat.card ↥(genFittingFStar X) :=
    (Nat.card_congr E.toEquiv).symm
  have h5 := Subgroup.card_mul_index (genFittingFStar X)
  have hpos : 0 < Nat.card ↥(genFittingFStar X) := Nat.card_pos
  nlinarith

end MF163

end CFSG.ClassicalInvolution.Q3.TL4

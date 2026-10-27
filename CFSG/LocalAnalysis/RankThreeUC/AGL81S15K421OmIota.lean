module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421OmStab
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421OmCount
public import CFSG.LargeExtraspecial.DWFldOrth

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421OmProof

open CFSG.Open Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

section Reflection

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem rWGL_ne_one (hb : b ≠ 0) : rWGL b ≠ 1 := by
  intro h
  have h1 := congrArg (fun A : GL OmI F => (A : Matrix OmI OmI F) uI vI) h
  have h2 : rWmat b uI vI = b := by
    rw [rWmat_apply]
    simp [uI, vI]
  have h3 : ((rWGL b : GL OmI F) : Matrix OmI OmI F) uI vI = b := h2
  simp only [h3] at h1
  simp [uI, vI] at h1
  exact hb h1

theorem rWGL_not_mem_omega (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    rWGL b ∉ StatedOmega (StatedQuadMinus 4 F b c) := by
  intro hmem
  have hb : b ≠ 0 := b_ne_zero hirr
  have hQ : ⇑(quadMinus 4 F b c) = StatedQuadMinus 4 F b c := coe_quadMinus (n := 4) (K := F) b c
  rw [statedOmega_eq_comap hQ] at hmem
  have ht := Subgroup.mem_comap.1 hmem
  have h1 : (toLinEquiv OmI F) (rWGL b) ≠ 1 := fun h => rWGL_ne_one hb
    ((toLinEquiv OmI F).injective (h.trans (map_one _).symm))
  refine CFSG.LargeExtraspecial.DW.not_line_of_mem_commutator (nondegenerate_polarBilin_quadMinus_of_finite 4 F hirr) ht h1 eU
    (fun y => ?_)
  rw [Submodule.mem_span_singleton]
  refine ⟨b * y vI, ?_⟩
  ext i
  simp only [LinearEquiv.coe_coe, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  show (b * y vI) * eU i = (rWmat b *ᵥ y) i - y i
  rw [rWmat_mulVec]
  simp [eU, Pi.single_apply]

end Reflection

section Embedding

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

abbrev OmG (F : Type) [Field F] (b c : F) : Subgroup (GL OmI F) :=
  StatedOmega (StatedQuadMinus 4 F b c)

abbrev stabOm (F : Type) [Field F] (b c : F) : Subgroup ↥(OmG F b c) :=
  MulAction.stabilizer ↥(OmG F b c) (eU : OmI → F)

theorem mem_stabOm_iff (A : ↥(OmG F b c)) :
    A ∈ stabOm F b c ↔ ((A : GL OmI F) : Matrix OmI OmI F) *ᵥ eU = eU :=
  MulAction.mem_stabilizer_iff

@[expose] def stabOmToStabW : ↥(stabOm F b c) →* ↥(stabW F b c) :=
  ((OmG F b c).subtype.comp (stabOm F b c).subtype).codRestrict (stabW F b c)
    (fun A => ⟨statedOmega_le_isoGrp _ A.1.2, (mem_stabOm_iff A.1).1 A.2⟩)

@[expose] def rhoH (hb : b ≠ 0) : ↥(stabOm F b c) →* ↥(StatedSp 3 F) :=
  ((rho hb).comp stabOmToStabW).codRestrict (StatedSp 3 F)
    (fun A => rho_mem_statedSp hb (stabOmToStabW A))

theorem rhoH_injective (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Function.Injective (rhoH (c := c) (b_ne_zero hirr)) := by
  have hb : b ≠ 0 := b_ne_zero hirr
  rw [injective_iff_map_eq_one]
  intro A hA
  have h1 : ((rho hb (stabOmToStabW A) : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3)
      (Fin 3 ⊕ Fin 3) F) = 1 := by
    have := congrArg (fun g : ↥(StatedSp 3 F) => ((g : GL (Fin 3 ⊕ Fin 3) F) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)) hA
    exact this
  rw [rho_val] at h1
  rcases eq_one_or_rWGL hb (stabOmToStabW A).2 h1 with h | h
  · exact Subtype.ext (Subtype.ext h)
  · exfalso
    apply rWGL_not_mem_omega hirr
    rw [← h]
    exact A.1.2

theorem card_orbit_le (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (MulAction.orbit ↥(OmG F b c) (eU : OmI → F)) ≤
      Nat.card F ^ 7 + Nat.card F ^ 3 := by
  rw [← K421OmCountProof.card_quadMinus_eq_one hirr]
  refine Nat.card_le_card_of_injective
    (fun x => ⟨x.1, ?_⟩ : MulAction.orbit ↥(OmG F b c) (eU : OmI → F) →
      {v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F // StatedQuadMinus 4 F b c v = 1}) ?_
  · obtain ⟨A, hA⟩ := x.2
    have h1 := statedOmega_le_isoGrp (StatedQuadMinus 4 F b c) A.2 eU
    rw [← hA]
    show StatedQuadMinus 4 F b c (((A : GL OmI F) : Matrix OmI OmI F) *ᵥ eU) = 1
    rw [h1, quadMinus_eU]
  · intro x y h
    exact Subtype.ext (Subtype.mk.inj h)

theorem card_stabOm_ge (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ f)
    (hΩ : Nat.card ↥(OmG F b c) = ordTwistedD 4 (Nat.card F)) :
    Nat.card ↥(StatedSp 3 F) ≤ Nat.card ↥(stabOm F b c) := by
  have h1 : Nat.card (MulAction.orbit ↥(OmG F b c) (eU : OmI → F)) *
      Nat.card ↥(stabOm F b c) = Nat.card ↥(OmG F b c) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥(OmG F b c) (eU : OmI → F))
  have h2 := card_orbit_le (c := c) hirr
  rw [hΩ, ordTwistedD_four_eq hF hf] at h1
  have hpos : 0 < Nat.card F ^ 7 + Nat.card F ^ 3 := by
    have : 0 < Nat.card F := Nat.card_pos
    positivity
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc (Nat.card F ^ 7 + Nat.card F ^ 3) * Nat.card ↥(StatedSp 3 F)
      = Nat.card (MulAction.orbit ↥(OmG F b c) (eU : OmI → F)) * Nat.card ↥(stabOm F b c) := h1.symm
    _ ≤ (Nat.card F ^ 7 + Nat.card F ^ 3) * Nat.card ↥(stabOm F b c) :=
        Nat.mul_le_mul_right _ h2

@[expose] noncomputable def stabOmEquiv (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {f : ℕ}
    (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    (hΩ : Nat.card ↥(OmG F b c) = ordTwistedD 4 (Nat.card F)) :
    ↥(stabOm F b c) ≃* ↥(StatedSp 3 F) :=
  MulEquiv.ofBijective (rhoH (b_ne_zero hirr))
    ((rhoH_injective hirr).bijective_of_nat_card_le (card_stabOm_ge hirr hf hF hΩ))

@[expose] noncomputable def iotaOm (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ f) (hΩ : Nat.card ↥(OmG F b c) = ordTwistedD 4 (Nat.card F)) :
    ↥(StatedSp 3 F) →* ↥(OmG F b c) :=
  (stabOm F b c).subtype.comp (stabOmEquiv hirr hf hF hΩ).symm.toMonoidHom

theorem iotaOm_injective (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ f) (hΩ : Nat.card ↥(OmG F b c) = ordTwistedD 4 (Nat.card F)) :
    Function.Injective (iotaOm hirr hf hF hΩ) :=
  Subtype.val_injective.comp (stabOmEquiv hirr hf hF hΩ).symm.injective

end Embedding

end K421OmProof

end CFSG.LocalAnalysis.RankThreeUC.S15

module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.BrNative
public import CFSG.RankThree.SteinbergR3ESmallReeCosetDescent
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Codes

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Blueprint.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.Census.Carrier.G2Three (dec14 x0c x1c y0c y1c)


@[expose] noncomputable def iotaN : NG →* Matrix (Fin 14) (Fin 14) (ZMod 3) :=
  (Units.coeHom (Matrix (Fin 14) (Fin 14) (ZMod 3))).comp
    ((CFSG.Quasithin.G2U.glHom (RingEquiv.refl (ZMod 3))).comp
      (adjointGroup ReeTag.G2.tag (ZMod 3)).subtype)

theorem iotaN_injective : Function.Injective iotaN := by
  intro a b h
  apply Subtype.val_injective
  apply CFSG.Quasithin.G2U.glHom_injective (RingEquiv.refl (ZMod 3))
  exact Units.val_injective h

private theorem one_ne_zero_matrix : (1 : Matrix (Fin 14) (Fin 14) (ZMod 3)) ≠ 0 := by
  intro h
  have h11 : (1 : ZMod 3) = 0 := by
    simpa using congrFun (congrFun h 0) 0
  exact one_ne_zero h11

theorem iotaN_ne_zero (g : NG) : iotaN g ≠ 0 := by
  intro h
  have h1 : iotaN g * iotaN g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [h, zero_mul] at h1
  exact one_ne_zero_matrix h1.symm

theorem iotaN_x0 : iotaN (xElement ⟨0, by decide⟩ 1) = dec14 x0c := by
  change ((CFSG.RankThree.PartTwo.Census.Carrier.G2Three.gX 0 :
    GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) = dec14 x0c
  exact CFSG.RankThree.PartTwo.Census.Carrier.G2Three.coe_gX0

theorem iotaN_x1 : iotaN (xElement ⟨1, by decide⟩ 1) = dec14 x1c := by
  change ((CFSG.RankThree.PartTwo.Census.Carrier.G2Three.gX 1 :
    GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) = dec14 x1c
  exact CFSG.RankThree.PartTwo.Census.Carrier.G2Three.coe_gX1

theorem iotaN_y0 : iotaN (yElement ⟨0, by decide⟩ 1) = dec14 y0c := by
  change ((CFSG.RankThree.PartTwo.Census.Carrier.G2Three.gY 0 :
    GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) = dec14 y0c
  exact CFSG.RankThree.PartTwo.Census.Carrier.G2Three.coe_gY0

theorem iotaN_y1 : iotaN (yElement ⟨1, by decide⟩ 1) = dec14 y1c := by
  change ((CFSG.RankThree.PartTwo.Census.Carrier.G2Three.gY 1 :
    GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) = dec14 y1c
  exact CFSG.RankThree.PartTwo.Census.Carrier.G2Three.coe_gY1

theorem phiN_x0 : phiN (xElement ⟨0, by decide⟩ 1) = xElement ⟨1, by decide⟩ 1 := by
  have h := (CFSG.RankThree.finiteExceptionalAut_G2_formulas (K := ZMod 3)).1 1
  simpa [phiN] using h

theorem phiN_x1 : phiN (xElement ⟨1, by decide⟩ 1) = xElement ⟨0, by decide⟩ 1 := by
  have h := (CFSG.RankThree.finiteExceptionalAut_G2_formulas (K := ZMod 3)).2.1 1
  simpa [phiN] using h

theorem phiN_y0 : phiN (yElement ⟨0, by decide⟩ 1) = yElement ⟨1, by decide⟩ 1 := by
  have h := (CFSG.RankThree.finiteExceptionalAut_G2_formulas (K := ZMod 3)).2.2.1 1
  simpa [phiN] using h

theorem phiN_y1 : phiN (yElement ⟨1, by decide⟩ 1) = yElement ⟨0, by decide⟩ 1 := by
  have h := (CFSG.RankThree.finiteExceptionalAut_G2_formulas (K := ZMod 3)).2.2.2 1
  simpa [phiN] using h

private theorem phiN_apply_apply (g : NG) : phiN (phiN g) = g := by
  have h := congrArg (fun θ : MulAut NG => θ g) phiN_mul_self
  simpa [MulAut.mul_apply] using h

private theorem conj_mul_phi_not_inner (g : NG) :
    ¬ ∃ x : NG, MulAut.conj g * phiN = MulAut.conj x := by
  rintro ⟨x, hx⟩
  apply phiN_not_inner
  refine ⟨g⁻¹ * x, ?_⟩
  rw [map_mul, map_inv, ← hx]
  group

private noncomputable def rhoFun (α : MulAut NG) : Wm := by
  classical
  exact if h : ∃ t : NG, α = MulAut.conj t then
    wdiag (iotaN h.choose) (iotaN (phiN h.choose))
  else
    wanti (iotaN ((Or.resolve_left (aut_cases_NG α) h).choose))
      (iotaN (phiN ((Or.resolve_left (aut_cases_NG α) h).choose)))

private theorem rhoFun_conj (g : NG) :
    rhoFun (MulAut.conj g) = wdiag (iotaN g) (iotaN (phiN g)) := by
  unfold rhoFun
  have hp : ∃ x : NG, MulAut.conj g = MulAut.conj x := ⟨g, rfl⟩
  rw [dif_pos hp]
  have hc : hp.choose = g := (conj_inj_NG hp.choose_spec).symm
  rw [hc]

private theorem rhoFun_conj_mul_phi (g : NG) :
    rhoFun (MulAut.conj g * phiN) = wanti (iotaN g) (iotaN (phiN g)) := by
  unfold rhoFun
  have hp : ¬ ∃ x : NG, MulAut.conj g * phiN = MulAut.conj x :=
    conj_mul_phi_not_inner g
  rw [dif_neg hp]
  let x := (Or.resolve_left (aut_cases_NG (MulAut.conj g * phiN)) hp).choose
  have hxspec : MulAut.conj g * phiN = MulAut.conj x * phiN :=
    (Or.resolve_left (aut_cases_NG (MulAut.conj g * phiN)) hp).choose_spec
  have hxg : x = g := (conj_inj_NG (mul_right_cancel hxspec)).symm
  change wanti (iotaN x) (iotaN (phiN x)) = wanti (iotaN g) (iotaN (phiN g))
  rw [hxg]

private theorem rhoFun_mul (α β : MulAut NG) :
    rhoFun (α * β) = rhoFun α * rhoFun β := by
  rcases aut_cases_NG α with ⟨g, rfl⟩ | ⟨g, rfl⟩ <;>
    rcases aut_cases_NG β with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · rw [show MulAut.conj g * MulAut.conj h = MulAut.conj (g * h) by rw [map_mul]]
    simp only [rhoFun_conj, wdiag_mul]
    simp only [map_mul]
  · rw [show MulAut.conj g * (MulAut.conj h * phiN) = MulAut.conj (g * h) * phiN by
      rw [← mul_assoc, map_mul]]
    simp only [rhoFun_conj_mul_phi, rhoFun_conj, wdiag_mul_wanti]
    simp only [map_mul]
  · have h1 : (MulAut.conj g * phiN) * MulAut.conj h =
        MulAut.conj (g * phiN h) * phiN := by
      calc (MulAut.conj g * phiN) * MulAut.conj h
          = MulAut.conj g * (phiN * MulAut.conj h) := by group
        _ = MulAut.conj g * (MulAut.conj (phiN h) * phiN) := by rw [phiN_mul_conj]
        _ = MulAut.conj (g * phiN h) * phiN := by rw [← mul_assoc, map_mul]
    rw [h1]
    simp only [rhoFun_conj_mul_phi, rhoFun_conj, wanti_mul_wdiag]
    simp only [map_mul, phiN_apply_apply]
  · have h1 : (MulAut.conj g * phiN) * (MulAut.conj h * phiN) =
        MulAut.conj (g * phiN h) := by
      calc (MulAut.conj g * phiN) * (MulAut.conj h * phiN)
          = MulAut.conj g * (phiN * MulAut.conj h) * phiN := by group
        _ = MulAut.conj g * (MulAut.conj (phiN h) * phiN) * phiN := by rw [phiN_mul_conj]
        _ = (MulAut.conj g * MulAut.conj (phiN h)) * (phiN * phiN) := by group
        _ = MulAut.conj (g * phiN h) := by rw [phiN_mul_self, mul_one, map_mul]
    rw [h1]
    simp only [rhoFun_conj, rhoFun_conj_mul_phi, wanti_mul_wanti]
    simp only [map_mul, phiN_apply_apply]

private theorem wdiag_inj₁ {A B C D : Matrix (Fin 14) (Fin 14) (ZMod 3)}
    (h : wdiag A B = wdiag C D) : A = C := by
  simpa [wdiag] using congrArg Matrix.toBlocks₁₁ h

private theorem wanti_inj₁ {A B C D : Matrix (Fin 14) (Fin 14) (ZMod 3)}
    (h : wanti A B = wanti C D) : A = C := by
  simpa [wanti] using congrArg Matrix.toBlocks₁₂ h

private theorem wdiag_eq_wanti_fst {A B C D : Matrix (Fin 14) (Fin 14) (ZMod 3)}
    (h : wdiag A B = wanti C D) : A = 0 := by
  simpa [wdiag, wanti] using (Matrix.fromBlocks_inj.mp h).1

private theorem wanti_eq_wdiag_fst {A B C D : Matrix (Fin 14) (Fin 14) (ZMod 3)}
    (h : wanti A B = wdiag C D) : A = 0 := by
  simpa [wdiag, wanti] using (Matrix.fromBlocks_inj.mp h).2.1

private theorem rhoFun_injective : Function.Injective rhoFun := by
  intro α β h
  rcases aut_cases_NG α with ⟨g, rfl⟩ | ⟨g, rfl⟩ <;>
    rcases aut_cases_NG β with ⟨h', rfl⟩ | ⟨h', rfl⟩
  · rw [rhoFun_conj, rhoFun_conj] at h
    rw [iotaN_injective (wdiag_inj₁ h)]
  · rw [rhoFun_conj, rhoFun_conj_mul_phi] at h
    exact absurd (wdiag_eq_wanti_fst h) (iotaN_ne_zero g)
  · rw [rhoFun_conj_mul_phi, rhoFun_conj] at h
    exact absurd (wanti_eq_wdiag_fst h) (iotaN_ne_zero g)
  · rw [rhoFun_conj_mul_phi, rhoFun_conj_mul_phi] at h
    rw [iotaN_injective (wanti_inj₁ h)]

theorem exists_rho : ∃ ρ : MulAut NG →* Wm, Function.Injective ρ ∧
    (∀ g : NG, ρ (MulAut.conj g) = wdiag (iotaN g) (iotaN (phiN g))) ∧
    ρ phiN = wanti 1 1 := by
  refine ⟨{ toFun := rhoFun, map_one' := ?_, map_mul' := rhoFun_mul }, rhoFun_injective, ?_, ?_⟩
  · rw [show (1 : MulAut NG) = MulAut.conj 1 by simp, rhoFun_conj]
    simp only [map_one, wdiag_one]
  · intro g
    exact rhoFun_conj g
  · change rhoFun phiN = wanti 1 1
    rw [show phiN = MulAut.conj 1 * phiN by simp, rhoFun_conj_mul_phi]
    simp only [map_one]

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

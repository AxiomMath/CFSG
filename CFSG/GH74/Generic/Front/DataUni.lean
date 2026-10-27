module

public import CFSG.GH74.Generic.Front.DataUniLA

public section

namespace CFSG.GH74.Generic

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank CFSG.GH74.Filter.ClassicalOdd
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
  CFSG.ClassicalInvolution CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary Subgroup
open scoped MatrixGroups

theorem hmat_uni {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (h2 : (2 : F) ≠ 0) (t : ↥(ModelData.uni hF).K4)
    (hT : ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1)
    (h1 : ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠ 1)
    (hm1 : ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠ -1) :
    ∃ g : GL (Fin 4) F, g ∈ (ModelData.uni hF).K4 ∧
      ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) =
        (g : Matrix (Fin 4) (Fin 4) F) * Matrix.diagonal (![-1, -1, 1, 1] : Fin 4 → F) := by
  obtain ⟨hmemU, hdet⟩ := ((ModelData.uni hF).mem_K4 _).1 t.2
  have hU : conjTr (unitaryInvolution F p f) ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := (mem_uniGL _).1 hmemU
  obtain ⟨P, hPdet, hPU, hTP⟩ := exists_unitary_conj_yMat
    (isUnitaryInvolution_unitaryInvolution hF) h2 _ hT hU hdet h1 hm1
  refine ⟨Matrix.GeneralLinearGroup.mk'' P (by rw [hPdet]; exact isUnit_one), ?_, hTP⟩
  exact ((ModelData.uni hF).mem_K4 _).2 ⟨(mem_uniGL _).2 hPU, hPdet⟩

theorem frontData0_statedSU4 {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 1) : Nonempty (FrontData0 ↥(StatedSU 4 q F)) := by
  obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (Nat.odd_iff.2 (by omega : p ^ f % 2 = 1)).pow
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hp2 : p ≠ 2 := prime_ne_two_of_odd_card (F := F) (p := p) hodd
  have hK2 : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    exact hp2
  obtain ⟨a, b, ha, hb, hab⟩ := exists_quat_unitary hp2 hF
  have hσ : ∀ x, (unitaryInvolution F p f : F →+* F) x = x ^ (p ^ f) :=
    unitaryInvolution_apply F p f
  let ρ : Q8 →* GL (Fin 2) F :=
    (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).comp (quatHom hab)
  have hρ : ∀ g, ρ g ∈ (ModelData.uni hF).H2 := fun g =>
    ((ModelData.uni hF).mem_H2 _).2 ⟨isUni_quatHom hab
      (σ := (unitaryInvolution F p f : F →+* F)) (by rw [hσ]; exact ha) (by rw [hσ]; exact hb) g,
      (quatHom hab g).2⟩
  have hinj : Function.Injective ρ :=
    SpecialLinearGroup.toGL_injective.comp (quatHom_injective hK2 hab)
  have hz : ρ (QuaternionGroup.a 2) = -1 := by
    apply Units.ext
    change ((quatHom hab (QuaternionGroup.a 2) : Matrix (Fin 2) (Fin 2) F)) = _
    rw [quatHom_a_two hab]
    simp
  refine frontData0_of_model (ModelData.uni hF) ρ hρ hinj hz
    (hone_of_model _ (mem_center_uni_iff hF hq) (fun t hT h1 hm1 => hmat_uni hF h2 t hT h1 hm1))
    ?_
  obtain ⟨e⟩ := nonempty_sl2_equiv_uni_H2 hF
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  have hr : 2 ≤ p ^ f := by
    by_contra h
    have h' : p ^ f ≤ 1 := by omega
    have : (p ^ f) ^ 2 ≤ 1 := by
      calc (p ^ f) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h' 2
        _ = 1 := by norm_num
    omega
  have h4 : 4 ≤ Nat.card (fixedSubfield F p f) := by
    rw [card_fixedSubfield hF]
    omega
  exact goodSub_J2_sup_J4 (ModelData.uni hF) _ h4 e

end CFSG.GH74.Generic

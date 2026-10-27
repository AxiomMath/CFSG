module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5g0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5Norm

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem exists_Z (ha : Ctx4P t L S x₁ x₂ lam rho tau) :
    ∃ Z : Subgroup G, fourGrp x₁ x₂ ≤ Z ∧ Z ≤ ctxO t tau x₁ x₂ ∧ 16 ≤ Nat.card Z ∧
      (∀ z ∈ Z, ∀ p ∈ ctxPL t tau x₁ x₂, z * p * z⁻¹ * p⁻¹ ∈ fourGrp x₁ x₂) ∧
      (∀ g ∈ ctxLO t tau x₁ x₂, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z) := by
  obtain ⟨Z, hZ⟩ := exists_zP (ctxPL t tau x₁ x₂) (fourGrp x₁ x₂) (P_comm_V ha)
  refine ⟨Z, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro v hv
    rw [hZ v]
    refine ⟨V_le_P ha hv, fun q hq => ?_⟩
    have hvq : v * q = q * v := (P_comm_V ha q hq v hv).symm
    have h1 : v * q * v⁻¹ * q⁻¹ = 1 := by rw [hvq]; group
    rw [h1]
    exact (fourGrp x₁ x₂).one_mem
  ·
    intro z hz
    exact ha.CL_Obar z (P_le_LO ha ((hZ z).mp hz).1)
      (fun o ho => ((hZ z).mp hz).2 o (O_le_ctxPL ha.toCtx4A ho))
  ·
    obtain ⟨A, _hVA, hAP, hcardA, hA⟩ := ha.Z_P
    have hAZ : A ≤ Z := fun a ha' => (hZ a).mpr ⟨hAP ha', fun q hq => hA a ha' q hq⟩
    have hcardAZ : Nat.card A ≤ Nat.card Z := Subgroup.card_le_of_le hAZ
    have h16 : 16 ≤ Nat.card A := by
      rw [card_fourGrp ha.toCtx4L.toCtx4Q] at hcardA
      simpa using hcardA
    exact le_trans h16 hcardAZ
  ·
    intro z hz p hp
    exact ((hZ z).mp hz).2 p hp
  ·
    intro g hg z hz
    rw [hZ (g * z * g⁻¹)]
    refine ⟨LO_conj_P ha g hg z ((hZ z).mp hz).1, fun q hq => ?_⟩
    have hq' : g⁻¹ * q * g ∈ ctxPL t tau x₁ x₂ := by
      have h := LO_conj_P ha g⁻¹ (inv_mem hg) q hq
      simpa using h
    have hzq' : z * (g⁻¹ * q * g) * z⁻¹ * (g⁻¹ * q * g)⁻¹ ∈ fourGrp x₁ x₂ :=
      ((hZ z).mp hz).2 (g⁻¹ * q * g) hq'
    have heq : (g * z * g⁻¹) * q * (g * z * g⁻¹)⁻¹ * q⁻¹
        = g * (z * (g⁻¹ * q * g) * z⁻¹ * (g⁻¹ * q * g)⁻¹) * g⁻¹ := by group
    rw [heq]
    exact LO_conj_V ha g hg _ hzq'

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z

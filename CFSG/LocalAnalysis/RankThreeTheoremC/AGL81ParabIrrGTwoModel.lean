module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrGTwoLevi
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrGTwoTorus
import CFSG.GH74.GLS.Stage2.OddAut.HeisField

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.GTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.GTwo


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_conj_of_wCent {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {A : Subgroup (adjointGroup .G2 K)} (hBA : borel (g2Datum K) (torus (τ := .G2) K) ≤ A)
    {i : Fin (Tag.rank .G2)} (hI : negIndices (g2Datum K) A = {i})
    {β : MulAut (adjointGroup .G2 K)} (hAβ : ∀ a ∈ A, β a ∈ A)
    (hWβ : ∀ s ∈ rankOne (g2Datum K).rootGroup i, β s * s⁻¹ ∈ CFSG.Open.pCoreOf 2 A) :
    ∃ g ∈ A, β = MulAut.conj g ∧
      ∀ s ∈ rankOne (g2Datum K).rootGroup i, g * s * g⁻¹ * s⁻¹ ∈ CFSG.Open.pCoreOf 2 A := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨g, hg, σ, rfl⟩ := exists_mem_conj_mul hf hK hBA hAβ
  have hσ : σ = 1 := eq_one_of_conj_mul_mem h4 hBA hI hg σ fun s hs => by
    simpa [MulAut.conj_apply] using hWβ s hs
  subst hσ
  refine ⟨g, hg, by simp, fun s hs => ?_⟩
  simpa [MulAut.conj_apply] using hWβ s hs

theorem g2_model_pow {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {A : Subgroup (adjointGroup .G2 K)} (hBA : borel (g2Datum K) (torus (τ := .G2) K) ≤ A)
    {i : Fin (Tag.rank .G2)} (hI : negIndices (g2Datum K) A = {i})
    {α : MulAut (adjointGroup .G2 K)} (hAα : ∀ a ∈ A, α a ∈ A) :
    ∃ k : ℕ, ∀ β : MulAut (adjointGroup .G2 K), (∀ a ∈ A, β a ∈ A) →
      (∀ s ∈ rankOne (g2Datum K).rootGroup i, β s * s⁻¹ ∈ CFSG.Open.pCoreOf 2 A) →
      ∃ j : ℕ, (α * β * α⁻¹ * (β ^ 2 ^ k)⁻¹) ^ 2 ^ j = 1 := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hD := parabLeviData h4 hBA hI
  obtain ⟨h, hh, σ, rfl⟩ := exists_mem_conj_mul hf hK hBA hAα
  obtain ⟨k, -, hk⟩ :=
    CFSG.GH74.GLS.Stage2.OddAut.exists_frobenius_pow Nat.prime_two (by omega) hK σ
  refine ⟨k, fun β hAβ hWβ => ?_⟩
  obtain ⟨g, hg, rfl, hgL⟩ := exists_conj_of_wCent hf hK hBA hI hAβ hWβ
  have hST : ∀ t ∈ ⨆ k, torus (τ := .G2) K k, g2FieldHom K σ t = t ^ 2 ^ k := fun t ht =>
    g2FieldHom_eq_pow_of_mem_torus hk (fun a ha b hb => hD.T_comm a ha b hb) ht
  have hmem := hD.mem_core (S := g2FieldHom K σ) (n := 2 ^ k)
    (fun x hx => g2FieldHom_mem_rankOne σ i hx)
    (fun x hx => by rw [← map_inv]; exact g2FieldHom_mem_rankOne σ⁻¹ i hx)
    (fun u hu => g2FieldHom_mem_posUnipotentExcept σ i hu) hST hg hgL hh
  obtain ⟨j, hj⟩ := isPGroup_pCoreOf A ⟨_, hmem⟩
  refine ⟨j, ?_⟩
  have key : MulAut.conj h * g2FieldHom K σ * MulAut.conj g =
      MulAut.conj (h * g2FieldHom K σ g * h⁻¹) * (MulAut.conj h * g2FieldHom K σ) := by
    refine MulEquiv.ext fun x => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply]
    simp only [map_mul, map_inv]
    group
  have hid : MulAut.conj h * g2FieldHom K σ * MulAut.conj g * (MulAut.conj h * g2FieldHom K σ)⁻¹ *
      (MulAut.conj g ^ 2 ^ k)⁻¹ =
        MulAut.conj (h * g2FieldHom K σ g * h⁻¹ * (g ^ 2 ^ k)⁻¹) := by
    rw [key, mul_inv_cancel_right, ← map_pow, ← map_inv, ← map_mul]
  rw [hid, ← map_pow]
  have hD1 : (h * g2FieldHom K σ g * h⁻¹ * (g ^ 2 ^ k)⁻¹) ^ 2 ^ j = 1 := by
    simpa using congrArg Subtype.val hj
  rw [hD1, map_one]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.GTwo

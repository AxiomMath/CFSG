module

import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeAltSix
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.LocalAnalysis.ComponentClassification.HSFLitConjOrbit
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenSolvDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding Subgroup
open scoped commutatorElement

namespace SolvNone

variable {Y X I₀ : Type} [Group Y] [Group X] [Group I₀] [Finite I₀]

theorem symThree_of_autCond {π : Y →* X} {Y₀ : Subgroup Y} {N : Subgroup X} (σ : I₀ →* Y)
    (hσY : σ.range ≤ Y₀) (hNn : Y₀.map π ≤ normalizer (N : Set X)) (hNp : IsPGroup 3 N)
    (hN : ∀ y ∈ Y₀, (∃ k : ℕ, y ^ 3 ^ k = 1) → π y ∈ N)
    (hker : (π.comp σ).ker ≤ CFSG.pCore 2 I₀) (hcond : SolvThreeAutCond Y₀ σ) :
    Nonempty (I₀ ⧸ CFSG.pCore 2 I₀ ≃* Equiv.Perm (Fin 3)) := by
  rcases hcond with h | ⟨y, hyY, hy3, α, hα, g, hg⟩
  · exact h
  exfalso
  apply hg
  have hσu : σ (α g * g⁻¹) = y * σ g * y⁻¹ * (σ g)⁻¹ := by rw [map_mul, map_inv, hα]
  have hπu : π (σ (α g * g⁻¹)) ∈ N := by
    rw [hσu, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h1 : π y ∈ N := hN y hyY hy3
    have hgN : π (σ g) ∈ normalizer (N : Set X) :=
      hNn ⟨σ g, hσY (MonoidHom.mem_range.mpr ⟨g, rfl⟩), rfl⟩
    have h2 : π (σ g) * (π y)⁻¹ * (π (σ g))⁻¹ ∈ N :=
      (mem_normalizer_iff.mp hgN _).mp (N.inv_mem h1)
    have he : π y * π (σ g) * (π y)⁻¹ * (π (σ g))⁻¹ =
        π y * (π (σ g) * (π y)⁻¹ * (π (σ g))⁻¹) := by group
    rw [he]
    exact N.mul_mem h1 h2
  obtain ⟨m, hm⟩ := hNp ⟨_, hπu⟩
  have hm' : (π.comp σ) ((α g * g⁻¹) ^ 3 ^ m) = 1 := by
    rw [map_pow]
    simpa using congrArg Subtype.val hm
  have hu2 : (α g * g⁻¹) ^ 3 ^ m ∈ CFSG.pCore 2 I₀ := hker hm'
  have hodd : Odd (orderOf (QuotientGroup.mk' (CFSG.pCore 2 I₀) (α g * g⁻¹))) := by
    have h1 : (QuotientGroup.mk' (CFSG.pCore 2 I₀) (α g * g⁻¹)) ^ 3 ^ m = 1 := by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hu2
    exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one h1)
  obtain ⟨g', hg', hgu⟩ := exists_oUpperTwo_of_odd (QuotientGroup.mk' (CFSG.pCore 2 I₀))
    (MonoidHom.mem_range.mpr ⟨α g * g⁻¹, rfl⟩) hodd
  have h2 : g'⁻¹ * (α g * g⁻¹) ∈ CFSG.pCore 2 I₀ := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hgu
    exact QuotientGroup.eq.mp hgu
  have he : α g * g⁻¹ = g' * (g'⁻¹ * (α g * g⁻¹)) := by group
  rw [he]
  exact Subgroup.mul_mem_sup hg' h2

private theorem mem_of_inv_of_isSubnormal {D H : Subgroup X} (hD : IsSubnormal D H) {t v : X}
    (htD : t ∈ D) (hvH : v ∈ H) (htv : t * v * t⁻¹ = v⁻¹) (hodd : Odd (orderOf v)) : v ∈ D := by
  have hct : ⁅v, t⁆ = v ^ 2 := by
    rw [commutatorElement_def]
    calc v * t * v⁻¹ * t⁻¹ = v * (t * v * t⁻¹)⁻¹ := by group
      _ = v ^ 2 := by rw [htv, inv_inv, sq]
  have hvz : v ∈ zpowers (v ^ 2) := by
    obtain ⟨j, hj⟩ := hodd
    refine ⟨((j + 1 : ℕ) : ℤ), ?_⟩
    change (v ^ 2) ^ ((j + 1 : ℕ) : ℤ) = v
    rw [zpow_natCast, ← pow_mul, show 2 * (j + 1) = orderOf v + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hiter : ∀ n : ℕ, zpowers v ≤ (fun A : Subgroup X => ⁅A, D⁆)^[n] (zpowers v) := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      refine zpowers_le.mpr ?_
      have hm : ⁅v, t⁆ ∈ ⁅(fun A : Subgroup X => ⁅A, D⁆)^[n] (zpowers v), D⁆ :=
        Subgroup.commutator_mem_commutator (ih (mem_zpowers v)) htD
      rw [hct] at hm
      exact (zpowers_le.mpr hm) hvz
  obtain ⟨d, hd⟩ := exists_iterate_commutator_le_of_isSubnormal hD (zpowers_le.mpr hvH)
  exact hd (hiter d (mem_zpowers v))

theorem relIndex_centralizer_le_of_isSubnormal [Finite X] {H D T W : Subgroup X}
    (hD : IsSubnormal D H) (hTH : T ≤ H) (hT : IsPGroup 3 T) {t : X} (htD : t ∈ D)
    (ht2 : t ^ 2 = 1) (htT : t ∈ normalizer (T : Set X))
    (hW : ∀ v ∈ D, (∃ k : ℕ, v ^ 3 ^ k = 1) → v ∈ W) :
    (T ⊓ centralizer ({t} : Set X)).relIndex T ≤ Nat.card W := by
  rw [CFSG.ComponentClassification.HSFLit.relIndex_inf_centralizer_eq_ncard T t]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq, ht2])
  have hsub : (fun y => y * t⁻¹) '' {y | ∃ g ∈ T, g * t * g⁻¹ = y} ⊆ (W : Set X) := by
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    set v := g * t * g⁻¹ * t⁻¹ with hv
    have hvT : v ∈ T := by
      have h1 : t * g⁻¹ * t⁻¹ ∈ T := (mem_normalizer_iff.mp htT _).mp (T.inv_mem hg)
      have he : v = g * (t * g⁻¹ * t⁻¹) := by rw [hv]; group
      rw [he]
      exact T.mul_mem hg h1
    have htv : t * v * t⁻¹ = v⁻¹ := by
      rw [hv]
      calc t * (g * t * g⁻¹ * t⁻¹) * t⁻¹ = t * g * t * g⁻¹ * (t⁻¹ * t⁻¹) := by group
        _ = t * g * t * g⁻¹ := by rw [htinv, ← sq, ht2, mul_one]
        _ = (g * t * g⁻¹ * t⁻¹)⁻¹ := by
          have he : (g * t * g⁻¹ * t⁻¹)⁻¹ = t * g * t⁻¹ * g⁻¹ := by group
          rw [he, htinv]
    obtain ⟨k, hk⟩ := hT ⟨v, hvT⟩
    have hk' : v ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hodd : Odd (orderOf v) :=
      Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one hk')
    exact hW v (mem_of_inv_of_isSubnormal hD htD (hTH hvT) htv hodd) ⟨k, hk'⟩
  calc {y | ∃ g ∈ T, g * t * g⁻¹ = y}.ncard
      = ((fun y => y * t⁻¹) '' {y | ∃ g ∈ T, g * t * g⁻¹ = y}).ncard :=
        (Set.ncard_image_of_injective _ (mul_left_injective t⁻¹)).symm
    _ ≤ (W : Set X).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card W := by rw [← Nat.card_coe_set_eq]; rfl

end SolvNone

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

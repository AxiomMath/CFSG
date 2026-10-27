module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ8

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement


section Filt

variable {G : Type*} [Group G] [Finite G] {H N : Subgroup G}

theorem card_inf_le_mul (h : IsLayer H N) (A : Subgroup G) (S : Set (Lyr h))
    (hS : ∀ a (ha : a ∈ A) (haH : a ∈ H), Lyr.mk h ⟨a, haH⟩ ∈ S) :
    Nat.card ↥(A ⊓ H) ≤ Nat.card S * Nat.card ↥(A ⊓ N) := by
  have h1 := Subgroup.relIndex_mul_card (H := A ⊓ N) (K := A ⊓ H)
  have e : (A ⊓ N) ⊓ (A ⊓ H) = A ⊓ N := inf_eq_left.2 (inf_le_inf_left A h.le)
  rw [e] at h1
  rw [← h1]
  exact Nat.mul_le_mul_right _ (Lyr.relIndex_inf_le h A S hS)

end Filt

section Invol

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 3] {J : Set (Fin τ.rank)}

theorem lconj_involutive {Γ : ModGL τ K} (hΓ : NormAll J Γ) {d : ℤ} (hd : 1 ≤ d)
    (h2 : ∀ x ∈ degSeries τ K J d, Γ * Γ * x * (Γ * Γ)⁻¹ = x)
    (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) :
    lconj hΓ hd (lconj hΓ hd z) = z := by
  rw [← lconj_mul hΓ hΓ hd z]
  obtain ⟨x, rfl⟩ := Lyr.mk_surjective _ z
  rw [lconj_mk]
  congr 1
  exact Subtype.ext (h2 x.1 x.2)

theorem card_fix_sq_of_N {Γ y q : ModGL τ K} (hΓ : NormAll J Γ) (hy : NormAll J y)
    (hq : q ∈ parabolicRadical τ K J)
    (h : y * Γ * y⁻¹ = q * (rootDiagUnit τ (zetaDiag (K := K) J) * Γ)) {d : ℤ} (hd : 1 ≤ d)
    (hodd : Odd d) (h2 : ∀ x ∈ degSeries τ K J d, Γ * Γ * x * (Γ * Γ)⁻¹ = x) :
    Nat.card (fixSp (lconj hΓ hd)) ^ 2 =
      Nat.card (Lyr (isLayer_degSeries (K := K) (J := J) hd)) := by
  let Y : Lyr (isLayer_degSeries (K := K) (J := J) hd) ≃ₗ[ZMod 3]
      Lyr (isLayer_degSeries (K := K) (J := J) hd) :=
    LinearEquiv.ofLinear (lconj hy hd) (lconj hy.inv hd)
      (LinearMap.ext fun z => lconj_lconj_inv hy hd z)
      (LinearMap.ext fun z => lconj_inv_lconj hy hd z)
  exact card_sq_of_anticomm (lconj hΓ hd) (lconj_involutive hΓ hd h2) Y
    (fun x => lconj_anticomm_odd hΓ hy hq h hd hodd x)

end Invol

end CFSG.LocalAnalysis.GLTheoremA

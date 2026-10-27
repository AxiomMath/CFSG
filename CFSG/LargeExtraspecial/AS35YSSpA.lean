module

public import CFSG.LargeExtraspecial.AS35QCoNat
public import CFSG.LargeExtraspecial.AS35TMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions
  CFSG.Sporadic.Co2Smith

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem false_of_small_YS (hS : S.SixHyp)
    (hst : S.Asc512Standing) (θ : S.LbarAsc ≃* Sp62) (hZ : center S.LbarAsc = ⊥) {g : G}
    (ht : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) (W' : Submodule (ZMod 2) S.Qt)
    (hW' : ∀ m ∈ S.Mbar, ∀ w ∈ W', (m : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W')
    (hWfix : W' ≤ fixSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (hWc : ¬ W' ≤ commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (hcard : Nat.card W' ≤ 4) : False := by
  obtain ⟨Φ, hΦ⟩ := AS35QCo.exists_retraction S hst θ hZ
  have htD : S.ρ ⟨_, htM⟩ ∈ S.DbarAsc := ⟨_, ht, htM, rfl⟩
  have hτL : S.ρ ⟨_, htM⟩ ∈ S.LbarAsc := subset_closure htD
  have hτA := AS35QCo.isTypeA_of_mem_dbar S hS htD
  obtain ⟨Y, hYP, hτY, hYnot, hYcard, hYnorm⟩ :=
    S14.asc512SymStmt G S hS g ht htM W' hW' hWfix hWc
  obtain ⟨-, hext, -, hcent, -, -, -⟩ := S14.asc512PbarStmt G S hS g ht htM
  have hPM : S.PbarAsc g ≤ S.Mbar := map_le_range _ _
  generalize S.ρ ⟨g * S.z * g⁻¹, htM⟩ = τ at htD hτL hτA hτY hYnot hYnorm hext hcent
  obtain ⟨hτc, hconjP⟩ := AS35QCo.pbar_facts S hext hcent
  obtain ⟨y, hyY, hyz⟩ : ∃ y ∈ Y, y ∉ zpowers τ := by
    by_contra h
    push Not at h
    exact hYnot h
  have hy1 : y ≠ 1 := fun h => hyz (h ▸ one_mem _)
  have hyτ : y ≠ τ := fun h => hyz (h ▸ mem_zpowers τ)
  have hyP : y ∈ S.PbarAsc g := hYP hyY
  obtain ⟨p, hpP, hpy⟩ := hconjP y hyP hy1 hyτ
  have hyM := hPM hyP
  have hpM := hPM hpP
  have hyτc := hτc y hyP
  have hpτ := hτc p hpP
  have hττ : τ * τ = 1 := Subtype.ext hτA.2.2.1
  have hτ1 : τ ≠ 1 := fun h => hτA.2.1 (congrArg Subtype.val h)
  have hτM := AS35QCo.lbar_le_mbar S hτL
  have hsmall := AS35QCo.ncard_conj_le S θ Φ hΦ hτL hτ1 hτY hyY hy1 hyτ hyM (by omega) hYnorm
  have hprod := AS35QCo.orderOf_mem_of_typeA S θ hτL hτA
  have hΦτ : Φ ⟨τ, hτM⟩ = θ ⟨τ, hτL⟩ := hΦ τ hτL
  generalize hθτ : θ ⟨τ, hτL⟩ = τ' at hsmall hprod hΦτ
  generalize hy' : Φ ⟨y, hyM⟩ = y' at hsmall
  generalize hh₀ : Φ ⟨p, hpM⟩ = h₀
  have hcomm' : ∀ (a b : S.O) (ha : a ∈ S.Mbar) (hb : b ∈ S.Mbar), a * b = b * a →
      Φ ⟨a, ha⟩ * Φ ⟨b, hb⟩ = Φ ⟨b, hb⟩ * Φ ⟨a, ha⟩ := fun a b ha hb h => by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h
  have hτ'τ' : τ' * τ' = 1 := by
    rw [← hθτ, ← map_mul, ← map_one θ]
    congr 1
    exact Subtype.ext hττ
  have hτ'1 : τ' ≠ 1 := fun h => hτ1 (by
    have h' : θ ⟨τ, hτL⟩ = θ 1 := hθτ.trans (h.trans (map_one θ).symm)
    exact congrArg Subtype.val (θ.injective h'))
  have hy'τ' : y' * τ' = τ' * y' := by
    rw [← hy', ← hΦτ]
    exact hcomm' _ _ hyM hτM hyτc
  have hh₀τ' : h₀ * τ' = τ' * h₀ := by
    rw [← hh₀, ← hΦτ]
    exact hcomm' _ _ hpM hτM hpτ
  have hconj : h₀ * y' * h₀⁻¹ = τ' * y' := by
    have e : Φ (⟨p, hpM⟩ * ⟨y, hyM⟩ * (⟨p, hpM⟩ : S.Mbar)⁻¹) = Φ (⟨τ, hτM⟩ * ⟨y, hyM⟩) := by
      congr 1
      exact Subtype.ext hpy
    simp only [map_mul, map_inv, hy', hh₀, hΦτ] at e
    exact e
  have hy'1 : y' ≠ 1 := by
    intro h
    rw [h, mul_one, mul_inv_cancel, mul_one] at hconj
    exact hτ'1 hconj.symm
  have hy'τ'' : y' ≠ τ' := by
    intro h
    rw [h, hτ'τ', hh₀τ', mul_assoc, mul_inv_cancel, mul_one] at hconj
    exact hτ'1 hconj
  have hy'C : y' ∈ centralizer ({τ'} : Set Sp62) := mem_centralizer_singleton_iff.mpr hy'τ'
  have hh₀C : h₀ ∈ centralizer ({τ'} : Set Sp62) := mem_centralizer_singleton_iff.mpr hh₀τ'
  exact AS35QCo.false_of_small_conj hτ'τ' hτ'1 hprod hy'C hy'1 hy'τ'' hsmall hh₀C hconj

end Setting

end CFSG.LargeExtraspecial

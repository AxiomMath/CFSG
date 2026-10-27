module

public import CFSG.RankThree.PartTwo.Sec11.Wreath
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28IVWreathBase
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup CFSG.RankThree.PartTwo.Sec11

theorem l28iv_isEmpty_quotient_wreath {Q : Type*} [Group Q] [Finite Q] {t z : Q}
    (htz : t * z = z * t) (hidx : Nat.card Q ≤ 3 * Nat.card ↥(zpowers t ⊔ zpowers z))
    (K : Subgroup Q) [K.Normal] : IsEmpty ((Q ⧸ K) ≃* W33) := by
  refine ⟨fun e => ?_⟩
  set A : Subgroup Q := zpowers t ⊔ zpowers z with hA
  set f : Q →* W33 := e.toMonoidHom.comp (QuotientGroup.mk' K) with hf
  have hfs : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective K)
  have hcomm : ∀ a ∈ zpowers t, ∀ c ∈ zpowers z, a * c = c * a := by
    intro a ha c hc
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
    exact (Commute.zpow_zpow (show Commute t z from htz) i j).eq
  set B : Subgroup W33 := A.map f with hB
  have hBeq : B = zpowers (f t) ⊔ zpowers (f z) := by
    rw [hB, hA, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  have hcommB : ∀ a ∈ zpowers (f t), ∀ c ∈ zpowers (f z), a * c = c * a := by
    intro a ha c hc
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
    exact (Commute.zpow_zpow (show Commute (f t) (f z) by
      show f t * f z = f z * f t
      rw [← map_mul, ← map_mul, htz]) i j).eq
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rw [hBeq]
    intro a ha b hb
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := u3l42_decomp hcommB ha
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := u3l42_decomp hcommB hb
    have h1 : a₁ * b₁ = b₁ * a₁ := by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha₁
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb₁
      exact (Commute.zpow_zpow_self (f t) i j).eq
    have h2 : a₂ * b₂ = b₂ * a₂ := by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha₂
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb₂
      exact (Commute.zpow_zpow_self (f z) i j).eq
    have h3 := hcommB b₁ hb₁ a₂ ha₂
    have h4 := hcommB a₁ ha₁ b₂ hb₂
    calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
      _ = a₁ * (b₁ * a₂) * b₂ := by rw [h3]
      _ = (a₁ * b₁) * (a₂ * b₂) := by group
      _ = (b₁ * a₁) * (b₂ * a₂) := by rw [h1, h2]
      _ = b₁ * (a₁ * b₂) * a₂ := by group
      _ = b₁ * (b₂ * a₁) * a₂ := by rw [h4]
      _ = b₁ * b₂ * (a₁ * a₂) := by group
  have hBcard : 27 ≤ Nat.card B := by
    have hApos : 0 < Nat.card A := Nat.card_pos
    have hAidx : A.index ≤ 3 := by
      have h := A.index_mul_card
      by_contra hlt
      push Not at hlt
      have : 4 * Nat.card A ≤ A.index * Nat.card A := Nat.mul_le_mul_right _ hlt
      omega
    have hBidx : B.index ∣ A.index := Subgroup.index_map_dvd A hfs
    have hBidx3 : B.index ≤ 3 := (Nat.le_of_dvd (Nat.pos_of_ne_zero
      Subgroup.index_ne_zero_of_finite) hBidx).trans hAidx
    have h81 : B.index * Nat.card B = 81 := by rw [Subgroup.index_mul_card, card_wreath]
    by_contra hlt
    push Not at hlt
    have : B.index * Nat.card B ≤ 3 * 26 := Nat.mul_le_mul hBidx3 (by omega)
    omega
  have hexp := l28iv_w33_pow_three_of_abelian hBab hBcard
  have hft : f t ^ 3 = 1 := hexp _ ⟨t, mem_sup_left (mem_zpowers t), rfl⟩
  have hfz : f z ^ 3 = 1 := hexp _ ⟨z, mem_sup_right (mem_zpowers z), rfl⟩
  have hle : Nat.card B ≤ 9 := by
    rw [hBeq]
    set U := zpowers (f t)
    set V := zpowers (f z)
    let m : U × V → ↥(U ⊔ V) := fun p => ⟨p.1 * p.2, mul_mem_sup p.1.2 p.2.2⟩
    have hm : Function.Surjective m := by
      rintro ⟨w, hw⟩
      obtain ⟨u, hu, v, hv, rfl⟩ := u3l42_decomp hcommB hw
      exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
    have hU : Nat.card U ≤ 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) hft
    have hV : Nat.card V ≤ 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) hfz
    calc Nat.card ↥(U ⊔ V) ≤ Nat.card (U × V) := Nat.card_le_card_of_surjective m hm
      _ = Nat.card U * Nat.card V := Nat.card_prod _ _
      _ ≤ 3 * 3 := Nat.mul_le_mul hU hV
      _ = 9 := by norm_num
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC

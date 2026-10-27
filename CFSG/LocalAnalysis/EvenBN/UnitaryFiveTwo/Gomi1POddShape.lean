module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1POddQuad
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1POddBound

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open Subgroup CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open scoped MatrixGroups

theorem gomiOdd_mem_zpowers_of_sq {G : Type*} [Group G] {z g : G} (hz : z * z = 1)
    (hg : g ∈ Subgroup.zpowers z) : g = 1 ∨ g = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
  obtain ⟨n, hn | hn⟩ := Int.even_or_odd' k
  · left
    rw [hn, zpow_mul, h2, one_zpow]
  · right
    rw [hn, zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

@[expose] def gomiMulHom {Y : Type*} [Group Y] (I₁ I₂ : Subgroup Y)
    (hcomm : ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a) : ↥I₁ × ↥I₂ →* Y where
  toFun p := (p.1 : Y) * (p.2 : Y)
  map_one' := by simp
  map_mul' p q := by
    have h := hcomm (q.1 : Y) q.1.2 (p.2 : Y) p.2.2
    show ((p.1 : Y) * q.1) * ((p.2 : Y) * q.2) = ((p.1 : Y) * p.2) * ((q.1 : Y) * q.2)
    calc ((p.1 : Y) * q.1) * ((p.2 : Y) * q.2)
        = (p.1 : Y) * ((q.1 : Y) * p.2) * q.2 := by group
      _ = (p.1 : Y) * ((p.2 : Y) * q.1) * q.2 := by rw [h]
      _ = ((p.1 : Y) * p.2) * ((q.1 : Y) * q.2) := by group

theorem gomiMulHom_apply {Y : Type*} [Group Y] (I₁ I₂ : Subgroup Y)
    (hcomm : ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a) (p : ↥I₁ × ↥I₂) :
    gomiMulHom I₁ I₂ hcomm p = (p.1 : Y) * (p.2 : Y) := rfl

variable {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem gomiOdd_false_of_shape [Finite Y] (h₁ : (2 : F₁) ≠ 0) (h₂ : (2 : F₂) ≠ 0)
    (S : Shape Y F₁ F₂) (E : Subgroup Y) (hEcard : Nat.card E = 2 ^ 6)
    (hEsq : ∀ x ∈ E, x * x = 1) : False := by
  haveI : S.I₁.Normal := S.normal₁
  haveI : S.I₂.Normal := S.normal₂
  set J : Subgroup Y := S.I₁ ⊔ S.I₂ with hJ
  haveI hJn : J.Normal := inferInstance
  have hYJ : ∀ g : Y, g ∈ J ∨ g * S.t ∈ J := by
    intro g
    have hg : g ∈ J ⊔ Subgroup.zpowers S.t := by
      rw [hJ, S.gen]
      exact Subgroup.mem_top g
    obtain ⟨n, hn, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    rcases gomiOdd_mem_zpowers_of_sq S.t_sq hh with rfl | rfl
    · exact Or.inl (by simpa using hn)
    · right
      rw [mul_assoc, S.t_sq, mul_one]
      exact hn
  set A : Subgroup Y := E ⊓ J with hA
  have hEA : Nat.card E ≤ 2 * Nat.card A := by
    by_cases hEJ : E ≤ J
    · refine gomiOdd_card_le_two_mul E A 1 ?_
      intro x hx
      exact Or.inl ⟨hx, hEJ hx⟩
    · obtain ⟨y₀, hy₀E, hy₀J⟩ := SetLike.not_le_iff_exists.mp hEJ
      refine gomiOdd_card_le_two_mul E A y₀ ?_
      intro x hx
      by_cases hxJ : x ∈ J
      · exact Or.inl ⟨hx, hxJ⟩
      · right
        refine ⟨E.mul_mem (E.inv_mem hy₀E) hx, ?_⟩
        have ha : y₀ * S.t ∈ J := (hYJ y₀).resolve_left hy₀J
        have hb : x * S.t ∈ J := (hYJ x).resolve_left hxJ
        have : y₀⁻¹ * x = S.t * ((y₀ * S.t)⁻¹ * (x * S.t)) * S.t⁻¹ := by group
        rw [this]
        exact hJn.conj_mem _ (J.mul_mem (J.inv_mem ha) hb) S.t
  set μ := gomiMulHom S.I₁ S.I₂ S.comm with hμ
  set P : Subgroup (↥S.I₁ × ↥S.I₂) := A.comap μ with hP
  set zI₁ : ↥S.I₁ := ⟨S.z, S.z_mem₁⟩ with hzI₁
  set zI₂ : ↥S.I₂ := ⟨S.z, S.z_mem₂⟩ with hzI₂
  have hAE : A ≤ E := inf_le_left
  have hzP : (zI₁, zI₂) ∈ P := by
    rw [hP, Subgroup.mem_comap, gomiMulHom_apply]
    show S.z * S.z ∈ A
    rw [S.z_sq]
    exact A.one_mem
  set zQ : ↥P := ⟨(zI₁, zI₂), hzP⟩ with hzQ
  have hcen₁ : ∀ a : ↥S.I₁, a * zI₁ = zI₁ * a := by
    intro a
    apply S.e₁.injective
    rw [map_mul, map_mul, show S.e₁ zI₁ = -1 from S.e₁_z]
    simp
  have hcen₂ : ∀ b : ↥S.I₂, b * zI₂ = zI₂ * b := by
    intro b
    apply S.e₂.injective
    rw [map_mul, map_mul, show S.e₂ zI₂ = -1 from S.e₂_z]
    simp
  have hsq : ∀ x : ↥P, x * x = 1 ∨ x * x = zQ := by
    rintro ⟨⟨a, b⟩, hx⟩
    have hxA : (a : Y) * b ∈ A := by
      rw [hP, Subgroup.mem_comap, gomiMulHom_apply] at hx
      exact hx
    have h1 : ((a : Y) * b) * ((a : Y) * b) = 1 := hEsq _ (hAE hxA)
    have hab : (a : Y) * b = b * a := S.comm a a.2 b b.2
    have h2 : ((a : Y) * a) * ((b : Y) * b) = 1 := by
      calc ((a : Y) * a) * ((b : Y) * b) = (a : Y) * ((a : Y) * b) * b := by group
        _ = (a : Y) * ((b : Y) * a) * b := by rw [hab]
        _ = ((a : Y) * b) * ((a : Y) * b) := by group
        _ = 1 := h1
    have h3 : (a : Y) * a = ((b : Y) * b)⁻¹ := eq_inv_of_mul_eq_one_left h2
    have hmem : ((a : Y) * a) ∈ S.I₁ ⊓ S.I₂ := by
      refine ⟨S.I₁.mul_mem a.2 a.2, ?_⟩
      rw [h3]
      exact S.I₂.inv_mem (S.I₂.mul_mem b.2 b.2)
    rw [S.inter] at hmem
    rcases gomiOdd_mem_zpowers_of_sq S.z_sq hmem with h4 | h4
    · left
      have h5 : (b : Y) * b = 1 := by
        rw [h4, one_mul] at h2
        exact h2
      apply Subtype.ext
      apply Prod.ext
      · exact Subtype.ext h4
      · exact Subtype.ext h5
    · right
      have h5 : (b : Y) * b = S.z := by
        rw [h4] at h3
        have : ((b : Y) * b)⁻¹ = S.z := h3.symm
        calc (b : Y) * b = ((b : Y) * b)⁻¹⁻¹ := (inv_inv _).symm
          _ = S.z⁻¹ := by rw [this]
          _ = S.z := inv_eq_of_mul_eq_one_right S.z_sq
      apply Subtype.ext
      apply Prod.ext
      · exact Subtype.ext h4
      · exact Subtype.ext h5
  have hquad : GomiQuad ↥P zQ := by
    refine ⟨?_, ?_, hsq⟩
    · rintro ⟨⟨a, b⟩, hx⟩
      apply Subtype.ext
      apply Prod.ext
      · exact hcen₁ a
      · exact hcen₂ b
    · apply Subtype.ext
      apply Prod.ext
      · exact Subtype.ext S.z_sq
      · exact Subtype.ext S.z_sq
  have hbound : ∀ W : Subgroup ↥P, GomiElemAb W → Nat.card W ≤ 4 := by
    intro W hW
    have hA₁ : ∀ a : ↥S.I₁, a * a = 1 → a = 1 ∨ a = zI₁ := by
      intro a ha
      have : (S.e₁ a)⁻¹ = S.e₁ a := by
        rw [← map_inv]
        congr 1
        exact inv_eq_of_mul_eq_one_right ha
      rcases CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self F₁ h₁ _ this with
        h | h
      · left
        exact S.e₁.injective (by rw [h, map_one])
      · right
        refine S.e₁.injective ?_
        rw [h, show S.e₁ zI₁ = -1 from S.e₁_z]
        rfl
    have hB₂ : ∀ b : ↥S.I₂, b * b = 1 → b = 1 ∨ b = zI₂ := by
      intro b hb
      have : (S.e₂ b)⁻¹ = S.e₂ b := by
        rw [← map_inv]
        congr 1
        exact inv_eq_of_mul_eq_one_right hb
      rcases CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self F₂ h₂ _ this with
        h | h
      · left
        exact S.e₂.injective (by rw [h, map_one])
      · right
        refine S.e₂.injective ?_
        rw [h, show S.e₂ zI₂ = -1 from S.e₂_z]
        rfl
    set W' : Subgroup (↥S.I₁ × ↥S.I₂) := W.map P.subtype with hW'
    have hW'card : Nat.card W' = Nat.card W := by
      rw [hW']
      exact Subgroup.card_map_of_injective Subtype.val_injective
    have hsqW : ∀ w ∈ W', w * w = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      have := hW.2 x hx
      exact congrArg Subtype.val this
    rw [← hW'card]
    exact gomiOdd_card_le_four_of_prod zI₁ zI₂ hA₁ hB₂ W' hsqW
  have hle := hquad.card_le_thirty_two hbound
  let φ : ↥P →* ↥A := (μ.comp P.subtype).codRestrict A (fun x => x.2)
  have hφ : Function.Surjective φ := by
    rintro ⟨g, hg⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp (hg.2 : g ∈ J)
    have hmem : ((⟨a, ha⟩ : ↥S.I₁), (⟨b, hb⟩ : ↥S.I₂)) ∈ P := by
      rw [hP, Subgroup.mem_comap, gomiMulHom_apply]
      show a * b ∈ A
      rw [hab]
      exact hg
    exact ⟨⟨_, hmem⟩, Subtype.ext hab⟩
  have hzker : zQ ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show S.z * S.z = 1
    exact S.z_sq
  have hzne : zQ ≠ 1 := by
    intro h
    have := congrArg (fun x : ↥P => ((x : ↥S.I₁ × ↥S.I₂).1 : Y)) h
    exact S.z_ne this
  have hker : 1 < Nat.card φ.ker := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hzker
    exact hzne hzker
  have hPcard : Nat.card ↥P = Nat.card (↥P ⧸ φ.ker) * Nat.card φ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hquot : Nat.card (↥P ⧸ φ.ker) = Nat.card A :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv
  rw [hquot] at hPcard
  have hApos : 0 < Nat.card A := Nat.card_pos
  have h2A : 2 * Nat.card A ≤ Nat.card ↥P := by
    rw [hPcard]
    exact Nat.mul_le_mul_left _ hker |>.trans' (by omega)
  omega

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

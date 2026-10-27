module

public import CFSG.GH74.Generic.S1.DecompCore
public import CFSG.RankThree.PartOne.S11c.Sec68
public import CFSG.GH74.KGroups.L3EpsBlockLin
public import CFSG.GH74.Generic.S1.TPairFacts

public section

open Subgroup CFSG CFSG.GH74 CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
  CFSG.GH74.Filter.ClassicalOdd CFSG.LocalCores
open scoped MatrixGroups

namespace CFSG.GH74.Generic.S1

theorem odd_center_of_model_five (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) {p f : ℕ}
    (hmod : StatedClassicalModel (K ⧸ center K) .PSL 5 p f ∨
      StatedClassicalModel (K ⧸ center K) .PSU 5 p f) : Odd (Nat.card (center K)) := by
  rcases hmod with hm | hm
  · have h := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA hK hm
    have hexc : exceptionalOrders .PSL 5 p f = (1, 1) := by
      unfold exceptionalOrders
      split <;> simp_all
    have hgen : genericOrders .PSL 5 p f = (Nat.gcd 5 (p ^ f - 1), 1) := rfl
    rw [hexc, hgen] at h
    simp only [mul_one] at h
    exact Odd.of_dvd_nat (by decide : Odd 5) (h.trans (Nat.gcd_dvd_left 5 _))
  · have h := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA hK hm
    have hexc : exceptionalOrders .PSU 5 p f = (1, 1) := by
      unfold exceptionalOrders
      split <;> simp_all
    have hgen : genericOrders .PSU 5 p f = (Nat.gcd 5 (p ^ f + 1), 1) := rfl
    rw [hexc, hgen] at h
    simp only [mul_one] at h
    exact Odd.of_dvd_nat (by decide : Odd 5) (h.trans (Nat.gcd_dvd_left 5 _))

@[expose] def KL5Table : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) → GHList S →
    ∀ A B : Subgroup S, (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → IsQuasisimple ↥A → IsQuasisimple ↥B →
      ∀ (ε : ℤ) (p f : ℕ), p.Prime → p ≠ 2 → 5 ≤ p ^ f →
        ((ε = 1 ∧ StatedClassicalModel (↥A ⧸ center ↥A) .PSL 3 p f) ∨
          (ε = -1 ∧ StatedClassicalModel (↥A ⧸ center ↥A) .PSU 3 p f)) →
        StatedClassicalModel (↥B ⧸ center ↥B) .PSL 2 p f →
        ∃ p' f' : ℕ, p'.Prime ∧ 1 ≤ f' ∧ p' ≠ 2 ∧
          ((p' ^ f' % 4 = 3 ∧ StatedClassicalModel S .PSL 5 p' f') ∨
            (p' ^ f' % 4 = 1 ∧ StatedClassicalModel S .PSU 5 p' f'))

section Abstract

variable {H : Type} [Group H] [Finite H]

theorem jcentral_of_KL5 (hKL5 : KL5Table)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) (hH : Gen4 H)
    {M D B A : Subgroup H} (hM : IsQuasisimple ↥M) (hGHS : GHList (↥M ⧸ center ↥M))
    (hDM : ∀ d ∈ D, ∀ m ∈ M, d * m = m * d) (hZD : ∀ z ∈ center ↥M, (z : H) ∈ D)
    (hdec : ∀ j ∈ B, ∃ m ∈ M, ∃ d ∈ D, j = m * d) (hBq : IsQuasisimple ↥B) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (hBsl2 : CFSG.GH74.GLS.HasSL2Model ↥B (fun q => q = p ^ f)) {cb : H} (hcbD : cb ∈ D)
    (hcb1 : cb ≠ 1) (hBcen : ∀ z ∈ B, (∀ w ∈ B, z * w = w * z) → z = 1 ∨ z = cb)
    (ψB : Q8 →* H) (hψB : ∀ g, ψB g ∈ B) (hψBi : Function.Injective ψB)
    (hψBc : ψB (QuaternionGroup.a 2) = cb) {ε : ℤ}
    (hAmodel : (ε = 1 ∧ StatedClassicalModel (↥A ⧸ center ↥A) .PSL 3 p f) ∨
      (ε = -1 ∧ StatedClassicalModel (↥A ⧸ center ↥A) .PSU 3 p f))
    (hAq : IsQuasisimple ↥A) (hAM : A ≤ M)
    (hAodd : ∀ z ∈ A, (∀ w ∈ A, z * w = w * z) → Odd (orderOf z))
    (ψA : Q8 →* H) (hψAi : Function.Injective ψA) (hψA : ∀ g, ψA g ∈ A)
    (hAB : ∀ a ∈ A, ∀ j ∈ B, a * j = j * a) :
    ∀ j ∈ B, ∀ m ∈ M, j * m = m * j := by
  by_cases hcent : ∀ j ∈ B, ∀ m ∈ M, j * m = m * j
  · exact hcent
  exfalso
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at h5
    · exact h
  obtain ⟨F₂, _, _, hF₂, ⟨eB⟩⟩ := hBsl2
  let e' : SL(2, F₂) ≃* ↥B := (specialLinearGroupEquivStatedSL 2 F₂).trans eB.symm
  have hF4 : 4 ≤ Nat.card F₂ := by rw [hF₂]; omega
  have hSL2q : IsQuasisimple SL(2, F₂) := CFSG.GH74.KGroups.L3Eps.isQuasisimple_sl2c hF4
  let lam := lamHom hDM hdec
  let ψ₂ : SL(2, F₂) →* ↥M ⧸ center ↥M := lam.comp e'.toMonoidHom
  have hker₂ : ψ₂.ker ≤ center SL(2, F₂) := by
    rcases quasisimple_normal_subgroups hSL2q (inferInstance : ψ₂.ker.Normal) with htop | hc
    · exfalso
      apply hcent
      intro j hj m hm
      have h1 : ψ₂ (e'.symm ⟨j, hj⟩) = 1 := by
        have : e'.symm ⟨j, hj⟩ ∈ ψ₂.ker := by rw [htop]; trivial
        exact this
      have h2 : lam ⟨j, hj⟩ = 1 := by simpa [ψ₂] using h1
      have hjD := mem_of_lamHom_eq_one hDM hZD hdec ⟨j, hj⟩ h2
      exact hDM j hjD m hm
    · exact hc
  have hsurj₂ : Function.Surjective ψ₂.rangeRestrict := ψ₂.rangeRestrict_surjective
  have hker₂' : ψ₂.rangeRestrict.ker ≤ center SL(2, F₂) := by
    rw [MonoidHom.ker_rangeRestrict]; exact hker₂
  have hZ₂ := CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hSL2q hsurj₂ hker₂'
  let e₂ := CFSG.LieType.CurtisTits.centerQuotientEquivOfSurjective ψ₂.rangeRestrict hsurj₂ hker₂'
    hZ₂
  have hBhq : IsQuasisimple ↥ψ₂.range := isQuasisimple_range_of_ker hSL2q ψ₂ hker₂
  have hmodB : StatedClassicalModel (↥ψ₂.range ⧸ center ↥ψ₂.range) .PSL 2 p f := by
    have hadm : StatedLieAdmissible .PSL (1 + 1) p f :=
      ⟨hp, hf, by norm_num, fun h => by have := (Prod.mk.inj h).2; omega,
        fun h => by have := (Prod.mk.inj h).2; omega⟩
    have := CFSG.LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient 1 F₂ hadm hF₂
    exact CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e₂ this
  let gA : ↥A →* ↥M ⧸ center ↥M := (QuotientGroup.mk' (center ↥M)).comp (Subgroup.inclusion hAM)
  have hkerA : gA.ker ≤ center ↥A := by
    intro a ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ha
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subgroup.inclusion_injective hAM
    have := Subgroup.mem_center_iff.1 ha (Subgroup.inclusion hAM b)
    simpa using this
  have hAhq : IsQuasisimple ↥gA.range := isQuasisimple_range_of_ker hAq gA hkerA
  have hsurjA : Function.Surjective gA.rangeRestrict := gA.rangeRestrict_surjective
  have hkerA' : gA.rangeRestrict.ker ≤ center ↥A := by
    rw [MonoidHom.ker_rangeRestrict]; exact hkerA
  have hZA := CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hAq hsurjA hkerA'
  let eA := CFSG.LieType.CurtisTits.centerQuotientEquivOfSurjective gA.rangeRestrict hsurjA hkerA'
    hZA
  have hmodA : (ε = 1 ∧ StatedClassicalModel (↥gA.range ⧸ center ↥gA.range) .PSL 3 p f) ∨
      (ε = -1 ∧ StatedClassicalModel (↥gA.range ⧸ center ↥gA.range) .PSU 3 p f) := by
    rcases hAmodel with ⟨h1, h⟩ | ⟨h1, h⟩
    · exact Or.inl ⟨h1, CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv eA h⟩
    · exact Or.inr ⟨h1, CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv eA h⟩
  have hcomm : ∀ a ∈ gA.range, ∀ b ∈ ψ₂.range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨s, rfl⟩
    obtain ⟨m, hm, d, hd, hj⟩ := hdec ((e' s : ↥B) : H) (e' s).2
    have hlam : ψ₂ s = QuotientGroup.mk ⟨m, hm⟩ := lamHom_eq hDM hdec (e' s) hm hd hj
    have h1 : (a : H) * ((e' s : ↥B) : H) = ((e' s : ↥B) : H) * (a : H) :=
      hAB (a : H) a.2 _ (e' s).2
    rw [hj] at h1
    have hda : d * (a : H) = (a : H) * d := hDM d hd a (hAM a.2)
    have hmc : (a : H) * m = m * (a : H) := by
      apply mul_right_cancel (b := d)
      calc (a : H) * m * d = (a : H) * (m * d) := by group
        _ = m * d * (a : H) := h1
        _ = m * (d * (a : H)) := by group
        _ = m * ((a : H) * d) := by rw [hda]
        _ = m * (a : H) * d := by group
    show gA a * ψ₂ s = ψ₂ s * gA a
    rw [hlam]
    show QuotientGroup.mk (Subgroup.inclusion hAM a) * QuotientGroup.mk (⟨m, hm⟩ : ↥M) =
      QuotientGroup.mk (⟨m, hm⟩ : ↥M) * QuotientGroup.mk (Subgroup.inclusion hAM a)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hmc
  have hsimple : IsSimpleGroup (↥M ⧸ center ↥M) := hM.2.1
  have hnonab : ∃ x y : ↥M ⧸ center ↥M, x * y ≠ y * x := hM.2.2
  obtain ⟨p', f', -, -, -, hout⟩ := hKL5 (↥M ⧸ center ↥M) hsimple hnonab hGHS gA.range ψ₂.range
    hcomm hAhq hBhq ε p f hp hp2 h5 hmodA hmodB
  have hZodd : Odd (Nat.card (center ↥M)) := by
    rcases hout with ⟨-, hm⟩ | ⟨-, hm⟩
    · exact odd_center_of_model_five hGA hM (Or.inl hm)
    · exact odd_center_of_model_five hGA hM (Or.inr hm)
  exact hcent (jcentral_of_odd_center hH hZodd hDM hdec hBq hcbD hcb1 hBcen ψB hψB hψBi hψBc hAM
    hAodd ψA hψAi hψA hAB)

end Abstract


end CFSG.GH74.Generic.S1

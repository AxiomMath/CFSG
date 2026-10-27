module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Row54b
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Row50
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Dict

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.CatB CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 fieldFactor4 fieldSU4 mem_range_conj_of_fieldFactor4_eq_one)

section Row


theorem fieldU3RestrictAt_holds (G : Type) [Group G] [Finite G] : FieldU3RestrictAt G := by
  intro X M g y hM hcat hFO hy3 hy1 hyc hgy
  have hZ := center_pquot_eq_bot_of_u48 hM hcat
  let e₀ := pqModelP hZ hcat
  have hφ₀s := piOf_surjective M e₀
  have hφ₀k := not_three_dvd_card_ker_piOf e₀
  have hgM : g ∈ Subgroup.normalizer (M : Set G) := hFO.1
  let γ : MulAut SU4 := e₀.symm.trans ((barAut M g hgM).trans e₀)
  have hγ : ∀ q : PQuot 3 M, γ (e₀ q) = e₀ (barAut M g hgM q) := fun q => by simp [γ]
  let τ : PSimple 3 M ≃* SU4 :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e₀
  have hτmk : ∀ x : PQuot 3 M, τ (QuotientGroup.mk x) = e₀ x := fun x => by
    show e₀ (QuotientGroup.quotientBot (QuotientGroup.quotientMulEquivOfEq hZ (QuotientGroup.mk x))) = e₀ x
    congr 1
  have hγτ : ∀ q : PQuot 3 M, γ (τ (QuotientGroup.mk q)) =
      τ (QuotientGroup.mk (barAut M g hgM q)) := fun q => by rw [hτmk, hτmk, hγ]
  obtain ⟨hγ3, hγout⟩ := dict_outer hcat hFO τ γ hγτ
  have hγ1 : fieldFactor4 γ ≠ 1 := fun h1 => hγout (mem_range_conj_of_fieldFactor4_eq_one h1)
  obtain ⟨h, hh⟩ := exists_conj_fieldSU4 hγ3 hγ1
  have hyM : y ∈ M := hyc.1
  have hgi : g⁻¹ * y = y * g⁻¹ := by
    have e : g⁻¹ * y = g⁻¹ * (y * g) * g⁻¹ := by group
    rw [e, ← hgy]
    group
  have hc : conjL M g hgM ⟨y, hyM⟩ = ⟨y, hyM⟩ := Subtype.ext (by
    show g⁻¹ * y * g = y
    rw [hgi]
    group)
  let Y : SU4 := piOf M e₀ ⟨y, hyM⟩
  have hY : γ Y = Y := by
    show γ (e₀ (QuotientGroup.mk ⟨y, hyM⟩)) = e₀ (QuotientGroup.mk ⟨y, hyM⟩)
    rw [hγ, barAut_mk, hc]
  obtain ⟨g₀, t, ht, hg₀⟩ := exists_conj_of_central (piOf M e₀) hφ₀s hφ₀k hy3 hy1 hyc
  obtain ⟨k, hk1, hk2⟩ := nf_model hγ3 hγ1 hh hY ht hg₀
  let φ₁ : ↥M →* SU4 := (MulAut.conj k).toMonoidHom.comp (piOf M e₀)
  have hφ₁s : Function.Surjective φ₁ := (MulAut.conj k).surjective.comp hφ₀s
  have hφ₁k : ¬ 3 ∣ Nat.card φ₁.ker := by
    have hker : φ₁.ker = (piOf M e₀).ker :=
      MonoidHom.ker_comp_of_injective _ _ (MulAut.conj k).injective
    rw [hker]
    exact hφ₀k
  have hφ₁y : φ₁ ⟨y, hyM⟩ = yStd t := hk2
  have hφ₁g : ∀ x : ↥M, φ₁ (conjL M g hgM x) = fieldSU4 (fieldFactor4 γ) (φ₁ x) := by
    intro x
    have hx : piOf M e₀ (conjL M g hgM x) = γ (piOf M e₀ x) := by
      show e₀ (QuotientGroup.mk (conjL M g hgM x)) = γ (e₀ (QuotientGroup.mk x))
      rw [hγ, barAut_mk]
    have hk := hk1 (k * piOf M e₀ x * k⁻¹)
    have e : k⁻¹ * (k * piOf M e₀ x * k⁻¹) * k = piOf M e₀ x := by group
    rw [e] at hk
    show k * piOf M e₀ (conjL M g hgM x) * k⁻¹ = fieldSU4 (fieldFactor4 γ) (k * piOf M e₀ x * k⁻¹)
    rw [hx]
    exact hk
  have hpow : fieldFactor4 γ ^ 3 = 1 := by rw [← map_pow, hγ3, map_one]
  exact fieldOn_layer_model hgM hgy φ₁ hφ₁s hφ₁k ht hyM hy3 hφ₁y hpow hγ1 hφ₁g

end Row

end CFSG.LocalAnalysis.GLTheoremA

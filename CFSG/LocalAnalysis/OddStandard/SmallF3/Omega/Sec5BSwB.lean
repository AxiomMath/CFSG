module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwBImg
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwBLift
public import CFSG.Quasithin.H13.GoldschmidtU43ModOne

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Multipliers.U43 CFSG.Quasithin.H13.U43 Subgroup

theorem sw_core_invol_aux {Λ : Type} [Group Λ] [Finite Λ] {τ : Λ →* X₀} (hτ : SwCentralTwo τ)
    (hF : SwFinite) {A₁ A₂ : Subgroup Λ} {z : Λ} (S : SwSetup A₁ A₂ z) (hz2 : orderOf z = 2)
    (hz : τ z = xElt) : ∃ c ∈ centralizer ({z} : Set Λ), CFSG.conjugate A₁ c = A₂ := by
  obtain ⟨c₀, _hc₀, hconj⟩ := sw_img_conj hτ hF S hz
  obtain ⟨c, hc⟩ := hτ.surj c₀
  have hconj' : CFSG.conjugate (A₁.map τ) (τ c) = A₂.map τ := by
    rw [hc]
    exact hconj
  exact ⟨c, sw_cent_of_conj S hz2 (sw_conj_of_img hτ S hconj'),
    sw_conj_of_img hτ S hconj'⟩

theorem sw_core_invol {Λ : Type} [Group Λ] [Finite Λ] {τ : Λ →* X₀} (hτ : SwCentralTwo τ)
    (hone : X0OneClass) (hx : orderOf xElt = 2) (hF : SwFinite) {A₁ A₂ : Subgroup Λ} {z : Λ}
    (S : SwSetup A₁ A₂ z) (hz2 : orderOf z = 2) (hz1 : τ z ≠ 1) :
    ∃ c ∈ centralizer ({z} : Set Λ), CFSG.conjugate A₁ c = A₂ := by
  have hdvd : orderOf (τ z) ∣ 2 := by
    rw [← hz2]
    exact orderOf_map_dvd τ z
  have horder : orderOf (τ z) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  obtain ⟨g, hg⟩ := isConj_iff.mp (hone (τ z) xElt horder hx)
  let τ' : Λ →* X₀ := (MulAut.conj g).toMonoidHom.comp τ
  have hτ' : SwCentralTwo τ' := hτ.comp_conj g
  have hτ'z : τ' z = xElt := by
    show (MulAut.conj g) (τ z) = xElt
    rw [MulAut.conj_apply, hg]
  exact sw_core_invol_aux hτ' hF S hz2 hτ'z

end CFSG.OddStandard.SmallF3.Omega

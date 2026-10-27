module

public import CFSG.ClassicalInvolution.Uniform.U3M11b
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Blueprint CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform

abbrev M11T : Type := ↥NativeSporadic.M11

theorem m11_center_eq_bot : Subgroup.center M11T = ⊥ := by
  have hs := isSimpleGroup_m11_kernel
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center M11T) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative M11T := Subgroup.center_eq_top_iff.1 h
    have hp := Group.is_simple_iff_prime_card.1 hs
    rw [card_m11_kernel] at hp
    norm_num at hp

private theorem exists_two_group_card_eight {J : Subgroup M11T} (hJ : Nat.card J = 24) :
    ∃ R : Subgroup M11T, R ≤ J ∧ IsPGroup 2 R ∧ Nat.card R = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥J) := inferInstance
  have h8 : Nat.card (P : Subgroup ↥J) = 8 := by
    rw [Sylow.card_eq_multiplicity, hJ]
    have h : (Nat.factorization 24) 2 = 3 := by
      rw [Nat.factorization_def _ Nat.prime_two]
      have h1 : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
      rw [h1, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
      have h0 : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
      omega
    rw [h]
    norm_num
  refine ⟨(P : Subgroup ↥J).map J.subtype, ?_, P.isPGroup'.map _, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective J.subtype_injective, h8]

theorem m11_involution_centralizes_classical {J : Subgroup M11T} {w : M11T}
    (hJ : IsClassicalMember3 J w) {e : M11T} (he : orderOf e = 2) (hc : ∀ j ∈ J, e * j = j * e) :
    e = w := by
  have hJ24 : Nat.card J = 24 := hJ.card_eq_of_mulEquiv_m11 (MulEquiv.refl _)
  have hJU := (IsClassicalMemberU.ofQ3 hJ).isUniqueInvolution_sl2
  obtain ⟨R, hRJ, hR2, hR8⟩ := exists_two_group_card_eight hJ24
  by_cases heR : e ∈ R
  · have hesq : e * e = 1 := by
      have := pow_orderOf_eq_one e
      rwa [he, pow_two] at this
    rcases hJU.unique e (hRJ heR) hesq with h | h
    · exact absurd (h ▸ he) (by simp)
    · exact h
  · exact (false_of_central_involution_outside m11_sylow_card m11_sylow_center_le_two hR2 hR8 he
      heR fun r hr => hc r (hRJ hr)).elim

theorem m11_exists_commuting_involution {w : M11T} (hw : orderOf w = 2) :
    ∃ u : M11T, orderOf u = 2 ∧ u ≠ w ∧ u * w = w * u := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_m11SdZ_of_orderOf_eq_two hw)
  set y : M11T := ⟨m11SdY, m11SdY_mem⟩ with hy
  have hy2 : y * y = 1 := Subtype.ext (by simpa [pow_two] using m11SdY_sq)
  have hy1 : y ≠ 1 := fun h => by
    have : m11SdY ≠ 1 := by decide +kernel
    exact this (congrArg Subtype.val h)
  have hyz : y * m11SdZ = m11SdZ * y := Subtype.ext (by
    have : m11SdY * m11SdX ^ 4 = m11SdX ^ 4 * m11SdY := by decide +kernel
    exact this)
  have hyne : y ≠ m11SdZ := fun h => by
    have : m11SdY ≠ m11SdX ^ 4 := by decide +kernel
    exact this (congrArg Subtype.val h)
  have hyord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  refine ⟨c * y * c⁻¹, ?_, ?_, ?_⟩
  · have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective y
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rw [this, hyord]
  · intro h
    apply hyne
    rw [← hc] at h
    exact mul_left_cancel (mul_right_cancel h)
  · rw [← hc]
    calc c * y * c⁻¹ * (c * m11SdZ * c⁻¹) = c * (y * m11SdZ) * c⁻¹ := by group
      _ = c * (m11SdZ * y) * c⁻¹ := by rw [hyz]
      _ = c * m11SdZ * c⁻¹ * (c * y * c⁻¹) := by group

theorem m11_classical_of_involution {J₀ : Subgroup M11T} {w₀ : M11T} (h₀ : IsClassicalMember3 J₀ w₀)
    {u : M11T} (hu : orderOf u = 2) : ∃ J : Subgroup M11T, IsClassicalMember3 J u := by
  obtain ⟨c, hc⟩ := isConj_iff.mp ((isConj_m11SdZ_of_orderOf_eq_two h₀.orderOf_eq_two).symm.trans
    (isConj_m11SdZ_of_orderOf_eq_two hu))
  refine ⟨conjSub c J₀, ?_⟩
  rw [← hc]
  exact h₀.conj c

theorem m11_fund_iSup_eq_top {J₀ : Subgroup M11T} {w₀ : M11T} (h₀ : IsClassicalMember3 J₀ w₀) :
    (⨆ R ∈ M11ClassicalClass, R) = ⊤ := by
  have hs := isSimpleGroup_m11_kernel
  set H : Subgroup M11T := ⨆ R ∈ M11ClassicalClass, R with hH
  have hcl : ∀ R ∈ M11ClassicalClass, ∀ g : M11T, conjSub g R ∈ M11ClassicalClass := by
    rintro R ⟨z, hz⟩ g
    exact ⟨g * z * g⁻¹, hz.conj g⟩
  have hnorm : H.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
      rw [hH, Subgroup.map_iSup]
      refine iSup_le fun R => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hR => ?_
      exact le_iSup₂ (f := fun (R : Subgroup M11T) (_ : R ∈ M11ClassicalClass) => R) (conjSub g R)
        (hcl R hR g)
    exact hle ⟨n, hn, rfl⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
  · exfalso
    have hw : w₀ ∈ H :=
      (le_iSup₂ (f := fun (R : Subgroup M11T) (_ : R ∈ M11ClassicalClass) => R) J₀ ⟨w₀, h₀⟩ :
        J₀ ≤ H) h₀.mem
    rw [h, Subgroup.mem_bot] at hw
    exact h₀.ne_one hw
  · exact h

section Dichotomy

variable {X : Type} [Group X]

theorem m11_aut_dichotomy (hOut : ∀ φ : MulAut M11T, ∃ g, φ = MulAut.conj g) (ψ : M11T →* X)
    (hker : ψ.ker ≤ Subgroup.center M11T) (σ : X ≃* X) (hσσ : ∀ a, σ (σ a) = a)
    (hstab : ∀ x, σ (ψ x) ∈ ψ.range) {R₀ : Subgroup M11T} {r₀ : M11T}
    (hR₀ : IsClassicalMember3 R₀ r₀) (hfix : ∀ r ∈ R₀, σ (ψ r) = ψ r) :
    ∃ k : M11T, (k = 1 ∨ k = r₀) ∧ ∀ x, σ (ψ x) = ψ (k * x * k⁻¹) := by
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [m11_center_eq_bot] at hker
    exact le_bot_iff.mp hker
  choose f hf using hstab
  have hmul : ∀ x y, f (x * y) = f x * f y := fun x y => by
    apply hinj
    rw [map_mul, hf, hf, hf, map_mul, map_mul]
  have hone : f 1 = 1 := by
    apply hinj
    rw [hf, map_one, map_one]
  let φ₀ : M11T →* M11T := { toFun := f, map_one' := hone, map_mul' := hmul }
  have hφinj : Function.Injective φ₀ := fun x y h => by
    apply hinj
    have h1 := hf x
    have h2 := hf y
    have h3 : f x = f y := h
    rw [h3] at h1
    exact σ.injective (h1.symm.trans h2)
  have hφbij : Function.Bijective φ₀ := Finite.injective_iff_bijective.mp hφinj
  obtain ⟨k, hk⟩ := hOut (MulEquiv.ofBijective φ₀ hφbij)
  have hfk : ∀ x, f x = k * x * k⁻¹ := fun x => by
    have := congrArg (fun α : MulAut M11T => α x) hk
    simp only [MulAut.conj_apply] at this
    exact this
  have hconj : ∀ x, σ (ψ x) = ψ (k * x * k⁻¹) := fun x => by rw [← hfk, hf]
  have hkR : ∀ r ∈ R₀, k * r = r * k := fun r hr => by
    have h := hconj r
    rw [hfix r hr] at h
    have h' := hinj h
    exact (eq_mul_inv_iff_mul_eq.mp h').symm
  have hkk : k * k = 1 := by
    have hc : k * k ∈ Subgroup.center M11T := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : ψ (k * (k * g * k⁻¹) * k⁻¹) = ψ g := by
        rw [← hconj, ← hconj, hσσ]
      have h2 : k * (k * g * k⁻¹) * k⁻¹ = k * k * g * (k * k)⁻¹ := by group
      rw [h2] at h1
      have h3 := hinj h1
      exact (mul_inv_eq_iff_eq_mul.mp h3).symm
    rw [m11_center_eq_bot, Subgroup.mem_bot] at hc
    exact hc
  refine ⟨k, ?_, hconj⟩
  by_cases hk1 : k = 1
  · exact Or.inl hk1
  · right
    have hord : orderOf k = 2 := orderOf_eq_prime (by rw [pow_two]; exact hkk) hk1
    exact m11_involution_centralizes_classical hR₀ hord fun j hj => hkR j hj

end Dichotomy

end CFSG.ClassicalInvolution.Q3.Q3W

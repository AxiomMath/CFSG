module

public import CFSG.SignalizerFunctorTheorem.Inheritance.Sections
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Defs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem not_inner_of_not_isSectionOf_A8 {H : Type} [Group H] (a b c : H) (ha2 : a * a = 1)
    (hc2 : c * c = 1) (hac : (a * c) ^ 2 = b) (K : Subgroup H)
    (φ : alternatingGroup (Fin 8) ≃* ↥K) (hKa : ∀ k ∈ K, a * k = k * a)
    (hKb : ∀ k ∈ K, b * k = k * b)
    (hA8 : ∀ g : H, g ^ 2 = b → ¬ CFSG.SignalizerFunctorTheorem.IsSectionOf
      (alternatingGroup (Fin 8)) ↥(Subgroup.centralizer ({g} : Set H))) :
    ¬ ∃ k ∈ K, ∀ x ∈ K, c * x * c⁻¹ = k * x * k⁻¹ := by
  rintro ⟨k, hkK, hk⟩
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hc_inv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hac' : a * c * a * c = b := by simpa only [pow_two, mul_assoc] using hac
  have hca' : c * a * c = a * b := by
    have h := congrArg (fun y => a * y) hac'
    have hL : a * (a * c * a * c) = c * a * c := by
      calc a * (a * c * a * c) = (a * a) * c * a * c := by group
        _ = c * a * c := by rw [ha2]; group
    rw [hL] at h
    exact h
  have hca : c * a = a * b * c := by
    have h := congrArg (fun y => y * c) hca'
    rw [show c * a * c * c = c * a by rw [mul_assoc, hc2, mul_one]] at h
    exact h
  have hckc : c * k * c⁻¹ = k := by
    rw [hk k hkK]; group
  have hck : c * k = k * c := by
    calc c * k = c * k * c⁻¹ * c := by group
      _ = k * c := by rw [hckc]
  have hx' : ∀ x ∈ K, c * x * c⁻¹ ∈ K := by
    intro x hx
    rw [hk x hx]
    exact K.mul_mem (K.mul_mem hkK hx) (K.inv_mem hkK)
  have hkey : ∀ x ∈ K, x = k * (k * x * k⁻¹) * k⁻¹ := by
    intro x hx
    have h2 := hk (c * x * c⁻¹) (hx' x hx)
    have hL : c * (c * x * c⁻¹) * c⁻¹ = x := by
      rw [hc_inv]
      calc c * (c * x * c) * c = (c * c) * x * (c * c) := by group
        _ = x := by rw [hc2]; group
    rw [hL] at h2
    rw [hk x hx] at h2
    exact h2
  have hyk : ∀ y : ↥K, (y : H) * (k * k) = (k * k) * (y : H) := by
    intro y
    conv_lhs => rw [hkey (y : H) y.2]
    group
  have hk2mem : (⟨k * k, K.mul_mem hkK hkK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hyk y)
  have hcenter : Subgroup.center ↥K = ⊥ := by
    apply le_antisymm
    · intro z hz
      rw [Subgroup.mem_bot]
      have hzA : φ.symm z ∈ Subgroup.center (alternatingGroup (Fin 8)) := by
        rw [Subgroup.mem_center_iff]
        intro w
        apply φ.injective
        simp only [map_mul, MulEquiv.apply_symm_apply]
        exact Subgroup.mem_center_iff.mp hz (φ w)
      have hzA1 : φ.symm z = 1 := by
        have h := hzA
        rw [alternatingGroup.center_eq_bot (α := Fin 8) (by simp)] at h
        simpa using h
      exact φ.symm.injective (by rw [hzA1, map_one])
    · exact bot_le
  have hk2 : k * k = 1 := by
    have h := hk2mem
    rw [hcenter] at h
    rw [Subgroup.mem_bot] at h
    exact congrArg Subtype.val h
  have hk_inv : k⁻¹ = k := inv_eq_of_mul_eq_one_right hk2
  have hak : a * k = k * a := hKa k hkK
  have hbk : b * k = k * b := hKb k hkK
  let t : H := k⁻¹ * c
  let g : H := a * t
  have ht_eq : t = k⁻¹ * c := rfl
  have hg_eq : g = a * t := rfl
  have htK : ∀ x ∈ K, t * x * t⁻¹ = x := by
    intro x hx
    have h1 : t * x * t⁻¹ = k⁻¹ * (c * x * c⁻¹) * k := by
      rw [ht_eq]; group
    rw [h1, hk x hx]
    group
  have hgK : ∀ x ∈ K, g * x = x * g := by
    intro x hx
    have hxt : t * x = x * t := by
      calc t * x = t * x * t⁻¹ * t := by group
        _ = x * t := by rw [htK x hx]
    calc g * x = a * t * x := by rw [hg_eq]
      _ = a * (t * x) := by group
      _ = a * (x * t) := by rw [hxt]
      _ = (a * x) * t := by group
      _ = (x * a) * t := by rw [hKa x hx]
      _ = x * (a * t) := by group
      _ = x * g := by rw [hg_eq]
  have hg2 : g ^ 2 = b := by
    rw [pow_two]
    rw [hg_eq, ht_eq, hk_inv]
    calc (a * (k * c)) * (a * (k * c)) = a * k * (c * a) * k * c := by group
      _ = a * k * (a * b * c) * k * c := by rw [hca]
      _ = k * a * (a * b * c) * k * c := by rw [hak]
      _ = k * (a * a) * b * c * k * c := by group
      _ = k * b * c * k * c := by rw [ha2]; group
      _ = k * b * (c * k) * c := by group
      _ = k * b * (k * c) * c := by rw [hck]
      _ = k * b * k * (c * c) := by group
      _ = k * b * k := by rw [hc2]; group
      _ = k * (b * k) := by group
      _ = k * (k * b) := by rw [hbk]
      _ = k * k * b := by group
      _ = b := by rw [hk2]; group
  have hKle : K ≤ Subgroup.centralizer ({g} : Set H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hgK x hx).symm
  have hsect : CFSG.SignalizerFunctorTheorem.IsSectionOf (alternatingGroup (Fin 8))
      ↥(Subgroup.centralizer ({g} : Set H)) :=
    (CFSG.SignalizerFunctorTheorem.IsSectionOf.of_mulEquiv
        ((Subgroup.subgroupOfEquivOfLe hKle).trans φ.symm)).trans
      (CFSG.SignalizerFunctorTheorem.IsSectionOf.of_subgroup _)
  exact hA8 g hg2 hsect

end CFSG.EvenSporadicStandard.HNRecog.Section3

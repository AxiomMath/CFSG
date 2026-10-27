module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.OddInner
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Swap

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed

@[expose] def conjAut {K : Type*} [Group K] (S : Subgroup K) {y : K}
    (hy : y ∈ normalizer (S : Set K)) : MulAut ↥S where
  toFun s := ⟨y * s * y⁻¹, (Subgroup.mem_normalizer_iff.1 hy _).1 s.2⟩
  invFun s := ⟨y⁻¹ * s * y, by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hy) _).1 s.2
    simpa using this⟩
  left_inv s := by apply Subtype.ext; group
  right_inv s := by apply Subtype.ext; group
  map_mul' s t := by
    apply Subtype.ext
    show y * ((s : K) * t) * y⁻¹ = (y * s * y⁻¹) * (y * t * y⁻¹)
    group

@[simp] theorem conjAut_apply {K : Type*} [Group K] {S : Subgroup K} {y : K}
    (hy : y ∈ normalizer (S : Set K)) (s : ↥S) :
    (((conjAut S hy) s : ↥S) : K) = y * (s : K) * y⁻¹ := rfl

theorem conjAut_pow_apply {K : Type*} [Group K] {S : Subgroup K} {y : K}
    (hy : y ∈ normalizer (S : Set K)) (n : ℕ) (s : ↥S) :
    ((((conjAut S hy) ^ n) s : ↥S) : K) = y ^ n * (s : K) * (y ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, conjAut_apply, ih, pow_succ']
      group

theorem odd_mem_of_fixedData {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    (hS : FixedData G S) (hodd : OddInner ↥S) : ∀ x : G, Odd (orderOf x) → x ∈ S := by
  intro x hx
  haveI := hS.normal
  have hσodd : Odd (orderOf (MulAut.conjNormal x : MulAut ↥S)) :=
    hx.of_dvd_nat (orderOf_map_dvd (MulAut.conjNormal : G →* MulAut ↥S) x)
  obtain ⟨s, hs_conj⟩ := hodd (MulAut.conjNormal x) hσodd
  have hconj : ∀ y : ↥S, (s : G) * (y : G) * (s : G)⁻¹ = x * (y : G) * x⁻¹ := by
    intro y
    have h := congrArg (fun φ : MulAut ↥S => (((φ y : ↥S)) : G)) hs_conj
    simpa [MulAut.conj_apply] using h
  have hc : (s : G)⁻¹ * x ∈ centralizer (S : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h := hconj ⟨y, hy⟩
    calc y * ((s : G)⁻¹ * x) = ((s : G)⁻¹ * ((s : G) * y * (s : G)⁻¹)) * x := by group
      _ = ((s : G)⁻¹ * (x * y * x⁻¹)) * x := by rw [h]
      _ = ((s : G)⁻¹ * x) * y := by group
  rw [hS.cent, mem_bot] at hc
  have hxeq : x = (s : G) := (inv_mul_eq_one.mp hc).symm
  rw [hxeq]
  exact s.2

theorem odd_mem_layer_of_swapData {K : Type*} [Group K] [Finite K] {z : K} {B S₁ S₂ : Subgroup K}
    (h : Setting K z B) (hs : SwapData K z B S₁ S₂) (h₁ : OddInner ↥S₁) (h₂ : OddInner ↥S₂) :
    ∀ x : K, Odd (orderOf x) → x ∈ layer K := by
  intro x hx
  have hxN₁ : x ∈ normalizer (S₁ : Set K) := by
    by_contra hxnot
    have hxS₂ : S₁.map (MulAut.conj x).toMonoidHom = S₂ := by
      rcases hs.comp_cases _ (isComponent_conj hs.comp x) with h1 | h1
      · exact absurd (mem_normalizer_iff_map.2 h1) hxnot
      · exact h1
    have hx2N : x * x ∈ normalizer (S₁ : Set K) := by
      rcases hs.comp_cases _ (isComponent_conj hs.comp₂ x) with h2 | h2
      · rw [mem_normalizer_iff_map]
        have hcomp : (MulAut.conj (x * x)).toMonoidHom =
            (MulAut.conj x).toMonoidHom.comp (MulAut.conj x).toMonoidHom := by
          ext y
          show x * x * y * (x * x)⁻¹ = x * (x * y * x⁻¹) * x⁻¹
          group
        rw [hcomp, ← Subgroup.map_map]
        rw [hxS₂, h2]
      · exfalso
        apply hs.ne
        apply Subgroup.map_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective
        rw [hxS₂, h2]
    obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime (x := x) (n := 2) hx.coprime_two_left
    have hxN : x ∈ normalizer (S₁ : Set K) := by
      rw [← hk]
      simpa [pow_two] using pow_mem hx2N k
    have hmap : S₁.map (MulAut.conj x).toMonoidHom = S₁ := mem_normalizer_iff_map.1 hxN
    rw [hxS₂] at hmap
    exact hs.ne hmap.symm
  have hxN₂ : x ∈ normalizer (S₂ : Set K) := hs.normalizer_le x hxN₁
  have hodd₁ : Odd (orderOf (conjAut S₁ hxN₁)) := by
    apply hx.of_dvd_nat
    rw [orderOf_dvd_iff_pow_eq_one]
    apply MulEquiv.ext
    intro s
    apply Subtype.ext
    rw [conjAut_pow_apply, pow_orderOf_eq_one]
    simp
  have hodd₂ : Odd (orderOf (conjAut S₂ hxN₂)) := by
    apply hx.of_dvd_nat
    rw [orderOf_dvd_iff_pow_eq_one]
    apply MulEquiv.ext
    intro t
    apply Subtype.ext
    rw [conjAut_pow_apply, pow_orderOf_eq_one]
    simp
  obtain ⟨a₁, ha₁⟩ := h₁ (conjAut S₁ hxN₁) hodd₁
  obtain ⟨a₂, ha₂⟩ := h₂ (conjAut S₂ hxN₂) hodd₂
  have ha₁act : ∀ s ∈ S₁, x * s * x⁻¹ = (a₁ : K) * s * (a₁ : K)⁻¹ := by
    intro s hsS
    have h := congrArg (fun φ : MulAut ↥S₁ => (((φ ⟨s, hsS⟩ : ↥S₁)) : K)) ha₁
    simpa [MulAut.conj_apply] using h.symm
  have ha₂act : ∀ t ∈ S₂, x * t * x⁻¹ = (a₂ : K) * t * (a₂ : K)⁻¹ := by
    intro t htS
    have h := congrArg (fun φ : MulAut ↥S₂ => (((φ ⟨t, htS⟩ : ↥S₂)) : K)) ha₂
    simpa [MulAut.conj_apply] using h.symm
  have hcomm : (a₂ : K)⁻¹ * (a₁ : K)⁻¹ = (a₁ : K)⁻¹ * (a₂ : K)⁻¹ := by
    have h := hs.commute a₁ a₁.2 a₂ a₂.2
    have h' := congrArg Inv.inv h
    rwa [mul_inv_rev, mul_inv_rev] at h'
  obtain ⟨c, hcdef⟩ : ∃ c : K, c = (a₂ : K)⁻¹ * ((a₁ : K)⁻¹ * x) := ⟨_, rfl⟩
  have hd : ∀ s ∈ S₁, s * ((a₁ : K)⁻¹ * x) = ((a₁ : K)⁻¹ * x) * s := by
    intro s hsS
    have h1 := ha₁act s hsS
    have hconj : ((a₁ : K)⁻¹ * x) * s * ((a₁ : K)⁻¹ * x)⁻¹ = s := by
      rw [show ((a₁ : K)⁻¹ * x) * s * ((a₁ : K)⁻¹ * x)⁻¹ =
          (a₁ : K)⁻¹ * (x * s * x⁻¹) * (a₁ : K) by group]
      rw [h1]
      group
    have hmul : ((a₁ : K)⁻¹ * x) * s = s * ((a₁ : K)⁻¹ * x) := by
      have := congrArg (fun u => u * ((a₁ : K)⁻¹ * x)) hconj
      simpa [mul_assoc] using this
    exact hmul.symm
  have hd₂ : ∀ t ∈ S₂, t * ((a₂ : K)⁻¹ * x) = ((a₂ : K)⁻¹ * x) * t := by
    intro t htS
    have h1 := ha₂act t htS
    have hconj : ((a₂ : K)⁻¹ * x) * t * ((a₂ : K)⁻¹ * x)⁻¹ = t := by
      rw [show ((a₂ : K)⁻¹ * x) * t * ((a₂ : K)⁻¹ * x)⁻¹ =
          (a₂ : K)⁻¹ * (x * t * x⁻¹) * (a₂ : K) by group]
      rw [h1]
      group
    have hmul : ((a₂ : K)⁻¹ * x) * t = t * ((a₂ : K)⁻¹ * x) := by
      have := congrArg (fun u => u * ((a₂ : K)⁻¹ * x)) hconj
      simpa [mul_assoc] using this
    exact hmul.symm
  have hcen_a₂inv : ∀ s ∈ S₁, s * (a₂ : K)⁻¹ = (a₂ : K)⁻¹ * s :=
    cen_inv (S := S₁) (y := (a₂ : K)) (fun s hsS => hs.commute s hsS a₂ a₂.2)
  have hcen_a₁inv : ∀ t ∈ S₂, t * (a₁ : K)⁻¹ = (a₁ : K)⁻¹ * t :=
    cen_inv (S := S₂) (y := (a₁ : K)) (fun t htS => (hs.commute a₁ a₁.2 t htS).symm)
  have hcen₁ : ∀ s ∈ S₁, s * c = c * s := by
    intro s hsS
    rw [hcdef]
    exact cen_mul (S := S₁) (u := (a₂ : K)⁻¹) (v := (a₁ : K)⁻¹ * x) hcen_a₂inv hd s hsS
  have hc_eq : c = (a₁ : K)⁻¹ * ((a₂ : K)⁻¹ * x) := by
    rw [hcdef]
    calc (a₂ : K)⁻¹ * ((a₁ : K)⁻¹ * x)
        = ((a₂ : K)⁻¹ * (a₁ : K)⁻¹) * x := by group
      _ = ((a₁ : K)⁻¹ * (a₂ : K)⁻¹) * x := by rw [hcomm]
      _ = (a₁ : K)⁻¹ * ((a₂ : K)⁻¹ * x) := by group
  have hcen₂ : ∀ t ∈ S₂, t * c = c * t := by
    intro t htS
    rw [hc_eq]
    exact cen_mul (S := S₂) (u := (a₁ : K)⁻¹) (v := (a₂ : K)⁻¹ * x) hcen_a₁inv hd₂ t htS
  have hcE : c ∈ centralizer (layer K : Set K) := hs.mem_centralizer_layer hcen₁ hcen₂
  have hcentE : centralizer (layer K : Set K) = ⊥ := centralizer_layer_eq_bot h.fitting_eq_bot
  rw [hcentE, mem_bot] at hcE
  have hc1 : (a₂ : K)⁻¹ * ((a₁ : K)⁻¹ * x) = 1 := by
    rw [← hcdef]
    exact hcE
  have hx_eq : x = (a₁ : K) * (a₂ : K) := by
    calc x = (a₁ : K) * ((a₂ : K) * ((a₂ : K)⁻¹ * ((a₁ : K)⁻¹ * x))) := by group
      _ = (a₁ : K) * ((a₂ : K) * 1) := by rw [hc1]
      _ = (a₁ : K) * (a₂ : K) := by group
  rw [hx_eq, hs.layer_eq]
  exact mul_mem (Subgroup.mem_sup_left a₁.2) (Subgroup.mem_sup_right a₂.2)

end CFSG.EvenSporadicStandard.HSStd.InvCent

module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HDConn

public section

namespace CFSG.ComponentClassification.GrSLit.HeDiag

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

namespace SwapData

variable {M K T : Subgroup X} {a : X} (h : SwapData M K T a)
include h

variable (e₁ : K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He)
  (e₂ : (conjugate K a) ⧸ pPrimeCore 2 ↥(conjugate K a) ≃* Blueprint.NativeSporadic.He)

include e₁ e₂ in
theorem exists_connected (h64 : HeldSylowElementarySixtyFour) (hOut : HeldOuterInvolutionRank)
    {A : Subgroup X} (hAT : A ≤ T) (hA : IsAbelianTwoOfRank 3 A) :
    ∃ A' : Subgroup X, A' ≤ T ⊓ K ⊔ T ⊓ conjugate K a ∧ IsAbelianTwoOfRank 3 A' ∧
      AbelianConnectedIn T 3 A A' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ζ, hζR, hζ2, hζc⟩ := h.exists_central
  have hRT : T ⊓ K ⊔ T ⊓ conjugate K a ≤ T := sup_le inf_le_left inf_le_left
  have hζT : ζ ∈ T := hRT hζR
  have hζζ : ζ * ζ = 1 := by rw [← pow_two, ← hζ2, pow_orderOf_eq_one]
  have hζ1 : ζ ≠ 1 := fun h' => by rw [h', orderOf_one] at hζ2; exact absurd hζ2 (by norm_num)
  have hRN : T ⊓ K ⊔ T ⊓ conjugate K a ≤ normalizer (K : Set X) :=
    sup_le (inf_le_right.trans le_normalizer)
      (inf_le_right.trans fun y hy => (mem_coreActionKernel.mp (h.le_coreActionKernel.2 hy)).1)
  have hζN : ζ ∈ normalizer (K : Set X) := hRN hζR
  obtain ⟨F, hFA, hF, hF8⟩ := exists_isElemTwo_eight hA
  have hFT : F ≤ T := hFA.trans hAT
  have hFr : IsAbelianTwoOfRank 3 F := hF.isAbelianTwoOfRank (by omega)
  have hAF : AbelianConnectedIn T 3 A F :=
    ⟨hAT, hA, Relation.ReflTransGen.single ⟨hFT, hFr, fun x hx y hy => hA.2.1 x hx y (hFA hy)⟩⟩
  suffices hF' : ∃ A' : Subgroup X, A' ≤ T ⊓ K ⊔ T ⊓ conjugate K a ∧
      IsAbelianTwoOfRank 3 A' ∧ AbelianConnectedIn T 3 F A' by
    obtain ⟨A', hA'R, hA', hc⟩ := hF'
    exact ⟨A', hA'R, hA', hAF.trans hc⟩
  by_cases hFU : F ≤ T ⊓ normalizer (K : Set X)
  · exact h.exists_connected_of_le e₁ e₂ hOut hζR hζ2 hζc hFU hF hF8
  obtain ⟨x, hxF, hxU⟩ := IsConcreteLE.not_le_iff_exists.mp hFU
  have hxT : x ∈ T := hFT hxF
  have hxN : x ∉ normalizer (K : Set X) := fun hx => hxU (mem_inf.mpr ⟨hxT, hx⟩)
  have hxx : x * x = 1 := hF.2 x hxF
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hswap := h.swap hxT hxN
  have hidx : ∀ f ∈ F, f ∉ normalizer (K : Set X) → x⁻¹ * f ∈ normalizer (K : Set X) := by
    intro f hf hfN
    rw [mem_normalizer_iff_conjugate_eq, ← conjugate_conjugate, hxi, hswap.1]
    exact (h.swap (hFT hf) hfN).2
  have hF₀4 : 4 ≤ Nat.card ↥(F ⊓ normalizer (K : Set X)) := by
    have := card_le_two_mul_card_inf_of_mul hxF hidx
    omega
  have hF₀ : Nat.card ↥(F ⊓ normalizer (K : Set X)) = 4 := by
    have hdvd : Nat.card ↥(F ⊓ normalizer (K : Set X)) ∣ 8 := hF8 ▸ card_dvd_of_le inf_le_left
    have hne : Nat.card ↥(F ⊓ normalizer (K : Set X)) ≠ 8 := fun h8 => hxN (mem_inf.mp
      ((eq_of_le_of_card_ge (inf_le_left : F ⊓ normalizer (K : Set X) ≤ F)
        (by rw [h8, hF8])) ▸ hxF)).2
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hc : Nat.card ↥(F ⊓ normalizer (K : Set X)) <;> simp_all
  have hcz : ∀ u ∈ T, ∀ v ∈ zpowers ζ, u * v = v * u := by
    intro u hu v hv
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
    exact (Commute.zpow_right (show Commute u ζ from hζc u hu) k).eq
  by_cases hζF : ζ ∈ F
  ·
    have hζF₀ : ζ ∈ F ⊓ normalizer (K : Set X) := mem_inf.mpr ⟨hζF, hζN⟩
    obtain ⟨y, hyF₀, hy1, hyz⟩ : ∃ y ∈ F ⊓ normalizer (K : Set X), y ≠ 1 ∧ y ≠ ζ := by
      by_contra h'
      push Not at h'
      have hle : F ⊓ normalizer (K : Set X) ≤ zpowers ζ := by
        intro w hw
        by_cases hw1 : w = 1
        · rw [hw1]
          exact one_mem _
        · rw [h' w hw hw1]
          exact mem_zpowers ζ
      have h2 := card_le_of_le hle
      rw [Nat.card_zpowers, hζ2, hF₀] at h2
      omega
    have hyy : y * y = 1 := hF.2 y (mem_inf.mp hyF₀).1
    have hyT : y ∈ T := hFT (mem_inf.mp hyF₀).1
    have hF₀eq : zpowers y ⊔ zpowers ζ = F ⊓ normalizer (K : Set X) := by
      refine eq_of_le_of_card_ge (sup_le (zpowers_le.mpr hyF₀) (zpowers_le.mpr hζF₀)) ?_
      rw [hF₀]
      exact four_le_card_sup_zpowers hyy hζζ hy1 hζ1 hyz (hζc y hyT)
    obtain ⟨Fy, hFyS, hFyC, hFye, hFy8⟩ := exists_eight_fixed e₁ h64 hOut
      (S := T ⊓ normalizer (K : Set X)) inf_le_right (h.isPGroup.to_le inf_le_left)
      h.card_left' (mem_inf.mpr ⟨hyT, (mem_inf.mp hyF₀).2⟩) hyy
    have hFyK : Fy ≤ T ⊓ K := by
      have := hFyS
      rwa [inf_normalizer_inf] at this
    have hxr : ∀ r ∈ T ⊓ K, x * r * x⁻¹ ∈ T ⊓ conjugate K a := by
      intro r hr
      refine mem_inf.mpr ⟨mul_mem (mul_mem hxT (mem_inf.mp hr).1) (inv_mem hxT), ?_⟩
      rw [← hswap.1, mem_conjugate_iff, show x * (x * r * x⁻¹) * x⁻¹ = (x * x) * r * (x⁻¹ * x⁻¹)
        by group, hxx, ← mul_inv_rev, hxx, inv_one, one_mul, mul_one]
      exact (mem_inf.mp hr).2
    let δ : ↥Fy →* X :=
      { toFun := fun r => r * (x * r * x⁻¹)
        map_one' := by simp
        map_mul' := fun r s => by
          change (r : X) * s * (x * (r * s) * x⁻¹) = r * (x * r * x⁻¹) * (s * (x * s * x⁻¹))
          have hc := h.commute_left_right (hFyK s.2) (hxr r (hFyK r.2))
          calc (r : X) * s * (x * (r * s) * x⁻¹) = r * (s * (x * r * x⁻¹)) * (x * s * x⁻¹) := by
                group
            _ = r * ((x * r * x⁻¹) * s) * (x * s * x⁻¹) := by rw [hc]
            _ = r * (x * r * x⁻¹) * (s * (x * s * x⁻¹)) := by group }
    have hδ : ∀ r : ↥Fy, δ r = (r : X) * (x * r * x⁻¹) := fun r => rfl
    have hδinj : Function.Injective δ := by
      rw [injective_iff_map_eq_one]
      intro r hr
      rw [hδ] at hr
      have hrK' : (r : X) ∈ conjugate K a := by
        have h1 : (r : X) = (x * r * x⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hr
        rw [h1]
        exact inv_mem (mem_inf.mp (hxr r (hFyK r.2))).2
      exact Subtype.ext (eq_one_of_mem_coreActionKernel e₁ h.isPGroup (mem_inf.mp (hFyK r.2)).1
        (mem_inf.mp (hFyK r.2)).2 (h.le_coreActionKernel.2 hrK'))
    have hBe : IsElemTwo δ.range := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨r, rfl⟩ _ ⟨s, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hFye.1 _ r.2 _ s.2)
      · rintro _ ⟨r, rfl⟩
        rw [← map_mul, show r * r = 1 from Subtype.ext (hFye.2 _ r.2), map_one]
    have hB8 : Nat.card δ.range = 8 := by
      rw [← hFy8]
      exact (Nat.card_congr (MonoidHom.ofInjective hδinj).toEquiv).symm
    have hBR : δ.range ≤ T ⊓ K ⊔ T ⊓ conjugate K a := by
      rintro _ ⟨r, rfl⟩
      rw [hδ]
      exact mul_mem (mem_sup_left (hFyK r.2)) (mem_sup_right (hxr r (hFyK r.2)))
    have hcomm₀ : ∀ f ∈ F ⊓ normalizer (K : Set X), ∀ r ∈ Fy, f * r = r * f := by
      rw [← hF₀eq]
      refine commute_sup_left (commute_zpowers_left fun r hr => ?_) (fun u hu r hr =>
        (hcz r (hFyK hr |> mem_inf.mp |>.1) u hu).symm)
      exact (mem_centralizer_singleton_iff.mp (hFyC hr)).symm
    have hxδ : ∀ r : ↥Fy, x * δ r = δ r * x := by
      intro r
      rw [hδ]
      have hc := h.commute_left_right (hFyK r.2) (hxr r (hFyK r.2))
      calc x * ((r : X) * (x * r * x⁻¹)) = (x * r * x⁻¹) * ((x * x) * r * (x⁻¹ * x⁻¹)) * x := by
            group
        _ = (x * r * x⁻¹) * r * x := by
            rw [hxx, ← mul_inv_rev, hxx, inv_one, one_mul, mul_one]
        _ = (r : X) * (x * r * x⁻¹) * x := by rw [hc]
    have hf₀δ : ∀ f ∈ F ⊓ normalizer (K : Set X), ∀ r : ↥Fy, f * δ r = δ r * f := by
      intro f hf r
      rw [hδ]
      have h1 := hcomm₀ f hf r r.2
      have h2 : f * x = x * f := hF.1 f (mem_inf.mp hf).1 x hxF
      have h2' : f * x⁻¹ = x⁻¹ * f := by rw [hxi, h2]
      have h3 : f * (x * r * x⁻¹) = (x * r * x⁻¹) * f := by
        calc f * (x * r * x⁻¹) = f * x * r * x⁻¹ := by group
          _ = x * (f * r) * x⁻¹ := by rw [h2]; group
          _ = x * (r * f) * x⁻¹ := by rw [h1]
          _ = x * r * (f * x⁻¹) := by group
          _ = x * r * (x⁻¹ * f) := by rw [h2']
          _ = (x * r * x⁻¹) * f := by group
      calc f * ((r : X) * (x * r * x⁻¹)) = (f * r) * (x * r * x⁻¹) := by group
        _ = (r * f) * (x * r * x⁻¹) := by rw [h1]
        _ = (r : X) * (f * (x * r * x⁻¹)) := by group
        _ = (r : X) * ((x * r * x⁻¹) * f) := by rw [h3]
        _ = (r : X) * (x * r * x⁻¹) * f := by group
    have hFB : ∀ f ∈ F, ∀ v ∈ δ.range, f * v = v * f := by
      rintro f hf _ ⟨r, rfl⟩
      by_cases hfN : f ∈ normalizer (K : Set X)
      · exact hf₀δ f (mem_inf.mpr ⟨hf, hfN⟩) r
      · have hf₀ : x⁻¹ * f ∈ F ⊓ normalizer (K : Set X) :=
          mem_inf.mpr ⟨mul_mem (inv_mem hxF) hf, hidx f hf hfN⟩
        have e1 := hf₀δ _ hf₀ r
        have e2 := hxδ r
        calc f * δ r = x * ((x⁻¹ * f) * δ r) := by group
          _ = x * (δ r * (x⁻¹ * f)) := by rw [e1]
          _ = (x * δ r) * (x⁻¹ * f) := by group
          _ = (δ r * x) * (x⁻¹ * f) := by rw [e2]
          _ = δ r * f := by group
    have hBT : δ.range ≤ T := hBR.trans hRT
    have hBr : IsAbelianTwoOfRank 3 δ.range := hBe.isAbelianTwoOfRank (by omega)
    exact ⟨δ.range, hBR, hBr, hFT, hFr, Relation.ReflTransGen.single ⟨hBT, hBr, hFB⟩⟩
  ·
    have hF'e : IsElemTwo (F ⊓ normalizer (K : Set X) ⊔ zpowers ζ) :=
      (hF.mono inf_le_left).sup (isElemTwo_zpowers hζζ)
        (fun u hu v hv => hcz u (hFT (mem_inf.mp hu).1) v hv)
    have hF'U : F ⊓ normalizer (K : Set X) ⊔ zpowers ζ ≤ T ⊓ normalizer (K : Set X) :=
      sup_le (le_inf (inf_le_left.trans hFT) inf_le_right)
        (zpowers_le.mpr (mem_inf.mpr ⟨hζT, hζN⟩))
    have hF'8 : 8 ≤ Nat.card ↥(F ⊓ normalizer (K : Set X) ⊔ zpowers ζ) := by
      refine eight_le_card_of_not_mem (H := F ⊓ normalizer (K : Set X)) ?_
        (mem_sup_right (mem_zpowers ζ)) (fun h' => hζF (mem_inf.mp h').1)
      rw [inf_of_le_right le_sup_left, hF₀]
    obtain ⟨F'', hF''F', hF''8⟩ := exists_le_card_eight hF'e.isPGroup hF'8
    obtain ⟨A', hA'R, hA', hc⟩ := h.exists_connected_of_le e₁ e₂ hOut hζR hζ2 hζc
      (hF''F'.trans hF'U) (hF'e.mono hF''F') hF''8
    have hFF'' : ∀ u ∈ F, ∀ v ∈ F'', u * v = v * u := fun u hu v hv =>
      commute_sup_right (fun u hu v hv => hF.1 u hu v (mem_inf.mp hv).1)
        (fun u hu v hv => hcz u (hFT hu) v hv) u hu v (hF''F' hv)
    have hF''T : F'' ≤ T := hF''F'.trans (hF'U.trans inf_le_left)
    have hF''r : IsAbelianTwoOfRank 3 F'' := (hF'e.mono hF''F').isAbelianTwoOfRank (by omega)
    exact ⟨A', hA'R, hA', (show AbelianConnectedIn T 3 F F'' from
      ⟨hFT, hFr, Relation.ReflTransGen.single ⟨hF''T, hF''r, hFF''⟩⟩).trans hc⟩

include e₁ e₂ in
theorem isThreeConnected (h64 : HeldSylowElementarySixtyFour) (hOut : HeldOuterInvolutionRank) :
    IsThreeConnected T := by
  have hRT : T ⊓ K ⊔ T ⊓ conjugate K a ≤ T := sup_le inf_le_left inf_le_left
  obtain ⟨E₁, hE₁R, hR₁N, hE₁e, hE₁64⟩ := exists_elem_sixtyFour e₁ h64 inf_le_right
    (h.isPGroup.to_le inf_le_left) h.card_left
  obtain ⟨E₂, hE₂R, hR₂N, hE₂e, hE₂64⟩ := exists_elem_sixtyFour e₂ h64 inf_le_right
    (h.isPGroup.to_le inf_le_left) h.card_right
  have hE₁₂ : ∀ u ∈ E₁, ∀ v ∈ E₂, u * v = v * u := fun u hu v hv =>
    h.commute_left_right (hE₁R hu) (hE₂R hv)
  have hEe : IsElemTwo (E₁ ⊔ E₂) := hE₁e.sup hE₂e hE₁₂
  have hE32 : 32 ≤ Nat.card ↥(E₁ ⊔ E₂) := by
    have := card_le_of_le (le_sup_left : E₁ ≤ E₁ ⊔ E₂)
    omega
  have hER : E₁ ⊔ E₂ ≤ T ⊓ K ⊔ T ⊓ conjugate K a :=
    sup_le (hE₁R.trans le_sup_left) (hE₂R.trans le_sup_right)
  have hRN : T ⊓ K ⊔ T ⊓ conjugate K a ≤ normalizer ((E₁ ⊔ E₂ : Subgroup X) : Set X) := by
    refine sup_le (fun r hr => mem_normalizer_sup (hR₁N hr) (mem_normalizer_of_commute
      fun v hv => h.commute_left_right hr (hE₂R hv))) (fun r hr => mem_normalizer_sup
      (mem_normalizer_of_commute fun v hv => (h.commute_left_right (hE₁R hv) hr).symm)
      (hR₂N hr))
  have hR2 : IsPGroup 2 ↥(T ⊓ K ⊔ T ⊓ conjugate K a) := h.isPGroup.to_le hRT
  intro A B hAT hBT hA hB
  obtain ⟨A', hA'R, hA', hAA'⟩ := h.exists_connected e₁ e₂ h64 hOut hAT hA
  obtain ⟨B', hB'R, hB', hBB'⟩ := h.exists_connected e₁ e₂ h64 hOut hBT hB
  have hA'E := (abelianConnectedIn_of_normal_elementary hR2 hER hRN hEe hE32 hA'R hA').mono hRT
  have hB'E := (abelianConnectedIn_of_normal_elementary hR2 hER hRN hEe hE32 hB'R hB').mono hRT
  exact hAA'.trans (hA'E.trans (hB'E.symm.trans hBB'.symm))

end SwapData

end CFSG.ComponentClassification.GrSLit.HeDiag

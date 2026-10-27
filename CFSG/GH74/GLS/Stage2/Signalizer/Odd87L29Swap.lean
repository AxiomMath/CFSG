module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Class

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage12
open scoped commutatorElement

section Swap

variable {G : Type} [Group G]

theorem isCentralInvolution_conj_aux {z : G} (h : CFSG.GH74.IsCentralInvolution z) (g : G) :
    CFSG.GH74.IsCentralInvolution (g * z * g⁻¹) := by
  obtain ⟨hz2, S, hzS, hzc⟩ := h
  refine ⟨?_, g • S, ?_, ?_⟩
  · have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z
    simpa [MulAut.conj_apply, hz2] using this
  · rw [Sylow.coe_subgroup_smul]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨z, hzS, by simp [MulAut.conj_apply]⟩
  · intro s hs
    rw [Sylow.coe_subgroup_smul] at hs
    obtain ⟨s', hs', rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hs
    have h1 : (MulAut.conj g • s') = g * s' * g⁻¹ := by simp
    rw [h1]
    calc g * s' * g⁻¹ * (g * z * g⁻¹) = g * (s' * z) * g⁻¹ := by group
      _ = g * (z * s') * g⁻¹ := by rw [hzc s' hs']
      _ = g * z * g⁻¹ * (g * s' * g⁻¹) := by group

theorem isNonCentralInvolution_of_conj {x u : G} (hx : IsNonCentralInvolution x) (h : IsConj x u) :
    IsNonCentralInvolution u := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine ⟨?_, fun hu => hx.2 ?_⟩
  · have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
    rw [← hc]
    simpa [MulAut.conj_apply, hx.1] using this
  · have := isCentralInvolution_conj_aux hu c⁻¹
    rwa [← hc, show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at this

end Swap

section Dichotomy

variable {G : Type} [Group G] {z : G}

theorem swaps_or_normalizes {L₁ L₂ : Subgroup (CentralizerBar z)} (hne : L₁ ≠ L₂)
    (hcomps : {K : Subgroup (CentralizerBar z) | IsComponent K} = {L₁, L₂}) {t : G}
    (ht : t ∈ Cen z) :
    Swaps z t L₁ L₂ ∨
      (conjugate L₁ (toBar z ⟨t, ht⟩) = L₁ ∧ conjugate L₂ (toBar z ⟨t, ht⟩) = L₂) := by
  set c : CentralizerBar z := toBar z ⟨t, ht⟩ with hc
  have hcomp : ∀ K : Subgroup (CentralizerBar z),
      K ∈ ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) →
      conjugate K c ∈ ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) := by
    intro K hK
    rw [← hcomps] at hK ⊢
    exact CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj c⁻¹) hK
  have hinj : ∀ K K' : Subgroup (CentralizerBar z), conjugate K c = conjugate K' c → K = K' := by
    intro K K' h
    exact Subgroup.map_injective (MulAut.conj c⁻¹).injective h
  have h1 := hcomp L₁ (by simp)
  have h2 := hcomp L₂ (by simp)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  ·
    exact absurd (hinj _ _ (h1.trans h2.symm)) hne
  · exact Or.inr ⟨h1, h2⟩
  · exact Or.inl ⟨ht, h1, h2⟩
  · exact absurd (hinj _ _ (h1.trans h2.symm)) hne

end Dichotomy

section Generation

variable {G : Type} [Group G]

theorem eq_zpowers_sup_of_mem {U : Subgroup G} (hU : IVK.IsFourSubgroup U) {a b : G} (ha : a ∈ U)
    (hb : b ∈ U) (ha1 : a ≠ 1) (hba : b ∉ zpowers a) : zpowers a ⊔ zpowers b = U := by
  have hle : zpowers a ⊔ zpowers b ≤ U := sup_le ((zpowers_le).mpr ha) ((zpowers_le).mpr hb)
  have hsq := four_sq_eq_one hU ha
  have ho : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) ha1
  have hcard : Nat.card ↥(zpowers a) = 2 := by rw [Nat.card_zpowers, ho]
  have hfU : Finite ↥U := Nat.finite_of_card_ne_zero (by rw [hU.2]; norm_num)
  have hfJ : Finite ↥(zpowers a ⊔ zpowers b) :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hne : zpowers a ≠ zpowers a ⊔ zpowers b := fun h => hba (by
    rw [h]
    exact Subgroup.mem_sup_right (mem_zpowers b))
  have hdvd : Nat.card ↥(zpowers a ⊔ zpowers b) ∣ 4 := by
    rw [← hU.2]
    exact Subgroup.card_dvd_of_le hle
  have hgt : 2 < Nat.card ↥(zpowers a ⊔ zpowers b) := by
    by_contra hcon
    push Not at hcon
    exact hne (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcard]; exact hcon))
  have h4 : Nat.card ↥(zpowers a ⊔ zpowers b) = 4 := by
    have hle4 : Nat.card ↥(zpowers a ⊔ zpowers b) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have h3 : Nat.card ↥(zpowers a ⊔ zpowers b) ≠ 3 := by
      intro h
      rw [h] at hdvd
      omega
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hU.2, h4])

end Generation

section TwoClass

variable {G : Type} [Group G] [Finite G]

theorem lemma29Alt_of_swap_twoClass {z : G} {k : Kind} {S : Subgroup G}
    (ctx : Stage2Ctx G z k S) (hk : IsClassicalKind k) (hND : NonCentralDihedral)
    {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)} {x : G}
    (hne : L₁ ≠ L₂) (hcomps : {K : Subgroup (CentralizerBar z) | IsComponent K} = {L₁, L₂})
    (htc : TwoClassData G z S L₁ L₂ q x) {U : Subgroup G} (hU : IVK.IsFourSubgroup U)
    (hzU : z ∈ U) {u : G} (huU : u ∈ U) (huS : u ∈ S) (hu : u ∉ zpowers z)
    (hsw : Swaps z u L₁ L₂) : Lemma29Alt z k U := by
  have hz1 : z ≠ 1 := by
    intro h
    have := ctx.central.1
    rw [h, orderOf_one] at this
    omega
  have hu1 : u ≠ 1 := fun h => hu (h ▸ one_mem _)
  have hu2 : u * u = 1 := four_sq_eq_one hU huU
  have huo : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  have hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    have := hU.1.toIsMulCommutative
    exact fun a ha b hb => congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥U) ⟨b, hb⟩)
  obtain ⟨w, hwU, hw⟩ : ∃ w ∈ U, IsNonCentralInvolution w := by
    rcases htc.classes u huo with hzu | hxu
    · have hconseq := htc.swap_conseq u huS hzu hsw
      refine ⟨u * z, U.mul_mem huU hzU, ?_⟩
      have hxo : IsNonCentralInvolution x := ⟨htc.x_inv, htc.x_nonCentral⟩
      have hnc := isNonCentralInvolution_of_conj hxo hconseq.1
      exact hnc
    · exact ⟨u, huU, isNonCentralInvolution_of_conj ⟨htc.x_inv, htc.x_nonCentral⟩ hxu⟩
  have hF := hND G z k S ctx w hw
  have hUeq : zpowers z ⊔ zpowers u = U := eq_zpowers_sup_of_mem hU hzU huU hz1 hu
  refine lemma29Alt_of_noncentral hk hwU hF (Or.inr ⟨u, 1, ?_, ?_⟩)
  · exact ⟨L₁, L₂, hne, hcomps, hsw⟩
  · show (zpowers z ⊔ zpowers u).map (MulAut.conj (1 : G)⁻¹).toMonoidHom = U
    rw [← hUeq]
    ext y
    simp

end TwoClass

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

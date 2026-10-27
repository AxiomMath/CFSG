module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3GraphRed

public section

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.KGroups.L3Eps
open CFSG.ComponentClassification.Burgoyne.PSL
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

variable {F : Type} [Field F]

theorem fl3g_ringEquiv_eq_one_of_card_three [Finite F] (hF3 : Nat.card F = 3) (σ : F ≃+* F) :
    σ = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 3 := fl3g_charP_of_dvd_card (by rw [hF3])
  let f : ZMod 3 →+* F := ZMod.castHom (dvd_refl 3) F
  have hinj : Function.Injective f := f.injective
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le (by rw [Nat.card_zmod, hF3])
  ext x
  obtain ⟨y, rfl⟩ := hbij.2 x
  have : σ.toRingHom.comp f = f := RingHom.ext_zmod _ _
  exact congrArg (fun g : ZMod 3 →+* F => g y) this

theorem fl3g_scalars_eq_bot_of_card_three [Finite F] (hF3 : Nat.card F = 3) : scalars 3 F = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 3 := fl3g_charP_of_dvd_card (by rw [hF3])
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
  obtain ⟨c, hc, hgc⟩ := mem_scalars.1 hg
  have h1 : ((c : F)) ^ 3 = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) hc
    simpa using this
  have h2 : ((c : F) - 1) ^ 3 = 0 := by
    rw [sub_pow_char, h1]; simp
  have h3 : (c : F) = 1 := by
    have := pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.1 h2
    linear_combination this
  apply Subtype.ext
  rw [hgc, h3]
  simp


section Sylow

variable {A : Type} [Group A] [Finite A] {K : Subgroup A}

theorem fl3_three_sylow_false [Finite F] (hF3 : Nat.card F = 3) (e : ↥K ≃* projectiveSL 3 F)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpF : ¬ p ∣ Nat.card F) {X : Subgroup A}
    (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥) (hXK : X ≤ K) (T : Subgroup ↥K)
    (hT : T ≤ normalizer (((X.subgroupOf K : Subgroup ↥K)) : Set ↥K)) (h12 : 12 ∣ Nat.card T) :
    False := by
  classical
  have hKcard : Nat.card K = 5616 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_projectiveSL_three_of_card_three hF3
  have hXdvd : Nat.card X ∣ 5616 := hKcard ▸ Subgroup.card_dvd_of_le hXK
  have hpX : p ∣ Nat.card X := by
    rcases hX.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hX1
    · exact h
  have hp13 : p = 13 := by
    refine prime_eq_thirteen (Fact.out) hp2 ?_ (hpX.trans hXdvd)
    rwa [hF3] at hpF
  subst hp13
  obtain ⟨n, hn⟩ := hX.exists_card_eq
  have hXcard : Nat.card X = 13 := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · exact absurd (Subgroup.card_eq_one.1 (by simpa using hn)) hX1
      · simpa using hn
    · exfalso
      have h169 : 13 ^ 2 ∣ Nat.card X := hn ▸ pow_dvd_pow 13 h
      have := h169.trans hXdvd
      norm_num at this
  set X' : Subgroup K := X.subgroupOf K with hX'
  have hX'card : Nat.card X' = 13 := by
    rw [← hXcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv
  let P : Sylow 13 K := Sylow.ofCard X' (by rw [hX'card, hKcard, factorization_5616_thirteen]; rfl)
  have hP : (P : Subgroup K) = X' := rfl
  have hPc : Nat.card (P : Subgroup K) = 13 := hX'card
  have h12' : 12 ∣ Nat.card (normalizer ((P : Subgroup K) : Set K)) :=
    h12.trans (Subgroup.card_dvd_of_le (by rw [hP]; exact hT))
  have h13 : 13 ∣ Nat.card (normalizer ((P : Subgroup K) : Set K)) := by
    have := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := (P : Subgroup K)))
    rwa [hPc] at this
  have h156 : 156 ∣ Nat.card (normalizer ((P : Subgroup K) : Set K)) :=
    (show Nat.Coprime 12 13 by norm_num).mul_dvd_of_dvd_of_dvd h12' h13
  obtain ⟨m, hm⟩ := h156
  have hidx := Subgroup.index_mul_card (normalizer ((P : Subgroup K) : Set K))
  rw [hm, hKcard] at hidx
  have hidx36 : (normalizer ((P : Subgroup K) : Set K)).index * m = 36 := by nlinarith
  have hmod := card_sylow_modEq_one 13 K
  rw [P.card_eq_index_normalizer] at hmod
  have hone : (normalizer ((P : Subgroup K) : Set K)).index = 1 := by
    have h36 : (normalizer ((P : Subgroup K) : Set K)).index ∣ 36 := ⟨m, hidx36.symm⟩
    have hle : (normalizer ((P : Subgroup K) : Set K)).index ≤ 36 := Nat.le_of_dvd (by norm_num) h36
    unfold Nat.ModEq at hmod
    interval_cases hi : (normalizer ((P : Subgroup K) : Set K)).index <;>
      first | rfl | omega
  have htop : normalizer ((P : Subgroup K) : Set K) = ⊤ := Subgroup.index_eq_one.1 hone
  have hnorm : (P : Subgroup K).Normal := Subgroup.normalizer_eq_top_iff.1 htop
  have := isSimpleGroup_projectiveSL_three F
  have : IsSimpleGroup K := e.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup K) with h | h
  · rw [h, Subgroup.card_bot] at hPc
    omega
  · rw [h, Subgroup.card_top, hKcard] at hPc
    omega

end Sylow


structure FL3GraphThree (R : GL (Fin 3) F) (Ω : Subgroup SL(3, F)) : Prop where
  isometry : Ω ≤ isometrySL 3 R
  irred : ∀ W : Submodule F (Fin 3 → F),
    (∀ g ∈ Ω, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤
  comm : ∀ T : Matrix (Fin 3) (Fin 3) F,
    (∀ g ∈ Ω, T * (g : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) * T) →
      ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F)
  twelve : 12 ∣ Nat.card Ω

section Three

theorem fl3g_card_subgroupOfEquiv {A : Type} [Group A] {K : Subgroup A}
    (e : ↥K ≃* projectiveSL 3 F) (S : Subgroup (projectiveSL 3 F)) :
    Nat.card (subgroupOfEquiv e S) = Nat.card S := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun k => (⟨e k.1, (mem_subgroupOfEquiv e S k.1).1 k.2⟩ : ↥S)) ⟨?_, ?_⟩)
  · intro a b hab
    apply Subtype.ext
    exact e.injective (congrArg (fun s : ↥S => (s : projectiveSL 3 F)) hab)
  · rintro ⟨s, hs⟩
    refine ⟨⟨e.symm s, (mem_subgroupOfEquiv e S _).2 (by simpa using hs)⟩, ?_⟩
    apply Subtype.ext
    simp

variable {A : Type} [Group A] [Finite A] {K : Subgroup A} [K.Normal] (e : ↥K ≃* projectiveSL 3 F)

theorem fl3_graph_false_three [Finite F] (hF3 : Nat.card F = 3) {φ : MulAut ↥K} {Asym : GL (Fin 3) F}
    (hφ : ∀ k, e (φ k) = (conjAut 3 F Asym * dualAut 3 F) (e k))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Subgroup A} (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hfaith : X ⊓ centralizer (K : Set A) = ⊥)
    (hJ : ∀ j : ↥K, φ j = j → (j : A) ∈ normalizer (X : Set A)) {Ω : Subgroup SL(3, F)}
    (hΩ : FL3GraphThree Asym⁻¹ Ω) : False := by
  classical
  have hZ : scalars 3 F = ⊥ := fl3g_scalars_eq_bot_of_card_three hF3
  have hnorm : ∀ k ∈ subgroupOfEquiv e (Ω.map (proj 3 F)),
      (k : A) ∈ normalizer ((X ⊓ K : Subgroup A) : Set A) := fun k hk =>
    mem_normalizer_inf_of_normal (hJ k (phi_fixes_of_isometry e hφ hΩ.isometry hk))
  have hX0 : X ⊓ K = ⊥ := by
    by_cases hpF : p ∣ Nat.card F
    · have : CharP F p := fl3g_charP_of_dvd_card hpF
      exact fl3g_X0_bot_of_char e hΩ.irred hX hnorm
    · by_contra hne
      have hinj : Function.Injective (proj 3 F) := by
        intro a b hab
        have := proj_eq_proj_iff.1 hab
        rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at this
        exact this
      have hTcard : Nat.card (subgroupOfEquiv e (Ω.map (proj 3 F))) = Nat.card Ω := by
        have h1 := fl3g_card_subgroupOfEquiv e (Ω.map (proj 3 F))
        have h2 : Nat.card (Ω.map (proj 3 F)) = Nat.card Ω :=
          (Nat.card_congr (Ω.equivMapOfInjective (proj 3 F) hinj).toEquiv).symm
        rw [h1, h2]
      refine fl3_three_sylow_false hF3 e hp2 hpF (X := X ⊓ K) (hX.to_le inf_le_left) hne inf_le_right
        (subgroupOfEquiv e (Ω.map (proj 3 F))) ?_ (hTcard ▸ hΩ.twelve)
      intro k hk
      have := hnorm k hk
      rw [Subgroup.mem_normalizer_iff] at this ⊢
      intro y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact this (y : A)
  exact fl3g_false_of_X0_bot e hφ hp2 hX hX1 hfaith hJ hΩ.isometry
    (fun A σ h => semiSL_fix_of_center_bot A σ hZ h) hΩ.comm
    (fun σ _ => fl3g_ringEquiv_eq_one_of_card_three hF3 σ) hX0

end Three

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

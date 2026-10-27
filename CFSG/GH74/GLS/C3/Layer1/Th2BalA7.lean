module

public import CFSG.GH74.GLS.C3.Layer1.Th2BalL2Local

public section

namespace CFSG.GH74.GLS.Th2.Bal

open Equiv Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
  CFSG.ClassicalInvolution.Balance

section Perm5

theorem eq_bot_of_normal_odd_perm5 (W : Subgroup (Perm (Fin 5))) [W.Normal]
    (hW : Odd (Nat.card W)) : W = ⊥ := by
  have hle : W ≤ alternatingGroup (Fin 5) := by
    intro w hw
    rw [Equiv.Perm.mem_alternatingGroup]
    have h1 : orderOf w ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W hw
    have hodd : Odd (orderOf w) := Odd.of_dvd_nat hW h1
    have h2 : orderOf (Equiv.Perm.sign w) ∣ orderOf w := orderOf_map_dvd Equiv.Perm.sign w
    have h3 : orderOf (Equiv.Perm.sign w) ∣ 2 := orderOf_dvd_of_pow_eq_one (Int.units_pow_two _)
    have h4 : orderOf (Equiv.Perm.sign w) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h3 with h | h
      · exact h
      · rw [h] at h2
        exact absurd (Odd.of_dvd_nat hodd h2) (by decide)
    exact orderOf_eq_one_iff.1 h4
  have hn : (W.subgroupOf (alternatingGroup (Fin 5))).Normal := Subgroup.Normal.subgroupOf inferInstance _
  have hs : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases hs.eq_bot_or_eq_top_of_normal (W.subgroupOf (alternatingGroup (Fin 5))) with h | h
  · rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    have : (⟨w, hle hw⟩ : alternatingGroup (Fin 5)) ∈ W.subgroupOf (alternatingGroup (Fin 5)) := hw
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · exfalso
    have hA : alternatingGroup (Fin 5) ≤ W := by
      intro a ha
      have : (⟨a, ha⟩ : alternatingGroup (Fin 5)) ∈ W.subgroupOf (alternatingGroup (Fin 5)) := by
        rw [h]
        exact Subgroup.mem_top _
      exact this
    have hdvd : Nat.card (alternatingGroup (Fin 5)) ∣ Nat.card W := Subgroup.card_dvd_of_le hA
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    rw [h60] at hdvd
    obtain ⟨k, hk⟩ := hW
    omega

end Perm5

section Theta

variable {K : Type} [Group K]

noncomputable def a7Theta (φ : K ≃* alternatingGroup (Fin 7)) : Perm (Fin 7) ≃* MulAut K :=
  (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num))).trans (MulAut.congr φ.symm)

theorem a7Theta_apply (φ : K ≃* alternatingGroup (Fin 7)) (σ : Perm (Fin 7)) (k : K) :
    ((φ (a7Theta φ σ k) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      σ * (φ k : Perm (Fin 7)) * σ⁻¹ := by
  simp [a7Theta, MulAut.conjNormal_apply]

theorem a7Theta_even (φ : K ≃* alternatingGroup (Fin 7)) (a : alternatingGroup (Fin 7)) :
    a7Theta φ (a : Perm (Fin 7)) = MulAut.conj (φ.symm a) := by
  ext k
  apply φ.injective
  apply Subtype.ext
  rw [a7Theta_apply]
  simp [MulAut.conj_apply]

theorem a7Theta_conj_injective (φ : K ≃* alternatingGroup (Fin 7)) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have h1 : a7Theta φ ((φ k : alternatingGroup (Fin 7)) : Perm (Fin 7)) = 1 := by
    rw [a7Theta_even, φ.symm_apply_apply]
    exact hk
  have h2 : ((φ k : alternatingGroup (Fin 7)) : Perm (Fin 7)) = 1 := (a7Theta φ).injective
    (h1.trans (map_one _).symm)
  have h3 : φ k = 1 := Subtype.ext h2
  exact φ.injective (h3.trans (map_one φ).symm)

theorem a7_odd_orderOf_mem_innAut (φ : K ≃* alternatingGroup (Fin 7)) {w : MulAut K}
    (hw : Odd (orderOf w)) : w ∈ innAut K := by
  obtain ⟨σ, rfl⟩ := (a7Theta φ).surjective w
  have hσ : Odd (orderOf σ) := by rwa [MulEquiv.orderOf_eq] at hw
  have h2 : orderOf (Equiv.Perm.sign σ) ∣ orderOf σ := orderOf_map_dvd Equiv.Perm.sign σ
  have h3 : orderOf (Equiv.Perm.sign σ) ∣ 2 := orderOf_dvd_of_pow_eq_one (Int.units_pow_two _)
  have h4 : orderOf (Equiv.Perm.sign σ) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h3 with h | h
    · exact h
    · rw [h] at h2
      exact absurd (Odd.of_dvd_nat hσ h2) (by decide)
  have h5 : σ ∈ alternatingGroup (Fin 7) :=
    Equiv.Perm.mem_alternatingGroup.2 (orderOf_eq_one_iff.1 h4)
  have := a7Theta_even φ ⟨σ, h5⟩
  rw [show ((⟨σ, h5⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) = σ from rfl] at this
  rw [this]
  exact ⟨_, rfl⟩

theorem a7_fixed_equiv (φ : K ≃* alternatingGroup (Fin 7)) (σ : Perm (Fin 7)) :
    Nonempty (↥(fixedSubgroup K (a7Theta φ σ)) ≃*
      ↥(centralizer ({σ} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7))) := by
  let ψ : ↥(fixedSubgroup K (a7Theta φ σ)) →* Perm (Fin 7) :=
    (alternatingGroup (Fin 7)).subtype.comp (φ.toMonoidHom.comp (fixedSubgroup K (a7Theta φ σ)).subtype)
  have hinj : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    apply φ.injective
    exact Subtype.ext hab
  have hrange : ψ.range = centralizer ({σ} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨mem_centralizer_singleton_iff.mpr ?_, (φ (k : K)).2⟩
      have hk : a7Theta φ σ (k : K) = k := k.2
      have := a7Theta_apply φ σ (k : K)
      rw [hk] at this
      show ((φ (k : K) : alternatingGroup (Fin 7)) : Perm (Fin 7)) * σ =
        σ * ((φ (k : K) : alternatingGroup (Fin 7)) : Perm (Fin 7))
      calc ((φ (k : K) : alternatingGroup (Fin 7)) : Perm (Fin 7)) * σ
          = σ * ((φ (k : K) : alternatingGroup (Fin 7)) : Perm (Fin 7)) * σ⁻¹ * σ := by
            rw [← this]
        _ = σ * ((φ (k : K) : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by group
    · rintro ⟨hy1, hy2⟩
      refine ⟨⟨φ.symm ⟨y, hy2⟩, ?_⟩, ?_⟩
      · show a7Theta φ σ (φ.symm ⟨y, hy2⟩) = φ.symm ⟨y, hy2⟩
        apply φ.injective
        apply Subtype.ext
        rw [a7Theta_apply]
        simp only [MulEquiv.apply_symm_apply]
        have : σ * y = y * σ := by
          have := (mem_centralizer_singleton_iff.mp hy1)
          exact this.symm
        show σ * y * σ⁻¹ = y
        rw [this]
        group
      · simp [ψ]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

end Theta

section Main

variable {K : Type} [Group K] [Finite K]

theorem eq_bot_of_normal_odd_of_equiv_perm5 {C : Type*} [Group C] (ρ : C ≃* Perm (Fin 5))
    (W : Subgroup C) [W.Normal] (hW : Odd (Nat.card W)) : W = ⊥ := by
  have hn : (W.map ρ.toMonoidHom).Normal := Subgroup.Normal.map inferInstance ρ.toMonoidHom ρ.surjective
  have hodd : Odd (Nat.card ↥(W.map ρ.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective ρ.injective]
    exact hW
  have := eq_bot_of_normal_odd_perm5 _ hodd
  exact (Subgroup.map_eq_bot_iff_of_injective _ ρ.injective).1 this

omit [Finite K] in
theorem eq_bot_of_odd_normal_fixed {y : MulAut K} {W' : Subgroup K}
    (hle : W' ≤ fixedSubgroup K y) (hodd : Odd (Nat.card ↥W'))
    (hnorm : ∀ c ∈ fixedSubgroup K y, ∀ k ∈ W', c * k * c⁻¹ ∈ W')
    (hC : ∀ W : Subgroup ↥(fixedSubgroup K y), W.Normal → Odd (Nat.card ↥W) → W = ⊥) :
    W' = ⊥ := by
  have hWn : (W'.subgroupOf (fixedSubgroup K y)).Normal := ⟨fun n hn c => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm c c.2 n hn⟩
  have hWodd : Odd (Nat.card ↥(W'.subgroupOf (fixedSubgroup K y))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hodd
  have hbot := hC _ hWn hWodd
  rw [Subgroup.eq_bot_iff_forall]
  intro k hk
  have hk' : (⟨k, hle hk⟩ : ↥(fixedSubgroup K y)) ∈ W'.subgroupOf (fixedSubgroup K y) := hk
  rw [hbot, Subgroup.mem_bot] at hk'
  exact congrArg Subtype.val hk'

theorem isLocallyKBalanced_three_of_a7 (φ : K ≃* alternatingGroup (Fin 7)) :
    IsLocallyKBalanced 3 K := by
  classical
  intro H hH F' hF8 hF2
  have hinj := a7Theta_conj_injective φ
  obtain ⟨B, hB⟩ : ∃ B : Subgroup (Perm (Fin 7)),
      B = (F'.map H.subtype).comap (a7Theta φ : Perm (Fin 7) →* MulAut K) := ⟨_, rfl⟩
  have hBsq : ∀ x ∈ B, x * x = 1 := by
    intro x hx
    rw [hB] at hx
    obtain ⟨g, hgF, hg⟩ := hx
    apply (a7Theta φ).injective
    rw [map_mul, map_one]
    have h1 : H.subtype g = a7Theta φ x := hg
    rw [← h1, ← map_mul]
    have := hF2 g hgF
    rw [this, map_one]
  have hBcard : Nat.card ↥B = Nat.card ↥F' := by
    rw [hB, Subgroup.comap_equiv_eq_map_symm, Subgroup.card_map_of_injective (a7Theta φ).symm.injective,
      Subgroup.card_map_of_injective H.subtype_injective]
  have hBnot : ¬ B ≤ alternatingGroup (Fin 7) := by
    intro hle
    have h4 : Nat.card ↥B ≤ 4 := A7.card_le_four_of_sq_eq_one B hle hBsq
    have h8 : 8 ≤ Nat.card ↥F' := by simpa using hF8
    omega
  obtain ⟨σ, hσB, hσA⟩ := Set.not_subset.mp hBnot
  have hσ2 : σ * σ = 1 := hBsq σ hσB
  have hσ1 : σ ≠ 1 := fun h => hσA (h ▸ one_mem _)
  have hsign : Equiv.Perm.sign σ = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · exact absurd (Equiv.Perm.mem_alternatingGroup.2 h) hσA
    · exact h
  obtain ⟨g, hgF, hg⟩ : ∃ g : H, g ∈ F' ∧ H.subtype g = a7Theta φ σ := by
    have : σ ∈ (F'.map H.subtype).comap (a7Theta φ : Perm (Fin 7) →* MulAut K) := hB ▸ hσB
    exact this
  have hg1 : g ≠ 1 := by
    intro h1
    rw [h1, map_one] at hg
    exact hσ1 ((a7Theta φ).injective (hg.symm.trans (map_one _).symm))
  have hbot : CFSG.Assembly.Dichotomy.involutionOddCore g = ⊥ := by
    by_contra hne
    have hW : pPrimeCoreOf 2 (H ⊓ centralizer ({(g : MulAut K)} : Set (MulAut K))) ≠ ⊥ :=
      fun h => hne (involutionOddCore_eq_bot_of_pPrimeCoreOf H g h)
    rw [show (g : MulAut K) = a7Theta φ σ from hg] at hW
    obtain ⟨W', hW'ne, hle, hodd, hnorm⟩ :=
      exists_normal_odd_fixed hinj (fun w hw => a7_odd_orderOf_mem_innAut φ hw) hH hW
    obtain ⟨ρ0⟩ := a7_fixed_equiv φ σ
    apply hW'ne
    rcases A7.involution_cycleType σ (by rw [pow_two]; exact hσ2) hσ1 with h | h | h
    · obtain ⟨ρ1⟩ := A7.centralizer_A7_swap_equiv (Equiv.Perm.isSwap_iff_cycleType.mpr h)
      refine eq_bot_of_odd_normal_fixed hle hodd hnorm ?_
      intro W hWn hWodd
      exact eq_bot_of_normal_odd_of_equiv_perm5 (ρ0.trans ρ1) W hWodd
    · exfalso
      have := Equiv.Perm.sign_of_cycleType σ
      rw [h, hsign] at this
      have h6 : ((-1 : ℤˣ)) ^ (Multiset.sum ({2, 2} : Multiset ℕ) + Multiset.card ({2, 2} : Multiset ℕ)) = 1 :=
        Even.neg_one_pow (by decide)
      rw [h6] at this
      exact absurd this (by decide)
    · obtain ⟨ρ1⟩ := A7.centralizer_A7_two_two_two_equiv h
      refine eq_bot_of_odd_normal_fixed hle hodd hnorm ?_
      intro W hWn hWodd
      exact eq_bot_of_normal_odd_of_equiv_perm4 (ρ0.trans ρ1) W hWodd
  exact le_bot_iff.mp ((deltaCore_le_involutionOddCore hgF hg1).trans hbot.le)

end Main

end CFSG.GH74.GLS.Th2.Bal

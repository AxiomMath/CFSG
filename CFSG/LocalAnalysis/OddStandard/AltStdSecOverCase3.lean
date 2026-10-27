module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenMain
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootS1
public import CFSG.Sporadic.HN

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal

section Arith

theorem factorial_add_two_lt_sq : ∀ m : ℕ, 9 ≤ m →
    (m + 2).factorial < (m.factorial / 2) * (m.factorial / 2) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ m hm ih =>
    obtain ⟨k, hk⟩ : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h1 : (m + 1).factorial = (m + 1) * (2 * k) := by rw [Nat.factorial_succ, hk]
    have h2 : (m + 1).factorial / 2 = (m + 1) * k := by
      rw [h1, show (m + 1) * (2 * k) = 2 * ((m + 1) * k) by ring]
      omega
    have h3 : m.factorial / 2 = k := by omega
    rw [h3] at ih
    have h4 : (m + 1 + 2).factorial = (m + 3) * (m + 2).factorial := by
      rw [show m + 1 + 2 = (m + 2) + 1 by ring, Nat.factorial_succ]
    rw [h2, h4]
    calc (m + 3) * (m + 2).factorial < (m + 3) * (k * k) := by
          exact Nat.mul_lt_mul_of_pos_left ih (by omega)
      _ ≤ ((m + 1) * (m + 1)) * (k * k) := by
          apply Nat.mul_le_mul_right
          nlinarith
      _ = (m + 1) * k * ((m + 1) * k) := by ring

theorem not_dvd_sq_factorial_div_two_of_perm {m : ℕ} (hm : 9 ≤ m) :
    ¬ (m.factorial / 2) * (m.factorial / 2) ∣ (m + 2).factorial := fun h =>
  absurd (Nat.le_of_dvd (Nat.factorial_pos _) h) (not_le.2 (factorial_add_two_lt_sq m hm))

end Arith

section Pair

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem exists_sec_pair (e : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) {H : Subgroup G}
    (hH : WreathPair L z n H) {S : Finset (Fin n)} (hS : S.card = 3)
    (ht : z ∈ centralizer (corr (X := G) e (altSub S) : Set G)) :
    ∃ f₁ f₂ : ↥(corr (X := G) e (altSub Sᶜ)) →* Sec G (corr (X := G) e (altSub S)),
      Function.Injective f₁ ∧ Function.Injective f₂ ∧ (∀ a b, f₁ a * f₂ b = f₂ b * f₁ a) ∧
        ∀ b, f₂ b = (QuotientGroup.mk (⟨z, ht⟩ :
            ↥(centralizer (corr (X := G) e (altSub S) : Set G))) :
            Sec G (corr (X := G) e (altSub S))) * f₁ b *
          (QuotientGroup.mk (⟨z, ht⟩ :
            ↥(centralizer (corr (X := G) e (altSub S) : Set G))) :
            Sec G (corr (X := G) e (altSub S)))⁻¹ := by
  classical
  obtain ⟨Ψ, hΨH, hΨ2, hΨ3, hΨinj, hΨsurj, hΨrig⟩ := exists_global_lift hH (by omega)
  have hroot := isRootLift_of_global (e := e) S hΨ2 hΨ3 hΨinj hΨrig
  set R : Subgroup G := corr (X := G) e (altSub S) with hR
  set C : Subgroup G := centralizer (R : Set G) with hC
  set B : Subgroup G := corr (X := G) e (altSub Sᶜ) with hB
  let ψ : ↥B →* G := Ψ.comp (Subgroup.inclusion (corr_le (X := G) e (altSub Sᶜ)))
  let ψ' : ↥B →* ↥C := ψ.codRestrict C hroot.cent
  have hψ'inj : Function.Injective ψ' := fun a b hab => hroot.inj (congrArg Subtype.val hab)
  let π : ↥C →* Sec G R := QuotientGroup.mk' (CFSG.oddCore ↥C)
  let tC : ↥C := ⟨z, ht⟩
  obtain ⟨eB⟩ := exists_equiv_corr_altSub (X := G) e Sᶜ
  have hSc : 5 ≤ Sᶜ.card := by rw [card_compl_fin]; omega
  have hbot : ψ'.range ⊓ CFSG.oddCore ↥C = ⊥ :=
    inf_oddCore_eq_bot_of_alt hSc ((MonoidHom.ofInjective hψ'inj).symm.trans eB)
  have hinj1 : Function.Injective (π.comp ψ') := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hb' : ψ' b ∈ CFSG.oddCore ↥C := by
      have : π (ψ' b) = 1 := hb
      exact (QuotientGroup.eq_one_iff _).1 this
    have hbr : ψ' b ∈ ψ'.range ⊓ CFSG.oddCore ↥C := ⟨⟨b, rfl⟩, hb'⟩
    rw [hbot] at hbr
    exact hψ'inj ((Subgroup.mem_bot.1 hbr).trans (map_one ψ').symm)
  refine ⟨π.comp ψ', (MulAut.conj (π tC)).toMonoidHom.comp (π.comp ψ'), hinj1,
    (MulAut.conj (π tC)).injective.comp hinj1, ?_, ?_⟩
  · intro a b
    have h1 : ψ' a * (tC * ψ' b * tC⁻¹) = (tC * ψ' b * tC⁻¹) * ψ' a :=
      Subtype.ext (hroot.comm a b)
    have h2 := congrArg π h1
    simp only [map_mul, map_inv] at h2
    simpa [MulAut.conj_apply] using h2
  · intro b
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rfl

end Pair

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem caseIIIAt_of_wreathPair (htri : ExactShapeTrichotomy)
    (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (e : L ≃* alternatingGroup (Fin n)) (hn : 12 ≤ n) {H : Subgroup G}
    (hH : WreathPair L z n H) {S : Finset (Fin n)} (hS : S.card = 3) : CaseIIIAt e z S := by
  classical
  have hex : ExactShape z L n := exactShape_of_setting h d hQ2
  have ht : z ∈ centralizer (corr (X := G) e (altSub S) : Set G) :=
    t_mem_centralizer_corr (X := G) e hex (altSub S)
  have hSc : 5 ≤ n - S.card := by omega
  have hsec := exactShape_section_three hex e hS hSc ht
  have hKcat : CFSG.SectionRank.IsKGroupCat (Sec G (corr (X := G) e (altSub S))) :=
    isKGroupCat_sec (isKGroupCat_of_kProper h.std.kProper)
      (centralizer_ne_top_of_ne_one h (exists_ne_one_of_card_ge_three e (by omega)))
  have hO := oddCore_sec_eq_bot (corr (X := G) e (altSub S))
  obtain ⟨f₁, f₂, hf₁, hf₂, hcomm, hswap⟩ := exists_sec_pair e (by omega) hH hS ht
  obtain ⟨eB⟩ := exists_equiv_corr_altSub (X := G) e Sᶜ
  have hm : Sᶜ.card = n - S.card := card_compl_fin S
  have hcardB : Nat.card ↥(corr (X := G) e (altSub Sᶜ)) = (n - S.card).factorial / 2 := by
    rw [card_eq_of_equiv_alt (by omega) eB, hm]
  have hcen : center ↥(corr (X := G) e (altSub Sᶜ)) = ⊥ := center_eq_bot_of_alt (by omega) eB
  let Φ := f₁.noncommCoprod f₂ (fun a b => hcomm a b)
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have hab' : f₁ a * f₂ b = 1 := hab
    have h2b : f₁ a = f₂ b⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_left hab'
    have hacen : a ∈ center ↥(corr (X := G) e (altSub Sᶜ)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply hf₁
      rw [map_mul, map_mul, h2b]
      exact hcomm g b⁻¹
    rw [hcen, Subgroup.mem_bot] at hacen
    have hb1 : f₂ b = 1 := by
      have := hab'
      rw [hacen, map_one, one_mul] at this
      exact this
    exact Prod.ext hacen (hf₂ (hb1.trans (map_one f₂).symm))
  have hdvd : (n - S.card).factorial / 2 * ((n - S.card).factorial / 2) ∣
      Nat.card (Sec G (corr (X := G) e (altSub S))) := by
    have := Subgroup.card_dvd_of_injective Φ hΦ
    rwa [Nat.card_prod, hcardB] at this
  rcases htri _ _ _ (n - S.card) (by omega) hKcat hO hsec with h1 | h2 | h3 | h4
  · exfalso
    have hff : ∀ b, f₂ b = f₁ b := by
      intro b
      rw [hswap b]
      have := Subgroup.mem_center_iff.1 h1 (f₁ b)
      rw [← this]
      exact mul_inv_cancel_right _ _
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_alt (by omega) eB
    apply hab
    apply hf₁
    rw [map_mul, map_mul]
    have := hcomm a b
    rwa [hff b] at this
  · exact ⟨ht, h2⟩
  · exfalso
    obtain ⟨e', -⟩ := h3
    have hc : Nat.card (Sec G (corr (X := G) e (altSub S))) = (n - S.card + 2).factorial := by
      rw [← Nat.card_congr e'.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
    rw [hc] at hdvd
    exact not_dvd_sq_factorial_div_two_of_perm (by omega) hdvd
  · exfalso
    obtain ⟨hm10, W, -, hWi, -, ⟨eW⟩⟩ := h4
    have hcardW : Nat.card (Sec G (corr (X := G) e (altSub S))) = 546061824000000 := by
      have h1 := Subgroup.card_mul_index W
      rw [hWi, Nat.card_congr eW.toEquiv, CFSG.Sporadic.HN.card_HN] at h1
      omega
    rw [hcardW, hm10] at hdvd
    revert hdvd
    norm_num [Nat.factorial]

theorem wreathPair_unique (htri : ExactShapeTrichotomy)
    (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) (hn : 12 ≤ n)
    {H₁ H₂ : Subgroup G} (h₁ : WreathPair L z n H₁) (h₂ : WreathPair L z n H₂) :
    H₂ = H₁ ∨ H₂ = H₁.map (MulAut.conj z).toMonoidHom := by
  obtain ⟨e⟩ := h.iso
  let S₀ : Finset (Fin n) := {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩}
  have hS₀ : S₀.card = 3 := by
    simp only [S₀]
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · simp [Fin.ext_iff]
    · simp [Fin.ext_iff]
  exact wreath_unique_of_caseIII_root (exactShape_of_setting h d hQ2) e (by omega) hS₀
    (caseIIIAt_of_wreathPair htri h d hQ2 e hn h₁ hS₀) h₁ h₂

end Main

section Unique

@[expose] def WreathPairUniqueAt (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (z : G), Setting G L n → Cyc L Q z →
    Nat.card Q = 2 → ∀ H₁ H₂ : Subgroup G, WreathPair L z n H₁ → WreathPair L z n H₂ →
      H₂ = H₁ ∨ H₂ = H₁.map (MulAut.conj z).toMonoidHom

theorem wreathPairUniqueAt_of_tri (htri : ExactShapeTrichotomy)
    {n : ℕ} (hn : 12 ≤ n) : WreathPairUniqueAt n :=
  fun _ _ _ _ _ _ h d hQ2 _ _ h₁ h₂ => wreathPair_unique htri h d hQ2 hn h₁ h₂

end Unique

end CFSG.OddStandard.AltStdSec

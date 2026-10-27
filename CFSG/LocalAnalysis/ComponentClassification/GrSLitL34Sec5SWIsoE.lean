module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoReal

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
  CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G] [Finite G]

theorem two_mul_le_of_dvd_ne {d n : ℕ} (hd : d ∣ n) (hne : d ≠ n) (hn : 0 < n) : 2 * d ≤ n := by
  obtain ⟨m, rfl⟩ := hd
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hn
  have hm1 : m ≠ 1 := by
    rintro rfl
    simp at hne
  have hm2 : 2 ≤ m := by omega
  nlinarith

theorem sup_zpowers_inf_withKernel {J E₁ : Subgroup G} {f : G} (hE₁ : IsElemTwo E₁)
    (hE₁K : E₁ ≤ withKernel J) (hf2 : f * f = 1) (hfK : f ∉ withKernel J)
    (hc : ∀ e ∈ E₁, e * f = f * e) :
    (E₁ ⊔ zpowers f) ⊓ withKernel J = E₁ ∧ IsElemTwo (E₁ ⊔ zpowers f) ∧
      Nat.card ↥(E₁ ⊔ zpowers f) = 2 * Nat.card E₁ := by
  have hfE₁ : f ∉ E₁ := fun h => hfK (hE₁K h)
  obtain ⟨hF, hFc⟩ := GrS4.isElemTwo_sup_zpowers hE₁ hf2 hfE₁ hc
  refine ⟨?_, hF, hFc⟩
  have hle : E₁ ≤ (E₁ ⊔ zpowers f) ⊓ withKernel J := le_inf le_sup_left hE₁K
  have hdvd : Nat.card ↥((E₁ ⊔ zpowers f) ⊓ withKernel J) ∣ Nat.card ↥(E₁ ⊔ zpowers f) :=
    Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card ↥((E₁ ⊔ zpowers f) ⊓ withKernel J) ≠ Nat.card ↥(E₁ ⊔ zpowers f) := by
    intro h
    apply hfK
    have heq := Subgroup.eq_of_le_of_card_ge
      (inf_le_left : (E₁ ⊔ zpowers f) ⊓ withKernel J ≤ E₁ ⊔ zpowers f) h.ge
    have hfF : f ∈ E₁ ⊔ zpowers f := mem_sup_right (mem_zpowers f)
    rw [← heq] at hfF
    exact (mem_inf.mp hfF).2
  have h2 := two_mul_le_of_dvd_ne hdvd hne Nat.card_pos
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem eq_sup_zpowers {J E : Subgroup G} (hE : IsEightGroup E)
    (h4 : Nat.card ↥(E ⊓ withKernel J) = 4) {e : G} (heE : e ∈ E) (heK : e ∉ withKernel J) :
    E ⊓ withKernel J ⊔ zpowers e = E := by
  have hc : ∀ w ∈ E ⊓ withKernel J, w * e = e * w := fun w hw =>
    hE.1.1 w (mem_inf.mp hw).1 e heE
  obtain ⟨-, -, hcard⟩ := sup_zpowers_inf_withKernel (hE.1.mono inf_le_left) inf_le_right
    (hE.1.2 e heE) heK hc
  refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left (zpowers_le.mpr heE)) ?_
  rw [hcard, h4, hE.2]

variable {J S : Subgroup G} {hSN : S ≤ normalizer (J : Set G)}

namespace WStd

theorem exists_k (D : WStd J S hSN) (hJ : ⁅J, J⁆ = J) (hS2 : IsPGroup 2 S) {E₁ : Subgroup G}
    (hE₁S : E₁ ≤ S) (hE₁K : E₁ ≤ withKernel J) (h4 : Nat.card E₁ = 4) {c : G} (hcE : c ∈ E₁)
    (hcC : c ∈ coreActionKernel J) (hc1 : c ≠ 1) :
    ∃ k < 64, (∀ w (hw : w ∈ E₁), D.ψ ⟨w, hE₁S hw⟩ = 1 ∨ D.ψ ⟨w, hE₁S hw⟩ = wordPerm (tg k)) ∧
      (k = 0 ∨ ∃ w, ∃ hw : w ∈ E₁, w ∉ coreActionKernel J ∧
        D.ψ ⟨w, hE₁S hw⟩ = wordPerm (tg k)) := by
  by_cases hall : ∀ w ∈ E₁, w ∈ coreActionKernel J
  · exact ⟨0, by norm_num, fun w hw => Or.inl ((D.ψ_eq_one_iff hJ (hE₁S hw)).2 (hall w hw)),
      Or.inl rfl⟩
  push Not at hall
  obtain ⟨w₀, hw₀E, hw₀C⟩ := hall
  obtain ⟨k, hk, hke⟩ := exists_tg (D.ψ_mem_T0 hS2 (hE₁S hw₀E) (hE₁K hw₀E))
  refine ⟨k, hk, fun w hw => ?_, Or.inr ⟨w₀, hw₀E, hw₀C, hke.symm⟩⟩
  have hw₀1 : w₀ ≠ 1 := fun h => hw₀C (h ▸ one_mem _)
  have hcw : c ≠ w₀ := fun h => hw₀C (h ▸ hcC)
  have hcw₀ : c * w₀ ∉ coreActionKernel J := fun h => hw₀C (by
    have := mul_mem (inv_mem hcC) h
    rwa [inv_mul_cancel_left] at this)
  have h1cw : (1 : G) ≠ c * w₀ := fun h => hcw₀ (h ▸ one_mem _)
  have hccw : c ≠ c * w₀ := fun h => hw₀1 (by
    have := congrArg (c⁻¹ * ·) h
    simpa using this.symm)
  have hwcw : w₀ ≠ c * w₀ := fun h => hc1 (by
    have := congrArg (· * w₀⁻¹) h
    simpa using this.symm)
  rcases mem_of_card_four h4 (one_mem E₁) hcE hw₀E (mul_mem hcE hw₀E) hc1.symm
      (fun h => hw₀1 h.symm) h1cw hcw hccw hwcw hw with rfl | rfl | rfl | rfl
  · left
    exact map_one D.ψ
  · left
    exact (D.ψ_eq_one_iff hJ (hE₁S hcE)).2 hcC
  · right
    exact hke.symm
  · right
    have e1 : (⟨c * w₀, hE₁S hw⟩ : ↥S) = ⟨c, hE₁S hcE⟩ * ⟨w₀, hE₁S hw₀E⟩ := rfl
    rw [e1, map_mul, (D.ψ_eq_one_iff hJ (hE₁S hcE)).2 hcC, one_mul, hke]

omit [Finite G] in
theorem mem_kVals
    (D : WStd J S hSN) {f : G} (hf : f ∈ S) {t i : ℕ} (ht : t < 64) (hi : i < 36)
    (hβ : ∀ x : MElt, x.1 < 64 → betaHat J (hSN hf) (nfM D.l x) = nfM D.l (betaYM t i x))
    {k : ℕ} (hk : k < 64)
    (hk0 : k = 0 ∨ ∃ w, ∃ hw : w ∈ S, w * w = 1 ∧ f * w = w * f ∧
      D.ψ ⟨w, hw⟩ = wordPerm (tg k)) : k ∈ kVals t i := by
  refine mem_kVals_of hk ?_
  rcases hk0 with rfl | ⟨w, hw, hw2, hfw, hψw⟩
  · exact Or.inl rfl
  right
  have hk0 : (k, (0 : ZMod 4), (0 : ZMod 4)).1 < 64 := hk
  constructor
  · have hm := mulM_lt hk0 hk0
    have e1 : wordPerm (tg (mulM (k, 0, 0) (k, 0, 0)).1) = wordPerm (tg 0) := by
      rw [← q_nfM D.hQ hm, ← nfM_mul D.hQ hk0 hk0, map_mul, q_nfM D.hQ hk0, ← hψw, ← map_mul,
        show (⟨w, hw⟩ : ↥S) * ⟨w, hw⟩ = 1 from Subtype.ext hw2, map_one, wordPerm_tg_zero']
    exact tg_injective hm (by norm_num) e1
  · have hm := betaYM_lt ht hi hk0
    have hc : D.ψ ⟨f, hf⟩ * D.ψ ⟨w, hw⟩ = D.ψ ⟨w, hw⟩ * D.ψ ⟨f, hf⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hfw
    have e1 : wordPerm (tg (betaYM t i (k, 0, 0)).1) = wordPerm (tg k) := by
      rw [← q_nfM D.hQ hm, ← hβ _ hk0, D.hψ ⟨f, hf⟩, q_nfM D.hQ hk0, ← hψw]
      calc (D.ψ ⟨f, hf⟩)⁻¹ * D.ψ ⟨w, hw⟩ * D.ψ ⟨f, hf⟩ =
          (D.ψ ⟨f, hf⟩)⁻¹ * (D.ψ ⟨f, hf⟩ * D.ψ ⟨w, hw⟩) := by rw [mul_assoc, hc]
        _ = D.ψ ⟨w, hw⟩ := by group
    exact tg_injective hm hk e1

theorem comm_of_fix
    (D : WStd J S hSN) (hS2 : IsPGroup 2 S) {f : G} (hf : f ∈ S) {t i : ℕ} (ht : t < 64)
    (hi : i < 36)
    (hβ : ∀ x : MElt, x.1 < 64 → betaHat J (hSN hf) (nfM D.l x) = nfM D.l (betaYM t i x))
    {x : MElt} (hx : x.1 < 64) (hfix : fixKB D.kb t i x = true) {p : G} (hpP : p ∈ S ⊓ J)
    (hpe : jq J ⟨p, (mem_inf.mp hpP).2⟩ = nfM D.l x) : p * f = f * p := by
  have hP2 : IsPGroup 2 (S ⊓ J : Subgroup G) := hS2.to_le inf_le_left
  have hfp : f⁻¹ * p * f = p := by
    rw [GrS4.conj_eq_iff_betaHat inf_le_right hP2 (hSN hf) (mem_normalizer_P hSN hf) hpP, hpe,
      hβ x hx]
    exact (eqKB_iff D.hQ D.hkb (betaYM_lt ht hi hx) hx).1 hfix
  calc p * f = f * (f⁻¹ * p * f) := by group
    _ = f * p := by rw [hfp]

end WStd

end CFSG.ComponentClassification.GrSLit.GrS5S

module

public import CFSG.GH74.GLS.IVK.Proofs2.GHInvSym
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup

theorem s5_odd_involution_swap : ∀ r : Perm (Fin 5), r * r = 1 → Perm.sign r = -1 →
    ∃ i j : Fin 5, i ≠ j ∧ r = swap i j := by decide +kernel

theorem s5_cl1 : ∀ (i j : Fin 5), i ≠ j → ∀ b : Perm (Fin 5), b * b = 1 →
    b * swap i j = swap i j * b → b ≠ 1 → b ≠ swap i j →
    ∃ c d : Fin 5, c ≠ d ∧ c ≠ i ∧ c ≠ j ∧ d ≠ i ∧ d ≠ j ∧
      (b = swap c d ∨ b = swap i j * swap c d) := by decide +kernel

theorem s5_cl3 : ∀ (i j c d : Fin 5), i ≠ j → c ≠ d → c ≠ i → c ≠ j → d ≠ i → d ≠ j →
    ∃ e : Fin 5, e ≠ i ∧ e ≠ j ∧ e ≠ c ∧ e ≠ d := by decide +kernel

theorem s5_cl4 : ∀ (i j c d e : Fin 5), i ≠ j → c ≠ d → c ≠ i → c ≠ j → d ≠ i → d ≠ j →
    e ≠ i → e ≠ j → e ≠ c → e ≠ d →
    (swap c d * swap d e) * (swap c d * swap d e) * (swap c d * swap d e) = 1 ∧
    swap c d * swap d e ≠ 1 ∧ Perm.sign (swap c d * swap d e) = 1 ∧
    swap i j * (swap c d * swap d e) = (swap c d * swap d e) * swap i j ∧
    swap c d * (swap c d * swap d e) * swap c d = (swap c d * swap d e)⁻¹ := by decide +kernel

theorem s5_klein_data (R : Subgroup (Perm (Fin 5)))
    (hcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hsq : ∀ a ∈ R, a * a = 1)
    (hcard : 4 ≤ Nat.card R) (hodd : ∃ r ∈ R, Perm.sign r = -1) :
    ∃ (v b c : Perm (Fin 5)), v ∈ R ∧ b ∈ R ∧ v ≠ 1 ∧ Nat.card R = 2 * Nat.card (zpowers v) ∧
      Perm.sign c = 1 ∧ orderOf c = 3 ∧ v * c = c * v ∧ b * c * b⁻¹ = c⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hrR, hrodd⟩ := hodd
  obtain ⟨i, j, hij, rfl⟩ := s5_odd_involution_swap r (hsq r hrR) hrodd
  have hr1 : swap i j ≠ 1 := by
    intro h
    have := congrArg (fun p : Perm (Fin 5) => p i) h
    simp at this
    exact hij this.symm
  have hr2 : orderOf (swap i j) = 2 := orderOf_eq_prime (by rw [sq]; exact hsq _ hrR) hr1
  have hzp : Nat.card (zpowers (swap i j)) = 2 := by rw [Nat.card_zpowers, hr2]
  obtain ⟨b₀, hb₀R, hb₀1, hb₀r⟩ : ∃ b₀ ∈ R, b₀ ≠ 1 ∧ b₀ ≠ swap i j := by
    by_contra hno
    push Not at hno
    have hle : R ≤ zpowers (swap i j) := by
      intro g hg
      by_cases hg1 : g = 1
      · rw [hg1]; exact one_mem _
      · rw [hno g hg hg1]; exact mem_zpowers _
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨c', d', hcd, hci, hcj, hdi, hdj, hb₀eq⟩ :=
    s5_cl1 i j hij b₀ (hsq b₀ hb₀R) (hcomm b₀ hb₀R _ hrR) hb₀1 hb₀r
  have hsR : swap c' d' ∈ R := by
    rcases hb₀eq with h | h
    · rw [← h]; exact hb₀R
    · have : swap c' d' = (swap i j)⁻¹ * b₀ := by rw [h]; group
      rw [this]
      exact R.mul_mem (R.inv_mem hrR) hb₀R
  obtain ⟨e', hei, hej, hec, hed⟩ := s5_cl3 i j c' d' hij hcd hci hcj hdi hdj
  obtain ⟨h3, h31, h3s, h3v, h3b⟩ := s5_cl4 i j c' d' e' hij hcd hci hcj hdi hdj hei hej hec hed
  have hR4 : Nat.card R = 4 := by
    obtain ⟨k, hk1, hk2, hksign, hkcard⟩ := CFSG.GH74.GLS.IVK.GHInv.perm_involution_data (swap i j) (hsq _ hrR) hr1
    have hk : k = 1 := by
      rw [Equiv.Perm.sign_swap hij] at hksign
      have hk3 : k ≤ 2 := by omega
      interval_cases k
      · rfl
      · simp at hksign
    subst hk
    have hC : Nat.card (centralizer ({swap i j} : Set (Perm (Fin 5)))) = 12 := by
      rw [hkcard]; decide
    have hRC : R ≤ centralizer ({swap i j} : Set (Perm (Fin 5))) := by
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm g hg _ hrR)
    have hdvd : Nat.card R ∣ 12 := hC ▸ Subgroup.card_dvd_of_le hRC
    have hRp : IsPGroup 2 ↥R := fun g => ⟨1, Subtype.ext (by simpa [sq] using hsq g g.2)⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hRp
    rw [hm] at hdvd hcard ⊢
    have hm2 : m ≤ 2 := by
      by_contra hlt
      push Not at hlt
      have h8 : 2 ^ 3 ∣ 2 ^ m := pow_dvd_pow 2 hlt
      have := h8.trans hdvd
      omega
    interval_cases m <;> simp_all
  refine ⟨swap i j, swap c' d', swap c' d' * swap d' e', hrR, hsR, hr1, ?_, h3s, ?_, h3v, ?_⟩
  · rw [hR4, hzp]
  · exact orderOf_eq_prime (by rw [pow_three']; exact h3) h31
  · rw [Equiv.swap_inv]; exact h3b

section Aut5

noncomputable def autEquivPerm5 : MulAut (alternatingGroup (Fin 5)) ≃* Perm (Fin 5) :=
  (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 5)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num) (by norm_num))).symm

theorem conjNormal_autEquivPerm5 (ψ : MulAut (alternatingGroup (Fin 5))) :
    MulAut.conjNormal (H := alternatingGroup (Fin 5)) (autEquivPerm5 ψ) = ψ :=
  (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 5)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num) (by norm_num))).apply_symm_apply ψ

variable {X : Type} [Group X] (e5 : X ≃* alternatingGroup (Fin 5))

noncomputable def autPerm5 : MulAut X ≃* Perm (Fin 5) := (MulAut.congr e5).trans autEquivPerm5

theorem autPerm5_apply (φ : MulAut X) (x : X) :
    ((e5 (φ x) : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
      autPerm5 e5 φ * (e5 x : Perm (Fin 5)) * (autPerm5 e5 φ)⁻¹ := by
  have h1 := conjNormal_autEquivPerm5 (MulAut.congr e5 φ)
  have h2 := congrArg (fun ψ : MulAut (alternatingGroup (Fin 5)) => ((ψ (e5 x) : alternatingGroup (Fin 5)) :
    Perm (Fin 5))) h1
  simp only [MulAut.conjNormal_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h2
  have h3 : autPerm5 e5 φ = autEquivPerm5 (MulAut.congr e5 φ) := rfl
  rw [h3]
  exact h2.symm

end Aut5

section Transport

variable {X : Type} [Group X]

theorem exists_klein_data_aut5 (e5 : X ≃* alternatingGroup (Fin 5)) (R' : Subgroup (MulAut X))
    (hcomm : ∀ a ∈ R', ∀ b ∈ R', a * b = b * a) (hsq : ∀ a ∈ R', a * a = 1)
    (hcard : 4 ≤ Nat.card R') (hout : ∃ r ∈ R', r ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ (v b : MulAut X) (c : X), v ∈ R' ∧ b ∈ R' ∧ v ≠ 1 ∧
      Nat.card R' = 2 * Nat.card (zpowers v) ∧ orderOf c = 3 ∧ v c = c ∧ b c = c⁻¹ := by
  classical
  set Φ : MulAut X ≃* Perm (Fin 5) := autPerm5 e5 with hΦ
  set R : Subgroup (Perm (Fin 5)) := R'.map Φ.toMonoidHom with hR
  have hmemR : ∀ σ ∈ R, ∃ a ∈ R', Φ a = σ := fun σ hσ => by
    obtain ⟨a, ha, rfl⟩ := hσ
    exact ⟨a, ha, rfl⟩
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show Φ a * Φ b = Φ b * Φ a
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  have hRsq : ∀ a ∈ R, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    show Φ a * Φ a = 1
    rw [← map_mul, hsq a ha, map_one]
  have hRcard : Nat.card R = Nat.card R' := Subgroup.card_map_of_injective Φ.injective
  have hRodd : ∃ r ∈ R, Perm.sign r = -1 := by
    obtain ⟨r, hrR, hrn⟩ := hout
    refine ⟨Φ r, ⟨r, hrR, rfl⟩, ?_⟩
    rcases Int.units_eq_one_or (Perm.sign (Φ r)) with h | h
    · exfalso
      apply hrn
      have hmem : Φ r ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.2 h
      refine ⟨e5.symm ⟨Φ r, hmem⟩, ?_⟩
      ext x
      apply e5.injective
      apply Subtype.ext
      rw [autPerm5_apply e5 r x]
      simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rfl
    · exact h
  obtain ⟨v'', b'', c'', hv''R, hb''R, hv''1, hcardv, hc''sign, hc''ord, hvc, hbc⟩ :=
    s5_klein_data R hRcomm hRsq (by rw [hRcard]; exact hcard) hRodd
  obtain ⟨v, hvR', hv⟩ := hmemR v'' hv''R
  obtain ⟨b, hbR', hb⟩ := hmemR b'' hb''R
  have hc''A : c'' ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.2 hc''sign
  refine ⟨v, b, e5.symm ⟨c'', hc''A⟩, hvR', hbR', ?_, ?_, ?_, ?_, ?_⟩
  · intro h1
    apply hv''1
    rw [← hv, h1, map_one]
  · rw [← hRcard, hcardv, Nat.card_zpowers, Nat.card_zpowers, ← hv, MulEquiv.orderOf_eq]
  · rw [MulEquiv.orderOf_eq]
    have : orderOf (⟨c'', hc''A⟩ : alternatingGroup (Fin 5)) = orderOf c'' := Subgroup.orderOf_mk _ _
    rw [this]
    exact hc''ord
  · apply e5.injective
    apply Subtype.ext
    have h1 := autPerm5_apply e5 v (e5.symm ⟨c'', hc''A⟩)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [h1, MulEquiv.apply_symm_apply]
    change Φ v * c'' * (Φ v)⁻¹ = c''
    rw [hv, mul_inv_eq_iff_eq_mul]
    exact hvc
  · apply e5.injective
    apply Subtype.ext
    have h1 := autPerm5_apply e5 b (e5.symm ⟨c'', hc''A⟩)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [h1, map_inv, MulEquiv.apply_symm_apply]
    change Φ b * c'' * (Φ b)⁻¹ = (c'' : Perm (Fin 5))⁻¹
    rw [hb]
    exact hbc

end Transport

end CFSG.GH74.GLS.Th2.Obs

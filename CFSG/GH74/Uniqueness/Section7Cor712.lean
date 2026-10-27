module

public import CFSG.GH74.Uniqueness.Section6Defs
public import CFSG.GH74.Uniqueness.Section5Stmt
public import CFSG.GH74.Uniqueness.Section5Lemma51
public import CFSG.GH74.Uniqueness.Setup

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Cor712

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

private theorem card_le_of_isSylowOf_of_isPGroup {p : ℕ} (hp : p.Prime) {P K R : Subgroup X}
    (hP : ABGLocalTools.IsSylowOf p P K) (hRK : R ≤ K) (hR : IsPGroup p R) :
    Nat.card R ≤ Nat.card P := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR
  have hdvd : p ^ k ∣ Nat.card K := hk ▸ Subgroup.card_dvd_of_le hRK
  have hkle : k ≤ (Nat.card K).factorization p :=
    (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
  rw [hk, hP.card_eq]
  exact Nat.pow_le_pow_right hp.pos hkle

omit [Finite X] in
private theorem card_conjugate_eq_card (A : Subgroup X) (g : X) :
    Nat.card (conjugate A g) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem IsProductDisconnected.card_le_of_two_le_ncard_omegaFix (h : IsProductDisconnected Z M)
    (hD : DoublyTransitive M) {p : ℕ} (hp : p.Prime) {β : Subgroup X} (hβ : β ∈ omega M)
    (hβM : β ≠ M) {P : Subgroup X} (hP : ABGLocalTools.IsSylowOf p P (M ⊓ β)) {R : Subgroup X}
    (hR : IsPGroup p R) (h2 : 2 ≤ (omegaFix M (R : Set X)).ncard) : Nat.card R ≤ Nat.card P := by
  obtain ⟨δ, hδ⟩ : (omegaFix M (R : Set X)).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]
    omega
  obtain ⟨g, hg⟩ := exists_conjugate_eq_base hδ.1
  have hΩR' : omegaFix M ((conjugate R g : Subgroup X) : Set X) =
      (fun β => conjugate β g) '' omegaFix M (R : Set X) := omegaFix_conjugate R g
  have hMΩ : M ∈ omegaFix M ((conjugate R g : Subgroup X) : Set X) := by
    rw [hΩR']
    exact ⟨δ, hδ, hg⟩
  have hR'M : conjugate R g ≤ M := (h.mem_omegaFix_iff.mp hMΩ).2
  have h2' : 1 < (omegaFix M ((conjugate R g : Subgroup X) : Set X)).ncard := by
    rw [ncard_omegaFix_conjugate]
    omega
  obtain ⟨ε, hε, hεM⟩ := Set.exists_ne_of_one_lt_ncard h2' M
  obtain ⟨hεΩ, hR'ε⟩ := h.mem_omegaFix_iff.mp hε
  obtain ⟨m, hm, hmβ⟩ := h.exists_mem_conjugate_of_doublyTransitive hD hβ hεΩ hβM hεM
  have hle : conjugate (conjugate R g) m⁻¹ ≤ M ⊓ β := by
    intro x hx
    have h1 : m⁻¹ * x * m⁻¹⁻¹ ∈ conjugate R g := mem_conjugate_iff.mp hx
    have h2 : m⁻¹ * x * m⁻¹⁻¹ ∈ M ⊓ conjugate β m := by
      rw [hmβ]
      exact le_inf hR'M hR'ε h1
    obtain ⟨h3, h4⟩ := Subgroup.mem_inf.mp h2
    have h5 : x ∈ β := by
      have := mem_conjugate_iff.mp h4
      have e : m * (m⁻¹ * x * m⁻¹⁻¹) * m⁻¹ = x := by group
      rwa [e] at this
    have h6 : x ∈ M := by
      have := M.mul_mem (M.mul_mem hm h3) (M.inv_mem hm)
      have e : m * (m⁻¹ * x * m⁻¹⁻¹) * m⁻¹ = x := by group
      rwa [e] at this
    exact Subgroup.mem_inf.mpr ⟨h6, h5⟩
  have hRp : IsPGroup p (conjugate (conjugate R g) m⁻¹) := (hR.map _).map _
  have := card_le_of_isSylowOf_of_isPGroup hp hP hle hRp
  rwa [card_conjugate_eq_card, card_conjugate_eq_card] at this

theorem IsProductDisconnected.maximal_prop52Cond (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) (hD : DoublyTransitive M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {β : Subgroup X} (hβ : β ∈ omega M) (hβM : β ≠ M) {P : Subgroup X}
    (hP : ABGLocalTools.IsSylowOf p P (M ⊓ β)) (h3 : 3 ≤ (omegaFix M (P : Set X)).ncard) :
    Maximal (Prop52Cond Z M p) P := by
  have hM : M ∈ omega M := self_mem_omega M
  refine ⟨⟨hP.isPGroup, h3, ?_⟩, fun R hR hPR => ?_⟩
  · obtain ⟨s, hs, hsP, hs1, -⟩ := h.exists_swap_of_isSylowOf hZ hp hp2 hM hβ hβM.symm hP
    exact ⟨s, hs, hsP, h.lemma39_card hZ hM hβM.symm hp hp2 hs hs1 hP hsP⟩
  · have hcard := h.card_le_of_two_le_ncard_omegaFix hD hp hβ hβM hP hR.pgroup
      (by have := hR.three_le; omega)
    exact le_of_eq (Subgroup.eq_of_le_of_card_ge hPR hcard).symm

theorem ZDSetup.cor712 (S : ZDSetup X Z M) (hT4 : Theorem4Stmt Z M) (h52 : Prop52Stmt Z M)
    {β : Subgroup X} (hβ : β ∈ omega M) (hβM : β ≠ M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup X} (hP : ABGLocalTools.IsSylowOf p P (M ⊓ β)) :
    ((omegaFix M (P : Set X)).ncard = 2 → ABGLocalTools.IsSylowOf p P ⊤) ∧
    (3 ≤ (omegaFix M (P : Set X)).ncard →
      zNumShare Z M p = 1 ∧ ∃ y ∈ Z, y ∈ M ∧ y ∈ centralizer (P : Set X)) ∧
    (p ∣ zNum Z M → (omegaFix M (P : Set X)).ncard = 2 ∧ ABGLocalTools.IsSylowOf p P ⊤) := by
  have hZ := S.invariant
  have h := S.prodDisc
  have : Fact p.Prime := ⟨hp⟩
  have hM : M ∈ omega M := self_mem_omega M
  have hPM : P ≤ M := hP.le.trans inf_le_left
  have hPβ : P ≤ β := hP.le.trans inf_le_right
  have hMΩ : M ∈ omegaFix M (P : Set X) := h.mem_omegaFix_iff.mpr ⟨hM, hPM⟩
  have hβΩ : β ∈ omegaFix M (P : Set X) := h.mem_omegaFix_iff.mpr ⟨hβ, hPβ⟩
  have hpair : ({M, β} : Set (Subgroup X)).ncard = 2 := Set.ncard_pair hβM.symm
  have hsub : ({M, β} : Set (Subgroup X)) ⊆ omegaFix M (P : Set X) := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hMΩ
    · exact hβΩ
  have ha : (omegaFix M (P : Set X)).ncard = 2 → ABGLocalTools.IsSylowOf p P ⊤ := by
    intro hΩ
    have heq : ({M, β} : Set (Subgroup X)) = omegaFix M (P : Set X) :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hΩ, hpair]) (Set.toFinite _)
    exact h.isSylowOf_omegaFix_pair' hp hp2 hβM.symm hP heq.symm
  have hb : 3 ≤ (omegaFix M (P : Set X)).ncard →
      zNumShare Z M p = 1 ∧ ∃ y ∈ Z, y ∈ M ∧ y ∈ centralizer (P : Set X) := by
    intro h3
    have hmax := h.maximal_prop52Cond hZ hT4.1 hp hp2 hβ hβM hP h3
    obtain ⟨y, hy, hyN, hyfix⟩ := (h52 p hp hp2 P hmax).2 hT4.1 M hMΩ
    have hyM : y ∈ M := (h.conjugate_eq_iff_mem hM).mp hyfix
    have hodd : Odd (Nat.card P) := by
      rw [hP.card_eq]
      exact (hp.odd_of_ne_two hp2).pow
    have hyP : y ∈ centralizer (P : Set X) := by
      rcases hT4.2 y hy hyM P hodd hPM hyN with hc | hc
      · rw [Subgroup.mem_centralizer_iff]
        intro w hw
        exact (hc w hw).symm
      · exact absurd (hc β hβΩ) hβM
    refine ⟨?_, y, hy, hyM, hyP⟩
    obtain ⟨t, ht, htβ⟩ := h.exists_swap hZ hM hβ
    have htM : t ∉ M := fun htM => hβM (by
      rw [← htβ]
      exact (h.conjugate_eq_iff_mem hM).mpr htM)
    have hr := (h.prop36d hZ ht htM hy hyM).2.2.2
    rw [htβ] at hr
    have h2 := Subgroup.relIndex_mul_card (centralizer ({y} : Set X)) (M ⊓ β)
    rw [hr] at h2
    have hr0 : 0 < zNum Z M := S.odd_zNum.pos
    have hfac : (Nat.card (M ⊓ β : Subgroup X)).factorization p = (zNum Z M).factorization p +
        (Nat.card ↥(centralizer ({y} : Set X) ⊓ (M ⊓ β))).factorization p := by
      rw [← h2, Nat.factorization_mul hr0.ne' Nat.card_pos.ne']
      rfl
    have hPle : P ≤ centralizer ({y} : Set X) ⊓ (M ⊓ β) := by
      refine le_inf (fun w hw => ?_) hP.le
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hyP w hw)
    have hdvd : p ^ (Nat.card (M ⊓ β : Subgroup X)).factorization p ∣
        Nat.card ↥(centralizer ({y} : Set X) ⊓ (M ⊓ β)) := by
      rw [← hP.card_eq]
      exact Subgroup.card_dvd_of_le hPle
    have hle := (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
    have hv : (zNum Z M).factorization p = 0 := by omega
    unfold zNumShare
    rw [hv, pow_zero]
  refine ⟨ha, hb, fun hpm => ?_⟩
  have hr0 : 0 < zNum Z M := S.odd_zNum.pos
  have hle2 : (omegaFix M (P : Set X)).ncard ≤ 2 := by
    by_contra hlt
    have h1 := (hb (by omega)).1
    have hpos : 0 < (zNum Z M).factorization p := hp.factorization_pos_of_dvd hr0.ne' hpm
    have hpow : p ^ 1 ≤ p ^ (zNum Z M).factorization p := Nat.pow_le_pow_right hp.pos hpos
    unfold zNumShare at h1
    rw [h1, pow_one] at hpow
    have := hp.two_le
    omega
  have hge2 : 2 ≤ (omegaFix M (P : Set X)).ncard :=
    hpair ▸ Set.ncard_le_ncard hsub (Set.toFinite _)
  have hΩ : (omegaFix M (P : Set X)).ncard = 2 := le_antisymm hle2 hge2
  exact ⟨hΩ, ha hΩ⟩

end Cor712

end CFSG.GH74.Uniqueness

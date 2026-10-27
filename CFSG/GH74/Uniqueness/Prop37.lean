module

public import CFSG.GH74.Uniqueness.Prop36

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Prop37

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem commutator_eq_sq_of_inverts {t x : X} (hx : t * x * t⁻¹ = x⁻¹) :
    x * t * x⁻¹ * t⁻¹ = x * x := by
  calc x * t * x⁻¹ * t⁻¹ = x * (t * x * t⁻¹)⁻¹ := by group
    _ = x * (x⁻¹)⁻¹ := by rw [hx]
    _ = x * x := by rw [inv_inv]

omit [Finite X] in
theorem odd_orderOf_of_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup X}
    (hP : IsPGroup p P) {x : X} (hx : x ∈ P) : Odd (orderOf x) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk]
  exact (hp.odd_of_ne_two hp2).pow

theorem IsProductDisconnected.isZStarIn_of_le_inf_conjugate (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t : X} (ht : t ∈ Z) (htM : t ∉ M) {W : Subgroup X}
    (hW : W ≤ M ⊓ conjugate M t) (htW : t ∈ normalizer (W : Set X)) :
    IsZStarIn (W ⊔ zpowers t) t :=
  IsZStarIn.restrict (hZ.mul_self_eq_one ht) (h.isZStarIn_inf_conjugate_sup hZ ht htM)
    (hW.trans le_sup_left) htW

theorem IsProductDisconnected.relIndex_inf_conjugate_eq_zNum (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t : X} (ht : t ∈ Z) (htM : t ∉ M) :
    (centralizer ({t} : Set X)).relIndex (M ⊓ conjugate M t) = zNum Z M := by
  obtain ⟨z, hz, hzM⟩ := h.2.1
  exact (h.prop36d hZ ht htM hz hzM).2.2.1

theorem IsProductDisconnected.prop37a (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t : X} (ht : t ∈ Z) (htM : t ∉ M) {W P : Subgroup X}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hW : W ≤ M ⊓ conjugate M t)
    (htW : t ∈ normalizer (W : Set X)) (hPW : P ≤ W) (hPp : IsPGroup p P)
    (htP : t ∈ normalizer (P : Set X)) :
    ∃ Q : Subgroup X, ABGLocalTools.IsSylowOf p Q W ∧ P ≤ Q ∧ t ∈ normalizer (Q : Set X) :=
  exists_invariant_sylow hp hp2 (hZ.1 t ht) htW
    (h.isZStarIn_of_le_inf_conjugate hZ ht htM hW htW) hPW hPp htP

theorem IsProductDisconnected.prop37b (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t : X} (ht : t ∈ Z) (htM : t ∉ M) {W P : Subgroup X}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hW : W ≤ M ⊓ conjugate M t)
    (htW : t ∈ normalizer (W : Set X)) (hP : ABGLocalTools.IsSylowOf p P W)
    (htP : t ∈ normalizer (P : Set X)) :
    ∃ S : Subgroup X, S ≤ P ∧ ABGLocalTools.IsSylowOf p S (W ⊓ centralizer ({t} : Set X)) :=
  exists_sylow_le_centralizer hp hp2 (hZ.1 t ht) htW
    (h.isZStarIn_of_le_inf_conjugate hZ ht htM hW htW) hP htP

theorem IsProductDisconnected.prop37d (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t : X} (ht : t ∈ Z) (htM : t ∉ M) {P : Subgroup X} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hP : ABGLocalTools.IsSylowOf p P (M ⊓ conjugate M t))
    (htP : t ∈ normalizer (P : Set X)) :
    Nat.card (CFSG.OddInversion.invertedSet P t) = p ^ (zNum Z M).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  set D := M ⊓ conjugate M t with hD
  have ht2 : orderOf t = 2 := hZ.1 t ht
  have htD : t ∈ normalizer (D : Set X) := mem_normalizer_inf_conjugate (hZ.mul_self_eq_one ht)
  obtain ⟨S, hSP, hS⟩ := h.prop37b hZ ht htM hp hp2 le_rfl htD hP htP
  have hPC : P ⊓ centralizer ({t} : Set X) = S := by
    refine hS.eq_of_le (le_inf hSP (hS.le.trans inf_le_right))
      (inf_le_inf_right _ hP.le) hP.isPGroup.to_inf_left
  have hPcard := hP.card_eq
  have hScard := hS.card_eq
  have hPodd : Odd (Nat.card P) := by
    rw [hPcard]
    exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨-, -, hIcard⟩ := CFSG.OddInversion.odd_inversion_coset_count hPodd htP
    (CFSG.OddInversion.notMem_of_odd_card hPodd ht2) ht2
  have h1 := Subgroup.relIndex_mul_card (centralizer ({t} : Set X)) P
  have h2 := Subgroup.relIndex_mul_card (centralizer ({t} : Set X)) D
  rw [inf_comm, hPC, ← hIcard] at h1
  rw [inf_comm, h.relIndex_inf_conjugate_eq_zNum hZ ht htM] at h2
  have hr : 0 < zNum Z M := by
    unfold zNum
    have := h.2.1.to_subtype
    exact Nat.card_pos
  have hc : 0 < Nat.card ↥(D ⊓ centralizer ({t} : Set X)) := Nat.card_pos
  have hfac : (Nat.card D).factorization p =
      (zNum Z M).factorization p + (Nat.card ↥(D ⊓ centralizer ({t} : Set X))).factorization p := by
    rw [← h2, Nat.factorization_mul hr.ne' hc.ne']
    rfl
  rw [hPcard, hScard, hfac, pow_add] at h1
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) h1

theorem IsProductDisconnected.prop37c (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t : X} (ht : t ∈ Z) (htM : t ∉ M) {W P : Subgroup X}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hW : W ≤ M ⊓ conjugate M t)
    (htW : t ∈ normalizer (W : Set X)) (hPW : P ≤ W) (hPp : IsPGroup p P)
    (htP : t ∈ normalizer (P : Set X)) :
    CFSG.OddInversion.invertedSet P t ⊆ (pPrimeCoreIn W : Set X) ∧
      Nat.card (CFSG.OddInversion.invertedSet P t) ≤ p ^ (zNum Z M).factorization p := by
  refine ⟨fun x hx => ?_, ?_⟩
  · have hcomm := commutator_mem_pPrimeCoreIn
      (h.isZStarIn_of_le_inf_conjugate hZ ht htM hW htW) htW (hPW hx.1)
    rw [commutator_eq_sq_of_inverts hx.2] at hcomm
    exact mem_of_mul_self_mem_of_odd_orderOf (odd_orderOf_of_isPGroup hp hp2 hPp hx.1) hcomm
  · have htD : t ∈ normalizer ((M ⊓ conjugate M t : Subgroup X) : Set X) :=
      mem_normalizer_inf_conjugate (hZ.mul_self_eq_one ht)
    obtain ⟨Q, hQ, hPQ, htQ⟩ := h.prop37a hZ ht htM hp hp2 le_rfl htD (hPW.trans hW) hPp htP
    rw [← h.prop37d hZ ht htM hp hp2 hQ htQ]
    exact Nat.card_mono (Set.toFinite _) (CFSG.OddInversion.invertedSet_mono hPQ)

end Prop37

section Omega37

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem IsProductDisconnected.prop37a_omega (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t : X} (ht : t ∈ Z) {β : Subgroup X} (hβ : β ∈ omega M)
    (hβt : conjugate β t ≠ β) {W P : Subgroup X} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hW : W ≤ β ⊓ conjugate β t) (htW : t ∈ normalizer (W : Set X)) (hPW : P ≤ W)
    (hPp : IsPGroup p P) (htP : t ∈ normalizer (P : Set X)) :
    ∃ Q : Subgroup X, ABGLocalTools.IsSylowOf p Q W ∧ P ≤ Q ∧ t ∈ normalizer (Q : Set X) := by
  obtain ⟨g, rfl⟩ := hβ
  exact (h.conjugate_point hZ g).prop37a hZ ht ((h.conjugate_ne_iff ⟨g, rfl⟩).mp hβt) hp hp2 hW
    htW hPW hPp htP

theorem IsProductDisconnected.prop37b_omega (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t : X} (ht : t ∈ Z) {β : Subgroup X} (hβ : β ∈ omega M)
    (hβt : conjugate β t ≠ β) {W P : Subgroup X} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hW : W ≤ β ⊓ conjugate β t) (htW : t ∈ normalizer (W : Set X))
    (hP : ABGLocalTools.IsSylowOf p P W) (htP : t ∈ normalizer (P : Set X)) :
    ∃ S : Subgroup X, S ≤ P ∧ ABGLocalTools.IsSylowOf p S (W ⊓ centralizer ({t} : Set X)) := by
  obtain ⟨g, rfl⟩ := hβ
  exact (h.conjugate_point hZ g).prop37b hZ ht ((h.conjugate_ne_iff ⟨g, rfl⟩).mp hβt) hp hp2 hW
    htW hP htP

theorem IsProductDisconnected.prop37c_omega (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t : X} (ht : t ∈ Z) {β : Subgroup X} (hβ : β ∈ omega M)
    (hβt : conjugate β t ≠ β) {W P : Subgroup X} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hW : W ≤ β ⊓ conjugate β t) (htW : t ∈ normalizer (W : Set X)) (hPW : P ≤ W)
    (hPp : IsPGroup p P) (htP : t ∈ normalizer (P : Set X)) :
    CFSG.OddInversion.invertedSet P t ⊆ (pPrimeCoreIn W : Set X) ∧
      Nat.card (CFSG.OddInversion.invertedSet P t) ≤ p ^ (zNum Z M).factorization p := by
  obtain ⟨g, rfl⟩ := hβ
  rw [← zNum_conjugate hZ M g]
  exact (h.conjugate_point hZ g).prop37c hZ ht ((h.conjugate_ne_iff ⟨g, rfl⟩).mp hβt) hp hp2 hW
    htW hPW hPp htP

theorem IsProductDisconnected.prop37d_omega (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t : X} (ht : t ∈ Z) {β : Subgroup X} (hβ : β ∈ omega M)
    (hβt : conjugate β t ≠ β) {P : Subgroup X} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hP : ABGLocalTools.IsSylowOf p P (β ⊓ conjugate β t)) (htP : t ∈ normalizer (P : Set X)) :
    Nat.card (CFSG.OddInversion.invertedSet P t) = p ^ (zNum Z M).factorization p := by
  obtain ⟨g, rfl⟩ := hβ
  rw [← zNum_conjugate hZ M g]
  exact (h.conjugate_point hZ g).prop37d hZ ht ((h.conjugate_ne_iff ⟨g, rfl⟩).mp hβt) hp hp2 hP htP

theorem IsProductDisconnected.prop35_omega (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t : X} (ht : t ∈ Z) {β γ : Subgroup X} (hβ : β ∈ omega M)
    (hβγ : β ≠ γ) (hγ : conjugate β t = γ) : IsZStarIn ((β ⊓ γ) ⊔ zpowers t) t := by
  obtain ⟨g, rfl⟩ := hβ
  have htβ : t ∉ conjugate M g :=
    (h.conjugate_ne_iff ⟨g, rfl⟩).mp (fun heq => hβγ (heq.symm.trans hγ))
  rw [← hγ]
  exact (h.conjugate_point hZ g).isZStarIn_inf_conjugate_sup hZ ht htβ

end Omega37

end CFSG.GH74.Uniqueness

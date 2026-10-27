module

public import CFSG.GH74.Uniqueness.Prop37

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped Pointwise commutatorElement

section Prop38

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem card_invertedSet_mul_card_inf_centralizer {Q : Subgroup X} {z : X}
    (hQ : Odd (Nat.card Q)) (hz : orderOf z = 2) (hzQ : z ∈ normalizer (Q : Set X)) :
    Nat.card (CFSG.OddInversion.invertedSet Q z) *
      Nat.card ↥(centralizer ({z} : Set X) ⊓ Q) = Nat.card Q := by
  obtain ⟨-, -, hIcard⟩ := CFSG.OddInversion.odd_inversion_coset_count hQ hzQ
    (CFSG.OddInversion.notMem_of_odd_card hQ hz) hz
  rw [hIcard]
  exact Subgroup.relIndex_mul_card _ _

theorem IsProductDisconnected.conjugate_ne_of_ne_self (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) {β : Subgroup X}
    (hβ : β ∈ omega M) (hβM : β ≠ M) : conjugate β z ≠ β := by
  intro hfix
  obtain ⟨γ, -, huniq⟩ := h.existsUnique_fixed_point hZ hz
  have h1 := huniq β ⟨hβ, hfix⟩
  have h2 := huniq M ⟨self_mem_omega M, (h.conjugate_eq_iff_mem (self_mem_omega M)).mpr hzM⟩
  exact hβM (h1.trans h2.symm)

omit [Finite X] in
theorem prop38a {β A : Subgroup X} {z : X} (hA : A ≤ M ⊓ β)
    (hzA : z ∈ normalizer (A : Set X)) : A ≤ M ⊓ β ⊓ conjugate β z := by
  intro x hx
  refine Subgroup.mem_inf.mpr ⟨hA hx, mem_conjugate_iff.mpr ?_⟩
  exact (Subgroup.mem_inf.mp (hA ((Subgroup.mem_normalizer_iff.mp hzA x).mp hx))).2

theorem IsProductDisconnected.prop38b (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) {β : Subgroup X}
    (hβ : β ∈ omega M) (hβM : β ≠ M) {P : Subgroup X} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hPD : P ≤ M ⊓ β) (hPp : IsPGroup p P) (hzP : z ∈ normalizer (P : Set X)) :
    Nat.card (CFSG.OddInversion.invertedSet P z) ≤ p ^ (zNum Z M).factorization p ∧
      (ABGLocalTools.IsSylowOf p P (M ⊓ β) →
        Nat.card (CFSG.OddInversion.invertedSet P z) = p ^ (zNum Z M).factorization p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hβz := h.conjugate_ne_of_ne_self hZ hz hzM hβ hβM
  have hz2 : orderOf z = 2 := hZ.1 z hz
  have hPE := prop38a hPD hzP
  have hPF : P ≤ β ⊓ conjugate β z := fun x hx => by
    have := Subgroup.mem_inf.mp (hPE hx)
    exact ⟨(Subgroup.mem_inf.mp this.1).2, this.2⟩
  have hF : z ∈ normalizer ((β ⊓ conjugate β z : Subgroup X) : Set X) :=
    mem_normalizer_inf_conjugate (M := β) (hZ.mul_self_eq_one hz)
  have hle := (h.prop37c_omega hZ hz hβ hβz hp hp2 le_rfl hF hPF hPp hzP).2
  refine ⟨hle, fun hP => le_antisymm hle ?_⟩
  obtain ⟨t, ht, rfl⟩ := h.exists_swap hZ (self_mem_omega M) hβ
  have htM : t ∉ M := fun htM => hβM ((h.conjugate_eq_iff_mem (self_mem_omega M)).mpr htM)
  set D := M ⊓ conjugate M t with hD
  have hr : (centralizer ({z} : Set X)).relIndex D = zNum Z M :=
    (h.prop36d hZ ht htM hz hzM).2.2.2
  have hPcard := hP.card_eq
  have hPodd : Odd (Nat.card P) := by
    rw [hPcard]
    exact (hp.odd_of_ne_two hp2).pow
  have h1 := card_invertedSet_mul_card_inf_centralizer hPodd hz2 hzP
  have h2 := Subgroup.relIndex_mul_card (centralizer ({z} : Set X)) D
  rw [hr] at h2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hPp.to_inf_right (H := centralizer ({z} : Set X)))
  have hkdvd : p ^ k ∣ Nat.card ↥(centralizer ({z} : Set X) ⊓ D) := by
    rw [← hk]
    exact Subgroup.card_dvd_of_le (inf_le_inf_left _ hP.le)
  have hkb : k ≤ (Nat.card ↥(centralizer ({z} : Set X) ⊓ D)).factorization p :=
    (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hkdvd
  have hr0 : 0 < zNum Z M := by
    unfold zNum
    have := h.2.1.to_subtype
    exact Nat.card_pos
  have hfac : (Nat.card D).factorization p = (zNum Z M).factorization p +
      (Nat.card ↥(centralizer ({z} : Set X) ⊓ D)).factorization p := by
    rw [← h2, Nat.factorization_mul hr0.ne' Nat.card_pos.ne']
    rfl
  rw [hk, hPcard, hfac] at h1
  set b := (Nat.card ↥(centralizer ({z} : Set X) ⊓ D)).factorization p with hb
  set v := (zNum Z M).factorization p with hv
  have hexp : p ^ (v + b) = p ^ v * p ^ (b - k) * p ^ k := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hI : Nat.card (CFSG.OddInversion.invertedSet P z) = p ^ v * p ^ (b - k) :=
    Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos k) (by rw [h1, hexp])
  rw [hI]
  exact Nat.le_mul_of_pos_right _ (pow_pos hp.pos _)

theorem IsProductDisconnected.exists_invariant_sylow_of_card_eq (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) {β : Subgroup X}
    (hβ : β ∈ omega M) (hβM : β ≠ M) {P : Subgroup X} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hPD : P ≤ M ⊓ β) (hPp : IsPGroup p P) (hzP : z ∈ normalizer (P : Set X))
    (hcard : Nat.card (CFSG.OddInversion.invertedSet P z) = p ^ (zNum Z M).factorization p) :
    ∃ Q : Subgroup X, ABGLocalTools.IsSylowOf p Q (M ⊓ β) ∧ Q ≤ M ⊓ β ⊓ conjugate β z ∧
      z ∈ normalizer (Q : Set X) := by
  obtain ⟨t, ht, rfl⟩ := h.exists_swap hZ (self_mem_omega M) hβ
  have htM : t ∉ M := fun htM => hβM ((h.conjugate_eq_iff_mem (self_mem_omega M)).mpr htM)
  have : Fact p.Prime := ⟨hp⟩
  have hβz := h.conjugate_ne_of_ne_self hZ hz hzM hβ hβM
  have hz2 : orderOf z = 2 := hZ.1 z hz
  set D := M ⊓ conjugate M t with hD
  have hr : (centralizer ({z} : Set X)).relIndex D = zNum Z M :=
    (h.prop36d hZ ht htM hz hzM).2.2.2
  set E := D ⊓ conjugate (conjugate M t) z with hE
  have hPE : P ≤ E := prop38a hPD hzP
  have hED : E ≤ D := inf_le_left
  have hEF : E ≤ conjugate M t ⊓ conjugate (conjugate M t) z := fun x hx => by
    have := Subgroup.mem_inf.mp hx
    exact ⟨(Subgroup.mem_inf.mp this.1).2, this.2⟩
  have hF : z ∈ normalizer ((conjugate M t ⊓ conjugate (conjugate M t) z : Subgroup X) : Set X) :=
    mem_normalizer_inf_conjugate (M := conjugate M t) (hZ.mul_self_eq_one hz)
  have hzE : z ∈ normalizer (E : Set X) := by
    rw [hE, hD, inf_assoc]
    exact mem_normalizer_inf (Subgroup.le_normalizer hzM) hF
  obtain ⟨Q, hQ, hPQ, hzQ⟩ := h.prop37a_omega hZ hz hβ hβz hp hp2 hEF hzE hPE hPp hzP
  obtain ⟨S, hSQ, hS⟩ := h.prop37b_omega hZ hz hβ hβz hp hp2 hEF hzE hQ hzQ
  have hQp := hQ.isPGroup
  have hQD : Q ≤ D := hQ.le.trans hED
  refine ⟨Q, ?_, hQ.le, hzQ⟩
  have hQC : centralizer ({z} : Set X) ⊓ Q = S := by
    rw [inf_comm]
    exact hS.eq_of_le (le_inf hSQ (hS.le.trans inf_le_right)) (inf_le_inf_right _ hQ.le)
      hQp.to_inf_left
  have hEC : E ⊓ centralizer ({z} : Set X) = centralizer ({z} : Set X) ⊓ D := by
    ext x
    constructor
    · rintro ⟨hxE, hxC⟩
      exact ⟨hxC, hED hxE⟩
    · rintro ⟨hxC, hxD⟩
      have hcomm : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
      refine ⟨Subgroup.mem_inf.mpr ⟨hxD, mem_conjugate_iff.mpr ?_⟩, hxC⟩
      have e : z * x * z⁻¹ = x := by rw [← hcomm]; group
      rw [e]
      exact (Subgroup.mem_inf.mp hxD).2
  have hQcard := hQ.card_eq
  have hQodd : Odd (Nat.card Q) := by
    rw [hQcard]
    exact (hp.odd_of_ne_two hp2).pow
  have h1 := card_invertedSet_mul_card_inf_centralizer hQodd hz2 hzQ
  rw [hQC] at h1
  have hScard := hS.card_eq
  rw [hEC] at hScard
  have h2 := Subgroup.relIndex_mul_card (centralizer ({z} : Set X)) D
  rw [hr] at h2
  have hr0 : 0 < zNum Z M := by
    unfold zNum
    have := h.2.1.to_subtype
    exact Nat.card_pos
  have hfac : (Nat.card D).factorization p = (zNum Z M).factorization p +
      (Nat.card ↥(centralizer ({z} : Set X) ⊓ D)).factorization p := by
    rw [← h2, Nat.factorization_mul hr0.ne' Nat.card_pos.ne']
    rfl
  have hIQ : p ^ (zNum Z M).factorization p ≤ Nat.card (CFSG.OddInversion.invertedSet Q z) := by
    rw [← hcard]
    exact Nat.card_mono (Set.toFinite _) (CFSG.OddInversion.invertedSet_mono hPQ)
  rw [hScard] at h1
  have hlow : p ^ (Nat.card D).factorization p ≤ Nat.card Q := by
    rw [hfac, pow_add, ← h1]
    exact Nat.mul_le_mul_right _ hIQ
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hQp
  have hjdvd : p ^ j ∣ Nat.card D := by
    rw [← hj]
    exact Subgroup.card_dvd_of_le hQD
  have hjle : j ≤ (Nat.card D).factorization p :=
    (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hjdvd
  refine ABGLocalTools.isSylowOf_of_card hQD (le_antisymm ?_ hlow)
  rw [hj]
  exact Nat.pow_le_pow_right hp.pos hjle

theorem IsProductDisconnected.prop38c (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) {β : Subgroup X}
    (hβ : β ∈ omega M) (hβM : β ≠ M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    List.TFAE [
      ∃ Q : Subgroup X, ABGLocalTools.IsSylowOf p Q (M ⊓ β) ∧ z ∈ normalizer (Q : Set X),
      ∃ Q : Subgroup X, ABGLocalTools.IsSylowOf p Q (M ⊓ β) ∧ Q ≤ M ⊓ β ⊓ conjugate β z ∧
        z ∈ normalizer (Q : Set X),
      ∃ P : Subgroup X, P ≤ M ⊓ β ∧ IsPGroup p P ∧ z ∈ normalizer (P : Set X) ∧
        Nat.card (CFSG.OddInversion.invertedSet P z) = p ^ (zNum Z M).factorization p] := by
  tfae_have 1 → 2 := fun ⟨Q, hQ, hzQ⟩ => ⟨Q, hQ, prop38a hQ.le hzQ, hzQ⟩
  tfae_have 2 → 1 := fun ⟨Q, hQ, _, hzQ⟩ => ⟨Q, hQ, hzQ⟩
  tfae_have 1 → 3 := fun ⟨Q, hQ, hzQ⟩ => ⟨Q, hQ.le, hQ.isPGroup, hzQ,
    (h.prop38b hZ hz hzM hβ hβM hp hp2 hQ.le hQ.isPGroup hzQ).2 hQ⟩
  tfae_have 3 → 2 := fun ⟨P, hPD, hPp, hzP, hcard⟩ =>
    h.exists_invariant_sylow_of_card_eq hZ hz hzM hβ hβM hp hp2 hPD hPp hzP hcard
  tfae_finish

theorem IsProductDisconnected.prop38d_invertedSet (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t z : X} (ht : t ∈ Z) (htM : t ∉ M) (hz : z ∈ Z)
    (hzM : z ∈ M) :
    ((M ⊓ conjugate M t : Subgroup X) : Set X) =
      CFSG.OddInversion.invertedSet (pPrimeCoreIn (M ⊓ conjugate M t)) t *
        (((M ⊓ conjugate M t) ⊓ centralizer ({z} : Set X) : Subgroup X) : Set X) := by
  set D := M ⊓ conjugate M t with hD
  ext d
  rw [Set.mem_mul]
  constructor
  · intro hd
    have hdIC : d ∈ CFSG.OddInversion.invertedSet (pPrimeCoreIn D) t *
        ((centralizer ({z} : Set X) : Subgroup X) : Set X) := by
      rw [(h.prop36b hZ ht htM hz hzM).2]
      exact (Subgroup.mem_inf.mp hd).1
    rw [Set.mem_mul] at hdIC
    obtain ⟨x, hx, c, hc, rfl⟩ := hdIC
    have hcD : c ∈ D := by
      have := D.mul_mem (D.inv_mem (pPrimeCoreIn_le D hx.1)) hd
      simpa using this
    exact ⟨x, hx, c, Subgroup.mem_inf.mpr ⟨hcD, hc⟩, rfl⟩
  · rintro ⟨x, hx, c, hc, rfl⟩
    exact D.mul_mem (pPrimeCoreIn_le D hx.1) (Subgroup.mem_inf.mp hc).1

theorem IsProductDisconnected.prop38d (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) {β : Subgroup X}
    (hβ : β ∈ omega M) (hβM : β ≠ M) :
    ((M ⊓ β : Subgroup X) : Set X) =
        (pPrimeCoreIn (M ⊓ β) : Set X) *
          (((M ⊓ β) ⊓ centralizer ({z} : Set X) : Subgroup X) : Set X) ∧
      ∀ t ∈ Z, conjugate M t = β →
        ((M ⊓ β : Subgroup X) : Set X) =
          CFSG.OddInversion.invertedSet (pPrimeCoreIn (M ⊓ β)) t *
            (((M ⊓ β) ⊓ centralizer ({z} : Set X) : Subgroup X) : Set X) := by
  have key : ∀ t ∈ Z, conjugate M t = β →
      ((M ⊓ β : Subgroup X) : Set X) =
        CFSG.OddInversion.invertedSet (pPrimeCoreIn (M ⊓ β)) t *
          (((M ⊓ β) ⊓ centralizer ({z} : Set X) : Subgroup X) : Set X) := by
    rintro t ht rfl
    have htM : t ∉ M := fun htM => hβM ((h.conjugate_eq_iff_mem (self_mem_omega M)).mpr htM)
    exact h.prop38d_invertedSet hZ ht htM hz hzM
  refine ⟨?_, key⟩
  obtain ⟨t, ht, hβt⟩ := h.exists_swap hZ (self_mem_omega M) hβ
  have hD := key t ht hβt
  refine le_antisymm ?_ ?_
  · intro d hd
    rw [hD] at hd
    obtain ⟨x, hx, c, hc, rfl⟩ := Set.mem_mul.mp hd
    exact Set.mem_mul.mpr ⟨x, hx.1, c, hc, rfl⟩
  · intro d hd
    obtain ⟨x, hx, c, hc, rfl⟩ := Set.mem_mul.mp hd
    exact (M ⊓ β).mul_mem (pPrimeCoreIn_le _ hx) (Subgroup.mem_inf.mp hc).1

theorem IsProductDisconnected.lemma39_exists (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {β γ : Subgroup X} (hβ : β ∈ omega M) (hγ : γ ∈ omega M)
    (hβγ : β ≠ γ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ s ∈ Z, ∃ P : Subgroup X, conjugate β s = γ ∧ ABGLocalTools.IsSylowOf p P (β ⊓ γ) ∧
      s ∈ normalizer (P : Set X) := by
  obtain ⟨s, hs, hsγ⟩ := h.exists_swap hZ hβ hγ
  have hβs : conjugate β s ≠ β := fun heq => hβγ (heq.symm.trans hsγ)
  have hsW : s ∈ normalizer ((β ⊓ γ : Subgroup X) : Set X) := by
    rw [← hsγ]
    exact mem_normalizer_inf_conjugate (M := β) (hZ.mul_self_eq_one hs)
  have hbot : s ∈ normalizer ((⊥ : Subgroup X) : Set X) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top s
  obtain ⟨Q, hQ, -, hsQ⟩ := h.prop37a_omega hZ hs hβ hβs hp hp2 (W := β ⊓ γ) (P := ⊥)
    (by rw [← hsγ]) hsW bot_le IsPGroup.of_bot hbot
  exact ⟨s, hs, Q, hsγ, hQ, hsQ⟩

theorem IsProductDisconnected.lemma39_card (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {β γ : Subgroup X} (hβ : β ∈ omega M)
    (hβγ : β ≠ γ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {s : X} (hs : s ∈ Z)
    (hsγ : conjugate β s = γ) {P : Subgroup X} (hP : ABGLocalTools.IsSylowOf p P (β ⊓ γ))
    (hsP : s ∈ normalizer (P : Set X)) :
    Nat.card {y : X // y ∈ Z ∧ y * s⁻¹ ∈ P} = p ^ (zNum Z M).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  have hβs : conjugate β s ≠ β := fun heq => hβγ (heq.symm.trans hsγ)
  have hPodd : Odd (Nat.card P) := by
    rw [hP.card_eq]
    exact (hp.odd_of_ne_two hp2).pow
  rw [card_zCoset_eq_card_invertedSet hZ hs hPodd hsP]
  exact h.prop37d_omega hZ hs hβ hβs hp hp2 (by rw [hsγ]; exact hP) hsP

omit [Finite X] in
theorem eq_one_or_eq_of_mem_zpowers {t g : X} (ht : t * t = 1) (hg : g ∈ zpowers t) :
    g = 1 ∨ g = t := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' j
  · left
    rw [zpow_mul, ht2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, ht2, one_zpow, one_mul]

omit [Finite X] in
theorem zpowers_sup_commutator_eq_closure {K : Subgroup X} {t : X} (ht : t * t = 1) :
    zpowers t ⊔ ⁅zpowers t, K⁆ = Subgroup.closure {y : X | ∃ k ∈ K, y = k⁻¹ * t * k} := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have ht_mem : t ∈ Subgroup.closure {y : X | ∃ k ∈ K, y = k⁻¹ * t * k} :=
    Subgroup.subset_closure ⟨1, K.one_mem, by simp⟩
  apply le_antisymm
  · refine sup_le ((Subgroup.zpowers_le).mpr ht_mem) ?_
    rw [Subgroup.commutator_le]
    intro g hg k hk
    rcases eq_one_or_eq_of_mem_zpowers ht hg with hg1 | hgt
    · rw [hg1]
      simp
    · rw [hgt, commutatorElement_def]
      have e : t * k * t⁻¹ * k⁻¹ = t * (k * t⁻¹ * k⁻¹) := by group
      rw [e]
      exact mul_mem ht_mem (Subgroup.subset_closure ⟨k⁻¹, K.inv_mem hk, by rw [inv_inv, hti]⟩)
  · rw [Subgroup.closure_le]
    rintro y ⟨k, hk, rfl⟩
    have e : t⁻¹ * ⁅t, k⁻¹⁆ = k⁻¹ * t⁻¹ * k := by rw [commutatorElement_def]; group
    have e' : k⁻¹ * t * k = t⁻¹ * ⁅t, k⁻¹⁆ := by rw [e, hti]
    rw [SetLike.mem_coe, e']
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.mem_zpowers t)))
      (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers t)
        (K.inv_mem hk)))

@[expose] def lSubgroup (M : Subgroup X) (z t : X) : Subgroup X :=
  zpowers z ⊔ zpowers t ⊔ ⁅zpowers t, pPrimeCoreIn (M ⊓ conjugate M t)⁆

omit [Finite X] in
theorem lSubgroup_eq_sup_closure (M : Subgroup X) {t : X} (z : X) (ht : t * t = 1) :
    lSubgroup M z t = zpowers z ⊔
      Subgroup.closure {y : X | ∃ k ∈ pPrimeCoreIn (M ⊓ conjugate M t), y = k⁻¹ * t * k} := by
  rw [lSubgroup, sup_assoc, zpowers_sup_commutator_eq_closure ht]

theorem IsProductDisconnected.conj_mem_conjSet (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t : X} (ht : t ∈ Z) (htM : t ∉ M) {d : X}
    (hd : d ∈ M ⊓ conjugate M t) {y : X}
    (hy : y ∈ {y : X | ∃ k ∈ pPrimeCoreIn (M ⊓ conjugate M t), y = k⁻¹ * t * k}) :
    d⁻¹ * y * d ∈ {y : X | ∃ k ∈ pPrimeCoreIn (M ⊓ conjugate M t), y = k⁻¹ * t * k} := by
  obtain ⟨k, hk, rfl⟩ := hy
  obtain ⟨a, ha, c, hc, hdc⟩ := h.exists_mul_centralizer_inf_conjugate hZ ht htM
    ((M ⊓ conjugate M t).inv_mem hd)
  have hcD : c ∈ M ⊓ conjugate M t := (Subgroup.mem_inf.mp hc).1
  have hct : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
  have hk1 : c * k * c⁻¹ ∈ pPrimeCoreIn (M ⊓ conjugate M t) :=
    (Subgroup.mem_normalizer_iff.mp (pPrimeCoreIn_normalizes _ hcD) k).mp hk
  refine ⟨(c * k * c⁻¹) * a⁻¹, (pPrimeCoreIn (M ⊓ conjugate M t)).mul_mem hk1
    ((pPrimeCoreIn (M ⊓ conjugate M t)).inv_mem ha), ?_⟩
  have hd' : d = (a * c)⁻¹ := by rw [← hdc, inv_inv]
  have e : c * t * c⁻¹ = t := by rw [hct]; group
  rw [hd']
  calc ((a * c)⁻¹)⁻¹ * (k⁻¹ * t * k) * (a * c)⁻¹
      = a * (c * k⁻¹ * c⁻¹) * (c * t * c⁻¹) * (c * k * c⁻¹) * a⁻¹ := by group
    _ = a * (c * k⁻¹ * c⁻¹) * t * (c * k * c⁻¹) * a⁻¹ := by rw [e]
    _ = ((c * k * c⁻¹) * a⁻¹)⁻¹ * t * ((c * k * c⁻¹) * a⁻¹) := by group

theorem IsProductDisconnected.le_normalizer_closure_conjSet (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t : X} (ht : t ∈ Z) (htM : t ∉ M) :
    M ⊓ conjugate M t ≤ normalizer ((Subgroup.closure
      {y : X | ∃ k ∈ pPrimeCoreIn (M ⊓ conjugate M t), y = k⁻¹ * t * k} : Subgroup X) : Set X) := by
  set T := {y : X | ∃ k ∈ pPrimeCoreIn (M ⊓ conjugate M t), y = k⁻¹ * t * k} with hT
  have hmap : ∀ d ∈ M ⊓ conjugate M t, ∀ x ∈ Subgroup.closure T,
      d⁻¹ * x * d ∈ Subgroup.closure T := by
    intro d hd x hx
    have : Subgroup.closure T ≤ (Subgroup.closure T).comap (MulAut.conj d⁻¹).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have e : (MulAut.conj d⁻¹).toMonoidHom y = d⁻¹ * y * d := by simp
      rw [e]
      exact Subgroup.subset_closure (h.conj_mem_conjSet hZ ht htM hd hy)
    simpa [MulAut.conj_apply] using this hx
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := hmap d⁻¹ ((M ⊓ conjugate M t).inv_mem hd) x hx
    simpa using this
  · intro hx
    have := hmap d hd _ hx
    simpa [mul_assoc] using this

omit [Finite X] in
theorem IsProductDisconnected.zHull_lSubgroup (hZ : IsInvariantInvolutionSet Z) {t z : X}
    (ht : t ∈ Z) (hz : z ∈ Z) (M : Subgroup X) :
    zHull Z (lSubgroup M z t) = lSubgroup M z t := by
  have ht2 : t * t = 1 := hZ.mul_self_eq_one ht
  apply le_antisymm
  · exact (Subgroup.closure_le _).mpr Set.inter_subset_right
  · rw [lSubgroup_eq_sup_closure M z ht2]
    set T := {y : X | ∃ k ∈ pPrimeCoreIn (M ⊓ conjugate M t), y = k⁻¹ * t * k} with hT
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure ⟨hz, Subgroup.mem_sup_left (Subgroup.mem_zpowers z)⟩
    · rw [Subgroup.closure_le]
      intro y hy
      obtain ⟨k, hk, rfl⟩ := hy
      refine Subgroup.subset_closure ⟨hZ.2 t ht k, ?_⟩
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨k, hk, rfl⟩)

theorem IsProductDisconnected.inter_le_lSubgroup (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t z : X} (ht : t ∈ Z) (htM : t ∉ M) (hz : z ∈ Z)
    (hzM : z ∈ M) : Z ∩ (M : Set X) ⊆ (lSubgroup M z t : Set X) := by
  have ht2 : t * t = 1 := hZ.mul_self_eq_one ht
  have hIL : ∀ x ∈ CFSG.OddInversion.invertedSet (pPrimeCoreIn (M ⊓ conjugate M t)) t,
      x ∈ lSubgroup M z t := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := CFSG.OddInversion.exists_sq_eq_of_mem_invertedSet
      (odd_card_pPrimeCoreIn (M ⊓ conjugate M t)) hx
    have hcomm : ⁅t, d⁻¹⁆ = d ^ 2 := by
      calc ⁅t, d⁻¹⁆ = (t * d * t⁻¹)⁻¹ * d := by rw [commutatorElement_def]; group
        _ = d ^ 2 := by rw [hd.2, inv_inv, sq]
    rw [← hcomm]
    exact Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers t)
      ((pPrimeCoreIn (M ⊓ conjugate M t)).inv_mem hd.1))
  intro y hy
  obtain ⟨x, hx, hxy⟩ := ((h.prop36c hZ ht htM).1 z ⟨hz, hzM⟩).surjOn hy
  rw [SetLike.mem_coe, ← hxy]
  have hzL : z ∈ lSubgroup M z t :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  exact mul_mem (mul_mem (inv_mem (hIL x hx)) hzL) (hIL x hx)

theorem IsProductDisconnected.le_normalizer_lSubgroup (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t z : X} (ht : t ∈ Z) (htM : t ∉ M) (hz : z ∈ Z)
    (hzM : z ∈ M) : M ⊓ conjugate M t ≤ normalizer (lSubgroup M z t : Set X) := by
  have ht2 : t * t = 1 := hZ.mul_self_eq_one ht
  set D := M ⊓ conjugate M t with hD
  set T := {y : X | ∃ k ∈ pPrimeCoreIn D, y = k⁻¹ * t * k} with hT
  have hL := lSubgroup_eq_sup_closure M z ht2
  have hIL : ∀ x ∈ CFSG.OddInversion.invertedSet (pPrimeCoreIn D) t, x ∈ lSubgroup M z t := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := CFSG.OddInversion.exists_sq_eq_of_mem_invertedSet
      (odd_card_pPrimeCoreIn D) hx
    have hcomm : ⁅t, d⁻¹⁆ = d ^ 2 := by
      calc ⁅t, d⁻¹⁆ = (t * d * t⁻¹)⁻¹ * d := by rw [commutatorElement_def]; group
        _ = d ^ 2 := by rw [hd.2, inv_inv, sq]
    rw [← hcomm]
    exact Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers t)
      ((pPrimeCoreIn D).inv_mem hd.1))
  have hcN : ∀ c ∈ D ⊓ centralizer ({z} : Set X), c ∈ normalizer (lSubgroup M z t : Set X) := by
    have hmap : ∀ c ∈ D ⊓ centralizer ({z} : Set X), ∀ x ∈ lSubgroup M z t,
        c⁻¹ * x * c ∈ lSubgroup M z t := by
      intro c hc x hx
      have hcD : c ∈ D := (Subgroup.mem_inf.mp hc).1
      have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp
        (Subgroup.mem_inf.mp hc).2
      have hczz : c⁻¹ * z * c = z := by rw [mul_assoc, ← hcz]; group
      have : lSubgroup M z t ≤ (lSubgroup M z t).comap (MulAut.conj c⁻¹).toMonoidHom := by
        rw [hL]
        refine sup_le ?_ ?_
        · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hczz]
          exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
        · rw [Subgroup.closure_le]
          intro y hy
          rw [SetLike.mem_coe, Subgroup.mem_comap]
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          exact Subgroup.mem_sup_right (Subgroup.subset_closure
            (h.conj_mem_conjSet hZ ht htM hcD hy))
      simpa [MulAut.conj_apply] using this hx
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have := hmap c⁻¹ ((D ⊓ centralizer ({z} : Set X)).inv_mem hc) x hx
      simpa using this
    · intro hx
      have := hmap c hc _ hx
      simpa [mul_assoc] using this
  intro d hd
  have hd' : d ∈ CFSG.OddInversion.invertedSet (pPrimeCoreIn D) t *
      (((D ⊓ centralizer ({z} : Set X) : Subgroup X)) : Set X) := by
    rw [← h.prop38d_invertedSet hZ ht htM hz hzM]
    exact hd
  obtain ⟨x, hx, c, hc, rfl⟩ := Set.mem_mul.mp hd'
  exact mul_mem (Subgroup.le_normalizer (hIL x hx)) (hcN c hc)

end Prop38

end CFSG.GH74.Uniqueness

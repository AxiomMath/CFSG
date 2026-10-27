module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenTransport
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseOpen

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv

section SecConj

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_centralizer_of {R R' : Subgroup G} {g : G}
    (hR : ∀ x, x ∈ R ↔ g * x * g⁻¹ ∈ R') {x : G} (hx : x ∈ centralizer (R : Set G)) :
    g * x * g⁻¹ ∈ centralizer (R' : Set G) := by
  rw [mem_centralizer_iff] at hx ⊢
  intro r' hr'
  have hr : g⁻¹ * r' * g ∈ R := by
    rw [hR]
    have : g * (g⁻¹ * r' * g) * g⁻¹ = r' := by group
    rw [this]; exact hr'
  have := hx _ hr
  calc r' * (g * x * g⁻¹) = g * ((g⁻¹ * r' * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * r' * g)) * g⁻¹ := by rw [this]
    _ = g * x * g⁻¹ * r' := by group

@[expose] noncomputable def centralizerConj {R R' : Subgroup G} (g : G)
    (hR : ∀ x, x ∈ R ↔ g * x * g⁻¹ ∈ R') :
    ↥(centralizer (R : Set G)) ≃* ↥(centralizer (R' : Set G)) where
  toFun x := ⟨g * (x : G) * g⁻¹, conj_mem_centralizer_of hR x.2⟩
  invFun y := ⟨g⁻¹ * (y : G) * g, by
    have h1 : ∀ x, x ∈ R' ↔ g⁻¹ * x * g ∈ R := fun x => by
      rw [hR]; simp [mul_assoc]
    have := conj_mem_centralizer_of (R := R') (R' := R) (g := g⁻¹) (by
      intro x
      rw [h1 x]; simp [mul_assoc]) y.2
    simpa [mul_assoc] using this⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

@[expose] noncomputable def secConj {R R' : Subgroup G} (g : G) (hR : ∀ x, x ∈ R ↔ g * x * g⁻¹ ∈ R') :
    Sec G R ≃* Sec G R' :=
  QuotientGroup.congr _ _ (centralizerConj g hR)
    (ClassicalInvolution.QuaternionStructure.oddCore_map_mulEquiv (centralizerConj g hR))

theorem secConj_mk {R R' : Subgroup G} (g : G) (hR : ∀ x, x ∈ R ↔ g * x * g⁻¹ ∈ R')
    (x : ↥(centralizer (R : Set G))) :
    secConj g hR (QuotientGroup.mk x) = QuotientGroup.mk (centralizerConj g hR x) := rfl

end SecConj

section Defs

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ}

@[expose] def CaseIAt (e : L ≃* alternatingGroup (Fin n)) (z : G) (S : Finset (Fin n)) : Prop :=
  ∃ ht : z ∈ centralizer (corr (X := G) e (altSub S) : Set G),
    (QuotientGroup.mk ⟨z, ht⟩ : Sec G (corr (X := G) e (altSub S))) ∈
      Subgroup.center (Sec G (corr (X := G) e (altSub S)))

@[expose] def CaseIIAt (e : L ≃* alternatingGroup (Fin n)) (z : G) (S : Finset (Fin n)) : Prop :=
  ∃ ht : z ∈ centralizer (corr (X := G) e (altSub S) : Set G),
    SymOutcome (QuotientGroup.mk ⟨z, ht⟩ : Sec G (corr (X := G) e (altSub S))) (n - S.card)

theorem SymOutcome.map' {X X' : Type} [Group X] [Group X'] (Φ : X ≃* X') {t : X} {m : ℕ}
    (h : SymOutcome t m) : SymOutcome (Φ t) m := by
  obtain ⟨ε, hε⟩ := h
  refine ⟨ε.trans Φ, ?_⟩
  simpa using hε

end Defs

section Transport

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {z : G}

theorem exists_secEquiv_of_card_eq (h : ExactShape z L n) (e : L ≃* alternatingGroup (Fin n))
    {S S' : Finset (Fin n)} (hS : S.card = S'.card) (hSc : 2 ≤ Sᶜ.card) :
    ∃ (ht : z ∈ centralizer (corr (X := G) e (altSub S) : Set G))
      (ht' : z ∈ centralizer (corr (X := G) e (altSub S') : Set G))
      (Φ : Sec G (corr (X := G) e (altSub S)) ≃* Sec G (corr (X := G) e (altSub S'))),
      Φ (QuotientGroup.mk ⟨z, ht⟩) = QuotientGroup.mk ⟨z, ht'⟩ := by
  have ht : z ∈ centralizer (corr (X := G) e (altSub S) : Set G) :=
    t_mem_centralizer_corr (X := G) e h (altSub S)
  have ht' : z ∈ centralizer (corr (X := G) e (altSub S') : Set G) :=
    t_mem_centralizer_corr (X := G) e h (altSub S')
  obtain ⟨π, hsign, hπ⟩ := exists_even_perm_of_card_eq hS hSc
  have hπA : π ∈ alternatingGroup (Fin n) := Perm.mem_alternatingGroup.2 hsign
  set lg : G := ((e.symm ⟨π, hπA⟩ : L) : G) with hlg
  have hlgL : lg ∈ L := (e.symm ⟨π, hπA⟩ : L).2
  have hlz : lg * z * lg⁻¹ = z := by
    have := mem_centralizer_singleton_iff.1 (h.le_cent hlgL)
    rw [this]; group
  have hRS := corr_conj_iff (G := G) e hπA hπ
  refine ⟨ht, ht', secConj lg hRS, ?_⟩
  rw [secConj_mk]
  congr 1
  exact Subtype.ext hlz

theorem caseIAt_transport (h : ExactShape z L n) (e : L ≃* alternatingGroup (Fin n))
    {S S' : Finset (Fin n)} (hS : S.card = S'.card) (hSc : 2 ≤ Sᶜ.card) (hI : CaseIAt e z S) :
    CaseIAt e z S' := by
  obtain ⟨ht0, hc⟩ := hI
  obtain ⟨ht, ht', Φ, hΦ⟩ := exists_secEquiv_of_card_eq h e hS hSc
  refine ⟨ht', ?_⟩
  rw [← hΦ, Subgroup.mem_center_iff]
  intro y
  obtain ⟨y', rfl⟩ := Φ.surjective y
  have hc' := Subgroup.mem_center_iff.1 hc y'
  rw [← map_mul, ← map_mul, hc']

theorem caseIIAt_transport (h : ExactShape z L n) (e : L ≃* alternatingGroup (Fin n))
    {S S' : Finset (Fin n)} (hS : S.card = S'.card) (hSc : 2 ≤ Sᶜ.card) (hII : CaseIIAt e z S) :
    CaseIIAt e z S' := by
  obtain ⟨ht0, hs⟩ := hII
  obtain ⟨ht, ht', Φ, hΦ⟩ := exists_secEquiv_of_card_eq h e hS hSc
  refine ⟨ht', ?_⟩
  have := SymOutcome.map' Φ hs
  rw [hΦ] at this
  rw [← hS]
  exact this

end Transport

section ConjSec

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {z : G}

theorem exists_secEquiv_of_conj (e : L ≃* alternatingGroup (Fin n)) {S S₁ : Finset (Fin n)}
    {g a : G} (hrS : rootGroup (G := G) e S = conjSub g (rootGroup e S₁)) (hg : g * z * g⁻¹ = a)
    (hz : z ∈ centralizer (corr (X := G) e (altSub S₁) : Set G))
    (ha : a ∈ centralizer (corr (X := G) e (altSub S) : Set G)) :
    ∃ Φ : Sec G (corr (X := G) e (altSub S₁)) ≃* Sec G (corr (X := G) e (altSub S)),
      Φ (QuotientGroup.mk ⟨z, hz⟩) = QuotientGroup.mk ⟨a, ha⟩ := by
  have hR : ∀ x, x ∈ corr (X := G) e (altSub S₁) ↔
      g * x * g⁻¹ ∈ corr (X := G) e (altSub S) := by
    intro x
    have h1 : g * x * g⁻¹ ∈ rootGroup (G := G) e S ↔ x ∈ rootGroup (G := G) e S₁ := by
      rw [hrS, mem_conjSub_iff]
      simp [mul_assoc]
    exact h1.symm
  refine ⟨secConj g hR, ?_⟩
  rw [secConj_mk]
  congr 1
  exact Subtype.ext hg

end ConjSec

end CFSG.OddStandard.AltStdSec

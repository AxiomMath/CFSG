module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreBasic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsShape

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup

variable {A : Type} [Group A]

abbrev PairCaseOne (R D : Subgroup A) : Prop :=
  ∀ c ∈ R, (∀ d ∈ D, c * d = d * c) → c ∈ D

abbrev PairCaseTwo (R D : Subgroup A) (k : A) : Prop :=
  k ∈ R ∧ (∀ d ∈ D, k * d = d * k) ∧ k ∉ D ∧ k ^ 2 = 1 ∧ 8 ≤ Nat.card D ∧
    ∀ c ∈ R, (∀ d ∈ D, c * d = d * c) → c ∈ D ∨ c * k ∈ D

structure AutPair (R D : Subgroup A) : Prop where
  gen3 : ∀ R' : Subgroup A, R' ≤ R →
    ∃ s : Finset A, s.card ≤ 3 ∧ closure (s : Set A) = R'
  dichotomy : PairCaseOne R D ∨ ∃ k, PairCaseTwo R D k
  index_one : PairCaseOne R D → ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ ∉ D → r₂ ∉ D → r₁ * r₂⁻¹ ∈ D
  klein_one : PairCaseOne R D → ∀ E : Subgroup A, E ≤ D → Nat.card E = 4 →
    (∀ e ∈ E, e ^ 2 = 1) → ∀ c ∈ R, (∀ e ∈ E, c * e = e * c) → c ∈ D
  inv_one : PairCaseOne R D → ∀ σ ∈ R, σ ∉ D → σ ^ 2 = 1 →
    Nat.card ↥(D ⊓ centralizer ({σ} : Set A)) ≤ 2
  two : ∀ k, PairCaseTwo R D k → ∃ Tbar : Subgroup A, Tbar ≤ R ∧ D ≤ Tbar ∧
    (∀ r ∈ R, r ^ 2 = 1 → r ∈ Tbar ∨ r * k ∈ D) ∧
    (∀ δ ∈ Tbar, δ ∉ D → δ * k ≠ k * δ) ∧
    (Nat.card D = 8 → ∀ r ∈ R, r ∈ Tbar ∨ r * k ∈ Tbar) ∧
    (Tbar ≠ D → ∃ m : ℕ, Nonempty (↥Tbar ≃* DihedralGroup m))

namespace AutPair

variable {A' : Type} [Group A'] (Φ : A ≃* A')

theorem memΦ {K : Subgroup A} {x : A} : Φ x ∈ K.map Φ.toMonoidHom ↔ x ∈ K := by
  rw [mem_map_equiv, MulEquiv.symm_apply_apply]

theorem commΦ {K : Subgroup A} {c : A} :
    (∀ d ∈ K, c * d = d * c) ↔ ∀ d' ∈ K.map Φ.toMonoidHom, Φ c * d' = d' * Φ c := by
  constructor
  · rintro h _ ⟨d, hd, rfl⟩
    change Φ c * Φ d = Φ d * Φ c
    rw [← map_mul, ← map_mul, h d hd]
  · intro h d hd
    apply Φ.injective
    rw [map_mul, map_mul]
    exact h _ ((memΦ Φ).mpr hd)

theorem caseOne_iff {R D : Subgroup A} :
    PairCaseOne R D ↔ PairCaseOne (R.map Φ.toMonoidHom) (D.map Φ.toMonoidHom) := by
  constructor
  · intro h c' hc' hcD
    obtain ⟨c, hc, rfl⟩ := hc'
    exact (memΦ Φ).mpr (h c hc ((commΦ Φ).mpr hcD))
  · intro h c hc hcD
    exact (memΦ Φ).mp (h _ ((memΦ Φ).mpr hc) ((commΦ Φ).mp hcD))

theorem caseTwo_iff {R D : Subgroup A} {k : A} :
    PairCaseTwo R D k ↔ PairCaseTwo (R.map Φ.toMonoidHom) (D.map Φ.toMonoidHom) (Φ k) := by
  rw [PairCaseTwo, PairCaseTwo, memΦ, memΦ, commΦ Φ, card_map_of_injective Φ.injective]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr ?_ (and_congr_right fun _ => ?_)
  · rw [← map_pow, ← map_one Φ, Φ.injective.eq_iff]
  · constructor
    · intro h c' hc' hcD
      obtain ⟨c, hc, rfl⟩ := hc'
      rcases h c hc ((commΦ Φ).mpr hcD) with h' | h'
      · exact Or.inl ((memΦ Φ).mpr h')
      · right
        have := (memΦ Φ (K := D)).mpr h'
        rwa [map_mul] at this
    · intro h c hc hcD
      rcases h _ ((memΦ Φ).mpr hc) ((commΦ Φ).mp hcD) with h' | h'
      · exact Or.inl ((memΦ Φ).mp h')
      · right; rw [← map_mul] at h'; exact (memΦ Φ).mp h'

theorem of_map {R D : Subgroup A} (h : AutPair (R.map Φ.toMonoidHom) (D.map Φ.toMonoidHom)) :
    AutPair R D where
  gen3 R' hR' := by
    classical
    obtain ⟨s, hs, hcl⟩ := h.gen3 (R'.map Φ.toMonoidHom) (map_mono hR')
    refine ⟨s.image Φ.symm, Finset.card_image_le.trans hs, ?_⟩
    rw [Finset.coe_image]
    have := MonoidHom.map_closure Φ.symm.toMonoidHom (s : Set A')
    rw [hcl] at this
    rw [show (Φ.symm '' (s : Set A')) = Φ.symm.toMonoidHom '' (s : Set A') from rfl, ← this]
    ext x
    simp
  dichotomy := by
    rcases h.dichotomy with h1 | ⟨k', hk'⟩
    · exact Or.inl ((caseOne_iff Φ).mpr h1)
    · right
      refine ⟨Φ.symm k', (caseTwo_iff Φ).mpr ?_⟩
      rwa [MulEquiv.apply_symm_apply]
  index_one h1 r₁ hr₁ r₂ hr₂ hn₁ hn₂ := by
    have := h.index_one ((caseOne_iff Φ).mp h1) _ ((memΦ Φ).mpr hr₁) _ ((memΦ Φ).mpr hr₂)
      (fun h' => hn₁ ((memΦ Φ).mp h')) (fun h' => hn₂ ((memΦ Φ).mp h'))
    rwa [← map_inv, ← map_mul, memΦ] at this
  klein_one h1 E hED hE4 hEsq c hc hcE := by
    refine (memΦ Φ).mp (h.klein_one ((caseOne_iff Φ).mp h1) (E.map Φ.toMonoidHom) (map_mono hED)
      (by rw [card_map_of_injective Φ.injective, hE4]) ?_ _ ((memΦ Φ).mpr hc)
      ((commΦ Φ).mp hcE))
    rintro _ ⟨e, he, rfl⟩
    change Φ e ^ 2 = 1
    rw [← map_pow, hEsq e he, map_one]
  inv_one h1 σ hσ hσD hσ2 := by
    have := h.inv_one ((caseOne_iff Φ).mp h1) _ ((memΦ Φ).mpr hσ) (fun h' => hσD ((memΦ Φ).mp h'))
      (by rw [← map_pow, hσ2, map_one])
    have heq : (D.map Φ.toMonoidHom ⊓ centralizer ({Φ σ} : Set A')) =
        (D ⊓ centralizer ({σ} : Set A)).map Φ.toMonoidHom := by
      rw [AutL2Facts.map_inf_mulEquiv, AutL2Facts.map_centralizer_singleton]
    rwa [heq, card_map_of_injective Φ.injective] at this
  two k hk := by
    obtain ⟨Tb, hTR, hDT, hinv, hnc, h8, hdih⟩ := h.two (Φ k) ((caseTwo_iff Φ).mp hk)
    refine ⟨Tb.map Φ.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rw [mem_map_equiv, MulEquiv.symm_symm] at hx
      exact (memΦ Φ).mp (hTR hx)
    · intro x hx
      rw [mem_map_equiv, MulEquiv.symm_symm]
      exact hDT ((memΦ Φ).mpr hx)
    · intro r hr hr2
      rw [mem_map_equiv, MulEquiv.symm_symm]
      rcases hinv _ ((memΦ Φ).mpr hr) (by rw [← map_pow, hr2, map_one]) with h' | h'
      · exact Or.inl h'
      · right; rw [← map_mul] at h'; exact (memΦ Φ).mp h'
    · intro δ hδ hδD hc
      rw [mem_map_equiv, MulEquiv.symm_symm] at hδ
      exact hnc _ hδ (fun h' => hδD ((memΦ Φ).mp h')) (by rw [← map_mul, ← map_mul, hc])
    · intro hD8 r hr
      rcases h8 (by rw [card_map_of_injective Φ.injective, hD8]) _ ((memΦ Φ).mpr hr) with
        h' | h'
      · left; rw [mem_map_equiv, MulEquiv.symm_symm]; exact h'
      · right; rw [mem_map_equiv, MulEquiv.symm_symm, map_mul]; exact h'
    · intro hne
      have hne' : Tb ≠ D.map Φ.toMonoidHom := fun h' => hne (by
        rw [h']
        ext x
        simp)
      obtain ⟨m, ⟨e⟩⟩ := hdih hne'
      exact ⟨m, ⟨(Tb.equivMapOfInjective Φ.symm.toMonoidHom Φ.symm.injective).symm.trans e⟩⟩

end AutPair

namespace LocalDatum

variable {X : Type} [Group X] (Δ : LocalDatum X A)

theorem autFacts_of_autPair (h : AutPair Δ.R Δ.Dbar) : AutFacts Δ := by
  have hcard := Δ.card_Dbar
  have h2 : ∀ k, Δ.CaseTwo k ↔ PairCaseTwo Δ.R Δ.Dbar k := fun k => by
    rw [LocalDatum.CaseTwo, PairCaseTwo, hcard]
  refine ⟨h.gen3, ?_, h.index_one, h.klein_one, h.inv_one, fun k hk => ?_⟩
  · rcases h.dichotomy with h1 | ⟨k, hk⟩
    · exact Or.inl h1
    · exact Or.inr ⟨k, (h2 k).mpr hk⟩
  · obtain ⟨Tb, h1, h2', h3, h4, h5, h6⟩ := h.two k ((h2 k).mp hk)
    exact ⟨Tb, h1, h2', h3, h4, fun h8 => h5 (by rw [hcard]; exact h8), h6⟩

end LocalDatum

end CFSG.ComponentClassification.HSDihedral

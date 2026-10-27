module

public import CFSG.GH74.GLS.Stage2.Final.L26.G2Three
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.GH74.GLS.Stage2.Final.L26.Core

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open CFSG.GH74.GLS.Stage2.Final.L26 (card_eq_of_hasSL2Model_three alternatingGroup_le_of_pow_three
  mem_of_pow_three_of_index_two)

section S4

theorem perm4_even_sq :
    ∀ σ : Equiv.Perm (Fin 4), Equiv.Perm.sign σ = 1 → σ ^ 4 = 1 → σ ^ 2 = 1 := by
  decide +kernel

theorem perm4_card_inv :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 4) => Equiv.Perm.sign σ = 1 ∧ σ ^ 2 = 1)).card =
      4 := by
  decide +kernel

theorem perm4_centralizer : ∀ τ : Equiv.Perm (Fin 4),
    (∀ σ : Equiv.Perm (Fin 4), Equiv.Perm.sign σ = 1 → σ ^ 2 = 1 → τ * σ = σ * τ) →
      Equiv.Perm.sign τ = 1 ∧ τ ^ 2 = 1 := by
  decide +kernel

end S4

section Theta

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem exists_theta {L SB : Subgroup Y} (hL : HasSL2Model ↥L (fun q => q = 3))
    (hind : InducedPGL2 L SB 3) :
    ∃ Θ : ↥(L ⊔ SB) →* Equiv.Perm (Fin 4), Function.Surjective Θ ∧
      (∀ m : ↥(L ⊔ SB), Θ m = 1 ↔ (m : Y) ∈ centralizer (L : Set Y)) ∧
      (∀ m : ↥(L ⊔ SB), Equiv.Perm.sign (Θ m) = 1 ↔
        ∃ a ∈ L, ∃ c ∈ centralizer (L : Set Y), (m : Y) = a * c) := by
  obtain ⟨hn, F₀, hF₀, hFin₀, hcard₀, ⟨e⟩⟩ := hind
  have hF3 : Nat.card F₀ = 3 := hcard₀
  have : Fintype F₀ := Fintype.ofFinite F₀
  have hcardF : Fintype.card F₀ = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hF3, ZMod.card]
  let φ : F₀ ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hcardF
  let ε : ↥(L ⊔ SB) ⧸ (centralizer (L : Set Y)).subgroupOf (L ⊔ SB) ≃* Equiv.Perm (Fin 4) :=
    (e.trans (GorensteinWalter.pgl2RingEquiv φ)).trans GorensteinWalter.pgl2_three_equiv_perm
  let C' : Subgroup ↥(L ⊔ SB) := (centralizer (L : Set Y)).subgroupOf (L ⊔ SB)
  let Θ : ↥(L ⊔ SB) →* Equiv.Perm (Fin 4) := ε.toMonoidHom.comp (QuotientGroup.mk' C')
  have hΘs : Function.Surjective Θ := ε.surjective.comp (QuotientGroup.mk'_surjective C')
  have hΘone : ∀ m : ↥(L ⊔ SB), Θ m = 1 ↔ m ∈ C' := by
    intro m
    show ε (QuotientGroup.mk m) = 1 ↔ _
    rw [map_eq_one_iff ε ε.injective, QuotientGroup.eq_one_iff]
  have hLM : L ≤ L ⊔ SB := le_sup_left
  let g : ↥L →* Equiv.Perm (Fin 4) := Θ.comp (Subgroup.inclusion hLM)
  have hgone : ∀ a : ↥L, g a = 1 ↔ a ∈ center ↥L := by
    intro a
    show Θ (Subgroup.inclusion hLM a) = 1 ↔ _
    rw [hΘone, Subgroup.mem_subgroupOf, Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h g'
      exact Subtype.ext (h g' g'.2)
    · intro h g' hg'
      exact congrArg Subtype.val (h ⟨g', hg'⟩)
  have hgker : g.ker = center ↥L := by
    ext a
    rw [MonoidHom.mem_ker]
    exact hgone a
  have hLcard : Nat.card ↥L = 24 := card_eq_of_hasSL2Model_three hL
  have hZ : Nat.card (center ↥L) = 2 := (sl2_model_center_inv ⟨1, rfl⟩ hL).1
  have hrange : Nat.card g.range = 12 := by
    have h1 := Subgroup.index_ker g
    have h2 := g.ker.index_mul_card
    rw [h1] at h2
    have h3 : Nat.card g.ker = 2 := by rw [hgker, hZ]
    rw [h3, hLcard] at h2
    omega
  have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hidx : g.range.index = 2 := by
    have := g.range.index_mul_card
    rw [hrange, hperm] at this
    omega
  have hA : alternatingGroup (Fin 4) ≤ g.range :=
    alternatingGroup_le_of_pow_three fun σ hσ => mem_of_pow_three_of_index_two hidx hσ
  have hAcard : Nat.card (alternatingGroup (Fin 4)) = 12 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    rfl
  have hrA : g.range = alternatingGroup (Fin 4) :=
    (Subgroup.eq_of_le_of_card_ge hA (by rw [hrange, hAcard])).symm
  refine ⟨Θ, hΘs, fun m => (hΘone m).trans (Subgroup.mem_subgroupOf), fun m => ?_⟩
  constructor
  · intro hsign
    have hmem : Θ m ∈ g.range := by
      rw [hrA]
      exact Equiv.Perm.mem_alternatingGroup.2 hsign
    obtain ⟨a, ha⟩ := hmem
    have h1 : (Subgroup.inclusion hLM a)⁻¹ * m ∈ C' := (hΘone _).1 (by
      rw [map_mul, map_inv, inv_mul_eq_one]
      exact ha)
    refine ⟨a, a.2, (a : Y)⁻¹ * m, ?_, by group⟩
    simpa using Subgroup.mem_subgroupOf.mp h1
  · rintro ⟨a, ha, c, hc, hmac⟩
    have hmem : Θ m ∈ g.range := by
      refine ⟨⟨a, ha⟩, ?_⟩
      have hcH : (c : Y) ∈ L ⊔ SB := by
        have : c = a⁻¹ * (m : Y) := by rw [hmac]; group
        rw [this]
        exact mul_mem (inv_mem (hLM ha)) m.2
      have hcC : (⟨c, hcH⟩ : ↥(L ⊔ SB)) ∈ C' := Subgroup.mem_subgroupOf.2 hc
      have h1 : Θ ⟨c, hcH⟩ = 1 := (hΘone _).2 hcC
      have hmeq : m = Subgroup.inclusion hLM ⟨a, ha⟩ * ⟨c, hcH⟩ := Subtype.ext hmac
      show Θ (Subgroup.inclusion hLM ⟨a, ha⟩) = Θ m
      rw [hmeq, map_mul, h1, mul_one]
    rw [hrA] at hmem
    exact Equiv.Perm.mem_alternatingGroup.1 hmem

omit [Finite Y] in
theorem exists_outer_of_inducedPGL2 {L SB : Subgroup Y} (hL : HasSL2Model ↥L (fun q => q = 3))
    (hind : InducedPGL2 L SB 3) :
    ∃ s ∈ SB, ¬ ∃ a ∈ L, ∃ c ∈ centralizer (L : Set Y), s = a * c := by
  by_contra hcon
  push Not at hcon
  obtain ⟨Θ, hΘs, -, hΘsign⟩ := exists_theta hL hind
  have hLC : ∀ a ∈ L, ∀ c ∈ centralizer (L : Set Y), a * c = c * a := fun a ha c hc =>
    mem_centralizer_iff.1 hc a ha
  have hle : L ⊔ SB ≤ L ⊔ centralizer (L : Set Y) := by
    refine sup_le le_sup_left fun s hs => ?_
    obtain ⟨a, ha, c, hc, rfl⟩ := hcon s hs
    exact mul_mem (mem_sup_left ha) (mem_sup_right hc)
  obtain ⟨m, hm⟩ := hΘs (Equiv.swap 0 1)
  obtain ⟨a, ha, c, hc, hmac⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hLC (hle m.2)
  have h1 := (hΘsign m).2 ⟨a, ha, c, hc, hmac.symm⟩
  rw [hm, Equiv.Perm.sign_swap (by decide)] at h1
  exact absurd h1 (by decide)

theorem exists_mul_centralizer_of_commutes {L SB W' : Subgroup Y}
    (hL : HasSL2Model ↥L (fun q => q = 3)) (hind : InducedPGL2 L SB 3) (hWL : W' ≤ L)
    (hW8 : Nat.card ↥W' = 8) (hW4 : ∀ w ∈ W', w ^ 4 = 1) {x : Y} (hx : x ∈ L ⊔ SB)
    (hcomm : ∀ w ∈ W', x * w * x⁻¹ * w⁻¹ ∈ centralizer (L : Set Y)) :
    ∃ w ∈ W', w⁻¹ * x ∈ centralizer (L : Set Y) := by
  classical
  obtain ⟨Θ, hΘs, hΘone, hΘsign⟩ := exists_theta hL hind
  have hWH : W' ≤ L ⊔ SB := hWL.trans le_sup_left
  let θ : ↥W' →* Equiv.Perm (Fin 4) := Θ.comp (Subgroup.inclusion hWH)
  let T4 : Finset (Equiv.Perm (Fin 4)) :=
    Finset.univ.filter (fun σ => Equiv.Perm.sign σ = 1 ∧ σ ^ 2 = 1)
  have hmemT4 : ∀ σ, σ ∈ T4 ↔ Equiv.Perm.sign σ = 1 ∧ σ ^ 2 = 1 := by
    intro σ
    simp only [T4, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsubT : ∀ w : ↥W', θ w ∈ T4 := by
    intro w
    have hw : (w : Y) ∈ L := hWL w.2
    have hsign : Equiv.Perm.sign (θ w) = 1 :=
      (hΘsign (Subgroup.inclusion hWH w)).2 ⟨w, hw, 1, one_mem _, by simp⟩
    have h4 : (θ w) ^ 4 = 1 := by
      have : w ^ 4 = 1 := Subtype.ext (hW4 w w.2)
      rw [← map_pow, this, map_one]
    exact (hmemT4 _).2 ⟨hsign, perm4_even_sq _ hsign h4⟩
  have hker : Nat.card θ.ker ≤ 2 := by
    have hZ : Nat.card (center ↥L) = 2 := (sl2_model_center_inv ⟨1, rfl⟩ hL).1
    have hle : θ.ker.map (Subgroup.inclusion hWL) ≤ center ↥L := by
      rintro _ ⟨k, hk, rfl⟩
      have hk1 : Θ (Subgroup.inclusion hWH k) = 1 := hk
      have hkC := (hΘone _).1 hk1
      rw [Subgroup.mem_center_iff]
      intro g'
      exact Subtype.ext (mem_centralizer_iff.1 hkC g' g'.2)
    have := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hWL), hZ] at this
  have hrange : 4 ≤ Nat.card θ.range := by
    have h1 := Subgroup.index_ker θ
    have h2 := θ.ker.index_mul_card
    rw [h1, hW8] at h2
    have h3 : 0 < Nat.card θ.ker := Nat.card_pos
    nlinarith
  have hT4range : ∀ σ ∈ T4, σ ∈ θ.range := by
    have hfin : (θ.range : Set (Equiv.Perm (Fin 4))).Finite := Set.toFinite _
    have hRsub : hfin.toFinset ⊆ T4 := by
      intro σ hσ
      obtain ⟨w, rfl⟩ := hfin.mem_toFinset.1 hσ
      exact hsubT w
    have hRcard : Nat.card θ.range = hfin.toFinset.card :=
      Nat.card_eq_card_finite_toFinset hfin
    have hT4card : T4.card = 4 := perm4_card_inv
    have heq : hfin.toFinset = T4 :=
      Finset.eq_of_subset_of_card_le hRsub (by rw [hT4card, ← hRcard]; exact hrange)
    intro σ hσ
    have : σ ∈ hfin.toFinset := by rw [heq]; exact hσ
    exact hfin.mem_toFinset.1 this
  let x' : ↥(L ⊔ SB) := ⟨x, hx⟩
  have hxc : ∀ σ ∈ T4, Θ x' * σ = σ * Θ x' := by
    intro σ hσ
    obtain ⟨w, hw⟩ := hT4range σ hσ
    have hwc : Θ (x' * Subgroup.inclusion hWH w * x'⁻¹ * (Subgroup.inclusion hWH w)⁻¹) = 1 :=
      (hΘone _).2 (by simpa [x'] using hcomm w w.2)
    have hθw : Θ (Subgroup.inclusion hWH w) = σ := hw
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hθw] at hwc
    calc Θ x' * σ = (Θ x' * σ * (Θ x')⁻¹ * σ⁻¹) * (σ * Θ x') := by group
      _ = σ * Θ x' := by rw [hwc, one_mul]
  have hxT4 : Θ x' ∈ T4 := by
    obtain ⟨h1, h2⟩ := perm4_centralizer (Θ x') fun σ hs hs2 => hxc σ ((hmemT4 σ).2 ⟨hs, hs2⟩)
    exact (hmemT4 _).2 ⟨h1, h2⟩
  obtain ⟨w, hw⟩ := hT4range _ hxT4
  have hθw : Θ (Subgroup.inclusion hWH w) = Θ x' := hw
  refine ⟨w, w.2, ?_⟩
  have h1 : Θ ((Subgroup.inclusion hWH w)⁻¹ * x') = 1 := by
    rw [map_mul, map_inv, hθw, inv_mul_cancel]
  simpa [x'] using (hΘone _).1 h1

end Theta

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

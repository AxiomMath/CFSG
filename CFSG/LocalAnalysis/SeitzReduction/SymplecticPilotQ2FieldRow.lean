module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2FieldCT
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotUniqueField
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore statedSpMap)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Unique

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem conjugate_eq_of_nsFieldRow (hset : SeitzSetting G L) {n : ℕ} (hn : 3 ≤ n) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ : orderOf σ = 2)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {ψ : StatedSp n F →* G}
    (hinj : Function.Injective ψ) (hrange : ψ.range = nsGlobal e) (h : G)
    (htM : t ∈ normalizer (CFSG.conjugate (nsGlobal e) h : Set G)) :
    CFSG.conjugate (nsGlobal e) h = nsGlobal e := by
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    omega
  have hF : Nat.card F = Nat.card K ^ 2 := LinearPilot.natCard_eq_sq_of_fixedField ι hσ1 hσσ hfix
  have hF4 : 4 ≤ Nat.card F := by rw [hF, hK]; norm_num
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp hn e)
  set Ψ : StatedSp n F →* G := (MulAut.conj h⁻¹).toMonoidHom.comp ψ with hΨ
  have hinjΨ : Function.Injective Ψ := (MulAut.conj h⁻¹).injective.comp hinj
  have hrangeΨ : Ψ.range = CFSG.conjugate (nsGlobal e) h := by
    rw [hΨ, MonoidHom.range_comp, hrange]
    rfl
  obtain ⟨β, hβ⟩ := exists_mulAut_of_mem_normalizer_range hinjΨ (hrangeΨ ▸ htM)
  have hβi := not_mem_range_conj_of_fieldRow hset.standardSetting.standard hn hKc e ht hKt hF
    hinjΨ hβ
  obtain ⟨Φ, hΦr, hΦ⟩ := exists_comp_statedSpMap_eq hset.standardSetting hOut hn e htC ht ι hσ
    hfix hinjΨ hβ hβi
  have hle : CFSG.conjugate (nsGlobal e) h ≤ nsGlobal e := by
    rw [← hrangeΨ, ← hΦr]
    exact range_le_nsGlobal_of_comp_spFieldMap hF4 hn e ι fun x => by
      rw [spFieldMap_eq_statedSpMap]
      exact hΦ x
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).ge

theorem unique_of_nsFieldRow (hset : SeitzSetting G L) {n : ℕ} (hn : 3 ≤ n) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ : orderOf σ = 2)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {ψ : StatedSp n F →* G}
    (hinj : Function.Injective ψ) (hrange : ψ.range = nsGlobal e) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G) →
      g ∈ normalizer (nsGlobal e : Set G) :=
  F4Pilot.unique_of_forall_conjugate_eq fun h htM =>
    conjugate_eq_of_nsFieldRow hset hn hK e ht hKt ι hσ hfix hinj hrange h htM

end Unique

section Endgame

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {F : Type} [Field F] [Finite F] {n : ℕ}

theorem false_of_nsFieldRow (hset : SeitzSetting G L) (hn : 3 ≤ n) (e : L ≃* StatedSp n K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {ι : K →+* F}
    {σ : F ≃+* F} (hσ : orderOf σ = 2) {ψ : StatedSp n F →* G} (hinj : Function.Injective ψ)
    (hrange : ψ.range = nsGlobal e)
    (hψι : ∀ x : StatedSp n K, ψ (spFieldMap n ι x) = ((e.symm x : L) : G))
    (hσψ : ∀ x : StatedSp n F, t * ψ x * t⁻¹ = ψ (fieldSp n F σ x))
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G) →
      g ∈ normalizer (nsGlobal e : Set G)) : False := by
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have : IsSimpleGroup G := hset.1
  have : NeZero n := ⟨by omega⟩
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_nsGlobal e htC
  have hσ1 : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have htZ : t ∉ centralizer ((nsGlobal e : Subgroup G) : Set G) := by
    intro htZ
    apply hσ1
    refine F4Pilot.eq_one_of_fieldSp_eq_one (r := n) (MulEquiv.ext fun x => hinj ?_)
    have hx : ψ x ∈ nsGlobal e := hrange ▸ ⟨x, rfl⟩
    rw [MulAut.one_apply, ← hσψ]
    have hc : ψ x * t = t * ψ x := mem_centralizer_iff.1 htZ (ψ x) hx
    rw [← hc, mul_inv_cancel_right]
  have hLG : L ≤ nsGlobal e := (le_range_of_comp_spFieldMap e ι hψι).trans hrange.le
  have hZ := EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt hLG ht htN htZ
  exact false_of_simple_of_spField hn hinj hrange ht htN hσ1 hσψ hZ huniq

end Endgame

section Row

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem false_of_forall_nsKindSp_field (hset : SeitzSetting G L) {n : ℕ} [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (hn : 4 ≤ n) (e : L ≃* StatedSp (n + 1) K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hfield : ∀ k : Fin (n + 1), NsKindSp e t k .field) : False := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := exists_quadraticExtension K
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    omega
  have hF4 : 4 ≤ Nat.card F := by
    rw [LinearPilot.natCard_eq_sq_of_fixedField ι hσ1 hσσ hfix, hK]
    norm_num
  have hparam : ∀ k : Fin (n + 1), Nonempty (NsFieldParam e t ι σ k) := fun k =>
    nonempty_nsFieldParam hset hK (by omega) e htC ht k ι hσ hfix (hfield k)
  obtain ⟨ψ, hinj, hrange, hψι, hσψ⟩ :=
    exists_injective_nsFieldRow hF4 (by omega) hσ hfix hparam
  exact false_of_nsFieldRow hset (by omega) e ht hKt hσ hinj hrange hψι hσψ
    (unique_of_nsFieldRow hset (by omega) hK e ht hKt ι hσ hfix hinj hrange)

end Row

@[expose] def SpTwoFieldRowEightInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → n = 3 →
    ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (n + 1), NsKindSp e t k .field) → False

theorem spTwoRowInput_field_of_eight
    (h8 : SpTwoFieldRowEightInput) : SpTwoRowInput .field := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt hfield
  rcases (show n = 3 ∨ 4 ≤ n by omega) with h3 | h4
  · exact h8 G L hset n K hK h3 e t ht hKt hfield
  · exact false_of_forall_nsKindSp_field hset hK h4 e ht hKt hfield

end CFSG.SeitzReduction.SymplecticPilot

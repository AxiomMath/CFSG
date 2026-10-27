module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndOddBasic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeSp
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHsyl
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizePieces

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (elt)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.F4Pilot (normalizerMulAut)

section Aut

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

omit [Finite F] [CharP F 2] in
theorem fieldSp_eq_one_of_mem_range_conj (hn : 1 ≤ n) {ρ : F ≃+* F}
    (h : fieldSp n F ρ ∈ (MulAut.conj : StatedSp n F →* MulAut (StatedSp n F)).range) :
    fieldSp n F ρ = 1 := by
  obtain ⟨s, hs⟩ := h
  have hρ : ρ = 1 := eq_one_of_forall_conj_fieldSp_elt (s := s⁻¹)
    (ρ := .positiveLong ⟨0, by omega⟩) fun c => by
      rw [← hs, MulAut.conj_apply]
      group
  rw [hρ, map_one]

theorem exists_frobenius_pow (ρ : F ≃+* F) {φ : F ≃+* F} (hφ : ∀ c, φ c = c ^ 2) :
    ∃ m : ℕ, ρ = φ ^ m := by
  obtain ⟨m, hm⟩ := F4Pilot.exists_pow_eq_of_charTwo ρ
  exact ⟨m, RingEquiv.ext fun c => by
    rw [hm, CFSG.ComponentClassification.UnbalancedCatalog.SpChain.ringAut_pow_apply_of_sq hφ]⟩

end Aut

section Endgame

variable {G : Type*} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
  {G₀ : Subgroup G}

omit [Finite G] [Finite F] [CharP F 2] in
theorem normalizerMulAut_eq_fieldSp {ψ : StatedSp n F →* G} (hinj : Function.Injective ψ)
    (hrange : ψ.range = G₀) {t : G} (htN : t ∈ normalizer (G₀ : Set G)) {σ : F ≃+* F}
    (hσψ : ∀ x : StatedSp n F, t * ψ x * t⁻¹ = ψ (fieldSp n F σ x)) :
    normalizerMulAut ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm
      ⟨t, htN⟩ = fieldSp n F σ := by
  set E : StatedSp n F ≃* G₀ := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
    with hE
  have hEapp : ∀ x, ((E x : G₀) : G) = ψ x := fun x => rfl
  apply MulEquiv.ext
  intro x
  apply E.injective
  apply Subtype.ext
  have h := F4Pilot.coe_symm_normalizerMulAut_apply E.symm ⟨t, htN⟩ x
  rw [MulEquiv.symm_symm] at h
  rw [h, hEapp, hEapp, hσψ]

theorem exists_normal_index_two_of_spField (hn : 3 ≤ n) {ψ : StatedSp n F →* G}
    (hinj : Function.Injective ψ) (hrange : ψ.range = G₀) {t : G} (ht : orderOf t = 2)
    (htN : t ∈ normalizer (G₀ : Set G)) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσψ : ∀ x : StatedSp n F, t * ψ x * t⁻¹ = ψ (fieldSp n F σ x))
    (hZ : Odd (Nat.card (centralizer (G₀ : Set G))))
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  set e : G₀ ≃* StatedSp n F :=
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm with he
  obtain ⟨φ, hφ⟩ := F4Pilot.exists_ringEquiv_eq_sq_of_charTwo (K := F)
  set C : Subgroup (MulAut (StatedSp n F)) := zpowers (fieldSp n F φ) with hC
  have hker : Odd (Nat.card (normalizerMulAut e).ker) := by
    rw [EPilot.card_ker_normalizerMulAut]
    exact hZ
  have hCInn : ∀ β ∈ C, β ∈ (MulAut.conj : StatedSp n F →* MulAut (StatedSp n F)).range →
      β = 1 := by
    rintro β ⟨k, rfl⟩ hβ
    have hk : fieldSp n F φ ^ k = fieldSp n F (φ ^ k) := (map_zpow _ _ _).symm
    change fieldSp n F φ ^ k ∈ _ at hβ
    change fieldSp n F φ ^ k = 1
    rw [hk] at hβ ⊢
    exact fieldSp_eq_one_of_mem_range_conj (by omega) hβ
  have hNF : ∀ α : MulAut (StatedSp n F), ∃ g : StatedSp n F, ∃ β ∈ C, α = MulAut.conj g * β := by
    intro α
    obtain ⟨s, ρ, rfl⟩ := exists_eq_conj_mul_fieldSp hn α
    obtain ⟨m, rfl⟩ := exists_frobenius_pow ρ hφ
    exact ⟨s, fieldSp n F (φ ^ m), ⟨m, by
      change fieldSp n F φ ^ (m : ℤ) = _
      rw [map_pow, zpow_natCast]⟩, rfl⟩
  have hact := normalizerMulAut_eq_fieldSp hinj hrange htN hσψ
  have hout : normalizerMulAut e ⟨t, htN⟩ ∉
      (MulAut.conj : StatedSp n F →* MulAut (StatedSp n F)).range := by
    rw [hact]
    intro h
    have : NeZero n := ⟨by omega⟩
    exact hσ1 (F4Pilot.eq_one_of_fieldSp_eq_one (r := n) (fieldSp_eq_one_of_mem_range_conj
      (by omega) h))
  have hσC : fieldSp n F σ ∈ C := by
    obtain ⟨m, rfl⟩ := exists_frobenius_pow σ hφ
    exact ⟨m, by
      change fieldSp n F φ ^ (m : ℤ) = _
      rw [map_pow, zpow_natCast]⟩
  exact EPilot.exists_normal_index_two_of_action_complement_of_isConj (normalizerMulAut e) hker
    hCInn hNF (EPilot.exists_normalizerMulAut_eq_conj e) htN ht hout huniq
    ⟨1, by rw [hact, one_mul, inv_one, mul_one]; exact hσC⟩

theorem false_of_simple_of_spField [IsSimpleGroup G] (hn : 3 ≤ n) {ψ : StatedSp n F →* G}
    (hinj : Function.Injective ψ) (hrange : ψ.range = G₀) {t : G} (ht : orderOf t = 2)
    (htN : t ∈ normalizer (G₀ : Set G)) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσψ : ∀ x : StatedSp n F, t * ψ x * t⁻¹ = ψ (fieldSp n F σ x))
    (hZ : Odd (Nat.card (centralizer (G₀ : Set G))))
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    False := by
  set e : G₀ ≃* StatedSp n F :=
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm with he
  have hact := normalizerMulAut_eq_fieldSp hinj hrange htN hσψ
  have htG : t ∉ G₀ := EPilot.not_mem_of_normalizerMulAut_not_mem_range e htN (by
    rw [hact]
    intro h
    have : NeZero n := ⟨by omega⟩
    exact hσ1 (F4Pilot.eq_one_of_fieldSp_eq_one (r := n) (fieldSp_eq_one_of_mem_range_conj
      (by omega) h)))
  exact CFSG.SeitzReduction.not_exists_normal_index_two_of_simple
    (EPilot.two_lt_card_of_odd_centralizer hZ ht htG)
    (exists_normal_index_two_of_spField hn hinj hrange ht htN hσ1 hσψ hZ huniq)

end Endgame

section Seitz

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] {n : ℕ}

omit [Finite K] in
theorem false_of_spFieldRow (hset : SeitzSetting G L) (hK : 4 ≤ Nat.card K) (hn : 3 ≤ n)
    (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {ι : K →+* F}
    {σ : F ≃+* F} (hσ : orderOf σ = 2) {ψ : StatedSp n F →* G} (hinj : Function.Injective ψ)
    (hrange : ψ.range = spGlobal e)
    (hσψ : ∀ x : StatedSp n F, t * ψ x * t⁻¹ = ψ (fieldSp n F σ x))
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G) →
      g ∈ normalizer (spGlobal e : Set G)) : False := by
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have : IsSimpleGroup G := hset.1
  have : NeZero n := ⟨by omega⟩
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_spGlobal e htC
  have hσ1 : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have htZ : t ∉ centralizer ((spGlobal e : Subgroup G) : Set G) := by
    intro htZ
    apply hσ1
    refine F4Pilot.eq_one_of_fieldSp_eq_one (r := n) (MulEquiv.ext fun x => hinj ?_)
    have hx : ψ x ∈ spGlobal e := hrange ▸ ⟨x, rfl⟩
    rw [MulAut.one_apply, ← hσψ]
    have hc : ψ x * t = t * ψ x := mem_centralizer_iff.1 htZ (ψ x) hx
    rw [← hc, mul_inv_cancel_right]
  have hZ := EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt (le_spGlobal hK (by omega) e) ht
    htN htZ
  exact false_of_simple_of_spField hn hinj hrange ht htN hσ1 hσψ hZ huniq

end Seitz

end CFSG.SeitzReduction.SymplecticPilot

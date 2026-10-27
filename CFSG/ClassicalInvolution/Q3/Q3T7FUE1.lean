module

public import CFSG.ClassicalInvolution.Q3.Q3T7FUE0
public import CFSG.ClassicalInvolution.Q3.Q3T7M00
public import CFSG.ClassicalInvolution.Q3.Q3T8Defs

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.T7FU

variable {MT : CFSG.ClassicalInvolution.Uniform.MemberType}
open CFSG.ClassicalInvolution.Q3.Q3T7M (omegaNbr_subset_kPerp_of_twin mem_kPerp_of_twin
  omegaStarDiff_subset_of_twin l6_3 le_of_sq_mem_of_oddGen odd_mem_of_mem_sup_central
      oddGen_conjSub)
open CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
    (HypOmegaMod L6_2 l6_2 L6_7 l6_7_proved L6_10 l6_10_proved
  L6_11 l6_11_proved L6_9 l6_9_proved)

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification.AschbacherTheorem3
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem eq_of_conjSub_le_of_l6_7 [Finite G] (h67 : L6_7On Ω)
    (hΩ : HM MT Ω) {R Y X S : Subgroup G} (hR : R ∈ RSet Ω) (hRY : R ≤ Y)
    (hXn : ∀ y ∈ Y, conjSub y X = X) (hRX : R ⊓ X = ⊥) (hS2 : IsPGroup 2 S)
    (hRS : R ≤ S) (hSH : S ≤ X ⊔ R) {g : G} (hg : g ∈ Y) (hle : conjSub g R ≤ S) :
    conjSub g R = R := by
  by_contra hne
  have hR2 : IsPGroup 2 R := (mem_RSet_iff.mp hR).choose_spec.2.2.1
  have hR'' : conjSub g R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hR g
  obtain ⟨S₀, hS₀⟩ := IsPGroup.exists_le_sylow hS2
  have hcomm : Commutes R (conjSub g R) :=
    h67 S₀ R hR (conjSub g R) hR'' (hRS.trans hS₀) (hle.trans hS₀) (Ne.symm hne)
  have hRN : R ≤ Subgroup.normalizer (X : Set G) := fun x hx =>
    mem_normalizer_of_normal_in hXn (hRY hx)
  have hR''Y : conjSub g R ≤ Y := conjSub_le_of_le_of_mem_left hRY hg
  have hR''N : conjSub g R ≤ Subgroup.normalizer (X : Set G) := fun x hx =>
    mem_normalizer_of_normal_in hXn (hR''Y hx)
  have hR''X : X ⊓ conjSub g R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxX, hxR⟩ := Subgroup.mem_inf.mp hx
    rw [mem_conjSub_iff] at hxR
    have hxX' : g⁻¹ * x * g ∈ X := by
      have := conj_mem_conjSub (n := g⁻¹) hxX
      rwa [hXn g⁻¹ (Y.inv_mem hg), inv_inv] at this
    have h1 : g⁻¹ * x * g ∈ R ⊓ X := ⟨hxR, hxX'⟩
    rw [hRX, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h1]
    group
  have hcard : Nat.card (conjSub g R) = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hc1 : Nat.card (X ⊔ conjSub g R : Subgroup G) = Nat.card X * Nat.card (conjSub g R) :=
    card_sup_of_le_normalizer hR''N hR''X
  have hc2 : Nat.card (X ⊔ R : Subgroup G) = Nat.card X * Nat.card R :=
    card_sup_of_le_normalizer hRN (by rwa [inf_comm])
  have hle2 : X ⊔ conjSub g R ≤ X ⊔ R := sup_le le_sup_left (hle.trans hSH)
  have heq : X ⊔ conjSub g R = X ⊔ R :=
    Subgroup.eq_of_le_of_card_ge hle2 (by rw [hc1, hc2, hcard])
  have hF : Frame X (conjSub g R) :=
    ⟨hR''N, by rwa [inf_comm], isPGroup_conjSub g hR2⟩
  obtain ⟨a, ha, b, hb, hab⟩ := (hΩ.isQuatSub_of_mem_RSet hR).exists_not_commute
  apply hab
  have hamem : a ∈ X ⊔ conjSub g R := heq ▸ (le_sup_right : R ≤ X ⊔ R) ha
  obtain ⟨t, ht, c, hc, hr⟩ := hF.mem_sup_iff.mp hamem
  have hcdef : c = t⁻¹ * a := by rw [← hr]; group
  have hct : t⁻¹ * (a * b * a⁻¹) * t = a * b * a⁻¹ := by
    have := hcomm (a * b * a⁻¹) (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) t ht
    rw [mul_assoc, this]
    group
  have hw1 : a * b * a⁻¹ * b⁻¹ ∈ R := R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha))
    (R.inv_mem hb)
  have hw2 : a * b * a⁻¹ * b⁻¹ ∈ X := by
    have e : a * b * a⁻¹ * b⁻¹ = c * (b * c⁻¹ * b⁻¹) := by
      calc a * b * a⁻¹ * b⁻¹ = (t⁻¹ * (a * b * a⁻¹) * t) * b⁻¹ := by rw [hct]
        _ = c * (b * c⁻¹ * b⁻¹) := by rw [hcdef]; group
    rw [e]
    refine X.mul_mem hc ?_
    have := conj_mem_conjSub (n := b) (X.inv_mem hc)
    rwa [hXn b (hRY hb)] at this
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ R ⊓ X := ⟨hw1, hw2⟩
  rw [hRX, Subgroup.mem_bot] at h1
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h1, one_mul]

theorem l6_13_on [Finite G] (hΩ : HM MT Ω) (h67 : L6_7On Ω) :
    ∀ R ∈ RSet Ω, ∀ Y X : Subgroup G, R ≤ Y → X ≤ Y → (∀ y ∈ Y, conjSub y X = X) →
      R ⊓ X = ⊥ →
        (⨆ R' ∈ {R' : Subgroup G | (∃ y ∈ Y, R' = conjSub y R) ∧ R' ≤ R ⊔ X}, R') ≤
            R ⊔ oddCoreOf X ∧
          ⁅R, X⁆ ≤ oddCoreOf X := by
  intro R hR Y X hRY hXY hXn hRX
  have hR2 : IsPGroup 2 R := (mem_RSet_iff.mp hR).choose_spec.2.2.1
  have hRN : R ≤ Subgroup.normalizer (X : Set G) := fun x hx =>
    mem_normalizer_of_normal_in hXn (hRY hx)
  have hHY : X ⊔ R ≤ Y := sup_le hXY hRY
  obtain ⟨S, hS, hRS⟩ := exists_isSylowOf_le hR2 (le_sup_right : R ≤ X ⊔ R)
  have hclosed : ∀ g ∈ Y, conjSub g R ≤ S → conjSub g R = R := fun g hg hle =>
    eq_of_conjSub_le_of_l6_7 h67 hΩ hR hRY hXn hRX hS.isPGroup hRS hS.le hg hle
  have h42 : Hyp42 X R S :=
    { frame := ⟨hRN, hRX, hR2⟩
      sylow := hS
      le := hRS
      closed := fun g hg hle => hclosed g⁻¹ (Y.inv_mem (hXY hg)) hle }
  have hcomm : ⁅X, R⁆ ≤ oddCoreOf X := lemma_4_2_oddCore h42
  have hcomm' : ⁅R, X⁆ ≤ oddCoreOf X := by
    rw [Subgroup.commutator_comm]
    exact hcomm
  refine ⟨?_, hcomm'⟩
  refine iSup₂_le fun R' hR' => ?_
  obtain ⟨⟨y, hy, hR'eq⟩, hR'le⟩ := hR'
  subst hR'eq
  have hR'2 : IsPGroup 2 (conjSub y R) := isPGroup_conjSub y hR2
  obtain ⟨S', hS', hR'S'⟩ := exists_isSylowOf_le hR'2 (sup_comm R X ▸ hR'le)
  obtain ⟨c, hcH, hconj⟩ := exists_rightConjugate_eq_of_isSylowOf hS' hS
  have hcY : c ∈ Y := hHY hcH
  have hle : conjSub (c * y) R ≤ S := by
    rw [conjSub_mul]
    have h1 : conjSub y R ≤ conjSub c⁻¹ S := by
      have : rightConjugate S c = conjSub c⁻¹ S := rfl
      rw [← this, hconj]
      exact hR'S'
    have h2 := conjSub_mono (n := c) h1
    rwa [conjSub_conjSub_inv] at h2
  have hceq : conjSub (c * y) R = R := hclosed _ (Y.mul_mem hcY hy) hle
  have hyR : conjSub y R = conjSub c⁻¹ R := by
    calc conjSub y R = conjSub (c⁻¹ * (c * y)) R := by rw [inv_mul_cancel_left]
      _ = conjSub c⁻¹ (conjSub (c * y) R) := conjSub_mul _ _ _
      _ = conjSub c⁻¹ R := by rw [hceq]
  have hF : Frame X R := ⟨hRN, hRX, hR2⟩
  obtain ⟨ρ, hρ, x, hx, hρx⟩ := hF.mem_sup_iff.mp (Subgroup.inv_mem _ hcH)
  have hinv : c⁻¹ = (ρ * x * ρ⁻¹) * ρ := by rw [← hρx]; group
  have hxX : ρ * x * ρ⁻¹ ∈ X := by
    have := conj_mem_conjSub (n := ρ) hx
    rwa [hXn ρ (hRY hρ)] at this
  rw [hyR, hinv, conjSub_mul, conjSub_eq_self_of_mem hρ]
  intro u hu
  rw [mem_conjSub_iff] at hu
  have hu' : u = ((ρ * x * ρ⁻¹) * ((ρ * x * ρ⁻¹)⁻¹ * u * (ρ * x * ρ⁻¹)) * (ρ * x * ρ⁻¹)⁻¹ *
      ((ρ * x * ρ⁻¹)⁻¹ * u * (ρ * x * ρ⁻¹))⁻¹) * ((ρ * x * ρ⁻¹)⁻¹ * u * (ρ * x * ρ⁻¹)) := by
    group
  rw [hu', sup_comm]
  refine Subgroup.mul_mem_sup (hcomm (Subgroup.commutator_mem_commutator hxX hu)) hu

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic

@[expose] def E18_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex MT Ω K S R W H →
      (∀ g : G, conjSub g K ∈ dstarComp Ω K → g ∈ H) ∧ ∃ J ∈ Ω, J ∉ dstarComp Ω K

@[expose] def E18_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex MT Ω K S R W H →
      ∀ u ∈ K, orderOf u = 4 → ∀ g : G, g * u * g⁻¹ ∈ H → g ∈ H

@[expose] def E18_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex MT Ω K S R W H → ∀ J ∈ Ω, ∃ g : G, conjSub g K = J

@[expose] def E18_zW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex MT Ω K S R W H → ∃ z : G, IsUniqueInvolution K z ∧ z ∈ W

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
section CaseA
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem e189_caseA (hΩ : HM MT Ω) {K J : Subgroup G}
    {z t : G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (htz : t ≠ z) (hzt : z * t = t * z)
    (hnorm : conjSub t K = K) : (∃ g : G, g * t * g⁻¹ = z * t) ∨ J ∈ KPerp Ω K :=
  E187C.e189_caseA_of (fun hQ => hΩ.eight_le_of_mem_RSet hQ) (l6_2 G Ω hΩ) hK hJ hz ht htz hzt hnorm

end CaseA
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic

theorem e18_zW : (@E18_zW MT) := by
  intro G _ _ Ω K S R W H c
  exact E187C.e18_zW_of c.stand.hyp.conjInvariant c.stand.mem c.stand.hR c.stand.hW
    (fun hK => c.stand.hyp.exists_uniqueInvolution hK)
    (fun hQ => c.stand.hyp.isQuatSub_of_mem_RSet hQ)
    (fun hK hJ hA h4 hAK hAJ => c.stand.hyp.eq_of_le_of_le hK hJ hA h4 hAK hAJ)
    (fun h hK hU hUK =>
      CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.exists_mem_of_mem_etaSet c.stand.hyp
        h hK hU hUK)
    (fun hU => by
      obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := c.stand.hyp.exists_data_of_mem_USet hU
      exact h4)
    (fun hU => c.stand.hyp.isPGroup_of_mem_USet hU)

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic

theorem e18_3 (h67 : L6_7) : (@E18_3 MT) := by
  intro G _ _ Ω K S R W H c
  exact E187C.e18_3_of c.stand.hyp.conjInvariant c.stand.mem c.stand.hR c.hyp.trans
    (fun hK => c.stand.hyp.exists_uniqueInvolution hK)
    (fun hQ => c.stand.hyp.eight_le_of_mem_RSet hQ)
    (fun hK hJ hA h4 hAK hAJ => c.stand.hyp.eq_of_le_of_le hK hJ hA h4 hAK hAJ)
    (h67 G Ω c.stand.hyp)
    (fun hK hJ hKJ hz hAJ hA2 hA3 hAc =>
      c.stand.hyp.le_normalizer_of_le_centralizer hK hJ hKJ hz hAJ hA2 hA3 hAc)
    (fun hQ => c.stand.hyp.isQuatSub_of_mem_RSet hQ)

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic

theorem MinCex.centralizer_le {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G} (c : MinCex MT Ω K S R W H) {z : G}
    (hz : IsUniqueInvolution K z) : Subgroup.centralizer ({z} : Set G) ≤ H :=
  E187C.centralizer_le_of c.stand.mem c.stand.hR.1 c.stand.hR.2.1
    (c.stand.hyp.eight_le_of_mem_RSet c.stand.hR.1) c.hyp.cent hz

theorem MinCex.exists_centralizer_le {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G} (c : MinCex MT Ω K S R W H) :
    ∃ z : G, IsUniqueInvolution K z ∧ Subgroup.centralizer ({z} : Set G) ≤ H := by
  obtain ⟨z, hz⟩ := c.stand.hyp.exists_uniqueInvolution c.stand.mem
  exact ⟨z, hz, c.centralizer_le hz⟩

theorem e18_1 : (@E18_1 MT) := by
  intro G _ _ Ω K S R W H c
  obtain ⟨z, hz, hcz⟩ := c.exists_centralizer_le
  exact E187C.e18_1_of c.stand.hyp.conjInvariant c.stand.mem hz hcz c.hyp.trans c.proper
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem mem_dstarComp_of_mem_USet_le_W [Finite G] (hΩ : HM MT Ω) {K J W V₀ V₁ : Subgroup G} (hK
    : K ∈ Ω) (hJ : J ∈ Ω)
    (hV₀ : V₀ ∈ USet Ω) (hV₀K : V₀ ≤ K) (hV₀W : V₀ ≤ W) (hV₁ : V₁ ∈ USet Ω) (hV₁J : V₁ ≤ J)
    (hV₁W : V₁ ≤ W) (habel : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : J ∈ dstarComp Ω K :=
  E187C.mem_dstarComp_of_mem_USet_le_W_of (fun hK => hΩ.exists_uniqueInvolution hK)
    (fun hU => by
      obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hU
      exact h4)
    (fun hU => hΩ.isPGroup_of_mem_USet hU)
    (fun hK hJ hKJ hz hAJ hA2 hA3 hAc =>
      hΩ.le_normalizer_of_le_centralizer hK hJ hKJ hz hAJ hA2 hA3 hAc)
    hK hJ hV₀ hV₀K hV₀W hV₁ hV₁J hV₁W habel

theorem EtaAbelian.of_l6_9 [Finite G] (h : L6_9) (hΩ : HM MT Ω) : EtaAbelian Ω :=
  fun S _ hη hinv => ((h G Ω hΩ S).2 _ hη hinv).1

theorem EtaMeet.of_l6_11 [Finite G] (h : L6_11) (hΩ : HM MT Ω) : EtaMeet Ω :=
  fun S _ hη hηS _ hK h2 => h G Ω hΩ S _ hη hηS _ hK h2

section MinCex
variable [Finite G] {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.exists_eta (c : MinCex MT Ω K S R W H) (hA : EtaAbelian Ω) :
    ∃ η : Set (Subgroup G), η ∈ etaG Ω ∧ W = ⨆ V ∈ η, V ∧
      (∀ V ∈ η, V ∈ USet Ω ∧ V ≤ (S : Subgroup G)) ∧
      (∀ x ∈ W, ∀ y ∈ W, x * y = y * x) ∧ ∃ V₀ ∈ η, V₀ ≤ K := by
  have hΩ : HM MT Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨hWW, hWS, -⟩ := c.stand.hW
  obtain ⟨η, hη, hWη⟩ := hWW
  obtain ⟨S₁, hS₁, hinv⟩ := hη
  have hAW : ∀ V ∈ η, V ≤ W := fun V hV => hWη ▸ le_iSup₂_of_le V hV le_rfl
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hAW V hV).trans hWS
  have hηS' : η ∈ etaSet Ω (S : Subgroup G) := mem_etaSet_of_le hΩ.conjInvariant hS₁ hηS
  have hRK' : IsSylow2In R K := hΩ.isSylow2In_of_mem_RSet_of_le hK hRR hRK
  obtain ⟨U₀, hU₀R, hcyc, hcard⟩ := (hΩ.isQuatSub_of_mem_RSet hRR).exists_cyclic_index_two
  have hU₀ : U₀ ∈ USet Ω := mem_USet_of_natCard hK hRK' hU₀R hcyc hcard
  obtain ⟨V₀, hV₀η, hV₀K⟩ :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.exists_mem_of_mem_etaSet hΩ hηS' hK
      ⟨hU₀, hU₀R.trans hRS⟩
    (hU₀R.trans hRK)
  refine ⟨η, ⟨S₁, hS₁, hinv⟩, hWη, fun V hV => ⟨(hS₁.1 hV).1, hηS V hV⟩, ?_, V₀, hV₀η, hV₀K⟩
  have := hA S₁ η hS₁ hinv
  rwa [← hWη] at this

theorem MinCex.mem_of_conjSub_eq_W (c : MinCex MT Ω K S R W H) (hA : EtaAbelian Ω) {n : G}
    (hn : conjSub n W = W) : n ∈ H := by
  obtain ⟨η, -, hWη, hηU, habel, V₀, hV₀η, hV₀K⟩ := c.exists_eta hA
  have hΩ : HM MT Ω := c.stand.hyp
  have hV₀U : V₀ ∈ USet Ω := (hηU V₀ hV₀η).1
  have hV₀W : V₀ ≤ W := hWη ▸ le_iSup₂_of_le V₀ hV₀η le_rfl
  have hmem : conjSub n K ∈ dstarComp Ω K :=
    mem_dstarComp_of_mem_USet_le_W hΩ c.stand.mem (hΩ.conjInvariant n K c.stand.mem)
      hV₀U hV₀K hV₀W (USet.conj hΩ.conjInvariant hV₀U n) (conjSub_mono hV₀K)
      (hn ▸ conjSub_mono hV₀W) habel
  exact (e18_1 G Ω K S R W H c).1 n hmem

theorem MinCex.sylow_le (c : MinCex MT Ω K S R W H) (hA : EtaAbelian Ω) :
    (S : Subgroup G) ≤ H :=
  fun s hs => c.mem_of_conjSub_eq_W hA (c.stand.hW.2.2 s hs)

theorem MinCex.mem_of_conj_mem (c : MinCex MT Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {u : G} (hu : u ∈ K) (hu4 : orderOf u = 4) {g : G} (hg : g * u * g⁻¹ ∈ H) :
    g ∈ H := by
  exact E187C.mem_of_conj_mem_of c.stand.hyp.conjInvariant c.stand.mem hM (c.exists_eta hA)
    (c.sylow_le hA)
    (fun hJ hV₀ hV₀K hV₀W hV₁ hV₁J hV₁W habel =>
      mem_dstarComp_of_mem_USet_le_W c.stand.hyp c.stand.mem hJ hV₀ hV₀K hV₀W hV₁ hV₁J hV₁W habel)
    (e18_1 G Ω K S R W H c).1 hu hu4 hg

end MinCex

theorem e18_2_of_l6_9_l6_11 (h69 : L6_9) (h611 : L6_11) : (@E18_2 MT) := by
  intro G _ _ Ω K S R W H c u hu hu4 g hg
  exact c.mem_of_conj_mem (EtaAbelian.of_l6_9 h69 c.stand.hyp)
    (EtaMeet.of_l6_11 h611 c.stand.hyp) hu hu4 hg

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
section General

private theorem sq_eq_of_orderOf_four {J : Subgroup G} {z u : G} (hz : IsUniqueInvolution J z)
    (hu : u ∈ J) (h4 : orderOf u = 4) : u * u = z := by
  have h1 : (u * u) * (u * u) = 1 := by
    have := pow_orderOf_eq_one u
    rw [h4] at this
    calc (u * u) * (u * u) = u ^ 4 := by simp [pow_succ, mul_assoc]
      _ = 1 := this
  rcases hz.unique (u * u) (J.mul_mem hu hu) h1 with h | h
  · exfalso
    have : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [h4] at this
    omega
  · exact h

private theorem isPGroup_zpowers_of_orderOf_four {u : G} (h4 : orderOf u = 4) :
    IsPGroup 2 (Subgroup.zpowers u) :=
  IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, h4]; norm_num)

end General
section MinCex
variable [Finite G] {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.le_H (c : MinCex MT Ω K S R W H) : K ≤ H := by
  obtain ⟨z, hz, hcz⟩ := c.exists_centralizer_le
  intro k hk
  apply hcz
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hz.commute_of_mem hk).symm

theorem MinCex.mem_of_conjSub_le (c : MinCex MT Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {g : G} (hg : conjSub g R ≤ H) : g ∈ H := by
  obtain ⟨u, huR, hu4⟩ :=
    c.stand.hyp.exists_orderOf_eq_four_of_mem_RSet c.stand.hR.1
  exact c.mem_of_conj_mem hA hM (c.stand.hR.2.1 huR) hu4 (hg (conj_mem_conjSub huR))

theorem MinCex.normalizer_le_of_le (c : MinCex MT Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {Y : Subgroup G} (hRY : R ≤ Y) (hYH : Y ≤ H) :
    Subgroup.normalizer (Y : Set G) ≤ H :=
  E187C.normalizer_le_of_le_of (fun hg => c.mem_of_conjSub_le hA hM hg) hRY hYH

theorem MinCex.exists_orderOf_four_mem_W (c : MinCex MT Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {J T : Subgroup G} (hJ : J ∈ Ω) (hT : IsSylow2In T J)
    (hTS : T ≤ (S : Subgroup G)) : ∃ u ∈ J ⊓ W, orderOf u = 4 ∧ u ∈ T := by
  exact E187C.exists_orderOf_four_mem_W_of hM (c.exists_eta hA) hJ hT hTS
    (fun hQ => c.stand.hyp.eight_le_of_mem_RSet hQ)
    (fun hU => by
      obtain ⟨-, -, -, -, -, -, hcyc, -, h4⟩ := c.stand.hyp.exists_data_of_mem_USet hU
      exact ⟨hcyc, h4⟩)
    (fun hU => c.stand.hyp.isPGroup_of_mem_USet hU)

theorem MinCex.exists_fourGroup (c : MinCex MT Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {K' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hK'ne : K' ≠ K)
    {R' : Subgroup G} (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) :
    ∃ U : Subgroup G, U ≤ R ⊔ R' ∧ U ≤ W ∧ (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) ∧
      (∀ x ∈ U, x * x = 1) ∧ 4 ≤ Nat.card U ∧
      ∀ e ∈ U, e ≠ 1 → Subgroup.centralizer ({e} : Set G) ≤ H := by
  have hΩ : HM MT Ω := c.stand.hyp
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  exact E187C.exists_fourGroup_of
    (fun hJ hT hTS => c.exists_orderOf_four_mem_W hA hM hJ hT hTS)
    (by obtain ⟨-, -, -, -, habel, -⟩ := c.exists_eta hA; exact habel)
    (fun hK hR hRK => hΩ.isSylow2In_of_mem_RSet_of_le hK hR hRK)
    (fun hK hJ hA hcard hAK hAJ => hΩ.eq_of_le_of_le hK hJ hA hcard hAK hAJ)
    (fun hK hJ hKJ hzK hzJ => hΩ.le_normalizer_of_twin hK hJ hKJ hzK hzJ)
    (fun hK hJ hKJ hzK hzJ hA hB hAB =>
      hΩ.commutes_of_twin_of_isPGroup hK hJ hKJ hzK hzJ hA hB hAB)
    (fun hz hJ hR₂ hR₂J hcomm a ha _ ha1 ha2 =>
      c.hyp.cent K ⟨c.stand.mem, _, hz, hz⟩ _ hJ R _ hRR hRK hR₂ hR₂J (Or.inl hcomm) a ha ha1 ha2)
    c.stand.mem hRR hRK hRS hK' hK'ne hR' hR'K' hR'S

theorem MinCex.oddCoreOf_le (c : MinCex MT Ω K S R W H) (hA : EtaAbelian Ω) (hM : EtaMeet Ω)
    {K' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hK'ne : K' ≠ K) {R' : Subgroup G}
    (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) {Y : Subgroup G}
    (hY : R ⊔ R' ≤ Y) : oddCoreOf Y ≤ H := by
  obtain ⟨U, hUR, -, hcomm, hsq, hU4, hC⟩ := c.exists_fourGroup hA hM hK' hK'ne hR' hR'K' hR'S
  have hUY : U ≤ Y := hUR.trans hY
  have : IsMulCommutative ↥U := ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩
  exact CFSG.Goldschmidt.LemmaX.le_of_forall_inf_centralizer_le (E := U) (N := oddCoreOf Y)
    (J := H) this (fun x hx => by rw [pow_two]; exact hsq x hx) hU4
    (fun u hu => mem_normalizer_oddCoreOf (hUY hu)) (odd_natCard_oddCoreOf Y)
    (fun e he he1 => inf_le_right.trans (hC e he he1))

end MinCex
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem omegaNbr_subgroupOf [Finite G] (hΩ : HM MT Ω) {Y K J : Subgroup G}
    (hKY : K ≤ Y) (hJY : J ≤ Y) (hJ : J ∈ Ω) (h : J ∈ omegaNbr Ω K) :
    J.subgroupOf Y ∈ omegaNbr (restrictFamily Ω Y) (K.subgroupOf Y) :=
  E187C.omegaNbr_subgroupOf_of (fun hJ hT hTJ => hΩ.isSylow2In_of_mem_RSet_of_le hJ hT hTJ) hKY hJY
    hJ h

theorem AEmpty.restrict [Finite G] (hΩ : HM MT Ω) {Y K : Subgroup G}
    (hKY : K ≤ Y) (hA : AEmpty Ω K) : AEmpty (restrictFamily Ω Y) (K.subgroupOf Y) :=
  E187C.AEmpty.restrict_of (fun hJ hT hTJ => hΩ.isSylow2In_of_mem_RSet_of_le hJ hT hTJ) hKY hA

end Asc77
end
end CFSG.ClassicalInvolution.T7FU

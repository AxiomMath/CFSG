module

public import CFSG.GH74.GLS.C3.Layer1.Th2P61Wrap

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_pRank_le_four_cent (hG4 : pRank 2 G ≤ 4) {b : G} (hb2 : orderOf b = 2)
    {J : Subgroup G} (hJ : IsPCompIn 2 (centralizer ({b} : Set G)) J) (hJcen : CenterlessBar J)
    (hJ2 : 2 ≤ pRank 2 ↥J) {β : G} (hβC : β ∈ centralizer ({b} : Set G)) :
    β ∈ normalizer (J : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hβJ
  have hβb' : β * b = b * β := mem_centralizer_singleton_iff.1 hβC
  have hJ' : IsPCompIn 2 (centralizer ({b} : Set G)) (cj β J) := by
    have := Stage1.Thm2.Recip.isPCompIn_map_conj hJ β
    rwa [C3.Layer1.Thm1.map_conj_eq_self_of_mem hβC] at this
  have hne : cj β J ≠ J := fun h => hβJ (mem_normalizer_of_cj_eq h)
  have hle : cj β J ≤ centralizerSection J (pPrimeCoreOf 2 J) :=
    Stage1.Thm2.Recip.le_cSec_of_ne hJ' hJ hne
  obtain ⟨E₀, hE₀J, hE₀el, hE₀rk⟩ := exists_elemAbelian_pRank J
  have hEβel : CFSG.IsElementaryAbelian 2 ↥(cj β E₀) := isElementaryAbelian_cj β hE₀el
  have hEβrk : pRank 2 ↥(cj β E₀) = pRank 2 ↥J := by rw [pRank_cj, hE₀rk]
  have hEβJ' : cj β E₀ ≤ cj β J := Subgroup.map_mono hE₀J
  have hEβle : cj β E₀ ≤ centralizerSection J (pPrimeCoreOf 2 J) := hEβJ'.trans hle
  have hbJc : ∀ k ∈ J, b * k = k * b := fun k hk => (mem_centralizer_singleton_iff.1 (hJ.1 hk)).symm
  have hbEc : ∀ e ∈ cj β E₀, b * e = e * b := fun e he =>
    (mem_centralizer_singleton_iff.1 (hJ'.1 (hEβJ' he))).symm
  have hbEβ : b ∉ cj β E₀ := by
    intro hbE
    rw [mem_cj_iff] at hbE
    have hβb : β⁻¹ * b * β = b := by
      calc β⁻¹ * b * β = β⁻¹ * (b * β) := by group
        _ = β⁻¹ * (β * b) := by rw [hβb']
        _ = b := by group
    rw [hβb] at hbE
    have hbJ : b ∈ J := hE₀J hbE
    have hbO : b ∈ pPrimeCoreOf 2 J := by
      refine mem_pPrimeCoreOf_of_commutators hJcen hbJ (fun k hk => ?_)
      have : ⁅k, b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hbJc k hk).symm
      rw [this]
      exact one_mem _
    have hodd : Odd (orderOf b) :=
      Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd J) (Subgroup.orderOf_dvd_natCard _ hbO)
    rw [hb2] at hodd
    exact absurd hodd (by decide)
  have hcd : CommDisj (zpowers b) (cj β E₀) := by
    refine ⟨fun p hp q hq => ?_, ?_⟩
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hp
      exact (Commute.zpow_left (show Commute b q from hbEc q hq) m).eq
    · refine eq_bot_iff.2 fun z hz => ?_
      rcases mem_zpowers_two hb2 hz.1 with h0 | h0
      · simp [h0]
      · exact absurd (h0 ▸ hz.2) hbEβ
  have hbel := Th2.isElementaryAbelian_zpowers_of_orderOf_two hb2
  have hW₀el : CFSG.IsElementaryAbelian 2 ↥(zpowers b ⊔ cj β E₀) :=
    hcd.isElementaryAbelian_sup' hbel hEβel le_rfl le_rfl
  have hW₀rk : pRank 2 ↥(zpowers b ⊔ cj β E₀) = 1 + pRank 2 ↥J := by
    rw [hcd.pRank_sup hbel hEβel le_rfl le_rfl, Th2.pRank_zpowers_of_orderOf_two hb2, hEβrk]
  have hbcs : b ∈ centralizerSection J (pPrimeCoreOf 2 J) :=
    C3.Layer1.Back.mem_centralizerSection_of_centralizes hbJc (TwoThin.pPrimeCoreOf_le J)
  have hW₀cs : zpowers b ⊔ cj β E₀ ≤ centralizerSection J (pPrimeCoreOf 2 J) :=
    sup_le (zpowers_le.2 hbcs) hEβle
  have hW₀2 : IsPGroup 2 ↥(zpowers b ⊔ cj β E₀) := CFSG.IsElementaryAbelian.isPGroup 2 _
  obtain ⟨S₀, hS₀J, hS₀p, hS₀card, hS₀norm⟩ :=
    IVK.Proofs2.exists_normalized_sylow_two J (zpowers b ⊔ cj β E₀) hW₀2 (fun w hw => (hW₀cs hw).1)
  have hSyl : IsSylowOf 2 S₀ J := isSylowOf_of_card hS₀J hS₀card.symm
  have hS₀W : ∀ e ∈ S₀, ∀ w ∈ zpowers b ⊔ cj β E₀, e * w = w * e := by
    intro e he w hw
    have h1 : ⁅e, w⁆ ∈ pPrimeCoreOf 2 J := (hW₀cs hw).2.2 e (hS₀J he)
    have h2 : ⁅e, w⁆ ∈ S₀ := by
      have := hS₀norm w hw e⁻¹ (S₀.inv_mem he)
      rw [commutatorElement_def]
      have e1 : e * w * e⁻¹ * w⁻¹ = e * (w * e⁻¹ * w⁻¹) := by group
      rw [e1]
      exact S₀.mul_mem he this
    have h3 : ⁅e, w⁆ ∈ S₀ ⊓ pPrimeCoreOf 2 J := ⟨h2, h1⟩
    rw [C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot J hS₀p, Subgroup.mem_bot] at h3
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  obtain ⟨E', hE'S, hE'el, hE'rk⟩ := exists_elemAbelian_pRank S₀
  have hE'rk' : pRank 2 ↥E' = pRank 2 ↥J := by rw [hE'rk, Th2.pRank_eq_of_isSylowOf hSyl]
  have hcd2 : CommDisj E' (zpowers b ⊔ cj β E₀) := by
    refine ⟨fun p hp q hq => hS₀W p (hE'S hp) q hq, ?_⟩
    refine eq_bot_iff.2 fun u hu => ?_
    obtain ⟨huE, huW⟩ := hu
    have huS : u ∈ S₀ := hE'S huE
    have huJ : u ∈ J := hS₀J huS
    have huO : u ∈ pPrimeCoreOf 2 J :=
      mem_pPrimeCoreOf_of_commutators hJcen huJ (fun k hk => (hW₀cs huW).2.2 k hk)
    have h3 : u ∈ S₀ ⊓ pPrimeCoreOf 2 J := ⟨huS, huO⟩
    rw [C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot J hS₀p] at h3
    exact h3
  have hrk := hcd2.pRank_sup hE'el hW₀el le_rfl le_rfl
  have h4 := pRank_le_top' (E' ⊔ (zpowers b ⊔ cj β E₀))
  omega

theorem Obstr52.normalizes_centralizer {B : Subgroup G} {b : G} {J : Subgroup G}
    (h : Obstr52 B b J) (hG4 : pRank 2 G ≤ 4) (hB : CFSG.IsElementaryAbelian 2 ↥B) :
    ∀ g ∈ centralizer ({b} : Set G), g ∈ normalizer (J : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq b h.mem) h.ne_one
  intro g hg
  exact mem_normalizer_of_pRank_le_four_cent hG4 hb2 h.comp h.centerlessBar h.two_le_pRank hg

end CFSG.GH74.GLS.Th2.Obs

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2

@[expose] def B_prop617_obs : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → Nonempty (kBar K ≃* alternatingGroup (Fin 7)) →
      pRank 2 ↥(T ⊓ CxK x K) ≤ 2 → ¬ (Nat.card ↥(T ⊓ CxK x K) = 4 ∧ T < S) →
        ∀ B : Subgroup G, IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B →
          ∀ (b : G) (J : Subgroup G), Th2.Obs.Obstr52 B b J → False

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2

theorem b_prop617b_of_obs
    (hGKF : Generic.GenericKnownFacts) (hE2 : E2.E2ComponentFacts) (hL34 : B_gen4_noL34_elem)
    (h : B_prop617_obs) : B_prop617b := by
  intro G _ _ hG x y K T S hs h7 _ hnc B hB
  by_contra hweak
  have hE : IsE 4 ⊤ B := isE_of_isSn le_top hB le_rfl
  obtain ⟨b, J, hobs⟩ := Th2.Obs.exists_obstr52 hGKF hE2 hL34 hG hE hweak
  have hQ2 : pRank 2 ↥(T ⊓ CxK x K) ≤ 2 := by
    by_contra h3
    push Not at h3
    obtain ⟨e⟩ := h7
    exact false_of_three_le_rank_Q hG hs (centerlessBar_of_A7 ⟨e⟩)
      (rankTwoShape_sylow_A7 hs.sylow_P ⟨e⟩) h3
  exact h G hG x y K T S hs h7 hQ2 hnc B hB b J hobs

end CFSG.GH74.GLS

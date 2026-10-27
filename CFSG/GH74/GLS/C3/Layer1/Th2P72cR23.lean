module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR16

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pRank_add_le_of_le_cSec {J W : Subgroup G} (hJcen : CenterlessBar J)
    (hWel : CFSG.IsElementaryAbelian 2 ↥W)
    (hWcs : W ≤ centralizerSection J (pPrimeCoreOf 2 J)) :
    pRank 2 ↥J + pRank 2 ↥W ≤ pRank 2 G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW2 : IsPGroup 2 ↥W := CFSG.IsElementaryAbelian.isPGroup 2 _
  obtain ⟨S₀, hS₀J, hS₀p, hS₀card, hS₀norm⟩ :=
    IVK.Proofs2.exists_normalized_sylow_two J W hW2 (fun w hw => (hWcs hw).1)
  have hSyl : IsSylowOf 2 S₀ J := isSylowOf_of_card hS₀J hS₀card.symm
  have hS₀W : ∀ e ∈ S₀, ∀ w ∈ W, e * w = w * e := by
    intro e he w hw
    have h1 : ⁅e, w⁆ ∈ pPrimeCoreOf 2 J := (hWcs hw).2.2 e (hS₀J he)
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
  have hcd2 : CommDisj E' W := by
    refine ⟨fun p hp q hq => hS₀W p (hE'S hp) q hq, ?_⟩
    refine eq_bot_iff.2 fun u hu => ?_
    obtain ⟨huE, huW⟩ := hu
    have huS : u ∈ S₀ := hE'S huE
    have huJ : u ∈ J := hS₀J huS
    have huO : u ∈ pPrimeCoreOf 2 J :=
      mem_pPrimeCoreOf_of_commutators hJcen huJ (fun k hk => (hWcs huW).2.2 k hk)
    have h3 : u ∈ S₀ ⊓ pPrimeCoreOf 2 J := ⟨huS, huO⟩
    rw [C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot J hS₀p] at h3
    exact h3
  have hrk := hcd2.pRank_sup hE'el hWel le_rfl le_rfl
  have h4 := pRank_le_top' (E' ⊔ W)
  omega

omit [Finite G] in
theorem conj_mem_cSec {J : Subgroup G} {c n : G} (hc : c ∈ normalizer (J : Set G))
    (hn : n ∈ centralizerSection J (pPrimeCoreOf 2 J)) :
    c * n * c⁻¹ ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
  have hnN : n ∈ normalizer (J : Set G) := hn.1
  have h1 : barAct J ⟨n, hnN⟩ = 1 := (barAct_eq_one_iff _).2 hn
  have hmem : c * n * c⁻¹ ∈ normalizer (J : Set G) :=
    (normalizer (J : Set G)).mul_mem ((normalizer (J : Set G)).mul_mem hc hnN)
      ((normalizer (J : Set G)).inv_mem hc)
  rw [← barAct_eq_one_iff ⟨c * n * c⁻¹, hmem⟩]
  have : (⟨c * n * c⁻¹, hmem⟩ : ↥(normalizer (J : Set G))) = ⟨c, hc⟩ * ⟨n, hnN⟩ * ⟨c, hc⟩⁻¹ :=
    Subtype.ext (by simp)
  rw [this, map_mul, map_mul, map_inv, h1]
  simp

theorem mem_cSec_pumpup_of_mem_cSec {x v g : G} {K M : Subgroup G} (hlt : PumpUpLT 2 x K v M)
    (hxM : x ∈ normalizer (M : Set G)) (e : kBar M ≃* kBar K) (hgM : g ∈ normalizer (M : Set G))
    (hgcK : g ∈ centralizerSection K (pPrimeCoreOf 2 K)) (hgv : g * v = v * g) :
    g ∈ centralizerSection M (pPrimeCoreOf 2 M) := by
  obtain ⟨Θ, hΘ⟩ := exists_theta hlt hxM e
  have hgK : g ∈ normalizer (K : Set G) := hgcK.1
  have hbarK : barAct K ⟨g, hgK⟩ = 1 := (barAct_eq_one_iff _).2 hgcK
  rw [← barAct_eq_one_iff ⟨g, hgM⟩]
  ext c
  have h1 := hΘ g hgM hgK hgv c
  rw [hbarK] at h1
  simp only [MulAut.one_apply] at h1 ⊢
  exact Θ.injective h1

theorem row2_maximality (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2)
    {x y : G} {K T S : Subgroup G} (hstd : Th2Std x y K T S) {B : Subgroup G}
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hxB : x ∈ B)
    (hE2 : pRank 2 ↥(B ⊓ (T ⊓ CxK x K)) = 2) {e : G} (heE : e ∈ B ⊓ (T ⊓ CxK x K))
    (he2 : orderOf e = 2) :
    ∃ N : Subgroup G, B ⊓ (T ⊓ CxK x K) ≤ N ∧
      (∀ c ∈ centralizer ({e} : Set G), ∀ n ∈ N, c * n * c⁻¹ ∈ N) ∧
      ∀ F : Subgroup G, B ⊓ (T ⊓ CxK x K) ≤ F → F ≤ N → CFSG.IsElementaryAbelian 2 ↥F →
        F = B ⊓ (T ⊓ CxK x K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  obtain ⟨M, hlt⟩ := HY.exists_pumpup_at hG hstd heE.2.2 he2
  obtain ⟨⟨eMK⟩, hMcen, hM2, hMN⟩ := hstd.pumpup_facts hG hL34 h102 he2 hlt
  have heB : e ∈ B := heE.1
  have hxM : x ∈ normalizer (M : Set G) :=
    hMN x (mem_centralizer_singleton_iff.2 (hBc x hxB e heB))
  refine ⟨centralizer ({e} : Set G) ⊓ centralizerSection M (pPrimeCoreOf 2 M), ?_, ?_, ?_⟩
  · intro g hg
    have hge : g * e = e * g := hBc g hg.1 e heB
    exact ⟨mem_centralizer_singleton_iff.2 hge,
      mem_cSec_pumpup_of_mem_cSec hlt hxM eMK (hMN g (mem_centralizer_singleton_iff.2 hge))
        hg.2.2.2 hge⟩
  · intro c hc n hn
    have hcN : c ∈ normalizer (M : Set G) := hMN c hc
    refine ⟨?_, conj_mem_cSec hcN hn.2⟩
    exact (centralizer ({e} : Set G)).mul_mem ((centralizer ({e} : Set G)).mul_mem hc hn.1)
      ((centralizer ({e} : Set G)).inv_mem hc)
  · intro F hEF hFN hFel
    have hFcs : F ≤ centralizerSection M (pPrimeCoreOf 2 M) := fun f hf => (hFN hf).2
    have h1 := pRank_add_le_of_le_cSec hMcen hFel hFcs
    have h4 := hG.pRank_eq_four
    have hFle : pRank 2 ↥F ≤ 2 := by omega
    have hcardF := C3.Layer1.Back.card_eq_two_pow_pRank hFel
    have hEel : CFSG.IsElementaryAbelian 2 ↥(B ⊓ (T ⊓ CxK x K)) :=
      isElementaryAbelian_le hBel inf_le_left
    have hcardE := C3.Layer1.Back.card_eq_two_pow_pRank hEel
    have hFE : Nat.card ↥F ≤ Nat.card ↥(B ⊓ (T ⊓ CxK x K)) := by
      rw [hcardF, hcardE, hE2]
      exact Nat.pow_le_pow_right (by norm_num) hFle
    exact (Subgroup.eq_of_le_of_card_ge hEF hFE).symm

end CFSG.GH74.GLS.Th2.Obs

module

public import CFSG.GH74.GLS.C3.Layer1.Th2Conn
public import CFSG.GH74.GLS.C3.Layer1.Th2Main
public import CFSG.GH74.GLS.C3.Layer1.Thm1Normal
public import CFSG.GH74.GLS.C3.Layer1.BackAction
public import CFSG.GH74.GLS.C3.Layer1.Back112A5
import CFSG.GH74.GLS.C3.Layer1.BkA7Facts
public import CFSG.GH74.GLS.C3.Layer1.BkS4Prelim
public import CFSG.GH74.GLS.C3.Layer1.Thm1AutA7
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Th2
open scoped commutatorElement

section Std

variable {G : Type} [Group G] {x y : G} {K T S : Subgroup G}

theorem Th2Std.isIL2 (h : Th2Std x y K T S) : IsIL2Pair x K := h.v2ss.isV2Triple.1.1

theorem Th2Std.orderOf_x (h : Th2Std x y K T S) : orderOf x = 2 := h.isIL2.1

theorem Th2Std.comp (h : Th2Std x y K T S) : IsPCompIn 2 (centralizer ({x} : Set G)) K := h.isIL2.2

theorem Th2Std.K_le_C (h : Th2Std x y K T S) : K ≤ centralizer ({x} : Set G) := h.comp.1

theorem Th2Std.T_le_C (h : Th2Std x y K T S) : T ≤ centralizer ({x} : Set G) :=
  h.setup.sylowT.le

theorem Th2Std.T_pGroup [Finite G] (h : Th2Std x y K T S) : IsPGroup 2 ↥T :=
  h.setup.sylowT.isPGroup

theorem Th2Std.x_mem_T [Finite G] (h : Th2Std x y K T S) : x ∈ T :=
  C3.Layer1.Back.mem_of_isSylowOf_of_central h.setup.sylowT (mem_centralizer_singleton_iff.2 rfl)
    (fun _ hs => mem_centralizer_singleton_iff.1 hs) h.orderOf_x

theorem Th2Std.K_le_NxK (h : Th2Std x y K T S) : K ≤ NxK x K :=
  le_inf h.K_le_C Subgroup.le_normalizer

theorem CxK_le_NxK (x : G) (K : Subgroup G) : CxK x K ≤ NxK x K :=
  le_inf inf_le_left (inf_le_right.trans fun _ hc => hc.1)

theorem Th2Std.x_mem_CxK (h : Th2Std x y K T S) : x ∈ CxK x K := by
  refine ⟨mem_centralizer_singleton_iff.2 rfl, C3.Layer1.Back.mem_centralizerSection_of_centralizes ?_ ?_⟩
  · intro k hk
    exact (mem_centralizer_singleton_iff.1 (h.K_le_C hk)).symm
  · unfold pPrimeCoreOf
    intro z hz
    obtain ⟨z', -, rfl⟩ := hz
    exact z'.2

theorem NxK_mem_normalizer_K {n : G} (hn : n ∈ NxK x K) : ∀ k ∈ K, n * k * n⁻¹ ∈ K :=
  fun k hk => (Subgroup.mem_normalizer_iff.1 hn.2 k).1 hk

theorem NxK_le_normalizer_CxK (x : G) (K : Subgroup G) :
    NxK x K ≤ normalizer (CxK x K : Set G) := by
  intro n hn
  have hnorm : ∀ m ∈ NxK x K, ∀ l ∈ K, m * l * m⁻¹ ∈ K := fun m hm l hl =>
    NxK_mem_normalizer_K hm l hl
  have hCMK : CMK (NxK x K) K = CxK x K := by
    apply le_antisymm
    · exact inf_le_inf_right _ (inf_le_left : NxK x K ≤ centralizer ({x} : Set G))
    · exact le_inf (CxK_le_NxK x K) inf_le_right
  have h1 := Th2.cmk_normal (M := NxK x K) (L := K) hnorm
  rw [hCMK] at h1
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc; exact h1 n hn c hc
  · intro hc
    have := h1 n⁻¹ (Subgroup.inv_mem _ hn) _ hc
    simpa [mul_assoc] using this

theorem Th2Std.sylow_P [Finite G] (h : Th2Std x y K T S) : IsSylowOf 2 (T ⊓ K) K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.setup.sylowT0.inf_of_le_normalizer h.K_le_NxK (fun n hn => hn.2)
  rwa [inf_assoc, inf_eq_right.2 h.K_le_NxK] at this

theorem Th2Std.sylow_Q [Finite G] (h : Th2Std x y K T S) : IsSylowOf 2 (T ⊓ CxK x K) (CxK x K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.setup.sylowT0.inf_of_le_normalizer (CxK_le_NxK x K) (NxK_le_normalizer_CxK x K)
  rwa [inf_assoc, inf_eq_right.2 (CxK_le_NxK x K)] at this

@[expose] def CenterlessBar (K : Subgroup G) : Prop :=
  ∀ a : kBar K, (∀ b : kBar K, a * b = b * a) → a = 1

theorem centerlessBar_of_conj_injective {K : Subgroup G}
    (h : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K))) : CenterlessBar K := by
  intro a ha
  apply h
  rw [map_one]
  ext b
  simp only [MulAut.conj_apply, MulAut.one_apply]
  rw [ha b]; group

theorem centerlessBar_of_hasL2Model {K : Subgroup G} {Pr : ℕ → Prop} (hPr : ∀ q, Pr q → Odd q)
    (h : HasL2Model (kBar K) Pr) : CenterlessBar K := by
  obtain ⟨p, f, hp, hf, hq, hL⟩ := h
  have h' : HasL2Model (kBar K) Odd := ⟨p, f, hp, hf, hPr _ hq, hL⟩
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := C3.Layer1.Thm1.exists_l2_model_of_hasL2Model h'
  exact centerlessBar_of_conj_injective (IVK.conj_injective_of_L2 e)

theorem centerlessBar_of_A7 {K : Subgroup G} (h : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    CenterlessBar K := by
  obtain ⟨e⟩ := h
  exact centerlessBar_of_conj_injective (C3.Layer1.Thm1.conj_injective_of_A7 e)

theorem mk_comm_of_commutator_mem {K : Subgroup G} {k p : K} (hkp : ⁅k, p⁆ ∈ pPrimeCore 2 ↥K) :
    (QuotientGroup.mk k : kBar K) * QuotientGroup.mk p = QuotientGroup.mk p * QuotientGroup.mk k := by
  have h1 : (QuotientGroup.mk ⁅k, p⁆ : kBar K) = 1 := (QuotientGroup.eq_one_iff _).2 hkp
  rw [commutatorElement_def] at h1
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 (by simpa [commutatorElement_def] using h1)

theorem mem_pPrimeCoreOf_of_commutators {K : Subgroup G} (hcen : CenterlessBar K) {p : G}
    (hpK : p ∈ K) (hp : ∀ k ∈ K, ⁅k, p⁆ ∈ pPrimeCoreOf 2 K) : p ∈ pPrimeCoreOf 2 K := by
  have hcomm : ∀ b : kBar K, QuotientGroup.mk (⟨p, hpK⟩ : ↥K) * b =
      b * QuotientGroup.mk (⟨p, hpK⟩ : ↥K) := by
    intro b
    induction b using QuotientGroup.induction_on with | H k => ?_
    obtain ⟨hmem, hO⟩ := C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.1 (hp k k.2)
    have : (⁅k, (⟨p, hpK⟩ : ↥K)⁆ : ↥K) ∈ pPrimeCore 2 ↥K := hO
    exact (mk_comm_of_commutator_mem this).symm
  have h1 := hcen _ hcomm
  have : (⟨p, hpK⟩ : ↥K) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 h1
  exact C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hpK, this⟩

theorem Th2Std.commDisj [Finite G] (h : Th2Std x y K T S) (hcen : CenterlessBar K) :
    CommDisj (T ⊓ K) (T ⊓ CxK x K) := by
  have hT2 := h.T_pGroup
  have hbot := C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot K hT2
  refine ⟨fun p hp q hq => ?_, ?_⟩
  · have h1 : ⁅p, q⁆ ∈ pPrimeCoreOf 2 K := hq.2.2.2.2 p hp.2
    have h2 : ⁅p, q⁆ ∈ T := by
      rw [commutatorElement_def]
      exact T.mul_mem (T.mul_mem (T.mul_mem hp.1 hq.1) (T.inv_mem hp.1)) (T.inv_mem hq.1)
    have h3 : ⁅p, q⁆ ∈ T ⊓ pPrimeCoreOf 2 K := ⟨h2, h1⟩
    rw [hbot, Subgroup.mem_bot] at h3
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  · refine eq_bot_iff.2 fun p hp => ?_
    have hpO : p ∈ pPrimeCoreOf 2 K :=
      mem_pPrimeCoreOf_of_commutators hcen hp.1.2 (fun k hk => hp.2.2.2.2.2 k hk)
    have h3 : p ∈ T ⊓ pPrimeCoreOf 2 K := ⟨hp.1.1, hpO⟩
    rw [hbot] at h3
    exact h3

theorem pRank_le_top' [Finite G] (A : Subgroup G) : pRank 2 ↥A ≤ pRank 2 G := by
  have h1 := C3.Layer1.Back.pRank_mono' (le_top : A ≤ ⊤)
  have h2 : pRank 2 ↥(⊤ : Subgroup G) = pRank 2 G :=
    CFSG.RankThree.PartOne.Quotient36.pRank_congr_mulEquiv one_lt_two (Subgroup.topEquiv (G := G))
  rw [h2] at h1
  exact h1

theorem Th2.exists_cj_le_of_isSylowOf [Finite G] {H Q W : Subgroup G} (hQ : IsSylowOf 2 Q H)
    (hWH : W ≤ H) (hW : IsPGroup 2 ↥W) : ∃ g ∈ H, cj g W ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW' : IsPGroup 2 ↥(W.subgroupOf H) := hW.comap_subtype
  obtain ⟨S, hS⟩ := hW'.exists_le_sylow
  have hS' : IsSylowOf 2 ((S : Subgroup ↥H).map H.subtype) H := ⟨S, rfl⟩
  obtain ⟨k, hk, hconj⟩ := hQ.exists_mem_conj hS'
  refine ⟨k⁻¹, H.inv_mem hk, ?_⟩
  intro b hb
  rw [mem_cj_iff] at hb
  have hw : k * b * k⁻¹ ∈ (S : Subgroup ↥H).map H.subtype := by
    refine ⟨⟨k * b * k⁻¹, hWH (by simpa using hb)⟩, hS ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    simpa using hb
  have := (hconj _).1 hw
  simpa [mul_assoc] using this

public theorem normal_of_card_sylow_cSec_lt {G : Type} [Group G] [Finite G]
    {M K P Q : Subgroup G}
    (hK : IsPCompIn 2 M K) (hPleK : P ≤ K) (hP2 : IsPGroup 2 ↥P)
    (hQ : IsSylowOf 2 Q (M ⊓ centralizerSection K (pPrimeCoreOf 2 K)))
    (hcard : Nat.card ↥Q < Nat.card ↥P) :
    ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K := by
  intro m hm k hk
  by_contra hmk
  have hMconj : M.map (MulAut.conj m).toMonoidHom = M :=
    C3.Layer1.Thm1.map_conj_eq_self_of_mem hm
  have hK' : IsPCompIn 2 M (K.map (MulAut.conj m).toMonoidHom) := by
    have := Stage1.Thm2.Recip.isPCompIn_map_conj hK m
    rwa [hMconj] at this
  have hne : K.map (MulAut.conj m).toMonoidHom ≠ K := by
    intro h0
    apply hmk
    have hmem : m * k * m⁻¹ ∈ K.map (MulAut.conj m).toMonoidHom :=
      ⟨k, hk, by simp [MulAut.conj_apply]⟩
    rwa [h0] at hmem
  have hle : K.map (MulAut.conj m).toMonoidHom ≤
      centralizerSection K (pPrimeCoreOf 2 K) :=
    Stage1.Thm2.Recip.le_cSec_of_ne hK' hK hne
  have hPm2 : IsPGroup 2 ↥(P.map (MulAut.conj m).toMonoidHom) :=
    hP2.map (MulAut.conj m).toMonoidHom
  have hPmH : P.map (MulAut.conj m).toMonoidHom ≤
      M ⊓ centralizerSection K (pPrimeCoreOf 2 K) :=
    le_inf ((Subgroup.map_mono hPleK).trans hK'.1)
      ((Subgroup.map_mono hPleK).trans hle)
  obtain ⟨g, -, hgQ⟩ := Th2.exists_cj_le_of_isSylowOf hQ hPmH hPm2
  have hcard_m : Nat.card ↥(P.map (MulAut.conj m).toMonoidHom) = Nat.card ↥P :=
    Subgroup.card_map_of_injective (MulAut.conj m).injective
  have hcard_gm : Nat.card ↥((P.map (MulAut.conj m).toMonoidHom).map
      (MulAut.conj g).toMonoidHom) = Nat.card ↥(P.map (MulAut.conj m).toMonoidHom) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hle_card : Nat.card ↥((P.map (MulAut.conj m).toMonoidHom).map
      (MulAut.conj g).toMonoidHom) ≤ Nat.card ↥Q := Subgroup.card_le_of_le hgQ
  rw [hcard_gm, hcard_m] at hle_card
  omega

public theorem Th2Std.K_normal_of_card_Q_lt_card_P [Finite G]
    {x y : G} {K T S : Subgroup G} (h : Th2Std x y K T S)
    (hcard : Nat.card ↥(T ⊓ CxK x K) < Nat.card ↥(T ⊓ K)) :
    ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
  refine normal_of_card_sylow_cSec_lt h.comp (inf_le_right : T ⊓ K ≤ K)
    h.sylow_P.isPGroup ?_ hcard
  simpa [CxK] using h.sylow_Q

public theorem Th2Std.K_normal_of_A7_card_Q_four [Finite G]
    {x y : G} {K T S : Subgroup G} (h : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) :
    Nat.card ↥(T ⊓ K) = 8 ∧
      ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
  have hD8 := CFSG.GH74.GLS.C3.Layer1.Bk.isD8_of_inf_alt7 h.T_pGroup h.sylow_P e7
  have hP8 : Nat.card ↥(T ⊓ K) = 8 := hD8.card_eq
  exact ⟨hP8, Th2Std.K_normal_of_card_Q_lt_card_P h (by omega)⟩

theorem mem_zpowers_two {x z : G} (hx : orderOf x = 2) (hz : z ∈ zpowers x) : z = 1 ∨ z = x := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hz
  have h1 : x ^ (n % (orderOf x : ℤ)) = x ^ n := zpow_mod_orderOf x n
  rw [hx] at h1
  rcases Int.emod_two_eq_zero_or_one n with h0 | h0
  · left; simpa [h0] using h1.symm
  · right; simpa [h0] using h1.symm

theorem Th2Std.K_normal [Finite G] (hG4 : pRank 2 G ≤ 4) (h : Th2Std x y K T S)
    (hcen : CenterlessBar K) (hP : 2 ≤ pRank 2 ↥(T ⊓ K)) :
    ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
  intro c hc k hk
  by_contra hkc
  have hK := h.comp
  have hK' : IsPCompIn 2 (centralizer ({x} : Set G)) (cj c K) := by
    have := Stage1.Thm2.Recip.isPCompIn_map_conj hK c
    rwa [C3.Layer1.Thm1.map_conj_eq_self_of_mem hc] at this
  have hne : cj c K ≠ K := by
    intro h0
    apply hkc
    have hmem : c * k * c⁻¹ ∈ cj c K := ⟨k, hk, by simp [MulAut.conj_apply]⟩
    rwa [h0] at hmem
  have hle : cj c K ≤ CxK x K := le_inf hK'.1 (Stage1.Thm2.Recip.le_cSec_of_ne hK' hK hne)
  obtain ⟨E, hEP, hEel, hErk⟩ := exists_elemAbelian_pRank (T ⊓ K)
  have hE2 : 2 ≤ pRank 2 ↥E := hErk ▸ hP
  have hE'K : cj c E ≤ cj c K := Subgroup.map_mono (hEP.trans inf_le_right)
  have hE'el := isElementaryAbelian_cj c hEel
  have hE'rk : pRank 2 ↥(cj c E) = pRank 2 ↥E := pRank_cj c E
  have hxE' : x ∉ cj c E := by
    intro hxE
    have hx1 : c⁻¹ * x * c ∈ K := (mem_cj_iff c K x).1 (hE'K hxE)
    have hcx : c⁻¹ * x * c = x := by
      have := mem_centralizer_singleton_iff.1 hc
      calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
        _ = c⁻¹ * (c * x) := by rw [this]
        _ = x := by group
    rw [hcx] at hx1
    have hxO : x ∈ pPrimeCoreOf 2 K := by
      refine mem_pPrimeCoreOf_of_commutators hcen hx1 (fun k' hk' => ?_)
      have hk'x : k' * x = x * k' := by
        have := mem_centralizer_singleton_iff.1 (h.K_le_C hk')
        exact this
      rw [commutatorElement_def, hk'x]
      simp
    have hbot := C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot K h.T_pGroup
    have h3 : x ∈ T ⊓ pPrimeCoreOf 2 K := ⟨h.x_mem_T, hxO⟩
    rw [hbot, Subgroup.mem_bot] at h3
    have := h.orderOf_x
    rw [h3, orderOf_one] at this
    omega
  have hxel : CFSG.IsElementaryAbelian 2 ↥(zpowers x) := by
    have : x ^ 2 = 1 := by rw [pow_two]; exact mul_self_eq_one_of_orderOf_eq_two h.orderOf_x
    exact CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one this
  have hcd : CommDisj (cj c E) (zpowers x) := by
    refine ⟨fun e he t ht => ?_, ?_⟩
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ht
      have : e ∈ centralizer ({x} : Set G) := hK'.1 (hE'K he)
      exact (Commute.zpow_right (mem_centralizer_singleton_iff.1 this) m).symm.eq.symm
    · refine eq_bot_iff.2 fun z hz => ?_
      rcases mem_zpowers_two h.orderOf_x hz.2 with h0 | h0
      · simp [h0]
      · exact absurd (h0 ▸ hz.1) hxE'
  have hFel := hcd.isElementaryAbelian_sup' hE'el hxel le_rfl le_rfl
  have hrx : pRank 2 ↥(zpowers x) = 1 := by
    have hc : Nat.card ↥(zpowers x) = 2 := by rw [Nat.card_zpowers]; exact h.orderOf_x
    have h2 := C3.Layer1.Back.card_eq_two_pow_pRank hxel
    rw [hc] at h2
    have : (2 : ℕ) ^ 1 = 2 ^ pRank 2 ↥(zpowers x) := by simpa using h2
    exact (Nat.pow_right_injective le_rfl this).symm
  have hFrk : pRank 2 ↥(cj c E ⊔ zpowers x) = pRank 2 ↥E + 1 := by
    rw [hcd.pRank_sup hE'el hxel le_rfl le_rfl, hE'rk, hrx]
  have hFC : cj c E ⊔ zpowers x ≤ CxK x K :=
    sup_le (hE'K.trans hle) (zpowers_le.2 h.x_mem_CxK)
  have hFp : IsPGroup 2 ↥(cj c E ⊔ zpowers x) := CFSG.IsElementaryAbelian.isPGroup 2 _
  obtain ⟨g, hgC, hgF⟩ := Th2.exists_cj_le_of_isSylowOf h.sylow_Q hFC hFp
  have hWel := isElementaryAbelian_cj g hFel
  have hWrk : pRank 2 ↥(cj g (cj c E ⊔ zpowers x)) = pRank 2 ↥E + 1 := by
    rw [pRank_cj, hFrk]
  have hPQ := h.commDisj hcen
  have hsup := hPQ.pRank_sup hEel hWel hEP hgF
  have h4 := pRank_le_top' (E ⊔ cj g (cj c E ⊔ zpowers x))
  omega

theorem Th2Std.card_T_le_of_A5 [Finite G] (h : Th2Std x y K T S)
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (e5 : kBar K ≃* alternatingGroup (Fin 5)) :
    Nat.card ↥T ≤ 8 * Nat.card ↥(T ⊓ CxK x K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hker⟩ := C3.Layer1.Back.lemma113d_ne6 (M := centralizer ({x} : Set G)) h.K_le_C hKN
    (by norm_num) (by norm_num) e5
  have hTC : T ≤ centralizer ({x} : Set G) := h.T_le_C
  let φ : ↥(T.subgroupOf (centralizer ({x} : Set G))) →* Equiv.Perm (Fin 5) :=
    ψ.comp (T.subgroupOf (centralizer ({x} : Set G))).subtype
  have hTpM : IsPGroup 2 ↥(T.subgroupOf (centralizer ({x} : Set G))) :=
    h.T_pGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hTC).symm
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card ↥φ.range ∣ 8 := C3.Layer1.Back.card_perm_five_dvd_two_part φ hTpM
  have hmemQ : ∀ t : ↥φ.ker,
      (((t : ↥(T.subgroupOf (centralizer ({x} : Set G)))) : ↥(centralizer ({x} : Set G))) : G) ∈
        T ⊓ CxK x K := by
    intro t
    have ht : φ (t : ↥(T.subgroupOf (centralizer ({x} : Set G)))) = 1 := t.2
    have h3 : ((t : ↥(T.subgroupOf (centralizer ({x} : Set G)))) : ↥(centralizer ({x} : Set G))) ∈
        ψ.ker := ht
    rw [hker, Subgroup.mem_subgroupOf] at h3
    have h4 : (((t : ↥(T.subgroupOf (centralizer ({x} : Set G)))) :
        ↥(centralizer ({x} : Set G))) : G) ∈ T :=
      Subgroup.mem_subgroupOf.1 (t : ↥(T.subgroupOf (centralizer ({x} : Set G)))).2
    exact ⟨h4, h3⟩
  let f : ↥φ.ker → ↥(T ⊓ CxK x K) := fun t =>
    ⟨(((t : ↥(T.subgroupOf (centralizer ({x} : Set G)))) : ↥(centralizer ({x} : Set G))) : G),
      hmemQ t⟩
  have hf : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact this
  have h6 : Nat.card ↥φ.ker ≤ Nat.card ↥(T ⊓ CxK x K) := Nat.card_le_card_of_injective f hf
  have h7 : Nat.card ↥φ.range ≤ 8 := Nat.le_of_dvd (by norm_num) h2
  have h8 : Nat.card ↥T = Nat.card ↥(T.subgroupOf (centralizer ({x} : Set G))) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv).symm
  rw [h8, ← h1]
  calc Nat.card ↥φ.ker * Nat.card ↥φ.range ≤ Nat.card ↥(T ⊓ CxK x K) * 8 := Nat.mul_le_mul h6 h7
    _ = 8 * Nat.card ↥(T ⊓ CxK x K) := by ring

end Std

end CFSG.GH74.GLS

module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.GLS.C3.Layer1.Th2HYStruct
public import CFSG.GH74.GLS.C3.Layer1.Th2L84
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.GH74.GLS.Th2.NV7

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.HY
  CFSG.GH74.GLS.C3.Layer1.Back
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S V : Subgroup G}

theorem pPrimeCoreOf_HV (hG : C3Hyp G) (hS : HYSetup x y K T S V) :
    pPrimeCoreOf 2 (HV K V) = OV V := by
  refine le_antisymm ?_ ?_
  · show pPrimeCoreOf 2 (HV K V) ≤ pPrimeCoreOf 2 (normalizer (V : Set G))
    refine le_pPrimeCoreOf_of_norm ((TwoThin.pPrimeCoreOf_le _).trans (HYSetup.HV_le_N K V)) ?_
      (TwoThin.card_pPrimeCoreOf_odd _)
    intro n hn o ho
    exact C3.Layer1.U1a.pPrimeCoreOf_norm (hS.hnormH hG) hn ho
  · refine le_pPrimeCoreOf_of_norm le_sup_right ?_ (TwoThin.card_pPrimeCoreOf_odd _)
    intro h hh o ho
    exact HYSetup.OV_norm V h (HYSetup.HV_le_N K V hh) o ho

theorem exists_thetaHK (hG : C3Hyp G) (hS : HYSetup x y K T S V) :
    ∃ θ : kBar (HV K V) ≃* kBar K, ∀ (l : G) (hH : l ∈ HV K V) (hK : l ∈ K), l ∈ lamV K V →
      θ (QuotientGroup.mk (⟨l, hH⟩ : ↥(HV K V))) = QuotientGroup.mk (⟨l, hK⟩ : ↥K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLK : lamV K V ≤ K := (twoGen_le _).trans inf_le_left
  have hLH : lamV K V ≤ HV K V := le_sup_left
  let fH : ↥(lamV K V) →* kBar (HV K V) :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥(HV K V))).comp (Subgroup.inclusion hLH)
  let fK : ↥(lamV K V) →* kBar K :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion hLK)
  have hfK : Function.Surjective fK := by
    intro b
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨l, hl, o, ho, hk⟩ := hS.lam_cover k k.2
    refine ⟨⟨l, hl⟩, ?_⟩
    show (QuotientGroup.mk ⟨l, hLK hl⟩ : kBar K) = QuotientGroup.mk k
    rw [QuotientGroup.eq]
    obtain ⟨hoK, hocore⟩ := Setup91.mem_pPrimeCoreOf_iff.1 ho
    have : (⟨l, hLK hl⟩ : ↥K)⁻¹ * k = ⟨o, hoK⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hk]; group
    rw [this]
    exact hocore
  have hfH : Function.Surjective fH := by
    intro b
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨l, hl, o, ho, hho⟩ :=
      (mem_sup_iff_mul_of_le_normalizer (HYSetup.lamV_le_normalizer_OV K V)).1 h.2
    refine ⟨⟨l, hl⟩, ?_⟩
    show (QuotientGroup.mk ⟨l, hLH hl⟩ : kBar (HV K V)) = QuotientGroup.mk h
    rw [QuotientGroup.eq]
    have hoO : o ∈ pPrimeCoreOf 2 (HV K V) := (pPrimeCoreOf_HV hG hS).symm ▸ ho
    obtain ⟨hoH, hocore⟩ := Setup91.mem_pPrimeCoreOf_iff.1 hoO
    have : (⟨l, hLH hl⟩ : ↥(HV K V))⁻¹ * h = ⟨o, hoH⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hho]; group
    rw [this]
    exact hocore
  have hH1 : ∀ l : ↥(lamV K V), fH l = 1 ↔ (l : G) ∈ OV V := by
    intro l
    show (QuotientGroup.mk (⟨l, hLH l.2⟩ : ↥(HV K V)) : kBar (HV K V)) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro h
      have : (l : G) ∈ pPrimeCoreOf 2 (HV K V) := Setup91.mem_pPrimeCoreOf_iff.2 ⟨hLH l.2, h⟩
      rwa [pPrimeCoreOf_HV hG hS] at this
    · intro h
      have : (l : G) ∈ pPrimeCoreOf 2 (HV K V) := by rwa [pPrimeCoreOf_HV hG hS]
      exact (Setup91.mem_pPrimeCoreOf_iff.1 this).2
  have hK1 : ∀ l : ↥(lamV K V), fK l = 1 ↔ (l : G) ∈ pPrimeCoreOf 2 K := by
    intro l
    show (QuotientGroup.mk (⟨l, hLK l.2⟩ : ↥K) : kBar K) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact Setup91.mem_pPrimeCoreOf_iff.2 ⟨hLK l.2, h⟩
    · intro h
      exact (Setup91.mem_pPrimeCoreOf_iff.1 h).2
  have hker : fH.ker = fK.ker := by
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hH1, hK1]
    constructor
    · intro h
      exact hS.lam_inf_O_le ⟨l.2, h⟩
    · intro h
      exact hS.lam_inf_OK_le_OV hG ⟨l.2, h⟩
  let eH := QuotientGroup.quotientKerEquivOfSurjective fH hfH
  let eK := QuotientGroup.quotientKerEquivOfSurjective fK hfK
  have hθ : ∀ z : ↥(lamV K V),
      (eH.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker).trans eK)) (fH z) = fK z := by
    intro z
    show eK (QuotientGroup.quotientMulEquivOfEq hker (eH.symm (fH z))) = fK z
    have h1 : eH.symm (fH z) = (QuotientGroup.mk z : ↥(lamV K V) ⧸ fH.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [h1, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  refine ⟨eH.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker).trans eK), ?_⟩
  intro l hH hK hl
  exact hθ ⟨l, hl⟩

theorem isDSub_HV (hG : C3Hyp G) (hS : HYSetup x y K T S V) {U : Subgroup G}
    (hU : IsDSub K (T ⊓ K) U) : IsDSub (HV K V) (T ⊓ K) U := by
  obtain ⟨hUP, hPK, hel, hcard, e, he⟩ := hU
  obtain ⟨θ, hθ⟩ := exists_thetaHK hG hS
  have hPH : T ⊓ K ≤ HV K V := hS.P_le_lamV.trans le_sup_left
  refine ⟨hUP, hPH, hel, hcard, θ.trans e, ?_⟩
  rw [← he]
  congr 1
  ext i
  constructor
  · rintro ⟨d, hd, hdH, hi⟩
    have hdP : d ∈ T ⊓ K := hUP hd
    refine ⟨d, hd, hPK hdP, ?_⟩
    rw [MulEquiv.trans_apply, hθ d hdH (hPK hdP) (hS.P_le_lamV hdP)] at hi
    exact hi
  · rintro ⟨d, hd, hdK, hi⟩
    have hdP : d ∈ T ⊓ K := hUP hd
    refine ⟨d, hd, hPH hdP, ?_⟩
    rw [MulEquiv.trans_apply, hθ d (hPH hdP) hdK (hS.P_le_lamV hdP)]
    exact hi

theorem eq_one_of_mem_T_OV (hS : HYSetup x y K T S V) {q : G} (hqT : q ∈ T) (hqO : q ∈ OV V) :
    q = 1 := by
  have h3 : q ∈ T ⊓ OV V := ⟨hqT, hqO⟩
  rw [Setup91.inf_pPrimeCoreOf_eq_bot (normalizer (V : Set G)) hS.std.T_pGroup,
    Subgroup.mem_bot] at h3
  exact h3

theorem inf_HV_eq (hG : C3Hyp G) (hS : HYSetup x y K T S V) :
    ((T ⊓ K) ⊔ (normalizer (V : Set G) ⊓ (T ⊓ CxK x K))) ⊓ HV K V = T ⊓ K := by
  have hPQ := hS.std.commDisj hS.cen
  have hPH : T ⊓ K ≤ HV K V := hS.P_le_lamV.trans le_sup_left
  refine le_antisymm ?_ (le_inf le_sup_left hPH)
  rintro s ⟨hs, hsH⟩
  obtain ⟨p, hp, q, hq, rfl⟩ :=
    C3.Layer1.Bk.mem_sup_of_commute (A := T ⊓ K) (B := normalizer (V : Set G) ⊓ (T ⊓ CxK x K))
      (fun a ha b hb => hPQ.comm a ha b hb.2) hs
  have hqH : q ∈ HV K V := by
    have := (HV K V).mul_mem ((HV K V).inv_mem (hPH hp)) hsH
    simpa using this
  have hqO : q ∈ OV V := hS.HV_inf_YV_le_OV hG ⟨hqH, hS.Q₁_le_YV hG hq⟩
  have hq1 : q = 1 := eq_one_of_mem_T_OV hS hq.2.1 hqO
  rw [hq1, mul_one]
  exact hp

theorem inf_YV_eq (hG : C3Hyp G) (hS : HYSetup x y K T S V) :
    ((T ⊓ K) ⊔ (normalizer (V : Set G) ⊓ (T ⊓ CxK x K))) ⊓ YV K V =
      normalizer (V : Set G) ⊓ (T ⊓ CxK x K) := by
  have hPQ := hS.std.commDisj hS.cen
  have hPH : T ⊓ K ≤ HV K V := hS.P_le_lamV.trans le_sup_left
  refine le_antisymm ?_ (le_inf le_sup_right (hS.Q₁_le_YV hG))
  rintro s ⟨hs, hsY⟩
  obtain ⟨p, hp, q, hq, rfl⟩ :=
    C3.Layer1.Bk.mem_sup_of_commute (A := T ⊓ K) (B := normalizer (V : Set G) ⊓ (T ⊓ CxK x K))
      (fun a ha b hb => hPQ.comm a ha b hb.2) hs
  have hqY : q ∈ YV K V := hS.Q₁_le_YV hG hq
  have hpY : p ∈ YV K V := by
    have := (YV K V).mul_mem hsY ((YV K V).inv_mem hqY)
    simpa using this
  have hpO : p ∈ OV V := hS.HV_inf_YV_le_OV hG ⟨hPH hp, hpY⟩
  have hp1 : p = 1 := eq_one_of_mem_T_OV hS hp.1 hpO
  rw [hp1, one_mul]
  exact hq

theorem mem_normalizer_P_Q₁ (hG : C3Hyp G) (hS : HYSetup x y K T S V) {m : G}
    (hmN : m ∈ normalizer (V : Set G))
    (hmS : m ∈ normalizer
      ((((T ⊓ K) ⊔ (normalizer (V : Set G) ⊓ (T ⊓ CxK x K)) : Subgroup G)) : Set G)) :
    m ∈ normalizer ((T ⊓ K : Subgroup G) : Set G) ∧
      m ∈ normalizer ((normalizer (V : Set G) ⊓ (T ⊓ CxK x K) : Subgroup G) : Set G) := by
  have hmH : m ∈ normalizer ((HV K V : Subgroup G) : Set G) := hS.mem_normalizer_HV hG hmN
  have hmY : m ∈ normalizer ((YV K V : Subgroup G) : Set G) :=
    C3.Layer1.U1a.mem_normalizer_of_norm (hS.YV_norm hG) hmN
  constructor
  · have := Th2.mem_normalizer_inf' hmS hmH
    rwa [inf_HV_eq hG hS] at this
  · have := Th2.mem_normalizer_inf' hmS hmY
    rwa [inf_YV_eq hG hS] at this

theorem conj_mem_U (hG : C3Hyp G) (hS : HYSetup x y K T S V) {U : Subgroup G}
    (hU : IsDSub K (T ⊓ K) U) {m : G} (hmN : m ∈ normalizer (V : Set G))
    (hmP : m ∈ normalizer ((T ⊓ K : Subgroup G) : Set G)) : ∀ u ∈ U, m * u * m⁻¹ ∈ U := by
  have hUH := isDSub_HV hG hS hU
  have hm := CFSG.GH74.GLS.isDSub_conj (hS.mem_normalizer_HV hG hmN) hmP hUH
  have heq := CFSG.GH74.GLS.Th2.isDSub_unique hS.P_sylow_HV hUH hm
  intro u hu
  have : m * u * m⁻¹ ∈ U.map (MulAut.conj m).toMonoidHom :=
    ⟨u, hu, by simp [MulAut.conj_apply]⟩
  rwa [← heq] at this

theorem mem_M_of_normalizes_S₀ (hG : C3Hyp G) (hS : HYSetup x y K T S V) {M U : Subgroup G}
    (hU : IsDSub K (T ⊓ K) U)
    (hUQ₁ : normalizer ((U ⊔ (normalizer (V : Set G) ⊓ (T ⊓ CxK x K)) : Subgroup G) : Set G) ≤ M)
    {m : G} (hmN : m ∈ normalizer (V : Set G))
    (hmS : m ∈ normalizer
      ((((T ⊓ K) ⊔ (normalizer (V : Set G) ⊓ (T ⊓ CxK x K)) : Subgroup G)) : Set G)) : m ∈ M := by
  obtain ⟨hmP, hmQ⟩ := mem_normalizer_P_Q₁ hG hS hmN hmS
  have hmU : m ∈ normalizer (U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨fun hu => conj_mem_U hG hS hU hmN hmP u hu, fun hu => ?_⟩
    have := conj_mem_U hG hS hU (Subgroup.inv_mem _ hmN) (Subgroup.inv_mem _ hmP) _ hu
    simpa [mul_assoc] using this
  exact hUQ₁ (Th2.mem_normalizer_sup hmU hmQ)

end CFSG.GH74.GLS.Th2.NV7

module

public import CFSG.GH74.GLS.SP.Local.SPLOrdOut
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR5
public import CFSG.GH74.GLS.C3.Layer1.Th2L83GenCore
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR3

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

section Facts

variable {G : Type} [Group G] [Finite G]

theorem kBar_u2_of_unbal (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) {u t : G}
    {L : Subgroup G} (hunb : IsUnbalancingTriple u t L) :
    Nonempty (kBar L ≃* alternatingGroup (Fin 7)) ∨ HasL2Model (kBar L) Odd := by
  obtain ⟨-, hcases⟩ := h102 G hG u t L hunb.isLocallyUnbalancing
  rcases hcases with h | h | ⟨hl34, hc1, hc2⟩
  · exact Or.inr h
  · exact Or.inl h
  · exact (hL34 G hG.gen4 u L hunb.1.1 hunb.1.2 ⟨hl34, hc1, hc2⟩).elim

theorem centerless_two_le_of_u2 {u : G} {L : Subgroup G}
    (hL : IsPCompIn 2 (centralizer ({u} : Set G)) L)
    (hu : Nonempty (kBar L ≃* alternatingGroup (Fin 7)) ∨ HasL2Model (kBar L) Odd) :
    CenterlessBar L ∧ 2 ≤ pRank 2 ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen : CenterlessBar L := by
    rcases hu with hA | hL2
    · exact centerlessBar_of_A7 hA
    · exact centerlessBar_of_hasL2Model (fun q hq => hq) hL2
  refine ⟨hcen, ?_⟩
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 L
  have hshape : RankTwoShape P := by
    rcases hu with hA | hL2
    · exact rankTwoShape_sylow_A7 hP hA
    · exact rankTwoShape_sylow_L2 hP (TwoThin.isQuasisimple_hat hL) (fun q hq => hq) hL2
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hshape
  have hPJ : P ≤ L := by
    rcases hP with ⟨Q, hQ⟩
    rw [← hQ]
    exact Subgroup.map_subtype_le _
  have hUJ : U ≤ L := hU.1.trans hPJ
  have h1 := C3.Layer1.Back.card_eq_two_pow_pRank hU.2.1
  have h2 : 2 ^ 2 ≤ 2 ^ pRank 2 ↥U := by rw [← h1, hU.2.2]; norm_num
  have h3 : 2 ≤ pRank 2 ↥U := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  exact h3.trans (C3.Layer1.Back.pRank_mono' hUJ)

theorem centralizer_le_normalizer_of_u2 (hG4 : pRank 2 G ≤ 4) {u : G} (hu2 : orderOf u = 2)
    {L : Subgroup G} (hL : IsPCompIn 2 (centralizer ({u} : Set G)) L)
    (hu : Nonempty (kBar L ≃* alternatingGroup (Fin 7)) ∨ HasL2Model (kBar L) Odd) :
    ∀ g ∈ centralizer ({u} : Set G), g ∈ normalizer (L : Set G) := fun _ hg =>
  let h := centerless_two_le_of_u2 hL hu
  mem_normalizer_of_pRank_le_four_cent hG4 hu2 hL h.1 h.2 hg

omit [Finite G] in
theorem barAct_mk' (J : Subgroup G) (m : ↥(normalizer (J : Set G))) (l : ↥J) :
    barAct J m (QuotientGroup.mk l : kBar J) =
      QuotientGroup.mk ⟨(m : G) * l * (m : G)⁻¹, normalizer_conj_mem (m : G) m.2 (l : G) l.2⟩ :=
  C3.Layer1.Back.actHom_mk normalizer_conj_mem m l

theorem exists_mem_cent_lift {t : G} (ht2 : orderOf t = 2) {L : Subgroup G}
    (htL : t ∈ normalizer (L : Set G)) {k : kBar L} (hk : barAct L ⟨t, htL⟩ k = k) :
    ∃ (l : G) (hl : l ∈ L), l * t = t * l ∧ (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : kBar L) = k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨l₀, hl₀⟩, rfl⟩ := QuotientGroup.mk_surjective k
  rw [barAct_mk'] at hk
  have hO : ∀ f ∈ zpowers t, ∀ o ∈ pPrimeCoreOf 2 L, f * o * f⁻¹ ∈ pPrimeCoreOf 2 L := by
    intro f hf o ho
    have htN : t ∈ normalizer ((pPrimeCoreOf 2 L : Subgroup G) : Set G) :=
      TwoThin.mem_normalizer_pPrimeCoreOf htL
    have hfN : f ∈ normalizer ((pPrimeCoreOf 2 L : Subgroup G) : Set G) :=
      (Subgroup.zpowers_le.2 htN) hf
    exact (Subgroup.mem_normalizer_iff.1 hfN o).1 ho
  have hr : l₀⁻¹ * (t * l₀ * t⁻¹) ∈ pPrimeCoreOf 2 L := by
    have hk2 : (QuotientGroup.mk ⟨t * l₀ * t⁻¹, normalizer_conj_mem t htL l₀ hl₀⟩ : kBar L) =
        QuotientGroup.mk ⟨l₀, hl₀⟩ := hk
    have h1 := QuotientGroup.eq.1 hk2
    have hmem : l₀⁻¹ * (t * l₀ * t⁻¹) ∈ L :=
      L.mul_mem (L.inv_mem hl₀) (normalizer_conj_mem t htL l₀ hl₀)
    refine C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hmem, ?_⟩
    have h3 : (⟨l₀⁻¹ * (t * l₀ * t⁻¹), hmem⟩ : ↥L) =
        ((⟨t * l₀ * t⁻¹, normalizer_conj_mem t htL l₀ hl₀⟩ : ↥L)⁻¹ * ⟨l₀, hl₀⟩)⁻¹ :=
      Subtype.ext (by simp)
    rw [h3]
    exact (pPrimeCore 2 ↥L).inv_mem h1
  have hk' : ∀ f ∈ zpowers t, l₀⁻¹ * (f * l₀ * f⁻¹) ∈ pPrimeCoreOf 2 L := by
    intro f hf
    rcases mem_zpowers_two ht2 hf with rfl | rfl
    · simp
    · exact hr
  have hF : IsPGroup 2 ↥(zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2]; norm_num)
  have hOodd : ¬ 2 ∣ Nat.card (pPrimeCoreOf 2 L) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 (coprime_card_pPrimeCoreOf L)
  obtain ⟨o, ho, hfix⟩ := Th2.L83.exists_fixed_mem_coset hOodd hF hO hk'
  have hoL : o ∈ L := TwoThin.pPrimeCoreOf_le L ho
  have hlL : l₀ * o ∈ L := L.mul_mem hl₀ hoL
  refine ⟨l₀ * o, hlL, ?_, ?_⟩
  · have h := hfix t (mem_zpowers t)
    exact (mul_inv_eq_iff_eq_mul.1 h).symm
  · rw [QuotientGroup.eq]
    obtain ⟨hoL', hom⟩ := C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.1 ho
    have : (⟨l₀ * o, hlL⟩ : ↥L)⁻¹ * ⟨l₀, hl₀⟩ = (⟨o, hoL'⟩ : ↥L)⁻¹ := Subtype.ext (by simp)
    rw [this]
    exact (pPrimeCore 2 ↥L).inv_mem hom

theorem exists_mem_J_mul_cSec_of_u2 {L : Subgroup G}
    (hu : Nonempty (kBar L ≃* alternatingGroup (Fin 7)) ∨ HasL2Model (kBar L) Odd) {x b : G}
    (hx : x ∈ normalizer (L : Set G)) (hb : b ∈ normalizer (L : Set G))
    (hodd : Odd (orderOf x)) (hinv : b * x * b⁻¹ = x⁻¹) :
    ∃ j ∈ L, x * j⁻¹ ∈ centralizerSection L (pPrimeCoreOf 2 L) := by
  rcases hu with ⟨⟨e⟩⟩ | hL2
  · exact exists_mem_J_mul_cSec_of_odd_A7 e hx hodd
  · obtain ⟨F, _, _, hF, -, ⟨e⟩⟩ := IVK.exists_l2Field_of_hasL2Model_pred (fun q hq => hq) hL2
    refine exists_mem_J_mul_cSec_of_inverted (fun g h => ?_) hx hb hodd hinv
    exact SP.Local.out_abelian hF e (barAct L g) (barAct L h)

end Facts

end CFSG.GH74.GLS.Th2.Obs

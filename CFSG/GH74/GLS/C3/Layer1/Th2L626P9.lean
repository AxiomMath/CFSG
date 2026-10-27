module

public import CFSG.GH74.GLS.C3.Layer1.Th2L626P8
public import CFSG.GH74.GLS.C3.Layer1.Th2L626P5
public import CFSG.GH74.GLS.C3.Layer1.Th2L626P7
public import CFSG.GH74.GLS.C3.Layer1.Th2L627N

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools

section Clause

variable {G : Type} [Group G] [Finite G] {t u : G} {J B T : Subgroup G}

theorem pRank_centralizer_pair (hG : pRank 2 G = 4) (hB : IsE 4 ⊤ B) {a b : G}
    (ha : ∀ x ∈ B, x * a = a * x) (hb : ∀ x ∈ B, x * b = b * x) :
    pRank 2 ↥(centralizer ({a, b} : Set G)) = 4 := by
  refine le_antisymm (hG ▸ pRank_le_top' _) ?_
  have hle : B ≤ centralizer ({a, b} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rcases hg with rfl | hg
    · exact (ha x hx).symm
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact (hb x hx).symm
  exact hB.2.2.trans (C3.Layer1.Back.pRank_mono' hle)

theorem Cfg626.sylow_clause
    (I : L626Inputs) (hG : C3Hyp G) {x y : G} {K : Subgroup G} (hV : IsV2StarTriple x y K)
    (hK5 : HasL2Model (kBar K) (fun q => q = 5)) (hCx : pRank 2 ↥(CxK x K) = 2)
    (hJ2 : HasL2Model (kBar J) (fun q => Odd q ∧ IsFM9 q))
    (cfg : Cfg626 t u J B T) {z : G} (hzT : z ∈ T) (hzC : z ∈ CxK t J) (hz2 : orderOf z = 2)
    (hzc : ∀ w ∈ T, z * w = w * z) {L : Subgroup G} (hlt : PumpUpLT 2 t J z L) :
    IsSylowOf 2 (T ⊓ CxK t J) (CxK z L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hunb : IsUnbalancingTriple t u J := cfg.hmax.1.1
  have hzB : ∀ b ∈ B, b * z = z * b := fun b hb => (hzc b (cfg.hBT hb)).symm
  have hzu : z * u = u * z := hzc u (cfg.hBT cfg.huB)
  have hrk : pRank 2 ↥(centralizer ({z, u} : Set G)) = 4 :=
    pRank_centralizer_pair hG.pRank_eq_four cfg.hB hzB (fun b hb => cfg.B_comm b hb u cfg.huB)
  obtain ⟨htz, hunb'⟩ := trivial_of_commute_unb I hG hV hK5 hCx hunb hz2 hzC hzu hrk hlt
  have hz2' : z * z = 1 := by rw [← sq]; exact hz2 ▸ pow_orderOf_eq_one z
  have hB'el : CFSG.IsElementaryAbelian 2 ↥(B ⊔ zpowers z) :=
    Th2.L625.isElementaryAbelian_sup_zpowers cfg.hB.2.1 hz2' hzB
  have hE : IsEStarUnbal z u L :=
    ⟨hunb', B ⊔ zpowers z,
      ⟨le_top, hB'el, cfg.hB.2.2.trans (C3.Layer1.Back.pRank_mono' le_sup_left)⟩,
      Subgroup.mem_sup_right (Subgroup.mem_zpowers z), Subgroup.mem_sup_left cfg.huB⟩
  have hcmp : twoPartCard (centralizer ({z} : Set G)) ≤ twoPartCard (centralizer ({t} : Set G)) :=
    cfg.hmax.2 z u L hE
  have hTcz : T ≤ centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzc w hw).symm
  obtain ⟨R, hR, hTR⟩ := C3.Layer1.Iv251.exists_isSylowOf_ge hTcz cfg.hT.isPGroup
  have hcardT : Nat.card T = twoPartCard (centralizer ({t} : Set G)) := by
    rw [cfg.hT.card_eq]; rfl
  have hcardR : Nat.card R = twoPartCard (centralizer ({z} : Set G)) := by
    rw [hR.card_eq]; rfl
  have hTeq : T = R :=
    Subgroup.eq_of_le_of_card_ge hTR (by rw [hcardT, hcardR]; exact hcmp)
  have hTz : IsSylowOf 2 T (centralizer ({z} : Set G)) := hTeq ▸ hR
  have hJ2odd : HasL2Model (kBar J) Odd :=
    C3.Layer1.Back.hasL2Model_mono (fun q hq => hq.1) hJ2
  obtain ⟨e⟩ := htz.2
  have hL2odd : HasL2Model (kBar L) Odd := TwoThin.hasL2Model_of_mulEquiv e.symm hJ2odd
  have hnorm : ∀ c ∈ centralizer ({z} : Set G), ∀ k ∈ L, c * k * c⁻¹ ∈ L :=
    Th2.L625.normal_of_pRank_le_four hG.pRank_eq_four.le hunb'.1 hL2odd
  have hNL : ∀ c ∈ centralizer ({z} : Set G), c ∈ normalizer (L : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hnorm c hc k hk, fun hk => ?_⟩
    have := hnorm c⁻¹ (inv_mem hc) _ hk
    have e : c⁻¹ * (c * k * c⁻¹) * c⁻¹⁻¹ = k := by group
    rwa [e] at this
  have hKN : centralizer ({z} : Set G) ≤ normalizer (CxK z L : Set G) := fun c hc =>
    C3.Layer1.PumpL42.mem_normalizer_CxK ⟨hc, hNL c hc⟩
  have hSyl : IsSylowOf 2 (T ⊓ CxK z L) (CxK z L) :=
    hTz.inf_of_le_normalizer inf_le_left hKN
  obtain ⟨Λ, hΛ⟩ := C3.Layer1.Iv251.exists_trivData hlt htz
  have hQC : T ⊓ CxK t J ≤ CxK t J := inf_le_right
  have hQ2 : IsPGroup 2 ↥(T ⊓ CxK t J) := cfg.sylow_Q.isPGroup
  have hJc : IsPCompIn 2 (centralizer ({t} : Set G)) J := hunb.1.2
  have hEq : T ⊓ CxK z L = T ⊓ CxK t J := by
    refine le_antisymm (fun s hs' => ?_) (fun q hq => ⟨hq.1, hΛ.cent q hq.2 (hzc q hq.1)⟩)
    have hsT : s ∈ T := hs'.1
    have hsN : s ∈ normalizer ((T ⊓ CxK t J : Subgroup G) : Set G) := cfg.T_le_normalizer_Q hsT
    have hbig : s ∈ C3.Layer1.Iv251.bigC J (T ⊓ CxK t J) :=
      C3.Layer1.Iv251.mem_bigC_of_mem_CxK hΛ cfg.t_mem_Q ⟨hzT, hzC⟩ hs'.2 hsN
    exact ⟨hsT, C3.Layer1.Iv251.mem_CxK_of_mem_bigC_self hJc hQC hQ2 hbig (cfg.hT.le hsT)
      (cfg.hN s (cfg.hT.le hsT))⟩
  rw [hEq] at hSyl
  exact hSyl

end Clause

end CFSG.GH74.GLS

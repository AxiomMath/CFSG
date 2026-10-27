module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma4Four
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint Subgroup
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem inf_centralizer_eq_pCoreOf_F4 (h1222 : Stmt12_2_2_F4) [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) : L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L := by
  obtain ⟨hc, hnat⟩ := h.natural
  obtain ⟨e⟩ := h.quot
  have hn : 1 ≤ n := by rcases h.n_mem with rfl | rfl | rfl <;> omega
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  rcases h1222 G T h.hyp.simple h.hyp.nonabelian h.hyp.qtke h.hyp.sylow with hA | h3
  · exact absurd hA h.hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L h.hyp.maximal h.hyp.faithful h.hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -⟩ := hall V h.hyp.irrPlus
  have hO2 : pCoreOf 2 L ≤ L ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf (LieType.BorelTits.pCoreOf_le 2 L)
      (pCoreOf_le_centralizer_of_reduced h.hyp.normalizes hVT hred)
  refine (Subgroup.eq_of_le_of_card_ge hO2 ?_).symm
  let φ : ↥L →* MulAut ↥V := (conjAct V).comp (Subgroup.inclusion hLV)
  have hrange : φ.range = autOn L V := by
    ext a
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨⟨l, hLV l.2⟩, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
    · rintro ⟨⟨x, hx⟩, hxL, rfl⟩
      exact ⟨⟨x, Subgroup.mem_subgroupOf.1 hxL⟩, rfl⟩
  have hker : φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hl v hv
      have h1 := congrArg (fun f : MulAut ↥V => ((f ⟨v, hv⟩ : ↥V) : G)) hl
      change (l : G) * v * (l : G)⁻¹ = v at h1
      calc v * l = ((l : G) * v * (l : G)⁻¹) * l := by rw [h1]
        _ = l * v := by group
    · intro hl
      apply MulEquiv.ext
      rintro ⟨v, hv⟩
      apply Subtype.ext
      change (l : G) * v * (l : G)⁻¹ = v
      rw [← hl v hv]
      group
  have hcardL1 : Nat.card L = Nat.card (autOn L V) *
      Nat.card ↥(L ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange, hker,
      ← Subgroup.card_map_of_injective (f := L.subtype) L.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have hcardL2 : Nat.card L = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) * Nat.card (pCoreOf 2 L) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)]
    congr 1
    rw [pCoreOf, Subgroup.card_map_of_injective L.subtype_injective]
  have hSL : Nat.card (autOn L V) = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [card_eq_of_binaryNaturalSL hnat hn, Nat.card_congr e.toEquiv, card_sl_zmod_two_flag hn]
  have hpos : 0 < Nat.card (autOn L V) := Nat.card_pos
  rw [hcardL1, hSL] at hcardL2
  rw [hSL] at hpos
  exact (Nat.eq_of_mul_eq_mul_left hpos hcardL2).le

theorem lemma12_8_4_four_F4 (h1222 : Stmt12_2_2_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) : Lemma12_8_4_four_F4 := by
  intro G _ _ T L V n h V₁ H hV₁ hH
  obtain ⟨-, hsq, -⟩ := h.card_sq
  obtain ⟨hVT, hTV⟩ := h.hyp.le_and_normalizes_F4 h1222
  have hA := lemma12_8_4_one_F4 h1222 h hV₁ hH
  have hHN : H ≤ Subgroup.normalizer (V₁ : Set G) := hH.2.1
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hT2 : IsPGroup 2 T := h.hyp.sylow.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  have hCH : centralizerMod V₁ H (conjClosure V H) ≤ H := centralizerMod_le_left _ _ _
  have hHC : H ≤ Subgroup.normalizer (centralizerMod V₁ H (conjClosure V H) : Set G) :=
    le_normalizer_centralizerMod hHN Subgroup.le_normalizer (le_normalizer_conjClosure V H)
  have hNVM : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    normalizer_le_of_hyp1223 h37 h38 h39 h.hyp hTV (hT2.to_le hVT)
  have hCL : L ⊓ Subgroup.centralizer (V : Set G) ≤ T := by
    rw [inf_centralizer_eq_pCoreOf_F4 h1222 h]
    have hLT : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) := hA.sylow_LT
    have hle : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
        ((sup_le Subgroup.le_normalizer h.hyp.normalizes).trans
          (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
        (LieType.BorelTits.pCoreOf_isPGroup 2 L)
    exact hle.trans (pCoreOf_two_le_of_isSylowTwoOf hLT)
  apply le_antisymm
  · have hC2 : IsPGroup 2 (centralizerMod V₁ H (conjClosure V H)) := by
      refine isPGroup_two_of_odd_orderOf_eq_one fun x hx hodd => ?_
      by_contra hx1
      set C := centralizerMod V₁ H (conjClosure V H) with hCdef
      set Y := oTwoUpper C with hYdef
      have hgen : ∀ g ∈ C, Odd (orderOf g) → g ∈ Subgroup.centralizer (V : Set G) :=
        fun g hg ho => mem_centralizer_of_odd_of_commutator_mem hV₁.1 hV₁.2.1 hsq hg.2.1
          (fun v hv => hg.2.2 v (le_conjClosure V H hv)) ho
      have hgenM : ∀ g ∈ C, Odd (orderOf g) → g ∈ Subgroup.normalizer (L : Set G) :=
        fun g hg ho => hNVM (Subgroup.centralizer_le_normalizer _ (hgen g hg ho))
      have hHY : H ≤ Subgroup.normalizer (Y : Set G) :=
        hHC.trans (normalizer_le_normalizer_oTwoUpper C)
      have hconjgen : ∀ l ∈ L, ∀ g ∈ C, Odd (orderOf g) → l * g * l⁻¹ ∈ Y := by
        intro l hl g hg ho
        have hgM := hgenM g hg ho
        have hgCV := hgen g hg ho
        have hlNV : l ∈ Subgroup.normalizer (V : Set G) := hLV hl
        set w := l * g * l⁻¹ * g⁻¹ with hw
        have hwL : w ∈ L := by
          have h1 : g * l⁻¹ * g⁻¹ ∈ L :=
            (Subgroup.mem_normalizer_iff.mp hgM _).mp (L.inv_mem hl)
          have e : w = l * (g * l⁻¹ * g⁻¹) := by rw [hw]; group
          rw [e]
          exact L.mul_mem hl h1
        have hwC : w ∈ Subgroup.centralizer (V : Set G) := by
          have h1 : l * g * l⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
            rw [Subgroup.mem_centralizer_iff]
            intro v hv
            have hv' : l⁻¹ * v * l ∈ V := by
              have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlNV) v).mp hv
              simpa using this
            have hc := (Subgroup.mem_centralizer_iff.mp hgCV) _ hv'
            calc v * (l * g * l⁻¹) = l * ((l⁻¹ * v * l) * g) * l⁻¹ := by group
              _ = l * (g * (l⁻¹ * v * l)) * l⁻¹ := by rw [hc]
              _ = l * g * l⁻¹ * v := by group
          exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hgCV)
        have hwT : w ∈ T := hCL ⟨hwL, hwC⟩
        have hgY : g ∈ Y := mem_oTwoUpper_of_odd hg ho
        have hodd' : Odd (orderOf (w * g)) := by
          have e : w * g = l * g * l⁻¹ := by rw [hw]; group
          rw [e, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
          exact ho
        have hwY : w ∈ Y := mem_of_mul_of_odd_orderOf (hTH.trans hHY) hT2 hwT hgY hodd'
        have e : l * g * l⁻¹ = w * g := by rw [hw]; group
        rw [e]
        exact Y.mul_mem hwY hgY
      have hLY : L ≤ Subgroup.normalizer (Y : Set G) := by
        refine le_normalizer_of_conj_mem fun l hl y hy => ?_
        induction hy using Subgroup.closure_induction with
        | mem g hg => exact hconjgen l hl g hg.1 hg.2
        | one => simp
        | mul a b _ _ iha ihb =>
          have e : l * (a * b) * l⁻¹ = (l * a * l⁻¹) * (l * b * l⁻¹) := by group
          rw [e]
          exact Y.mul_mem iha ihb
        | inv a _ iha =>
          have e : l * a⁻¹ * l⁻¹ = (l * a * l⁻¹)⁻¹ := by group
          rw [e]
          exact Y.inv_mem iha
      have hYH : Y ≤ H := (oTwoUpper_le C).trans hCH
      have hYchar : QuasithinUnique.CharTwo Y := QuasithinUnique.CharTwo.of_normal hA.charTwo hYH
        (Subgroup.normal_subgroupOf_of_le_normalizer hHY)
      have hYne : Y ≠ ⊥ := by
        intro hY
        apply hx1
        have : x ∈ Y := mem_oTwoUpper_of_odd hx hodd
        rw [hY, Subgroup.mem_bot] at this
        exact this
      have hOY : pCoreOf 2 Y ≠ ⊥ := pCoreOf_ne_bot_of_charTwo hYchar hYne
      have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 Y : Set G)) :=
        ⟨pCoreOf 2 Y, hOY, LieType.BorelTits.pCoreOf_isPGroup 2 Y, rfl⟩
      have hNY : Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
        LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y
      obtain ⟨N, hNmax, hNle⟩ := exists_maxTwoLocal_ge hloc
      have hLTN : L ⊔ T ≤ N :=
        (sup_le (hLY.trans hNY) (hTH.trans (hHY.trans hNY))).trans hNle
      have hU := lemma_1_2_7_three h.hyp.qtke h.hyp.simple h.hyp.nonabelian h37 h38 h39
        h.hyp.sylow h.hyp.maximal
      rw [h.hyp.conjClosure_eq] at hU
      have hNM : N = Subgroup.normalizer (L : Set G) := hU.2 N ⟨hNmax, hLTN⟩
      exact hH.2.2 (hNM ▸ (hHY.trans hNY).trans hNle)
    exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCH hHC hC2
  · intro q hq
    have hqH : q ∈ H := LieType.BorelTits.pCoreOf_le 2 H hq
    have hqN : q ∈ Subgroup.normalizer (V₁ : Set G) := hHN hqH
    refine ⟨hqH, hqN, fun u hu => ?_⟩
    have hcc := hA.conjClosure_le_N
    have hmemY : tmk V₁ ⟨u, hcc hu⟩ ∈ omegaOneCenterOf (tildeOf V₁ (pCoreOf 2 H)) :=
      (secImg_le_iff.1 hA.G22_one.2) ⟨u, hcc hu⟩ hu
    have hqQ : tmk V₁ ⟨q, hqN⟩ ∈ tildeOf V₁ (pCoreOf 2 H) := secMk_mem_secImg hq
    exact commutator_mem_of_secMk_commute (mem_centralizer_of_mem_omegaOneCenterOf hmemY hqQ)

theorem lemma12_8_4_F4 (h1222 : Stmt12_2_2_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) : Lemma12_8_4_F4 :=
  lemma12_8_4_of_four_F4 h1222 (lemma12_8_4_four_F4 h1222 h37 h38 h39)

end CFSG.Quasithin.H13

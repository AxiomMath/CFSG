module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Facts
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Plumb
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Exp
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem zjp_card_le {q n : ℕ} (hq : q.Prime) {H : Subgroup G} (hH : CFSG.Open.pRank q H ≤ n)
    (E : Subgroup ↥H) (hE : IsElemAbelian q E) : Nat.card E ≤ q ^ n := by
  have : Fact q.Prime := ⟨hq⟩
  have hEp : IsPGroup q E := fun x => ⟨1, by
    have := hE.2 x x.2
    exact Subtype.ext (by simpa using this)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hcardG : Nat.card (E.map H.subtype) = q ^ k := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hk]
  have hk2 : k ≤ n := by
    have : k ≤ CFSG.Open.pRank q H := by
      refine le_csSup ⟨Nat.card G, ?_⟩
        ⟨E.map H.subtype, Subgroup.map_subtype_le E,
          CFSG.SectionRank.isElemAbelian_map hE H.subtype, hcardG⟩
      rintro r ⟨B, -, -, hB⟩
      calc r ≤ q ^ r := (Nat.lt_pow_self hq.one_lt).le
        _ = Nat.card B := hB.symm
        _ ≤ Nat.card G := Subgroup.card_le_card_group B
    exact this.trans hH
  rw [hk]
  exact Nat.pow_le_pow_right hq.pos hk2

omit [Finite G] in
theorem zjp_conj_mem {V : Subgroup G} {g : G} (hg : g ∈ normalizer (V : Set G)) {h : G}
    (hh : h ∈ V) : g * h * g⁻¹ ∈ V :=
  (mem_normalizer_iff.mp hg h).mp hh

omit [Finite G] in
theorem zjp_conj_inv_mem {V : Subgroup G} {g : G} (hg : g ∈ normalizer (V : Set G)) {h : G}
    (hh : h ∈ V) : g⁻¹ * h * g ∈ V := by
  simpa using (mem_normalizer_iff.mp (inv_mem hg) h).mp hh

omit [Finite G] in
def zjp_conjAut {H V : Subgroup G} (hVH : V ≤ H) {g : G}
    (hg : g ∈ normalizer (V : Set G)) : MulAut ↥(V.subgroupOf H) where
  toFun x := ⟨⟨g * (x.1 : G) * g⁻¹, hVH (zjp_conj_mem hg x.2)⟩, zjp_conj_mem hg x.2⟩
  invFun x := ⟨⟨g⁻¹ * (x.1 : G) * g, hVH (zjp_conj_inv_mem hg x.2)⟩, zjp_conj_inv_mem hg x.2⟩
  left_inv x := by
    apply Subtype.ext; apply Subtype.ext
    change g⁻¹ * (g * (x.1 : G) * g⁻¹) * g = x.1
    group
  right_inv x := by
    apply Subtype.ext; apply Subtype.ext
    change g * (g⁻¹ * (x.1 : G) * g) * g⁻¹ = x.1
    group
  map_mul' x y := by
    apply Subtype.ext; apply Subtype.ext
    change g * ((x.1 : G) * (y.1 : G)) * g⁻¹ = g * (x.1 : G) * g⁻¹ * (g * (y.1 : G) * g⁻¹)
    group

omit [Finite G] in
theorem zjp_normalizer_le {H V : Subgroup G} (hVH : V ≤ H) {Z : Subgroup ↥H}
    (hZV : Z ≤ V.subgroupOf H) (hZc : (Z.subgroupOf (V.subgroupOf H)).Characteristic) :
    normalizer (V : Set G) ≤ normalizer ((Z.map H.subtype : Subgroup G) : Set G) := by
  have key : ∀ g ∈ normalizer (V : Set G), ∀ z ∈ Z.map H.subtype,
      g * z * g⁻¹ ∈ Z.map H.subtype := by
    intro g hg z hz
    obtain ⟨z', hz', rfl⟩ := hz
    have hz'V : z' ∈ V.subgroupOf H := hZV hz'
    have hmem : (⟨z', hz'V⟩ : ↥(V.subgroupOf H)) ∈ Z.subgroupOf (V.subgroupOf H) := hz'
    have hfix := hZc.fixed (zjp_conjAut hVH hg)
    have : zjp_conjAut hVH hg ⟨z', hz'V⟩ ∈ Z.subgroupOf (V.subgroupOf H) := by
      rw [← hfix] at hmem
      exact hmem
    exact ⟨_, this, rfl⟩
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key g hg h hh, fun hh => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hh
  simpa [mul_assoc] using this

omit [Finite G] in
theorem zjp_join_le {D H : Subgroup G} (hDH : D ≤ H) (Z : Subgroup ↥H) :
    (invariantTwoJoinIn (D.subgroupOf H) (normalizer (Z : Set ↥H))).map H.subtype ≤
      invariantTwoJoinIn D (H ⊓ normalizer ((Z.map H.subtype : Subgroup G) : Set G)) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine invariantTwoJoinIn_le_of_forall fun W hW hW2 hDW => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_invariantTwoJoinIn ?_ (hW2.map _) ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.2, thg_mem_normalizer_map (hW hw)⟩
  · intro g hg
    exact thg_mem_normalizer_map (hDW (show (⟨g, hDH hg⟩ : ↥H) ∈ D.subgroupOf H from hg))

theorem IsOptimalRelPair.zjFrame {p : ℕ} {P : Sylow p G} {M D R T H V : Subgroup G}
    (hS : Setting G) (hD1 : TheoremD1 G) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) (hp : p ∈ rankThreeSigmaA G)
    (hd : MaximalRelativePair p P M D R T) (hopt : IsOptimalRelPair p M D R T H V)
    (hfacts : OptimalRelPairFacts p M D H V) :
    ZJFrame p (primeComplementCore (G := H) p) (D.subgroupOf H) (V.subgroupOf H) := by
  have := hS.simple
  have hTwoLocal : IsTwoLocal H := hopt.pair.cand.twoLocal
  have hDH : D ≤ H := (le_sup_right : D ≤ relPairBase R T ⊔ D).trans hopt.pair.cand.base_le
  have hVH : V ≤ H := hfacts.maximal.1
  have hV2 : IsPGroup 2 V := hfacts.maximal.2.1
  have hDV : D ≤ normalizer (V : Set G) := hfacts.maximal.2.2.1
  refine
    { pre := hopt.thompsonPreFrame hS hD1 hR h13 hp hd hfacts
      exists_component := ?_
      sections := CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper H
        (twoLocal_ne_top hS.nonab H hTwoLocal)
      rank3 := fun E hE => zjp_card_le Nat.prime_three
        ((local_pRank_le_evenRank 3 Nat.prime_three (by norm_num) H hTwoLocal).trans
          hS.rank.le) E hE
      charTwo := ?_
      sylow2 := ?_
      V_two := hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVH).symm
      D_norm := ?_
      core_le := ?_
      noncover := ?_
      exp := (hd.normalizerExponent hS hD1 hR h13 hp).subgroupOf hDH }
  · obtain ⟨L, hL, -, -, -, hpL, hcat⟩ := hfacts.exists_component
    exact ⟨L, (CFSG.isComponent_iff_open L).mpr hL, hpL, hcat⟩
  · intro c hc
    have hcH : (c : G) ∈ H ⊓ centralizer (pCoreOf 2 H : Set G) := by
      refine ⟨c.2, ?_⟩
      show (c : G) ∈ centralizer (pCoreOf 2 H : Set G)
      rw [mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.mp hc y hy)
    obtain ⟨y, hy, hyc⟩ := hS.charTwo H hTwoLocal hcH
    have : y = c := Subtype.ext hyc
    rwa [← this]
  · rw [← isSylowOf_map_subtype_iff H]
    exact hfacts.sylow
  · rw [← Subgroup.subgroupOf_normalizer_eq hVH]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hDV (Subgroup.mem_subgroupOf.mp hx))
  · intro x hx
    exact hfacts.pCore_le ⟨x, hx, rfl⟩
  · intro Z hZV hZ1 hZc hdvd
    have hZgV : Z.map H.subtype ≤ V := by
      rintro _ ⟨z, hz, rfl⟩
      exact hZV hz
    have hZg1 : Z.map H.subtype ≠ ⊥ := fun h => hZ1 (eq_bot_iff.mpr fun z hz => by
      have : (z : G) ∈ (⊥ : Subgroup G) := h ▸ ⟨z, hz, rfl⟩
      exact Subtype.ext (Subgroup.mem_bot.mp this))
    refine hfacts.not_dvd _ hZgV hZg1 (zjp_normalizer_le hVH hZV hZc) (hdvd.trans ?_)
    rw [← Subgroup.card_map_of_injective H.subtype_injective]
    exact Subgroup.card_dvd_of_le (zjp_join_le hDH Z)

end CFSG.LocalAnalysis.RankThreeTheoremC

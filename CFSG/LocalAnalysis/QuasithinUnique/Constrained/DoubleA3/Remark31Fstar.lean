module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Remark31
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma30Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.SetupAt
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtra
public import CFSG.Quasithin.Background.C2Nine
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoOfNoComponent
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped commutatorElement

section A4

variable {G : Type} [Group G]

theorem IsA4Block.opResidual_eq [Finite G] {L U : Subgroup G} (h : IsA4Block L U) :
    opResidual 2 L = L := by
  obtain ⟨c, hcL, hc3, hcN, hcfp, hLc⟩ := h.exists_c
  refine le_antisymm (opResidual_le 2 L) ?_
  have hcN' : c ∈ opResidual 2 L :=
    mem_opResidual_of_coprime hcL (by rw [hc3]; norm_num)
  have hnorm : L ≤ normalizer (opResidual 2 L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (opResidual_le 2 L)).mp (opResidual_normal 2 L)
  have hUN : U ≤ opResidual 2 L := by
    obtain ⟨u, hu, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
      by_contra hcon
      have h1 : U = ⊥ := by
        rw [eq_bot_iff]
        intro g hg
        by_contra hg1
        exact hcon ⟨g, hg, fun h => hg1 (by rw [h]; exact one_mem _)⟩
      have := h.card_U
      rw [h1, Subgroup.card_bot] at this
      omega
    have hUL : U ≤ L := h.le
    have h1 : u⁻¹ * c * u ∈ opResidual 2 L := by
      have := (Subgroup.mem_normalizer_iff.mp (hnorm (hUL (U.inv_mem hu))) c).mp hcN'
      simpa [mul_assoc] using this
    have h2 : c⁻¹ * (u⁻¹ * c * u) ∈ opResidual 2 L :=
      (opResidual 2 L).mul_mem ((opResidual 2 L).inv_mem hcN') h1
    have h3 : c⁻¹ * (u⁻¹ * c * u) ∈ U := by
      have hc' : c⁻¹ ∈ normalizer (U : Set G) := (normalizer (U : Set G)).inv_mem hcN
      have h4 := (Subgroup.mem_normalizer_iff.mp hc' u⁻¹).mp (U.inv_mem hu)
      have : c⁻¹ * (u⁻¹ * c * u) = (c⁻¹ * u⁻¹ * c) * u := by group
      rw [this]
      have h5 : c⁻¹ * u⁻¹ * c ∈ U := by simpa [mul_assoc] using h4
      exact U.mul_mem h5 hu
    have h6 : c⁻¹ * (u⁻¹ * c * u) ≠ 1 := by
      intro h0
      apply hcfp u hu hu1
      have : u⁻¹ * c * u = c := by
        calc u⁻¹ * c * u = c * (c⁻¹ * (u⁻¹ * c * u)) := by group
          _ = c := by rw [h0]; group
      calc c * u * c⁻¹ = u * (u⁻¹ * c * u) * c⁻¹ := by group
        _ = u * c * c⁻¹ := by rw [this]
        _ = u := by group
    exact h.le_of_mem hnorm h2 h3 h6
  exact hLc.le.trans (sup_le hUN (zpowers_le.mpr hcN'))

theorem IsA4Block.isPGroup_U {L U : Subgroup G} (h : IsA4Block L U) : IsPGroup 2 ↥U :=
  IsPGroup.of_card (n := 2) (by rw [h.card_U]; norm_num)

theorem IsA4Block.isElemAbelian_U {L U : Subgroup G} (h : IsA4Block L U) : IsElemAbelian 2 U :=
  ⟨⟨⟨fun a b => Subtype.ext (h.comm_U a a.2 b b.2)⟩⟩, fun x hx => h.sq_U x hx⟩

end A4

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s x z₁ z₂ : G}

theorem A3A3x.rank1₂ (hD : AppC.C56DoubleA3)
    (hA : A3A3x T M H S L s x z₁ z₂) :
    C5.Rank1 (baum S) (baum S ⊓ centralizer (blockU2 L s : Set G)) (blockU2 L s)
      (zpowers z₂) 2 := by
  obtain ⟨_, w₂, -, -, -, hw₂C, -, R2⟩ := rank1_blocks hD hA.toA3A3
  have hw₂mem : w₂ ∈ blockU2 L s ⊓ centralizer (baum S : Set G) := by
    rw [hw₂C]; exact Subgroup.mem_zpowers w₂
  have hw₂sq : w₂ ^ 2 = 1 := hA.isA4s.sq_U w₂ hw₂mem.1
  have hz : z₂ ∈ zpowers w₂ := by
    rw [← hw₂C]; exact ⟨hA.z₂_mem.1, hA.z₂_mem.2⟩
  rcases (mem_zpowers_iff_of_sq_eq_one hw₂sq).mp hz with h | h
  · exact absurd h hA.z₂_ne
  · rw [h]; exact R2

theorem A3A3x.z₂_mem_commutator (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) (hA : A3A3x T M H S L s x z₁ z₂) :
    z₂ ∈ ⁅baum S, baum S⁆ := by
  have hcs := hA.cs
  have hB := basic31 hD h27_1 hA.toA3A3
  have R2 := hA.rank1₂ hD
  have hxN : x ∈ normalizer (baum S : Set G) :=
    normalizer_le_normalizer_baum S
      (normalizer_of_relIndex_two hcs.le_T hB.idx_T hA.x_mem)
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hA.s_mem
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs hA.a3
  have hU₂B : blockU2 L s ≤ baum S :=
    (C5.conjSubgroup_mono hUB s).trans (le_of_eq (C5.conjSubgroup_eq_self hsB))
  have hx1 : ¬ conjSubgroup (blockU2 L s) x ≤ baum S ⊓ centralizer (blockU2 L s : Set G) :=
    fun h => hA.x_good₂ (h.trans inf_le_right)
  have hx2 : ¬ conjSubgroup (blockU2 L s) x⁻¹ ≤ baum S ⊓ centralizer (blockU2 L s : Set G) :=
    fun h => not_conj_inv_le_centralizer hA.x_good₂ (h.trans inf_le_right)
  have hcomm := (R2.commutator_conj hxN hx1 hx2).1
  have hz : z₂ ∈ ⁅blockU2 L s, conjSubgroup (blockU2 L s) x⁆ := by
    rw [hcomm]; exact Subgroup.mem_zpowers z₂
  exact Subgroup.commutator_mono hU₂B (R2.conj_le_B hxN) hz

omit [Finite G] in
theorem commutator_le_of_commute_sup {R D W : Subgroup G} (hR : R ≤ D ⊔ W)
    (hDW : ∀ d ∈ D, ∀ w ∈ W, d * w = w * d) (hD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) :
    ⁅R, R⁆ ≤ W := by
  have hDN : D ≤ normalizer (W : Set G) := C5.le_normalizer_of_commute hDW
  have hdec : ∀ g ∈ R, ∃ d ∈ D, ∃ w ∈ W, g = d * w := by
    intro g hg
    have hg' : g ∈ ((D ⊔ W : Subgroup G) : Set G) := hR hg
    rw [Subgroup.coe_mul_of_left_le_normalizer_right D W hDN] at hg'
    obtain ⟨d, hd, w, hw, hdw⟩ := hg'
    exact ⟨d, hd, w, hw, hdw.symm⟩
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨d₁, hd₁, w₁, hw₁, rfl⟩ := hdec g₁ hg₁
  obtain ⟨d₂, hd₂, w₂, hw₂, rfl⟩ := hdec g₂ hg₂
  have e : ⁅d₁ * w₁, d₂ * w₂⁆ = ⁅w₁, w₂⁆ := by
    have h1 : d₁ * w₁ * (d₂ * w₂) * (d₁ * w₁)⁻¹ * (d₂ * w₂)⁻¹ =
        w₁ * w₂ * w₁⁻¹ * w₂⁻¹ := by
      have a1 : w₁ * d₂ = d₂ * w₁ := (hDW d₂ hd₂ w₁ hw₁).symm
      have a3 : d₁ * d₂ = d₂ * d₁ := hD d₁ hd₁ d₂ hd₂
      calc d₁ * w₁ * (d₂ * w₂) * (d₁ * w₁)⁻¹ * (d₂ * w₂)⁻¹
          = d₁ * (w₁ * d₂) * w₂ * w₁⁻¹ * d₁⁻¹ * w₂⁻¹ * d₂⁻¹ := by group
        _ = d₁ * (d₂ * w₁) * w₂ * w₁⁻¹ * d₁⁻¹ * w₂⁻¹ * d₂⁻¹ := by rw [a1]
        _ = (d₁ * d₂) * (w₁ * w₂ * w₁⁻¹) * d₁⁻¹ * w₂⁻¹ * d₂⁻¹ := by group
        _ = (d₂ * d₁) * (w₁ * w₂ * w₁⁻¹) * d₁⁻¹ * w₂⁻¹ * d₂⁻¹ := by rw [a3]
        _ = d₂ * (d₁ * (w₁ * w₂ * w₁⁻¹) * d₁⁻¹) * w₂⁻¹ * d₂⁻¹ := by group
        _ = d₂ * (w₁ * w₂ * w₁⁻¹) * w₂⁻¹ * d₂⁻¹ := by
              have : d₁ * (w₁ * w₂ * w₁⁻¹) * d₁⁻¹ = w₁ * w₂ * w₁⁻¹ := by
                have hW : w₁ * w₂ * w₁⁻¹ ∈ W := W.mul_mem (W.mul_mem hw₁ hw₂) (W.inv_mem hw₁)
                have := hDW d₁ hd₁ _ hW
                calc d₁ * (w₁ * w₂ * w₁⁻¹) * d₁⁻¹ = (w₁ * w₂ * w₁⁻¹) * d₁ * d₁⁻¹ := by rw [this]
                  _ = w₁ * w₂ * w₁⁻¹ := by group
              rw [this]
        _ = w₁ * w₂ * w₁⁻¹ * w₂⁻¹ := by
              have hW : w₁ * w₂ * w₁⁻¹ * w₂⁻¹ ∈ W :=
                W.mul_mem (W.mul_mem (W.mul_mem hw₁ hw₂) (W.inv_mem hw₁)) (W.inv_mem hw₂)
              have := hDW d₂ hd₂ _ hW
              calc d₂ * (w₁ * w₂ * w₁⁻¹) * w₂⁻¹ * d₂⁻¹
                  = d₂ * (w₁ * w₂ * w₁⁻¹ * w₂⁻¹) * d₂⁻¹ := by group
                _ = (w₁ * w₂ * w₁⁻¹ * w₂⁻¹) * d₂ * d₂⁻¹ := by rw [this]
                _ = w₁ * w₂ * w₁⁻¹ * w₂⁻¹ := by group
    rw [commutatorElement_def, commutatorElement_def]
    exact h1
  rw [e, commutatorElement_def]
  exact W.mul_mem (W.mul_mem (W.mul_mem hw₁ hw₂) (W.inv_mem hw₁)) (W.inv_mem hw₂)

omit [Finite G] in
theorem elemAbelian_comm {D : Subgroup G} (h : IsElemAbelian 2 D) {a b : G} (ha : a ∈ D)
    (hb : b ∈ D) : a * b = b * a := CFSG.Open.IsElemAbelian.comm h ha hb

theorem false_of_A3A3_centralizer₂ (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) (hA : A3A3x T M H S L s x z₁ z₂) {P L' : Subgroup G} {s' : G}
    (hPG : P ≤ centralizerElem z₂) (hcfg' : A3A3 T M P (sOne S x) L' s') : False := by
  have hcs := hA.cs
  have hcs' := hcfg'.cs
  have hB := basic31 hD h27_1 hA.toA3A3
  have hB' := basic31 hD h27_1 hcfg'
  have hJT : thompsonJ T = baum S := hB.hJT.symm.trans hB.hbJ.symm
  have hRS₁ : baum S ≤ sOne S x := le_sup_left
  have hJ : thompsonJ (sOne S x) = baum S := by
    rw [GammaExtra.thompsonJ_eq_of_le (hJT ▸ hRS₁) hA.sOne_le_T, hJT]
  obtain ⟨x', hx'T, hx'S⟩ : ∃ x' ∈ T, x' ∉ sOne S x := by
    by_contra hcon
    apply hcs'.ne_T
    exact le_antisymm hcs'.le_T (fun g hg => by
      by_contra h
      exact hcon ⟨g, hg, h⟩)
  obtain ⟨h1, -, -, h4, -⟩ := lemma2_4_30 hD h27_1 G T M P (sOne S x) L' s' hcfg'
  obtain ⟨-, hbJ'⟩ := h1 x' hx'T hx'S
  have hRR : baum (sOne S x) = baum S := hbJ'.trans hJ
  obtain ⟨hprod, hinf, hcomm', hel, -⟩ := h4 x' hx'T hx'S
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hA.s_mem
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs hA.a3
  have hU₂B : blockU2 L s ≤ baum S :=
    (C5.conjSubgroup_mono hUB s).trans (le_of_eq (C5.conjSubgroup_eq_self hsB))
  have hz₂R : z₂ ∈ baum S := hU₂B hA.z₂_mem.1
  have hL₀P : conjJoin (sOne S x) L' ≤ P := by rw [hcs'.eq_join]; exact le_sup_left
  have hz₂C : z₂ ∈ centralizer (conjJoin (sOne S x) L' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mp (hPG (hL₀P hg))
  have hz₂D : z₂ ∈ blockD (sOne S x) L' := by
    rw [← hB'.hbD]
    exact ⟨by rw [hRR]; exact hz₂R, hz₂C⟩
  have hcomm : ⁅baum (sOne S x), baum (sOne S x)⁆ ≤
      conjJoin (sOne S x) L' ⊔ conjR (blockU0 (sOne S x) L') x' :=
    commutator_le_of_commute_sup (le_sup_left.trans hprod.le) hcomm'
      (fun a ha b hb => elemAbelian_comm hel ha hb)
  rw [hRR] at hcomm
  have hz₂W := hcomm (hA.z₂_mem_commutator hD h27_1)
  have hmem : z₂ ∈ blockD (sOne S x) L' ⊓
      (conjJoin (sOne S x) L' ⊔ conjR (blockU0 (sOne S x) L') x') := ⟨hz₂D, hz₂W⟩
  rw [hinf] at hmem
  exact hA.z₂_ne (Subgroup.mem_bot.mp hmem)

theorem not_charTwo_centralizer₂ (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) (hSA : ConstrainedSetupAt) (hlin : Lin2BlockExcluded)
    (ha5 : A5BlockExcluded) (ha3 : SingleA3Excluded) (hA : A3A3x T M H S L s x z₁ z₂) :
    ¬ CharTwo (centralizerElem z₂) := by
  intro hct
  have hcs := hA.cs
  obtain ⟨hΓ2, -, hS₁M⟩ := remark31_G₂ hD h27_1 hA
  obtain ⟨P, L', hPG, hcs'⟩ := hSA G T M (centralizerElem z₂) (sOne S x) hcs.setting
    hcs.notBender hcs.notSmall (Or.inr hΓ2) hct hS₁M hA.sOne_le_T
  rcases hcs'.block.2 with ⟨n, hn, hlin2⟩ | h3 | h5
  · exact hlin G T M P (sOne S x) L' hcs' n hn hlin2
  · by_cases hj : conjJoin (sOne S x) L' = L'
    · exact ha3 G T M P (sOne S x) L' hcs' h3 hj
    · obtain ⟨s', hcfg'⟩ := exists_A3A3 hcs' h3 hj
      exact false_of_A3A3_centralizer₂ hD h27_1 hA hPG hcfg'
  · exact ha5 G T M P (sOne S x) L' hcs' h5

theorem pRank_pCoreOf_le_two (hcs : ConstrainedSetting G T M H S L) {X : Subgroup G}
    (hX : pCoreOf 2 X ≠ ⊥) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (pCoreOf p X) ≤ 2 := by
  intro p hp hp2
  have hsqt : CFSG.IsStronglyQuasithin ↥X := (hcs.setting.qtke.1 X hX).1
  have h1 := (CFSG.SectionRank.isStronglyQuasithin_iff.mp hsqt) p hp hp2
  have : Fact p.Prime := ⟨hp⟩
  rw [pRank_top_subtype] at h1
  exact (CFSG.SectionRank.pRank_mono hp.one_lt (CFSG.LieType.BorelTits.pCoreOf_le p X)).trans h1

theorem blockU_le_centralizer_oddCore (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) (hA : A3A3x T M H S L s x z₁ z₂) :
    blockU L ≤ centralizer (oddCoreIn (centralizerElem z₂) : Set G) := by
  have hcs := hA.cs
  obtain ⟨hΓ2, -, -⟩ := remark31_G₂ hD h27_1 hA
  have hL₂ : L ≤ centralizerElem z₂ := hA.L_le_cent₂
  exact a126_one hL₂ hA.isA4.opResidual_eq (hA.isA4.le.trans hL₂) hA.isA4.isPGroup_U
    (C1.commutator_blockU hA.isShort) (pRank_pCoreOf_le_two hcs hΓ2.1.1)
    (C2Nine.frattiniIn_eq_bot_of_isElemAbelian hA.isA4.isElemAbelian_U)

theorem oddCoreIn_centralizer₂_eq_bot (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) (hA : A3A3x T M H S L s x z₁ z₂) :
    oddCoreIn (centralizerElem z₂) = ⊥ := by
  have hcs := hA.cs
  have hB := basic31 hD h27_1 hA.toA3A3
  obtain ⟨hΓ2, -, hS₁M⟩ := remark31_G₂ hD h27_1 hA
  have hUc := blockU_le_centralizer_oddCore hD h27_1 hA
  obtain ⟨-, hinv⟩ := IsGamma0.centralizer_le_and_inverts_oddCoreIn hcs.setting (Or.inr hΓ2) hS₁M
    hcs.setting.isSylowTwoOf_M hA.sOne_le_T (z_central hB hA) hA.z_ne hA.sq_z
  rw [eq_bot_iff]
  intro y hy
  have hyG : y ∈ centralizerElem z₂ := oddCoreIn_le _ hy
  have hz₁y : y * z₁ = z₁ * y := Subgroup.mem_centralizer_iff.mp (hUc hA.z₁_mem.1) y hy
  have hz₂y : y * z₂ = z₂ * y := Subgroup.mem_centralizer_singleton_iff.mp hyG
  have hty : (z₁ * z₂) * y = y * (z₁ * z₂) := by
    calc (z₁ * z₂) * y = z₁ * (z₂ * y) := by group
      _ = z₁ * (y * z₂) := by rw [hz₂y]
      _ = (z₁ * y) * z₂ := by group
      _ = (y * z₁) * z₂ := by rw [hz₁y]
      _ = y * (z₁ * z₂) := by group
  have h1 : (z₁ * z₂)⁻¹ * y * (z₁ * z₂) = y := by
    calc (z₁ * z₂)⁻¹ * y * (z₁ * z₂) = (z₁ * z₂)⁻¹ * (y * (z₁ * z₂)) := by group
      _ = (z₁ * z₂)⁻¹ * ((z₁ * z₂) * y) := by rw [hty]
      _ = y := by group
  have h2 : y = y⁻¹ := by rw [← hinv y hy, h1]
  have h3 : y * y = 1 := by
    calc y * y = y * y⁻¹ := by rw [← h2]
      _ = 1 := by group
  have hord : orderOf (⟨y, hy⟩ : oddCoreIn (centralizerElem z₂)) ∣
      Nat.card (oddCoreIn (centralizerElem z₂)) := orderOf_dvd_natCard _
  have hord2 : orderOf (⟨y, hy⟩ : oddCoreIn (centralizerElem z₂)) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [pow_two] using h3))
  have hcop : Nat.Coprime 2 (Nat.card (oddCoreIn (centralizerElem z₂))) :=
    Nat.coprime_two_left.mpr (odd_card_oddCoreIn _)
  have hone : orderOf (⟨y, hy⟩ : oddCoreIn (centralizerElem z₂)) = 1 := by
    have := Nat.dvd_gcd hord2 hord
    rw [hcop.gcd_eq_one] at this
    exact Nat.dvd_one.mp this
  have : (⟨y, hy⟩ : oddCoreIn (centralizerElem z₂)) = 1 := orderOf_eq_one_iff.mp hone
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

theorem charTwo_of_no_component {X : Subgroup G} (hE : ∀ K : Subgroup G, ¬ IsComponentIn K X)
    (hodd : oddCoreIn X = ⊥) : CharTwo X :=
  CFSG.QuasithinUnique.charTwo_of_forall_not_isComponentIn hE hodd

theorem exists_component_centralizer₂ (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) (hSA : ConstrainedSetupAt) (hlin : Lin2BlockExcluded)
    (ha5 : A5BlockExcluded) (ha3 : SingleA3Excluded) (hA : A3A3x T M H S L s x z₁ z₂) :
    ∃ K : Subgroup G, IsComponentIn K (centralizerElem z₂) := by
  by_contra h
  exact not_charTwo_centralizer₂ hD h27_1 hSA hlin ha5 ha3 hA
    (charTwo_of_no_component (fun K hK => h ⟨K, hK⟩)
      (oddCoreIn_centralizer₂_eq_bot hD h27_1 hA))

end CFSG.QuasithinUnique.DoubleA3

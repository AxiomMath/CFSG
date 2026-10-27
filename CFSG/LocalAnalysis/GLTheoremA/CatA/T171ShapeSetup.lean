module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
public import CFSG.GroupTheory.SupCommute
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import TauCeti.GroupTheory.ExponentPrime

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement IsMulCommutative

variable {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ} {B : Subgroup Ω} {x : Ω} {L D K : Subgroup Ω}

theorem exists_isCompl_of_isElemAbelian {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    {B W H : Subgroup G} (hB : IsElemAbelian p B) (hW : W ≤ B) (hH : H ≤ B)
    (hHW : H ⊓ W = ⊥) :
    ∃ A : Subgroup G, A ≤ B ∧ H ≤ A ∧ A ⊓ W = ⊥ ∧ A ⊔ W = B := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hBel : CFSG.IsElementaryAbelian p B :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hB
  let H' : Subgroup B := H.subgroupOf B
  let W' : Subgroup B := W.subgroupOf B
  have hHW' : H' ⊓ W' = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyG : (y : G) ∈ H ⊓ W := ⟨hy.1, hy.2⟩
    rw [hHW] at hyG
    exact Subtype.ext (by simpa using hyG)
  let φ : Subgroup B ≃o Submodule (ZMod p) (Additive B) :=
    (Subgroup.toAddSubgroup (G := B)).trans (AddSubgroup.toZModSubmodule (n := p))
  have hdisj : Disjoint (φ H') (φ W') := by
    rw [disjoint_iff, ← map_inf, hHW', map_bot]
  obtain ⟨A'', hHA'', hcompl''⟩ := Disjoint.exists_isCompl hdisj
  set A' : Subgroup B := φ.symm A'' with hA'
  have hH'A' : H' ≤ A' := by
    rw [hA', ← φ.le_iff_le]
    simpa using hHA''
  have hcompl' : IsCompl A' W' := by
    have h := φ.symm.isCompl hcompl''
    simpa [hA'] using h
  have hWmap : W'.map B.subtype = W :=
    (Subgroup.subgroupOf_map_subtype W B).trans (inf_eq_left.mpr hW)
  refine ⟨A'.map B.subtype, Subgroup.map_subtype_le A', ?_, ?_, ?_⟩
  · calc H = H'.map B.subtype := ((Subgroup.subgroupOf_map_subtype H B).trans
          (inf_eq_left.mpr hH)).symm
      _ ≤ A'.map B.subtype := Subgroup.map_mono hH'A'
  · calc Subgroup.map B.subtype A' ⊓ W
        = Subgroup.map B.subtype A' ⊓ Subgroup.map B.subtype W' := by rw [hWmap]
      _ = Subgroup.map B.subtype (A' ⊓ W') := by
          rw [Subgroup.map_inf _ _ _ B.subtype_injective]
      _ = ⊥ := by rw [hcompl'.inf_eq_bot, Subgroup.map_bot]
  · calc Subgroup.map B.subtype A' ⊔ W
        = Subgroup.map B.subtype A' ⊔ Subgroup.map B.subtype W' := by rw [hWmap]
      _ = Subgroup.map B.subtype (A' ⊔ W') := by rw [Subgroup.map_sup]
      _ = Subgroup.map B.subtype ⊤ := by rw [hcompl'.sup_eq_top]
      _ = B := by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem setup_of_cfg {β : Ω} (hcfg : S171.Cfg Ω p B x L) (hpre : GLAStdSubPre p B x L D K)
    (hK : GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set Ω)) K)
    (hch : IsChevSimple 2 (PSimple p K)) (hβ : β ∈ B) (hβD : β ∉ D)
    (hni : ¬ InnDiagOn p (Subgroup.zpowers β) K) :
    ∃ (A : Subgroup Ω) (d : Ω), A ≤ B ∧ x ∉ A ∧ Setup p L K A d β ∧
      Nat.card B = p * Nat.card A := by
  have hp := hcfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hxCL : x ∈ Subgroup.centralizer (L : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  have hLx : L ≤ Subgroup.centralizer ({x} : Set Ω) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 hxCL l hl
  obtain ⟨y, hyD, hyx⟩ := S171.exists_y hp hcfg.ne_one hpre
  have hyB : y ∈ B := hpre.1 hyD
  have hLcs : L ⊓ Subgroup.centralizer (D : Set Ω) =
      L ⊓ Subgroup.centralizer ({y} : Set Ω) :=
    S171.L_cs_eq hp hcfg.ne_one hpre hyD hyx hLx
  have hβpow : β ^ p = 1 := hcfg.elem.2 β hβ
  have hypow : y ^ p = 1 := hcfg.elem.2 y hyB
  have hy_ne : y ≠ 1 := fun h => hyx (h.symm ▸ Subgroup.one_mem (Subgroup.zpowers x))
  have hcomm_yβ : ∀ a ∈ Subgroup.zpowers y, ∀ b ∈ Subgroup.zpowers β, Commute a b :=
    fun a ha b hb => hcfg.elem.comm (Subgroup.zpowers_le.2 hyB ha) (Subgroup.zpowers_le.2 hβ hb)
  have hHW : (Subgroup.zpowers y ⊔ Subgroup.zpowers β) ⊓ Subgroup.zpowers x = ⊥ := by
    refine le_antisymm ?_ bot_le
    rintro g ⟨hgH, hgx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (CFSG.mem_sup_of_commute hcomm_yβ).1 hgH
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hgD : y ^ i * β ^ j ∈ D := Subgroup.zpowers_le.2 hpre.2.2.2.1 hgx
    have hyiD : y ^ i ∈ D := Subgroup.zpowers_le.2 hyD (Subgroup.zpow_mem_zpowers y i)
    have hβjD : β ^ j ∈ D := by
      have h := D.mul_mem (D.inv_mem hyiD) hgD
      rwa [inv_mul_cancel_left] at h
    by_cases hbj : β ^ j = 1
    · have hyi_mem : y ^ i ∈ Subgroup.zpowers x := by
        have h1 : y ^ i = y ^ i * β ^ j := by rw [hbj, mul_one]
        rw [h1]
        exact hgx
      have hyi1 : y ^ i = 1 := by
        by_contra hne
        have hzy := TauCeti.zpowers_eq_zpowers_of_mem_zpowers hp hypow hne
          (Subgroup.zpow_mem_zpowers y i)
        have hy_mem : y ∈ Subgroup.zpowers (y ^ i) := by
          rw [hzy]
          exact Subgroup.mem_zpowers y
        exact hyx (Subgroup.zpowers_le.2 hyi_mem hy_mem)
      rw [hyi1, hbj, mul_one]
      exact Subgroup.mem_bot.mpr rfl
    · exfalso
      have hzy := TauCeti.zpowers_eq_zpowers_of_mem_zpowers hp hβpow hbj
        (Subgroup.zpow_mem_zpowers β j)
      have hβmem : β ∈ Subgroup.zpowers (β ^ j) := by
        rw [hzy]
        exact Subgroup.mem_zpowers β
      exact hβD (Subgroup.zpowers_le.2 hβjD hβmem)
  have hHle : Subgroup.zpowers y ⊔ Subgroup.zpowers β ≤ B :=
    sup_le (Subgroup.zpowers_le.2 hyB) (Subgroup.zpowers_le.2 hβ)
  have hWle : Subgroup.zpowers x ≤ B := Subgroup.zpowers_le.2 hcfg.mem
  obtain ⟨A, hAB, hHA, hAW, hAsup⟩ :=
    exists_isCompl_of_isElemAbelian hp hcfg.elem hWle hHle hHW
  have hxA : x ∉ A := by
    intro hx
    have hxW : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
    have hxbot : x ∈ (⊥ : Subgroup Ω) := by
      rw [← hAW]
      exact ⟨hx, hxW⟩
    exact hcfg.ne_one (by simpa using hxbot)
  have hyA : y ∈ A := hHA (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))
  have hβA : β ∈ A := hHA (Subgroup.mem_sup_right (Subgroup.mem_zpowers β))
  have hcommAW : ∀ a ∈ A, ∀ b ∈ Subgroup.zpowers x, Commute a b :=
    fun a ha b hb => hcfg.elem.comm (hAB ha) (hWle hb)
  have hdisjAW : A ⊓ Subgroup.zpowers x = ⊥ := hAW
  have hWcard : Nat.card ↥(Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one
  have hcardB : Nat.card B = p * Nat.card A := by
    have h := CFSG.card_sup_eq_mul_of_commute A (Subgroup.zpowers x) hcommAW hdisjAW
    rw [hAsup, hWcard] at h
    rw [h, Nat.mul_comm]
  refine ⟨A, y, hAB, hxA, ?_, hcardB⟩
  have hfaith : A ⊓ Subgroup.centralizer (L : Set Ω) = ⊥ := by
    refine le_antisymm ?_ bot_le
    rintro g ⟨hgA, hgC⟩
    have hgB : g ∈ B := hAB hgA
    have hgx : g ∈ Subgroup.zpowers x := (hcfg.cent g hgB).1 hgC
    have hbot : g ∈ (⊥ : Subgroup Ω) := by
      rw [← hAW]
      exact ⟨hgA, hgx⟩
    simpa using hbot
  have hBK : B ≤ Subgroup.normalizer (K : Set Ω) := S171.B_norm_K hcfg.elem hcfg.norm hpre
  have hcompD : IsComponentOf K (L ⊓ Subgroup.centralizer (D : Set Ω)) :=
    hpre.2.2.2.2.2.1
  have hlayerD : GLALayer (L ⊓ Subgroup.centralizer (D : Set Ω)) = K :=
    hpre.2.2.2.2.1.symm
  refine ⟨hcfg.prime, hcfg.odd, hcfg.qs, hcfg.chev2, hcfg.elem.mono hAB,
    S171.innerDiagMarking_mono hcfg.idiag hAB, hfaith, hyA, hy_ne, hβA, ?_, ?_, hch,
    hBK hβ, hni⟩
  · exact ⟨hLcs ▸ hcompD, hLcs ▸ hlayerD⟩
  · exact hLcs ▸ hK

theorem card_le_of_twoLocal (hcfg : S171.Cfg Ω p B x L) (hmax : S171.MaxG p B)
    {E U : Subgroup Ω} (hEL : E ≤ L) (hUL : U ≤ L) (hE : IsElemAbelian p E)
    (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥) (hEU : E ≤ Subgroup.normalizer (U : Set Ω)) :
    p * Nat.card E ≤ Nat.card B * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Ω)) := by
  have hp := hcfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hxCL : x ∈ Subgroup.centralizer (L : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  have hxp : x ^ p = 1 := hcfg.elem.2 x hcfg.mem
  have hWle : Subgroup.zpowers x ≤ B := Subgroup.zpowers_le.2 hcfg.mem
  have hcommEx : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers x, Commute a b := by
    intro a ha b hb
    have hbC : b ∈ Subgroup.centralizer (L : Set Ω) := Subgroup.zpowers_le.2 hxCL hb
    exact Subgroup.mem_centralizer_iff.1 hbC a (hEL ha)
  have hsupE : IsElemAbelian p (E ⊔ Subgroup.zpowers x) :=
    IsElemAbelian.sup_of_commute hE (isElemAbelian_zpowers hxp) hcommEx
  have hxCU : x ∈ Subgroup.centralizer (U : Set Ω) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_iff.1 hxCL u (hUL hu)
  have hxNU : x ∈ Subgroup.normalizer (U : Set Ω) :=
    Subgroup.centralizer_le_normalizer (U : Set Ω) hxCU
  have hsupN : E ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (U : Set Ω) :=
    sup_le hEU (Subgroup.zpowers_le.2 hxNU)
  have hcardB : Nat.card ↥(E ⊔ Subgroup.zpowers x) ≤ Nat.card B :=
    hmax (E ⊔ Subgroup.zpowers x) U hsupE hU hU1 hsupN
  have hEN : E ≤ Subgroup.normalizer (Subgroup.zpowers x : Set Ω) := by
    intro a ha
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcommEx a ha b hb).eq.symm
  have hprod :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := E) (K := Subgroup.zpowers x) hEN
  have hWcard : Nat.card ↥(Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hxp hcfg.ne_one
  have hinf_le : Nat.card ↥(E ⊓ Subgroup.zpowers x) ≤
      Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Ω)) :=
    Subgroup.card_le_of_le (inf_le_inf_left E (Subgroup.zpowers_le.2 hxCL))
  calc p * Nat.card E = Nat.card E * p := Nat.mul_comm _ _
    _ = Nat.card ↥(E ⊔ Subgroup.zpowers x) * Nat.card ↥(E ⊓ Subgroup.zpowers x) := by
        rw [hprod, hWcard]
    _ ≤ Nat.card B * Nat.card ↥(E ⊓ Subgroup.zpowers x) := Nat.mul_le_mul_right _ hcardB
    _ ≤ Nat.card B * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Ω)) :=
        Nat.mul_le_mul_left _ hinf_le

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end

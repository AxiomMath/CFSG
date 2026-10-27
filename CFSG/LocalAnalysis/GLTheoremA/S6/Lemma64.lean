module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Setup
public import CFSG.LocalAnalysis.GLTheoremA.S6.Inputs6364
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma6364Aux

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure Lemma64Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i267 : I267At G p
  i71 : I71U3At G p

namespace L64

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem isElemAbelian_zpowers {x : G} (hx : x ^ p = 1) : IsElemAbelian p (Subgroup.zpowers x) := by
  refine ⟨inferInstance, fun y hy => ?_⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem isBmax_of_card_le (hp : p.Prime) {B B' T : Subgroup G} (hB : GLAIsBmax p B)
    (hB' : IsElemAbelian p B') (hcard : Nat.card B ≤ Nat.card B') (hT : T ≠ ⊥)
    (hT2 : IsPGroup 2 T) (hBT : B' ≤ Subgroup.normalizer (T : Set G)) : GLAIsBmax p B' :=
  ⟨hB', le_antisymm (card_le_pow_glaTwoLocalRank hp hB' hT hT2 hBT)
    (by rw [← hB.2.1]; exact hcard), T, hT, hT2, hBT⟩

theorem mem_of_isBmax_of_commute (hp : p.Prime) {B' T : Subgroup G} {x : G} (hB' : GLAIsBmax p B')
    (hx : x ^ p = 1) (hcomm : ∀ b ∈ B', b * x = x * b) (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hBT : B' ≤ Subgroup.normalizer (T : Set G)) (hxT : ∀ t ∈ T, t * x = x * t) : x ∈ B' := by
  have hZ : IsElemAbelian p (Subgroup.zpowers x) := isElemAbelian_zpowers hx
  have hE : IsElemAbelian p (B' ⊔ Subgroup.zpowers x) := by
    refine isElemAbelian_sup_of_commute hB'.1 hZ fun b hb => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_left (hcomm b hb).symm m).eq
  have hxN : x ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hxT)
  have hEN : B' ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (T : Set G) :=
    sup_le hBT (Subgroup.zpowers_le.2 hxN)
  have hEq := GLAIsBmax.eq_of_le hp hB' le_sup_left hE hT hT2 hEN
  rw [← hEq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem centModEqZpowers_of_card (hp : p.Prime) {B' L : Subgroup G} {x : G} (hxB : x ∈ B')
    (hx1 : x ≠ 1) (hxp : x ^ p = 1) (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hcard : Nat.card ↥(B' ⊓ centModSubgroup p L) = p) : CentModEqZpowers p B' L x := by
  haveI := Fact.mk hp
  have hxc : x ∈ centModSubgroup p L := centMod_iff.1 (centMod_of_mem_centralizer hxL)
  have hle : Subgroup.zpowers x ≤ B' ⊓ centModSubgroup p L :=
    Subgroup.zpowers_le.2 ⟨hxB, hxc⟩
  have heq : Subgroup.zpowers x = B' ⊓ centModSubgroup p L := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcard, Nat.card_zpowers, orderOf_eq_prime hxp hx1]
  intro b hb
  constructor
  · intro h
    rw [heq]
    exact ⟨hb, centMod_iff.1 h⟩
  · intro h
    rw [heq] at h
    exact centMod_iff.2 h.2

theorem glaTwoLocalRank_lt_of_pRank_lt (hp : p.Prime) {q : ℕ} (hq : q.Prime) {X B : Subgroup G}
    (hB : GLAIsBmax p B) (h : CFSG.Open.pRank p B < GLATwoLocalRank q ↥X) :
    GLATwoLocalRank p G < GLATwoLocalRank q G := by
  rw [L6364.pRank_eq_of_card hp hB.1 hB.2.1] at h
  exact h.trans_le (glaTwoLocalRank_subgroup_le hq.one_lt X)

end L64

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem lemma64_holds (hc : S6Ctx G p) (hin : Lemma64Inputs G p) (h62 : Lemma62At G p)
    (h63 : Lemma63At G p) : Lemma64At G p := by
  intro q hq hq2 hqp B x L hTq
  obtain ⟨⟨hBmax, hxB, hx1, hLcomp, hBL, hcent⟩, hchev⟩ := hTq
  have hBel : IsElemAbelian p B := hBmax.1
  have hxp : x ^ p = 1 := hBel.2 x hxB
  have hLC : L ≤ Subgroup.centralizer ({x} : Set G) := hLcomp.1
  have hBC : B ≤ Subgroup.centralizer ({x} : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact isElemAbelian_commute hBel hxB hb
  have hXC : L ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := sup_le hLC hBC
  have hXN : L ⊔ B ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBL
  have hCk := kGroup_centralizer hc hx1
  have hXk : CFSG.Open.IsKGroup ↥(L ⊔ B) := hCk.of_le hXC
  have hLL : GLAPComponent p L L := glaPComponent_of_le hc.prime hLcomp le_rfl hLC
  have hLay : GLAPLayer p (L ⊔ B) = L := L6364.glaPLayer_sup_eq hc.prime hLL hBL (GLAIsBmax.isPGroup hBmax)
  have hcardC := L6364.card_inf_centModSubgroup hc.prime hBel hxB hx1 hcent
  have hrank : p ^ GLATwoLocalRank p ↥(L ⊔ B) ≤ Nat.card B := by
    rw [hBmax.2.1]
    exact Nat.pow_le_pow_right hc.prime.pos (glaTwoLocalRank_subgroup_le hc.prime.one_lt _)
  have hxL : x ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun l hl =>
      (Subgroup.mem_centralizer_iff.1 (hLC hl) x rfl).symm
  rcases hin.i267 hc.prime hc.odd q hq hq2 hqp (L ⊔ B) L B hXk hLay hchev hBel le_sup_right hrank
    (pow_four_le_card_of_bmax hc hBmax) hcardC with
    ⟨B', D, J, hB'el, hB'X, hInD, h1, h2, h3⟩ | hb | hcc | hd | he
  ·
    have hB'N : B' ≤ Subgroup.normalizer (L : Set G) := hB'X.trans hXN
    have hB'C : B' ≤ Subgroup.centralizer ({x} : Set G) := hB'X.trans hXC
    have hB'max : GLAIsBmax p B' ∧ x ∈ B' := by
      rcases h1 with h | ⟨hcard, T, hTX, hT1, hT2, hB'T⟩
      · subst h
        exact ⟨hBmax, hxB⟩
      · have hmax := L64.isBmax_of_card_le hc.prime hBmax hB'el hcard hT1 hT2 hB'T
        refine ⟨hmax, L64.mem_of_isBmax_of_commute hc.prime hmax hxp (fun b hb => ?_) hT1 hT2
          hB'T (fun t ht => ?_)⟩
        · exact (Subgroup.mem_centralizer_iff.1 (hB'C hb) x rfl).symm
        · exact (Subgroup.mem_centralizer_iff.1 (hXC (hTX ht)) x rfl).symm
    have hcent' : CentModEqZpowers p B' L x :=
      L64.centModEqZpowers_of_card hc.prime hB'max.2 hx1 hxp hxL h2
    have hTq' : InTq q p B' x L := ⟨⟨hB'max.1, hB'max.2, hx1, hLcomp, hB'N, hcent'⟩, hchev⟩
    have hInD' : InD p B' x L D J := hInD
    have hlt : GLATwoLocalRank p G < GLATwoLocalRank q G := by
      rcases h3 with h3 | ⟨T, hTX, hT1, hT2, hDT, hcov⟩
      · exact L64.glaTwoLocalRank_lt_of_pRank_lt hc.prime hq hBmax h3
      · exfalso
        refine h62 q hq hq2 hqp B' x L hTq' D J
          ⟨hInD', Subgroup.normalizer (T : Set G), ⟨T, hT1, hT2, rfl⟩, hDT, ?_⟩
        show (Subgroup.normalizer (T : Set G) ⊓ J) ⊔ GLAPPrimeCoreOf p J = J
        refine le_antisymm (sup_le inf_le_right (Subgroup.map_subtype_le _)) ?_
        calc J = (((L ⊔ B) ⊓ Subgroup.normalizer (T : Set G)) ⊓ J) ⊔ GLAPPrimeCoreOf p J := hcov.symm
          _ ≤ (Subgroup.normalizer (T : Set G) ⊓ J) ⊔ GLAPPrimeCoreOf p J :=
            sup_le_sup_right (inf_le_inf_right _ inf_le_right) _
    rcases h63 q hq hq2 hqp B' x L hTq' hlt with hU | hnoD
    ·
      have hle := hin.i71 hc.prime hc.odd q hq hq2 hqp _ L B hCk hLcomp hU hBel hBL
      rw [hcardC] at hle
      have hcardB : Nat.card B = p ^ 4 :=
        le_antisymm (by rw [pow_succ]; exact hle) (pow_four_le_card_of_bmax hc hBmax)
      obtain ⟨Q, hQp, hdvd, hlie⟩ := hU
      exact Or.inl ⟨hcardB, Q, hQp, Or.inr ⟨hlie, hdvd⟩⟩
    · exact absurd hInD' (hnoD D J)
  ·
    exact Or.inl ⟨hb.1, hb.2.2⟩
  ·
    exact Or.inr (Or.inl ⟨hcc.1, L6364.isDirectZpowersInf_of_cent hxB hcent hcc.2.1 hcc.2.2.1,
      hcc.2.2.2.1, hcc.2.2.2.2⟩)
  ·
    exact Or.inr (Or.inr (Or.inl ⟨hd.1, L6364.isDirectZpowersInf_of_cent hxB hcent hd.2.1 hd.2.2.1,
      hd.2.2.2.1, hd.2.2.2.2⟩))
  ·
    exact Or.inr (Or.inr (Or.inr he))

end CFSG.LocalAnalysis.GLTheoremA

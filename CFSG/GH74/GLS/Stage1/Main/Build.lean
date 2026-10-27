module

public import CFSG.GH74.GLS.Stage1.Main.Basic
public import CFSG.GH74.GLS.Stage1.Main.BrFusedNoDiag
public import CFSG.GH74.GLS.Stage1.Main.BridgeField

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7 CFSG.GH74.GLS.Stage1.Thm3.Sec8

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem detail_of_bridge (hdet : NoFAutBridge) (hdet1 : NoFAutBridgeR1) {k : Kind} (hcen : Cen2 G z S)
    (hdata : Stage1Data G z S k) (hk : k = Kind.g2 ∨ k = Kind.psp4 ∨ ∃ ε : Bool, k = Kind.l4 ε)
    (hr : RigidData G z S) (hc6 : ∀ K : Subgroup G, IsRigidRankOneComp z K → Cond6a S K)
    (htwo : L4TwoFieldStmt G z k S) :
    Stage1Detail G z k S := by
  refine ⟨?_, (fun h => by rcases hk with rfl | rfl | ⟨ε, rfl⟩ <;> cases h), htwo⟩
  rcases hr with ⟨K₁, K₂, h4⟩ | ⟨K₀, h6, hg⟩
  · exact hdet G z S k hcen hdata hk K₁ K₂ h4 hc6
  · exact hdet1 G z S k hcen hdata hk K₀ h6 hg hc6

theorem out_g2 (hbase : BaseBridge) (hG2 : G2ShapeBridge) (hdet : NoFAutBridge) (hdet1 : NoFAutBridgeR1)
    (hcen : Cen2 G z S) (hzc : ZCen z S) (hr : RigidData G z S) (hc6 : ∀ K : Subgroup G, IsRigidRankOneComp z K → Cond6a S K)
    (hg : G2Term G z S) (hrank : pRank 2 G = 3) : Stage1Out G z S Kind.g2 := by
  have hb : Stage1Base G z S :=
    Stage1Base.of_parts hzc (hbase G z S hcen (Or.inl hg))
  have hone : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v := by
    obtain ⟨p, f, -, -, -, hc, -⟩ := hg
    intro u v hu hv
    exact (hc u hu).symm.trans (hc v hv)
  have h1 : Stage1G2 G z S := ⟨hb, hone, (hG2 G z S hcen hg).1, (hG2 G z S hcen hg).2⟩
  have hdata : Stage1Data G z S Kind.g2 := Stage1Data.g2 h1
  exact Stage1Out.g2 ⟨hcen.std, hcen.central, hcen.sylow, hdata,
    detail_of_bridge hdet hdet1 hcen hdata (Or.inl rfl) hr hc6
      (L4TwoFieldStmt.of_one_class hcen.central hone Kind.g2), fun _ => hrank⟩ hg

theorem out_psp4 (hbase : BaseBridge) (hpair : PairBridge7) (hpsp : PSp4Extra) (hdet : NoFAutBridge) (hdet1 : NoFAutBridgeR1)
    (hcen : Cen2 G z S) (hzc : ZCen z S) (hr : RigidData G z S) (hc6 : ∀ K : Subgroup G, IsRigidRankOneComp z K → Cond6a S K)
    {q : ℕ} (hT : Term7Out G z S q 1) : Stage1Out G z S Kind.psp4 := by
  have hb : Stage1Base G z S :=
    Stage1Base.of_parts hzc (hbase G z S hcen (Or.inr (Or.inl ⟨q, 1, hT⟩)))
  obtain ⟨L₁, L₂, hp⟩ := hpair G z S q 1 hcen hT hb
  obtain ⟨hidx, hx⟩ := hpsp G z S q hcen hT L₁ L₂ hp
  have h4 : Stage1PSp4 G z S q L₁ L₂ := ⟨hp, hidx, hx⟩
  have hdata : Stage1Data G z S Kind.psp4 := Stage1Data.psp4 ⟨q, L₁, L₂, h4⟩
  exact Stage1Out.psp4 ⟨hcen.std, hcen.central, hcen.sylow, hdata,
    detail_of_bridge hdet hdet1 hcen hdata (Or.inr (Or.inl rfl)) hr hc6
      (L4TwoFieldStmt.of_ne (fun ε h => by cases h)),
      fun h => by rcases h with h | h <;> cases h⟩ q L₁ L₂ h4 hT

theorem out_l4NF (hbase : BaseBridge) (hpair : PairBridge7) (hl4 : L4NFExtra) (hfld : L4NFField) (hdet : NoFAutBridge) (hdet1 : NoFAutBridgeR1)
    (hcen : Cen2 G z S) (hzc : ZCen z S) (hr : RigidData G z S) (hc6 : ∀ K : Subgroup G, IsRigidRankOneComp z K → Cond6a S K)
    {q : ℕ} {w : G} (hT : Term7Out G z S q w) (hw : w ≠ 1) :
    ∃ ε : Bool, Stage1Out G z S (Kind.l4 ε) := by
  have hodd : Odd q := by obtain ⟨K₁, K₂, -, h, -⟩ := hT; exact h
  have hq : q % 4 = 1 ∨ q % 4 = 3 := by
    obtain ⟨k, hk⟩ := hodd; omega
  obtain ⟨ε, hε⟩ : ∃ ε : Bool, q % 4 = (if ε then 3 else 1) := by
    rcases hq with h | h
    · exact ⟨false, by simpa using h⟩
    · exact ⟨true, by simpa using h⟩
  refine ⟨ε, ?_⟩
  have hb : Stage1Base G z S :=
    Stage1Base.of_parts hzc (hbase G z S hcen (Or.inr (Or.inl ⟨q, w, hT⟩)))
  obtain ⟨L₁, L₂, hp⟩ := hpair G z S q w hcen hT hb
  obtain ⟨hidx, hpgl, x, hx, hy, hyc⟩ := hl4 G z S q w ε hcen hT hw hε L₁ L₂ hp
  have hmod : q % 8 ≠ (if ε then 1 else 7) := by
    cases ε <;> simp at hε ⊢ <;> omega
  have h4 : Stage1L4 G z S ε q L₁ L₂ :=
    ⟨hp, hmod, hidx, hpgl, Or.inr ⟨hε, x, hx, hy, hyc⟩, noDiag_of_twoClass hcen.central hx⟩
  have hdata : Stage1Data G z S (Kind.l4 ε) := Stage1Data.l4 ε ⟨q, L₁, L₂, h4⟩
  exact Stage1Out.l4NF ε ⟨hcen.std, hcen.central, hcen.sylow, hdata,
    detail_of_bridge hdet hdet1 hcen hdata (Or.inr (Or.inr ⟨ε, rfl⟩)) hr hc6
      (L4TwoFieldStmt.of_term7 hfld hcen hT hw hp (Kind.l4 ε)),
      fun h => by rcases h with h | h <;> cases h⟩ q L₁ L₂ h4 hε w hw hT

theorem out_l4F (hbase : BaseBridge) (hpair : PairBridgeF) (hl4 : L4FExtra) (hdet : NoFAutBridge) (hdet1 : NoFAutBridgeR1)
    (hcen : Cen2 G z S) (hzc : ZCen z S) (hr : RigidData G z S) (hc6 : ∀ K : Subgroup G, IsRigidRankOneComp z K → Cond6a S K)
    {ε : Bool} (hT : L4U4TermTypeE ε G z S) : Stage1Out G z S (Kind.l4 ε) := by
  have hb : Stage1Base G z S :=
    Stage1Base.of_parts hzc (hbase G z S hcen (Or.inr (Or.inr ⟨ε, hT⟩)))
  obtain ⟨q, L₁, L₂, hp, hQ⟩ := hpair G z S ε hcen hT hb
  obtain ⟨hq8, hidx, hpgl⟩ := hl4 G z S ε q hcen hT L₁ L₂ hp
  have hone : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v := fun u v hu hv =>
    (hT.1 u hu).symm.trans (hT.1 v hv)
  have hmod : q % 8 ≠ (if ε then 1 else 7) := by
    cases ε <;> simp at hq8 ⊢ <;> omega
  have hq4 : q % 4 = (if ε then 1 else 3) := by
    cases ε <;> simp at hq8 ⊢ <;> omega
  have h4 : Stage1L4 G z S ε q L₁ L₂ :=
    ⟨hp, hmod, hidx, hpgl, Or.inl ⟨hq4, hone⟩, fun _ => fused_noDiag hcen hT⟩
  have hdata : Stage1Data G z S (Kind.l4 ε) := Stage1Data.l4 ε ⟨q, L₁, L₂, h4⟩
  exact Stage1Out.l4F ε ⟨hcen.std, hcen.central, hcen.sylow, hdata,
    detail_of_bridge hdet hdet1 hcen hdata (Or.inr (Or.inr ⟨ε, rfl⟩)) hr hc6
      (L4TwoFieldStmt.of_one_class hcen.central hone (Kind.l4 ε)),
      fun h => by rcases h with h | h <;> cases h⟩ q L₁ L₂ h4 hQ

theorem out_sporadic (hspor : SporadicNoRank1) (hcen : Cen2 G z S) {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11)
    (hsp : Stage1Sporadic G z S n) :
    (Stage1Out G z S Kind.mcl ∨ Stage1Out G z S Kind.ly) ∧
      (n ≤ 9 → Stage1Out G z S Kind.mcl) ∧ (10 ≤ n → Stage1Out G z S Kind.ly) := by
  have hdet : ∀ k : Kind, k ≠ Kind.m12 → Stage1Detail G z k S := fun k hk =>
    ⟨fun s _ K hK h1 _ => absurd h1 (hspor G z S n hcen hn8 hsp K hK), fun h => absurd h hk,
      L4TwoFieldStmt.of_one_class hcen.central hsp.one_class k⟩
  have hmcl : n ≤ 9 → Stage1Out G z S Kind.mcl := fun h9 =>
    Stage1Out.mcl ⟨hcen.std, hcen.central, hcen.sylow,
      Stage1Data.mcl ⟨n, by omega, hsp⟩, hdet Kind.mcl (by intro h; cases h),
      fun h => by rcases h with h | h <;> cases h⟩
  have hly : 10 ≤ n → Stage1Out G z S Kind.ly := fun h10 =>
    Stage1Out.ly ⟨hcen.std, hcen.central, hcen.sylow,
      Stage1Data.ly ⟨n, by omega, hsp⟩, hdet Kind.ly (by intro h; cases h),
      fun h => by rcases h with h | h <;> cases h⟩
  refine ⟨?_, hmcl, hly⟩
  by_cases h9 : n ≤ 9
  · exact Or.inl (hmcl h9)
  · exact Or.inr (hly (by omega))

end CFSG.GH74.GLS.Stage1.Main

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AEightThirteenR3
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentTenFourteenNarrow
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt
import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeDataAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open

@[expose] def KFactIIModelThreeCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.RankThreeEven.IIModel G →
    ∃ P : Sylow 3 G, rankThreeAschCore 2 3 (P : Subgroup G) = ⊤

theorem normalizer_le_rankThreeAschCore {G : Type*} [Group G] [Finite G] {P E X : Subgroup G}
    (hEP : E ≤ P) (hE : IsElemAbelian 3 E) {k : ℕ} (hk : 3 ≤ k) (hEc : Nat.card E = 3 ^ k)
    (hXE : X ≤ E) (hXc : Nat.card X = 3 ^ 2) :
    Subgroup.normalizer (X : Set G) ≤ rankThreeAschCore 2 3 P := by
  have h31 : 1 < 3 := by norm_num
  have hX : IsElemAbelian 3 X :=
    ⟨⟨⟨fun a b => Subtype.ext (show (a : G) * b = b * a from congrArg Subtype.val
      (hE.1.is_comm.comm ⟨a, hXE a.2⟩ ⟨b, hXE b.2⟩))⟩⟩, fun x hx => hE.2 x (hXE hx)⟩
  refine le_sSup ⟨X, hXE.trans hEP, CFSG.SectionRank.le_pRank h31 le_rfl hX hXc, ?_, rfl⟩
  refine hk.trans
    (CFSG.SectionRank.le_pRank h31 (le_sup_of_le_right (le_inf hEP fun e he => ?_)) hE hEc)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hXE hx⟩ ⟨e, he⟩)

theorem rankThreeAschCore_eq_top_of_planes {G : Type*} [Group G] [Finite G] {E X₁ X₂ : Subgroup G}
    (hE : IsElemAbelian 3 E) {k : ℕ} (hk : 3 ≤ k) (hEc : Nat.card E = 3 ^ k) (h1 : X₁ ≤ E)
    (h1c : Nat.card X₁ = 3 ^ 2) (h2 : X₂ ≤ E) (h2c : Nat.card X₂ = 3 ^ 2)
    (hgen : Subgroup.normalizer (X₁ : Set G) ⊔ Subgroup.normalizer (X₂ : Set G) = ⊤) :
    ∃ P : Sylow 3 G, rankThreeAschCore 2 3 (P : Subgroup G) = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hEP⟩ := (IsPGroup.of_card hEc).exists_le_sylow
  refine ⟨P, eq_top_iff.2 ?_⟩
  rw [← hgen]
  exact sup_le (normalizer_le_rankThreeAschCore hEP hE hk hEc h1 h1c)
    (normalizer_le_rankThreeAschCore hEP hE hk hEc h2 h2c)

@[expose] def ThreePlaneGen (X : Type*) [Group X] : Prop :=
  ∃ (E X₁ X₂ : Subgroup X) (k : ℕ), IsElemAbelian 3 E ∧ 3 ≤ k ∧ Nat.card E = 3 ^ k ∧ X₁ ≤ E ∧
    Nat.card X₁ = 3 ^ 2 ∧ X₂ ≤ E ∧ Nat.card X₂ = 3 ^ 2 ∧
    Subgroup.normalizer (X₁ : Set X) ⊔ Subgroup.normalizer (X₂ : Set X) = ⊤

theorem ThreePlaneGen.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (h : ThreePlaneGen X)
    (e : X ≃* Y) : ThreePlaneGen Y := by
  obtain ⟨E, X₁, X₂, k, hE, hk, hEc, h1, h1c, h2, h2c, hgen⟩ := h
  refine ⟨E.map e.toMonoidHom, X₁.map e.toMonoidHom, X₂.map e.toMonoidHom, k,
    RankOneCent.isElemAbelian_map _ hE, hk, by rw [Subgroup.card_map_of_injective e.injective, hEc],
    Subgroup.map_mono h1, by rw [Subgroup.card_map_of_injective e.injective, h1c],
    Subgroup.map_mono h2, by rw [Subgroup.card_map_of_injective e.injective, h2c], ?_⟩
  rw [← Subgroup.map_equiv_normalizer_eq, ← Subgroup.map_equiv_normalizer_eq, ← Subgroup.map_sup,
    hgen, Subgroup.map_top_of_surjective _ e.surjective]

theorem ThreePlaneGen.exists_core_eq_top {G : Type*} [Group G] [Finite G] (h : ThreePlaneGen G) :
    ∃ P : Sylow 3 G, rankThreeAschCore 2 3 (P : Subgroup G) = ⊤ := by
  obtain ⟨E, X₁, X₂, k, hE, hk, hEc, h1, h1c, h2, h2c, hgen⟩ := h
  exact rankThreeAschCore_eq_top_of_planes hE hk hEc h1 h1c h2 h2c hgen

@[expose] def ThreeCoreAt (X : Type*) [Group X] : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* X) →
    ∃ P : Sylow 3 G, rankThreeAschCore 2 3 (P : Subgroup G) = ⊤

theorem threeCoreAt_of_threePlaneGen {M X : Type*} [Group M] [Group X] (e : M ≃* X)
    (h : ThreePlaneGen M) : ThreeCoreAt X := fun _ _ _ ⟨f⟩ =>
  (h.of_mulEquiv (e.trans f.symm)).exists_core_eq_top

theorem threeCoreAt_of_tcGenDatum {M X : Type} [Group M] [Group X] (e : M ≃* X)
    (h : ∀ [Finite M], CFSG.AGLEmbedding.TCGenDatum M 3) : ThreeCoreAt X := by
  intro G _ _ ⟨f⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let g : M ≃* G := e.trans f.symm
  haveI : Finite M := Finite.of_equiv G g.symm.toEquiv
  let T : Sylow 3 M := default
  refine ⟨Sylow.mapSurjective (f := g.toMonoidHom) g.surjective T, ?_⟩
  exact CFSG.AGLEmbedding.glbWeakCore_eq_top_of_mulEquiv Nat.prime_three g
    (Sylow.coe_mapSurjective _ _) (CFSG.AGLEmbedding.weakCoreOfTC M 3 h T)

section List

open CFSG.Assembly.RankThreeEven

theorem kFactIIModelThreeCore_of
    (hCo2 : ThreeCoreAt (TauCeti.CFSGIndex.sporadic .Co2).Group)
    (hTh : ThreeCoreAt (TauCeti.CFSGIndex.sporadic .Th).Group)
    (hU52 : ThreeCoreAt (projSU 5 2 1)) (hU62 : ThreeCoreAt (projSU 6 2 1))
    (hL62 : ThreeCoreAt (projSL 6 (GaloisField 2 1)))
    (hL72 : ThreeCoreAt (projSL 7 (GaloisField 2 1)))
    (hSp82 : ThreeCoreAt (projSp 4 (GaloisField 2 1)))
    (hO8p : ThreeCoreAt (projOmegaPlus 4 (GaloisField 2 1)))
    (hO8m : ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
      ThreeCoreAt (projOmegaMinus 3 (GaloisField 2 1) b c))
    (hL44 : ThreeCoreAt (projSL 4 (GaloisField 2 2)))
    (hSp64 : ThreeCoreAt (projSp 3 (GaloisField 2 2)))
    (hU58 : ThreeCoreAt (projSU 5 2 3))
    (hF42 : ThreeCoreAt (TauCeti.CFSGIndex.lie f4TwoIndex).Group) :
    KFactIIModelThreeCore := by
  intro G _ _ hII
  rcases hII with e | e | hcl | e
  · exact hCo2 G e
  · exact hTh G e
  · rcases hcl with e | e | e | e | e | e | ⟨b, c, hbc, e⟩ | e | e | e
    · exact hU52 G e
    · exact hU62 G e
    · exact hL62 G e
    · exact hL72 G e
    · exact hSp82 G e
    · exact hO8p G e
    · exact hO8m b c hbc G e
    · exact hL44 G e
    · exact hSp64 G e
    · exact hU58 G e
  · exact hF42 G e

end List

theorem agl81EightThirteenCKnown_of_threeCore (h433 : CFSG.RankThree.PartTwo.Item433)
    (h : KFactIIModelThreeCore) : AGL81EightThirteenCKnown :=
  agl81EightThirteenCKnown_of_iiModel h433 fun G _ _ hII hS h3 => by
    exfalso
    haveI := hS.simple
    obtain ⟨P, hP⟩ := h G hII
    obtain ⟨H, hH, hle⟩ := hS.pre 3 h3 P
    rw [hP, top_le_iff] at hle
    exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hH hle

end CFSG.LocalAnalysis.RankThreeTheoremC

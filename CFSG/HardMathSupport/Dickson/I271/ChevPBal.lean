module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Split
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma31Proof
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Families
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4

@[expose] def InnerNoncyclicIn {X : Type} [Group X] (B K : Subgroup X) : Prop :=
  ∃ A : Subgroup X, A ≤ B ∧ ¬ IsCyclic ↥A ∧ A ⊓ Subgroup.centralizer (K : Set X) = ⊥ ∧
    ∀ a ∈ A, ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X)

theorem not_isCyclic_of_elemAbelian {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {C : Subgroup X} (hC : IsElemAbelian p C) (hcard : p ^ 2 ≤ Nat.card C) : ¬ IsCyclic ↥C := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card C := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hC.2 g g.2)
  have hle : orderOf g ≤ p := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hgp)
  have h2 := hp.two_le
  rw [hord] at hle
  nlinarith

theorem exists_faithful_noncyclic {X : Type} [Group X] [Finite X] {p : ℕ} {K B : Subgroup X}
    (hp : p.Prime) (hBel : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (h2 : p ^ 2 ≤ autOrderIn B K) :
    ∃ A : Subgroup X, A ≤ B ∧ ¬ IsCyclic ↥A ∧ A ⊓ Subgroup.centralizer (K : Set X) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨C, hCB, hdisj, -, hcard⟩ := i224_exists_complement hBel
    (inf_le_left : B ⊓ Subgroup.centralizer (K : Set X) ≤ B)
  have hrel : autOrderIn B K * Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) =
      Nat.card B := by
    unfold autOrderIn
    rw [inf_of_le_left hBN, inf_comm]
    exact Subgroup.relIndex_mul_card (Subgroup.centralizer (K : Set X)) B
  have hpos : 0 < Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) := Nat.card_pos
  have hCcard : Nat.card C = autOrderIn B K :=
    Nat.eq_of_mul_eq_mul_left hpos (hcard.symm.trans (hrel.symm.trans (mul_comm _ _)))
  refine ⟨C, hCB, not_isCyclic_of_elemAbelian hp (CFSG.Open.IsElemAbelian.mono hBel hCB)
    (hCcard ▸ h2), ?_⟩
  rw [eq_bot_iff]
  intro x hx
  have hxB : x ∈ B ⊓ Subgroup.centralizer (K : Set X) := ⟨hCB hx.1, hx.2⟩
  have : x ∈ (B ⊓ Subgroup.centralizer (K : Set X)) ⊓ C := ⟨hxB, hx.1⟩
  rw [hdisj] at this
  exact this

end CFSG.HardMathSupport.Dickson.I271

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Planes
public import CFSG.HardMathSupport.Lang.E6Descent.MaxClassRank
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup

theorem bal3MaxClassEightyOne :
    ∀ (X : Type) [Group X] [Finite X] (P : Subgroup X) (z : X) (D : Subgroup X),
      IsPGroup 3 P → orderOf z = 3 → z ∈ centralizer (P : Set X) →
      (∀ y ∈ P, y ∈ centralizer (P : Set X) → y ^ 3 = 1 → y ∈ zpowers z) →
      D ≤ P → IsElemAbelian 3 D → Nat.card D = 3 ^ 2 → z ∈ D →
      (∀ y ∈ P, y ∈ centralizer (D : Set X) → y ∈ D) →
      CFSG.Open.pRank 3 P = 3 → Nat.card P = 81 := by
  classical
  intro X _ _ P z D hP hzo hzc huniq hDP hDe hDc hzD hCD hrk
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  have hzP : z ∈ P := hDP hzD
  obtain ⟨x, hxD, hxz⟩ := exists_mem_notMem_zpowers hp3 hzo hDc
  have hxP : x ∈ P := hDP hxD
  have hx3 : x ^ 3 = 1 := hDe.2 x hxD
  have hx1 : x ≠ 1 := fun h => hxz (h ▸ one_mem _)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hDgen : ∀ d ∈ D, ∃ i j : ℤ, d = z ^ i * x ^ j := fun d hd =>
    exists_zpow_mul_zpow_of_card_eq_sq hp3 hDe hDc hzo hzD hxD hxz hd
  let x' : P := ⟨x, hxP⟩
  have hx'o : orderOf x' = 3 := by rw [Subgroup.orderOf_mk]; exact hxo
  have hC : Subgroup.centralizer ({x'} : Set P) = D.subgroupOf P := by
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      have hgx : (g : X) * x = x * (g : X) := congrArg Subtype.val hg
      have hgz : (g : X) * z = z * (g : X) := mem_centralizer_iff.1 hzc g g.2
      refine hCD g g.2 ?_
      rw [mem_centralizer_iff]
      intro d hd
      obtain ⟨i, j, rfl⟩ := hDgen d hd
      have h1 : Commute (z ^ i * x ^ j) (g : X) :=
        (Commute.zpow_left (show Commute z g from hgz.symm) i).mul_left
          (Commute.zpow_left (show Commute x g from hgx.symm) j)
      exact h1.eq
    · intro hg
      have hgD : (g : X) ∈ D := hg
      have : (g : X) * x = x * (g : X) := (hDe.comm hgD hxD)
      exact Subtype.ext this
  have hC9 : Nat.card (Subgroup.centralizer ({x'} : Set P)) = 3 ^ 2 := by
    rw [hC, ← hDc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDP).toEquiv
  have hmax : CFSG.Walter.W67.IsMaximalClass 3 P :=
    CFSG.Walter.W67.isMaximalClass_of_card_centralizer hP x' hx'o hC9
  obtain ⟨B, hBP, hBe, hBc⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 hp3 P
  rw [hrk] at hBc
  have hBe' : IsElemAbelian 3 (B.subgroupOf P) := IsElemAbelian.comap hBe P.subtype_injective
  have hBc' : Nat.card (B.subgroupOf P) = 27 := by
    rw [show (27 : ℕ) = Nat.card B by rw [hBc]; norm_num]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv
  exact CFSG.HardMathSupport.Lang.E6Descent.card_eq_81_of_maxClass_of_elemAbelian27 hP hmax
    (B.subgroupOf P) hBe' hBc'.ge

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

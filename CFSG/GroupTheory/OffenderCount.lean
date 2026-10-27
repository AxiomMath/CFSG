module

public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.SectionRank

variable {G : Type} [Group G] [Finite G]

private theorem card_sup_inf_centralizer_le_of_pRank {T A V : Subgroup G} {i : ℕ}
    (hA : IsElemAbelian 2 A) (hV : IsElemAbelian 2 V) (hAT : A ≤ T) (hVT : V ≤ T)
    (hrk : pRank 2 T ≤ pRank 2 A + i) :
    Nat.card ↥((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) ≤ 2 ^ i * Nat.card A := by
  let B : Subgroup G := A ⊓ Subgroup.centralizer (V : Set G)
  have hBA : B ≤ A := inf_le_left
  have hBe : IsElemAbelian 2 B := hA.mono hBA
  have hBc : ∀ b ∈ B, ∀ v ∈ V, b * v = v * b := by
    intro b hb v hv
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb).2 v hv).symm
  have hBVe : IsElemAbelian 2 (B ⊔ V) := hBe.sup_of_commute hV hBc
  have hBVT : B ⊔ V ≤ T := sup_le (hBA.trans hAT) hVT
  have hcardB : Nat.card ↥(B ⊔ V) = 2 ^ pRank 2 (B ⊔ V) :=
    card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hBVe
  have hcardA : Nat.card A = 2 ^ pRank 2 A :=
    card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hA
  calc Nat.card ↥(B ⊔ V) = 2 ^ pRank 2 (B ⊔ V) := hcardB
    _ ≤ 2 ^ pRank 2 T := Nat.pow_le_pow_right (by norm_num) (pRank_mono (by norm_num) hBVT)
    _ ≤ 2 ^ (pRank 2 A + i) := Nat.pow_le_pow_right (by norm_num) hrk
    _ = 2 ^ i * Nat.card A := by
        rw [pow_add, ← hcardA, mul_comm]

theorem card_mul_card_inf_centralizer_le {T A V : Subgroup G} {i : ℕ}
    (hA : IsElemAbelian 2 A) (hV : IsElemAbelian 2 V) (hAT : A ≤ T) (hVT : V ≤ T)
    (hrk : pRank 2 T ≤ pRank 2 A + i) :
    Nat.card V * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) ≤
      2 ^ i * (Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) := by
  let B : Subgroup G := A ⊓ Subgroup.centralizer (V : Set G)
  have hcardSup : Nat.card ↥(B ⊔ V) ≤ 2 ^ i * Nat.card A :=
    card_sup_inf_centralizer_le_of_pRank hA hV hAT hVT hrk
  have hVcentB : V ≤ Subgroup.centralizer (B : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb).2 v hv).symm
  have hBnorm : V ≤ Subgroup.normalizer (B : Set G) :=
    hVcentB.trans (Subgroup.centralizer_le_normalizer (B : Set G))
  have hprod : Nat.card V * Nat.card ↥B =
      Nat.card ↥(B ⊔ V) * Nat.card ↥(V ⊓ B) := by
    rw [← CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := V) (K := B) hBnorm, sup_comm V B]
  have hinf : V ⊓ B ≤ V ⊓ Subgroup.centralizer (A : Set G) := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨hx.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hxA : x ∈ A := (Subgroup.mem_inf.mp hx.2).1
    exact congrArg Subtype.val (hA.1.is_comm.comm (⟨a, ha⟩ : A) ⟨x, hxA⟩)
  change Nat.card V * Nat.card ↥B ≤ _
  calc Nat.card V * Nat.card ↥B
      = Nat.card ↥(B ⊔ V) * Nat.card ↥(V ⊓ B) := hprod
    _ ≤ (2 ^ i * Nat.card A) *
        Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
        Nat.mul_le_mul hcardSup (Subgroup.card_le_of_le hinf)
    _ = 2 ^ i * (Nat.card A *
        Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) := by ring

end CFSG.GroupTheory

end

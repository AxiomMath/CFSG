module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Desc
public import CFSG.RankThree.PartTwo.Sec4.Item413AutU3

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec6.BThreeCensus
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank

theorem three_ne_zero_GF64 : (3 : GF64) ≠ 0 := by decide +kernel

theorem suConj_eq_one_iff (A : GU) :
    suConj hU A = 1 ↔ (A : GL (Fin 3) GF64) ∈ StatedScalars (Fin 3) GF64 := by
  rw [← psuConj_eq_one_iff]
  constructor
  · intro hA
    rw [← suDescend_suConj hU hq2, hA, map_one]
  · intro hA
    apply eq_of_suDescend_eq hU hq2
    rw [suDescend_suConj, hA, map_one]

theorem card_le_nine_of_range {G : Type*} [Group G] (Φ : GU →* MulAut G)
    (hker : ∀ A : GU, Φ A = 1 ↔ (A : GL (Fin 3) GF64) ∈ StatedScalars (Fin 3) GF64)
    (B : Subgroup (MulAut G)) (hBr : B ≤ Φ.range)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB3 : ∀ x ∈ B, x ^ 3 = 1) : Nat.card B ≤ 9 := by
  set N := Φ.range
  set ψ : GU →* GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64 :=
    (QuotientGroup.mk' _).comp GU.subtype
  have hk : Φ.ker = ψ.ker := by
    ext A
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hker]
    change _ ↔ QuotientGroup.mk' _ (A : GL (Fin 3) GF64) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set χ : N →* GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64 :=
    (QuotientGroup.kerLift ψ).comp ((QuotientGroup.quotientMulEquivOfEq hk).toMonoidHom.comp
      (QuotientGroup.quotientKerEquivRange Φ).symm.toMonoidHom)
  have hχ : Function.Injective χ :=
    (QuotientGroup.kerLift_injective ψ).comp ((QuotientGroup.quotientMulEquivOfEq hk).injective.comp
      (QuotientGroup.quotientKerEquivRange Φ).symm.injective)
  set E := (B.subgroupOf N).map χ
  have hcardE : Nat.card E = Nat.card B := by
    rw [Subgroup.card_map_of_injective hχ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBr).toEquiv
  rw [← hcardE]
  refine card_le_nine_of_pgl3 three_ne_zero_GF64 E ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hBc _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hB3 _ (Subgroup.mem_subgroupOf.mp hx))
    rw [this, map_one]

theorem card_le_nine_psu (B : Subgroup (MulAut (unitaryPSU hU 3))) (hBr : B ≤ (psuConj hU).range)
    (hB : CFSG.Open.IsElemAbelian 3 B) : Nat.card B ≤ 9 :=
  card_le_nine_of_range (psuConj hU) (psuConj_eq_one_iff) B hBr
    (fun x hx y hy => congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (fun x hx => hB.2 x hx)

end CFSG.AGLEmbedding.ChevOuter.U38

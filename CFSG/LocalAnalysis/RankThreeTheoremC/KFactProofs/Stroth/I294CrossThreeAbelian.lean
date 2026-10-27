module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeClassical
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SigmaDich
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.AbelianTransfer
import CFSG.GroupTheory.WeirSylow.Unitary
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieGUDet

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup
open CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
open CFSG.Quasithin (StatedGU)

theorem I294Cross.sylow_comm_psl {F : Type} [Field F] [Finite F] {n : ℕ} (hn : n ≤ 5)
    (h3 : ¬ 3 ∣ Nat.card F) (h2 : Nat.card F % 3 = 2) :
    ∀ S : Sylow 3 (StatedProj (StatedSL n F)),
      IsMulCommutative (S : Subgroup (StatedProj (StatedSL n F))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hpF : ¬ 3 ∣ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have he : orderOf (Fintype.card F : ZMod 3) = 2 := by
    rw [← Nat.card_eq_fintype_card]; exact I294Cross.orderOf_natCast_two h2
  have hc := sylow_isMulCommutative_of_sigmaModel_of_lt Nat.prime_three
    (G := GL (Fin n) F) (e := orderOf (Fintype.card F : ZMod 3))
    (a := padicValNat 3 (Fintype.card F ^ orderOf (Fintype.card F : ZMod 3) - 1)) (N := n)
    (by rw [he]; omega) (fun P => sylow_GL (by decide) F hpF n P)
  exact sylow_comm_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (sylow_comm_of_subgroup (StatedSL n F) hc)

theorem I294Cross.sylow_comm_psp_two {K : Type} [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K) :
    ∀ S : Sylow 3 (StatedProj (StatedSp 2 K)),
      IsMulCommutative (S : Subgroup (StatedProj (StatedSp 2 K))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hpK : ¬ 3 ∣ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  have hlt : (if Even (orderOf (Fintype.card K : ZMod 3)) then 2 * 2 else 2) /
      orderOf (Fintype.card K : ZMod 3) < 3 := by
    rw [← Nat.card_eq_fintype_card]
    rcases (by omega : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2) with h1 | h2
    · have he : orderOf ((Nat.card K : ℕ) : ZMod 3) = 1 := by
        rw [orderOf_eq_one_iff, ← ZMod.natCast_mod, h1]; rfl
      rw [he]; decide
    · rw [I294Cross.orderOf_natCast_two h2]; decide
  have hc := sylow_isMulCommutative_of_sigmaModel_of_lt Nat.prime_three
    (G := StatedSp 2 K) (e := orderOf (Fintype.card K : ZMod 3))
    (a := padicValNat 3 (Fintype.card K ^ orderOf (Fintype.card K : ZMod 3) - 1))
    (N := if Even (orderOf (Fintype.card K : ZMod 3)) then 2 * 2 else 2) hlt
    (fun P => sylow_Sp (by decide) K hpK 2 P)
  exact sylow_comm_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) hc

theorem I294Cross.sylow_comm_psu {L : Type} [Field L] [Finite L] {q n : ℕ}
    (hL : Nat.card L = q ^ 2) (hq3 : ¬ 3 ∣ q) (hq1 : q % 3 = 1) (hn1 : 1 ≤ n) (hn5 : n ≤ 5) :
    ∀ S : Sylow 3 (StatedProj (StatedSU n q L)),
      IsMulCommutative (S : Subgroup (StatedProj (StatedSU n q L))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := Fintype.ofFinite L
  have hLc : Fintype.card L = q ^ 2 := by rw [Fintype.card_eq_nat_card]; exact hL
  have he : orderOf (-((q : ℕ) : ZMod 3)) = 2 := I294Cross.orderOf_neg_natCast_one hq1
  have hGU : ∀ P : Sylow 3 ↥(StatedGU n q L), IsMulCommutative (P : Subgroup ↥(StatedGU n q L)) :=
    sylow_isMulCommutative_of_sigmaModel_of_lt Nat.prime_three
      (e := orderOf (-((q : ℕ) : ZMod 3))) (by rw [he]; omega)
      (fun P => sylow_GU (by decide) L hLc hq3 hn1 P)
  have hSub := sylow_comm_of_subgroup
    ((StatedSU n q L).subgroupOf (StatedGU n q L)) hGU
  have hSU := sylow_comm_of_surjective
    (Subgroup.subgroupOfEquivOfLe
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.statedSU_le_statedGU
        (L := L) (q := q) (n := n))).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.statedSU_le_statedGU
        (L := L) (q := q) (n := n))).surjective hSub
  exact sylow_comm_of_surjective
    (QuotientGroup.mk' ((StatedScalars (Fin n) L).subgroupOf (StatedSU n q L)))
    (QuotientGroup.mk'_surjective _) hSU

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

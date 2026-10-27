module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yCommon
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yBasic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62ySylow
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem sr628_exists_invariant {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
    {T : Subgroup G} (hf : Prop627Failure G p P M x z T) (hcov : SmallRankCover p M x) :
    ∃ f : ℕ, f.Prime ∧ f ≠ 2 ∧ f ≠ p ∧ ∃ F₁ : Subgroup G, IsPGroup f F₁ ∧
      smallRankS x T ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (F₁ : Set G) ∧ ¬ F₁ ≤ M := by
  have hp : p.Prime := hf.prime
  have hp2 : p ≠ 2 := hf.ne_two
  have : Fact p.Prime := ⟨hp⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set D : Subgroup G := smallRankD p x with hD
  set O : Subgroup G := rankThreePrimeCore 2 D with hO
  have hDspec : D ≤ C ∧ C ≤ normalizer (D : Set G) ∧ Nat.Coprime p (Nat.card D) :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p C
  have hOspec : O ≤ D ∧ D ≤ normalizer (O : Set G) ∧ Nat.Coprime 2 (Nat.card O) :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 2 D
  have hCO : C ≤ normalizer (O : Set G) := sr628_centralizer_le_normalizer_oddCore p x
  have hOM : ¬ O ≤ M := fun hOM =>
    hf.point.not_centralizer_le (hcov.trans (sup_le inf_le_left hOM))
  have hSC : smallRankS x T ≤ C := inf_le_right
  have hBC : zpowers x ⊔ zpowers z ≤ C := by
    have hxz : x * z = z * x := mem_centralizer_iff.mp hf.central.centralizes x hf.point.mem
    exact sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxz.symm))
  have hAO : smallRankS x T ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (O : Set G) :=
    (sup_le hSC hBC).trans hCO
  have hBp : IsPGroup p ↥(zpowers x ⊔ zpowers z) := P.isPGroup'.to_le hf.B_le_P
  obtain ⟨hcardA, hAsolv⟩ :=
    sr628_card_sup_and_solvable hp hp2 hf.S_isPGroup hBp hf.B_le_normalizer_S
  have hcop : Nat.Coprime (Nat.card ↥(smallRankS x T ⊔ (zpowers x ⊔ zpowers z)))
      (Nat.card O) := by
    rw [hcardA]
    obtain ⟨a, ha⟩ := hf.S_isPGroup.exists_card_eq
    obtain ⟨b, hb⟩ := hBp.exists_card_eq
    rw [ha, hb]
    refine Nat.Coprime.mul_left (Nat.Coprime.pow_left a hOspec.2.2)
      (Nat.Coprime.pow_left b (Nat.Coprime.coprime_dvd_right
        (Subgroup.card_dvd_of_le hOspec.1) hDspec.2.2))
  have hOsolv : Group.IsSolvable ↥O :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.1 hOspec.2.2)
  obtain ⟨f, hfp, F₁, hF₁O, hF₁p, hAF₁, hF₁M⟩ :=
    sr628_exists_invariant_pGroup_not_le hAO hcop hOM
  have : Fact f.Prime := ⟨hfp⟩
  have hF₁ne : F₁ ≠ ⊥ := fun h => hF₁M (h ▸ bot_le)
  have hfdvd : f ∣ Nat.card F₁ :=
    hF₁p.card_eq_or_dvd.resolve_left fun h1 => hF₁ne (Subgroup.eq_bot_of_card_eq _ h1)
  have hfO : f ∣ Nat.card O := hfdvd.trans (Subgroup.card_dvd_of_le hF₁O)
  have hf2 : f ≠ 2 := fun h =>
    absurd (Nat.Coprime.eq_one_of_dvd hOspec.2.2 (h ▸ hfO)) (by norm_num)
  have hfD : f ∣ Nat.card D := hfO.trans (Subgroup.card_dvd_of_le hOspec.1)
  have hfp' : f ≠ p := fun h =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hDspec.2.2 (h ▸ hfD))
  exact ⟨f, hfp, hf2, hfp', F₁, hF₁p, hAF₁, hF₁M⟩

end CFSG.LocalAnalysis.RankThreeTheoremC

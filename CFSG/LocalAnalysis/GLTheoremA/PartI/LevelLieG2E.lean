module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLie
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieG2ELev
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieG2EInn
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieG2EOut
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieG2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.GLTheoremA.LevelLieG2E
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders
open CFSG.QuasithinUnique.Id2519 (isSimpleGroup_adjointGroup_g2)

private theorem lieRowG2E_nonab {S : Type} [Group S] [IsSimpleGroup S]
    (hc : ¬ (Nat.card S).Prime) : ∃ a b : S, a * b ≠ b * a := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  letI : CommGroup S := { ‹Group S› with mul_comm := fun a b => h a b }
  exact hc ((CommGroup.is_simple_iff_prime_card (α := S)).1 ‹IsSimpleGroup S›)


theorem downLe_adjointG2_eight {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 8) :
    DownLe 3 2 ↥(adjointGroup .G2 K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩
  have hqcard : q.card = 8 := by
    rw [TauCeti.PrimePower.card_def]
    norm_num [q]
  have hv : (TauCeti.LieTypeIndex.G2 q).Valid :=
    (TauCeti.LieTypeIndex.valid_iff _).2
      ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).2 (show 3 ≤ q.card by omega),
        by simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]⟩
  have hZ : Subgroup.center ↥(adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨eQ⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv K (by rw [hK, hqcard])
  let e : ↥(adjointGroup .G2 K) ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eQ
  haveI : Finite ↥(adjointGroup .G2 K) := inferInstance
  haveI : IsSimpleGroup ↥(adjointGroup .G2 K) := isSimpleGroup_adjointGroup_g2 (by rw [hK]; norm_num)
  have hcard : Nat.card ↥(adjointGroup .G2 K) = 2 ^ 18 * (3 ^ 5 * 7 ^ 2 * 19 * 73) := by
    rw [card_adjointGroup_G2, hK]
    norm_num [CFSG.Open.ordG2]
  have hnc : ∃ a b : ↥(adjointGroup .G2 K), a * b ≠ b * a :=
    lieRowG2E_nonab (by rw [hcard]; norm_num)
  have hp2 : q.p = 2 := primePower_p_eq (r := 2) (e := 3) Nat.prime_two (by norm_num)
    (by rw [hqcard]; norm_num)
  refine downLe_of_chev2 hnc ⟨.G2 q, hv⟩ e (by simpa using hp2) ?_ ?_ ?_
  · rw [hcard]
    unfold Nbig
    norm_num
  · exact kLevel_le_two_of_k2 ⟨TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩, ⟨rfl, hqcard⟩, ⟨e⟩⟩
  · rintro β hβ h1 ⟨-, h73⟩
    by_cases hin : ∃ g : ↥(adjointGroup .G2 K), β = MulAut.conj g
    · obtain ⟨g, rfl⟩ := hin
      have hg1 : g ≠ 1 := fun h => h1 (by rw [h]; exact map_one _)
      have hg3 : g ^ 3 = 1 := by
        have h3 : g ^ 3 ∈ Subgroup.center ↥(adjointGroup .G2 K) := by
          rw [Subgroup.mem_center_iff]
          intro x
          have h1 := congrArg (fun φ : MulAut ↥(adjointGroup .G2 K) => φ x)
            (show MulAut.conj (g ^ 3) = 1 by rw [map_pow]; exact hβ)
          simp only [MulAut.conj_apply, MulAut.one_apply] at h1
          exact (mul_inv_eq_iff_eq_mul.1 h1).symm
        rwa [hZ, Subgroup.mem_bot] at h3
      have hord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
      have hfix : fixSubgroup (MulAut.conj g) = Subgroup.centralizer ({g} : Set ↥(adjointGroup .G2 K)) := by
        ext x
        rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
        constructor
        · intro hx
          exact (mul_inv_eq_iff_eq_mul.1 hx).symm
        · intro hx
          exact mul_inv_eq_iff_eq_mul.2 hx.symm
      rw [hfix] at h73
      exact g2e_inner_not73 K hK g hord h73
    · push Not at hin
      have hc := g2e_outer_card hK hβ hin
      rw [hc] at h73
      omega


theorem kdLieRowG2Eight_holds : KDLieRowG2Eight := by
  intro q hv hq
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 3) = q.card := by
    rw [GaloisField.card 2 3 (by norm_num), hq]
    norm_num
  have hZ : Subgroup.center ↥(adjointGroup .G2 (GaloisField 2 3)) = ⊥ :=
    center_adjointGroup_eq_bot
  obtain ⟨eQ⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv (GaloisField 2 3) hK
  let e : ↥(adjointGroup .G2 (GaloisField 2 3)) ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eQ
  exact downLe_of_mulEquiv e
    (downLe_adjointG2_eight (K := GaloisField 2 3) (by rw [GaloisField.card 2 3 (by norm_num)]; norm_num))

end CFSG.LocalAnalysis.GLTheoremA

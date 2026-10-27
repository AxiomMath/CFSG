module

public import CFSG.HardMathSupport.Dickson.Bal207.ExcVac
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTGeneric
import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
import CFSG.RankThree.PartOne.KE.SuzukiFinal
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.FieldAut

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)
open CFSG.HardMathSupport.Dickson.SuzukiReeB (exists_eq_conj_of_mem_range)

theorem excSz_index {d : TauCeti.ValidLieTypeIndex} (hd : IsExcSz32 d.1) :
    ∃ hv : (TauCeti.LieTypeIndex.suzuki 2).Valid, d = ⟨.suzuki 2, hv⟩ := by
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | suzuki m =>
    simp only [IsExcSz32] at hd
    subst hd
    exact ⟨hv, rfl⟩
  | _ => exact absurd hd (by simp [IsExcSz32])

theorem excSz_isSolvable_fixSubgroup_suzuki {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * 2 + 1)) {β : MulAut (suzukiGroup 2 K)}
    (hβ : β ^ 5 = 1) (hβ1 : β ≠ 1) : Group.IsSolvable ↥(fixSubgroup β) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfin : Finite (suzukiGroup 2 K) := (suzuki_simple (by norm_num) hK).1
  have hord : orderOf β = 5 := orderOf_eq_prime hβ hβ1
  by_cases hin : β ∈ inner (suzukiGroup 2 K)
  · obtain ⟨x, rfl, hxp, hx1⟩ := exists_eq_conj_of_mem_range
      (CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot (by norm_num) hK) hin hβ hβ1
    have hodd : Odd (orderOf x) := by
      rw [orderOf_eq_prime hxp hx1]
      exact ⟨2, rfl⟩
    obtain ⟨hcard, -⟩ :=
      (CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers (by norm_num)
        hK).2 x hx1 hodd
    have hsolv : Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (suzukiGroup 2 K))) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ hcard
    rw [CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj]
    exact hsolv
  · obtain ⟨σ, h, b, k, _, _, -, hbp, hk, hconj, ⟨efix⟩⟩ :=
      CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent 2 (by norm_num) K hK 5
        (by norm_num) (by norm_num) β hord hin
    have hb0 : b = 0 := by omega
    subst hb0
    have hk2 : Nat.card k = 2 := by rw [hk]; norm_num
    have hcard := (suzuki_two_normal_five_complement_core_trivial hk2).1
    have hsolv : Group.IsSolvable (suzukiGroup 0 k) :=
      CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [hcard]; norm_num)
    have hφ : MulAut.congr (MulAut.conj h : suzukiGroup 2 K ≃* suzukiGroup 2 K) β =
        szFieldAut 2 K σ := by
      have : MulAut.congr (MulAut.conj h : suzukiGroup 2 K ≃* suzukiGroup 2 K) β =
          MulAut.conj h * β * (MulAut.conj h)⁻¹ := rfl
      rw [this, hconj]
    refine LieComp.SRT.isSolvable_fixSubgroup_of_congr
      (MulAut.conj h : suzukiGroup 2 K ≃* suzukiGroup 2 K) β ?_
    rw [hφ]
    exact Group.isSolvable_of_isSolvable_injective (f := efix.toMonoidHom) efix.injective

theorem excSz_isSolvable_fixSubgroup {S : Type} [Group S]
    {hv : (TauCeti.LieTypeIndex.suzuki 2).Valid}
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group) {β : MulAut S} (hβ : β ^ 5 = 1)
    (hβ1 : β ≠ 1) : Group.IsSolvable ↥(fixSubgroup β) := by
  obtain ⟨-, a, -, K, _, _, hf, hK', ⟨θ⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index 2 hv
  have ha2 : a = 2 := by omega
  subst ha2
  have hβ' : MulAut.congr (e.trans θ) β ^ 5 = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr (e.trans θ) β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr (e.trans θ)).injective (h.trans (map_one _).symm))
  exact LieComp.SRT.isSolvable_fixSubgroup_of_congr (e.trans θ) β
    (excSz_isSolvable_fixSubgroup_suzuki hK' hβ' hβ1')

theorem excSz_clauses
    {G : ∀ (S : Type) [Group S], MulAut S → Prop} {X : Type} [Group X] [Finite X]
    {K B A : Subgroup X} (ctx : Bal207PlusCtx G 5 K B A) (hq : IsLieQuot ↥K IsExcSz32) :
    Bal207PlusFamClauses 5 K B A := by
  obtain ⟨d, hd, ⟨f⟩⟩ := hq
  obtain ⟨hv, rfl⟩ := excSz_index hd
  exact bal207PlusFamClauses_of_fix_solvable ctx fun β hβ hβ1 =>
    excSz_isSolvable_fixSubgroup f hβ hβ1

theorem bal207PlusFamSz32
    (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Bal207PlusFamSz32 G := by
  intro X _ _ _ p K B A ctx hq _
  obtain ⟨d, ⟨hp5, hd⟩, e⟩ := hq
  subst hp5
  exact excSz_clauses ctx ⟨d, hd, e⟩

end CFSG.HardMathSupport.Dickson.Bal207

end

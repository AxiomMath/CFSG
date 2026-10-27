module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Model
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3Ru
public import Certificates.Data.B3Spor3Checks

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.RuSchreier CFSG.EvenSporadicStandard.RuStd.S2
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3

theorem centralizer_singleton_eq_of_zpowers_eq {G : Type*} [Group G] {a b : G}
    (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  have key : ∀ {a b : G}, Subgroup.zpowers a = Subgroup.zpowers b → ∀ z : G, Commute z b →
      Commute z a := by
    intro a b h z hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
      (h ▸ Subgroup.mem_zpowers a : a ∈ Subgroup.zpowers b)
    rw [← hk]
    exact hz.zpow_right k
  ext z
  simp only [Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun hz => key h.symm z (show Commute z a from hz),
    fun hz => key h z (show Commute z b from hz)⟩


theorem b3Phi_ru : ∀ x : ↥ruP, orderOf x = 3 →
    B3Phi 3 (Subgroup.centralizer ({x} : Set ↥ruP)) := by
  intro r hr
  obtain ⟨c, hc⟩ := exists_conj_ruThree r hr
  rw [← centralizer_singleton_eq_of_zpowers_eq hc, ← MulAut.conj_apply,
    ← map_centralizer_mulEquiv (MulAut.conj c) ruThreeX0]
  exact (b3Phi_map_iff Nat.prime_three (MulAut.conj c).toMonoidHom
    (MulAut.conj c).injective).2 (b3Phi_of_oPrime ruThree_oPrime.2)

theorem b3SporPair_Ru_three
    (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) :
    B3SporPair .Ru 3 :=
  let e : CFSG.Blueprint.NativeSporadic.Ru ≃* ↥ruP := ruEquivP
  b3SporPair_of_model hOut ↥ruP ⟨e.symm.trans (hbr .Ru).some⟩ b3Phi_ru

end CFSG.HardMathSupport.Solomon.Coordinator

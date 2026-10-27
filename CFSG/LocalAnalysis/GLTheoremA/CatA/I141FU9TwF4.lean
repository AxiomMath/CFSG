module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9Small
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9Lab
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgE6Res2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup lieOrderBridge_holds)

open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

open CFSG.LocalAnalysis.GLTheoremA.I2018 (catalogIs_congr' fixSubgroup_one_eq_top)


section Certs


theorem i141U9Fam_twF4Eight (hG2 : U9Gf8Absurd) : I141U9Fam u9FamTwF4Eight := by
  intro Γ _ _ K J x a hQ hx ha hxa hxna hI1 hI2 hJ hJU hZ hF
  obtain ⟨hs, hna⟩ := u9_simple_nonabelian hI1
  obtain ⟨hα3, hJ', ⟨eJ⟩⟩ := u9_transfer_chev hx hI1 hJ
  have hU' : catalogIs (PSimple 3 (chevTransfer 3 K J)) S9.isU3eight := catalogIs_congr' eJ hJU
  obtain ⟨i, hi, ⟨e⟩⟩ := hQ
  cases i with
  | lie d' =>
    obtain ⟨d, hv⟩ := d'
    cases d with
    | reeF4 m =>
      have hm : m = 1 := by
        rcases m with _ | _ | m
        · exact absurd hi (by simp [u9FamTwF4Eight, onLie])
        · rfl
        · exact absurd hi (by simp [u9FamTwF4Eight, onLie])
      subst hm
      have hm1 : 1 ≤ (1 : ℕ) := le_rfl
      by_cases hα1 : chevAut 3 K ⟨x, hI1.1 (Subgroup.mem_zpowers x)⟩ = 1
      · exfalso
        haveI := hs
        have hI : GLAPComponent 3 (⊤ : Subgroup (PSimple 3 K)) (chevTransfer 3 K J) := by
          rw [hα1, fixSubgroup_one_eq_top] at hJ'
          exact hJ'
        obtain ⟨eT⟩ := chevQ_pSimple_top_equiv Nat.prime_three hna hI
        have hcard : Nat.card (PSimple 3 K) = 5515776 := by
          rw [← Nat.card_congr eT.toEquiv]
          exact CatSingle.card_isU3eight lieOrderBridge_holds hU'
        rw [lieOrderBridge_holds ⟨.reeF4 1, hv⟩ _ ⟨e⟩] at hcard
        have := u9_twF4_gt 1 le_rfl
        exact absurd hcard (by
          show orderTwistedF4 (2 ^ (2 * 1 + 1)) ≠ 5515776
          omega)
      · have hfs : KD264Lie.fieldSize (TauCeti.LieTypeIndex.reeF4 1) = 8 := by
          simp [KD264Lie.fieldSize]
        exact (hG2 Γ K J x a hx ha hxa hI1 hI2 hJ hJU hF ⟨.reeF4 1, hv⟩ ⟨e⟩
          (TauCeti.LieTypeIndex.characteristic_reeF4 1) hfs
          (KD264Lie.lieCompAlg_excTwisted_kd264e6 ⟨.reeF4 1, hv⟩ (by simp [KD264Lie.isExcTwistedIdx]) hfs)
          hα1).elim
    | _ => exact hi.elim
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I141F

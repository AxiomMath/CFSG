module

public import CFSG.Quasithin.H13.A5S136m
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136l

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem Lv_le_normalizer_of_mem_cComp_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G))) :
    S.Lv ≤ Subgroup.normalizer (K : Set G) := by
  have : IsSimpleGroup G := S.h13.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hO2 := (S.lemma115Hyp_Gv_F4 h1222 h517).pCore_ne_bot
  have hKG : K ≤ Gv := le_of_mem_cComp hK
  have hLvGv : S.Lv ≤ Gv := by
    rw [Lv, oTwoRes_eq_oTwoUpper]
    exact (oTwoUpper_le _).trans inf_le_right
  rcases Vol2Native.lemma_1_2_1_three hloc h37 h38 hO2 hK with hn | ⟨h2, -⟩
  · exact hLvGv.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mp hn)
  · rw [ncard_conjSubgroupsBy_eq_index] at h2
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, m, hm, hxm⟩
    have hxG : x ∈ Gv := hx.2
    have h1 : (⟨x, hxG⟩ : ↥Gv) ∈ (Subgroup.normalizer (K : Set G)).subgroupOf Gv :=
      mem_of_index_two_of_odd h2 hm (Subtype.ext (by simpa using hxm))
    exact Subgroup.mem_subgroupOf.mp h1

end Setting

theorem elim1366CD_of_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hout : FactOutAlt67) :
    Elim1366CD_F4 := by
  intro G _ _ T L V S hab K hK hcase
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hKG : K ≤ Gv := hK.1
  have hKc : K ∈ cComp Gv := by
    have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le hKG] at h2
  have hLvN := S.Lv_le_normalizer_of_mem_cComp_F4 h1222 h517 h37 h38 hKc
  have hqs : CFSG.IsQuasisimple ↥K :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hKG)).1 hK.2.1

  have hinner : (Nat.card (Subgroup.center ↥K) = 1 ∨ Nat.card (Subgroup.center ↥K) = 3) →
      (Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 6)) ∨
        Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 7))) →
      InducesInner S.z K := by
    intro hZ hshape
    have hLv : ∀ x ∈ S.Lv, InducesInner x K := by
      intro x hx
      have hx' : x ∈ Subgroup.closure
          {y | y ∈ L ⊓ Gv ∧ ∃ m : ℕ, Odd m ∧ y ^ m = 1} := hx
      clear hx
      induction hx' using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨hy1, m, hm, hym⟩ := hy
        exact hout G K hqs hZ hshape y (hLvN (Subgroup.subset_closure ⟨hy1, m, hm, hym⟩))
          (Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hym))
      | one => exact ⟨1, K.one_mem, fun x _ => by group⟩
      | mul a b ha hb iha ihb => exact InducesInner.mul iha ihb
      | inv a ha iha => exact InducesInner.inv iha (hLvN ha)
    obtain ⟨l, hl, hwl⟩ := hLv _ S.z_mul_inv_v12_mem_Lv
    refine ⟨l, hl, fun x hx => ?_⟩
    have hxv : x * S.v12 = S.v12 * x := Subgroup.mem_centralizer_singleton_iff.mp (hKG hx)
    have h1 := hwl x hx
    have h2 : (S.z * S.v12⁻¹)⁻¹ * x * (S.z * S.v12⁻¹) ∈ K := by
      rw [h1]
      exact K.mul_mem (K.mul_mem (K.inv_mem hl) hx) hl
    have hv2 : (S.z * S.v12⁻¹)⁻¹ * x * (S.z * S.v12⁻¹) * S.v12 =
        S.v12 * ((S.z * S.v12⁻¹)⁻¹ * x * (S.z * S.v12⁻¹)) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hKG h2)
    rw [← h1]
    calc S.z⁻¹ * x * S.z = S.v12⁻¹ * ((S.z * S.v12⁻¹)⁻¹ * x * (S.z * S.v12⁻¹)) * S.v12 := by
          group
      _ = S.v12⁻¹ * (S.v12 * ((S.z * S.v12⁻¹)⁻¹ * x * (S.z * S.v12⁻¹))) := by
          rw [mul_assoc, hv2]
      _ = (S.z * S.v12⁻¹)⁻¹ * x * (S.z * S.v12⁻¹) := by group
  rcases hcase with ⟨φ, σ, hZ, hswap, hact⟩ | ⟨φ, σ, hZ, hcyc, hact⟩
  · refine false_of_inner_of_permAction6 φ ?_ (hinner hZ (Or.inl ⟨φ⟩)) hact
    rw [hswap.sign_eq]
    decide
  · refine false_of_inner_of_permAction7 φ ?_ (hinner hZ (Or.inr ⟨φ⟩)) hact
    rw [Equiv.Perm.sign_of_cycleType, hcyc]
    decide

end CFSG.Quasithin.H13.A5

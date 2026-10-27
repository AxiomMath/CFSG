module

public import CFSG.Quasithin.H13.A6S13812
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C2Six
open scoped commutatorElement

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem lem13812_one_F4 (h139 : Stmt13_3_9_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H) :
    ¬ K ≤ Subgroup.normalizer (L : Set G) ∧ (K ⊔ T) ⊔ S.L1 ∈ S.Hz := by
  set M := Subgroup.normalizer (L : Set G) with hM
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hHG : H ≤ S.G1 := hH.2.1
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTM : T ≤ M := S.T_le_NL
  have hV1T : fsuV1 T V ≤ T := ((S.V1_le_V2.trans S.V2_le_V3).trans S.V3_le_V).trans S.V_le_T
  have hKM : ¬ K ≤ M := by
    intro hKM
    set Y := conjClosure K T with hY
    have hYH : H ≤ Subgroup.normalizer (Y : Set G) :=
      normal_conjClosure_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian h37 h38
        hH.1.2 (isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH) hK
    have hYle : Y ≤ H := conjClosure_le fun t ht k hk =>
      H.mul_mem (H.mul_mem (hTH ht) (hKH hk)) (H.inv_mem (hTH ht))
    have hYM : Y ≤ M := conjClosure_le fun t ht k hk =>
      M.mul_mem (M.mul_mem (hTM ht) (hKM hk)) (M.inv_mem (hTM ht))
    have hYperf : ⁅Y, Y⁆ = Y := A6O2F.perfect_conjClosure (perfect_of_mem_cComp hK)
    have hYres : oTwoRes Y = Y := by
      rw [oTwoRes_eq_oTwoUpper]
      exact (eq_oTwoUpper_of_perfect hYperf).symm
    have hz : S.z ∈ fsuV1 T V := S.mem_V1_iff.2 (Or.inr rfl)
    have hzL : S.z ∉ Subgroup.centralizer (L : Set G) := by
      intro h
      have h1 : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨S.z_mem_V, h⟩
      rw [S.zv, Subgroup.mem_bot] at h1
      exact S.z_ne_one h1
    have hInH : InH T H := ⟨hTH, hH.1.2⟩
    have hKne : K ≠ ⊥ := ne_bot_of_mem_cComp hK
    have hKY : K ≤ Y := le_conjClosure K T
    rcases h139 G T L V H Y S.z S.h13 S.irr S.a6 hInH hH.2.2 hYres hYle hYH hz hzL
      (le_inf hYM (hYle.trans hHG)) with hY0 | ⟨-, hA6, hhat⟩
    · exact hKne (le_bot_iff.mp (hY0 ▸ hKY))

    have hYL1 : Y ≤ S.L1 := by
      by_cases hh : IsHatA6 L
      · rw [hhat hh]
        refine (oTwoRes_le _).trans (Subgroup.commutator_le.mpr fun a ha b hb => ?_)
        rw [commutatorElement_def]
        have h1 := (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L1 hb.1) _).mp
          (S.L1.inv_mem ha)
        have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
        rw [e]
        exact S.L1.mul_mem ha h1
      · rw [hA6 (S.nonempty_alt6_of_not_hat hh)]
        exact le_rfl

    have hYN : Y ≤ Subgroup.normalizer (V : Set G) := hYL1.trans (S.L1_le_L.trans S.frame.L_le)
    have hYC := A6O2F.perfect_le_ker_of_A4 hYperf hYN S.frame.ρ fun y hy =>
      S.rho_L1 (g := ⟨y, hYN hy⟩) (hYL1 hy)
    have hYZ : Y ≤ o2Z L := fun y hy =>
      S.centralizer_le_o2Z ⟨S.L1_le_L (hYL1 hy), (S.rho_eq_one_iff _).1 (hYC y hy)⟩
    have hYO : Y ≤ pCoreOf 2 L := by
      rw [← hYperf, Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨-, hab⟩ := mem_o2Z_iff.1 (hYZ ha)
      rw [commutatorElement_def]
      exact hab b (S.L1_le_L (hYL1 hb))
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsolv : Group.IsSolvable ↥(pCoreOf 2 L) := by
      have := (pCoreOf_isPGroup 2 L).isNilpotent
      infer_instance
    exact hKne (le_bot_iff.mp ((A6O2F.eq_bot_of_perfect_le hsolv hYperf hYO) ▸ hKY))
  have hXG : (K ⊔ T) ⊔ S.L1 ≤ S.G1 :=
    sup_le (sup_le (hKH.trans hHG) (hTH.trans hHG)) (le_sup_left.trans (hH.1.1.trans hHG))
  refine ⟨hKM, ⟨sup_le le_sup_right (le_sup_right.trans le_sup_left),
    S.pCoreOf_ne_bot_of_le_G1 (hV1T.trans (le_sup_right.trans le_sup_left)) hXG⟩, hXG,
    fun h => hKM ((le_sup_left.trans le_sup_left).trans h)⟩

end Setting4

end CFSG.Quasithin.H13.A6

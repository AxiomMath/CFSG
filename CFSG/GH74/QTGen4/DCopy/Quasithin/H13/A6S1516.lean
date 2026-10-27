module

public import CFSG.Quasithin.H13.A6S1516
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1515b

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section Data

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hhat : ¬ IsHatA6 L)
  (hn : H ≤ Subgroup.normalizer (S.L1 : Set G)) (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hhat hn hna

omit hhat in

theorem inf_conjugate_UH_F4
    (hTV : T ⊓ Subgroup.centralizer (V : Set G) = V)
    (y : ↥(Subgroup.normalizer (V : Set G))) (hy : S.frame.ρ y = yK) :
    conjClosure S.V3 H ⊓ CFSG.conjugate (conjClosure S.V3 H) (y : G) = S.V2 := by
  set A := S.toA5Sit_F4 hNS h13315 h1356two hH hna
  have hUL1 := S.UH_le_L1_six_F4 hNS h13315 h1356two hH hn hna
  obtain ⟨hK4, -⟩ := S.lemma13_5_14_two_F4 hNS h1356two h13315 hH hUL1 hna
  have hUN : ∀ u ∈ conjClosure S.V3 H, u ∈ Subgroup.normalizer (V : Set G) := fun u hu =>
    S.frame.L_le (S.L1_le.trans inf_le_left (hUL1 hu))

  have hV3 : ∀ x (hx : x ∈ conjClosure S.V3 H),
      S.frame.ρ ⟨x, hUN x hx⟩ = 1 → x ∈ S.V3 := by
    intro x hx h1
    have hxV : x ∈ V := by
      rw [← hTV]
      exact ⟨S.UH_le_T_F4 hNS h1356two h13315 hH hx, (S.rho_eq_one_iff _).1 h1⟩
    rw [← A.inf_Q_eq]
    exact ⟨hxV, A.U_le_Q hx⟩
  apply le_antisymm
  · rintro x ⟨hxU, u, huU, hux⟩
    have hux' : x = (y : G)⁻¹ * u * (y : G) := by
      rw [← hux]
      simp
    have hu' : u = (y : G) * x * (y : G)⁻¹ := by
      rw [hux']
      group

    have e : (⟨u, hUN u huU⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        y * ⟨x, hUN x hxU⟩ * y⁻¹ := Subtype.ext hu'
    have hρu := hK4 u huU
    rw [e, map_mul, map_mul, map_inv, hy] at hρu
    have hρx : S.frame.ρ ⟨x, hUN x hxU⟩ = 1 := yK_K4L _ (hK4 x hxU) hρu
    have hρu1 : S.frame.ρ ⟨u, hUN u huU⟩ = 1 := by
      rw [e, map_mul, map_mul, map_inv, hρx, mul_one, mul_inv_cancel]
    obtain ⟨hxV, hx3⟩ := S.mem_pre.1 (hV3 x hxU hρx)
    obtain ⟨huV, hu3⟩ := S.mem_pre.1 (hV3 u huU hρu1)
    have hyx : (y : G) * x * (y : G)⁻¹ ∈ V := hu' ▸ huV
    have hψ := S.psi_conj_coe y hxV hyx
    rw [hy] at hψ
    have hu3' : InW3 (act4f yK (S.frame.ψ ⟨x, hxV⟩)) := by
      rw [← hψ]
      have : (⟨(y : G) * x * (y : G)⁻¹, hyx⟩ : ↥V) = ⟨u, huV⟩ := Subtype.ext hu'.symm
      rw [this]
      exact hu3
    exact S.mem_pre.2 ⟨hxV, yK_W3 _ (S.frame.ψ ⟨x, hxV⟩).2 hx3 hu3'⟩
  · intro v hv
    have hv3 : v ∈ S.V3 := S.V2_le_V3 hv
    refine ⟨le_conjClosure _ _ hv3, ?_⟩
    obtain ⟨hvV, hv2⟩ := S.mem_pre.1 hv
    have hyv : (y : G) * v * (y : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp y.2 v).mp hvV
    have hψ := S.psi_conj_coe y hvV hyv
    rw [hy] at hψ
    have hyv3 : (y : G) * v * (y : G)⁻¹ ∈ S.V3 := S.mem_pre.2 ⟨hyv, by
      show InW3 _
      rw [hψ]
      exact yK_W2 _ hv2⟩
    refine ⟨_, le_conjClosure _ _ hyv3, ?_⟩
    simp [mul_assoc]

theorem psu43_of_le_F4
    (hU43 : StmtU43Type) (hobl : Obl13_5_14Six_F4) (hctk : Input13515CTK_F4)
    (hTL : T ≤ L) : LieModel G .PSU 4 3 1 := by
  obtain ⟨l, hlL, hl⟩ := S.exists_lK
  have hHG := S.H_eq_G1_six_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL
  have hQU := S.pCoreOf_H_eq_six_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL
  obtain ⟨P⟩ := S.nonempty_pf15_six_F4 hNS h13315 h1356two hH hn hna hhat hlL hl hobl
  set A := S.toA5Sit_F4 hNS h13315 h1356two hH hna
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hTV : T ⊓ Subgroup.centralizer (V : Set G) = V :=
    S.cT.trans (S.pCoreOf_LT_six_F4 hNS h13315 h1356two hH hn hna hhat hlL hl hobl hctk)
  have hG : Subgroup.centralizer ({S.z} : Set G) = H := hHG.symm
  refine hU43 G S.z S.orderOf_z ?_ ?_ ?_ ?_ ?_ <;> rw [hG, hQU]
  · exact nonempty_mulEquiv_q8Q8 P.hUQ8
  · apply le_antisymm
    · rintro x ⟨hx, hxc⟩
      have : x ∈ fsuV1 T V := P.mem_V1_of_central hx fun u hu =>
        (Subgroup.mem_centralizer_iff.mp hxc u hu).symm
      rwa [S.V1_eq] at this
    · intro x hx
      rw [← S.V1_eq] at hx
      refine ⟨le_conjClosure _ _ ((S.V1_le_V2.trans S.V2_le_V3) hx),
        Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
      rcases S.mem_V1_iff.1 hx with rfl | rfl
      · simp
      · exact Subgroup.mem_centralizer_singleton_iff.mp
          (hH.2.1 (A.U_le_Q.trans (pCoreOf_le 2 H) hu))
  · have h := hF.charTwo_H
    unfold CharTwo at h
    rwa [hQU] at h
  · rw [P.card_H, S.card_range_six_F4 hNS h13315 h1356two hH hhat hna P, hQU, mul_comm]
  · obtain ⟨y, hyL, hy⟩ := (S.frame.image_L yK).2 (Perm.mem_alternatingGroup.2 yK_facts.1)
    have hzy : (y : G)⁻¹ * S.z * (y : G) ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ y.2) S.z).mp S.z_mem_V
      simpa using this
    have hψ := S.psi_conj_inv_coe y S.z_mem_V hzy
    rw [hy, S.psi_z] at hψ
    refine ⟨y, le_conjClosure _ _ (S.mem_pre.2 ⟨hzy, ?_⟩), fun h => ?_, ?_⟩
    · show InW3 _
      rw [hψ]
      exact yK_facts.2.1
    · apply yK_facts.2.2
      have e : (⟨(y : G)⁻¹ * S.z * (y : G), hzy⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ := Subtype.ext h
      rw [← hψ, e, S.psi_z]
    · rw [S.inf_conjugate_UH_F4 hNS h13315 h1356two hH hn hna hTV y hy, S.card_V2]

end Data

end Setting4

end CFSG.Quasithin.H13.A6

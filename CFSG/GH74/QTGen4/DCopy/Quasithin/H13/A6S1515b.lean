module

public import CFSG.Quasithin.H13.A6S1515b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1515

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section Data

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hhat : ¬ IsHatA6 L)
include hNS h13315 h1356two hH hhat

theorem rho_Q_F4
    {q : G} (hq : q ∈ pCoreOf 2 H) (hqN : q ∈ Subgroup.normalizer (V : Set G)) :
    S.frame.ρ ⟨q, hqN⟩ ∈ K4L ∨ S.frame.ρ ⟨q, hqN⟩ * swap 4 5 ∈ K4L := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hF.sylow_H
  have hcH : (S.cL1 hhat : G) ∈ H := hH.1.1 ((le_sup_left : S.L1 ≤ S.L1 ⊔ T) (S.cL1_mem hhat))
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hD : ∀ x (hx : x ∈ Subgroup.normalizer (V : Set G)), x ∈ pCoreOf 2 H →
      InD6 (S.frame.ρ ⟨x, hx⟩) := fun x hx hxQ => S.frame.T_D ⟨x, hx⟩ (hQT hxQ)
  have hcN := (S.cL1 hhat).2
  refine dNormAt_all _ (hD q hqN hq) ?_ ?_
  · have h1 : (S.cL1 hhat : G) * q * (S.cL1 hhat : G)⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (hQn hcH) q).mp hq
    have hmem : (S.cL1 hhat : G) * q * (S.cL1 hhat : G)⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hcN hqN) (Subgroup.inv_mem _ hcN)
    have e : (⟨(S.cL1 hhat : G) * q * (S.cL1 hhat : G)⁻¹, hmem⟩ :
        ↥(Subgroup.normalizer (V : Set G))) = S.cL1 hhat * ⟨q, hqN⟩ * (S.cL1 hhat)⁻¹ := rfl
    have := hD _ hmem h1
    rwa [e, map_mul, map_mul, map_inv, S.cL1_rho hhat] at this
  · have h1 : (S.cL1 hhat : G)⁻¹ * q * (S.cL1 hhat : G)⁻¹⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (hQn (H.inv_mem hcH)) q).mp hq
    rw [inv_inv] at h1
    have hmem : (S.cL1 hhat : G)⁻¹ * q * (S.cL1 hhat : G) ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hcN) hqN) hcN
    have e : (⟨(S.cL1 hhat : G)⁻¹ * q * (S.cL1 hhat : G), hmem⟩ :
        ↥(Subgroup.normalizer (V : Set G))) = (S.cL1 hhat)⁻¹ * ⟨q, hqN⟩ * S.cL1 hhat := rfl
    have := hD _ hmem h1
    rwa [e, map_mul, map_mul, map_inv, S.cL1_rho hhat] at this

theorem card_range_six_F4
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H))
    {SY : A5SitY (S.toA5Sit_F4 hNS h13315 h1356two hH hna) S.L1}
    (P : A5SitPf15 (S.toA5Sit_F4 hNS h13315 h1356two hH hna) SY) : Nat.card P.Φ.range = 36 := by
  obtain ⟨hD, hA, hK1, hK2⟩ := s0145_facts
  obtain ⟨t, htT, hρt⟩ := S.frame.DA_T _ hD (Perm.mem_alternatingGroup.2 hA)
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hvT : P.v ∈ T := S.V_le_T P.v_mem
  have hvN : P.v ∈ Subgroup.normalizer (V : Set G) := S.frame.T_le hvT
  have hρv : S.frame.ρ ⟨P.v, hvN⟩ = 1 :=
    (S.rho_eq_one_iff _).2 (S.V_le_centralizer_V P.v_mem)
  refine P.card_range_eq hF.T_le_H S.h13.sylow.1 htT hvT ?_ P.v_not ?_
  · intro htQ
    rcases S.rho_Q_F4 hNS h13315 h1356two hH hhat htQ t.2 with h | h <;>
      rw [Subtype.coe_eta, hρt] at h
    exacts [hK1 h, hK2 h]
  · intro hQ
    have hmem : (t : G) * P.v⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ t.2 (Subgroup.inv_mem _ hvN)
    have e : (⟨(t : G) * P.v⁻¹, hmem⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        t * (⟨P.v, hvN⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ := rfl
    rcases S.rho_Q_F4 hNS h13315 h1356two hH hhat hQ hmem with h | h <;>
      rw [e, map_mul, map_inv, hρv, inv_one, mul_one, hρt] at h
    exacts [hK1 h, hK2 h]

variable (hn : H ≤ Subgroup.normalizer (S.L1 : Set G))
  (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H))
  {l : ↥(Subgroup.normalizer (V : Set G))} (hlL : (l : G) ∈ L) (hl : S.frame.ρ l = lK)
include hn hna hlL hl

theorem pCoreOf_H_eq_six_F4
    (hobl : Obl13_5_14Six_F4) (hctk : Input13515CTK_F4) (hTL : T ≤ L) :
    pCoreOf 2 H = conjClosure S.V3 H := by
  set A := S.toA5Sit_F4 hNS h13315 h1356two hH hna
  refine le_antisymm (fun q hq => ?_) A.U_le_Q
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hqT : q ∈ T := pCoreOf_two_le_of_isSylowTwoOf hF.sylow_H hq
  have hqN := S.frame.T_le hqT
  have hsign : Perm.sign (S.frame.ρ ⟨q, hqN⟩) = 1 :=
    Perm.mem_alternatingGroup.1 ((S.frame.image_L _).1 ⟨⟨q, hqN⟩, hTL hqT, rfl⟩)
  have hK : S.frame.ρ ⟨q, hqN⟩ ∈ K4L := by
    rcases S.rho_Q_F4 hNS h13315 h1356two hH hhat hq hqN with h | h
    · exact h
    · exact absurd hsign (sign_ne_of_mul_swap_mem h)
  have hUL1 := S.UH_le_L1_six_F4 hNS h13315 h1356two hH hn hna
  obtain ⟨-, hsurj⟩ := S.lemma13_5_14_two_F4 hNS h1356two h13315 hH hUL1 hna
  obtain ⟨u, hu, hρu⟩ := hsurj _ hK

  have huN : u ∈ Subgroup.normalizer (V : Set G) :=
    S.frame.L_le (S.L1_le.trans inf_le_left (hUL1 hu))
  have hc : S.frame.ρ ((⟨u, huN⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ * ⟨q, hqN⟩) = 1 := by
    rw [map_mul, map_inv, hρu, inv_mul_cancel]
  have hcC := (S.rho_eq_one_iff _).1 hc
  have huT : u ∈ T := S.UH_le_T_F4 hNS h1356two h13315 hH hu
  have hcV : u⁻¹ * q ∈ V := by
    have hLT := S.pCoreOf_LT_six_F4 hNS h13315 h1356two hH hn hna hhat hlL hl hobl hctk
    rw [← hLT, ← S.cT]
    exact ⟨T.mul_mem (T.inv_mem huT) hqT, hcC⟩
  have hcQ : u⁻¹ * q ∈ pCoreOf 2 H :=
    (pCoreOf 2 H).mul_mem ((pCoreOf 2 H).inv_mem (A.U_le_Q hu)) hq
  have hc3 : u⁻¹ * q ∈ S.V3 := by
    rw [← A.inf_Q_eq]
    exact ⟨hcV, hcQ⟩
  have := (conjClosure S.V3 H).mul_mem hu (le_conjClosure _ _ hc3)
  simpa using this

omit hhat hn hlL hl in

theorem C_z_eq_F4
    {SY : A5SitY (S.toA5Sit_F4 hNS h13315 h1356two hH hna) S.L1}
    (P : A5SitPf15 (S.toA5Sit_F4 hNS h13315 h1356two hH hna) SY) : P.C.z = S.z := by
  rcases (P.Cz S.z).1 (S.mem_V1_iff.2 (Or.inr rfl)) with h | h
  · exact absurd h S.z_ne_one
  · exact h.symm

theorem H_eq_G1_six_F4
    (hobl : Obl13_5_14Six_F4) (hctk : Input13515CTK_F4) (hTL : T ≤ L) : H = S.G1 := by
  obtain ⟨P⟩ := S.nonempty_pf15_six_F4 hNS h13315 h1356two hH hn hna hhat hlL hl hobl
  have hz := S.C_z_eq_F4 hNS h13315 h1356two hH hna P
  refine P.H_eq_of (S.pCoreOf_H_eq_six_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL)
    (S.hypF91_F4 hNS h13315 h1356two (S.G1_mem_Hz hH)) hH.2.1 ?_
  rw [hz]
  exact le_rfl

end Data

end Setting4

end CFSG.Quasithin.H13.A6

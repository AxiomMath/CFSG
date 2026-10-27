module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Remark612
public import CFSG.Quasithin.Vol2.Ch6OrthNotNat

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin
open scoped IsMulCommutative commutatorElement Matrix
open CFSG.Quasithin.JonesParshall

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611

theorem omegaOne_le_of_orth_ch6_F4 (h512 : Stmt5_1_2_F4) (h513 : Stmt5_1_3_F4) (h : Hyp611 G T M L V n)
    (horth : IsOrthCh5 L V n) (hn : 2 < n) :
    omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  set R := omegaOneCenterOf Q with hRdef
  have hQ : ch6Q T V = Q := h.centralizer_eq
  have hRZ : R ≤ centerOf Q := A4.omegaOneCenterOf_le_centerOf Q
  have hQLT : Q ≤ L ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hRN : L ⊔ T ≤ Subgroup.normalizer (R : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)).trans
      (normalizer_le_normalizer_of_map_mulEquiv (F := fun X => omegaOneCenterOf X)
        (fun φ X => omegaOneCenterOf_map_mulEquiv φ X) _)
  have hRe : IsElemAbelian 2 R := B2F.isElemAbelian_omegaOneCenterOf Q
  have hVR : V ≤ R := by
    intro v hv
    have hvC : v ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      rw [← hQ] at hq
      exact (Subgroup.mem_centralizer_iff.mp hq.2 v hv).symm
    exact Subgroup.subset_closure ⟨⟨h.le_pCoreOf hv, hvC⟩, h.isElemAbelian.2 v hv⟩
  have hRred : IsTwoReducedIn (L ⊔ T) R := by
    refine ⟨hRZ.trans (inf_le_left.trans hQLT), hRN, hRe, fun D hDH hHD hD => ?_⟩
    have hCV : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ Q :=
      h.toHyp5_0_1.sup_inf_centralizer_le_pCoreOf h.sup_le_normalizer h.module.2.2
    have hD2 : IsPGroup 2 D := by
      intro d
      obtain ⟨k, hk⟩ := hD d d.2
      have hkV : (d : G) ^ 2 ^ k ∈ Subgroup.centralizer (V : Set G) :=
        Subgroup.centralizer_le hVR hk
      have hkQ : (d : G) ^ 2 ^ k ∈ Q := hCV ⟨(L ⊔ T).pow_mem (hDH d.2) _, hkV⟩
      obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T) ⟨_, hkQ⟩
      refine ⟨k + j, Subtype.ext ?_⟩
      have hj' : ((d : G) ^ 2 ^ k) ^ 2 ^ j = 1 := congrArg Subtype.val hj
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [pow_add, pow_mul]
      exact hj'
    have hDQ : D ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hDH hHD hD2
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (Subgroup.mem_centralizer_iff.mp (hRZ hr).2 d (hDQ hd)).symm
  have hRL : ⁅R, L⁆ ≠ ⊥ := fun h0 => h.module.2.2 (by
    rw [eq_bot_iff, ← h0]
    exact Subgroup.commutator_mono hVR le_rfl)
  have hRmod : IsCh5Module T L R :=
    ⟨hRred.1, (isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp hRred).2, hRL⟩
  have hR611 : Hyp611 G T M L R n :=
    { toHyp5_0_1 := h.toHyp5_0_1
      module := hRmod
      not_a5 := fun hc => absurd hc.1 (by omega)
      nParam_eq_one := h.nParam_eq_one
      noLie := h.noLie }
  obtain ⟨hVLc, hVC⟩ := h.commutator_eq_and_inf_of_orth_ch6 horth (by omega)
  rcases ((stmt6_1_2_F4 h512 h513) G T M L R n hR611).1 with hsum | hnat | ⟨-, hRorth⟩
  · exact (horth.false_of_sumTwo_ch6 (by omega) hVR hsum
      (fun a ha b hb => B2F.isElemAbelian_comm hRe ha hb)).elim
  · have hVRc : V ≤ ⁅R, L⁆ := hVLc ▸ Subgroup.commutator_mono hVR le_rfl
    exact (horth.false_of_isNatQuot_ch6 hVRc hVC hnat).elim
  · rcases hRorth.irreducible_ch6 (by omega) V hVR h.L_le_normalizer with h0 | h0
    · exact absurd h0 h.ne_bot
    · exact h0 ▸ le_rfl

end Hyp611

end CFSG.Quasithin.H13

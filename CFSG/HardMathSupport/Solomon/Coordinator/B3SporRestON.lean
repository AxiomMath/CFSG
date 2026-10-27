module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveKit
public import CFSG.RankThree.Native.ONSevenCentralizers
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.Native CFSG.ONSchreier

theorem zpowers_pow_eq_of_lt_prime {G : Type*} [Group G] [Finite G] {y : G} {p k : ℕ}
    (hp : p.Prime) (hy : orderOf y = p) (hk1 : 0 < k) (hkp : k < p) :
    Subgroup.zpowers (y ^ k) = Subgroup.zpowers y := by
  have hcop : (orderOf y).Coprime k := hy ▸ Nat.coprime_of_lt_prime hk1.ne' hkp hp
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 (Subgroup.pow_mem _
    (Subgroup.mem_zpowers y) k)) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, Nat.Coprime.orderOf_pow hcop]


theorem gLAPPrimeCoreOf_onSevenRecord_eq_bot (r : Fin 5) :
    GLAPPrimeCoreOf 7
      (Subgroup.centralizer ({onSevenLine (onSevenRep r)} : Set (Equiv.Perm (Fin N))) ⊓ Pv) =
        ⊥ := by
  obtain ⟨-, -, hCeq, hlow, hhigh, -⟩ := R3E_ON_full_seven_centralizer_structures
  have hp7 : Nat.Prime 7 := by norm_num
  rw [← hCeq r]
  by_cases hr : r.val < 3
  · obtain ⟨-, hFC, hFn, hFcard, hFc, -⟩ := hlow ⟨r.val, hr⟩
    have e : (Fin.castLE (by norm_num) ⟨r.val, hr⟩ : Fin 5) = r := Fin.ext rfl
    rw [e] at hFC hFn hFc
    exact gLAPPrimeCoreOf_eq_bot_of_record_pgroup hp7 hFC hFn
      (IsPGroup.of_card (n := 3) (by rw [hFcard]; norm_num)) hFc
  · have hX : IsPGroup 7 (onSevenC r) :=
      IsPGroup.of_card (n := 2) (by rw [hhigh r (by omega)]; norm_num)
    have h := inf_eq_bot_of_coprime_isPGroup hp7 (coprime_card_GLAPPrimeCoreOf hp7 (onSevenC r)) hX
    rwa [inf_eq_left.mpr (GLAPPrimeCoreOf_le _)] at h

theorem b3Phi_seven_Pv :
    ∀ y ∈ Pv, orderOf y = 7 →
      B3Phi 7 (Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin N))) ⊓ Pv) := by
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlines, -⟩, -, -, -, htrans, hcover⟩ :=
    R3E_ON_full_seven_centralizer_structures
  have hp7 : Nat.Prime 7 := by norm_num
  have : Fact (Nat.Prime 7) := ⟨hp7⟩
  have hPn : ∀ r ∈ Pv, ∀ q ∈ Pv, r * q * r⁻¹ ∈ Pv := fun r hr q hq =>
    Pv.mul_mem (Pv.mul_mem hr hq) (Pv.inv_mem hr)
  refine b3Phi_of_lines hp7 hQP (card_eq_of_sylow_subgroupOf hQP hQsyl) onSevenLine
    (lines_of_eq hlines) fun j => ?_
  obtain ⟨r, t, ht, htj⟩ := hcover j
  obtain ⟨htP, hpow1, hpow6, hj, hconj⟩ := htrans r t ht
  have hjj : (⟨t.line, hj⟩ : Fin 57) = j := Fin.ext htj
  rw [hjj] at hconj
  set h := onSevenTransporterPerm t
  set x := onSevenLine (onSevenRep r)
  have hxo : orderOf x = 7 := orderOf_onSevenLine (onSevenRep r)
  have hyo : orderOf (h * x * h⁻¹) = 7 := by
    have := (MulAut.conj h : Equiv.Perm (Fin N) ≃* Equiv.Perm (Fin N)).orderOf_eq x
    simpa [MulAut.conj_apply, hxo] using this
  have hz : Subgroup.zpowers (onSevenLine j) = Subgroup.zpowers (h * x * h⁻¹) := by
    rw [← hconj]
    exact zpowers_pow_eq_of_lt_prime hp7 hyo (by omega) (by omega)
  rw [centralizer_singleton_eq_of_zpowers hz]
  exact b3Phi_conj_of_normalizes hp7 hPn htP
    (b3Phi_of_oPrime (gLAPPrimeCoreOf_onSevenRecord_eq_bot r))

theorem b3SporPair_ONan_seven (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) :
    B3SporPair .ONan 7 :=
  b3SporPair_of_model_prime (by norm_num) (by norm_num) hOut ↥Pv
    ⟨onEquivPv.symm.trans (hbr .ONan).some⟩
    (b3Phi_centralizer_of_sub (by norm_num) Pv b3Phi_seven_Pv)

end CFSG.HardMathSupport.Solomon.Coordinator

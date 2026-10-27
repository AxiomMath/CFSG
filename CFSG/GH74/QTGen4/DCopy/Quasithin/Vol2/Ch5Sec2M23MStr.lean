module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23MStr
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23Fus

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem pCoreOf_M_eq_F4 (h527 : Stmt5_2_7_F4) {T M L V H B D L₂ : Subgroup G} {n : ℕ}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) : pCoreOf 2 M = pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hO2L, -⟩ := h527 G T M L V H B D L₂ n hyp
  have hBM : B ≤ M := hyp.notation59.1.1.trans inf_le_left
  have hDM : D ≤ M := hyp.notation59.2.1.1.trans (inf_le_left.trans hyp.L_le)
  have hTs : IsSylowTwoOf T M := isSylowTwoOf_of_isSylowTwo hyp.sylow hyp.T_le
  have hMT : pCoreOf 2 M ≤ T := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTs
  apply le_antisymm
  · rw [hO2L]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hMT.trans le_sup_right) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
    exact (sup_le (sup_le (sup_le hyp.L_le hBM) hDM) hyp.T_le).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hyp.L_le)
      (hyp.normal.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem centralizer_le_pCoreOf_L_F4 (h527 : Stmt5_2_7_F4) {T M L V H B D L₂ : Subgroup G} {n : ℕ}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (h16 : Nat.card ↥(pCoreOf 2 L) = 16) :
    M ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) ≤ pCoreOf 2 L := by
  have hM := pCoreOf_M_eq_F4 h527 hyp
  have hchar : CharTwo M :=
    charTwo_of_inH' hyp.qtke hyp.sylow ⟨hyp.T_le, hM ▸ pCoreOf_L_ne_bot h16⟩
  have h := hchar
  unfold CharTwo at h
  rwa [hM] at h

theorem inf_L_facts_of_setting_F4
    (h526 : Stmt5_2_6_F4) (h527 : Stmt5_2_7_F4) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4)
    (hU4 : Stmt5_2_8_U4_F4) (hsp : Stmt5_2_8_special_F4) (hQ : Stmt5_2_8_Q_F4)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) :
    T ⊓ L = T ⊓ oTwoUpper H ∧ pCoreOf 2 M2 ≤ T ⊓ L ∧ pCoreOf 2 L ≤ T ⊓ L ∧
      Nat.card ↥(T ⊓ L) = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hQeq, -, -⟩ := setting_K_facts_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨-, -, -, -, hcardL⟩ := setting_L_facts_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨-, ⟨-, -, -, hSL, hSK, -⟩, -⟩ := h527 G T M L V H B D L₂ n hyp
  have hTK : T ⊓ L = T ⊓ oTwoUpper H := hSL.symm.trans hSK
  have hTsM2 : IsSylowTwoOf T M2 := isSylowTwoOf_of_isSylowTwo hyp.sylow hS.T_le
  have hTsM : IsSylowTwoOf T M := isSylowTwoOf_of_isSylowTwo hyp.sylow hyp.T_le
  have hUT : pCoreOf 2 M2 ≤ T := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTsM2
  have hUK : pCoreOf 2 M2 ≤ oTwoUpper H :=
    hQeq ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoUpper H)
  have hVT : pCoreOf 2 L ≤ T :=
    pCoreOf_M_eq_F4 h527 hyp ▸ CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTsM
  refine ⟨hTK, hTK ▸ le_inf hUT hUK, le_inf hVT (CFSG.LieType.BorelTits.pCoreOf_le 2 L), ?_⟩
  have hSyl : IsSylowTwoOf (T ⊓ L) L :=
    CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hTsM hyp.L_le hyp.normal
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSyl.2.1
  have h2 := Subgroup.relIndex_mul_card (H := T ⊓ L) (K := L)
  rw [inf_of_le_left inf_le_right, hk, hcardL, mul_comm] at h2
  have h6 : k = 6 := eq_six_of_two_pow_mul_eq_960 h2 hSyl.2.2
  rw [hk, h6]
  norm_num

theorem fix_five_six_of_mem_oTwoUpper_F4 (h526 : Stmt5_2_6_F4)
    (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4) (hU4 : Stmt5_2_8_U4_F4) (hsp : Stmt5_2_8_special_F4)
    (hQ : Stmt5_2_8_Q_F4) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) {k : G}
    (hk : k ∈ oTwoUpper H) (hkM2 : k ∈ M2) :
    π ⟨k, hkM2⟩ 5 = 5 ∧ π ⟨k, hkM2⟩ 6 = 6 := by
  have hHstab := eq_setStabIn_of_setting_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  set F : Subgroup (Equiv.Perm (Fin 7)) :=
    MulAction.stabilizer (Equiv.Perm (Fin 7)) (5 : Fin 7) ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 7)) (6 : Fin 7) with hF
  have hle : oTwoUpper H ≤ (F.comap π).map M2.subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxH, hxo⟩
    rw [hHstab, mem_setStabIn] at hxH
    obtain ⟨hxM2, hx56⟩ := hxH
    refine ⟨⟨x, hxM2⟩, ?_, rfl⟩
    rw [smul_pair_set_eq_iff] at hx56
    have hodd : Odd (orderOf (π ⟨x, hxM2⟩)) := by
      have hd : orderOf (π ⟨x, hxM2⟩) ∣ orderOf x := by
        rw [← Subgroup.orderOf_mk x hxM2]
        exact orderOf_map_dvd π _
      exact Odd.of_dvd_nat hxo hd
    rcases hx56 with ⟨h5, h6⟩ | ⟨h5, h6⟩
    · exact ⟨h5, h6⟩
    · exfalso
      obtain ⟨m, hm⟩ := hodd
      have hsq : (π ⟨x, hxM2⟩ ^ 2) 5 = 5 := by
        rw [sq, Equiv.Perm.mul_apply, h5, h6]
      have hpow : ∀ j : ℕ, (π ⟨x, hxM2⟩ ^ (2 * j)) 5 = 5 := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          rw [show 2 * (j + 1) = 2 + 2 * j by ring, pow_add, Equiv.Perm.mul_apply, ih, hsq]
      have h1 : (π ⟨x, hxM2⟩ ^ orderOf (π ⟨x, hxM2⟩)) 5 = 5 := by
        rw [pow_orderOf_eq_one]
        rfl
      rw [hm, pow_succ, Equiv.Perm.mul_apply, h5, pow_mul] at h1
      have h2 := hpow m
      rw [pow_mul] at h2
      have h3 : ((π ⟨x, hxM2⟩ ^ 2) ^ m) 6 = 6 := by
        have h6' : (π ⟨x, hxM2⟩ ^ 2) 6 = 6 := by
          rw [sq, Equiv.Perm.mul_apply, h6, h5]
        clear h1 h2 hpow hm
        induction m with
        | zero => simp
        | succ j ih => rw [pow_succ, Equiv.Perm.mul_apply, h6', ih]
      rw [h3] at h1
      exact absurd h1 (by decide)
  obtain ⟨k', hk', hkk'⟩ := hle hk
  have e : k' = ⟨k, hkM2⟩ := Subtype.ext hkk'
  rw [← e]
  exact hk'

end CFSG.Quasithin.H13

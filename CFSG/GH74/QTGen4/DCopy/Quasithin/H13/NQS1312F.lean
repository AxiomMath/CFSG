module

public import CFSG.Quasithin.H13.NQS1312F
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.NQS1312H
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3E61

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem two_le_rParam_F4
    (h1332 : Stmt13_3_2_F4) (h311 : Theorem311Stmt) {T L V : Subgroup G} {z : G}
    [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z) :
    (2 : ℕ∞) ≤ E3.rParam V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV64 : Nat.card V = 64 := hF.2.2.2.1
  obtain ⟨-, -, hTIM, -, -⟩ := u3_selected_local_normalizer_and_TI_of_1332_F4 h1332 hH hF
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 6) (by rw [hV64]; norm_num)
  refine le_iInf fun U => le_iInf fun hU => ?_
  obtain ⟨hUV, hUN⟩ := hU
  by_contra hlt
  have hm : E3.mQuot V U < 2 := by
    push Not at hlt
    exact_mod_cast hlt
  interval_cases hm' : E3.mQuot V U
  ·
    have hUeq : U = V := (E3.mQuot_eq_zero_iff hV2 hUV).1 hm'
    apply hUN
    rw [hUeq]
    intro c hc
    have hcx : ∀ y ∈ V, c * y * c⁻¹ = y := fun y hy => by
      have h := (mem_centralizer_iff.1 hc) y hy
      calc c * y * c⁻¹ = y * c * c⁻¹ := by rw [← h]
        _ = y := by group
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hcx x hx]
      exact hx
    · intro hx
      have h1 := hcx _ hx
      have h2 : c * x * c⁻¹ = x := by
        have h3 : c * (c * x * c⁻¹) * c⁻¹ = c * x * c⁻¹ := h1
        have h4 := congrArg (fun w => c⁻¹ * w * c) h3
        simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at h4
        rw [mul_assoc]
        exact h4
      rw [← h2]
      exact hx
  ·
    have hidx : U.relIndex V = 2 := by
      rw [E3.relIndex_eq_two_pow hV2 U, hm', pow_one]
    have hCM := u3_hyperplane_centralizer_F4 h1332 h311 hH hU3 hF hUV hidx
    have hU1 : U ≠ ⊥ := by
      intro h
      have h1 := card_mul_relIndex hUV
      rw [hidx, hV64, h, card_bot] at h1
      norm_num at h1
    apply hUN
    intro c hc
    rcases hTIM c (hCM hc) with h | h
    · rw [mem_normalizer_iff]
      intro x
      rw [← mem_conjugate_iff', h]
    · exfalso
      apply hU1
      rw [eq_bot_iff, ← h]
      intro f hf
      refine ⟨hUV hf, mem_conjugate_iff'.2 ?_⟩
      rw [← (mem_centralizer_iff.1 hc) f hf, mul_inv_cancel_right]
      exact hUV hf

theorem two_le_mParam_F4
    (h1332 : Stmt13_3_2_F4) {T L V : Subgroup G} {z : G} [IsElementaryAbelian 2 V]
    (hH : QTH13 G T L) (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    (hF : QTU3InternalFrame T L V z) (hV : IsElemAbelian 2 V) :
    2 ≤ E3.mParam (autI hV ⊤) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV64 : Nat.card V = 64 := hF.2.2.2.1
  have hcardI : Nat.card (IntMod V hV) = 64 := hV64
  obtain ⟨-, b, -, -, -, hprof⟩ := u3_six_action_profile_producer_F4 h1332 G T L V z hH hU3 hF
  unfold E3.mParam
  split_ifs with hev
  · obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(autI hV ⊤)) 2
      (even_iff_two_dvd.1 hev)
    refine le_csInf ⟨_, (t : MulAut (IntMod V hV)), t.2, by rw [Subgroup.orderOf_coe, ht], rfl⟩
      ?_
    rintro _ ⟨s, hs, hso, rfl⟩
    obtain ⟨n, -, rfl⟩ := (mem_autI hV).1 hs
    set e := u3ConjLin V (normalizer (V : Set G)) le_rfl n with he

    have hn2 : ((n ^ 2 : normalizer (V : Set G)) : G) ∈ centralizer (V : Set G) := by
      refine (convI_eq_one_iff hV (n ^ 2)).1 ?_
      rw [map_pow, ← hso, pow_orderOf_eq_one]
    have he2 : e ^ 2 = 1 := by
      rw [he, ← map_pow]
      exact (u3ConjLin_eq_one_iff (n ^ 2)).2 hn2
    have he1 : e ≠ 1 := by
      intro h1
      have hnC := (u3ConjLin_eq_one_iff n).1 h1
      have hc1 := (convI_eq_one_iff hV n).2 hnC
      rw [hc1, orderOf_one] at hso
      exact absurd hso (by norm_num)
    have hord : orderOf e = 2 := orderOf_eq_prime he2 he1
    have hrank : 2 ≤ linRank e := hprof.2.2.2.2.1 e ⟨n, rfl⟩ hord
    have hcard := two_pow_linRank_mul_card (hH := (le_rfl : normalizer (V : Set G) ≤ _)) n
    rw [hV64] at hcard
    have hC16 : Nat.card (V ⊓ centralizer ({(n : G)} : Set G) : Subgroup G) ≤ 16 := by
      have h4 : 4 ≤ 2 ^ linRank e := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ linRank e := Nat.pow_le_pow_right (by norm_num) hrank
      nlinarith

    set X := fixV (zpowers (convI hV n)) with hX
    have hXcard : Nat.card X ≤ 16 := by
      have hmem : ∀ x : X, (x : IntMod V hV).val ∈ centralizer ({(n : G)} : Set G) := by
        intro x
        rw [mem_centralizer_singleton_iff]
        have hx := (mem_fixV.1 x.2) (convI hV n) (mem_zpowers _)
        have h1 := congrArg IntMod.val hx
        rw [convI_apply_val] at h1
        exact (calc (n : G) * (x : IntMod V hV).val
            = (n : G) * (x : IntMod V hV).val * (n : G)⁻¹ * n := by group
          _ = (x : IntMod V hV).val * n := by rw [h1]).symm
      refine le_trans (Nat.card_le_card_of_injective
        (fun x : X => (⟨(x : IntMod V hV).val,
          Subgroup.mem_inf.2 ⟨(x : IntMod V hV).val_mem, hmem x⟩⟩ :
            (V ⊓ centralizer ({(n : G)} : Set G) : Subgroup G))) ?_) hC16
      intro x y hxy
      have h := congrArg Subtype.val hxy
      simp only at h
      exact Subtype.ext (IntMod.val_injective h)
    have hidx : X.index * Nat.card X = 64 := by
      rw [Subgroup.index_mul_card, hcardI]
    have hXd : Nat.card X ∣ 16 :=
      dvd_sixteen_of_dvd (hcardI ▸ Subgroup.card_subgroup_dvd_card X) hXcard
    have h4 : 2 ^ 2 ∣ X.index := by
      obtain ⟨d, hd⟩ := hXd
      have hpos : 0 < Nat.card X := Nat.card_pos
      refine ⟨d, ?_⟩
      have : X.index * Nat.card X = 4 * d * Nat.card X := by
        rw [hidx]
        nlinarith
      have := Nat.eq_of_mul_eq_mul_right hpos this
      rw [this]
      ring
    unfold rkIdx
    exact (padicValNat_dvd_iff_le (Subgroup.index_ne_zero_of_finite)).1 h4
  ·
    unfold rk
    rw [hcardI]
    have : padicValNat 2 64 = 6 := by
      rw [show (64 : ℕ) = 2 ^ 6 by norm_num, padicValNat.prime_pow]
    omega

theorem one_lt_sParam_F4
    (h1332 : Stmt13_3_2_F4) (h311 : Theorem311Stmt) {T L V : Subgroup G} {z : G}
    [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z)
    (hV : IsElemAbelian 2 V) : 1 < E3.sParam hV :=
  E3.lt_sParam_of_lt hV (lt_of_lt_of_le (by norm_num) (two_le_rParam_F4 h1332 h311 hH hU3 hF))
    (two_le_mParam_F4 h1332 hH hU3 hF hV)

theorem oTwoFIn_le_line_F4
    (h1332 : Stmt13_3_2_F4) (h311 : Theorem311Stmt) {T L V : Subgroup G} {z : G}
    [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z)
    {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j)
    (hΦN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
      linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k) :
    oTwoFIn (centralizer ({ptOf Φ (vecOf 15), ptOf Φ (vecOf 52)} : Set G)) ≤
      normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hV64, hVQ, hVCQ, -, -, -, -, -, -, -⟩ := id hF
  obtain ⟨-, hVM, -, -, -⟩ := u3_selected_local_normalizer_and_TI_of_1332_F4 h1332 hH hF
  set H := centralizer ({ptOf Φ (vecOf 15), ptOf Φ (vecOf 52)} : Set G) with hHdef
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  have hC23 := hypC23_line_F4 h1332 hH hF hΦLs hΦN
  have hV := isElemAbelian_of_frame (V := V)
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQH : Q ≤ H := hC23.radical.1
  have hQ1 : Q ≠ ⊥ := hC23.radical.2.1
  set X := oTwoFIn H ⊔ Q with hX
  have hQX : IsSylowTwoOf Q X := c2_6_one hC23
  have hS : IsSylowIn 2 Q X := hQX

  have hXsolv : Group.IsSolvable ↥X :=
    isSolvable_sup_line (isSolvable_oTwoFIn_line H) hQp (hQH.trans C2Six.le_normalizer_oTwoFIn)
  have hn1 : E1.nParam X ≤ 1 := E1.solvable_nParam_le_one hXsolv
  have hn0 : ¬ E1.nParam X ≤ 0 := by
    intro h0
    have hodd := E1.odd_of_nParam_le_zero h0
    have h2Q : 2 ∣ Nat.card Q := by
      rcases hQp.card_eq_or_dvd with h | h
      · exact absurd ((Subgroup.card_eq_one).1 h) hQ1
      · exact h
    have h2X : 2 ∣ Nat.card X := h2Q.trans (Subgroup.card_dvd_of_le le_sup_right)
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2X)
  have hj : E1.nParam X = ((1 : ℕ) : ℕ∞) := by
    refine le_antisymm (by exact_mod_cast hn1) ?_
    push Not at hn0
    exact_mod_cast Order.one_le_iff_pos.2 hn0
  have hsP := one_lt_sParam_F4 h1332 h311 hH hU3 hF hV
  have h19 := E3.e3_19 hV hS (i := 0) hj (by simpa using hsP)

  have hVW : V ≤ E3.wClos V 0 Q := by
    refine E3.le_wClos_of_mQuot_le_self hV hVQ le_rfl (by rw [E3.mQuot_self]) ?_
    unfold rk
    rw [hV64, show (64 : ℕ) = 2 ^ 6 by norm_num, padicValNat.prime_pow]
    norm_num
  have hV1 : V ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hV64
    norm_num at hV64
  have hW1 : E3.wClos V 0 Q ≠ ⊥ := fun h => hV1 (le_bot_iff.1 (h ▸ hVW))
  have hWQ : E3.wClos V 0 Q ≤ Q := E3.wClos_le 0 Q
  have hNW : normalizer (E3.wClos V 0 Q : Set G) ≤ normalizer (L : Set G) :=
    normalizer_le_of_le_Q_F4 h1332 hH hW1 (hQp.to_le hWQ) hWQ
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans
        (E3.normalizer_le_normalizer_wClos Q))
  have hVC1 : V ≤ E3.cClos V (0 + 1) Q := by
    refine le_inf hVQ fun v hv => mem_centralizer_iff.2 fun w hw => ?_
    exact (mem_centralizer_iff.1 (hVCQ hv)) w (E3.wClos_le _ Q hw)
  have hXM : X ≤ normalizer (L : Set G) := by
    rw [← h19]
    refine sup_le ?_ ?_
    · exact inf_le_right.trans ((Subgroup.centralizer_le hVC1).trans
        ((centralizer_le_normalizer_self V).trans hVM))
    · exact inf_le_right.trans hNW
  exact le_sup_left.trans hXM

end CFSG.Quasithin.H13.U3.NLine

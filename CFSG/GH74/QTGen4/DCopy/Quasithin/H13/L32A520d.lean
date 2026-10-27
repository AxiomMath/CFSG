module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A520a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A520b
public import CFSG.Quasithin.H13.L32A520c
public import CFSG.Quasithin.H13.L32A53c

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

section Setting

variable {T L V H : Subgroup G}

theorem l1_facts_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (S : Setting147 G T L V H) {Y : Subgroup G} (hYH : Y ≤ H)
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) :
    T ≤ Subgroup.normalizer (l1 T L V : Set G) ∧ pCoreOf 2 Y ≤ T ∧
      ∀ P : Subgroup G, IsPGroup 2 P → ¬ l1 T L V ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  refine ⟨fun t ht => normalizer_le_normalizer_oTwoUpper _
    (Subgroup.inf_normalizer_le_normalizer_inf ⟨S14.TL_F4 ht, Subgroup.le_normalizer (S14.T_V1_F4 ht)⟩),
    ?_, fun P hP hle => ?_⟩
  · exact (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans hYH)
      (hHY.trans (normalizer_le_normalizer_pCoreOf 2 Y)) (pCoreOf_isPGroup 2 Y)).trans
      (pCoreOf_le_of_le S.hyp hTH)
  · have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
    have h3 := S14.Lp3_F4
    rw [hl1eq] at h3
    have hle' : l1 T L V ≤ pCoreOf 2 (l1 T L V) :=
      le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer (hP.to_le hle)
    rw [Subgroup.relIndex_eq_one.mpr hle'] at h3
    exact absurd h3 (by norm_num)

theorem lemma14_5_20_i_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (S : Setting147 G T L V H) {Y : Subgroup G} (hYH : Y ≤ H)
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) (hL₁Y : l1 T L V ≤ Y)
    (hc : Nat.card (↥Y ⧸ (pCoreOf 2 Y).subgroupOf Y) = 3) :
    l1 T L V ⊔ pCoreOf 2 Y = Y ∧ H ≤ Subgroup.normalizer (l1 T L V : Set G) := by
  obtain ⟨hTl1, hQT, hl1two⟩ := l1_facts_F4 h1222 h1332 h1334 S hYH hHY
  have hY3 : (pCoreOf 2 Y).relIndex Y = 3 := by rw [relIndex_eq_card_quot, hc]
  have hle : l1 T L V ⊔ pCoreOf 2 Y ≤ Y := sup_le hL₁Y (pCoreOf_le 2 Y)
  have hJ : l1 T L V ⊔ pCoreOf 2 Y = Y := by
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_right : pCoreOf 2 Y ≤ _) hle
    rw [hY3] at hmul
    have hne1 : (pCoreOf 2 Y).relIndex (l1 T L V ⊔ pCoreOf 2 Y) ≠ 1 := fun h =>
      hl1two _ (pCoreOf_isPGroup 2 Y) (le_sup_left.trans (Subgroup.relIndex_eq_one.mp h))
    have hd : (pCoreOf 2 Y).relIndex (l1 T L V ⊔ pCoreOf 2 Y) ∣ 3 := ⟨_, hmul.symm⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd h hne1
    · rw [h] at hmul
      have h2 : (l1 T L V ⊔ pCoreOf 2 Y).relIndex Y = 1 := by omega
      exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h2)
  refine ⟨hJ, ?_⟩
  have hO : oTwoUpper Y = l1 T L V := by
    refine le_antisymm ?_ ?_
    · rw [← hJ]
      exact oTwoUpper_sup_le_of_two (pCoreOf_isPGroup 2 Y) (hQT.trans hTl1)
    · calc l1 T L V = oTwoUpper (l1 T L V) := (oTwoUpper_oTwoUpper _).symm
        _ ≤ oTwoUpper Y := oTwoUpper_mono hL₁Y
  rw [← hO]
  exact hHY.trans (normalizer_le_normalizer_oTwoUpper Y)

theorem lemma14_5_20_ii_F4 (h331 : Stmt3_3_1_F4) (hThm : Thm14_5_3_F4) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (S : Setting147 G T L V H) {Y : Subgroup G}
    (hYH : Y ≤ H) (hHY : H ≤ Subgroup.normalizer (Y : Set G))
    (hY3 : ∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 Y) (hL₁Y : l1 T L V ≤ Y)
    (hP : IsPOnePlusTwo 3 (↥Y ⧸ (pCoreOf 2 Y).subgroupOf Y)) :
    l1 T L V = oTwoUpper (o2z Y) ∧
      l1 T L V = oTwoUpper (Y ⊓ Subgroup.normalizer (L : Set G)) ∧
      ∀ W : Subgroup G, l1 T L V ⊔ pCoreOf 2 Y ≤ W → W ≤ Y →
        T ≤ Subgroup.normalizer (W : Set G) → W = l1 T L V ⊔ pCoreOf 2 Y ∨ W = Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTl1, hQT, hl1two⟩ := l1_facts_F4 h1222 h1332 h1334 S hYH hHY
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := hTH.trans hHY
  have hTQ : T ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    hTY.trans (normalizer_le_normalizer_pCoreOf 2 Y)
  have hQY : pCoreOf 2 Y ≤ Y := pCoreOf_le 2 Y

  have hQZ : pCoreOf 2 Y ≤ o2z Y := fun q hq => mem_o2z_iff.mpr ⟨hQY hq, fun y hy => by
    have h1 : y * q⁻¹ * y⁻¹ ∈ pCoreOf 2 Y :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Y hy) _).mp (inv_mem hq)
    rw [show q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) by group]
    exact mul_mem hq h1⟩
  have hZ3 : ∀ z ∈ o2z Y, z ^ 3 ∈ pCoreOf 2 Y := fun z hz => hY3 z (o2z_le Y hz)

  have hYZ3 : (pCoreOf 2 (oTwoUpper (o2z Y))).relIndex (oTwoUpper (o2z Y)) = 3 := by
    rw [relIndex_oTwoUpper_eq hQZ (o2z_le Y) hZ3, relIndex_o2z hP]
  have hHYZ : H ≤ Subgroup.normalizer (oTwoUpper (o2z Y) : Set G) :=
    (hHY.trans (normalizer_le_normalizer_o2z Y)).trans (normalizer_le_normalizer_oTwoUpper _)
  have hYZH : oTwoUpper (o2z Y) ≤ H := (oTwoUpper_le _).trans ((o2z_le Y).trans hYH)

  have hYZM : oTwoUpper (o2z Y) ≤ Subgroup.normalizer (L : Set G) :=
    le_M_of_index_three_F4 h331 hThm h1222 h1332 h1334 S hYZH (oTwoUpper_oTwoUpper _)
      (hTH.trans hHYZ) hYZ3 (Subgroup.set_mul_normalizer_comm _ _ (hL1H.trans hHYZ)).symm

  have hYZY3 : ∀ y ∈ oTwoUpper (o2z Y), y ^ 3 ∈ pCoreOf 2 (oTwoUpper (o2z Y)) := fun y hy => by
    rw [← oTwoUpper_inf_pCoreOf (o2z_le Y) hZ3]
    exact ⟨pow_mem hy 3, hZ3 y (oTwoUpper_le _ hy)⟩
  have hL₁YZ : l1 T L V ≤ oTwoUpper (o2z Y) := by
    rcases lemma14_5_20A_F4 h1222 h1332 h1334 S Nat.prime_three hYZH hHYZ hYZY3 with h | ⟨-, h⟩
    · exfalso
      rw [inf_eq_left.mpr hYZM] at h
      rw [← h, Subgroup.relIndex_self] at hYZ3
      exact absurd hYZ3 (by norm_num)
    · exact h

  have hL₁eq : l1 T L V = oTwoUpper (o2z Y) := by
    refine le_antisymm hL₁YZ ?_
    have hO2 : pCoreOf 2 (oTwoUpper (o2z Y)) ≤ T := by
      rw [← oTwoUpper_inf_pCoreOf (o2z_le Y) hZ3]
      exact inf_le_right.trans hQT
    have hle : l1 T L V ⊔ pCoreOf 2 (oTwoUpper (o2z Y)) ≤ oTwoUpper (o2z Y) :=
      sup_le hL₁YZ (pCoreOf_le 2 _)
    have hJ : l1 T L V ⊔ pCoreOf 2 (oTwoUpper (o2z Y)) = oTwoUpper (o2z Y) := by
      have hmul := Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_right :
        pCoreOf 2 (oTwoUpper (o2z Y)) ≤ _) hle
      rw [hYZ3] at hmul
      have hne1 : (pCoreOf 2 (oTwoUpper (o2z Y))).relIndex
          (l1 T L V ⊔ pCoreOf 2 (oTwoUpper (o2z Y))) ≠ 1 := fun h =>
        hl1two _ (pCoreOf_isPGroup 2 _) (le_sup_left.trans (Subgroup.relIndex_eq_one.mp h))
      have hd : (pCoreOf 2 (oTwoUpper (o2z Y))).relIndex
          (l1 T L V ⊔ pCoreOf 2 (oTwoUpper (o2z Y))) ∣ 3 := ⟨_, hmul.symm⟩
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
      · exact absurd h hne1
      · rw [h] at hmul
        have h2 : (l1 T L V ⊔ pCoreOf 2 (oTwoUpper (o2z Y))).relIndex (oTwoUpper (o2z Y)) = 1 := by
          omega
        exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h2)
    calc oTwoUpper (o2z Y) = oTwoUpper (oTwoUpper (o2z Y)) := (oTwoUpper_oTwoUpper _).symm
      _ = oTwoUpper (l1 T L V ⊔ pCoreOf 2 (oTwoUpper (o2z Y))) := by rw [hJ]
      _ ≤ l1 T L V := oTwoUpper_sup_le_of_two (pCoreOf_isPGroup 2 _) (hO2.trans hTl1)

  have hL₁Q : l1 T L V ⊔ pCoreOf 2 Y = o2z Y := by
    rw [hL₁eq]
    exact oTwoUpper_sup_pCoreOf_eq hQZ hZ3
  have hYL₁ : Y ≤ Subgroup.normalizer (l1 T L V : Set G) := by
    rw [hL₁eq]
    exact Subgroup.le_normalizer.trans ((normalizer_le_normalizer_o2z Y).trans
      (normalizer_le_normalizer_oTwoUpper _))

  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hYnotM : ¬ Y ≤ Subgroup.normalizer (L : Set G) := by
    intro hYM
    have hV1 : fsuV1 T V ≠ ⊥ := fun h => by
      have := S14.card_V1_F4
      rw [h, Subgroup.card_bot] at this
      exact absurd this (by norm_num)
    have h6 := lemma1433Six_of_inputs_F4 h1332 h1334 h1222 G T L V S.hyp.hyp S.hyp.fsu
      (fsuV1 T V) H inf_le_left hV1 S.hz.2.1
    have hYX : Y ≤ L32NSet14.nX T V := fun y hy => by
      have h2 : y ∈ H ⊓ Subgroup.normalizer (L : Set G) := ⟨hYH hy, hYM hy⟩
      rw [h6] at h2
      exact ⟨h2.2, S.hz.2.1 h2.1⟩
    obtain ⟨ψ, hψ⟩ := S14.exists_rep_F4

    obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis_F4
    obtain ⟨x, hx, -, hxa, -⟩ := S14.exists_x_F4 hz hz1 ha haV hb hbV
    have hxX : x ∈ L32NSet14.nX T V := S14.L1_le_X_F4 hx
    have hψx : ψ ⟨x, hxX⟩ ≠ 1 := by
      intro h
      have h2 : x * a * x⁻¹ * a⁻¹ ∈ fsuV1 T V := ((hψ _).mp h).2.2 a (S14.hV2.2.1 ha)
      rw [hxa] at h2
      apply hbV
      have := mul_mem (S14.hV2.1 h2) ha
      rwa [inv_mul_cancel_right] at this
    have hψx3 : ψ ⟨x, hxX⟩ ^ 3 = 1 := S14.cube_eq_one_F4 ψ hx
    have hxY : x ∈ Y := hL₁Y (hl1eq ▸ hx)

    have h2el : ∀ r (hr : r ∈ pCoreOf 2 Y), ψ ⟨r, hYX (hQY hr)⟩ ^ 2 = 1 := by
      intro r hr
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 Y ⟨r, hr⟩
      refine L32NSet14.sl2_sq_of_two (k := k) ?_
      rw [← map_pow]
      have e : (⟨r, hYX (hQY hr)⟩ : ↥(L32NSet14.nX T V)) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [e, map_one]
    have hψQ : ∀ q (hq : q ∈ pCoreOf 2 Y), ψ ⟨q, hYX (hQY hq)⟩ = 1 := by
      intro q hq
      have hxq : x * q * x⁻¹ ∈ pCoreOf 2 Y :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Y hxY) q).mp hq
      refine L32NSet14.sl2_eq_one_of_conj _ _ hψx3 hψx (h2el q hq) ?_
      have h2 := h2el _ (mul_mem hq hxq)
      have e : ψ ⟨q * (x * q * x⁻¹), hYX (hQY (mul_mem hq hxq))⟩ =
          ψ ⟨q, hYX (hQY hq)⟩ * (ψ ⟨x, hxX⟩ * ψ ⟨q, hYX (hQY hq)⟩ * (ψ ⟨x, hxX⟩)⁻¹) := by
        rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
        rfl
      rwa [e] at h2

    have hψ3 : ∀ y (hy : y ∈ Y), ψ ⟨y, hYX hy⟩ ^ 3 = 1 := by
      intro y hy
      rw [← map_pow]
      exact hψQ _ (hY3 y hy)
    have hcommK : ∀ c ∈ Y, ∀ d ∈ Y,
        c * d * c⁻¹ * d⁻¹ ∈ Y ⊓ L32NSet14.trivSub V (fsuV1 T V) := by
      intro c hc d hd
      have hcd : c * d * c⁻¹ * d⁻¹ ∈ Y :=
        mul_mem (mul_mem (mul_mem hc hd) (inv_mem hc)) (inv_mem hd)
      refine Subgroup.mem_inf.mpr ⟨hcd, (hψ ⟨_, hYX hcd⟩).mp ?_⟩
      have e : ψ ⟨c * d * c⁻¹ * d⁻¹, hYX hcd⟩ = ψ ⟨c, hYX hc⟩ * ψ ⟨d, hYX hd⟩ *
          (ψ ⟨c, hYX hc⟩)⁻¹ * (ψ ⟨d, hYX hd⟩)⁻¹ := by
        rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
        rfl
      rw [e, L32NSet14.sl2_cube_comm _ _ (hψ3 c hc) (hψ3 d hd)]
      group
    have hQK : pCoreOf 2 Y ≤ Y ⊓ L32NSet14.trivSub V (fsuV1 T V) := fun q hq =>
      Subgroup.mem_inf.mpr ⟨hQY hq, (hψ ⟨q, hYX (hQY hq)⟩).mp (hψQ q hq)⟩
    have hZK := o2z_le_of_comm_mem hP hQK hcommK
    have hxZ : x ∈ o2z Y := by
      rw [← hL₁Q]
      exact Subgroup.mem_sup_left (hl1eq ▸ hx)
    exact hψx ((hψ _).mpr (Subgroup.mem_inf.mp (hZK hxZ)).2)

  have hYQ : (pCoreOf 2 Y).relIndex Y = 27 := by rw [relIndex_eq_card_quot, hP.2.1]; norm_num
  have hL₁Q3 : (pCoreOf 2 Y).relIndex (l1 T L V ⊔ pCoreOf 2 Y) = 3 := by
    rw [hL₁Q, relIndex_o2z hP]
  have hL₁QY : l1 T L V ⊔ pCoreOf 2 Y ≤ Y := sup_le hL₁Y hQY
  have hTL₁Q : T ≤ Subgroup.normalizer ((l1 T L V ⊔ pCoreOf 2 Y : Subgroup G) : Set G) :=
    fun t ht => F6.mem_normalizer_sup (hTl1 ht) (hTQ ht)
  have hcopT : Nat.Coprime 3 (Nat.card T) := by
    obtain ⟨k, hk⟩ := S.hyp.fsu.sylow.1.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hconj : ∀ {K : Subgroup G}, T ≤ Subgroup.normalizer (K : Set G) →
      ∀ d ∈ T, ∀ x ∈ K, d * x * d⁻¹ ∈ K := fun hK d hd x hx =>
    (Subgroup.mem_normalizer_iff.mp (hK hd) x).mp hx

  have hM3 : ∀ N : Subgroup G, pCoreOf 2 Y ≤ N → N ≤ Y → T ≤ Subgroup.normalizer (N : Set G) →
      (pCoreOf 2 Y).relIndex N = 3 → N ≤ Subgroup.normalizer (L : Set G) := by
    intro N hQN hNY hTN h3
    have hN3 : ∀ k ∈ N, k ^ 3 ∈ pCoreOf 2 Y := fun k hk => hY3 k (hNY hk)
    have hO : oTwoUpper N ≤ Subgroup.normalizer (L : Set G) :=
      le_M_of_index_three_F4 h331 hThm h1222 h1332 h1334 S ((oTwoUpper_le N).trans (hNY.trans hYH))
        (oTwoUpper_oTwoUpper N) (hTN.trans (normalizer_le_normalizer_oTwoUpper N))
        (by rw [relIndex_oTwoUpper_eq hQN hNY hN3, h3])
        (Subgroup.set_mul_normalizer_comm _ _ (((oTwoUpper_le N).trans hNY).trans hYL₁))
    rw [← oTwoUpper_sup_pCoreOf_eq hQN hN3]
    exact sup_le hO (hQT.trans S14.TL_F4)

  have hirr : ∀ W : Subgroup G, l1 T L V ⊔ pCoreOf 2 Y ≤ W → W ≤ Y →
      T ≤ Subgroup.normalizer (W : Set G) → W = l1 T L V ⊔ pCoreOf 2 Y ∨ W = Y := by
    intro W hW1 hW2 hTW
    by_contra hne
    push Not at hne
    apply hYnotM
    have hQW : pCoreOf 2 Y ≤ W := le_sup_right.trans hW1

    have hm1 := Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_right : pCoreOf 2 Y ≤ _) hL₁QY
    rw [hYQ, hL₁Q3] at hm1
    have hm2 := Subgroup.relIndex_mul_relIndex _ _ _ hW1 hW2
    have h9 : (l1 T L V ⊔ pCoreOf 2 Y).relIndex Y = 9 := by omega
    rw [h9] at hm2
    have hn1 : (l1 T L V ⊔ pCoreOf 2 Y).relIndex W ≠ 1 := fun h =>
      hne.1 (le_antisymm (Subgroup.relIndex_eq_one.mp h) hW1)
    have hn2 : W.relIndex Y ≠ 1 := fun h => hne.2 (le_antisymm hW2 (Subgroup.relIndex_eq_one.mp h))
    have hd : (l1 T L V ⊔ pCoreOf 2 Y).relIndex W ∣ 3 ^ 2 := ⟨_, by rw [hm2]; norm_num⟩
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    have hW3 : (l1 T L V ⊔ pCoreOf 2 Y).relIndex W = 3 := by
      interval_cases i
      · exact absurd hi' (by simpa using hn1)
      · simpa using hi'
      · rw [hi'] at hm2
        exact absurd (by omega : W.relIndex Y = 1) hn2
    have hWY3 : W.relIndex Y = 3 := by rw [hW3] at hm2; omega
    have hWQ9 : (pCoreOf 2 Y).relIndex W = 9 := by
      rw [← Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_right : pCoreOf 2 Y ≤ _) hW1, hL₁Q3, hW3]

    have hcW := comm_mem_of_relIndex_le hW2 (fun k hk => hY3 k (hW2 hk)) hWQ9.le
    obtain ⟨N₁, hQN₁, hN₁W, hTN₁, hsup₁, hinf₁⟩ :=
      CFSG.GH74.BNPair.exists_invariant_complement_interval (p := 3) (Q := W)
        (Φ := pCoreOf 2 Y) (D := T) (T := l1 T L V ⊔ pCoreOf 2 Y) hQW hcW
        (fun k hk => hY3 k (hW2 hk)) hcopT (hconj hTW) (hconj hTQ) le_sup_right hW1 (hconj hTL₁Q)
    have hTN₁' : T ≤ Subgroup.normalizer (N₁ : Set G) := fun d hd => by
      refine Subgroup.mem_normalizer_fintype fun x hx => hTN₁ d hd x hx
    have hN₁3 : (pCoreOf 2 Y).relIndex N₁ = 3 := by
      have hn := le_normalizer_of_comm_mem hQN₁ hcW hN₁W
      have := U3.relIndex_sup_eq (hW1.trans hn)
      rw [sup_comm N₁, hsup₁, inf_comm N₁, hinf₁, hW3] at this
      exact this.symm
    have hN₁M := hM3 N₁ hQN₁ (hN₁W.trans hW2) hTN₁' hN₁3

    have hcY : ∀ x ∈ Y, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ l1 T L V ⊔ pCoreOf 2 Y := by
      rw [hL₁Q]
      exact comm_mem_o2z hP
    obtain ⟨N₂, hZN₂, hN₂Y, hTN₂, hsup₂, hinf₂⟩ :=
      CFSG.GH74.BNPair.exists_invariant_complement_interval (p := 3) (Q := Y)
        (Φ := l1 T L V ⊔ pCoreOf 2 Y) (D := T) (T := W) hL₁QY hcY
        (fun k hk => Subgroup.mem_sup_right (hY3 k hk)) hcopT (hconj hTY) (hconj hTL₁Q) hW1 hW2
        (hconj hTW)
    have hN₂3 : (l1 T L V ⊔ pCoreOf 2 Y).relIndex N₂ = 3 := by
      have hn := le_normalizer_of_comm_mem hZN₂ hcY hN₂Y
      have := U3.relIndex_sup_eq (hW2.trans hn)
      rw [sup_comm N₂, hsup₂, inf_comm N₂, hinf₂, hWY3] at this
      exact this.symm
    have hN₂Q9 : (pCoreOf 2 Y).relIndex N₂ = 9 := by
      rw [← Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_right : pCoreOf 2 Y ≤ _) hZN₂, hL₁Q3,
        hN₂3]
    have hTN₂' : T ≤ Subgroup.normalizer (N₂ : Set G) := fun d hd =>
      Subgroup.mem_normalizer_fintype fun x hx => hTN₂ d hd x hx

    have hcN₂ := comm_mem_of_relIndex_le hN₂Y (fun k hk => hY3 k (hN₂Y hk)) hN₂Q9.le
    obtain ⟨N₃, hQN₃, hN₃N₂, hTN₃, hsup₃, hinf₃⟩ :=
      CFSG.GH74.BNPair.exists_invariant_complement_interval (p := 3) (Q := N₂)
        (Φ := pCoreOf 2 Y) (D := T) (T := l1 T L V ⊔ pCoreOf 2 Y) (le_sup_right.trans hZN₂) hcN₂
        (fun k hk => hY3 k (hN₂Y hk)) hcopT (hconj hTN₂') (hconj hTQ) le_sup_right hZN₂
        (hconj hTL₁Q)
    have hTN₃' : T ≤ Subgroup.normalizer (N₃ : Set G) := fun d hd =>
      Subgroup.mem_normalizer_fintype fun x hx => hTN₃ d hd x hx
    have hN₃3 : (pCoreOf 2 Y).relIndex N₃ = 3 := by
      have hn := le_normalizer_of_comm_mem hQN₃ hcN₂ hN₃N₂
      have := U3.relIndex_sup_eq (hZN₂.trans hn)
      rw [sup_comm N₃, hsup₃, inf_comm N₃, hinf₃, hN₂3] at this
      exact this.symm
    have hN₃M := hM3 N₃ hQN₃ (hN₃N₂.trans hN₂Y) hTN₃' hN₃3

    have hL₁QM : l1 T L V ⊔ pCoreOf 2 Y ≤ Subgroup.normalizer (L : Set G) :=
      sup_le ((oTwoUpper_le _).trans (inf_le_left.trans Subgroup.le_normalizer)) (hQT.trans S14.TL_F4)
    rw [← hsup₂, ← hsup₁, ← hsup₃]
    exact sup_le (sup_le hL₁QM hN₁M) (sup_le hL₁QM hN₃M)

  refine ⟨hL₁eq, ?_, hirr⟩
  have hL₁M : l1 T L V ≤ Y ⊓ Subgroup.normalizer (L : Set G) :=
    le_inf hL₁Y ((oTwoUpper_le _).trans (inf_le_left.trans Subgroup.le_normalizer))
  have hl1O : l1 T L V ≤ oTwoUpper (Y ⊓ Subgroup.normalizer (L : Set G)) :=
    calc l1 T L V = oTwoUpper (l1 T L V) := (oTwoUpper_oTwoUpper _).symm
      _ ≤ _ := oTwoUpper_mono hL₁M
  have hTJ : T ≤ Subgroup.normalizer
      ((oTwoUpper (Y ⊓ Subgroup.normalizer (L : Set G)) ⊔ pCoreOf 2 Y : Subgroup G) : Set G) :=
    fun t ht => F6.mem_normalizer_sup (normalizer_le_normalizer_oTwoUpper _
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨hTY ht, Subgroup.le_normalizer (S14.TL_F4 ht)⟩))
      (hTQ ht)
  rcases hirr _ (sup_le_sup_right hl1O _)
    (sup_le ((oTwoUpper_le _).trans inf_le_left) hQY) hTJ with h | h
  · refine le_antisymm hl1O ?_
    calc oTwoUpper (Y ⊓ Subgroup.normalizer (L : Set G)) =
        oTwoUpper (oTwoUpper (Y ⊓ Subgroup.normalizer (L : Set G))) := (oTwoUpper_oTwoUpper _).symm
      _ ≤ oTwoUpper (l1 T L V ⊔ pCoreOf 2 Y) := oTwoUpper_mono (le_sup_left.trans h.le)
      _ ≤ l1 T L V := oTwoUpper_sup_le_of_two (pCoreOf_isPGroup 2 Y) (hQT.trans hTl1)
  · exfalso
    apply hYnotM
    rw [← h]
    exact sup_le ((oTwoUpper_le _).trans inf_le_right) (hQT.trans S14.TL_F4)

end Setting

end CFSG.Quasithin.H13.L32A

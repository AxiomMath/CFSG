module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20TrB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem20Stmts
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem20TrA

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

open Lem20T

theorem lem12220Transv_of_F4 (h1222 : Stmt12_2_2_F4) : Lem12220Transv_F4 := by
  classical
  intro G _ _ T L V hH _ A hA hA4 hle
  have htop := autOn_eq_top_F4 h1222 hH hA hA4 hle
  have hC := inf_centralizer_eq_bot_F4 h1222 hH hA hle
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨-, hTV, hred, -⟩, -, -, _, hmod⟩ := hall V hH.irrPlus
  have hV2' : ∀ v : ↥V, v * v = 1 := fun v => by
    rw [← pow_two]
    exact sq_eq_one_of_hyp1223 hH hred v
  have hLV := le_normalizer_of_hyp1223 hH
  have hO2 := pCoreOf_le_centralizer_of_hyp1223 hH hred
  have hT := le_sup_inf_centralizer hH hTV htop

  have hcardL : Nat.card (autOn L V) = Nat.card (MulAut ↥V) := by
    rw [htop, Subgroup.card_top]
  obtain ⟨m, hVm⟩ : ∃ m : ℕ, Nat.card ↥V = 2 ^ m := by
    let _ := MulAutTwo.zmod2Module hV2'
    exact ⟨_, MulAutTwo.card_eq_pow_finrank⟩
  have hAut : Nat.card (MulAut ↥V) = ∏ i : Fin m, (2 ^ m - 2 ^ (i : ℕ)) :=
    MulAutTwo.card_mulAut hV2' hVm
  rw [hAut] at hcardL

  have hZ : (Subgroup.centralizer (L : Set G)).subgroupOf V = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have : (v : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨v.2, Subgroup.mem_subgroupOf.mp hv⟩
    rw [hC, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hpow : ∀ k, Nat.card ↥V = 2 ^ k → m = k := fun k hk =>
    Nat.pow_right_injective le_rfl (hVm.symm.trans hk)
  rcases hmod with ⟨n, hn, -, hnat⟩ | ⟨⟨e⟩, hV16, -⟩ | ⟨⟨e⟩, hV10, -⟩ |
      ⟨n, hn5, hn8, -, hnat⟩ | ⟨hV16, φ, hφs, hφk⟩ | ⟨hLie, hG2⟩ | ⟨-, hZ3, ⟨e⟩, -, hV64, -⟩
  ·
    refine ⟨n, hn, ?_, htop, hnat, hT⟩
    obtain ⟨K, _, _, hK, hR⟩ := hnat
    rw [card_eq_of_realizes hR]
    have e2 : Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin n → K))) ⧸
        (⊥ : Subgroup (Multiplicative (Fin n → K))).subgroupOf ⊤) = Nat.card (Fin n → K) := by
      rw [← Subgroup.index_eq_card, Subgroup.bot_subgroupOf, Subgroup.index_bot,
        Subgroup.card_top]
      exact Nat.card_congr Multiplicative.toAdd
    rw [Nat.card_fun, Nat.card_fin, hK, pow_one] at e2
    exact e2
  ·
    exfalso
    have h1 := card_autOn_le_quotient hLV hO2
    rw [Nat.card_congr e.toEquiv, Nat.card_congr (MulAutTwo.slEquivGL 3).toEquiv,
      Matrix.card_GL_field, ZMod.card, hcardL, hpow 4 hV16] at h1
    exact absurd h1 (by decide)
  ·
    exfalso
    have h1 := card_autOn_le_quotient hLV hO2
    rw [Nat.card_congr e.toEquiv, Nat.card_congr (MulAutTwo.slEquivGL 5).toEquiv,
      Matrix.card_GL_field, ZMod.card, hcardL, hpow 10 hV10] at h1
    exact absurd h1 (by decide)
  ·
    exfalso
    rw [hZ] at hnat
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have : Finite (FFModel.altDn n).Gam := inferInstanceAs (Finite ↥(alternatingGroup (Fin n)))
    have h1 : Nat.card (autOn L V) ≤ Nat.card ↥(alternatingGroup (Fin n)) :=
      card_le_of_realizes hnat
    rw [nat_card_alternatingGroup, Nat.card_fin, hcardL] at h1
    have h2 := card_altDn_ge (n := n) (by omega)
    rw [← card_eq_of_realizes hnat, hVm] at h2
    have h3 : 2 ^ m ≤ 2 ^ (n - 1) := by
      have : Finite (FFModel.altDn n).Amb := inferInstanceAs (Finite (Fin n → ZMod 2))
      rw [← hVm, card_eq_of_realizes hnat]
      calc Nat.card (↥(FFModel.altDn n).sec ⧸ (FFModel.altDn n).ker.subgroupOf
            (FFModel.altDn n).sec) ≤ Nat.card ↥(FFModel.altDn n).sec :=
            Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective)
        _ = 2 ^ (n - 1) := by
          have hc := card_coreMod_mul_two (n := n) (by omega)
          have hsec : Nat.card ↥(FFModel.altDn n).sec = Nat.card (G6.coreMod n) := rfl
          rw [hsec]
          obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          rw [pow_succ] at hc
          simpa using hc
    have hm1 : m ≤ n - 1 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h3
    have hm2 : n ≤ m + 2 := by
      have : 2 ^ n ≤ 2 ^ (m + 2) := by rw [pow_add]; simpa using h2
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    have hcases : (n = 5 ∧ (m = 3 ∨ m = 4)) ∨ (n = 6 ∧ (m = 4 ∨ m = 5)) ∨
        (n = 7 ∧ (m = 5 ∨ m = 6)) ∨ (n = 8 ∧ (m = 6 ∨ m = 7)) := by omega
    rcases hcases with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ |
        ⟨rfl, rfl | rfl⟩ <;> exact absurd h1 (by decide)
  ·
    exfalso
    have h1 := card_autOn_le hLV φ hφs (le_of_eq hφk)
    rw [nat_card_alternatingGroup, Nat.card_fin, hcardL, hpow 4 hV16] at h1
    exact absurd h1 (by decide)
  ·
    exfalso
    have h1 : Nat.card (autOn L V) ≤ 339655680 := by
      have h2 := card_autOn_le_quotient hLV hO2
      rcases hLie with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · rw [Nat.card_congr e.toEquiv] at h2
        have : Fintype K := Fintype.ofFinite K
        have h3 : Nat.card (StatedProj (StatedSU 3 (3 ^ 1) K)) ≤ Nat.card (GL (Fin 3) K) :=
          (Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective).trans
            (Subgroup.card_le_card_group _)
        have hq : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
        rw [Matrix.card_GL_field, hq] at h3
        exact h2.trans (h3.trans (by decide))
      all_goals exact absurd h0 (by norm_num)
    rw [hcardL] at h1
    rw [hZ] at hG2
    obtain ⟨K, _, _, hK, hR⟩ := hG2
    have h6 : Nat.card ↥V = Nat.card (↥(zornO0 K) ⧸ (zornR K).subgroupOf (zornO0 K)) :=
      card_eq_of_realizes hR
    have h4 := card_zornQ_ge (K := K)
    rw [← h6, hK, hVm] at h4
    have h5 : 2 ^ m ≤ 2 ^ 7 := by
      rw [← hVm, h6]
      calc Nat.card (↥(zornO0 K) ⧸ (zornR K).subgroupOf (zornO0 K)) ≤ Nat.card ↥(zornO0 K) :=
            Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective)
        _ = 2 ^ 7 := by rw [card_zornO0, hK]; norm_num
    have hm1 : m ≤ 7 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h5
    have hm2 : 6 ≤ m := by
      by_contra hlt
      have h7 : 2 ^ m ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h4 h7
      omega
    interval_cases m <;> exact absurd h1 (by decide)
  ·
    exfalso
    have h1 := card_autOn_le_quotient hLV hO2
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
    rw [Nat.card_congr e.toEquiv, hZ3, nat_card_alternatingGroup, Nat.card_fin] at h3
    rw [h3, hcardL, hpow 6 hV64] at h1
    exact absurd h1 (by decide)

end CFSG.Quasithin.H13

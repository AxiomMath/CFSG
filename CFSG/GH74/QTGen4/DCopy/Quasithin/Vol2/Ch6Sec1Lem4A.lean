module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem4B
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Remark612

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611

theorem false_of_orth_six_ch6_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (hE63 : Ch6InE63)
    (hH11 : Ch6InH11) (h : Hyp611 G T M L V n) (horth : IsOrthCh5 L V n) (hn : 6 ≤ n) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := h.isElemAbelian
  obtain ⟨a, hna, -, hc, hB⟩ := id horth
  have ha : 3 ≤ a := by omega
  have hB' : BinaryOrthogonalFour (V := IntMod V hV) (autI hV L) ⊤ ⊥ a := hB
  have hLM : autI hV L ≤ autI hV M := A4.autOn_mono h.L_le
  have hMN : autI hV M ≤ Subgroup.normalizer (autI hV L : Set (MulAut (IntMod V hV))) := by
    have key : ∀ k : Subgroup.normalizer (V : Set G), (k : G) ∈ M → ∀ ψ ∈ autI hV L,
        convI hV k * ψ * (convI hV k)⁻¹ ∈ autI hV L := by
      intro k hkM ψ hψ
      obtain ⟨ℓ, hℓL, rfl⟩ := (mem_autI hV).mp hψ
      rw [← map_inv, ← map_mul, ← map_mul]
      have hmem : ((k * ℓ * k⁻¹ : Subgroup.normalizer (V : Set G)) : G) ∈ L := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact (Subgroup.mem_normalizer_iff.mp (h.normal hkM) ℓ).mp hℓL
      exact convI_mem_autI hV hmem (k * ℓ * k⁻¹).2
    intro φ hφ
    obtain ⟨g, hgM, rfl⟩ := (mem_autI hV).mp hφ
    rw [Subgroup.mem_normalizer_iff]
    intro ψ
    refine ⟨key g hgM ψ, fun hψ => ?_⟩
    have := key g⁻¹ (M.inv_mem hgM) _ hψ
    rwa [map_inv, inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc,
      inv_mul_cancel, mul_one] at this
  have hH := fun (A : Subgroup (MulAut (IntMod V hV))) (hAM : A ≤ autI hV M) (hA1 : A ≠ ⊥)
      (hAe : IsElemAbelian2 A) =>
    hH11 (IntMod V hV) (autI hV L) (autI hV M) a IntMod.sq_eq_one (by omega) hLM hMN hB' A hAM
      hA1 hAe

  have hJ : thompsonJk 1 T ≤ ch6Q T V := by
    unfold thompsonJk
    refine iSup₂_le fun A hA => ?_
    obtain ⟨hAT, hAe, hAmax⟩ := hA
    refine le_inf hAT ?_
    intro x hxA
    by_contra hxC
    obtain ⟨E, hET, hEe, hEc⟩ := H.exists_isElemAbelian_card_pRank T
    have hAE := hAmax E hET hEe
    have hAle := H.card_le_two_pow_pRank hAT hAe
    obtain ⟨k, hk⟩ := H.exists_card_eq_two_pow_of_isElemAbelian hAe
    set m := CFSG.Open.pRank 2 T with hm
    have hkm : k ≤ m := by
      rw [hk] at hAle
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hAle
    have hmk : m ≤ k + 1 := by
      have h2 : 2 ^ m ≤ 2 ^ (k + 1) :=
        calc 2 ^ m ≤ 2 ^ 1 * 2 ^ k := by rw [← hEc, ← hk]; exact hAE
          _ = 2 ^ (k + 1) := by ring
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
    have hcor : IsElemAbelianCorank T (m - k) A :=
      ⟨hAT, hAe, by rw [hk, ← pow_add]; congr 1; omega⟩
    have hB24 := card_le_relIndex_mul_card_mul_two_pow hV h.le_T hcor
    have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAT.trans h.T_le_normalizer
    have hĀM : autI hV A ≤ autI hV M := A4.autOn_mono (hAT.trans h.T_le)
    have hĀ1 : autI hV A ≠ ⊥ := by
      intro h0
      apply hxC
      have hmem := convI_mem_autI hV hxA (hAN hxA)
      rw [h0, Subgroup.mem_bot] at hmem
      exact (convI_eq_one_iff hV _).mp hmem
    have hĀe : IsElemAbelian2 (autI hV A) := isElemAbelian2_autI hV hAe hAN
    obtain ⟨-, h2 | ⟨ha2, -⟩, -⟩ := hH _ hĀM hĀ1 hĀe
    · rw [E3.rk_autI_eq_mQuot hV hAN, E3.rkIdx_fixV_autI hV hAN] at h2
      have hA2 : IsPGroup 2 A := B2F.isPGroup_of_isElemAbelian hAe
      have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
      rw [E3.relIndex_eq_two_pow hA2 (A ⊓ Subgroup.centralizer (V : Set G)),
        E3.card_eq_two_pow_mul hV2
          (inf_le_left : V ⊓ Subgroup.centralizer (A : Set G) ≤ V)] at hB24
      set x := mQuot A (A ⊓ Subgroup.centralizer (V : Set G))
      set y := mQuot V (V ⊓ Subgroup.centralizer (A : Set G))
      set c := Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))
      have hc : 0 < c := Nat.card_pos
      have hj : 2 ^ (m - k) ≤ 2 :=
        calc 2 ^ (m - k) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 2 := by norm_num
      have h4 : 2 ^ y * c ≤ 2 ^ (x + 1) * c :=
        hB24.trans (calc 2 ^ x * c * 2 ^ (m - k) ≤ 2 ^ x * c * 2 := Nat.mul_le_mul_left _ hj
          _ = 2 ^ (x + 1) * c := by ring)
      have h5 : 2 ^ y ≤ 2 ^ (x + 1) := Nat.le_of_mul_le_mul_right h4 hc
      have h6 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h5
      omega
    · omega

  have hr : rParam V = 1 :=
    ((stmt6_1_3_F4 h331 h432) G T M L V n h).2.resolve_right (not_not.mpr hJ)

  have hE := stmt6_1_3_one_F4 h432 h (h.isTISetIn_of_orth_ch6 horth (by omega))

  have hlow : ∀ t ∈ autI hV M, orderOf t = 2 → 3 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
    intro t ht hot
    have ht2 : t ^ 2 = 1 := by rw [← hot]; exact pow_orderOf_eq_one t
    have hAe : IsElemAbelian2 (Subgroup.zpowers t) := by
      refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [← zpow_add, ← zpow_add, add_comm]
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
    have hA1 : Subgroup.zpowers t ≠ ⊥ := by
      intro h0
      have : t = 1 := by
        have := Subgroup.mem_zpowers t
        rwa [h0, Subgroup.mem_bot] at this
      rw [this, orderOf_one] at hot
      exact absurd hot (by norm_num)
    obtain ⟨h1, -, -⟩ := hH _ (Subgroup.zpowers_le.mpr ht) hA1 hAe
    have hrk : rk ↥(Subgroup.zpowers t) = 1 := by
      unfold rk
      rw [Nat.card_zpowers, hot]
      simp
    omega
  have hm : 2 < mParam (autI hV M) := by
    obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(autI hV M)) 2
      (h.two_dvd_card_autI_ch6 hV)
    have hot₀ : orderOf (t₀ : MulAut (IntMod V hV)) = 2 := by
      rw [Subgroup.orderOf_coe]; exact ht₀
    have hev : Even (Nat.card (autI hV M)) :=
      even_iff_two_dvd.mpr (h.two_dvd_card_autI_ch6 hV)
    unfold mParam
    simp only [hev, ↓reduceIte]
    have hne : {k : ℕ | ∃ t ∈ autI hV M, orderOf t = 2 ∧
        k = rkIdx (fixV (Subgroup.zpowers t))}.Nonempty := ⟨_, t₀, t₀.2, hot₀, rfl⟩
    obtain ⟨t, ht, hot, heq⟩ := Nat.sInf_mem hne
    rw [heq]
    have := hlow t ht hot
    omega

  have h5 := (hE63 G T M V hE hV hm).1
  rw [hr] at h5
  have h6 : mParam (autI hV M) ≤ 1 := by exact_mod_cast h5
  omega

end Hyp611

@[expose] def Lem614OrthFour_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G), Hyp611 G T M L V 4 →
    IsOrthCh5 L V 4 → False

theorem stmt6_1_4_of_F4 (h311 : Theorem311Stmt) (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4)
    (h512 : Stmt5_1_2_F4) (h513 : Stmt5_1_3_F4) (hE63 : Ch6InE63) (hH11 : Ch6InH11)
    (hA4 : Lem614OrthFour_F4) : Stmt6_1_4_F4 := by
  intro G _ _ T M L V n h
  rcases ((stmt6_1_2_F4 h512 h513) G T M L V n h).1 with hsum | hnat | ⟨hn, horth⟩
  · exact (h.false_of_sumTwo_F4 h311 h331 h432 hsum).elim
  · exact hnat
  · obtain ⟨a, hna, -⟩ := id horth
    by_cases h6 : 6 ≤ n
    · exact (h.false_of_orth_six_ch6_F4 h331 h432 hE63 hH11 horth h6).elim
    · obtain rfl : n = 4 := by omega
      exact (hA4 G T M L V h horth).elim

end CFSG.Quasithin.H13

module

public import CFSG.GF2Type.Smith1979.WidthFourKP.TriPlus.Data
public import CFSG.GF2Type.Smith1979.WidthFourKP.TriPlus.RmodN
public import CFSG.LargeExtraspecial.S14C10Alt2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.TriPlus

open Subgroup Module CFSG.Open CFSG.GroupTheory CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S5 CFSG.LargeExtraspecial.S7

variable {G : Type} [Group G] [Finite G]

namespace TriData

variable {S : Setting G} {g : G} (T : TriData S g)

theorem e_mem_Mbar (i : Fin 3) : eb T.σ i ∈ S.Mbar :=
  S7.Obar_le_Mbar (T.basis.eb_mem i)

theorem l_mem (i : Fin 3) : T.l i ∈ S.Lbar g :=
  T.basis.l_mem i

theorem e_ne_one (i : Fin 3) : eb T.σ i ≠ 1 := by
  intro h
  have h1 : (Pi.single i 1 : Fin 3 → ZMod 3) = 0 := by
    apply Multiplicative.ofAdd.injective
    exact T.basis.inj (by simpa [eb] using h)
  have h2 := congrFun h1 i
  simpa using h2

theorem e_pow_three (i : Fin 3) : eb T.σ i ^ 3 = 1 := by
  simpa [T.basis.orderOf_eb i] using pow_orderOf_eq_one (eb T.σ i)

theorem card_zpowers_e (i : Fin 3) : Nat.card (zpowers (eb T.σ i)) = 3 := by
  rw [Nat.card_zpowers, T.basis.orderOf_eb i]

theorem l_ne_one (i : Fin 3) : T.l i ≠ 1 := by
  intro h
  have hc := T.basis.conj_l_single i (1 : ZMod 3)
  rw [h] at hc
  have h1 : eb T.σ i = (eb T.σ i)⁻¹ := by
    exact hc
  have h2 : eb T.σ i * eb T.σ i = 1 :=
    mul_eq_one_iff_eq_inv.mpr h1
  have h3 : eb T.σ i ^ 2 * eb T.σ i = 1 := by
    simpa [pow_succ] using T.e_pow_three i
  rw [pow_two, h2, one_mul] at h3
  exact T.e_ne_one i h3

theorem e_fpf (i : Fin 3) (v : S.Qt)
    (hv : ((eb T.σ i : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : v = 0 :=
  (T.fpf_iff (Pi.single i 1)).mpr
    ⟨i, by simp, fun j hj => by simp [Pi.single_eq_of_ne hj]⟩ v hv

theorem l_conj_e (i : Fin 3) :
    T.l i * eb T.σ i * (T.l i)⁻¹ = (eb T.σ i)⁻¹ :=
  T.basis.conj_l_single i (1 : ZMod 3)

theorem l_conj_e_of_ne {i j : Fin 3} (h : i ≠ j) :
    T.l i * eb T.σ j * (T.l i)⁻¹ = eb T.σ j :=
  T.basis.conj_l_single_of_ne (i := i) (j := j) (Ne.symm h) (1 : ZMod 3)

theorem mem_normalizer_iff (x : S.Mbar) (i : Fin 3) :
    (x : S.O) ∈ normalizer (zpowers (eb T.σ i) : Set S.O) ↔ T.perm x i = i := by
  classical
  constructor
  · intro hx
    have hmem : (x : S.O) * eb T.σ i * (x : S.O)⁻¹ ∈ zpowers (eb T.σ i) :=
      (Subgroup.mem_normalizer_iff.mp hx (eb T.σ i)).mp (Subgroup.mem_zpowers _)
    obtain ⟨s, hs, hconj⟩ := T.conj_e x i
    rw [hconj] at hmem
    have hsupp := (T.basis.mem_zpowers_eb_iff i (Pi.single (T.perm x i) s)).mp hmem
    by_contra hne
    exact hs (by simpa using hsupp (T.perm x i) hne)
  · intro hpi
    let P : Subgroup S.O := zpowers (eb T.σ i)
    have hconj : (x : S.O) * eb T.σ i * (x : S.O)⁻¹ ∈ P := by
      obtain ⟨s, -, hconj⟩ := T.conj_e x i
      rw [hconj, hpi, T.basis.sigma_single_eq_pow i s]
      exact Subgroup.pow_mem P (Subgroup.mem_zpowers _) _
    have hmap_le : P.map (MulAut.conj (x : S.O)).toMonoidHom ≤ P := by
      rintro p ⟨q, hq, rfl⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
      change (MulAut.conj (x : S.O)) (eb T.σ i ^ n) ∈ P
      rw [MulAut.conj_apply, ← conj_zpow]
      exact Subgroup.zpow_mem P hconj n
    have hcard : Nat.card (P.map (MulAut.conj (x : S.O)).toMonoidHom) = Nat.card P :=
      Subgroup.card_map_of_injective (MulAut.conj (x : S.O)).injective
    have hEq : P.map (MulAut.conj (x : S.O)).toMonoidHom = P :=
      Subgroup.eq_of_le_of_card_ge hmap_le (by rw [hcard])
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEq

theorem comm_mem_zpowers (x : S.Mbar) {k : Fin 3} (hk : T.perm x k = k) :
    (x : S.O) * T.l k * (x : S.O)⁻¹ * (T.l k)⁻¹ ∈ zpowers (eb T.σ k) := by
  obtain ⟨c, hc⟩ := T.conj_l x
  let y : S.O := T.σ (Multiplicative.ofAdd c)
  have hy : y ∈ S7.Obar S := T.basis.mem_iff.mpr ⟨c, rfl⟩
  have hyinv : y⁻¹ = T.σ (Multiplicative.ofAdd (-c)) := by
    dsimp only [y]
    rw [← map_inv, ← ofAdd_neg]
  have h1 : (x : S.O) * T.l k * (x : S.O)⁻¹ = y * T.l k * y⁻¹ := by
    rw [hc k, hk]
  have hact := T.basis.act k (-c)
  have hneg : negAt k (-c) = -negAt k c := by
    funext j
    by_cases h : j = k
    · subst h
      simp [negAt]
    · simp [negAt, h]
  have hconjneg : y * T.l k * y⁻¹ * (T.l k)⁻¹ =
      T.σ (Multiplicative.ofAdd (c - negAt k c)) := by
    calc y * T.l k * y⁻¹ * (T.l k)⁻¹
        = y * (T.l k * y⁻¹ * (T.l k)⁻¹) := by group
      _ = y * (T.l k * T.σ (Multiplicative.ofAdd (-c)) * (T.l k)⁻¹) := by rw [hyinv]
      _ = y * T.σ (Multiplicative.ofAdd (negAt k (-c))) := by rw [hact]
      _ = y * T.σ (Multiplicative.ofAdd (-negAt k c)) := by rw [hneg]
      _ = T.σ (Multiplicative.ofAdd c) * T.σ (Multiplicative.ofAdd (-negAt k c)) := rfl
      _ = T.σ (Multiplicative.ofAdd (c + (-negAt k c))) := by rw [← map_mul, ← ofAdd_add]
      _ = T.σ (Multiplicative.ofAdd (c - negAt k c)) := by rw [sub_eq_add_neg]
  have hsingle : c - negAt k c = Pi.single k (2 * c k) := by
    funext j
    by_cases h : j = k
    · subst h
      simp [negAt]
      ring
    · simp [negAt, h, sub_eq_add_neg]
  rw [h1, hconjneg, hsingle, T.basis.sigma_single_eq_pow k (2 * c k)]
  exact Subgroup.pow_mem (Subgroup.zpowers (eb T.σ k)) (Subgroup.mem_zpowers _) _

theorem perm_eq_of_commute {x : S.Mbar} {i : Fin 3}
    (hx : (x : S.O) * T.l i = T.l i * (x : S.O)) : T.perm x i = i := by
  classical
  obtain ⟨c, hc⟩ := T.conj_l x
  let y : S.O := T.σ (Multiplicative.ofAdd c)
  have hy : y ∈ S7.Obar S := T.basis.mem_iff.mpr ⟨c, rfl⟩
  have hxconj : (x : S.O) * T.l i * (x : S.O)⁻¹ = T.l i := by
    rw [hx]
    group
  have hli : T.l i = y * T.l (T.perm x i) * y⁻¹ := by
    dsimp only [y]
    rw [← hxconj]
    exact hc i
  have hact_eq : ∀ d : Fin 3 → ZMod 3,
      T.σ (Multiplicative.ofAdd (negAt i d)) =
        T.σ (Multiplicative.ofAdd (negAt (T.perm x i) d)) := by
    intro d
    have hdy : T.σ (Multiplicative.ofAdd d) ∈ S7.Obar S := T.basis.mem_iff.mpr ⟨d, rfl⟩
    have hzy : T.σ (Multiplicative.ofAdd (negAt (T.perm x i) d)) ∈ S7.Obar S :=
      T.basis.mem_iff.mpr ⟨negAt (T.perm x i) d, rfl⟩
    have hleft := T.basis.act i d
    have hright := T.basis.act (T.perm x i) d
    rw [hli] at hleft
    have hcomm : y⁻¹ * T.σ (Multiplicative.ofAdd d) =
        T.σ (Multiplicative.ofAdd d) * y⁻¹ := by
      have hzy : y * T.σ (Multiplicative.ofAdd d) =
          T.σ (Multiplicative.ofAdd d) * y := T.basis.comm hy hdy
      calc y⁻¹ * T.σ (Multiplicative.ofAdd d)
          = y⁻¹ * (T.σ (Multiplicative.ofAdd d) * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * T.σ (Multiplicative.ofAdd d)) * y⁻¹ := by rw [← hzy]
        _ = T.σ (Multiplicative.ofAdd d) * y⁻¹ := by group
    calc T.σ (Multiplicative.ofAdd (negAt i d))
        = (y * T.l (T.perm x i) * y⁻¹) * T.σ (Multiplicative.ofAdd d) *
            (y * T.l (T.perm x i) * y⁻¹)⁻¹ := hleft.symm
      _ = y * T.l (T.perm x i) * (y⁻¹ * T.σ (Multiplicative.ofAdd d) * y) *
            (T.l (T.perm x i))⁻¹ * y⁻¹ := by group
      _ = y * T.l (T.perm x i) * (T.σ (Multiplicative.ofAdd d) * y⁻¹ * y) *
            (T.l (T.perm x i))⁻¹ * y⁻¹ := by rw [hcomm]
      _ = y * (T.l (T.perm x i) * T.σ (Multiplicative.ofAdd d) *
            (T.l (T.perm x i))⁻¹) * y⁻¹ := by group
      _ = y * T.σ (Multiplicative.ofAdd (negAt (T.perm x i) d)) * y⁻¹ := by rw [hright]
      _ = T.σ (Multiplicative.ofAdd (negAt (T.perm x i) d)) := by
            rw [T.basis.comm hy hzy]
            group
  have harg : negAt i (Pi.single i 1) = negAt (T.perm x i) (Pi.single i 1) :=
    Multiplicative.ofAdd.injective (T.basis.inj (hact_eq (Pi.single i 1)))
  by_contra hki
  have hat := congrFun harg i
  rw [negAt, negAt, Function.update_self,
    Function.update_of_ne (Ne.symm hki)] at hat
  have hat' : (-1 : ZMod 3) = 1 := by simpa using hat
  exact absurd hat' (by decide)

theorem Rbar_le (T : TriData S g) (t : S.O) :
    Rbar S g t ≤ S7.Obar S ⊔ S.Lbar g := by
  classical
  refine sSup_le ?_
  rintro X ⟨h, rfl, -⟩
  intro x hx
  obtain ⟨l, hl, hxl⟩ : ∃ l ∈ S.Lbar g, x = S.ρ h * l * (S.ρ h)⁻¹ :=
    ⟨(S.ρ h)⁻¹ * x * S.ρ h, (S4.mem_Lbar_mul_iff S h g).mp hx, by group⟩
  have hxM : x ∈ S.Mbar := S.Lbar_le_Mbar ((h : G) * g) hx
  have hρM : S.ρ h ∈ S.Mbar := MonoidHom.mem_range.mpr ⟨h, rfl⟩
  have hxM' : (⟨x, hxM⟩ : S.Mbar) =
      ⟨S.ρ h, hρM⟩ * ⟨l, S.Lbar_le_Mbar g hl⟩ * ⟨S.ρ h, hρM⟩⁻¹ := by
    apply Subtype.ext
    exact hxl
  have hker : T.perm (⟨l, S.Lbar_le_Mbar g hl⟩ : S.Mbar) = 1 :=
    (T.ker_iff _).mpr (Subgroup.mem_sup_right hl)
  rw [← (T.ker_iff ⟨x, hxM⟩)]
  rw [hxM', map_mul, map_mul, map_inv, hker, mul_one]
  simp

end TriData

theorem TriData.exists_eq_l {S : Setting G} {g : G} (T : TriData S g) (H : Hyp4 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hplus : PlusTypeAt S g ht) :
    ∃ i0 : Fin 3, t = T.l i0 := by
  classical
  have hLY : ∀ x ∈ S.Lbar g, ∀ y ∈ S7.Obar S, x * y * x⁻¹ ∈ S7.Obar S :=
    fun x hx y hy => S7.conj_mem_Obar (S.Lbar_le_Mbar g hx) hy
  have hLsq : ∀ x ∈ S.Lbar g, x * x = 1 :=
    fun x hx => S4.mul_self_of_mem_Lbar S H.conj_mem hx
  have hYL : ∀ x ∈ S7.Obar S, x ∈ S.Lbar g → x = 1 := by
    intro x hxY hxL
    have h2 : orderOf x ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hLsq x hxL)
    have h27 : orderOf x ∣ 27 := by
      have h := Subgroup.orderOf_dvd_natCard (S7.Obar S) hxY
      rwa [T.basis.card_range] at h
    have h1 : orderOf x ∣ 1 := by
      have h := Nat.dvd_gcd h2 h27
      rwa [show Nat.gcd 2 27 = 1 from by norm_num] at h
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  have h9R : 9 ∣ Nat.card (Rbar S g t) := by
    rw [CFSG.LargeExtraspecial.S14.card_Rbar_eq H.conj_mem t,
      card_RmodN_eq_thirtysix H C ht ht1 hVQ hΩ h4 hplus]
    exact dvd_mul_of_dvd_right (by norm_num : 9 ∣ 36) _
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P, hPcard⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := Rbar S g t) 3 (n := 2) h9R
  have hPcard9 : Nat.card P = 9 := by
    rw [hPcard]
    norm_num
  let P' : Subgroup S.O := P.map (Rbar S g t).subtype
  have hP'card : Nat.card P' = 9 := by
    dsimp only [P']
    rw [Subgroup.card_subtype (Rbar S g t) P, hPcard9]
  have hP'R : P' ≤ Rbar S g t := Subgroup.map_subtype_le P
  have hP'Y : P' ≤ S7.Obar S := by
    intro x hx
    have hxsup : x ∈ S7.Obar S ⊔ S.Lbar g := Rbar_le T t (hP'R hx)
    have h9 : x ^ (3 ^ 2) = 1 := by
      have hdvd : orderOf x ∣ 9 := by
        have h := Subgroup.orderOf_dvd_natCard P' hx
        rwa [hP'card] at h
      exact orderOf_dvd_iff_pow_eq_one.mp (by simpa using hdvd)
    exact mem_left_of_mem_sup hLY hLsq hYL hxsup h9
  have hP'C : P' ≤ centralizer ({t} : Set S.O) :=
    hP'R.trans (S4.Rbar_le_centralizer H.conj_mem)
  obtain ⟨s, hs, hact⟩ := T.basis.diag ht
  let neg : Finset (Fin 3) := Finset.univ.filter fun j => s j = -1
  have hneg_le_one : neg.card ≤ 1 := by
    by_contra hle
    have h2 : 2 ≤ neg.card := by omega
    obtain ⟨j1, hj1, j2, hj2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < neg.card)
    have hj1neg : s j1 = -1 := by
      simpa [neg] using (Finset.mem_filter.mp hj1).2
    have hj2neg : s j2 = -1 := by
      simpa [neg] using (Finset.mem_filter.mp hj2).2
    have hex : ∀ j1 j2 : Fin 3, j1 ≠ j2 → ∃ i : Fin 3, i ≠ j1 ∧ i ≠ j2 := by
      decide
    obtain ⟨i, hi1, hi2⟩ := hex j1 j2 hne
    have hcompl : ∀ i j1 j2 : Fin 3, i ≠ j1 → i ≠ j2 → j1 ≠ j2 →
        ∀ j : Fin 3, j ≠ i → j = j1 ∨ j = j2 := by
      decide
    have hP'zp : P' ≤ zpowers (eb T.σ i) := by
      intro y hy
      have hyY : y ∈ S7.Obar S := hP'Y hy
      obtain ⟨c, hc⟩ := T.basis.mem_iff.mp hyY
      have hyt : t * y = y * t :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hP'C hy)).symm
      have hconj : t * T.σ (Multiplicative.ofAdd c) * t⁻¹ =
          T.σ (Multiplicative.ofAdd c) := by
        rw [hc]
        calc t * y * t⁻¹ = y * t * t⁻¹ := by rw [hyt]
          _ = y := by group
      have hsc : s * c = c := by
        have h := hact c
        rw [hconj] at h
        exact (T.basis.inj h).symm
      have hczero : ∀ j, s j = -1 → c j = 0 := by
        intro j hj
        have h := congrFun hsc j
        rw [Pi.mul_apply, hj, neg_one_mul] at h
        have hnc : -c j = c j := h
        have hsum : c j + c j = 0 := by
          calc c j + c j = (-c j) + c j := by rw [hnc]
            _ = 0 := neg_add_cancel _
        have h2c : (2 : ZMod 3) * c j = 0 := by
          simpa [two_mul] using hsum
        exact (mul_eq_zero.mp h2c).resolve_left (by decide)
      rw [← hc]
      refine (T.basis.mem_zpowers_eb_iff i c).mpr ?_
      intro j hj
      rcases hcompl i j1 j2 hi1 hi2 hne j hj with hjeq | hjeq
      · rw [hjeq]
        exact hczero j1 hj1neg
      · rw [hjeq]
        exact hczero j2 hj2neg
    have hcardle := Subgroup.card_le_of_le hP'zp
    rw [hP'card, T.card_zpowers_e i] at hcardle
    omega
  have hneg01 : neg.card = 0 ∨ neg.card = 1 := by omega
  rcases hneg01 with h0 | h1
  ·
    have hs1 : ∀ j, s j = 1 := by
      intro j
      rcases hs j with h | h
      · exact h
      · exfalso
        have hjmem : j ∈ neg := by
          change j ∈ Finset.univ.filter (fun j => s j = -1)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩
        have hpos : 0 < neg.card := Finset.card_pos.mpr ⟨j, hjmem⟩
        omega
    have htcent : ∀ y ∈ S7.Obar S, t * y = y * t := by
      intro y hy
      obtain ⟨c, hc⟩ := T.basis.mem_iff.mp hy
      have hs1' : s = 1 := funext hs1
      have hconj : t * T.σ (Multiplicative.ofAdd c) * t⁻¹ =
          T.σ (Multiplicative.ofAdd c) := by
        rw [hact c, hs1']
        simp
      rw [← hc]
      calc t * T.σ (Multiplicative.ofAdd c)
          = (t * T.σ (Multiplicative.ofAdd c) * t⁻¹) * t := by group
        _ = T.σ (Multiplicative.ofAdd c) * t := by rw [hconj]
    have htY : t ∈ S7.Obar S := T.cent t (S.Lbar_le_Mbar g ht) htcent
    exact absurd (hYL t htY ht) ht1
  ·
    obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp h1
    have hi0neg : s i0 = -1 := by
      have hmem : i0 ∈ neg := by rw [hi0]; exact Finset.mem_singleton_self i0
      simpa [neg] using (Finset.mem_filter.mp hmem).2
    have hspos : ∀ j, j ≠ i0 → s j = 1 := by
      intro j hj
      rcases hs j with h | h
      · exact h
      · exfalso
        have hjmem : j ∈ neg := by
          change j ∈ Finset.univ.filter (fun j => s j = -1)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩
        rw [hi0] at hjmem
        exact hj (by simpa using hjmem)
    have hs_eq : s = signAt i0 := by
      funext j
      by_cases hj : j = i0
      · subst hj
        rw [hi0neg, signAt, if_pos rfl]
        rfl
      · rw [hspos j hj, signAt]
        simp [hj]
    let x : S.O := t * (T.l i0)⁻¹
    have hxM : x ∈ S.Mbar :=
      S.Mbar.mul_mem (S.Lbar_le_Mbar g ht)
        (S.Mbar.inv_mem (S.Lbar_le_Mbar g (T.l_mem i0)))
    have hxcent : ∀ y ∈ S7.Obar S, x * y = y * x := by
      intro y hy
      obtain ⟨c, hc⟩ := T.basis.mem_iff.mp hy
      have hli : (T.l i0)⁻¹ * T.σ (Multiplicative.ofAdd c) * T.l i0 =
          T.σ (Multiplicative.ofAdd (negAt i0 c)) := by
        have h := T.basis.act i0 (negAt i0 c)
        rw [negAt_negAt] at h
        calc (T.l i0)⁻¹ * T.σ (Multiplicative.ofAdd c) * T.l i0
            = (T.l i0)⁻¹ * (T.l i0 * T.σ (Multiplicative.ofAdd (negAt i0 c)) *
                (T.l i0)⁻¹) * T.l i0 := by rw [h]
          _ = T.σ (Multiplicative.ofAdd (negAt i0 c)) := by group
      have hconj : x * T.σ (Multiplicative.ofAdd c) * x⁻¹ =
          T.σ (Multiplicative.ofAdd c) := by
        calc x * T.σ (Multiplicative.ofAdd c) * x⁻¹
            = t * ((T.l i0)⁻¹ * T.σ (Multiplicative.ofAdd c) * T.l i0) * t⁻¹ := by
                dsimp only [x]
                group
          _ = t * T.σ (Multiplicative.ofAdd (negAt i0 c)) * t⁻¹ := by rw [hli]
          _ = T.σ (Multiplicative.ofAdd (s * negAt i0 c)) := hact (negAt i0 c)
          _ = T.σ (Multiplicative.ofAdd c) := by
                rw [hs_eq, ← signAt_mul_eq_negAt i0 c, ← mul_assoc, signAt_mul_self,
                  one_mul]
      rw [← hc]
      calc x * T.σ (Multiplicative.ofAdd c)
          = (x * T.σ (Multiplicative.ofAdd c) * x⁻¹) * x := by group
        _ = T.σ (Multiplicative.ofAdd c) * x := by rw [hconj]
    have hxY : x ∈ S7.Obar S := T.cent x hxM hxcent
    have hxL : x ∈ S.Lbar g := (S.Lbar g).mul_mem ht ((S.Lbar g).inv_mem (T.l_mem i0))
    have hx1 : x = 1 := hYL x hxY hxL
    refine ⟨i0, ?_⟩
    exact mul_inv_eq_one.mp (by simpa [x] using hx1)

end CFSG.GF2Type.Smith1979.TriPlus

end

module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma118
public import CFSG.GH74.GLS.C3.Layer1.BackConj
public import CFSG.Assembly.GL83LieDefs
public import CFSG.GH74.GLS.TwoThin.Basic

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG
open CFSG.GH74.GLS.IVK.Proofs2.Lemma118

theorem exists_l2Field_of_hasL2Model_pred {K : Type} [Group K] {P : ℕ → Prop}
    (hP : ∀ q, P q → Odd q) (h : HasL2Model K P) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), L2Field F ∧ P (Nat.card F) ∧
      Nonempty (K ≃* L2 F) := by
  obtain ⟨p, f, hp, hf, hPq, hL⟩ := h
  rcases hL with ⟨-, hadm, F, hF, hFin, hcard, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · refine ⟨F, hF, hFin, ⟨?_, ?_⟩, ?_, ⟨e⟩⟩
    · rw [hcard]; exact hP _ hPq
    · have h1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
      have h2 : (2, p ^ f) ≠ (2, 3) := hadm.2.2.2.2
      have h3 : p ^ f ≠ 3 := fun h => h2 (by rw [h])
      have h4 : (p ^ f) % 2 = 1 := Nat.odd_iff.1 (hP _ hPq)
      rw [hcard]
      omega
    · rw [hcard]; exact hPq
  all_goals exact absurd h0 (by norm_num)


section Dihedral

theorem two_mul_val_of_two_mul_eq_zero {k : ℕ} [NeZero k] {x : ZMod k} (hx0 : x ≠ 0)
    (hx : 2 * x = 0) : 2 * x.val = k := by
  have h1 : ((2 * x.val : ℕ) : ZMod k) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hx
  have h2 : k ∣ 2 * x.val := (ZMod.natCast_eq_zero_iff _ k).1 h1
  have h3 : x.val < k := ZMod.val_lt x
  have h4 : x.val ≠ 0 := by
    intro h
    exact hx0 ((ZMod.val_eq_zero x).1 h)
  obtain ⟨m, hm⟩ := h2
  have hm1 : m = 1 := by
    have h5 : 0 < 2 * x.val := by omega
    have h6 : 2 * x.val < 2 * k := by omega
    rw [hm] at h5 h6
    have h7 : 0 < m := by
      by_contra h
      have : m = 0 := by omega
      simp [this] at h5
    have h8 : m < 2 := by
      by_contra h
      have : 2 ≤ m := by omega
      have := Nat.mul_le_mul_left k this
      omega
    omega
  rw [hm, hm1, mul_one]

theorem eq_of_two_mul_eq_zero {k : ℕ} [NeZero k] {x y : ZMod k} (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hx : 2 * x = 0) (hy : 2 * y = 0) : x = y := by
  have h1 := two_mul_val_of_two_mul_eq_zero hx0 hx
  have h2 := two_mul_val_of_two_mul_eq_zero hy0 hy
  exact ZMod.val_injective k (by omega)

theorem exists_sr_of_involution_ne_central {k : ℕ} [NeZero k] (hk : 3 ≤ k) {b v : DihedralGroup k}
    (hb2 : b * b = 1) (hb1 : b ≠ 1) (hv2 : v * v = 1) (hv1 : v ≠ 1)
    (hvc : ∀ y : DihedralGroup k, v * y = y * v) (hbv : b ≠ v) :
    ∃ j : ZMod k, b = DihedralGroup.sr j := by
  have h20 : (2 : ZMod k) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod k) = 0 := by exact_mod_cast h
    have := (ZMod.natCast_eq_zero_iff 2 k).1 this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  rcases b with i | j
  · exfalso
    rcases v with i₀ | j₀
    · have hi : i + i = 0 := by
        have := hb2
        simp only [DihedralGroup.r_mul_r, DihedralGroup.one_def, DihedralGroup.r.injEq] at this
        exact this
      have hi₀ : i₀ + i₀ = 0 := by
        have := hv2
        simp only [DihedralGroup.r_mul_r, DihedralGroup.one_def, DihedralGroup.r.injEq] at this
        exact this
      have hi0 : i ≠ 0 := by
        intro h
        apply hb1
        rw [h, DihedralGroup.one_def]
      have hi₀0 : i₀ ≠ 0 := by
        intro h
        apply hv1
        rw [h, DihedralGroup.one_def]
      have := eq_of_two_mul_eq_zero hi0 hi₀0 (by rw [two_mul]; exact hi)
        (by rw [two_mul]; exact hi₀)
      exact hbv (by rw [this])
    · have h1 := hvc (DihedralGroup.r 1)
      simp only [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr.injEq] at h1
      apply h20
      have : j₀ + 1 - (j₀ - 1) = 0 := by rw [h1]; ring
      have h3 : j₀ + 1 - (j₀ - 1) = 2 := by ring
      rw [h3] at this
      exact this
  · exact ⟨j, rfl⟩

end Dihedral


theorem ivk_10_6_L2 {K : Type} [Group K] [Finite K]
    (hK : HasL2Model K (fun q => Odd q ∧ ¬ IsFM9 q)) {B : Subgroup K}
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hB4 : Nat.card ↥B = 4) :
    ∃ V : Subgroup K, V ≤ B ∧ ∃ b ∈ B, Nat.card ↥B = 2 * Nat.card ↥V ∧
      ∃ c : K, Nat.Prime (orderOf c) ∧ Odd (orderOf c) ∧
        c ∈ pPrimeCoreOf 2 (centralizer (V : Set K)) ∧ b * c * b⁻¹ = c⁻¹ := by
  classical
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  obtain ⟨F, _, _, hF, ⟨-, hnfm⟩, ⟨e⟩⟩ :=
    exists_l2Field_of_hasL2Model_pred (fun q hq => hq.1) hK
  obtain ⟨v, hvB, hv1⟩ : ∃ v ∈ B, v ≠ 1 := by
    by_contra hno
    push Not at hno
    have : B = ⊥ := (Subgroup.eq_bot_iff_forall B).2 hno
    rw [this, Subgroup.card_bot] at hB4
    omega
  have hv2 : v * v = 1 := hBsq v hvB
  have hvo : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) hv1
  have hVcard : Nat.card ↥(zpowers v) = 2 := by rw [Nat.card_zpowers, hvo]
  obtain ⟨b, hbB, hbv⟩ : ∃ b ∈ B, b ∉ zpowers v := by
    by_contra hno
    push Not at hno
    have hle : B ≤ zpowers v := fun g hg => hno g hg
    have := Subgroup.card_le_of_le hle
    omega
  have hb2 : b * b = 1 := hBsq b hbB
  have hb1 : b ≠ 1 := fun h => hbv (h ▸ one_mem _)
  have hbvne : b ≠ v := fun h => hbv (h ▸ mem_zpowers v)
  have hbc : b * v = v * b := hBc b hbB v hvB
  set x : MulAut K := MulAut.conj v with hx
  have hxD : x ∈ innDiagSub e := innAut_le_innDiagSub e ⟨v, rfl⟩
  have hx2 : orderOf x = 2 := by rw [hx, orderOf_conj_eq e v]; exact hvo
  obtain ⟨k, m, hk, hm, hm1, hmk, ⟨φ⟩⟩ := exists_dihedral_data hF hnfm e x hxD hx2
  have hX := xu_of_dihedral x hk hm hm1 hmk φ
  have hk3 : 3 ≤ k := by
    have h3 : 3 ≤ m := by
      obtain ⟨n, hn⟩ := hm
      omega
    exact h3.trans (Nat.le_of_dvd (by omega) hmk)
  have : NeZero k := ⟨by omega⟩
  have hxu : xu x = pPrimeCoreOf 2 (centralizer ({v} : Set K)) := by
    show pPrimeCoreOf 2 (fixedSubgroup K (MulAut.conj v)) = _
    rw [fixedSubgroup_conj]
  have hXodd : Odd (Nat.card (pPrimeCore 2 ↥(fixedSubgroup K x))) :=
    Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hXcard : Nat.card ↥(xu x) = Nat.card (pPrimeCore 2 ↥(fixedSubgroup K x)) :=
    Subgroup.card_map_of_injective (fixedSubgroup K x).subtype_injective
  have hXnt : 1 < Nat.card ↥(xu x) := by
    rcases Nat.lt_or_ge 1 (Nat.card ↥(xu x)) with h | h
    · exact h
    · exfalso
      apply hX.1
      rw [← Subgroup.card_eq_one]
      have : 0 < Nat.card ↥(xu x) := Nat.card_pos
      omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show Nat.card ↥(xu x) ≠ 1 by omega)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c', hc'⟩ := exists_prime_orderOf_dvd_card' p hpd
  set c : K := (c' : K) with hcdef
  have hco : orderOf c = p := by rw [hcdef, Subgroup.orderOf_coe]; exact hc'
  have hcodd : Odd (orderOf c) := by
    rw [hco]
    have : p ∣ Nat.card (pPrimeCore 2 ↥(fixedSubgroup K x)) := hXcard ▸ hpd
    exact Odd.of_dvd_nat hXodd this
  have hcX : c ∈ pPrimeCoreOf 2 (centralizer ({v} : Set K)) := by
    rw [← hxu]; exact c'.2
  have hcC : c ∈ fixedSubgroup K x := by
    rw [hx, fixedSubgroup_conj]
    exact TwoThin.pPrimeCoreOf_le _ hcX
  have hmem : ∀ y : K, y ∈ fixedSubgroup K x ↔ y * v = v * y := fun y => by
    rw [hx, fixedSubgroup_conj, Subgroup.mem_centralizer_singleton_iff]
  have hvC : v ∈ fixedSubgroup K x := (hmem v).2 rfl
  have hbC : b ∈ fixedSubgroup K x := (hmem b).2 hbc
  set vD : ↥(fixedSubgroup K x) := ⟨v, hvC⟩ with hvD
  set bD : ↥(fixedSubgroup K x) := ⟨b, hbC⟩ with hbD
  set cD : ↥(fixedSubgroup K x) := ⟨c, hcC⟩ with hcD
  have hvDc : ∀ y : ↥(fixedSubgroup K x), vD * y = y * vD := fun y => by
    apply Subtype.ext
    have := (hmem y).1 y.2
    exact this.symm
  have hvD2 : vD * vD = 1 := Subtype.ext hv2
  have hbD2 : bD * bD = 1 := Subtype.ext hb2
  have hvD1 : vD ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
  have hbD1 : bD ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hbDv : bD ≠ vD := fun h => hbvne (congrArg Subtype.val h)
  obtain ⟨j, hj⟩ := exists_sr_of_involution_ne_central hk3
    (b := φ bD) (v := φ vD) (by rw [← map_mul, hbD2, map_one]) (fun h => hbD1 (φ.injective (by
      rw [h, map_one]))) (by rw [← map_mul, hvD2, map_one])
    (fun h => hvD1 (φ.injective (by rw [h, map_one])))
    (fun y => by
      obtain ⟨y', rfl⟩ := φ.surjective y
      rw [← map_mul, ← map_mul, hvDc]) (fun h => hbDv (φ.injective h))
  have hcD' : orderOf cD = p := by
    rw [hcD]
    rw [← Subgroup.orderOf_coe]
    exact hco
  obtain ⟨i, hi⟩ : ∃ i : ZMod k, φ cD = DihedralGroup.r i := by
    rcases hφc : φ cD with i | j'
    · exact ⟨i, rfl⟩
    · exfalso
      have h1 : orderOf (φ cD) = orderOf cD := MulEquiv.orderOf_eq φ cD
      rw [hφc, DihedralGroup.orderOf_sr, hcD'] at h1
      have h2 : Odd p := by rw [← hco]; exact hcodd
      rw [← h1] at h2
      exact absurd h2 (by decide)
  have hinv : bD * cD * bD⁻¹ = cD⁻¹ := by
    apply φ.injective
    rw [map_mul, map_mul, map_inv, map_inv, hj, hi]
    simp only [DihedralGroup.sr_mul_r, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr,
      DihedralGroup.inv_r]
    congr 1
    ring
  have hCV : centralizer ((zpowers v : Subgroup K) : Set K) = centralizer ({v} : Set K) := by
    ext y
    simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff,
      forall_eq]
    constructor
    · intro h
      exact h v (mem_zpowers v)
    · intro h g hg
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
      have hcomm : Commute v y := h
      exact (Commute.zpow_left hcomm n).eq
  refine ⟨zpowers v, ?_, b, hbB, ?_, c, ?_, hcodd, ?_, ?_⟩
  · exact zpowers_le.2 hvB
  · rw [hB4, hVcard]
  · rw [hco]; exact hp
  · rw [hCV]; exact hcX
  · have := congrArg Subtype.val hinv
    exact this

end CFSG.GH74.GLS.IVK

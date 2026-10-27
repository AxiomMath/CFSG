module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26L2Pkg
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26X
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26Expo
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocle

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.CGT.PushingUpLit.SolKNA.R4
open scoped commutatorElement

theorem s26_l2_x_mem {r : ℕ} (hr : 4 ≤ r) {X : Type} [Group X] [Finite X]
    (hO : classicalInvolutionOddCore X = ⊥)
    {Φ : Set (Subgroup X)} (hΦ : TypeRFam r Φ) {A : Subgroup X} (hA : A ∈ Φ)
    {S : Sylow 2 ↥A} {z : X} (hd : TightDatum A S z) (hz : IsUniqueInvolution A z)
    {L : Subgroup X} [L.Normal] (hzn : z ∉ Subgroup.center X)
    (hnt : ∀ y : X, ∀ m ∈ Subgroup.center X, y * z * y⁻¹ = z * m → m = 1)
    (hL2 : CFSG.ClassicalInvolution.Q3.TA3.SmallL2 ↥(socleOf L))
    (hTC : Subgroup.centralizer ((socleOf L : Subgroup (X ⧸ Subgroup.center X)) :
      Set (X ⧸ Subgroup.center X)) = ⊥)
    {u b : X} (huS : u ∈ (S : Subgroup A).map A.subtype) (hbS : b ∈ (S : Subgroup A).map A.subtype)
    (hou : orderOf u = 2 ^ (r - 1)) (hbu : b * u * b⁻¹ = u⁻¹)
    (hbb : b * b = u ^ 2 ^ (r - 2)) (hzu : u ^ 2 ^ (r - 2) = z) :
    (QuotientGroup.mk b : X ⧸ Subgroup.center X) ∉ socleOf L ∧ u ∈ L ∧
      (∀ B : MulAut ↥(socleOf L),
        B * MulAut.conjNormal (QuotientGroup.mk u : X ⧸ Subgroup.center X) =
          MulAut.conjNormal (QuotientGroup.mk u : X ⧸ Subgroup.center X) * B →
        B ^ 2 ^ (r - 1) = 1 → B ^ 2 ^ (r - 2) = 1 ∨
          B ^ 2 ^ (r - 2) = MulAut.conjNormal (QuotientGroup.mk z : X ⧸ Subgroup.center X)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hInfZ := inf_center_eq_bot_of_unique_involution hO hz hzn
  have huA : u ∈ A := Subgroup.map_subtype_le _ huS
  have hbA : b ∈ A := Subgroup.map_subtype_le _ hbS
  have hmkz : (QuotientGroup.mk z : X ⧸ Subgroup.center X) ≠ 1 := fun h =>
    hzn ((QuotientGroup.eq_one_iff z).mp h)
  have hxo : orderOf (QuotientGroup.mk u : X ⧸ Subgroup.center X) = 2 ^ (r - 1) := by
    have h1 : ¬ (QuotientGroup.mk u : X ⧸ Subgroup.center X) ^ 2 ^ (r - 2) = 1 := by
      rw [← QuotientGroup.mk_pow, hzu]
      exact hmkz
    have h2 : (QuotientGroup.mk u : X ⧸ Subgroup.center X) ^ 2 ^ (r - 2 + 1) = 1 := by
      rw [← QuotientGroup.mk_pow, show r - 2 + 1 = r - 1 by omega, ← hou, pow_orderOf_eq_one,
        QuotientGroup.mk_one]
    rw [orderOf_eq_prime_pow h1 h2, show r - 2 + 1 = r - 1 by omega]
  have hbx : (QuotientGroup.mk b : X ⧸ Subgroup.center X) * QuotientGroup.mk u *
      (QuotientGroup.mk b)⁻¹ = (QuotientGroup.mk u)⁻¹ := by
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_inv, hbu]
  have hbb' : (QuotientGroup.mk b : X ⧸ Subgroup.center X) * QuotientGroup.mk b =
      (QuotientGroup.mk u) ^ 2 ^ (r - 2) := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, hbb]
  have hz' : (QuotientGroup.mk u : X ⧸ Subgroup.center X) ^ 2 ^ (r - 2) = QuotientGroup.mk z := by
    rw [← QuotientGroup.mk_pow, hzu]
  obtain ⟨hbT, -, N, hrN, ⟨w, hwT, hwz, m, hm, hord, hzp⟩, hdich⟩ :=
    l2_package hr (socleOf L) hL2 hTC hxo hbx hbb' hz'
  obtain ⟨wt, hwtL, hwt⟩ := hwT
  have hwt' : (QuotientGroup.mk wt : X ⧸ Subgroup.center X) = w := hwt
  have hwtz : wt * z = z * wt := by
    have h1 : (QuotientGroup.mk (wt * z * wt⁻¹) : X ⧸ Subgroup.center X) = QuotientGroup.mk z := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hwt']
      calc w * QuotientGroup.mk z * w⁻¹ = (QuotientGroup.mk z * w) * w⁻¹ := by rw [hwz]
        _ = QuotientGroup.mk z := by group
    have h3 : z⁻¹ * (wt * z * wt⁻¹) ∈ Subgroup.center X := by
      rw [← QuotientGroup.eq]
      exact h1.symm
    have h4 := hnt wt (z⁻¹ * (wt * z * wt⁻¹)) h3 (by group)
    have h5 : wt * z * wt⁻¹ = z := by
      have : wt * z * wt⁻¹ = z * (z⁻¹ * (wt * z * wt⁻¹)) := by group
      rw [this, h4, mul_one]
    calc wt * z = wt * z * wt⁻¹ * wt := by group
      _ = z * wt := by rw [h5]
  have hwtA : wt ∈ Subgroup.normalizer (A : Set X) :=
    hd.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hwtz)
  have hcA : ⁅b, wt⁆ ∈ A := by
    have h1 : wt * b⁻¹ * wt⁻¹ ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp hwtA b⁻¹).mp (A.inv_mem hbA)
      simpa using this
    have h2 : ⁅b, wt⁆ = b * (wt * b⁻¹ * wt⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [h2]
    exact A.mul_mem hbA h1
  have hcL : ⁅b, wt⁆ ∈ L := by
    have h1 : b * wt * b⁻¹ ∈ L := (inferInstance : L.Normal).conj_mem wt hwtL b
    have h2 : ⁅b, wt⁆ = (b * wt * b⁻¹) * wt⁻¹ := by simp [commutatorElement_def]
    rw [h2]
    exact L.mul_mem h1 (L.inv_mem hwtL)
  have hmk : (QuotientGroup.mk (⁅b, wt⁆ ^ m) : X ⧸ Subgroup.center X) =
      (⁅(QuotientGroup.mk b : X ⧸ Subgroup.center X), w⁆) ^ m := by
    have h := map_pow (QuotientGroup.mk' (Subgroup.center X)) ⁅b, wt⁆ m
    rw [map_commutatorElement, hwt] at h
    exact h
  have hNr : N = r := by
    refine le_antisymm ?_ hrN
    have hcA' : ⁅b, wt⁆ ^ m ∈ A := Subgroup.pow_mem _ hcA m
    have hdv : 2 ^ (N - 1) ∣ orderOf (⁅b, wt⁆ ^ m) := by
      rw [← hord, ← hmk]
      exact orderOf_map_dvd (QuotientGroup.mk' (Subgroup.center X)) (⁅b, wt⁆ ^ m)
    obtain ⟨a, o, ho, hco⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (⁅b, wt⁆ ^ m)).ne'
    have hcop : Nat.Coprime (2 ^ (N - 1)) o :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ho)
    have hNa : N - 1 ≤ a := by
      rw [hco] at hdv
      have h1 : 2 ^ (N - 1) ∣ 2 ^ a := hcop.dvd_of_dvd_mul_right hdv
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
    have hc₂A : (⁅b, wt⁆ ^ m) ^ o ∈ A := Subgroup.pow_mem _ hcA' o
    have hc₂o : orderOf ((⁅b, wt⁆ ^ m) ^ o) = 2 ^ a := by
      rw [orderOf_pow_of_dvd (by have := ho.pos; omega) ⟨2 ^ a, by rw [hco]; ring⟩, hco]
      exact Nat.mul_div_cancel _ ho.pos
    have h2a : ((⁅b, wt⁆ ^ m) ^ o) ^ 2 ^ a = 1 := by
      rw [← hc₂o]
      exact pow_orderOf_eq_one _
    have hr1 := two_elt_pow_eq_one_of_mem (by omega : 3 ≤ r) hΦ hA hc₂A h2a
    have hdv2 : 2 ^ a ∣ 2 ^ (r - 1) := by
      rw [← hc₂o]
      exact orderOf_dvd_of_pow_eq_one hr1
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdv2
    omega
  refine ⟨hbT, ?_, fun B hB hB1 => hdich hNr B hB hB1⟩
  have hgen := hzp hNr
  have hxmem : (QuotientGroup.mk u : X ⧸ Subgroup.center X) ∈ Subgroup.zpowers
      ((⁅(QuotientGroup.mk b : X ⧸ Subgroup.center X), w⁆) ^ m) := by
    rw [hgen]
    exact Subgroup.mem_zpowers _
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hxmem
  have hui : u⁻¹ * (⁅b, wt⁆ ^ m) ^ i ∈ Subgroup.center X := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_zpow, hmk, hi]
  have hui1 : u⁻¹ * (⁅b, wt⁆ ^ m) ^ i = 1 :=
    hInfZ _ (A.mul_mem (A.inv_mem huA) (Subgroup.zpow_mem _ (Subgroup.pow_mem _ hcA m) i)) hui
  have hueq : u = (⁅b, wt⁆ ^ m) ^ i := inv_mul_eq_one.mp hui1
  rw [hueq]
  exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ hcL m) i

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

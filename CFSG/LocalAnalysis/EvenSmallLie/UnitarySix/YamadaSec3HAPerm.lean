module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3HASpec2
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutL1

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (dP sP autT mem_autT_iff norm_chA4 norm_chA3
  dP_centralizer_spec eq_zero_of_mem_T46 dP_pow_three)
open scoped commutatorElement Pointwise

theorem mem_normalizer_of_centralizer {X : Subgroup (Equiv.Perm (Fin 693))}
    {y : Equiv.Perm (Fin 693)} (hy : y ∈ centralizer (X : Set (Equiv.Perm (Fin 693)))) :
    y ∈ normalizer (X : Set (Equiv.Perm (Fin 693))) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← mem_centralizer_iff.1 hy h hh, mul_inv_cancel_right]
    exact hh
  · intro hh
    have e := mem_centralizer_iff.1 (inv_mem hy) _ hh
    have e2 : y * h * y⁻¹ = h := by
      have : y * h * y⁻¹ * y⁻¹ = h * y⁻¹ := by
        calc y * h * y⁻¹ * y⁻¹ = y⁻¹ * (y * h * y⁻¹) := e
          _ = h * y⁻¹ := by group
      exact mul_right_cancel this
    rwa [e2] at hh

theorem conj_mem_centralizer {X : Subgroup (Equiv.Perm (Fin 693))} {g u : Equiv.Perm (Fin 693)}
    (hg : g ∈ normalizer (X : Set (Equiv.Perm (Fin 693))))
    (hu : u ∈ centralizer (X : Set (Equiv.Perm (Fin 693)))) :
    g⁻¹ * u * g ∈ centralizer (X : Set (Equiv.Perm (Fin 693))) := by
  rw [mem_centralizer_iff]
  intro b hb
  have hb' : g * b * g⁻¹ ∈ X := (mem_normalizer_iff.1 hg b).1 hb
  have e := mem_centralizer_iff.1 hu _ hb'
  calc b * (g⁻¹ * u * g) = g⁻¹ * ((g * b * g⁻¹) * u) * g := by group
    _ = g⁻¹ * (u * (g * b * g⁻¹)) * g := by rw [e]
    _ = g⁻¹ * u * g * b := by group


theorem dPow_mem_normalizer {X : Subgroup (Equiv.Perm (Fin 693))}
    (h : dP ∈ normalizer (X : Set (Equiv.Perm (Fin 693))) ∧
      sP ∈ normalizer (X : Set (Equiv.Perm (Fin 693)))) (i j : ℕ) :
    dP ^ i * sP ^ j ∈ normalizer (X : Set (Equiv.Perm (Fin 693))) :=
  mul_mem (pow_mem h.1 i) (pow_mem h.2 j)

theorem dExp_eq_zero {l : Equiv.Perm (Fin 693)} (hl : l ∈ T46) {i : ℕ} (hi : i < 3) {n : ℕ}
    (h : (l * dP ^ i) ^ (2 ^ n) = 1) : i = 0 := by
  have hpow : ∀ m : ℕ, ∃ l' ∈ T46, (l * dP ^ i) ^ m = l' * dP ^ (i * m) := by
    intro m
    induction m with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ m ih =>
      obtain ⟨l', hl', e⟩ := ih
      have hc : dP ^ (i * m) * l * (dP ^ (i * m))⁻¹ ∈ T46 :=
        (YamadaHAut.conj_mem_T46_iff (pow_mem YamadaHAut.dP_mem_autT _)).2 hl
      refine ⟨l' * (dP ^ (i * m) * l * (dP ^ (i * m))⁻¹), mul_mem hl' hc, ?_⟩
      rw [pow_succ, e, show i * (m + 1) = i * m + i by ring, pow_add]
      group
  obtain ⟨l', hl', e⟩ := hpow (2 ^ n)
  rw [h] at e
  have hm : dP ^ (i * 2 ^ n) ∈ T46 := by
    rw [eq_inv_of_mul_eq_one_right e.symm]
    exact inv_mem hl'
  have hk : ∀ k : ℕ, dP ^ k = dP ^ (k % 3) := fun k => by
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, dP_pow_three, one_pow, one_mul]
  have hmod : dP ^ (i * 2 ^ n % 3) * sP ^ 0 ∈ T46 := by
    rw [pow_zero, mul_one, ← hk]
    exact hm
  have h0 := (eq_zero_of_mem_T46 _ (Nat.mod_lt _ (by norm_num)) 0 (by norm_num) hmod).1
  have h3 : 3 ∣ i * 2 ^ n := Nat.dvd_of_mod_eq_zero h0
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  have : 3 ∣ i := hcop.dvd_of_dvd_mul_right h3
  omega

theorem P2_dec {l : Equiv.Perm (Fin 693)} (hl : l ∈ chP2.grp) :
    ∃ x ∈ chLam.grp, ∃ s ∈ chSig.grp, ∃ a ∈ chA3.grp, l = x * s * a := by
  have hLS : chLam.grp ⊔ chSig.grp ≤ normalizer (chA3.grp : Set (Equiv.Perm (Fin 693))) :=
    sup_le xNorm_spec.2.1 xNorm_spec.2.2.1
  have hL : chLam.grp ≤ normalizer (chSig.grp : Set (Equiv.Perm (Fin 693))) := fun x hx =>
    mem_normalizer_of_centralizer (xComm_spec.2.2.2.2.1 hx)
  have h2 : l ∈ ((chLam.grp ⊔ chSig.grp : Subgroup (Equiv.Perm (Fin 693))) :
      Set (Equiv.Perm (Fin 693))) * (chA3.grp : Set (Equiv.Perm (Fin 693))) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hLS]
    exact chP2_le hl
  obtain ⟨h, hh, a, ha, rfl⟩ := Set.mem_mul.1 h2
  have h3 : h ∈ (chLam.grp : Set (Equiv.Perm (Fin 693))) * (chSig.grp : Set _) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hL]
    exact hh
  obtain ⟨x, hx, s, hs, rfl⟩ := Set.mem_mul.1 h3
  exact ⟨x, hx, s, hs, a, ha, rfl⟩

theorem K1A1_dec {l : Equiv.Perm (Fin 693)} (hl : l ∈ chK1A1.grp) :
    ∃ k ∈ chK1.grp, ∃ a ∈ chA1.grp, l = k * a := by
  rw [chK1A1_eq] at hl
  have h2 : l ∈ (chK1.grp : Set (Equiv.Perm (Fin 693))) * (chA1.grp : Set _) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ chK1_le_normalizer_A1]
    exact hl
  obtain ⟨k, hk, a, ha, rfl⟩ := Set.mem_mul.1 h2
  exact ⟨k, hk, a, ha, rfl⟩

theorem NHA4_perm {y : Equiv.Perm (Fin 693)} (hy : y ∈ autT)
    (hn : y ∈ normalizer (chA4.grp : Set (Equiv.Perm (Fin 693)))) :
    y ∈ normalizer (chA3.grp : Set (Equiv.Perm (Fin 693))) := by
  obtain ⟨l, hl, i, -, j, -, rfl⟩ := mem_autT_iff.1 hy
  have hd4 := dPow_mem_normalizer norm_chA4 i j
  have hl4 : l ∈ normalizer (chA4.grp : Set (Equiv.Perm (Fin 693))) := by
    have e : l = l * dP ^ i * sP ^ j * (dP ^ i * sP ^ j)⁻¹ := by group
    rw [e]
    exact mul_mem hn (inv_mem hd4)
  rw [mul_assoc]
  exact mul_mem (YamadaHAut.normalizer_chA4_le_normalizer_A3 hl hl4)
    (dPow_mem_normalizer norm_chA3 i j)


theorem centralizer_A4_dec : ∀ y ∈ autT,
    y ∈ centralizer (chA4.grp : Set (Equiv.Perm (Fin 693))) →
    ∃ s ∈ chSig.grp, ∃ a ∈ chA3.grp, ∃ i < 3, y = s * a * dP ^ i := by
  intro y hy hc
  obtain ⟨l, hl, i, hi, j, hj, rfl⟩ := mem_autT_iff.1 hy
  have hd4 := dPow_mem_normalizer norm_chA4 i j
  have hl4 : l ∈ normalizer (chA4.grp : Set (Equiv.Perm (Fin 693))) := by
    have e : l = l * dP ^ i * sP ^ j * (dP ^ i * sP ^ j)⁻¹ := by group
    rw [e]
    exact mul_mem (mem_normalizer_of_centralizer hc) (inv_mem hd4)
  obtain ⟨x, hx, s, hs, a, ha, rfl⟩ := P2_dec (YamadaHAut.normalizer_chA4_le hl hl4)
  have hu : s * a * dP ^ i ∈ centralizer (chA4.grp : Set (Equiv.Perm (Fin 693))) :=
    mul_mem (mul_mem (xComm_spec.2.2.2.1 hs) (xComm_spec.2.1 ha))
      (pow_mem dP_centralizer_spec.2.2.1 i)
  have hu' := conj_mem_centralizer (pow_mem norm_chA4.2 j) hu
  have hxC : x * sP ^ j ∈ centralizer (chA4.grp : Set (Equiv.Perm (Fin 693))) := by
    have e : x * sP ^ j = x * s * a * dP ^ i * sP ^ j *
        ((sP ^ j)⁻¹ * (s * a * dP ^ i) * sP ^ j)⁻¹ := by group
    rw [e]
    exact mul_mem hc (inv_mem hu')
  obtain ⟨rfl, rfl⟩ := c6_spec hx hj fun w hw =>
    (mem_centralizer_iff.1 hxC (wP w) (wP_mem_grp hw)).symm
  exact ⟨s, hs, a, ha, i, hi, by group⟩

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3

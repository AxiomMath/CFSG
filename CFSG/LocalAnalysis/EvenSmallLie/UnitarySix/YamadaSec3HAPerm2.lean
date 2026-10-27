module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3HAPerm
public import CFSG.Monster.B.TwoA.Census.PermClasses

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (dP sP autT mem_autT_iff norm_chA4 norm_chA3
  norm_chZ2S dP_centralizer_spec eq_zero_of_mem_T46 dP_pow_three letter_spec)
open scoped commutatorElement

theorem le_of_two_group {X S N : Subgroup (Equiv.Perm (Fin 693))} (hN : IsPGroup 2 N)
    (hS : IsPGroup 2 S) (hNX : N ≤ X) (hSX : S ≤ X)
    (hSN : S ≤ normalizer (N : Set (Equiv.Perm (Fin 693)))) {m r : ℕ}
    (hX : Nat.card X = 2 ^ m * r) (hr : Odd r) (hcS : Nat.card S = 2 ^ m) : N ≤ S := by
  have h2 : IsPGroup 2 (N ⊔ S : Subgroup (Equiv.Perm (Fin 693))) :=
    hN.to_sup_of_normal_left' hS hSN
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
  have hdvd : Nat.card (N ⊔ S : Subgroup (Equiv.Perm (Fin 693))) ∣ Nat.card X :=
    Subgroup.card_dvd_of_le (sup_le hNX hSX)
  rw [hk, hX] at hdvd
  have hcop : Nat.Coprime (2 ^ k) r := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hr)
  have h3 : 2 ^ k ∣ 2 ^ m := hcop.dvd_of_dvd_mul_right hdvd
  have hle : Nat.card (N ⊔ S : Subgroup (Equiv.Perm (Fin 693))) ≤ Nat.card S := by
    rw [hk, hcS]
    exact Nat.le_of_dvd (by positivity) h3
  have heq := Subgroup.eq_of_le_of_card_ge le_sup_right hle
  rw [heq]
  exact le_sup_left

theorem mem_normalizer_inf {A B : Subgroup (Equiv.Perm (Fin 693))} {g : Equiv.Perm (Fin 693)}
    (hA : g ∈ normalizer (A : Set (Equiv.Perm (Fin 693))))
    (hB : g ∈ normalizer (B : Set (Equiv.Perm (Fin 693)))) :
    g ∈ normalizer ((A ⊓ B : Subgroup (Equiv.Perm (Fin 693))) : Set (Equiv.Perm (Fin 693))) := by
  rw [mem_normalizer_iff]
  intro h
  rw [mem_inf, mem_inf, mem_normalizer_iff.1 hA h, mem_normalizer_iff.1 hB h]


theorem comm_mem_T46 {q g : Equiv.Perm (Fin 693)} (hq : q ∈ autT) (hg : g ∈ T46) :
    ⁅q, g⁆ ∈ T46 := by
  rw [commutatorElement_def]
  exact mul_mem ((YamadaHAut.conj_mem_T46_iff hq).2 hg) (inv_mem hg)

theorem comm_mem_of_normalizer {P : Subgroup (Equiv.Perm (Fin 693))} {q g : Equiv.Perm (Fin 693)}
    (hq : q ∈ P) (hg : g ∈ normalizer (P : Set (Equiv.Perm (Fin 693)))) : ⁅q, g⁆ ∈ P := by
  have h1 : g * q⁻¹ * g⁻¹ ∈ P := (mem_normalizer_iff.1 hg _).1 (inv_mem hq)
  have e : ⁅q, g⁆ = q * (g * q⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact mul_mem hq h1

theorem oTwo_NA4_perm {P : Subgroup (Equiv.Perm (Fin 693))} (hPa : P ≤ autT)
    (hPN : P ≤ normalizer (chA4.grp : Set (Equiv.Perm (Fin 693)))) (h2 : IsPGroup 2 P)
    (hnorm : chP2.grp ≤ normalizer (P : Set (Equiv.Perm (Fin 693)))) : P ≤ chA3.grp := by
  have hN2 : IsPGroup 2 (P ⊓ T46 : Subgroup (Equiv.Perm (Fin 693))) := h2.to_le inf_le_left
  have hNP2 : P ⊓ T46 ≤ chP2.grp := fun x hx => YamadaHAut.normalizer_chA4_le hx.2 (hPN hx.1)
  have hP2T : chP2.grp ≤ T46 := grp_le_T46 gensOK_chP2
  have hP2N : chP2.grp ≤ normalizer ((P ⊓ T46 : Subgroup (Equiv.Perm (Fin 693))) :
      Set (Equiv.Perm (Fin 693))) := fun g hg =>
    mem_normalizer_inf (hnorm hg) (le_normalizer (hP2T hg))
  have hSP2 : chS.grp ≤ chP2.grp := grp_le_of_subset (by decide)
  have hS2 : IsPGroup 2 chS.grp := IsPGroup.of_card (n := 15) (by rw [card_chS]; norm_num)
  have hNS := le_of_two_group hN2 hS2 hNP2 hSP2 (hSP2.trans hP2N) (m := 15) (r := 45)
    (by rw [card_chP2]; norm_num) (by decide) (by rw [card_chS]; norm_num)
  have hg : wP [15, 17] ∈ chP2.grp := wP_mem_of_letters [15, 17] (by decide)
  have hNA3 : P ⊓ T46 ≤ chA3.grp := fun n hn => by
    have h1 := (mem_normalizer_iff.1 (hP2N (inv_mem hg)) n).1 hn
    rw [inv_inv] at h1
    exact i8_spec (hNS hn) (hNS h1)
  intro q hq
  obtain ⟨l, hl, i, hi, j, hj, rfl⟩ := mem_autT_iff.1 (hPa hq)
  have hd4 := dPow_mem_normalizer norm_chA4 i j
  have hd3 := dPow_mem_normalizer norm_chA3 i j
  have hl4 : l ∈ normalizer (chA4.grp : Set (Equiv.Perm (Fin 693))) := by
    have e : l = l * dP ^ i * sP ^ j * (dP ^ i * sP ^ j)⁻¹ := by group
    rw [e]
    exact mul_mem (hPN hq) (inv_mem hd4)
  obtain ⟨x, hx, s, hs, a, ha, rfl⟩ := P2_dec (YamadaHAut.normalizer_chA4_le hl hl4)
  set q := x * s * a * dP ^ i * sP ^ j with hqdef
  have hq3 : q ∈ normalizer (chA3.grp : Set (Equiv.Perm (Fin 693))) :=
    NHA4_perm (hPa hq) (hPN hq)
  have hcomm : ∀ g ∈ chP2.grp, ⁅q, g⁆ ∈ chA3.grp := fun g hg =>
    hNA3 ⟨comm_mem_of_normalizer hq (hnorm hg), comm_mem_T46 (hPa hq) (hP2T hg)⟩
  have ha' : (dP ^ i * sP ^ j)⁻¹ * a * (dP ^ i * sP ^ j) ∈ chA3.grp := by
    have := (mem_normalizer_iff.1 (inv_mem hd3) a).1 ha
    rwa [inv_inv] at this
  have hyN : x * s * (dP ^ i * sP ^ j) ∈ normalizer (chA3.grp : Set (Equiv.Perm (Fin 693))) :=
    mul_mem (mul_mem (xNorm_spec.2.1 hx) (xNorm_spec.2.2.1 hs)) hd3
  have hy : ∀ g ∈ chP2.grp, ⁅x * s * (dP ^ i * sP ^ j), g⁆ ∈ chA3.grp := by
    intro g hg
    set a' := (dP ^ i * sP ^ j)⁻¹ * a * (dP ^ i * sP ^ j)
    have hc : a' * (g * a'⁻¹ * g⁻¹) ∈ chA3.grp :=
      mul_mem ha' ((mem_normalizer_iff.1 (chP2_le_normalizer hg) _).1 (inv_mem ha'))
    have e : ⁅x * s * (dP ^ i * sP ^ j), g⁆ = (x * s * (dP ^ i * sP ^ j) *
        (a' * (g * a'⁻¹ * g⁻¹)) * (x * s * (dP ^ i * sP ^ j))⁻¹)⁻¹ * ⁅q, g⁆ := by
      simp only [hqdef, a', commutatorElement_def]
      group
    rw [e]
    exact mul_mem (inv_mem ((mem_normalizer_iff.1 hyN _).1 hc)) (hcomm g hg)
  obtain ⟨rfl, rfl, rfl⟩ := c7_spec hx hs hi hj
    (fun w hw => hy _ (wP_mem_grp (c := chP2) (by revert w; decide)))
    (fun w hw => hy _ (wP_mem_grp (c := chP2) (by revert w; decide)))
  obtain ⟨n, hn⟩ := h2 ⟨q, hq⟩
  have h1 : q ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hn' : (a * dP ^ i) ^ 2 ^ n = 1 := by
    rw [hqdef] at h1
    simpa using h1
  have hi0 := dExp_eq_zero (grp_le_T46 gensOK_chA3 ha) hi hn'
  subst hi0
  rw [hqdef]
  simpa using ha

theorem oTwo_CA4_perm {P : Subgroup (Equiv.Perm (Fin 693))} (hPa : P ≤ autT)
    (hPC : P ≤ centralizer (chA4.grp : Set (Equiv.Perm (Fin 693)))) (h2 : IsPGroup 2 P)
    (hnorm : chSigA3.grp ≤ normalizer (P : Set (Equiv.Perm (Fin 693)))) : P ≤ chA3.grp := by
  have hN2 : IsPGroup 2 (P ⊓ T46 : Subgroup (Equiv.Perm (Fin 693))) := h2.to_le inf_le_left
  have hNX : P ⊓ T46 ≤ chSigA3.grp := fun y hy => by
    obtain ⟨s', hs', a', ha', i', hi', rfl⟩ := centralizer_A4_dec y (hPa hy.1) (hPC hy.1)
    have hsa : s' * a' ∈ T46 := mul_mem (grp_le_T46 gensOK_chSig hs') (grp_le_T46 gensOK_chA3 ha')
    have hd : dP ^ i' * sP ^ 0 ∈ T46 := by
      have e : dP ^ i' * sP ^ 0 = (s' * a')⁻¹ * (s' * a' * dP ^ i') := by group
      rw [e]
      exact mul_mem (inv_mem hsa) hy.2
    obtain ⟨rfl, -⟩ := eq_zero_of_mem_T46 i' hi' 0 (by norm_num) hd
    rw [pow_zero, mul_one, chSigA3_eq]
    exact mul_mem (mem_sup_left hs') (mem_sup_right ha')
  have hXT : chSigA3.grp ≤ T46 := grp_le_T46 gensOK_chSigA3
  have hXN : chSigA3.grp ≤ normalizer ((P ⊓ T46 : Subgroup (Equiv.Perm (Fin 693))) :
      Set (Equiv.Perm (Fin 693))) := fun g hg =>
    mem_normalizer_inf (hnorm hg) (le_normalizer (hXT hg))
  have hSX : chX3A3.grp ≤ chSigA3.grp := grp_le_of_subset (by decide)
  have hS2 : IsPGroup 2 chX3A3.grp := IsPGroup.of_card (n := 13) (by rw [card_chX3A3]; norm_num)
  have hNS := le_of_two_group hN2 hS2 hNX hSX (hSX.trans hXN) (m := 13) (r := 3)
    (by rw [card_chSigA3]; norm_num) (by decide) (by rw [card_chX3A3]; norm_num)
  have hpe : wP [4, 17] ∈ chSigA3.grp := wP_mem_of_letters [4, 17] (by decide)
  intro q hq
  obtain ⟨s, hs, a, ha, i, hi, rfl⟩ := centralizer_A4_dec q (hPa hq) (hPC hq)
  have hsa : s * a ∈ T46 := mul_mem (grp_le_T46 gensOK_chSig hs) (grp_le_T46 gensOK_chA3 ha)
  obtain ⟨n, hn⟩ := h2 ⟨_, hq⟩
  have hn' : (s * a * dP ^ i) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  obtain rfl := dExp_eq_zero hsa hi hn'
  have hmem : s * a * dP ^ 0 ∈ P ⊓ T46 := ⟨hq, by rw [pow_zero, mul_one]; exact hsa⟩
  have h1 := (mem_normalizer_iff.1 (hXN (inv_mem hpe)) _).1 hmem
  rw [inv_inv] at h1
  exact i8b_spec (hNS hmem) (hNS h1)

theorem NZ2S_perm {y : Equiv.Perm (Fin 693)} (hy : y ∈ autT)
    (hn : y ∈ normalizer (chZ2S.grp : Set (Equiv.Perm (Fin 693)))) :
    y ∈ normalizer (chA4.grp : Set (Equiv.Perm (Fin 693))) := by
  have hz : gP 14 ∈ chZ2S.grp := by
    rw [← wP_single]
    exact wP_mem_grp (by decide)
  have hyz : y * gP 14 * y⁻¹ = gP 14 :=
    c11a_spec ((mem_normalizer_iff.1 hn _).1 hz) (fixCard_conj _ _)
  obtain ⟨l, hl, i, hi, j, hj, rfl⟩ := mem_autT_iff.1 hy
  have c1 : Commute dP (gP 14) := letter_spec.1 14 (by decide)
  have c2 : Commute sP (gP 14) := letter_spec.2.1 14 (by decide)
  have hdz : Commute (dP ^ i * sP ^ j) (gP 14) := (c1.pow_left i).mul_left (c2.pow_left j)
  have hlz : l * gP 14 * l⁻¹ = gP 14 := by
    calc l * gP 14 * l⁻¹ = l * ((dP ^ i * sP ^ j) * gP 14 * (dP ^ i * sP ^ j)⁻¹) * l⁻¹ := by
          rw [hdz.eq, mul_inv_cancel_right]
      _ = l * dP ^ i * sP ^ j * gP 14 * (l * dP ^ i * sP ^ j)⁻¹ := by group
      _ = gP 14 := hyz
  obtain ⟨k, hk, a, ha, rfl⟩ := K1A1_dec (centralizer_gP14_le hl
    (by rw [← mul_inv_eq_iff_eq_mul, hlz]))
  have hkN : k ∈ normalizer (chZ2S.grp : Set (Equiv.Perm (Fin 693))) := by
    have e : k = k * a * dP ^ i * sP ^ j * (dP ^ i * sP ^ j)⁻¹ * a⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hn (inv_mem (dPow_mem_normalizer norm_chZ2S i j)))
      (inv_mem (nm_spec.1 ha))
  exact mul_mem (mul_mem (mul_mem (YamadaHAut.chP2_le_normalizer_A4 (c11b_spec hk hkN))
    (nm_spec.2.1 ha)) (pow_mem norm_chA4.1 i)) (pow_mem norm_chA4.2 j)

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3

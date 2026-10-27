module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26X

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3
open scoped Pointwise

section SylowL

variable {X : Type} [Group X] [Finite X]

theorem central_orderOf_two_pow (hO : classicalInvolutionOddCore X = ⊥) {c : X}
    (hc : c ∈ Subgroup.center X) : ∃ a : ℕ, orderOf c = 2 ^ a := by
  obtain ⟨a, q, hq, hcq⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hpow : orderOf (c ^ 2 ^ a) = q := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) ⟨q, hcq⟩, hcq,
      Nat.mul_div_cancel_left q (pow_pos two_pos a)]
  have hone : c ^ 2 ^ a = 1 :=
    central_odd_eq_one hO (Subgroup.pow_mem _ hc _) (by rw [hpow]; exact hq)
  have hq1 : q = 1 := by
    rw [← hpow, hone, orderOf_one]
  exact ⟨a, by rw [hcq, hq1, mul_one]⟩

theorem odd_part_mem (hO : classicalInvolutionOddCore X = ⊥) {L : Subgroup X} [L.Normal]
    {k : X} {m : ℕ} (hm : Odd m) (hkm : k ^ m = 1) (hk : k ∈ L ⊔ Subgroup.center X) :
    k ∈ L := by
  obtain ⟨l, hl, c, hc, hlc⟩ := Subgroup.mem_sup_of_normal_right.mp hk
  have hcomm : Commute l c := Subgroup.mem_center_iff.mp hc l
  have hcm : c ^ m = (l ^ m)⁻¹ := by
    have h1 : (l * c) ^ m = 1 := by rw [hlc]; exact hkm
    rw [hcomm.mul_pow] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hcmL : c ^ m ∈ L := by
    rw [hcm]; exact L.inv_mem (L.pow_mem hl m)
  obtain ⟨a, ha⟩ := central_orderOf_two_pow hO hc
  have hcop : IsCoprime (orderOf c : ℤ) (m : ℤ) := by
    rw [Nat.isCoprime_iff_coprime, ha]
    exact Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  obtain ⟨u, v, huv⟩ := hcop
  have hA : c ^ (u * (orderOf c : ℤ)) = 1 :=
    orderOf_dvd_iff_zpow_eq_one.mp (dvd_mul_left _ _)
  have hB : c ^ (v * (m : ℤ)) = (c ^ m) ^ v := by
    rw [zpow_mul', zpow_natCast]
  have hcv : c = (c ^ m) ^ v := by
    have h1 : c ^ (u * (orderOf c : ℤ) + v * (m : ℤ)) = c := by rw [huv, zpow_one]
    rw [zpow_add, hA, hB, one_mul] at h1
    exact h1.symm
  have hcL : c ∈ L := by
    rw [hcv]; exact zpow_mem hcmL v
  rw [← hlc]
  exact mul_mem hl hcL

theorem two_part_mem {L : Subgroup X} [L.Normal]
    {R : Subgroup X} {S : Sylow 2 ↥R} {u b : X}
    (huL : u ∈ L) (hbn : b ∉ L ⊔ Subgroup.center X)
    (hcos : ∀ s ∈ (S : Subgroup R).map R.subtype,
      s ∈ Subgroup.zpowers u ∨ b⁻¹ * s ∈ Subgroup.zpowers u)
    {k : X} (hkR : k ∈ R) (hkL : k ∈ L ⊔ Subgroup.center X) {a : ℕ} (hka : k ^ 2 ^ a = 1) :
    k ∈ L := by
  obtain ⟨k', hk'⟩ : ∃ k' : ↥R, (k' : X) = k := ⟨⟨k, hkR⟩, rfl⟩
  have hk'pow : k' ^ 2 ^ a = 1 := Subtype.ext (by simpa [hk'] using hka)
  have hfin : IsPGroup 2 (Subgroup.zpowers k') :=
    IsPGroup.of_card_dvd_pow (n := a) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hk'pow)
  obtain ⟨Q, hQ⟩ := hfin.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥R) S Q
  have hmem : k' ∈ (g • S : Sylow 2 ↥R) := by
    rw [hg]; exact hQ (Subgroup.mem_zpowers k')
  have hmem1 : k' ∈ MulAut.conj g • (S : Subgroup R) := by
    rw [← Sylow.coe_subgroup_smul]; exact hmem
  have hmem2 : (MulAut.conj g)⁻¹ • k' ∈ (S : Subgroup R) :=
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hmem1
  have hconj : (MulAut.conj g)⁻¹ • k' = g⁻¹ * k' * g := MulAut.conj_inv_apply g k'
  rw [hconj] at hmem2
  obtain ⟨s, hs_def⟩ : ∃ s : X, s = (g : X)⁻¹ * k * (g : X) := ⟨_, rfl⟩
  have hs : s ∈ (S : Subgroup R).map R.subtype := by
    rw [hs_def, ← hk']
    exact Subgroup.mem_map_of_mem R.subtype hmem2
  have hsLZ : s ∈ L ⊔ Subgroup.center X := by
    have hN : (L ⊔ Subgroup.center X).Normal := inferInstance
    have h3 := hN.conj_mem k hkL (g : X)⁻¹
    rw [hs_def]
    rwa [inv_inv] at h3
  have hk_eq : k = (g : X) * s * (g : X)⁻¹ := by
    rw [hs_def]; group
  rcases hcos s hs with h1 | h2
  · have hsL : s ∈ L := (Subgroup.zpowers_le.mpr huL) h1
    rw [hk_eq]
    exact Subgroup.Normal.conj_mem inferInstance _ hsL _
  · exfalso
    have hbL : b⁻¹ * s ∈ L := (Subgroup.zpowers_le.mpr huL) h2
    apply hbn
    have h3 := mul_mem hsLZ (inv_mem (Subgroup.mem_sup_left hbL))
    have h4 : s * (b⁻¹ * s)⁻¹ = b := by group
    rwa [h4] at h3

end SylowL

theorem mem_of_mem_sup_center {X : Type} [Group X] [Finite X]
    (hO : CFSG.Open.classicalInvolutionOddCore X = ⊥) {L : Subgroup X} [L.Normal]
    {R : Subgroup X} {S : Sylow 2 ↥R} {u b : X}
    (huS : u ∈ (S : Subgroup R).map R.subtype) (hbS : b ∈ (S : Subgroup R).map R.subtype)
    (huL : u ∈ L) (hbn : b ∉ L ⊔ Subgroup.center X)
    (hcos : ∀ s ∈ (S : Subgroup R).map R.subtype,
      s ∈ Subgroup.zpowers u ∨ b⁻¹ * s ∈ Subgroup.zpowers u) :
    ∀ k ∈ R, k ∈ L ⊔ Subgroup.center X → k ∈ L := by
  intro k hkR hkLZ
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  obtain ⟨x, y, hxy⟩ : IsCoprime ((2 ^ a : ℕ) : ℤ) (m : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm))
  have hsplit : k ^ (y * (m : ℤ)) * k ^ (x * ((2 ^ a : ℕ) : ℤ)) = k := by
    rw [← zpow_add, add_comm, hxy, zpow_one]
  have hk₀m : (k ^ (x * ((2 ^ a : ℕ) : ℤ))) ^ m = 1 := by
    have h1 : (k ^ (x * ((2 ^ a : ℕ) : ℤ))) ^ (m : ℤ) = 1 := by
      rw [← zpow_mul]
      apply orderOf_dvd_iff_zpow_eq_one.mp
      exact ⟨x, by rw [hn]; push_cast; ring⟩
    rwa [zpow_natCast] at h1
  have hk₂sq : (k ^ (y * (m : ℤ))) ^ 2 ^ a = 1 := by
    have h1 : (k ^ (y * (m : ℤ))) ^ ((2 ^ a : ℕ) : ℤ) = 1 := by
      rw [← zpow_mul]
      apply orderOf_dvd_iff_zpow_eq_one.mp
      exact ⟨y, by rw [hn]; push_cast; ring⟩
    rwa [zpow_natCast] at h1
  have hk₀L : k ^ (x * ((2 ^ a : ℕ) : ℤ)) ∈ L :=
    odd_part_mem hO hm hk₀m (zpow_mem hkLZ _)
  have hk₂L : k ^ (y * (m : ℤ)) ∈ L :=
    two_part_mem huL hbn hcos (zpow_mem hkR _) (zpow_mem hkLZ _) hk₂sq
  have h := mul_mem hk₂L hk₀L
  rwa [hsplit] at h

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

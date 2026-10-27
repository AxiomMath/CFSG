module

public import CFSG.GH74.Generic.S3.Lem26
public import CFSG.GH74.Generic.S45.LTransfer

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup

theorem eq_one_of_odd_center_of_two_power {L : Type*} [Group L] (hodd : Odd (Nat.card (center L)))
    {u : L} (hu : u ∈ center L) {k : ℕ} (hk : orderOf u = 2 ^ k) : u = 1 := by
  have h1 : orderOf u ∣ Nat.card (center L) := Subgroup.orderOf_dvd_natCard (center L) hu
  rw [hk] at h1
  by_cases hk0 : k = 0
  · rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    exact hk
  · exfalso
    obtain ⟨m, hm⟩ := (dvd_pow_self 2 hk0).trans h1
    obtain ⟨j, hj⟩ := hodd
    omega

theorem b_S3_Z_P_of_sylow (hsyl : B_L3_sylow) : B_S3_Z_P := by
  intro G _ _ hG t p f v w Iv Iw Ivw P hconf z hzP hzc hzz
  have hIw : IsNormCompC Iw w := hconf.comp_w
  have hIwC : Iw ≤ centralizer ({w} : Set G) := hIw.1.1
  have hq : IsQuasisimple ↥Iw := hIw.1.isQuasisimple
  have hR : IsSylowOf 2 (P ⊓ Iw) Iw :=
    hconf.sylow_w.inf_of_le_normalizer hIwC hIw.le_normalizer
  obtain ⟨hcyc, -, -, hksplit⟩ := hsyl G t p f hconf.tag hconf.prime.1 hconf.prime.2.1
    hconf.prime.2.2 Iw hq hconf.odd_w hconf.model_w _ hR
  have hzN : z ∈ normalizer (Iw : Set G) := hIw.le_normalizer (hconf.sylow_w.le hzP)
  have hAN : Subgroup.zpowers z ≤ normalizer (Iw : Set G) := Subgroup.zpowers_le.mpr hzN
  have hAcent : ∀ a ∈ Subgroup.zpowers z, ∀ r ∈ P ⊓ Iw, a * r = r * a := by
    intro a ha r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hcomm : Commute z r := (hzc r hr.1).symm
    exact (hcomm.zpow_left k).eq
  obtain ⟨z', hz'R, hz'c⟩ := hksplit (Subgroup.zpowers z) hAN (isPGroup_zpowers_of_involution hzz)
    hAcent z (Subgroup.mem_zpowers z)
  have hz'P : z' ∈ P := hz'R.1.1
  have hz'I : z' ∈ Iw := hz'R.1.2
  set c : G := z * z'⁻¹ with hc
  have hcP : c ∈ P := P.mul_mem hzP (P.inv_mem hz'P)
  have hzc' : z = c * z' := by rw [hc]; group
  have hcz' : z' * c = c * z' := mem_centralizer_iff.mp hz'c z' hz'I
  have h1 : c * c * (z' * z') = 1 := by
    have hcomm : Commute z' c := hcz'
    have := hcomm.mul_mul_mul_comm c z'
    rw [← this, ← hzc']
    exact hzz
  have hzz' : z' * z' = 1 := by
    have hu : z' * z' = (c * c)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hmem : (⟨z' * z', Iw.mul_mem hz'I hz'I⟩ : ↥Iw) ∈ center ↥Iw := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hcc : (c * c) ∈ centralizer (Iw : Set G) :=
        (centralizer (Iw : Set G)).mul_mem hz'c hz'c
      have : ((c * c)⁻¹) ∈ centralizer (Iw : Set G) := (centralizer (Iw : Set G)).inv_mem hcc
      rw [← hu] at this
      exact mem_centralizer_iff.mp this g g.2
    have hRz : z' * z' ∈ P ⊓ Iw := (P ⊓ Iw).mul_mem hz'R.1 hz'R.1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR.isPGroup) ⟨z' * z', hRz⟩
    have hk' : orderOf (⟨z' * z', Iw.mul_mem hz'I hz'I⟩ : ↥Iw) = 2 ^ k := by
      rw [← hk, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe (⟨z' * z', hRz⟩ : ↥(P ⊓ Iw))]
    have := eq_one_of_odd_center_of_two_power hconf.odd_w hmem hk'
    exact congrArg Subtype.val this
  have hcc : c * c = 1 := by
    rwa [hzz', mul_one] at h1
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hconf.w_inv, pow_two] at this
  have hw1 : w ≠ 1 := fun h => by
    have := hconf.w_inv
    rw [h, orderOf_one] at this
    omega
  have hcQ : c ∈ P ⊓ centralizer (Iw : Set G) := ⟨hcP, hz'c⟩
  have hwQ : w ∈ P ⊓ centralizer (Iw : Set G) :=
    ⟨hconf.w_P, mem_centralizer_iff.mpr fun i hi =>
      mem_centralizer_singleton_iff.1 (hIwC hi)⟩
  have hcw : c = 1 ∨ c = w := by
    by_cases hc1 : c = 1
    · exact Or.inl hc1
    · exact Or.inr (eq_of_involutions_of_cyclic hconf.Q_cyc hcQ hwQ hc1 hw1 hcc hww)
  have hv2 : v * v = 1 := by
    have := pow_orderOf_eq_one v
    rwa [hconf.v_inv, pow_two] at this
  have hv1 : v ≠ 1 := fun h => by
    have := hconf.v_inv
    rw [h, orderOf_one] at this
    omega
  have hvZ : v ∈ (P ⊓ Iw) ⊓ centralizer ((P ⊓ Iw : Subgroup G) : Set G) :=
    ⟨⟨hconf.v_P, hconf.le_w hconf.v_mem⟩, mem_centralizer_iff.mpr fun r hr =>
      hconf.v_central r hr.1⟩
  have hz'v : z' = 1 ∨ z' = v := by
    by_cases hz'1 : z' = 1
    · exact Or.inl hz'1
    · exact Or.inr (eq_of_involutions_of_cyclic hcyc hz'R hvZ hz'1 hv1 hzz' hv2)
  rw [hzc']
  rcases hcw with h1 | h1 <;> rcases hz'v with h2 | h2
  · left; rw [h1, h2, mul_one]
  · right; right; left; rw [h1, h2, one_mul]
  · right; left; rw [h1, h2, mul_one]
  · right; right; right; rw [h1, h2, hconf.comm]

theorem b_S3_lemma26_transfer_of_sylow (hsyl : B_L3_sylow) : B_S3_lemma26_transfer :=
  b_S3_lemma26_transfer_of_zP S45.b_III8_6_3 (b_S3_Z_P_of_sylow hsyl)

end CFSG.GH74.Generic.S3

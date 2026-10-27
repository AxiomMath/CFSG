module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreA0TypeOne
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreA0TypeTwoBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreA0TypeTwoTransfer

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}
  {N : Subgroup J} {M : ℕ}

namespace A0Config

section Involutions

variable (φ : a0Kernel Q B N ≃* QuaternionGroup M) [NeZero M] (hc : A0Config Q B z u N)

include hc in
theorem eq_of_mul_self_mem (m : ℕ) (hm : 2 ≤ m) (hM : M = 2 ^ m)
    (hII : ∃ k ∈ a0Kernel Q B N, z * k * z⁻¹ ≠ u * k * u⁻¹)
    {b : J} (hb : b ∈ a0Kernel Q B N) (hba : ¬ ∃ k : ℕ, b = kerGen φ ^ k) (hbz : z * b = b * z)
    {r : J} (hrQ : r ∈ (Q : Subgroup J)) (hrb : r * b = b * r) (hru : r * u = u * r)
    (hrr : r * r = 1 ∨ r * r = centralElt J) :
    r = 1 ∨ r = centralElt J ∨ r = z ∨ r = centralElt J * z := by
  have h := hc.setting
  have hz := hc.fourGen
  have h3 : 3 ≤ M := by
    rw [hM]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hza := hc.conj_kerGen_eq φ h3 hII
  obtain ⟨i, hi⟩ := hc.exists_conj_kerGen_eq_pow φ h3 hrQ
  have hrrc : r * r ∈ Subgroup.center J := by
    rcases hrr with h1 | h1 <;> rw [h1]
    · exact (Subgroup.center J).one_mem
    · exact h.centralElt_mem_center
  have hii : kerGen φ ^ (i * i) = kerGen φ := by
    calc kerGen φ ^ (i * i) = (r * kerGen φ * r⁻¹) ^ i := by rw [hi, ← pow_mul]
      _ = r * (r * kerGen φ * r⁻¹) * r⁻¹ := by rw [conj_pow, hi]
      _ = (r * r) * kerGen φ * (r * r)⁻¹ := by group
      _ = kerGen φ := by
          rw [← Subgroup.mem_center_iff.mp hrrc (kerGen φ), mul_inv_cancel_right]
  obtain ⟨j₀, hj₀⟩ := hc.exists_self_eq_pow φ h3
  have hui : u ^ i = u := by
    have h1 : r * u * r⁻¹ = u := by rw [hru, mul_inv_cancel_right]
    rw [hj₀] at h1 ⊢
    rw [← conj_pow, hi, ← pow_mul, mul_comm, pow_mul] at h1
    exact h1
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hi
      have h2 : kerGen φ = 1 := by
        calc kerGen φ = r⁻¹ * (r * kerGen φ * r⁻¹) * r := by group
          _ = 1 := by rw [hi]; group
      have h4 := orderOf_kerGen φ
      rw [h2, orderOf_one] at h4
      omega
    · exact h0
  have h4u : 4 ∣ i - 1 := by
    rw [← h.orderOf_eq_four hc.sq]
    apply orderOf_dvd_of_pow_eq_one
    rw [← mul_left_cancel_iff (a := u), ← pow_succ', Nat.sub_add_cancel hi1, hui, mul_one]
  have h2M : 2 * 2 ^ m ∣ i * i - 1 := by
    rw [← hM, ← orderOf_kerGen φ]
    apply orderOf_dvd_of_pow_eq_one
    rw [← mul_left_cancel_iff (a := kerGen φ), ← pow_succ', Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))), hii, mul_one]
  obtain ⟨q, hq⟩ := dvd_sub_one_of_sq hm hi1 h2M h4u
  have hra : r * kerGen φ * r⁻¹ = kerGen φ ∨ r * kerGen φ * r⁻¹ = centralElt J * kerGen φ := by
    rw [hi, show i = 1 + (i - 1) by omega, pow_add, pow_one, hq, ← hM, pow_mul,
      hc.kerGen_pow φ]
    rcases Nat.even_or_odd q with ⟨l, rfl⟩ | ⟨l, rfl⟩
    · left
      rw [← two_mul, pow_mul, pow_two, h.centralElt_mul_self, one_pow, mul_one]
    · right
      rw [pow_succ, pow_mul, pow_two, h.centralElt_mul_self, one_pow, one_mul,
        ← (h.commute_centralElt _).eq]
  rcases hra with h1 | h1
  · have hrc : r * kerGen φ = kerGen φ * r := by
      calc r * kerGen φ = r * kerGen φ * r⁻¹ * r := by group
        _ = kerGen φ * r := by rw [h1]
    rcases hc.eq_of_centralizes φ h3 hII hrQ (hc.centralizes_of_comm φ h3 hb hba hrc hrb) with
      h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
  · have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz.mul_self
    have hzrc : z * r * kerGen φ = kerGen φ * (z * r) := by
      have h2 : z * r * kerGen φ * (z * r)⁻¹ = kerGen φ := by
        calc z * r * kerGen φ * (z * r)⁻¹ = z * (r * kerGen φ * r⁻¹) * z⁻¹ := by group
          _ = centralElt J * (z * kerGen φ * z⁻¹) := by rw [h1, h.mul_central_left]; group
          _ = kerGen φ := by rw [hza, ← mul_assoc, h.centralElt_mul_self, one_mul]
      calc z * r * kerGen φ = z * r * kerGen φ * (z * r)⁻¹ * (z * r) := by group
        _ = kerGen φ * (z * r) := by rw [h2]
    have hzrb : z * r * b = b * (z * r) := by
      rw [mul_assoc, hrb, ← mul_assoc, hbz, mul_assoc]
    rcases hc.eq_of_centralizes φ h3 hII ((Q : Subgroup J).mul_mem hz.mem hrQ)
        (hc.centralizes_of_comm φ h3 hb hba hzrc hzrb) with h2 | h2
    · right; right; left
      calc r = z⁻¹ * (z * r) := by group
        _ = z := by rw [h2, mul_one, hzinv]
    · right; right; right
      calc r = z⁻¹ * (z * r) := by group
        _ = centralElt J * z := by rw [h2, hzinv, ← (h.commute_centralElt z).eq]

end Involutions

theorem false_of_typeTwo (hc : A0Config Q B z u N) (h16 : 16 ≤ Nat.card (a0Kernel Q B N))
    (hII : ∃ k ∈ a0Kernel Q B N, z * k * z⁻¹ ≠ u * k * u⁻¹) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hc.setting
  have hz := hc.fourGen
  obtain ⟨n, hn, hcard, ⟨φ⟩⟩ := hc.a0Kernel_quaternion
  have hn4 : 4 ≤ n := by
    by_contra hlt
    push Not at hlt
    have h8 : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set M := 2 ^ (n - 2) with hMdef
  have hm2 : 2 ≤ n - 2 := by omega
  have : NeZero M := ⟨by positivity⟩
  have h3 : 3 ≤ M := by
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) hm2
  have hza := hc.conj_kerGen_eq φ h3 hII
  obtain ⟨t, htQ, ht, htV⟩ := hz.exists_involution_not_mem_fourGroup h
  have hztK := hc.mul_mem_a0Kernel htQ ht htV
  set b := kerGen φ * (z * t) with hbdef
  have hbK : b ∈ a0Kernel Q B N := (a0Kernel Q B N).mul_mem (kerGen_mem φ) hztK
  have hbu : b * u * b⁻¹ = centralElt J * u := by
    have h1 := hc.conj_self_eq_of_mul htQ ht htV
    have h2 : kerGen φ * u * (kerGen φ)⁻¹ = u := by
      have := hc.pow_comm_self φ h3 1
      rw [pow_one] at this
      rw [this, mul_inv_cancel_right]
    calc b * u * b⁻¹ = kerGen φ * (z * t * u * (z * t)⁻¹) * (kerGen φ)⁻¹ := by rw [hbdef]; group
      _ = centralElt J * u := by rw [h1, h.mul_central_left, mul_assoc, h2]
  have hba : ¬ ∃ k : ℕ, b = kerGen φ ^ k := hc.not_pow_of_conj_self φ h3 hbu
  have hbz : z * b = b * z := by
    have h1 : z * b * z⁻¹ = b := by
      calc z * b * z⁻¹ = (z * kerGen φ * z⁻¹) * (z * (z * t) * z⁻¹) := by rw [hbdef]; group
        _ = b := by rw [hza, hc.conj_mul_eq_central_mul htQ ht htV, h.central_mul_central]
    calc z * b = z * b * z⁻¹ * z := by group
      _ = b * z := by rw [h1]
  set R₂ : Subgroup J := (Q : Subgroup J) ⊓ Subgroup.centralizer {b} ⊓
    Subgroup.centralizer {u} with hR₂
  have hmemR₂ : ∀ r : J, r ∈ R₂ ↔ r ∈ (Q : Subgroup J) ∧ r * b = b * r ∧ r * u = u * r := by
    intro r
    simp only [hR₂, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
  set π := QuotientGroup.mk' (Subgroup.center J) with hπ
  set R := R₂.map π with hR
  have hR2 : IsPGroup 2 R := (Q.isPGroup'.to_le (inf_le_left.trans inf_le_left)).map π
  have hzR₂ : z ∈ R₂ := (hmemR₂ z).mpr ⟨hz.mem, hbz, hc.comm.symm⟩
  have hzR : π z ∈ R := Subgroup.mem_map_of_mem π hzR₂
  have hπz : π z ≠ 1 := hz.mk_ne_one
  have hRcomm : ∀ x y : R, x * y = y * x := by
    rintro ⟨_, r, hr, rfl⟩ ⟨_, r', hr', rfl⟩
    obtain ⟨hrQ, hrb, -⟩ := (hmemR₂ r).mp hr
    obtain ⟨hr'Q, hr'b, -⟩ := (hmemR₂ r').mp hr'
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul]
    have h1 := hc.comm_mod φ h3 hII hbK hba hr'Q hrQ hr'b hrb
    have h2 : r'⁻¹ * r⁻¹ * r' * r ∈ Subgroup.center J := by
      rcases h1 with h1 | h1 <;> rw [h1]
      · exact (Subgroup.center J).one_mem
      · exact h.centralElt_mem_center
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [show (r * r')⁻¹ * (r' * r) = r'⁻¹ * r⁻¹ * r' * r by group]
    exact h2
  have hRinv : ∀ x ∈ R, orderOf x = 2 → x = π z := by
    rintro _ ⟨r, hr, rfl⟩ hord
    obtain ⟨hrQ, hrb, hru⟩ := (hmemR₂ r).mp hr
    have hrr : r * r ∈ Subgroup.center J := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
      change π r * π r = 1
      rw [← pow_two, ← hord, pow_orderOf_eq_one]
    rcases hc.eq_of_mul_self_mem φ (n - 2) hm2 rfl hII hbK hba hbz hrQ hrb hru
        (h.mem_center_iff.mp hrr) with h1 | h1 | h1 | h1
    · exfalso
      rw [h1, map_one, orderOf_one] at hord
      exact absurd hord (by decide)
    · exfalso
      rw [h1, hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr
        h.centralElt_mem_center, orderOf_one] at hord
      exact absurd hord (by decide)
    · rw [h1]
    · rw [h1, map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff _).mpr h.centralElt_mem_center, one_mul]
  have hRcyc : IsCyclic R := by
    rcases CFSG.TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion R hR2
        (twoRank_le_one_of_unique hRinv) with hcyc | ⟨k, hk, ⟨ψ⟩⟩
    · exact hcyc
    · exfalso
      have : NeZero (2 ^ (k - 2)) := ⟨by positivity⟩
      have h1 := hRcomm (ψ.symm (QuaternionGroup.xa 0)) (ψ.symm (QuaternionGroup.a 1))
      have h2 := congrArg ψ h1
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
        QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa, QuaternionGroup.xa.injEq] at h2
      have h3 : ((2 : ℕ) : ZMod (2 * 2 ^ (k - 2))) = 0 := by
        push_cast
        linear_combination h2
      rw [ZMod.natCast_eq_zero_iff] at h3
      have h4 := Nat.le_of_dvd (by norm_num) h3
      have h5 : 2 ≤ 2 ^ (k - 2) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (k - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  obtain ⟨g, hg⟩ := hRcyc.exists_generator
  obtain ⟨s, hsR₂, hsg⟩ := Subgroup.mem_map.mp g.2
  obtain ⟨hsQ, hsb, hsu⟩ := (hmemR₂ s).mp hsR₂
  obtain ⟨f, hf⟩ := (IsPGroup.iff_orderOf.mp hR2) g
  have hgz : (⟨π z, hzR⟩ : R) ∈ Subgroup.zpowers g := hg _
  have hf1 : 1 ≤ f := by
    by_contra hf0
    have hf0' : f = 0 := by omega
    rw [hf0', pow_zero, orderOf_eq_one_iff] at hf
    rw [hf, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hgz
    exact hπz (congrArg Subtype.val hgz)
  have hsz : s ^ 2 ^ (f - 1) = z ∨ s ^ 2 ^ (f - 1) = centralElt J * z := by
    have hord : orderOf (g ^ 2 ^ (f - 1)) = 2 := by
      rw [orderOf_pow' _ (pow_ne_zero _ two_ne_zero), hf, Nat.gcd_eq_right
        (pow_dvd_pow 2 (Nat.sub_le f 1)), Nat.pow_div (Nat.sub_le f 1) (by norm_num),
        Nat.sub_sub_self hf1, pow_one]
    have h1 := hRinv _ (g ^ 2 ^ (f - 1)).2 (by rw [Subgroup.orderOf_coe]; exact hord)
    rw [Subgroup.coe_pow, ← hsg, ← map_pow, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    rcases h.mem_center_iff.mp h1 with h2 | h2
    · left
      exact inv_mul_eq_one.mp h2
    · right
      have h3 : s ^ 2 ^ (f - 1) = z * (centralElt J)⁻¹ := by rw [← h2]; group
      rw [h3, inv_eq_of_mul_eq_one_right h.centralElt_mul_self, (h.commute_centralElt z).eq]
  have hdec : ∀ x ∈ (Q : Subgroup J), ∃ k ∈ a0Kernel Q B N, ∃ j : ℤ, x = k * s ^ j := by
    intro x hx
    obtain ⟨k, hk, hkb, hku⟩ := hc.exists_mul_comm φ h3 hbK hba hbz hza hx
    have hkx : k * x ∈ R₂ := (hmemR₂ _).mpr ⟨(Q : Subgroup J).mul_mem (hk.1) hx, hkb, hku⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨π (k * x), Subgroup.mem_map_of_mem π hkx⟩)
    have hj' : π (s ^ j) = π (k * x) := by
      have := congrArg Subtype.val hj
      rw [Subgroup.coe_zpow] at this
      rw [map_zpow, hsg]
      exact this
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hj'
    refine ⟨k⁻¹ * (s ^ j * ((s ^ j)⁻¹ * (k * x)) * (s ^ j)⁻¹), (a0Kernel Q B N).mul_mem
      ((a0Kernel Q B N).inv_mem hk) ?_, j, by group⟩
    rw [Setting.conj_eq_of_mem_center hj']
    rcases h.mem_center_iff.mp hj' with h1 | h1 <;> rw [h1]
    · exact (a0Kernel Q B N).one_mem
    · exact hc.centralElt_mem_a0Kernel
  have hpowK : ∀ j : ℤ, s ^ j ∈ a0Kernel Q B N → (2 ^ f : ℤ) ∣ j := by
    intro j hj
    have hsjb : s ^ j * b = b * s ^ j := ((Commute.zpow_left (show Commute s b from hsb) j)).eq
    have hsju : s ^ j * u = u * s ^ j := ((Commute.zpow_left (show Commute s u from hsu) j)).eq
    have h1 := hc.eq_of_mem_of_comm φ h3 hbK hba hj hsjb hsju
    have h2 : g ^ j = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow, ← hsg, ← map_zpow, Subgroup.coe_one]
      rcases h1 with h1 | h1 <;> rw [h1]
      · exact map_one π
      · rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact h.centralElt_mem_center
    have h3' := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rw [hf] at h3'
    exact_mod_cast h3'
  exact hc.false_of_cyclic_quotient hf1 hsQ hsz hdec hpowK

theorem false_of_a0Config
    (hc : A0Config Q B z u N) (IH : CanonicalBelow (Nat.card J)) :
    False :=
  (hc.typeOne_or_typeTwo).elim (hc.false_of_typeOne IH) fun ⟨h16, hII⟩ =>
    hc.false_of_typeTwo h16 hII

end A0Config

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

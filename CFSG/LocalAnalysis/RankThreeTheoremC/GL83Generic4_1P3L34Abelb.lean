module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34abel_mem_zpowers_three {H : Type*} [Group H] {y c : H} (hy : y ^ 3 = 1)
    (hc : c ∈ zpowers y) : c = 1 ∨ c = y ∨ c = y⁻¹ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
  have hy' : y ^ (3 : ℤ) = 1 := by exact_mod_cast hy
  have hk : y ^ k = y ^ (k % 3) := by
    obtain ⟨q, hq⟩ : ∃ q : ℤ, k = 3 * q + k % 3 := ⟨k / 3, by omega⟩
    conv_lhs => rw [hq]
    rw [zpow_add, zpow_mul, hy', one_zpow, one_mul]
  rw [hk]
  have h0 := Int.emod_nonneg k (by norm_num : (3 : ℤ) ≠ 0)
  have h3 := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 3)
  obtain h | h | h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  · left
    rw [h, zpow_zero]
  · right; left
    rw [h, zpow_one]
  · right; right
    rw [h, eq_inv_iff_mul_eq_one, ← hy']
    group

theorem l34abel_conj_eq {H : Type*} [Group H] {g y : H} {n : ℕ} (hg : g ^ 3 ^ n = 1)
    (hy : y ^ 3 = 1) (h : g * y * g⁻¹ ∈ zpowers y) : g * y * g⁻¹ = y := by
  rcases l34abel_mem_zpowers_three hy h with h1 | h1 | h1
  · have hy1 : y = 1 := by
      have e : y = g⁻¹ * (g * y * g⁻¹) * g := by group
      rw [e, h1]
      group
    rw [hy1]
    group
  · exact h1
  · have e1 : g * y⁻¹ * g⁻¹ = y := by
      have e : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
      rw [e, h1, inv_inv]
    have h2 : Commute (g ^ 2) y := by
      calc g ^ 2 * y = g * (g * y * g⁻¹) * g⁻¹ * g ^ 2 := by simp [pow_two, mul_assoc]
        _ = y * g ^ 2 := by rw [h1, e1]
    obtain ⟨m, hm⟩ : Odd (3 ^ n) := Odd.pow (by decide)
    have hg2 : g = (g ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = 3 ^ n + 1 by omega, pow_succ, hg, one_mul]
    have hc : g * y = y * g := by
      rw [hg2]
      exact (h2.pow_left (m + 1)).eq
    calc g * y * g⁻¹ = y * g * g⁻¹ := by rw [hc]
      _ = y := by group

theorem l34abel_mem_of_pow {P : Sylow 3 G} {J : Subgroup G} {x : G} (hR1 : L34Prop34 3 P J x)
    {U F : Subgroup G} (hU : IsElemAbelian 3 U) (hUc : Nat.card U = 3 ^ 2) (hUF : U ≤ F)
    (hF : IsPGroup 3 F) (hrk : CFSG.Open.pRank 3 F ≤ 2) {f : G} (hf : f ∈ F) (hf3 : f ^ 3 = 1) :
    f ∈ U := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hEel, -, hΩ, -⟩ := hR1
  set E : Subgroup G := ((P : Subgroup G) ⊓ J) ⊔ zpowers x with hE
  obtain ⟨Q, hFQ⟩ := hF.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  set E' : Subgroup G := E.map (MulAut.conj g).toMonoidHom with hE'
  have hQE : ∀ q ∈ (Q : Subgroup G), q ^ 3 = 1 → q ∈ E' := by
    intro q hq hq3
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hq
    obtain ⟨p, hp, hpq⟩ := hq
    have hpq' : (MulAut.conj g) p = q := hpq
    have hp3 : p ^ 3 = 1 := by
      have h1 : (MulAut.conj g) (p ^ 3) = 1 := by rw [map_pow, hpq', hq3]
      exact (MulEquiv.map_eq_one_iff _).mp h1
    exact ⟨p, hΩ p hp hp3, hpq'⟩
  have hE'ab : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := hEel.1
    have hab : a * b = b * a :=
      congrArg Subtype.val ((IsMulCommutative.is_comm (M := E)).comm ⟨a, ha⟩ ⟨b, hb⟩)
    rw [← map_mul, ← map_mul, hab]
  have hE'3 : ∀ a ∈ E', a ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hEel.2 a ha, map_one]
  have hAel : IsElemAbelian 3 (F ⊓ E') :=
    ⟨⟨⟨fun a b => Subtype.ext (hE'ab a a.2.2 b b.2.2)⟩⟩, fun a ha => hE'3 a ha.2⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hF.to_le inf_le_left : IsPGroup 3 (F ⊓ E' : Subgroup G))
  have hkle : k ≤ CFSG.Open.pRank 3 F := le_pRank_of_elemAbelian_card inf_le_left hAel hk
  have hUA : U ≤ F ⊓ E' := fun u hu => ⟨hUF hu, hQE u (hFQ (hUF hu)) (hU.2 u hu)⟩
  have hAU : U = F ⊓ E' := Subgroup.eq_of_le_of_card_ge hUA (by
    rw [hk, hUc]
    exact Nat.pow_le_pow_right (by norm_num) (hkle.trans hrk))
  have hfA : f ∈ F ⊓ E' := ⟨hf, hQE f (hFQ hf) hf3⟩
  rw [← hAU] at hfA
  exact hfA

theorem l34abel_le_normalizer {U F : Subgroup G} (hU : IsElemAbelian 3 U) (hUF : U ≤ F)
    (hmem : ∀ f ∈ F, f ^ 3 = 1 → f ∈ U) : F ≤ normalizer (U : Set G) := by
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun u hu => hmem _ ?_ ?_
  · exact F.mul_mem (F.mul_mem hg (hUF hu)) (F.inv_mem hg)
  · rw [conj_pow, hU.2 u hu, mul_one, mul_inv_cancel]

omit [Finite G] in
theorem l34abel_le_centralizer {P : Sylow 3 G} {x : G} {U F : Subgroup G}
    (hwc : LineWeaklyClosed x (P : Subgroup G)) (hx3 : x ^ 3 = 1) (hxU : x ∈ U)
    (hUP : U ≤ (P : Subgroup G)) (hFU : F ≤ normalizer (U : Set G)) (hF : IsPGroup 3 F) :
    F ≤ centralizer ({x} : Set G) := by
  intro g hg
  have hle : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) := by
    rintro _ ⟨z, hz, rfl⟩
    exact hUP ((mem_normalizer_iff.mp (hFU hg) z).mp (zpowers_le.mpr hxU hz))
  have hmem : g * x * g⁻¹ ∈ zpowers x := by
    rw [← hwc g hle]
    exact ⟨x, mem_zpowers x, rfl⟩
  obtain ⟨n, hn⟩ := hF ⟨g, hg⟩
  have hgn : g ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h := l34abel_conj_eq hgn hx3 hmem
  rw [mem_centralizer_singleton_iff]
  calc g * x = g * x * g⁻¹ * g := by group
    _ = x * g := by rw [h]

theorem l34abel_inf_comm {x : G} {J U F : Subgroup G}
    (hCJ : centralizer ({x} : Set G) ≤ normalizer (J : Set G)) (hU : IsElemAbelian 3 U)
    (hUc : Nat.card U = 3 ^ 2) (hxU : x ∈ U) (hxJ : x ∉ J) (hFC : F ≤ centralizer ({x} : Set G))
    (hFU : F ≤ normalizer (U : Set G)) (hF : IsPGroup 3 F) {u : G} (hu : u ∈ U ⊓ J) {g : G}
    (hg : g ∈ F) : g * u * g⁻¹ = u := by
  by_cases hu1 : u = 1
  · rw [hu1]
    group
  have hu3 : u ^ 3 = 1 := hU.2 u hu.1
  have hou : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hcard : Nat.card (U ⊓ J : Subgroup G) = 3 := by
    have h1 : Nat.card (U ⊓ J : Subgroup G) ∣ 3 ^ 2 := hUc ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (zpowers u) ∣ Nat.card (U ⊓ J : Subgroup G) :=
      Subgroup.card_dvd_of_le (zpowers_le.mpr hu)
    rw [Nat.card_zpowers, hou] at h2
    have h3 : Nat.card (U ⊓ J : Subgroup G) ≠ 3 ^ 2 := by
      intro h
      have hUJ : U ⊓ J = U := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hUc])
      have hx : x ∈ U ⊓ J := by rw [hUJ]; exact hxU
      exact hxJ hx.2
    obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
    interval_cases i
    · rw [hie] at h2
      norm_num at h2
    · rw [hie]
      norm_num
    · exact absurd hie h3
  have hUJ : zpowers u = U ⊓ J :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hu) (by rw [hcard, Nat.card_zpowers, hou])
  have hmem : g * u * g⁻¹ ∈ zpowers u := by
    rw [hUJ]
    exact ⟨(mem_normalizer_iff.mp (hFU hg) u).mp hu.1,
      (mem_normalizer_iff.mp (hCJ (hFC hg)) u).mp hu.2⟩
  obtain ⟨n, hn⟩ := hF ⟨g, hg⟩
  exact l34abel_conj_eq (by simpa using congrArg Subtype.val hn) hu3 hmem

end CFSG.LocalAnalysis.RankThreeTheoremC

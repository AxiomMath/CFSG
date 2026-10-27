module

import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec87c
import CFSG.Goldschmidt.Steps.Sec89a
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG

public section

namespace CFSG.Goldschmidt.Sec89

open CFSG.Open
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem exists_sq_eq_one_not_mem (hset : GoldSetting G S A) (h4 : Nat.card A = 4) :
    ∃ t ∈ (S : Subgroup G), t ^ 2 = 1 ∧ t ∉ A := by
  obtain ⟨E, hES, hE, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two (S : Subgroup G)
  have h8 : 8 ≤ Nat.card E := by
    rw [hcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 (S : Subgroup G) :=
        Nat.pow_le_pow_right (by norm_num) (Sec8.three_le_pRank hset)
  by_contra h
  push Not at h
  have hEA : E ≤ A := fun t ht => h t (hES ht) (hE.2 t ht)
  have := Subgroup.card_le_of_le hEA
  omega

theorem comm_of_mem (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {s : G}
    (hs : s ∈ (S : Subgroup G)) {a : G} (ha : a ∈ A) : a * s = s * a :=
  Subgroup.mem_centralizer_iff.mp (Sec8.le_centralizer hset h4 hs) a ha

theorem sq_eq_one_of_sup_eq (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {t : G}
    {B : Subgroup G} (hB : B ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G))
    (hAB : A ⊓ B = ⊥) (hsup : A ⊔ B = (S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G))
    {z : G} (hz : z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G)) (hz2 : z ^ 2 ∈ A) :
    z ^ 2 = 1 := by
  have hle : A ≤ Subgroup.normalizer (B : Set G) := fun a ha =>
    mem_normalizer_of_forall_comm fun b hb => (comm_of_mem hset h4 (hB hb).1 ha).symm
  have hz' : z ∈ (A : Set G) * (B : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A B hle, hsup]
    exact hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hz'
  have hab := comm_of_mem hset h4 (hB hb).1 ha
  have ha2 : a ^ 2 = 1 := hset.elem.2 a ha
  have hsq : (a * b) ^ 2 = b ^ 2 := by
    calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
      _ = a ^ 2 * b ^ 2 := by rw [← hab]; simp only [pow_two]; group
      _ = b ^ 2 := by rw [ha2, one_mul]
  rw [hsq] at hz2 ⊢
  have hmem : b ^ 2 ∈ A ⊓ B := ⟨hz2, B.pow_mem hb 2⟩
  rwa [hAB, Subgroup.mem_bot] at hmem

theorem center_le (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    (hL : ∀ t ∈ (S : Subgroup G), t ^ 2 = 1 → t ∉ A → ∀ z ∈ (S : Subgroup G), z * t = t * z →
      z ^ 2 ∈ A → z ^ 2 = 1)
    (hΩZ : A = Omega1 ((S : Subgroup G) ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G))) :
    (S : Subgroup G) ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) ≤ A := by
  obtain ⟨t, htS, ht2, htA⟩ := exists_sq_eq_one_not_mem hset h4
  set Z := (S : Subgroup G) ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) with hZ
  have key := mem_of_forall_sq (A := A) (Z := (Z : Set G)) (fun z hz => Z.pow_mem hz 2)
    (fun z hz hz2 => by rw [hΩZ]; exact Subgroup.subset_closure ⟨hz, hz2⟩)
    (fun z hz hz2 => hL t htS ht2 htA z hz.1
      ((Subgroup.mem_centralizer_iff.mp hz.2 t htS).symm) hz2)
  intro z hz
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨z, hz.1⟩
  exact key k z hz (by simpa using congrArg Subtype.val hk)

theorem mul_mem_of_commute (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    (hrank : CFSG.Open.pRank 2 (S : Subgroup G) ≤ 3) {u v : G} (hu : u ∈ (S : Subgroup G))
    (hv : v ∈ (S : Subgroup G)) (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1) (huv : u * v = v * u)
    (huA : u ∉ A) (hvA : v ∉ A) : u * v ∈ A := by
  by_contra h
  have huc : ∀ a ∈ A, a * u = u * a := fun a ha => comm_of_mem hset h4 hu ha
  obtain ⟨hE1, hc1⟩ := isElemAbelian_sup_zpowers hset.elem huA hu2 huc
  have hvE1 : v ∉ A ⊔ Subgroup.zpowers u := fun hvE => by
    rcases mem_or_mul_mem_of_mem_sup hu2 huc hvE with hvA' | ⟨a, ha, rfl⟩
    · exact hvA hvA'
    · apply h
      have e : u * (a * u) = a := by
        calc u * (a * u) = (u * a) * u := by group
          _ = (a * u) * u := by rw [← huc a ha]
          _ = a := by rw [mul_assoc, ← pow_two, hu2, mul_one]
      rw [e]
      exact ha
  have hvc : ∀ e ∈ A ⊔ Subgroup.zpowers u, e * v = v * e := fun e he => by
    rcases mem_or_mul_mem_of_mem_sup hu2 huc he with heA | ⟨a, ha, rfl⟩
    · exact comm_of_mem hset h4 hv heA
    · rw [mul_assoc, huv, ← mul_assoc, comm_of_mem hset h4 hv ha, mul_assoc]
  obtain ⟨hE2, hc2⟩ := isElemAbelian_sup_zpowers hE1 hvE1 hv2 hvc
  have hle : A ⊔ Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ (S : Subgroup G) :=
    sup_le (sup_le hset.le (Subgroup.zpowers_le.mpr hu)) (Subgroup.zpowers_le.mpr hv)
  obtain ⟨k, hk⟩ := (S.isPGroup'.to_le hle).exists_card_eq
  have hk4 := CFSG.SectionRank.le_pRank one_lt_two hle hE2 hk
  have h16 : 16 ≤ 2 ^ k := by rw [← hk]; omega
  have : 2 ^ 4 ≤ 2 ^ k := by simpa using h16
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp this
  omega

theorem eq_one_of_conj_eq (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {x : G}
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) (hxC : x ∉ Subgroup.centralizer (A : Set G))
    {c : G} (hc : c ∈ A) (hxc : x⁻¹ * c * x = c) : c = 1 := by
  by_contra hc1
  refine hxC ?_
  have h := Sec8.mem_centralizer_of_conj_eq hset h4 (Subgroup.inv_mem _ hxA) hc hc1
    (by rw [inv_inv]; exact hxc)
  simpa using Subgroup.inv_mem _ h

theorem exists_mem_normalizer_pow (hset : GoldSetting G S A) (h4 : Nat.card A = 4) :
    ∃ x ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
      x ∉ Subgroup.centralizer (A : Set G) ∧ ∃ b : ℕ, orderOf x = 3 ^ b := by
  obtain ⟨a, ha, ha1⟩ := Sec8.exists_mem_ne_one hset
  obtain ⟨x₀, hx₀S, -, hx₀a⟩ := Sec8.exists_mem_normalizer_sylow hset h4 ha ha1
  have hx₀A := Sec8.normalizer_le_normalizer hset hx₀S
  have hx₀C : x₀ ∉ Subgroup.centralizer (A : Set G) := fun h => hx₀a (by
    have := Sec8.conj_eq_of_mem_centralizer (Subgroup.inv_mem _ h) ha
    simpa using this)
  obtain ⟨b, m, hm3, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x₀).ne' 3
    (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (orderOf_pos x₀).ne' (by rw [hm, mul_zero])
  refine ⟨x₀ ^ m, Subgroup.pow_mem _ hx₀S m, fun hC => hx₀C ?_, b, ?_⟩
  · have h3 := Sec8.pow_three_mem_centralizer hset h4 hx₀A
    have hcop : IsCoprime (m : ℤ) ((3 : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_comm.mp
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3)))
    obtain ⟨u, v, huv⟩ := hcop
    have e : x₀ = (x₀ ^ m) ^ u * (x₀ ^ 3) ^ v := by
      rw [← zpow_natCast, ← zpow_natCast x₀ 3, ← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm,
        mul_comm _ v, huv, zpow_one]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hC u) (Subgroup.zpow_mem _ h3 v)
  · rw [orderOf_pow_of_dvd hm0 (by rw [hm]; exact Dvd.intro_left _ rfl), hm,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]

omit [Finite G] in
theorem conj_sq_eq_one {x y : G} (hy : y ^ 2 = 1) : (x⁻¹ * y * x) ^ 2 = 1 := by
  rw [pow_two] at hy ⊢
  calc x⁻¹ * y * x * (x⁻¹ * y * x) = x⁻¹ * (y * y) * x := by group
    _ = 1 := by rw [hy]; group

theorem false_of_mul_conj_mem (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    (hrank : CFSG.Open.pRank 2 (S : Subgroup G) ≤ 3) {x : G}
    (hxS : x ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) {t : G} (ht : t ∈ (S : Subgroup G))
    (ht2 : t ^ 2 = 1) (htA : t ∉ A)
    (hm : t * (x⁻¹ * t * x) * (x⁻¹ * (x⁻¹ * t * x) * x) ∈ A) : False := by
  obtain ⟨u, hu⟩ : ∃ u, x⁻¹ * t * x = u := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, x⁻¹ * u * x = v := ⟨_, rfl⟩
  rw [hu, hv] at hm
  have huS : u ∈ (S : Subgroup G) := hu ▸ conj_mem_of_mem_normalizer hxS ht
  have hvS : v ∈ (S : Subgroup G) := hv ▸ conj_mem_of_mem_normalizer hxS huS
  have hu2 : u ^ 2 = 1 := hu ▸ conj_sq_eq_one ht2
  have hv2 : v ^ 2 = 1 := hv ▸ conj_sq_eq_one hu2
  have ht1 : t * t = 1 := by rw [← pow_two]; exact ht2
  have hu1 : u * u = 1 := by rw [← pow_two]; exact hu2
  have hv1 : v * v = 1 := by rw [← pow_two]; exact hv2
  have huA : u ∉ A := fun h => htA (by
    have := conj_mem_of_mem_normalizer (Subgroup.inv_mem _ hxA) h
    rw [← hu] at this
    simpa [mul_assoc] using this)
  have hav : t * u * v * v = v * (t * u * v) := comm_of_mem hset h4 hvS hm
  have hcomm : t * u = u * t := by
    have htu : t * u = t * u * v * v := by rw [mul_assoc (t * u) v v, hv1, mul_one]
    have h1 : t * u * (t * u) = 1 := by
      calc t * u * (t * u) = t * u * v * v * (t * u * v * v) := by rw [← htu]
        _ = (t * u * v) * (v * (t * u * v)) * v := by group
        _ = (t * u * v) * (t * u * v * v) * v := by rw [hav]
        _ = (t * u * v) ^ 2 * (v * v) := by rw [pow_two]; group
        _ = 1 := by rw [hset.elem.2 _ hm, hv1, one_mul]
    calc t * u = (t * u)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = u * t := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hu1, inv_eq_of_mul_eq_one_right ht1]
  have htuA : t * u ∉ A := fun h => htA (by
    have hc' : x⁻¹ * (t * u) * x ∈ A := conj_mem_of_mem_normalizer hxA h
    have e1 : x⁻¹ * (t * u) * x = u * v := by
      calc x⁻¹ * (t * u) * x = (x⁻¹ * t * x) * (x⁻¹ * u * x) := by group
        _ = u * v := by rw [hu, hv]
    have e2 : v = u * (x⁻¹ * (t * u) * x) := by
      rw [e1, ← mul_assoc, hu1, one_mul]
    have e3 : t = t * u * v * (x⁻¹ * (t * u) * x)⁻¹ := by
      calc t = t * (u * u) * (x⁻¹ * (t * u) * x) * (x⁻¹ * (t * u) * x)⁻¹ := by
            rw [hu1]; group
        _ = t * u * v * (x⁻¹ * (t * u) * x)⁻¹ := by
            rw [e2]; group
    rw [e3]
    exact A.mul_mem hm (A.inv_mem hc'))
  exact htuA (mul_mem_of_commute hset h4 hrank ht huS ht2 hu2 hcomm htA huA)

end CFSG.Goldschmidt.Sec89

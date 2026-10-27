module

import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec85a
import CFSG.Goldschmidt.Steps.Sec87c
import CFSG.Goldschmidt.Steps.Sec89a
import CFSG.Goldschmidt.Steps.Sec89c
import CFSG.Goldschmidt.Steps.Sec89f
import CFSG.GroupTheory.SuzukiTwoGroups
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG

public section

namespace CFSG.Goldschmidt.Sec89

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem sq_eq_one_of_central (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    {T₁ : Subgroup G} (hT₁S : T₁ ≤ (S : Subgroup G)) (hAT₁ : A ≤ T₁)
    (hinv : ∀ t ∈ T₁, t ^ 2 = 1 → t ∈ A) {x : G} (hxA : x ∈ Subgroup.normalizer (A : Set G))
    (hxC : x ∉ Subgroup.centralizer (A : Set G)) (hxT : x ∈ Subgroup.normalizer (T₁ : Set G))
    (hnab : ¬ IsMulCommutative T₁) {z : G} (hz : z ∈ T₁) (hzc : ∀ w ∈ T₁, w * z = z * w) :
    z ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha, ha1⟩ := Sec8.exists_mem_ne_one hset
  set φ : MulAut T₁ := T₁.normalizerMonoidHom ⟨x, hxT⟩ with hφ
  have hφapp : ∀ y : T₁, ((φ y : T₁) : G) = x * y * x⁻¹ := fun y => rfl
  have hinv' : ∀ y : T₁, orderOf y = 2 → (y : G) ∈ A ∧ (y : G) ≠ 1 := fun y hy => by
    have h2 : (y : G) ^ 2 = 1 := by
      have := pow_orderOf_eq_one y
      rw [hy] at this
      simpa using congrArg Subtype.val this
    refine ⟨hinv y y.2 h2, fun h1 => ?_⟩
    have : y = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hy
    exact absurd hy (by norm_num)
  have htrans : ∀ y y' : T₁, orderOf y = 2 → orderOf y' = 2 →
      ∃ β ∈ Subgroup.zpowers φ, β y = y' := by
    intro y y' hy hy'
    obtain ⟨hyA, hy1⟩ := hinv' y hy
    obtain ⟨hy'A, hy'1⟩ := hinv' y' hy'
    obtain ⟨hne, hsq⟩ := Sec8.conj_conj_eq_mul hset h4 hxA hxC hyA hy1
    rcases Sec8.mem_four hset.elem h4 hyA (Sec8.conj_mem hxA hyA) hy'A hy1 (Sec8.conj_ne_one hy1)
      (Ne.symm hne) with h | h | h | h
    · exact absurd h hy'1
    · exact ⟨1, Subgroup.one_mem _, Subtype.ext (by rw [h]; rfl)⟩
    · exact ⟨φ, Subgroup.mem_zpowers φ, Subtype.ext (by rw [hφapp, h])⟩
    · refine ⟨φ * φ, Subgroup.mul_mem _ (Subgroup.mem_zpowers φ) (Subgroup.mem_zpowers φ),
        Subtype.ext ?_⟩
      rw [MulAut.mul_apply, hφapp, hφapp, h, hsq]
  have hab : (⟨a, hAT₁ ha⟩ : T₁) ≠ ⟨x * a * x⁻¹, hAT₁ (Sec8.conj_mem hxA ha)⟩ := fun h =>
    (Sec8.conj_conj_eq_mul hset h4 hxA hxC ha ha1).1 (congrArg Subtype.val h).symm
  have hord : ∀ c ∈ A, c ≠ 1 → ∀ hc : c ∈ T₁, orderOf (⟨c, hc⟩ : T₁) = 2 :=
    fun c hc hc1 _ => by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (hset.elem.2 c hc) hc1
  have hsuz : CFSG.GroupTheory.IsSuzukiTwoGroup T₁ :=
    ⟨inferInstance, S.isPGroup'.to_le hT₁S, hnab,
      ⟨⟨a, hAT₁ ha⟩, ⟨x * a * x⁻¹, hAT₁ (Sec8.conj_mem hxA ha)⟩, hord a ha ha1 _,
        hord _ (Sec8.conj_mem hxA ha) (Sec8.conj_ne_one ha1) _, hab⟩,
      Subgroup.zpowers φ, inferInstance, htrans⟩
  obtain ⟨-, -, -, hZel, -⟩ := hsuz.higman
  have hzZ : (⟨z, hz⟩ : T₁) ∈ Subgroup.center T₁ :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hzc g g.2)
  have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Subgroup.center T₁) _ hzZ
  simpa using congrArg Subtype.val this

theorem exists_T1_abelian (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    (hL : ∀ t ∈ (S : Subgroup G), t ^ 2 = 1 → t ∉ A → ∀ z ∈ (S : Subgroup G), z * t = t * z →
      z ^ 2 ∈ A → z ^ 2 = 1)
    (hDc : IsMulCommutative (⁅(S : Subgroup G), (S : Subgroup G)⁆ : Subgroup G))
    (hΩD : A = Omega1 ⁅(S : Subgroup G), (S : Subgroup G)⁆)
    (hD : ¬ ⁅(S : Subgroup G), (S : Subgroup G)⁆ ≤ A) {x : G}
    (hxS : x ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hxC : x ∉ Subgroup.centralizer (A : Set G)) {b : ℕ} (hb : orderOf x = 3 ^ b) :
    ∃ T₁ : Subgroup G, T₁ ≤ (S : Subgroup G) ∧ A ≤ T₁ ∧
      (S : Subgroup G) ≤ Subgroup.normalizer (T₁ : Set G) ∧
      x ∈ Subgroup.normalizer (T₁ : Set G) ∧ (∀ s ∈ (S : Subgroup G), s ^ 2 ∈ T₁) ∧
      (∀ s ∈ (S : Subgroup G), (∀ w ∈ T₁, w * s = s * w) → s ∈ T₁) ∧
      (∀ t ∈ T₁, t ^ 2 = 1 → t ∈ A) ∧ (∀ c ∈ T₁, x⁻¹ * c * x = c → c = 1) ∧
      ∀ s ∈ (S : Subgroup G), x⁻¹ * (x⁻¹ * (x⁻¹ * s * x) * x) * x = s := by
  have hxA := Sec8.normalizer_le_normalizer hset hxS
  obtain ⟨T₁, hT₁S, hAT₁, hST₁, hxT₁, hsq, hself, y₀, hy₀T, hy₀c, hy₀A, hy₀1⟩ :=
    exists_T1 hset h4 hDc hΩD hD hxS hxA
  have hinv : ∀ t ∈ T₁, t ^ 2 = 1 → t ∈ A := fun t ht ht2 => by
    by_contra htA
    exact hy₀1 (hL t (hT₁S ht) ht2 htA y₀ (hT₁S hy₀T) (hy₀c t ht).symm hy₀A)
  have hfixT : ∀ c ∈ T₁, x⁻¹ * c * x = c → c = 1 := by
    intro c hc hcx
    by_contra hc1
    have hK : IsPGroup 2 (T₁ ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) :=
      S.isPGroup'.to_le (inf_le_left.trans hT₁S)
    have hne : T₁ ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := fun h => hc1 (by
      have hmem : c ∈ T₁ ⊓ Subgroup.centralizer ({x} : Set G) := Subgroup.mem_inf.mpr ⟨hc, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc c * x = x * (x⁻¹ * c * x) := by group
          _ = x * c := by rw [hcx]⟩
      rwa [h, Subgroup.mem_bot] at hmem)
    obtain ⟨t, htK, ht1, ht2⟩ := Sec8.exists_involution hK hne
    obtain ⟨htT, htx⟩ := Subgroup.mem_inf.mp htK
    refine ht1 (eq_one_of_conj_eq hset h4 hxA hxC (hinv t htT ht2) ?_)
    rw [Subgroup.mem_centralizer_singleton_iff] at htx
    rw [mul_assoc, htx]
    group
  have hT₁c : ∀ w ∈ T₁, ∀ w' ∈ T₁, w * w' = w' * w := by
    by_contra hnc
    refine hy₀1 (sq_eq_one_of_central hset h4 hT₁S hAT₁ hinv hxA hxC hxT₁ (fun h => hnc ?_)
      hy₀T hy₀c)
    exact fun w hw w' hw' => congrArg Subtype.val (h.is_comm.comm ⟨w, hw⟩ ⟨w', hw'⟩)
  have hodd : Odd (orderOf (x ^ 3)) :=
    Odd.of_dvd_nat (by rw [hb]; exact Odd.pow (by decide)) (orderOf_pow_dvd 3)
  have hgA := Sec8.pow_three_mem_centralizer hset h4 hxA
  have hx3T : ∀ w ∈ T₁, (x ^ 3)⁻¹ * w * x ^ 3 = w :=
    conj_eq_of_forall_sq (S.isPGroup'.to_le hT₁S) hT₁c (Subgroup.pow_mem _ hxT₁ 3) hodd
      fun w hw hw2 => by
        have hc := Subgroup.mem_centralizer_iff.mp hgA w (hinv w hw hw2)
        calc (x ^ 3)⁻¹ * w * x ^ 3 = (x ^ 3)⁻¹ * (w * x ^ 3) := by group
          _ = (x ^ 3)⁻¹ * (x ^ 3 * w) := by rw [hc]
          _ = w := by group
  refine ⟨T₁, hT₁S, hAT₁, hST₁, hxT₁, hsq, hself, hinv, hfixT, fun s hs => ?_⟩
  have hgS : x ^ 3 ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := Subgroup.pow_mem _ hxS 3
  have hw : s⁻¹ * ((x ^ 3)⁻¹ * s * x ^ 3) ∈ T₁ := by
    refine hself _ ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hs)
      (conj_mem_of_mem_normalizer hgS hs)) fun w hw => ?_
    have h1 : s * w * s⁻¹ ∈ T₁ := by
      have := conj_mem_of_mem_normalizer (Subgroup.inv_mem _ (hST₁ hs)) hw
      simpa using this
    have h2 := hx3T _ h1
    have h3 := hx3T w hw
    calc w * (s⁻¹ * ((x ^ 3)⁻¹ * s * x ^ 3))
        = s⁻¹ * (s * w * s⁻¹) * ((x ^ 3)⁻¹ * s * x ^ 3) := by group
      _ = s⁻¹ * ((x ^ 3)⁻¹ * (s * w * s⁻¹) * x ^ 3) * ((x ^ 3)⁻¹ * s * x ^ 3) := by rw [h2]
      _ = s⁻¹ * ((x ^ 3)⁻¹ * s * x ^ 3) * ((x ^ 3)⁻¹ * w * x ^ 3) := by group
      _ = s⁻¹ * ((x ^ 3)⁻¹ * s * x ^ 3) * w := by rw [h3]
  have hwg := hx3T _ hw
  obtain ⟨k, hk⟩ := (S.isPGroup'.to_le hT₁S) ⟨_, hw⟩
  have h1 := eq_one_of_conj_eq_mul
    (show (x ^ 3)⁻¹ * s * x ^ 3 = s * (s⁻¹ * ((x ^ 3)⁻¹ * s * x ^ 3)) by group) hwg hodd
    (k := k) (by simpa using congrArg Subtype.val hk)
  calc x⁻¹ * (x⁻¹ * (x⁻¹ * s * x) * x) * x = s * (s⁻¹ * ((x ^ 3)⁻¹ * s * x ^ 3)) := by
        simp only [pow_succ, pow_zero, one_mul]; group
    _ = s := by rw [h1, mul_one]

end CFSG.Goldschmidt.Sec89

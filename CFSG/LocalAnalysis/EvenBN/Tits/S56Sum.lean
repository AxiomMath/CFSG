module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.S56

open Subgroup

variable {G : Type*} [Group G]

private theorem five_mul_left_eq {E : Subgroup G} (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    {z a b c d g : G} (hz : z ∈ E) (hzz : z * z = 1) (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E)
    (hd : d ∈ E) (hg : g ∈ E) :
    (z * a) * (z * b) * (z * c) * (z * d) * (z * g) = z * (a * b * c * d * g) := by
  haveI : IsMulCommutative E := IsMulCommutative.of_comm fun p q => Subtype.ext (hEc p p.2 q q.2)
  have hZ : (⟨z, hz⟩ : E) * ⟨z, hz⟩ = 1 := Subtype.ext hzz
  have h : ((⟨z, hz⟩ : E) * ⟨a, ha⟩) * (⟨z, hz⟩ * ⟨b, hb⟩) * (⟨z, hz⟩ * ⟨c, hc⟩) *
      (⟨z, hz⟩ * ⟨d, hd⟩) * (⟨z, hz⟩ * ⟨g, hg⟩) =
      ⟨z, hz⟩ * (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨c, hc⟩ * ⟨d, hd⟩ * ⟨g, hg⟩) := by
    calc _ = ((⟨z, hz⟩ : E) * ⟨z, hz⟩) * (⟨z, hz⟩ * ⟨z, hz⟩) * ⟨z, hz⟩ *
          (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨c, hc⟩ * ⟨d, hd⟩ * ⟨g, hg⟩) := by ac_rfl
      _ = _ := by rw [hZ, one_mul, one_mul]
  exact congrArg Subtype.val h

theorem exists_conj_comm_of_five {E : Subgroup G} {x v z : G}
    (hx5 : x ^ 5 = 1) (hxE : x ∈ normalizer (E : Set G))
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hz : z ∈ E) (hzz : z * z = 1) (hz1 : z ≠ 1)
    (_hvz : v * z = z * v) (hCx : ∀ n ∈ E, n * x = x * n → n * v = v * n)
    (hv : ∀ e ∈ E, v * e * v⁻¹ = e ∨ v * e * v⁻¹ = z * e) {e : G} (he : e ∈ E) :
    ∃ i : ℕ, i < 5 ∧ v * ((x ^ i)⁻¹ * e * x ^ i) = ((x ^ i)⁻¹ * e * x ^ i) * v := by
  by_contra hcon
  push Not at hcon
  obtain ⟨f, hf⟩ : ∃ f : ℕ → G, ∀ i, f i = (x ^ i)⁻¹ * e * x ^ i := ⟨_, fun _ => rfl⟩
  have hfE : ∀ i, f i ∈ E := by
    intro i
    rw [hf]
    have h := (mem_normalizer_iff.1 (inv_mem (pow_mem hxE i))) e |>.1 he
    rwa [inv_inv] at h
  have hfv : ∀ i, i < 5 → v * f i * v⁻¹ = z * f i := by
    intro i hi
    rcases hv _ (hfE i) with h | h
    · exact absurd (mul_inv_eq_iff_eq_mul.1 h) (by rw [hf]; exact hcon i hi)
    · exact h
  have hx4 : x ^ 4 = x⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hx5)
  have hs1 : x * f 1 * x⁻¹ = f 0 := by rw [hf, hf]; group
  have hs2 : x * f 2 * x⁻¹ = f 1 := by rw [hf, hf]; group
  have hs3 : x * f 3 * x⁻¹ = f 2 := by rw [hf, hf]; group
  have hs4 : x * f 4 * x⁻¹ = f 3 := by rw [hf, hf]; group
  have hs0 : x * f 0 * x⁻¹ = f 4 := by rw [hf, hf, hx4]; group
  obtain ⟨n, hn⟩ : ∃ n : G, n = f 0 * f 1 * f 2 * f 3 * f 4 := ⟨_, rfl⟩
  have hnE : n ∈ E := by
    rw [hn]
    exact mul_mem (mul_mem (mul_mem (mul_mem (hfE 0) (hfE 1)) (hfE 2)) (hfE 3)) (hfE 4)
  have hxn : x * n * x⁻¹ = n := by
    have e1 : x * n * x⁻¹ = (x * f 0 * x⁻¹) * (x * f 1 * x⁻¹) * (x * f 2 * x⁻¹) *
        (x * f 3 * x⁻¹) * (x * f 4 * x⁻¹) := by rw [hn]; group
    rw [e1, hs0, hs1, hs2, hs3, hs4]
    have hc := hEc (f 4) (hfE 4) (f 0 * f 1 * f 2 * f 3)
      (mul_mem (mul_mem (mul_mem (hfE 0) (hfE 1)) (hfE 2)) (hfE 3))
    rw [hn, ← hc]
    group
  have hvn : v * n * v⁻¹ = z * n := by
    have e1 : v * n * v⁻¹ = (v * f 0 * v⁻¹) * (v * f 1 * v⁻¹) * (v * f 2 * v⁻¹) *
        (v * f 3 * v⁻¹) * (v * f 4 * v⁻¹) := by rw [hn]; group
    rw [e1, hfv 0 (by norm_num), hfv 1 (by norm_num), hfv 2 (by norm_num), hfv 3 (by norm_num),
      hfv 4 (by norm_num), hn]
    exact five_mul_left_eq hEc hz hzz (hfE 0) (hfE 1) (hfE 2) (hfE 3) (hfE 4)
  have hnv : n * v = v * n := hCx n hnE (mul_inv_eq_iff_eq_mul.1 hxn).symm
  have h1 : v * n * v⁻¹ = n := mul_inv_eq_iff_eq_mul.2 hnv.symm
  rw [hvn] at h1
  exact hz1 (by simpa using h1)

end CFSG.LocalAnalysis.EvenBN.Tits.S56

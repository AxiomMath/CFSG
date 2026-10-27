module

public import CFSG.GH74.GLS.IVK.L2.ExistNotation
public import CFSG.GH74.GLS.IVK.L2.Lemma14j

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.GH74.GLS.IVK

theorem sec5pe8_field_power
    {F : Type} [Field F] [Finite F] (hF : L2Field F) {Y : Type} [Group Y] [Finite Y]
    (P : Sylow 2 Y) (J : Subgroup Y) [J.Normal] (hJ : Nonempty (↥J ≃* L2 F))
    (κ : MulAut ↥J) (hodd : Odd (orderOf κ))
    (hfix : ∀ x : ↥J, (x : Y) ∈ (P : Subgroup Y) → κ x = x) (hne : κ ≠ 1) :
    ∃ (e' : ↥J ≃* L2 F) (r : ℕ) (x : MulAut ↥J), r.Prime ∧ r ≠ 2 ∧
      x ∈ Subgroup.zpowers κ ∧ orderOf x = r ∧ x ∉ innDiagSub e' := by
  obtain ⟨e', N, -, hPeq⟩ := ivk_1_2_general F hF Y J hJ P
  have hmem : κ ∈ Subgroup.centralizer (N.P : Set (MulAut ↥J)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [← hPeq] at hg
    obtain ⟨p, hp, hpg⟩ := hg
    rw [← hpg]
    have hconj : (MulAut.conjNormal p : MulAut ↥J) = MulAut.conj (⟨p, hp.2⟩ : ↥J) :=
      MulAut.conjNormal_val (H := J) (h := (⟨p, hp.2⟩ : ↥J))
    rw [hconj]
    ext j
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply,
      map_mul, map_mul, map_inv, hfix ⟨p, hp.2⟩ hp.1]
  obtain ⟨σ, hσ⟩ : ∃ σ : F ≃+* F, fieldAutHom e' σ = κ :=
    (odd_elt_mem (e := e') hF N κ hmem hodd).1
  have hordκσ : orderOf κ = orderOf σ := by
    rw [← hσ]
    exact orderOf_injective (fieldAutHom e') (fieldAutHom_injective e') σ
  have hoddσ : Odd (orderOf σ) := hordκσ ▸ hodd
  have hσne : σ ≠ 1 := by
    intro h
    exact hne (by rw [← hσ, h, map_one])
  have hnne1 : orderOf σ ≠ 1 := fun h => hσne (orderOf_eq_one_iff.mp h)
  set r : ℕ := Nat.minFac (orderOf σ) with hr
  have hrprime : r.Prime := by rw [hr]; exact Nat.minFac_prime hnne1
  have hrdvdσ : r ∣ orderOf σ := by rw [hr]; exact Nat.minFac_dvd _
  have hrodd : Odd r := hoddσ.of_dvd_nat hrdvdσ
  have hr2 : r ≠ 2 := by
    intro h2
    obtain ⟨k, hk⟩ := hrodd
    omega
  have hrdvdκ : r ∣ orderOf κ := by rw [hordκσ]; exact hrdvdσ
  set m : ℕ := orderOf κ / r with hm
  have hrm : r * m = orderOf κ := by rw [hm]; exact Nat.mul_div_cancel' hrdvdκ
  have hmpos : 0 < m := Nat.pos_of_mul_pos_left (by rw [hrm]; exact hodd.pos)
  have hm_lt : m < orderOf σ := by
    rw [← hordκσ, ← hrm]
    exact lt_mul_of_one_lt_left hmpos hrprime.one_lt
  have hxord : orderOf (κ ^ m) = r := by
    rw [hm]
    exact orderOf_pow_orderOf_div hodd.pos.ne' hrdvdκ
  have hxmem : κ ^ m ∈ Subgroup.zpowers κ := Subgroup.npow_mem_zpowers κ m
  have hxσ : κ ^ m = fieldAutHom e' (σ ^ m) := by
    rw [← hσ, ← map_pow]
  have hxnot : κ ^ m ∉ innDiagSub e' := by
    intro hxin
    rw [mem_innDiagSub_iff] at hxin
    rw [hxσ, fieldProj_fieldAutHom] at hxin
    exact Nat.not_dvd_of_pos_of_lt hmpos hm_lt (orderOf_dvd_of_pow_eq_one hxin)
  exact ⟨e', r, κ ^ m, hrprime, hr2, hxmem, hxord, hxnot⟩

end CFSG.OddStandard.SmallF3.Omega

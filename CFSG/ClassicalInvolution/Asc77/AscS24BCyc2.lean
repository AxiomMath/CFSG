module

public import CFSG.ClassicalInvolution.Asc77.AscS24BCyc1

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace S24B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] [Fact p.Prime] in
theorem eq_one_or_eq_sq_of_mem_zpowers {x y : G} (hx : orderOf x = 4)
    (hy : y ∈ Subgroup.zpowers x) (h2 : y * y = 1) : y = 1 ∨ y = x ^ 2 := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h : (4 : ℤ) ∣ m + m := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr (show x ^ (m + m) = 1 by rw [zpow_add]; exact h2)
    rw [hx] at this
    exact_mod_cast this
  rcases (by omega : m % 4 = 0 ∨ m % 4 = 2) with h4 | h4
  · left
    exact orderOf_dvd_iff_zpow_eq_one.mp (by rw [hx]; push_cast; omega)
  · right
    have h5 : x ^ (m - 2) = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hx]; push_cast; omega)
    calc x ^ m = x ^ (m - 2) * x ^ (2 : ℤ) := by rw [← zpow_add, sub_add_cancel]
      _ = x ^ 2 := by rw [h5, one_mul, zpow_two, sq]

omit [Finite G] [Fact p.Prime] in
theorem sq_and_gen_of_mem_zpowers {x y : G} (hx : orderOf x = 4) (hy : y ∈ Subgroup.zpowers x)
    (h2 : y * y ≠ 1) : y * y = x ^ 2 ∧ ∀ v ∈ Subgroup.zpowers x, ∃ k : ℤ, y ^ k = v := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hodd : m % 2 = 1 := by
    by_contra hm
    apply h2
    rw [← zpow_add]
    exact orderOf_dvd_iff_zpow_eq_one.mp (by rw [hx]; push_cast; omega)
  obtain ⟨t, rfl⟩ : ∃ t, m = 2 * t + 1 := ⟨m / 2, by omega⟩
  have hmm : x ^ ((2 * t + 1) * (2 * t + 1)) = x := by
    have h4 : x ^ ((2 * t + 1) * (2 * t + 1) - 1) = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by rw [hx]; push_cast; exact ⟨t * t + t, by ring⟩)
    calc x ^ ((2 * t + 1) * (2 * t + 1))
        = x ^ ((2 * t + 1) * (2 * t + 1) - 1) * x ^ (1 : ℤ) := by rw [← zpow_add, sub_add_cancel]
      _ = x := by rw [h4, one_mul, zpow_one]
  refine ⟨?_, ?_⟩
  · rw [← zpow_add]
    have h4 : x ^ (2 * t + 1 + (2 * t + 1) - 2) = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by rw [hx]; push_cast; omega)
    calc x ^ (2 * t + 1 + (2 * t + 1)) = x ^ (2 * t + 1 + (2 * t + 1) - 2) * x ^ (2 : ℤ) := by
          rw [← zpow_add, sub_add_cancel]
      _ = x ^ 2 := by rw [h4, one_mul, zpow_two, sq]
  · intro v hv
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    refine ⟨(2 * t + 1) * n, ?_⟩
    rw [← zpow_mul, ← mul_assoc, zpow_mul, hmm]

namespace Ctx8

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Ctx8 p f Ω K K' W S R R' z u)

theorem Dg_pow_four [IsSimpleGroup G] (h3 : H3 p f) {d : G} (hd : d ∈ C.Dg) : d ^ 4 = 1 := by
  obtain ⟨μ, hμ⟩ := C.exists_inj_D h3
  have hy4 : (μ ⟨d, hd⟩ : G) ^ 4 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ← C.orderOf_x₃]
    exact orderOf_dvd_of_mem_zpowers (μ ⟨d, hd⟩).2
  have h : μ (⟨d, hd⟩ ^ 4) = μ 1 := by
    rw [map_pow, map_one]
    exact Subtype.ext hy4
  exact congrArg Subtype.val (hμ h)

theorem Dg_comm [IsSimpleGroup G] (h3 : H3 p f) {d e : G} (hd : d ∈ C.Dg) (he : e ∈ C.Dg) :
    d * e = e * d := by
  obtain ⟨μ, hμ⟩ := C.exists_inj_D h3
  have h : μ (⟨d, hd⟩ * ⟨e, he⟩) = μ (⟨e, he⟩ * ⟨d, hd⟩) := by
    rw [map_mul, map_mul]
    apply Subtype.ext
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (μ ⟨d, hd⟩).2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (μ ⟨e, he⟩).2
    simp only [Subgroup.coe_mul, ← hi, ← hj]
    exact (Commute.zpow_zpow_self C.D.x₃ i j).eq
  exact congrArg Subtype.val (hμ h)

theorem Dg_involution [IsSimpleGroup G] (h3 : H3 p f) {d : G} (hd : d ∈ C.Dg)
    (h2 : d * d = 1) : d = 1 ∨ d = z := by
  obtain ⟨μ, hμ⟩ := C.exists_inj_D h3
  have key : ∀ e : ↥C.Dg, e * e = 1 → e = 1 ∨ (μ e : G) = C.D.x₃ ^ 2 := by
    intro e he
    have hy : (μ e : G) * (μ e : G) = 1 := by
      have h := congrArg (fun q => (μ q : G)) he
      simpa only [map_mul, map_one, Subgroup.coe_mul, OneMemClass.coe_one] using h
    rcases eq_one_or_eq_sq_of_mem_zpowers C.orderOf_x₃ (μ e).2 hy with h | h
    · left
      apply hμ
      rw [map_one]
      exact Subtype.ext h
    · exact Or.inr h
  rcases key ⟨d, hd⟩ (Subtype.ext h2) with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · right
    rcases key ⟨z, C.z_mem_Dg⟩ (Subtype.ext C.hzK.sq) with h' | h'
    · exact absurd (congrArg Subtype.val h') C.hzK.ne_one
    · have e : (⟨d, hd⟩ : ↥C.Dg) = ⟨z, C.z_mem_Dg⟩ := hμ (Subtype.ext (h.trans h'.symm))
      exact congrArg Subtype.val e

include C in
theorem z_mem_P : z ∈ (S : Subgroup G) ⊓ MGrp Ω W := C.W_le_P C.hd.hzW

include C in
theorem P_normal {g : G} (hg : g ∈ (S : Subgroup G)) {x : G}
    (hx : x ∈ (S : Subgroup G) ⊓ MGrp Ω W) : g * x * g⁻¹ ∈ (S : Subgroup G) ⊓ MGrp Ω W := by
  refine ⟨S.mul_mem (S.mul_mem hg hx.1) (S.inv_mem hg), ?_⟩
  have hgN : g ∈ Subgroup.normalizer (MGrp Ω W : Set G) :=
    le_normalizer_MGrp C.hs.stand.hyp (C.le_normalizer_W hg)
  exact (Subgroup.mem_normalizer_iff.mp hgN x).mp hx.2

theorem Dg_mem_P {d : G} (hd : d ∈ C.Dg) (hdP : d ∈ (S : Subgroup G) ⊓ MGrp Ω W) :
    d = 1 ∨ d = z := by
  have hdA := C.Dg_le_A hd
  have hdW := C.mem_W_of_mem_P_A hdP hdA
  have hdR := ((C.mem_A).mp hdA).2.2.1
  have hdR' : d ∈ Subgroup.centralizer (R' : Set G) := hd.2
  refine C.eq_one_or_eq_z_of_mem_W hdW ?_ ?_
  · have h := Subgroup.mem_centralizer_iff.mp hdR _ C.r_mem_R
    calc C.D.F.ρ.r * d * C.D.F.ρ.r⁻¹ = d * C.D.F.ρ.r * C.D.F.ρ.r⁻¹ := by rw [h]
      _ = d := by group
  · have h := Subgroup.mem_centralizer_iff.mp hdR' _ C.t_mem_R'
    calc C.D.F.ρ'.r * d * C.D.F.ρ'.r⁻¹ = d * C.D.F.ρ'.r * C.D.F.ρ'.r⁻¹ := by rw [h]
      _ = d := by group

theorem Dg_sq_of_not_mem [IsSimpleGroup G] (h3 : H3 p f) {d : G} (hd : d ∈ C.Dg)
    (hdP : d ∉ (S : Subgroup G) ⊓ MGrp Ω W) : d * d = z := by
  have hdd : d * d ∈ C.Dg := C.Dg.mul_mem hd hd
  have h4 : (d * d) * (d * d) = 1 := by
    calc (d * d) * (d * d) = d ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := C.Dg_pow_four h3 hd
  rcases C.Dg_involution h3 hdd h4 with h | h
  · exfalso
    apply hdP
    rcases C.Dg_involution h3 hd h with h' | h'
    · rw [h']
      exact Subgroup.one_mem _
    · rw [h']
      exact C.z_mem_P
  · exact h

theorem Dg_inv_mul_mem [IsSimpleGroup G] (h3 : H3 p f) {d e : G} (hd : d ∈ C.Dg)
    (he : e ∈ C.Dg) (hdP : d ∉ (S : Subgroup G) ⊓ MGrp Ω W)
    (heP : e ∉ (S : Subgroup G) ⊓ MGrp Ω W) : d⁻¹ * e ∈ (S : Subgroup G) ⊓ MGrp Ω W := by
  have hd2 := C.Dg_sq_of_not_mem h3 hd hdP
  have he2 := C.Dg_sq_of_not_mem h3 he heP
  have hc : Commute d e := C.Dg_comm h3 hd he
  have hc' : e * d⁻¹ = d⁻¹ * e := hc.inv_left.eq.symm
  have hde : d⁻¹ * e ∈ C.Dg := C.Dg.mul_mem (C.Dg.inv_mem hd) he
  have h2 : (d⁻¹ * e) * (d⁻¹ * e) = 1 := by
    calc (d⁻¹ * e) * (d⁻¹ * e) = d⁻¹ * (e * d⁻¹) * e := by group
      _ = d⁻¹ * (d⁻¹ * e) * e := by rw [hc']
      _ = (d * d)⁻¹ * (e * e) := by group
      _ = 1 := by rw [hd2, he2, inv_mul_cancel]
  rcases C.Dg_involution h3 hde h2 with h | h
  · rw [h]
    exact Subgroup.one_mem _
  · rw [h]
    exact C.z_mem_P

end Ctx8

end S24B

end CFSG.ClassicalInvolution.Asc77

module

public import CFSG.CGT.Timmesfeld75.Sec77Q
public import CFSG.CGT.Timmesfeld75.Sec78Linear

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups Matrix

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem inv_conj_mul_of_commute {w z c ub u : G} (hu : u = ub * c) (hub : ub = w * z * w⁻¹)
    (hw : w * c = c * w) : w⁻¹ * u * w = z * c := by
  have h1 : w⁻¹ * c * w = c := by
    calc w⁻¹ * c * w = w⁻¹ * (c * w) := by group
      _ = w⁻¹ * (w * c) := by rw [hw]
      _ = c := by group
  rw [hu, hub]
  calc w⁻¹ * (w * z * w⁻¹ * c) * w = z * (w⁻¹ * c * w) := by group
    _ = z * c := by rw [h1]

section Same

variable [(T.subgroupOf (hSub T (normIn T₁ T))).Normal]

theorem Sec6Ctx.false_of_same_hyperplane (h66 : Sec66) (h1 : Sec4NoA) (h62 : Sec62)
    (h63 : Sec63) (hc : Sec6Ctx T T₁ n m) (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m)
    (hn3 : 3 ≤ n) (hA8 : ¬ (n = 4 ∧ m = 1)) (M : TModel T T₁ n m) {x z u ub cu : G}
    {fz g fb : Module.Dual (GaloisField 2 m) (Fin n → GaloisField 2 m)}
    {vz vb : Fin n → GaloisField 2 m} (hxT : x ∈ T) (hx1 : x ≠ 1) (hz : z ∈ normD T)
    (hu : u ∈ normD T) (huT : u ∉ T) (hub : ub ∈ normD T) (hubT : ub ∉ T) (hvz : vz ≠ 0)
    (hvb : vb ≠ 0) (hgv : g vz = 0) (hfbv : fb vb = 0) (hfzv : fz vz = 0) (hg0 : g ≠ 0)
    (hfb0 : fb ≠ 0) (hdz : ∀ w, sact (ubar M.ε z) w = w + fz w • vz)
    (hdu : ∀ w, sact (ubar M.ε u) w = w + g w • vz)
    (hdb : ∀ w, sact (ubar M.ε ub) w = w + fb w • vb)
    (hindg : ∀ r t : GaloisField 2 m, r • g + t • fz = 0 → r = 0 ∧ t = 0)
    (hker : ∀ w, fb w = 0 ↔ fz w = 0) (hcu : u * ub = cu) (hubu : u * ub = ub * u)
    (hcu1 : cu ≠ 1) (hcuD : cu ∉ classD T) (hbD : z * cu ∈ classD T)
    (hbx : z * cu * x = x * (z * cu)) : False := by
  have := hc.finite
  have hTwc := hc.hy.pair.wc
  have hindz : ∀ r t : GaloisField 2 m, r • fz + t • g = 0 → r = 0 ∧ t = 0 := fun r t h =>
    (hindg t r (by rw [add_comm]; exact h)).symm
  have hbN : z * cu ∈ normD T :=
    ⟨hbD, hTwc.centralizer_le_normalizer hxT hx1 (Subgroup.mem_centralizer_singleton_iff.2 hbx)⟩
  obtain ⟨w₁, hw₁g, hw₁f⟩ := exists_vec_eq_one_zero hindg
  obtain ⟨w₂, hw₂f, hw₂g⟩ := exists_vec_eq_one_zero hindz
  have hfbw₁ : fb w₁ = 0 := (hker w₁).2 hw₁f
  have hfzvb : fz vb = 0 := (hker vb).1 hfbv
  have hfbw₂ : fb w₂ ≠ 0 := fun h => by
    have := (hker w₂).1 h
    rw [hw₂f] at this
    exact one_ne_zero this
  have hzH := M.mem_H hz
  have huH := M.mem_H hu
  have hubH := M.mem_H hub
  have hbub : ubar M.ε (z * cu) = ubar M.ε z * (ubar M.ε u * ubar M.ε ub) := by
    rw [← hcu, ubar_mul M.ε hzH ((hSub T (normIn T₁ T)).mul_mem huH hubH),
      ubar_mul M.ε huH hubH]
  have hact : ∀ w, sact (ubar M.ε (z * cu)) w =
      w + (fb w • vb + (g w + fb w * g vb) • vz + (fz w + fb w * fz vb) • vz) := by
    intro w
    rw [hbub, sact_mul, sact_mul, hdb w, hdu, hdz]
    simp only [map_add, map_smul, smul_eq_mul, hfzv, mul_zero, add_zero]
    module
  have hv1 : sact (ubar M.ε (z * cu)) w₁ = w₁ + vz := by
    rw [hact, hw₁g, hw₁f, hfbw₁]
    simp
  have hv2 : sact (ubar M.ε (z * cu)) w₂ = w₂ + (fb w₂ • vb + (fb w₂ * g vb + 1) • vz) := by
    rw [hact, hw₂f, hw₂g, hfzvb]
    module
  by_cases hbT : z * cu ∈ T
  · have h1' : ubar M.ε (z * cu) = 1 := (ubar_eq_one_iff M.ε (M.mem_H hbN)).2 hbT
    rw [h1', sact_one] at hv1
    have : w₁ + 0 = w₁ + vz := by rw [add_zero]; exact hv1
    exact hvz (add_left_cancel this).symm
  · obtain ⟨fbb, vbb, -, -, -, hdbb⟩ := M.exists_data hbN hbT
    have e1 : fbb w₁ • vbb = vz := by
      have := hdbb w₁
      rw [hv1] at this
      exact (add_left_cancel this).symm
    have e2 : fbb w₂ • vbb = fb w₂ • vb + (fb w₂ * g vb + 1) • vz := by
      have := hdbb w₂
      rw [hv2] at this
      exact (add_left_cancel this).symm
    have hf1 : fbb w₁ ≠ 0 := fun h => hvz (by rw [← e1, h, zero_smul])
    have e3 : vbb = (fbb w₁)⁻¹ • vz := by
      rw [← e1, smul_smul, inv_mul_cancel₀ hf1, one_smul]
    obtain ⟨a, ha⟩ : ∃ a : GaloisField 2 m, vb = a • vz := by
      have h4 : fb w₂ • vb = (fbb w₂ * (fbb w₁)⁻¹ - (fb w₂ * g vb + 1)) • vz := by
        have h5 : fb w₂ • vb = fbb w₂ • vbb - (fb w₂ * g vb + 1) • vz := by
          rw [e2]
          abel
        rw [h5, e3, smul_smul, sub_smul]
      refine ⟨(fb w₂)⁻¹ * (fbb w₂ * (fbb w₁)⁻¹ - (fb w₂ * g vb + 1)), ?_⟩
      calc vb = (fb w₂)⁻¹ • (fb w₂ • vb) := by rw [smul_smul, inv_mul_cancel₀ hfbw₂, one_smul]
        _ = (fb w₂)⁻¹ • ((fbb w₂ * (fbb w₁)⁻¹ - (fb w₂ * g vb + 1)) • vz) := by rw [h4]
        _ = ((fb w₂)⁻¹ * (fbb w₂ * (fbb w₁)⁻¹ - (fb w₂ * g vb + 1))) • vz := by rw [smul_smul]
    have ha0 : a ≠ 0 := fun h => hvb (by rw [ha, h, zero_smul])
    have hfbvz : fb vz = 0 := by
      have h6 : fb vb = 0 := hfbv
      rw [ha, map_smul, smul_eq_mul] at h6
      exact (mul_eq_zero.1 h6).resolve_left ha0
    have hdb' : ∀ w, sact (ubar M.ε ub) w = w + (a • fb) w • vz := by
      intro w
      rw [hdb w, ha, smul_smul]
      simp only [LinearMap.smul_apply, smul_eq_mul, mul_comm]
    have hfb'vz : (a • fb) vz = 0 := by
      simp only [LinearMap.smul_apply, smul_eq_mul, hfbvz, mul_zero]
    have hfb'0 : a • fb ≠ 0 := smul_ne_zero ha0 hfb0
    rcases hc.mul_mem_of_same_center h66 h1 h62 h63 hnat hn3 hA8 M hu huT hub hubT hubu hvz hgv
      hfb'vz hg0 hfb'0 hdu hdb' with hT' | hD'
    · exact hcuD (mem_classD_of_mem (hcu ▸ hT') hcu1)
    · exact hcuD (hcu ▸ hD')

end Same

end CFSG.CGT.Timmesfeld75

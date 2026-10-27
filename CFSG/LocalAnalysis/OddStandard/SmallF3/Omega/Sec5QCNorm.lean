module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CentDPull

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {t : OGroup Q}

private theorem q8_map_le_twoCoreIn {g : SL2F3 →* OGroup Q} {K : Subgroup (OGroup Q)}
    (hNK : q8SL.map g ≤ K) (hKg : ∀ k ∈ K, ∃ C : SL2F3, g C = k) :
    q8SL.map g ≤ twoCoreIn K := by
  refine le_twoCoreIn_of_normal hNK ?_ ?_
  · rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    refine ⟨2, ?_⟩
    obtain ⟨A, hA, hxA⟩ := Subgroup.mem_map.mp x.2
    have hA4 : A ^ 4 = 1 := (mem_q8SL_iff A).mp hA
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    show ((x : OGroup Q)) ^ 4 = 1
    rw [← hxA, ← map_pow, hA4, map_one]
  · rw [Subgroup.normal_subgroupOf_iff hNK]
    intro h k hh hk
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hh
    obtain ⟨C, rfl⟩ := hKg k hk
    refine Subgroup.mem_map.mpr ⟨C * A * C⁻¹, q8SL_normal.conj_mem A hA C, ?_⟩
    simp only [map_mul, map_inv]

private theorem theta_left_q8_le_twoCoreIn (D : Om6Par Q t) {a : SL2F3} (ha : a ^ 4 = 1) :
    D.theta (leftMulHom a) ∈ twoCoreIn D.L := by
  have hle : q8SL.map (D.theta.comp leftMulHom) ≤ D.L := by
    rintro x ⟨A, -, rfl⟩
    rw [Om6Par.L]
    exact Subgroup.mem_map.mpr ⟨leftMulHom A, ⟨A, rfl⟩, rfl⟩
  have hsurj : ∀ k ∈ D.L, ∃ C : SL2F3, (D.theta.comp leftMulHom) C = k := by
    rintro k hk
    rw [Om6Par.L] at hk
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hk
    obtain ⟨C, rfl⟩ := hx
    exact ⟨C, rfl⟩
  exact q8_map_le_twoCoreIn hle hsurj (Subgroup.mem_map.mpr ⟨a, (mem_q8SL_iff a).mpr ha, rfl⟩)

private theorem theta_right_q8_le_twoCoreIn (D : Om6Par Q t) {b : SL2F3} (hb : b ^ 4 = 1) :
    D.theta (rightMulHom b) ∈ twoCoreIn D.R := by
  have hle : q8SL.map (D.theta.comp rightMulHom) ≤ D.R := by
    rintro x ⟨A, -, rfl⟩
    rw [Om6Par.R]
    exact Subgroup.mem_map.mpr ⟨rightMulHom A, ⟨A, rfl⟩, rfl⟩
  have hsurj : ∀ k ∈ D.R, ∃ C : SL2F3, (D.theta.comp rightMulHom) C = k := by
    rintro k hk
    rw [Om6Par.R] at hk
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hk
    obtain ⟨C, rfl⟩ := hx
    exact ⟨C, rfl⟩
  exact q8_map_le_twoCoreIn hle hsurj (Subgroup.mem_map.mpr ⟨b, (mem_q8SL_iff b).mpr hb, rfl⟩)

theorem sec5qc_norm (D : Om6Par Q t) {p q : OGroup Q} (hp : p ∈ D.L ⊔ D.R)
    (hq : q ∈ twoCoreIn D.L ⊔ twoCoreIn D.R) : p * q * p⁻¹ ∈ twoCoreIn D.L ⊔ twoCoreIn D.R := by
  have hL : D.L ≤ Subgroup.normalizer (twoCoreIn D.L ⊔ twoCoreIn D.R : Subgroup (OGroup Q)) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha h hh
    have hmap : (twoCoreIn D.L ⊔ twoCoreIn D.R : Subgroup (OGroup Q)).map (MulAut.conj a) ≤
        twoCoreIn D.L ⊔ twoCoreIn D.R := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro x ⟨y, hy, rfl⟩
        change a * y * a⁻¹ ∈ twoCoreIn D.L ⊔ twoCoreIn D.R
        exact Subgroup.mem_sup_left ((Subgroup.normal_subgroupOf_iff (twoCoreIn_le_self D.L)).mp
          (normal_subgroupOf_twoCoreIn D.L) y a hy ha)
      · rintro x ⟨y, hy, rfl⟩
        change a * y * a⁻¹ ∈ twoCoreIn D.L ⊔ twoCoreIn D.R
        rw [D.sec5Pair.comm a ha y (twoCoreIn_le_self D.R hy), mul_assoc, mul_inv_cancel, mul_one]
        exact Subgroup.mem_sup_right hy
    have hm : MulAut.conj a h ∈
        (twoCoreIn D.L ⊔ twoCoreIn D.R : Subgroup (OGroup Q)).map (MulAut.conj a) :=
      ⟨h, hh, rfl⟩
    have hconj := hmap hm
    change a * h * a⁻¹ ∈ twoCoreIn D.L ⊔ twoCoreIn D.R at hconj
    exact hconj
  have hR : D.R ≤ Subgroup.normalizer (twoCoreIn D.L ⊔ twoCoreIn D.R : Subgroup (OGroup Q)) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb h hh
    have hmap : (twoCoreIn D.L ⊔ twoCoreIn D.R : Subgroup (OGroup Q)).map (MulAut.conj b) ≤
        twoCoreIn D.L ⊔ twoCoreIn D.R := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro x ⟨y, hy, rfl⟩
        change b * y * b⁻¹ ∈ twoCoreIn D.L ⊔ twoCoreIn D.R
        rw [← D.sec5Pair.comm y (twoCoreIn_le_self D.L hy) b hb, mul_assoc, mul_inv_cancel, mul_one]
        exact Subgroup.mem_sup_left hy
      · rintro x ⟨y, hy, rfl⟩
        change b * y * b⁻¹ ∈ twoCoreIn D.L ⊔ twoCoreIn D.R
        exact Subgroup.mem_sup_right ((Subgroup.normal_subgroupOf_iff (twoCoreIn_le_self D.R)).mp
          (normal_subgroupOf_twoCoreIn D.R) y b hy hb)
    have hm : MulAut.conj b h ∈
        (twoCoreIn D.L ⊔ twoCoreIn D.R : Subgroup (OGroup Q)).map (MulAut.conj b) :=
      ⟨h, hh, rfl⟩
    have hconj := hmap hm
    change b * h * b⁻¹ ∈ twoCoreIn D.L ⊔ twoCoreIn D.R at hconj
    exact hconj
  exact (Subgroup.mem_normalizer_iff.mp (sup_le hL hR hp) q).mp hq

theorem sec5qc_q8Img_le (D : Om6Par Q t) : D.q8Img ≤ twoCoreIn D.L ⊔ twoCoreIn D.R := by
  intro g hg
  obtain ⟨a, b, ha, hb, hgab⟩ := (Om6Par.mem_q8Img_iff D).mp hg
  have hLa : D.theta (leftMulHom a) ∈ twoCoreIn D.L := theta_left_q8_le_twoCoreIn D ha
  have hRb : D.theta (rightMulHom b) ∈ twoCoreIn D.R := theta_right_q8_le_twoCoreIn D hb
  rw [← hgab, detPhi_apply, map_mul]
  exact Subgroup.mul_mem_sup hLa hRb

end CFSG.OddStandard.SmallF3.Omega

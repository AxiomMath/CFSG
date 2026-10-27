module

public import CFSG.LargeExtraspecial.AS35U2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35K

open Subgroup Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
  CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
  CFSG.LocalAnalysis.GorensteinLyons.FourUnitary
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

@[expose] noncomputable def Rhat (m : ℕ) (e : Fin m → K) : Subgroup (SUid frob m) :=
  (axisKernel (AS35U.hermB m) e).comap (AS35U.ι m)

@[expose] noncomputable def Rbar (m : ℕ) (e : Fin m → K) : Subgroup (PG m) :=
  (Rhat m e).map (QuotientGroup.mk' (center (SUid frob m)))

theorem fix_of_mem_Rhat {e : Fin m → K} {a : SUid frob m} (ha : a ∈ Rhat m e) : a • e = e := by
  rw [← AS35U.ι_apply]
  exact (mem_axisKernel.mp ha).2.1

theorem map_Rhat_ι (hm : 3 ≤ m) {e : Fin m → K} (he0 : e ≠ 0) (he : herm frob e e = 0) :
    (Rhat m e).map (AS35U.ι m) = axisKernel (AS35U.hermB m) e := by
  have he' : AS35U.hermB m e e = 0 := he
  have hd : 3 ≤ Module.finrank K (Fin m → K) := by rw [Module.finrank_fin_fun]; omega
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hSU, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.four_element_unitary_axis_flag_kernel_and_regular_orbit
      AS35U.hF AS35U.hermB_isSymm AS35U.hermB_separatingLeft hd he0 he'
  exact Subgroup.map_comap_eq_self fun y hy => by
    obtain ⟨a, ha⟩ := AS35U.exists_ι_eq (hSU hy)
    exact ⟨a, ha⟩

theorem eq_one_of_mem_Rhat (hm : 3 ≤ m) {e : Fin m → K} (he0 : e ≠ 0) {x : SUid frob m}
    (hx : x ∈ Rhat m e) (h1 : QuotientGroup.mk' (center (SUid frob m)) x = 1) : x = 1 := by
  have hxZ : x ∈ center (SUid frob m) := (QuotientGroup.eq_one_iff _).mp h1
  rw [center_SUid hm] at hxZ
  obtain ⟨c, hc⟩ := exists_smul_eq_of_mem_scalars hxZ
  have hce : c • e = e := (hc e).symm.trans (fix_of_mem_Rhat hx)
  have hc1 : c = 1 := by
    have h0 : (c - 1) • e = 0 := by rw [sub_smul, one_smul, hce, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right he0)
  exact ext_smul _ fun y => by rw [hc, hc1, one_smul, one_smul]

theorem card_Rbar (hm : 3 ≤ m) {e : Fin m → K} (he0 : e ≠ 0) (he : herm frob e e = 0) :
    Nat.card (Rbar m e) = 2 ^ (1 + 2 * (m - 2)) := by
  have he' : AS35U.hermB m e e = 0 := he
  have hd : 3 ≤ Module.finrank K (Fin m → K) := by rw [Module.finrank_fin_fun]; omega
  obtain ⟨-, -, -, -, -, -, -, -, -, hcard, -, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.four_element_unitary_axis_flag_kernel_and_regular_orbit
      AS35U.hF AS35U.hermB_isSymm AS35U.hermB_separatingLeft hd he0 he'
  set π := QuotientGroup.mk' (center (SUid frob m))
  set r := π.comp (Rhat m e).subtype
  have hr : Function.Injective r := (injective_iff_map_eq_one r).mpr fun x hx =>
    Subtype.ext (eq_one_of_mem_Rhat hm he0 x.2 hx)
  have hrange : r.range = Rbar m e := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hr).toEquiv,
    ← Subgroup.card_map_of_injective (K := Rhat m e) (f := AS35U.ι m) AS35U.ι_injective,
    map_Rhat_ι hm he0 he, hcard, Module.finrank_fin_fun]

theorem isPGroup_Rbar (hm : 3 ≤ m) {e : Fin m → K} (he0 : e ≠ 0) (he : herm frob e e = 0) :
    IsPGroup 2 (Rbar m e) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPGroup.of_card (card_Rbar hm he0 he)

theorem tq_mem_Rbar (hm : 3 ≤ m) {e : Fin m → K} (he0 : e ≠ 0) (he : herm frob e e = 0) :
    tq e ∈ Rbar m e := by
  have he' : AS35U.hermB m e e = 0 := he
  have hd : 3 ≤ Module.finrank K (Fin m → K) := by rw [Module.finrank_fin_fun]; omega
  obtain ⟨-, hT, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.four_element_unitary_axis_flag_kernel_and_regular_orbit
      AS35U.hF AS35U.hermB_isSymm AS35U.hermB_separatingLeft hd he0 he'
  refine ⟨tvU e, ?_, rfl⟩
  change AS35U.ι m (tvU e) ∈ axisKernel (AS35U.hermB m) e
  rw [AS35U.ι_tvU he']
  exact hT

theorem Rbar_le_centralizer {e : Fin m → K} (he : herm frob e e = 0) :
    Rbar m e ≤ centralizer {tq e} := by
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have h1 : a * tvU e = tvU e * a := by
    calc a * tvU e = a * tvU e * a⁻¹ * a := by group
      _ = tvU e * a := by rw [conj_tvU a he, fix_of_mem_Rhat ha]
  change QuotientGroup.mk' _ a * QuotientGroup.mk' _ (tvU e) =
    QuotientGroup.mk' _ (tvU e) * QuotientGroup.mk' _ a
  rw [← map_mul, ← map_mul, h1]

theorem conj_mem_Rbar (hm : 3 ≤ m) {e : Fin m → K} (he0 : e ≠ 0) (he : herm frob e e = 0)
    {c : PG m} (hc : c ∈ centralizer {tq e}) {x : PG m} (hx : x ∈ Rbar m e) :
    c * x * c⁻¹ ∈ Rbar m e := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center (SUid frob m)) c
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨μ, hμ0, hgμ⟩ := AS35U.exists_smul_eq_of_mem_centralizer hm he0 he hc
  have hginv : g⁻¹ • e = μ⁻¹ • e := by
    calc g⁻¹ • e = g⁻¹ • (μ⁻¹ • (μ • e)) := by rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      _ = μ⁻¹ • e := by rw [smul_comm g⁻¹ μ⁻¹ (μ • e), ← hgμ, inv_smul_smul]
  refine ⟨g * a * g⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  change AS35U.ι m (g * a * g⁻¹) ∈ axisKernel (AS35U.hermB m) e
  refine mem_axisKernel.mpr ⟨(mem_sesqSpecialUnitaryGroup.mp (AS35U.ι_mem _)).1, ?_, ?_⟩
  · rw [AS35U.ι_apply, mul_smul, mul_smul, hginv, smul_comm a μ⁻¹ e, fix_of_mem_Rhat ha,
      smul_comm g μ⁻¹ e, hgμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  · intro x hx
    have hx' : herm frob e x = 0 := mem_axisPerp.mp hx
    have hy : herm frob e (g⁻¹ • x) = 0 := by
      have h := herm_smul_smul frob g e (g⁻¹ • x)
      rw [hgμ, smul_inv_smul, herm_smul_left, hx', mul_zero] at h
      exact h.symm
    have ha' := (mem_axisKernel.mp ha).2.2 (g⁻¹ • x) (mem_axisPerp.mpr hy)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha'
    rw [AS35U.ι_apply] at hc
    refine Submodule.mem_span_singleton.mpr ⟨c * μ, ?_⟩
    rw [AS35U.ι_apply]
    calc (c * μ) • e = g • (c • e) := by rw [smul_comm, hgμ, smul_smul]
      _ = g • (a • (g⁻¹ • x) - g⁻¹ • x) := by rw [hc]
      _ = (g * a * g⁻¹) • x - x := by rw [smul_sub, smul_inv_smul, mul_smul, mul_smul]

end CFSG.LargeExtraspecial.AS35K

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Ctx

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

section Quad

variable {K : Fin 4 → Subgroup G} {z : G}

theorem Sec5B517Quad.pair_invol_conj (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j)
    {d d' : G} (hd : d ∈ K i ⊔ K j) (hd2 : d * d = 1) (hd1 : d ≠ 1) (hdz : d ≠ z)
    (hd' : d' ∈ K i ⊔ K j) (hd'2 : d' * d' = 1) (hd'1 : d' ≠ 1) (hd'z : d' ≠ z) :
    ∃ y ∈ K i ⊔ K j, y⁻¹ * d * y = d' := by
  obtain ⟨a, ha, b, hb, hdab, ha2, hb2⟩ := sec5b513_decomp (Classical.choice (hq.iso i))
    (Classical.choice (hq.iso j)) (hq.comm i j hij) (hq.z_mem i) (hq.z_mem j) hq.z_sq hq.z_ne
    hd hd2 hd1 hdz
  obtain ⟨a', ha', b', hb', hdab', ha2', hb2'⟩ := sec5b513_decomp (Classical.choice (hq.iso i))
    (Classical.choice (hq.iso j)) (hq.comm i j hij) (hq.z_mem i) (hq.z_mem j) hq.z_sq hq.z_ne
    hd' hd'2 hd'1 hd'z
  obtain ⟨u, hu, hua⟩ := sec5b513_conj_of_sq (Classical.choice (hq.iso i)) (hq.z_mem i) hq.z_sq
    hq.z_ne ha ha' ha2 ha2'
  obtain ⟨v, hv, hvb⟩ := sec5b513_conj_of_sq (Classical.choice (hq.iso j)) (hq.z_mem j) hq.z_sq
    hq.z_ne hb hb' hb2 hb2'
  refine ⟨u * v, Subgroup.mul_mem_sup hu hv, ?_⟩
  have hub : u⁻¹ * b * u = b := by
    rw [mul_assoc, show b * u = u * b from (hq.comm i j hij u hu b hb).symm, inv_mul_cancel_left]
  have hva : v⁻¹ * a' * v = a' := by
    rw [mul_assoc, show a' * v = v * a' from hq.comm i j hij a' ha' v hv, inv_mul_cancel_left]
  rw [hdab, hdab']
  calc (u * v)⁻¹ * (a * b) * (u * v)
      = v⁻¹ * (u⁻¹ * a * u) * (u⁻¹ * b * u) * v := by group
    _ = v⁻¹ * a' * b * v := by rw [hua, hub]
    _ = (v⁻¹ * a' * v) * (v⁻¹ * b * v) := by group
    _ = a' * b' := by rw [hva, hvb]

end Quad

section Ctx

variable [Finite G] {t : G} {L S : Subgroup G} {z r : G} {B A K₁ K₂ : Subgroup G} {h : G}

private theorem l515S_twoRes_le (H : Subgroup G) : twoRes H ≤ H := by
  rw [twoRes]
  exact (Subgroup.closure_le H).mpr fun _ hx => hx.1

theorem l515S_sup_le_L (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : K₁ ⊔ K₂ ≤ L := by
  rw [c.prod]
  exact (l515S_twoRes_le _).trans inf_le_left

private theorem l515S_sq_of_orderOf {d : G} (hd : orderOf d = 2) : d * d = 1 := by
  rw [← pow_two, ← hd, pow_orderOf_eq_one]

private theorem l515S_ne_one_of_orderOf {d : G} (hd : orderOf d = 2) : d ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hd
  omega

theorem l515S_tclass_K34 (h37 : Asc82Lemma37) (h514 : Asc82Lemma514)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {d : G} (hd2 : orderOf d = 2) (hdz : d ≠ z)
    (hd : d ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) :
    ∃ I : Subgroup G, Sec5Setting G d I ∧
      ∃ P : Subgroup G, IsKOf (Gamma5 K₁ K₂ h) d P ∧ P ≤ I := by
  have hq : Sec5B517Quad (Kfam5 K₁ K₂ h) z := sec5b517_quad h514 c
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have hK2 : Kfam5 K₁ K₂ h 2 = CFSG.conjugate K₁ h := by simp [Kfam5]
  have hK3 : Kfam5 K₁ K₂ h 3 = CFSG.conjugate K₂ h := by simp [Kfam5]
  have hK0 : Kfam5 K₁ K₂ h 0 = K₁ := by simp [Kfam5]
  have hK1 : Kfam5 K₁ K₂ h 1 = K₂ := by simp [Kfam5]
  have hdq : d ∈ Kfam5 K₁ K₂ h 2 ⊔ Kfam5 K₁ K₂ h 3 := by rw [hK2, hK3]; exact hd
  have htq : t ∈ Kfam5 K₁ K₂ h 2 ⊔ Kfam5 K₁ K₂ h 3 := by rw [hK2, hK3]; exact c.t_mem_sup₃₄
  obtain ⟨y, hy, hyd⟩ := hq.pair_invol_conj h23 htq c.t_mul_self c.t_ne_one (c.t_ne_z h37) hdq
    (l515S_sq_of_orderOf hd2) (l515S_ne_one_of_orderOf hd2) hdz
  have hcent : ∀ l : Fin 4, l ≠ 2 → l ≠ 3 → Kfam5 K₁ K₂ h l ≤ centralizer ({y} : Set G) :=
    fun l hl2 hl3 => hq.le_centralizer_of_mem_pair hl2 hl3 hy
  have hK1y : K₁ ≤ centralizer ({y} : Set G) := hK0 ▸ hcent 0 (by decide) (by decide)
  have hK2y : K₂ ≤ centralizer ({y} : Set G) := hK1 ▸ hcent 1 (by decide) (by decide)
  have hKd : K₁ ⊔ K₂ ≤ centralizer ({d} : Set G) := by
    have h0 : K₁ ≤ centralizer ({d} : Set G) :=
      hK0 ▸ hq.le_centralizer_of_mem_pair (by decide) (by decide) hdq
    have h1 : K₂ ≤ centralizer ({d} : Set G) :=
      hK1 ▸ hq.le_centralizer_of_mem_pair (by decide) (by decide) hdq
    exact sup_le h0 h1
  have hset : Sec5Setting G d (CFSG.conjugate L y) := by
    have := (sec5HCtx_conj c y).toSec5Setting
    rwa [hyd] at this
  refine ⟨CFSG.conjugate L y, hset, K₁ ⊔ K₂, ⟨K₁, ?_, K₂, ?_, c.ne, rfl, hKd⟩, ?_⟩
  · simp [Gamma5]
  · simp [Gamma5]
  · intro w hw
    rw [sec5b_mem_conjugate_iff]
    have hwc : y * w * y⁻¹ = w := by
      have hw' : w ∈ centralizer ({y} : Set G) := (sup_le hK1y hK2y) hw
      have := Subgroup.mem_centralizer_singleton_iff.mp hw'
      calc y * w * y⁻¹ = (w * y) * y⁻¹ := by rw [this]
        _ = w := by group
    rw [hwc]
    exact l515S_sup_le_L c hw

theorem l515S_tclass_K12 (h37 : Asc82Lemma37) (h514 : Asc82Lemma514)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {d : G} (hd2 : orderOf d = 2) (hdz : d ≠ z)
    (hd : d ∈ K₁ ⊔ K₂) :
    ∃ I : Subgroup G, Sec5Setting G d I ∧
      ∃ P : Subgroup G, IsKOf (Gamma5 K₁ K₂ h) d P ∧ P ≤ I := by
  have hq : Sec5B517Quad (Kfam5 K₁ K₂ h) z := sec5b517_quad h514 c
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have hK2 : Kfam5 K₁ K₂ h 2 = CFSG.conjugate K₁ h := by simp [Kfam5]
  have hK3 : Kfam5 K₁ K₂ h 3 = CFSG.conjugate K₂ h := by simp [Kfam5]
  have hK0 : Kfam5 K₁ K₂ h 0 = K₁ := by simp [Kfam5]
  have hK1 : Kfam5 K₁ K₂ h 1 = K₂ := by simp [Kfam5]
  have hdq : d ∈ Kfam5 K₁ K₂ h 0 ⊔ Kfam5 K₁ K₂ h 1 := by rw [hK0, hK1]; exact hd
  have hhz : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp c.h_z
  have hs2 : (h⁻¹ * t * h) * (h⁻¹ * t * h) = 1 := by
    calc (h⁻¹ * t * h) * (h⁻¹ * t * h) = h⁻¹ * (t * t) * h := by group
      _ = 1 := by rw [c.t_mul_self]; group
  have hs1 : h⁻¹ * t * h ≠ 1 := by
    intro hs
    apply c.t_ne_one
    calc t = h * (h⁻¹ * t * h) * h⁻¹ := by group
      _ = 1 := by rw [hs]; group
  have hsz : h⁻¹ * t * h ≠ z := by
    intro hs
    apply c.t_ne_z h37
    calc t = h * (h⁻¹ * t * h) * h⁻¹ := by group
      _ = h * z * h⁻¹ := by rw [hs]
      _ = z := by rw [hhz]; group
  have hsq : h⁻¹ * t * h ∈ Kfam5 K₁ K₂ h 0 ⊔ Kfam5 K₁ K₂ h 1 := by rw [hK0, hK1]; exact c.h_t
  obtain ⟨y, hy, hyd⟩ := hq.pair_invol_conj h01 hsq hs2 hs1 hsz hdq
    (l515S_sq_of_orderOf hd2) (l515S_ne_one_of_orderOf hd2) hdz
  have hcent : ∀ l : Fin 4, l ≠ 0 → l ≠ 1 → Kfam5 K₁ K₂ h l ≤ centralizer ({y} : Set G) :=
    fun l hl0 hl1 => hq.le_centralizer_of_mem_pair hl0 hl1 hy
  have hK3y : CFSG.conjugate K₁ h ≤ centralizer ({y} : Set G) :=
    hK2 ▸ hcent 2 (by decide) (by decide)
  have hK4y : CFSG.conjugate K₂ h ≤ centralizer ({y} : Set G) :=
    hK3 ▸ hcent 3 (by decide) (by decide)
  have hKd : CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h ≤ centralizer ({d} : Set G) := by
    have h0 : CFSG.conjugate K₁ h ≤ centralizer ({d} : Set G) :=
      hK2 ▸ hq.le_centralizer_of_mem_pair (by decide) (by decide) hdq
    have h1 : CFSG.conjugate K₂ h ≤ centralizer ({d} : Set G) :=
      hK3 ▸ hq.le_centralizer_of_mem_pair (by decide) (by decide) hdq
    exact sup_le h0 h1
  have hdeq : (h * y)⁻¹ * t * (h * y) = d := by
    rw [← hyd]
    group
  have hset : Sec5Setting G d (CFSG.conjugate L (h * y)) := by
    have := (sec5HCtx_conj c (h * y)).toSec5Setting
    rwa [hdeq] at this
  refine ⟨CFSG.conjugate L (h * y), hset,
    CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h,
    ⟨CFSG.conjugate K₁ h, ?_, CFSG.conjugate K₂ h, ?_, ?_, rfl, hKd⟩, ?_⟩
  · simp [Gamma5]
  · simp [Gamma5]
  · have := hq.ne (i := 2) (j := 3) (by decide)
    rwa [hK2, hK3] at this
  · intro w hw
    rw [sec5b_mem_conjugate_iff]
    have hwy : y * w * y⁻¹ = w := by
      have hw' : w ∈ centralizer ({y} : Set G) := (sup_le hK3y hK4y) hw
      have := Subgroup.mem_centralizer_singleton_iff.mp hw'
      calc y * w * y⁻¹ = (w * y) * y⁻¹ := by rw [this]
        _ = w := by group
    have hwh : h * w * h⁻¹ ∈ K₁ ⊔ K₂ := by
      rw [← sec5b_conjugate_sup K₁ K₂ h] at hw
      exact sec5b_mem_conjugate_iff.mp hw
    have : (h * y) * w * (h * y)⁻¹ = h * w * h⁻¹ := by
      calc (h * y) * w * (h * y)⁻¹ = h * (y * w * y⁻¹) * h⁻¹ := by group
        _ = h * w * h⁻¹ := by rw [hwy]
    rw [this]
    exact l515S_sup_le_L c hwh

theorem l515S_tclass (h37 : Asc82Lemma37) (h514 : Asc82Lemma514)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {d : G} (hd2 : orderOf d = 2) (hdz : d ≠ z)
    (hd : d ∈ K₁ ⊔ K₂ ∨ d ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) :
    ∃ I : Subgroup G, Sec5Setting G d I ∧
      ∃ P : Subgroup G, IsKOf (Gamma5 K₁ K₂ h) d P ∧ P ≤ I := by
  rcases hd with hd | hd
  · exact l515S_tclass_K12 h37 h514 c hd2 hdz hd
  · exact l515S_tclass_K34 h37 h514 c hd2 hdz hd

end Ctx

end CFSG.OddStandard.SmallF3.Omega

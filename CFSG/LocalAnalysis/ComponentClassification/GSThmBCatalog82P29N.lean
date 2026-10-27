module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29M
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29T

public section

namespace CFSG.ComponentClassification.GSThmB.P29.A10

open CFSG Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.GSThmB.Catalog82A10

@[expose] def parDHom : DihedralGroup 4 →* Multiplicative (ZMod 2) := MonoidHom.mk' parD parD_mul

@[expose] def embR : DihedralGroup 4 →* W :=
  MonoidHom.mk' (fun y => ((1, y), parD y)) (by decide +kernel)

@[expose] def embL : DihedralGroup 4 →* W :=
  MonoidHom.mk' (fun x => ((x, 1), parD x)) (by decide +kernel)

@[expose] def D : Subgroup (Perm (Fin 10)) := (phi.comp embR).range

@[expose] def D' : Subgroup (Perm (Fin 10)) := (phi.comp embL).range

theorem mem_D {g : Perm (Fin 10)} : g ∈ D ↔ ∃ y, phiFun ((1, y), parD y) = g :=
  MonoidHom.mem_range

theorem mem_D' {g : Perm (Fin 10)} : g ∈ D' ↔ ∃ x, phiFun ((x, 1), parD x) = g :=
  MonoidHom.mem_range

theorem t0_inv : t0⁻¹ = t0 := inv_eq_of_mul_eq_one_right t0_mul_self

theorem t0_mem : t0 ∈ alternatingGroup (Fin 10) := mem_alternatingGroup.mpr sign_t0

theorem mem_centralizer_altOn {g : Perm (Fin 10)} :
    g ∈ centralizer (altOn fixTwo : Set (Perm (Fin 10))) ↔ ∀ x ∈ fixTwo, g x = x := by
  rw [mem_centralizer_iff]
  constructor
  · intro h
    exact fix_of_commute_altOn fun n hn => (h n hn).symm
  · intro h n hn
    have hsub : g.support ⊆ n.supportᶜ := by
      intro x hx
      rw [Finset.mem_compl]
      intro hxn
      exact (Equiv.Perm.mem_support.mp hx) (h x ((mem_altOn.mp hn).2 hxn))
    exact (commute_of_support_subset_compl hsub).symm

variable {R : Subgroup (Perm (Fin 10))}

theorem inf_altOn (hR : alternatingGroup (Fin 10) ≤ R) : P ⊓ R ⊓ altOn fixTwo = D := by
  ext g
  constructor
  · intro hg
    rw [mem_inf, mem_inf] at hg
    obtain ⟨⟨hP, -⟩, hJ⟩ := hg
    obtain ⟨⟨⟨x, y⟩, z⟩, rfl⟩ := mem_P.mp hP
    rw [mem_altOn, mem_alternatingGroup] at hJ
    obtain ⟨h1, h2⟩ := (altOn_iff _).mp hJ
    simp only at h1 h2
    rw [h1, ← h2]
    exact mem_D.mpr ⟨y, rfl⟩
  · intro hg
    obtain ⟨y, rfl⟩ := mem_D.mp hg
    have hJ : phiFun ((1, y), parD y) ∈ altOn fixTwo := by
      rw [mem_altOn, mem_alternatingGroup]
      exact (altOn_iff _).mpr ⟨rfl, rfl⟩
    exact ⟨⟨mem_P.mpr ⟨_, rfl⟩, hR (mem_altOn.mp hJ).1⟩, hJ⟩

theorem conjugate_D : conjugate D t0 = D' := by
  ext g
  rw [conjugate]
  constructor
  · rintro ⟨_, hd, rfl⟩
    obtain ⟨y, rfl⟩ := mem_D.mp hd
    refine mem_D'.mpr ⟨y, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, t0_inv]
    exact (t0_phiFun ((1, y), parD y)).symm
  · intro hg
    obtain ⟨x, rfl⟩ := mem_D'.mp hg
    refine ⟨phiFun ((1, x), parD x), mem_D.mpr ⟨x, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, t0_inv]
    exact t0_phiFun ((1, x), parD x)

theorem t0_normalizer (hR : alternatingGroup (Fin 10) ≤ R) :
    t0 ∈ normalizer ((P ⊓ R : Subgroup (Perm (Fin 10))) : Set (Perm (Fin 10))) := by
  have hP : ∀ g ∈ P, t0 * g * t0⁻¹ ∈ P := by
    intro g hg
    obtain ⟨w, rfl⟩ := mem_P.mp hg
    rw [t0_inv, t0_phiFun]
    exact mem_P.mpr ⟨_, rfl⟩
  have ht : t0 ∈ R := hR t0_mem
  rw [mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨hgP, hgR⟩
    exact ⟨hP g hgP, R.mul_mem (R.mul_mem ht hgR) (R.inv_mem ht)⟩
  · rintro ⟨hgP, hgR⟩
    have hg : t0 * (t0 * g * t0⁻¹) * t0⁻¹ = g := by
      rw [show t0 * (t0 * g * t0⁻¹) * t0⁻¹ = t0 * t0 * g * (t0 * t0)⁻¹ by group, t0_mul_self]
      group
    rw [← hg]
    exact ⟨hP _ hgP, R.mul_mem (R.mul_mem ht hgR) (R.inv_mem ht)⟩

theorem t0_not_mem : t0 ∉ P ⊓ R := by
  rintro ⟨hP, -⟩
  obtain ⟨w, hw⟩ := mem_P.mp hP
  have h := phiFun_comm w
  rw [hw] at h
  exact t0_not_comm h

theorem D_inf_D' : D ⊓ D' = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hg, hg'⟩
  obtain ⟨y, rfl⟩ := mem_D.mp hg
  obtain ⟨x, hx⟩ := mem_D'.mp hg'
  have h := phi_injective (show phi ((x, 1), parD x) = phi ((1, y), parD y) from hx)
  have hy : y = 1 := (congrArg (fun w : W => w.1.2) h).symm
  rw [hy, parD_one, mem_bot, ← phi_apply]
  exact map_one phi

theorem D_comm {d e : Perm (Fin 10)} (hd : d ∈ D) (he : e ∈ D') : d * e = e * d := by
  obtain ⟨y, rfl⟩ := mem_D.mp hd
  obtain ⟨x, rfl⟩ := mem_D'.mp he
  rw [← phi_apply, ← phi_apply, ← map_mul, ← map_mul]
  congr 1
  exact Prod.ext (Prod.ext (by simp) (by simp)) (mul_comm _ _)

theorem D_sup (hR : alternatingGroup (Fin 10) ≤ R) :
    D ⊔ D' = P ⊓ R ⊓ alternatingGroup (Fin 10) := by
  apply le_antisymm
  · rw [sup_le_iff]
    constructor
    · intro g hg
      obtain ⟨y, rfl⟩ := mem_D.mp hg
      have hA : phiFun ((1, y), parD y) ∈ alternatingGroup (Fin 10) := by
        rw [mem_alternatingGroup, sign_iff]
        simp [parD_one]
      exact ⟨⟨mem_P.mpr ⟨_, rfl⟩, hR hA⟩, hA⟩
    · intro g hg
      obtain ⟨x, rfl⟩ := mem_D'.mp hg
      have hA : phiFun ((x, 1), parD x) ∈ alternatingGroup (Fin 10) := by
        rw [mem_alternatingGroup, sign_iff]
        simp [parD_one]
      exact ⟨⟨mem_P.mpr ⟨_, rfl⟩, hR hA⟩, hA⟩
  · intro g hg
    rw [mem_inf, mem_inf] at hg
    obtain ⟨⟨hP, -⟩, hA⟩ := hg
    obtain ⟨⟨⟨x, y⟩, z⟩, rfl⟩ := mem_P.mp hP
    rw [mem_alternatingGroup, sign_iff] at hA
    simp only at hA
    have h : phiFun ((x, y), z) = phiFun ((x, 1), parD x) * phiFun ((1, y), parD y) := by
      rw [← phi_apply, ← phi_apply, ← phi_apply, ← map_mul, ← hA]
      congr 1
      exact Prod.ext (Prod.ext (by simp) (by simp)) rfl
    rw [h]
    exact mul_mem (mem_sup_right (mem_D'.mpr ⟨x, rfl⟩)) (mem_sup_left (mem_D.mpr ⟨y, rfl⟩))

theorem injective_embL : Function.Injective (phi.comp embL) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have h := phi_injective ((MonoidHom.mem_ker.mp hx).trans (map_one phi).symm)
  exact mem_bot.mpr (congrArg (fun w : W => w.1.1) h)

theorem relIndex_D' :
    (D' ⊓ centralizer (altOn fixTwo : Set (Perm (Fin 10)))).relIndex D' = 2 := by
  have h1 : D' ⊓ centralizer (altOn fixTwo : Set (Perm (Fin 10))) =
      parDHom.ker.map (phi.comp embL) := by
    ext g
    constructor
    · rintro ⟨hg, hc⟩
      obtain ⟨x, rfl⟩ := mem_D'.mp hg
      exact ⟨x, (fix_iff x).mp (mem_centralizer_altOn.mp hc), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mem_D'.mpr ⟨x, rfl⟩, mem_centralizer_altOn.mpr ((fix_iff x).mpr hx)⟩
  have h2 : D' = (⊤ : Subgroup (DihedralGroup 4)).map (phi.comp embL) :=
    MonoidHom.range_eq_map _
  rw [h1, h2, relIndex_map_map_of_injective _ _ injective_embL, relIndex_top_right]
  exact index_eq_two_iff.mpr ⟨DihedralGroup.sr 0, fun b => parD_xor b⟩

theorem sigmaTwo_mem :
    sigmaTwo ∈ D' ⊓ centralizer (altOn fixTwo : Set (Perm (Fin 10))) :=
  ⟨mem_D'.mpr ⟨DihedralGroup.r 2, phiFun_sigmaTwo⟩, mem_centralizer_altOn.mpr sigmaTwo_fix⟩

theorem sigmaTwo_comm {e : Perm (Fin 10)} (he : e ∈ D') : sigmaTwo * e = e * sigmaTwo := by
  obtain ⟨x, rfl⟩ := mem_D'.mp he
  exact (phiFun_comm _).symm

theorem outer {d : Perm (Fin 10)} (hd : d ∈ D')
    (hdC : d ∉ centralizer (altOn fixTwo : Set (Perm (Fin 10)))) {j : Perm (Fin 10)}
    (hj : j ∈ altOn fixTwo) : ∃ w ∈ altOn fixTwo, d * w * d⁻¹ ≠ j * w * j⁻¹ := by
  obtain ⟨x, hdx⟩ := mem_D'.mp hd
  have hx : parD x ≠ 1 := fun h =>
    hdC (hdx ▸ mem_centralizer_altOn.mpr ((fix_iff x).mpr h))
  by_contra hne
  push Not at hne
  have hc : j⁻¹ * d ∈ centralizer (altOn fixTwo : Set (Perm (Fin 10))) := by
    rw [mem_centralizer_iff]
    intro n hn
    calc n * (j⁻¹ * d) = j⁻¹ * (j * n * j⁻¹) * d := by group
      _ = j⁻¹ * (d * n * d⁻¹) * d := by rw [hne n hn]
      _ = j⁻¹ * d * n := by group
  rw [mem_centralizer_altOn] at hc
  have hj' : j = swap 8 9 := by
    refine Equiv.ext fun y => ?_
    by_cases hy : y ∈ fixTwo
    · have h1 := hc y hy
      rw [Perm.mul_apply, ← hdx, phiFun_outer x hx y hy, Perm.inv_eq_iff_eq] at h1
      exact h1.symm
    · have hjy : j y = y := by
        by_contra hjy
        exact hy ((mem_altOn.mp hj).2 (Perm.mem_support.mpr hjy))
      have h8 : y ≠ 8 := fun h => hy (by rw [h]; decide)
      have h9 : y ≠ 9 := fun h => hy (by rw [h]; decide)
      rw [hjy, swap_apply_of_ne_of_ne h8 h9]
  have hsign := (mem_altOn.mp hj).1
  rw [hj', mem_alternatingGroup, sign_swap (show (8 : Fin 10) ≠ 9 by decide)] at hsign
  exact absurd hsign (by decide)

theorem modelConcl (hR : alternatingGroup (Fin 10) ≤ R) {cyc : Prop} (hcyc : ¬ cyc) :
    ModelConcl (alternatingGroup (Fin 10)) sigmaTwo (altOn fixTwo) (P ⊓ R) cyc := by
  unfold ModelConcl
  rw [inf_altOn hR]
  refine ⟨t0, t0_mem, t0_normalizer hR, t0_not_mem, by rw [t0_mul_self]; exact one_mem _, ?_⟩
  rw [conjugate_D, D_sup hR]
  exact ⟨D_inf_D', fun d hd e he => D_comm hd he, rfl, relIndex_D', sigmaTwo_mem,
    fun e he => sigmaTwo_comm he, fun h => absurd h hcyc, fun d hd hdC j hj => outer hd hdC hj⟩

end CFSG.ComponentClassification.GSThmB.P29.A10

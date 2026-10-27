module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GKbar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA CFSG.EvenSporadicStandard.HNRecog
  CFSG.RankThree.Literature.FSmith

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} {n : G}

@[expose] noncomputable def A0W (h : Setting25 G t z z₁ ι zv R0 F) :
    Submodule (ZMod 2) (Wsp h) where
  carrier := {w | ∃ (x : G) (hx : x ∈ Rgrp h), x ∈ Cgrp ι zv ∧ toW h x hx = w}
  add_mem' := by
    rintro _ _ ⟨x, hx, hxC, rfl⟩ ⟨y, hy, hyC, rfl⟩
    exact ⟨x * y, mul_mem hx hy, mul_mem hxC hyC, toW_mul h hx hy⟩
  zero_mem' := ⟨1, one_mem _, one_mem _, (toW_eq_zero_iff h (one_mem _)).2 (one_mem _)⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, hxC, rfl⟩
    rcases zmod2_cases c with rfl | rfl
    · exact ⟨1, one_mem _, one_mem _, by
        rw [zero_smul]; exact (toW_eq_zero_iff h (one_mem _)).2 (one_mem _)⟩
    · exact ⟨x, hx, hxC, by rw [one_smul]⟩

private theorem toW_proof_irrel (h : Setting25 G t z z₁ ι zv R0 F) {x : G}
    (h1 h2 : x ∈ Rgrp h) : toW h x h1 = toW h x h2 :=
  congrArg (toW h x) (Subsingleton.elim h1 h2)

theorem z_mem_Cgrp (h : Setting25 G t z z₁ ι zv R0 F) : z ∈ Cgrp ι zv := by
  rw [← h.coord_z]
  exact (coordElt_mem_Cgrp h.injective_ι).mpr (bil_self zv)

theorem mem_A0W_iff (h : Setting25 G t z z₁ ι zv R0 F) {x : G} (hx : x ∈ Rgrp h) :
    toW h x hx ∈ A0W h ↔ x ∈ Cgrp ι zv := by
  constructor
  · rintro ⟨x', hx', hx'C, hx'eq⟩
    have hmem : x' * x⁻¹ ∈ zpowers z := (toW_eq_toW_iff h hx' hx).1 hx'eq
    have hmemC : x' * x⁻¹ ∈ Cgrp ι zv :=
      (Subgroup.zpowers_le (g := z)).2 (z_mem_Cgrp h) hmem
    have h1 : (x' * x⁻¹)⁻¹ * x' ∈ Cgrp ι zv := mul_mem (inv_mem hmemC) hx'C
    rwa [show (x' * x⁻¹)⁻¹ * x' = x by group] at h1
  · intro hxC
    exact ⟨x, hx, hxC, rfl⟩

theorem finrank_A0W (h : Setting25 G t z z₁ ι zv R0 F) :
    Module.finrank (ZMod 2) (A0W h) = 4 := by
  classical
  let f : ↥(Cgrp ι zv) → Multiplicative (A0W h) := fun c =>
    Multiplicative.ofAdd ⟨toW h c.1 (Cgrp_le_Rgrp h c.2),
      ⟨c.1, Cgrp_le_Rgrp h c.2, c.2, rfl⟩⟩
  have hf : ∀ c d, f (c * d) = f c * f d := by
    intro c d
    change Multiplicative.ofAdd (⟨toW h (c.1 * d.1) (Cgrp_le_Rgrp h (mul_mem c.2 d.2)), _⟩ :
        A0W h) =
      Multiplicative.ofAdd (⟨toW h c.1 (Cgrp_le_Rgrp h c.2), _⟩ : A0W h) *
      Multiplicative.ofAdd (⟨toW h d.1 (Cgrp_le_Rgrp h d.2), _⟩ : A0W h)
    rw [← ofAdd_add]
    apply Multiplicative.ext
    simp only [toAdd_ofAdd]
    apply Subtype.ext
    show toW h (c.1 * d.1) (Cgrp_le_Rgrp h (mul_mem c.2 d.2)) =
      toW h c.1 (Cgrp_le_Rgrp h c.2) + toW h d.1 (Cgrp_le_Rgrp h d.2)
    rw [toW_proof_irrel h _ (mul_mem (Cgrp_le_Rgrp h c.2) (Cgrp_le_Rgrp h d.2)),
      toW_mul h (Cgrp_le_Rgrp h c.2) (Cgrp_le_Rgrp h d.2)]
  let π : ↥(Cgrp ι zv) →* Multiplicative (A0W h) := MonoidHom.mk' f hf
  have hsurj : Function.Surjective π := by
    intro y
    rcases y.2 with ⟨x, hx, hxC, heq⟩
    refine ⟨⟨x, hxC⟩, ?_⟩
    change f ⟨x, hxC⟩ = y
    rw [show f ⟨x, hxC⟩ = Multiplicative.ofAdd (⟨toW h x (Cgrp_le_Rgrp h hxC),
      ⟨x, Cgrp_le_Rgrp h hxC, hxC, rfl⟩⟩ : A0W h) from rfl]
    apply Multiplicative.ext
    simp only [toAdd_ofAdd]
    exact Subtype.ext (by
      show toW h x (Cgrp_le_Rgrp h hxC) = y.1
      rw [toW_proof_irrel h _ hx, heq])
  have hker_mem : ∀ c : ↥(Cgrp ι zv),
      c ∈ π.ker ↔ c ∈ (zpowers z).subgroupOf (Cgrp ι zv) := by
    intro c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change f c = 1 ↔ c.1 ∈ zpowers z
    rw [show f c = Multiplicative.ofAdd (⟨toW h c.1 (Cgrp_le_Rgrp h c.2),
      ⟨c.1, Cgrp_le_Rgrp h c.2, c.2, rfl⟩⟩ : A0W h) from rfl]
    rw [ofAdd_eq_one, Subtype.ext_iff]
    exact toW_eq_zero_iff h (Cgrp_le_Rgrp h c.2)
  have hker : π.ker = (zpowers z).subgroupOf (Cgrp ι zv) := Subgroup.ext hker_mem
  have hker_card : Nat.card π.ker = 2 := by
    rw [hker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((Subgroup.zpowers_le (g := z)).2 (z_mem_Cgrp h))).toEquiv]
    rw [Nat.card_zpowers, orderOf_eq_prime h.z_sq h.z_ne_one]
  have hq : Nat.card (↥(Cgrp ι zv) ⧸ π.ker) = Nat.card (A0W h) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hsurj).toEquiv).trans
      (Nat.card_congr Multiplicative.toAdd)
  have hcard : Nat.card (A0W h) = 16 := by
    have hcard_eq := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    rw [card_Cgrp h.injective_ι h.zv_ne_zero, hq, hker_card] at hcard_eq
    omega
  have hnat := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := A0W h)
  rw [Nat.card_zmod, hcard] at hnat
  have hpow : (2 : ℕ) ^ Module.finrank (ZMod 2) (A0W h) = 2 ^ 4 := by
    rw [← hnat]; norm_num
  exact Nat.pow_right_injective (le_refl 2) hpow

theorem A0W_isotropic (h : Setting25 G t z z₁ ι zv R0 F) :
    ∀ u ∈ A0W h, ∀ u' ∈ A0W h, QuadraticMap.polar (qW h) u u' = 0 := by
  intro u hu u' hu'
  rcases hu with ⟨x, hx, hxC, rfl⟩
  rcases hu' with ⟨x', hx', hx'C, rfl⟩
  exact (polar_toW h hx hx').2 (Cgrp_mul_comm hxC hx'C)

theorem A0W_orth_le (h : Setting25 G t z z₁ ι zv R0 F) :
    ∀ w : Wsp h, (∀ u ∈ A0W h, QuadraticMap.polar (qW h) w u = 0) → w ∈ A0W h := by
  intro w hw
  have hB : (qW h).polarBilin.Nondegenerate := nondegenerate_qW h
  have hmem : w ∈ LinearMap.BilinForm.orthogonal ((qW h).polarBilin) (A0W h) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
    exact hw u hu
  have hle : A0W h ≤ LinearMap.BilinForm.orthogonal ((qW h).polarBilin) (A0W h) := by
    intro u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u' hu'
    rw [QuadraticMap.polarBilin_apply_apply]
    exact A0W_isotropic h u' hu' u hu
  have hfin : Module.finrank (ZMod 2) (A0W h) =
      Module.finrank (ZMod 2)
        (LinearMap.BilinForm.orthogonal ((qW h).polarBilin) (A0W h)) := by
    rw [LinearMap.BilinForm.finrank_orthogonal hB, finrank_Wsp h, finrank_A0W h]
  have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
  rw [← heq] at hmem
  exact hmem

theorem centralizer_A0_inf_Rgrp (h : Setting25 G t z z₁ ι zv R0 F) {x : G} (hx : x ∈ Rgrp h)
    (hc : ∀ a ∈ Cgrp ι zv, x * a = a * x) : x ∈ Cgrp ι zv := by
  have hmem : toW h x hx ∈ A0W h := by
    apply A0W_orth_le h (toW h x hx)
    intro u hu
    rcases hu with ⟨a, ha, haC, rfl⟩
    exact (polar_toW h hx ha).2 (hc a haC)
  exact (mem_A0W_iff h hx).1 hmem

theorem A0W_stable (h : Setting25 G t z z₁ ι zv R0 F) {k : G} (hk : k ∈ Kgrp ι z) {u : Wsp h}
    (hu : u ∈ A0W h) :
    ((rho0 h ⟨k, Kgrp_le_Ngrp h hk⟩ : TauCeti.QuadraticMap.orthogonalGroup (qW h)) :
      Wsp h ≃ₗ[ZMod 2] Wsp h) u ∈ A0W h := by
  rcases hu with ⟨a, ha, haC, rfl⟩
  have hkN : k ∈ normalizer (ι.range : Set G) := (Subgroup.mem_inf.mp hk).1
  have hmemA : k * a * k⁻¹ ∈ ι.range :=
    (Subgroup.mem_set_normalizer_iff.mp hkN a).mp (Cgrp_le_range haC)
  have hR : k * a * k⁻¹ ∈ Rgrp h := Rgrp_conj h hk (Cgrp_le_Rgrp h haC)
  have hC : k * a * k⁻¹ ∈ Cgrp ι zv := by
    rw [← Rgrp_inf_range h]; exact ⟨hR, hmemA⟩
  rw [rho0_toW h ⟨k, Kgrp_le_Ngrp h hk⟩ ha]
  exact (mem_A0W_iff h (conj_mem_Rgrp h (Kgrp_le_Ngrp h hk) ha)).2 hC

theorem A0W_fixed_by_vbar (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) {u : Wsp h} (hu : u ∈ A0W h) :
    (rhoX h (vbar h hn) : Wsp h ≃ₗ[ZMod 2] Wsp h) u = u := by
  rcases hu with ⟨a, ha, haC, rfl⟩
  have hvA : n * t * n⁻¹ ∈ ι.range := conj_t_mem_range h hn
  have haA : a ∈ ι.range := Cgrp_le_range haC
  have hcomm : (n * t * n⁻¹) * a = a * (n * t * n⁻¹) := by
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hvA
    obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp haA
    rw [← hp, ← hq, ← map_mul, ← map_mul, mul_comm p q]
  have hconj : (n * t * n⁻¹) * a * (n * t * n⁻¹)⁻¹ = a := by
    rw [hcomm]; group
  have hkey : ((rhoX h (vbar h hn) : Wsp h ≃ₗ[ZMod 2] Wsp h)) =
      ((rho0 h ⟨n * t * n⁻¹, conj_t_mem_Ngrp h hn⟩ :
        TauCeti.QuadraticMap.orthogonalGroup (qW h)) : Wsp h ≃ₗ[ZMod 2] Wsp h) := rfl
  rw [hkey, rho0_toW h ⟨n * t * n⁻¹, conj_t_mem_Ngrp h hn⟩ ha]
  exact (toW_eq_toW_iff h _ ha).2 (by rw [hconj]; simp)

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27

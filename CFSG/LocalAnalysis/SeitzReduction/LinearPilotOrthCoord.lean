module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthCoordAct
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRigidityBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCores

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.EvenSmallLie CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)

section Chart

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]

theorem modelToG_eq_map (e : L ≃* projectiveSL n K) (A : Subgroup (projectiveSL n K)) :
    modelToG e A = A.map (L.subtype.comp e.symm.toMonoidHom) := by
  rw [modelToG, Subgroup.map_map]

theorem subtype_comp_symm_injective (e : L ≃* projectiveSL n K) :
    Function.Injective (L.subtype.comp e.symm.toMonoidHom) :=
  L.subtype_injective.comp e.symm.injective

theorem range_subtype_comp_symm (e : L ≃* projectiveSL n K) :
    (L.subtype.comp e.symm.toMonoidHom).range = L := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.symm.surjective, ← MonoidHom.range_eq_map,
    range_subtype]

@[expose] noncomputable def chartOfInjective {φ : projectiveSL n K →* G}
    (hφ : Function.Injective φ) (hφL : φ.range = L) : L ≃* projectiveSL n K :=
  ((MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hφL)).symm

theorem coe_chartOfInjective_symm {φ : projectiveSL n K →* G} (hφ : Function.Injective φ)
    (hφL : φ.range = L) (p : projectiveSL n K) :
    (((chartOfInjective hφ hφL).symm p : L) : G) = φ p := by
  simp [chartOfInjective, MonoidHom.ofInjective_apply]

theorem subtype_comp_chartOfInjective_symm {φ : projectiveSL n K →* G}
    (hφ : Function.Injective φ) (hφL : φ.range = L) :
    L.subtype.comp (chartOfInjective hφ hφL).symm.toMonoidHom = φ := by
  ext p
  exact coe_chartOfInjective_symm hφ hφL p

theorem modelToG_chartOfInjective {φ : projectiveSL n K →* G} (hφ : Function.Injective φ)
    (hφL : φ.range = L) (A : Subgroup (projectiveSL n K)) :
    modelToG (chartOfInjective hφ hφL) A = A.map φ := by
  rw [modelToG_eq_map, subtype_comp_chartOfInjective_symm]

theorem modelToG_perfectCore_centralizer [Finite G] [Finite K] (e : L ≃* projectiveSL n K)
    (x : projectiveSL n K) :
    modelToG e (perfectCore (centralizer ({x} : Set (projectiveSL n K)))) =
      perfectCore (L ⊓ centralizer ({((e.symm x : L) : G)} : Set G)) := by
  rw [modelToG_eq_map, map_perfectCore_centralizer_singleton (subtype_comp_symm_injective e),
    range_subtype_comp_symm e]
  rfl

end Chart

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem xab_one_mul_self {n : ℕ} {K : Type*} [Field K] [CharP K 2] {a b : Fin n} (hab : a ≠ b) :
    xab (K := K) hab 1 * xab hab 1 = 1 := by
  rw [← xab_add, CharTwo.add_self_eq_zero, xab_zero]

variable {n : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem perfectCore_inf_centralizer_xab_eq (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (e : L ≃* projectiveSL n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b) {g : G}
    (hg : g⁻¹ * t * g = t * ((e.symm (xab hab 1) : L) : G)) :
    perfectCore (L ⊓ centralizer ({((e.symm (xab hab 1) : L) : G)} : Set G)) =
      perfectCore (CFSG.conjugate L g ⊓
        centralizer ({((e.symm (xab hab 1) : L) : G)} : Set G)) := by
  set z := ((e.symm (xab hab 1) : L) : G) with hz
  have hzz : z * z = 1 := by
    rw [hz, ← L.coe_mul, ← map_mul, xab_one_mul_self, map_one, L.coe_one]
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have htz : z * t = t * z := mem_centralizer_iff.1 htC z (e.symm (xab hab 1)).2
  have hw : z⁻¹ * t ∈ centralizer (CFSG.conjugate L g : Set G) := by
    rw [hzinv, htz, ← hg, mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_singleton_iff.1 (EPilot.conjugate_le_centralizer_conj htC g hl)
  exact EPilot.perfectCore_inf_centralizer_eq_of_inv_mul_mem hset hOut htC ht (Or.inr hg) hw

theorem exists_conjugate_chart_xab (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    (e : L ≃* projectiveSL n K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {a b : Fin n} (hab : a ≠ b) {g : G} (hg : g⁻¹ * t * g = t * ((e.symm (xab hab 1) : L) : G)) :
    ∃ e₁ : CFSG.conjugate L g ≃* projectiveSL n K,
      ((e₁.symm (xab hab 1) : CFSG.conjugate L g) : G) = ((e.symm (xab hab 1) : L) : G) := by
  classical
  set z := ((e.symm (xab hab 1) : L) : G) with hz
  have hzz : z * z = 1 := by
    rw [hz, ← L.coe_mul, ← map_mul, xab_one_mul_self, map_one, L.coe_one]
  have hΛeq := perfectCore_inf_centralizer_xab_eq hset hOut e htC ht hab hg
  have hΛ0 := modelToG_perfectCore_centralizer e (xab hab 1)
  have hzΛ : z ∈ perfectCore (L ⊓ centralizer ({z} : Set G)) := by
    rw [← hΛ0]
    refine symm_mem_modelToG e (radicalP_le_perfectCore_centralizer_xab hq hn hab ?_)
    rw [← pairPlacement_elt hab]
    exact (pairPlacement hab).elt_mem_radicalP
  have hzL' : z ∈ CFSG.conjugate L g := by
    rw [hΛeq] at hzΛ
    exact ((perfectCore_le _).trans inf_le_left) hzΛ
  set e₀ := conjChart e g with he₀
  set z₀ := e₀ ⟨z, hzL'⟩ with hz₀
  have hz₀2 : z₀ * z₀ = 1 := by
    have h : (⟨z, hzL'⟩ : CFSG.conjugate L g) * ⟨z, hzL'⟩ = 1 := Subtype.ext hzz
    rw [hz₀, ← map_mul, h, map_one]
  obtain ⟨k', P', c', hc'⟩ := exists_conj_eq_elt hz₀2
  set e'₁ := e₀.trans (MulAut.conj c') with he'₁
  have he'₁z : e'₁ ⟨z, hzL'⟩ = P'.elt K := by
    rw [he'₁, MulEquiv.trans_apply, MulAut.conj_apply, ← hz₀, hc']
  have he'₁symm : ((e'₁.symm (P'.elt K) : CFSG.conjugate L g) : G) = z := by
    rw [← he'₁z, MulEquiv.symm_apply_apply]
  have hΛ : (perfectCore (centralizer ({(pairPlacement hab).elt K} :
      Set (projectiveSL n K)))).map (L.subtype.comp e.symm.toMonoidHom) =
      (perfectCore (centralizer ({P'.elt K} : Set (projectiveSL n K)))).map
        ((CFSG.conjugate L g).subtype.comp e'₁.symm.toMonoidHom) := by
    rw [pairPlacement_elt, ← modelToG_eq_map, ← modelToG_eq_map, modelToG_perfectCore_centralizer,
      modelToG_perfectCore_centralizer, he'₁symm, hΛeq]
  have hk' : 0 < k' := by
    rcases Nat.eq_zero_or_pos k' with h0 | h
    · exfalso
      have h1 : z = 1 := by
        rw [← he'₁symm, P'.elt_eq_one_of_eq_zero h0, map_one]
        rfl
      apply proj_transvection_ne_one (K := K) hab one_ne_zero
      apply e.symm.injective
      apply Subtype.ext
      rw [map_one]
      exact h1
    · exact h
  have hJ2 : 2 ≤ (pairPlacement hab).free.card := by
    rw [pairPlacement_free]
    exact two_le_card_compl_pair hn hab
  have hJ'2 := two_le_card_free_of_map_perfectCore_eq hq hn (subtype_comp_symm_injective e)
    (subtype_comp_symm_injective e'₁) (pairPlacement hab) P' one_pos hJ2 hΛ
  have hcard := card_free_eq_of_map_perfectCore_eq hq (subtype_comp_symm_injective e)
    (subtype_comp_symm_injective e'₁) (pairPlacement hab) P' one_pos hk' hJ2 hJ'2 hΛ
  have hk'1 : k' = 1 := by
    have h1 := (pairPlacement hab).card_free
    have h2 := P'.card_free
    omega
  subst hk'1
  obtain ⟨c₂, hc₂⟩ := exists_conj_xab_eq_xab (P'.u_ne_w 0 0) hab (1 : K)
  have hP' : P'.elt K = xab (P'.u_ne_w 0 0) 1 := by
    rw [InvPlacement.elt, P'.mat_eq_transvection]
    rfl
  refine ⟨e'₁.trans (MulAut.conj c₂), ?_⟩
  have h1 : (e'₁.trans (MulAut.conj c₂)) ⟨z, hzL'⟩ = xab hab 1 := by
    rw [MulEquiv.trans_apply, he'₁z, hP', MulAut.conj_apply, hc₂]
  rw [← h1, MulEquiv.symm_apply_apply]

theorem exists_coords_blockScalar (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    (hκ : ∃ κ : Kˣ, κ ^ n ≠ 1) (e : L ≃* projectiveSL n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b) {g : G}
    (hg : g⁻¹ * t * g = t * ((e.symm (xab hab 1) : L) : G)) :
    ∃ e' : CFSG.conjugate L g ≃* projectiveSL n K,
      ((e'.symm (xab hab 1) : CFSG.conjugate L g) : G) = ((e.symm (xab hab 1) : L) : G) ∧
      (∀ y ∈ modelToG e (pairTorus (K := K) a b), ∃ (D : GL (Fin n) K) (l ν : K),
        (D : Matrix (Fin n) (Fin n) K) = pairDiag a b l ν ∧
        ∀ p, ((e'.symm (conjAut n K D p) : CFSG.conjugate L g) : G) =
          y * ((e'.symm p : CFSG.conjugate L g) : G) * y⁻¹) ∧
      modelToG e (blockSL ({a, b}ᶜ : Finset (Fin n))) =
        modelToG e' (blockSL ({a, b}ᶜ : Finset (Fin n))) ∧
      perfectCore (CFSG.conjugate L g ⊓
          centralizer (modelToG e (pairTorus (K := K) a b) : Set G)) =
        modelToG e' (blockSL ({a, b} : Finset (Fin n))) ⊔
          modelToG e (blockSL ({a, b}ᶜ : Finset (Fin n))) := by
  obtain ⟨e₁, he₁⟩ := exists_conjugate_chart_xab hset hOut hq hn e htC ht hab hg
  have hφinj := subtype_comp_symm_injective e
  have hφ₁inj := subtype_comp_symm_injective e₁
  have hφ₁r := range_subtype_comp_symm e₁
  have hΛ : (perfectCore (centralizer ({xab hab 1} : Set (projectiveSL n K)))).map
      (L.subtype.comp e.symm.toMonoidHom) =
      (perfectCore (centralizer ({xab hab 1} : Set (projectiveSL n K)))).map
        ((CFSG.conjugate L g).subtype.comp e₁.symm.toMonoidHom) := by
    rw [← modelToG_eq_map, ← modelToG_eq_map, modelToG_perfectCore_centralizer,
      modelToG_perfectCore_centralizer, he₁,
      perfectCore_inf_centralizer_xab_eq hset hOut e htC ht hab hg]
  have hY : (pairTorus (K := K) a b).map (L.subtype.comp e.symm.toMonoidHom) ≤
      normalizer (((CFSG.conjugate L g).subtype.comp e₁.symm.toMonoidHom).range : Set G) := by
    rw [hφ₁r]
    rintro _ ⟨y, hy, rfl⟩
    refine centralizer_conj_le_normalizer_conjugate
      (centralizer_le_normalizer_of_standard hset.standard htC ht) g ?_
    rw [hg, mem_centralizer_singleton_iff]
    set w := (L.subtype.comp e.symm.toMonoidHom) y with hw
    have h1 : w * t = t * w := mem_centralizer_iff.1 htC w (e.symm y).2
    have h2 : w * ((e.symm (xab hab 1) : L) : G) = ((e.symm (xab hab 1) : L) : G) * w := by
      have h := mem_centralizer_singleton_iff.1 (pairTorus_le_centralizer_xab hab 1 hy)
      have h' := congrArg (L.subtype.comp e.symm.toMonoidHom) h
      rwa [map_mul, map_mul] at h'
    calc w * (t * ((e.symm (xab hab 1) : L) : G))
        = (w * t) * ((e.symm (xab hab 1) : L) : G) := by group
      _ = t * (w * ((e.symm (xab hab 1) : L) : G)) := by rw [h1]; group
      _ = t * ((e.symm (xab hab 1) : L) : G) * w := by rw [h2]; group
  obtain ⟨φ'', hφ'', hrange, hz'', hact, hBeq, hcore⟩ :=
    exists_coords_blockScalar_of_map hq hn hκ hab hφinj hφ₁inj hΛ hY
  set e' := chartOfInjective hφ'' (hrange.trans hφ₁r) with he'
  refine ⟨e', ?_, ?_, ?_, ?_⟩
  · rw [coe_chartOfInjective_symm, hz'', ← he₁]
    rfl
  · intro y hy
    rw [modelToG_eq_map] at hy
    obtain ⟨D, l, ν, hD, hA⟩ := hact y hy
    refine ⟨D, l, ν, hD, fun p => ?_⟩
    rw [coe_chartOfInjective_symm, coe_chartOfInjective_symm]
    exact hA p
  · rw [modelToG_chartOfInjective, modelToG_eq_map, hBeq]
  · rw [modelToG_chartOfInjective, modelToG_eq_map, modelToG_eq_map, ← hcore, hφ₁r]

end Setting

end CFSG.SeitzReduction.LinearPilot

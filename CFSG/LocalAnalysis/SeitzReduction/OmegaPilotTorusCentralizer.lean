module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTori

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap
open scoped commutatorElement
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)

section Commute

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] {a b : ι}

theorem units_inv_ne_self [CharP K 2] {c₀ : Kˣ} (hc₀ : c₀ ≠ 1) : ((c₀⁻¹ : Kˣ) : K) ≠ c₀ := by
  intro h
  apply hc₀
  apply Units.ext
  apply eq_one_of_mul_self_eq_one
  calc (c₀ : K) * c₀ = ((c₀⁻¹ : Kˣ) : K) * c₀ := by rw [h]
    _ = 1 := by simp

theorem units_val_ne_one {c₀ : Kˣ} (hc₀ : c₀ ≠ 1) : (c₀ : K) ≠ 1 := fun h =>
  hc₀ (Units.ext h)

theorem units_inv_val_ne_one {c₀ : Kˣ} (hc₀ : c₀ ≠ 1) : ((c₀⁻¹ : Kˣ) : K) ≠ 1 := fun h =>
  hc₀ (inv_eq_one.mp (Units.ext h))

theorem eq_zero_of_torusLin_eq_smul {c₀ : Kˣ} {μ : K} {w : ι → K}
    (hw : torusLin a b c₀ w = μ • w) {i : ι} (hi : (torusEntry a b c₀ i : K) ≠ μ) : w i = 0 := by
  have h := congrFun hw i
  rw [torusLin_apply, Pi.smul_apply, smul_eq_mul] at h
  have h' : ((torusEntry a b c₀ i : K) - μ) * w i = 0 := by linear_combination h
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hi)

theorem torusLin_eq_self_of {p : ι → K} (hpa : p a = 0) (hpb : p b = 0) (c : Kˣ) :
    torusLin a b c p = p := by
  ext i
  by_cases hia : i = a
  · subst hia
    rw [torusLin_apply_left, hpa, mul_zero]
  · by_cases hib : i = b
    · subst hib
      rw [torusLin_apply, hpb, mul_zero]
    · exact torusLin_apply_of_ne hia hib c p

theorem apply_of_commute_torusLin [CharP K 2] (hab : a ≠ b) {c₀ : Kˣ} (hc₀ : c₀ ≠ 1)
    {g : (ι → K) ≃ₗ[K] (ι → K)} (hg : g * torusLin a b c₀ = torusLin a b c₀ * g) :
    g (Pi.single a 1) = g (Pi.single a 1) a • Pi.single a 1 ∧
      g (Pi.single b 1) = g (Pi.single b 1) b • Pi.single b 1 ∧
      ∀ p : ι → K, p a = 0 → p b = 0 → g p a = 0 ∧ g p b = 0 := by
  have hcomm : ∀ x, torusLin a b c₀ (g x) = g (torusLin a b c₀ x) := fun x => by
    have := LinearEquiv.congr_fun hg x
    simp only [LinearEquiv.mul_apply] at this
    exact this.symm
  refine ⟨?_, ?_, fun p hpa hpb => ?_⟩
  · have hw : torusLin a b c₀ (g (Pi.single a 1)) = (c₀ : K) • g (Pi.single a 1) := by
      rw [hcomm, torusLin_single_left hab, map_smul]
    ext i
    by_cases hia : i = a
    · subst hia
      simp
    · have hne : (torusEntry a b c₀ i : K) ≠ c₀ := by
        by_cases hib : i = b
        · subst hib
          simp only [torusEntry, hia, ite_false, ite_true]
          exact units_inv_ne_self hc₀
        · simp only [torusEntry, hia, hib, ite_false, Units.val_one]
          exact (units_val_ne_one hc₀).symm
      rw [eq_zero_of_torusLin_eq_smul hw hne]
      simp [hia]
  · have hw : torusLin a b c₀ (g (Pi.single b 1)) = ((c₀⁻¹ : Kˣ) : K) • g (Pi.single b 1) := by
      rw [hcomm, torusLin_single_right hab, map_smul]
    ext i
    by_cases hib : i = b
    · subst hib
      simp
    · have hne : (torusEntry a b c₀ i : K) ≠ ((c₀⁻¹ : Kˣ) : K) := by
        by_cases hia : i = a
        · subst hia
          simp only [torusEntry, ite_true]
          exact (units_inv_ne_self hc₀).symm
        · simp only [torusEntry, hia, hib, ite_false, Units.val_one]
          exact (units_inv_val_ne_one hc₀).symm
      rw [eq_zero_of_torusLin_eq_smul hw hne]
      simp [hib]
  · have hw : torusLin a b c₀ (g p) = (1 : K) • g p := by
      rw [hcomm, torusLin_eq_self_of hpa hpb, one_smul]
    refine ⟨eq_zero_of_torusLin_eq_smul hw ?_, eq_zero_of_torusLin_eq_smul hw ?_⟩
    · simp only [torusEntry, ite_true]
      exact units_val_ne_one hc₀
    · simp only [torusEntry, hab.symm, ite_false, ite_true]
      exact units_inv_val_ne_one hc₀

variable {Q : QuadraticForm K (ι → K)}

theorem IsHypCoord.exists_torusLin_inv_mul_mem_stabSub [CharP K 2] (h : IsHypCoord Q a b)
    {c₀ : Kˣ} (hc₀ : c₀ ≠ 1) {g : (ι → K) ≃ₗ[K] (ι → K)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg : g * torusLin a b c₀ = torusLin a b c₀ * g) :
    ∃ α : Kˣ, (torusLin a b α)⁻¹ * g ∈ stabSub a b := by
  obtain ⟨hga, hgb, -⟩ := apply_of_commute_torusLin h.ne hc₀ hg
  set α' := g (Pi.single a 1) a with hα'
  set β' := g (Pi.single b 1) b with hβ'
  have hpol := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO
    (Pi.single a 1) (Pi.single b 1)
  rw [hga, hgb, polar_smul_left, polar_smul_right, h.polar_left] at hpol
  have hαβ : α' * β' = 1 := by simpa using hpol
  have hα0 : α' ≠ 0 := left_ne_zero_of_mul_eq_one hαβ
  refine ⟨Units.mk0 α' hα0, ?_, ?_⟩
  · rw [← map_inv, LinearEquiv.mul_apply, hga, map_smul, torusLin_single_left h.ne, smul_smul]
    have : α' * ((Units.mk0 α' hα0)⁻¹ : Kˣ) = 1 := by simp [hα0]
    rw [this, one_smul]
  · rw [← map_inv, LinearEquiv.mul_apply, hgb, map_smul, torusLin_single_right h.ne, smul_smul,
      inv_inv]
    have : β' * ((Units.mk0 α' hα0 : Kˣ) : K) = 1 := by
      rw [Units.val_mk0, mul_comm]
      exact hαβ
    rw [this, one_smul]

theorem IsHypCoord.apply_mem_perp_of_mem_stabSub (h : IsHypCoord Q a b)
    {g : (ι → K) ≃ₗ[K] (ι → K)} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg : g ∈ stabSub a b) {p : ι → K} (hpa : p a = 0) (hpb : p b = 0) :
    g p a = 0 ∧ g p b = 0 := by
  have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO (Pi.single a 1) p
  have h2 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO (Pi.single b 1) p
  rw [hg.1, h.polar_left, h.polar_left, hpb] at h1
  rw [hg.2, h.polar_right, h.polar_right, hpa] at h2
  exact ⟨h2, h1⟩

theorem IsHypCoord.commute_torusLin_of_mem_stabSub (h : IsHypCoord Q a b)
    {g : (ι → K) ≃ₗ[K] (ι → K)} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg : g ∈ stabSub a b) (c : Kˣ) : g * torusLin a b c = torusLin a b c * g := by
  ext v
  simp only [LinearEquiv.mul_apply]
  have hpa := perpPart_apply_left h.ne v
  have hpb := perpPart_apply_right h.ne v
  obtain ⟨hgpa, hgpb⟩ := h.apply_mem_perp_of_mem_stabSub hgO hg hpa hpb
  rw [eq_add_perpPart a b v]
  simp only [map_add, map_smul, hg.1, hg.2, torusLin_single_left h.ne,
    torusLin_single_right h.ne, torusLin_eq_self_of hpa hpb, torusLin_eq_self_of hgpa hgpb]


theorem commutator_mem_stabSub_of_commute [CharP K 2] (hab : a ≠ b) {c₀ : Kˣ} (hc₀ : c₀ ≠ 1)
    {g h : (ι → K) ≃ₗ[K] (ι → K)} (hg : g * torusLin a b c₀ = torusLin a b c₀ * g)
    (hh : h * torusLin a b c₀ = torusLin a b c₀ * h) : g * h * g⁻¹ * h⁻¹ ∈ stabSub a b := by
  have hinv : ∀ {f : (ι → K) ≃ₗ[K] (ι → K)}, f * torusLin a b c₀ = torusLin a b c₀ * f →
      f⁻¹ * torusLin a b c₀ = torusLin a b c₀ * f⁻¹ := fun {f} hf =>
    Commute.inv_left (a := f) (b := torusLin a b c₀) hf
  have key : ∀ x : ι → K, x ≠ 0 →
      (∀ f : (ι → K) ≃ₗ[K] (ι → K), f * torusLin a b c₀ = torusLin a b c₀ * f →
        ∃ μ : K, f x = μ • x) → (g * h * g⁻¹ * h⁻¹) x = x := by
    intro x hx hsc
    obtain ⟨μg, hμg⟩ := hsc g hg
    obtain ⟨μh, hμh⟩ := hsc h hh
    obtain ⟨μg', hμg'⟩ := hsc g⁻¹ (hinv hg)
    obtain ⟨μh', hμh'⟩ := hsc h⁻¹ (hinv hh)
    have hg1 : μg * μg' = 1 := by
      have h1 : x = (μg * μg') • x := by
        calc x = g (g⁻¹ x) := (g.apply_symm_apply x).symm
          _ = (μg * μg') • x := by rw [hμg', map_smul, hμg, smul_smul, mul_comm]
      have h2 : (1 - μg * μg') • x = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
      exact (sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hx)).symm
    have hh1 : μh * μh' = 1 := by
      have h1 : x = (μh * μh') • x := by
        calc x = h (h⁻¹ x) := (h.apply_symm_apply x).symm
          _ = (μh * μh') • x := by rw [hμh', map_smul, hμh, smul_smul, mul_comm]
      have h2 : (1 - μh * μh') • x = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
      exact (sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hx)).symm
    simp only [LinearEquiv.mul_apply, hμh', map_smul, hμg', hμh, hμg, smul_smul]
    convert one_smul K x using 2
    linear_combination (μh * μh') * hg1 + hh1
  refine ⟨key _ (by simp) fun f hf => ⟨_, (apply_of_commute_torusLin hab hc₀ hf).1⟩,
    key _ (by simp) fun f hf => ⟨_, (apply_of_commute_torusLin hab hc₀ hf).2.1⟩⟩

end Commute

section ProjCentralizer

variable {K : Type*} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {a b : Fin d}

theorem exists_units_ne_one [Finite K] (hq : 3 ≤ Nat.card K) : ∃ c₀ : Kˣ, c₀ ≠ 1 := by
  have h1 : 1 < Nat.card Kˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp h1
  exact exists_ne 1

theorem IsHypCoord.commute_of_projHom_mem_centralizer [Finite K] [CharP K 2]
    (h : IsHypCoord Q a b) {g : orthDerived Q}
    (hg : projHom Q g ∈ centralizer (pairTorusOf Q a b : Set (matrixProjectiveDerived Q)))
    (c : Kˣ) : (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) * torusLin a b c = torusLin a b c * g := by
  set t : orthDerived Q := ⟨torusLin a b c, h.torusLin_mem_orthDerived c⟩
  have ht : projHom Q t ∈ pairTorusOf Q a b := ⟨t, ⟨c, rfl⟩, rfl⟩
  have hcomm := mem_centralizer_iff.mp hg _ ht
  rw [← map_mul, ← map_mul] at hcomm
  exact (congrArg Subtype.val (projHom_injective h.exists_ne_zero hcomm)).symm

theorem IsHypCoord.centralizer_pairTorusOf [Finite K] [CharP K 2] (h : IsHypCoord Q a b)
    (hq : 4 ≤ Nat.card K) :
    centralizer (pairTorusOf Q a b : Set (matrixProjectiveDerived Q)) =
      pairTorusOf Q a b ⊔ pairPerpOf Q a b := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := projHom_surjective Q x
    obtain ⟨c₀, hc₀⟩ := exists_units_ne_one (K := K) (by omega)
    obtain ⟨α, hα⟩ := h.exists_torusLin_inv_mul_mem_stabSub hc₀
      (Subgroup.commutator_le_self _ g.2) (h.commute_of_projHom_mem_centralizer hx c₀)
    set tα : orthDerived Q := ⟨torusLin a b α, h.torusLin_mem_orthDerived α⟩
    have hg : g = tα * (tα⁻¹ * g) := by group
    rw [hg, map_mul]
    exact mul_mem_sup ⟨tα, ⟨α, rfl⟩, rfl⟩ ⟨tα⁻¹ * g, hα, rfl⟩
  · rw [sup_le_iff]
    constructor
    · rintro _ ⟨y, ⟨c, hc⟩, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨z, ⟨c', hc'⟩, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      change (z : (Fin d → K) ≃ₗ[K] (Fin d → K)) * y = y * z
      have hc1 : torusLin a b c = (y : (Fin d → K) ≃ₗ[K] (Fin d → K)) := hc
      have hc2 : torusLin a b c' = (z : (Fin d → K) ≃ₗ[K] (Fin d → K)) := hc'
      rw [← hc1, ← hc2, ← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨y, hy, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨z, ⟨c', hc'⟩, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      change (z : (Fin d → K) ≃ₗ[K] (Fin d → K)) * y = y * z
      have hc2 : torusLin a b c' = (z : (Fin d → K) ≃ₗ[K] (Fin d → K)) := hc'
      rw [← hc2]
      exact (h.commute_torusLin_of_mem_stabSub (Subgroup.commutator_le_self _ y.2) hy c').symm

theorem IsHypCoord.commutator_mem_pairPerpOf [Finite K] [CharP K 2] (h : IsHypCoord Q a b)
    (hq : 4 ≤ Nat.card K) {x y : matrixProjectiveDerived Q}
    (hx : x ∈ centralizer (pairTorusOf Q a b : Set (matrixProjectiveDerived Q)))
    (hy : y ∈ centralizer (pairTorusOf Q a b : Set (matrixProjectiveDerived Q))) :
    x * y * x⁻¹ * y⁻¹ ∈ pairPerpOf Q a b := by
  obtain ⟨g, rfl⟩ := projHom_surjective Q x
  obtain ⟨g', rfl⟩ := projHom_surjective Q y
  obtain ⟨c₀, hc₀⟩ := exists_units_ne_one (K := K) (by omega)
  refine ⟨g * g' * g⁻¹ * g'⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  exact commutator_mem_stabSub_of_commute h.ne hc₀ (h.commute_of_projHom_mem_centralizer hx c₀)
    (h.commute_of_projHom_mem_centralizer hy c₀)

theorem IsHypCoord.pairPerpOf_le_centralizer [Finite K] [CharP K 2] (h : IsHypCoord Q a b)
    (hq : 4 ≤ Nat.card K) :
    pairPerpOf Q a b ≤ centralizer (pairTorusOf Q a b : Set (matrixProjectiveDerived Q)) := by
  rw [h.centralizer_pairTorusOf hq]
  exact le_sup_right

end ProjCentralizer

end CFSG.SeitzReduction.OmegaPilot

module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscP1Nine3
public import CFSG.ClassicalInvolution.Asc77.AscT8Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3 CFSG.ClassicalInvolution.Asc77.T8

namespace T8R

section Pure

variable {Γ : Type} [Group Γ]

theorem braid_conj_gen {a b : Γ} (ha : a * a = 1) (hb : b * b = 1) (h3 : (a * b) ^ 3 = 1) :
    a * b * a * b⁻¹ * a⁻¹ = b := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h3' : a * b * a * b * a * b = 1 := by
    have : (a * b) ^ 3 = a * b * a * b * a * b := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rwa [this] at h3
  rw [hai, hbi]
  calc a * b * a * b * a = (a * b * a * b * a * b) * b⁻¹ := by group
    _ = b := by rw [h3', one_mul, hbi]

end Pure

section Core

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G} {z t zM : G}

theorem extraTrans_core (hcl : ConjInvariant Ω) (ρK ρM : Rep Ω W) (hzMsq : zM * zM = 1)
    (hsz : ρM.r * z * ρM.r⁻¹ = zM * z) (hst : ρM.r * t * ρM.r⁻¹ = zM * t)
    (hzzM : zM * z = z * zM) (hrC : ρK.r ∈ Subgroup.centralizer ({z * t} : Set G))
    (hr2 : ρK.r * ρK.r ∈ W) (hs2 : ρM.r * ρM.r ∈ W)
    (hcube : (piG W ρK.r * piG W ρM.r) ^ 3 = 1)
    (hKeq : ∀ ρ' : Rep Ω W, ρ'.img = ρM.img → ρ'.K = ρM.K) :
    ∃ c ∈ Subgroup.centralizer ({z * t} : Set G), conjSub c ρK.K = ρM.K := by
  have hsa : ρM.r * (z * t) * ρM.r⁻¹ = z * t := by
    calc ρM.r * (z * t) * ρM.r⁻¹ = (ρM.r * z * ρM.r⁻¹) * (ρM.r * t * ρM.r⁻¹) := by group
      _ = (zM * z) * (zM * t) := by rw [hsz, hst]
      _ = (z * zM) * (zM * t) := by rw [hzzM]
      _ = z * (zM * zM) * t := by group
      _ = z * t := by rw [hzMsq]; group
  have hsC : ρM.r ∈ Subgroup.centralizer ({z * t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ρM.r * (z * t) = (ρM.r * (z * t) * ρM.r⁻¹) * ρM.r := by group
      _ = (z * t) * ρM.r := by rw [hsa]
  set r := ρK.r with hrdef
  set s := ρM.r with hsdef
  have hcC : r * s * r⁻¹ ∈ Subgroup.centralizer ({z * t} : Set G) :=
    (Subgroup.centralizer ({z * t} : Set G)).mul_mem
      ((Subgroup.centralizer ({z * t} : Set G)).mul_mem hrC hsC)
      ((Subgroup.centralizer ({z * t} : Set G)).inv_mem hrC)
  refine ⟨r * s * r⁻¹, hcC, ?_⟩
  have hrN : r ∈ Subgroup.normalizer (W : Set G) := ρK.r_mem_normalizer
  have hsN : s ∈ Subgroup.normalizer (W : Set G) := ρM.r_mem_normalizer
  have hcN : r * s * r⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    (Subgroup.normalizer (W : Set G)).mul_mem ((Subgroup.normalizer (W : Set G)).mul_mem hrN hsN)
      ((Subgroup.normalizer (W : Set G)).inv_mem hrN)
  set c := r * s * r⁻¹ with hcdef
  have hRle : conjSub c ρK.R ≤ Subgroup.normalizer (W : Set G) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : c⁻¹ * x * c ∈ Subgroup.normalizer (W : Set G) := ρK.hR.2 hx
    have h2 := (Subgroup.normalizer (W : Set G)).mul_mem
      ((Subgroup.normalizer (W : Set G)).mul_mem hcN h1)
      ((Subgroup.normalizer (W : Set G)).inv_mem hcN)
    simpa [mul_assoc] using h2
  let ρ' : Rep Ω W :=
    { K := conjSub c ρK.K
      R := conjSub c ρK.R
      r := c * r * c⁻¹
      hK := hcl c ρK.K ρK.hK
      hR := ⟨RSet.conj hcl ρK.hR.1 c, hRle⟩
      hRK := ρK.hRK.conj c
      hr := conj_mem_conjSub ρK.hr
      hrW := fun h => ρK.hrW (by
        have h1 : c⁻¹ * (c * r * c⁻¹) * c⁻¹⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (W : Set G)).inv_mem hcN) _).mp h
        simpa [mul_assoc] using h1) }
  have ha1 : piG W r * piG W r = 1 := by
    rw [← piG_mul hrN hrN]
    exact piG_of_mem_sup (Subgroup.mem_sup_left hr2)
  have hb1 : piG W s * piG W s = 1 := by
    rw [← piG_mul hsN hsN]
    exact piG_of_mem_sup (Subgroup.mem_sup_left hs2)
  have himg : ρ'.img = ρM.img := by
    show piG W (c * r * c⁻¹) = piG W s
    rw [piG_mul ((Subgroup.normalizer (W : Set G)).mul_mem hcN hrN)
        ((Subgroup.normalizer (W : Set G)).inv_mem hcN),
      piG_mul hcN hrN, piG_inv hcN, hcdef,
      piG_mul ((Subgroup.normalizer (W : Set G)).mul_mem hrN hsN)
        ((Subgroup.normalizer (W : Set G)).inv_mem hrN), piG_mul hrN hsN, piG_inv hrN]
    have hb := braid_conj_gen ha1 hb1 hcube
    calc piG W r * piG W s * (piG W r)⁻¹ * piG W r * (piG W r * piG W s * (piG W r)⁻¹)⁻¹
        = piG W r * piG W s * piG W r * (piG W s)⁻¹ * (piG W r)⁻¹ := by group
      _ = piG W s := hb
  exact hKeq ρ' himg

end Core

end T8R

end CFSG.ClassicalInvolution.Asc77

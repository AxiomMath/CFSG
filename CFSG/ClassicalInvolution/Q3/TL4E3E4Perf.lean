module

public import CFSG.ClassicalInvolution.Q3.TL4E3E4Sec
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Red
import CFSG.ClassicalInvolution.Q3.TL4Q8HomEng

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.Blueprint
open QuaternionGroup

theorem E3.q8_hom_eq_one_of_aut3 {A : Type*} [CommGroup A] (f : QuaternionGroup 2 →* A)
    {φ : MulAut (QuaternionGroup 2)} (h3 : φ ^ 3 = 1) (h1 : φ ≠ 1)
    (hf : ∀ y, f (φ y) = f y) (y : QuaternionGroup 2) : f y = 1 :=
  CFSG.ClassicalInvolution.Q3.TL4.E3.q8_hom_eq_one_of_aut3_gen f h3 h1 hf y

section Cit3


theorem tightE4Perfect_of_acts3 (hA : ∀ (M : Type) [Group M] [Finite M],
    PhilipHall.QuaternionBridge.ExLie M → ∀ (K : Subgroup M) (s : M), QuatTwinDatum K s →
      ∃ x : M, x ^ 3 = 1 ∧ conjSub x K = K ∧ ∃ k ∈ K, x * k ≠ k * x) :
    TightE4Perfect := by
  intro X _ _ R S t hd hc hO2 hE4
  obtain ⟨-, -, -, -, -, -, hZ, -, hM⟩ := E3.e4_center hd hc hO2 hE4
  have hQ := Vtx.quatTwinDatum_quot hd hc hO2 hZ hM
  obtain ⟨xb, hx3, hxK, kb, hkb, hne⟩ := hA (X ⧸ Subgroup.center X) hM _ _ hQ
  have hZ2 : IsPGroup 2 ↥(Subgroup.center X) := Vtx.isPGroup_center_of_oddFree hc.2.2
  have htZ : t ∉ Subgroup.center X := Vtx.not_mem_center_of_not_tightInO2 hd.order hO2
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) xb
  have hx3Z : x₀ ^ 3 ∈ Subgroup.center X := by
    have h : QuotientGroup.mk' (Subgroup.center X) (x₀ ^ 3) = 1 := by rw [map_pow]; exact hx3
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  obtain ⟨m, hm⟩ := hZ2 ⟨x₀ ^ 3, hx3Z⟩
  have hm' : (x₀ ^ 3) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have h4 : (4 : ℕ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
  have hxx : (x₀ ^ 4 ^ m) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, h4, pow_mul, hm', one_pow]
  have hπx : QuotientGroup.mk' (Subgroup.center X) (x₀ ^ 4 ^ m) =
      QuotientGroup.mk' (Subgroup.center X) x₀ := by
    rw [map_pow]
    have h41 : 4 ^ m % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    rw [← Nat.div_add_mod (4 ^ m) 3, h41, pow_add, pow_mul, hx3, one_pow, one_mul, pow_one]
  generalize hxdef : x₀ ^ 4 ^ m = x at hxx hπx
  have heq : QuotientGroup.mk' (Subgroup.center X) x * QuotientGroup.mk' (Subgroup.center X) t *
      (QuotientGroup.mk' (Subgroup.center X) x)⁻¹ = QuotientGroup.mk' (Subgroup.center X) t := by
    rw [hπx]
    have h1 := hQ.inv.conj (QuotientGroup.mk' (Subgroup.center X) x₀)
    rw [hxK] at h1
    exact h1.eq hQ.inv
  have hν : x * t * x⁻¹ * t⁻¹ ∈ Subgroup.center X := by
    have h : QuotientGroup.mk' (Subgroup.center X) (x * t * x⁻¹ * t⁻¹) = 1 := by
      simp only [map_mul, map_inv, heq, mul_inv_cancel]
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  generalize hνdef : x * t * x⁻¹ * t⁻¹ = ν at hν
  have hxt : x * t = ν * t * x := by rw [← hνdef]; group
  have hk : ∀ k : ℕ, x ^ k * t = ν ^ k * t * x ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hc' : x * ν ^ k = ν ^ k * x :=
        Subgroup.mem_center_iff.mp ((Subgroup.center X).pow_mem hν k) x
      calc x ^ (k + 1) * t = x * (x ^ k * t) := by rw [pow_succ', mul_assoc]
        _ = x * (ν ^ k * t * x ^ k) := by rw [ih]
        _ = ν ^ k * (x * t) * x ^ k := by
          rw [← mul_assoc, ← mul_assoc, hc']
          group
        _ = ν ^ (k + 1) * t * x ^ (k + 1) := by
          rw [hxt]
          group
  have hν3 : ν ^ 3 = 1 := by
    have h := hk 3
    rw [hxx, one_mul, mul_one] at h
    exact mul_eq_right.mp h.symm
  have hν1 : ν = 1 := by
    obtain ⟨j, hj⟩ := hZ2 ⟨ν, hν⟩
    have hj' : ν ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hd1 : orderOf ν ∣ Nat.gcd 3 (2 ^ j) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hν3) (orderOf_dvd_of_pow_eq_one hj')
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right j (by norm_num))] at hd1
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1)
  have hxC : x ∈ Subgroup.centralizer ({t} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [hxt, hν1, one_mul]
  have hxK0 : conjSub x (tightCore R) = tightCore R :=
    mem_normalizer_iff_conjSub_eq.mp (hd.le_normalizer_core hxC)
  obtain ⟨k, hk, rfl⟩ := hkb
  have hxk : x * k ≠ k * x := by
    intro h
    apply hne
    rw [← hπx, ← map_mul, ← map_mul, h]
  obtain ⟨eQ⟩ := hQ.q8
  have hKZ : tightCore R ⊓ Subgroup.center X = ⊥ :=
    PhilipHall.QuaternionBridge.core_inf_eq_bot hd hZ2 htZ
  let e : ↥(tightCore R) ≃* QuaternionGroup 2 := (AscQuot.quotRestrictEquiv hKZ).trans eQ
  let cK : ↥(tightCore R) ≃* ↥(tightCore R) :=
    ((MulAut.conj x).subgroupMap (tightCore R)).trans (MulEquiv.subgroupCongr hxK0)
  have hcK : ∀ y : ↥(tightCore R), ((cK y : ↥(tightCore R)) : X) = x * y * x⁻¹ := fun y => rfl
  let φ : MulAut (QuaternionGroup 2) := e.symm.trans (cK.trans e)
  have hφ : ∀ y, e.symm (φ y) = cK (e.symm y) := fun y => by
    simp [φ]
  have hφ3 : φ ^ 3 = 1 := by
    ext y
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply]
    apply e.symm.injective
    apply Subtype.ext
    rw [hφ, hcK, hφ, hcK, hφ, hcK]
    calc x * (x * (x * ((e.symm y : ↥(tightCore R)) : X) * x⁻¹) * x⁻¹) * x⁻¹ =
        x * x * x * ((e.symm y : ↥(tightCore R)) : X) * (x * x * x)⁻¹ := by group
      _ = _ := by rw [← pow_three', hxx, one_mul, inv_one, mul_one]
  have hφ1 : φ ≠ 1 := by
    intro h
    apply hxk
    have h1 : e.symm (φ (e ⟨k, hk⟩)) = ⟨k, hk⟩ := by rw [h]; simp
    rw [hφ, MulEquiv.symm_apply_apply] at h1
    have h3 : x * k * x⁻¹ = k := by
      have := congrArg Subtype.val h1
      rwa [hcK] at this
    calc x * k = x * k * x⁻¹ * x := by group
      _ = k * x := by rw [h3]
  let f : QuaternionGroup 2 →* Abelianization X :=
    Abelianization.of.comp ((tightCore R).subtype.comp e.symm.toMonoidHom)
  have hf : ∀ y, f (φ y) = f y := by
    intro y
    simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
    rw [hφ, hcK, map_mul, map_mul, map_inv, mul_comm (Abelianization.of x), mul_assoc,
      mul_inv_cancel, mul_one]
  have hall := E3.q8_hom_eq_one_of_aut3 f hφ3 hφ1 hf
  have hKle : tightCore R ≤ commutator X := by
    intro y hy
    have h := hall (e ⟨y, hy⟩)
    simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype] at h
    rwa [← MonoidHom.mem_ker, Abelianization.ker_of] at h
  rw [eq_top_iff, ← hc.2.1]
  refine iSup_le fun g => ?_
  rintro _ ⟨y, hy, rfl⟩
  exact (inferInstance : (commutator X).Normal).conj_mem y (hKle hy) g

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4

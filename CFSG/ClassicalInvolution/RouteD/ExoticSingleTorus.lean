module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Steinberg.Minuscule.BruhatExtras
public import CFSG.LieType.TitsSimplicity.Core

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule

section Torus

variable (F : Type) [Field F]

theorem hm_comm (i j : Fin (Tag.rank .E6)) (s t : Fˣ) :
    e6Data_valid.hm F i s * e6Data_valid.hm F j t = e6Data_valid.hm F j t * e6Data_valid.hm F i s :=
  e6Data_valid.endo_injective F (by
    rw [e6Data_valid.endo_mul, e6Data_valid.endo_mul, e6Data_valid.endo_hm,
      e6Data_valid.endo_hm]
    exact diagOp_comm _ _)

noncomputable def torusProd : (Fin (Tag.rank .E6) → Fˣ) →* e6Data_valid.minGroup F :=
  MonoidHom.noncommPiCoprod (fun i => e6Data_valid.hHom F i) (fun i j _ x y => hm_comm F i j x y)

theorem range_torusProd : (torusProd F).range = ⨆ i, e6Data_valid.torus F i :=
  MonoidHom.noncommPiCoprod_range (fun i => e6Data_valid.hHom F i)

def rootChar (γ : Fin (Tag.rank .E6) → ℤ) (t : Fin (Tag.rank .E6) → Fˣ) : Fˣ :=
  ∏ i, t i ^ MinData.toWeight γ i

theorem rootChar_mul (γ : Fin (Tag.rank .E6) → ℤ) (s t : Fin (Tag.rank .E6) → Fˣ) :
    rootChar F γ (s * t) = rootChar F γ s * rootChar F γ t := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem rootChar_one (γ : Fin (Tag.rank .E6) → ℤ) : rootChar F γ 1 = 1 := by
  simp [rootChar]

theorem rootChar_mulSingle (γ : Fin (Tag.rank .E6) → ℤ) (i : Fin (Tag.rank .E6)) (x : Fˣ) :
    rootChar F γ (Pi.mulSingle i x) = x ^ MinData.toWeight γ i := by
  classical
  unfold rootChar
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.mulSingle_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem torusProd_mulSingle (i : Fin (Tag.rank .E6)) (x : Fˣ) :
    torusProd F (Pi.mulSingle i x) = e6Data_valid.hm F i x :=
  MonoidHom.noncommPiCoprod_mulSingle (fun i => e6Data_valid.hHom F i) i x

theorem torusProd_conj_xm {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (t : Fin (Tag.rank .E6) → Fˣ) (c : F) :
    torusProd F t * e6Data_valid.xm F γ c * (torusProd F t)⁻¹ =
      e6Data_valid.xm F γ (((rootChar F γ t : Fˣ) : F) * c) := by
  classical
  have key : ∀ t : Fin (Tag.rank .E6) → Fˣ, ∀ c : F,
      torusProd F t * e6Data_valid.xm F γ c * (torusProd F t)⁻¹ =
        e6Data_valid.xm F γ (((rootChar F γ t : Fˣ) : F) * c) := by
    intro t
    rw [← Finset.univ_prod_mulSingle t]
    refine Finset.prod_induction (fun i => Pi.mulSingle i (t i))
      (fun t => ∀ c : F, torusProd F t * e6Data_valid.xm F γ c * (torusProd F t)⁻¹ =
        e6Data_valid.xm F γ (((rootChar F γ t : Fˣ) : F) * c)) ?_ ?_ ?_
    · intro s t hs ht c
      rw [map_mul, mul_inv_rev, rootChar_mul]
      calc torusProd F s * torusProd F t * e6Data_valid.xm F γ c *
            ((torusProd F t)⁻¹ * (torusProd F s)⁻¹)
          = torusProd F s * (torusProd F t * e6Data_valid.xm F γ c * (torusProd F t)⁻¹) *
              (torusProd F s)⁻¹ := by group
        _ = e6Data_valid.xm F γ (((rootChar F γ s * rootChar F γ t : Fˣ) : F) * c) := by
          rw [ht c, hs, Units.val_mul, mul_assoc]
    · intro c
      simp [rootChar_one]
    · intro i _ c
      rw [rootChar_mulSingle, torusProd_mulSingle]
      exact e6Data_valid.hm_conj_xm F hγ i (t i) c
  exact key t c

def invThree : Fin (Tag.rank .E6) → Fin (Tag.rank .E6) → ℤ :=
  ![![4, 3, 5, 6, 4, 2], ![3, 6, 6, 9, 6, 3], ![5, 6, 10, 12, 8, 4], ![6, 9, 12, 18, 12, 6],
    ![4, 6, 8, 12, 10, 5], ![2, 3, 4, 6, 5, 4]]

theorem cartan_mul_invThree (i k : Fin (Tag.rank .E6)) :
    ∑ j : Fin (Tag.rank .E6), Tag.cartan .E6 i j * invThree j k = if i = k then 3 else 0 := by
  revert i k
  decide

theorem three_smul_eq_zero {M : Type*} [AddCommGroup M] (u : Fin (Tag.rank .E6) → M)
    (h : ∀ j, ∑ i, Tag.cartan .E6 i j • u i = 0) (k : Fin (Tag.rank .E6)) : (3 : ℤ) • u k = 0 := by
  calc (3 : ℤ) • u k = ∑ i, (if i = k then (3 : ℤ) else 0) • u i := by
        simp [ite_smul]
    _ = ∑ i, (∑ j, Tag.cartan .E6 i j * invThree j k) • u i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [cartan_mul_invThree]
    _ = ∑ i, ∑ j, (Tag.cartan .E6 i j * invThree j k) • u i := by
        simp only [Finset.sum_smul]
    _ = ∑ j, ∑ i, (Tag.cartan .E6 i j * invThree j k) • u i := Finset.sum_comm
    _ = ∑ j, invThree j k • ∑ i, Tag.cartan .E6 i j • u i := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_comm, mul_smul]
    _ = 0 := by simp [h]

theorem torusProd_pow_three {t : Fin (Tag.rank .E6) → Fˣ}
    (hχ : ∀ j, rootChar F (Pi.single j 1) t = 1) : torusProd F t ^ 3 = 1 := by
  have hχ' : ∀ j, ∏ i, t i ^ Tag.cartan .E6 i j = 1 := fun j => by
    simpa [rootChar, MinData.toWeight_single] using hχ j
  have ht3 : ∀ k, t k ^ 3 = 1 := by
    intro k
    have h := three_smul_eq_zero (fun i => Additive.ofMul (t i)) (fun j => by
      have := congrArg Additive.ofMul (hχ' j)
      simpa [ofMul_prod, ofMul_zpow] using this) k
    have h' : Additive.ofMul (t k ^ (3 : ℤ)) = 0 := by rw [ofMul_zpow]; exact h
    have h'' : t k ^ (3 : ℤ) = 1 := ofMul_eq_zero.mp h'
    simpa using h''
  have h3 : t ^ 3 = 1 := funext fun k => ht3 k
  rw [← map_pow, h3, map_one]

theorem pow_three_eq_one_of_torus {z : e6Data_valid.minGroup F}
    (hz : z ∈ ⨆ i, e6Data_valid.torus F i)
    (hc : ∀ j : Fin (Tag.rank .E6),
      z * e6Data_valid.xm F (Pi.single j 1) 1 * z⁻¹ = e6Data_valid.xm F (Pi.single j 1) 1) :
    z ^ 3 = 1 := by
  rw [← range_torusProd] at hz
  obtain ⟨t, rfl⟩ := hz
  refine torusProd_pow_three F fun j => ?_
  have h := torusProd_conj_xm F (isRoot_single .E6 j) t 1
  rw [hc j, mul_one] at h
  exact Units.ext (e6Data_valid.xm_injective F (isRoot_single .E6 j) h).symm

theorem center_le_iSup_torus {z : e6Data_valid.minGroup F}
    (hz : z ∈ Subgroup.center (e6Data_valid.minGroup F)) : z ∈ ⨆ i, e6Data_valid.torus F i := by
  have hct := e6Datum_isCTGroupDatum F
  have hext := e6Datum_steinbergExtras F
  have hBU := e6Datum_bruhatExtras F
  rw [CFSG.LieType.TitsSimplicity.center_eq_normalCore_borel hct hext hBU] at hz
  exact CFSG.LieType.TitsSimplicity.normalCore_borel_le_iSup hct hBU hz

theorem center_pow_three {z : e6Data_valid.minGroup F}
    (hz : z ∈ Subgroup.center (e6Data_valid.minGroup F)) : z ^ 3 = 1 := by
  refine pow_three_eq_one_of_torus F (center_le_iSup_torus F hz) fun j => ?_
  rw [mul_inv_eq_iff_eq_mul]
  exact (Subgroup.mem_center_iff.mp hz (e6Data_valid.xm F (Pi.single j 1) 1)).symm

end Torus

end CFSG.ClassicalInvolution.RouteD.Exotic

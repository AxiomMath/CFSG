module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0AutExtension
public import CFSG.Sporadic.SuzOddCore.SmallModel

public section

namespace CFSG.ComponentClassification.GS79bSec5

open Subgroup CFSG.ComponentClassification.AS81.SuzB0 CFSG.Sporadic.SuzOddCore

private noncomputable def conjM
    {c : Equiv.Perm (Fin 1782)} (hc : c ∈ suzT) : MulAut ↥suzM where
  toFun x := ⟨c * x * c⁻¹, suzT_conj_mem_suzM hc x.2⟩
  invFun x := ⟨c⁻¹ * x * c, by simpa only [inv_inv] using suzT_conj_mem_suzM (inv_mem hc) x.2⟩
  left_inv x := Subtype.ext (by
    show c⁻¹ * (c * (x : Equiv.Perm (Fin 1782)) * c⁻¹) * c = x
    group)
  right_inv x := Subtype.ext (by
    show c * (c⁻¹ * (x : Equiv.Perm (Fin 1782)) * c) * c⁻¹ = x
    group)
  map_mul' x y := Subtype.ext (by
    show c * ((x : Equiv.Perm (Fin 1782)) * y) * c⁻¹ =
      (c * (x : Equiv.Perm (Fin 1782)) * c⁻¹) * (c * (y : Equiv.Perm (Fin 1782)) * c⁻¹)
    group)

private theorem conjM_apply
    {c : Equiv.Perm (Fin 1782)} (hc : c ∈ suzT) (x : ↥suzM) :
    ((conjM hc x : ↥suzM) : Equiv.Perm (Fin 1782)) = c * x * c⁻¹ :=
  rfl

theorem exists_mulAut_of_suz_twoA_centralizer
    {S : Type} [Group S] [Finite S]
    (hS : CFSG.Blueprint.NativeSporadic.IsSporadic S .Suz)
    {d : S} (hd : orderOf d = 2)
    (hcard : Nat.card (Subgroup.centralizer ({d} : Set S)) = 3317760)
    (alpha : MulAut ↥(Subgroup.centralizer ({d} : Set S))) :
    ∃ beta : MulAut S, beta d = d ∧
      ∀ x : ↥(Subgroup.centralizer ({d} : Set S)), beta (x : S) = (alpha x : S) := by
  obtain ⟨e₀⟩ := hS
  obtain ⟨e⟩ : Nonempty (S ≃* ↥suzM) := ⟨e₀.trans suzEquivM⟩
  have hd' : orderOf ((e d : ↥suzM) : Equiv.Perm (Fin 1782)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hd]
  obtain ⟨c, hc, hct⟩ := suzM_involution_class (e d).2 hd'
  have hmap : ∀ t : Equiv.Perm (Fin 1782), c * t * c⁻¹ = (e d : Equiv.Perm (Fin 1782)) →
      ∃ φ : S →* Equiv.Perm (Fin 1782), Function.Injective φ ∧
        (∀ x, φ x = c⁻¹ * (e x : Equiv.Perm (Fin 1782)) * c) ∧
        (centralizer ({d} : Set S)).map φ = centM t := by
    intro t ht
    let φ : S →* Equiv.Perm (Fin 1782) :=
      { toFun := fun x => c⁻¹ * (e x : Equiv.Perm (Fin 1782)) * c
        map_one' := by simp
        map_mul' := fun x y => by
          simp only [map_mul, Subgroup.coe_mul]
          group }
    have hφ : ∀ x, φ x = c⁻¹ * (e x : Equiv.Perm (Fin 1782)) * c := fun _ => rfl
    have hinj : Function.Injective φ := by
      intro x y hxy
      rw [hφ, hφ, mul_left_inj, mul_right_inj] at hxy
      exact e.injective (Subtype.ext hxy)
    have hφd : φ d = t := by
      rw [hφ, ← ht]
      group
    refine ⟨φ, hinj, hφ, le_antisymm (fun y hy => ?_) (fun y hy => ?_)⟩
    · obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
      rw [centM, mem_inf]
      refine ⟨?_, ?_⟩
      · rw [mem_centralizer_singleton_iff] at hx ⊢
        rw [← hφd, ← map_mul, ← map_mul, hx]
      · rw [hφ]
        simpa only [inv_inv] using suzT_conj_mem_suzM (inv_mem hc) (e x).2
    · rw [centM, mem_inf] at hy
      obtain ⟨hyt, hyM⟩ := hy
      obtain ⟨x, hx⟩ := e.surjective ⟨c * y * c⁻¹, suzT_conj_mem_suzM hc hyM⟩
      have hφx : φ x = y := by
        rw [hφ, hx]
        show c⁻¹ * (c * y * c⁻¹) * c = y
        group
      refine mem_map.mpr ⟨x, ?_, hφx⟩
      rw [mem_centralizer_singleton_iff] at hyt ⊢
      apply hinj
      rw [map_mul, map_mul, hφx, hφd]
      exact hyt
  rcases hct with h0 | h1
  · exfalso
    obtain ⟨φ, hinj, -, hφC⟩ := hmap _ h0
    have h := Subgroup.card_map_of_injective (K := centralizer ({d} : Set S)) hinj
    rw [hφC, hcard, ← invE_eq_centM (by norm_num), card_invE (by norm_num)] at h
    norm_num [invInnerOrders] at h
  obtain ⟨φ, hinj, hφ, hφC⟩ := hmap _ h1
  rw [← invE_eq_centM (by norm_num)] at hφC
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ↥(centralizer ({d} : Set S)) ≃* ↥(invE 1),
      ∀ x, ((Ψ x : ↥(invE 1)) : Equiv.Perm (Fin 1782)) =
        c⁻¹ * (e x : Equiv.Perm (Fin 1782)) * c :=
    ⟨((centralizer ({d} : Set S)).equivMapOfInjective φ hinj).trans
      (MulEquiv.subgroupCongr hφC), fun x => hφ x⟩
  obtain ⟨g, hgT, hgt, hg⟩ := exists_suzT_of_mulAut_invE_one (Ψ.symm.trans (alpha.trans Ψ))
  have hkT : c * g * c⁻¹ ∈ suzT := mul_mem (mul_mem hc hgT) (inv_mem hc)
  refine ⟨e.trans ((conjM hkT).trans e.symm), ?_, fun x => ?_⟩
  · rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [conjM_apply, ← h1]
    calc c * g * c⁻¹ * (c * suzInv 1 * c⁻¹) * (c * g * c⁻¹)⁻¹
        = c * (g * suzInv 1) * g⁻¹ * c⁻¹ := by group
      _ = c * (suzInv 1 * g) * g⁻¹ * c⁻¹ := by rw [hgt]
      _ = c * suzInv 1 * c⁻¹ := by group
  · rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [conjM_apply]
    have h := hg (Ψ x)
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hΨ, hΨ] at h
    calc c * g * c⁻¹ * (e x : Equiv.Perm (Fin 1782)) * (c * g * c⁻¹)⁻¹
        = c * (g * (c⁻¹ * (e x : Equiv.Perm (Fin 1782)) * c) * g⁻¹) * c⁻¹ := by group
      _ = c * (c⁻¹ * (e (alpha x : S) : Equiv.Perm (Fin 1782)) * c) * c⁻¹ := by rw [h]
      _ = (e (alpha x : S) : Equiv.Perm (Fin 1782)) := by group

end CFSG.ComponentClassification.GS79bSec5

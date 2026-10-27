module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance

public section

namespace CFSG

open CFSG.Open

theorem mulAutConj_injective_of_center_eq_bot {S : Type*} [Group S]
    (hZ : Subgroup.center S = ⊥) : Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  rw [MonoidHom.mem_ker] at hz
  rw [← hZ, Subgroup.mem_center_iff]
  intro g
  have h := congrArg (fun φ : MulAut S => φ g) hz
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc g * z = z * g * z⁻¹ * z := by rw [h]
    _ = z * g := by group

theorem eqLocus_congr_map {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (α : MulAut G) :
    (((MulAut.congr e α : MulAut H) : H →* H).eqLocus (MonoidHom.id H)) =
      ((α : G →* G).eqLocus (MonoidHom.id G)).map (e : G →* H) := by
  ext x
  constructor
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change α (e.symm x) = e.symm x
    have h := congrArg e.symm hx
    simpa using h
  · rintro ⟨y, hy, rfl⟩
    change e (α (e.symm (e y))) = e y
    rw [e.symm_apply_apply]
    exact congrArg e hy

theorem innerAut_inf_centralizer_eq_map_eqLocus {S : Type*} [Group S]
    (hZ : Subgroup.center S = ⊥) (α : MulAut S) :
    CFSG.HardMathSupport.Solomon.LocalBalance.innerAut S ⊓
        Subgroup.centralizer ({α} : Set (MulAut S)) =
      ((α : S →* S).eqLocus (MonoidHom.id S)).map
        (MulAut.conj : S →* MulAut S) := by
  have hinj := mulAutConj_injective_of_center_eq_bot hZ
  apply le_antisymm
  · rintro φ ⟨⟨t, rfl⟩, hφ⟩
    refine Subgroup.mem_map.mpr ⟨t, ?_, rfl⟩
    have hcomm : MulAut.conj t * α = α * MulAut.conj t :=
      Subgroup.mem_centralizer_singleton_iff.mp hφ
    have hconj : MulAut.conj (α⁻¹ t) = MulAut.conj t := by
      have h1 : MulAut.conj (α⁻¹ t) = α⁻¹ * MulAut.conj t * α := by
        ext x
        simp [MulAut.mul_apply, MulAut.conj_apply]
      calc MulAut.conj (α⁻¹ t) = α⁻¹ * MulAut.conj t * α := h1
        _ = α⁻¹ * (MulAut.conj t * α) := by rw [mul_assoc]
        _ = α⁻¹ * (α * MulAut.conj t) := by rw [hcomm]
        _ = (α⁻¹ * α) * MulAut.conj t := by rw [mul_assoc]
        _ = MulAut.conj t := by rw [inv_mul_cancel, one_mul]
    have ht : α⁻¹ t = t := hinj hconj
    change (α : S →* S) t = (MonoidHom.id S) t
    simpa using (congrArg (fun x => α x) ht).symm
  · rintro φ ⟨t, ht, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨⟨t, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply]
    have ht' : α t = t := ht
    calc t * (α x) * t⁻¹ = α t * α x * (α t)⁻¹ := by rw [ht']
      _ = α (t * x * t⁻¹) := by rw [map_mul, map_mul, map_inv]

theorem innerAut_inf_centralizer_conj {S : Type*} [Group S]
    (hZ : Subgroup.center S = ⊥) (s : S) :
    CFSG.HardMathSupport.Solomon.LocalBalance.innerAut S ⊓
        Subgroup.centralizer ({MulAut.conj s} : Set (MulAut S)) =
      (Subgroup.centralizer ({s} : Set S)).map
        (MulAut.conj : S →* MulAut S) := by
  rw [innerAut_inf_centralizer_eq_map_eqLocus hZ]
  congr 1
  ext x
  change (MulAut.conj s : S →* S) x = (MonoidHom.id S) x ↔
    x ∈ Subgroup.centralizer ({s} : Set S)
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [MulAut.conj_apply, MonoidHom.id_apply]
  constructor
  · intro h
    have h'' : s * x * s⁻¹ = x := h
    have h' : s * x = x * s := by
      calc s * x = (s * x * s⁻¹) * s := by group
        _ = x * s := by rw [h'']
    exact h'.symm
  · intro h
    calc s * x * s⁻¹ = (x * s) * s⁻¹ := by rw [h.symm]
      _ = x := mul_inv_cancel_right _ _

theorem card_gLAPPrimeCoreOf_map_of_injective {G H : Type*} [Group G] [Group H]
    (p : ℕ) (f : G →* H) (hf : Function.Injective f) (K : Subgroup G) :
    Nat.card (GLAPPrimeCoreOf p (K.map f)) = Nat.card (GLAPPrimeCoreOf p K) := by
  change Nat.card ↥((pPrimeCore p ↥(K.map f)).map (K.map f).subtype) =
    Nat.card ↥((pPrimeCore p ↥K).map K.subtype)
  rw [Subgroup.card_map_of_injective (K.map f).subtype_injective,
    Subgroup.card_map_of_injective K.subtype_injective]
  let e : ↥K ≃* ↥(K.map f) := K.equivMapOfInjective f hf
  rw [← pPrimeCore_map_iso p e, Subgroup.card_map_of_injective e.injective]

theorem odd_card_gLAPPrimeCoreOf_innerAut_inf_centralizer_iff {S : Type*} [Group S]
    (hZ : Subgroup.center S = ⊥) (p : ℕ) (α : MulAut S) :
    Odd (Nat.card (GLAPPrimeCoreOf p
        (CFSG.HardMathSupport.Solomon.LocalBalance.innerAut S ⊓
          Subgroup.centralizer ({α} : Set (MulAut S))))) ↔
      Odd (Nat.card (GLAPPrimeCoreOf p
        ((α : S →* S).eqLocus (MonoidHom.id S)))) := by
  rw [innerAut_inf_centralizer_eq_map_eqLocus hZ,
    card_gLAPPrimeCoreOf_map_of_injective p _
      (mulAutConj_injective_of_center_eq_bot hZ)]

end CFSG

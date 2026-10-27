module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillMain
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillKer
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneMainBits
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneCoordsDefs
public import Mathlib

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

theorem enc6_inj {p p' : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)} (h : enc6 p = enc6 p') : p = p' := by
  have h0 : enc6 (p + p') = 0 := by rw [enc6_add, h, Nat.xor_self]
  have h1 : p + p' = 0 := (enc6_eq_zero _).1 h0
  have h2 : p' + p' = 0 := by
    ext i
    · exact CharTwo.add_self_eq_zero _
    · exact CharTwo.add_self_eq_zero _
  calc p = p + p' + p' := by rw [add_assoc, h2, add_zero]
    _ = p' := by rw [h1, zero_add]

section Bridge

variable {G : Type} [Group G] {Jh E₂ C₂ D : Subgroup G} {z : G}
  {lev : GL (Fin 3) (ZMod 2) →* G} {δν : G → Fin 3 → ZMod 2}
  {cV : G → (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)} {u : Bool}
  {cE : G → Matrix (Fin 3) (Fin 3) (ZMod 2)}

theorem cV_inv_of (hV : EpsOneVCoords Jh E₂ C₂ z lev δν cV) {x : G} (hx : x ∈ Jh) :
    cV x⁻¹ = cV x := by
  have h := hV.mul x hx x⁻¹ (inv_mem hx)
  rw [mul_inv_cancel, (hV.eq_zero 1 (one_mem _)).2 (one_mem _)] at h
  calc cV x⁻¹ = cV x + cV x + cV x⁻¹ := by
        rw [show cV x + cV x = 0 by ext i <;> exact CharTwo.add_self_eq_zero _, zero_add]
    _ = cV x := by rw [add_assoc, ← h, add_zero]

theorem killData_of_coords [Finite G] (hV : EpsOneVCoords Jh E₂ C₂ z lev δν cV)
    (hE : EpsOneECoords Jh E₂ cV u cE) (hEJ : E₂ ≤ Jh) (hJE : Jh ≤ centralizer (E₂ : Set G))
    (hsq : ∀ x ∈ Jh, x * x ∈ E₂) (hcomm : ∀ x ∈ Jh, ∀ y ∈ Jh, x⁻¹ * y⁻¹ * x * y ∈ E₂)
    (hcard : Nat.card Jh = 2 ^ 15) (hD : Jh ⊔ zpowers z = D) (hcardD : Nat.card D = 2 ^ 16)
    (hzJ : z ∈ normalizer (Jh : Set G)) (hz2 : z * z = 1)
    (hzE : ∀ e ∈ E₂, z * e * z⁻¹ ∈ E₂)
    (hker : ∀ x ∈ normalizer (Jh : Set G), x ∈ normalizer (D : Set G) →
      (∀ j ∈ Jh, x * j * x⁻¹ * j⁻¹ ∈ E₂) → x ∈ Jh)
    (hidx : ∀ K : Subgroup G, K.index = 2 → z ∈ K)
    (hC : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({z} : Set G) →
      Nat.card P ≤ 2 ^ 10) :
    KillData u Jh E₂ (fun x => enc6 (cV x)) (fun x => enc9 (cE x)) z (lev g₁) (lev g₂) := by
  have hcomm' : ∀ x ∈ Jh, ∀ y ∈ Jh, x * y * x⁻¹ * y⁻¹ ∈ E₂ := fun x hx y hy => by
    have := hcomm x⁻¹ (inv_mem hx) y⁻¹ (inv_mem hy)
    simpa using this
  have hzK : ∃ j ∈ Jh, z * j * z⁻¹ * j⁻¹ ∉ E₂ := by
    obtain ⟨j, hj, hjv⟩ := hV.surj (0, Pi.single 0 1)
    refine ⟨j, hj, fun hmem => ?_⟩
    have hzj : z * j * z⁻¹ ∈ Jh := (mem_normalizer_iff.1 hzJ j).1 hj
    have h0 := (hV.eq_zero _ (mul_mem hzj (inv_mem hj))).2 hmem
    rw [hV.mul _ hzj _ (inv_mem hj), hV.z_act j hj, cV_inv_of hV hj, hjv] at h0
    have := congrArg (fun p => p.1 0) h0
    simp at this
  refine
    { E_le := hEJ
      cV_lt := fun x _ => enc6_lt _
      cV_mul := fun x hx y hy => by
        show enc6 (cV (x * y)) = enc6 (cV x) ^^^ enc6 (cV y)
        rw [hV.mul x hx y hy, enc6_add]
      cV_eq_zero := fun x hx => by
        show enc6 (cV x) = 0 ↔ x ∈ E₂
        rw [enc6_eq_zero]
        exact hV.eq_zero x hx
      cV_surj := fun v hv => by
        obtain ⟨x, hx, hxv⟩ := hV.surj (dec3 (wpart v), dec3 (xpart v))
        exact ⟨x, hx, by show enc6 (cV x) = v; rw [hxv, enc6_surj hv]⟩
      cE_lt := fun x _ => enc9_lt _
      cE_mul := fun x hx y hy => by
        show enc9 (cE (x * y)) = enc9 (cE x) ^^^ enc9 (cE y)
        rw [hE.mul x hx y hy, enc9_add]
      cE_inj := fun x hx h0 => hE.inj x hx ((enc9_eq_zero _).1 h0)
      cE_surj := fun e he => by
        obtain ⟨x, hx, hxe⟩ := hE.surj (dec9 e)
        exact ⟨x, hx, by show enc9 (cE x) = e; rw [hxe, enc9_surj he]⟩
      sq := fun x hx => ⟨hsq x hx, by
        show enc9 (cE (x * x)) = qOf u (enc6 ((cV x).1, (cV x).2))
        rw [hE.sq x hx, qOf_enc6]
        rfl⟩
      central := fun e he x hx => mem_centralizer_iff.1 (hJE hx) e he
      z_norm := hzJ
      z_sq := hz2
      z_act := fun x hx => by
        show enc6 (cV (z * x * z⁻¹)) = evalV z0T (enc6 ((cV x).1, (cV x).2))
        rw [hV.z_act x hx, z0T_enc6]
      l₁_norm := hV.lev_mem g₁
      l₁_act := fun x hx => by
        show enc6 (cV (lev g₁ * x * (lev g₁)⁻¹)) = evalV lam1T (enc6 ((cV x).1, (cV x).2))
        rw [hV.lev_act g₁ x hx, lam1T_enc6]
      l₂_norm := hV.lev_mem g₂
      l₂_act := fun x hx => by
        show enc6 (cV (lev g₂ * x * (lev g₂)⁻¹)) = evalV lam2T (enc6 ((cV x).1, (cV x).2))
        rw [hV.lev_act g₂ x hx, lam2T_enc6]
      ker := fun P hP hPK => by
        have hle : P ≤ kerSub hEJ := fun x hx => by
          obtain ⟨hxN, hxv⟩ := hPK x hx
          refine ⟨hxN, fun j hj => ?_⟩
          have hxj : x * j * x⁻¹ ∈ Jh := (mem_normalizer_iff.1 hxN j).1 hj
          have heq : cV (x * j * x⁻¹) = cV j := enc6_inj (hxv j hj)
          refine (hV.eq_zero _ (mul_mem hxj (inv_mem hj))).1 ?_
          rw [hV.mul _ hxj _ (inv_mem hj), heq, cV_inv_of hV hj]
          ext i <;> exact CharTwo.add_self_eq_zero _
        have h := card_le_of_kernel hEJ hcomm' (IsPGroup.of_card hcard) hD
          (by rw [hcardD, hcard]; norm_num) hzJ hz2 hzE hzK hker hP hle
        rwa [hcard] at h
      index2 := hidx
      cent := hC }

theorem false_of_coords [Finite G]
    (hV : EpsOneVCoords Jh E₂ C₂ z lev δν cV)
    (hE : EpsOneECoords Jh E₂ cV u cE) (hEJ : E₂ ≤ Jh) (hJE : Jh ≤ centralizer (E₂ : Set G))
    (hsq : ∀ x ∈ Jh, x * x ∈ E₂) (hcomm : ∀ x ∈ Jh, ∀ y ∈ Jh, x⁻¹ * y⁻¹ * x * y ∈ E₂)
    (hcard : Nat.card Jh = 2 ^ 15) (hD : Jh ⊔ zpowers z = D) (hcardD : Nat.card D = 2 ^ 16)
    (hzJ : z ∈ normalizer (Jh : Set G)) (hz2 : z * z = 1)
    (hzE : ∀ e ∈ E₂, z * e * z⁻¹ ∈ E₂)
    (hker : ∀ x ∈ normalizer (Jh : Set G), x ∈ normalizer (D : Set G) →
      (∀ j ∈ Jh, x * j * x⁻¹ * j⁻¹ ∈ E₂) → x ∈ Jh)
    (hidx : ∀ K : Subgroup G, K.index = 2 → z ∈ K)
    (hC : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({z} : Set G) →
      Nat.card P ≤ 2 ^ 10) : False :=
  (killData_of_coords hV hE hEJ hJE hsq hcomm hcard hD hcardD hzJ hz2 hzE hker hidx
    hC).false_of_killData

end Bridge

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDKap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12InputsS8

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {V : Subgroup G}

namespace AddCoord

@[expose] noncomputable def s8dTw (K : AddCoord V) (T : (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ) :
    AddCoord V where
  Ψ := (s8dThetaE T).toEquiv.trans K.Ψ
  add p q := by
    show K.Ψ (s8dThetaE T (p + q)) = K.Ψ (s8dThetaE T p) * K.Ψ (s8dThetaE T q)
    rw [map_add, K.add]

theorem s8dTw_Ψ (K : AddCoord V) (T : (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ) (p : EvW × EvW) :
    (K.s8dTw T).Ψ p = K.Ψ (s8dAp (s8dTheta T) p) := rfl

theorem s8dKap_tw (K : AddCoord V) (T : (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ) (c : MulAut ↥V) :
    (K.s8dTw T).s8dKap c = (s8dTheta T)⁻¹ * K.s8dKap c * s8dTheta T := by
  refine AddCoord.s8dKap_eq _ fun p => ?_
  rw [s8dTw_Ψ, s8dTw_Ψ, ← K.s8dKap_spec c]
  congr 1
  rw [s8dAp_mul, s8dAp_mul, s8dAp_ap_inv]

end AddCoord

private theorem s8d_evW_add_self (w : EvW) : w + w = 0 := by
  have h : ∀ x : ZMod 2, x + x = 0 := by decide
  exact Subtype.ext (funext fun i => h (w.1 i))

private def s8dFac (K : AddCoord V) (ι : EvW → EvW × EvW)
    (hι : ∀ a b, ι (a + b) = ι a + ι b) (h0 : ι 0 = 0) : Subgroup ↥V where
  carrier := {x | ∃ w : EvW, K.Ψ (ι w) = x}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by rw [hι, K.add]⟩
  one_mem' := ⟨0, by rw [h0, K.zero]⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨a, (inv_eq_of_mul_eq_one_right ?_).symm⟩
    rw [← K.add, ← hι, s8d_evW_add_self, h0, K.zero]

theorem s8d_splitNat_of (K : AddCoord V) {Z : Subgroup (MulAut ↥V)}
    (ψ : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)) ≃* ↥Z)
    (hψ : ∀ x, K.s8dKap (ψ x) = s8dProdA x) : Sec128SplitNat V Z := by
  classical
  have hι1 : ∀ a b : EvW, ((a + b, 0) : EvW × EvW) = (a, 0) + (b, 0) := fun a b => by
    rw [Prod.mk_add_mk, add_zero]
  have hι2 : ∀ a b : EvW, ((0, a + b) : EvW × EvW) = (0, a) + (0, b) := fun a b => by
    rw [Prod.mk_add_mk, add_zero]
  let V1 := s8dFac K (fun w => (w, 0)) hι1 rfl
  let V2 := s8dFac K (fun w => (0, w)) hι2 rfl
  let φ1 : (Fin 5 → ZMod 2) → ↥V := fun v => if h : IsEvenVec v then K.Ψ (⟨v, h⟩, 0) else 1
  let φ2 : (Fin 5 → ZMod 2) → ↥V := fun v => if h : IsEvenVec v then K.Ψ (0, ⟨v, h⟩) else 1
  have hφ1 : ∀ v (h : IsEvenVec v), φ1 v = K.Ψ (⟨v, h⟩, 0) := fun v h => dif_pos h
  have hφ2 : ∀ v (h : IsEvenVec v), φ2 v = K.Ψ (0, ⟨v, h⟩) := fun v h => dif_pos h
  have hact : ∀ x p, ((ψ x : MulAut ↥V)) (K.Ψ p) = K.Ψ (s8dAp (s8dProdA x) p) := by
    intro x p
    rw [← hψ x, K.s8dKap_spec]
  have heven : ∀ {v w : Fin 5 → ZMod 2}, IsEvenVec v → IsEvenVec w → IsEvenVec (v + w) :=
    fun hv hw => evenSub.add_mem hv hw
  refine ⟨V1, V2, φ1, φ2, ψ, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [eq_top_iff]
    intro x _
    obtain ⟨⟨a, b⟩, rfl⟩ := K.Ψ.surjective x
    have hab : K.Ψ (a, b) = K.Ψ (a, 0) * K.Ψ (0, b) := by
      rw [← K.add, Prod.mk_add_mk, add_zero, zero_add]
    rw [hab]
    exact Subgroup.mul_mem_sup ⟨a, rfl⟩ ⟨b, rfl⟩
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := Subgroup.mem_inf.mp hx
    have h := K.Ψ.injective (ha.trans hb.symm)
    have ha0 : a = 0 := congrArg Prod.fst h
    rw [Subgroup.mem_bot, ← ha, ha0]
    exact K.zero
  · intro v h
    rw [hφ1 v h]
    exact ⟨⟨v, h⟩, rfl⟩
  · intro v w hv hw
    rw [hφ1 v hv, hφ1 w hw, hφ1 (v + w) (heven hv hw), ← K.add, Prod.mk_add_mk, add_zero]
    rfl
  · intro v h h1
    rw [hφ1 v h] at h1
    have h0 := K.Ψ.injective (h1.trans K.zero.symm)
    exact congrArg (fun q : EvW × EvW => (q.1 : Fin 5 → ZMod 2)) h0
  · rintro x ⟨w, rfl⟩
    refine ⟨w.1, w.2, ?_⟩
    rw [hφ1 _ w.2]
  · intro v h
    rw [hφ2 v h]
    exact ⟨⟨v, h⟩, rfl⟩
  · intro v w hv hw
    rw [hφ2 v hv, hφ2 w hw, hφ2 (v + w) (heven hv hw), ← K.add, Prod.mk_add_mk, add_zero]
    rfl
  · intro v h h1
    rw [hφ2 v h] at h1
    have h0 := K.Ψ.injective (h1.trans K.zero.symm)
    exact congrArg (fun q : EvW × EvW => (q.2 : Fin 5 → ZMod 2)) h0
  · rintro x ⟨w, rfl⟩
    refine ⟨w.1, w.2, ?_⟩
    rw [hφ2 _ w.2]
  · intro a b v h
    refine ⟨?_, ?_⟩
    · rw [hφ1 v h, hact, hφ1 _ (sec128_isEven_permVec _ h)]
      rfl
    · rw [hφ2 v h, hact, hφ2 _ (sec128_isEven_permVec _ h)]
      rfl

theorem s8d_concl_S (K : AddCoord V) {Z : Subgroup (MulAut ↥V)}
    (T : (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ)
    (ψ : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)) ≃* ↥Z)
    (hψ : ∀ x : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)),
      K.s8dKap (ψ x) = s8dTheta T * s8dProdA x * (s8dTheta T)⁻¹) :
    Sec128SplitNat V Z := by
  refine s8d_splitNat_of (K.s8dTw T) ψ fun x => ?_
  rw [AddCoord.s8dKap_tw, hψ x]
  group

end CFSG.OddStandard.SmallF3.Omega

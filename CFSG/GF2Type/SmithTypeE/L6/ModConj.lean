module

public import CFSG.GF2Type.SmithTypeE.LMod.RhoT6
public import CFSG.LargeExtraspecial.S14SMGBits

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open CFSG.SmithL6 CFSG.GF2Type.SmithTypeE.LMod
open CFSG.SmithE (applyCols)
open CFSG.LargeExtraspecial.SMod20 (V decode eq_of_decode_eq)
open CFSG.LargeExtraspecial.S14.SMG (applyCols_lt testBit_code)

section Generic

variable {M : Type*} [Group M]

@[expose] def RelC (a b : M) : Prop := a * b = b * a

theorem RelC.symm {a b : M} (h : RelC a b) : RelC b a := Eq.symm h

@[expose] def RelB (a b : M) : Prop := a * b * a = b * a * b

@[expose] def RelD (a b : M) : Prop := a * b * a * b = b * a * b * a

theorem RelC.conj {a b : M} (h : RelC a b) (ρ : M) : RelC (ρ * a * ρ⁻¹) (ρ * b * ρ⁻¹) := by
  unfold RelC at *
  calc ρ * a * ρ⁻¹ * (ρ * b * ρ⁻¹) = ρ * (a * b) * ρ⁻¹ := by group
    _ = ρ * (b * a) * ρ⁻¹ := by rw [h]
    _ = ρ * b * ρ⁻¹ * (ρ * a * ρ⁻¹) := by group

theorem RelB.conj {a b : M} (h : RelB a b) (ρ : M) : RelB (ρ * a * ρ⁻¹) (ρ * b * ρ⁻¹) := by
  unfold RelB at *
  calc ρ * a * ρ⁻¹ * (ρ * b * ρ⁻¹) * (ρ * a * ρ⁻¹) = ρ * (a * b * a) * ρ⁻¹ := by group
    _ = ρ * (b * a * b) * ρ⁻¹ := by rw [h]
    _ = ρ * b * ρ⁻¹ * (ρ * a * ρ⁻¹) * (ρ * b * ρ⁻¹) := by group

theorem RelD.conj {a b : M} (h : RelD a b) (ρ : M) : RelD (ρ * a * ρ⁻¹) (ρ * b * ρ⁻¹) := by
  unfold RelD at *
  calc ρ * a * ρ⁻¹ * (ρ * b * ρ⁻¹) * (ρ * a * ρ⁻¹) * (ρ * b * ρ⁻¹) = ρ * (a * b * a * b) * ρ⁻¹ := by
        group
    _ = ρ * (b * a * b * a) * ρ⁻¹ := by rw [h]
    _ = ρ * b * ρ⁻¹ * (ρ * a * ρ⁻¹) * (ρ * b * ρ⁻¹) * (ρ * a * ρ⁻¹) := by group

end Generic

@[expose] def InEV (a : V ≃ₗ[ZMod 2] V) (v : V) : Prop := ∃ x, v = a x + x

theorem InEV.conj {a : V ≃ₗ[ZMod 2] V} {v : V} (h : InEV a v) (ρ : V ≃ₗ[ZMod 2] V) :
    InEV (ρ * a * ρ⁻¹) (ρ v) := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨ρ x, ?_⟩
  show ρ (a x + x) = ρ (a (ρ.symm (ρ x))) + ρ x
  rw [ρ.symm_apply_apply, map_add]

section Conj

@[expose] noncomputable def tvE (k : Fin 1953) : V ≃ₗ[ZMod 2] V := tvEquiv k.val

theorem tvE_conj (g : T6) (k : Fin 1953) :
    tvE ((g : Equiv.Perm (Fin 1953)) k) = rhoMod g * tvE k * (rhoMod g)⁻¹ :=
  (rhoMod_conj_tvEquiv g k).symm

theorem relC_tvE (g : T6) {k l : Fin 1953} (h : RelC (tvE k) (tvE l)) :
    RelC (tvE ((g : Equiv.Perm (Fin 1953)) k)) (tvE ((g : Equiv.Perm (Fin 1953)) l)) := by
  rw [tvE_conj, tvE_conj]
  exact h.conj _

theorem relB_tvE (g : T6) {k l : Fin 1953} (h : RelB (tvE k) (tvE l)) :
    RelB (tvE ((g : Equiv.Perm (Fin 1953)) k)) (tvE ((g : Equiv.Perm (Fin 1953)) l)) := by
  rw [tvE_conj, tvE_conj]
  exact h.conj _

theorem relD_tvE (g : T6) {k l : Fin 1953} (h : RelD (tvE k) (tvE l)) :
    RelD (tvE ((g : Equiv.Perm (Fin 1953)) k)) (tvE ((g : Equiv.Perm (Fin 1953)) l)) := by
  rw [tvE_conj, tvE_conj]
  exact h.conj _

theorem inEV_tvE_smul (g : T6) (k : Fin 1953) (v : V) :
    InEV (tvE ((g : Equiv.Perm (Fin 1953)) k)) (rhoMod g v) ↔ InEV (tvE k) v := by
  constructor
  · intro h
    have h' := h.conj (rhoMod g)⁻¹
    have e : (rhoMod g)⁻¹ * tvE ((g : Equiv.Perm (Fin 1953)) k) * ((rhoMod g)⁻¹)⁻¹ = tvE k := by
      rw [tvE_conj]
      group
    have e2 : (rhoMod g)⁻¹ (rhoMod g v) = v := (rhoMod g).symm_apply_apply v
    rw [e, e2] at h'
    exact h'
  · intro h
    rw [tvE_conj]
    exact h.conj _

theorem tvE_fix_smul (g : T6) (l : Fin 1953) (v : V) :
    tvE ((g : Equiv.Perm (Fin 1953)) l) (rhoMod g v) = rhoMod g v ↔ tvE l v = v := by
  rw [tvE_conj]
  show rhoMod g (tvE l ((rhoMod g).symm (rhoMod g v))) = rhoMod g v ↔ _
  rw [LinearEquiv.symm_apply_apply]
  exact ⟨fun h => (rhoMod g).injective h, fun h => by rw [h]⟩

@[expose] noncomputable def wordF : List (Fin 1953) → V → V
  | [], v => v
  | r :: w, v => tvE r (wordF w v)

theorem wordF_map (g : T6) (w : List (Fin 1953)) (v : V) :
    wordF (w.map fun r => (g : Equiv.Perm (Fin 1953)) r) (rhoMod g v) = rhoMod g (wordF w v) := by
  induction w with
  | nil => rfl
  | cons r w ih =>
    simp only [List.map_cons, wordF, ih]
    rw [tvE_conj]
    show rhoMod g (tvE r ((rhoMod g).symm (rhoMod g (wordF w v)))) = rhoMod g (tvE r (wordF w v))
    rw [LinearEquiv.symm_apply_apply]

@[expose] def CReach (a : V ≃ₗ[ZMod 2] V) (u v : V) : Prop :=
  ∃ w : List (Fin 1953), (∀ r ∈ w, RelC (tvE r) a) ∧ wordF w u = v

theorem CReach.refl (a : V ≃ₗ[ZMod 2] V) (u : V) : CReach a u u :=
  ⟨[], fun r hr => absurd hr (by simp), rfl⟩

theorem CReach.cons {a : V ≃ₗ[ZMod 2] V} {u v : V} (r : Fin 1953) (hr : RelC (tvE r) a)
    (h : CReach a u v) : CReach a u (tvE r v) := by
  obtain ⟨w, hw, e⟩ := h
  refine ⟨r :: w, fun x hx => ?_, by rw [← e]; rfl⟩
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact hr
  · exact hw x hx'

theorem CReach.smul (g : T6) {k : Fin 1953} {u v : V} (h : CReach (tvE k) u v) :
    CReach (tvE ((g : Equiv.Perm (Fin 1953)) k)) (rhoMod g u) (rhoMod g v) := by
  obtain ⟨w, hw, e⟩ := h
  refine ⟨w.map fun r => (g : Equiv.Perm (Fin 1953)) r, fun r hr => ?_, ?_⟩
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    exact relC_tvE g (hw r' hr')
  · rw [wordF_map, e]

end Conj

section Code

theorem applyCols_tv_lt {k : Nat} (hk : k < 1953) (c : Nat) :
    applyCols (tvCols k) c < 2 ^ 20 := by
  refine applyCols_lt (fun m hm => ?_) c
  have hm' : m < 20 := by simpa [size_tvCols k] using hm
  exact (tvInv_parts hk m hm').1

theorem tv_invol_code {k : Nat} (hk : k < 1953) {c : Nat} (hc : c < 2 ^ 20) :
    applyCols (tvCols k) (applyCols (tvCols k) c) = c := by
  have h := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (decode c)) (tvEquiv_mul_self hk)
  have h1 : (1 : V ≃ₗ[ZMod 2] V) (decode c) = decode c := rfl
  simp only [LinearEquiv.mul_apply, tvEquiv_decode hk, h1] at h
  exact eq_of_decode_eq (applyCols_tv_lt hk _) hc h

theorem decode_tv_comm {k l : Nat} (hk : k < 1953) (hl : l < 1953) (c : Nat) :
    tvEquiv k (tvEquiv l (decode c)) = decode (applyCols (tvCols k) (applyCols (tvCols l) c)) := by
  rw [tvEquiv_decode hl, tvEquiv_decode hk]

theorem comm_code_of_relC {k l : Nat} (hk : k < 1953) (hl : l < 1953)
    (h : RelC (tvEquiv k) (tvEquiv l)) : ∀ c < 2 ^ 20,
      applyCols (tvCols k) (applyCols (tvCols l) c) =
        applyCols (tvCols l) (applyCols (tvCols k) c) := by
  intro c _
  have h' := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (decode c)) h
  simp only [LinearEquiv.mul_apply, decode_tv_comm hk hl, decode_tv_comm hl hk] at h'
  exact eq_of_decode_eq (applyCols_tv_lt hk _) (applyCols_tv_lt hl _) h'

theorem braid_code_of_relB {k l : Nat} (hk : k < 1953) (hl : l < 1953)
    (h : RelB (tvEquiv k) (tvEquiv l)) : ∀ c < 2 ^ 20,
      applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k) c)) =
        applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l) c)) := by
  intro c _
  have h' := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (decode c)) h
  simp only [LinearEquiv.mul_apply, tvEquiv_decode hk, tvEquiv_decode hl] at h'
  exact eq_of_decode_eq (applyCols_tv_lt hk _) (applyCols_tv_lt hl _) h'

theorem dih_code_of_relD {k l : Nat} (hk : k < 1953) (hl : l < 1953)
    (h : RelD (tvEquiv k) (tvEquiv l)) : ∀ c < 2 ^ 20,
      applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k)
        (applyCols (tvCols l) c))) =
      applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l)
        (applyCols (tvCols k) c))) := by
  intro c _
  have h' := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (decode c)) h
  simp only [LinearEquiv.mul_apply, tvEquiv_decode hk, tvEquiv_decode hl] at h'
  exact eq_of_decode_eq (applyCols_tv_lt hk _) (applyCols_tv_lt hl _) h'

end Code

theorem decode_code (v : V) : decode (CFSG.LargeExtraspecial.S14.SMG.code v) = v := by
  funext m
  rw [CFSG.LargeExtraspecial.SMod20.decode_apply, testBit_code]
  have key : ∀ a : ZMod 2, (if decide (a = 1) = true then (1 : ZMod 2) else 0) = a := by decide
  simpa [m.isLt] using key (v m)

end CFSG.GF2Type.SmithTypeE.L6

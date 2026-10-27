module

public import CFSG.GF2Type.SmithTypeE.DMod.RhoTD6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 (applyCols tvCols)
open CFSG.GF2Type.SmithTypeE.DMod

section Generic

variable {M : Type*} [Group M]

@[expose] def RelC (a b : M) : Prop := a * b = b * a

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
  calc ρ * a * ρ⁻¹ * (ρ * b * ρ⁻¹) * (ρ * a * ρ⁻¹) * (ρ * b * ρ⁻¹)
        = ρ * (a * b * a * b) * ρ⁻¹ := by
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

@[expose] noncomputable def tvE (k : Fin 365211) : V ≃ₗ[ZMod 2] V := tvEquiv k.val

theorem tvE_mul_self (k : Fin 365211) : tvE k * tvE k = 1 := tvEquiv_mul_self k.2

theorem tvE_tvE (k : Fin 365211) (v : V) : tvE k (tvE k v) = v := by
  have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) (tvE_mul_self k)
  exact this

@[expose] noncomputable def wordF : List (Fin 365211) → V → V
  | [], v => v
  | r :: w, v => tvE r (wordF w v)

theorem wordF_append (u w : List (Fin 365211)) (v : V) :
    wordF (u ++ w) v = wordF u (wordF w v) := by
  induction u with
  | nil => rfl
  | cons r u ih => simp only [List.cons_append, wordF, ih]

theorem wordF_reverse (w : List (Fin 365211)) (v : V) : wordF w.reverse (wordF w v) = v := by
  induction w with
  | nil => rfl
  | cons r w ih =>
    rw [List.reverse_cons, wordF_append]
    simp only [wordF, tvE_tvE]
    exact ih

@[expose] def CReach (a : V ≃ₗ[ZMod 2] V) (u v : V) : Prop :=
  ∃ w : List (Fin 365211), (∀ r ∈ w, RelC (tvE r) a) ∧ wordF w u = v

theorem CReach.refl (a : V ≃ₗ[ZMod 2] V) (u : V) : CReach a u u :=
  ⟨[], fun r hr => absurd hr (by simp), rfl⟩

theorem CReach.trans {a : V ≃ₗ[ZMod 2] V} {u v x : V} (h₁ : CReach a u v)
    (h₂ : CReach a v x) : CReach a u x := by
  obtain ⟨w₁, hw₁, e₁⟩ := h₁
  obtain ⟨w₂, hw₂, e₂⟩ := h₂
  refine ⟨w₂ ++ w₁, fun r hr => ?_, ?_⟩
  · rcases List.mem_append.mp hr with h | h
    · exact hw₂ r h
    · exact hw₁ r h
  · rw [wordF_append, e₁, e₂]

theorem CReach.cons {a : V ≃ₗ[ZMod 2] V} {u v : V} (r : Fin 365211) (hr : RelC (tvE r) a)
    (h : CReach a u v) : CReach a u (tvE r v) := by
  obtain ⟨w, hw, e⟩ := h
  refine ⟨r :: w, fun x hx => ?_, by rw [← e]; rfl⟩
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact hr
  · exact hw x hx'

theorem CReach.symm {a : V ≃ₗ[ZMod 2] V} {u v : V} (h : CReach a u v) : CReach a v u := by
  obtain ⟨w, hw, e⟩ := h
  refine ⟨w.reverse, fun r hr => hw r (List.mem_reverse.mp hr), ?_⟩
  rw [← e]
  exact wordF_reverse w u

end Conj

section ConjRho

theorem tvE_conj (g : TD6) (k : Fin 365211) :
    tvE ((g : Equiv.Perm (Fin 365211)) k) = rhoMod g * tvE k * (rhoMod g)⁻¹ :=
  (rhoMod_conj_tvEquiv g k).symm

theorem relC_tvE (g : TD6) {k l : Fin 365211} (h : RelC (tvE k) (tvE l)) :
    RelC (tvE ((g : Equiv.Perm (Fin 365211)) k)) (tvE ((g : Equiv.Perm (Fin 365211)) l)) := by
  rw [tvE_conj, tvE_conj]
  exact h.conj (rhoMod g)

theorem relB_tvE (g : TD6) {k l : Fin 365211} (h : RelB (tvE k) (tvE l)) :
    RelB (tvE ((g : Equiv.Perm (Fin 365211)) k)) (tvE ((g : Equiv.Perm (Fin 365211)) l)) := by
  rw [tvE_conj, tvE_conj]
  exact h.conj (rhoMod g)

theorem relD_tvE (g : TD6) {k l : Fin 365211} (h : RelD (tvE k) (tvE l)) :
    RelD (tvE ((g : Equiv.Perm (Fin 365211)) k)) (tvE ((g : Equiv.Perm (Fin 365211)) l)) := by
  rw [tvE_conj, tvE_conj]
  exact h.conj (rhoMod g)

theorem inEV_tvE_smul (g : TD6) (k : Fin 365211) (v : V) :
    InEV (tvE ((g : Equiv.Perm (Fin 365211)) k)) (rhoMod g v) ↔ InEV (tvE k) v := by
  constructor
  · intro h
    have h' := h.conj (rhoMod g)⁻¹
    have e : (rhoMod g)⁻¹ * tvE ((g : Equiv.Perm (Fin 365211)) k) * ((rhoMod g)⁻¹)⁻¹ =
        tvE k := by
      rw [tvE_conj]
      group
    have e2 : (rhoMod g)⁻¹ (rhoMod g v) = v := (rhoMod g).symm_apply_apply v
    rw [e, e2] at h'
    exact h'
  · intro h
    rw [tvE_conj]
    exact h.conj (rhoMod g)

theorem tvE_fix_smul (g : TD6) (l : Fin 365211) (v : V) :
    tvE ((g : Equiv.Perm (Fin 365211)) l) (rhoMod g v) = rhoMod g v ↔ tvE l v = v := by
  rw [tvE_conj]
  show rhoMod g (tvE l ((rhoMod g).symm (rhoMod g v))) = rhoMod g v ↔ _
  rw [LinearEquiv.symm_apply_apply]
  exact ⟨fun h => (rhoMod g).injective h, fun h => by rw [h]⟩

theorem wordF_map (g : TD6) (w : List (Fin 365211)) (v : V) :
    wordF (w.map fun r => (g : Equiv.Perm (Fin 365211)) r) (rhoMod g v) =
      rhoMod g (wordF w v) := by
  induction w with
  | nil => rfl
  | cons r w ih =>
    simp only [List.map_cons, wordF, ih]
    rw [tvE_conj]
    show rhoMod g (tvE r ((rhoMod g).symm (rhoMod g (wordF w v))))
      = rhoMod g (tvE r (wordF w v))
    rw [LinearEquiv.symm_apply_apply]

theorem CReach.smul (g : TD6) {k : Fin 365211} {u v : V} (h : CReach (tvE k) u v) :
    CReach (tvE ((g : Equiv.Perm (Fin 365211)) k)) (rhoMod g u) (rhoMod g v) := by
  obtain ⟨w, hw, e⟩ := h
  refine ⟨w.map fun r => (g : Equiv.Perm (Fin 365211)) r, fun r hr => ?_, ?_⟩
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    exact relC_tvE g (hw r' hr')
  · rw [wordF_map, e]

end ConjRho

section Code

theorem applyCols_tv_lt {k : Nat} (_hk : k < 365211) (c : Nat) :
    applyCols (tvCols k) c < 2 ^ 32 :=
  applyCols_lt (size_tvCols k) (fun c' hc' => tvCols_lt k hc') c

theorem tv_invol_code {k : Nat} (hk : k < 365211) {c : Nat} (hc : c < 2 ^ 32) :
    applyCols (tvCols k) (applyCols (tvCols k) c) = c := by
  have h := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (decode32 c)) (tvEquiv_mul_self hk)
  have h1 : (1 : V ≃ₗ[ZMod 2] V) (decode32 c) = decode32 c := rfl
  simp only [LinearEquiv.mul_apply, tvEquiv_decode hk, h1] at h
  exact eq_of_decode32_eq (applyCols_tv_lt hk (applyCols (tvCols k) c)) hc h

theorem decode_tv_comm {k l : Nat} (hk : k < 365211) (hl : l < 365211) (c : Nat) :
    tvEquiv k (tvEquiv l (decode32 c)) =
      decode32 (applyCols (tvCols k) (applyCols (tvCols l) c)) := by
  rw [tvEquiv_decode hl, tvEquiv_decode hk]

theorem comm_code_of_relC {k l : Nat} (hk : k < 365211) (hl : l < 365211)
    (h : RelC (tvEquiv k) (tvEquiv l)) : ∀ c < 2 ^ 32,
      applyCols (tvCols k) (applyCols (tvCols l) c) =
        applyCols (tvCols l) (applyCols (tvCols k) c) := by
  intro c _
  have h' := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (decode32 c)) h
  simp only [LinearEquiv.mul_apply, decode_tv_comm hk hl, decode_tv_comm hl hk] at h'
  exact eq_of_decode32_eq (applyCols_tv_lt hk (applyCols (tvCols l) c))
    (applyCols_tv_lt hl (applyCols (tvCols k) c)) h'

theorem braid_code_of_relB {k l : Nat} (hk : k < 365211) (hl : l < 365211)
    (h : RelB (tvEquiv k) (tvEquiv l)) : ∀ c < 2 ^ 32,
      applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k) c)) =
        applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l) c)) := by
  intro c _
  have h' := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (decode32 c)) h
  simp only [LinearEquiv.mul_apply, tvEquiv_decode hk, tvEquiv_decode hl] at h'
  exact eq_of_decode32_eq
    (applyCols_tv_lt hk (applyCols (tvCols l) (applyCols (tvCols k) c)))
    (applyCols_tv_lt hl (applyCols (tvCols k) (applyCols (tvCols l) c))) h'

theorem dih_code_of_relD {k l : Nat} (hk : k < 365211) (hl : l < 365211)
    (h : RelD (tvEquiv k) (tvEquiv l)) : ∀ c < 2 ^ 32,
      applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k)
        (applyCols (tvCols l) c))) =
      applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l)
        (applyCols (tvCols k) c))) := by
  intro c _
  have h' := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (decode32 c)) h
  simp only [LinearEquiv.mul_apply, tvEquiv_decode hk, tvEquiv_decode hl] at h'
  exact eq_of_decode32_eq
    (applyCols_tv_lt hk (applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l) c))))
    (applyCols_tv_lt hl (applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k) c))))
    h'

end Code

end CFSG.GF2Type.SmithTypeE.E7

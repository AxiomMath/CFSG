module

public import CFSG.LargeExtraspecial.GLRElimCent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {C : Config S}

namespace Config

theorem commute_of_isometry {s : S.O} (hs : s ∈ S.Mbar) (hsX : s ∉ C.Xbar) (hss : s * s = 1)
    {x : S.O} (hx : x ∈ C.Xbar)
    (hiso : ∀ a a', C.formOf s (C.resAt ⟨x, hx⟩ a) (C.resAt ⟨x, hx⟩ a') = C.formOf s a a') :
    s * x = x * s := by
  have hAt : ∀ a ∈ C.At, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) a) =
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) a) := by
    intro a ha
    have hsa := C.apply_mem_Bt_of_not_mem hs hsX ha
    have h1 := C.Bt.sub_mem (C.apply_mem_Bt_of_not_mem hs hsX (C.apply_At x hx a ha))
      (C.apply_Bt x hx _ hsa)
    refine sub_eq_zero.mp (C.eq_zero_of_mem_Bt_of_forall_polar h1 fun c hc => ?_)
    rw [polar_sub_right, sub_eq_zero]
    have hc' := C.apply_At _ (C.Xbar.inv_mem hx) c hc
    rw [← apply_inv_apply x c, polar_apply_apply x]
    have := hiso ⟨_, hc'⟩ ⟨a, ha⟩
    exact this
  have hss' : ∀ v, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := fun v => by
    rw [← mul_apply, hss]
    rfl
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  obtain ⟨a, ha, b, hb, rfl⟩ := C.exists_eq_add v
  change (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) (a + b)) =
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) (a + b))
  have hb' := C.apply_mem_At_of_not_mem hs hsX hb
  have e1 : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) b) =
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) b) := by
    conv_lhs => rw [← hss' b, ← hAt _ hb', hss']
  rw [map_add, map_add, map_add, map_add, hAt a ha, e1]

end Config

namespace Levi

variable (Λ : Levi C)

theorem exists_lift {a : S.Qt} (ha : a ∈ C.At) : ∃ h ∈ Λ.H₀, S.cl h = a := by
  obtain ⟨x, hx, rfl⟩ := S.exists_cl a
  rcases Λ.isZCompl.2.2 x ⟨hx, ha⟩ with h | h
  · exact ⟨x, h, rfl⟩
  · exact ⟨x * S.z, h, S.cl_mul_z hx⟩

theorem eq_of_cl_eq {h h' : G} (hh : h ∈ Λ.H₀) (hh' : h' ∈ Λ.H₀) (e : S.cl h = S.cl h') :
    h = h' := by
  have hQ := fun {x} (hx : x ∈ Λ.H₀) => C.A_le_QG (Λ.isZCompl.1 hx)
  rcases (S.cl_eq_cl_iff (hQ hh) (hQ hh')).mp e with h1 | h1
  · exact h1.symm
  · exfalso
    apply Λ.isZCompl.2.1
    have := Λ.H₀.mul_mem (Λ.H₀.inv_mem hh) hh'
    rwa [h1, inv_mul_cancel_left] at this

@[expose] noncomputable def hlift (a : C.At) : G := Classical.choose (Λ.exists_lift a.2)

theorem hlift_mem (a : C.At) : Λ.hlift a ∈ Λ.H₀ := (Classical.choose_spec (Λ.exists_lift a.2)).1

theorem cl_hlift (a : C.At) : S.cl (Λ.hlift a) = a :=
  (Classical.choose_spec (Λ.exists_lift a.2)).2

theorem hlift_mem_A (a : C.At) : Λ.hlift a ∈ C.A := Λ.isZCompl.1 (Λ.hlift_mem a)

theorem hlift_mem_QG (a : C.At) : Λ.hlift a ∈ S.QG := C.A_le_QG (Λ.hlift_mem_A a)

theorem hlift_eq {h : G} (hh : h ∈ Λ.H₀) {a : C.At} (e : S.cl h = a) : Λ.hlift a = h :=
  Λ.eq_of_cl_eq (Λ.hlift_mem a) hh (by rw [cl_hlift, e])

theorem hlift_add (a a' : C.At) : Λ.hlift (a + a') = Λ.hlift a * Λ.hlift a' :=
  Λ.hlift_eq (Λ.H₀.mul_mem (Λ.hlift_mem a) (Λ.hlift_mem a'))
    (by rw [S.cl_mul (Λ.hlift_mem_QG a) (Λ.hlift_mem_QG a'), cl_hlift, cl_hlift]; rfl)

theorem hlift_zero : Λ.hlift 0 = 1 :=
  Λ.hlift_eq Λ.H₀.one_mem (by rw [S.cl_one]; rfl)

theorem conj_hlift {l : G} (hl : l ∈ Λ.L) (a : C.At) :
    l * Λ.hlift a * l⁻¹ = Λ.hlift (C.resAt (Λ.toXbar ⟨l, hl⟩) a) := by
  refine (Λ.hlift_eq (Λ.conj_mem_H₀ l hl _ (Λ.hlift_mem a)) ?_).symm
  rw [Config.cl_conj (Λ.L_le_M hl) (Λ.hlift_mem_QG a), cl_hlift]
  rfl

variable {τ : G}

@[expose] noncomputable def phi (τ : G) (a : C.At) : G :=
  Λ.hlift a * (τ * Λ.hlift a * τ⁻¹)

theorem phi_zero : Λ.phi τ 0 = 1 := by
  rw [phi, hlift_zero]
  group

variable (hτM : τ ∈ S.M) (hτX : τ ∉ C.X)
include hτM hτX

theorem phi_mem_QG (a : C.At) : Λ.phi τ a ∈ S.QG :=
  S.QG.mul_mem (Λ.hlift_mem_QG a)
    (C.B_le_QG (C.conj_mem_B_of_not_mem_X hτM hτX (Λ.hlift_mem_A a)))

theorem conj_hlift_mem_B (a : C.At) : τ * Λ.hlift a * τ⁻¹ ∈ C.B :=
  C.conj_mem_B_of_not_mem_X hτM hτX (Λ.hlift_mem_A a)

theorem commute_iff (a a' : C.At) :
    Λ.hlift a' * (τ * Λ.hlift a * τ⁻¹) = (τ * Λ.hlift a * τ⁻¹) * Λ.hlift a' ↔
      C.formOf (S.ρ ⟨τ, hτM⟩) a' a = 0 := by
  rw [← S.polar_cl_eq_zero_iff (Λ.hlift_mem_QG a') (C.B_le_QG (Λ.conj_hlift_mem_B hτM hτX a)),
    Config.cl_conj hτM (Λ.hlift_mem_QG a), cl_hlift, cl_hlift]
  rfl

theorem phi_mul_of_eq_zero {a a' : C.At} (h : C.formOf (S.ρ ⟨τ, hτM⟩) a' a = 0) :
    Λ.phi τ a * Λ.phi τ a' = Λ.phi τ (a + a') := by
  have hc := (Λ.commute_iff hτM hτX a a').mpr h
  simp only [phi, hlift_add]
  calc Λ.hlift a * (τ * Λ.hlift a * τ⁻¹) * (Λ.hlift a' * (τ * Λ.hlift a' * τ⁻¹))
      = Λ.hlift a * ((τ * Λ.hlift a * τ⁻¹) * Λ.hlift a') * (τ * Λ.hlift a' * τ⁻¹) := by group
    _ = Λ.hlift a * (Λ.hlift a' * (τ * Λ.hlift a * τ⁻¹)) * (τ * Λ.hlift a' * τ⁻¹) := by rw [hc]
    _ = _ := by group

theorem phi_mul_of_eq_one {a a' : C.At} (h : C.formOf (S.ρ ⟨τ, hτM⟩) a' a = 1) :
    Λ.phi τ a * Λ.phi τ a' = Λ.phi τ (a + a') * S.z := by
  have hne : ¬ (Λ.hlift a' * (τ * Λ.hlift a * τ⁻¹) = (τ * Λ.hlift a * τ⁻¹) * Λ.hlift a') :=
    fun hc => by
      rw [(Λ.commute_iff hτM hτX a a').mp hc] at h
      exact zero_ne_one h
  have hzc : ∀ g ∈ S.M, g * S.z = S.z * g := fun g hg => S.z_comm hg
  rcases S.mul_comm_or (C.B_le_QG (Λ.conj_hlift_mem_B hτM hτX a)) (Λ.hlift_mem_QG a')
    with hc | hc
  · exact absurd hc.symm hne
  · simp only [phi, hlift_add]
    have hM : τ * Λ.hlift a' * τ⁻¹ ∈ S.M :=
      S.QG_le_M (C.B_le_QG (Λ.conj_hlift_mem_B hτM hτX a'))
    have hM' : Λ.hlift a' * (τ * Λ.hlift a * τ⁻¹) ∈ S.M :=
      S.M.mul_mem (S.QG_le_M (Λ.hlift_mem_QG a'))
        (S.QG_le_M (C.B_le_QG (Λ.conj_hlift_mem_B hτM hτX a)))
    calc Λ.hlift a * (τ * Λ.hlift a * τ⁻¹) * (Λ.hlift a' * (τ * Λ.hlift a' * τ⁻¹))
        = Λ.hlift a * ((τ * Λ.hlift a * τ⁻¹) * Λ.hlift a') * (τ * Λ.hlift a' * τ⁻¹) := by group
      _ = Λ.hlift a * (S.z * (Λ.hlift a' * (τ * Λ.hlift a * τ⁻¹))) *
            (τ * Λ.hlift a' * τ⁻¹) := by rw [hc]
      _ = Λ.hlift a * ((Λ.hlift a' * (τ * Λ.hlift a * τ⁻¹)) * S.z) *
            (τ * Λ.hlift a' * τ⁻¹) := by rw [hzc _ hM']
      _ = Λ.hlift a * (Λ.hlift a' * (τ * Λ.hlift a * τ⁻¹)) *
            (S.z * (τ * Λ.hlift a' * τ⁻¹)) := by group
      _ = Λ.hlift a * (Λ.hlift a' * (τ * Λ.hlift a * τ⁻¹)) *
            ((τ * Λ.hlift a' * τ⁻¹) * S.z) := by rw [hzc _ hM]
      _ = _ := by group

theorem phi_mul_self {a : C.At} (h : C.formOf (S.ρ ⟨τ, hτM⟩) a a = 0) :
    Λ.phi τ a * Λ.phi τ a = 1 := by
  rw [Λ.phi_mul_of_eq_zero hτM hτX h, ZModModule.add_self, phi_zero]

variable (hττ : τ * τ = 1)
include hττ

theorem phi_comm {a : C.At} (h : C.formOf (S.ρ ⟨τ, hτM⟩) a a = 0) :
    τ * Λ.phi τ a = Λ.phi τ a * τ := by
  have h1 := (Config.conj_mul_conj_eq_iff hτM hτX (Or.inl hττ) (Λ.hlift_mem_A a)).mpr
    (by
      have e : (⟨S.cl (Λ.hlift a), (Λ.hlift_mem_A a).2⟩ : C.At) = a := Subtype.ext (cl_hlift _ a)
      rw [e]
      exact h)
  have h2 : τ * Λ.phi τ a * τ⁻¹ = Λ.phi τ a := by
    unfold phi
    exact h1
  calc τ * Λ.phi τ a = τ * Λ.phi τ a * τ⁻¹ * τ := by group
    _ = Λ.phi τ a * τ := by rw [h2]

omit hττ hτM hτX in
theorem conj_phi {l : G} (hl : l ∈ Λ.L) (hlτ : l * τ = τ * l) (a : C.At) :
    l * Λ.phi τ a * l⁻¹ = Λ.phi τ (C.resAt (Λ.toXbar ⟨l, hl⟩) a) := by
  rw [phi, phi, ← Λ.conj_hlift hl a]
  calc l * (Λ.hlift a * (τ * Λ.hlift a * τ⁻¹)) * l⁻¹
      = l * Λ.hlift a * l⁻¹ * ((l * τ) * Λ.hlift a * (l * τ)⁻¹) := by group
    _ = l * Λ.hlift a * l⁻¹ * ((τ * l) * Λ.hlift a * (τ * l)⁻¹) := by rw [hlτ]
    _ = _ := by group

omit hττ in
theorem commutator_phi {l : G} (hl : l ∈ Λ.L) (hlτ : l * τ = τ * l) {a : C.At}
    (hla : C.formOf (S.ρ ⟨τ, hτM⟩) (C.resAt (Λ.toXbar ⟨l, hl⟩) a)
      (C.resAt (Λ.toXbar ⟨l, hl⟩) a) = 0) :
    ⁅Λ.phi τ a, l⁆ = Λ.phi τ a * Λ.phi τ (C.resAt (Λ.toXbar ⟨l, hl⟩) a) := by
  have h1 := Λ.conj_phi hl hlτ a
  have h2 := Λ.phi_mul_self hτM hτX hla
  rw [commutatorElement_def]
  calc Λ.phi τ a * l * (Λ.phi τ a)⁻¹ * l⁻¹ = Λ.phi τ a * (l * Λ.phi τ a * l⁻¹)⁻¹ := by group
    _ = _ := by rw [h1, inv_eq_of_mul_eq_one_right h2]

include hττ in
theorem exists_lift_commute (hτL : Λ.Normalizes τ) (g : C.At ≃ₗ[ZMod 2] C.At)
    (hg : ∀ a a', C.formOf (S.ρ ⟨τ, hτM⟩) (g a) (g a') = C.formOf (S.ρ ⟨τ, hτM⟩) a a') :
    ∃ l : Λ.L, (l : G) * τ = τ * l ∧ C.resAt (Λ.toXbar l) = g := by
  obtain ⟨x, hx⟩ := C.resAt_bijective.2 g
  obtain ⟨l, rfl⟩ := Λ.toXbar_bijective.2 x
  refine ⟨l, ?_, hx⟩
  set s := S.ρ ⟨τ, hτM⟩
  have hss : s * s = 1 := by
    rw [← map_mul, show (⟨τ, hτM⟩ : S.M) * ⟨τ, hτM⟩ = 1 from Subtype.ext hττ, map_one]
  have hcomm := Config.commute_of_isometry (Config.ρ_mem_Mbar _) (Config.ρ_not_mem_Xbar hτM hτX)
    hss
    (Λ.toXbar l).2 (fun a a' => by
      have := hg a a'
      rwa [← hx] at this)
  have hτl : τ * l * τ⁻¹ ∈ Λ.L := hτL _ l.2
  have h1 : Λ.toXbar ⟨τ * l * τ⁻¹, hτl⟩ = Λ.toXbar l := by
    refine Subtype.ext ?_
    rw [toXbar_coe, toXbar_coe]
    have : (⟨τ * l * τ⁻¹, Λ.L_le_M hτl⟩ : S.M) = ⟨τ, hτM⟩ * ⟨l, Λ.L_le_M l.2⟩ * ⟨τ, hτM⟩⁻¹ :=
      rfl
    rw [this, map_mul, map_mul, map_inv, ← toXbar_coe Λ l]
    change s * _ * s⁻¹ = _
    rw [hcomm, mul_inv_cancel_right]
  have h2 : τ * (l : G) * τ⁻¹ = l := congrArg Subtype.val (Λ.toXbar_bijective.1 h1)
  calc (l : G) * τ = τ * l * τ⁻¹ * τ := by rw [h2]
    _ = τ * l := by group

end Levi

end CFSG.LargeExtraspecial.GLR

module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCSpan

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.Open
open scoped commutatorElement

section Algebra

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def eigP0 (h : V ≃ₗ[ZMod 2] V) (v : V) : V := v + h v + h (h v)

@[expose] def eigP1 (h ω : V ≃ₗ[ZMod 2] V) (v : V) : V := v + ω (ω (h v)) + ω (h (h v))

@[expose] def eigP2 (h ω : V ≃ₗ[ZMod 2] V) (v : V) : V := v + ω (h v) + ω (ω (h (h v)))

section
variable {h ω : V ≃ₗ[ZMod 2] V} (hc : ∀ x, h (ω x) = ω (h x))
  (h3 : ∀ x, h (h (h x)) = x) (w3 : ∀ x, ω (ω (ω x)) = x)
include hc h3 w3

theorem eigP_sum {v : V} (r0 : ω (ω v) = ω v + v) :
    eigP0 h v + eigP1 h ω v + eigP2 h ω v = v := by
  have r1 : ω (ω (h v)) = ω (h v) + h v := by
    have := congrArg h r0
    simp only [map_add, hc] at this
    exact this
  have r2 : ω (ω (h (h v))) = ω (h (h v)) + h (h v) := by
    have := congrArg h r1
    simp only [map_add, hc] at this
    exact this
  unfold eigP0 eigP1 eigP2
  rw [r1, r2]
  have a1 := vec_add_self v
  have a2 := vec_add_self (h v)
  have a3 := vec_add_self (h (h v))
  have a4 := vec_add_self (ω (h v))
  have a5 := vec_add_self (ω (h (h v)))
  linear_combination (norm := module) a1 + a2 + a3 + a4 + a5

theorem h_eigP0 (v : V) : h (eigP0 h v) = eigP0 h v := by
  unfold eigP0
  simp only [map_add, h3]
  abel

theorem h_eigP1 (v : V) : h (eigP1 h ω v) = ω (eigP1 h ω v) := by
  unfold eigP1
  simp only [map_add, hc, h3, w3]
  abel

theorem h_eigP2 (v : V) : h (eigP2 h ω v) = ω (ω (eigP2 h ω v)) := by
  unfold eigP2
  simp only [map_add, hc, h3, w3]
  abel

end

theorem eigP_mem {h ω : V ≃ₗ[ZMod 2] V} (M : Submodule (ZMod 2) V) (hh : ∀ x ∈ M, h x ∈ M)
    (hω : ∀ x ∈ M, ω x ∈ M) {v : V} (hv : v ∈ M) :
    eigP0 h v ∈ M ∧ eigP1 h ω v ∈ M ∧ eigP2 h ω v ∈ M := by
  have h1 := hh v hv
  have h2 := hh _ h1
  refine ⟨?_, ?_, ?_⟩
  · exact M.add_mem (M.add_mem hv h1) h2
  · exact M.add_mem (M.add_mem hv (hω _ (hω _ h1))) (hω _ h2)
  · exact M.add_mem (M.add_mem hv (hω _ h1)) (hω _ (hω _ h2))

theorem eigP_fix {h ω e : V ≃ₗ[ZMod 2] V} (he1 : ∀ x, e (h x) = h (e x))
    (he2 : ∀ x, e (ω x) = ω (e x)) {v : V} (hv : e v = v) :
    e (eigP0 h v) = eigP0 h v ∧ e (eigP1 h ω v) = eigP1 h ω v ∧
      e (eigP2 h ω v) = eigP2 h ω v := by
  refine ⟨?_, ?_, ?_⟩
  · unfold eigP0
    simp only [map_add, he1, hv]
  · unfold eigP1
    simp only [map_add, he1, he2, hv]
  · unfold eigP2
    simp only [map_add, he1, he2, hv]

end Algebra

section OmegaSpace

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def omegaSpace (ω : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) V where
  carrier := {x | ω (ω x) + ω x + x = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    linear_combination (norm := module) ha + hb
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, map_smul] at hx ⊢
    linear_combination (norm := module) c • hx

theorem mem_omegaSpace {ω : V ≃ₗ[ZMod 2] V} {x : V} :
    x ∈ omegaSpace ω ↔ ω (ω x) + ω x + x = 0 := Iff.rfl

theorem omegaSpace_rel {ω : V ≃ₗ[ZMod 2] V} {x : V} (hx : x ∈ omegaSpace ω) :
    ω (ω x) = ω x + x := by
  rw [mem_omegaSpace] at hx
  have := vec_add_self (ω x + x)
  linear_combination (norm := module) hx - this

theorem omegaSpace_orbit {ω : V ≃ₗ[ZMod 2] V} {x : V} (hx : x ∈ omegaSpace ω) :
    x + ω x + ω (ω x) = 0 := by
  rw [mem_omegaSpace] at hx
  linear_combination (norm := module) hx

theorem map_mem_omegaSpace {ω h : V ≃ₗ[ZMod 2] V} (hc : ∀ x, h (ω x) = ω (h x)) {x : V}
    (hx : x ∈ omegaSpace ω) : h x ∈ omegaSpace ω := by
  rw [mem_omegaSpace] at hx ⊢
  have := congrArg h hx
  simp only [map_add, hc, map_zero] at this
  exact this

theorem omega_mem_omegaSpace {ω : V ≃ₗ[ZMod 2] V} {x : V} (hx : x ∈ omegaSpace ω) :
    ω x ∈ omegaSpace ω :=
  map_mem_omegaSpace (fun _ => rfl) hx

end OmegaSpace

section Orth

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem polar_shift {h ω A : V ≃ₗ[ZMod 2] V} (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hAω : ∀ x, A (ω x) = ω (A x)) {x y : V}
    (hx : h x = A x) (hy : h y = ω (A y)) : polar Q x y = polar Q x (ω y) := by
  have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hh x y
  rw [hx, hy, ← hAω y, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hA] at h1
  exact h1.symm

theorem polar_eq_zero_of_eig {h ω A : V ≃ₗ[ZMod 2] V}
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hAω : ∀ x, A (ω x) = ω (A x))
    (hc : ∀ x, h (ω x) = ω (h x)) {x y : V} (hx : h x = A x) (hy : h y = ω (A y))
    (hrel : y + ω y + ω (ω y) = 0) : polar Q x y = 0 := by
  have e0 := polar_shift hh hA hAω hx hy
  have hy' : h (ω y) = ω (A (ω y)) := by rw [hc, hy, hAω]
  have e1 := polar_shift hh hA hAω hx hy'
  have := congrArg (polar Q x) hrel
  rw [polar_add_right, polar_add_right, polar_zero_right, ← e1, ← e0] at this
  generalize polar Q x y = c at this ⊢
  revert c
  decide

theorem map_add_three (a b c : V) : Q (a + b + c) =
    Q a + Q b + Q c + polar Q a b + polar Q a c + polar Q b c := by
  rw [QuadraticMap.map_add Q (a + b) c, QuadraticMap.map_add Q a b, polar_add_left]
  abel

end Orth

section StepA

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
variable {E : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem E_comm (hE : IsElemAbelian 3 E) {g h : V ≃ₗ[ZMod 2] V} (hg : g ∈ E) (hh : h ∈ E)
    (x : V) : g (h x) = h (g x) := by
  have := congrArg Subtype.val (hE.1.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)
  exact congrArg (fun φ : V ≃ₗ[ZMod 2] V => φ x) this

theorem E_pow3 (hE : IsElemAbelian 3 E) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ E) (x : V) :
    g (g (g x)) = x := by
  have := congrArg (fun φ : V ≃ₗ[ZMod 2] V => φ x) (hE.2 g hg)
  rw [pow_three] at this
  exact this

theorem E_polar (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ E) (x y : V) : polar Q (g x) (g y) = polar Q x y :=
  TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hEO hg) x y

theorem E_map (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ E) (x : V) : Q (g x) = Q x :=
  TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hEO hg) x

theorem exists_omega_anisotropic (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hE : IsElemAbelian 3 E) {N : Submodule (ZMod 2) V} (hN : ∀ g ∈ E, ∀ x ∈ N, g x ∈ N)
    (hnd : ∀ x ∈ N, (∀ y ∈ N, polar Q x y = 0) → x = 0) {g₀ : V ≃ₗ[ZMod 2] V} (hg₀ : g₀ ∈ E)
    {x₀ : V} (hx₀ : x₀ ∈ N) (hmov : g₀ x₀ ≠ x₀) :
    ∃ v ∈ N ⊓ omegaSpace g₀, Q v = 1 := by
  by_contra hcon
  push Not at hcon
  have hQ0 : ∀ v ∈ N ⊓ omegaSpace g₀, Q v = 0 := fun v hv =>
    (zmod_two_cases (Q v)).resolve_right (hcon v hv)
  have hBz : ∀ y ∈ N ⊓ omegaSpace g₀, ∀ z ∈ N ⊓ omegaSpace g₀, polar Q y z = 0 := by
    intro y hy z hz
    rw [polar_eq Q, hQ0 _ (Submodule.add_mem _ hy hz), hQ0 y hy, hQ0 z hz]
    simp
  have h3 := E_pow3 hE hg₀
  have hy₀N : g₀ x₀ + x₀ ∈ N := N.add_mem (hN g₀ hg₀ x₀ hx₀) hx₀
  have hy₀Ω : g₀ x₀ + x₀ ∈ omegaSpace g₀ := by
    rw [mem_omegaSpace]
    simp only [map_add, h3]
    have a1 := vec_add_self x₀
    have a2 := vec_add_self (g₀ x₀)
    have a3 := vec_add_self (g₀ (g₀ x₀))
    linear_combination (norm := module) a1 + a2 + a3
  have hy₀ : g₀ x₀ + x₀ = 0 := by
    refine hnd _ hy₀N (fun z hz => ?_)
    set z₂ := g₀ z + g₀ (g₀ z) with hz₂
    set z₁ := z + g₀ z + g₀ (g₀ z) with hz₁
    have hzz : z = z₁ + z₂ := by
      have a1 := vec_add_self (g₀ z)
      have a2 := vec_add_self (g₀ (g₀ z))
      rw [hz₁, hz₂]
      linear_combination (norm := module) -a1 - a2
    have hz₂N : z₂ ∈ N ⊓ omegaSpace g₀ := by
      refine ⟨N.add_mem (hN g₀ hg₀ z hz) (hN g₀ hg₀ _ (hN g₀ hg₀ z hz)), ?_⟩
      show g₀ (g₀ z₂) + g₀ z₂ + z₂ = 0
      rw [hz₂]
      simp only [map_add, h3]
      have a1 := vec_add_self z
      have a2 := vec_add_self (g₀ z)
      have a3 := vec_add_self (g₀ (g₀ z))
      linear_combination (norm := module) a1 + a2 + a3
    have hz₁fix : g₀ z₁ = z₁ := by
      rw [hz₁]
      simp only [map_add, h3]
      abel
    have hp1 : polar Q (g₀ x₀ + x₀) z₁ = 0 := by
      rw [polar_add_left]
      have := E_polar hEO hg₀ x₀ z₁
      rw [hz₁fix] at this
      rw [this]
      generalize polar Q x₀ z₁ = c
      revert c
      decide
    have hp2 : polar Q (g₀ x₀ + x₀) z₂ = 0 := hBz _ ⟨hy₀N, hy₀Ω⟩ _ hz₂N
    rw [hzz, polar_add_right, hp1, hp2, add_zero]
  have := vec_add_self x₀
  apply hmov
  linear_combination (norm := module) hy₀ - this

end StepA

section StepB

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

@[expose] def stabE (E : Subgroup (V ≃ₗ[ZMod 2] V)) (v : V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | g ∈ E ∧ g v = v}
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [LinearEquiv.mul_apply, hb.2, ha.2]⟩
  one_mem' := ⟨one_mem _, rfl⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, (LinearEquiv.symm_apply_eq a).2 ha.2.symm⟩

theorem key_orbit [Finite V] {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hE : IsElemAbelian 3 E)
    {N : Submodule (ZMod 2) V} (hN : ∀ g ∈ E, ∀ x ∈ N, g x ∈ N) {ω : V ≃ₗ[ZMod 2] V}
    (hg₀ : ω ∈ E) {v : V} (hvM : v ∈ N ⊓ omegaSpace ω) (hvQ : Q v = 1)
    (hmax : ∀ q ∈ N ⊓ omegaSpace ω, Q q = 1 → Nat.card (stabE E q) ≤ Nat.card (stabE E v)) :
    ∀ h ∈ E, h v = v ∨ h v = ω v ∨ h v = ω (ω v) := by
  intro h hh
  by_contra hcon
  push Not at hcon
  obtain ⟨hv0, hv1, hv2⟩ := hcon
  have hcomm : ∀ x, h (ω x) = ω (h x) := fun x => E_comm hE hh hg₀ x
  have hh3 := E_pow3 hE hh
  have hω3 := E_pow3 hE hg₀
  have r0 := omegaSpace_rel hvM.2
  have hMh : ∀ x ∈ N ⊓ omegaSpace ω, h x ∈ N ⊓ omegaSpace ω := fun x hx =>
    ⟨hN h hh x hx.1, map_mem_omegaSpace hcomm hx.2⟩
  have hMω : ∀ x ∈ N ⊓ omegaSpace ω, ω x ∈ N ⊓ omegaSpace ω := fun x hx =>
    ⟨hN ω hg₀ x hx.1, omega_mem_omegaSpace hx.2⟩
  obtain ⟨m0, m1, m2⟩ := eigP_mem (h := h) (ω := ω) (N ⊓ omegaSpace ω) hMh hMω hvM
  have hsum := eigP_sum hcomm hh3 hω3 r0
  have e0 := h_eigP0 hcomm hh3 hω3 v
  have e1 := h_eigP1 hcomm hh3 hω3 v
  have e2 := h_eigP2 hcomm hh3 hω3 v
  have hhO := hEO hh
  have hωO := hEO hg₀
  have rel0 := omegaSpace_orbit m0.2
  have rel1 := omegaSpace_orbit m1.2
  have rel2 := omegaSpace_orbit m2.2
  have o01 : polar Q (eigP0 h v) (eigP1 h ω v) = 0 :=
    polar_eq_zero_of_eig (ω := ω) (A := 1) hhO (one_mem _) (fun x => rfl) hcomm
      (by rw [e0]; rfl) (by rw [e1]; rfl) rel1
  have o12 : polar Q (eigP1 h ω v) (eigP2 h ω v) = 0 :=
    polar_eq_zero_of_eig (ω := ω) (A := ω) hhO hωO (fun x => rfl) hcomm (by rw [e1]) e2 rel2
  have o20 : polar Q (eigP2 h ω v) (eigP0 h v) = 0 :=
    polar_eq_zero_of_eig (ω := ω) (A := ω * ω) hhO (mul_mem hωO hωO) (fun x => rfl) hcomm
      (by rw [e2]; rfl) (by rw [e0]; exact (hω3 (eigP0 h v)).symm) rel0
  have o02 : polar Q (eigP0 h v) (eigP2 h ω v) = 0 := by rw [polar_comm]; exact o20
  have hQsum : Q v = Q (eigP0 h v) + Q (eigP1 h ω v) + Q (eigP2 h ω v) := by
    conv_lhs => rw [← hsum]
    rw [map_add_three, o01, o02, o12]
    simp
  have hex : Q (eigP0 h v) = 1 ∨ Q (eigP1 h ω v) = 1 ∨ Q (eigP2 h ω v) = 1 := by
    by_contra hno
    push Not at hno
    have a0 := (zmod_two_cases (Q (eigP0 h v))).resolve_right hno.1
    have a1 := (zmod_two_cases (Q (eigP1 h ω v))).resolve_right hno.2.1
    have a2 := (zmod_two_cases (Q (eigP2 h ω v))).resolve_right hno.2.2
    rw [a0, a1, a2, hvQ] at hQsum
    exact absurd hQsum (by decide)
  have bigger : ∀ q ∈ N ⊓ omegaSpace ω, Q q = 1 → stabE E v ≤ stabE E q → ∀ w ∈ stabE E q,
      w ∉ stabE E v → False := by
    intro q hq hQq hle w hw hnw
    have heq := Subgroup.eq_of_le_of_card_ge hle (hmax q hq hQq)
    exact hnw (heq ▸ hw)
  have hle : ∀ e ∈ stabE E v, e (eigP0 h v) = eigP0 h v ∧ e (eigP1 h ω v) = eigP1 h ω v ∧
      e (eigP2 h ω v) = eigP2 h ω v := fun e he =>
    eigP_fix (fun x => E_comm hE he.1 hh x) (fun x => E_comm hE he.1 hg₀ x) he.2
  have hωi : ω.symm ∈ E := inv_mem hg₀
  rcases hex with hq | hq | hq
  · refine bigger _ m0 hq (fun e he => ⟨he.1, (hle e he).1⟩) h ⟨hh, e0⟩ ?_
    exact fun hmem => hv0 hmem.2
  · refine bigger _ m1 hq (fun e he => ⟨he.1, (hle e he).2.1⟩) (ω.symm * h)
      ⟨mul_mem hωi hh, ?_⟩ ?_
    · rw [LinearEquiv.mul_apply, e1]
      exact (LinearEquiv.symm_apply_apply ω _)
    · intro hmem
      have := hmem.2
      rw [LinearEquiv.mul_apply, LinearEquiv.symm_apply_eq] at this
      exact hv1 this
  · refine bigger _ m2 hq (fun e he => ⟨he.1, (hle e he).2.2⟩) (ω.symm * (ω.symm * h))
      ⟨mul_mem hωi (mul_mem hωi hh), ?_⟩ ?_
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e2, LinearEquiv.symm_apply_apply,
        LinearEquiv.symm_apply_apply]
    · intro hmem
      have := hmem.2
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.symm_apply_eq,
        LinearEquiv.symm_apply_eq] at this
      exact hv2 this

theorem exists_adapted_pair [Finite V] {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hE : IsElemAbelian 3 E)
    {N : Submodule (ZMod 2) V} (hN : ∀ g ∈ E, ∀ x ∈ N, g x ∈ N)
    (hnd : ∀ x ∈ N, (∀ y ∈ N, polar Q x y = 0) → x = 0) {g₀ : V ≃ₗ[ZMod 2] V} (hg₀ : g₀ ∈ E)
    {x₀ : V} (hx₀ : x₀ ∈ N) (hmov : g₀ x₀ ≠ x₀) :
    ∃ a b : V, a ∈ N ∧ b ∈ N ∧ MinusPair Q a b ∧
      ∀ g ∈ E, ∃ k : ℕ, g a = (rot Q a b ^ k) a ∧ g b = (rot Q a b ^ k) b := by
  obtain ⟨v₁, hv₁M, hv₁Q⟩ := exists_omega_anisotropic hEO hE hN hnd hg₀ hx₀ hmov
  let S : Set V := {v | v ∈ N ⊓ omegaSpace g₀ ∧ Q v = 1}
  obtain ⟨v, hvS, hmax⟩ := Set.exists_max_image S (fun v => Nat.card (stabE E v))
    (Set.toFinite S) ⟨v₁, hv₁M, hv₁Q⟩
  have key := key_orbit hEO hE hN hg₀ hvS.1 hvS.2 (fun q hq hQ => hmax q ⟨hq, hQ⟩)
  have r0 := omegaSpace_rel hvS.1.2
  have hQb : Q (g₀ v) = 1 := by rw [E_map hEO hg₀, hvS.2]
  have hsum : v + g₀ v = g₀ (g₀ v) := by rw [r0, add_comm]
  have hpair : MinusPair Q v (g₀ v) := by
    refine ⟨hvS.2, hQb, ?_⟩
    rw [polar_eq, hsum, E_map hEO hg₀, E_map hEO hg₀, hvS.2]
    decide
  refine ⟨v, g₀ v, hvS.1.1, hN g₀ hg₀ v hvS.1.1, hpair, ?_⟩
  intro g hg
  have hgω : g (g₀ v) = g₀ (g v) := E_comm hE hg hg₀ v
  rcases key g hg with h0 | h1 | h2
  · refine ⟨0, ?_, ?_⟩
    · rw [pow_zero]
      exact h0
    · rw [pow_zero, hgω, h0]
      rfl
  · refine ⟨1, ?_, ?_⟩
    · rw [pow_one, rot_apply_left hpair, h1]
    · rw [pow_one, rot_apply_right hpair, hgω, h1, r0, add_comm]
  · refine ⟨2, ?_, ?_⟩
    · rw [pow_two, LinearEquiv.mul_apply, rot_apply_left hpair, rot_apply_right hpair, h2, r0,
        add_comm]
    · rw [pow_two, LinearEquiv.mul_apply, rot_apply_right hpair, map_add, rot_apply_left hpair,
        rot_apply_right hpair, hgω, h2, E_pow3 hE hg₀]
      have := vec_add_self (g₀ v)
      linear_combination (norm := module) -this

end StepB

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

end

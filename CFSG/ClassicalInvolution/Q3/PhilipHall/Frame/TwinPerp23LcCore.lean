module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcSL
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcFit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcPerf
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcLayerAD
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcLayerA6

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc

open CFSG CFSG.Open
open scoped MatrixGroups

theorem mem_centralizer_sup_iff {G : Type*} [Group G] {P P' : Subgroup G} {x : G} :
    x ∈ Subgroup.centralizer ((P ⊔ P' : Subgroup G) : Set G) ↔
      (∀ k ∈ P, k * x = x * k) ∧ (∀ k ∈ P', k * x = x * k) := by
  constructor
  · intro h
    exact ⟨fun k hk => Subgroup.mem_centralizer_iff.mp h k (Subgroup.mem_sup_left hk),
      fun k hk => Subgroup.mem_centralizer_iff.mp h k (Subgroup.mem_sup_right hk)⟩
  · rintro ⟨h1, h2⟩
    have hle : P ⊔ P' ≤ Subgroup.centralizer ({x} : Set G) :=
      sup_le (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (h1 k hk))
        (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (h2 k hk))
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hk)

theorem perfect_of_atype {G : Type} [Group G] {A : Subgroup G}
    (h : A = ⊥ ∨ Nonempty (↥A ≃* alternatingGroup (Fin 6))) : Group.IsPerfect ↥A := by
  rcases h with rfl | ⟨⟨e⟩⟩
  · infer_instance
  · have h6 : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem central_main {G : Type} [Group G] [Finite G] {P P' Λ L : Subgroup G} {t w y : G}
    (hP8 : Nat.card ↥P = 8) (hPq : Nonempty (↥P ≃* QuaternionGroup 2))
    (hP'q : Nonempty (↥P' ≃* QuaternionGroup 2)) (hne : P ≠ P')
    (hperm : ∀ c ∈ Subgroup.centralizer ({t} : Set G),
      (P.map (MulAut.conj c).toMonoidHom = P ∨ P.map (MulAut.conj c).toMonoidHom = P') ∧
      (P'.map (MulAut.conj c).toMonoidHom = P ∨ P'.map (MulAut.conj c).toMonoidHom = P'))
    (htP : t ∈ P)
    (e : ↥Λ ≃* SL(2, ZMod 3)) (hPΛ : P ≤ Λ) (hΛP' : ∀ l ∈ Λ, ∀ x ∈ P', l * x = x * l)
    (hwF : w ∈ Subgroup.centralizer ((P ⊔ P' : Subgroup G) : Set G)) (hw2 : w * w = 1)
    (hΛw : ∀ l ∈ Λ, l * w = w * l)
    (hnorm : ∀ x ∈ Subgroup.centralizer ((P ⊔ P' : Subgroup G) : Set G), x * w = w * x →
      ∀ l ∈ Λ, x * l * x⁻¹ ∈ Λ)
    (hOF : oddCore ↥(Subgroup.centralizer ((P ⊔ P' : Subgroup G) : Set G)) = ⊥)
    (hFL : ∀ f ∈ Subgroup.centralizer ((P ⊔ P' : Subgroup G) : Set G), ∀ l ∈ L, f * l * f⁻¹ ∈ L)
    (hDw : ∀ x ∈ Subgroup.centralizer ((P ⊔ P' : Subgroup G) : Set G),
      (∀ l ∈ L, x * l = l * x) → x * w = w * x)
    (hyL : y ∈ L) (hty : ∀ l ∈ L, t * l * t⁻¹ = y * l * y⁻¹)
    (hAex : ∃ A : Subgroup G, A ≤ L ∧ (∀ x ∈ A, x * y = y * x) ∧
      (A = ⊥ ∨ Nonempty (↥A ≃* alternatingGroup (Fin 6))) ∧
      ∀ Q : Subgroup G, Q ≤ L → (∀ x ∈ Q, x * y = y * x) → Group.IsPerfect ↥Q → Q ≤ A)
    (hOut : ∀ Q : Subgroup (MulAut ↥L), Group.IsPerfect ↥Q →
      Q ≤ (MulAut.conj : ↥L →* MulAut ↥L).range)
    (hA6 : ∀ (B : Type) [Group B] [Finite B], Nonempty (B ≃* alternatingGroup (Fin 6)) →
      ∀ f α : MulAut B, f * f = 1 → f ≠ 1 → α * α * α = 1 → α * f = f * α →
        (∀ x, f x = x → α x = x) → α = 1) :
    ∀ l ∈ Λ, ∀ x ∈ Subgroup.centralizer ((P ⊔ P' : Subgroup G) : Set G), l * x = x * l := by
  set F : Subgroup G := Subgroup.centralizer ((P ⊔ P' : Subgroup G) : Set G) with hF
  obtain ⟨hKnorm, ⟨a, haΛ, ha3, hdec⟩, -⟩ := sl2_facts e hPΛ hP8
  have hxP : ∀ x ∈ F, ∀ k ∈ P, k * x = x * k := fun x hx => (mem_centralizer_sup_iff.mp hx).1
  have hxP' : ∀ x ∈ F, ∀ k ∈ P', k * x = x * k := fun x hx => (mem_centralizer_sup_iff.mp hx).2
  have hzF : ∀ x ∈ F, x * t = t * x := fun x hx => (hxP x hx t htP).symm
  have haF : ∀ x ∈ F, a * x * a⁻¹ ∈ F := by
    intro x hx
    rw [hF, mem_centralizer_sup_iff]
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · have h1 : a⁻¹ * k * a ∈ P := by
        have := hKnorm a⁻¹ (Subgroup.inv_mem _ haΛ) k hk
        simpa using this
      have h2 := hxP x hx _ h1
      calc k * (a * x * a⁻¹) = a * ((a⁻¹ * k * a) * x) * a⁻¹ := by group
        _ = a * (x * (a⁻¹ * k * a)) * a⁻¹ := by rw [h2]
        _ = a * x * a⁻¹ * k := by group
    · have h1 : a * k = k * a := hΛP' a haΛ k hk
      have h2 := hxP' x hx k hk
      calc k * (a * x * a⁻¹) = (k * a) * x * a⁻¹ := by group
        _ = (a * k) * x * a⁻¹ := by rw [h1]
        _ = a * (k * x) * a⁻¹ := by group
        _ = a * (x * k) * a⁻¹ := by rw [h2]
        _ = a * x * a⁻¹ * k := by
          have h3 : k * a⁻¹ = a⁻¹ * k := (Commute.inv_left (show Commute a k from h1)).eq.symm
          calc a * (x * k) * a⁻¹ = a * x * (k * a⁻¹) := by group
            _ = a * x * (a⁻¹ * k) := by rw [h3]
            _ = a * x * a⁻¹ * k := by group
  have haw : a * w = w * a := hΛw a haΛ
  have hfix : ∀ x ∈ F, x * w = w * x → a * x = x * a := by
    intro x hx hxw
    have := centralizes_of_normalizes e hPΛ hP8 (hnorm x hx hxw) (fun k hk => (hxP x hx k hk).symm)
      a haΛ
    exact this.symm
  obtain ⟨A, hAL, hAy, hAtype, hAmax⟩ := hAex
  have hAperf : Group.IsPerfect ↥A := perfect_of_atype hAtype
  have hAt : A ≤ Subgroup.centralizer ({t} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hty x (hAL hx)
    have h2 : y * x * y⁻¹ = x := by
      calc y * x * y⁻¹ = (y * x) * y⁻¹ := rfl
        _ = (x * y) * y⁻¹ := by rw [hAy x hx]
        _ = x := by group
    rw [h2] at h1
    calc x * t = (t * x * t⁻¹) * t := by rw [h1]
      _ = t * x := by group
  have hAF : A ≤ F := perfect_centralizes_twins hPq hP'q hne hperm hAt hAperf
  have hAnorm := A_normalized hFL hzF hty hyL hAL hAy hAperf hAmax
  have hAD := layer_le_mul hFL hyL hzF hty hAL hAy hAF hAmax hOut
  have hlay := layer_central_of_mul haF ha3 hwF hw2 haw hfix hDw hAL hAF hAnorm hAtype hAD hA6
  have hfit := a_centralizes_fitting hOF haF ha3 hwF hw2 haw hfix
  have hall := central_of_fitting_layer hOF haF ha3 hfit hlay
  intro l hl x hx
  obtain ⟨k, hk, i, rfl⟩ := hdec l hl
  have hax : Commute (a ^ i) x := Commute.pow_left (hall x hx) i
  calc k * a ^ i * x = k * (a ^ i * x) := by group
    _ = k * (x * a ^ i) := by rw [hax.eq]
    _ = (k * x) * a ^ i := by group
    _ = (x * k) * a ^ i := by rw [hxP x hx k hk]
    _ = x * (k * a ^ i) := by group

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc

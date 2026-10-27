module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.Open.LocalVocabulary

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap CFSG.Open CFSG.ClassicalGroups.Orthogonal

variable {X : Type*} [Group X] {K : Subgroup X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

@[expose] def ActsAsConj (e : ↥K ≃* ↥(elementaryGroup Q)) (x : X) (g : V ≃ₗ[ZMod 2] V) : Prop :=
  ∀ (k : ↥K) (hk : x * (k : X) * x⁻¹ ∈ K),
    ((e ⟨x * (k : X) * x⁻¹, hk⟩ : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V) =
      g * (e k : V ≃ₗ[ZMod 2] V) * g⁻¹

namespace ActsAsConj

variable {e : ↥K ≃* ↥(elementaryGroup Q)} {x y : X} {g h : V ≃ₗ[ZMod 2] V}

theorem mul (hy : y ∈ Subgroup.normalizer (K : Set X)) (h1 : ActsAsConj e x g)
    (h2 : ActsAsConj e y h) : ActsAsConj e (x * y) (g * h) := by
  intro k hk
  have hk' : y * (k : X) * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hy k).mp k.2
  have hk'' : x * (y * (k : X) * y⁻¹) * x⁻¹ ∈ K := by
    have : x * (y * (k : X) * y⁻¹) * x⁻¹ = x * y * (k : X) * (x * y)⁻¹ := by group
    rw [this]
    exact hk
  have e1 : (⟨x * y * (k : X) * (x * y)⁻¹, hk⟩ : ↥K) =
      ⟨x * (y * (k : X) * y⁻¹) * x⁻¹, hk''⟩ := Subtype.ext (by group)
  rw [e1, h1 ⟨_, hk'⟩ hk'']
  have := h2 k hk'
  rw [this]
  group

theorem inv (h1 : ActsAsConj e x g) :
    ActsAsConj e x⁻¹ g⁻¹ := by
  intro k hk
  have hk0 : x * (x⁻¹ * (k : X) * x⁻¹⁻¹) * x⁻¹ = (k : X) := by group
  have hkk : x * (x⁻¹ * (k : X) * x⁻¹⁻¹) * x⁻¹ ∈ K := by rw [hk0]; exact k.2
  have h3 := h1 ⟨x⁻¹ * (k : X) * x⁻¹⁻¹, hk⟩ hkk
  have e1 : (⟨x * (x⁻¹ * (k : X) * x⁻¹⁻¹) * x⁻¹, hkk⟩ : ↥K) = k := Subtype.ext hk0
  simp only [e1] at h3
  rw [h3]
  group

theorem eq_of_mem_orthogonalGroup (hx : x ∈ Subgroup.normalizer (K : Set X))
    (hcO : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      (∀ y ∈ elementaryGroup Q, g * y = y * g) → g = 1)
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h1 : ActsAsConj e x g)
    (h2 : ActsAsConj e x h) : g = h := by
  have key : g⁻¹ * h = 1 := by
    refine hcO _ (mul_mem (inv_mem hg) hh) fun z hz => ?_
    obtain ⟨k, hk⟩ := e.surjective ⟨z, hz⟩
    have hkx : x * (k : X) * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hx k).mp k.2
    have e1 := h1 k hkx
    have e2 := h2 k hkx
    have hz' : (e k : V ≃ₗ[ZMod 2] V) = z := by rw [hk]
    rw [hz'] at e1 e2
    calc g⁻¹ * h * z = g⁻¹ * (h * z * h⁻¹) * h := by group
      _ = g⁻¹ * (g * z * g⁻¹) * h := by rw [← e2, e1]
      _ = z * (g⁻¹ * h) := by group
  exact inv_mul_eq_one.mp key

end ActsAsConj

theorem hcenter_of_hcenterO
    (hcO : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      (∀ y ∈ elementaryGroup Q, g * y = y * g) → g = 1) :
    ∀ z : ↥(elementaryGroup Q), (∀ x : ↥(elementaryGroup Q), z * x = x * z) → z = 1 := by
  intro z hz
  have : (z : V ≃ₗ[ZMod 2] V) = 1 :=
    hcO z (elementaryGroup_le_orthogonalGroup Q z.2) fun y hy => by
      have := hz ⟨y, hy⟩
      exact congrArg Subtype.val this
  exact Subtype.ext this

theorem exists_action_hom {p : ℕ} {B : Subgroup X} (hB : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (e : ↥K ≃* ↥(elementaryGroup Q))
    (hAut : ∀ σ : MulAut ↥(elementaryGroup Q), σ ^ p = 1 →
      ∃ y : ↥(elementaryGroup Q), σ = MulAut.conj y)
    (hcenter : ∀ z : ↥(elementaryGroup Q), (∀ x : ↥(elementaryGroup Q), z * x = x * z) → z = 1) :
    ∃ Yh : B →* ↥(elementaryGroup Q), ∀ b : B, ActsAsConj e (b : X) (Yh b : V ≃ₗ[ZMod 2] V) := by
  classical
  let α : B →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  let ψ : B →* MulAut ↥(elementaryGroup Q) := (MulAut.congr e).toMonoidHom.comp α
  have hψp : ∀ a : B, ψ a ^ p = 1 := by
    intro a
    rw [← map_pow]
    have : a ^ p = 1 := Subtype.ext (hB.2 a a.2)
    rw [this, map_one]
  choose yfun hyfun using fun a : B => hAut (ψ a) (hψp a)
  have hconj_inj : ∀ u v : ↥(elementaryGroup Q), MulAut.conj u = MulAut.conj v → u = v := by
    intro u v h
    have h1 : v⁻¹ * u = 1 := hcenter _ (fun x => by
      have := congrArg (fun f : MulAut ↥(elementaryGroup Q) => f x) h
      simp only [MulAut.conj_apply] at this
      have h2 : (v⁻¹ * u) * x = x * (v⁻¹ * u) := by
        calc (v⁻¹ * u) * x = v⁻¹ * (u * x * u⁻¹) * u := by group
          _ = v⁻¹ * (v * x * v⁻¹) * u := by rw [this]
          _ = x * (v⁻¹ * u) := by group
      exact h2)
    exact (inv_mul_eq_one.mp h1).symm
  let Yh : B →* ↥(elementaryGroup Q) :=
    { toFun := yfun
      map_one' := by
        apply hconj_inj
        rw [← hyfun, map_one, map_one]
      map_mul' := fun a b => by
        apply hconj_inj
        rw [map_mul, ← hyfun, ← hyfun, ← hyfun, map_mul] }
  refine ⟨Yh, fun b k hk => ?_⟩
  have h1 : ψ b (e k) = MulAut.conj (Yh b) (e k) := by
    rw [hyfun b]
    rfl
  have h2 : ψ b (e k) = e ⟨(b : X) * (k : X) * (b : X)⁻¹, hk⟩ := by
    change e (α b (e.symm (e k))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have h3 := congrArg (fun z : ↥(elementaryGroup Q) => (z : V ≃ₗ[ZMod 2] V)) (h2.symm.trans h1)
  simpa using h3

theorem commute_of_actsAsConj_transv {B T : Subgroup X} {e : ↥K ≃* ↥(elementaryGroup Q)}
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hTN : T ≤ Subgroup.normalizer (K : Set X))
    (hBT : B ≤ Subgroup.normalizer (T : Set X))
    (hcO : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      (∀ y ∈ elementaryGroup Q, g * y = y * g) → g = 1)
    {Yh : B →* ↥(elementaryGroup Q)} (hY : ∀ b : B, ActsAsConj e (b : X) (Yh b : V ≃ₗ[ZMod 2] V))
    {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ht1 : t ≠ 1)
    (hTact : ∀ x ∈ T, ActsAsConj e x 1 ∨ ActsAsConj e x t)
    (hTex : ∃ x ∈ T, ActsAsConj e x t) (b : B) :
    (Yh b : V ≃ₗ[ZMod 2] V) * t = t * (Yh b : V ≃ₗ[ZMod 2] V) := by
  obtain ⟨x0, hx0T, hx0⟩ := hTex
  have hbO : (Yh b : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (Yh b).2
  have hyT : (b : X) * x0 * (b : X)⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hBT b.2) x0).mp hx0T
  have hb1 : ActsAsConj e ((b : X)⁻¹) ((Yh b : V ≃ₗ[ZMod 2] V)⁻¹) := (hY b).inv
  have hbx : ActsAsConj e ((b : X) * x0) ((Yh b : V ≃ₗ[ZMod 2] V) * t) :=
    (hY b).mul (hTN hx0T) hx0
  have hbxb : ActsAsConj e ((b : X) * x0 * (b : X)⁻¹)
      ((Yh b : V ≃ₗ[ZMod 2] V) * t * (Yh b : V ≃ₗ[ZMod 2] V)⁻¹) :=
    hbx.mul (hBN (inv_mem b.2)) hb1
  have hsO : (Yh b : V ≃ₗ[ZMod 2] V) * t * (Yh b : V ≃ₗ[ZMod 2] V)⁻¹ ∈
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    mul_mem (mul_mem hbO ht) (inv_mem hbO)
  rcases hTact _ hyT with h | h
  · exfalso
    have := ActsAsConj.eq_of_mem_orthogonalGroup (hTN hyT) hcO hsO (one_mem _) hbxb h
    apply ht1
    have h2 : t = (Yh b : V ≃ₗ[ZMod 2] V)⁻¹ * 1 * (Yh b : V ≃ₗ[ZMod 2] V) := by
      rw [← this]
      group
    rw [h2]
    group
  · have := ActsAsConj.eq_of_mem_orthogonalGroup (hTN hyT) hcO hsO ht hbxb h
    calc (Yh b : V ≃ₗ[ZMod 2] V) * t
        = (Yh b : V ≃ₗ[ZMod 2] V) * t * (Yh b : V ≃ₗ[ZMod 2] V)⁻¹ * (Yh b : V ≃ₗ[ZMod 2] V) := by
          group
      _ = t * (Yh b : V ≃ₗ[ZMod 2] V) := by rw [this]

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

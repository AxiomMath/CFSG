module

public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.Timmesfeld.ARS.NaturalModule
public import CFSG.Quasithin.Background.G6PGroup

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Timmesfeld Matrix

variable {V : Type} [CommGroup V]

@[expose, instance_reducible] def slAction {K : Type*} [Field K] (G : Subgroup (MulAut V))
    (φ : ↥G ≃* SpecialLinearGroup (Fin 2) K) :
    DistribMulAction (SpecialLinearGroup (Fin 2) K) (Additive V) where
  smul x v := Additive.ofMul (((φ.symm x : ↥G) : MulAut V) (Additive.toMul v))
  one_smul v := by
    show Additive.ofMul (((φ.symm 1 : ↥G) : MulAut V) (Additive.toMul v)) = v
    simp
  mul_smul x y v := by
    show Additive.ofMul (((φ.symm (x * y) : ↥G) : MulAut V) (Additive.toMul v)) =
      Additive.ofMul (((φ.symm x : ↥G) : MulAut V)
        (Additive.toMul (Additive.ofMul (((φ.symm y : ↥G) : MulAut V) (Additive.toMul v)))))
    simp [MulAut.mul_apply]
  smul_zero x := by
    show Additive.ofMul (((φ.symm x : ↥G) : MulAut V) (Additive.toMul (0 : Additive V))) = 0
    simp
  smul_add x v w := by
    show Additive.ofMul (((φ.symm x : ↥G) : MulAut V) (Additive.toMul (v + w))) =
      Additive.ofMul (((φ.symm x : ↥G) : MulAut V) (Additive.toMul v)) +
        Additive.ofMul (((φ.symm x : ↥G) : MulAut V) (Additive.toMul w))
    simp

theorem isSLNatSection_of_quadratic [Finite V] {n : ℕ} (hn : 1 ≤ n) {G A : Subgroup (MulAut V)}
    (φ : ↥G ≃* SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (hA : (A.subgroupOf G).map φ.toMonoidHom = upperUnipotent (GaloisField 2 n))
    (hquad : IsQuadratic A) (hfix : fixV G = ⊥) (hw : fixV A ≠ ⊥)
    (hcard : Nat.card V = 4 ^ n) : IsSLNatSection G ⊤ ⊥ n := by
  set K := GaloisField 2 n with hK
  let _inst : DistribMulAction (SpecialLinearGroup (Fin 2) K) (Additive V) := slAction G φ
  have hact : ∀ (x : SpecialLinearGroup (Fin 2) K) (v : Additive V),
      x • v = Additive.ofMul (((φ.symm x : ↥G) : MulAut V) (Additive.toMul v)) := fun _ _ => rfl
  have hup : ∀ a ∈ upperUnipotent K, ((φ.symm a : ↥G) : MulAut V) ∈ A := by
    intro a ha
    rw [← hA] at ha
    obtain ⟨z, hz, rfl⟩ := ha
    simpa using Subgroup.mem_subgroupOf.1 hz
  have hfix' : ∀ v : Additive V, (∀ x : SpecialLinearGroup (Fin 2) K, x • v = v) → v = 0 := by
    intro v hv
    have : Additive.toMul v ∈ fixV G := by
      intro g hg
      have := hv (φ ⟨g, hg⟩)
      rw [hact] at this
      simpa using congrArg Additive.toMul this
    rw [hfix] at this
    exact this
  have hquad' : ∀ a ∈ upperUnipotent K, ∀ a' ∈ upperUnipotent K, ∀ v : Additive V,
      a' • (a • v - v) = a • v - v := by
    intro a ha a' ha' v
    have h1 : (φ.symm a : MulAut V) (Additive.toMul v) * (Additive.toMul v)⁻¹ ∈ commV A :=
      G6.mem_commV_of_mem (hup a ha) _
    have h2 := (mem_fixV.1 (hquad h1)) _ (hup a' ha')
    simp only [hact]
    apply Additive.toMul.injective
    simpa [div_eq_mul_inv] using h2
  obtain ⟨w₀, hw₀A, hw₀1⟩ : ∃ w₀ ∈ fixV A, w₀ ≠ 1 := by
    obtain ⟨⟨w₀, hw₀⟩, h1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hw
    exact ⟨w₀, hw₀, fun h0 => h1 (Subtype.ext h0)⟩
  have hw' : ∀ a ∈ upperUnipotent K, a • Additive.ofMul w₀ = Additive.ofMul w₀ := by
    intro a ha
    rw [hact]
    simp only [toMul_ofMul]
    rw [(mem_fixV.1 hw₀A) _ (hup a ha)]
  have hw0 : Additive.ofMul w₀ ≠ 0 := fun h0 => hw₀1 h0
  obtain ⟨θ, hθinj, -, -, hθ⟩ :=
    CFSG.Timmesfeld.ARS.exists_natural_of_quadratic hfix' hquad' hw' hw0
  have hcardK : Nat.card K = 2 ^ n := GaloisField.card 2 n (by omega)
  have hbij : Function.Bijective θ := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨hθinj, ?_⟩
    have h1 : Nat.card (Additive V) = Nat.card V := rfl
    rw [h1, hcard, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hcardK,
      ← pow_mul, show 4 = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]
  let e : (Fin 2 → K) ≃+ Additive V := AddEquiv.ofBijective θ hbij
  have he : ∀ w, e w = θ w := fun _ => rfl
  let β : ↥(⊤ : Subgroup V) →* Multiplicative (Fin 2 → K) :=
    { toFun := fun p => Multiplicative.ofAdd (e.symm (Additive.ofMul p.1))
      map_one' := by
        show Multiplicative.ofAdd (e.symm (Additive.ofMul (1 : V))) = 1
        have : Additive.ofMul (1 : V) = 0 := rfl
        rw [this, map_zero]
        rfl
      map_mul' := by
        intro p q
        show Multiplicative.ofAdd (e.symm (Additive.ofMul (p.1 * q.1))) =
          Multiplicative.ofAdd (e.symm (Additive.ofMul p.1)) *
            Multiplicative.ofAdd (e.symm (Additive.ofMul q.1))
        have : Additive.ofMul (p.1 * q.1) = Additive.ofMul p.1 + Additive.ofMul q.1 := rfl
        rw [this, map_add]
        rfl }
  refine ⟨fun _ _ _ _ => trivial, φ, β, ?_, ?_, ?_⟩
  · intro y
    refine ⟨⟨Additive.toMul (e (Multiplicative.toAdd y)), Subgroup.mem_top _⟩, ?_⟩
    show Multiplicative.ofAdd (e.symm (Additive.ofMul (Additive.toMul
      (e (Multiplicative.toAdd y))))) = y
    simp
  · ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    show Multiplicative.ofAdd (e.symm (Additive.ofMul p.1)) = 1 ↔ p.1 = 1
    constructor
    · intro h0
      have : e.symm (Additive.ofMul p.1) = 0 := h0
      have h1 : Additive.ofMul p.1 = 0 := by
        have := congrArg e this
        simpa using this
      exact h1
    · intro h0
      rw [h0]
      have : Additive.ofMul (1 : V) = 0 := rfl
      rw [this, map_zero]
      rfl
  · intro x p hp
    have h1 := hθ (φ x) (Multiplicative.toAdd (β p))
    rw [hact] at h1
    simp only [MulEquiv.symm_apply_apply] at h1
    have h2 : θ (Multiplicative.toAdd (β p)) = Additive.ofMul p.1 := by
      rw [← he]
      show e (e.symm (Additive.ofMul p.1)) = _
      simp
    rw [h2] at h1
    show Multiplicative.ofAdd (e.symm (Additive.ofMul ((x : MulAut V) p.1))) =
      Multiplicative.ofAdd (((φ x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
        (Multiplicative.toAdd (β p)))
    have h3 : Additive.ofMul ((x : MulAut V) p.1) =
        θ (((φ x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
          (Multiplicative.toAdd (β p))) := h1.symm
    rw [h3, ← he]
    simp

end CFSG.CGT.PushingUpLit.BHS

module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2
public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusData
public import CFSG.LieType.Universal.Spin.Twisted.RankOne

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.ClassicalInvolution.WeakCT.SU4
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Models

theorem exists_kleinData_free {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : f ≠ 0)
    {b c : GaloisField p f} (hirr : ∀ s : GaloisField p f, s ^ 2 + b * s + c ≠ 0) :
    ∃ inst : Algebra (GaloisField p f) (GaloisField p (2 * f)),
      Nonempty (@KleinData (GaloisField p f) (GaloisField p (2 * f)) _ _ inst
        (unitaryInvolution (GaloisField p (2 * f)) p f) b c) := by
  have : NeZero f := ⟨hf⟩
  have : NeZero (2 * f) := ⟨by omega⟩
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have hcardK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  have hcardF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hcardE : Nat.card (ShortField b c) = (p ^ f) ^ 2 := by
    rw [Nat.card_congr (QuadraticAlgebra.equivProd (-c) b), Nat.card_prod, hcardF]
    ring
  let : Fintype (ShortField b c) := Fintype.ofFinite _
  let : Fintype (GaloisField p (2 * f)) := Fintype.ofFinite _
  let : Fintype (GaloisField p f) := Fintype.ofFinite _
  let φ : ShortField b c ≃+* GaloisField p (2 * f) :=
    FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardE, hcardK])
  let τ : GaloisField p f →+* GaloisField p (2 * f) :=
    φ.toRingHom.comp (algebraMap (GaloisField p f) (ShortField b c))
  let inst : Algebra (GaloisField p f) (GaloisField p (2 * f)) := τ.toAlgebra
  have hτ : ∀ r, algebraMap (GaloisField p f) (GaloisField p (2 * f)) r =
      φ (algebraMap (GaloisField p f) (ShortField b c) r) := fun r => rfl
  have hω₀ : (⟨0, 1⟩ : ShortField b c) * ⟨0, 1⟩ =
      algebraMap (GaloisField p f) (ShortField b c) (-c) +
        algebraMap (GaloisField p f) (ShortField b c) b * ⟨0, 1⟩ := by
    ext <;> simp [QuadraticAlgebra.algebraMap_eq]
  have hspanE : ∀ t : ShortField b c, t = algebraMap (GaloisField p f) (ShortField b c) t.re +
      algebraMap (GaloisField p f) (ShortField b c) t.im * ⟨0, 1⟩ := by
    intro t
    ext <;> simp [QuadraticAlgebra.algebraMap_eq]
  have hστ : ∀ r : GaloisField p f,
      unitaryInvolution (GaloisField p (2 * f)) p f
        (algebraMap (GaloisField p f) (GaloisField p (2 * f)) r) =
        algebraMap (GaloisField p f) (GaloisField p (2 * f)) r := by
    intro r
    rw [unitaryInvolution_apply, ← map_pow]
    congr 1
    have h := FiniteField.pow_card r
    rwa [← Nat.card_eq_fintype_card, hcardF] at h
  have hω_sq : (-φ ⟨0, 1⟩) ^ 2 + algebraMap (GaloisField p f) (GaloisField p (2 * f)) b *
      (-φ ⟨0, 1⟩) + algebraMap (GaloisField p f) (GaloisField p (2 * f)) c = 0 := by
    have h := congrArg φ hω₀
    simp only [map_mul, map_add, map_neg] at h
    rw [hτ b, hτ c]
    linear_combination h
  have hspan : ∀ x : GaloisField p (2 * f), ∃ u v : GaloisField p f,
      x = algebraMap (GaloisField p f) (GaloisField p (2 * f)) u -
        algebraMap (GaloisField p f) (GaloisField p (2 * f)) v * (-φ ⟨0, 1⟩) := by
    intro x
    refine ⟨(φ.symm x).re, (φ.symm x).im, ?_⟩
    have h := congrArg φ (hspanE (φ.symm x))
    rw [RingEquiv.apply_symm_apply, map_add, map_mul] at h
    refine h.trans ?_
    rw [hτ, hτ]
    ring
  have h2K : (2 : GaloisField p (2 * f)) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have h2F : (2 : GaloisField p f) ≠ 0 := fun h =>
    h2K (by rw [← map_ofNat (algebraMap (GaloisField p f) (GaloisField p (2 * f))) 2, h, map_zero])
  have hσω : unitaryInvolution (GaloisField p (2 * f)) p f (-φ ⟨0, 1⟩) =
      -algebraMap (GaloisField p f) (GaloisField p (2 * f)) b - (-φ ⟨0, 1⟩) := by
    set ω : GaloisField p (2 * f) := -φ ⟨0, 1⟩ with hω
    set σ := unitaryInvolution (GaloisField p (2 * f)) p f with hσ
    have h1 : (σ ω) ^ 2 + algebraMap (GaloisField p f) (GaloisField p (2 * f)) b * σ ω +
        algebraMap (GaloisField p f) (GaloisField p (2 * f)) c = 0 := by
      have h := congrArg σ hω_sq
      simpa only [map_add, map_mul, map_pow, hστ, map_zero] using h
    have h2 : (σ ω - ω) * (σ ω + ω + algebraMap (GaloisField p f) (GaloisField p (2 * f)) b) =
        0 := by
      linear_combination h1 - hω_sq
    rcases mul_eq_zero.mp h2 with h | h
    · exfalso
      have hωσ : σ ω = ω := sub_eq_zero.mp h
      obtain ⟨z, hz⟩ := exists_unitaryInvolution_ne hcardK
      obtain ⟨u, v, hz'⟩ := hspan z
      apply hz
      rw [hz', map_sub, map_mul, hστ, hστ, hωσ]
    · linear_combination h
  have hdisc : b ^ 2 - 4 * c ≠ 0 := by
    intro h
    apply hirr (-b / 2)
    have h4 : (4 : GaloisField p f) = 2 * 2 := by norm_num
    field_simp
    linear_combination (-1 : GaloisField p f) * h
  exact ⟨inst, ⟨{
    ω := -φ ⟨0, 1⟩
    σσ := unitaryInvolution_involutive hcardK
    σ_alg := hστ
    ω_sq := hω_sq
    σ_ω := hσω
    span := hspan
    two_ne := h2K
    disc_ne := hdisc }⟩⟩

theorem disc_eq_neg_one {F : Type} [Field F] (e : ZMod 3 ≃+* F) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : b ^ 2 - 4 * c = -1 := by
  have key : ∀ b' c' : ZMod 3, (∀ s : ZMod 3, s ^ 2 + b' * s + c' ≠ 0) → b' ^ 2 - 4 * c' = -1 := by
    decide
  have h' : ∀ s : ZMod 3, s ^ 2 + e.symm b * s + e.symm c ≠ 0 := by
    intro s hs
    apply hirr (e s)
    have := congrArg e hs
    simpa using this
  have h := key _ _ h'
  apply e.symm.injective
  rw [map_sub, map_pow, map_mul, map_ofNat e.symm 4, map_neg, map_one]
  exact h

section Eps

variable {F K : Type} [Field F] [Field K] [Algebra F K] {σ₀ : K ≃+* K} {b c : F}

theorem kleinEps_sq (D : KleinData F K σ₀ b c) (h : b ^ 2 - 4 * c = -1) : D.ε ^ 2 = -1 := by
  have h1 := D.δ_mul_ε
  have h2 := D.δ_mul_δ
  rw [h, map_neg, map_one] at h2
  linear_combination D.ε ^ 2 * h2 - (D.δ * D.ε + 1) * h1

theorem kleinDelta_eq_neg_eps (D : KleinData F K σ₀ b c) (h : b ^ 2 - 4 * c = -1) :
    D.δ = -D.ε := by
  have h1 := D.δ_mul_ε
  have h2 := kleinEps_sq D h
  linear_combination D.δ * h2 - D.ε * h1

end Eps

end CFSG.ClassicalInvolution.Q3.Q3TW

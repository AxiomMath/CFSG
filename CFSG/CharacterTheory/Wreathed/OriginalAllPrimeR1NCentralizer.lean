module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersBasic
public import CFSG.CharacterTheory.Wreathed.ReducedNoncentralInvolution

public section

namespace CFSG.Wreathed.OriginalAllPrime.R1NFacts

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.OriginalAllPrime.ModelSignalizers CFSG.Wreathed.CentralSL2

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

theorem exists_eq_inl_mul_inr {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f)
    (hm2 : m = 2 ^ padicValInt 2 ((p ^ f : ℕ) - (if p ^ f % 4 = 1 then (1 : ℤ) else -1)))
    (hd : Odd (Nat.card Sigma)) (hb : ¬ IsSquare b)
    {W : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hW : ∀ g, g ∈ W ↔ g ∈ Subgroup.centralizer {weyl F} ∧ Odd (orderOf g))
    {x : SemilinearExtension F b m hm heven Sigma hSigma}
    (hx : x ∈ modelC b m hm heven Sigma hSigma) {r : ℕ} (hr : Odd r) (hxr : x ^ r = 1) :
    ∃ w ∈ W, ∃ σ : Sigma, x = SemidirectProduct.inl (specialInclusion F b m hm heven w) *
      SemidirectProduct.inr σ := by
  have hred :=
    ReducedInvolution.reduced_noncentral_involution_centralizer_has_exact_odd_torus_field_complement
    hp hpodd hf hcard _ rfl m hm heven hm2 Sigma hd b hSigma hb
  dsimp only at hred
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hWall⟩ := hred
  obtain ⟨-, ⟨φ, hφ⟩, hφall⟩ := hWall W hW
  obtain ⟨-, hΘ, -, -⟩ := hφall φ hφ
  obtain ⟨P⟩ : Nonempty (Sylow 2 (Subgroup.centralizer {involutionY F b m hm heven})) :=
    inferInstance
  obtain ⟨Θ, hΘ'⟩ := hΘ P
  set xC : modelC b m hm heven Sigma hSigma := ⟨x, hx⟩ with hxCdef
  set y := Θ.symm xC with hydef
  have hxy : x = ((Θ y : modelC b m hm heven Sigma hSigma) :
      SemilinearExtension F b m hm heven Sigma hSigma) :=
    (congrArg Subtype.val (Θ.apply_symm_apply xC)).symm
  have hy : y ^ r = 1 := by
    apply Θ.injective
    apply Subtype.ext
    rw [map_pow, map_one, Subgroup.coe_pow, OneMemClass.coe_one, ← hxy, hxr]
  have hy1 : y.1 = 1 := by
    have h1 : y.1 ^ r = 1 := by rw [← Prod.pow_fst, hy, Prod.fst_one]
    obtain ⟨s, hs⟩ := P.isPGroup' y.1
    have hcop : Nat.Coprime r (2 ^ s) := Nat.Coprime.pow_right s (Nat.coprime_two_right.mpr hr)
    have h := pow_gcd_eq_one.mpr ⟨h1, hs⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h
  refine ⟨y.2.left, y.2.left.2, y.2.right, ?_⟩
  rw [hxy, show y = (y.1, y.2) from rfl, hΘ', hy1]
  simp

theorem eq_one_of_forall_commute {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f)
    (hm2 : m = 2 ^ padicValInt 2 ((p ^ f : ℕ) - (if p ^ f % 4 = 1 then (1 : ℤ) else -1)))
    (hd : Odd (Nat.card Sigma)) (hb : ¬ IsSquare b)
    {W : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hW : ∀ g, g ∈ W ↔ g ∈ Subgroup.centralizer {weyl F} ∧ Odd (orderOf g))
    {X : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)} (hX : IsPGroup p X)
    (hXC : X ≤ modelC b m hm heven Sigma hSigma)
    (hXB : X ⊓ ModelSignalizers.modelBase b m hm heven Sigma hSigma = ⊥)
    {x : SemilinearExtension F b m hm heven Sigma hSigma} (hx : x ∈ X)
    (hc : ∀ w ∈ W, x * SemidirectProduct.inl (specialInclusion F b m hm heven w) =
      SemidirectProduct.inl (specialInclusion F b m hm heven w) * x) : x = 1 := by
  have hp2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hpodd)
  obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
  have hk' : x ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨w, hw, σ, rfl⟩ := exists_eq_inl_mul_inr hp hpodd hf hcard hm2 hd hb hW (hXC hx)
    hpodd.pow hk'
  by_cases hσ : σ = 1
  · subst hσ
    have hxB : SemidirectProduct.inl (specialInclusion F b m hm heven w) *
        SemidirectProduct.inr (1 : Sigma) ∈ X ⊓ ModelSignalizers.modelBase b m hm heven Sigma
          hSigma := by
      refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
      rw [map_one, mul_one]
      exact ⟨_, rfl⟩
    rw [hXB] at hxB
    exact hxB
  exfalso
  have hfix : ∀ t ∈ W, fieldSL F σ t = t := by
    intro t ht
    have hconj := hc t ht
    have hconj' : (SemidirectProduct.inl (specialInclusion F b m hm heven w) *
        SemidirectProduct.inr σ : SemilinearExtension F b m hm heven Sigma hSigma) *
        SemidirectProduct.inl (specialInclusion F b m hm heven t) *
        (SemidirectProduct.inl (specialInclusion F b m hm heven w) * SemidirectProduct.inr σ)⁻¹ =
          SemidirectProduct.inl (specialInclusion F b m hm heven t) := by
      rw [hconj, mul_inv_cancel_right]
    rw [semidirect_conj_inl] at hconj'
    have h1 := SemidirectProduct.inl_injective hconj'
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.left_inr,
      SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.right_inr,
      one_mul, map_one, mul_one, fieldAction_specialInclusion] at h1
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    have h2 := specialInclusion_injective F b m hm heven h1
    have hσt : fieldSL F σ t ∈ W :=
      CFSG.Wreathed.OddFieldTorus.fieldAction_mem W hW (σ : F ≃+* F) ht
    have hcomm := CFSG.Wreathed.OddFieldTorus.W_comm W hW ⟨w, hw⟩ ⟨_, hσt⟩
    have hcomm' : w * fieldSL F σ t = fieldSL F σ t * w := congrArg Subtype.val hcomm
    rw [hcomm', mul_inv_cancel_right] at h2
    exact h2
  have hp2' : p ≠ 2 := hp2
  obtain ⟨-, -, -, -, hWall⟩ :=
    CFSG.Wreathed.OddFieldTorus.odd_field_fixed_torus_derived_centralizer hp hp2' hf hcard _ rfl
      m hm2 Sigma hd
  obtain ⟨-, -, hσall, -⟩ := hWall W hW
  have hσ1 : (σ : F ≃+* F) ≠ 1 := fun h => hσ (Subtype.ext h)
  have hlt := (hσall σ σ.2).2.2.2.2 hσ1
  have heq : Nat.card {g // g ∈ W ∧ Matrix.SpecialLinearGroup.map (σ : F ≃+* F).toRingHom g = g} =
      Nat.card W :=
    Nat.card_congr ⟨fun g => ⟨g.1, g.2.1⟩, fun g => ⟨g.1, g.2, hfix g.1 g.2⟩, fun _ => rfl,
      fun _ => rfl⟩
  rw [heq] at hlt
  have hpos : 0 < Nat.card W := Nat.card_pos
  nlinarith

end CFSG.Wreathed.OriginalAllPrime.R1NFacts

module

public import CFSG.ClassicalInvolution.Q3.TL4MF163PGL
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

namespace MF163

open CFSG.GorensteinWalter

section Cyclic

theorem ringAut_isCyclic (K : Type) [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K)) :
    IsCyclic (K ≃+* K) := by
  rcases hK with ⟨p, n, hp, _hpOdd, _hn, hcard⟩
  let : Fintype K := Fintype.ofFinite K
  have hcardF : Fintype.card K = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let : Fact p.Prime := ⟨hp⟩
  let : CharP K p := charP_of_card_eq_prime_pow hcardF
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let e : (K ≃+* K) ≃* (K ≃ₐ[ZMod p] K) := {
    toFun := fun sigma =>
      AlgEquiv.ofRingEquiv (f := sigma) (by
        intro x
        have h :
            (sigma.toRingHom.comp (algebraMap (ZMod p) K) :
              ZMod p →+* K) = algebraMap (ZMod p) K :=
          RingHom.ext_zmod _ _
        exact DFunLike.congr_fun h x)
    invFun := fun sigma => sigma.toRingEquiv
    left_inv := by intro sigma; ext x; rfl
    right_inv := by intro sigma; ext x; rfl
    map_mul' := by intro sigma tau; ext x; rfl }
  exact e.isCyclic.mpr inferInstance

theorem eq_of_mul_self_eq_one {G : Type*} [Group G] [Finite G] [IsCyclic G] {u v : G}
    (hu : u * u = 1) (hv : v * v = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) : u = v := by
  classical
  have := Fintype.ofFinite G
  by_contra huv
  have hsub : ({1, u, v} : Finset G) ⊆ Finset.univ.filter (fun a : G => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> simp [sq, hu, hv]
  have hcard : ({1, u, v} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hu1, Ne.symm hv1]), Finset.card_pair huv]
  have hle := Finset.card_le_card hsub
  have h2 : (Finset.univ.filter (fun a : G => a ^ 2 = 1)).card ≤ 2 := by
    convert IsCyclic.card_pow_eq_one_le (α := G) (n := 2) (by norm_num)
  omega

end Cyclic

section Gamma

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem eq_inl_of_right_eq_one {x : PGammaL2 F} (h : x.right = 1) :
    x = SemidirectProduct.inl x.left :=
  SemidirectProduct.ext rfl (by rw [h]; rfl)

theorem pgammaL2_eq_of_quat (hK : IsOddPrimePower (Nat.card F)) (h2 : (2 : F) ≠ 0)
    {c₀ : PGL2 F} {y b : PGammaL2 F} (hc2 : c₀ ^ 2 ≠ 1) (hc4 : c₀ ^ 4 = 1)
    (hy : y * SemidirectProduct.inl c₀ * y⁻¹ = (SemidirectProduct.inl c₀)⁻¹)
    (hy2 : y * y = SemidirectProduct.inl c₀ ^ 2) (hb : b * b = 1)
    (hbc : b * SemidirectProduct.inl c₀ = SemidirectProduct.inl c₀ * b) (hby : b * y = y * b) :
    b = 1 ∨ b = SemidirectProduct.inl c₀ ^ 2 := by
  have : IsCyclic (F ≃+* F) := ringAut_isCyclic F hK
  have : Finite (F ≃+* F) :=
    Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective
  set c : PGammaL2 F := SemidirectProduct.inl c₀ with hcdef
  have hyr : y.right ≠ 1 := by
    intro h
    have hye := eq_inl_of_right_eq_one h
    rw [hye, hcdef, ← map_inv, ← map_inv, ← map_mul, ← map_mul, SemidirectProduct.inl_inj] at hy
    have h1 := pgl2_mul_self_of_inv h2 hc2 hc4 hy
    apply hc2
    rw [hye, ← map_mul, h1, map_one] at hy2
    exact (SemidirectProduct.inl_injective (by rw [map_pow, ← hy2, map_one])).symm
  have hyr2 : y.right * y.right = 1 := by
    have := congrArg SemidirectProduct.right hy2
    rwa [SemidirectProduct.mul_right, hcdef, ← map_pow, SemidirectProduct.right_inl] at this
  by_cases hbr : b.right = 1
  · have hbe := eq_inl_of_right_eq_one hbr
    rw [hbe, hcdef, ← map_mul, ← map_mul, SemidirectProduct.inl_inj] at hbc
    rw [hbe, ← map_mul, ← map_one SemidirectProduct.inl, SemidirectProduct.inl_inj] at hb
    rcases pgl2_eq_of_comm h2 hc2 hc4 hbc hb with h | h
    · left
      rw [hbe, h, map_one]
    · right
      rw [hbe, h, map_pow]
  · exfalso
    have hbr2 : b.right * b.right = 1 := by
      have := congrArg SemidirectProduct.right hb
      rwa [SemidirectProduct.mul_right] at this
    have hbyr : b.right = y.right := eq_of_mul_self_eq_one hbr2 hyr2 hbr hyr
    set w : PGammaL2 F := b * y⁻¹ with hw
    have hwr : w.right = 1 := by
      rw [hw, SemidirectProduct.mul_right, SemidirectProduct.inv_right, hbyr, mul_inv_cancel]
    have hwe := eq_inl_of_right_eq_one hwr
    have hyinv : y⁻¹ * c * y = c⁻¹ := by
      have h1 : y * c⁻¹ * y⁻¹ = c := by
        have := congrArg (·⁻¹) hy
        simpa [mul_assoc] using this
      calc y⁻¹ * c * y = y⁻¹ * (y * c⁻¹ * y⁻¹) * y := by rw [h1]
        _ = c⁻¹ := by group
    have hwc : w * c * w⁻¹ = c⁻¹ := by
      have hbc' : b * c⁻¹ * b⁻¹ = c⁻¹ := by
        have : b * c⁻¹ = c⁻¹ * b := by
          rw [mul_inv_eq_iff_eq_mul, mul_assoc, hbc, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [this, mul_inv_cancel_right]
      calc w * c * w⁻¹ = b * (y⁻¹ * c * y) * b⁻¹ := by rw [hw]; group
        _ = c⁻¹ := by rw [hyinv, hbc']
    rw [hwe, hcdef, ← map_inv, ← map_inv, ← map_mul, ← map_mul, SemidirectProduct.inl_inj] at hwc
    have hww := pgl2_mul_self_of_inv h2 hc2 hc4 hwc
    have hw2 : w * w = c ^ 2 := by
      have hby' : b * y⁻¹ = y⁻¹ * b := by
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, hby, ← mul_assoc, inv_mul_cancel, one_mul]
      have hc2' : (c ^ 2)⁻¹ = c ^ 2 := by
        rw [inv_eq_iff_mul_eq_one, ← pow_add, hcdef, ← map_pow, hc4, map_one]
      calc w * w = b * (y⁻¹ * b) * y⁻¹ := by rw [hw]; group
        _ = b * (b * y⁻¹) * y⁻¹ := by rw [hby']
        _ = (b * b) * (y * y)⁻¹ := by group
        _ = c ^ 2 := by rw [hb, hy2, hc2', one_mul]
    apply hc2
    rw [hwe, ← map_mul, hww, map_one, hcdef, ← map_pow] at hw2
    exact (SemidirectProduct.inl_injective hw2).symm

theorem right_a_two (hK : IsOddPrimePower (Nat.card F)) (ρ : QuaternionGroup 2 →* PGammaL2 F) :
    (ρ (QuaternionGroup.a 2)).right = 1 := by
  have : IsCyclic (F ≃+* F) := ringAut_isCyclic F hK
  have hcomm : ∀ x y : F ≃+* F, x * y = y * x := fun x y => IsCyclic.commGroup.mul_comm x y
  have h : (QuaternionGroup.a 2 : QuaternionGroup 2) =
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 * (QuaternionGroup.xa 0)⁻¹ *
        (QuaternionGroup.a 1)⁻¹ := by decide
  rw [h, map_mul, map_mul, map_mul, map_inv, map_inv, SemidirectProduct.mul_right,
    SemidirectProduct.mul_right, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
    SemidirectProduct.inv_right, hcomm (ρ (QuaternionGroup.xa 0)).right]
  group

theorem pgammaL2_eq_of_quat_hom (hK : IsOddPrimePower (Nat.card F)) (h2 : (2 : F) ≠ 0)
    (ρ : QuaternionGroup 2 →* PGammaL2 F) (hρ : ρ (QuaternionGroup.a 2) ≠ 1) {b : PGammaL2 F}
    (hb : b * b = 1) (hbρ : ∀ g, b * ρ g = ρ g * b) : b = 1 ∨ b = ρ (QuaternionGroup.a 2) := by
  have : IsCyclic (F ≃+* F) := ringAut_isCyclic F hK
  have : Finite (F ≃+* F) :=
    Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective
  have core : ∀ g h : QuaternionGroup 2, (ρ g).right = 1 → g ^ 2 = QuaternionGroup.a 2 →
      h * g * h⁻¹ = g⁻¹ → h * h = g ^ 2 → b = 1 ∨ b = ρ (QuaternionGroup.a 2) := by
    intro g h hg hg2 hhg hh
    have hge := eq_inl_of_right_eq_one hg
    have hg4 : g ^ 4 = 1 := by
      have h4 : g ^ 4 = (g ^ 2) ^ 2 := by rw [← pow_mul]
      rw [h4, hg2]
      decide
    have hc2 : (ρ g).left ^ 2 ≠ 1 := by
      intro h1
      apply hρ
      rw [← hg2, map_pow, hge, ← map_pow, h1, map_one]
    have hc4 : (ρ g).left ^ 4 = 1 := by
      have h5 : (SemidirectProduct.inl ((ρ g).left ^ 4) : PGammaL2 F) =
          SemidirectProduct.inl 1 := by
        rw [map_pow, ← hge, ← map_pow, hg4, map_one, map_one]
      exact SemidirectProduct.inl_injective h5
    rcases pgammaL2_eq_of_quat hK h2 (y := ρ h) hc2 hc4
        (by rw [← hge, ← map_inv, ← map_inv, ← map_mul, ← map_mul, hhg])
        (by rw [← map_mul, hh, map_pow]; exact congrArg (· ^ 2) hge) hb
        (by rw [← hge]; exact hbρ g) (hbρ h) with h1 | h1
    · exact Or.inl h1
    · right
      rw [h1, ← hge, ← map_pow, hg2]
  have hr2 : ∀ g : QuaternionGroup 2, g ^ 2 = QuaternionGroup.a 2 →
      (ρ g).right * (ρ g).right = 1 := by
    intro g hg
    rw [← SemidirectProduct.mul_right, ← map_mul, ← sq, hg, right_a_two hK]
  by_cases h1 : (ρ (QuaternionGroup.a 1)).right = 1
  · exact core (QuaternionGroup.a 1) (QuaternionGroup.xa 0) h1 (by decide) (by decide)
      (by decide)
  by_cases h2' : (ρ (QuaternionGroup.xa 0)).right = 1
  · exact core (QuaternionGroup.xa 0) (QuaternionGroup.a 1) h2' (by decide) (by decide)
      (by decide)
  have h3 : (ρ (QuaternionGroup.a 1 * QuaternionGroup.xa 0)).right = 1 := by
    have he := eq_of_mul_self_eq_one (hr2 _ (by decide)) (hr2 _ (by decide)) h1 h2'
    rw [map_mul, SemidirectProduct.mul_right, he, ← SemidirectProduct.mul_right, ← map_mul,
      ← sq, show (QuaternionGroup.xa 0 : QuaternionGroup 2) ^ 2 = QuaternionGroup.a 2 by decide,
      right_a_two hK]
  exact core (QuaternionGroup.a 1 * QuaternionGroup.xa 0) (QuaternionGroup.a 1) h3 (by decide)
    (by decide) (by decide)

end Gamma

end MF163

end CFSG.ClassicalInvolution.Q3.TL4

module

public import CFSG.LieType.Steinberg.Classical.SpinPlus.Basic
public import CFSG.LieType.Steinberg.PartB

public noncomputable section

namespace CFSG.LieType.Steinberg.SpinPlus

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.PlusCT CFSG.LieType.Steinberg.SpinFrame
  CFSG.LieType.RootSystem

variable {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)

theorem coroot_eq_dotProduct (hn2 : 2 ≤ n) (k : Fin n) (v : Fin n → ℤ) :
    coroot (cartanD n) k v = toStdD n v ⬝ᵥ toStdD n (Pi.single k 1) := by
  by_cases h : k.val + 1 < n
  · rw [coroot_cartanD_of_lt n h, toStdD_single_of_lt n h, dotProduct_sub, dotProduct_single,
      dotProduct_single, mul_one, mul_one]
  · have hk : (⟨k.val - 1, by omega⟩ : Fin n) = ⟨n - 2, by omega⟩ := Fin.ext (by simp only; omega)
    rw [coroot_cartanD_of_not_lt n h, toStdD_single_of_not_lt n h hn2, dotProduct_add,
      dotProduct_single, dotProduct_single, mul_one, mul_one, hk]

theorem weylElement_eq (k : Fin n) (t : Kˣ) :
    weylElement (x n K hn) k t = torusD K hn k t * weylD K hn k := by
  rw [weylElement, x_single, x_neg_single, ← map_mul, ← map_mul, ← weylSL2_eq, rankOneD,
    longSL2_weylSL2]
  rfl

theorem weyl (i : Fin n) {β : Fin n → ℤ} (hβ : β ∈ roots (isFiniteType_cartanD n) ∅) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (t : Kˣ) (u : K),
      weylElement (x n K hn) i t * x n K hn β u * (weylElement (x n K hn) i t)⁻¹ =
        x n K hn (reflection (cartanD n) i β)
          ((ε : K) * ((t ^ (-(∑ j, cartanD n i j * β j)) : Kˣ) : K) * u) := by
  obtain ⟨k, l, hkl, u, v, hβ'⟩ := exists_toStdD_eq_of_mem_rootsD (by omega) hβ
  obtain ⟨ε, hε, hconj⟩ := longWeyl_conj_rootElt (K := K) (plusFrame n K hn)
    (rootIdxD_ne n (by omega) i) true (rootSignD n i) hkl hβ'
  refine ⟨ε, hε, fun t c => ?_⟩
  have hrefl := toStdD_reflection_eq (by omega) i hβ'
  have hlong : IsLong (toStdD n (reflection (cartanD n) i β)) :=
    (isLong_toStdD_iff (by omega)).mpr ((Φ n K hn).refl_mem i β hβ)
  have hii : cartanD n i i = 2 := by simp [cartanD]
  rw [weylElement_eq, _root_.mul_inv_rev,
    show ∀ a b c : spinGroup (quadPlus n K), a * b * c * (b⁻¹ * a⁻¹) = a * (b * c * b⁻¹) * a⁻¹ by
      intros; group]
  unfold x
  rw [weylD, hconj c, ← hrefl, torusD, longTorus_conj_rootElt _ _ _ _ _ hlong, ← toStdD_single_eq
    (by omega), ← coroot_eq_dotProduct (by omega), coroot_reflection hii, coroot_apply]
  congr 1
  ring

theorem rankOne (k : Fin n) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) K →* spinGroup (quadPlus n K), Function.Injective φ ∧
      (∀ c, φ (sl2Upper c) = x n K hn (Pi.single k 1) c) ∧
        ∀ c, φ (sl2Lower c) = x n K hn (-Pi.single k 1) c :=
  ⟨rankOneD K hn k, longSL2_injective _ _ _ _, fun c => (x_single hn k c).symm,
    fun c => (x_neg_single hn k c).symm⟩

end CFSG.LieType.Steinberg.SpinPlus

module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteLinearized

public section

namespace CFSG.LieType.Steinberg.CentralExt

variable {K : Type} [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]

theorem zpow_form_eq_zero {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) {e₁ e₂ : ℤ}
    (hnd : ∀ i j : ℕ, i < f → j < f →
      ¬ ((p ^ f - 1 : ℕ) : ℤ) ∣ (p : ℤ) ^ i * e₁ + (p : ℤ) ^ j * e₂)
    (F : K → K → ZMod p) (hF₁ : ∀ c₁ c₂ d, F (c₁ + c₂) d = F c₁ d + F c₂ d)
    (hF₂ : ∀ c d₁ d₂, F c (d₁ + d₂) = F c d₁ + F c d₂)
    (hFT : ∀ (t : Kˣ) c d, F (((t ^ e₁ : Kˣ) : K) * c) (((t ^ e₂ : Kˣ) : K) * d) = F c d) :
    ∀ c d, F c d = 0 := by
  classical
  let ι : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hι : Function.Injective ι := ι.injective
  let G : K →+ K →+ K := AddMonoidHom.mk'
    (fun c => AddMonoidHom.mk' (fun d => ι (F c d)) fun d₁ d₂ => by rw [hF₂, map_add])
    fun c₁ c₂ => by
      ext d
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [hF₁, map_add]
  have hG : ∀ c d, G c d = ι (F c d) := fun _ _ => rfl
  obtain ⟨-, h2, -⟩ := CFSG.LocalAnalysis.ComponentInitial.finite_field_linearized_map_bases
    hp.out hf hK
  obtain ⟨A, hA, hAuniq⟩ := h2 G
  have hcoef : ∀ (t : Kˣ) (i j : Fin f),
      A i j * (((t ^ e₁ : Kˣ) : K) ^ p ^ (i : ℕ) * ((t ^ e₂ : Kˣ) : K) ^ p ^ (j : ℕ)) =
        A i j := by
    intro t
    have huniq := hAuniq
      (fun i j => A i j * (((t ^ e₁ : Kˣ) : K) ^ p ^ (i : ℕ) * ((t ^ e₂ : Kˣ) : K) ^ p ^ (j : ℕ)))
      fun x y => by
        have h1 : G x y = G (((t ^ e₁ : Kˣ) : K) * x) (((t ^ e₂ : Kˣ) : K) * y) := by
          rw [hG, hG, hFT]
        rw [h1, hA]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [mul_pow, mul_pow]
        ring
    intro i j
    exact congrFun (congrFun huniq i) j
  have hA0 : ∀ i j, A i j = 0 := by
    intro i j
    by_contra hne
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hord : orderOf g = p ^ f - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
    refine hnd i j i.2 j.2 ?_
    have key := (mul_eq_left₀ hne).1 (hcoef g i j)
    have hg1 : g ^ ((p : ℤ) ^ (i : ℕ) * e₁ + (p : ℤ) ^ (j : ℕ) * e₂) = 1 := by
      apply Units.ext
      rw [zpow_add, mul_comm ((p : ℤ) ^ (i : ℕ)), mul_comm ((p : ℤ) ^ (j : ℕ)), zpow_mul,
        zpow_mul, ← Nat.cast_pow, ← Nat.cast_pow, zpow_natCast, zpow_natCast, Units.val_mul,
        Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_one]
      exact key
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.2 hg1
  intro c d
  have h0 : G c d = 0 := by
    rw [hA]
    simp [hA0]
  exact hι (by rw [map_zero, ← hG]; exact h0)

end CFSG.LieType.Steinberg.CentralExt

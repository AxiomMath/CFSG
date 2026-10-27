module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagFin

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Fixes


theorem rfFx_three_dvd_mod_sub (n : ℕ) : (3 : ℤ) ∣ ((n % 3 : ℕ) : ℤ) - (n : ℤ) := by
  omega

theorem rfFx_getD_comb (a b : ℕ) : ∀ (k₁ k₂ : List ℕ), k₁.length = k₂.length → ∀ i : ℕ,
    (comb a b k₁ k₂).getD i 0 = (a * k₁.getD i 0 + b * k₂.getD i 0) % 3
  | [], [], _, i => by simp [comb]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | _ :: _, _ :: _, _, 0 => by simp [comb]
  | p :: ps, q :: qs, h, i + 1 => by
    have ih := rfFx_getD_comb a b ps qs (by simpa using h) i
    simpa [comb] using ih

theorem rfFx_sum_lin (c f g : Fin Tag.E6.rank → ℤ) (a b : ℤ) :
    ∑ i, (a * f i + b * g i) * c i = a * ∑ i, f i * c i + b * ∑ i, g i * c i := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem rfFx_dvd_of_congr (c f g : Fin Tag.E6.rank → ℤ) (t : Fin Tag.E6.rank)
    (hfg : ∀ i, (3 : ℤ) ∣ g i - f i) (hf : (3 : ℤ) ∣ (∑ i, f i * c i) - f t) :
    (3 : ℤ) ∣ (∑ i, g i * c i) - g t := by
  have e : (∑ i, g i * c i) - g t =
      ((∑ i, f i * c i) - f t) + ((∑ i, (g i - f i) * c i) - (g t - f t)) := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [e]
  exact dvd_add hf (dvd_sub (Finset.dvd_sum fun i _ => Dvd.dvd.mul_right (hfg i) _) (hfg t))

theorem rfFx_R_lin (c x y : Fin Tag.E6.rank → ℤ) (a b : ℤ) (t : Fin Tag.E6.rank)
    (h₁ : (3 : ℤ) ∣ (∑ i, x i * c i) - x t) (h₂ : (3 : ℤ) ∣ (∑ i, y i * c i) - y t) :
    (3 : ℤ) ∣ (∑ i, (a * x i + b * y i) * c i) - (a * x t + b * y t) := by
  have e : (∑ i, (a * x i + b * y i) * c i) - (a * x t + b * y t) =
      a * ((∑ i, x i * c i) - x t) + b * ((∑ i, y i * c i) - y t) := by
    rw [rfFx_sum_lin]
    ring
  rw [e]
  exact dvd_add (Dvd.dvd.mul_left h₁ a) (Dvd.dvd.mul_left h₂ b)

theorem rfFx_getD_ofFn (k : Fin Tag.E6.rank → ℕ) (i : Fin Tag.E6.rank) :
    (List.ofFn fun j : Fin Tag.E6.rank => k j % 3).getD (i : ℕ) 0 = k i % 3 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn]

theorem rfFixes_comb (w : WeylGroup Tag.E6) {κ₁ κ₂ : List ℕ}
    (h₁ : κ₁.length = Tag.E6.rank) (h₂ : κ₂.length = Tag.E6.rank) (a b : ℕ)
    (hf₁ : RfFixes w κ₁) (hf₂ : RfFixes w κ₂) : RfFixes w (comb a b κ₁ κ₂) := by
  intro t
  have hlen : κ₁.length = κ₂.length := h₁.trans h₂.symm
  refine rfFx_dvd_of_congr (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ))
    (fun i : Fin Tag.E6.rank =>
      (a : ℤ) * ((κ₁.getD (i : ℕ) 0 : ℕ) : ℤ) + (b : ℤ) * ((κ₂.getD (i : ℕ) 0 : ℕ) : ℤ))
    (fun i : Fin Tag.E6.rank => (((comb a b κ₁ κ₂).getD (i : ℕ) 0 : ℕ) : ℤ)) t ?_ ?_
  · intro i
    simp only [rfFx_getD_comb a b κ₁ κ₂ hlen]
    exact_mod_cast rfFx_three_dvd_mod_sub (a * κ₁.getD (i : ℕ) 0 + b * κ₂.getD (i : ℕ) 0)
  · exact rfFx_R_lin _ _ _ _ _ t (hf₁ t) (hf₂ t)

theorem rfFixes_of_fin (w : WeylGroup Tag.E6) (k : Fin Tag.E6.rank → ℕ)
    (h : ∀ t : Fin Tag.E6.rank, (3 : ℤ) ∣
      (∑ i : Fin Tag.E6.rank, (k i : ℤ) * (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) i) -
        (k t : ℤ)) :
    RfFixes w (List.ofFn fun i : Fin Tag.E6.rank => k i % 3) := by
  intro t
  refine rfFx_dvd_of_congr (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ))
    (fun i : Fin Tag.E6.rank => ((k i : ℕ) : ℤ))
    (fun i : Fin Tag.E6.rank =>
      (((List.ofFn fun j : Fin Tag.E6.rank => k j % 3).getD (i : ℕ) 0 : ℕ) : ℤ))
    t ?_ (h t)
  intro i
  simp only [rfFx_getD_ofFn]
  exact_mod_cast rfFx_three_dvd_mod_sub (k i)

end Fixes

end CFSG.LieType.SeitzGeneration.ExcWideThree

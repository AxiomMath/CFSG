module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveWords

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Five

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem exists_rep_wordA {n j : ℕ} {gs gsInv : Array (Array ℕ)} {Gs : ℕ → Equiv.Perm (Fin n)}
    {K : Subgroup (Equiv.Perm (Fin n))} (hS : ∀ h < j, Rep n gs[h]! (Gs h))
    (hSinv : ∀ h < j, Rep n gsInv[h]! (Gs h)⁻¹) (hK : ∀ h < j, Gs h ∈ K) :
    ∀ w : List ℤ, lettersOK j w = true → ∃ g ∈ K, Rep n (wordA n gs gsInv w) g
  | [], _ => ⟨1, K.one_mem, rep_idA⟩
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : lettersOK j w = true := by
      simpa [lettersOK, List.all_eq_true] using hw
    obtain ⟨g, hgK, hg⟩ := exists_rep_wordA hS hSinv hK w hw'
    have hlet := rep_letterA (gs := Gs) hS hSinv ⟨hl0, hlj⟩
    refine ⟨_, K.mul_mem ?_ hgK, rep_compA hlet hg⟩
    by_cases hpos : decide (0 < l) = true
    · rw [ite_eq_left hpos]
      exact hK _ (by omega)
    · rw [ite_eq_right hpos]
      exact K.inv_mem (hK _ (by omega))

theorem yPows_get {a : ℕ} (ha : a < 6) : yPows[a]! = pw yA a := by
  have h : a < yPows.size := by simp [yPows, ha]
  rw [getElem!_pos yPows a h]
  simp [yPows]

theorem rep_yConjT {Y V : Equiv.Perm (Fin 3510)} (hy : Rep 3510 yA Y) {v : Array Nat}
    (hv : Rep 3510 v V) {a : ℕ} (ha : a ≤ 5) :
    Rep 3510 (yConjT v a) (Y ^ a * (V * Y ^ (5 - a))) := by
  unfold yConjT
  rw [yPows_get (by omega), yPows_get (by omega)]
  exact rep_compA (rep_pw hy a) (rep_compA hv (rep_pw hy (5 - a)))

theorem rep_p24 {V : Equiv.Perm (Fin 3510)} {v : Array Nat} (hv : Rep 3510 v V) :
    Rep 3510 (p24 v) (V ^ 24) := by
  unfold p24
  have h3 : Rep 3510 (compA 3510 v (compA 3510 v v)) (V ^ 3) := by
    have := rep_compA hv (rep_compA hv hv)
    rwa [← pow_three] at this
  have h6 := rep_compA h3 h3
  rw [← pow_add] at h6
  have h12 := rep_compA h6 h6
  rw [← pow_add] at h12
  have h24 := rep_compA h12 h12
  rwa [← pow_add] at h24

theorem rep_star5W1 {Y V : Equiv.Perm (Fin 3510)} (hy : Rep 3510 yA Y) {v : Array Nat}
    (hv : Rep 3510 v V) :
    Rep 3510 (star5W1 v) ((Y ^ 0 * (V * Y ^ (5 - 0))) * ((Y ^ 1 * (V * Y ^ (5 - 1))) *
      ((Y ^ 2 * (V * Y ^ (5 - 2))) * (Y ^ 3 * (V * Y ^ (5 - 3)))))) :=
  rep_compA (rep_yConjT hy hv (by omega)) (rep_compA (rep_yConjT hy hv (by omega))
    (rep_compA (rep_yConjT hy hv (by omega)) (rep_yConjT hy hv (by omega))))

theorem rep_star5W2 {Y V : Equiv.Perm (Fin 3510)} (hy : Rep 3510 yA Y) {v : Array Nat}
    (hv : Rep 3510 v V) :
    Rep 3510 (star5W2 v) ((Y ^ 0 * (V * Y ^ (5 - 0))) * ((Y ^ 0 * (V * Y ^ (5 - 0))) *
      ((Y ^ 1 * (V * Y ^ (5 - 1))) * (Y ^ 4 * (V * Y ^ (5 - 4)))))) :=
  rep_compA (rep_yConjT hy hv (by omega)) (rep_compA (rep_yConjT hy hv (by omega))
    (rep_compA (rep_yConjT hy hv (by omega)) (rep_yConjT hy hv (by omega))))

end CFSG.AGLEmbedding.KFactProofs.Fi22Five

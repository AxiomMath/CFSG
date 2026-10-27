module

public import CFSG.Sporadic.Schreier.ONPermArr
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Set.Card

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.ONSchreier CFSG.ONSchreier.Native

variable {H : Type*} [Group H]

@[expose] def letterVal (gs : ℕ → H) (l : ℤ) : H :=
  if 0 < l then gs (l.toNat - 1) else (gs ((-l).toNat - 1))⁻¹

@[expose] def wordProd (gs : ℕ → H) (w : List ℤ) : H := (w.map (letterVal gs)).prod

@[simp] theorem wordProd_nil (gs : ℕ → H) : wordProd gs [] = 1 := rfl

@[simp] theorem wordProd_cons (gs : ℕ → H) (l : ℤ) (w : List ℤ) :
    wordProd gs (l :: w) = letterVal gs l * wordProd gs w := by
  simp [wordProd]

theorem wordProd_append (gs : ℕ → H) (u v : List ℤ) :
    wordProd gs (u ++ v) = wordProd gs u * wordProd gs v := by
  simp [wordProd]

@[expose] def conjBy (x u : H) : H := x * u * x⁻¹

theorem conjBy_def (x u : H) : conjBy x u = x * u * x⁻¹ := rfl

theorem letterVal_neg (gs : ℕ → H) {l : ℤ} (hl : l ≠ 0) :
    letterVal gs (-l) = (letterVal gs l)⁻¹ := by
  unfold letterVal
  by_cases h : 0 < l
  · have h' : ¬ 0 < -l := by omega
    rw [ite_eq_right h', ite_eq_left h]
    simp
  · have h' : 0 < -l := by omega
    rw [ite_eq_left h', ite_eq_right h]
    simp

theorem mem_centralizer_of_map_commute {K : Type*} [Group K] (f : H →* K)
    (hf : Function.Injective f) {x y : H} (h : f x * f y = f y * f x) :
    x ∈ Subgroup.centralizer ({y} : Set H) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply hf
  rw [map_mul, map_mul]
  exact h

theorem mul_conjBy_of_commute {K : Type*} [Group K] {a c : K} (h : c * a = a * c) (v : K) :
    a * conjBy c v = conjBy c (a * v) := by
  unfold conjBy
  calc a * (c * v * c⁻¹) = (a * c) * v * c⁻¹ := by simp [mul_assoc]
    _ = (c * a) * v * c⁻¹ := by rw [h]
    _ = c * (a * v) * c⁻¹ := by simp [mul_assoc]

theorem map_conjBy {K : Type*} [Group K] (f : H →* K) (c u : H) :
    f (conjBy c u) = conjBy (f c) (f u) := by
  simp [conjBy_def, map_mul, map_inv]

theorem map_commute_of_mem_centralizer {K : Type*} [Group K] (f : H →* K) {a c : H}
    (hc : c ∈ Subgroup.centralizer ({a} : Set H)) : f c * f a = f a * f c := by
  have h : c * a = a * c := Subgroup.mem_centralizer_singleton_iff.1 hc
  rw [← map_mul, ← map_mul, h]

theorem ncard_fixed_conjBy {Ω : Type*} (ρ : H →* Equiv.Perm Ω) (c w : H) :
    Set.ncard {p : Ω | ρ (conjBy c w) p = p} = Set.ncard {p : Ω | ρ w p = p} := by
  have : {p : Ω | ρ (conjBy c w) p = p} = ρ c '' {p : Ω | ρ w p = p} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_image, conjBy_def, map_mul, map_inv,
      Equiv.Perm.mul_apply]
    constructor
    · intro h
      refine ⟨(ρ c)⁻¹ p, ?_, by simp⟩
      have := congrArg (fun x => (ρ c)⁻¹ x) h
      simpa using this
    · rintro ⟨q, hq, rfl⟩
      simp [hq]
  rw [this, Set.ncard_image_of_injective _ (ρ c).injective]

theorem ncard_fixed_in_conjBy {Ω : Type*} (ρ : H →* Equiv.Perm Ω) (F : Set Ω) {c : H}
    (hc : ρ c '' F = F) (w : H) :
    Set.ncard {p : Ω | p ∈ F ∧ ρ (conjBy c w) p = p} = Set.ncard {p : Ω | p ∈ F ∧ ρ w p = p} := by
  have : {p : Ω | p ∈ F ∧ ρ (conjBy c w) p = p} = ρ c '' {p : Ω | p ∈ F ∧ ρ w p = p} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_image, conjBy_def, map_mul, map_inv,
      Equiv.Perm.mul_apply]
    constructor
    · rintro ⟨hp, h⟩
      have hp' : p ∈ ρ c '' F := hc.symm ▸ hp
      obtain ⟨q, hq, rfl⟩ := hp'
      refine ⟨q, ⟨hq, ?_⟩, rfl⟩
      have := congrArg (fun x => (ρ c)⁻¹ x) h
      simpa using this
    · rintro ⟨q, ⟨hq, hw⟩, rfl⟩
      refine ⟨hc ▸ ⟨q, hq, rfl⟩, ?_⟩
      simp [hw]
  rw [this, Set.ncard_image_of_injective _ (ρ c).injective]

@[expose] def invWord (w : List ℤ) : List ℤ := w.reverse.map (fun l => -l)

theorem wordProd_invWord (gs : ℕ → H) :
    ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0) → wordProd gs (invWord w) = (wordProd gs w)⁻¹
  | [], _ => by simp [invWord]
  | l :: w, hw => by
    have hl : l ≠ 0 := hw l (List.mem_cons_self)
    have ih := wordProd_invWord gs w (fun x hx => hw x (List.mem_cons_of_mem _ hx))
    have e : invWord (l :: w) = invWord w ++ [-l] := by simp [invWord]
    rw [e, wordProd_append, ih]
    simp [letterVal_neg gs hl]

theorem prep_pword_prod {n : ℕ} (ρ : H →* Equiv.Perm (Fin n)) {S Sinv : Array (Array ℕ)}
    (gs : ℕ → H) {j : ℕ} (hS : ∀ h < j, PRep n S[h]! (ρ (gs h)))
    (hSinv : ∀ h < j, PRep n Sinv[h]! (ρ (gs h))⁻¹) :
    ∀ w : List ℤ, plettersOK j w = true → PRep n (pword n S Sinv w) (ρ (wordProd gs w))
  | [], _ => by
    simpa [pword] using (prep_pid (n := n))
  | l :: w, hw => by
    simp only [plettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : plettersOK j w = true := by
      simpa [plettersOK, List.all_eq_true] using hw
    have ih := prep_pword_prod ρ gs hS hSinv w hw'
    have hlet : PRep n (pletter S Sinv l) (ρ (letterVal gs l)) := by
      unfold pletter letterVal
      by_cases hpos : 0 < l
      · rw [ite_eq_left hpos, ite_eq_left hpos]
        exact hS _ (by omega)
      · rw [ite_eq_right hpos, ite_eq_right hpos, map_inv]
        exact hSinv _ (by omega)
    rw [pword, wordProd_cons, map_mul]
    exact prep_pcomp hlet ih

end CFSG.EvenSporadicStandard.Solomon78

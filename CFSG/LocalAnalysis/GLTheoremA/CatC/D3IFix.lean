module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FAlg
public import CFSG.HardMathSupport.Lang.D4Three.CharThreeCount

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.HardMathSupport.Lang.D4Three

variable {K : Type} [Field K] [Finite K] {I : Type} [Fintype I]

theorem card_fixed_supp_pow_le (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (hσ : σ ≠ 1) (r : I → I) (f : I → K)
    (S : Finset I) :
    Nat.card {a : I → K // monoTauAdd r f σ a = a ∧ ∀ j, j ∉ S → a j = 0} ^ 3 ≤
      Nat.card K ^ S.card := by
  classical
  let ι : (S → K) →+ (I → K) :=
    { toFun := fun v j => if h : j ∈ S then v ⟨j, h⟩ else 0
      map_zero' := by
        funext j
        by_cases h : j ∈ S <;> simp [h]
      map_add' := by
        intro v w
        funext j
        by_cases h : j ∈ S <;> simp [h] }
  let ρ : (I → K) →+ (S → K) :=
    { toFun := fun a j => a j.1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let τ' : (S → K) →+ (S → K) := ρ.comp ((monoTauAdd r f σ).comp ι)
  have hτ' : ∀ (c : K) (v : S → K), τ' (c • v) = σ c • τ' v := by
    intro c v
    funext j
    have h1 : ι (c • v) = c • ι v := by
      funext i
      by_cases h : i ∈ S <;> simp [ι, h]
    simp only [τ', AddMonoidHom.comp_apply, ρ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, h1,
      monoTauAdd_apply, Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  have h := card_fixed_pow_le σ hσ3 hσ τ' hτ'
  rw [Fintype.card_coe] at h
  refine le_trans (Nat.pow_le_pow_left ?_ 3) h
  refine Nat.card_le_card_of_injective
    (fun a => ⟨ρ a.1, ?_⟩) ?_
  · have hι : ι (ρ a.1) = a.1 := by
      funext i
      by_cases hi : i ∈ S
      · simp [ι, ρ, hi]
      · simp [ι, hi, a.2.2 i hi]
    change τ' (ρ a.1) = ρ a.1
    simp only [τ', AddMonoidHom.comp_apply]
    rw [hι, a.2.1]
  · intro a b hab
    have h1 := congrArg Subtype.val hab
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S
    · exact congrFun h1 ⟨i, hi⟩
    · rw [a.2.2 i hi, b.2.2 i hi]

theorem card_fixed_supp_orbit_le [DecidableEq I] (r : I → I) (f : I → K) (hr3 : ∀ j, r (r (r j)) = j)
    (S R : Finset I)
    (hR : ∀ j, j ∈ S → r j ∈ S → r (r j) ∈ S → j ∈ R ∨ r j ∈ R ∨ r (r j) ∈ R) :
    Nat.card {a : I → K // monoTauAdd r f 1 a = a ∧ ∀ j, j ∉ S → a j = 0} ≤
      Nat.card K ^ (R.filter fun j => j ∈ S ∧ r j ∈ S ∧ r (r j) ∈ S).card := by
  classical
  set T : Finset I := R.filter fun j => j ∈ S ∧ r j ∈ S ∧ r (r j) ∈ S with hT
  have hcard : Nat.card (T → K) = Nat.card K ^ T.card := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := ↥T), Fintype.card_coe]
  rw [← hcard]
  refine Nat.card_le_card_of_injective (fun a => fun j : T => a.1 j.1) ?_
  intro a b hab
  have hT' : ∀ j, j ∈ T → a.1 j = b.1 j := fun j hj => congrFun hab ⟨j, hj⟩
  have hfa : ∀ c : {a : I → K // monoTauAdd r f 1 a = a ∧ ∀ j, j ∉ S → a j = 0}, ∀ j,
      c.1 j = f j * c.1 (r j) := by
    intro c j
    have := congrFun c.2.1 j
    rw [monoTauAdd_apply] at this
    exact this.symm
  have hzero : ∀ c : {a : I → K // monoTauAdd r f 1 a = a ∧ ∀ j, j ∉ S → a j = 0}, ∀ j,
      ¬ (j ∈ S ∧ r j ∈ S ∧ r (r j) ∈ S) → c.1 j = 0 := by
    intro c j hj
    by_cases h1 : j ∈ S
    · by_cases h2 : r j ∈ S
      · have h3 : r (r j) ∉ S := fun h3 => hj ⟨h1, h2, h3⟩
        have e3 : c.1 (r (r j)) = 0 := c.2.2 _ h3
        have e2 : c.1 (r j) = 0 := by rw [hfa c (r j), e3, mul_zero]
        rw [hfa c j, e2, mul_zero]
      · have e2 : c.1 (r j) = 0 := c.2.2 _ h2
        rw [hfa c j, e2, mul_zero]
    · exact c.2.2 _ h1
  apply Subtype.ext
  funext j
  by_cases hj : j ∈ S ∧ r j ∈ S ∧ r (r j) ∈ S
  · obtain ⟨h1, h2, h3⟩ := hj
    have e3 : r (r (r j)) = j := hr3 j
    have e4 : r (r (r (r j))) = r j := hr3 (r j)
    rcases hR j h1 h2 h3 with h | h | h
    · exact hT' j (Finset.mem_filter.2 ⟨h, h1, h2, h3⟩)
    · have e : a.1 (r j) = b.1 (r j) :=
        hT' (r j) (Finset.mem_filter.2 ⟨h, h2, h3, by rw [e3]; exact h1⟩)
      rw [hfa a j, hfa b j, e]
    · have e : a.1 (r (r j)) = b.1 (r (r j)) :=
        hT' (r (r j)) (Finset.mem_filter.2 ⟨h, h3, by rw [e3]; exact h1, by rw [e4]; exact h2⟩)
      rw [hfa a j, hfa b j, hfa a (r j), hfa b (r j), e]
  · rw [hzero a j hj, hzero b j hj]

end CFSG.LocalAnalysis.GLTheoremA

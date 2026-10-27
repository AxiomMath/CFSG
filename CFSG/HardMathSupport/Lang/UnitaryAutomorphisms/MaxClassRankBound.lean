module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.MaxClassCubes

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem comm_word {a b d : G} (hab : Commute a b) (had : Commute a d) (hbd : Commute b d) :
    a * b * b * d * a * b * a = a ^ 3 * b ^ 3 * d := by
  have hc : ({a, b, d} : Set G).Pairwise Commute := by
    intro u hu v hv huv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
      first | exact absurd rfl huv | assumption | exact (by assumption : Commute _ _).symm
  have hcomm := Subgroup.isMulCommutative_closure hc
  let H := Subgroup.closure ({a, b, d} : Set G)
  let a' : H := ⟨a, Subgroup.subset_closure (by simp)⟩
  let b' : H := ⟨b, Subgroup.subset_closure (by simp)⟩
  let d' : H := ⟨d, Subgroup.subset_closure (by simp)⟩
  have key : a' * b' * b' * d' * a' * b' * a' = a' ^ 3 * b' ^ 3 * d' := by
    let _ : CommGroup H := { (inferInstance : Group H) with
      mul_comm := fun x y => IsMulCommutative.is_comm.comm x y }
    simp only [pow_succ, pow_zero, one_mul]
    ac_rfl
  exact congrArg Subtype.val key

@[expose] def fseq (g c : G) : ℕ → G
  | 0 => c
  | j + 1 => cx g (fseq g c j)

theorem fseq_succ (g c : G) (j : ℕ) : fseq g c (j + 1) = cx g (fseq g c j) := rfl


set_option linter.unusedSectionVars false

namespace CubeSetup

variable {x : G} {A : ℕ → Subgroup G} {n : ℕ} (S : CubeSetup x A n) {g c : G}

include S

theorem fseq_mem (hcg : ∀ j, 2 ≤ j → ∀ w ∈ A j, cx g w ∈ A (j + 1)) (hc2 : c ∈ A 2) :
    ∀ j, fseq g c j ∈ A (2 + j) := by
  intro j
  induction j with
  | zero => exact hc2
  | succ j ih =>
    rw [fseq_succ, show 2 + (j + 1) = (2 + j) + 1 by ring]
    exact hcg (2 + j) (by omega) _ ih

theorem fseq_step (hg3 : g ^ 3 = 1) (hcg : ∀ j, 2 ≤ j → ∀ w ∈ A j, cx g w ∈ A (j + 1))
    (hc2 : c ∈ A 2) {i : ℕ} (hi : i + 6 ≤ n) (h : fseq g c (i + 1) ∉ A (4 + i)) :
    fseq g c (i + 3) ∉ A (6 + i) := by
  have hm := S.fseq_mem hcg hc2
  set c1 := fseq g c (i + 1) with hc1
  set c2 := fseq g c (i + 2) with hc2'
  set c3 := fseq g c (i + 3) with hc3
  have e2 : c2 = cx g c1 := rfl
  have e3 : c3 = cx g c2 := rfl
  have e1 : c1 = cx g (fseq g c i) := rfl
  have hc1m : c1 ∈ A (3 + i) := by have := hm (i + 1); rwa [show 2 + (i + 1) = 3 + i by ring] at this
  have hc2m : c2 ∈ A (4 + i) := by have := hm (i + 2); rwa [show 2 + (i + 2) = 4 + i by ring] at this
  have hT := cx_cube_identity hg3 (fseq g c i)
  rw [← e1, ← e2, ← e3] at hT
  have hN := S.normal (6 + i)
  have hcomm : ⁅c1, c2⁆ ∈ A (6 + i) := by
    have := S.comm (3 + i) (4 + i) (by omega) (by omega) _ hc1m _ hc2m
    exact S.anti _ _ (by omega) this
  have hprod : c1 ^ 3 * c2 ^ 3 * c3 ∈ A (6 + i) := by
    rw [cube_reorder hT]
    have := Subgroup.Normal.conj_mem hN _ hcomm (c1 ^ 2)
    simpa [mul_assoc] using this
  have h2cube : c2 ^ 3 ∈ A (6 + i) := by
    have := S.cube_mem' (k := 4 + i) (by omega) hc2m
    rwa [show 4 + i + 2 = 6 + i by ring] at this
  have h1cube : c1 ^ 3 ∉ A (6 + i) := by
    have := S.cube_not_mem (k := 3 + i) (by omega) (by omega) hc1m (by
      rwa [show 3 + i + 1 = 4 + i by ring])
    rwa [show 3 + i + 3 = 6 + i by ring] at this
  intro hc3m
  apply h1cube
  have := (A (6 + i)).mul_mem
    ((A (6 + i)).mul_mem hprod ((A (6 + i)).inv_mem hc3m)) ((A (6 + i)).inv_mem h2cube)
  have e : c1 ^ 3 * c2 ^ 3 * c3 * c3⁻¹ * (c2 ^ 3)⁻¹ = c1 ^ 3 := by group
  rwa [e] at this

theorem fseq_nonzero (hg3 : g ^ 3 = 1) (hcg : ∀ j, 2 ≤ j → ∀ w ∈ A j, cx g w ∈ A (j + 1))
    (hc2 : c ∈ A 2) (h1 : fseq g c 1 ∉ A 4) (h2 : fseq g c 2 ∉ A 5) :
    ∀ j, 1 ≤ j → j + 3 ≤ n → fseq g c j ∉ A (3 + j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hjn
    by_cases hj1 : j = 1
    · subst hj1; exact h1
    by_cases hj2 : j = 2
    · subst hj2; exact h2
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 3 := ⟨j - 3, by omega⟩
    have := S.fseq_step hg3 hcg hc2 (i := i) (by omega)
      (by
        have := ih (i + 1) (by omega) (by omega) (by omega)
        rwa [show 3 + (i + 1) = 4 + i by ring] at this)
    rwa [show 3 + (i + 3) = 6 + i by ring]

theorem false_of_centralizes (hn : 5 ≤ n) {y : G} (hcg : ∀ j, 2 ≤ j → ∀ w ∈ A j, cx y⁻¹ w ∈ A (j + 1))
    (hc2 : c ∈ A 2) (h : fseq y⁻¹ c (n - 3) ∉ A n)
    (hcent : ∀ z ∈ A (n - 2), y * z = z * y) : False := by
  have hm := S.fseq_mem hcg hc2 (n - 4)
  rw [show 2 + (n - 4) = n - 2 by omega] at hm
  have hz := hcent _ hm
  apply h
  rw [show n - 3 = (n - 4) + 1 by omega, fseq_succ]
  have : cx y⁻¹ (fseq y⁻¹ c (n - 4)) = 1 := by
    simp only [cx, inv_inv]
    have e : y⁻¹ * fseq y⁻¹ c (n - 4) * y = fseq y⁻¹ c (n - 4) := by
      calc y⁻¹ * fseq y⁻¹ c (n - 4) * y = y⁻¹ * (fseq y⁻¹ c (n - 4) * y) := by rw [mul_assoc]
        _ = y⁻¹ * (y * fseq y⁻¹ c (n - 4)) := by rw [hz]
        _ = fseq y⁻¹ c (n - 4) := by group
    rw [e]; group
  rw [this]
  exact (A n).one_mem

theorem fseq_base (hn : 5 ≤ n) {y : G} (hy1 : y ∈ A 1) (hy2 : y ∉ A 2) (hy3 : y ^ 3 = 1)
    (hcg : ∀ j, 2 ≤ j → ∀ w ∈ A j, cx y⁻¹ w ∈ A (j + 1)) :
    fseq y⁻¹ (cx x y) 1 ∉ A 4 ∧ fseq y⁻¹ (cx x y) 2 ∉ A 5 := by
  have hc2 : cx x y ∈ A 2 := S.hc 1 le_rfl y hy1
  have hc3 : cx x y ∉ A 3 := S.hinj 1 le_rfl (by omega) y hy1 hy2
  set c := cx x y with hc
  have hm := S.fseq_mem hcg hc2
  set f1 := fseq y⁻¹ c 1 with hf1
  set f2 := fseq y⁻¹ c 2 with hf2
  have e1 : f1 = cx y⁻¹ c := rfl
  have e2 : f2 = cx y⁻¹ f1 := rfl
  have hf1m : f1 ∈ A 3 := hm 1
  have hf2m : f2 ∈ A 4 := hm 2
  have key : ∀ (h a : G), h * a * h⁻¹ = a * cx h a := fun h a => by rw [cx, mul_inv_cancel_left]
  have hφc : y⁻¹ * c * y = c * f1 := by simpa [e1] using key y⁻¹ c
  have hφf : y⁻¹ * f1 * y = f1 * f2 := by simpa [e2] using key y⁻¹ f1
  have hxy : x * y * x⁻¹ = y * c := key x y
  have hy3' : y * y * y = 1 := by simpa [pow_succ, mul_assoc] using hy3
  have hcube : y * c * (y * c) * (y * c) = 1 := by
    rw [← hxy]
    calc x * y * x⁻¹ * (x * y * x⁻¹) * (x * y * x⁻¹) = x * (y * y * y) * x⁻¹ := by group
      _ = 1 := by rw [hy3']; group
  have hR : c * f1 * f1 * f2 * c * f1 * c = 1 := by
    have hφ2 : y⁻¹ * (y⁻¹ * c * y) * y = c * f1 * f1 * f2 := by
      rw [hφc]
      calc y⁻¹ * (c * f1) * y = (y⁻¹ * c * y) * (y⁻¹ * f1 * y) := by group
        _ = c * f1 * f1 * f2 := by rw [hφc, hφf]; group
    calc c * f1 * f1 * f2 * c * f1 * c
        = (y * y * y) * (y⁻¹ * (y⁻¹ * c * y) * y) * (y⁻¹ * c * y) * c := by
          rw [hφ2, hφc, hy3']; group
      _ = y * c * (y * c) * (y * c) := by group
      _ = 1 := hcube
  have := S.normal 5
  let π : G →* G ⧸ A 5 := QuotientGroup.mk' (A 5)
  have hcomm : ∀ {a b : G} {j l : ℕ}, 1 ≤ j → 1 ≤ l → 5 ≤ j + l → a ∈ A j → b ∈ A l →
      Commute (π a) (π b) := by
    intro a b j l hj hl hjl ha hb
    have h1 : ⁅a, b⁆ ∈ A 5 := S.anti _ _ hjl (S.comm j l hj hl a ha b hb)
    have h2 : π ⁅a, b⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  have hcf1 : Commute (π c) (π f1) := hcomm (j := 2) (l := 3) (by omega) (by omega) (by omega) hc2 hf1m
  have hcf2 : Commute (π c) (π f2) := hcomm (j := 2) (l := 4) (by omega) (by omega) (by omega) hc2 hf2m
  have hf12 : Commute (π f1) (π f2) :=
    hcomm (j := 3) (l := 4) (by omega) (by omega) (by omega) hf1m hf2m
  have hπR : π c ^ 3 * π f1 ^ 3 * π f2 = 1 := by
    have := congrArg π hR
    simp only [map_mul, map_one] at this
    rw [← this]
    exact (comm_word hcf1 hcf2 hf12).symm
  have hf1cube : f1 ^ 3 ∈ A 5 := S.cube_mem' (k := 3) (by omega) hf1m
  have hπf1 : π f1 ^ 3 = 1 := by
    rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).2 hf1cube
  have hf2not : f2 ∉ A 5 := by
    intro hf2
    have hπf2 : π f2 = 1 := (QuotientGroup.eq_one_iff _).2 hf2
    rw [hπf1, hπf2, mul_one, mul_one] at hπR
    have hc3cube : c ^ 3 ∈ A 5 := by
      rw [← map_pow] at hπR
      exact (QuotientGroup.eq_one_iff _).1 hπR
    exact S.cube_not_mem (k := 2) le_rfl (by omega) hc2 (by simpa using hc3) hc3cube
  refine ⟨fun h4 => hf2not ?_, hf2not⟩
  rw [e2]
  exact hcg 4 (by omega) _ h4

theorem false_of_order_three (hn : 5 ≤ n) {y : G} (hy1 : y ∈ A 1) (hy2 : y ∉ A 2)
    (hy3 : y ^ 3 = 1) (hcg : ∀ j, 2 ≤ j → ∀ w ∈ A j, cx y⁻¹ w ∈ A (j + 1))
    (hcent : ∀ z ∈ A (n - 2), y * z = z * y) : False := by
  have hg3 : y⁻¹ ^ 3 = 1 := by rw [inv_pow, hy3, inv_one]
  have hc2 : cx x y ∈ A 2 := S.hc 1 le_rfl y hy1
  obtain ⟨h1, h2⟩ := S.fseq_base hn hy1 hy2 hy3 hcg
  have hne := S.fseq_nonzero hg3 hcg hc2 h1 h2 (n - 3) (by omega) (by omega)
  rw [show 3 + (n - 3) = n by omega] at hne
  exact S.false_of_centralizes hn hcg hc2 hne hcent

end CubeSetup

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

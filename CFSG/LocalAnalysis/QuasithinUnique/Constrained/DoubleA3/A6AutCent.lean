module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6AutCentCore

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Equiv

theorem exists_of_mem_tauList {c : List ℕ} (hc : c ∈ tauList) :
    ∃ y : P10, y ∈ A6Models.psl29 ∧ y * A6Models.tFrob = A6Models.tFrob * y ∧ code y = c := by
  unfold tauList Core.cpslList at hc
  rw [List.mem_filter] at hc
  obtain ⟨hc1, hc2⟩ := hc
  obtain ⟨y, hy, rfl⟩ := exists_psl29_of_code hc1
  simp only [beq_iff_eq] at hc2
  refine ⟨y, hy, code_injective ?_, rfl⟩
  rw [code_mul, code_mul, tFrob_code]
  exact hc2

theorem mem_of_order_three {Λ : Subgroup P10}
    (hΛ : Λ ≤ A6Models.psl29 ⊓ Subgroup.centralizer ({A6Models.tFrob} : Set P10))
    (hcard : Nat.card Λ = 12) {y : P10} (hy : y ∈ A6Models.psl29)
    (hyc : y * A6Models.tFrob = A6Models.tFrob * y) (hy3 : y ^ 3 = 1) : y ∈ Λ := by
  set C : Subgroup P10 := A6Models.psl29 ⊓ Subgroup.centralizer ({A6Models.tFrob} : Set P10) with hC
  have hCcard : Nat.card C = 24 := by
    rw [hC, card_psl29_centralizer, tFrob_code]
    exact tauList_length
  have hΛC : Nat.card (Λ.subgroupOf C) = 12 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΛ).toEquiv]
    exact hcard
  have hidx : (Λ.subgroupOf C).index = 2 := by
    have h := (Λ.subgroupOf C).card_mul_index
    rw [hΛC, hCcard] at h
    omega
  have hyC : y ∈ C := ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hyc⟩
  have h1 := Subgroup.mul_self_mem_of_index_two hidx ⟨y, hyC⟩
  have h2 := Subgroup.mul_self_mem_of_index_two hidx (⟨y, hyC⟩ * ⟨y, hyC⟩)
  have h3 : (⟨y, hyC⟩ * ⟨y, hyC⟩ * (⟨y, hyC⟩ * ⟨y, hyC⟩) : ↥C) = ⟨y, hyC⟩ := by
    apply Subtype.ext
    show y * y * (y * y) = y
    have : y * y * (y * y) = y ^ 3 * y := by rw [pow_three']; simp only [mul_assoc]
    rw [this, hy3, one_mul]
  rw [h3] at h2
  exact Subgroup.mem_subgroupOf.mp h2

theorem aut_eq_of_fixes_A4 {K : Type*} [Group K] (e₀ : K ≃* alternatingGroup (Fin 6))
    (α : MulAut K) (hα2 : ∀ k, α (α k) = k) (hα1 : ∃ k, α k ≠ k)
    (L : Subgroup K) (hL : Nat.card L = 12) (hαL : ∀ l ∈ L, α l = l)
    (β : MulAut K) (hβL : ∀ l ∈ L, β l = l) : β = 1 ∨ β = α := by
  obtain ⟨φ, hφ⟩ := exists_swap_model e₀ α hα2 hα1 L hL hαL
  obtain ⟨b, hbA, hb⟩ := exists_aut_model φ β
  let f : K →* P10 := A6Models.psl29.subtype.comp φ.toMonoidHom
  have hfinj : Function.Injective f := Subtype.val_injective.comp φ.injective
  have hfC : L.map f ≤ A6Models.psl29 ⊓ Subgroup.centralizer ({A6Models.tFrob} : Set P10) := by
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨(φ l).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h := hφ l
    rw [hαL l hl] at h
    show ((φ l : ↥A6Models.psl29) : P10) * A6Models.tFrob =
      A6Models.tFrob * ((φ l : ↥A6Models.psl29) : P10)
    calc ((φ l : ↥A6Models.psl29) : P10) * A6Models.tFrob
        = (A6Models.tFrob * ((φ l : ↥A6Models.psl29) : P10) * A6Models.tFrob⁻¹) *
            A6Models.tFrob := by rw [← h]
      _ = A6Models.tFrob * ((φ l : ↥A6Models.psl29) : P10) := by group
  have hLcard : Nat.card (L.map f) = 12 := by
    rw [Subgroup.card_map_of_injective hfinj]
    exact hL
  have hcomm : ∀ y : P10, y ∈ A6Models.psl29 → y * A6Models.tFrob = A6Models.tFrob * y →
      y ^ 3 = 1 → b * y = y * b := by
    intro y hy hyc hy3
    obtain ⟨l, hl, hly⟩ := mem_of_order_three hfC hLcard hy hyc hy3
    have h := hb l
    rw [hβL l hl] at h
    have h' : ((φ l : ↥A6Models.psl29) : P10) = b * ((φ l : ↥A6Models.psl29) : P10) * b⁻¹ := h
    have hly' : ((φ l : ↥A6Models.psl29) : P10) = y := hly
    rw [hly'] at h'
    calc b * y = (b * y * b⁻¹) * b := by group
      _ = y * b := by rw [← h']
  have hcheck := aut_cent_check
  rw [List.all_eq_true] at hcheck
  have h1 := hcheck (code b) (code_mem_autL hbA)
  have h2 : (e3List.all fun e => Core.cmul (code b) e == Core.cmul e (code b)) = true := by
    rw [List.all_eq_true]
    intro e he
    unfold e3List at he
    rw [List.mem_filter] at he
    obtain ⟨he1, he2⟩ := he
    obtain ⟨y, hy, hyc, rfl⟩ := exists_of_mem_tauList he1
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at he2
    obtain ⟨he3, -⟩ := he2
    have hy3 : y ^ 3 = 1 := by
      apply code_injective
      rw [code_pow, he3, code_one]
    rw [← code_mul, ← code_mul, hcomm y hy hyc hy3]
    simp
  simp only [h2, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h1
  have hmain : ∀ k : K, ((φ (β k) : ↥A6Models.psl29) : P10) = b * ((φ k : ↥A6Models.psl29) : P10) * b⁻¹ :=
    hb
  rcases h1 with h1 | h1
  · left
    have hb1 : b = 1 := code_injective (h1.trans code_one.symm)
    ext k
    apply φ.injective
    apply Subtype.ext
    rw [hmain k, hb1]
    simp
  · right
    have hbt : b = A6Models.tFrob := code_injective (h1.trans tFrob_code.symm)
    ext k
    apply φ.injective
    apply Subtype.ext
    rw [hmain k, hφ k, hbt]

end CFSG.QuasithinUnique.DoubleA3

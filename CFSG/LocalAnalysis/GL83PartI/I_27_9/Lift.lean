module

public import CFSG.LocalAnalysis.GL83PartI.I_22_5.IndexGen

public section

namespace GL83.PiGen

open GL83.CompFam
open scoped commutatorElement

section Central

variable {K : Type*} [Group K]

theorem eq_top_of_forall_exists_mul_mem_center (hperf : commutator K = ⊤) {W : Subgroup K}
    (hW : ∀ g : K, ∃ w ∈ W, w⁻¹ * g ∈ Subgroup.center K) : W = ⊤ := by
  have hcomm : ∀ (w : K) (z : K), z ∈ Subgroup.center K → ∀ y : K, ⁅w * z, y⁆ = ⁅w, y⁆ := by
    intro w z hz y
    have h := Subgroup.mem_center_iff.1 hz
    rw [commutatorElement_def, commutatorElement_def]
    calc w * z * y * (w * z)⁻¹ * y⁻¹ = w * (z * y) * (z⁻¹ * w⁻¹) * y⁻¹ := by group
      _ = w * (y * z) * (z⁻¹ * w⁻¹) * y⁻¹ := by rw [h y]
      _ = w * y * w⁻¹ * y⁻¹ := by group
  have hcomm' : ∀ (x : K) (w : K) (z : K), z ∈ Subgroup.center K → ⁅x, w * z⁆ = ⁅x, w⁆ := by
    intro x w z hz
    have h := Subgroup.mem_center_iff.1 hz
    rw [commutatorElement_def, commutatorElement_def]
    calc x * (w * z) * x⁻¹ * (w * z)⁻¹ = x * w * (z * x⁻¹) * (z⁻¹ * w⁻¹) := by group
      _ = x * w * (x⁻¹ * z) * (z⁻¹ * w⁻¹) := by rw [h x⁻¹]
      _ = x * w * x⁻¹ * w⁻¹ := by group
  have hle : commutator K ≤ W := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    obtain ⟨w₁, hw₁, hz₁⟩ := hW g₁
    obtain ⟨w₂, hw₂, hz₂⟩ := hW g₂
    have e₁ : g₁ = w₁ * (w₁⁻¹ * g₁) := by group
    have e₂ : g₂ = w₂ * (w₂⁻¹ * g₂) := by group
    rw [e₁, hcomm w₁ _ hz₁ g₂, e₂, hcomm' w₁ w₂ _ hz₂]
    rw [commutatorElement_def]
    exact W.mul_mem (W.mul_mem (W.mul_mem hw₁ hw₂) (W.inv_mem hw₁)) (W.inv_mem hw₂)
  rw [hperf] at hle
  exact eq_top_iff.2 hle

end Central

section Lift

variable {K : Type*} [Group K] {Z : Subgroup K}

theorem pow_two_pow_bijective (hodd : Odd (Nat.card Z)) (j : ℕ) :
    Function.Bijective (fun z : Z => z ^ (2 ^ j)) :=
  Nat.Coprime.pow_left_bijective (Nat.Coprime.pow_right j (Nat.coprime_two_right.2 hodd))

theorem exists_pow_eq_one_lift (hZ : Z ≤ Subgroup.center K) (hodd : Odd (Nat.card Z)) {x₀ : K}
    {j : ℕ} (h : x₀ ^ (2 ^ j) ∈ Z) : ∃ x : K, x⁻¹ * x₀ ∈ Z ∧ x ^ (2 ^ j) = 1 := by
  obtain ⟨z, hz⟩ := (pow_two_pow_bijective hodd j).2 (⟨x₀ ^ (2 ^ j), h⟩ : Z)⁻¹
  have hz' : (z : K) ^ (2 ^ j) = (x₀ ^ (2 ^ j))⁻¹ := congrArg Subtype.val hz
  have hcomm : Commute x₀ (z : K) := Subgroup.mem_center_iff.1 (hZ z.2) x₀
  refine ⟨x₀ * (z : K), ?_, ?_⟩
  · have : (x₀ * (z : K))⁻¹ * x₀ = (z : K)⁻¹ := by group
    rw [this]
    exact Z.inv_mem z.2
  · rw [hcomm.mul_pow, hz', mul_inv_cancel]

theorem eq_of_pow_eq_one (hZ : Z ≤ Subgroup.center K) (hodd : Odd (Nat.card Z)) {x y : K}
    {j : ℕ} (hxy : x⁻¹ * y ∈ Z) (hx : x ^ (2 ^ j) = 1) (hy : y ^ (2 ^ j) = 1) : x = y := by
  set z : Z := ⟨x⁻¹ * y, hxy⟩ with hzdef
  have hy' : y = x * (z : K) := by simp [hzdef]
  have hcomm : Commute x (z : K) := Subgroup.mem_center_iff.1 (hZ z.2) x
  have hz : (z : K) ^ (2 ^ j) = 1 := by
    have h := hy
    rw [hy', hcomm.mul_pow, hx, one_mul] at h
    exact h
  have hz1 : z ^ (2 ^ j) = 1 := Subtype.ext hz
  have hord : orderOf z ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hz1
  have hord' : orderOf z ∣ Nat.card Z := orderOf_dvd_natCard z
  have hcop : Nat.Coprime (2 ^ j) (Nat.card Z) :=
    Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hodd)
  have h1 : orderOf z = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hord hcop) hord'
  have : z = 1 := orderOf_eq_one_iff.1 h1
  have hz1' : (z : K) = 1 := congrArg Subtype.val this
  rw [hy', hz1', mul_one]

end Lift

section Main

variable {X : Type*} [Group X] {p : ℕ}

theorem le_centGenI_of_closure {K A : Subgroup X} (hperf : commutator K = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center K))) (𝒴 : Set (K ⧸ Subgroup.center K))
    (h𝒴 : Subgroup.closure 𝒴 = ⊤) (h2 : ∀ y ∈ 𝒴, ∃ j : ℕ, y ^ (2 ^ j) = 1)
    (hfix : ∀ y ∈ 𝒴, ∃ E : Subgroup X, E ≤ A ∧ Nat.card A ≤ p * Nat.card E ∧
      ∀ e ∈ E, ∀ x : K, (QuotientGroup.mk x : K ⧸ Subgroup.center K) = y →
        ∃ z : K, z ∈ Subgroup.center K ∧ e * (x : X) * e⁻¹ = (x : X) * (z : X)) :
    K ≤ centGenI p A K := by
  set W' : Subgroup K := (centGenI p A K).subgroupOf K with hW'
  have key : ∀ y ∈ 𝒴, y ∈ W'.map (QuotientGroup.mk' (Subgroup.center K)) := by
    intro y hy
    obtain ⟨j, hj⟩ := h2 y hy
    obtain ⟨E, hEA, hEi, hE⟩ := hfix y hy
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective y
    have hx₀ : x₀ ^ (2 ^ j) ∈ Subgroup.center K := by
      have : (QuotientGroup.mk (x₀ ^ (2 ^ j)) : K ⧸ Subgroup.center K) = 1 := by
        rw [QuotientGroup.mk_pow]
        exact hj
      exact (QuotientGroup.eq_one_iff _).1 this
    obtain ⟨x, hxZ, hx⟩ := exists_pow_eq_one_lift (le_refl (Subgroup.center K)) hodd hx₀
    have hmk : (QuotientGroup.mk x : K ⧸ Subgroup.center K) = QuotientGroup.mk x₀ :=
      QuotientGroup.eq.2 hxZ
    have hxX : (x : X) ^ (2 ^ j) = 1 := by
      rw [← SubgroupClass.coe_pow, hx]
      rfl
    have hcomm : ∀ e ∈ E, e * (x : X) = (x : X) * e := by
      intro e he
      obtain ⟨z, hz, hez⟩ := hE e he x hmk
      have hu : (x * z) ^ (2 ^ j) = 1 := by
        refine Subtype.ext ?_
        rw [SubgroupClass.coe_pow, Subgroup.coe_mul, ← hez, conj_pow, hxX]
        simp
      have hxz : x⁻¹ * (x * z) ∈ Subgroup.center K := by
        rw [inv_mul_cancel_left]
        exact hz
      have hxu : x = x * z := eq_of_pow_eq_one (le_refl (Subgroup.center K)) hodd hxz hx hu
      have hxu' : (x : X) = (x : X) * (z : X) := congrArg Subtype.val hxu
      rw [← hxu'] at hez
      calc e * (x : X) = e * (x : X) * e⁻¹ * e := by group
        _ = (x : X) * e := by rw [hez]
    have hxc : (x : X) ∈ K ⊓ Subgroup.centralizer (E : Set X) :=
      ⟨x.2, Subgroup.mem_centralizer_iff.2 hcomm⟩
    exact ⟨x, Subgroup.mem_subgroupOf.2 (le_centGenI hEA hEi hxc), hmk⟩
  have hP : W'.map (QuotientGroup.mk' (Subgroup.center K)) = ⊤ :=
    eq_top_iff.2 (h𝒴 ▸ (Subgroup.closure_le _).2 key)
  have hW'top : W' = ⊤ := by
    refine eq_top_of_forall_exists_mul_mem_center hperf fun g => ?_
    have hg : (QuotientGroup.mk' (Subgroup.center K)) g ∈
        W'.map (QuotientGroup.mk' (Subgroup.center K)) := by
      rw [hP]
      trivial
    obtain ⟨w, hw, hwg⟩ := Subgroup.mem_map.1 hg
    exact ⟨w, hw, QuotientGroup.eq.1 hwg⟩
  intro k hk
  have : (⟨k, hk⟩ : K) ∈ W' := by rw [hW'top]; trivial
  exact Subgroup.mem_subgroupOf.1 this

end Main

end GL83.PiGen

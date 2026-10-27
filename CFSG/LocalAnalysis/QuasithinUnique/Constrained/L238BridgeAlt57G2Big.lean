module

public import CFSG.Quasithin.Background.JonesParshallG2Perfect
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57ModelBasic

public section

namespace CFSG.QuasithinUnique.Bridge.Alt57Model

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall Matrix
open CFSG.QuasithinUnique.Bridge
open scoped commutatorElement

variable {K : Type} [Field K]

theorem exists_ne_zero_one [Finite K] (h4 : 4 ≤ Nat.card K) : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  have : Fintype K := Fintype.ofFinite K
  by_contra hcon
  push Not at hcon
  have hsurj : Function.Surjective (fun b : Bool => if b then (1 : K) else 0) := by
    intro x
    by_cases hx : x = 0
    · exact ⟨false, by simp [hx]⟩
    · exact ⟨true, by simp [hcon x hx]⟩
  have := Fintype.card_le_of_surjective _ hsurj
  rw [Fintype.card_bool, ← Nat.card_eq_fintype_card] at this
  omega

theorem sq_ne_one [CharP K 2] {c : K} (hc1 : c ≠ 1) : c ^ 2 ≠ 1 := by
  intro h
  apply hc1
  have : (c + 1) ^ 2 = 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination h + (c + 1) * h2
  exact CharTwo.add_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)

theorem card_alt_cases {m : ℕ} (hm : m = 5 ∨ m = 7) :
    Nat.card (alternatingGroup (Fin m)) = 60 ∨ Nat.card (alternatingGroup (Fin m)) = 2520 := by
  rcases hm with rfl | rfl
  · exact Or.inl card_alt_five
  · exact Or.inr card_alt_seven

theorem sl3_image_trivial [CharP K 2] [Finite K] {n : ℕ} (hn : Nat.card K = 2 ^ n) (hn2 : 2 ≤ n)
    {m : ℕ} (hm : m = 5 ∨ m = 7) {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (φ : SL3 K →* alternatingGroup (Fin m)) : ∀ A : SL3 K, φ A = 1 := by
  have hperf : commutator (SL3 K) = ⊤ := sl3_commutator_eq_top hc0 (sq_ne_one hc1)
  have hsimple : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 3) K) :=
    (CFSG.LinearGroups.linear_projective_simple (n := 3) (K := K) (by norm_num)
      (Or.inl le_rfl)).2.1
  set Z := Subgroup.center (SL3 K) with hZ
  set π : SL3 K →* ProjectiveSpecialLinearGroup (Fin 3) K := QuotientGroup.mk' Z with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hN : (φ.ker.map π).Normal := Subgroup.Normal.map inferInstance π hπs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.map π) with h | h
  ·
    exfalso
    have hkZ : ∀ k ∈ φ.ker, k ∈ Z := by
      intro k hk
      have : π k ∈ φ.ker.map π := ⟨k, hk, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff k).1 this
    let Q : Multiplicative (K × K) →* SL3 K :=
      { toFun := fun p => qMat3 (Multiplicative.toAdd p).1 (Multiplicative.toAdd p).2
        map_one' := qMat3_zero
        map_mul' := fun p q => by
          simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
          exact (qMat3_mul _ _ _ _).symm }
    have hinj : Function.Injective (φ.comp Q) := by
      rw [injective_iff_map_eq_one]
      intro p hp
      have hmem : Q p ∈ φ.ker := hp
      obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (hkZ _ hmem)
      have h01 := congrFun (congrFun hr 0) 1
      have h02 := congrFun (congrFun hr 0) 2
      simp [Q, qMat3_coe] at h01 h02
      apply Multiplicative.toAdd.injective
      exact Prod.ext h01.symm h02.symm
    have hdvd := Subgroup.card_dvd_of_injective (φ.comp Q) hinj
    have hc : Nat.card (Multiplicative (K × K)) = Nat.card K ^ 2 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, sq]
    rw [hc, hn, ← pow_mul] at hdvd
    have h16 : 16 ∣ 2 ^ (n * 2) := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ∣ 2 ^ (n * 2) := pow_dvd_pow 2 (by omega)
    have := h16.trans hdvd
    rcases card_alt_cases hm with h60 | h2520
    · rw [h60] at this; omega
    · rw [h2520] at this; omega
  ·
    have hcen : ∀ s : SL3 K, ∃ z ∈ Z, φ s = φ z := by
      intro s
      have : π s ∈ φ.ker.map π := by rw [h]; trivial
      obtain ⟨k, hk, hks⟩ := this
      have hz : k⁻¹ * s ∈ Z := QuotientGroup.eq.1 hks
      refine ⟨k⁻¹ * s, hz, ?_⟩
      rw [map_mul, map_inv, MonoidHom.mem_ker.1 hk, inv_one, one_mul]
    have hker : commutator (SL3 K) ≤ φ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨z₁, hz₁, ha⟩ := hcen a
      obtain ⟨z₂, hz₂, hb⟩ := hcen b
      have hcomm : ⁅z₁, z₂⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.1 hz₁ z₂).symm
      rw [MonoidHom.mem_ker, map_commutatorElement, ha, hb, ← map_commutatorElement, hcomm,
        map_one]
    intro A
    exact MonoidHom.mem_ker.1 (hker (hperf ▸ Subgroup.mem_top A))

section Cayley

variable [CharP K 2]

theorem no_epi_cayley_alt [Finite K] {n : ℕ} (hn : Nat.card K = 2 ^ n) (hn2 : 2 ≤ n)
    {m : ℕ} (hm : m = 5 ∨ m = 7) (ψ : ↥(cayleyGroup K) →* alternatingGroup (Fin m)) :
    ¬ Function.Surjective ψ := by
  intro hψ
  have h4 : 4 ≤ Nat.card K := by
    rw [hn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_one h4
  have hA : ∀ A : SL3 K, ψ (g2A A) = 1 := sl3_image_trivial hn hn2 hm hc0 hc1 (ψ.comp g2A)
  have hconstX : ∀ a : Fin 3 → K, a ≠ 0 → ψ (g2X a) = ψ (g2X (e0 : Fin 3 → K)) := by
    intro a ha
    obtain ⟨B, hB⟩ := MulAction.mem_orbit_iff.mp (mulVec3_e0_mem_orbit a ha)
    have h := congrArg ψ (g2A_mul_g2X B (e0 : Fin 3 → K))
    rw [map_mul, map_mul, hA B, one_mul, mul_one] at h
    have hBa : (B : Matrix (Fin 3) (Fin 3) K) *ᵥ (e0 : Fin 3 → K) = a := hB
    rw [hBa] at h
    exact h.symm
  have hc10 : (1 + c) ≠ 0 := fun h => hc1 (CharTwo.add_eq_zero.1 h).symm
  have hξ : ψ (g2X (e0 : Fin 3 → K)) = 1 := by
    have h := congrArg ψ (g2X_smul_mul (e0 : Fin 3 → K) 1 c)
    have hne1 : c • (e0 : Fin 3 → K) ≠ 0 := fun h0 => hc0 (by simpa [e0] using congrFun h0 0)
    have hne2 : (1 + c) • (e0 : Fin 3 → K) ≠ 0 := fun h0 => hc10 (by simpa [e0] using congrFun h0 0)
    rw [map_mul, one_smul, hconstX _ hne1, hconstX _ hne2] at h
    exact mul_left_cancel (a := ψ (g2X (e0 : Fin 3 → K))) (h.trans (mul_one _).symm)
  have hX : ∀ a : Fin 3 → K, ψ (g2X a) = 1 := by
    intro a
    by_cases ha : a = 0
    · rw [ha, g2X_zero, map_one]
    · rw [hconstX a ha, hξ]
  have hconstY : ∀ b : Fin 3 → K, b ≠ 0 → ψ (g2Y b) = ψ (g2Y (e0 : Fin 3 → K)) := by
    intro b hb
    obtain ⟨B, hB⟩ := MulAction.mem_orbit_iff.mp (mulVec3_e0_mem_orbit b hb)
    set B' : SL3 K := invTransposeFun B
    have hB' : (adjugate (B' : Matrix (Fin 3) (Fin 3) K))ᵀ = (B : Matrix (Fin 3) (Fin 3) K) := by
      change (adjugate ((B⁻¹ : SL3 K) : Matrix (Fin 3) (Fin 3) K)ᵀ)ᵀ = _
      rw [← adjugate_transpose, transpose_transpose]
      change adjugate (adjugate (B : Matrix (Fin 3) (Fin 3) K)) = _
      rw [adjugate_adjugate _ (by simp), B.2]
      simp
    have h := congrArg ψ (g2A_mul_g2Y B' (e0 : Fin 3 → K))
    rw [map_mul, map_mul, hA B', one_mul, mul_one, hB'] at h
    have hBb : (B : Matrix (Fin 3) (Fin 3) K) *ᵥ (e0 : Fin 3 → K) = b := hB
    rw [hBb] at h
    exact h.symm
  have hη : ψ (g2Y (e0 : Fin 3 → K)) = 1 := by
    have h := congrArg ψ (g2Y_smul_mul (e0 : Fin 3 → K) 1 c)
    have hne1 : c • (e0 : Fin 3 → K) ≠ 0 := fun h0 => hc0 (by simpa [e0] using congrFun h0 0)
    have hne2 : (1 + c) • (e0 : Fin 3 → K) ≠ 0 := fun h0 => hc10 (by simpa [e0] using congrFun h0 0)
    rw [map_mul, one_smul, hconstY _ hne1, hconstY _ hne2] at h
    exact mul_left_cancel (a := ψ (g2Y (e0 : Fin 3 → K))) (h.trans (mul_one _).symm)
  have hY : ∀ b : Fin 3 → K, ψ (g2Y b) = 1 := by
    intro b
    by_cases hb : b = 0
    · rw [hb, g2Y_zero, map_one]
    · rw [hconstY b hb, hη]
  have hle : Subgroup.closure (gensG2 K) ≤ ψ.ker.map (cayleyGroup K).subtype := by
    rw [Subgroup.closure_le]
    rintro g (⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨A, rfl⟩)
    · exact ⟨g2X a, MonoidHom.mem_ker.2 (hX a), rfl⟩
    · exact ⟨g2Y b, MonoidHom.mem_ker.2 (hY b), rfl⟩
    · exact ⟨g2A A, MonoidHom.mem_ker.2 (hA A), rfl⟩
  have hall : ∀ g : ↥(cayleyGroup K), ψ g = 1 := by
    intro g
    have hg : (g : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈ Subgroup.closure (gensG2 K) := by
      rw [← cayleyGroup_eq_closure]
      exact g.2
    obtain ⟨k, hk, hkg⟩ := hle hg
    have : k = g := Subtype.ext hkg
    rw [← this]
    exact MonoidHom.mem_ker.1 hk
  have hcard : Nat.card (alternatingGroup (Fin m)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨1⟩⟩
    obtain ⟨g, rfl⟩ := hψ x
    obtain ⟨g', rfl⟩ := hψ y
    rw [hall g, hall g']
  rcases card_alt_cases hm with h60 | h2520 <;> omega

theorem isPerfect_cayleyGroup {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    Group.IsPerfect ↥(cayleyGroup K) := by
  refine ⟨?_⟩
  have h1 : (⊤ : Subgroup ↥(cayleyGroup K)).map (cayleyGroup K).subtype = cayleyGroup K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply Subgroup.map_injective (cayleyGroup K).subtype_injective
  rw [commutator_def, Subgroup.map_commutator, h1, cayley_commutator_eq hc0 hc1]

theorem noAlt57Image_cayley_big [Finite K] {n : ℕ} (hn : Nat.card K = 2 ^ n) (hn2 : 2 ≤ n) :
    NoAlt57Image ↥(cayleyGroup K) := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_one h4
  exact noAlt57Image_of_perfect (isPerfect_cayleyGroup hc0 hc1)
    fun m hm ψ => no_epi_cayley_alt hn hn2 hm ψ

end Cayley

end CFSG.QuasithinUnique.Bridge.Alt57Model

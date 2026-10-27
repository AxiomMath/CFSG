module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Step2

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace Stage

variable {H : Setting G} {S Λ : Subgroup G} (h : Stage H S Λ)

include h in
theorem exists_sylow_N (hS : 2 ∣ S.index) :
    ∃ T : Subgroup G, IsPGroup 2 T ∧ S ≤ T ∧ T ≤ normalizer (S : Set G) ∧
      Nat.card T = 8 * Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ :=
    (h.pgroup.comap_subtype (K := normalizer (S : Set G))).exists_le_sylow
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h.pgroup
  have hNcard : Nat.card (normalizer (S : Set G) : Subgroup G) = 21 * 2 ^ (k + 3) := by
    have h1 := h.card_N hS
    have h2 := h.card_S
    have h3 : 2 ^ (k + 3) = 8 * 2 ^ k := by ring
    omega
  have hQcard : Nat.card Q = 2 ^ (k + 3) := by
    rw [Sylow.card_eq_multiplicity, hNcard, Nat.factorization_mul (by norm_num) (by positivity),
      Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 21)]
  refine ⟨(Q : Subgroup (normalizer (S : Set G))).map (normalizer (S : Set G)).subtype,
    Q.isPGroup'.map _, fun s hs => ⟨⟨s, le_normalizer hs⟩, hQ hs, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective (normalizer (S : Set G)).subtype_injective, hQcard, hk]
    ring

include h in
theorem exists_sq_of_mem_E (hΛ : 8 < Nat.card Λ) {e : G} (he : e ∈ H.E) :
    ∃ l ∈ Λ, e = l * l := by
  obtain ⟨σ, hσ, h7⟩ := H.exists_sigma
  have hσΛ : σ ∈ normalizer (Λ : Set G) := h.B_Λ (H.NL_le_B hσ)
  obtain ⟨l₀, hl₀, hl₀sq⟩ : ∃ l₀ ∈ Λ, l₀ * l₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : Λ ≤ H.E := fun l hl => h.mem_E_of_sq hl (hcon l hl)
    have := Subgroup.card_le_of_le hle
    rw [H.card_E] at this
    omega
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 h.pgroup ⟨l₀ * l₀, h.le (mul_mem hl₀ hl₀)⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact hl₀sq (orderOf_eq_one_iff.1 hk)
  have hbΛ : (l₀ * l₀) ^ 2 ^ (k - 1) ∈ Λ := Subgroup.pow_mem Λ (mul_mem hl₀ hl₀) _
  have hbsq : (l₀ * l₀) ^ 2 ^ (k - 1) * (l₀ * l₀) ^ 2 ^ (k - 1) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk1),
      ← hk]
    exact pow_orderOf_eq_one _
  have hb1 : (l₀ * l₀) ^ 2 ^ (k - 1) ≠ 1 := by
    refine pow_ne_one_of_lt_orderOf (by positivity) ?_
    rw [hk]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hbE : (l₀ * l₀) ^ 2 ^ (k - 1) ∈ H.E := h.mem_E_of_sq hbΛ hbsq
  have hbc : (l₀ * l₀) ^ 2 ^ (k - 1) = l₀ ^ 2 ^ (k - 1) * l₀ ^ 2 ^ (k - 1) :=
    (Commute.refl l₀).mul_pow _
  by_cases he1 : e = 1
  · exact ⟨1, one_mem Λ, by rw [he1, mul_one]⟩
  obtain ⟨i, hi⟩ := (H.sigma_orbit hσ h7).2 _ hbE e he hb1 he1
  refine ⟨σ ^ i * l₀ ^ 2 ^ (k - 1) * (σ ^ i)⁻¹, ?_, ?_⟩
  · have hσi : σ ^ i ∈ normalizer (Λ : Set G) := pow_mem hσΛ i
    exact (mem_normalizer_iff.1 hσi _).1 (Subgroup.pow_mem Λ hl₀ _)
  · rw [← hi, hbc]
    group

include h in
theorem caseII_conj_le (_hS : 2 ∣ S.index) (hcase : Nat.card (H.RC S) = Nat.card S)
    (hΛ : 8 < Nat.card Λ) {T : Subgroup G} (_hT : IsPGroup 2 T) (_hST : S ≤ T)
    (hTN : T ≤ normalizer (S : Set G)) (_hTcard : Nat.card T = 8 * Nat.card S) :
    ∀ x ∈ T, IsConj H.z x → x ∈ S := by
  intro x hxT hxc
  have hRC : S = H.RC S := Subgroup.eq_of_le_of_card_ge h.S_le_RC hcase.le
  by_contra hxS
  have hxN : x ∈ normalizer (S : Set G) := hTN hxT
  have hx2 : x * x = 1 := H.sq_of_isConj hxc
  have hinv : ∀ l ∈ Λ, (l * l) * ((x * l * x⁻¹) * (x * l * x⁻¹)) = 1 := by
    intro l hl
    have hl' : x * l * x⁻¹ ∈ Λ := h.N_normalizes_Λ hxN hl
    have hcΛ : l * (x * l * x⁻¹) ∈ Λ := mul_mem hl hl'
    have hxcx : x * (l * (x * l * x⁻¹)) * x⁻¹ = l * (x * l * x⁻¹) :=
      calc x * (l * (x * l * x⁻¹)) * x⁻¹
          = (x * l * x⁻¹) * ((x * x) * l * (x * x)⁻¹) := by group
        _ = (x * l * x⁻¹) * l := by rw [hx2]; group
        _ = l * (x * l * x⁻¹) := h.comm hl' hl
    have hP : IsPGroup 2 (zpowers (l * (x * l * x⁻¹))) :=
      h.pgroup.to_le (zpowers_le.2 (h.le hcΛ))
    have hPC : zpowers (l * (x * l * x⁻¹)) ≤ centralizer ({x} : Set G) := by
      refine zpowers_le.2 (mem_centralizer_singleton_iff.2 ?_)
      calc l * (x * l * x⁻¹) * x = (x * (l * (x * l * x⁻¹)) * x⁻¹) * x := by rw [hxcx]
        _ = x * (l * (x * l * x⁻¹)) := by group
    have hcc := (H.star_conj hxc hP hPC).2 _ (mem_zpowers _)
    calc (l * l) * ((x * l * x⁻¹) * (x * l * x⁻¹))
        = l * (l * (x * l * x⁻¹)) * (x * l * x⁻¹) := by group
      _ = l * ((x * l * x⁻¹) * l) * (x * l * x⁻¹) := by rw [h.comm hl hl']
      _ = (l * (x * l * x⁻¹)) * (l * (x * l * x⁻¹)) := by group
      _ = 1 := hcc
  refine hxS (hRC ▸ Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun e he => ?_, hxN⟩)
  obtain ⟨l, hl, rfl⟩ := h.exists_sq_of_mem_E hΛ he
  have h1 := hinv l hl
  have h2 : x * (l * l) * x⁻¹ = (l * l)⁻¹ := by
    have := eq_inv_of_mul_eq_one_right h1
    rw [← this]
    group
  have h3 : x * (l * l) * x⁻¹ = l * l := by rw [h2, H.E_inv he]
  calc l * l * x = (x * (l * l) * x⁻¹) * x := by rw [h3]
    _ = x * (l * l) := by group

include h in
theorem caseII_not_two_dvd_index_of_conj_le (_hS : 2 ∣ S.index)
    {T : Subgroup G} (hT : IsPGroup 2 T) (hST : S ≤ T) (hTN : T ≤ normalizer (S : Set G))
    (hTcard : Nat.card T = 8 * Nat.card S)
    (hconj : ∀ x ∈ T, IsConj H.z x → x ∈ S) : ¬ 2 ∣ T.index := by
  have hVT : H.V ≤ T := h.V_le.trans hST
  have hmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({H.z} : Set G) →
      centralizer ({H.z} : Set G) ⊓ T ≤ P → P ≤ T := by
    intro P hP hPC hTP
    have hVP : H.V ≤ P := (le_inf H.V_le_centralizer hVT).trans hTP
    have := Subgroup.eq_of_le_of_card_ge hVP (by rw [H.card_V]; exact (H.star hP hPC).1)
    rw [← this]
    exact hVT
  have hC16 : Nat.card (centralizer ({H.z} : Set G) ⊓ T : Subgroup G) = 16 := by
    have hCV : H.V ≤ centralizer ({H.z} : Set G) ⊓ T := le_inf H.V_le_centralizer hVT
    refine le_antisymm ?_ (H.card_V ▸ Subgroup.card_le_of_le hCV)
    exact (H.star hT.to_inf_right inf_le_left).1
  have hTcard' : Nat.card T = 16 * Nat.card Λ := by
    have := h.card_S
    omega
  have hcls := card_eq_card_conjClass_mul T H.z
  rw [hC16, hTcard'] at hcls
  set A : Set G := {w | ∃ r ∈ T, w = r * H.z * r⁻¹} with hA
  set B : Set G := (fun l : G => l * H.z) '' (Λ : Set G) with hB
  have hAcard : A.ncard = Nat.card Λ := by
    have h1 : Nat.card {x : G // ∃ m ∈ T, x = m * H.z * m⁻¹} = A.ncard := by
      rw [← Nat.card_coe_set_eq]; rfl
    omega
  have hBcard : B.ncard = Nat.card Λ := by
    rw [hB, Set.ncard_image_of_injective _ (mul_left_injective H.z)]
    rw [← Nat.card_coe_set_eq]; rfl
  have hAB : A ⊆ B := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨hrS, hrΛ⟩ := h.N_conj_mem (hTN hr) h.z_mem h.z_not_mem
    refine ⟨r * H.z * r⁻¹ * H.z, (h.cover _ hrS).resolve_left hrΛ, ?_⟩
    show r * H.z * r⁻¹ * H.z * H.z = r * H.z * r⁻¹
    rw [mul_assoc _ H.z, H.z_mul_self, mul_one]
  have hAeq : A = B := Set.eq_of_subset_of_ncard_le hAB (by omega) (Set.toFinite B)
  refine not_two_dvd_index_of_invariant hT hmax fun n hn => ?_
  have hnz : n * H.z * n⁻¹ ∈ T := (mem_normalizer_iff.1 hn H.z).1 (hST h.z_mem)
  have hnc : IsConj H.z (n * H.z * n⁻¹) := _root_.isConj_iff.2 ⟨n, rfl⟩
  have hnS : n * H.z * n⁻¹ ∈ S := hconj _ hnz hnc
  have hnΛ : n * H.z * n⁻¹ ∉ Λ := fun hh => h.not_isConj_of_mem hh hnc
  have hmem : n * H.z * n⁻¹ ∈ B := by
    refine ⟨n * H.z * n⁻¹ * H.z, (h.cover _ hnS).resolve_left hnΛ, ?_⟩
    show n * H.z * n⁻¹ * H.z * H.z = n * H.z * n⁻¹
    rw [mul_assoc _ H.z, H.z_mul_self, mul_one]
  rw [← hAeq] at hmem
  obtain ⟨r, hr, hrn⟩ := hmem
  exact ⟨r, hr, hrn⟩

end Stage

end CFSG.EvenSporadicStandard.J1Std

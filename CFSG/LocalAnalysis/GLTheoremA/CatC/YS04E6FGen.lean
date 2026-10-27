module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.YS04E6F

open CFSG.Open CFSG.SectionRank CFSG.LocalAnalysis.ComponentInitial

theorem meets_inner_of_data {A Q : Type*} [Group A] [Finite A] [Group Q]
    (I : Subgroup A) [I.Normal] (Θ : A →* Q)
    (hQ : ∀ F : Subgroup Q, IsElemAbelian 3 F → Nat.card F ≤ 3)
    (hY : ∀ E : Subgroup A, E ≤ Θ.ker → IsElemAbelian 3 E → E ⊓ I = ⊥ → Nat.card E ≤ 3)
    (hdesc : ∀ α : A, α ^ 3 = 1 → Θ α ≠ 1 → ∃ ψ : A, ∀ δ ∈ Θ.ker,
      δ * (ψ * α * ψ⁻¹) = (ψ * α * ψ⁻¹) * δ → δ ∈ I)
    (D : Subgroup A) (hD : IsElemAbelian 3 D) (hc : Nat.card D = 9) :
    ∃ x ∈ D ⊓ I, x ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hDI : D ⊓ I = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (hcon x hx)
  by_cases hker : D ≤ Θ.ker
  · have := hY D hker hD hDI
    omega
  · obtain ⟨α, hαD, hαk⟩ := SetLike.not_le_iff_exists.1 hker
    have hα3 : α ^ 3 = 1 := hD.2 α hαD
    have hΘα : Θ α ≠ 1 := fun h => hαk (MonoidHom.mem_ker.2 h)
    obtain ⟨ψ, hψ⟩ := hdesc α hα3 hΘα
    set cψ : A →* A := (MulAut.conj ψ).toMonoidHom with hcψ
    have hinj : Function.Injective cψ := (MulAut.conj ψ).injective
    set D' : Subgroup A := D.map cψ with hD'
    have hD'ea : IsElemAbelian 3 D' := isElemAbelian_map hD cψ
    have hD'c : Nat.card D' = 9 := by rw [hD', Subgroup.card_map_of_injective hinj, hc]
    have hTD' : ψ * α * ψ⁻¹ ∈ D' := ⟨α, hαD, rfl⟩
    have hD'I : D' ⊓ I = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨⟨y, hyD, rfl⟩, hxI⟩
      have hyI : y ∈ I := by
        have := (inferInstance : I.Normal).conj_mem _ hxI ψ⁻¹
        simpa [cψ, MulAut.conj_apply, mul_assoc] using this
      have hy : y ∈ D ⊓ I := ⟨hyD, hyI⟩
      rw [hDI] at hy
      have hy1 : y = 1 := hy
      subst hy1
      simp
    set φ : D' →* Q := Θ.comp D'.subtype with hφ
    have hcard := Subgroup.card_ker_mul_card_range φ
    have hrange : φ.range = D'.map Θ := by
      rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
    have hker' : Nat.card φ.ker = Nat.card (D' ⊓ Θ.ker : Subgroup A) := by
      have : φ.ker = (D' ⊓ Θ.ker).subgroupOf D' := by
        ext x; simp [hφ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      rw [this]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : D' ⊓ Θ.ker ≤ D')).toEquiv
    rw [hrange, hker', hD'c] at hcard
    have h3 : Nat.card (D'.map Θ) ≤ 3 := hQ _ (isElemAbelian_map hD'ea Θ)
    have hgt : 1 < Nat.card (D' ⊓ Θ.ker : Subgroup A) := by
      by_contra hle
      push Not at hle
      have : Nat.card (D' ⊓ Θ.ker : Subgroup A) * Nat.card (D'.map Θ) ≤ 1 * 3 :=
        Nat.mul_le_mul hle h3
      omega
    have hne : (D' ⊓ Θ.ker : Subgroup A) ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot _).1 hgt
    obtain ⟨⟨δ, hδ⟩, hδ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have hδD' : δ ∈ D' := hδ.1
    have hδk : δ ∈ Θ.ker := hδ.2
    have hcomm : δ * (ψ * α * ψ⁻¹) = (ψ * α * ψ⁻¹) * δ := by
      haveI := hD'ea.1
      exact congrArg Subtype.val (mul_comm' (⟨δ, hδD'⟩ : D') ⟨_, hTD'⟩)
    have hδI : δ ∈ I := hψ δ hδk hcomm
    have : δ ∈ D' ⊓ I := ⟨hδD', hδI⟩
    rw [hD'I] at this
    exact hδ1 (Subtype.ext this)

theorem exists_cube_of_pow_eq_one {G : Type*} [Group G] [Finite G] [IsCyclic G] {x : G}
    (h3 : 3 ∣ Nat.card G) (hx : x ^ (Nat.card G / 3) = 1) : ∃ y : G, y ^ 3 = x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
  have hord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨N3, hN3⟩ := h3
  have hN3pos : 0 < N3 := by
    rcases Nat.eq_zero_or_pos N3 with h | h
    · have := Nat.card_pos (α := G)
      omega
    · exact h
  have hdiv : Nat.card G / 3 = N3 := by omega
  rw [hdiv, ← zpow_natCast, ← zpow_mul] at hx
  have hd := (orderOf_dvd_iff_zpow_eq_one.2 hx)
  rw [hord, hN3] at hd
  have h3i : (3 : ℤ) ∣ i := by
    have : (3 * N3 : ℤ) ∣ i * N3 := by exact_mod_cast hd
    obtain ⟨c, hc⟩ := this
    refine ⟨c, ?_⟩
    have hN : (N3 : ℤ) ≠ 0 := by exact_mod_cast hN3pos.ne'
    apply mul_right_cancel₀ hN
    linarith
  obtain ⟨j, hj⟩ := h3i
  refine ⟨g ^ j, ?_⟩
  rw [hj, ← zpow_natCast, ← zpow_mul]
  norm_num [mul_comm]

theorem exists_cube_of_fixed {K : Type} [Field K] [Finite K] (η : K ≃+* K) (hη : orderOf η = 3)
    (h3 : 3 ∣ Nat.card K - 1) (c : Kˣ) (hc : η (c : K) = c) : ∃ s : Kˣ, s ^ 3 = c := by
  classical
  obtain ⟨ℓ, f, hℓ, hf, hKℓ⟩ : ∃ ℓ f : ℕ, ℓ.Prime ∧ 1 ≤ f ∧ Nat.card K = ℓ ^ f := by
    haveI := Fintype.ofFinite K
    obtain ⟨n, hp', hn⟩ := FiniteField.card K (ringChar K)
    exact ⟨ringChar K, n, hp', n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩
  obtain ⟨-, -, -, -, -, hA⟩ := finite_field_automorphism_fixed_field_cardinality hℓ hf hKℓ
  obtain ⟨hdvd, S, hS, hScard⟩ := hA (Subgroup.zpowers η)
  rw [Nat.card_zpowers, hη] at hdvd hScard
  obtain ⟨e, he⟩ := hdvd
  set m : ℕ := ℓ ^ e with hm
  have hKm : Nat.card K = m ^ 3 := by
    rw [hKℓ, he, hm, ← pow_mul, mul_comm]
  have hScard' : Nat.card S = m := by
    rw [hScard, he, hm]
    congr 1
    omega
  have hcS : (c : K) ∈ S := by
    have hle : Subgroup.zpowers η ≤ MulAction.stabilizer (K ≃+* K) (c : K) :=
      (Subgroup.zpowers_le).2 (by rw [MulAction.mem_stabilizer_iff]; exact hc)
    have : (c : K) ∈ (S : Set K) := by
      rw [hS]
      intro τ hτ
      have := hle hτ
      rw [MulAction.mem_stabilizer_iff] at this
      exact this
    exact this
  have hm3 : m % 3 = 1 := by
    have hpos : 0 < Nat.card K := Nat.card_pos
    have h1 : Nat.card K % 3 = 1 := by omega
    rw [hKm, Nat.pow_mod] at h1
    have : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases this with h | h | h <;> simp [h] at h1 <;> omega
  obtain ⟨t, ht⟩ : ∃ t, m = 3 * t + 1 := ⟨m / 3, by omega⟩
  have hcm : (c : K) ^ (m - 1) = 1 := by
    haveI : Fintype S := Fintype.ofFinite S
    have hx0 : (⟨(c : K), hcS⟩ : S) ≠ 0 := fun h => c.ne_zero (congrArg Subtype.val h)
    have h1 := FiniteField.pow_card_sub_one_eq_one (⟨(c : K), hcS⟩ : S) hx0
    rw [← Nat.card_eq_fintype_card, hScard'] at h1
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hcmu : c ^ (m - 1) = 1 := Units.ext (by simpa using hcm)
  have hcard : Nat.card Kˣ = m ^ 3 - 1 := by rw [Nat.card_units, hKm]
  have hdiv3 : Nat.card Kˣ / 3 = (m - 1) * (3 * t ^ 2 + 3 * t + 1) := by
    rw [hcard, ht]
    have : (3 * t + 1) ^ 3 - 1 = 3 * ((3 * t + 1 - 1) * (3 * t ^ 2 + 3 * t + 1)) := by
      simp only [Nat.add_sub_cancel]
      ring_nf
      omega
    rw [this]
    omega
  have h3U : 3 ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact h3
  obtain ⟨y, hy⟩ := exists_cube_of_pow_eq_one h3U (by
    rw [hdiv3, pow_mul, hcmu, one_pow])
  exact ⟨y, hy⟩

end CFSG.LocalAnalysis.GLTheoremA.YS04E6F

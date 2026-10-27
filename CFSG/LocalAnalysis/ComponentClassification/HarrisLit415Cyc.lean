module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415W0Sylow
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415AutInputs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools

namespace L415

namespace IsProd

variable {G : Type} [Group G] [Finite G] {E K₁ K₂ : Subgroup G} {s : G}

theorem exists_pow_of_mem_zpowers {y x : G} (hx : x ∈ zpowers y) :
    ∃ n < orderOf y, y ^ n = x := by
  classical
  have := (mem_zpowers_iff_mem_range_orderOf (x := y) (y := x)).mp hx
  simpa using this

omit [Finite G] in
theorem pow_three_sq {y : G} (hy4 : orderOf y = 4) : (y ^ 3) ^ 2 = y ^ 2 := by
  rw [← pow_mul, show 3 * 2 = 2 + 4 by norm_num, pow_add, ← hy4, pow_orderOf_eq_one, mul_one]

theorem sq_eq_of_mem_zpowers {y x : G} (hy4 : orderOf y = 4) (hx : x ∈ zpowers y)
    (hx4 : orderOf x = 4) : x ^ 2 = y ^ 2 := by
  obtain ⟨n, hn, rfl⟩ := exists_pow_of_mem_zpowers hx
  rw [hy4] at hn
  interval_cases n
  · rw [pow_zero, orderOf_one] at hx4
    norm_num at hx4
  · rw [pow_one]
  · rw [orderOf_pow' y (by norm_num), hy4] at hx4
    norm_num at hx4
  · exact pow_three_sq hy4

variable (h : IsProd E K₁ K₂ s) (hE : E.Normal)
include h hE

theorem map_K₁_of_cyclic {P : Subgroup G} (h8 : 4 < Nat.card ↥(P ⊓ K₁)) {y : G}
    (hy4 : orderOf y = 4) (hyn : ∀ g ∈ P, g * y * g⁻¹ ∈ zpowers y) :
    K₁.map (MulAut.conj y).toMonoidHom = K₁ := by
  rcases h.conj_cases hE y with h1 | h1
  · exact h1
  · exfalso
    have hyK : ∀ k ∈ K₁, y * k * y⁻¹ ∈ K₂ := fun k hk => by
      rw [← h1]
      exact ⟨k, hk, rfl⟩
    have hmem : ∀ d ∈ P ⊓ K₁, d * (y * d⁻¹ * y⁻¹) ∈ zpowers y := by
      intro d hd
      have h2 := hyn d (mem_inf.mp hd).1
      have h3 : d * (y * d⁻¹ * y⁻¹) = (d * y * d⁻¹) * y⁻¹ := by group
      rw [h3]
      exact mul_mem h2 (inv_mem (mem_zpowers y))
    let f : ↥(P ⊓ K₁) → ↥(zpowers y) := fun d => ⟨_, hmem d d.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h2 : (a : G) * (y * (a : G)⁻¹ * y⁻¹) = b * (y * (b : G)⁻¹ * y⁻¹) :=
        congrArg Subtype.val hab
      have ha := (mem_inf.mp a.2).2
      have hb := (mem_inf.mp b.2).2
      exact Subtype.ext (h.eq_of_mul_eq ha hb (hyK _ (inv_mem ha)) (hyK _ (inv_mem hb)) h2).1
    have h2 := Nat.card_le_card_of_injective f hf
    rw [Nat.card_zpowers, hy4] at h2
    omega

theorem comm_of_cyclic {P : Subgroup G} (h8 : 4 < Nat.card ↥(P ⊓ K₁)) (hsP : s ∈ P)
    (hs2 : s * s = 1) {y : G} (hy4 : orderOf y = 4)
    (hyn : ∀ g ∈ P, g * y * g⁻¹ ∈ zpowers y) :
    (∀ d ∈ P ⊓ K₁, d * y = y * d) ∧ ∀ d ∈ P ⊓ K₂, d * y = y * d := by
  have hK₁ := h.map_K₁_of_cyclic hE h8 hy4 hyn
  have hK₂ := h.map_K₂_of_map_K₁ hE hK₁
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hy2c : ∀ g ∈ P, g * y ^ 2 * g⁻¹ = y ^ 2 := by
    intro g hg
    have h1 : (g * y * g⁻¹) ^ 2 = y ^ 2 := sq_eq_of_mem_zpowers hy4 (hyn g hg) (by
      have := MulEquiv.orderOf_eq (MulAut.conj g) y
      simp only [MulAut.conj_apply] at this
      rw [this, hy4])
    calc g * y ^ 2 * g⁻¹ = (g * y * g⁻¹) ^ 2 := by rw [sq, sq]; group
      _ = y ^ 2 := h1
  have hy21 : y ^ 2 ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hy4] at this
    norm_num at this
  have hcap : ∀ (K : Subgroup G), (K = K₁ ∨ K = K₂) → ∀ c ∈ K, c ∈ zpowers y → c = 1 := by
    intro K hK c hcK hcy
    by_contra hc1
    have hy2K : y ^ 2 ∈ K := by
      obtain ⟨n, hn, rfl⟩ := exists_pow_of_mem_zpowers hcy
      rw [hy4] at hn
      interval_cases n
      · exact absurd (pow_zero y) hc1
      · rw [pow_one] at hcK
        exact pow_mem hcK 2
      · exact hcK
      · rw [← pow_three_sq hy4]
        exact pow_mem hcK 2
    have h2 : s * y ^ 2 * s⁻¹ = y ^ 2 := hy2c s hsP
    rcases hK with rfl | rfl
    · have h3 : s⁻¹ * y ^ 2 * s ∈ K₂ := h.conj_mem_K₂ hy2K
      have h4 : s⁻¹ * y ^ 2 * s = y ^ 2 := by rw [hsi]; rw [hsi] at h2; exact h2
      have h5 : y ^ 2 ∈ K ⊓ K₂ := mem_inf.mpr ⟨hy2K, h4 ▸ h3⟩
      rw [h.inf_eq, mem_bot] at h5
      exact hy21 h5
    · have h3 : s * y ^ 2 * s⁻¹ ∈ K₁ := h.mem_K₂_iff.mp hy2K
      have h5 : y ^ 2 ∈ K₁ ⊓ K := mem_inf.mpr ⟨h2 ▸ h3, hy2K⟩
      rw [h.inf_eq, mem_bot] at h5
      exact hy21 h5
  have hcomm : ∀ (K : Subgroup G), (K = K₁ ∨ K = K₂) →
      K.map (MulAut.conj y).toMonoidHom = K → ∀ d ∈ P ⊓ K, d * y = y * d := by
    intro K hK hKy d hd
    have hyd : y * d⁻¹ * y⁻¹ ∈ K := by
      rw [← hKy]
      exact ⟨d⁻¹, inv_mem (mem_inf.mp hd).2, rfl⟩
    have h1 : d * (y * d⁻¹ * y⁻¹) ∈ K := mul_mem (mem_inf.mp hd).2 hyd
    have h2 : d * (y * d⁻¹ * y⁻¹) ∈ zpowers y := by
      rw [show d * (y * d⁻¹ * y⁻¹) = (d * y * d⁻¹) * y⁻¹ by group]
      exact mul_mem (hyn d (mem_inf.mp hd).1) (inv_mem (mem_zpowers y))
    have h3 := hcap K hK _ h1 h2
    calc d * y = d * (y * d⁻¹ * y⁻¹) * (y * d) := by group
      _ = y * d := by rw [h3, one_mul]
  exact ⟨hcomm K₁ (Or.inl rfl) hK₁, hcomm K₂ (Or.inr rfl) hK₂⟩

omit h hE in
theorem sq_comm_of_fix (hA : AutPSL2RCentralizerInput) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Subgroup G} (hlie : Blueprint.LieModel ↥K .PSL 2 p n) {P : Subgroup G}
    (hPK : IsSylowOf 2 (P ⊓ K) K) (h8 : 4 < Nat.card ↥(P ⊓ K)) {y : G}
    (hy4 : orderOf y = 4) (hyN : y ∈ normalizer (K : Set G))
    (hfix : ∀ d ∈ P ⊓ K, d * y = y * d) : ∀ k ∈ K, y ^ 2 * k = k * y ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a := normalizerConj K ⟨y, hyN⟩ with ha
  have hao : ∃ k : ℕ, orderOf a = 2 ^ k := by
    have h1 : orderOf a ∣ orderOf (⟨y, hyN⟩ : ↥(normalizer (K : Set G))) := orderOf_map_dvd _ _
    rw [Subgroup.orderOf_mk, hy4, show (4 : ℕ) = 2 ^ 2 by norm_num] at h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact ⟨k, hk⟩
  obtain ⟨Q, hQ⟩ := hPK
  have hQR : (Q : Subgroup ↥K) = (P ⊓ K).subgroupOf K := by
    rw [← hQ]
    exact (comap_map_eq_self_of_injective K.subtype_injective _).symm
  have hcardR : 8 ≤ Nat.card ↥((P ⊓ K).subgroupOf K) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : P ⊓ K ≤ K)).toEquiv]
    have hp' : IsPGroup 2 ↥(P ⊓ K) := hQ ▸ (Q.isPGroup'.map K.subtype)
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hp'
    rw [hm] at h8 ⊢
    have hm3 : 3 ≤ m := by
      by_contra hlt
      push Not at hlt
      interval_cases m <;> norm_num at h8
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
  have hfixa : ∀ x ∈ (P ⊓ K).subgroupOf K, a x = x := by
    intro x hx
    apply Subtype.ext
    rw [ha, normalizerConj_apply]
    have h1 := hfix x hx
    calc y * (x : G) * y⁻¹ = (y * x) * y⁻¹ := by group
      _ = (x * y) * y⁻¹ := by rw [h1]
      _ = x := by group
  have h1 := hA ↥K p n hp hp2 hlie _ ⟨Q, hQR⟩ hcardR a hao hfixa
  intro k hk
  have h2 := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : G)) h1
  simp only [MulAut.mul_apply, MulAut.one_apply] at h2
  rw [ha, normalizerConj_apply, normalizerConj_apply] at h2
  calc y ^ 2 * k = (y * (y * k * y⁻¹) * y⁻¹) * y ^ 2 := by rw [sq]; group
    _ = k * y ^ 2 := by rw [h2]

theorem sq_comm_of_cyclic (hA : AutPSL2RCentralizerInput) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlie : Blueprint.LieModel ↥K₁ .PSL 2 p n) {P : Subgroup G} (hP : IsSylowOf 2 P ⊤)
    (h8 : 4 < Nat.card ↥(P ⊓ K₁)) (hsP : s ∈ P) (hs2 : s * s = 1) {y : G}
    (hy4 : orderOf y = 4) (hyn : ∀ g ∈ P, g * y * g⁻¹ ∈ zpowers y) :
    ∀ e ∈ E, y ^ 2 * e = e * y ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK₁ := h.map_K₁_of_cyclic hE h8 hy4 hyn
  have hK₂ := h.map_K₂_of_map_K₁ hE hK₁
  obtain ⟨hc₁, hc₂⟩ := h.comm_of_cyclic hE h8 hsP hs2 hy4 hyn
  have hS₁ := h.isSylowOf_inf_K₁ hE hP
  have hS₂ := h.isSylowOf_inf_K₂ hE hP
  have hcard₂ : Nat.card ↥(P ⊓ K₂) = Nat.card ↥(P ⊓ K₁) := by
    rw [hS₁.card_eq, hS₂.card_eq, ← Nat.card_congr h.equivK₂.toEquiv]
  have h1 := sq_comm_of_fix hA hp hp2 hlie hS₁ h8 hy4
    ((mem_normalizer_iff_map _ _).mpr hK₁) hc₁
  have h2 := sq_comm_of_fix hA hp hp2 (GSThmB.OddQuot.lieModel_of_equiv h.equivK₂ hlie) hS₂
    (hcard₂ ▸ h8) hy4 ((mem_normalizer_iff_map _ _).mpr hK₂) hc₂
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul he
  rw [← mul_assoc, h1 a ha, mul_assoc, h2 b hb, mul_assoc]

end IsProd

end L415

end CFSG.ComponentClassification.HarrisLit

module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightK

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)} {E : Subgroup X} {D : Finset (Fin 9)}

theorem inf_centralizer_le_zpowers_of_pair
    (S₀ : Sig36 X t J 9 e E D) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    {M : Subgroup X} (hJM : J ≤ M) (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ)
    (hNoA9 : ∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      ∀ K : Subgroup X, K ≤ centralizer ({x} : Set X) →
        IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set X))) →
        IsEmpty (↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin 9)))
    {H Q : Subgroup X} (hHN : H ≤ normalizer (M : Set X))
    (hQK : Q ≤ H ⊓ UnbalancedLayer.coreActionKernel M) (hQ2 : IsPGroup 2 Q) (htQ : t ∈ Q)
    (hCt : centralizer ({t} : Set X) ≤ H) {s g : X} (hsH : s ∈ H) (hst : s * t = t * s)
    (hs2 : s * s = 1) (hgs : g⁻¹ * t * g = s)
    (hd4 : ∀ y ∈ Q, y * s = s * y → y ≠ 1 → ∀ hy : g * y * g⁻¹ ∈ normalizer (M : Set X),
      6 ≤ (ρ ⟨g * y * g⁻¹, hy⟩).support.card)
    {b₁ b₂ : Perm (Fin 9)} (hb₁A : b₁ ∈ alternatingGroup (Fin 9))
    (hb₂A : b₂ ∈ alternatingGroup (Fin 9))
    (hb₁σ : b₁ * ρ ⟨s, hHN hsH⟩ = ρ ⟨s, hHN hsH⟩ * b₁)
    (hb₂σ : b₂ * ρ ⟨s, hHN hsH⟩ = ρ ⟨s, hHN hsH⟩ * b₂) (hb₁3 : orderOf b₁ = 3)
    (hb₂3 : orderOf b₂ = 3) (hb₁₂2 : b₁ * b₂ * (b₁ * b₂) = 1)
    (hb₁₂4 : (b₁ * b₂).support.card = 4) :
    Q ⊓ centralizer ({s} : Set X) ≤ zpowers t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Q ⊓ centralizer ({s} : Set X) with hCdef
  have hCQ' : C ≤ Q := inf_le_left
  have hC2 : IsPGroup 2 C := hQ2.to_le hCQ'
  have hCN : C ≤ normalizer (M : Set X) := fun y hy => hHN (hQK (hCQ' hy)).1
  have hyC : ∀ y : X, y ∈ C ↔ y ∈ Q ∧ y * s = s * y := fun y => by
    rw [hCdef, mem_inf, mem_centralizer_singleton_iff]
  have hsNC : s ∈ normalizer (C : Set X) :=
    Subgroup.centralizer_le_normalizer (C : Set X)
      (mem_centralizer_iff.mpr fun y hy => ((hyC y).mp hy).2)
  set B := C ⊔ zpowers s with hBdef
  have hB2 : IsPGroup 2 B :=
    hC2.to_sup_of_normal_left' (isPGroup_zpowers_of_mul_self hs2) (zpowers_le.mpr hsNC)
  have hBN : B ≤ normalizer (M : Set X) := sup_le hCN (zpowers_le.mpr (hHN hsH))
  set σ := ρ ⟨s, hHN hsH⟩ with hσdef
  have hbB : ∀ b : Perm (Fin 9), b * σ = σ * b →
      ∀ (y : X) (hy : y ∈ B), b * ρ ⟨y, hBN hy⟩ = ρ ⟨y, hBN hy⟩ * b := by
    intro b hbσ
    set Z : Subgroup X := ((centralizer ({b} : Set (Perm (Fin 9)))).comap ρ).map
      (normalizer (M : Set X)).subtype with hZdef
    have hCZ : C ≤ Z := fun y hy => by
      refine ⟨⟨y, hCN hy⟩, ?_, rfl⟩
      have h1 : ρ ⟨y, hCN hy⟩ = 1 :=
        hρ.eq_one_of_mem_coreActionKernel (by norm_num) (hQK (hCQ' hy)).2
      show ρ ⟨y, hCN hy⟩ ∈ centralizer ({b} : Set (Perm (Fin 9)))
      rw [h1]
      exact one_mem _
    have hsZ : s ∈ Z :=
      ⟨⟨s, hHN hsH⟩, mem_comap.mpr (mem_centralizer_singleton_iff.mpr hbσ.symm), rfl⟩
    intro y hy
    obtain ⟨y', hy', hyy⟩ := sup_le hCZ (zpowers_le.mpr hsZ) hy
    have h1 : (⟨y, hBN hy⟩ : ↥(normalizer (M : Set X))) = y' := Subtype.ext hyy.symm
    rw [h1]
    exact (mem_centralizer_singleton_iff.mp (mem_comap.mp hy')).symm
  let fM : ↥M →* Perm (Fin 9) := ρ.comp (Subgroup.inclusion le_normalizer)
  have hlift : ∀ b : Perm (Fin 9), b ∈ alternatingGroup (Fin 9) → b * σ = σ * b →
      orderOf b = 3 → ∃ x : X, ∃ hxM : x ∈ M, x ∈ centralizer (B : Set X) ∧
        (∃ a : ℕ, orderOf x = 3 ^ a) ∧ ρ ⟨x, le_normalizer hxM⟩ = b := by
    intro b hbA hbσ hb3
    obtain ⟨x₁, hx₁B, hx₁θ⟩ := hρ.exists_lift_of_isPGroup hBN hB2 (b := ⟨b, hbA⟩) (hbB b hbσ)
    have hρx₁ : fM x₁ = b := by
      change ρ ⟨x₁, le_normalizer x₁.2⟩ = b
      rw [hρ.apply_of_mem (by norm_num) x₁, hx₁θ]
    obtain ⟨k, ⟨a, hxa⟩, hxk⟩ := exists_pow_three_pow_eq_map fM x₁ (by rw [hρx₁, hb3])
    refine ⟨((x₁ ^ k : ↥M) : X), (x₁ ^ k).2, ?_, ⟨a, by rw [Subgroup.orderOf_coe, hxa]⟩, ?_⟩
    · rw [Subgroup.coe_pow]
      exact pow_mem hx₁B k
    · change fM (x₁ ^ k) = b
      rw [hxk, hρx₁]
  obtain ⟨x₁, hx₁M, hx₁B, ⟨a₁, hx₁a⟩, hx₁ρ⟩ := hlift _ hb₁A hb₁σ hb₁3
  obtain ⟨x₂, hx₂M, hx₂B, ⟨a₂, hx₂a⟩, hx₂ρ⟩ := hlift _ hb₂A hb₂σ hb₂3
  have hxs : ∀ x ∈ centralizer (B : Set X), x * s = s * x := fun x hx =>
    (mem_centralizer_iff.mp hx s (mem_sup_right (mem_zpowers s))).symm
  have hxC : ∀ x ∈ centralizer (B : Set X), ∀ y ∈ Q, y * s = s * y → x * y = y * x :=
    fun x hx y hyQ hys =>
      (mem_centralizer_iff.mp hx y (mem_sup_left ((hyC y).mpr ⟨hyQ, hys⟩))).symm
  have hto : orderOf t = 2 := S₀.pair.1.1
  have hts : t = g * s * g⁻¹ := by rw [← hgs]; group
  have hgC : ∀ y : X, y * s = s * y → g * y * g⁻¹ ∈ H := by
    intro y hys
    apply hCt
    rw [mem_centralizer_singleton_iff, hts]
    calc g * y * g⁻¹ * (g * s * g⁻¹) = g * (y * s) * g⁻¹ := by group
      _ = g * (s * y) * g⁻¹ := by rw [hys]
      _ = g * s * g⁻¹ * (g * y * g⁻¹) := by group
  by_cases h₁ : ρ ⟨g * x₁ * g⁻¹, hHN (hgC x₁ (hxs x₁ hx₁B))⟩ = 1
  swap
  · exact inf_centralizer_le_zpowers_of_three hHN hQ2 hto htQ hst hgC hd4 (hxs x₁ hx₁B)
      (hxC x₁ hx₁B) hx₁a h₁
  by_cases h₂ : ρ ⟨g * x₂ * g⁻¹, hHN (hgC x₂ (hxs x₂ hx₂B))⟩ = 1
  swap
  · exact inf_centralizer_le_zpowers_of_three hHN hQ2 hto htQ hst hgC hd4 (hxs x₂ hx₂B)
      (hxC x₂ hx₂B) hx₂a h₂
  exfalso
  set y := x₁ * x₂ with hydef
  have hyM : y ∈ M := M.mul_mem hx₁M hx₂M
  have hyB : y ∈ centralizer (B : Set X) := mul_mem hx₁B hx₂B
  have hyρ : ρ ⟨y, le_normalizer hyM⟩ = b₁ * b₂ := by
    have h1 : (⟨y, le_normalizer hyM⟩ : ↥(normalizer (M : Set X))) =
        ⟨x₁, le_normalizer hx₁M⟩ * ⟨x₂, le_normalizer hx₂M⟩ := rfl
    rw [h1, map_mul, hx₁ρ, hx₂ρ]
  obtain ⟨c, m, hmodd, hym⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  set f := y ^ m with hfdef
  have hfM : f ∈ M := M.pow_mem hyM m
  have hfB : f ∈ centralizer (B : Set X) := pow_mem hyB m
  have hfρ : ρ ⟨f, le_normalizer hfM⟩ = b₁ * b₂ := by
    have h1 : (⟨f, le_normalizer hfM⟩ : ↥(normalizer (M : Set X))) =
        ⟨y, le_normalizer hyM⟩ ^ m := rfl
    rw [h1, map_pow, hyρ]
    obtain ⟨r, rfl⟩ := hmodd
    rw [pow_succ, pow_mul, sq, hb₁₂2, one_pow, one_mul]
  have hf2c : f ^ 2 ^ c = 1 := by rw [hfdef, ← pow_mul, mul_comm, ← hym, pow_orderOf_eq_one]
  have hf2 : f * f = 1 := by
    have hff : f * f ∈ M := M.mul_mem hfM hfM
    have hρff : ρ ⟨f * f, le_normalizer hff⟩ = 1 := by
      have h1 : (⟨f * f, le_normalizer hff⟩ : ↥(normalizer (M : Set X))) =
          ⟨f, le_normalizer hfM⟩ * ⟨f, le_normalizer hfM⟩ := rfl
      rw [h1, map_mul, hfρ, hb₁₂2]
    have hodd := odd_orderOf_of_rho_eq_one hρ hff hρff
    have h2 : (f * f) ^ 2 ^ c = 1 := by
      rw [← sq, ← pow_mul, mul_comm, pow_mul, hf2c, one_pow]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2)
    rcases j with _ | j
    · rw [pow_zero] at hj
      exact orderOf_eq_one_iff.mp hj
    · rw [hj, pow_succ] at hodd
      exact absurd hodd (by simp [Nat.odd_mul])
  have hf4 : (ρ ⟨f, le_normalizer hfM⟩).support.card = 4 := by rw [hfρ, hb₁₂4]
  have hfs : f * s = s * f := hxs f hfB
  have hft : g * f * g⁻¹ * t = t * (g * f * g⁻¹) := by
    rw [hts]
    calc g * f * g⁻¹ * (g * s * g⁻¹) = g * (f * s) * g⁻¹ := by group
      _ = g * (s * f) * g⁻¹ := by rw [hfs]
      _ = g * s * g⁻¹ * (g * f * g⁻¹) := by group
  have hρgf : ρ ⟨g * f * g⁻¹, hHN (hgC f hfs)⟩ = 1 := by
    have h1 : (⟨g * f * g⁻¹, hHN (hgC f hfs)⟩ : ↥(normalizer (M : Set X))) =
        (⟨g * x₁ * g⁻¹, hHN (hgC x₁ (hxs x₁ hx₁B))⟩ *
          ⟨g * x₂ * g⁻¹, hHN (hgC x₂ (hxs x₂ hx₂B))⟩) ^ m := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, Subgroup.coe_mul]
      rw [show g * x₁ * g⁻¹ * (g * x₂ * g⁻¹) = g * y * g⁻¹ by rw [hydef]; group, conj_pow]
    rw [h1, map_pow, map_mul, h₁, h₂, one_mul, one_pow]
  have hgfJ : g * f * g⁻¹ ∈ normalizer (J : Set X) :=
    S₀.centralizer_le_normalizer hT13 hML hSch (mem_centralizer_singleton_iff.mpr hft)
  obtain ⟨ρJ, hρJ⟩ := exists_isPermAction (M := J) (by norm_num) (by norm_num) e
  obtain ⟨π', hπ'⟩ := exists_conj_rho_of_sup (by norm_num) hJM hsup hρ hρJ
  have hρJgf : ρJ ⟨g * f * g⁻¹, hgfJ⟩ = 1 := by
    have h1 := hπ' (g * f * g⁻¹) hgfJ (hHN (hgC f hfs))
    rw [hρgf] at h1
    have h2 : ρJ ⟨g * f * g⁻¹, hgfJ⟩ = π'⁻¹ * (π' * ρJ ⟨g * f * g⁻¹, hgfJ⟩ * π'⁻¹) * π' := by
      group
    rw [h2, ← h1]
    group
  exact S₀.false_of_fourPoint_mem_coreActionKernel_conj hPump hN1 hNoA9 hfM hf2 hf4 hft
    (hρJ.mem_coreActionKernel hgfJ hρJgf)

theorem inf_centralizer_le_zpowers_of_six
    (S₀ : Sig36 X t J 9 e E D) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    {M : Subgroup X} (hJM : J ≤ M) (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ)
    (hNoA9 : ∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      ∀ K : Subgroup X, K ≤ centralizer ({x} : Set X) →
        IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set X))) →
        IsEmpty (↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin 9)))
    {H Q : Subgroup X} (hHN : H ≤ normalizer (M : Set X))
    (hQK : Q ≤ H ⊓ UnbalancedLayer.coreActionKernel M) (hQ2 : IsPGroup 2 Q) (htQ : t ∈ Q)
    (hCt : centralizer ({t} : Set X) ≤ H) {s g : X} (hsH : s ∈ H) (hst : s * t = t * s)
    (hs2 : s * s = 1) (hgs : g⁻¹ * t * g = s)
    (hd4 : ∀ y ∈ Q, y * s = s * y → y ≠ 1 → ∀ hy : g * y * g⁻¹ ∈ normalizer (M : Set X),
      6 ≤ (ρ ⟨g * y * g⁻¹, hy⟩).support.card)
    (hσ2 : ρ ⟨s, hHN hsH⟩ * ρ ⟨s, hHN hsH⟩ = 1) (hσ6 : (ρ ⟨s, hHN hsH⟩).support.card = 6) :
    Q ⊓ centralizer ({s} : Set X) ≤ zpowers t := by
  classical
  set σ := ρ ⟨s, hHN hsH⟩ with hσdef
  set σ₀ : Perm (Fin 9) := SixGen.permOf [(0, 1), (2, 3), (4, 5)] with hσ₀def
  have hσ₀2 : σ₀ * σ₀ = 1 := by decide
  have hσ₀6 : σ₀.support.card = 6 := by decide
  have hct : σ.cycleType = σ₀.cycleType := by
    rw [SixGen.cycleType_of_mul_self (k := 3) hσ2 (by norm_num) hσ6,
      SixGen.cycleType_of_mul_self (k := 3) hσ₀2 (by norm_num) hσ₀6]
  obtain ⟨π, hπ⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr hct.symm)
  set c₁ : Perm (Fin 9) := SixGen.permOf [(0, 2), (2, 4), (1, 3), (3, 5)] with hc₁def
  set c₂ : Perm (Fin 9) := SixGen.permOf [(0, 5), (5, 3), (1, 4), (4, 2)] with hc₂def
  have hc₁3 : c₁ ^ 3 = 1 := by decide
  have hc₂3 : c₂ ^ 3 = 1 := by decide
  have hc₁1 : c₁ ≠ 1 := by decide
  have hc₂1 : c₂ ≠ 1 := by decide
  have hc₁σ : c₁ * σ₀ = σ₀ * c₁ := by decide
  have hc₂σ : c₂ * σ₀ = σ₀ * c₂ := by decide
  have hc₁A : c₁ ∈ alternatingGroup (Fin 9) := by rw [Perm.mem_alternatingGroup]; decide
  have hc₂A : c₂ ∈ alternatingGroup (Fin 9) := by rw [Perm.mem_alternatingGroup]; decide
  have hc₁₂ : c₁ * c₂ * (c₁ * c₂) = 1 := by decide
  have hc₁₂4 : (c₁ * c₂).support.card = 4 := by decide
  have hconj : ∀ c : Perm (Fin 9), c ^ 3 = 1 → c ≠ 1 → c * σ₀ = σ₀ * c →
      c ∈ alternatingGroup (Fin 9) → π * c * π⁻¹ ∈ alternatingGroup (Fin 9) ∧
        π * c * π⁻¹ * σ = σ * (π * c * π⁻¹) ∧ orderOf (π * c * π⁻¹) = 3 := by
    intro c hc3 hc1 hcσ hcA
    refine ⟨(alternatingGroup.normal (α := Fin 9)).conj_mem c hcA π, ?_, ?_⟩
    · rw [← hπ]
      calc π * c * π⁻¹ * (π * σ₀ * π⁻¹) = π * (c * σ₀) * π⁻¹ := by group
        _ = π * (σ₀ * c) * π⁻¹ := by rw [hcσ]
        _ = π * σ₀ * π⁻¹ * (π * c * π⁻¹) := by group
    · refine orderOf_eq_prime (by rw [conj_pow, hc3]; group) fun h => hc1 ?_
      have := congrArg (fun z => π⁻¹ * z * π) h
      simpa [mul_assoc] using this
  obtain ⟨hb₁A, hb₁σ, hb₁3⟩ := hconj c₁ hc₁3 hc₁1 hc₁σ hc₁A
  obtain ⟨hb₂A, hb₂σ, hb₂3⟩ := hconj c₂ hc₂3 hc₂1 hc₂σ hc₂A
  have hb₁₂ : π * c₁ * π⁻¹ * (π * c₂ * π⁻¹) = π * (c₁ * c₂) * π⁻¹ := by group
  have hb₁₂2 : π * (c₁ * c₂) * π⁻¹ * (π * (c₁ * c₂) * π⁻¹) = 1 := by
    rw [show π * (c₁ * c₂) * π⁻¹ * (π * (c₁ * c₂) * π⁻¹) =
      π * (c₁ * c₂ * (c₁ * c₂)) * π⁻¹ by group, hc₁₂]
    group
  have hb₁₂4 : (π * (c₁ * c₂) * π⁻¹).support.card = 4 := by
    rw [Perm.card_support_conj]
    exact hc₁₂4
  exact S₀.inf_centralizer_le_zpowers_of_pair hT13 hML hSch hPump hN1 hJM hsup hρ hNoA9 hHN hQK
    hQ2 htQ hCt hsH hst hs2 hgs hd4 hb₁A hb₂A hb₁σ hb₂σ hb₁3 hb₂3 (by rw [hb₁₂]; exact hb₁₂2)
    (by rw [hb₁₂]; exact hb₁₂4)

end Sig36

end CFSG.ComponentClassification.SolMax

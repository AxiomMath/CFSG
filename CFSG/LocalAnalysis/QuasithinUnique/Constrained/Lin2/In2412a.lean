module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InOut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InTorus
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section Complement

variable {G : Type} [Group G] [Finite G] {T M H S L D P : Subgroup G} {n : ℕ}

theorem Lin2Cfg.mem_pCoreOf_of_commutator_le (h : Lin2Cfg G T M H S L n D)
    (hQL : pCoreOf 2 L = pCoreOf 2 H) {F : Subgroup G} (hF2 : IsPGroup 2 F)
    (hHF : H = L ⊔ F) {K : Type} [Field K] [Fintype K] (A : Adapted L P n K) {c : G}
    (hcH : c ∈ H) (hc : ∀ ℓ ∈ L, c * ℓ * c⁻¹ * ℓ⁻¹ ∈ pCoreOf 2 L) : c ∈ pCoreOf 2 H := by
  set Q := pCoreOf 2 H with hQ
  have hQLle : Q ≤ L := by
    rw [← hQL]
    exact CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L
  have h2K : (2 : K) = 0 := two_eq_zero_of_card h.one_pos A.card_eq
  have hFN : F ≤ Subgroup.normalizer (L : Set G) := (le_sup_right.trans hHF.ge).trans h.H_le_normalizer_L
  set C := centralizerSection H L Q with hC
  have hcC : c ∈ C := by
    rw [hC, mem_centralizerSection_iff_of_le hQLle]
    refine ⟨hcH, fun x hx => ?_⟩
    have := Q.inv_mem (hQL ▸ hc x hx)
    have e : (c * x * c⁻¹ * x⁻¹)⁻¹ = x * c * x⁻¹ * c⁻¹ := by group
    rwa [e] at this
  have hCL : ∀ y ∈ C, y ∈ L → y ∈ Q := by
    intro y hyC hyL
    have hy := (mem_centralizerSection_iff_of_le hQLle).1 hyC
    have hcent : ∀ ℓ : L, A.α ⟨y, hyL⟩ * A.α ℓ = A.α ℓ * A.α ⟨y, hyL⟩ := by
      intro ℓ
      have h1 := hy.2 (ℓ : G) ℓ.2
      have h2 : (ℓ : G) * y * (ℓ : G)⁻¹ * y⁻¹ ∈ pCoreOf 2 L := hQL ▸ h1
      have h3 := (A.mem_pCoreOf_iff ((ℓ * ⟨y, hyL⟩ * ℓ⁻¹ * ⟨y, hyL⟩⁻¹ : L))).1 h2
      simp only [map_mul, map_inv] at h3
      calc A.α ⟨y, hyL⟩ * A.α ℓ = (A.α ℓ * A.α ⟨y, hyL⟩ * (A.α ℓ)⁻¹ * (A.α ⟨y, hyL⟩)⁻¹)⁻¹ *
            (A.α ℓ * A.α ⟨y, hyL⟩) := by group
        _ = A.α ℓ * A.α ⟨y, hyL⟩ := by rw [h3]; simp
    have hz : A.α ⟨y, hyL⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨ℓ, rfl⟩ := A.α_surj g
      exact (hcent ℓ).symm
    rw [center_specialLinearGroup_eq_bot K h2K, Subgroup.mem_bot] at hz
    exact hQL ▸ (A.mem_pCoreOf_iff ⟨y, hyL⟩).2 hz
  have hC2 : IsPGroup 2 C := by
    intro g
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (g : G) ^ 2 ^ j ∈ L := by
      have hgH : (g : G) ∈ L ⊔ F := hHF ▸ (centralizerSection_le_left H L Q g.2)
      obtain ⟨ℓ, hℓ, f, hf, hgf⟩ := (mem_sup_iff_of_le_normalizer hFN).1 hgH
      obtain ⟨j, hj⟩ := hF2 ⟨f, hf⟩
      refine ⟨j, ?_⟩
      obtain ⟨x', hx', hx⟩ := A4.exists_pow_mul_eq hℓ (hFN hf) (2 ^ j)
      rw [hgf, hx]
      have : f ^ 2 ^ j = 1 := congrArg Subtype.val hj
      rw [this, mul_one]
      exact hx'
    have hgj : (g : G) ^ 2 ^ j ∈ Q := hCL _ (C.pow_mem g.2 _) hj
    obtain ⟨i, hi⟩ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H ⟨_, hgj⟩
    refine ⟨j + i, Subtype.ext ?_⟩
    have : ((g : G) ^ 2 ^ j) ^ 2 ^ i = 1 := congrArg Subtype.val hi
    rw [← pow_mul, ← pow_add] at this
    exact this
  have hCH : C ≤ H := centralizerSection_le_left H L Q
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => conj_mem_centralizerSection (Subgroup.le_normalizer hg)
      (h.H_le_normalizer_L hg) (h.H_le_normalizer_Q hg) hx, fun hx => ?_⟩
    have := conj_mem_centralizerSection (Subgroup.le_normalizer (Subgroup.inv_mem _ hg))
      (Subgroup.inv_mem _ (h.H_le_normalizer_L hg))
      (Subgroup.inv_mem _ (h.H_le_normalizer_Q hg)) hx
    simpa [mul_assoc] using this
  exact le_pCoreOf_of_normalizes hCH hHC hC2 hcC

theorem Lin2Cfg.exists_injective_of_complement (h : Lin2Cfg G T M H S L n D)
    (hQL : pCoreOf 2 L = pCoreOf 2 H) {F : Subgroup G} (hF2 : IsPGroup 2 F) (hFL : F ⊓ L = ⊥)
    (hHF : H = L ⊔ F) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K), Fintype.card K = 2 ^ n ∧
      ∃ φ : F →* (K ≃+* K), Function.Injective φ := by
  obtain ⟨K, _, _, ⟨A⟩⟩ := h.coord
  have h2K : (2 : K) = 0 := two_eq_zero_of_card h.one_pos A.card_eq
  obtain ⟨ψ, hψ⟩ := exists_injective_outer_sl2_char_two K h2K
  have hFH : F ≤ H := le_sup_right.trans hHF.ge
  have hFN : F ≤ Subgroup.normalizer (L : Set G) := hFH.trans h.H_le_normalizer_L
  have hFQ : F ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := hQL ▸ (hFH.trans h.H_le_normalizer_Q)
  let act : F →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hFN)
  have hact : ∀ (f : F) (ℓ : L), ((act f ℓ : L) : G) = (f : G) * (ℓ : G) * (f : G)⁻¹ :=
    fun _ _ => rfl
  have hker : ∀ f : F, ∀ ℓ : L, A.α (act f ℓ) = 1 ↔ A.α ℓ = 1 := by
    intro f ℓ
    rw [← A.mem_pCoreOf_iff, ← A.mem_pCoreOf_iff, hact]
    constructor
    · intro hmem
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hFQ f.2)) _).1 hmem
      simpa [mul_assoc] using this
    · intro hmem
      exact (Subgroup.mem_normalizer_iff.1 (hFQ f.2) _).1 hmem
  have hinner : ∀ a : F, (∃ k : SL(2, K), ∀ ℓ, A.α (act a ℓ) = k * A.α ℓ * k⁻¹) → a = 1 := by
    rintro f ⟨k, hk⟩
    obtain ⟨ℓ₀, rfl⟩ := A.α_surj k
    have hcH : (ℓ₀ : G)⁻¹ * (f : G) ∈ H :=
      H.mul_mem (H.inv_mem (h.L_le_H ℓ₀.2)) (hFH f.2)
    have hc : ∀ ℓ ∈ L, (ℓ₀ : G)⁻¹ * (f : G) * ℓ * ((ℓ₀ : G)⁻¹ * (f : G))⁻¹ * ℓ⁻¹ ∈ pCoreOf 2 L := by
      intro x hx
      set ℓ : L := ⟨x, hx⟩
      rw [show x = (ℓ : G) from rfl]
      have hα : A.α (act f ℓ) = A.α (ℓ₀ * ℓ * ℓ₀⁻¹) := by rw [hk ℓ]; simp
      have h1 : (ℓ₀⁻¹ * (act f ℓ * (ℓ₀ * ℓ * ℓ₀⁻¹)⁻¹) * ℓ₀ : L) ∈ A.α.ker := by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        rw [hα]
        simp
      have h2 := (A.mem_pCoreOf_iff _).2 h1
      convert h2 using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hact]
      group
    have hcQ := h.mem_pCoreOf_of_commutator_le hQL hF2 hHF A hcH hc
    have hfL : (f : G) ∈ L := by
      have := L.mul_mem ℓ₀.2 ((hQL ▸ hcQ : (ℓ₀ : G)⁻¹ * (f : G) ∈ pCoreOf 2 L) |>
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L))
      simpa using this
    have : (f : G) ∈ F ⊓ L := ⟨f.2, hfL⟩
    rw [hFL, Subgroup.mem_bot] at this
    exact Subtype.ext this
  obtain ⟨φ, hφ⟩ := exists_injective_of_act_quot A.α A.α_surj act hker hinner
  exact ⟨K, inferInstance, inferInstance, A.card_eq, ψ.comp φ, hψ.comp hφ⟩

theorem Lin2Cfg.isCyclic_of_complement (h : Lin2Cfg G T M H S L n D)
    (hQL : pCoreOf 2 L = pCoreOf 2 H) {F : Subgroup G} (hF2 : IsPGroup 2 F) (hFL : F ⊓ L = ⊥)
    (hHF : H = L ⊔ F) : IsCyclic F := by
  obtain ⟨K, _, _, -, φ, hφ⟩ := h.exists_injective_of_complement hQL hF2 hFL hHF
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  exact isCyclic_of_injective φ hφ

theorem Lin2Cfg.even_of_involution (h : Lin2Cfg G T M H S L n D)
    (hQL : pCoreOf 2 L = pCoreOf 2 H) {F : Subgroup G} (hF2 : IsPGroup 2 F) (hFL : F ⊓ L = ⊥)
    (hHF : H = L ⊔ F) {f : G} (hf : f ∈ F) (hf1 : f ≠ 1) (hf2 : f ^ 2 = 1) : Even n := by
  obtain ⟨K, _, _, hK, φ, hφ⟩ := h.exists_injective_of_complement hQL hF2 hFL hHF
  have hKn : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK]
  have hcard := (card_ringAut_and_isCyclic Nat.prime_two K hKn).1
  have hne : φ ⟨f, hf⟩ ≠ 1 := fun e => hf1 (congrArg Subtype.val (hφ (e.trans (map_one φ).symm)))
  have hsq : φ ⟨f, hf⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨f, hf⟩ : F) ^ 2 = 1 := Subtype.ext hf2
    rw [this, map_one]
  have hord : orderOf (φ ⟨f, hf⟩) = 2 := orderOf_eq_prime hsq hne
  have hdvd : orderOf (φ ⟨f, hf⟩) ∣ Nat.card (K ≃+* K) := orderOf_dvd_natCard _
  rw [hord] at hdvd
  have : 2 ∣ n := hcard ▸ hdvd
  exact even_iff_two_dvd.2 this

end Complement

end CFSG.QuasithinUnique.Lin2

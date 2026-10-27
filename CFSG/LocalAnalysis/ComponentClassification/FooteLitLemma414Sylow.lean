module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma414Trans

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem card_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {S X P : Subgroup G} (hS : IsSylowOf p S X)
    (hPX : P ≤ X) (hP : IsPGroup p P) : Nat.card P ≤ Nat.card S := by
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hS hPX hP
  rw [← card_conjugate_eq_card P k]
  exact card_le_of_le (conjugate_le_of_forall hk)

theorem exists_central_involution {T : Subgroup G} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    ∃ a ∈ T, orderOf a = 2 ∧ ∀ x ∈ T, x * a = a * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥T := (nontrivial_iff_ne_bot T).mpr hT1
  have hZnt : Nontrivial ↥(center ↥T) := hT.center_nontrivial
  obtain ⟨m, hm⟩ := (hT.to_subgroup (center ↥T)).exists_card_eq
  have hm1 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact (Finite.one_lt_card_iff_nontrivial.mpr hZnt).ne' hm
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥T)) 2
    (by rw [hm]; exact dvd_pow_self 2 hm1)
  refine ⟨((c : ↥T) : G), (c : ↥T).2, by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc],
    fun x hx => ?_⟩
  have h1 := mem_center_iff.mp c.2 ⟨x, hx⟩
  exact congrArg Subtype.val h1

theorem isSylowOf_centralizer_of_le
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) {M : Subgroup G} (hM : IsFooteM L M) {t : G}
    (ht : orderOf t = 2) (htC : t ∈ coreActionKernel M) {S : Subgroup G}
    (hS : IsSylowOf 2 S (normalizer (M : Set G))) (hSt : S ≤ centralizer ({t} : Set G)) :
    IsSylowOf 2 S (centralizer ({t} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀, hS₀N⟩ := exists_isSylowOf_centralizer_le_normalizer h h47 hST hM ht htC
  have h1 := card_le_of_isSylowOf hS hS₀N hS₀.isPGroup
  have h2 := card_le_of_isSylowOf hS₀ hSt hS.isPGroup
  apply isSylowOf_of_card hSt
  rw [← hS₀.card_eq]
  omega

theorem exists_omega_sylow
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G} (hM : IsFooteM L M) {t₁ t₂ : G}
    (ht₁ : FooteInCC M t₁) (ht₂ : FooteInCC M t₂) (ht₂K : t₂ ∈ footeK L t₁) (hne : t₂ ≠ t₁) :
    ∃ T A S : Subgroup G, IsSylowOf 2 T (coreActionKernel M) ∧ IsOmegaOneOf A T ∧
      8 ≤ Nat.card A ∧ t₁ ∈ A ∧ (∀ a ∈ A, a ≠ 1 → FooteAConj M A t₁ a) ∧
      (∀ a ∈ A, a ≠ 1 → FooteInCC M a) ∧ IsSylowOf 2 S (normalizer (M : Set G)) ∧
      S ≤ normalizer (A : Set G) ∧ T ≤ S ∧ S ⊓ coreActionKernel M = T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₁, A, hT₁, hA, ht₁A, -, hA8, htr⟩ :=
    exists_omega_transitive h h47 hST hAsc h2An hM ht₁ ht₂ ht₂K hne
  set C := coreActionKernel M with hC
  set N := normalizer (M : Set G) with hN
  have hCN : C ≤ N := fun c hc => (mem_coreActionKernel.mp hc).1
  have hCnC : N ≤ normalizer (C : Set G) := normalizer_le_normalizer_coreActionKernel M
  have ht₁2 : orderOf t₁ = 2 := ht₁.1
  have ht₁1 : t₁ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht₁2; omega
  have hT₁C : T₁ ≤ C := hT₁.le.trans inf_le_left
  have hACC : ∀ a ∈ A, a ≠ 1 → FooteInCC M a := by
    intro a ha ha1
    obtain ⟨n, hnN, -, rfl⟩ := htr a ha ha1
    exact ht₁.conj hnN
  obtain ⟨T, hT, hT₁T⟩ := exists_isSylowOf_ge_of_le hT₁C hT₁.isPGroup
  have hCT : T ⊓ centralizer ({t₁} : Set G) = T₁ :=
    hT₁.eq_of_le (le_inf hT₁T (hT₁.le.trans inf_le_right))
      (fun x hx => mem_inf.mpr ⟨hT.le (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩)
      (hT.isPGroup.to_le inf_le_left)
  have hTT₁ : T = T₁ := by
    have hT1 : T ≠ ⊥ := fun h1 => ht₁1 (by
      have h2 := hT₁T (hA.1 ht₁A)
      rwa [h1, mem_bot] at h2)
    obtain ⟨a, haT, ha2, haZ⟩ := exists_central_involution hT.isPGroup hT1
    have haT₁ : a ∈ T₁ := hCT ▸ mem_inf.mpr ⟨haT, mem_centralizer_singleton_iff.mpr
      (haZ t₁ (hT₁T (hA.1 ht₁A))).symm⟩
    have haA : a ∈ A := hA.2.2 a haT₁ (by rw [← ha2]; exact pow_orderOf_eq_one a)
    have ha1 : a ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ha2; omega
    obtain ⟨n, hnN, -, hna⟩ := htr a haA ha1
    have hle : conjugate T n ≤ C ⊓ centralizer ({t₁} : Set G) := by
      intro x hx
      rw [mem_conjugate_iff] at hx
      refine mem_inf.mpr ⟨?_, ?_⟩
      · have h1 := (mem_normalizer_iff.mp (hCnC (inv_mem hnN)) _).mp (hT.le hx)
        rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at h1
      · rw [mem_centralizer_singleton_iff]
        have h1 := haZ _ hx
        rw [← hna] at h1
        calc x * t₁ = n⁻¹ * ((n * x * n⁻¹) * (n * t₁ * n⁻¹)) * n := by group
          _ = n⁻¹ * ((n * t₁ * n⁻¹) * (n * x * n⁻¹)) * n := by rw [h1]
          _ = t₁ * x := by group
    have hcard := card_le_of_isSylowOf hT₁ hle (hT.isPGroup.of_equiv
      (equivMapOfInjective T _ (MulAut.conj n⁻¹).injective))
    rw [card_conjugate_eq_card] at hcard
    exact (eq_of_le_of_card_ge hT₁T hcard).symm
  subst hTT₁
  have hAC : A ≤ C := hA.1.trans hT₁C
  obtain ⟨W, hW, hWA⟩ := exists_isKleinFour_le hA.2.1 (by omega)
  have hNA : normalizer (A : Set G) ≤ N := foote_cor_4_8_iv h h47 hST hM hAC hW hWA
  have hTNA : T ≤ normalizer (A : Set G) := fun x hx => hA.mem_normalizer (le_normalizer hx)
  obtain ⟨S, hS, hTS⟩ := exists_isSylowOf_ge_of_le hTNA hT.isPGroup
  obtain ⟨S', hS', hSS'⟩ := exists_isSylowOf_ge_of_le (hS.le.trans hNA) hS.isPGroup
  have hS'C : S' ⊓ C = T :=
    hT.eq_of_le (le_inf (hTS.trans hSS') hT.le) inf_le_right (hS'.isPGroup.to_le inf_le_left)
  have hS'T : S' ≤ normalizer (T : Set G) := by
    intro s hs
    rw [← hS'C]
    exact mem_normalizer_inf_of_mem (le_normalizer hs) (hCnC (hS'.le hs))
  have hS'A : S' ≤ normalizer (A : Set G) := fun s hs => hA.mem_normalizer (hS'T hs)
  have hSS'eq : S' = S := hS.eq_of_le hSS' hS'A hS'.isPGroup
  subst hSS'eq
  exact ⟨T, A, S', hT, hA, hA8, ht₁A, htr, hACC, hS', hS'A, hTS.trans hSS', hS'C⟩

end CFSG.ComponentClassification.FooteLit

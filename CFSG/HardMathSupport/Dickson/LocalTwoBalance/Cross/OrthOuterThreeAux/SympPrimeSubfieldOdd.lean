module

public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog SpChain
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (odd_symplectic_automorphism_semilinear_representation)
open CFSG.RankThree.CASymplecticSubfield

variable {K : Type} [Field K]

theorem symplectic_prime_subfield_fixed_group_and_full_centralizer_odd {ℓ p f r : ℕ}
    (hℓ : ℓ.Prime) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hf : 1 ≤ f) (hr : 2 ≤ r)
    (hK : Nat.card K = ℓ ^ f) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    p ∣ f ∧ Nat.card (descentField σ) = ℓ ^ (f / p) ∧
    IsSimpleGroup (StatedProj (StatedSp r K)) ∧
    (∃ x y : StatedProj (StatedSp r K), x * y ≠ y * x) ∧
    Function.Injective (subfieldSpProj r (descentField σ)) ∧
    (∀ x : StatedProj (StatedSp r K), x ∈ subfieldFixedGroup K r σ ↔ fieldAut r K σ x = x) ∧
    CFSG.solvableRadical (subfieldFixedGroup K r σ) = ⊥ ∧
    (¬(r = 2 ∧ ℓ ^ (f / p) = 2) →
      IsSimpleGroup (subfieldFixedGroup K r σ) ∧
        ∃ x y : subfieldFixedGroup K r σ, x * y ≠ y * x) ∧
    (r = 2 ∧ ℓ ^ (f / p) = 2 →
      Nonempty (subfieldFixedGroup K r σ ≃* Equiv.Perm (Fin 6)) ∧
        Nonempty (↥(⁅subfieldFixedGroup K r σ, subfieldFixedGroup K r σ⁆ :
          Subgroup (StatedProj (StatedSp r K))) ≃* alternatingGroup (Fin 6)) ∧
        Nat.card (subfieldFixedGroup K r σ) = 720) ∧
    fixingSubgroup (MulAut (StatedProj (StatedSp r K)))
        (subfieldFixedGroup K r σ : Set (StatedProj (StatedSp r K))) =
      (fixingSubgroup (K ≃+* K) (descentField σ : Set K)).map (fieldAut r K) ∧
    (fixingSubgroup (K ≃+* K) (descentField σ : Set K)).map (fieldAut r K) =
      Subgroup.zpowers (fieldAut r K σ) ∧
    Nat.card (Subgroup.zpowers (fieldAut r K σ)) = p ∧
    Subgroup.centralizer (((subfieldFixedGroup K r σ).map MulAut.conj :
        Subgroup (MulAut (StatedProj (StatedSp r K)))) :
          Set (MulAut (StatedProj (StatedSp r K)))) =
      Subgroup.zpowers (fieldAut r K σ) ∧
    (r = 2 ∧ ℓ ^ (f / p) = 2 → (∃ x ∈ subfieldFixedGroup K r σ, orderOf x = p) →
      ℓ = 2 ∧ (p = 3 ∨ p = 5) ∧ f = p ∧ ℓ ^ f = 2 ^ p) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hr1 : 1 ≤ r := by omega
  have : NeZero r := ⟨by omega⟩
  set k := descentField σ with hkdef
  set H₀ := subfieldFixedGroup K r σ with hH₀
  obtain ⟨hpf, hkcard⟩ := CFSG.RankThree.PartOne.card_semilinearFixedSubfield hℓ hf hK hσ
  have hk : Nat.card k = ℓ ^ (f / p) := hkcard
  have hpf' : p ≤ f := Nat.le_of_dvd (by omega) hpf
  have hfp : 1 ≤ f / p := (Nat.one_le_div_iff hp.pos).mpr hpf'
  have hq0 : 2 ≤ ℓ ^ (f / p) := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by have := hp.two_le; omega)
      _ ≤ ℓ ^ f := Nat.pow_le_pow_left hℓ.two_le f
  have hTs : IsSimpleGroup (StatedProj (StatedSp r K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K r hr1
      (Or.inl (Or.inr hK4))
  have hTp : Group.IsPerfect (StatedProj (StatedSp r K)) :=
    CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect r K
      (Or.inl (exists_finset_card_four hK4))
  have hTnc : ∃ x y : StatedProj (StatedSp r K), x * y ≠ y * x := exists_ne_of_isPerfect
  have hcenter : Subgroup.center (StatedProj (StatedSp r K)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (StatedProj (StatedSp r K)))
      with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hTnc
      exact hxy (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x)
  have hconj := conj_injective_of_center_eq_bot hcenter
  have hinj := subfieldSpProj_injective hr1 k
  have hodd : Odd (orderOf σ) := hσ ▸ hp.odd_of_ne_two hp2
  have hfixpts : ∀ x, x ∈ H₀ ↔ fieldAut r K σ x = x := fun x =>
    (fieldAut_apply_eq_self_iff hr1 hodd x).symm
  let eH : StatedProj (StatedSp r k) ≃* H₀ := MonoidHom.ofInjective hinj
  have : Finite k := Subtype.finite
  have : Fintype k := Fintype.ofFinite k
  have hsimple : ¬(r = 2 ∧ ℓ ^ (f / p) = 2) → IsSimpleGroup H₀ ∧ Group.IsPerfect H₀ := by
    intro hne
    have hcases : 4 ≤ Nat.card k ∨ (Nat.card k = 3 ∧ 2 ≤ r) ∨ (Nat.card k = 2 ∧ 3 ≤ r) := by
      rw [hk]
      by_cases h4 : 4 ≤ ℓ ^ (f / p)
      · exact Or.inl h4
      · by_cases h3 : ℓ ^ (f / p) = 3
        · exact Or.inr (Or.inl ⟨h3, hr⟩)
        · refine Or.inr (Or.inr ⟨by omega, ?_⟩)
          by_contra hr3
          exact hne ⟨by omega, by omega⟩
    have hs : IsSimpleGroup (StatedProj (StatedSp r k)) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k r hr1
        (by rcases hcases with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr h)
    have hperf : Group.IsPerfect (StatedProj (StatedSp r k)) :=
      CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect r k
        (by rcases hcases with h | h
            · exact Or.inl (exists_finset_card_four h)
            · exact Or.inr h)
    exact ⟨eH.symm.isSimpleGroup, Group.IsPerfect.ofSurjective (f := eH.toMonoidHom)
      eH.surjective⟩
  have hexc : r = 2 ∧ ℓ ^ (f / p) = 2 → Nonempty (H₀ ≃* Equiv.Perm (Fin 6)) := by
    rintro ⟨rfl, h2⟩
    have hk2 : Fintype.card k = 2 := by rw [← Nat.card_eq_fintype_card, hk, h2]
    have : CharP k 2 := charP_of_card_eq_prime hk2
    obtain ⟨e6⟩ := nonempty_statedSp_two_mulEquiv_perm hk2
    exact ⟨eH.symm.trans ((MulEquiv.ofBijective (proj 2 k)
      UnitaryHigher.proj_bijective_of_charTwo).symm.trans e6)⟩
  have hrad : CFSG.solvableRadical H₀ = ⊥ := by
    by_cases he : r = 2 ∧ ℓ ^ (f / p) = 2
    · obtain ⟨e⟩ := hexc he
      exact solvableRadical_eq_bot_of_mulEquiv_perm_six e
    · obtain ⟨hs, hperf⟩ := hsimple he
      exact solvableRadical_eq_bot_of_isSimpleGroup
  have hprime : ∀ g : StatedSp r K, (g : GL (Fin r ⊕ Fin r) K) ∈ UnitaryHigher.primeFieldSp r K →
      proj r K g ∈ H₀ := by
    intro g hg
    obtain ⟨g₀, hg₀⟩ := primeFieldSp_le_range k hg
    exact mem_range_subfieldSpProj.mpr ⟨g₀, by rw [show subfieldSpHom r k g₀ = g from
      Subtype.ext hg₀]⟩
  have hallE : ∀ β : MulAut (StatedProj (StatedSp r K)), (∀ x ∈ H₀, β x = x) →
      β ∈ spSemilinearAutGroup r K := by
    intro β hβ
    rcases (by omega : 3 ≤ r ∨ r = 2) with h3 | rfl
    · rw [(automorphism_generation h3).1]
      exact Subgroup.mem_top β
    · by_cases hℓ2 : ℓ = 2
      · subst hℓ2
        exact mem_spSemilinearAutGroup_of_fixes hf hK β fun g hg => hβ _ (hprime g hg)
      · have hodd' : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
        obtain ⟨A, τ, hAτ⟩ :=
          (odd_symplectic_automorphism_semilinear_representation hodd' le_rfl).1 β
        exact mem_spSemilinearAutGroup_iff.mpr ⟨A, τ, hAτ⟩
  have hfixing : fixingSubgroup (MulAut (StatedProj (StatedSp r K)))
      (H₀ : Set (StatedProj (StatedSp r K))) =
        (fixingSubgroup (K ≃+* K) (k : Set K)).map (fieldAut r K) := by
    ext β
    rw [mem_fixingSubgroup_iff]
    constructor
    · intro hβ
      have hβ' : ∀ x ∈ H₀, β x = x := fun x hx => hβ x hx
      obtain ⟨A, τ, rfl⟩ := mem_spSemilinearAutGroup_iff.mp (hallE β hβ')
      obtain ⟨heq, hτ⟩ := eq_fieldAut_of_fixes hr1 A τ hβ'
      rw [heq]
      exact ⟨τ, (mem_fixingSubgroup_iff _).mpr fun t ht => by
        rw [RingAut.smul_def]; exact hτ t ht, rfl⟩
    · rintro ⟨τ, hτ, rfl⟩ x hx
      rw [MulAut.smul_def]
      exact fieldAut_apply_of_fixes (fun t ht => by
        have := (mem_fixingSubgroup_iff _).mp hτ t ht
        rwa [RingAut.smul_def] at this) hx
  have hfield : (fixingSubgroup (K ≃+* K) (k : Set K)).map (fieldAut r K) =
      Subgroup.zpowers (fieldAut r K σ) := by
    ext β
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      have hτσ : τ ∈ Subgroup.zpowers σ := mem_zpowers_of_fixed fun x hx => by
        have := (mem_fixingSubgroup_iff _).mp hτ x (mem_descentField.mpr hx)
        rwa [RingAut.smul_def] at this
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτσ
      exact ⟨n, (map_zpow (fieldAut r K) σ n).symm⟩
    · rintro ⟨n, rfl⟩
      refine ⟨σ ^ n, (mem_fixingSubgroup_iff _).mpr fun t ht => ?_, map_zpow _ _ _⟩
      have hσt : σ ∈ MulAction.stabilizer (K ≃+* K) t := by
        rw [MulAction.mem_stabilizer_iff, RingAut.smul_def]
        exact mem_descentField.mp ht
      exact (MulAction.stabilizer (K ≃+* K) t).zpow_mem hσt n
  have hfinj : Function.Injective (fieldAut r K) :=
    (CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent hℓ hf hr
      hK).2.1
  have hord : Nat.card (Subgroup.zpowers (fieldAut r K σ)) = p := by
    rw [Nat.card_zpowers, orderOf_injective (fieldAut r K) hfinj σ, hσ]
  have hcent : Subgroup.centralizer ((H₀.map MulAut.conj :
      Subgroup (MulAut (StatedProj (StatedSp r K)))) :
        Set (MulAut (StatedProj (StatedSp r K)))) = Subgroup.zpowers (fieldAut r K σ) := by
    rw [← hfield, ← hfixing]
    ext β
    rw [Subgroup.mem_centralizer_iff, mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      rw [MulAut.smul_def]
      have h1 := h (MulAut.conj x) ⟨x, hx, rfl⟩
      rw [mul_conj_eq] at h1
      exact (hconj (mul_right_cancel h1)).symm
    · rintro h _ ⟨x, hx, rfl⟩
      have h1 := h x hx
      rw [MulAut.smul_def] at h1
      change MulAut.conj x * β = β * MulAut.conj x
      rw [mul_conj_eq, h1]
  refine ⟨hpf, hk, hTs, hTnc, hinj, hfixpts, hrad, fun hne => ?_, fun he => ?_, hfixing, hfield,
    hord, hcent, fun he hx => ?_⟩
  · obtain ⟨hs, hperf⟩ := hsimple hne
    exact ⟨hs, exists_ne_of_isPerfect⟩
  · obtain ⟨e⟩ := hexc he
    refine ⟨⟨e⟩, nonempty_commutator_mulEquiv_alternating e, ?_⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  · obtain ⟨hr2, h2⟩ := he
    obtain ⟨x, hxH, hxp⟩ := hx
    obtain ⟨e⟩ := hexc ⟨hr2, h2⟩
    have hℓ2 : ℓ = 2 := by
      have hdvd : ℓ ∣ 2 := h2 ▸ dvd_pow_self ℓ (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp hdvd
    subst hℓ2
    have hfp1 : f / p = 1 := Nat.pow_right_injective (le_refl 2) (by simpa using h2)
    have hfeq : f = p := by
      obtain ⟨c, hc⟩ := hpf
      rw [hc, Nat.mul_div_cancel_left _ hp.pos] at hfp1
      rw [hc, hfp1, mul_one]
    have h720 : Nat.card H₀ = 720 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      rfl
    have hdvd : p ∣ 2 ^ 4 * (3 ^ 2 * 5) := by
      rw [← hxp]
      have := Subgroup.orderOf_dvd_natCard H₀ hxH
      rw [h720] at this
      exact this
    have hp35 : p = 3 ∨ p = 5 := by
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
      · exact absurd (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two |>.mp
          (hp.dvd_of_dvd_pow h)) hp2
      · rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
            (hp.dvd_of_dvd_pow h'))
        · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h')
    exact ⟨rfl, hp35, hfeq, by rw [hfeq]⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

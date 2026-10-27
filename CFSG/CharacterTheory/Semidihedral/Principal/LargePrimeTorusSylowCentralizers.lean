module

public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizersSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.TrivialCoreTorusSubgroups

public section

open scoped Classical Pointwise

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open
  LargePrimeTorus

theorem trivial_core_large_prime_torus_sylow_centralizers_are_strictly_larger
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 3 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2) :
    let q : ℕ := p ^ f
    let e : ℤ := if q % 4 = 1 then 1 else -1
    let s₀ : G := fS (s n)
    let V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    let H : Subgroup G := Subgroup.normalizer (W : Set G)
    let m : ℤ := ((q : ℤ) + e) / 2
    (N t = ⊥ →
      IsCyclic W ∧ Odd (Nat.card W) ∧ (Nat.card W : ℤ) = m ∧ 1 < m ∧
        (CFSG.pPrimeCore 2 K).map K.subtype = W ∧
        (Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 4)) ∨
          Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 5))) ∧
        ∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ → (ℓ : ℤ) ∣ m →
          (7 ≤ ℓ ∨ Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 4))) →
          ∀ P : Subgroup G, P ≤ W → Nat.card P = ℓ ^ (Nat.card W).factorization ℓ →
            let R : Subgroup G := (CFSG.pPrimeCore 2 (Subgroup.centralizer (P : Set G))).map
              (Subgroup.centralizer (P : Set G)).subtype
            P ≤ R ∧ R < W ∧ K < Subgroup.centralizer (P : Set G) ∧
              H < Subgroup.normalizer (P : Set G) ∧
              K.relIndex (Subgroup.centralizer (P : Set G)) =
                H.relIndex (Subgroup.normalizer (P : Set G)) ∧
              Odd (K.relIndex (Subgroup.centralizer (P : Set G))) ∧
              1 < K.relIndex (Subgroup.centralizer (P : Set G))) ∧
      ∀ ℓ a : ℕ, ℓ.Prime → 7 ≤ ℓ → 1 ≤ a → m = (ℓ : ℤ) ^ a → N t ≠ ⊥ := by
  intro q e s₀ V D W K H m
  have := Fintype.ofFinite G
  refine ⟨fun hN => ?_, fun ℓ a hℓ hℓ7 ha hma hN => ?_⟩
  · obtain ⟨-, hW1, hWcyc, hWodd, hWcard, -, -, -, -, -, -, hKM, ⟨PK, hPK⟩, hKH, -, -, -, -, hOK,
        -, -, ⟨hdich, -⟩, -, -, -⟩ :=
      perfect_field_factor_one_trivial_core_torus_has_two_small_normalizer_quotients n hn S fS t
        ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY
    have hWcard : (Nat.card W : ℤ) = m := hWcard
    have hOK : (CFSG.pPrimeCore 2 K).map K.subtype = W := hOK
    have hKH : K.relIndex H = 2 := hKH
    have hm1 : 1 < m := by
      rw [← hWcard]
      have h : 1 < Nat.card W := by
        rw [Nat.one_lt_iff_ne_zero_and_ne_one]
        exact ⟨Nat.card_pos.ne', fun h1 => hW1 ((Subgroup.card_eq_one).mp h1)⟩
      exact_mod_cast h
    have hA45 : (Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 4)) ∧
          Nat.card H = 24 * Nat.card W) ∨
        (Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 5)) ∧
          Nat.card H = 120 * Nat.card W) := by
      rcases hdich with ⟨h4, -, hH⟩ | ⟨h5, -, hH⟩
      · exact Or.inl ⟨h4, hH⟩
      · exact Or.inr ⟨nonempty_equiv_alternating_five_of_model h5, hH⟩
    refine ⟨hWcyc, hWodd, hWcard, hm1, hOK, hA45.imp (fun h => h.1) (fun h => h.1),
      fun ℓ hℓ hℓ5 hℓm hcase P hPW hPcard => ?_⟩
    intro R
    have hℓW : ℓ ∣ Nat.card W := by
      rw [← hWcard] at hℓm
      exact_mod_cast hℓm
    have hP1 : P ≠ ⊥ := by
      intro hP
      rw [hP, Subgroup.card_bot] at hPcard
      have hv : 1 ≤ (Nat.card W).factorization ℓ :=
        (hℓ.dvd_iff_one_le_factorization Nat.card_pos.ne').mp hℓW
      have : 1 < ℓ ^ (Nat.card W).factorization ℓ := Nat.one_lt_pow (by omega) hℓ.one_lt
      omega
    obtain ⟨-, -, -, -, -, -, hU⟩ :=
      perfect_trivial_core_every_torus_subgroup_has_inversion_normalizer_and_central_cyclic_odd_core
        n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY
    obtain ⟨⟨P₂, hP₂⟩, -, -, -, hAMset, hAJ2, -, hPR, hRW, -, -, hJeq, hAeq, -, -, -⟩ :=
      hU P hPW hP1
    have hRW' : R ≤ W := hRW
    have hRne : R ≠ W := by
      intro hRWeq
      have hCP : Subgroup.centralizer (P : Set G) = K := by
        rw [hAeq]
        change Subgroup.centralizer ((R : Subgroup G) : Set G) = _
        rw [hRWeq]
      have hNP : Subgroup.normalizer (P : Set G) = H := by
        rw [hJeq]
        change Subgroup.normalizer ((R : Subgroup G) : Set G) = _
        rw [hRWeq]
      rcases hA45 with ⟨h4, hH⟩ | ⟨h5, hH⟩
      · exact torus_sylow_centralizer_ne n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
          hmodel hN hY 4 (Or.inl rfl) h4 (by rw [hH]; rfl) ℓ hℓ hℓ5 (by omega) hℓW P hPW
          hPcard hCP hNP
      · have hℓ7 : 7 ≤ ℓ := by
          rcases hcase with h | h4'
          · exact h
          · exfalso
            obtain ⟨e4⟩ := h4'
            obtain ⟨e5⟩ := h5
            have h1 := Nat.card_congr (e4.symm.trans e5).toEquiv
            rw [CyclicAlternatingFive.nat_card_alternating, nat_card_alternatingGroup,
              Nat.card_eq_fintype_card, Fintype.card_fin] at h1
            norm_num at h1
        exact torus_sylow_centralizer_ne n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
          hmodel hN hY 5 (Or.inr rfl) h5 (by rw [hH]; rfl) ℓ hℓ hℓ5 (fun _ => hℓ7) hℓW P hPW
          hPcard hCP hNP
    have hRlt : R < W := lt_of_le_of_ne hRW' hRne
    obtain ⟨A, hA⟩ : ∃ A : Subgroup G, A = Subgroup.centralizer (P : Set G) := ⟨_, rfl⟩
    obtain ⟨J, hJ⟩ : ∃ J : Subgroup G, J = Subgroup.normalizer (P : Set G) := ⟨_, rfl⟩
    rw [← hA, ← hJ]
    have hKA : K ≤ A := hA ▸ Subgroup.centralizer_le hPW
    have hKne : K ≠ A := by
      intro hKA'
      apply hRne
      rw [← hOK, hKA', hA]
    have hKlt : K < A := lt_of_le_of_ne hKA hKne
    have hAMJ : (A : Set G) * (Subgroup.normalizer (V : Set G) : Set G) = (J : Set G) := by
      rw [hA, hJ]
      exact hAMset
    have hHJ : H ≤ J := by
      intro h hh
      have hh' : h ∈ (H : Set G) := hh
      rw [← hKM] at hh'
      obtain ⟨k, hk, x, hx, rfl⟩ := hh'
      have hmem : k * x ∈ (A : Set G) * (Subgroup.normalizer (V : Set G) : Set G) :=
        ⟨k, hKA hk, x, hx, rfl⟩
      rw [hAMJ] at hmem
      exact hmem
    have hAJ : A ≤ J := by
      rw [hA, hJ]
      exact Subgroup.centralizer_le_normalizer _
    have hAJ2' : A.relIndex J = 2 := by
      rw [hA, hJ]
      exact hAJ2
    have hidx : K.relIndex A = H.relIndex J := by
      have h1 := Subgroup.relIndex_mul_relIndex K A J hKA hAJ
      have h2 := Subgroup.relIndex_mul_relIndex K H J (Subgroup.centralizer_le_normalizer _) hHJ
      rw [hAJ2'] at h1
      rw [hKH] at h2
      omega
    have hidx1 : K.relIndex A ≠ 1 := fun h => hKne (le_antisymm hKA
      (Subgroup.relIndex_eq_one.mp h))
    have hHlt : H < J := by
      refine lt_of_le_of_ne hHJ fun hHJ' => hidx1 ?_
      rw [hidx, hHJ']
      exact Subgroup.relIndex_self _
    have hV4 : Nat.card V = 4 := (supplied_four_group_isKleinFour hn fS ht).card_four
    have hcardPK : Nat.card (PK : Subgroup K) = 4 := by
      have h := Subgroup.card_map_of_injective (f := K.subtype) (K := (PK : Subgroup K))
        K.subtype_injective
      rw [hPK] at h
      rw [← h, hV4]
    have hcardPA : Nat.card (P₂ : Subgroup (Subgroup.centralizer (P : Set G))) = 4 := by
      have h := Subgroup.card_map_of_injective (f := (Subgroup.centralizer (P : Set G)).subtype)
        (K := (P₂ : Subgroup (Subgroup.centralizer (P : Set G))))
        (Subgroup.centralizer (P : Set G)).subtype_injective
      rw [hP₂] at h
      rw [← h, hV4]
    have hKc := Subgroup.card_mul_index (PK : Subgroup K)
    have hAc := Subgroup.card_mul_index (P₂ : Subgroup (Subgroup.centralizer (P : Set G)))
    have hKoddi := Sylow.not_dvd_index PK
    have hAoddi := Sylow.not_dvd_index P₂
    have hKAc := Subgroup.card_mul_index (K.subgroupOf A)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv] at hKAc
    have hcA : Nat.card (Subgroup.centralizer (P : Set G)) = Nat.card A := by rw [hA]
    rw [hcardPK] at hKc
    rw [hcardPA] at hAc
    have hrel : K.relIndex A = (K.subgroupOf A).index := rfl
    have hprod : (P₂ : Subgroup (Subgroup.centralizer (P : Set G))).index =
        (PK : Subgroup K).index * K.relIndex A := by
      have h : 4 * (P₂ : Subgroup (Subgroup.centralizer (P : Set G))).index =
          4 * ((PK : Subgroup K).index * K.relIndex A) := by
        rw [hAc, hcA, ← hKAc, ← hKc, hrel]
        ring
      omega
    have hodd : Odd (K.relIndex A) := by
      have h : Odd ((PK : Subgroup K).index * K.relIndex A) := by
        rw [← hprod]
        exact Nat.odd_iff.mpr (by omega)
      exact (Nat.odd_mul.mp h).2
    have hpos : K.relIndex A ≠ 0 := hodd.pos.ne'
    exact ⟨hPR, hRlt, hKlt, hHlt, hidx, hodd, by omega⟩
  ·
    obtain ⟨-, -, -, -, hWcard, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hdich, -⟩, -, -,
        -⟩ :=
      perfect_field_factor_one_trivial_core_torus_has_two_small_normalizer_quotients n hn S fS t ht
        hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY
    have hWℓ : Nat.card W = ℓ ^ a := by
      have h : (Nat.card W : ℤ) = (ℓ : ℤ) ^ a := (hWcard : (Nat.card W : ℤ) = m).trans hma
      exact_mod_cast h
    have hfac : (Nat.card W).factorization ℓ = a := by
      rw [hWℓ, hℓ.factorization_pow, Finsupp.single_eq_same]
    have hℓW : ℓ ∣ Nat.card W := by
      rw [hWℓ]
      exact dvd_pow_self _ (by omega)
    have hWcard' : Nat.card W = ℓ ^ (Nat.card W).factorization ℓ := by rw [hfac, hWℓ]
    rcases hdich with ⟨h4, -, hH⟩ | ⟨h5, -, hH⟩
    · exact torus_sylow_centralizer_ne n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
        hN hY 4 (Or.inl rfl) h4 (by rw [hH]; rfl) ℓ hℓ (by omega) (by omega) hℓW W le_rfl hWcard'
        rfl rfl
    · exact torus_sylow_centralizer_ne n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
        hN hY 5 (Or.inr rfl) (nonempty_equiv_alternating_five_of_model h5) (by rw [hH]; rfl) ℓ hℓ
        (by omega) (fun _ => hℓ7) hℓW W le_rfl hWcard' rfl rfl

end CFSG.Semidihedral.Principal

module

public import CFSG.LocalAnalysis.ComponentClassification.GS82ResidueDefs
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP3Loc
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Lift
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23SocOdd
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55AltMult

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.P10

open CFSG Subgroup

theorem isPGroup_center_quot (Y : Type) [Group Y] [Finite Y] :
    IsPGroup 2 ↥(center (Y ⧸ pPrimeCore 2 Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact TBLit.center_isPGroup_two_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)

theorem oddLieType_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : Blueprint.OddLieType A) : Blueprint.OddLieType B := by
  obtain ⟨t, n, p, f, hp, hp2, hadm, hm⟩ := h
  exact ⟨t, n, p, f, hp, hp2, hadm, Blueprint.LieModel.of_mulEquiv e hm⟩

theorem typC_of_isSLTwoOver {T : Type} [Group T] [Finite T] {q₀ : ℕ}
    (hq₀ : q₀ ∈ ({5, 7, 9} : Finset ℕ)) (hSL : HarrisLit.IsSLTwoOver q₀ (T ⧸ pPrimeCore 2 T)) :
    TypC T ∧ center (T ⧸ pPrimeCore 2 T) ≠ ⊥ := by
  obtain ⟨p, k, hp, hp2, hk, hq⟩ : ∃ p k : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ k ∧ q₀ = p ^ k := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq₀
    rcases hq₀ with rfl | rfl | rfl
    · exact ⟨5, 1, by norm_num, by norm_num, le_rfl, by norm_num⟩
    · exact ⟨7, 1, by norm_num, by norm_num, le_rfl, by norm_num⟩
    · exact ⟨3, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩
  have h5 : 5 ≤ p ^ k := by
    rw [← hq]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq₀
    omega
  rw [hq] at hSL
  obtain ⟨-, hZ2, hL, -⟩ := HarrisLit.Lemma47.sl2_facts hp hp2 hk h5 hSL
  obtain ⟨eZ⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar T
  refine ⟨Or.inl (GSThmB.Soc.oddLieType_of_lieModel (Blueprint.LieModel.of_mulEquiv eZ hL) hp
    hp2), fun h => ?_⟩
  rw [h, Subgroup.card_bot] at hZ2
  exact absurd hZ2 (by norm_num)

theorem typC_of_surjective_quot {A B : Type} [Group A] [Group B]
    [Finite A] [Finite B] (hA : IsQuasisimple (A ⧸ pPrimeCore 2 A))
    (hB : IsQuasisimple (B ⧸ pPrimeCore 2 B))
    (φ : A ⧸ pPrimeCore 2 A →* B ⧸ pPrimeCore 2 B) (hφ : Function.Surjective φ)
    (hZ : center (A ⧸ pPrimeCore 2 A) ≠ ⊥) (h : TypC B) : TypC A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : φ.ker ≤ center (A ⧸ pPrimeCore 2 A) := by
    rcases LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hA φ.normal_ker with h1 | h1
    · exfalso
      obtain ⟨-, -, a, b, hab⟩ := hB
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      obtain ⟨a', rfl⟩ := hφ a
      obtain ⟨b', rfl⟩ := hφ b
      have ha : φ a' = 1 := φ.mem_ker.mp (h1 ▸ mem_top a')
      have hb : φ b' = 1 := φ.mem_ker.mp (h1 ▸ mem_top b')
      exact hab (by rw [ha, hb])
    · exact h1
  obtain ⟨eZ⟩ := FixedLoc.nonempty_fusionZStar_equiv_of_surjective_quot hB hA φ hφ
  obtain ⟨eC⟩ := LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hA φ hφ hker
  rcases h with hO | ⟨n, hn, hQ, hcard, ⟨eAlt⟩⟩ | ⟨hL, hE⟩
  · exact Or.inl (oddLieType_of_mulEquiv eZ hO)
  ·
    refine Or.inr (Or.inl ⟨n, hn, hA, ?_, ⟨eC.trans eAlt⟩⟩)
    have hdvd := GH74.GLS.Stage2.Signalizer.Ivk8.card_center_dvd_of_alt hA (by omega)
      (eC.trans eAlt)
    have h6 : Nat.card ↥(center (A ⧸ pPrimeCore 2 A)) ∣ 6 := by
      rcases Nat.lt_or_ge n 8 with h8 | h8
      · obtain rfl : n = 7 := by omega
        rwa [(Alternating.Multipliers.hopfMultiplier_alternatingGroup_seven).2] at hdvd
      · rw [Alternating.Multipliers.card_hopfMultiplier_alternatingGroup h8] at hdvd
        exact hdvd.trans (by norm_num)
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (isPGroup_center_quot A)
    have hne : Nat.card ↥(center (A ⧸ pPrimeCore 2 A)) ≠ 1 := fun h1 =>
      hZ (Subgroup.eq_bot_of_card_eq _ h1)
    rw [hj] at h6 hne ⊢
    have hj1 : j ≠ 0 := fun h0 => hne (by rw [h0, pow_zero])
    have hj2 : j < 2 := by
      by_contra hj2
      have h4 : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
      have h7 := h4.trans h6
      norm_num at h7
    obtain rfl : j = 1 := by omega
    rfl
  ·
    refine Or.inr (Or.inr ⟨Blueprint.LieModel.of_mulEquiv eC.symm hL, fun hEA => hE ?_⟩)
    have hperf : Group.IsPerfect (A ⧸ pPrimeCore 2 A) := hA.1
    have hc : (center (B ⧸ pPrimeCore 2 B)).comap φ = center (A ⧸ pPrimeCore 2 A) :=
      LocalCores.comap_center_eq_of_perfect hperf φ hφ hker
    have hmap : (center (A ⧸ pPrimeCore 2 A)).map φ = center (B ⧸ pPrimeCore 2 B) := by
      rw [← hc, Subgroup.map_comap_eq_self_of_surjective hφ]
    have h1 : IsElementaryAbelian 2 ↥((center (A ⧸ pPrimeCore 2 A)).map φ) :=
      IsElementaryAbelian.map φ
    exact IsElementaryAbelian.of_mulEquiv (MulEquiv.subgroupCongr hmap) h1

end CFSG.ComponentClassification.GS82PumpInputs.P10

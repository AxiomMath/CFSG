module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46gTools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitBlowup
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46c
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSemidihedralQ

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem pCore_cyclic_or_dihedral [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ)
    (hQ : ∀ N : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), N.Normal →
      ∀ k : ℕ, 1 ≤ k → IsEmpty (↥N ≃* QuaternionGroup (2 ^ k))) :
    IsCyclic ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∨
      ∃ k : ℕ, 1 ≤ k ∧
        Nonempty (↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≃*
          DihedralGroup (2 ^ k)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h46f := hσ.lemma46f hnonab hK hSch hFC hKC i j
  have htbo := hσ.orderOf_tBar i j
  have hPQ : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔ zpowers (hσ.tBar i j) := le_sup_left
  let eP := (subgroupOfEquivOfLe hPQ).symm
  rcases h46f.2.1 with h4 | ⟨k, hk, ⟨eQ⟩⟩ | ⟨n, hn, ⟨eQ⟩⟩
  ·
    have hdvd : Nat.card ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← h4]
      exact card_dvd_of_le hPQ
    obtain ⟨m, hm, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases m
    · left
      have : Subsingleton ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
        (Nat.card_eq_one_iff_unique.mp (by rw [hcard, pow_zero])).1
      exact isCyclic_of_subsingleton
    · left
      exact isCyclic_of_prime_card (p := 2) (by rw [hcard, pow_one])
    · by_cases hcyc : IsCyclic ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
      · exact .inl hcyc
      · right
        refine ⟨1, le_rfl, ?_⟩
        have hsq : ∀ x : ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))), x ^ 2 = 1 := by
          intro x
          have hx : orderOf x ∣ 2 ^ 2 := hcard ▸ orderOf_dvd_natCard x
          obtain ⟨a, ha, hax⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hx
          interval_cases a
          · rw [pow_zero, orderOf_eq_one_iff] at hax
            rw [hax, one_pow]
          · rw [pow_one] at hax
            have h1 := pow_orderOf_eq_one x
            rwa [hax] at h1
          · exact absurd (isCyclic_of_orderOf_eq_card x (by rw [hax, hcard])) hcyc
        have hexp :
            Monoid.exponent ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) = 2 := by
          rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq)
            with he | he
          · have : Subsingleton ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
              Monoid.exp_eq_one_iff.mp he
            have h1 := Nat.card_of_subsingleton
              (1 : ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
            rw [hcard] at h1
            exact absurd h1 (by norm_num)
          · exact he
        have : IsKleinFour ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
          ⟨by rw [hcard]; norm_num, hexp⟩
        rw [pow_one]
        exact IsKleinFour.nonempty_mulEquiv
  ·
    rcases GorensteinWalter.subgroups_dihedral_twoGroup_cyclic_or_dihedral (by omega : 1 ≤ k)
      (((pCore 2 _).subgroupOf (pCore 2 _ ⊔ zpowers (hσ.tBar i j))).map eQ.toMonoidHom) with
      hc | ⟨k', hk', ⟨eH⟩⟩
    · exact .inl ((eP.trans (equivMapOfInjective _ _ eQ.injective)).isCyclic.mpr hc)
    · exact .inr ⟨k', hk', ⟨(eP.trans (equivMapOfInjective _ _ eQ.injective)).trans eH⟩⟩
  ·
    by_cases htbP : hσ.tBar i j ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    · exfalso
      have hQP : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔ zpowers (hσ.tBar i j) =
          pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
        sup_eq_left.mpr (zpowers_le.mpr htbP)
      obtain ⟨N, hN, ⟨eN⟩⟩ := exists_normal_quaternion_of_semidihedral
        (P := pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) hn
        ((MulEquiv.subgroupCongr hQP.symm).trans eQ)
      exact (hQ N hN (n - 3) (by omega)).false eN
    · have hbot : (pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subgroupOf
          (zpowers (hσ.tBar i j)) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [mem_bot]
        rcases eq_one_or_eq_of_mem_zpowers_two htbo x.2 with h1 | h1
        · exact Subtype.ext h1
        · exact absurd (by rw [← h1]; exact hx) htbP
      have hidx : ((pCore 2 _).subgroupOf (pCore 2 _ ⊔ zpowers (hσ.tBar i j))).index = 2 := by
        change (pCore 2 _).relIndex (pCore 2 _ ⊔ zpowers (hσ.tBar i j)) = 2
        rw [relIndex_sup_left, relIndex, hbot, index_bot, Nat.card_zpowers, htbo]
      have hidx' : (((pCore 2 _).subgroupOf (pCore 2 _ ⊔ zpowers (hσ.tBar i j))).map
          eQ.toMonoidHom).index = 2 := by
        rw [MulEquiv.toMonoidHom_eq_coe, index_map_equiv]
        exact hidx
      rcases index_two_subgroup_semidihedral_cases hn hidx' with hc | hD | hQ8
      · exact .inl ((eP.trans (equivMapOfInjective _ _ eQ.injective)).isCyclic.mpr hc)
      · obtain ⟨eD⟩ := hD
        exact .inr ⟨n - 2, by omega,
          ⟨(eP.trans (equivMapOfInjective _ _ eQ.injective)).trans eD⟩⟩
      · exfalso
        obtain ⟨eQ8⟩ := hQ8
        exact (hQ _ (pCore_normal (p := 2)) (n - 3) (by omega)).false
          ((eP.trans (equivMapOfInjective _ _ eQ.injective)).trans eQ8)

theorem closure_odd_le_centralizer_pCore [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ)
    (hQ : ∀ N : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), N.Normal →
      ∀ k : ℕ, 1 ≤ k → IsEmpty (↥N ≃* QuaternionGroup (2 ^ k))) :
    closure {x : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) | Odd (orderOf x)} ≤
      centralizer (pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [closure_le]
  intro x hx
  have hP2 : IsPGroup 2 ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := pCore_isPGroup
  rcases hσ.pCore_cyclic_or_dihedral hnonab hK hSch hFC hKC i j hQ with hc | ⟨k, hk, ⟨e⟩⟩
  · exact mem_centralizer_of_odd_of_isPGroup_mulAut
      (FiveTransitive.CyclicTwoAutomorphismKernel.automorphism_two_group hP2) hx
  · rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk1 : k = 1 := by omega
      subst hk1
      have : IsKleinFour (DihedralGroup (2 ^ 1)) := by
        rw [pow_one]
        infer_instance
      have : IsKleinFour ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
        ⟨by rw [Nat.card_congr e.toEquiv]; exact IsKleinFour.card_four,
          by rw [Monoid.exponent_eq_of_mulEquiv e]; exact IsKleinFour.exponent_two⟩
      exact mem_centralizer_of_odd_of_kleinFour
        (betaBar_mem_pCore (hσ.sq_eq_one_of_mem_X (beta_mem_X i j))) (hσ.betaBar_ne_one i j)
        (betaBar_mem_center _) hx
    · exact mem_centralizer_of_odd_of_isPGroup_mulAut
        ((GorensteinWalter.dihedral_mulAut_is_twoGroup hk2).of_equiv (MulAut.congr e.symm)) hx

theorem centralizer_layer_eq_pCore [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ)
    (hQ : ∀ N : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), N.Normal →
      ∀ k : ℕ, 1 ≤ k → IsEmpty (↥N ≃* QuaternionGroup (2 ^ k))) :
    centralizer (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) =
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ pCore_le_centralizer_layer
  have hO : pPrimeCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = ⊥ :=
    pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hodd := hσ.closure_odd_le_centralizer_pCore hnonab hK hSch hFC hKC i j hQ
  have hEn : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := by
    have := LocalCores.layer_characteristic (G := MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    infer_instance
  have hCn : (centralizer (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
      Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))).Normal := normal_centralizer
  have h2 : IsPGroup 2 ↥(centralizer (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
      Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) := by
    intro y
    obtain ⟨a, u, hu, hy⟩ := Nat.exists_eq_two_pow_mul_odd
      (orderOf_pos (y : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).ne'
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    set g := (y : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ^ 2 ^ a with hg
    have hord : orderOf g = u := by
      rw [hg, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨u, hy⟩, hy,
        Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
    have hgP := hodd (subset_closure (show Odd (orderOf g) by rw [hord]; exact hu))
    have hgE : g ∈ centralizer (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := pow_mem y.2 _
    have hgPE : g ∈ centralizer ((pCore 2 _ ⊔ layer _ :
        Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :
          Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
      rw [mem_centralizer_iff]
      intro c hc
      have hle : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
          layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤ centralizer ({g} : Set _) :=
        sup_le (fun c hc => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hgP c hc))
          (fun c hc => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hgE c hc))
      exact mem_centralizer_singleton_iff.mp (hle hc)
    have hgO := centralizer_pCore_sup_layer_le hO hgPE
    obtain ⟨b, hb⟩ := pCore_isPGroup (p := 2) ⟨g, hgO⟩
    have hgb : g ^ 2 ^ b = 1 := congrArg Subtype.val hb
    have hu1 : u = 1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.pow_right b (Nat.coprime_two_right.mpr hu))
      (hord ▸ orderOf_dvd_of_pow_eq_one hgb)
    rw [← orderOf_eq_one_iff, hord, hu1]
  exact le_sSup ⟨hCn, h2⟩

theorem isLemma46g_of [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ)
    (hQ : ∀ N : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), N.Normal →
      ∀ k : ℕ, 1 ≤ k → IsEmpty (↥N ≃* QuaternionGroup (2 ^ k))) :
    IsLemma46g (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCE := hσ.centralizer_layer_eq_pCore hnonab hK hSch hFC hKC i j hQ
  have hPS : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      solvableRadical (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    refine le_antisymm (le_sSup ⟨pCore_normal, ?_⟩)
      (solvableRadical_le_centralizer_layer.trans hCE.le)
    have : Group.IsNilpotent ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
      (pCore_isPGroup (p := 2)).isNilpotent
    infer_instance
  exact ⟨hPS, hPS.symm.trans hCE.symm, hσ.pCore_cyclic_or_dihedral hnonab hK hSch hFC hKC i j hQ,
    hσ.closure_odd_le_centralizer_pCore hnonab hK hSch hFC hKC i j hQ⟩

end Standing.Setup42

theorem harris46g_of (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hQI : Harris46QuaternionInput) : Harris46gInput := by
  intro X _ _ _ hnonab hK hcat t L p f S w z V i j hs i' j'
  exact hs.setup.isLemma46g_of hnonab hK hSch hFC hKC i' j'
    (hQI X hnonab hK hcat t L p f S w z V i j hs i' j')

end CFSG.ComponentClassification.HarrisLit

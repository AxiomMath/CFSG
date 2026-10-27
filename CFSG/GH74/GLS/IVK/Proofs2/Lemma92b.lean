module

public import CFSG.GH74.GLS.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.AutAlternatingFour
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG CFSG.GorensteinWalter CFSG.GH74.GLS

theorem pPrimeCore_eq_bot_of_top {H : Type} [Group H] [Finite H]
    (h : pPrimeCoreOf 2 (⊤ : Subgroup H) = ⊥) : pPrimeCore 2 H = ⊥ := by
  have h1 : pPrimeCore 2 ↥(⊤ : Subgroup H) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (pPrimeCore 2 ↥(⊤ : Subgroup H))
      (Subgroup.subtype_injective _)).1 h
  have h2 := pPrimeCore_map_iso 2 (Subgroup.topEquiv : ↥(⊤ : Subgroup H) ≃* H)
  rw [h1, Subgroup.map_bot] at h2
  exact h2.symm

theorem sylow_le_of_odd_index {H : Type} [Group H] [Finite H] (L : Subgroup H) [L.Normal]
    (hL : Odd L.index) (S : Sylow 2 H) : (S : Subgroup H) ≤ L := by
  set I : Subgroup (H ⧸ L) := (S : Subgroup H).map (QuotientGroup.mk' L) with hI
  have h1 : Nat.card I ∣ Nat.card (S : Subgroup H) := Subgroup.card_map_dvd _ _
  have h2 : Nat.card I ∣ L.index := by
    rw [Subgroup.index]
    exact I.card_subgroup_dvd_card
  have h3 : Nat.card (S : Subgroup H) = 2 ^ (Nat.card H).factorization 2 := S.card_eq_multiplicity
  have hcop : Nat.Coprime (Nat.card (S : Subgroup H)) L.index := by
    rw [h3]
    exact (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hL))
  have h4 : Nat.card I = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h5 : I = ⊥ := Subgroup.eq_bot_of_card_eq _ h4
  intro x hx
  have : QuotientGroup.mk' L x ∈ I := Subgroup.mem_map_of_mem _ hx
  rw [h5, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff x).1 this

theorem isPGroup_of_core_bot {H : Type} [Group H] [Finite H] (hO : pPrimeCore 2 H = ⊥)
    (h : IsPGroup 2 (H ⧸ pPrimeCore 2 H)) : IsPGroup 2 H :=
  h.of_injective (QuotientGroup.mk' (pPrimeCore 2 H)) (by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hO])

theorem sylow_eq_top_of_isPGroup {H : Type} [Group H] [Finite H] (S : Sylow 2 H) (h : IsPGroup 2 H) :
    (S : Subgroup H) = ⊤ := by
  obtain ⟨n, hn⟩ := h.exists_card_eq
  have h3 : Nat.card (S : Subgroup H) = 2 ^ (Nat.card H).factorization 2 := S.card_eq_multiplicity
  rw [hn, Nat.Prime.factorization_pow Nat.prime_two] at h3
  simp at h3
  apply Subgroup.eq_top_of_card_eq
  rw [h3, hn]

theorem sylow_eq_top_of_cyclic {H : Type} [Group H] [Finite H] (hO : pPrimeCore 2 H = ⊥)
    (S : Sylow 2 H) (hcyc : IsCyclic ↥S) (h2 : 2 ∣ Nat.card H) : (S : Subgroup H) = ⊤ := by
  have hmin : (Nat.card H).minFac = 2 := (Nat.minFac_eq_two_iff _).2 h2
  have hNC : Subgroup.normalizer (S : Set H) ≤ Subgroup.centralizer (S : Set H) :=
    hcyc.normalizer_le_centralizer hmin
  have hScenter : (S : Subgroup H) ≤ centerIn (G := H) (Subgroup.normalizer (S : Subgroup H)) := by
    intro s hs
    refine ⟨Subgroup.le_normalizer hs, ?_⟩
    change s ∈ Subgroup.centralizer (Subgroup.normalizer (S : Set H) : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (Subgroup.mem_centralizer_iff.mp (hNC hg) s hs).symm
  have hcomp : HasNormalPComplement 2 H :=
    hasNormalPComplement_of_sylow_le_center_normalizer (G := H) 2 S hScenter
  have hQ : IsPGroup 2 (H ⧸ pPrimeCore 2 H) :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := 2) H hcomp
  exact sylow_eq_top_of_isPGroup S (isPGroup_of_core_bot hO hQ)

theorem card_eq_card_quot_core {H : Type} [Group H] [Finite H] (hO : pPrimeCore 2 H = ⊥) :
    Nat.card H = Nat.card (H ⧸ pPrimeCore 2 H) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 H)
  have h2 : Nat.card (pPrimeCore 2 H) = 1 := by
    rw [hO]
    exact Subgroup.card_bot
  rw [h2, mul_one] at h1
  exact h1

theorem ivk_9_2b_four
    :
    ∀ (H : Type) [Group H] [Finite H], pPrimeCoreOf 2 (⊤ : Subgroup H) = ⊥ →
      ∀ S : Sylow 2 H, Nat.card ↥S = 4 →
        (∀ a ∈ (S : Subgroup H), ∀ b ∈ (S : Subgroup H), a * b = b * a) →
          (S : Subgroup H) = ⊤ ∨ Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
            ∃ L : Subgroup H, L.Normal ∧ (S : Subgroup H) ≤ L ∧
              ∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧ 3 < Nat.card F ∧
                Nonempty (↥L ≃* PSL2 F) := by
  intro H _ _ hO S hS4 hSc
  have hS4' : Nat.card (S : Subgroup H) = 4 := hS4
  have hO' : pPrimeCore 2 H = ⊥ := pPrimeCore_eq_bot_of_top hO
  have hfac : (Nat.card H).factorization 2 = 2 := by
    have h3 : Nat.card (S : Subgroup H) = 2 ^ (Nat.card H).factorization 2 := S.card_eq_multiplicity
    rw [hS4'] at h3
    exact (Nat.pow_right_injective (le_refl 2)) (by simpa using h3.symm)
  have h2H : 2 ∣ Nat.card H := by
    have h4 : Nat.card (S : Subgroup H) ∣ Nat.card H := (S : Subgroup H).card_subgroup_dvd_card
    rw [hS4'] at h4
    exact (by norm_num : 2 ∣ 4).trans h4
  have h8 : ¬ (2 ^ 3 ∣ Nat.card H) := by
    intro h
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h
    omega
  by_cases hex : ∀ x ∈ (S : Subgroup H), x * x = 1
  ·
    have hKlein : IsKleinFour ↥S := by
      have : Nontrivial ↥S := by
        rw [← Finite.one_lt_card_iff_nontrivial]
        change 1 < Nat.card (S : Subgroup H)
        rw [hS4']
        norm_num
      refine ⟨hS4, ?_⟩
      rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
      intro g hg
      apply orderOf_eq_prime
      · have := hex g.1 g.2
        have h' : g * g = 1 := Subtype.ext this
        simpa [sq] using h'
      · exact hg
    have hD : HasDihedralSylowTwo H := by
      intro T
      refine ⟨1, le_refl 1, ?_⟩
      have e := (IsKleinFour.nonempty_mulEquiv (G₁ := ↥S) (G₂ := DihedralGroup 2)).some
      simpa using ⟨(Sylow.equiv T S).trans e⟩
    rcases (gorensteinWalter : gorensteinWalterStatement) H hD with
      ⟨hs, hq⟩ | ⟨hs, ⟨e⟩⟩ | ⟨hs, K, hKp, L, hLn, hLi, hLm⟩
    · exact Or.inl (sylow_eq_top_of_isPGroup S (isPGroup_of_core_bot hO' hq))
    · exfalso
      have hc := card_eq_card_quot_core hO'
      rw [Nat.card_congr e.toEquiv] at hc
      have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Nat.factorial]
      rw [h7] at hc
      apply h8
      rw [hc]
      norm_num
    ·
      let Φ : H ≃* (H ⧸ pPrimeCore 2 H) :=
        MulEquiv.ofBijective (QuotientGroup.mk' (pPrimeCore 2 H))
          ⟨by
            rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hO'], QuotientGroup.mk'_surjective _⟩
      let L' : Subgroup H := L.map (Φ.symm : (H ⧸ pPrimeCore 2 H) →* H)
      have hLn' : L'.Normal := hLn.map _ Φ.symm.surjective
      have hLi' : Odd L'.index := by
        have h := Subgroup.index_map_equiv (H := L) Φ.symm
        exact h ▸ hLi
      have hSL' : (S : Subgroup H) ≤ L' := sylow_le_of_odd_index L' hLi' S
      let eL' : ↥L ≃* ↥L' := L.equivMapOfInjective (Φ.symm : (H ⧸ pPrimeCore 2 H) →* H) Φ.symm.injective
      have hqodd : Odd (Nat.card K) := by
        obtain ⟨p, n, hp, hpodd, hn, hpn⟩ := hKp
        rw [hpn]
        exact hpodd.pow
      have hdvdH : Nat.card ↥L' ∣ Nat.card H := L'.card_subgroup_dvd_card
      rcases hLm with ⟨⟨eL1⟩⟩ | ⟨⟨eL1⟩⟩
      ·
        by_cases h3 : 3 < Nat.card K
        · exact Or.inr (Or.inr ⟨L', hLn', hSL', K, inferInstance, inferInstance, hqodd, h3,
            ⟨eL'.symm.trans eL1⟩⟩)
        ·
          have hK3 : Nat.card K = 3 := by
            obtain ⟨p, n, hp, hpodd, hn, hpn⟩ := hKp
            have hp3 : 3 ≤ p := by
              have h2 := hp.two_le
              rcases Nat.lt_or_ge p 3 with h | h
              · have : p = 2 := by omega
                subst this
                exact absurd hpodd (by decide)
              · exact h
            have : p ≤ p ^ n := Nat.le_self_pow (by omega) p
            omega
          have : Fintype K := Fintype.ofFinite K
          have hFcard : Fintype.card K = 3 := by simpa [Nat.card_eq_fintype_card] using hK3
          let eK : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three hFcard
          let eA : ↥L' ≃* alternatingGroup (Fin 4) :=
            ((eL'.symm.trans eL1).trans (psl2RingEquiv eK).symm).trans psl2_three_equiv_alternatingGroup
          have hPSL : IsIsoToPSL2OddExists (G := H) L' :=
            ⟨K, inferInstance, inferInstance, hKp, ⟨eL'.symm.trans eL1⟩⟩
          obtain ⟨φ, hφ⟩ := gw_lemma_3_3_vi_linear_normal_subgroup_mulAut_embedding hD hO' L' hLn'
            (Or.inl hPSL)
          have hA4 : Nat.card (alternatingGroup (Fin 4)) = 12 := by
            rw [Nat.card_eq_fintype_card, card_alternatingGroup]
            simp [Nat.factorial]
          have hL'card : Nat.card ↥L' = 12 := (Nat.card_congr eA.toEquiv).trans hA4
          let c : Equiv.Perm (Fin 4) →* MulAut (alternatingGroup (Fin 4)) :=
            MulAut.conjNormal (H := alternatingGroup (Fin 4))
          have hc : Function.Bijective c :=
            GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj
          let eAut : Equiv.Perm (Fin 4) ≃* MulAut (alternatingGroup (Fin 4)) :=
            MulEquiv.ofBijective c hc
          have hPermCard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
            rw [Nat.card_perm]
            norm_num [Nat.card_eq_fintype_card, Nat.factorial]
          have hAutAcard : Nat.card (MulAut (alternatingGroup (Fin 4))) = 24 :=
            (Nat.card_congr eAut.toEquiv).symm.trans hPermCard
          have hAut : Nat.card (MulAut ↥L') = 24 :=
            (Nat.card_congr (MulAut.congr eA).toEquiv).trans hAutAcard
          have hHle : Nat.card H ≤ 24 := (Nat.card_le_card_of_injective φ hφ).trans_eq hAut
          have hmul := Subgroup.card_mul_index L'
          rw [hL'card] at hmul
          have hidx : L'.index = 1 := by
            obtain ⟨k, hk⟩ := hLi'
            omega
          have hL'top : L' = ⊤ := Subgroup.index_eq_one.1 hidx
          exact Or.inr (Or.inl ⟨((Subgroup.topEquiv (G := H)).symm.trans
            (MulEquiv.subgroupCongr hL'top.symm)).trans eA⟩)
      ·
        exfalso
        have hq := pgl2_card_formula K
        have h8' : 8 ∣ Nat.card (PGL2 K) := by
          rw [hq]
          obtain ⟨m, hm⟩ := hqodd
          rw [hm]
          have h1 : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by
            have : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
            omega
          rw [h1]
          obtain ⟨t, ht⟩ := Nat.even_mul_succ_self m
          rw [ht]
          exact ⟨(2 * m + 1) * t, by ring⟩
        have h1 : Nat.card ↥L' = Nat.card (PGL2 K) := Nat.card_congr (eL'.symm.trans eL1).toEquiv
        apply h8
        norm_num
        rw [h1] at hdvdH
        exact h8'.trans hdvdH
  ·
    push Not at hex
    obtain ⟨x, hxS, hx⟩ := hex
    have hcyc : IsCyclic ↥S := by
      have hx' : (⟨x, hxS⟩ : ↥S) ≠ 1 := by
        intro h
        apply hx
        have : x = 1 := congrArg Subtype.val h
        rw [this, one_mul]
      have hord : orderOf (⟨x, hxS⟩ : ↥S) = 4 := by
        have h1 : orderOf (⟨x, hxS⟩ : ↥S) ∣ 4 := by
          rw [← hS4]
          exact orderOf_dvd_natCard _
        have h2 : ¬ orderOf (⟨x, hxS⟩ : ↥S) ∣ 2 := by
          intro h
          apply hx
          have : (⟨x, hxS⟩ : ↥S) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 h
          have h' := congrArg Subtype.val this
          simpa [sq] using h'
        have : orderOf (⟨x, hxS⟩ : ↥S) ∈ Nat.divisors 4 := by simpa using h1
        have hd : Nat.divisors 4 = {1, 2, 4} := by decide
        rw [hd] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h | h
        · exfalso
          exact hx' (orderOf_eq_one_iff.1 h)
        · exact absurd (by rw [h]) h2
        · exact h
      exact isCyclic_of_orderOf_eq_card _ (by rw [hord, hS4])
    exact Or.inl (sylow_eq_top_of_cyclic hO' S hcyc h2H)

end CFSG.GH74.GLS.IVK.Proofs2

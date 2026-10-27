module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Inner2
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4U4Center
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Omega
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma514G

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedLayer

theorem isPGroup_two_center_of_pPrimeCore_eq_bot {X : Type*} [Group X] [Finite X]
    (hO : pPrimeCore 2 X = ⊥) : IsPGroup 2 (center X) := by
  intro z
  obtain ⟨i, m, hm, him⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  refine ⟨i, ?_⟩
  set w := z ^ 2 ^ i with hw
  have hwo : orderOf w = m := by
    rw [hw, orderOf_pow_of_dvd (by positivity) (by rw [him]; exact dvd_mul_right _ _), him,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hwN : (zpowers ((w : center X) : X)).Normal := by
    constructor
    intro n hn g
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    have hc := Subgroup.mem_center_iff.mp (zpow_mem w.2 k) g
    rw [hc, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers _) k
  have hcop : Nat.Coprime 2 (Nat.card (zpowers ((w : center X) : X))) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hwo, Nat.coprime_two_left]
    exact hm
  have hle := le_pPrimeCore_of_normal hcop
  rw [hO] at hle
  exact Subtype.ext (mem_bot.mp (hle (mem_zpowers _)))

theorem two_mul_ordA_one {Q : ℕ} (hQ : Odd Q) : 2 * Open.ordA 1 Q = Q * (Q ^ 2 - 1) := by
  obtain ⟨t, rfl⟩ := hQ
  have hg : Nat.gcd 2 (2 * t + 1 - 1) = 2 := by
    rw [Nat.add_sub_cancel]
    exact Nat.gcd_eq_left (dvd_mul_right 2 t)
  have hdvd : 2 ∣ (2 * t + 1) * ((2 * t + 1) ^ 2 - 1) := by
    refine Dvd.dvd.mul_left ⟨2 * t ^ 2 + 2 * t, ?_⟩ _
    rw [show (2 * t + 1) ^ 2 = 4 * t ^ 2 + 4 * t + 1 by ring, Nat.add_sub_cancel]
    ring
  unfold Open.ordA
  rw [hg, show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton]
  exact Nat.mul_div_cancel' hdvd

section Hyp

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem inner_data {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hJ : Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f)) (hKa : conjugate h.K h.a = h.K)
    (hin : h.a ∈ h.K ⊔ coreActionKernel h.K) :
    ∃ ℓ : OddBar h.K, oddBarConj h.K ⟨h.a, a_mem_normalizer_K h hKa⟩ = MulAut.conj ℓ ∧
      ℓ ∉ center (OddBar h.K) ∧ ℓ ^ 2 ∈ center (OddBar h.K) ∧
      imJB h ≤ centralizer {ℓ} ∧ ⁅imJB h, imJB h⁆ = imJB h ∧
      (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ≤ 2 * Nat.card (imJB h) ∧
      (∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ∣ (p ^ f) ^ 2 + 1 ∧ s ∣ Nat.card (OddBar h.J) ∧
        s ∣ Nat.card (imJB h)) ∧
      ∀ x ∈ imJB h, (∀ w ∈ imJB h, x * w = w * x) → x * x = 1 → x = 1 := by
  obtain ⟨ℓ, hℓ⟩ := exists_oddBarConj_a_eq_conj h hKa hin
  have hconj1 : ∀ u : OddBar h.K, MulAut.conj u = 1 → u ∈ center (OddBar h.K) := by
    intro u hu
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut (OddBar h.K) => φ g) hu
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  have hℓZ : ℓ ∉ center (OddBar h.K) := by
    intro hc
    apply oddBarConj_a_ne_one h hKa
    rw [hℓ]
    ext g
    rw [MulAut.conj_apply, MulAut.one_apply, ← (Subgroup.mem_center_iff.mp hc g),
      mul_inv_cancel_right]
  have ha2 : (⟨h.a, a_mem_normalizer_K h hKa⟩ : normalizer (h.K : Set H)) ^ 2 = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← h.orderOf_a, pow_orderOf_eq_one]
    rfl
  have hℓ2 : ℓ ^ 2 ∈ center (OddBar h.K) := by
    apply hconj1
    rw [map_pow, ← hℓ, ← map_pow, ha2, map_one]
  have hJC : imJB h ≤ centralizer {ℓ} := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := oddBarConj_a_apply_of_mem_imJB h hKa hx
    rw [hℓ, MulAut.conj_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hQ : Odd (p ^ (2 * f)) := (hp.odd_of_ne_two hp2).pow
  have hpf : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
  have h2J : 2 * Nat.card (OddBar h.J) = (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) := by
    rw [card_of_lieModel_psl_two hp2 hJ, two_mul_ordA_one hQ, hpf, ← pow_mul (p ^ f) 2 2]
  have hdvd := card_oddBar_J_dvd h hKa
  have hle : Nat.card (OddBar h.J) ≤ Nat.card (imJB h) := Nat.le_of_dvd Nat.card_pos hdvd
  refine ⟨ℓ, hℓ, hℓZ, hℓ2, hJC, imJB_commutator_eq h hKa, by omega, ?_, ?_⟩
  · have h3 : 3 ≤ p ^ f := by
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hf1 : 1 ≤ f := by
        by_contra hf0
        have hf0' : f = 0 := by omega
        have := card_of_lieModel_psl_two hp2 hJ
        obtain ⟨⟨-, hf', -⟩, -⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hJ
        omega
      calc 3 ≤ p := hp3
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf1
    obtain ⟨s, hs, hs2, hsq⟩ := exists_odd_prime_dvd_sq_add_one hq h3
    suffices hsJ : s ∣ Nat.card (OddBar h.J) from ⟨s, hs, hs2, hsq, hsJ, dvd_trans hsJ hdvd⟩
    have h4 : s ∣ 2 * Nat.card (OddBar h.J) := by
      rw [h2J]
      apply Dvd.dvd.mul_left
      obtain ⟨Q, hQ1⟩ : ∃ Q, (p ^ f) ^ 2 = Q + 1 :=
        ⟨(p ^ f) ^ 2 - 1, by have : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
      have h5 : (p ^ f) ^ 4 - 1 = ((p ^ f) ^ 2 + 1) * ((p ^ f) ^ 2 - 1) := by
        rw [show (p ^ f) ^ 4 = ((p ^ f) ^ 2) ^ 2 by ring, hQ1,
          show (Q + 1) ^ 2 = (Q ^ 2 + 2 * Q) + 1 by ring, Nat.add_sub_cancel, Nat.add_sub_cancel]
        ring
      rw [h5]
      exact Dvd.dvd.mul_right hsq _
    exact (Nat.Coprime.dvd_of_dvd_mul_left
      ((Nat.coprime_primes hs Nat.prime_two).2 hs2) h4)
  · have : IsSimpleGroup (OddBar h.J) := isSimpleGroup_of_lieModel_psl_two hJ
    have hZJ : center (OddBar h.J) = ⊥ :=
      center_eq_bot_of_isSimpleGroup_of_isQuasisimple h.isQuasisimple_J
    intro x hx hc h2
    exact eq_one_of_central_sq h hKa hZJ hx hc h2

theorem inner_structure (hrow : h.Row516) (hin : h.a ∈ h.K ⊔ coreActionKernel h.K) :
    center (OddBar h.K) = ⊥ ∧ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f) ∧
      ((p ^ f % 4 = 3 ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F),
          Fintype.card F = p ^ f ∧ Nonempty (OddBar h.K ≃* StatedProj (StatedSL 4 F))) ∨
        (p ^ f % 4 = 1 ∧ ∃ (K' : Type) (_ : Field K'), UnitaryFieldData p f K' ∧
          Nonempty (OddBar h.K ≃* StatedProj (StatedSU 4 (p ^ f) K')))) := by
  classical
  obtain ⟨p, f, hp, hp2, hf, hJ, hKa, hK⟩ := hrow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect (OddBar h.K) := h.isQuasisimple_K.1
  have hZ2 : IsPGroup 2 (center (OddBar h.K)) :=
    isPGroup_two_center_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  obtain ⟨ℓ, -, hℓZ, hℓ2, hJC, hJp, hJc, ⟨s, hs, hs2, hsq, -, hsJ⟩, hnc⟩ :=
    inner_data h hp hp2 hJ hKa hin
  have := Fact.mk hs
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := imJB h) s hsJ
  set y : OddBar h.K := (y' : OddBar h.K) with hydef
  have hy : orderOf y = s := by rw [hydef, Subgroup.orderOf_coe, hy']
  have hyℓ : y * ℓ = ℓ * y := Subgroup.mem_centralizer_singleton_iff.mp (hJC y'.2)
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hiso : ∀ {M : Type} [Group M], center (OddBar h.K) = ⊥ → (ZStarBar h.K ≃* M) →
      Nonempty (OddBar h.K ≃* M) := fun hZ eM =>
    ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
      (eZ.trans eM)⟩
  rcases hK with hL | hU | ⟨e', rfl, hO8⟩
  · obtain ⟨-, F, _, _, hF, ⟨eL⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL
    let : Fintype F := Fintype.ofFinite F
    have hFq : Fintype.card F = p ^ f := by rw [Fintype.card_eq_nat_card, hF]
    have hqF : Odd (Fintype.card F) := hFq ▸ hq
    have hZ := center_eq_bot_of_inner_L4 hZ2 hqF (eZ.trans eL) hℓZ hℓ2 hJC hJp
      (by rw [hFq]; exact hJc) hs hs2 (by rw [hFq]; exact hsq) hsJ hnc
    refine ⟨hZ, p, f, hp, hp2, hf, hJ, Or.inl ⟨?_, F, inferInstance, inferInstance, hFq,
      hiso hZ eL⟩⟩
    have := card_mod_four_of_inner_L4 hZ2 hqF (eZ.trans eL) hℓZ hℓ2 hs hs2
      (by rw [hFq]; exact hsq) hy hyℓ
    rwa [hFq] at this
  · obtain ⟨-, K', _, _, hK', ⟨eU⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hU
    have hUF : UnitaryFieldData p f K' := ⟨hp, hf, by rw [hK', ← pow_mul, mul_comm]⟩
    have hZ := center_eq_bot_of_inner_U4 hUF hZ2 hp2 (eZ.trans eU) hℓZ hℓ2 hJC hJp hJc hs hs2
      hsq hsJ hnc
    refine ⟨hZ, p, f, hp, hp2, hf, hJ, Or.inr ⟨?_, K', inferInstance, hUF, hiso hZ eU⟩⟩
    exact card_mod_four_of_inner_U4 hUF hZ2 hp2 (eZ.trans eU) hℓZ hℓ2 hs hs2 hsq hy hyℓ
  · exfalso
    obtain ⟨-, K', _, _, hK', b, c, hbc, ⟨eO⟩⟩ :=
      statedClassicalModel_of_lieModel_ne_zero (by norm_num) hO8
    let : Fintype K' := Fintype.ofFinite K'
    have hKq : Fintype.card K' = p ^ e' := by rw [Fintype.card_eq_nat_card, hK']
    have h4 : (p ^ e') ^ 4 = (p ^ (2 * e')) ^ 2 := by rw [← pow_mul, ← pow_mul]; ring_nf
    set E := eZ.trans eO with hE
    apply false_of_omegaMinus_eight (K := K') (hKq ▸ (hp.odd_of_ne_two hp2).pow) hbc hs hs2
      (by rw [hKq, h4]; exact hsq) (E (QuotientGroup.mk ℓ)) (E (QuotientGroup.mk y))
    · rw [Ne, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
      exact hℓZ
    · rw [← map_pow, ← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff _).2 hℓ2, map_one]
    · rw [← map_pow, ← QuotientGroup.mk_pow, ← hy, pow_orderOf_eq_one, QuotientGroup.mk_one,
        map_one]
    · rw [Ne, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
      exact not_mem_of_isPGroup_two hZ2 hs hs2 hy
    · rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hyℓ]

end Hyp

theorem cfRow516InnerCenter : CFRow516InnerCenter :=
  fun _ _ _ h hrow hin => (inner_structure h hrow hin).1

end CFSG.ComponentClassification.CatFactsL4U4

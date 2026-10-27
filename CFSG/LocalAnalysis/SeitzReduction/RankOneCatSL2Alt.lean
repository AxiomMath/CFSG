module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2Small
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarCat

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (ProperFixedComponent IsAltType)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)
open scoped Nat

theorem eq_two_of_ordA_one_eq_factorial_div_two {f k : ℕ} (hf : 2 ≤ f)
    (hk : Open.ordA 1 (2 ^ f) = k ! / 2) : f = 2 := by
  obtain ⟨hdvd, -, hle⟩ := LinearPilot.ordA_two_pow_bounds (by norm_num : 1 ≤ 1)
    (by omega : 1 ≤ f)
  have hM : f * (1 * (1 + 1) / 2) = f := by norm_num
  rw [hM] at hdvd hle
  have hk2 : 2 ≤ k := by
    by_contra h
    have h60 := sixty_le_ordA_one hf
    interval_cases k <;> simp at hk <;> omega
  have hk! : k ! = 2 * Open.ordA 1 (2 ^ f) := by
    rw [hk, Nat.mul_div_cancel' (Nat.dvd_factorial (by norm_num) hk2)]
  have hdvd2 : 2 ^ (f + 1) ∣ k ! := by
    rw [hk!, pow_succ, mul_comm]
    exact Nat.mul_dvd_mul_left 2 hdvd
  have hlt : f + 1 < k := by
    have h1 := Nat.emultiplicity_two_factorial_lt (show k ≠ 0 by omega)
    have h2 := le_emultiplicity_of_pow_dvd hdvd2
    exact_mod_cast lt_of_le_of_lt h2 h1
  have hfac : (f + 2)! ≤ k ! := Nat.factorial_le (by omega)
  have hkle : k ! ≤ 2 ^ (3 * f + 1) := by
    rw [hk!, pow_succ]
    omega
  have hf12 : f ≤ 12 := by
    by_contra h
    have := LinearPilot.two_pow_lt_factorial_of_thirteen_le (show 13 ≤ f by omega)
    omega
  have hk16 : k < 16 := by
    by_contra h
    have h1 : (16 : ℕ)! ≤ k ! := Nat.factorial_le (by omega)
    have h2 : 2 ^ (3 * f + 1) ≤ 2 ^ 37 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ 37 < (16 : ℕ)! := by decide
    omega
  rw [RankThree.PartOne.S12K.ordA_one_eq (by omega)] at hk
  interval_cases f
  · rfl
  all_goals exfalso; revert hk; interval_cases k <;> decide

theorem eq_two_of_alternating {J : Type} [Group J] [Finite J] {m : ℕ} (hm : 5 ≤ m)
    (e : J ≃* alternatingGroup (Fin m)) {τ : MulAut J} (hτ : orderOf τ = 2)
    {D : Subgroup (fixedSubgroup τ)} (hD : IsComponent D) {n : ℕ}
    (hDm : LieModel (D ⧸ center D) .PSL 2 2 n) : n = 2 := by
  have hn : 2 ≤ n := two_le_of_lieModel_PSL_two_two hDm
  have hcardDZ := card_of_lieModel_PSL_two_two hDm
  have hσ2 : τ ^ 2 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
  have hσσ : ∀ y, τ (τ y) = y := fun y => by
    have := congrArg (fun ψ : MulAut J => ψ y) hσ2
    simpa [pow_two] using this
  set P : Subgroup J := D.map (fixedSubgroup τ).subtype with hPdef
  have hPF : P ≤ fixedSubgroup τ := map_subtype_le D
  have hPsub : P.subgroupOf (fixedSubgroup τ) = D :=
    comap_map_eq_self_of_injective (fixedSubgroup τ).subtype_injective D
  have hPne : P ≠ ⊤ := by
    intro htop
    have hσ1 : τ = 1 := by
      ext y
      exact hPF (htop ▸ mem_top y)
    rw [hσ1, orderOf_one] at hτ
    exact absurd hτ (by norm_num)
  have hPC : ProperFixedComponent τ P :=
    ⟨hσσ, hPF, hPsub ▸ LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD, hPne⟩
  have hcardP : Nat.card P = Nat.card D :=
    card_map_of_injective (fixedSubgroup τ).subtype_injective
  have hdvdS : Nat.card (D ⧸ center D) ∣ Nat.card J :=
    (card_quotient_dvd_card (center D)).trans (hcardP ▸ card_subgroup_dvd_card P)
  have hSn : Nat.card J = m ! / 2 := by
    have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  by_cases hm6 : m = 6
  · subst hm6
    rw [hSn, hcardDZ, show (6 : ℕ)! / 2 = 360 by decide,
      RankThree.PartOne.S12K.ordA_one_eq (by omega)] at hdvdS
    have h2 : 2 ^ n ∣ 360 := (Dvd.intro _ rfl).trans hdvdS
    have hn3 : n ≤ 3 := by
      by_contra h
      have h16 : 2 ^ 4 ∣ 2 ^ n := Nat.pow_dvd_pow 2 (by omega)
      have := h16.trans h2
      revert this
      decide
    interval_cases n
    · rfl
    · revert hdvdS
      decide
  · set L := P.subgroupOf (fixedSubgroup τ) with hLdef
    let eLD : L ≃* D := MulEquiv.subgroupCongr hPsub
    have hqL : IsQuasisimple L :=
      (LocalAnalysis.ComponentInitial.isQuasisimple_congr eLD).2 hD.1
    obtain ⟨-, ⟨eZ⟩⟩ := hPC.fusionZStar_equiv_of_quasisimple hqL
    let eP : P ⧸ Open.fusionZStar P ≃* D ⧸ center D :=
      eZ.trans (QuotientGroup.congr (center L) (center D) eLD (Subgroup.map_center_eq eLD))
    obtain ⟨hPC', ⟨eT⟩⟩ := hPC.map e
    have hAlt :=
      CFSG.ComponentClassification.CatLeaf.isAltType_of_properFixedComponent_alternating hm hm6
        hPC'
    have hAltD : IsAltType (D ⧸ center D) := IsAltType.of_mulEquiv (eP.symm.trans eT) hAlt
    obtain ⟨Ω, _, _, hΩ, ⟨eA⟩⟩ := hAltD
    have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hcardΩ : Open.ordA 1 (2 ^ n) = (Fintype.card Ω)! / 2 := by
      rw [← hcardDZ, Nat.card_congr eA.toEquiv, nat_card_alternatingGroup,
        Nat.card_eq_fintype_card]
    exact eq_two_of_ordA_one_eq_factorial_div_two hn hcardΩ

theorem card_le_of_isPGroup_mulAut_alternating {J : Type} [Group J] [Finite J]
    (hs : IsSimpleGroup J) (hna : ∃ a b : J, a * b ≠ b * a) {m : ℕ} (hm : 5 ≤ m) (hm11 : m ≤ 11)
    (e : J ≃* alternatingGroup (Fin m)) {P : Subgroup (MulAut J)} (hP : IsPGroup 2 P) :
    Nat.card P ≤ 2 ^ 8 := by
  have hZ : center J = ⊥ := center_eq_bot_of_simple_nonabelian hs hna
  have hcard := card_mulAut_of_center_eq_bot hZ
  have : Finite (MulAut J) :=
    Finite.of_injective (fun β : MulAut J => (β : J → J)) DFunLike.coe_injective
  have hJ : Nat.card J = m ! / 2 := by
    have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  by_cases hm6 : m = 6
  · subst hm6
    have hO := CatalogueSchreierAlternating.DegreeSix.outer_card_le_four_of_equiv e
    have hOpos : 0 < Nat.card (Outer J) := Nat.card_pos
    have h1 := card_le_of_isPGroup_of_card_dvd hP (N := 8 * Nat.card (Outer J)) (u := 45)
      (by decide) (by omega) (by
        rw [hcard, hJ, show (6 : ℕ)! / 2 = 360 by decide]
        exact dvd_of_eq (by ring))
    omega
  · have hO := CatalogueSchreierAlternating.outer_card_dvd_two_of_equiv_outside_six
      (by omega) e
    refine card_le_of_isPGroup_of_card_dvd hP (u := 155925) (by decide) (by norm_num) ?_
    rw [hcard, hJ]
    calc m ! / 2 * Nat.card (Outer J) ∣ m ! / 2 * 2 := mul_dvd_mul_left _ hO
      _ = m ! := Nat.div_mul_cancel (Nat.dvd_factorial (by norm_num) (by omega))
      _ ∣ 11 ! := Nat.factorial_dvd_factorial hm11
      _ = 2 ^ 8 * 155925 := by decide

theorem two_pow_eight_dvd_factorial_mul {m k : ℕ} (hm : 12 ≤ m) (hk : 1 ≤ k)
    (hkm : 2 * k ≤ m) : 2 ^ 8 ∣ (m - 2 * k)! * 2 ^ k * k ! := by
  rcases Nat.lt_or_ge k 8 with hk8 | hk8
  · have hfac : (12 - 2 * k)! ∣ (m - 2 * k)! := Nat.factorial_dvd_factorial (by omega)
    have hsmall : 2 ^ 8 ∣ (12 - 2 * k)! * 2 ^ k * k ! := by
      interval_cases k <;> decide
    exact hsmall.trans (mul_dvd_mul (mul_dvd_mul hfac dvd_rfl) dvd_rfl)
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow 2 hk8) _) _

theorem two_pow_seven_dvd_card_centralizer_alternating {m : ℕ} (hm : 12 ≤ m)
    {g : Equiv.Perm (Fin m)} (hg : orderOf g = 2) :
    2 ^ 7 ∣ Nat.card ((centralizer ({g} : Set (Equiv.Perm (Fin m)))).subgroupOf
      (alternatingGroup (Fin m))) := by
  classical
  set C := centralizer ({g} : Set (Equiv.Perm (Fin m))) with hCdef
  set A := alternatingGroup (Fin m) with hAdef
  obtain ⟨j, hj⟩ := Equiv.Perm.cycleType_prime_order (σ := g) (by rw [hg]; exact Nat.prime_two)
  rw [hg] at hj
  have hle := Equiv.Perm.sum_cycleType_le g
  rw [hj, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hle
  have hC : Nat.card C = (m - (j + 1) * 2)! * 2 ^ (j + 1) * (j + 1)! := by
    rw [hCdef, Equiv.Perm.nat_card_centralizer, hj, Multiset.sum_replicate, smul_eq_mul,
      Multiset.prod_replicate, Multiset.toFinset_replicate,
      ite_eq_right (show ¬ (j + 1 = 0) by omega), Finset.prod_singleton,
      Multiset.count_replicate_self, Fintype.card_fin]
  have h8 : 2 ^ 8 ∣ Nat.card C := by
    rw [hC, show (j + 1) * 2 = 2 * (j + 1) by ring]
    exact two_pow_eight_dvd_factorial_mul hm (by omega) (by omega)
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hidx : (A.subgroupOf C).index ∣ 2 := by
    have h := Subgroup.relIndex_dvd_index_of_normal A C
    rwa [alternatingGroup.index_eq_two] at h
  have hmul := (A.subgroupOf C).card_mul_index
  have h7 : 2 ^ 7 ∣ Nat.card (A.subgroupOf C) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h1 | h2
    · rw [h1, mul_one] at hmul
      rw [hmul]
      exact (pow_dvd_pow 2 (by norm_num)).trans h8
    · rw [h2] at hmul
      rw [← hmul, show 2 ^ 8 = 2 ^ 7 * 2 by norm_num] at h8
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h8
  have e1 : Nat.card (C.subgroupOf A) = Nat.card (C ⊓ A : Subgroup (Equiv.Perm (Fin m))) := by
    rw [← Subgroup.inf_subgroupOf_right C A]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have e2 : Nat.card (A.subgroupOf C) = Nat.card (A ⊓ C : Subgroup (Equiv.Perm (Fin m))) := by
    rw [← Subgroup.inf_subgroupOf_right A C]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [e1, inf_comm, ← e2]
  exact h7

theorem false_of_alternating_twelve_le {J : Type} [Group J] [Finite J] {m : ℕ} (hm : 12 ≤ m)
    (e : J ≃* alternatingGroup (Fin m)) {τ : MulAut J} (hτ : orderOf τ = 2)
    {D : Subgroup (fixedSubgroup τ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL 2 2 2) (h2 : FixedCentralizerTwoSmall τ D) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m (by omega)
    (by omega)
  obtain ⟨g, hg⟩ := hbij.2 (MulAut.congr e τ)
  have hgo : orderOf g = 2 := by
    rw [← orderOf_injective _ hbij.1 g, hg]
    exact (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective τ).trans hτ
  have hF : (centralizer ({g} : Set (Equiv.Perm (Fin m)))).subgroupOf (alternatingGroup (Fin m)) ≤
      fixedSubgroup (MulAut.conjNormal (H := alternatingGroup (Fin m)) g) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hx
    change MulAut.conjNormal g x = x
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, ← hx, mul_inv_cancel_right]
  let Ψ : fixedSubgroup τ ≃* fixedSubgroup (MulAut.conjNormal (H := alternatingGroup (Fin m)) g) :=
    (CatLeafProof.fixedSubgroupCongrEquiv e τ).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hg.symm))
  have h7 : 2 ^ 7 ∣ Nat.card (fixedSubgroup τ) := by
    rw [Nat.card_congr Ψ.toEquiv]
    exact (two_pow_seven_dvd_card_centralizer_alternating hm hgo).trans
      (Subgroup.card_dvd_of_le hF)
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime 2 h7
  have hbound := card_le_of_isPGroup_fixedSubgroup hD hDm h2 (IsPGroup.of_card hQ)
  rw [hQ, padicValNat.self (by norm_num : 1 < 2)] at hbound
  norm_num at hbound

theorem catSL2AlternatingBound (n : ℕ) : CatSL2AlternatingBound n := by
  rintro J _ _ hJ hna ⟨m, hm, ⟨e⟩⟩ τ ⟨hτ, D, hD, hDm, h2⟩ P hP
  obtain rfl : n = 2 := eq_two_of_alternating hm e hτ hD hDm
  rcases Nat.lt_or_ge m 12 with hm12 | hm12
  · have h := card_le_of_isPGroup_mulAut_alternating hJ hna hm (by omega) e hP
    have h' : (2 : ℕ) ^ 8 < 2 * (2 ^ 2) ^ 4 := by norm_num
    omega
  · exact (false_of_alternating_twelve_le hm12 e hτ hD hDm h2).elim

end CFSG.SeitzReduction.RankOne

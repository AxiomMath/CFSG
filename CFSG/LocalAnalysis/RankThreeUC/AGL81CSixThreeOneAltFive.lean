module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Invariant
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Faithful
import CFSG.RankThree.PartOne.K1214.OmegaAlg
import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2Perf

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

private theorem smul_eq_self_of_natCard_lt {p : ℕ} [hp : Fact p.Prime] {A G : Type*}
    [Group A] [Finite A] [Group G] [Finite G] [MulDistribMulAction A G]
    (hA : Nat.card A = p) (hG : Nat.card G < p) : CFSG.ActsTrivially A G := by
  have hAp : IsPGroup p A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hmod := hAp.card_modEq_card_fixedPoints G
  change Nat.card G ≡ Nat.card (CFSG.fixedPointSubgroup A G) [MOD p] at hmod
  have hle : Nat.card (CFSG.fixedPointSubgroup A G) ≤ Nat.card G :=
    Subgroup.card_le_card_group (H := CFSG.fixedPointSubgroup A G)
  have hlt : Nat.card (CFSG.fixedPointSubgroup A G) < p := lt_of_le_of_lt hle hG
  have heq : Nat.card (CFSG.fixedPointSubgroup A G) = Nat.card G :=
    (Nat.ModEq.eq_of_lt_of_lt hmod hG hlt).symm
  have htop : CFSG.fixedPointSubgroup A G = ⊤ := Subgroup.eq_top_of_card_eq _ heq
  intro a g
  have hg : g ∈ CFSG.fixedPointSubgroup A G := by rw [htop]; exact Subgroup.mem_top g
  exact hg a

private theorem natCard_sylow_lt_five_of_dvd_twelve {F : Type*} [Group F] [Finite F]
    (hF : Nat.card F ∣ 12) (q : ℕ) [hq : Fact q.Prime] (S : Sylow q F) :
    Nat.card (S : Subgroup F) < 5 := by
  have hqprime : q.Prime := hq.out
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hSdvd : Nat.card (S : Subgroup F) ∣ 12 :=
    (Subgroup.card_subgroup_dvd_card (S : Subgroup F)).trans hF
  rcases k with _ | k
  · rw [hk]; norm_num
  · have hq12 : q ∣ 12 :=
      (dvd_pow_self q (Nat.succ_ne_zero k)).trans (hk ▸ hSdvd)
    have hq_le : q ≤ 12 := Nat.le_of_dvd (by norm_num) hq12
    have hq23 : q = 2 ∨ q = 3 := by
      have hmem : q ∈ Nat.divisors 12 := Nat.mem_divisors.mpr ⟨hq12, by norm_num⟩
      have hd : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
      rw [hd] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h | h | h | h
      · exfalso; rw [h] at hqprime; norm_num at hqprime
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; rw [h] at hqprime; norm_num at hqprime
      · exfalso; rw [h] at hqprime; norm_num at hqprime
      · exfalso; rw [h] at hqprime; norm_num at hqprime
    rw [hk]
    rcases hq23 with rfl | rfl
    · have hk2 : k + 1 ≤ 2 := by
        by_contra h
        have h3 : 3 ≤ k + 1 := by omega
        have h8 : 2 ^ 3 ∣ 2 ^ (k + 1) := pow_dvd_pow 2 h3
        have : 2 ^ 3 ∣ 12 := h8.trans (hk ▸ hSdvd)
        norm_num at this
      calc 2 ^ (k + 1) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
        _ = 4 := by norm_num
        _ < 5 := by norm_num
    · have hk1 : k + 1 ≤ 1 := by
        by_contra h
        have h2 : 2 ≤ k + 1 := by omega
        have h9 : 3 ^ 2 ∣ 3 ^ (k + 1) := pow_dvd_pow 3 h2
        have : 3 ^ 2 ∣ 12 := h9.trans (hk ▸ hSdvd)
        norm_num at this
      calc 3 ^ (k + 1) ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 3 := by norm_num
        _ < 5 := by norm_num

private theorem fixedPointSubgroup_fitting_eq_top_of_natCard_eq_five_of_dvd_twelve
    {A N : Type} [Group A] [Finite A] [Group N] [Finite N] [MulDistribMulAction A N]
    (hA : Nat.card A = 5) (hN : Nat.card N ∣ 12) :
    CFSG.fixedPointSubgroup A ↥(CFSG.fittingSubgroup N) = ⊤ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hSylow_fixed : ∀ q ∈ (Nat.card ↥(CFSG.fittingSubgroup N)).primeFactors,
      ((default : Sylow q ↥(CFSG.fittingSubgroup N)) :
        Subgroup ↥(CFSG.fittingSubgroup N)) ≤
        CFSG.fixedPointSubgroup A ↥(CFSG.fittingSubgroup N) := by
    intro q hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    letI : Fact q.Prime := ⟨hqprime⟩
    let S : Sylow q ↥(CFSG.fittingSubgroup N) := default
    have hSchar : (S : Subgroup ↥(CFSG.fittingSubgroup N)).Characteristic :=
      Sylow.characteristic_of_normal S
        (Group.IsNilpotent.sylow_normal (CFSG.fittingSubgroup_nilpotent (G := N)) q S)
    letI : CFSG.IsInvariant A ↥(CFSG.fittingSubgroup N)
        (S : Subgroup ↥(CFSG.fittingSubgroup N)) :=
      CFSG.isInvariant_of_characteristic (S : Subgroup ↥(CFSG.fittingSubgroup N))
    letI : MulDistribMulAction A ↥(S : Subgroup ↥(CFSG.fittingSubgroup N)) :=
      CFSG.instMulDistribMulAction_subtype
    have hSdvd : Nat.card ↥(CFSG.fittingSubgroup N) ∣ 12 :=
      (Subgroup.card_subgroup_dvd_card (CFSG.fittingSubgroup N)).trans hN
    have hSlt : Nat.card ↥(S : Subgroup ↥(CFSG.fittingSubgroup N)) < 5 :=
      natCard_sylow_lt_five_of_dvd_twelve hSdvd q S
    have htriv : CFSG.ActsTrivially A ↥(S : Subgroup ↥(CFSG.fittingSubgroup N)) :=
      smul_eq_self_of_natCard_lt hA hSlt
    intro s hs a
    have hs' : a • (⟨s, hs⟩ : ↥(S : Subgroup ↥(CFSG.fittingSubgroup N))) = ⟨s, hs⟩ :=
      htriv a ⟨s, hs⟩
    exact congrArg Subtype.val hs'
  apply top_unique
  rw [← Sylow.iSup_sylow_eq_top (G := ↥(CFSG.fittingSubgroup N))]
  exact iSup₂_le hSylow_fixed

private theorem not_faithful_of_natCard_eq_five_of_dvd_twelve
    {A N : Type} [Group A] [Finite A] [Group N] [Finite N] [MulDistribMulAction A N]
    (hA : Nat.card A = 5) (hN : Nat.card N ∣ 12) : ¬ FaithfulSMul A N := by
  intro hfaith
  haveI : FaithfulSMul A N := hfaith
  have hN60 : Nat.card N ∣ 60 := hN.trans (by norm_num)
  have hNlt : Nat.card N < 60 := by
    have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 12) hN
    omega
  have hsolv : Group.IsSolvable N :=
    CFSG.Quasithin.A312J2.isSolvable_of_card_dvd_sixty hN60 hNlt
  have hcop : Nat.Coprime (Nat.card A) (Nat.card N) := by
    rw [hA]
    refine (Nat.prime_five.coprime_iff_not_dvd).mpr ?_
    intro h5
    have h512 : 5 ∣ 12 := h5.trans hN
    norm_num at h512
  have hfaithF : FaithfulSMul A ↥(CFSG.fittingSubgroup N) :=
    CFSG.faithful_on_fitting_of_coprime hsolv hcop
  have hfixed := fixedPointSubgroup_fitting_eq_top_of_natCard_eq_five_of_dvd_twelve hA hN
  have hsub : Subsingleton A := by
    refine ⟨fun a b => ?_⟩
    have key : ∀ a : A, a = 1 := by
      intro a
      apply (faithfulSMul_iff (G := A) (α := ↥(CFSG.fittingSubgroup N))).mp hfaithF a
      intro f
      have hf : f ∈ CFSG.fixedPointSubgroup A ↥(CFSG.fittingSubgroup N) := by
        rw [hfixed]; exact Subgroup.mem_top f
      exact hf a
    rw [key a, key b]
  have hA1 : Nat.card A = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
  omega

private theorem actsTrivially_of_not_faithful_of_natCard_eq_five
    {A N : Type} [Group A] [Finite A] [Group N] [MulDistribMulAction A N]
    (hA : Nat.card A = 5) (hfaith : ¬ FaithfulSMul A N) : CFSG.ActsTrivially A N := by
  have hKne : (MulDistribMulAction.toMulAut A N).ker ≠ ⊥ := by
    intro hbot
    apply hfaith
    refine (faithfulSMul_iff (G := A) (α := N)).mpr ?_
    intro a ha
    have hamem : a ∈ (MulDistribMulAction.toMulAut A N).ker := by
      rw [MonoidHom.mem_ker]
      ext n
      exact ha n
    rw [hbot] at hamem
    simpa using hamem
  have hK : (MulDistribMulAction.toMulAut A N).ker = ⊤ := by
    have hdvd : Nat.card ↥((MulDistribMulAction.toMulAut A N).ker) ∣ 5 := by
      rw [← hA]
      exact Subgroup.card_subgroup_dvd_card _
    have hlt : 1 < Nat.card ↥((MulDistribMulAction.toMulAut A N).ker) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hKne
    have hcard : Nat.card ↥((MulDistribMulAction.toMulAut A N).ker) = 5 := by
      rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
      · omega
      · exact h
    exact Subgroup.eq_top_of_card_eq _ (hcard.trans hA.symm)
  intro a n
  have hamem : a ∈ (MulDistribMulAction.toMulAut A N).ker := by
    rw [hK]; exact Subgroup.mem_top a
  have ha1 : MulDistribMulAction.toMulAut A N a = 1 := by
    simpa [MonoidHom.mem_ker] using hamem
  calc a • n = (MulDistribMulAction.toMulAut A N a) n := rfl
    _ = (1 : MulAut N) n := by rw [ha1]
    _ = n := rfl

private theorem actsTrivially_of_natCard_eq_five_of_dvd_twelve
    {A N : Type} [Group A] [Finite A] [Group N] [Finite N] [MulDistribMulAction A N]
    (hA : Nat.card A = 5) (hN : Nat.card N ∣ 12) : CFSG.ActsTrivially A N := by
  by_cases hfaith : FaithfulSMul A N
  · exact absurd hfaith (not_faithful_of_natCard_eq_five_of_dvd_twelve hA hN)
  · exact actsTrivially_of_not_faithful_of_natCard_eq_five hA hfaith

private theorem isPGroup_abelianization_of_closure_orderOf_five_eq_top {H : Type} [Group H]
    [Finite H]
    (hgen : Subgroup.closure {h : H | orderOf h = 5} = ⊤) :
    IsPGroup 5 (Abelianization H) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hSgen : Subgroup.closure ((Abelianization.of : H →* Abelianization H) ''
      {h : H | orderOf h = 5}) = ⊤ := by
    rw [← MonoidHom.map_closure]
    rw [hgen]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective (commutator H))
  have hcomm : ∀ x ∈ ((Abelianization.of : H →* Abelianization H) ''
      {h : H | orderOf h = 5}),
      ∀ y ∈ ((Abelianization.of : H →* Abelianization H) '' {h : H | orderOf h = 5}),
      x * y = y * x := by
    intro x _ y _
    exact mul_comm x y
  have hpow : ∀ x ∈ ((Abelianization.of : H →* Abelianization H) ''
      {h : H | orderOf h = 5}), x ^ 5 = 1 := by
    rintro x ⟨h, hh, rfl⟩
    rw [← map_pow]
    have hh5 : h ^ 5 = 1 := (orderOf_dvd_iff_pow_eq_one).mp (hh ▸ dvd_rfl)
    rw [hh5, map_one]
  haveI hEA : CFSG.IsElementaryAbelian 5
      ↥(Subgroup.closure ((Abelianization.of : H →* Abelianization H) ''
        {h : H | orderOf h = 5})) :=
    CFSG.RankThree.PartOne.K1214.isElementaryAbelian_closure hcomm hpow
  have hQ5 : ∀ x : Abelianization H, x ^ 5 = 1 := by
    intro x
    have hx : (⟨x, by rw [hSgen]; exact Subgroup.mem_top x⟩ :
        ↥(Subgroup.closure ((Abelianization.of : H →* Abelianization H) ''
          {h : H | orderOf h = 5}))) ^ 5 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (CFSG.IsElementaryAbelian.exponent_dvd_p 5 _) _
    simpa using congrArg Subtype.val hx
  refine IsPGroup.iff_orderOf.mpr fun x => ?_
  have hdvd : orderOf x ∣ 5 := orderOf_dvd_iff_pow_eq_one.mpr (hQ5 x)
  rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

private theorem card_abelianization_eq_one_or_five {H : Type} [Group H] [Finite H]
    (hH : Nat.card H ∣ 60)
    (hgen : Subgroup.closure {h : H | orderOf h = 5} = ⊤) :
    Nat.card (Abelianization H) = 1 ∨ Nat.card (Abelianization H) = 5 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hQp := isPGroup_abelianization_of_closure_orderOf_five_eq_top hgen
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
  have hQdvd : Nat.card (Abelianization H) ∣ 60 := by
    have hdvdH : Nat.card (Abelianization H) ∣ Nat.card H :=
      ⟨Nat.card (commutator H),
        Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator H)⟩
    exact hdvdH.trans hH
  have hk_le : k ≤ 1 := by
    have hpowdvd : 5 ^ k ∣ 60 := by rw [← hk]; exact hQdvd
    by_contra h
    have h2 : 2 ≤ k := by omega
    have h25 : 5 ^ 2 ∣ 5 ^ k := pow_dvd_pow 5 h2
    have : 5 ^ 2 ∣ 60 := h25.trans hpowdvd
    norm_num at this
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact Or.inl (by simpa using hk)
  · exact Or.inr (by simpa using hk)

private theorem card_abelianization_eq_five_of_not_perfect {H : Type} [Group H] [Finite H]
    (hH : Nat.card H ∣ 60)
    (hgen : Subgroup.closure {h : H | orderOf h = 5} = ⊤)
    (hperf : ¬ Group.IsPerfect H) : Nat.card (Abelianization H) = 5 := by
  rcases card_abelianization_eq_one_or_five hH hgen with h | h
  · exfalso
    apply hperf
    refine Group.IsPerfect.mk ?_
    rw [eq_top_iff]
    intro x _
    have hx1 : (Abelianization.of : H →* Abelianization H) x = 1 := by
      have hsub : Subsingleton (Abelianization H) := (Nat.card_eq_one_iff_unique.mp h).1
      exact Subsingleton.elim _ _
    have hxker : x ∈ (Abelianization.of : H →* Abelianization H).ker := by
      rw [MonoidHom.mem_ker]; exact hx1
    rwa [Abelianization.ker_of] at hxker
  · exact h

private theorem card_eq_five_mul_card_commutator {H : Type} [Group H] [Finite H]
    (hQ : Nat.card (Abelianization H) = 5) :
    Nat.card H = 5 * Nat.card (commutator H) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator H)
  have h' : Nat.card (H ⧸ commutator H) = 5 := hQ
  rw [h, h']

private theorem card_commutator_dvd_twelve {H : Type} [Group H] [Finite H]
    (hH : Nat.card H ∣ 60) (hQ : Nat.card (Abelianization H) = 5) :
    Nat.card (commutator H) ∣ 12 := by
  obtain ⟨c, hc⟩ := hH
  refine ⟨c, ?_⟩
  have hDH := card_eq_five_mul_card_commutator hQ
  rw [hDH] at hc
  have h5 : 5 * (Nat.card (commutator H) * c) = 5 * 12 := by
    calc 5 * (Nat.card (commutator H) * c) = 5 * Nat.card (commutator H) * c := by ring
      _ = 60 := hc.symm
      _ = 5 * 12 := by norm_num
  exact (Nat.mul_left_cancel (by norm_num : 0 < 5) h5).symm

private theorem natCard_sylow_eq_five_of_card_eq_five_mul {H : Type} [Group H] [Finite H]
    (P : Sylow 5 H) {m : ℕ} (hH : Nat.card H = 5 * m) (hm : m ∣ 12) :
    Nat.card (P : Subgroup H) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmne : m ≠ 0 := by
    obtain ⟨c, hc⟩ := hm
    intro h0
    rw [h0, zero_mul] at hc
    omega
  have h5m : ¬ 5 ∣ m := by
    intro h
    have : 5 ∣ 12 := h.trans hm
    norm_num at this
  have hndvdH25 : ¬ 5 ^ 2 ∣ Nat.card H := by
    intro h
    obtain ⟨c, hc⟩ := h
    rw [hH] at hc
    have hm5 : 5 ∣ m := by
      refine ⟨c, ?_⟩
      apply Nat.mul_left_cancel (n := 5) (by norm_num : 0 < 5)
      calc 5 * m = 5 ^ 2 * c := hc
        _ = 5 * (5 * c) := by ring
    exact h5m hm5
  have hfac : (Nat.card H).factorization 5 = 1 := by
    have hmul : (5 * m).factorization 5 = 1 := by
      rw [Nat.factorization_mul (by norm_num : (5 : ℕ) ≠ 0) hmne]
      simp [Nat.Prime.factorization_self Nat.prime_five,
        Nat.factorization_eq_zero_of_not_dvd h5m]
    rwa [← hH] at hmul
  rw [P.card_eq_multiplicity, hfac, pow_one]

private theorem inf_commutator_sylow_eq_bot {H : Type} [Group H] [Finite H]
    (P : Sylow 5 H) (hP : Nat.card (P : Subgroup H) = 5)
    (hD : Nat.card (commutator H) ∣ 12) :
    commutator H ⊓ (P : Subgroup H) = ⊥ := by
  rw [← Subgroup.card_eq_one]
  have hdvdD : Nat.card ↥(commutator H ⊓ (P : Subgroup H)) ∣ Nat.card (commutator H) :=
    Subgroup.card_dvd_of_le inf_le_left
  have hdvdP : Nat.card ↥(commutator H ⊓ (P : Subgroup H)) ∣ Nat.card (P : Subgroup H) :=
    Subgroup.card_dvd_of_le inf_le_right
  rw [hP] at hdvdP
  have h5D : ¬ 5 ∣ Nat.card (commutator H) := by
    intro h
    have : 5 ∣ 12 := h.trans hD
    norm_num at this
  rcases (Nat.dvd_prime Nat.prime_five).mp hdvdP with h | h
  · exact h
  · exact absurd (h ▸ hdvdD) h5D

private theorem image_sylow_abelianization_eq_top {H : Type} [Group H] [Finite H]
    (P : Sylow 5 H) (hP : Nat.card (P : Subgroup H) = 5)
    (hQ : Nat.card (Abelianization H) = 5)
    (hbot : commutator H ⊓ (P : Subgroup H) = ⊥) :
    (P : Subgroup H).map (Abelianization.of : H →* Abelianization H) = ⊤ := by
  have hne : (P : Subgroup H).map (Abelianization.of : H →* Abelianization H) ≠ ⊥ := by
    intro hmapbot
    have hPle : (P : Subgroup H) ≤ commutator H := by
      intro x hx
      have hxmap : (Abelianization.of : H →* Abelianization H) x ∈
          (P : Subgroup H).map (Abelianization.of : H →* Abelianization H) :=
        Subgroup.mem_map_of_mem _ hx
      rw [hmapbot] at hxmap
      rw [Subgroup.mem_bot] at hxmap
      have : x ∈ (Abelianization.of : H →* Abelianization H).ker := by
        rw [MonoidHom.mem_ker]; exact hxmap
      rwa [Abelianization.ker_of] at this
    have h1 : (P : Subgroup H) ≤ commutator H ⊓ (P : Subgroup H) := le_inf hPle le_rfl
    have h3 : (P : Subgroup H) = ⊥ := le_bot_iff.mp (hbot ▸ h1)
    have : Nat.card (P : Subgroup H) = 1 := by rw [h3]; simp
    omega
  have hdvdmap : Nat.card ↥((P : Subgroup H).map
      (Abelianization.of : H →* Abelianization H)) ∣ Nat.card (Abelianization H) :=
    Subgroup.card_subgroup_dvd_card _
  have hgt1 : 1 < Nat.card ↥((P : Subgroup H).map
      (Abelianization.of : H →* Abelianization H)) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  rw [hQ] at hdvdmap
  have hmap5 : Nat.card ↥((P : Subgroup H).map
      (Abelianization.of : H →* Abelianization H)) = 5 := by
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvdmap with h | h
    · omega
    · exact h
  exact Subgroup.eq_top_of_card_eq _ (by rw [hmap5, hQ])

private theorem sup_commutator_sylow_eq_top {H : Type} [Group H] [Finite H]
    (P : Sylow 5 H) (hPmap : (P : Subgroup H).map
      (Abelianization.of : H →* Abelianization H) = ⊤) :
    commutator H ⊔ (P : Subgroup H) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : (Abelianization.of : H →* Abelianization H) x ∈
      (P : Subgroup H).map (Abelianization.of : H →* Abelianization H) := by
    rw [hPmap]; exact Subgroup.mem_top _
  obtain ⟨y, hyP, hyx⟩ := Subgroup.mem_map.mp hx
  have hzD : y⁻¹ * x ∈ commutator H := by
    rw [← Abelianization.ker_of]
    rw [MonoidHom.mem_ker]
    rw [map_mul, map_inv, ← hyx, inv_mul_cancel]
  have hd' : y * (y⁻¹ * x) * y⁻¹ ∈ commutator H := by
    have := Subgroup.Normal.conj_mem (inferInstance : (commutator H).Normal)
      (y⁻¹ * x) hzD y
    simpa using this
  exact (Subgroup.mem_sup_of_normal_left (s := commutator H)
    (t := (P : Subgroup H))).mpr
    ⟨y * (y⁻¹ * x) * y⁻¹, hd', y, hyP, by group⟩

private theorem centralizes_commutator_of_sylow {H : Type} [Group H] [Finite H]
    (P : Sylow 5 H) (hP : Nat.card (P : Subgroup H) = 5)
    (hD : Nat.card (commutator H) ∣ 12) :
    ∀ p ∈ (P : Subgroup H), ∀ d ∈ commutator H, p * d * p⁻¹ = d := by
  letI : MulDistribMulAction ↥(P : Subgroup H) ↥(commutator H) :=
    MulDistribMulAction.compHom ↥(commutator H)
      ((MulAut.conjNormal (G := H) (H := commutator H)).comp (P : Subgroup H).subtype)
  have htriv : CFSG.ActsTrivially ↥(P : Subgroup H) ↥(commutator H) :=
    actsTrivially_of_natCard_eq_five_of_dvd_twelve (by simpa using hP) (by simpa using hD)
  intro p hp d hd
  have hfix := htriv ⟨p, hp⟩ ⟨d, hd⟩
  have hval : ((MulAut.conjNormal (G := H) (H := commutator H) p) ⟨d, hd⟩ :
      ↥(commutator H)) = ⟨d, hd⟩ := by
    simpa [MulAction.compHom_smul_def] using hfix
  exact congrArg Subtype.val (by simpa [MulAut.conjNormal_apply] using hval)

private theorem orderOf_five_mem_sylow_of_not_perfect {H : Type} [Group H] [Finite H]
    (P : Sylow 5 H) (hP : Nat.card (P : Subgroup H) = 5)
    (hD : Nat.card (commutator H) ∣ 12)
    (hsup : commutator H ⊔ (P : Subgroup H) = ⊤)
    (hcent : ∀ p ∈ (P : Subgroup H), ∀ d ∈ commutator H, p * d * p⁻¹ = d) :
    {h : H | orderOf h = 5} ⊆ (P : Subgroup H) := by
  intro h hh
  have hmem : h ∈ commutator H ⊔ (P : Subgroup H) := by
    rw [hsup]; exact Subgroup.mem_top h
  obtain ⟨d, hdD, p, hpP, hdp⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := commutator H) (t := (P : Subgroup H))).mp hmem
  have hcommdp : Commute d p := by
    show d * p = p * d
    calc d * p = (p * d * p⁻¹) * p := by rw [hcent p hpP d hdD]
      _ = p * d := by group
  have hh5 : h ^ 5 = 1 := (orderOf_dvd_iff_pow_eq_one).mp (hh ▸ dvd_rfl)
  have hdp5 : (d * p) ^ 5 = 1 := by rw [hdp]; exact hh5
  rw [hcommdp.mul_pow] at hdp5
  have hp5 : p ^ 5 = 1 := by
    have hord : orderOf p ∣ Nat.card (P : Subgroup H) := Subgroup.orderOf_dvd_natCard _ hpP
    rw [hP] at hord
    exact (orderOf_dvd_iff_pow_eq_one).mp hord
  have hd5 : d ^ 5 = 1 := by
    rw [hp5, mul_one] at hdp5
    exact hdp5
  have hordd5 : orderOf d ∣ 5 := orderOf_dvd_iff_pow_eq_one.mpr hd5
  have horddD : orderOf d ∣ Nat.card (commutator H) := Subgroup.orderOf_dvd_natCard _ hdD
  have h5D : ¬ 5 ∣ Nat.card (commutator H) := by
    intro h5
    have : 5 ∣ 12 := h5.trans hD
    norm_num at this
  have hcop5D : Nat.Coprime 5 (Nat.card (commutator H)) :=
    (Nat.prime_five.coprime_iff_not_dvd).mpr h5D
  have hgcd : orderOf d ∣ Nat.gcd 5 (Nat.card (commutator H)) := Nat.dvd_gcd hordd5 horddD
  rw [show Nat.gcd 5 (Nat.card (commutator H)) = 1 from hcop5D] at hgcd
  have hd1 : d = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
  rw [← hdp, hd1, one_mul]
  exact hpP

private theorem card_eq_five_of_not_perfect {H : Type} [Group H] [Finite H] [Nontrivial H]
    (hH : Nat.card H ∣ 60)
    (hgen : Subgroup.closure {h : H | orderOf h = 5} = ⊤)
    (hperf : ¬ Group.IsPerfect H) : Nat.card H = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hQ := card_abelianization_eq_five_of_not_perfect hH hgen hperf
  have hDH := card_eq_five_mul_card_commutator hQ
  have hD12 := card_commutator_dvd_twelve hH hQ
  obtain ⟨P⟩ := Sylow.nonempty (p := 5) (G := H)
  have hP : Nat.card (P : Subgroup H) = 5 :=
    natCard_sylow_eq_five_of_card_eq_five_mul P hDH hD12
  have hbot := inf_commutator_sylow_eq_bot P hP hD12
  have hmap := image_sylow_abelianization_eq_top P hP hQ hbot
  have hsup := sup_commutator_sylow_eq_top P hmap
  have hcent := centralizes_commutator_of_sylow P hP hD12
  have hSsub := orderOf_five_mem_sylow_of_not_perfect P hP hD12 hsup hcent
  have hPtop : (P : Subgroup H) = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Subgroup H) = Subgroup.closure {h : H | orderOf h = 5} := hgen.symm
      _ ≤ (P : Subgroup H) := by
          rw [Subgroup.closure_le]
          exact hSsub
  have hcardH : Nat.card H = Nat.card (P : Subgroup H) := by
    rw [hPtop]
    simp
  omega

private theorem nonempty_mulEquiv_alt_five_of_perfect_of_card_dvd_sixty {H : Type} [Group H]
    [Finite H] [Nontrivial H] (hH : Nat.card H ∣ 60) (hperf : Group.IsPerfect H) :
    Nonempty (H ≃* alternatingGroup (Fin 5)) := by
  haveI : Group.IsPerfect H := hperf
  have hH60 : Nat.card H = 60 := by
    have hle : Nat.card H ≤ 60 := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 60) hH
    by_contra hne
    have hlt : Nat.card H < 60 := lt_of_le_of_ne hle hne
    exact (Group.IsPerfect.not_isSolvable H)
      (CFSG.Quasithin.A312J2.isSolvable_of_card_dvd_sixty hH hlt)
  exact CFSG.Quasithin.A312J2.nonempty_mulEquiv_alt5_of_perfect hperf hH60

theorem alt_five_or_card_five {H : Type} [Group H] [Finite H] [Nontrivial H]
    (hH : Nat.card H ∣ 60) (hgen : Subgroup.closure {h : H | orderOf h = 5} = ⊤) :
    Nonempty (H ≃* alternatingGroup (Fin 5)) ∨ Nat.card H = 5 := by
  by_cases hperf : Group.IsPerfect H
  · exact Or.inl (nonempty_mulEquiv_alt_five_of_perfect_of_card_dvd_sixty hH hperf)
  · exact Or.inr (card_eq_five_of_not_perfect hH hgen hperf)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

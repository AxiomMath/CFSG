module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairWitnessSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFixedRootFull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankLocalCyclic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniActors
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairStatements
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairWitnessCommutator

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG CFSG.Open CFSG.OddInversion CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionFixedRoot
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini

universe u

theorem two_pow_double_sub_one (a : ℕ) : 2 ^ (2 * a) - 1 = (2 ^ a - 1) * (2 ^ a + 1) := by
  have h := Nat.mul_self_sub_mul_self_eq (2 ^ a) 1
  rw [one_mul, ← pow_add, ← two_mul] at h
  rw [h, mul_comm]

theorem prime_not_dvd_two_pow_sub_one {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ a + 1) : ¬ p ∣ 2 ^ a - 1 := by
  intro h
  have h2 : p ∣ (2 ^ a + 1) - (2 ^ a - 1) := Nat.dvd_sub hpq h
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  rw [show (2 ^ a + 1) - (2 ^ a - 1) = 2 by omega] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem factorization_two_pow_sub_one {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ a + 1) : (2 ^ a - 1).factorization p = 0 :=
  Nat.factorization_eq_zero_of_not_dvd (prime_not_dvd_two_pow_sub_one hp hp2 hpq)

theorem two_pow_sub_one_ne_zero {a : ℕ} (ha : 1 ≤ a) : 2 ^ a - 1 ≠ 0 := by
  have : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  omega

theorem factorization_two_pow_double_sub_one {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 1 ≤ a) (hpq : p ∣ 2 ^ a + 1) :
    (2 ^ (2 * a) - 1).factorization p = (2 ^ a + 1).factorization p := by
  rw [two_pow_double_sub_one, Nat.factorization_mul (two_pow_sub_one_ne_zero ha)
    (by positivity), Finsupp.add_apply, factorization_two_pow_sub_one hp hp2 hpq, zero_add]

theorem factorization_point_class {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a)
    (hpq : p ∣ 2 ^ a + 1) (ε : ℕ) :
    ((2 ^ a - 1) * (2 ^ a + 1) ^ ε).factorization p = ε * (2 ^ a + 1).factorization p := by
  rw [Nat.factorization_mul (two_pow_sub_one_ne_zero ha) (by positivity), Finsupp.add_apply,
    factorization_two_pow_sub_one hp hp2 hpq, zero_add, Nat.factorization_pow,
    Finsupp.smul_apply, smul_eq_mul]

theorem one_le_factorization {p a : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ a + 1) :
    1 ≤ (2 ^ a + 1).factorization p :=
  (hp.dvd_iff_one_le_factorization (by positivity)).mp hpq


variable {G : Type u} [Group G] [Finite G]

theorem high_rank_pair_prime_subgroup {H : Subgroup G} {z₀ : G}
    (h₀ : MinimalInvolutionPointLocalFailure H z₀)
    (hcomm : ProperStrongEmbeddingCommutingImages G) (hR1 : SmallerR1Full G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z₀ beta)
    {u v : G} (huB : u ∈ pairPointStabilizer H beta) (hvB : v ∈ pairPointStabilizer H beta)
    (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u ≠ v) (hcuv : Commute u v)
    (huz : Commute u z₀) (hvz : Commute v z₀) (hut : Commute u t) (hvt : Commute v t)
    {a ε : ℕ} (ha : 1 ≤ a)
    (hm : Nat.card (conjugacyWithin H z₀) = (2 ^ a - 1) * (2 ^ a + 1) ^ ε)
    (hΔu : Nat.card (pointRoots H z₀ u) = 2 ^ (2 * a) - 1)
    (hΔv : Nat.card (pointRoots H z₀ v) = 2 ^ (2 * a) - 1)
    {x : G} (hε : ε = 2 ∧ x = u * v ∧ Nat.card (pointRoots H z₀ (u * v)) = 2 ^ a - 1 ∨
      ε = 3 ∧ x = u ∧ Nat.card (pointRoots H z₀ (u * v)) = 2 ^ (2 * a) - 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ a + 1) :
    ∃ A : Subgroup G, A ≤ pairOddCore H beta ∧
      u ∈ Subgroup.normalizer (A : Set G) ∧ v ∈ Subgroup.normalizer (A : Set G) ∧
      t ∈ Subgroup.normalizer (A : Set G) ∧ IsPGroup p A ∧ ¬ IsCyclic A ∧
      ⁅A, Subgroup.zpowers t⁆ = A ∧
      (A ⊓ Subgroup.centralizer ({t} : Set G)).relIndex A =
        (p ^ (Nat.factorization (2 ^ a + 1) p)) ^ 2 ∧
      A ≤ Subgroup.centralizer ({x * t} : Set G) ∧
      ∀ w : G, w = u ∨ w = v ∨ w = u * v → ¬ A ≤ Subgroup.centralizer ({w} : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hzS, hzcenter⟩ := h₀.central_sylow
  set I := pairOddCore H beta with hIdef
  have hI : Odd (Nat.card I) := pairOddCore_odd H beta
  have htord : orderOf t = 2 := original_pair_flip_order h₀ ht
  have htH : t ∉ H := pair_flip_not_mem_point hbeta ht
  set W := Subgroup.zpowers u ⊔ Subgroup.zpowers v with hWdef
  obtain ⟨helem, hWcard, -⟩ := CFSG.ProperTwoGeneratedCore.commuting_distinct_involutions_four_group
    hu hv hcuv huv.symm
  let : IsElementaryAbelian 2 W :=
    { toIsMulCommutative := helem.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun w => by
        apply Subtype.ext
        exact helem.2 w w.property) }
  have hWB : W ≤ pairPointStabilizer H beta :=
    sup_le (Subgroup.zpowers_le.mpr huB) (Subgroup.zpowers_le.mpr hvB)
  have hWz : W ≤ Subgroup.centralizer ({z₀} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr huz.eq))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hvz.eq))
  have hWt : W ≤ Subgroup.centralizer ({t} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hut.eq))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hvt.eq))
  have hz₀W : z₀ ∈ Subgroup.centralizer (W : Set G) := Subgroup.mem_centralizer_iff.mpr
    fun w hw => Subgroup.mem_centralizer_singleton_iff.mp (hWz hw)
  have htW : t ∈ Subgroup.centralizer (W : Set G) := Subgroup.mem_centralizer_iff.mpr
    fun w hw => Subgroup.mem_centralizer_singleton_iff.mp (hWt hw)
  obtain ⟨-, hEcard⟩ := original_pair_generated_actor_structure h₀ hbeta ht W hWcard hWB hWt
  have hE2 : IsPGroup 2 (W ⊔ Subgroup.zpowers t : Subgroup G) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 3) (by rw [hEcard]; norm_num)
  have hBI : pairPointStabilizer H beta ≤ Subgroup.normalizer (I : Set G) :=
    original_pairOddCore_normalized h₀.local_datum hbeta ht
  have htI : t ∈ Subgroup.normalizer (I : Set G) :=
    pair_flip_normalizes_ambient_odd_core h₀.local_datum.distinguished_order hbeta ht
  have hEI : W ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (I : Set G) :=
    sup_le (hWB.trans hBI) (Subgroup.zpowers_le.mpr htI)
  obtain ⟨R, hR⟩ := exists_sylow_normalized hI hE2 hEI hp
  set P := (R : Subgroup I).map I.subtype with hPdef
  have hWP : W ≤ Subgroup.normalizer (P : Set G) := le_sup_left.trans hR
  have htP : t ∈ Subgroup.normalizer (P : Set G) :=
    hR (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have huW : u ∈ W := Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
  have hvW : v ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
  have huvW : u * v ∈ W := W.mul_mem huW hvW
  have hWord : ∀ w ∈ W, w ≠ 1 → orderOf w = 2 := fun w hw hw1 =>
    orderOf_eq_prime (helem.2 w hw) hw1
  have huv1 : u * v ≠ 1 := by
    intro h1
    apply huv
    have := mul_eq_one_iff_eq_inv.mp h1
    rw [this, inv_eq_of_mul_eq_one_right (by rw [← pow_two, ← hv, pow_orderOf_eq_one])]
  have hxW : x ∈ W := by
    rcases hε with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
    · exact huvW
    · exact huW
  have hx1 : x ≠ 1 := by
    rcases hε with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
    · exact huv1
    · intro h1
      rw [h1, orderOf_one] at hu
      omega
  have hxord : orderOf x = 2 := hWord x hxW hx1
  have hxB : x ∈ pairPointStabilizer H beta := hWB hxW
  have hxt : Commute x t := Subgroup.mem_centralizer_singleton_iff.mp (hWt hxW)
  have hxne : x ≠ t := fun h => htH (pairPointStabilizer_le_point H beta (h ▸ hxB))
  have hxI : x ∈ Subgroup.normalizer (I : Set G) := hBI hxB
  have hxP : x ∈ Subgroup.normalizer (P : Set G) := hWP hxW
  have hid := prime_index_identity hI hxord htord hxt hxne hxI htI hp R hxP htP
  have hmI : Nat.card (conjugacyWithin H z₀) =
      (Subgroup.centralizer ({t} : Set G)).relIndex I :=
    original_root_card_eq_t_centralizer_index h₀.local_datum S hzS hzcenter hbeta ht W hWB
      hz₀W htW
  have hδI : ∀ w ∈ W, Nat.card (pointRoots H z₀ w) =
      (Subgroup.centralizer ({t} : Set G)).relIndex (I ⊓ Subgroup.centralizer ({w} : Set G)) := by
    intro w hw
    have hwW : Subgroup.zpowers w ≤ W := Subgroup.zpowers_le.mpr hw
    have h1 := original_fixed_root_card_eq_centralizer_index h₀.local_datum S hzS hzcenter
      hbeta ht W hWB hz₀W htW (Subgroup.zpowers w) hwW
    rw [← centralizer_intersection_relative_index, centralizer_zpowers_eq_singleton] at h1
    exact h1
  set f := (2 ^ a + 1).factorization p with hfdef
  have hf1 : 1 ≤ f := one_le_factorization hp hpq
  have hFm : ((Subgroup.centralizer ({t} : Set G)).relIndex I).factorization p =
      ((Subgroup.centralizer ({t} : Set G)).relIndex
        (I ⊓ Subgroup.centralizer ({x} : Set G))).factorization p + 2 * f := by
    rw [← hmI, ← hδI x hxW, hm, factorization_point_class hp hp2 ha hpq]
    rcases hε with ⟨rfl, rfl, hδ⟩ | ⟨rfl, rfl, -⟩
    · rw [hδ, factorization_two_pow_sub_one hp hp2 hpq]
      ring
    · rw [hΔu, factorization_two_pow_double_sub_one hp hp2 ha hpq]
      ring
  set J := P ⊓ Subgroup.centralizer ({x * t} : Set G) with hJdef
  have hJr : (Subgroup.centralizer ({t} : Set G)).relIndex J = p ^ (2 * f) := by
    rw [hFm, pow_add, mul_comm (p ^ _)] at hid
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) hid
  have hPI : P ≤ I := Subgroup.map_subtype_le _
  have hJP : J ≤ P := inf_le_left
  have hJodd : Odd (Nat.card J) := hI.of_dvd_nat (Subgroup.card_dvd_of_le (hJP.trans hPI))
  have hWcomm : ∀ g ∈ W, ∀ k ∈ W, Commute g k := fun g hg k hk =>
    congrArg Subtype.val (helem.1.is_comm.comm ⟨g, hg⟩ ⟨k, hk⟩)
  have hWJ : ∀ g ∈ W, g ∈ Subgroup.normalizer (J : Set G) := by
    intro g hg
    have hgt : Commute g t := Subgroup.mem_centralizer_singleton_iff.mp (hWt hg)
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hWP hg,
      CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.commute_normalizes_centralizer g
        (x * t) ((hWcomm g hg x hxW).mul_right hgt)⟩
  have htJ : t ∈ Subgroup.normalizer (J : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨htP,
      CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.commute_normalizes_centralizer t
        (x * t) (hxt.symm.mul_right (Commute.refl t))⟩
  set A := Subgroup.closure (invertedSet J t) with hAdef
  have hAJ : A ≤ J := closure_invertedSet_le J t
  have hAI : A ≤ I := hAJ.trans (hJP.trans hPI)
  have hWA : ∀ g ∈ W, g ∈ Subgroup.normalizer (A : Set G) := fun g hg =>
    mem_normalizer_closure_invertedSet (hWJ g hg)
      (Subgroup.mem_centralizer_singleton_iff.mp (hWt hg))
  have htA : t ∈ Subgroup.normalizer (A : Set G) := flip_mem_normalizer_closure_invertedSet htJ
  have hAp : IsPGroup p A := (R.isPGroup'.map I.subtype).to_le (hAJ.trans hJP)
  have hArel : (Subgroup.centralizer ({t} : Set G)).relIndex A = p ^ (2 * f) := by
    rw [relIndex_closure_invertedSet hJodd htJ htord]
    exact hJr
  have hkey : ∀ w : G, w = u ∨ w = v ∨ w = u * v →
      ¬ A ≤ Subgroup.centralizer ({w} : Set G) := by
    intro w hw hAw
    have hwW : w ∈ W := by
      rcases hw with rfl | rfl | rfl
      · exact huW
      · exact hvW
      · exact huvW
    have hw1 : w ≠ 1 := by
      rcases hw with rfl | rfl | rfl
      · intro h1; rw [h1, orderOf_one] at hu; omega
      · intro h1; rw [h1, orderOf_one] at hv; omega
      · exact huv1
    have hΔw : Nat.card (pointRoots H z₀ w) = 2 ^ a - 1 ∨
        Nat.card (pointRoots H z₀ w) = 2 ^ (2 * a) - 1 := by
      rcases hw with rfl | rfl | rfl
      · exact Or.inr hΔu
      · exact Or.inr hΔv
      · rcases hε with ⟨-, -, h⟩ | ⟨-, -, h⟩
        · exact Or.inl h
        · exact Or.inr h
    have hword := hWord w hwW hw1
    have hwz : Commute w z₀ := Subgroup.mem_centralizer_singleton_iff.mp (hWz hwW)
    have hwt : Commute w t := Subgroup.mem_centralizer_singleton_iff.mp (hWt hwW)
    obtain ⟨hKset, -, hKcard, -⟩ := original_local_cyclic_commutator_and_normality h₀ hcomm hR1
      S hzS hzcenter beta hbeta t ht w hword hwz hwt
    have hAK : A ≤ rightInvolutionCommutatorSubgroup t
        (pairOddCore H beta ⊓ Subgroup.centralizer ({w} : Set G)) := by
      rw [hAdef, Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, ← SetLike.mem_coe, hKset]
      refine ⟨⟨hJP.trans hPI hy.1, hAw (Subgroup.subset_closure hy)⟩, ?_⟩
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right
        (by rw [← pow_two, ← htord, pow_orderOf_eq_one])
      change t⁻¹ * y * t = y⁻¹
      rw [← hy.2]
      nth_rewrite 2 [← htinv]
      rw [htinv]
    have hdvd : p ^ (2 * f) ∣ Nat.card (pointRoots H z₀ w) := by
      have hK : Nat.card (rightInvolutionCommutatorSubgroup t
          (pairOddCore H beta ⊓ Subgroup.centralizer ({w} : Set G))) =
          Nat.card (pointRoots H z₀ w) := hKcard
      rw [← hArel, ← hK]
      exact (Subgroup.relIndex_dvd_card _ A).trans (Subgroup.card_dvd_of_le hAK)
    have hle : (Nat.card (pointRoots H z₀ w)).factorization p ≤ f := by
      rcases hΔw with h | h
      · rw [h, factorization_two_pow_sub_one hp hp2 hpq]
        exact Nat.zero_le _
      · rw [h, factorization_two_pow_double_sub_one hp hp2 ha hpq]
    have hne : Nat.card (pointRoots H z₀ w) ≠ 0 := by
      rcases hΔw with h | h
      · rw [h]; exact two_pow_sub_one_ne_zero ha
      · rw [h]; exact two_pow_sub_one_ne_zero (by omega)
    have h2f := (hp.pow_dvd_iff_le_factorization hne).mp hdvd
    omega
  have hsq : ∀ g : G, orderOf g = 2 → g * g = 1 := fun g hg => by
    rw [← pow_two, ← hg, pow_orderOf_eq_one]
  refine ⟨A, hAI, hWA u huW, hWA v hvW, htA, hAp, ?_, commutator_closure_invertedSet hJodd htJ,
    ?_, hAJ.trans inf_le_right, hkey⟩
  · intro hcyc
    rcases cyclic_pgroup_four_group_centralizes hp hp2 hAp hcyc (hWA u huW) (hWA v hvW)
      (hsq u hu) (hsq v hv) with h | h | h
    · exact hkey u (Or.inl rfl) h
    · exact hkey v (Or.inr (Or.inl rfl)) h
    · exact hkey (u * v) (Or.inr (Or.inr rfl)) h
  · rw [Subgroup.inf_relIndex_left, hArel]
    ring

end CFSG.ProperTwoGeneratedCore.HighRankPair

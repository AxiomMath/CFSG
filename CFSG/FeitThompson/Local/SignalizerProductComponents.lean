module

public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

section PiCalculus

variable {X : Type*} [Group X] {π π' : Set ℕ} {x y : X}

theorem piConstituent_eq_pow_piExponent (hx : orderOf x ≠ 0) :
    piConstituent π x = x ^ piExponent π (orderOf x) :=
  piConstituent_eq_pow hx (piExponent_modEq_one _ _) (piExponent_modEq_zero _ _)

@[simp]
theorem piConstituent_one (π : Set ℕ) : piConstituent π (1 : X) = 1 := by
  rw [piConstituent_eq_pow_piExponent (by simp), one_pow]

theorem piPart_dvd_piPart_of_dvd (π : Set ℕ) {m n : ℕ} (hn : n ≠ 0) (hd : m ∣ n) :
    piPart π m ∣ piPart π n :=
  dvd_piPart hn ((piPart_dvd π m).trans hd) (piPart_ne_zero π m)
    (primeFactors_piPart_subset π m)

theorem IsPiElement.piConstituent_eq_self (hx : orderOf x ≠ 0) (h : IsPiElement π x) :
    piConstituent π x = x := by
  rw [piConstituent_eq_pow_piExponent hx]
  conv_rhs => rw [← pow_one x]
  refine pow_eq_pow_iff_modEq.2 ?_
  have h1 := piExponent_modEq_one π (orderOf x)
  rwa [piPart_eq_self hx fun q hq => isPiElement_iff.1 h q hq] at h1

theorem piPart_eq_one_of_forall_notMem {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p ∈ n.primeFactors, p ∉ π) : piPart π n = 1 := by
  have h1 : (piPart π n).primeFactors = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro q hq
    exact h q (Nat.primeFactors_mono (piPart_dvd π n) hn hq)
      (primeFactors_piPart_subset π n (Finset.mem_coe.2 hq))
  rcases Nat.primeFactors_eq_empty.1 h1 with h2 | h2
  · exact absurd h2 (piPart_ne_zero π n)
  · exact h2

theorem piConstituent_eq_one_of_forall_notMem (hx : orderOf x ≠ 0)
    (h : ∀ p ∈ (orderOf x).primeFactors, p ∉ π) : piConstituent π x = 1 := by
  rw [← orderOf_eq_one_iff, orderOf_piConstituent hx, piPart_eq_one_of_forall_notMem hx h]

theorem piConstituent_eq_one_of_inter_eq_empty (hx : orderOf x ≠ 0) (h : IsPiElement π' x)
    (hd : π ∩ π' = ∅) : piConstituent π x = 1 := by
  refine piConstituent_eq_one_of_forall_notMem hx fun q hq hqπ => ?_
  have hmem : q ∈ π ∩ π' := ⟨hqπ, isPiElement_iff.1 h q hq⟩
  rw [hd] at hmem
  exact hmem

theorem IsPiElement.nonempty (hx : orderOf x ≠ 0) (h : IsPiElement π x) (hx1 : x ≠ 1) :
    π.Nonempty := by
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (orderOf_eq_one_iff.not.2 hx1)
  exact ⟨q, isPiElement_iff.1 h q (Nat.mem_primeFactors.2 ⟨hq, hqd, hx⟩)⟩

theorem IsPiElement.coprime_orderOf (hx : orderOf x ≠ 0) (hy : orderOf y ≠ 0)
    (hxp : IsPiElement π x) (hyp : IsPiElement π' y) (hd : π ∩ π' = ∅) :
    (orderOf x).Coprime (orderOf y) := by
  refine (Nat.disjoint_primeFactors hx hy).1 (Finset.disjoint_left.2 fun q hq hq' => ?_)
  have hmem : q ∈ π ∩ π' := ⟨isPiElement_iff.1 hxp q hq, isPiElement_iff.1 hyp q hq'⟩
  rw [hd] at hmem
  exact hmem

theorem piConstituent_mul_of_commute_of_coprime (h : Commute x y) (hx : orderOf x ≠ 0)
    (hy : orderOf y ≠ 0) (hcop : (orderOf x).Coprime (orderOf y)) (π : Set ℕ) :
    piConstituent π (x * y) = piConstituent π x * piConstituent π y := by
  have hn : orderOf (x * y) = orderOf x * orderOf y :=
    h.orderOf_mul_eq_mul_orderOf_of_coprime hcop
  have hn0 : orderOf (x * y) ≠ 0 := by rw [hn]; exact Nat.mul_ne_zero hx hy
  have hdx : orderOf x ∣ orderOf (x * y) := by rw [hn]; exact dvd_mul_right _ _
  have hdy : orderOf y ∣ orderOf (x * y) := by rw [hn]; exact dvd_mul_left _ _
  have hxa : piConstituent π x = x ^ piExponent π (orderOf (x * y)) :=
    piConstituent_eq_pow hx
      ((piExponent_modEq_one π _).of_dvd (piPart_dvd_piPart_of_dvd π hn0 hdx))
      ((piExponent_modEq_zero π _).of_dvd (piPart_dvd_piPart_of_dvd πᶜ hn0 hdx))
  have hya : piConstituent π y = y ^ piExponent π (orderOf (x * y)) :=
    piConstituent_eq_pow hy
      ((piExponent_modEq_one π _).of_dvd (piPart_dvd_piPart_of_dvd π hn0 hdy))
      ((piExponent_modEq_zero π _).of_dvd (piPart_dvd_piPart_of_dvd πᶜ hn0 hdy))
  rw [piConstituent_eq_pow_piExponent hn0, hxa, hya, h.mul_pow]

variable [Finite X]

theorem isPiElement_of_mem_of_isPiSubgroup {N : Subgroup X} (hN : IsPiSubgroup π N) (hx : x ∈ N) :
    IsPiElement π x :=
  isPiElement_iff.2 fun q hq =>
    isPiSubgroup_iff.1 hN q (Nat.primeFactors_mono (N.orderOf_dvd_natCard hx) Nat.card_pos.ne' hq)

end PiCalculus

open _root_.CFSG.FeitThompson
  _root_.CFSG.FeitThompson.Prep09

variable {G : Type*} [Group G] [Finite G] {M N T : Subgroup G} {x r : G}

theorem sigmaPrimes_conjSub (g : G) (M : Subgroup G) :
    sigmaPrimes (conjSub g M) = sigmaPrimes M :=
  sigmaPrimes_eq_of_coe_eq_conj_image (by rw [coe_conjSub, conjSet_def])

theorem mem_sigmaPrimeSets_sigmaPrimes (hM : IsCoatom M) (hx : x ∈ sigmaCore M) (hx1 : x ≠ 1) :
    sigmaPrimes M ∈ sigmaPrimeSets G :=
  ⟨(isPiElement_of_mem_of_isPiSubgroup (isPiSubgroup_sigmaCore M) hx).nonempty
      (orderOf_pos x).ne' hx1, M, hM, rfl⟩

theorem mem_sigmaConstituents {x y : G} :
    y ∈ sigmaConstituents x ↔ ∃ π ∈ sigmaPrimeSets G, y = piConstituent π x ∧ y ≠ 1 := Iff.rfl

@[simp]
theorem sigmaConstituents_one : sigmaConstituents (1 : G) = ∅ := by
  ext y
  simp [mem_sigmaConstituents]

theorem sigmaPrimes_eq_or_inter_eq_empty
    (hsep : ∀ M T : Subgroup G, IsCoatom M → IsCoatom T →
      (∀ g : G, T ≠ conjSub g M) → sigmaPrimes M ∩ sigmaPrimes T = ∅)
    (hM : IsCoatom M) (hT : IsCoatom T) :
    sigmaPrimes T = sigmaPrimes M ∨ sigmaPrimes M ∩ sigmaPrimes T = ∅ := by
  by_cases hc : ∃ g : G, T = conjSub g M
  · obtain ⟨g, rfl⟩ := hc
    exact Or.inl (sigmaPrimes_conjSub g M)
  · exact Or.inr (hsep M T hM hT (by simpa using hc))

theorem sigmaConstituents_of_mem_sigmaCore (hM : IsCoatom M) (hx : x ∈ sigmaCore M) (hx1 : x ≠ 1)
    (hdich : ∀ T : Subgroup G, IsCoatom T →
      sigmaPrimes T = sigmaPrimes M ∨ sigmaPrimes M ∩ sigmaPrimes T = ∅) :
    sigmaConstituents x = {x} := by
  have hxpi : IsPiElement (sigmaPrimes M) x :=
    isPiElement_of_mem_of_isPiSubgroup (isPiSubgroup_sigmaCore M) hx
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_sigmaConstituents.2 ⟨sigmaPrimes M,
    mem_sigmaPrimeSets_sigmaPrimes hM hx hx1,
    (hxpi.piConstituent_eq_self (orderOf_pos x).ne').symm, hx1⟩, ?_⟩
  rintro y ⟨π, ⟨-, T, hT, rfl⟩, rfl, hy1⟩
  rcases hdich T hT with h | h
  · rw [h]
    exact hxpi.piConstituent_eq_self (orderOf_pos x).ne'
  · exact absurd (piConstituent_eq_one_of_inter_eq_empty (orderOf_pos x).ne' hxpi
      (by rw [Set.inter_comm]; exact h)) hy1

theorem sigmaConstituents_mul (hM : IsCoatom M) (hN : IsCoatom N) (hx : x ∈ sigmaCore M)
    (hx1 : x ≠ 1) (hr : r ∈ sigmaCore N) (hr1 : r ≠ 1)
    (hdisj : sigmaPrimes M ∩ sigmaPrimes N = ∅) (hcomm : Commute x r)
    (hdichM : ∀ T : Subgroup G, IsCoatom T →
      sigmaPrimes T = sigmaPrimes M ∨ sigmaPrimes M ∩ sigmaPrimes T = ∅)
    (hdichN : ∀ T : Subgroup G, IsCoatom T →
      sigmaPrimes T = sigmaPrimes N ∨ sigmaPrimes N ∩ sigmaPrimes T = ∅) :
    sigmaConstituents (x * r) = {x, r} ∧ x ≠ r := by
  have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hr0 : orderOf r ≠ 0 := (orderOf_pos r).ne'
  have hxpi : IsPiElement (sigmaPrimes M) x :=
    isPiElement_of_mem_of_isPiSubgroup (isPiSubgroup_sigmaCore M) hx
  have hrpi : IsPiElement (sigmaPrimes N) r :=
    isPiElement_of_mem_of_isPiSubgroup (isPiSubgroup_sigmaCore N) hr
  have hcop : (orderOf x).Coprime (orderOf r) := hxpi.coprime_orderOf hx0 hr0 hrpi hdisj
  have hMne : (sigmaPrimes M).Nonempty := hxpi.nonempty hx0 hx1
  have hxM : piConstituent (sigmaPrimes M) x = x := hxpi.piConstituent_eq_self hx0
  have hrN : piConstituent (sigmaPrimes N) r = r := hrpi.piConstituent_eq_self hr0
  have hrM : piConstituent (sigmaPrimes M) r = 1 :=
    piConstituent_eq_one_of_inter_eq_empty hr0 hrpi hdisj
  have hxN : piConstituent (sigmaPrimes N) x = 1 :=
    piConstituent_eq_one_of_inter_eq_empty hx0 hxpi (by rw [Set.inter_comm]; exact hdisj)
  have hsplit : ∀ π : Set ℕ,
      piConstituent π (x * r) = piConstituent π x * piConstituent π r :=
    piConstituent_mul_of_commute_of_coprime hcomm hx0 hr0 hcop
  refine ⟨Set.eq_of_subset_of_subset ?_ ?_, ?_⟩
  · rintro y ⟨π, ⟨-, T, hT, rfl⟩, rfl, hy1⟩
    rw [hsplit]
    rcases hdichM T hT with h | h
    · rcases hdichN T hT with h' | h'
      ·
        exact absurd (by rw [← h.symm.trans h', Set.inter_self] at hdisj; exact hdisj)
          hMne.ne_empty
      · rw [h, hxM, hrM, mul_one]
        exact Set.mem_insert _ _
    · rcases hdichN T hT with h' | h'
      · rw [h', hxN, hrN, one_mul]
        exact Set.mem_insert_of_mem _ rfl
      · refine absurd ?_ hy1
        rw [hsplit, piConstituent_eq_one_of_inter_eq_empty hx0 hxpi
            (by rw [Set.inter_comm]; exact h),
          piConstituent_eq_one_of_inter_eq_empty hr0 hrpi
            (by rw [Set.inter_comm]; exact h'), mul_one]
  · rintro y (rfl | rfl)
    · exact ⟨sigmaPrimes M, mem_sigmaPrimeSets_sigmaPrimes hM hx hx1,
        by rw [hsplit, hxM, hrM, mul_one], hx1⟩
    · exact ⟨sigmaPrimes N, mem_sigmaPrimeSets_sigmaPrimes hN hr hr1,
        by rw [hsplit, hxN, hrN, one_mul], hr1⟩
  ·
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.1 (by simpa [Nat.Coprime] using hcop))

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep09

universe u

theorem FTS_signalizer_product_components
    (h₁ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₂ : Statements.FTS_sigma_prime_separation.{u}) :
    Statements.FTS_signalizer_product_components.{u} := by
  intro G _ _ hG x hx
  have hamb : IsFTAmbient G :=
    { isSimpleGroup := hG.isSimpleGroup
      not_isMulCommutative := hG.not_isMulCommutative
      odd_natCard := hG.odd_natCard
      isSolvable := hG.isSolvable_of_ne_top }
  have hdich : ∀ M : Subgroup G, IsCoatom M → ∀ T : Subgroup G, IsCoatom T →
      sigmaPrimes T = sigmaPrimes M ∨ sigmaPrimes M ∩ sigmaPrimes T = ∅ :=
    fun _ hM _ hT => sigmaPrimes_eq_or_inter_eq_empty (h₂ G hG) hM hT
  obtain ⟨M, hM, hxM, hx1⟩ := mem_sigmaSupport.1 hx
  have hxsup : M ∈ sigmaSupportingMaximals (G := G) x := mem_sigmaSupportingMaximals.2 ⟨hM, hxM⟩
  have key : ∀ r ∈ sigmaSignalizer x,
      (r = 1 → sigmaConstituents (x * r) = {x}) ∧
        (r ≠ 1 → sigmaConstituents (x * r) = {x, r} ∧ r ∈ sigmaSupport G ∧ x ≠ r) := by
    intro r hr
    refine ⟨fun hr1 => ?_, fun hr1 => ?_⟩
    · rw [hr1, mul_one]
      exact sigmaConstituents_of_mem_sigmaCore hM hxM hx1 (hdich M hM)
    ·
      have hRne : sigmaSignalizer x ≠ ⊥ := fun h => hr1 (by simpa [h] using hr)
      obtain ⟨N, hN, -, hRN, -, hdisj⟩ := (h₁ G hamb x hx).2.2.2.2.2 hRne M hxsup
      have hrN : r ∈ sigmaCore N := hRN hr
      have hcomm : Commute x r :=
        Subgroup.mem_centralizer_iff.1 (sigmaSignalizer_le_centralizer x hr) x rfl
      obtain ⟨h1, h2⟩ :=
        sigmaConstituents_mul hM hN hxM hx1 hrN hr1 hdisj hcomm (hdich M hM) (hdich N hN)
      exact ⟨h1, mem_sigmaSupport.2 ⟨N, hN, hrN, hr1⟩, h2⟩
  refine ⟨key, fun hmem => ?_⟩
  have hxinv : x⁻¹ ∈ sigmaSignalizer x := by
    simpa using Set.mem_smul_set_iff_inv_smul_mem.1 hmem
  have hinv1 : x⁻¹ ≠ 1 := fun h => hx1 (inv_eq_one.1 h)
  obtain ⟨hset, -, -⟩ := (key x⁻¹ hxinv).2 hinv1
  rw [mul_inv_cancel x, sigmaConstituents_one] at hset
  exact absurd hset.symm (Set.insert_nonempty x {x⁻¹}).ne_empty

end

end CFSG.FeitThompson.Proofs

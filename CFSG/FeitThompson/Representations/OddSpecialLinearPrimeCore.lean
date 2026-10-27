module

public import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Representations.NormalPrimeKernelCommutative
import CFSG.FeitThompson.Representations.TrivialDeterminantKernelAbelianOrder
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Foundations.BurnsideNormalPComplement
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Matrix Subgroup MatrixGroups

section Aux

variable {G N : Type*} [Group G] [Group N]

private theorem normal_subgroupOf_map (f : G →* N) {Q H : Subgroup G} (hQH : Q ≤ H)
    (hnorm : H ≤ normalizer (Q : Set G)) : ((Q.map f).subgroupOf (H.map f)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hQH)]
  exact (Subgroup.map_mono hnorm).trans (Subgroup.le_normalizer_map f)

private theorem le_normalizer_map_subtype {D : Subgroup G} (K : Subgroup ↥D) [K.Normal] :
    D ≤ normalizer ((K.map D.subtype : Subgroup G) : Set G) := by
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le K)]
  change (Subgroup.comap D.subtype (K.map D.subtype)).Normal
  rw [Subgroup.comap_map_eq_self_of_injective D.subtype_injective]
  infer_instance

variable [Finite G]

private theorem pCoreIn_ne_bot_of_isPGroup {r : ℕ} (hr : r.Prime)
    {D : Subgroup G} (hD1 : D ≠ ⊥) (hDr : IsPGroup r ↥D) : pCoreIn r D ≠ ⊥ := fun hbot =>
  hD1 (le_bot_iff.mp (hbot ▸ le_pCoreIn hr le_rfl Subgroup.le_normalizer hDr))

private theorem pCoreIn_ne_bot_of_le_normalizer {r : ℕ} (hr : r.Prime)
    {M D : Subgroup G} (hMD : M ≤ D) (hnorm : D ≤ normalizer (M : Set G))
    (h : pCoreIn r M ≠ ⊥) : pCoreIn r D ≠ ⊥ := by
  refine fun hbot => h (le_bot_iff.mp (hbot ▸ ?_))
  exact le_pCoreIn hr ((pCoreIn_le r M).trans hMD) (le_normalizer_pCoreIn r hnorm)
    (isPGroup_pCoreIn hr M)

theorem pCoreIn_ne_bot_iff (r : ℕ) (D : Subgroup G) :
    pCoreIn r D ≠ ⊥ ↔ pCore r ↥D ≠ ⊥ := by
  rw [pCoreIn_eq, Ne, Ne, Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective]

theorem pCore_ne_bot_iff_exists_normal_isPGroup {r : ℕ} (hr : r.Prime) :
    pCore r G ≠ ⊥ ↔ ∃ M : Subgroup G, M.Normal ∧ IsPGroup r ↥M ∧ M ≠ ⊥ := by
  refine ⟨fun h => ⟨pCore r G, pCore_normal r G, isPGroup_pCore hr G, h⟩, ?_⟩
  rintro ⟨M, hM, hMr, hM1⟩ h
  exact hM1 (le_bot_iff.mp (h ▸ le_pCore hr hM hMr))

theorem pCore_ne_bot_congr [Finite N] (r : ℕ) (e : G ≃* N) :
    pCore r G ≠ ⊥ ↔ pCore r N ≠ ⊥ := by
  rw [← map_pCore_of_mulEquiv r e, Ne, Ne,
    Subgroup.map_eq_bot_iff_of_injective _ (EquivLike.injective e)]

end Aux

section Main

variable {k : Type*} [Field k] [Finite k] {p f q : ℕ}

private theorem exists_pCoreIn_ne_bot_aux [CharP k p] (hp : p.Prime) :
    ∀ n : ℕ, ∀ D : Subgroup (GL (Fin 2) k), Nat.card D ≤ n → D ≠ ⊥ → Odd (Nat.card D) →
      D ≤ (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := k)).range →
      ∃ r : ℕ, r.Prime ∧ pCoreIn r D ≠ ⊥ := by
  intro n
  induction n with
  | zero => exact fun D hcard => absurd hcard (by have := Nat.card_pos (α := ↥D); omega)
  | succ n ih =>
  intro D hcard hD1 hDodd hDSL
  by_cases hDp : IsPGroup p ↥D
  ·
    exact ⟨p, hp, pCoreIn_ne_bot_of_isPGroup hp hD1 hDp⟩
  rw [isPGroup_iff_primeFactors_card_subset hp.ne_zero, hp.primeFactors] at hDp
  obtain ⟨r, hrmem, hrp⟩ := Finset.not_subset.mp hDp
  have hr : r.Prime := Nat.prime_of_mem_primeFactors hrmem
  have hrdvd : r ∣ Nat.card ↥D := Nat.dvd_of_mem_primeFactors hrmem
  have hrp' : r ≠ p := by simpa using hrp
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨Q⟩ : Nonempty (Sylow r ↥D) := inferInstance
  have hQcard : Nat.card ↥(Q : Subgroup ↥D) = r ^ (Nat.card ↥D).factorization r :=
    Q.card_eq_multiplicity
  have hepos : 0 < (Nat.card ↥D).factorization r :=
    hr.factorization_pos_of_dvd Nat.card_pos.ne' hrdvd
  have h2 : 2 ≤ r ^ (Nat.card ↥D).factorization r :=
    Nat.one_lt_pow (a := r) hepos.ne' hr.one_lt
  have hQ1 : (Q : Subgroup ↥D) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hQcard
    omega
  set H : Subgroup ↥D := normalizer ((Q : Subgroup ↥D) : Set ↥D) with hH
  have hQH : (Q : Subgroup ↥D) ≤ H := Subgroup.le_normalizer
  have habs : IsMulCommutative ↥(H.map D.subtype) := by
    refine (isMulCommutative_and_not_dvd_of_normal_prime_kernel_isPGroup hp hr hrp'
      (G := H.map D.subtype) (R := (Q : Subgroup ↥D).map D.subtype) ?_ ?_ ?_ ?_ ?_ ?_).1
    · rw [Nat.card_congr
        (Subgroup.equivMapOfInjective H D.subtype D.subtype_injective).symm.toEquiv]
      exact hDodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card H)
    · exact Subgroup.map_mono hQH
    · exact normal_subgroupOf_map D.subtype hQH le_rfl
    · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective]
    · exact (Q.isPGroup').map _
    · exact (Subgroup.map_subtype_le _).trans hDSL
  have hcomm : ∀ x ∈ normalizer (((Q : Subgroup ↥D) : Subgroup ↥D) : Set ↥D),
      ∀ y ∈ (Q : Subgroup ↥D), x * y = y * x := by
    intro x hx y hy
    have hxm : D.subtype x ∈ H.map D.subtype := ⟨x, hx, rfl⟩
    have hym : D.subtype y ∈ H.map D.subtype := ⟨y, hQH hy, rfl⟩
    have hc := habs.is_comm.comm (⟨_, hxm⟩ : ↥(H.map D.subtype)) ⟨_, hym⟩
    refine D.subtype_injective ?_
    simpa using congrArg (fun z : ↥(H.map D.subtype) => (z : GL (Fin 2) k)) hc
  obtain ⟨K, hKnorm, -, hKindex, -, -⟩ :=
    exists_normal_pComplement_sylow_of_normalizer_comm Q hcomm
  have := hKnorm
  rw [hQcard] at hKindex
  by_cases hK1 : K = ⊥
  ·
    subst hK1
    rw [Subgroup.index_bot] at hKindex
    exact ⟨r, hr, pCoreIn_ne_bot_of_isPGroup hr hD1 (IsPGroup.of_card hKindex)⟩
  ·
    have hcardK : Nat.card ↥K < Nat.card ↥D :=
      calc Nat.card ↥K < Nat.card ↥K * 2 := by have := Nat.card_pos (α := ↥K); omega
        _ ≤ Nat.card ↥K * r ^ (Nat.card ↥D).factorization r := Nat.mul_le_mul_left _ h2
        _ = Nat.card ↥D := by rw [← hKindex, Subgroup.card_mul_index]
    have hKe := Nat.card_congr
      (Subgroup.equivMapOfInjective K D.subtype D.subtype_injective).symm.toEquiv
    obtain ⟨s, hs, hsK⟩ := ih (K.map D.subtype) (by rw [hKe]; omega)
      (by rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective])
      (by rw [hKe]; exact hDodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card K))
      ((Subgroup.map_subtype_le _).trans hDSL)
    exact ⟨s, hs, pCoreIn_ne_bot_of_le_normalizer hs (Subgroup.map_subtype_le _)
      (le_normalizer_map_subtype K) hsK⟩

theorem exists_prime_pCore_ne_bot [CharP k p] (hp : p.Prime) {D : Subgroup (GL (Fin 2) k)}
    (hD1 : D ≠ ⊥) (hDodd : Odd (Nat.card D))
    (hDSL : D ≤ (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := k)).range) :
    ∃ r : ℕ, r.Prime ∧ pCore r ↥D ≠ ⊥ := by
  obtain ⟨r, hr, h⟩ := exists_pCoreIn_ne_bot_aux hp (Nat.card ↥D) D le_rfl hD1 hDodd hDSL
  exact ⟨r, hr, (pCoreIn_ne_bot_iff r D).mp h⟩

theorem exists_prime_pCoreIn_ne_bot [CharP k p] (hp : p.Prime) {D : Subgroup (GL (Fin 2) k)}
    (hD1 : D ≠ ⊥) (hDodd : Odd (Nat.card D))
    (hDSL : D ≤ (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := k)).range) :
    ∃ r : ℕ, r.Prime ∧ pCoreIn r D ≠ ⊥ :=
  exists_pCoreIn_ne_bot_aux hp (Nat.card ↥D) D le_rfl hD1 hDodd hDSL

theorem exists_prime_pCore_ne_bot_specialLinearGroup [CharP k p] (hp : p.Prime)
    {D : Subgroup (Matrix.SpecialLinearGroup (Fin 2) k)} (hD1 : D ≠ ⊥)
    (hDodd : Odd (Nat.card D)) : ∃ r : ℕ, r.Prime ∧ pCore r ↥D ≠ ⊥ := by
  have hinj := Matrix.SpecialLinearGroup.toGL_injective (n := Fin 2) (R := k)
  have hcard := Nat.card_congr (Subgroup.equivMapOfInjective D _ hinj).toEquiv
  obtain ⟨r, hr, h⟩ := exists_prime_pCore_ne_bot hp
    (D := D.map (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := k)))
    (by rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hinj]) (by rwa [← hcard])
    (Subgroup.map_le_range _ _)
  exact ⟨r, hr, (pCore_ne_bot_congr r (Subgroup.equivMapOfInjective D _ hinj)).mpr h⟩

theorem exists_prime_pCore_ne_bot_card (hp : p.Prime) (_hf : 1 ≤ f) (hq : q = p ^ f)
    (hcard : Nat.card k = q) {D : Subgroup (GL (Fin 2) k)} (hD1 : D ≠ ⊥)
    (hDodd : Odd (Nat.card D))
    (hDSL : D ≤ (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := k)).range) :
    ∃ r : ℕ, r.Prime ∧ pCore r ↥D ≠ ⊥ :=
  have : CharP k p := charP_of_natCard_eq_prime_pow hp (by rw [hcard, hq])
  exists_prime_pCore_ne_bot hp hD1 hDodd hDSL

end Main

end

end CFSG.FeitThompson

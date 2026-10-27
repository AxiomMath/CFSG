module

public import CFSG.CGT.Timmesfeld75.Sec5ElevenNum
public import CFSG.RankThree.CentralLift.EvenScalarCover
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

@[expose] noncomputable def projectiveSLMulEquivStatedProj (n : ℕ) (K : Type) [Field K] :
    projectiveSL n K ≃* StatedProj (StatedSL n K) :=
  (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K).symm.trans
    (projectiveSpecialLinearGroupEquivStatedProj n K)

@[expose] def centralTorsion {Y : Type*} [Group Y] (Z : Subgroup Y) (hZ : Z ≤ Subgroup.center Y)
    (m : ℕ) : Subgroup Y where
  carrier := {z | z ∈ Z ∧ z ^ m = 1}
  mul_mem' := by
    rintro x y ⟨hx, hxm⟩ ⟨hy, hym⟩
    refine ⟨Z.mul_mem hx hy, ?_⟩
    have hc : Commute x y := Subgroup.mem_center_iff.1 (hZ hy) x
    rw [hc.mul_pow, hxm, hym, one_mul]
  one_mem' := ⟨Z.one_mem, one_pow m⟩
  inv_mem' := by
    rintro x ⟨hx, hxm⟩
    exact ⟨Z.inv_mem hx, by rw [inv_pow, hxm, inv_one]⟩

theorem exists_central_pPrime_subgroup {Y : Type*} [Group Y] [Finite Y] (Z : Subgroup Y)
    (hZ : Z ≤ Subgroup.center Y) (p : ℕ) (hp : p.Prime) :
    ∃ Q : Subgroup Y, Q ≤ Z ∧ ¬ p ∣ Nat.card Q ∧ ∀ z ∈ Z, ∃ k : ℕ, z ^ (p ^ k) ∈ Q := by
  have hN : Nat.card Z ≠ 0 := Nat.card_pos.ne'
  have hcop : Nat.Coprime p (Nat.card Z / p ^ (Nat.card Z).factorization p) :=
    Nat.coprime_ordCompl hp hN
  refine ⟨centralTorsion Z hZ (Nat.card Z / p ^ (Nat.card Z).factorization p),
    fun z hz => hz.1, ?_, ?_⟩
  · intro hpQ
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := centralTorsion Z hZ
      (Nat.card Z / p ^ (Nat.card Z).factorization p)) p hpQ
    have h1 : (z : Y) ^ (Nat.card Z / p ^ (Nat.card Z).factorization p) = 1 := z.2.2
    have hord : orderOf (z : Y) = p := by rw [Subgroup.orderOf_coe]; exact hz
    have h2 : p ∣ Nat.card Z / p ^ (Nat.card Z).factorization p := by
      have h4 := orderOf_dvd_of_pow_eq_one h1
      rwa [hord] at h4
    exact hp.one_lt.ne' (hcop.eq_one_of_dvd h2)
  · intro z hz
    refine ⟨(Nat.card Z).factorization p, Z.pow_mem hz _, ?_⟩
    rw [← pow_mul, Nat.ordProj_mul_ordCompl_eq_self]
    have h3 : (⟨z, hz⟩ : Z) ^ Nat.card Z = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h3

theorem prime_dvd_of_dvd_card_center
    {a s : ℕ} (ha : 2 ≤ a) {Y : Type} [Group Y] [Finite Y]
    (hperf : commutator Y = ⊤) {F : Type} [Field F] (hF : Nat.card F = 2 ^ s)
    (e : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSL a F)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpZ : p ∣ Nat.card (Subgroup.center Y)) : p ∣ a := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQZ, hpQ, hQpow⟩ := exists_central_pPrime_subgroup (Subgroup.center Y) le_rfl p hp
  have hQn : Q.Normal := Subgroup.normal_of_le_center hQZ
  have hperf' : Group.IsPerfect Y := Group.isPerfect_def.2 hperf
  have hQ1 : Group.IsPerfect (Y ⧸ Q) := inferInstance
  let E : Y ⧸ Subgroup.center Y ≃* projectiveSL a F :=
    e.trans (projectiveSLMulEquivStatedProj a F).symm
  let η : Y ⧸ Q →* projectiveSL a F :=
    (E : Y ⧸ Subgroup.center Y →* projectiveSL a F).comp
      (QuotientGroup.map Q (Subgroup.center Y) (MonoidHom.id Y) (fun x hx => hQZ hx))
  have hηmk : ∀ y : Y, η (y : Y ⧸ Q) = E (y : Y ⧸ Subgroup.center Y) := fun y => rfl
  have hη : Function.Surjective η := by
    intro w
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (E.symm w)
    exact ⟨(y : Y ⧸ Q), by rw [hηmk, hy, MulEquiv.apply_symm_apply]⟩
  have hker : ∀ y : Y, η (y : Y ⧸ Q) = 1 ↔ y ∈ Subgroup.center Y := by
    intro y
    rw [hηmk, ← map_one E, E.injective.eq_iff]
    exact QuotientGroup.eq_one_iff y
  have hkerc : η.ker ≤ Subgroup.center (Y ⧸ Q) := by
    intro g hg
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    have hy : y ∈ Subgroup.center Y := (hker y).1 hg
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hy y']
  have hkerp : IsPGroup p η.ker := by
    rintro ⟨g, hg⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨k, hk⟩ := hQpow y ((hker y).1 hg)
    refine ⟨k, Subtype.ext ?_⟩
    change (y : Y ⧸ Q) ^ (p ^ k) = 1
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hk
  have hcover :=
    CFSG.RankThree.CentralLift.even_field_linear_perfect_central_large_prime_scalar_cover
    (L := Y ⧸ Q) hp hp3 hF ha η hη hkerc hkerp
  obtain ⟨⟨φ, hφ, -⟩, hall⟩ := hcover
  have hdvd : Nat.card η.ker ∣ Nat.gcd a (2 ^ s - 1) := (hall φ hφ).2.2.2.2.2.2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Y) p hpZ
  have hzord : orderOf (z : Y) = p := by rw [Subgroup.orderOf_coe]; exact hz
  have hzQ : (z : Y) ∉ Q := fun h => hpQ (hzord ▸ Subgroup.orderOf_dvd_natCard Q h)
  have hzker : ((z : Y) : Y ⧸ Q) ∈ η.ker := (hker z).2 z.2
  have hgord : orderOf ((z : Y) : Y ⧸ Q) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow]
      have : (z : Y) ^ p = 1 := hzord ▸ pow_orderOf_eq_one _
      rw [this]
      exact QuotientGroup.mk_one _
    · intro h
      exact hzQ ((QuotientGroup.eq_one_iff _).1 h)
  have hpker : p ∣ Nat.card η.ker := by
    have := orderOf_dvd_natCard (⟨((z : Y) : Y ⧸ Q), hzker⟩ : η.ker)
    rwa [Subgroup.orderOf_mk, hgord] at this
  exact (Nat.dvd_gcd_iff.1 (hpker.trans hdvd)).1

theorem multPrimeInput :
    MultPrimeInput := by
  intro a s ha _ Y _ _ hperf ⟨F, _, _, hF, ⟨e⟩⟩ p hp hpZ
  by_cases h3 : p ≤ 3
  · exact h3.trans (le_max_right _ _)
  · push Not at h3
    exact (Nat.le_of_dvd (by omega) (prime_dvd_of_dvd_card_center ha hperf hF e hp h3 hpZ)).trans
      (le_max_left _ _)

end CFSG.CGT.Timmesfeld75

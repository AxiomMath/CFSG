module

public import CFSG.Goldschmidt.Steps.G37Quot
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Case1
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsB
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

section Transfer

variable {R : Type} [Group R] [Finite R]

theorem up34_eq_one_of_perfect {A : Type*} [CommGroup A] (hR : Group.IsPerfect R) (f : R →* A)
    (x : R) : f x = 1 := by
  have hx : x ∈ commutator R := by
    rw [Group.isPerfect_def.1 hR]
    exact Subgroup.mem_top x
  exact Abelianization.commutator_subset_ker f hx

theorem up34_eq_one_of_central_pGroup (hR : Group.IsPerfect R) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hN : ¬ ℓ ^ 2 ∣ (Subgroup.center R).index) {z : R} (hz : z ∈ Subgroup.center R) {k : ℕ}
    (hzk : z ^ (ℓ ^ k) = 1) : z = 1 := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hzp : IsPGroup ℓ (Subgroup.zpowers z) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzk, one_zpow]
  obtain ⟨P, hzP⟩ := hzp.exists_le_sylow
  have hzP' : z ∈ (P : Subgroup R) := hzP (Subgroup.mem_zpowers z)
  let f₀ : ↥(P : Subgroup R) →* R ⧸ Subgroup.center R :=
    (QuotientGroup.mk' (Subgroup.center R)).comp (P : Subgroup R).subtype
  let f : ↥(P : Subgroup R) →* ↥f₀.range := f₀.rangeRestrict
  have hpP : IsPGroup ℓ ↥(P : Subgroup R) := P.isPGroup'
  have hpR : IsPGroup ℓ ↥f₀.range := hpP.of_surjective f f₀.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := ℓ) (G := ↥f₀.range)).1 hpR
  have hdvd : Nat.card ↥f₀.range ∣ (Subgroup.center R).index := by
    rw [Subgroup.index_eq_card]
    exact Subgroup.card_subgroup_dvd_card _
  have hn1 : n ≤ 1 := by
    by_contra hcon
    push Not at hcon
    apply hN
    refine dvd_trans (pow_dvd_pow ℓ hcon) ?_
    rw [← hn]
    exact hdvd
  haveI : IsCyclic ↥f₀.range := by
    interval_cases n
    · haveI : Subsingleton ↥f₀.range := by
        rw [pow_zero] at hn
        exact (Nat.card_eq_one_iff_unique.1 hn).1
      exact isCyclic_of_subsingleton
    · rw [pow_one] at hn
      exact isCyclic_of_prime_card hn
  have hker : f.ker ≤ Subgroup.center ↥(P : Subgroup R) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx' : (QuotientGroup.mk (x : R) : R ⧸ Subgroup.center R) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      simpa [f, f₀] using this
    rw [QuotientGroup.eq_one_iff] at hx'
    exact Subtype.ext (Subgroup.mem_center_iff.1 hx' y)
  letI : CommGroup ↥(P : Subgroup R) := commGroupOfCyclicCenterQuotient f hker
  haveI : (P : Subgroup R).FiniteIndex := inferInstance
  let T : R →* ↥(P : Subgroup R) := MonoidHom.transfer (MonoidHom.id ↥(P : Subgroup R))
  have hT1 : T z = 1 := up34_eq_one_of_perfect hR T z
  have hTz : T z = ⟨z ^ (P : Subgroup R).index, _⟩ :=
    MonoidHom.transfer_eq_pow (MonoidHom.id ↥(P : Subgroup R)) z (fun j g₀ _ => by
      have h1 := Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ hz j) g₀⁻¹
      rw [h1, mul_assoc, inv_mul_cancel, mul_one])
  have hpow : z ^ (P : Subgroup R).index = 1 := by
    have := congrArg Subtype.val (hTz.symm.trans hT1)
    simpa using this
  have hcop : Nat.Coprime (ℓ ^ k) (P : Subgroup R).index :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hℓ).2 (Sylow.not_dvd_index P))
  have h1 : orderOf z ∣ ℓ ^ k := orderOf_dvd_of_pow_eq_one hzk
  have h2 : orderOf z ∣ (P : Subgroup R).index := orderOf_dvd_of_pow_eq_one hpow
  have h3 : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact orderOf_eq_one_iff.1 h3

end Transfer

section Orders

variable {R : Type} [Group R] [Finite R]

theorem up34_not_sq_dvd_20160 {ℓ : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) : ¬ ℓ ^ 2 ∣ 20160 := by
  intro h
  have hle : ℓ ^ 2 ≤ 20160 := Nat.le_of_dvd (by norm_num) h
  have hl : ℓ ≤ 141 := by nlinarith
  interval_cases ℓ <;> first | (exfalso; revert hℓ; norm_num; done) | (exfalso; revert h; norm_num; done)

theorem up34_pow_dvd_20160 {ℓ n : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) (h : ℓ ^ n ∣ 20160) :
    ℓ ^ n ≤ 7 := by
  have h2 : Nat.Coprime ℓ 2 := (Nat.coprime_primes hℓ Nat.prime_two).2 (by omega)
  have h3 : Nat.Coprime ℓ 3 := (Nat.coprime_primes hℓ Nat.prime_three).2 (by omega)
  have hc : Nat.Coprime (ℓ ^ n) (2 ^ 6 * 3 ^ 2) :=
    Nat.Coprime.mul_right (Nat.Coprime.pow _ _ h2) (Nat.Coprime.pow _ _ h3)
  have h35 : ℓ ^ n ∣ 35 := by
    have e : (20160 : ℕ) = 35 * (2 ^ 6 * 3 ^ 2) := by norm_num
    rw [e] at h
    exact hc.dvd_of_dvd_mul_right h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hle : ℓ ≤ 35 := le_trans (Nat.le_self_pow hn.ne' ℓ) (Nat.le_of_dvd (by norm_num) h35)
  by_contra hcon
  push Not at hcon
  have hn2 : n < 2 := by
    by_contra hn2
    push Not at hn2
    have : ℓ ^ 2 ∣ 35 := dvd_trans (pow_dvd_pow ℓ hn2) h35
    have h35' : ℓ ^ 2 ≤ 35 := Nat.le_of_dvd (by norm_num) this
    have hl6 : ℓ ≤ 5 := by nlinarith
    have : ℓ = 5 := by omega
    subst this
    norm_num at this
  have : n = 1 := by omega
  subst this
  rw [pow_one] at h35 hcon
  interval_cases ℓ <;> first | (exfalso; revert hℓ; norm_num; done) | (exfalso; revert h35; norm_num; done)

theorem up34_card_le_seven (hR : Group.IsPerfect R)
    (h : IsLThreeFour (R ⧸ Subgroup.center R)) {ℓ : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ)
    {V : Subgroup R} (hV : IsPGroup ℓ V) : Nat.card V ≤ 7 := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hidx : (Subgroup.center R).index = 20160 := by
    rw [Subgroup.index_eq_card]
    exact card_eq_of_isLThreeFour h
  have hN : ¬ ℓ ^ 2 ∣ (Subgroup.center R).index := by
    rw [hidx]
    exact up34_not_sq_dvd_20160 hℓ h5
  let g : ↥V →* R ⧸ Subgroup.center R := (QuotientGroup.mk' (Subgroup.center R)).comp V.subtype
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (x : R) ∈ Subgroup.center R := by
      have : (QuotientGroup.mk (x : R) : R ⧸ Subgroup.center R) = 1 := hx
      exact (QuotientGroup.eq_one_iff _).1 this
    obtain ⟨k, hk⟩ := hV x
    have hk' : (x : R) ^ (ℓ ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    exact Subtype.ext (up34_eq_one_of_central_pGroup hR hℓ hN hx' hk')
  have hdvd : Nat.card V ∣ 20160 := by
    rw [← card_eq_of_isLThreeFour h]
    exact Subgroup.card_dvd_of_injective g hinj
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := ℓ) (G := ↥V)).1 hV
  rw [hn] at hdvd ⊢
  exact up34_pow_dvd_20160 hℓ h5 hdvd

theorem not_isLThreeFour_of_pGroup (hR : Group.IsPerfect R) {ℓ : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ)
    {V : Subgroup R} (hV : IsPGroup ℓ V) (h8 : 8 ≤ Nat.card V) :
    ¬ IsLThreeFour (R ⧸ Subgroup.center R) := fun h =>
  absurd (up34_card_le_seven hR h hℓ h5 hV) (by omega)

end Orders

section Central

theorem isLThreeFour_of_surjective_central {C R : Type*} [Group C] [Group R]
    (hC : Group.IsPerfect C) (f : C →* R) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center C) (h : IsLThreeFour (R ⧸ Subgroup.center R)) :
    IsLThreeFour (C ⧸ Subgroup.center C) := by
  obtain ⟨e⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hC f hf hker
  exact IsLThreeFour.of_mulEquiv e.symm h

theorem not_isLThreeFour_of_surjective_central {C R : Type} [Group C] [Group R] [Finite C]
    (hC : Group.IsPerfect C) (f : C →* R) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center C) {ℓ : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ)
    {V : Subgroup C} (hV : IsPGroup ℓ V) (h8 : 8 ≤ Nat.card V) :
    ¬ IsLThreeFour (R ⧸ Subgroup.center R) := fun h =>
  not_isLThreeFour_of_pGroup hC hℓ h5 hV h8 (isLThreeFour_of_surjective_central hC f hf hker h)

end Central

end CFSG.HardMathSupport.Dickson.Sec6

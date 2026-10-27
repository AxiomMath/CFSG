module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09I133
public import CFSG.Milestones.ASVolI.A3OddFacts
public import CFSG.Goldschmidt.Steps.G3bL2
public import CFSG.GH74.KGroups.PSL2
public import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

instance fact_prime_seven_small : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem lieIndexChar_eq_characteristic (d : TauCeti.LieTypeIndex) :
    CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar d = d.characteristic := by
  cases d <;> simp [CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar]

theorem isChevIndexOfChar_two_of_char {d : TauCeti.LieTypeIndex} (h : d.characteristic = 2) :
    CFSG.HardMathSupport.Solomon.Coordinator.IsChevIndexOfChar 2 d := by
  unfold CFSG.HardMathSupport.Solomon.Coordinator.IsChevIndexOfChar
  split
  · left
    simpa using h
  · left
    simpa using h
  · rw [lieIndexChar_eq_characteristic]
    exact h

theorem ambiguous_two_lie {d : TauCeti.LieTypeIndex} (hv : d.Valid)
    (h : CFSG.Yardstones.Md0ec50421ce4.ambiguousChev 2 (TauCeti.CFSGIndex.lie ⟨d, hv⟩)) :
    (∃ q : TauCeti.PrimePower, d = .A 1 q ∧ q.card = 7) ∨
      (∃ q : TauCeti.PrimePower, d = .twistedA 2 q ∧ q.card = 3) := by
  revert h
  cases d
  case A r q =>
    match r, q with
    | 1, q => exact fun h => Or.elim h (fun h7 => Or.inl ⟨q, rfl, h7.1⟩) (fun h8 => absurd h8.2 (by norm_num))
    | 0, q => exact fun h => False.elim h
    | r + 2, q => exact fun h => False.elim h
  case twistedA r q =>
    match r, q with
    | 2, q => exact fun h => Or.inr ⟨q, rfl, h.1⟩
    | 3, q => exact fun h => absurd h.2 (by norm_num)
    | 0, q => exact fun h => False.elim h
    | 1, q => exact fun h => False.elim h
    | r + 4, q => exact fun h => False.elim h
  all_goals exact fun h => False.elim h

theorem chevTwo_small_cases (S : Type) [Group S] (hch : IsChevSimple 2 S)
    (hnot : ¬ CFSG.HardMathSupport.Solomon.Coordinator.IsChevOfChar 2 S) :
    Nonempty (S ≃* alternatingGroup (Fin 5)) ∨ Nonempty (S ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (S ≃* alternatingGroup (Fin 8)) ∨
      Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 7 1)) := by
  rcases hch with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  ·
    exfalso
    cases i with
    | cyclic p hp => exact hi.elim
    | alternating n h => exact hi.elim
    | lie d =>
      obtain ⟨d1, hv⟩ := d
      have h2 : d1.characteristic = 2 := hi
      exact hnot ⟨⟨d1, hv⟩, isChevIndexOfChar_two_of_char h2, ⟨e⟩⟩
    | sporadic s => exact hi.elim
  · cases i with
    | cyclic p hp => exact hi.elim
    | alternating n h =>
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inl ⟨e⟩
      · exact Or.inr (Or.inl ⟨e⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨e⟩))
    | lie d =>
      obtain ⟨d1, hv⟩ := d
      rcases ambiguous_two_lie hv hi with ⟨q, rfl, h7⟩ | ⟨q, rfl, h3⟩
      ·
        have hM := CFSG.Models.lieModel_A 1 q hv e
        have hsc : CFSG.Open.StatedClassicalModel S CFSG.Open.StatedLieTag.PSL 2 q.p q.exponent :=
          hM.2.resolve_right (fun h => absurd h.1 (by norm_num))
        have hq7 : q.p ^ q.exponent = 7 := (TauCeti.PrimePower.card_def q).symm.trans h7
        haveI : Fact (Nat.Prime q.p) := ⟨q.prime_p⟩
        have hF : Nat.card (GaloisField 7 1) = q.p ^ q.exponent := by
          rw [GaloisField.card 7 1 (by norm_num), pow_one, hq7]
        obtain ⟨e7⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_stated q.p q.exponent
          (F := GaloisField 7 1) q.exponent_pos hF hsc
        exact Or.inr (Or.inr (Or.inr ⟨e7⟩))
      ·
        exfalso
        exact hnot ⟨⟨.twistedA 2 q, hv⟩, Or.inr ⟨rfl, h3⟩, ⟨e⟩⟩
    | sporadic s => exact hi.elim

theorem oddInner_transport {S X : Type} [Group S] [Group X] (e : S ≃* X)
    (hX : ∀ ψ : MulAut X, Odd (orderOf ψ) → ∃ x : X, ψ = MulAut.conj x) :
    ∀ φ : MulAut S, Odd (orderOf φ) → ∃ g : S, φ = MulAut.conj g := by
  intro φ hφ
  have hψ : Odd (orderOf (MulAut.congr e φ)) := by
    rw [MulEquiv.orderOf_eq]
    exact hφ
  obtain ⟨x, hx⟩ := hX _ hψ
  refine ⟨e.symm x, MulEquiv.ext fun s => ?_⟩
  apply e.injective
  have h1 := congrArg (fun ψ : MulAut X => ψ (e s)) hx
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at h1
  simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact h1

theorem oddInner_alt5 : ∀ φ : MulAut (alternatingGroup (Fin 5)), Odd (orderOf φ) →
    ∃ g : alternatingGroup (Fin 5), φ = MulAut.conj g :=
  fun φ hφ => CFSG.ASVolI.burnsideA315x_alt_odd_inner (n := 5) (Or.inl rfl) hφ

theorem oddInner_alt6 : ∀ φ : MulAut (alternatingGroup (Fin 6)), Odd (orderOf φ) →
    ∃ g : alternatingGroup (Fin 6), φ = MulAut.conj g :=
  fun φ hφ => CFSG.ASVolI.burnsideA315x_alt6_odd_inner hφ

theorem oddInner_alt8 : ∀ φ : MulAut (alternatingGroup (Fin 8)), Odd (orderOf φ) →
    ∃ g : alternatingGroup (Fin 8), φ = MulAut.conj g :=
  fun φ hφ => CFSG.ASVolI.burnsideA315x_alt_odd_inner (n := 8) (Or.inr (by norm_num)) hφ

theorem oddInner_psl27 : ∀ φ : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 7 1)),
    Odd (orderOf φ) → ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 7 1),
      φ = MulAut.conj g :=
  fun φ hφ => CFSG.ASVolI.burnsideA315x_psl2_odd_inner (K := GaloisField 7 1) (p := 7) (k := 1)
    (by norm_num) (GaloisField.card 7 1 (by norm_num)) (Or.inl rfl) φ hφ

theorem card_centralizer_dvd_alt {n : ℕ} (t : alternatingGroup (Fin n)) :
    Nat.card (Subgroup.centralizer {t}) ∣
      Nat.card (Subgroup.centralizer {((t : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))}) := by
  rw [← Subgroup.card_map_of_injective (f := (alternatingGroup (Fin n)).subtype)
    (fun a b h => Subtype.ext h)]
  apply Subgroup.card_dvd_of_le
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.1 hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := congrArg (fun y : alternatingGroup (Fin n) => (y : Equiv.Perm (Fin n))) hx'
  simpa using h

theorem involution_cycleType_of_even {n : ℕ} (hn : n ≤ 6) (σ : Equiv.Perm (Fin n))
    (hσ : orderOf σ = 2) (hsign : Equiv.Perm.sign σ = 1) : σ.cycleType = {2, 2} := by
  have hall : ∀ c ∈ σ.cycleType, c = 2 := fun c hc => by
    have h1 : c ∣ 2 := by
      have h := Multiset.dvd_lcm hc
      rwa [Equiv.Perm.lcm_cycleType, hσ] at h
    exact le_antisymm (Nat.le_of_dvd (by norm_num) h1) (Equiv.Perm.two_le_of_mem_cycleType hc)
  obtain ⟨k, hk⟩ : ∃ k, σ.cycleType = Multiset.replicate k 2 :=
    ⟨σ.cycleType.card, Multiset.eq_replicate.2 ⟨rfl, hall⟩⟩
  have hsum := Equiv.Perm.sum_cycleType_le σ
  rw [hk, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  have hsign' := hsign
  rw [Equiv.Perm.sign_of_cycleType, hk, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul] at hsign'
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h0 : σ = 1 := Equiv.Perm.cycleType_eq_zero.1 (by rw [hk, Multiset.replicate_zero])
    rw [h0, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  · exfalso
    revert hsign'
    decide
  · rw [hk]
    rfl
  · exfalso
    revert hsign'
    decide

theorem card_centralizer_two_two_five (σ : Equiv.Perm (Fin 5)) (hc : σ.cycleType = {2, 2}) :
    Nat.card (Subgroup.centralizer {σ}) = 8 := by
  rw [Equiv.Perm.nat_card_centralizer, hc]
  decide

theorem card_centralizer_two_two_six (σ : Equiv.Perm (Fin 6)) (hc : σ.cycleType = {2, 2}) :
    Nat.card (Subgroup.centralizer {σ}) = 16 := by
  rw [Equiv.Perm.nat_card_centralizer, hc]
  decide

theorem hinv_alt5 : ∀ t : alternatingGroup (Fin 5), orderOf t = 2 →
    ∃ j : ℕ, Nat.card (Subgroup.centralizer {t}) = 2 ^ j := by
  intro t ht
  have hσ : orderOf (t : Equiv.Perm (Fin 5)) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hsgn : Equiv.Perm.sign (t : Equiv.Perm (Fin 5)) = 1 := Equiv.Perm.mem_alternatingGroup.1 t.2
  have hc := involution_cycleType_of_even (by norm_num) _ hσ hsgn
  have hd := card_centralizer_dvd_alt t
  rw [card_centralizer_two_two_five _ hc] at hd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show _ ∣ 2 ^ 3 by simpa using hd)
  exact ⟨j, hj⟩

theorem hinv_alt6 : ∀ t : alternatingGroup (Fin 6), orderOf t = 2 →
    ∃ j : ℕ, Nat.card (Subgroup.centralizer {t}) = 2 ^ j := by
  intro t ht
  have hσ : orderOf (t : Equiv.Perm (Fin 6)) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hsgn : Equiv.Perm.sign (t : Equiv.Perm (Fin 6)) = 1 := Equiv.Perm.mem_alternatingGroup.1 t.2
  have hc := involution_cycleType_of_even (by norm_num) _ hσ hsgn
  have hd := card_centralizer_dvd_alt t
  rw [card_centralizer_two_two_six _ hc] at hd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show _ ∣ 2 ^ 4 by simpa using hd)
  exact ⟨j, hj⟩

theorem hinv_psl27 : ∀ t : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 7 1),
    orderOf t = 2 → ∃ j : ℕ, Nat.card (Subgroup.centralizer {t}) = 2 ^ j := by
  intro t ht
  obtain ⟨φ⟩ := (CFSG.Goldschmidt.G3b.centralizer_dihedral_of_mulEquiv (MulEquiv.refl _)
    (by decide) (by norm_num) ht).2 (by norm_num)
  refine ⟨3, ?_⟩
  rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
  norm_num

def CoreStmt (X : Type) [Group X] : Prop :=
  ∀ g : X, Odd (orderOf g) → ∀ R : Subgroup X, IsPGroup 2 R → R ≠ ⊥ →
    twoPart (Nat.card X) ≤ 2 * Nat.card R → (∀ r ∈ R, g * r = r * g) → g = 1

theorem core_of_involution {X : Type} [Group X] [Finite X]
    (hinv : ∀ t : X, orderOf t = 2 → ∃ j : ℕ, Nat.card (Subgroup.centralizer {t}) = 2 ^ j)
    (g : X) (hg : Odd (orderOf g)) (R : Subgroup X) (hR : IsPGroup 2 R) (hRne : R ≠ ⊥)
    (hcomm : ∀ r ∈ R, g * r = r * g) : g = 1 := by
  have hcard : Nat.card R ≠ 1 := fun h => hRne (Subgroup.eq_bot_of_card_eq R h)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hR
  have h2 : 2 ∣ Nat.card R := by
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hcard (by simpa using hn)
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 h2
  have ht : orderOf (x : X) = 2 := (Subgroup.orderOf_coe x).trans hx
  have hgmem : g ∈ Subgroup.centralizer {(x : X)} :=
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm x x.2)
  obtain ⟨j, hj⟩ := hinv (x : X) ht
  have hdvd : orderOf g ∣ 2 ^ j := hj ▸ Subgroup.orderOf_dvd_natCard _ hgmem
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hi0 : i = 0 := by
    rcases Nat.eq_zero_or_pos i with h | h
    · exact h
    · exfalso
      rw [hi] at hg
      exact (Nat.not_even_iff_odd.2 hg) (Nat.even_pow.2 ⟨even_two, h.ne'⟩)
  rw [hi0, pow_zero] at hi
  exact orderOf_eq_one_iff.1 hi

theorem coreStmt_of_equiv {S X : Type} [Group S] [Group X] (e : S ≃* X) (hX : CoreStmt X) :
    CoreStmt S := by
  intro g hg R hR hRne hsize hcomm
  have hcardR : Nat.card (R.map e.toMonoidHom) = Nat.card R :=
    Subgroup.card_map_of_injective e.injective
  have key := hX (e g) (by rwa [MulEquiv.orderOf_eq]) (R.map e.toMonoidHom)
    (hR.map e.toMonoidHom) ?_ ?_ ?_
  · exact e.map_eq_one_iff.1 key
  · intro hbot
    apply hRne
    apply Subgroup.eq_bot_of_card_eq
    rw [← hcardR, hbot, Subgroup.card_bot]
  · rw [hcardR, ← Nat.card_congr e.toEquiv]
    exact hsize
  · rintro _ ⟨r, hr, rfl⟩
    show e g * e r = e r * e g
    rw [← map_mul, ← map_mul, hcomm r hr]

theorem twoPart_two_pow (k : ℕ) : twoPart (2 ^ k) = 2 ^ k := by
  unfold twoPart
  rw [Nat.factorization_pow_self Nat.prime_two]

theorem twoPart_20160 : twoPart 20160 = 64 := by
  have h : (20160 : ℕ) = 2 ^ 6 * 315 := by norm_num
  rw [h, i133_twoPart_mul_of_ne (a := 2 ^ 6) (b := 315) (by positivity) (by norm_num),
    i133_twoPart_eq_one_of_odd (n := 315) ⟨157, by norm_num⟩, mul_one, twoPart_two_pow]
  norm_num

theorem cycleType_of_prime_order {n : ℕ} (σ : Equiv.Perm (Fin n)) {p : ℕ} (hp : p.Prime)
    (hσ : orderOf σ = p) : ∃ k : ℕ, σ.cycleType = Multiset.replicate k p ∧ k * p ≤ n := by
  have hall : ∀ c ∈ σ.cycleType, c = p := fun c hc => by
    have h1 : c ∣ p := by
      have h := Multiset.dvd_lcm hc
      rwa [Equiv.Perm.lcm_cycleType, hσ] at h
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · have := Equiv.Perm.two_le_of_mem_cycleType hc
      omega
    · exact h
  obtain ⟨k, hk⟩ : ∃ k, σ.cycleType = Multiset.replicate k p :=
    ⟨σ.cycleType.card, Multiset.eq_replicate.2 ⟨rfl, hall⟩⟩
  refine ⟨k, hk, ?_⟩
  have hsum := Equiv.Perm.sum_cycleType_le σ
  rw [hk, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  exact hsum

theorem alt8_prime_case (g : alternatingGroup (Fin 8)) {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hord : orderOf g = p) (R : Subgroup (alternatingGroup (Fin 8))) (hR : IsPGroup 2 R)
    (h32 : 32 ≤ Nat.card R) (hcomm : ∀ r ∈ R, g * r = r * g) : False := by
  have hσ : orderOf (g : Equiv.Perm (Fin 8)) = p := (Subgroup.orderOf_coe g).trans hord
  obtain ⟨k, hk, hkp⟩ := cycleType_of_prime_order _ hp hσ
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h0 : (g : Equiv.Perm (Fin 8)) = 1 :=
      Equiv.Perm.cycleType_eq_zero.1 (by rw [hk, Multiset.replicate_zero])
    rw [h0, orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  have hsub : R.map (alternatingGroup (Fin 8)).subtype ≤
      Subgroup.centralizer {(g : Equiv.Perm (Fin 8))} := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (fun y : alternatingGroup (Fin 8) => (y : Equiv.Perm (Fin 8))) (hcomm r hr)
    simp only [Subgroup.coe_mul] at h
    exact h.symm
  have hdvd : Nat.card R ∣ Nat.card (Subgroup.centralizer {(g : Equiv.Perm (Fin 8))}) := by
    have h1 : Nat.card (R.map (alternatingGroup (Fin 8)).subtype) = Nat.card R :=
      Subgroup.card_map_of_injective (fun a b h => Subtype.ext h)
    rw [← h1]
    exact Subgroup.card_dvd_of_le hsub
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hR
  have h32d : 32 ∣ Nat.card R := by
    have ha5 : 5 ≤ a := by
      by_contra hlt
      have hlt' : a < 5 := Nat.lt_of_not_le hlt
      have : 2 ^ a < 2 ^ 5 := Nat.pow_lt_pow_right (by norm_num) hlt'
      omega
    rw [ha]
    exact pow_dvd_pow 2 ha5
  have hd32 : 32 ∣ Nat.card (Subgroup.centralizer {(g : Equiv.Perm (Fin 8))}) := h32d.trans hdvd
  rw [Equiv.Perm.nat_card_centralizer, hk] at hd32
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  have hk8 : k ≤ 8 := le_trans (Nat.le_mul_of_pos_right k hp.pos) hkp
  have hp8 : p ≤ 8 := le_trans (Nat.le_mul_of_pos_left p hk1) hkp
  interval_cases p <;> interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (norm_num at hpodd; done)
    | (revert hd32; decide)

theorem core_alt8 : CoreStmt (alternatingGroup (Fin 8)) := by
  intro g hg R hR hRne hsize hcomm
  have hcardA : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    rfl
  rw [hcardA, twoPart_20160] at hsize
  have h32 : 32 ≤ Nat.card R := by omega
  by_contra hne
  have hg1 : orderOf g ≠ 1 := fun h => hne (orderOf_eq_one_iff.1 h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg1
  have hpodd : Odd p := Odd.of_dvd_nat hg hpd
  exact alt8_prime_case (g ^ (orderOf g / p)) hp hpodd
    (orderOf_pow_orderOf_div (orderOf_pos g).ne' hpd) R hR h32
    (fun r hr => (show Commute g r from hcomm r hr).pow_left (orderOf g / p))

theorem coreStmt_alt5 : CoreStmt (alternatingGroup (Fin 5)) :=
  fun g hg R hR hRne _ hc => core_of_involution hinv_alt5 g hg R hR hRne hc

theorem coreStmt_alt6 : CoreStmt (alternatingGroup (Fin 6)) :=
  fun g hg R hR hRne _ hc => core_of_involution hinv_alt6 g hg R hR hRne hc

theorem coreStmt_psl27 : CoreStmt (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 7 1)) :=
  fun g hg R hR hRne _ hc => by
    haveI : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 7 1)) := inferInstance
    exact core_of_involution hinv_psl27 g hg R hR hRne hc

theorem small_facts {S : Type} [Group S]
    (h : Nonempty (S ≃* alternatingGroup (Fin 5)) ∨ Nonempty (S ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (S ≃* alternatingGroup (Fin 8)) ∨
      Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 7 1))) :
    (∀ φ : MulAut S, Odd (orderOf φ) → ∃ g : S, φ = MulAut.conj g) ∧ CoreStmt S := by
  rcases h with h | h | h | h
  · obtain ⟨e⟩ := h
    exact ⟨oddInner_transport e oddInner_alt5, coreStmt_of_equiv e coreStmt_alt5⟩
  · obtain ⟨e⟩ := h
    exact ⟨oddInner_transport e oddInner_alt6, coreStmt_of_equiv e coreStmt_alt6⟩
  · obtain ⟨e⟩ := h
    exact ⟨oddInner_transport e oddInner_alt8, coreStmt_of_equiv e core_alt8⟩
  · obtain ⟨e⟩ := h
    exact ⟨oddInner_transport e oddInner_psl27, coreStmt_of_equiv e coreStmt_psl27⟩

theorem central_pert_aux {H : Type} [Group H] {z₁ z₂ : H} (h₁ : z₁ ∈ Subgroup.center H)
    (h₂ : z₂ ∈ Subgroup.center H) (a b : H) :
    a * z₁ * (b * z₂) * (a * z₁)⁻¹ * (b * z₂)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have c₁ : ∀ g : H, z₁ * g = g * z₁ := fun g => (Subgroup.mem_center_iff.1 h₁ g).symm
  have c₂ : ∀ g : H, z₂ * g = g * z₂ := fun g => (Subgroup.mem_center_iff.1 h₂ g).symm
  calc a * z₁ * (b * z₂) * (a * z₁)⁻¹ * (b * z₂)⁻¹
      = a * (z₁ * b) * z₂ * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by group
    _ = a * (b * z₁) * z₂ * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by rw [← c₁ b]
    _ = a * b * (z₁ * z₂ * z₁⁻¹) * a⁻¹ * z₂⁻¹ * b⁻¹ := by group
    _ = a * b * z₂ * a⁻¹ * z₂⁻¹ * b⁻¹ := by rw [c₁ z₂, mul_inv_cancel_right]
    _ = a * b * (z₂ * a⁻¹ * z₂⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [c₂ a⁻¹, mul_inv_cancel_right]

theorem aut_eq_one_of_central_pert {H : Type} [Group H] (hperf : commutator H = ⊤) (α : MulAut H)
    (hpert : ∀ a : H, ∃ z ∈ Subgroup.center H, α a = a * z) : α = 1 := by
  let F : Subgroup H :=
    { carrier := {x | α x = x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [map_one]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv, ha] }
  have hcomm_fix : ∀ a b : H, α ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a b
    obtain ⟨z₁, hz₁, ha⟩ := hpert a
    obtain ⟨z₂, hz₂, hb⟩ := hpert b
    rw [commutatorElement_def]
    simp only [map_mul, map_inv]
    rw [ha, hb]
    exact central_pert_aux hz₁ hz₂ a b
  have hFtop : (⊤ : Subgroup H) ≤ F := by
    have h : commutator H ≤ F := Subgroup.commutator_le.2 fun a _ b _ => hcomm_fix a b
    rwa [hperf] at h
  exact MulEquiv.ext fun x => hFtop (Subgroup.mem_top x)

theorem smallChev2Aut_holds : SmallChev2Aut := by
  intro H _ _ hperf hsimple hch hnot hZcop α m hm hαm Q hQp hQne hsize hQfix
  obtain ⟨hodd, hcore⟩ := small_facts (chevTwo_small_cases (H ⧸ Subgroup.center H) hch hnot)
  have hZodd : Odd (Nat.card (Subgroup.center H)) := Nat.coprime_two_right.1 hZcop
  have htwo : twoPart (Nat.card H) = twoPart (Nat.card (H ⧸ Subgroup.center H)) := by
    have h1 : Nat.card (H ⧸ Subgroup.center H) ≠ 0 := Nat.card_pos.ne'
    have h2 : Nat.card (Subgroup.center H) ≠ 0 := Nat.card_pos.ne'
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center H),
      i133_twoPart_mul_of_ne h1 h2, i133_twoPart_eq_one_of_odd hZodd, mul_one]
  have hZS : Subgroup.center (H ⧸ Subgroup.center H) = ⊥ := by
    haveI : Nontrivial (H ⧸ Subgroup.center H) := hsimple.toNontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (H ⧸ Subgroup.center H)) with h | h
    · exact h
    · exfalso
      have hmapT : Subgroup.map (QuotientGroup.mk' (Subgroup.center H)) ⊤ = ⊤ :=
        Subgroup.map_top_of_surjective _ QuotientGroup.mk_surjective
      have hcomm_top : commutator (H ⧸ Subgroup.center H) = ⊤ := by
        have h1 := Subgroup.map_commutator (⊤ : Subgroup H) (⊤ : Subgroup H)
          (QuotientGroup.mk' (Subgroup.center H))
        rw [hmapT] at h1
        have h3 : Subgroup.map (QuotientGroup.mk' (Subgroup.center H)) (commutator H) =
            commutator (H ⧸ Subgroup.center H) := h1
        have h2 : Subgroup.map (QuotientGroup.mk' (Subgroup.center H)) (commutator H) = ⊤ := by
          rw [hperf, hmapT]
        exact h3.symm.trans h2
      have hbot : commutator (H ⧸ Subgroup.center H) = ⊥ :=
        (commutator_eq_bot_iff_center_eq_top (H ⧸ Subgroup.center H)).2 h
      obtain ⟨x, hx⟩ := exists_ne (1 : H ⧸ Subgroup.center H)
      have hxc : x ∈ commutator (H ⧸ Subgroup.center H) := by
        rw [hcomm_top]
        exact Subgroup.mem_top x
      rw [hbot] at hxc
      exact hx (Subgroup.mem_bot.1 hxc)
  have hZα : Subgroup.map (α : H →* H) (Subgroup.center H) = Subgroup.center H :=
    Subgroup.map_center_eq α
  let φ : MulAut (H ⧸ Subgroup.center H) :=
    QuotientGroup.congr (Subgroup.center H) (Subgroup.center H) α hZα
  have hφπ : ∀ x : H, φ (x : H ⧸ Subgroup.center H) = ((α x : H) : H ⧸ Subgroup.center H) :=
    fun x => QuotientGroup.congr_mk _ _ α hZα x
  have hφpow : ∀ k : ℕ, ∀ x : H, (φ ^ k) (x : H ⧸ Subgroup.center H) =
      ((α ^ k) x : H ⧸ Subgroup.center H) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      simp only [pow_succ, MulAut.mul_apply]
      rw [hφπ, ih]
  have hφm : φ ^ m = 1 := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hφpow m x, hαm]
    rfl
  have hφodd : Odd (orderOf φ) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hφm)
  obtain ⟨gb, hgb⟩ := hodd φ hφodd
  have hgbm : gb ^ m = 1 := by
    have h1 : MulAut.conj (gb ^ m) = 1 := by rw [map_pow, ← hgb, hφm]
    have hmem : gb ^ m ∈ Subgroup.center (H ⧸ Subgroup.center H) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h2 := congrArg (fun ψ : MulAut (H ⧸ Subgroup.center H) => ψ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      exact (mul_inv_eq_iff_eq_mul.1 h2).symm
    rw [hZS, Subgroup.mem_bot] at hmem
    exact hmem
  have hgbodd : Odd (orderOf gb) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hgbm)
  have hodd_inter : ∀ a : H, a ∈ Q → a ∈ Subgroup.center H → a = 1 := by
    intro a haQ haZ
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQp
    have h1 : orderOf a ∣ 2 ^ n := by
      rw [← hn]
      exact Subgroup.orderOf_dvd_natCard Q haQ
    have h2 : orderOf a ∣ Nat.card (Subgroup.center H) := Subgroup.orderOf_dvd_natCard _ haZ
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    have hcop : Nat.Coprime (orderOf a) (Nat.card (Subgroup.center H)) := by
      rw [hi]
      exact Nat.Coprime.pow_left i hZcop.symm
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) h2)
  let ψ : Q →* (H ⧸ Subgroup.center H) := (QuotientGroup.mk' (Subgroup.center H)).comp Q.subtype
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have haZ : (a : H) ∈ Subgroup.center H := (QuotientGroup.eq_one_iff (a : H)).1 ha
    exact Subtype.ext (hodd_inter a a.2 haZ)
  let Rbar : Subgroup (H ⧸ Subgroup.center H) := (⊤ : Subgroup Q).map ψ
  have hRbarcard : Nat.card Rbar = Nat.card Q := by
    rw [Subgroup.card_map_of_injective hψinj, Subgroup.card_top]
  have hRbarp : IsPGroup 2 Rbar := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQp
    exact (IsPGroup.iff_card).2 ⟨n, by rw [hRbarcard, hn]⟩
  have hRbarne : Rbar ≠ ⊥ := by
    intro hbot
    apply hQne
    apply Subgroup.eq_bot_of_card_eq
    rw [← hRbarcard, hbot, Subgroup.card_bot]
  have hRbarcomm : ∀ r ∈ Rbar, gb * r = r * gb := by
    rintro _ ⟨y, -, rfl⟩
    have hy : φ ((y : H) : H ⧸ Subgroup.center H) = ((y : H) : H ⧸ Subgroup.center H) := by
      rw [hφπ, hQfix y y.2]
    rw [hgb, MulAut.conj_apply] at hy
    exact mul_inv_eq_iff_eq_mul.1 hy
  have hsizeRbar : twoPart (Nat.card (H ⧸ Subgroup.center H)) ≤ 2 * Nat.card Rbar := by
    rw [hRbarcard, ← htwo]
    exact hsize
  have hgb1 : gb = 1 := hcore gb hgbodd Rbar hRbarp hRbarne hsizeRbar hRbarcomm
  have hφ1 : φ = 1 := by rw [hgb, hgb1, map_one]
  have hαπ : ∀ x : H, ((α x : H) : H ⧸ Subgroup.center H) = (x : H ⧸ Subgroup.center H) := by
    intro x
    rw [← hφπ x, hφ1]
    rfl
  have hαZ : ∀ x : H, (α x)⁻¹ * x ∈ Subgroup.center H := fun x => QuotientGroup.eq.1 (hαπ x)
  have hpert : ∀ a : H, ∃ z ∈ Subgroup.center H, α a = a * z := by
    intro a
    refine ⟨a⁻¹ * α a, ?_, by group⟩
    have h := inv_mem (hαZ a)
    rwa [mul_inv_rev, inv_inv] at h
  exact aut_eq_one_of_central_pert hperf α hpert

end CFSG.LocalAnalysis.GLTheoremA

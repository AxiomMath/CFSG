module

public import CFSG.LocalAnalysis.GLTheoremA.S3.KData
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldAut3
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldFixed
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import Certificates.Data.A5

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

private theorem kdamb_isSolvable_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : Group.IsSolvable H) : Group.IsSolvable G :=
  Group.isSolvable_of_isSolvable_injective (f := (e : G →* H)) e.injective

private theorem kdamb_solvable_transport {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {p : ℕ}
    (h : ∀ α : MulAut S, α ^ p = 1 → α ≠ 1 → Group.IsSolvable ↥(fixSubgroup α)) :
    ∀ α' : MulAut S', α' ^ p = 1 → α' ≠ 1 → Group.IsSolvable ↥(fixSubgroup α') := by
  intro α' hα' hα1'
  have hα : MulAut.congr e.symm α' ^ p = 1 := by
    rw [← map_pow, hα', map_one]
  have hα1 : MulAut.congr e.symm α' ≠ 1 := fun h1 =>
    hα1' ((MulAut.congr e.symm).injective (h1.trans (map_one _).symm))
  have hfix : fixSubgroup (MulAut.congr e.symm α') =
      (fixSubgroup α').map e.symm.toMonoidHom := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      have hx' : e.symm (α' (e x)) = x := hx
      refine ⟨e x, ?_, by simp⟩
      have h4 := congrArg e hx'
      exact mem_fixSubgroup.2 (by simpa using h4)
    · rintro ⟨y, hy, rfl⟩
      show e.symm (α' (e (e.symm y))) = e.symm y
      have hy' : α' y = y := hy
      simp [hy']
  have hsolv := h _ hα hα1
  rw [hfix] at hsolv
  exact kdamb_isSolvable_of_mulEquiv
    (Subgroup.equivMapOfInjective _ e.symm.toMonoidHom e.symm.injective) hsolv

private theorem kdamb_prime_dvd_360 {r : ℕ} (hr : r.Prime) (h : r ∣ 360) :
    r = 2 ∨ r = 3 ∨ r = 5 := by
  have h' : r ∣ 2 ^ 3 * 3 ^ 2 * 5 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hr).1 h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1
        (hr.dvd_of_dvd_pow h2)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h1))

private theorem kdamb_primeFactors_le_two {m q : ℕ} (hm : m ∣ 360) (hq35 : q = 3 ∨ q = 5)
    (hnd : ¬ q ∣ m) : m.primeFactors.card ≤ 2 := by
  have hsub : m.primeFactors ⊆ ({2, 3, 5} : Finset ℕ).erase q := by
    intro r hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrm : r ∣ m := Nat.dvd_of_mem_primeFactors hr
    rw [Finset.mem_erase]
    refine ⟨fun hrq => hnd (hrq ▸ hrm), ?_⟩
    rcases kdamb_prime_dvd_360 hrp (hrm.trans hm) with h | h | h <;> simp [h]
  refine (Finset.card_le_card hsub).trans ?_
  rcases hq35 with rfl | rfl <;> decide

private theorem kdamb_centralizer_solvable {G : Type} [Group G] [Finite G] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p * q = 15) (hq35 : q = 3 ∨ q = 5)
    (hcard : Nat.card G ∣ 360) (hno : ∀ x : G, orderOf x ≠ 15) (g : G) (hgp : g ^ p = 1)
    (hg1 : g ≠ 1) : Group.IsSolvable ↥(Subgroup.centralizer ({g} : Set G)) := by
  haveI := Fact.mk hp
  have hord : orderOf g = p := orderOf_eq_prime hgp hg1
  have hpq' : p ≠ q := by rcases hq35 with rfl | rfl <;> omega
  have hnd : ¬ q ∣ Nat.card (Subgroup.centralizer ({g} : Set G)) := by
    intro hdvd
    haveI := Fact.mk hq
    obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' q hdvd
    have hcomm : Commute g (h : G) := by
      have hmem : (h : G) ∈ Subgroup.centralizer ({g} : Set G) := h.2
      rw [Subgroup.mem_centralizer_iff] at hmem
      exact hmem g (Set.mem_singleton g)
    have hordh : orderOf (h : G) = q := by rw [Subgroup.orderOf_coe, hh]
    have hco : (orderOf g).Coprime (orderOf (h : G)) := by
      rw [hord, hordh]
      exact (Nat.coprime_primes hp hq).2 hpq'
    have hx : orderOf (g * (h : G)) = 15 := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco, hord, hordh, hpq]
    exact hno _ hx
  exact CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    (kdamb_primeFactors_le_two ((Subgroup.card_subgroup_dvd_card _).trans hcard) hq35 hnd)

private theorem kdamb_conj_of_pow {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card (Outer G)) (α : MulAut G) (hα : α ^ p = 1) :
    ∃ g : G, MulAut.conj g = α := by
  let π : MulAut G →* Outer G := QuotientGroup.mk' (inner G)
  have hp' : π α ^ p = 1 := by
    rw [← map_pow, hα, map_one]
  have hord : orderOf (π α) ∣ p := orderOf_dvd_of_pow_eq_one hp'
  have hdvd : orderOf (π α) ∣ Nat.card (Outer G) := orderOf_dvd_natCard _
  have hmem : α ∈ inner G := by
    rcases (Nat.dvd_prime hp).1 hord with h1 | h1
    · exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h1)
    · exact absurd (h1 ▸ hdvd) h
  obtain ⟨g, hg⟩ := hmem
  exact ⟨g, hg⟩

private theorem kdamb_gen {G : Type} [Group G] [Finite G] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p * q = 15) (hq35 : q = 3 ∨ q = 5)
    (hcard : Nat.card G ∣ 360) (hout : ¬ p ∣ Nat.card (Outer G))
    (hz : Subgroup.center G = ⊥) (hno : ∀ x : G, orderOf x ≠ 15)
    (α : MulAut G) (hα : α ^ p = 1) (hα1 : α ≠ 1) :
    Group.IsSolvable ↥(fixSubgroup α) := by
  obtain ⟨g, rfl⟩ := kdamb_conj_of_pow hp hout α hα
  have hgp : g ^ p = 1 := by
    have h1 : MulAut.conj (g ^ p) = 1 := by
      rw [map_pow]
      exact hα
    have h2 : g ^ p ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro h
      have h3 := congrArg (fun φ : MulAut G => φ h) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      exact (mul_inv_eq_iff_eq_mul.1 h3).symm
    rw [hz, Subgroup.mem_bot] at h2
    exact h2
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hα1 (by rw [map_one])
  have hfix : fixSubgroup (MulAut.conj g) = Subgroup.centralizer ({g} : Set G) := by
    ext x
    rw [mem_fixSubgroup, Subgroup.mem_centralizer_iff]
    simp only [MulAut.conj_apply, Set.mem_singleton_iff, forall_eq]
    exact mul_inv_eq_iff_eq_mul
  rw [hfix]
  exact kdamb_centralizer_solvable hp hq hpq hq35 hcard hno g hgp hg1

private theorem kdamb_perm5 : ∀ σ : Equiv.Perm (Fin 5), σ ^ 15 = 1 → σ ^ 3 = 1 ∨ σ ^ 5 = 1 := by
  decide +kernel

private theorem kdamb_perm6 : ∀ σ : Equiv.Perm (Fin 6), σ ^ 15 = 1 → σ ^ 3 = 1 ∨ σ ^ 5 = 1 := by
  decide +kernel

private theorem kdamb_alt_no15 {n : ℕ} (hn : n = 5 ∨ n = 6) (x : alternatingGroup (Fin n)) :
    orderOf x ≠ 15 := by
  intro h15
  have h1 : x ^ 15 = 1 := by
    rw [← h15]
    exact pow_orderOf_eq_one x
  have h2 : (x : Equiv.Perm (Fin n)) ^ 15 = 1 := by
    rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  have key : (x : Equiv.Perm (Fin n)) ^ 3 = 1 ∨ (x : Equiv.Perm (Fin n)) ^ 5 = 1 := by
    rcases hn with rfl | rfl
    · exact kdamb_perm5 _ h2
    · exact kdamb_perm6 _ h2
  rcases key with h3 | h5
  · have h3' : x ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h3, Subgroup.coe_one])
    have hd := orderOf_dvd_of_pow_eq_one h3'
    rw [h15] at hd
    norm_num at hd
  · have h5' : x ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h5, Subgroup.coe_one])
    have hd := orderOf_dvd_of_pow_eq_one h5'
    rw [h15] at hd
    norm_num at hd

private theorem kdamb_card_alt {n : ℕ} (hn : n = 5 ∨ n = 6) :
    Nat.card (alternatingGroup (Fin n)) ∣ 360 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rcases hn with rfl | rfl <;> norm_num [Nat.factorial]

private theorem kdamb_center_alt {n : ℕ} (hn : n = 5 ∨ n = 6) :
    Subgroup.center (alternatingGroup (Fin n)) = ⊥ := by
  apply alternatingGroup.center_eq_bot
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

private theorem kdamb_outer_alt {n p : ℕ} (hn : 5 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer (alternatingGroup (Fin n))) :=
  CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn p hp hp2

private theorem kdamb_card_L2_two {F₀ : Type} [Field F₀] [Finite F₀] (h2 : Nat.card F₀ = 2) :
    Nat.card (StatedProj (StatedSL 2 F₀)) = 6 := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F₀) (n := 2)
    (by norm_num), h2]
  norm_num

private theorem kdamb_isSolvable_of_card_six {G : Type*} [Group G] [Finite G]
    (h : Nat.card G = 6) : Group.IsSolvable G := by
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  rw [h, show (6 : ℕ) = 2 * 3 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
  decide

private theorem kdamb_l2_solvable (F : Type) [Field F] [Finite F] (hF8 : Nat.card F = 8)
    (α : MulAut (StatedProj (StatedSL 2 F))) (hα : α ^ 3 = 1) (hα1 : α ≠ 1) :
    Group.IsSolvable ↥(fixSubgroup α) := by
  rcases CFSG.HardMathSupport.Solomon.Coordinator.l2Aut3Classification_holds F α hα with
    h | h | ⟨σ, φ, γ, hφ, hβ⟩
  · exact absurd h hα1
  · exact h
  · obtain ⟨F₀, _, _, hcard, ⟨ψ⟩⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.l2FieldFixed_holds F α hα hα1 σ φ γ hφ hβ
    have h8 : Nat.card F₀ ^ 3 = 2 ^ 3 := by
      rw [← hcard, hF8]
      norm_num
    have h2 : Nat.card F₀ = 2 := Nat.pow_left_injective (n := 3) (by norm_num) h8
    have ψ' : ↥(fixSubgroup α) ≃* StatedProj (StatedSL 2 F₀) := ψ
    exact kdamb_isSolvable_of_card_six ((Nat.card_congr ψ'.toEquiv).trans (kdamb_card_L2_two h2))

private theorem kdamb_lie_l2 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) (hq8 : q.card = 8) :
    ∀ α : MulAut (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group, α ^ 3 = 1 → α ≠ 1 →
      Group.IsSolvable ↥(fixSubgroup α) := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card q.p q.exponent q.exponent_pos.ne'
  have e : StatedProj (StatedSL 2 (GaloisField q.p q.exponent)) ≃*
      (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group :=
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      (GaloisField q.p q.exponent)).symm.trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv).symm
  exact kdamb_solvable_transport e (fun α hα hα1 =>
    kdamb_l2_solvable (GaloisField q.p q.exponent) (hK.trans hq8) α hα hα1)

theorem kdAmbSolv_holds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hU42 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid),
      q.card = 2 → ∀ α : MulAut (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group,
        α ^ 3 = 1 → α ≠ 1 → IsSolvable ↥(fixSubgroup α)) :
    KDAmbSolv p := by
  intro i hi α hα hα1
  cases i with
  | cyclic r hr => simp [ambiguousChev] at hi
  | alternating n hn =>
    simp only [ambiguousChev] at hi
    rcases hi with ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩ | ⟨rfl, h⟩
    · exact absurd h hp2
    · subst h
      exact kdamb_gen (p := 5) (q := 3) (by norm_num) (by norm_num) (by norm_num) (Or.inl rfl)
        (kdamb_card_alt (Or.inl rfl)) (kdamb_outer_alt (by norm_num) (by norm_num) (by norm_num))
        (kdamb_center_alt (Or.inl rfl)) (kdamb_alt_no15 (Or.inl rfl)) α hα hα1
    · exact absurd h hp2
    · subst h
      exact kdamb_gen (p := 3) (q := 5) (by norm_num) (by norm_num) (by norm_num) (Or.inr rfl)
        (kdamb_card_alt (Or.inr rfl)) (kdamb_outer_alt (by norm_num) (by norm_num) (by norm_num))
        (kdamb_center_alt (Or.inr rfl)) (kdamb_alt_no15 (Or.inr rfl)) α hα hα1
    · exact absurd h hp2
  | lie d =>
    obtain ⟨ld, hv⟩ := d
    cases ld
    case A r q =>
      rcases r with _ | _ | r
      · simp [ambiguousChev] at hi
      · simp only [ambiguousChev] at hi
        rcases hi with ⟨-, h2⟩ | ⟨hq8, h3⟩
        · exact absurd h2 hp2
        · subst h3
          exact kdamb_lie_l2 q hv hq8 α hα hα1
      · simp [ambiguousChev] at hi
    case twistedA r q =>
      rcases r with _ | _ | _ | _ | r
      · simp [ambiguousChev] at hi
      · simp [ambiguousChev] at hi
      · simp only [ambiguousChev] at hi
        exact absurd hi.2 hp2
      · simp only [ambiguousChev] at hi
        obtain ⟨hq2, h3⟩ := hi
        subst h3
        exact hU42 q hv hq2 α hα hα1
      · simp [ambiguousChev] at hi
    all_goals simp [ambiguousChev] at hi
  | sporadic s => simp [ambiguousChev] at hi

end CFSG.LocalAnalysis.GLTheoremA

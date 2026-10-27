module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142CMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Abs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142M.Ambig

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.I142C
open CFSG.LocalAnalysis.GLTheoremA.AltDown CFSG.LocalAnalysis.GLTheoremA.I142
open scoped commutatorElement

theorem isSolvable_of_card_dvd_pow_mul_pow {P : Type*} [Group P] [Finite P] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card P ∣ p ^ a * q ^ b) :
    Group.IsSolvable P := by
  obtain ⟨x, y, hx, hy, hxy⟩ := Nat.dvd_mul.1 h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hx
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hq).1 hy
  haveI : Fintype P := Fintype.ofFinite P
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card, ← hxy])

theorem card_eq_sixty_of_perfect {P : Type*} [Group P] [Finite P] [Nontrivial P]
    [Group.IsPerfect P] (h : Nat.card P ∣ 60) : Nat.card P = 60 := by
  have hcases : Nat.card P ∣ 30 ∨ Nat.card P ∣ 2 ^ 2 * 3 ^ 1 ∨ Nat.card P ∣ 2 ^ 2 * 5 ^ 1 ∨
      Nat.card P = 60 := by
    have hle : Nat.card P ≤ 60 := Nat.le_of_dvd (by norm_num) h
    generalize Nat.card P = n at h hle ⊢
    interval_cases n <;> omega
  rcases hcases with h30 | h12 | h20 | h60
  · exact (false_of_perfect_card_dvd (by norm_num) h30).elim
  · exact absurd (isSolvable_of_card_dvd_pow_mul_pow Nat.prime_two Nat.prime_three (by norm_num) h12)
      (Group.IsPerfect.not_isSolvable P)
  · exact absurd (isSolvable_of_card_dvd_pow_mul_pow Nat.prime_two Nat.prime_five (by norm_num) h20)
      (Group.IsPerfect.not_isSolvable P)
  · exact h60

theorem perfect_eq_bot_of_card_168 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hc : Nat.card S = 168) {β : MulAut S} (hβ : β ≠ 1) {P : Subgroup S}
    (hP : P ≤ fixSubgroup β) (hperf : ⁅P, P⁆ = P) : P = ⊥ := by
  have hCtop : fixSubgroup β ≠ ⊤ := by
    intro htop
    apply hβ
    refine MulEquiv.ext fun x => ?_
    have hx : x ∈ fixSubgroup β := by rw [htop]; exact Subgroup.mem_top x
    rw [MulAut.one_apply]
    exact mem_fixSubgroup.1 hx
  have hPtop : P ≠ ⊤ := fun h => hCtop (top_le_iff.1 (h ▸ hP))
  by_contra hPne
  haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).2 hPne
  haveI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hperf
  have hidx : P.index ≠ 1 := fun h => hPtop (Subgroup.index_eq_one.1 h)
  have hmul := Subgroup.card_mul_index P
  rw [hc] at hmul
  have hdvd : Nat.card ↥P ∣ 168 := ⟨P.index, hmul.symm⟩
  have h168 : Nat.card ↥P ≠ 168 := by
    intro h
    rw [h] at hmul
    have : P.index = 1 := by omega
    exact hidx this
  have h84 : Nat.card ↥P ≠ 84 := by
    intro h
    rw [h] at hmul
    have h2 : P.index = 2 := by omega
    haveI : P.Normal := Subgroup.normal_of_index_eq_two h2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h' | h'
    · exact hPne h'
    · exact hPtop h'
  exact Group.IsPerfect.not_isSolvable ↥P (solvable_of_card_dvd_168 hdvd h84 h168)

theorem perfect_eq_bot_of_order_seven {S : Type} [Group S] [Finite S] (hc : Nat.card S = 6048)
    {x : S} (hx7 : orderOf x = 7) {P : Subgroup S}
    (hP : P ≤ Subgroup.centralizer ({x} : Set S)) (hperf : ⁅P, P⁆ = P) : P = ⊥ := by
  by_contra hne
  haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).2 hne
  haveI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hperf
  set C := Subgroup.centralizer ({x} : Set S) with hCdef
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  set x' : ↥C := ⟨x, hxC⟩ with hx'
  set N : Subgroup ↥C := Subgroup.zpowers x' with hN
  have hNc : N ≤ Subgroup.center ↥C := by
    rw [hN, Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  haveI hNn : N.Normal := ⟨fun n hn g => by
    have hcn := Subgroup.mem_center_iff.1 (hNc hn) g
    rw [hcn, mul_inv_cancel_right]
    exact hn⟩
  haveI : Group.IsSolvable ↥N := isSolvable_of_comm fun a b =>
    Subtype.ext ((Subgroup.mem_center_iff.1 (hNc b.2)) a)
  have hN7 : Nat.card ↥N = 7 := by
    rw [hN, Nat.card_zpowers, ← Subgroup.orderOf_coe]
    exact hx7
  have hCdvd : Nat.card ↥C ∣ 6048 := hc ▸ Subgroup.card_subgroup_dvd_card C
  have hQ : Nat.card (↥C ⧸ N) ∣ 2 ^ 5 * 3 ^ 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hN7] at h
    rw [h] at hCdvd
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 7) (by simpa using hCdvd)
  haveI : Group.IsSolvable (↥C ⧸ N) :=
    isSolvable_of_card_dvd_pow_mul_pow Nat.prime_two Nat.prime_three (by norm_num) hQ
  haveI : Group.IsSolvable ↥C := solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  exact Group.IsPerfect.not_isSolvable ↥P
    (solvable_of_solvable_injective (Subgroup.inclusion_injective hP))

theorem perfect_alt_equiv_alt5 {S : Type} [Group S] (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 8)
    (e : S ≃* alternatingGroup (Fin n)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {x : S}
    (hx : x ^ q = 1) (hx1 : x ≠ 1) {K : Subgroup S}
    (hKC : K ≤ Subgroup.centralizer ({x} : Set S)) (hperf : ⁅K, K⁆ = K) (hne : K ≠ ⊥) :
    Nonempty (↥K ≃* alternatingGroup (Fin 5)) := by
  set y : alternatingGroup (Fin n) := e x with hy
  set L : Subgroup (alternatingGroup (Fin n)) := K.map e.toMonoidHom with hL
  have hLC : L ≤ Subgroup.centralizer {y} := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 (hKC hk)
    simp only [MulEquiv.coe_toMonoidHom, hy]
    rw [← map_mul, ← map_mul, h]
  have hLperf : ⁅L, L⁆ = L := by rw [hL, ← Subgroup.map_commutator, hperf]
  have hLne : L ≠ ⊥ := fun h => hne ((Subgroup.map_eq_bot_iff_of_injective K e.injective).1 h)
  have hKL : Nonempty (↥K ≃* ↥L) := ⟨K.equivMapOfInjective e.toMonoidHom e.injective⟩
  have hyq : y ^ q = 1 := by rw [hy, ← map_pow, hx, map_one]
  have hy1 : y ≠ 1 := fun h => hx1 (e.injective (by rw [← hy, h, map_one]))
  have hσq : (y : Equiv.Perm (Fin n)) ^ q = 1 := by simpa using congrArg Subtype.val hyq
  have hσ1 : (y : Equiv.Perm (Fin n)) ≠ 1 := fun h => hy1 (Subtype.ext h)
  haveI : Fact q.Prime := ⟨hq⟩
  have hord : orderOf (y : Equiv.Perm (Fin n)) = q := orderOf_eq_prime hσq hσ1
  obtain ⟨k, hk, hkn⟩ := cq_cycleType_of_prime_order (y : Equiv.Perm (Fin n)) hq hord
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      apply hσ1
      rw [h0] at hk
      exact Equiv.Perm.cycleType_eq_zero.1 (by rw [hk]; rfl)
    · exact h0
  haveI : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).2 hLne
  haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hLperf
  by_cases hspec : n = 8 ∧ q = 3 ∧ k = 1
  · obtain ⟨rfl, rfl, rfl⟩ := hspec
    have hσ : (y : Equiv.Perm (Fin 8)).cycleType = {3} := by simpa using hk
    set σ : Equiv.Perm (Fin 8) := (y : Equiv.Perm (Fin 8)) with hσdef
    have hcyc : σ.IsCycle := Equiv.Perm.card_cycleType_eq_one.1 (by rw [hσ]; rfl)
    have hfac : σ.cycleFactorsFinset = {σ} := hcyc.cycleFactorsFinset_eq_singleton
    have hcomm : ∀ a ∈ L, Commute (a : Equiv.Perm (Fin 8)) σ := fun a ha =>
      cq_commute_coe (Subgroup.mem_centralizer_singleton_iff.1 (hLC ha))
    have hLF : L ≤ (alternatingGroup.ofSubtype σ.supportᶜ).range := by
      calc L = ⁅L, L⁆ := hLperf.symm
        _ ≤ _ := by
          refine Subgroup.commutator_le.2 fun a ha b hb => ?_
          rw [mem_range_ofSubtype_compl_iff]
          intro u hu
          have h := commutator_apply_of_mem_support (hcomm a ha) (hcomm b hb)
            (fun c hc => by rw [hfac, Finset.mem_singleton] at hc; rw [hc]; exact hcomm a ha)
            (fun c hc => by rw [hfac, Finset.mem_singleton] at hc; rw [hc]; exact hcomm b hb) hu
          simpa [commutatorElement_def] using h
    have hcard5 : (σ.supportᶜ).card = 5 := by
      have h1 : σ.support.card = 3 := by rw [← Equiv.Perm.sum_cycleType, hσ]; rfl
      rw [Finset.card_compl, h1]
      simp
    obtain ⟨e5⟩ := nonempty_range_ofSubtype_equiv σ.supportᶜ 5 hcard5
    have hF60 : Nat.card ↥(alternatingGroup.ofSubtype σ.supportᶜ).range = 60 := by
      rw [Nat.card_congr e5.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    have h60 : Nat.card ↥L = 60 :=
      card_eq_sixty_of_perfect (hF60 ▸ Subgroup.card_dvd_of_le hLF)
    have hLeq : L = (alternatingGroup.ofSubtype σ.supportᶜ).range :=
      Subgroup.eq_of_le_of_card_ge hLF (by rw [h60, hF60])
    obtain ⟨eKL⟩ := hKL
    exact ⟨eKL.trans ((MulEquiv.subgroupCongr hLeq).trans e5)⟩
  · exfalso
    have hdiv : Nat.card L ∣ (n - k * q).factorial * q ^ k * k.factorial := by
      rw [← cq_card_centralizer_replicate (y : Equiv.Perm (Fin n)) hk1 hk]
      exact (Subgroup.card_dvd_of_le hLC).trans (cq_card_centralizer_dvd_alt y)
    have hq3 : 3 ≤ q := by
      have := hq.two_le
      omega
    have hqn : q ≤ n := by nlinarith
    have hq357 : q = 3 ∨ q = 5 ∨ q = 7 := by
      have hq8 : q ≤ 8 := by rcases hn with rfl | rfl | rfl <;> omega
      interval_cases q <;> first | omega | (exfalso; revert hq; norm_num)
    have hkle : k ≤ 2 := by rcases hq357 with rfl | rfl | rfl <;> omega
    rcases hn with rfl | rfl | rfl <;> rcases hq357 with rfl | rfl | rfl <;> interval_cases k <;>
      first
        | omega
        | (norm_num [Nat.factorial] at hdiv
           exact false_of_perfect_card_dvd (by norm_num) hdiv)

theorem isChevSimple_two_of_equiv_alt5 {H : Type} [Group H] (e : H ≃* alternatingGroup (Fin 5)) :
    IsChevSimple 2 (H ⧸ Subgroup.center H) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  haveI : IsSimpleGroup H := e.isSimpleGroup
  have hA5 : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
    refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, ?_⟩, ⟨Equiv.swap 0 1 * Equiv.swap 2 3, ?_⟩, ?_⟩
    · exact Equiv.Perm.mem_alternatingGroup.2 (by decide)
    · exact Equiv.Perm.mem_alternatingGroup.2 (by decide)
    · intro h
      have := congrArg Subtype.val h
      revert this
      decide
  have hnc : ∃ a b : H, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hA5
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hZ : Subgroup.center H = ⊥ := b3Lie_center_eq_bot hnc
  refine Or.inr ⟨TauCeti.CFSGIndex.alternating 5 (by norm_num), by simp [ambiguousChev], ?_⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩

@[expose] def ChevCompTypesAmbig : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    catalogIs S (ambiguousChev 2) → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 →
      ∀ K : Subgroup S, IsComponentOf K (centFix (Subgroup.zpowers β)) →
        IsChevSimple 2 (↥K ⧸ Subgroup.center ↥K)

section Cert


theorem chevCompTypesAmbig_holds : ChevCompTypesAmbig := by
  intro S _ _ hS hnc hamb p hp hp2 β hβ hβ1 K hK
  haveI := hS
  rw [centFix_zpowers'] at hK
  have hz : Subgroup.center S = ⊥ := b3Lie_center_eq_bot hnc
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 ⟨hK.2.2.1⟩
  have hKnt : Nontrivial ↥K := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    haveI := h
    have := hK.2.2.2.toNontrivial
    exact (not_subsingleton_iff_nontrivial.2 this) inferInstance
  have hKne : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 hKnt
  obtain ⟨i, hi, ⟨e⟩⟩ := hamb
  cases i with
  | cyclic p' hp' => simp [ambiguousChev] at hi
  | sporadic s => simp [ambiguousChev] at hi
  | alternating n h =>
    have hn : n = 5 ∨ n = 6 ∨ n = 8 := by
      simp [ambiguousChev] at hi
      omega
    have hn5 : 5 ≤ n := by omega
    have e' : S ≃* alternatingGroup (Fin n) := e
    have hO : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) := by
      rw [Nat.card_congr
        (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
      exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 p hp hp2
    obtain ⟨x, rfl⟩ := exists_conj_of_pow_eq_one hp hO hβ
    have hxp : x ^ p = 1 :=
      conj_injective_of_center hz (by rw [map_pow, map_one]; exact hβ)
    have hx1 : x ≠ 1 := fun h => hβ1 (by rw [h, map_one])
    have hKC := hK.1
    rw [fixSubgroup_conj_eq_centralizer'] at hKC
    obtain ⟨e5⟩ := perfect_alt_equiv_alt5 n hn e' hp hp2 hxp hx1 hKC hKperf hKne
    exact isChevSimple_two_of_equiv_alt5 e5
  | lie d =>
    exfalso
    obtain ⟨d1, hv⟩ := d
    rcases chev2_lie_cases d1 hv hi with ⟨q, rfl, hq7⟩ | ⟨q, rfl, hq3⟩
    · have hcard : Nat.card S = 168 := by
        obtain ⟨hq7p, he1⟩ := primePower_eq_of_card (by norm_num : Nat.Prime 7) hq7
        obtain ⟨-, hSCor⟩ := CFSG.Models.lieModel_A 1 q hv e
        rcases hSCor with hSC | ⟨h0, -⟩
        · rw [hq7p, he1] at hSC
          exact CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven hSC
        · exact absurd h0 (by norm_num)
      exact hKne (perfect_eq_bot_of_card_168 hcard hβ1 hK.1 hKperf)
    · obtain ⟨hcard, hidx, h7⟩ := u33_data hS hnc q hv hq3 e
      have hO : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) := by
        change ¬ p ∣ (MulAut.conj : S →* MulAut S).range.index
        have hne : (MulAut.conj : S →* MulAut S).range.index ≠ 0 :=
          Subgroup.index_ne_zero_of_finite
        intro hpd
        have hle : (MulAut.conj : S →* MulAut S).range.index = 1 ∨
            (MulAut.conj : S →* MulAut S).range.index = 2 := by
          omega
        rcases hle with h | h <;> rw [h] at hpd
        · exact hp.one_lt.ne' (Nat.dvd_one.1 hpd)
        · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hpd)
      obtain ⟨x, rfl⟩ := exists_conj_of_pow_eq_one hp hO hβ
      have hxp : x ^ p = 1 :=
        conj_injective_of_center hz (by rw [map_pow, map_one]; exact hβ)
      have hx1 : x ≠ 1 := fun h => hβ1 (by rw [h, map_one])
      haveI : Fact p.Prime := ⟨hp⟩
      have hord : orderOf x = p := orderOf_eq_prime hxp hx1
      have hpd : p ∣ 2 ^ 5 * 3 ^ 3 * 7 := by
        have := orderOf_dvd_natCard x
        rw [hord, hcard] at this
        simpa using this
      have hKC := hK.1
      rw [fixSubgroup_conj_eq_centralizer'] at hKC
      rcases (Nat.Prime.dvd_mul hp).1 hpd with h23 | h7'
      · rcases (Nat.Prime.dvd_mul hp).1 h23 with h2 | h3
        · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
        · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
          subst hp3
          exact hKne (perfect_eq_bot_of_not_seven hcard (h7 x hxp hx1) hKC hKperf)
      · have hp7 : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7'
        subst hp7
        exact hKne (perfect_eq_bot_of_order_seven hcard hord hKC hKperf)

theorem chevCompTypesAmbig_holds' :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      catalogIs S (ambiguousChev 2) → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ β : MulAut S, β ^ p = 1 →
        β ≠ 1 → ∀ K : Subgroup S, IsComponentOf K (centFix (Subgroup.zpowers β)) →
          IsChevSimple 2 (↥K ⧸ Subgroup.center ↥K) :=
  chevCompTypesAmbig_holds

end Cert

end CFSG.LocalAnalysis.GLTheoremA.I142M.Ambig

module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt
public import CFSG.LocalAnalysis.AGLEmbedding.AltAlpha
import CFSG.LocalAnalysis.AGLEmbedding.AltCaseThreeKAux
import CFSG.LocalAnalysis.AGLEmbedding.CoverAbelianSylowAux

public section

namespace CFSG.AGLEmbedding


open CFSG.Open Equiv Equiv.Perm Finset

variable {K : Type*} [Group K] [Finite K] {n p : ℕ}

omit [Finite K] in
theorem apply_eq_of_mem_closure (e : K ≃* alternatingGroup (Fin n)) {X : Set K}
    {B : Finset (Fin n)} (hX : ∀ k ∈ X, ∀ b ∈ B, (e k : Perm (Fin n)) b = b) {k : K}
    (hk : k ∈ Subgroup.closure X) : ∀ b ∈ B, (e k : Perm (Fin n)) b = b := by
  induction hk using Subgroup.closure_induction with
  | mem x hx => exact hX x hx
  | one => simp
  | mul x y _ _ ihx ihy =>
    intro b hb
    rw [map_mul, Subgroup.coe_mul, Perm.mul_apply, ihy b hb, ihx b hb]
  | inv x _ ihx =>
    intro b hb
    rw [map_inv, InvMemClass.coe_inv, Perm.inv_eq_iff_eq]
    exact (ihx b hb).symm

omit [Finite K] in
theorem notMem_closure_of_forall_apply_eq (e : K ≃* alternatingGroup (Fin n)) {X : Set K} {c : K}
    (hc : (e c : Perm (Fin n)).support.Nonempty)
    (hX : ∀ k ∈ X, ∀ b ∈ (e c : Perm (Fin n)).support, (e k : Perm (Fin n)) b = b) :
    c ∉ Subgroup.closure X := fun h => by
  obtain ⟨b, hb⟩ := hc
  exact Perm.mem_support.mp hb (apply_eq_of_mem_closure e hX h b hb)

omit [Finite K] in
theorem commute_of_disjoint_support (e : K ≃* alternatingGroup (Fin n)) {a b : K}
    (h : _root_.Disjoint (e a : Perm (Fin n)).support (e b : Perm (Fin n)).support) :
    Commute a b := by
  apply e.injective
  apply Subtype.ext
  simp only [map_mul, Subgroup.coe_mul]
  exact (disjoint_iff_disjoint_support.mpr h).commute.eq

theorem three_le_pRank_closure (hp : p.Prime) {a b c : K} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (hoa : orderOf a = p) (hb : b ^ p = 1) (hc : c ^ p = 1)
    (hb' : b ∉ Subgroup.zpowers a) (hc' : c ∉ Subgroup.closure {a, b}) :
    3 ≤ Open.pRank p (Subgroup.closure {a, b, c}) := by
  have : Fact p.Prime := ⟨hp⟩
  set E := Subgroup.closure ({a, b, c} : Set K) with hE
  have hcomm : IsMulCommutative E := by
    refine Subgroup.isMulCommutative_closure ?_
    intro x hx y hy _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first | exact Commute.refl _ | assumption | exact Commute.symm ‹_›
  have hpow : ∀ x ∈ E, x ^ p = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · rw [← hoa]
        exact pow_orderOf_eq_one x
      · exact hb
      · exact hc
    | one => exact one_pow p
    | mul x y hx hy ihx ihy =>
      have h : Commute x y := congrArg Subtype.val ((isMulCommutative_iff.mp hcomm) ⟨x, hx⟩ ⟨y, hy⟩)
      rw [h.mul_pow, ihx, ihy, one_mul]
    | inv x hx ihx => rw [inv_pow, ihx, inv_one]
  have hP : IsPGroup p E := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hpow _ g.2)⟩
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  have h12 : Subgroup.zpowers a < Subgroup.closure {a, b} := IsConcreteLE.lt_iff_le_and_exists.mpr
    ⟨Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)), b,
      Subgroup.subset_closure (by simp), hb'⟩
  have h23 : Subgroup.closure {a, b} < E := IsConcreteLE.lt_iff_le_and_exists.mpr
    ⟨Subgroup.closure_mono
      (Set.insert_subset_insert (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))), c,
      Subgroup.subset_closure (by simp), hc'⟩
  obtain ⟨j, hj⟩ := (hP.to_le h23.le).exists_card_eq
  have hlt1 := Subgroup.card_lt_of_lt h12
  have hlt2 := Subgroup.card_lt_of_lt h23
  rw [Nat.card_zpowers, hoa, hj] at hlt1
  rw [hj, hm] at hlt2
  have hj2 : 1 < j := (Nat.pow_lt_pow_iff_right hp.one_lt).mp (by rwa [pow_one])
  have hm3 : j < m := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt2
  exact (show 3 ≤ m by omega).trans (SectionRank.le_pRank hp.one_lt le_rfl ⟨hcomm, hpow⟩ hm)

theorem two_le_pRank_closure_pair (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup K}
    (hP : IsPGroup p P) {a b : K} (ha : a ∈ P) (hb : b ∈ P) (hoa : orderOf a = p)
    (hob : orderOf b = p) (hb' : b ∉ Subgroup.zpowers a) :
    2 ≤ Open.pRank p (Subgroup.closure {a, b}) := by
  have haF : a ∈ Subgroup.closure ({a, b} : Set K) := Subgroup.subset_closure (by simp)
  have hbF : b ∈ Subgroup.closure ({a, b} : Set K) := Subgroup.subset_closure (by simp)
  refine two_le_pRank_of_isPGroup_not_isCyclic hp hp2 (hP.to_le ((Subgroup.closure_le _).mpr ?_)) ?_
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> assumption
  · intro hcyc
    have hle : Subgroup.zpowers (⟨b, hbF⟩ : Subgroup.closure ({a, b} : Set K)) ≤
        Subgroup.zpowers ⟨a, haF⟩ := by
      rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers,
        Subgroup.orderOf_mk, Subgroup.orderOf_mk, hoa, hob]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hle (Subgroup.mem_zpowers _))
    exact hb' (Subgroup.mem_zpowers_iff.mpr ⟨m, by simpa using congrArg Subtype.val hm⟩)

theorem mem_map_weakCore (hp : p.Prime) (hp2 : p ≠ 2) (e : K ≃* alternatingGroup (Fin n))
    (T : Sylow p K) {a b c : K} (ha : a ∈ (T : Subgroup K)) (hb : b ∈ (T : Subgroup K))
    (hc : c ∈ (T : Subgroup K)) (hoa : orderOf a = p) (hob : orderOf b = p)
    (hoc : orderOf c = p)
    (hab : _root_.Disjoint (e a : Perm (Fin n)).support (e b : Perm (Fin n)).support)
    (hac : _root_.Disjoint (e a : Perm (Fin n)).support (e c : Perm (Fin n)).support)
    (hbc : _root_.Disjoint (e b : Perm (Fin n)).support (e c : Perm (Fin n)).support)
    (hb0 : (e b : Perm (Fin n)).support.Nonempty) (hc0 : (e c : Perm (Fin n)).support.Nonempty)
    {g : Perm (Fin n)} (hg : g.IsThreeCycle) (hgd : _root_.Disjoint g.support
      ((e a : Perm (Fin n)).support ∪ (e b : Perm (Fin n)).support)) :
    g ∈ (GLBWeakCore p (T : Subgroup K)).map
      ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom) := by
  set F := Subgroup.closure ({a, b} : Set K) with hF
  have hFT : F ≤ (T : Subgroup K) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> assumption
  have hb' : b ∉ Subgroup.zpowers a := by
    rw [Subgroup.zpowers_eq_closure]
    refine notMem_closure_of_forall_apply_eq e hb0 fun k hk x hx => ?_
    rw [Set.mem_singleton_iff.mp hk]
    exact Perm.notMem_support.mp (Finset.disjoint_right.mp hab hx)
  have hc' : c ∉ F := by
    refine notMem_closure_of_forall_apply_eq e hc0 fun k hk x hx => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl
    · exact Perm.notMem_support.mp (Finset.disjoint_right.mp hac hx)
    · exact Perm.notMem_support.mp (Finset.disjoint_right.mp hbc hx)
  have hcen : ∀ y : K, Commute a y → Commute b y → y ∈ Subgroup.centralizer (F : Set K) := by
    intro y hay hby
    rw [hF, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with rfl | rfl
    · exact hay.eq
    · exact hby.eq
  have hle : Subgroup.closure ({a, b, c} : Set K) ≤
      F ⊔ ((T : Subgroup K) ⊓ Subgroup.centralizer (F : Set K)) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right ⟨hc, hcen x (commute_of_disjoint_support e hac)
        (commute_of_disjoint_support e hbc)⟩
  have h2 := two_le_pRank_closure_pair hp hp2 T.isPGroup' ha hb hoa hob hb'
  have h3 := (three_le_pRank_closure hp (commute_of_disjoint_support e hab)
    (commute_of_disjoint_support e hac) (commute_of_disjoint_support e hbc) hoa
    (hob ▸ pow_orderOf_eq_one b) (hoc ▸ pow_orderOf_eq_one c) hb' hc').trans
    (SectionRank.pRank_mono hp.one_lt hle)
  have hN := PreuniquenessRankFour.Helpers.normalizer_le_weakCore p hFT h2 h3
  set y := e.symm ⟨g, hg.mem_alternatingGroup⟩ with hy
  have hyg : (e y : Perm (Fin n)) = g := by simp [hy]
  have hd := Finset.disjoint_union_right.mp hgd
  refine ⟨y, hN (Subgroup.centralizer_le_normalizer _ (hcen y ?_ ?_)), by simp [hy]⟩
  · exact commute_of_disjoint_support e (by rw [hyg]; exact hd.1.symm)
  · exact commute_of_disjoint_support e (by rw [hyg]; exact hd.2.symm)

theorem weakCore_eq_top_of_three_mul_lt (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 * p + 1 ≤ n)
    (e : K ≃* alternatingGroup (Fin n)) (T : Sylow p K) :
    GLBWeakCore p (T : Subgroup K) = ⊤ := by
  obtain ⟨c₁, h₁T, c₂, h₂T, c₃, h₃T, ho₁, ho₂, ho₃, hs₁, hs₂, hs₃, d₁₂, d₁₃, d₂₃, x, hx₁, hx₂,
    hx₃⟩ := exists_three_disjoint_cycles_mem_sylow hp hp2 hn e T
  set φ : K →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom with hφ
  have hφinj : Function.Injective φ := (Subgroup.subtype_injective _).comp e.injective
  have hne : ∀ {k : K}, #(e k : Perm (Fin n)).support = p →
      (e k : Perm (Fin n)).support.Nonempty := fun h => Finset.card_pos.mp (h ▸ hp.pos)
  have hAle := alternatingGroup_le_of_three
    (fun g hg hgd => mem_map_weakCore hp hp2 e T h₂T h₃T h₁T ho₂ ho₃ ho₁ d₂₃ d₁₂.symm d₁₃.symm
      (hne hs₃) (hne hs₁) hg hgd)
    (fun g hg hgd => mem_map_weakCore hp hp2 e T h₁T h₃T h₂T ho₁ ho₃ ho₂ d₁₃ d₁₂ d₂₃.symm
      (hne hs₃) (hne hs₂) hg hgd)
    (fun g hg hgd => mem_map_weakCore hp hp2 e T h₁T h₂T h₃T ho₁ ho₂ ho₃ d₁₂ d₁₃ d₂₃
      (hne hs₂) (hne hs₃) hg hgd)
    d₁₂ d₁₃ d₂₃ (by rw [hs₁]; exact hp.one_lt) (by rw [hs₂]; exact hp.one_lt)
    (by rw [hs₃]; exact hp.one_lt) hx₁ hx₂ hx₃
  rw [eq_top_iff]
  intro k _
  obtain ⟨h, hh, hhk⟩ := hAle (show φ k ∈ alternatingGroup (Fin n) from (e k).2)
  rwa [hφinj hhk] at hh

theorem pRank_le_two_of_lt (hp : p.Prime) (e : K ≃* alternatingGroup (Fin n)) (hn : n < 3 * p)
    (H : Subgroup K) : Open.pRank p H ≤ 2 := by
  have h := (SectionRank.pRank_mono hp.one_lt (le_top : H ≤ ⊤)).trans
    ((SectionRank.pRank_top_le_of_injective hp.one_lt
      ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom)
      ((Subgroup.subtype_injective _).comp e.injective)).trans (pRank_top_perm_le hp))
  rw [Fintype.card_fin] at h
  exact h.trans (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega)))

theorem caseThreeKFact_of_center_ne_bot {K : Type} [Group K] [Finite K]
    (hK : Open.IsQuasisimple K) (hn : 5 ≤ n)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) [Fact p.Prime] (hp2 : p ≠ 2)
    (hZp : IsPGroup p (Subgroup.center K)) (hZ : Subgroup.center K ≠ ⊥) :
    CaseThreeKFact p K := by
  have : Group.IsPerfect K := ⟨hK.1⟩
  have hp : p.Prime := Fact.out
  have hn67 := eq_six_or_seven_of_center hn e hp hp2 hZ hZp
  have hZ6 : Nat.card (Subgroup.center K) ∣ 6 := by
    have h := card_center_dvd_card_hopfMultiplier e
    rwa [(Alternating.Multipliers.schurAlternatingMultiplierInput n hn).2, ite_eq_left hn67] at h
  have hpZ : p ∣ Nat.card (Subgroup.center K) :=
    hZp.card_eq_or_dvd.resolve_left fun h => hZ (Subgroup.card_eq_one.mp h)
  have hp3 : p = 3 := by
    rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 2 * 3 from hpZ.trans hZ6) with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
  subst hp3
  have hZ3 : Nat.card (Subgroup.center K) = 3 := by
    obtain ⟨k, hk⟩ := hZp.exists_card_eq
    rw [hk] at hZ6 hpZ ⊢
    have hk1 : k ≤ 1 := by
      by_contra h
      have h9 := (pow_dvd_pow 3 (show 2 ≤ k by omega)).trans hZ6
      norm_num at h9
    have hk0 : k ≠ 0 := by
      rintro rfl
      norm_num at hpZ
    obtain rfl : k = 1 := by omega
    rfl
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hKcard : Nat.card K = n.factorial / 2 * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K), hZ3,
      Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  have hKc : Nat.card K = 1080 ∨ Nat.card K = 7560 := by
    rcases hn67 with rfl | rfl
    · exact Or.inl (by rw [hKcard]; norm_num [Nat.factorial])
    · exact Or.inr (by rw [hKcard]; norm_num [Nat.factorial])
  intro T
  have hT27 : Nat.card (T : Subgroup K) = 3 ^ 3 := by
    obtain ⟨m, hm⟩ := T.isPGroup'.exists_card_eq
    have hidx := T.not_dvd_index
    have hmul := (T : Subgroup K).card_mul_index
    rw [hm] at hmul
    have hle : 3 ^ m ≤ Nat.card K := Nat.le_of_dvd Nat.card_pos (Dvd.intro _ hmul)
    have hm9 : m < 9 := by
      by_contra h
      have h1 : 19683 ≤ 3 ^ m := calc
        19683 = 3 ^ 9 := by norm_num
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      rcases hKc with hK | hK <;> omega
    have hm3 : m = 3 := by
      rcases hKc with hK | hK <;> rw [hK] at hmul <;> interval_cases m <;> norm_num at hmul <;>
        omega
    rw [hm, hm3]
  have hTna : ∃ a ∈ (T : Subgroup K), ∃ b ∈ (T : Subgroup K), a * b ≠ b * a := by
    obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
    obtain ⟨k, hzk⟩ := hZp ⟨z, hz⟩
    have hzT := center_le_commutator_of_isPerfect T hz ⟨k, congrArg Subtype.val hzk⟩
    by_contra hcon
    push Not at hcon
    have hbot : ⁅(T : Subgroup K), (T : Subgroup K)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hcon y hy x hx
    rw [hbot, Subgroup.mem_bot] at hzT
    exact hz1 (Subtype.ext hzT)
  have hrank : Open.pRank 3 (T : Subgroup K) ≤ 2 := by
    have h := pRank_sup_le_two (C := ⊥) hT27 hTna inferInstance bot_le
      fun c hc _ => by rw [Subgroup.mem_bot.mp hc]; exact one_mem _
    rwa [sup_bot_eq] at h
  exact Or.inr (Or.inl ⟨hrank, Or.inr hT27⟩)

theorem altCaseThreeKFacts : AltCaseThreeKFacts := by
  intro K _ _ hK n hn ⟨e⟩ p _ hp2 hZp _ hA
  have hp : p.Prime := Fact.out
  by_cases hZ : Subgroup.center K = ⊥
  · have e' : K ≃* alternatingGroup (Fin n) :=
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
    intro T
    rcases lt_trichotomy n (3 * p) with h | h | h
    · exact Or.inr (Or.inl ⟨pRank_le_two_of_lt hp e' h _, Or.inl hZ⟩)
    · exact absurd ⟨h, hZ⟩ hA
    · exact Or.inl (weakCore_eq_top_of_three_mul_lt hp hp2 (by omega) e' T)
  · exact caseThreeKFact_of_center_ne_bot hK hn e hp2 hZp hZ

end CFSG.AGLEmbedding

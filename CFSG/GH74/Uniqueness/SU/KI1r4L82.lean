module

public import CFSG.GH74.Uniqueness.SU.KI1r4L82A
public import CFSG.RankThree.GroupTheory.SteinbergCDRankOneAutPrimes

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.L82

open Subgroup CFSG.GH74.Uniqueness.SU.K.R3.Pow CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

variable {M : Type} [Group M] [Finite M]

theorem card_range_le_frattini_quot {P V : Type} [Group P] [Finite P] [Group V] [Finite V]
    (hP : IsPGroup 2 P) (hcomm : ∀ a b : V, a * b = b * a) (hsq : ∀ a : V, a * a = 1)
    (f : P →* V) : Nat.card f.range ≤ Nat.card (P ⧸ frattini P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 P) := ⟨hP⟩
  have hker : frattini P ≤ f.ker := by
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2), Subgroup.closure_le]
    rintro x (hx | ⟨a, rfl⟩)
    · have hcomm_le : commutator P ≤ f.ker := by
        rw [commutator_def, Subgroup.commutator_le]
        intro a _ b _
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
        exact hcomm (f a) (f b)
      exact hcomm_le hx
    · simp only [SetLike.mem_coe, MonoidHom.mem_ker, map_pow]
      rw [pow_two]; exact hsq _
  have h1 : Nat.card f.range = f.ker.index := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]; rfl
  have h2 : f.ker.index ∣ (frattini P).index := Subgroup.index_dvd_of_le hker
  have h3 : (frattini P).index = Nat.card (P ⧸ frattini P) := rfl
  have h4 : 0 < (frattini P).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [h1]
  exact (Nat.le_of_dvd h4 h2).trans (le_of_eq h3)


theorem sup_eq_top_of_card_four (hM : IsPGroup 2 M) {σ τ : MulAut M} (h : DihAct σ τ 1)
    (hV4 : Nat.card (M ⧸ frattini M) = 4) (c : M) (hc : (c : M ⧸ frattini M) ≠ 1) :
    zpowers c ⊔ zpowers (σ c) = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B : Subgroup M := zpowers c ⊔ zpowers (σ c) with hB
  set Bb : Subgroup (M ⧸ frattini M) := B.map (QuotientGroup.mk' (frattini M)) with hBb
  have hc1 : (c : M ⧸ frattini M) ∈ Bb := ⟨c, Subgroup.mem_sup_left (mem_zpowers c), rfl⟩
  have hσc : ((σ c : M) : M ⧸ frattini M) ∈ Bb := ⟨σ c, Subgroup.mem_sup_right (mem_zpowers _), rfl⟩
  have hσc1 : bar σ (c : M ⧸ frattini M) = ((σ c : M) : M ⧸ frattini M) := bar_mk σ c
  have hne1 : ((σ c : M) : M ⧸ frattini M) ≠ c := by
    intro heq
    rw [← hσc1] at heq
    exact hc (bar_fix hM h _ heq)
  have hdvd : Nat.card Bb ∣ 4 := hV4 ▸ Subgroup.card_subgroup_dvd_card Bb
  have hB4 : Nat.card Bb = 4 := by
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4] at hdvd
    obtain ⟨i, hi, hBi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases i
    · exfalso
      have hsub : Subsingleton Bb := (Nat.card_eq_one_iff_unique.mp (by simpa using hBi)).1
      apply hc
      have := Subsingleton.elim (⟨c, hc1⟩ : Bb) 1
      exact congrArg Subtype.val this
    · exfalso
      have hBi' : Nat.card Bb = 2 := by simpa using hBi
      rw [Nat.card_eq_two_iff' (1 : Bb)] at hBi'
      obtain ⟨y, -, hy⟩ := hBi'
      have e1 := hy ⟨c, hc1⟩ (fun h' => hc (congrArg Subtype.val h'))
      have e2 := hy ⟨_, hσc⟩ (fun h' => by
        have : ((σ c : M) : M ⧸ frattini M) = 1 := congrArg Subtype.val h'
        apply hc
        rw [← hσc1] at this
        have h2 : (bar σ) (c : M ⧸ frattini M) = (bar σ) 1 := by rw [this, map_one]
        exact (bar σ).injective h2)
      exact hne1 (congrArg Subtype.val (e2.trans e1.symm))
    · simpa using hBi
  have hBtop : Bb = ⊤ := Subgroup.eq_top_of_card_eq Bb (by rw [hB4, hV4])
  have hsup : B ⊔ frattini M = ⊤ := by
    have h1 : B.map (QuotientGroup.mk' (frattini M)) = ⊤ := hBtop
    have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' (frattini M)) B
    rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at h2
    exact h2.symm
  exact frattini_nongenerating hsup


theorem isMulCommutative_pair {σ τ : MulAut M} (h : DihAct σ τ 1) (c : M) :
    IsMulCommutative ↥(zpowers c ⊔ zpowers (σ c)) := by
  have h1 : zpowers c ⊔ zpowers (σ c) = Subgroup.closure ({c, σ c} : Set M) := by
    rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
      Subgroup.zpowers_eq_closure]
  rw [h1]
  exact Subgroup.isMulCommutative_closure (by
    intro x hx y hy hxy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact absurd rfl hxy
      · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact commute_sigma h x
    · rw [Set.mem_singleton_iff] at hx
      rcases hy with rfl | hy
      · rw [hx]; exact (commute_sigma h y).symm
      · rw [Set.mem_singleton_iff] at hy; exact absurd (hx.trans hy.symm) hxy)

theorem lemma82_small (hM : IsPGroup 2 M) {σ τ : MulAut M} (h : DihAct σ τ 1)
    (hrk : CFSG.pRank 2 (fixSub τ) ≤ 1) (hV : Nat.card (M ⧸ frattini M) ≤ 4) :
    IsMulCommutative M ∧ ∃ c : M, τ c = c ∧ zpowers c ⊔ zpowers (σ c) = ⊤ ∧
      Nat.card M = orderOf c ^ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hsub : Subsingleton M
  · refine ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, 1, map_one τ, ?_, ?_⟩
    · rw [eq_top_iff]
      intro x _
      rw [Subsingleton.elim x 1]
      exact one_mem _
    · have h1 : Nat.card M = 1 := Nat.card_of_subsingleton 1
      rw [h1, orderOf_one]; norm_num
  · have hnt : Nontrivial M := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨hcomm, hsq⟩ := quot_comm_sq hM
    have hbar2 : (bar τ) ^ 2 = 1 := by rw [← map_pow, h.sq, map_one]
    have hbarinv : bar τ * bar σ * (bar τ)⁻¹ = (bar σ)⁻¹ := by
      have := congrArg (quotientAutomorphism (frattini M)) h.inv
      simpa [map_mul, map_inv] using this
    have hVsq := card_fix_sq_elem hcomm hsq (bar σ) (bar τ) hbar2 hbarinv (bar_fix hM h)
    have hne : frattini M ≠ ⊤ := by
      intro htop
      have := frattini_nongenerating (G := M) (K := ⊥) (by rw [htop]; simp)
      exact bot_ne_top this
    have hV1 : 1 < Nat.card (M ⧸ frattini M) := Subgroup.one_lt_index_of_ne_top hne
    have hcV : Nat.card (fixSub (bar τ)) = 2 := by
      have h3 : Nat.card (fixSub (bar τ)) ≤ 2 := by
        by_contra hh
        push Not at hh
        have : 3 ^ 2 ≤ Nat.card (fixSub (bar τ)) ^ 2 := Nat.pow_le_pow_left hh 2
        omega
      have h4 : 1 < Nat.card (fixSub (bar τ)) := by
        by_contra hh
        push Not at hh
        have h5 : 0 < Nat.card (fixSub (bar τ)) := Nat.card_pos
        have h6 : Nat.card (fixSub (bar τ)) = 1 := by omega
        rw [h6] at hVsq
        omega
      omega
    have hV4 : Nat.card (M ⧸ frattini M) = 4 := by
      rw [← hVsq, hcV]; norm_num
    have hrange := range_resΦ hM h
    have hex : ∃ c₀ : fixSub τ, resΦ τ c₀ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have h1 : Nat.card (resΦ τ).range = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
        obtain ⟨a, ha⟩ := a.2
        obtain ⟨b, hb⟩ := b.2
        apply Subtype.ext
        rw [← ha, ← hb, hcon a, hcon b]
      rw [hrange] at h1
      omega
    obtain ⟨c₀, hc₀⟩ := hex
    have hgen₀ := sup_eq_top_of_card_four hM h hV4 (c₀ : M) hc₀
    have hcommM : ∀ a b : M, a * b = b * a := by
      have hcc := isMulCommutative_pair h (c₀ : M)
      rw [hgen₀] at hcc
      intro a b
      have := hcc.is_comm.comm ⟨a, mem_top a⟩ ⟨b, mem_top b⟩
      exact congrArg Subtype.val this
    have hMcomm : IsMulCommutative M := ⟨⟨hcommM⟩⟩
    have hCcyc : IsCyclic ↥(fixSub τ) := by
      have hC2 : IsPGroup 2 ↥(fixSub τ) := hM.to_subgroup _
      have h1 := (CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_abelian_subgroups
        Nat.prime_two hC2).mp hrk ⊤
        ⟨⟨fun a b => Subtype.ext (Subtype.ext (hcommM _ _))⟩⟩
      have := h1
      exact isCyclic_of_surjective (Subgroup.topEquiv).toMonoidHom Subgroup.topEquiv.surjective
    obtain ⟨g, hg⟩ := hCcyc.exists_generator
    have hg1 : resΦ τ g ≠ 1 := by
      intro hg1
      apply hc₀
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg c₀)
      rw [← hk, map_zpow, hg1, one_zpow]
    have hgM : ((g : M) : M ⧸ frattini M) ≠ 1 := hg1
    refine ⟨hMcomm, (g : M), g.2, sup_eq_top_of_card_four hM h hV4 (g : M) hgM, ?_⟩
    have hcard := card_fixSub_sq _ M rfl hM σ τ 1 h
    rw [← hcard, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]


omit [Finite M] in
theorem card_fixSub_char {τ : MulAut M} (N : Subgroup M) [N.Characteristic] :
    Nat.card (fixSub (MulAut.characteristic N τ)) =
      Nat.card ↥(N.subgroupOf (fixSub τ)) := by
  refine Nat.card_congr ?_
  have key : ∀ d : fixSub (MulAut.characteristic N τ), τ ((d.1 : N) : M) = ((d.1 : N) : M) :=
    fun d => by
      have := congrArg Subtype.val d.2
      simpa using this
  refine
    { toFun := fun d => ⟨⟨((d.1 : N) : M), key d⟩, d.1.2⟩
      invFun := fun c => ⟨⟨(c.1.1 : M), c.2⟩, ?_⟩
      left_inv := fun d => rfl
      right_inv := fun c => rfl }
  apply Subtype.ext
  have h1 : τ (c.1.1 : M) = c.1.1 := c.1.2
  simpa using h1

theorem quat_comm (n : ℕ) [NeZero n] :
    ⁅(QuaternionGroup.a 1 : QuaternionGroup n), (QuaternionGroup.xa 0 : QuaternionGroup n)⁆ =
      QuaternionGroup.a 2 := by
  have h1 : (QuaternionGroup.a 1 : QuaternionGroup n)⁻¹ = QuaternionGroup.a (-1) := rfl
  have h2 : (QuaternionGroup.xa 0 : QuaternionGroup n)⁻¹ = QuaternionGroup.xa (n + 0) := rfl
  rw [commutatorElement_def, h1, h2, QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a,
    QuaternionGroup.xa_mul_xa]
  congr 1
  have : ((2 * n : ℕ) : ZMod (2 * n)) = 0 := ZMod.natCast_self _
  push_cast at this
  linear_combination this

theorem quat_index_le (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    (commutator (QuaternionGroup n)).index ≤ 4 := by
  have hmem : (QuaternionGroup.a 2 : QuaternionGroup n) ∈ commutator (QuaternionGroup n) := by
    rw [← quat_comm n]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hle : Subgroup.zpowers (QuaternionGroup.a 2 : QuaternionGroup n) ≤
      commutator (QuaternionGroup n) := (Subgroup.zpowers_le).mpr hmem
  have hord : orderOf (QuaternionGroup.a 2 : QuaternionGroup n) = n := by
    rw [QuaternionGroup.orderOf_a]
    have h2 : ((2 : ZMod (2 * n))).val = 2 := by
      rw [ZMod.val_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [h2]
    have : (2 * n).gcd 2 = 2 := by
      rw [Nat.gcd_comm]; exact Nat.gcd_eq_left (dvd_mul_right 2 n)
    rw [this]; omega
  have hcardG : Nat.card (QuaternionGroup n) = 4 * n := by
    rw [Nat.card_eq_fintype_card]; exact QuaternionGroup.card
  have h1 : (Subgroup.zpowers (QuaternionGroup.a 2 : QuaternionGroup n)).index ≤ 4 := by
    have := (Subgroup.zpowers (QuaternionGroup.a 2 : QuaternionGroup n)).card_mul_index
    rw [Nat.card_zpowers, hord, hcardG] at this
    have hnpos : 0 < n := NeZero.pos n
    nlinarith
  have hpos : 0 < (Subgroup.zpowers (QuaternionGroup.a 2 : QuaternionGroup n)).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  exact (Nat.le_of_dvd hpos (Subgroup.index_dvd_of_le hle)).trans h1

theorem index_commutator_le_four {C : Type*} [Group C] {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (e : C ≃* QuaternionGroup n) : (commutator C).index ≤ 4 := by
  have h1 : (commutator C).map (e : C →* QuaternionGroup n) =
      commutator (QuaternionGroup n) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  have h2 := Subgroup.index_map_equiv (H := commutator C) e
  rw [← h2, h1]
  exact quat_index_le n hn

theorem card_center_of_quaternion {C : Type*} [Group C] {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (e : C ≃* QuaternionGroup n) : Nat.card (center C) = 2 := by
  have hc := (CFSG.GroupTheory.quaternion_centralizers hn).2.2.1
  have h1 : (center C).map (e : C →* QuaternionGroup n) = center (QuaternionGroup n) :=
    Subgroup.map_center_eq e
  have h2 : Nat.card (center C) = Nat.card (center (QuaternionGroup n)) := by
    rw [← h1]
    exact (Subgroup.card_map_of_injective (f := (e : C →* QuaternionGroup n)) e.injective
      (K := center C)).symm
  rw [h2, Nat.card_eq_two_iff' (⟨QuaternionGroup.a 0, (hc _).mpr (Or.inl rfl)⟩ :
    center (QuaternionGroup n))]
  refine ⟨⟨QuaternionGroup.a (n : ZMod (2 * n)), (hc _).mpr (Or.inr rfl)⟩, ?_, ?_⟩
  · intro h
    have h1 : (QuaternionGroup.a (n : ZMod (2 * n)) : QuaternionGroup n) =
        QuaternionGroup.a 0 := congrArg Subtype.val h
    have h2 : (n : ZMod (2 * n)) = 0 := QuaternionGroup.a.inj h1
    rw [ZMod.natCast_eq_zero_iff] at h2
    have hnpos : 0 < n := NeZero.pos n
    have := Nat.le_of_dvd hnpos h2
    omega
  · intro y hy
    rcases (hc y.1).mp y.2 with h | h
    · exact absurd (Subtype.ext h) hy
    · exact Subtype.ext h


theorem card_le_two_of_cyclic_sq {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (hsq : ∀ x : G, x * x = 1) : Nat.card G ≤ 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq g)
  exact Nat.le_of_dvd (by norm_num) this

theorem quaternion_not_comm (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    ¬ ∀ a b : QuaternionGroup n, a * b = b * a := by
  intro h
  have h1 := h (QuaternionGroup.a 1) (QuaternionGroup.xa 0)
  rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at h1
  have h2 : (0 - 1 : ZMod (2 * n)) = 0 + 1 := QuaternionGroup.xa.inj h1
  have h3 : (2 : ZMod (2 * n)) = 0 := by linear_combination -h2
  have h4 : ((2 : ℕ) : ZMod (2 * n)) = 0 := by exact_mod_cast h3
  rw [ZMod.natCast_eq_zero_iff] at h4
  have := Nat.le_of_dvd (by norm_num) h4
  omega

theorem lemma82_big (hM : IsPGroup 2 M) {σ τ : MulAut M} (h : DihAct σ τ 1)
    (hrk : CFSG.pRank 2 (fixSub τ) ≤ 1) (hV : Nat.card (M ⧸ frattini M) = 16) :
    Nat.card M = 64 ∧ Nat.card (center M) = 4 ∧ commutator M = center M ∧
      frattini M = center M ∧ (∀ u : M, u * u ∈ center M) ∧ (∀ a ∈ center M, a * a = 1) ∧
      Nonempty (fixSub τ ≃* QuaternionGroup 2) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC2 : IsPGroup 2 ↥(fixSub τ) := hM.to_subgroup _
  have hcardC : Nat.card (fixSub τ) ^ 2 = Nat.card M := card_fixSub_sq _ M rfl hM σ τ 1 h
  obtain ⟨hcomm, hsq⟩ := quot_comm_sq hM
  have hbar2 : (bar τ) ^ 2 = 1 := by rw [← map_pow, h.sq, map_one]
  have hbarinv : bar τ * bar σ * (bar τ)⁻¹ = (bar σ)⁻¹ := by
    have := congrArg (quotientAutomorphism (frattini M)) h.inv
    simpa [map_mul, map_inv] using this
  have hVsq := card_fix_sq_elem hcomm hsq (bar σ) (bar τ) hbar2 hbarinv (bar_fix hM h)
  have hcV : Nat.card (fixSub (bar τ)) = 4 := by
    rw [hV] at hVsq
    have h4 : (Nat.card (fixSub (bar τ))) ^ 2 = 4 ^ 2 := by rw [hVsq]; norm_num
    exact Nat.pow_left_injective (by norm_num) h4
  have hrange := range_resΦ hM h
  have hC4 : 4 ≤ Nat.card (↥(fixSub τ) ⧸ frattini ↥(fixSub τ)) := by
    have := card_range_le_frattini_quot hC2 hcomm hsq (resΦ τ)
    rwa [hrange, hcV] at this
  rcases (CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification Nat.prime_two
    hC2).mp hrk with hcyc | ⟨-, n, hn3, ⟨e⟩⟩
  · exfalso
    have : Fact (IsPGroup 2 ↥(fixSub τ)) := ⟨hC2⟩
    have : IsCyclic (↥(fixSub τ) ⧸ frattini ↥(fixSub τ)) :=
      isCyclic_of_surjective (QuotientGroup.mk' (frattini ↥(fixSub τ)))
        (QuotientGroup.mk'_surjective _)
    have hfsq : ∀ x : ↥(fixSub τ) ⧸ frattini ↥(fixSub τ), x * x = 1 := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, ← pow_two]
        exact CFSG.pth_power_mem_frattini_of_isPGroup y
    have := card_le_two_of_cyclic_sq hfsq
    omega
  ·
    have hm2 : 2 ≤ 2 ^ (n - 2) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
    have hcommC := index_commutator_le_four hm2 e
    have hcenC := card_center_of_quaternion hm2 e
    have hnoncomm := quaternion_not_comm (2 ^ (n - 2)) hm2
    have hCcard : Nat.card (fixSub τ) = 4 * 2 ^ (n - 2) := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]; exact QuaternionGroup.card
    have : Fact (IsPGroup 2 M) := ⟨hM⟩
    have hM'Φ : commutator M ≤ frattini M := CFSG.commutator_le_frattini_of_isPGroup (p := 2)
    have hM'Z : commutator M ≤ center M := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_center_iff]
      intro g
      exact (commutator_central h a b g).symm.eq
    set D : Subgroup ↥(fixSub τ) := (commutator M).subgroupOf (fixSub τ) with hD
    have hDle : commutator ↥(fixSub τ) ≤ D := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      show ((⁅a, b⁆ : ↥(fixSub τ)) : M) ∈ commutator M
      have : ((⁅a, b⁆ : ↥(fixSub τ)) : M) = ⁅(a : M), (b : M)⁆ := rfl
      rw [this]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have hDidx : D.index ≤ 4 := by
      have hpos : 0 < (commutator ↥(fixSub τ)).index :=
        Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      exact (Nat.le_of_dvd hpos (Subgroup.index_dvd_of_le hDle)).trans hcommC
    have hDcard : Nat.card (commutator M) = Nat.card D ^ 2 := by
      have h1 := card_fixSub_sq _ (commutator M) rfl (hM.to_subgroup _)
        (MulAut.characteristic (commutator M) σ) (MulAut.characteristic (commutator M) τ) 1
        (h.restrict (commutator M))
      rw [card_fixSub_char (τ := τ) (commutator M)] at h1
      exact h1.symm
    have hCD : Nat.card D * D.index = Nat.card (fixSub τ) := D.card_mul_index
    have hM'idx : (commutator M).index = D.index ^ 2 := by
      have h1 := (commutator M).card_mul_index
      have hDpos : 0 < Nat.card D := Nat.card_pos
      have h2 : Nat.card D ^ 2 * (commutator M).index = Nat.card D ^ 2 * D.index ^ 2 := by
        calc Nat.card D ^ 2 * (commutator M).index
            = Nat.card (commutator M) * (commutator M).index := by rw [hDcard]
          _ = Nat.card M := h1
          _ = Nat.card (fixSub τ) ^ 2 := hcardC.symm
          _ = (Nat.card D * D.index) ^ 2 := by rw [hCD]
          _ = Nat.card D ^ 2 * D.index ^ 2 := by ring
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
    have hΦidx : (frattini M).index = 16 := hV
    have hM'idx16 : (commutator M).index = 16 := by
      have hd : (frattini M).index ∣ (commutator M).index := Subgroup.index_dvd_of_le hM'Φ
      have hpos : 0 < (commutator M).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have h16 : 16 ≤ (commutator M).index := by
        rw [hΦidx] at hd; exact Nat.le_of_dvd hpos hd
      have h4 : D.index = 4 := by
        rw [hM'idx] at h16
        by_contra hne
        have : D.index ≤ 3 := by omega
        have : D.index ^ 2 ≤ 3 ^ 2 := Nat.pow_le_pow_left this 2
        omega
      rw [hM'idx, h4]; norm_num
    have hM'eqΦ : commutator M = frattini M := by
      have h1 := (commutator M).card_mul_index
      have h2 := (frattini M).card_mul_index
      rw [hM'idx16] at h1
      rw [hΦidx] at h2
      exact Subgroup.eq_of_le_of_card_ge hM'Φ (by omega)
    have hM'ne : commutator M ≠ ⊥ := by
      intro hbot
      apply hnoncomm
      have hcommM : ∀ a b : M, a * b = b * a := by
        intro a b
        have hmem : ⁅a, b⁆ ∈ commutator M :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
        rw [hbot, Subgroup.mem_bot] at hmem
        exact commutatorElement_eq_one_iff_mul_comm.mp hmem
      intro q₁ q₂
      apply e.symm.injective
      rw [map_mul, map_mul]
      exact Subtype.ext (hcommM _ _)
    have hZcard : Nat.card (center M) ≤ 4 := by
      have h1 := card_fixSub_sq _ (center M) rfl (hM.to_subgroup _)
        (MulAut.characteristic (center M) σ) (MulAut.characteristic (center M) τ) 1
        (h.restrict (center M))
      rw [card_fixSub_char (τ := τ) (center M)] at h1
      have h2 : Nat.card ((center M).subgroupOf (fixSub τ)) ≤ 2 := by
        rw [← hcenC]
        apply Subgroup.card_le_of_le
        intro x hx
        rw [Subgroup.mem_center_iff]
        intro y
        have := Subgroup.mem_center_iff.mp (Subgroup.mem_subgroupOf.mp hx) (y : M)
        exact Subtype.ext this
      have h3 : Nat.card ((center M).subgroupOf (fixSub τ)) ^ 2 ≤ 2 ^ 2 :=
        Nat.pow_le_pow_left h2 2
      omega
    have hM'card4 : Nat.card (commutator M) = 4 := by
      have h1 : 2 ≤ Nat.card (commutator M) := by
        have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hM'ne
        omega
      have h2 : Nat.card (commutator M) ≤ 4 :=
        (Subgroup.card_le_of_le hM'Z).trans hZcard
      have h3 : 2 ≤ Nat.card D := by
        by_contra hcon
        have : Nat.card D ≤ 1 := by omega
        have : Nat.card D ^ 2 ≤ 1 := by nlinarith
        omega
      have h4 : Nat.card D ≤ 2 := by
        by_contra hcon
        have : 3 ≤ Nat.card D := by omega
        have : 9 ≤ Nat.card D ^ 2 := by nlinarith
        omega
      have : Nat.card D = 2 := by omega
      rw [hDcard, this]; norm_num
    have hZeq : commutator M = center M := by
      refine Subgroup.eq_of_le_of_card_ge hM'Z ?_
      omega
    have hMcard : Nat.card M = 64 := by
      have h1 := (commutator M).card_mul_index
      rw [hM'idx16, hM'card4] at h1
      omega
    have hΦZ : frattini M = center M := hM'eqΦ.symm.trans hZeq
    have hsqc : ∀ u v : M, ⁅u, v⁆ * ⁅u, v⁆ = 1 := by
      intro u v
      have hc : ∀ g, Commute ⁅u, v⁆ g := commutator_central h u v
      have hu2 : u * u ∈ center M := by
        have : u ^ 2 ∈ frattini M := CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) u
        rw [hΦZ, pow_two] at this
        exact this
      have hc1 : u * v = ⁅u, v⁆ * (v * u) := by
        have : ⁅u, v⁆ * (v * u) = u * v := by simp only [commutatorElement_def]; group
        exact this.symm
      have hcu : ⁅u, v⁆ * u = u * ⁅u, v⁆ := (hc u).eq
      have h1 : (u * u) * v = ⁅u, v⁆ * ⁅u, v⁆ * (v * (u * u)) := by
        calc (u * u) * v = u * (u * v) := by group
          _ = u * (⁅u, v⁆ * (v * u)) := by rw [hc1]
          _ = (u * ⁅u, v⁆) * (v * u) := by group
          _ = (⁅u, v⁆ * u) * (v * u) := by rw [hcu]
          _ = ⁅u, v⁆ * ((u * v) * u) := by group
          _ = ⁅u, v⁆ * ((⁅u, v⁆ * (v * u)) * u) := by rw [hc1]
          _ = ⁅u, v⁆ * ⁅u, v⁆ * (v * (u * u)) := by group
      have h2 : v * (u * u) = (u * u) * v := Subgroup.mem_center_iff.mp hu2 v
      have h3 : 1 * (v * (u * u)) = (⁅u, v⁆ * ⁅u, v⁆) * (v * (u * u)) :=
        calc 1 * (v * (u * u)) = v * (u * u) := one_mul _
          _ = (u * u) * v := h2
          _ = (⁅u, v⁆ * ⁅u, v⁆) * (v * (u * u)) := h1
      exact (mul_right_cancel h3).symm
    have hcentSq : ∀ a ∈ commutator M, a * a = 1 ∧ a ∈ center M := by
      intro a ha
      rw [commutator_eq_closure] at ha
      induction ha using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨u, v, rfl⟩ := hx
        exact ⟨hsqc u v, hM'Z (Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
          (Subgroup.mem_top _))⟩
      | one => exact ⟨mul_one 1, one_mem _⟩
      | mul x y _ _ hx hy =>
        obtain ⟨hx2, hxz⟩ := hx
        obtain ⟨hy2, hyz⟩ := hy
        refine ⟨?_, mul_mem hxz hyz⟩
        have hxy : y * x = x * y := Subgroup.mem_center_iff.mp hxz y
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hxy]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [hx2, hy2]; group
      | inv x _ hx =>
        obtain ⟨hx2, hxz⟩ := hx
        refine ⟨?_, inv_mem hxz⟩
        calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
          _ = 1 := by rw [hx2]; simp
    refine ⟨hMcard, by rw [← hZeq]; exact hM'card4, hZeq, hΦZ, ?_, ?_, ?_⟩
    · intro u
      have : u ^ 2 ∈ frattini M := CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) u
      rw [hΦZ, pow_two] at this
      exact this
    · intro a ha
      exact (hcentSq a (hZeq ▸ ha)).1
    · have hC8 : Nat.card (fixSub τ) = 8 := by
        have h1 : Nat.card (fixSub τ) ^ 2 = 8 ^ 2 := by rw [hcardC, hMcard]; norm_num
        exact Nat.pow_left_injective (by norm_num) h1
      have hm : 2 ^ (n - 2) = 2 := by omega
      rw [hm] at e
      exact ⟨e⟩


theorem lemma82 (hM : IsPGroup 2 M) {σ τ : MulAut M} (h : DihAct σ τ 1)
    (hrk : CFSG.pRank 2 (fixSub τ) ≤ 1) :
    (IsMulCommutative M ∧ ∃ c : M, τ c = c ∧ zpowers c ⊔ zpowers (σ c) = ⊤ ∧
        Nat.card M = orderOf c ^ 2) ∨
    (Nat.card M = 64 ∧ Nat.card (center M) = 4 ∧ commutator M = center M ∧
      frattini M = center M ∧ (∀ u : M, u * u ∈ center M) ∧ (∀ a ∈ center M, a * a = 1) ∧
      Nonempty (fixSub τ ≃* QuaternionGroup 2)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hV4 : Nat.card (M ⧸ frattini M) ≤ 4
  · exact Or.inl (lemma82_small hM h hrk hV4)
  · right
    obtain ⟨hcomm, hsq⟩ := quot_comm_sq hM
    have hbar2 : (bar τ) ^ 2 = 1 := by rw [← map_pow, h.sq, map_one]
    have hbarinv : bar τ * bar σ * (bar τ)⁻¹ = (bar σ)⁻¹ := by
      have := congrArg (quotientAutomorphism (frattini M)) h.inv
      simpa [map_mul, map_inv] using this
    have hVsq := card_fix_sq_elem hcomm hsq (bar σ) (bar τ) hbar2 hbarinv (bar_fix hM h)
    have hC2 : IsPGroup 2 ↥(fixSub τ) := hM.to_subgroup _
    have hrange := range_resΦ hM h
    have hcV4 : Nat.card (fixSub (bar τ)) ≤ 4 := by
      have h1 := card_range_le_frattini_quot hC2 hcomm hsq (resΦ τ)
      have h2 := CFSG.RankThree.GroupTheory.card_frattini_quotient_le_four_of_pRank_le_one hC2 hrk
      rw [hrange] at h1
      exact h1.trans h2
    have hVdvd : Nat.card (M ⧸ frattini M) ∣ Nat.card M := Subgroup.card_quotient_dvd_card _
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hM
    have hV16 : Nat.card (M ⧸ frattini M) = 16 := by
      have h3 : 3 ≤ Nat.card (fixSub (bar τ)) := by
        by_contra hcon
        push Not at hcon
        have : Nat.card (fixSub (bar τ)) ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left (by omega) 2
        omega
      have h9 : Nat.card (fixSub (bar τ)) ≠ 3 := by
        intro h3'
        rw [h3'] at hVsq
        rw [hk] at hVdvd
        rw [← hVsq] at hVdvd
        have : 3 ∣ 2 ^ k := (dvd_pow_self 3 (by norm_num : (2 : ℕ) ≠ 0)).trans
          (by simpa using hVdvd)
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
        omega
      have h4 : Nat.card (fixSub (bar τ)) = 4 := by omega
      rw [← hVsq, h4]; norm_num
    exact lemma82_big hM h hrk hV16

end CFSG.GH74.Uniqueness.SU.K.R4.L82

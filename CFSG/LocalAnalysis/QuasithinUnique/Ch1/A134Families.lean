module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassical
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddRankOne
public import CFSG.RankThree.Chevalley.OddRankOneReeTitsModels
public import CFSG.RankThree.Asc83Table.M22
public import CFSG.RankThree.Asc83Table.M23
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Local
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
import CFSG.LocalAnalysis.SectionRank.TwoGenerators

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.SectionRank CFSG.Blueprint
open scoped commutatorElement

theorem two_le_pRank_of_gens {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : Commute x y) (hx1 : x ≠ 1)
    (hy1 : ∀ n : ℕ, x ^ n ≠ y) : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) :=
  CFSG.SectionRank.two_le_pRank_top_of_commute hx hy hxy hx1 hy1

theorem two_le_pRank_of_square_witness {G : Type*} [Group G] [Finite G] {r : ℕ} (hr : r.Prime)
    {x y : G} (hx : x ^ r = 1) (hy : y ^ r = 1) (hxy : x * y = y * x)
    (hcard : Nat.card (Subgroup.closure ({x, y} : Set G)) = r ^ 2) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup G) := by
  have : Fact r.Prime := ⟨hr⟩
  have hr2 := hr.two_le
  have hcyc : ∀ z : G, z ^ r = 1 → Nat.card (Subgroup.zpowers z) ≤ r := fun z hz => by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hr.pos (orderOf_dvd_of_pow_eq_one hz)
  refine two_le_pRank_of_gens hx hy hxy ?_ fun n hn => ?_
  · rintro rfl
    have hle : Subgroup.closure ({1, y} : Set G) ≤ Subgroup.zpowers y := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact one_mem _
      · exact Subgroup.mem_zpowers _
    have := Subgroup.card_le_of_le hle
    nlinarith [hcyc y hy]
  · have hle : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.zpowers x := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_zpowers _
      · rw [← hn]
        exact Subgroup.npow_mem_zpowers x n
    have := Subgroup.card_le_of_le hle
    nlinarith [hcyc x hx]

theorem two_le_pRank_of_cubic_witness {G : Type*} [Group G] [Finite G] {r : ℕ} (hr : r.Prime)
    {x y : G} (hx : x ^ r = 1) (hz1 : ⁅x, y⁆ ≠ 1) (hzx : Commute ⁅x, y⁆ x)
    (hzy : Commute ⁅x, y⁆ y) : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup G) := by
  have : Fact r.Prime := ⟨hr⟩
  have hzr : ⁅x, y⁆ ^ r = 1 := by
    rw [LocalWitness.commutator_pow_eq hzx, hx, commutatorElement_one_left]
  refine two_le_pRank_of_gens hx hzr hzx.symm ?_ fun n hn => ?_
  · rintro rfl
    exact hz1 (commutatorElement_one_left y)
  ·
    have hnr : ¬ r ∣ n := by
      rintro ⟨k, rfl⟩
      apply hz1
      rw [← hn, pow_mul, hx, one_pow]
    have hcop : Nat.Coprime n r := (Nat.Prime.coprime_iff_not_dvd hr).2 hnr |>.symm
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr.one_lt
    have hxz : x = ⁅x, y⁆ ^ m := by
      rw [← hn, ← pow_mul, pow_eq_pow_mod _ (show x ^ r = 1 from hx), hm, pow_one]
    apply hz1
    have hxy : Commute x y := by
      rw [hxz]
      exact hzy.pow_left m
    exact commutatorElement_eq_one_iff_mul_comm.2 hxy.eq


theorem two_le_pRank_of_mulEquiv {S G : Type} [Group S] [Finite S] [Group G] [Finite G] {r : ℕ}
    (hr : r.Prime) (e : S ≃* G) (h : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup G)) :
    2 ≤ CFSG.pRank r S := by
  rw [pRank_eq_open_pRank_top, pRank_top_eq_of_mulEquiv hr.one_lt e]
  exact h

section Sporadic

@[expose] def letterWord {G : Type*} [Group G] (a b : G) (w : List ℕ) : G :=
  (w.map fun i => if i = 0 then a else b).prod

@[expose] def m11WordX : List ℕ := [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1]

@[expose] def m11WordY : List ℕ := [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1]

theorem letterWord_mem_m11 (w : List ℕ) :
    letterWord CFSG.Sporadic.Mathieu.m11gA CFSG.Sporadic.Mathieu.m11gB w ∈ NativeSporadic.M11 := by
  unfold letterWord
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[irreducible] def m11X : Equiv.Perm (Fin 11) :=
  letterWord CFSG.Sporadic.Mathieu.m11gA CFSG.Sporadic.Mathieu.m11gB m11WordX

@[irreducible] def m11Y : Equiv.Perm (Fin 11) :=
  letterWord CFSG.Sporadic.Mathieu.m11gA CFSG.Sporadic.Mathieu.m11gB m11WordY

theorem m11X_mem : m11X ∈ NativeSporadic.M11 := by
  unfold m11X
  exact letterWord_mem_m11 _

theorem m11Y_mem : m11Y ∈ NativeSporadic.M11 := by
  unfold m11Y
  exact letterWord_mem_m11 _

theorem m11X_pow : m11X ^ 3 = 1 := by decide +kernel

theorem m11Y_pow : m11Y ^ 3 = 1 := by decide +kernel

theorem m11_comm : m11X * m11Y = m11Y * m11X := by decide +kernel

theorem m11X_ne_one : m11X ≠ 1 := by decide +kernel

theorem m11Y_ne_one : m11Y ≠ 1 := by decide +kernel

theorem m11Y_ne_X : m11Y ≠ m11X := by decide +kernel

theorem m11Y_ne_X_sq : m11Y ≠ m11X ^ 2 := by decide +kernel

theorem two_le_pRank_three_M11 {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.M11) :
    2 ≤ CFSG.pRank 3 S := by
  have : Finite NativeSporadic.M11 := Finite.of_equiv S e.toEquiv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let x : NativeSporadic.M11 := ⟨m11X, m11X_mem⟩
  let y : NativeSporadic.M11 := ⟨m11Y, m11Y_mem⟩
  have hx3 : x ^ 3 = 1 := Subtype.ext m11X_pow
  have hy3 : y ^ 3 = 1 := Subtype.ext m11Y_pow
  have hxy : x * y = y * x := Subtype.ext m11_comm
  have hx1 : x ≠ 1 := fun h => m11X_ne_one (congrArg Subtype.val h)
  have hy1 : y ≠ 1 := fun h => m11Y_ne_one (congrArg Subtype.val h)
  have hyx : y ≠ x := fun h => m11Y_ne_X (congrArg Subtype.val h)
  have hyx2 : y ≠ x ^ 2 := fun h => m11Y_ne_X_sq (congrArg Subtype.val h)
  refine two_le_pRank_of_mulEquiv Nat.prime_three e (two_le_pRank_of_gens hx3 hy3 hxy hx1 ?_)
  intro n hn
  have hn' : x ^ (n % 3) = y := by
    rw [← pow_eq_pow_mod n hx3]
    exact hn
  have : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : n % 3
  · exact hy1 (by rw [← hn']; simp)
  · exact hyx (by rw [← hn']; simp)
  · exact hyx2 hn'.symm


theorem two_le_pRank_three_M12
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.M12) :
    2 ≤ CFSG.pRank 3 S := by
  have : Finite NativeSporadic.M12 := Finite.of_equiv S e.toEquiv
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, -⟩ := M12_sylow3_cubic_witness
  exact two_le_pRank_of_mulEquiv Nat.prime_three e
    (two_le_pRank_of_cubic_witness Nat.prime_three hx hz hzx hzy)

theorem two_le_pRank_three_M24
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.M24) :
    2 ≤ CFSG.pRank 3 S := by
  have : Finite NativeSporadic.M24 := Finite.of_equiv S e.toEquiv
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, -⟩ := M24_sylow3_cubic_witness
  exact two_le_pRank_of_mulEquiv Nat.prime_three e
    (two_le_pRank_of_cubic_witness Nat.prime_three hx hz hzx hzy)

theorem two_le_pRank_three_J2
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.J2) :
    2 ≤ CFSG.pRank 3 S := by
  have : Finite NativeSporadic.J2 := Finite.of_equiv S e.toEquiv
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, -⟩ := J2_sylow3_cubic_witness
  exact two_le_pRank_of_mulEquiv Nat.prime_three e
    (two_le_pRank_of_cubic_witness Nat.prime_three hx hz hzx hzy)

theorem two_le_pRank_three_J4
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.J4) :
    2 ≤ CFSG.pRank 3 S := by
  have : Finite NativeSporadic.J4 := Finite.of_equiv S e.toEquiv
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, -⟩ := J4_sylow3_cubic_witness
  refine two_le_pRank_of_mulEquiv (G := NativeSporadic.J4) Nat.prime_three e ?_
  exact two_le_pRank_of_cubic_witness Nat.prime_three hx hz hzx hzy

theorem two_le_pRank_three_HS
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.HS) :
    2 ≤ CFSG.pRank 3 S := by
  have : Finite NativeSporadic.HS := Finite.of_equiv S e.toEquiv
  obtain ⟨x, y, h, hx, hy, hxy, hQ, -⟩ := HS_sylow3_square_witness
  refine two_le_pRank_of_mulEquiv (G := NativeSporadic.HS) Nat.prime_three e ?_
  exact two_le_pRank_of_square_witness Nat.prime_three hx hy hxy hQ

theorem two_le_pRank_three_He
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.He) :
    2 ≤ CFSG.pRank 3 S := by
  have : Finite NativeSporadic.He := Finite.of_equiv S e.toEquiv
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, -⟩ := He_sylow3_cubic_witness
  refine two_le_pRank_of_mulEquiv (G := NativeSporadic.He) Nat.prime_three e ?_
  exact two_le_pRank_of_cubic_witness Nat.prime_three hx hz hzx hzy

theorem two_le_pRank_three_Ru
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Ru) :
    2 ≤ CFSG.pRank 3 S := by
  have : Finite NativeSporadic.Ru := Finite.of_equiv S e.toEquiv
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, -⟩ := Ru_sylow3_cubic_witness
  refine two_le_pRank_of_mulEquiv (G := NativeSporadic.Ru) Nat.prime_three e ?_
  exact two_le_pRank_of_cubic_witness Nat.prime_three hx hz hzx hzy

end Sporadic



section Small

open CFSG.Assembly.LowTwoRank CFSG.Quasithin

theorem statedClassicalModel_psl_two_five_of_alternating
    {S : Type} [Group S]
    (e : S ≃* alternatingGroup (Fin 5)) : StatedClassicalModel S .PSL 2 5 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five (ZMod 5)
    (Or.inr (Nat.card_zmod 5))
  exact ⟨⟨Nat.prime_five, le_rfl, le_rfl, by decide, by decide⟩, ZMod 5, inferInstance,
    inferInstance, by rw [Nat.card_zmod, pow_one], ⟨e.trans e5.symm⟩⟩

theorem statedClassicalModel_psl_two_seven_of_three_two {S : Type} [Group S]
    (h : StatedClassicalModel S .PSL 3 2 1) : StatedClassicalModel S .PSL 2 7 1 := by
  have h' : CFSG.Blueprint.LieModel S .PSL 3 2 1 := Or.inl ⟨by decide, h⟩
  rcases CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism S h' with
    ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact hc
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem two_le_pRank_three_of_alternating {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 6 ≤ n)
    (e : S ≃* alternatingGroup (Fin n)) : 2 ≤ CFSG.pRank 3 S := by
  rw [pRank_eq_open_pRank_top, pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  exact le_pRank (by norm_num) le_top (isElemAbelian_sylowThreeAlt hn) (card_sylowThreeAlt hn)

end Small


section Main

open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.QuasithinUnique.Setup.Family

theorem a134RankOne_of_inputs
    (hOdd : OddRankOneOddClassicalProp)
    (hChev : ∀ (S : Type) [Group S] [Finite S], OddRankLeOne S → ∀ (t : StatedLieTag) (p f : ℕ),
      ChevalleyExceptionalModel S t p f → t = .trialityD4 ∧ p = 2 ∧ f = 1)
    (hRT : ∀ (S : Type) [Group S] [Finite S], OddRankLeOne S → ∀ (t : StatedLieTag) (p f : ℕ),
      ¬ ReeTitsModel S t p f)
    (hTri : TrialityTwoHasRankTwoProp)
    (hM22 : ∀ (S : Type) [Group S] [Finite S], NativeSporadic.IsSporadic S .M22 →
      2 ≤ CFSG.pRank 3 S)
    (hM23 : ∀ (S : Type) [Group S] [Finite S], NativeSporadic.IsSporadic S .M23 →
      2 ≤ CFSG.pRank 3 S)
    (hPSL3 : ∀ (S : Type) [Group S] [Finite S] (f : ℕ), 2 ≤ f → StatedClassicalModel S .PSL 3 2 f →
      ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.pRank r S)
    (hPSU3 : ∀ (S : Type) [Group S] [Finite S] (f : ℕ), 2 ≤ f → StatedClassicalModel S .PSU 3 2 f →
      ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.pRank r S)
    (hPSp4 : ∀ (S : Type) [Group S] [Finite S] (f : ℕ), 2 ≤ f → StatedClassicalModel S .PSp 2 2 f →
      ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.pRank r S)
    (hPSLn : ∀ (S : Type) [Group S] [Finite S] (n : ℕ), (n = 4 ∨ n = 5) →
      StatedClassicalModel S .PSL n 2 1 → ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.pRank r S)
    (S : Type) [Group S] [Finite S] (hlist : A23ListCat S) (hS : OddRankLeOne S) :
    A134Types S := by
  have hfalse : ∀ {r : ℕ}, r.Prime → r ≠ 2 → 2 ≤ CFSG.pRank r S → False := fun hr hr2 h => by
    have := hS _ hr hr2
    omega
  rcases hlist with ⟨n, hn5, hn8, ⟨e⟩⟩ | ⟨p, hp, hp2, hcl⟩ | ⟨⟨f, hf⟩ | hT⟩ | ⟨n, hn, hm⟩ |
      ⟨s, hs, ⟨e⟩⟩
  ·
    by_cases h5 : n = 5
    · subst h5
      exact Or.inr (Or.inr (Or.inr ⟨5, 1, by norm_num, by norm_num, le_rfl, by norm_num,
        statedClassicalModel_psl_two_five_of_alternating e⟩))
    · exact (hfalse Nat.prime_three (by norm_num)
        (two_le_pRank_three_of_alternating (by omega) e)).elim
  ·
    rcases hcl with ⟨f, -, hm⟩ | hm | hm
    · obtain ⟨-, -, rfl, hp5⟩ := hOdd S hS p hp hp2 .PSL 2 f hm
      exact Or.inr (Or.inr (Or.inr ⟨p, 1, hp, by omega, le_rfl, by norm_num, hm⟩))
    · obtain ⟨-, h3, -⟩ := hOdd S hS p hp hp2 .PSL 3 1 hm
      omega
    · obtain ⟨h, -⟩ := hOdd S hS p hp hp2 .PSU 3 1 hm
      cases h
  ·
    rcases hf with ⟨-, hm⟩ | ⟨hf1, hm⟩ | ⟨hf2, hm⟩ | ⟨hf2, hm⟩ | ⟨hf2, hm⟩ | ⟨-, hm⟩ | ⟨-, -, hm⟩ |
        ⟨-, -, hm⟩
    · exact Or.inl ⟨f, hm⟩
    · by_cases hf2 : 2 ≤ f
      · obtain ⟨r, hr, hr2, h2⟩ := hPSL3 S f hf2 hm
        exact (hfalse hr hr2 h2).elim
      · have hf1' : f = 1 := by omega
        subst hf1'
        exact Or.inr (Or.inr (Or.inr ⟨7, 1, by norm_num, by norm_num, le_rfl, by norm_num,
          statedClassicalModel_psl_two_seven_of_three_two hm⟩))
    · obtain ⟨r, hr, hr2, h2⟩ := hPSU3 S f hf2 hm
      exact (hfalse hr hr2 h2).elim
    · obtain ⟨r, hr, hr2, h2⟩ := hPSp4 S f hf2 hm
      exact (hfalse hr hr2 h2).elim
    · obtain ⟨h, -, -⟩ := hChev S hS .G2 2 f hm
      cases h
    · obtain ⟨-, -, hf1⟩ := hChev S hS .trialityD4 2 f hm
      subst hf1
      exact (hfalse Nat.prime_three (by norm_num) (hTri S hm)).elim
    · exact (hRT S hS .twistedF4 2 f hm).elim
    · exact Or.inr (Or.inl ⟨f, hm⟩)
  · exact (hRT S hS .Tits 2 1 hT).elim
  ·
    obtain ⟨r, hr, hr2, h2⟩ := hPSLn S n hn hm
    exact (hfalse hr hr2 h2).elim
  ·
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hfalse Nat.prime_three (by norm_num) (two_le_pRank_three_M11 e)).elim
    · exact (hfalse Nat.prime_three (by norm_num) (two_le_pRank_three_M12 e)).elim
    · exact (hfalse Nat.prime_three (by norm_num) (hM22 S ⟨e⟩)).elim
    · exact (hfalse Nat.prime_three (by norm_num) (hM23 S ⟨e⟩)).elim
    · exact (hfalse Nat.prime_three (by norm_num) (two_le_pRank_three_M24 e)).elim
    · exact Or.inr (Or.inr (Or.inl ⟨e⟩))
    · exact (hfalse Nat.prime_three (by norm_num) (two_le_pRank_three_J2 e)).elim
    · exact (hfalse Nat.prime_three (by norm_num) (two_le_pRank_three_J4 e)).elim
    · exact (hfalse Nat.prime_three (by norm_num) (two_le_pRank_three_HS e)).elim
    · exact (hfalse Nat.prime_three (by norm_num) (two_le_pRank_three_He e)).elim
    · exact (hfalse Nat.prime_three (by norm_num) (two_le_pRank_three_Ru e)).elim

theorem a134RankOneFact_of_triality
    (hTri : TrialityTwoHasRankTwoProp) : A134RankOneFact :=
  fun S _ _ hlist hS =>
  a134RankOne_of_inputs oddRankOneOddClassical
    (fun S _ _ hS t p f h =>
      CFSG.RankThree.Chevalley.odd_rank_one_Chevalley_exceptional_model_is_binary_triality S hS t p
        f h)
    (fun S _ _ hS t p f =>
      CFSG.RankThree.Chevalley.odd_rank_one_excludes_all_Ree_Tits_models S hS t p f)
    hTri (fun _ _ _ h => (CFSG.RankThree.Asc83Table.M22.table h).2.1.ge)
    (fun _ _ _ h => (CFSG.RankThree.Asc83Table.M23.table h).2.1.ge)
    (fun _ _ _ _ hf hm => EvenWit.exists_two_le_pRank_psl_three_even hf hm)
    (fun _ _ _ _ hf hm => EvenWit.exists_two_le_pRank_psu_three_even hf hm)
    (fun _ _ _ _ _ hm => EvenWit.exists_two_le_pRank_psp_of_two_le (by norm_num) hm)
    (fun _ _ _ n hn hm => EvenWit.exists_two_le_pRank_psl_of_four_le (by omega) hm) S hlist hS

end Main

end CFSG.QuasithinUnique.Vol2Native

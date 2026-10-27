module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal
import CFSG.LocalAnalysis.RankThreeTheoremC.PSLTwoRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem exists_isElemAbelian_card_succ_le {p s : ℕ} [Fact p.Prime] {A E C : Subgroup G}
    (hA : Nat.card A = p) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ s) (hAC : A ≤ C)
    (hEC : E ≤ C) (hcomm : ∀ a ∈ A, ∀ b ∈ E, a * b = b * a) (hdisj : A ⊓ E = ⊥) :
    ∃ F : Subgroup G, F ≤ C ∧ IsElemAbelian p F ∧ Nat.card F = p ^ (s + 1) := by
  let φ : A × E →* G := A.subtype.noncommCoprod E.subtype fun a b => hcomm a a.2 b b.2
  have hφ : ∀ x : A × E, φ x = (x.1 : G) * (x.2 : G) := fun x =>
    MonoidHom.noncommCoprod_apply _ _ _ x
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ h
    rw [hφ] at h
    have hab : (a : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left h
    have ha1 : (a : G) ∈ A ⊓ E := ⟨a.2, by rw [hab]; exact E.inv_mem b.2⟩
    rw [hdisj] at ha1
    have ha : a = 1 := Subtype.ext (mem_bot.mp ha1)
    have hb : b = 1 := Subtype.ext (by simpa [ha] using h)
    rw [ha, hb]
    rfl
  have hAcomm : IsMulCommutative A := (isCyclic_of_prime_card hA).isMulCommutative
  refine ⟨φ.range, ?_, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨u, rfl⟩
    rw [hφ]
    exact C.mul_mem (hAC u.1.2) (hEC u.2.2)
  · refine isMulCommutative_iff.mpr fun x y => ?_
    obtain ⟨u, hu⟩ := x.2
    obtain ⟨v, hv⟩ := y.2
    apply Subtype.ext
    change (x : G) * y = y * x
    rw [← hu, ← hv, ← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (hAcomm.is_comm.comm _ _) (hE.1.is_comm.comm _ _)
  · rintro x ⟨u, rfl⟩
    rw [← map_pow]
    have h1 : u.1 ^ p = 1 := by
      have := (pow_card_eq_one' : u.1 ^ Nat.card A = 1)
      rwa [hA] at this
    have h2 : u.2 ^ p = 1 := Subtype.ext (hE.2 _ u.2.2)
    rw [show u ^ p = 1 from Prod.ext h1 h2, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod, hA, hEcard,
      pow_succ, mul_comm]

private theorem succ_le_pRank_of_layer {p : ℕ} [Fact p.Prime] {P₀ C : Subgroup G}
    (hcard : Nat.card P₀ = p) (hPC : P₀ ≤ C) (hCP : centralizer (P₀ : Set G) ≤ C) {m : ℕ}
    (hm : 2 ≤ m)
    (e : rankThreeLayer (centralizer (P₀ : Set G)) ≃* PSL(2, GaloisField p m)) :
    m + 1 ≤ CFSG.Open.pRank p C := by
  have hprime : p.Prime := Fact.out
  set L := rankThreeLayer (centralizer (P₀ : Set G))
  have hLC : L ≤ centralizer (P₀ : Set G) := rankThreeLayer_le _
  have hm0 : m ≠ 0 := by omega
  have hs : m ≤ CFSG.Open.pRank p (⊤ : Subgroup PSL(2, GaloisField p m)) :=
    le_pRank_psl_two p m hm0
  obtain ⟨E₀, -, hE₀, hE₀card⟩ :=
    pRank_attained p (⊤ : Subgroup PSL(2, GaloisField p m)) (by omega)
  generalize CFSG.Open.pRank p (⊤ : Subgroup PSL(2, GaloisField p m)) = s at hs hE₀card
  let ι : PSL(2, GaloisField p m) →* G := L.subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι := L.subtype_injective.comp e.symm.injective
  have hEL : E₀.map ι ≤ L := by
    rintro _ ⟨x, -, rfl⟩
    exact (e.symm x).2
  have hEelem : IsElemAbelian p (E₀.map ι) := elementary_map_injective p E₀ ι hι hE₀
  have hEcard : Nat.card (E₀.map ι) = p ^ s := by
    rw [card_map_of_injective hι, hE₀card]
  have hsimple : IsSimpleGroup L := by
    refine e.isSimpleGroup_congr.mpr (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple ?_)
    rw [GaloisField.card p m hm0]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hprime.two_le 2
      _ ≤ p ^ m := Nat.pow_le_pow_right hprime.pos hm
  have hN : (P₀.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hcomm : (n : G) * g = g * n := mem_centralizer_iff.mp (hLC g.2) n hn
    rw [show g * n = n * g from Subtype.ext hcomm.symm, mul_inv_cancel_right]
    exact hn
  have hdisj : P₀ ⊓ E₀.map ι = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (P₀.subgroupOf L) with h | h
    · rw [eq_bot_iff]
      rintro x ⟨hxP, hxE⟩
      have hx : (⟨x, hEL hxE⟩ : L) ∈ P₀.subgroupOf L := hxP
      rw [h] at hx
      exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hx))
    · exfalso
      have hLP : E₀.map ι ≤ P₀ := fun x hx =>
        show (⟨x, hEL hx⟩ : L) ∈ P₀.subgroupOf L from h ▸ mem_top _
      have hle := card_le_of_le hLP
      rw [hEcard, hcard] at hle
      have h2 : p ^ 2 ≤ p ^ s := Nat.pow_le_pow_right hprime.pos (hm.trans hs)
      nlinarith [hprime.two_le]
  obtain ⟨F, hFC, hF, hFcard⟩ := exists_isElemAbelian_card_succ_le hcard hEelem hEcard hPC
    (hEL.trans (hLC.trans hCP))
    (fun a ha b hb => mem_centralizer_iff.mp (hLC (hEL hb)) a ha) hdisj
  have hrank : s + 1 ≤ CFSG.Open.pRank p C := by
    unfold CFSG.Open.pRank
    exact le_csSup (pRank_set_bddAbove p hprime.one_lt C) ⟨F, hFC, hF, hFcard⟩
  omega

theorem exists_isLargeObstruction_of_clauseB (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hB : rankThreeClauseB M (P : Subgroup G) p) : ∃ y : G, IsLargeObstruction p M y := by
  obtain ⟨-, -, P₀, hP₀P, hcard, -, ⟨hfact, m, hm, ⟨e⟩⟩, hLM, -⟩ := hB
  have hprime : p.Prime := hfact.out
  obtain ⟨y, hyP₀, hy1⟩ : ∃ y ∈ P₀, y ≠ 1 := by
    by_contra h
    push Not at h
    rw [(eq_bot_iff_forall P₀).mpr h, Subgroup.card_bot] at hcard
    exact hprime.one_lt.ne hcard
  have hyp : y ^ p = 1 := by
    have h := (pow_card_eq_one' : (⟨y, hyP₀⟩ : P₀) ^ Nat.card P₀ = 1)
    rw [hcard] at h
    simpa using congrArg Subtype.val h
  have hcomm : IsMulCommutative P₀ := (isCyclic_of_prime_card hcard).isMulCommutative
  have hPC : P₀ ≤ centralizer ({y} : Set G) := fun h hh =>
    mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (hcomm.is_comm.comm (⟨h, hh⟩ : P₀) ⟨y, hyP₀⟩))
  have hCP : centralizer (P₀ : Set G) ≤ centralizer ({y} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr hyP₀)
  refine ⟨y, (sylow_le_of_isCoreMaxLocal hS hp hM).1 (hP₀P hyP₀), hy1, hyp, ?_, ?_⟩
  · have := succ_le_pRank_of_layer hcard hPC hCP hm e
    omega
  · intro hle
    exact hLM ((rankThreeLayer_le _).trans (hCP.trans hle))

end CFSG.LocalAnalysis.RankThreeTheoremC

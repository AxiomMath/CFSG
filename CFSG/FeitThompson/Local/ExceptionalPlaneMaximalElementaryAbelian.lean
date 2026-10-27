module

public import CFSG.FeitThompson.Local.OutsideSigmaNormalizerRankTwoPlane
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Positivity.Finset

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G] {p : ℕ} {M A₀ A P : Subgroup G}

theorem not_normalizer_sylow_le_of_notMem_sigmaPrimes (hp : p.Prime) (hpM : p ∉ sigmaPrimes M)
    (hdvd : p ∣ Nat.card M) (S : Sylow p M) :
    ¬ normalizer (((S : Subgroup M).map M.subtype : Subgroup G) : Set G) ≤ M :=
  fun h => hpM (mem_sigmaPrimes_iff.2 ⟨hp, hdvd, S, h⟩)

theorem not_normalizer_le_of_notMem_sigmaPrimes [Finite G] (hp : p.Prime)
    (hpM : p ∉ sigmaPrimes M) (hdvd : p ∣ Nat.card M) (hPM : P ≤ M)
    (hPcard : Nat.card P = p ^ (Nat.card M).factorization p) :
    ¬ normalizer (P : Set G) ≤ M :=
  fun h => hpM ((mem_sigmaPrimes_iff_exists_subgroup hp).2 ⟨hdvd, P, hPM, hPcard, h⟩)

theorem centralizer_le_of_le_of_normalizer_le (hA₀A : A₀ ≤ A)
    (hNA₀ : normalizer (A₀ : Set G) ≤ M) : centralizer (A : Set G) ≤ M :=
  (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hA₀A)).trans
    ((Subgroup.centralizer_le_normalizer _).trans hNA₀)

theorem eq_of_isElementaryAbelian_of_le_of_centralizer_le [Finite G] (hp : p.Prime)
    (hAcard : Nat.card A = p ^ 2) (hCM : centralizer (A : Set G) ≤ M)
    (hrank : elementaryAbelianPRank p M = 2) {E : Subgroup G} (hE : IsElementaryAbelian p E)
    (hAE : A ≤ E) : E = A := by
  have hEM : E ≤ M := (hE.le_centralizer hAE).trans hCM
  obtain ⟨d, hd⟩ := hE.exists_natCard_eq_pow hp
  have hd2 : d ≤ 2 := hrank ▸ hE.le_elementaryAbelianPRank hp hd hEM
  refine (Subgroup.eq_of_le_of_card_ge hAE ?_).symm
  rw [hd, hAcard]
  exact Nat.pow_le_pow_right hp.pos hd2

theorem not_lt_of_isElementaryAbelian_of_centralizer_le [Finite G] (hp : p.Prime)
    (hAcard : Nat.card A = p ^ 2) (hCM : centralizer (A : Set G) ≤ M)
    (hrank : elementaryAbelianPRank p M = 2) {E : Subgroup G} (hE : IsElementaryAbelian p E) :
    ¬ A < E := fun hlt =>
  hlt.ne' (eq_of_isElementaryAbelian_of_le_of_centralizer_le hp hAcard hCM hrank hE hlt.le)

theorem maximal_isElementaryAbelian_of_centralizer_le [Finite G] (hp : p.Prime)
    (hAea : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 2)
    (hCM : centralizer (A : Set G) ≤ M) (hrank : elementaryAbelianPRank p M = 2) :
    Maximal (IsElementaryAbelian p) A :=
  ⟨hAea, fun _ hE hAE =>
    (eq_of_isElementaryAbelian_of_le_of_centralizer_le hp hAcard hCM hrank hE hAE).le⟩

theorem exceptional_maximal_plane [Finite G] [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable Y)
    (hM : IsCoatom M) (hp : p.Prime) (hpM : p ∉ sigmaPrimes M) (hA₀ : Nat.card A₀ = p)
    (hA₀A : A₀ ≤ A) (hAP : A ≤ P) (hPM : P ≤ M)
    (hPcard : Nat.card P = p ^ (Nat.card M).factorization p) (hAea : IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 2) (hNA₀ : normalizer (A₀ : Set G) ≤ M) :
    elementaryAbelianPRank p M = 2 ∧ ¬ normalizer (P : Set G) ≤ M ∧
      centralizer (A : Set G) ≤ M ∧
      ∀ E : Subgroup G, IsElementaryAbelian p E → ¬ A < E := by
  have hdvd : p ∣ Nat.card M := hA₀ ▸ Subgroup.card_dvd_of_le (hA₀A.trans (hAP.trans hPM))
  have hrank : elementaryAbelianPRank p M = 2 :=
    elementaryAbelianPRank_eq_two_of_notMem_sigmaPrimes hna hodd hsolv hM hp hpM hA₀ hNA₀
  have hCM : centralizer (A : Set G) ≤ M := centralizer_le_of_le_of_normalizer_le hA₀A hNA₀
  have hmax : Maximal (IsElementaryAbelian p) A :=
    maximal_isElementaryAbelian_of_centralizer_le hp hAea hAcard hCM hrank
  exact ⟨hrank, not_normalizer_le_of_notMem_sigmaPrimes hp hpM hdvd hPM hPcard, hCM,
    fun _ hE hlt => hlt.ne' (hmax.eq_of_ge hE hlt.le)⟩

theorem exceptional_maximal_plane_sylow [Finite G] [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable Y)
    (hM : IsCoatom M) (hp : p.Prime) (hpM : p ∉ sigmaPrimes M) (hA₀ : Nat.card A₀ = p)
    (hA₀A : A₀ ≤ A) (S : Sylow p M) (hAP : A ≤ (S : Subgroup M).map M.subtype)
    (hAea : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 2)
    (hNA₀ : normalizer (A₀ : Set G) ≤ M) :
    elementaryAbelianPRank p M = 2 ∧
      ¬ normalizer (((S : Subgroup M).map M.subtype : Subgroup G) : Set G) ≤ M ∧
      centralizer (A : Set G) ≤ M ∧ Maximal (IsElementaryAbelian p) A := by
  have hdvd : p ∣ Nat.card M :=
    hA₀ ▸ Subgroup.card_dvd_of_le (hA₀A.trans (hAP.trans (Subgroup.map_subtype_le _)))
  have hrank : elementaryAbelianPRank p M = 2 :=
    elementaryAbelianPRank_eq_two_of_notMem_sigmaPrimes hna hodd hsolv hM hp hpM hA₀ hNA₀
  have hCM : centralizer (A : Set G) ≤ M := centralizer_le_of_le_of_normalizer_le hA₀A hNA₀
  exact ⟨hrank, not_normalizer_sylow_le_of_notMem_sigmaPrimes hp hpM hdvd S, hCM,
    maximal_isElementaryAbelian_of_centralizer_le hp hAea hAcard hCM hrank⟩

theorem exceptional_maximal_plane_mulEquiv [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable Y) (hM : IsCoatom M) (hp : p.Prime)
    (hpM : p ∉ sigmaPrimes M) (hA₀ : Nat.card A₀ = p) (hA₀A : A₀ ≤ A) (hAP : A ≤ P) (hPM : P ≤ M)
    (hPcard : Nat.card P = p ^ (Nat.card M).factorization p)
    (hA : Nonempty (A ≃* (Fin 2 → Multiplicative (ZMod p))))
    (hNA₀ : normalizer (A₀ : Set G) ≤ M) :
    elementaryAbelianPRank p M = 2 ∧ ¬ normalizer (P : Set G) ≤ M ∧
      centralizer (A : Set G) ≤ M ∧
      ∀ E : Subgroup G, IsElementaryAbelian p E → ¬ A < E := by
  obtain ⟨e⟩ := hA
  exact exceptional_maximal_plane hna hodd hsolv hM hp hpM hA₀ hA₀A hAP hPM hPcard
    (isElementaryAbelian_of_nonempty_mulEquiv_pi ⟨e⟩)
    (by rw [Nat.card_congr e.toEquiv, card_pi_multiplicative_zmod]) hNA₀

end

end CFSG.FeitThompson

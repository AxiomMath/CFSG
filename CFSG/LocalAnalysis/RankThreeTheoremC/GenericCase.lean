module

public import CFSG.LocalAnalysis.RankThreeTheoremC.PrimeInduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseExtremal
import CFSG.LocalAnalysis.RankThreeTheoremC.FusionControl
import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTheoremE
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseLayer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def IsGenericPoint (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x : G) : Prop :=
  x ∈ (P : Subgroup G) ∧ IsLargeObstruction p M x ∧
    CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
      (centralizer ({x} : Set G)) ∧
    CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) = 3

@[expose] def GL83GenericLayer (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M →
    ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M → LargerPrimesUnique G p →
      ∀ x : G, IsGenericPoint p P M x →
        5 ≤ p ∧ ∃ (_ : Fact p.Prime) (m : ℕ), 2 ≤ m ∧
          Nonempty (rankThreeLayer (centralizer ({x} : Set G)) ≃* PSL(2, GaloisField p m))

@[expose] def GL83GenericUniquePlane (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M →
    ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M → LargerPrimesUnique G p →
      ∀ x : G, IsGenericPoint p P M x →
        ∀ R : Subgroup G, R ≤ P → IsElemAbelian p R → Nat.card R = p ^ 2 → x ∈ R →
          ∀ H : Subgroup G, IsTwoLocal H → R ≤ H → H ≤ M

@[expose] def GL83GenericStructure (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M →
    ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M → LargerPrimesUnique G p →
      ∀ x : G, IsGenericPoint p P M x →
        (∀ y : G, IsGenericPoint p P M y → zpowers y = zpowers x) ∧
          IsMulCommutative (P : Subgroup G) ∧ Group.IsSolvable M ∧
          rankThreeFrobeniusProduct (rankThreePrimeCore p M) (pCoreOf 2 M)
            (centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) : Set G))

theorem genericCase_of_inputs (hS : Setting G) (hD1 : TheoremD1 G) (hD2 : TheoremD2 G)
    (hU0 : FullCoreLocal G) (hL : GL83GenericLayer G) (hE : GL83GenericUniquePlane G)
    (hB : GL83GenericStructure G) : GenericCase G := by
  intro p hp P M hM hfail hex hIH
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨x₀, hx₀⟩ := hex
  obtain ⟨x, hxP, hx, hsyl, hx3⟩ := exists_largeObstruction_isSylowOf hS hU0 hp hM hx₀
  have hgen : IsGenericPoint p P M x := ⟨hxP, hx, hsyl, hx3⟩
  obtain ⟨h5, hlayer⟩ := hL p hp P M hM hfail hIH x hgen
  have hLM : ¬ rankThreeLayer (centralizer ({x} : Set G)) ≤ M := by
    obtain ⟨-, -, -, -, hxCM⟩ := id hx
    obtain ⟨hf, m, hm2, ⟨e⟩⟩ := hlayer
    exact not_rankThreeLayer_le_of_mulEquiv_psl hS hU0 hp hM hxCM hsyl hm2 e
  obtain ⟨hU, hPab, hsolv, hfrob⟩ := hB p hp P M hM hfail hIH x hgen
  obtain ⟨-, hx1, hxp, -, -⟩ := id hx
  have hPC : ∀ y ∈ (P : Subgroup G), (P : Subgroup G) ≤ centralizer ({y} : Set G) :=
    fun y hy g hg => mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hPab.is_comm.comm ⟨g, hg⟩ ⟨y, hy⟩))
  have hobs : ∀ y ∈ (P : Subgroup G), y ≠ 1 → y ^ p = 1 → ¬ centralizer ({y} : Set G) ≤ M →
      zpowers y = zpowers x := by
    intro y hyP hy1 hyp hyM
    have hinf : (P : Subgroup G) ⊓ centralizer ({y} : Set G) = P := inf_of_le_left (hPC y hyP)
    refine hU y ⟨hyP, ⟨hPM hyP, hy1, hyp, hP3.ge.trans (pRank_mono p hprime.one_lt (hPC y hyP)),
      hyM⟩, ?_, by rw [hinf, hP3]⟩
    rw [hinf]
    exact ⟨P.subtype (hPC y hyP), by rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le (hPC y hyP)]⟩
  have hCx : centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  refine ⟨Or.inr (Or.inl ⟨h5, hsolv, zpowers x, zpowers_le.mpr hxP, ?_, ?_, ?_, ?_, ?_, ?_⟩),
    fun H hH h2 => ?_⟩
  · rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
  ·
    intro g hg
    obtain ⟨c, hcM, hc⟩ := exists_mem_conj_eq_of_map_le hS hU0 hp hM (zpowers_le.mpr hxP) hg
    have hy : (MulAut.conj g⁻¹).toMonoidHom x = MulAut.conj c⁻¹ x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact (hc x (mem_zpowers x)).symm
    have hyP : MulAut.conj c⁻¹ x ∈ (P : Subgroup G) := hy ▸ hg (mem_map_of_mem _ (mem_zpowers x))
    obtain ⟨-, hy1, hyp, -, hyM⟩ := hx.conj (M.inv_mem hcM)
    change (zpowers x).map (MulAut.conj g⁻¹).toMonoidHom = zpowers x
    rw [MonoidHom.map_zpowers, hy]
    exact hobs _ hyP hy1 hyp hyM
  · rw [hCx]
    exact hlayer
  · rw [hCx]
    exact hLM
  · rw [hCx]
    exact hfrob
  ·
    intro Y hYP hYc hYne
    have hYne' : Y ≠ ⊥ := fun h => by
      rw [h, card_bot] at hYc
      exact hprime.one_lt.ne hYc
    obtain ⟨⟨y, hyY⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hYne'
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hyp : y ^ p = 1 := by
      have := pow_card_eq_one' (G := Y) (x := ⟨y, hyY⟩)
      rw [hYc] at this
      exact congrArg Subtype.val this
    have hYy : zpowers y = Y := by
      refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hyY) ?_
      rw [hYc, Nat.card_zpowers, orderOf_eq_prime hyp hy1']
    by_contra hNM
    rw [← hYy] at hNM hYne
    refine hYne (hobs y (hYP hyY) hy1' hyp fun hCM => hNM ?_)
    exact normalizer_zpowers_le_of_centralizer_le hS hU0 hp hM
      (by rw [inf_of_le_left (hPC y (hYP hyY)), hP3]; norm_num) hCM
  ·
    refine le_of_two_le_pRank_of_elemAbelian_obstructed hS hD2 hU0 hp hM
      (fun h3 => absurd (eq_three_of_three_mem_sigmaA hS.rank h3 hp) (by omega)) ?_ hH h2
    intro R hRP hRe k hk hRc y hyR hy1 hyp hyM H' hH' hRH'
    have hxR : x ∈ R := zpowers_le.mpr hyR (hobs y (hRP hyR) hy1 hyp hyM ▸ mem_zpowers x)
    rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | hk3
    · exact hE p hp P M hM hfail hIH x hgen R hRP hRe hRc hxR H' hH' hRH'
    · refine le_of_three_le_pRank_inf hD1 hp hM hH' (hk3.trans ?_)
      unfold CFSG.Open.pRank
      exact le_csSup (pRank_set_bddAbove p hprime.one_lt _)
        ⟨R, le_inf hRH' (hRP.trans hPM), hRe, hRc⟩

end CFSG.LocalAnalysis.RankThreeTheoremC

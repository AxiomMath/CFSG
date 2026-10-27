module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerSplit
public import CFSG.LocalAnalysis.ABGTheoremB.Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionCentralizer
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.RankThree.PartOne.Planes Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem comm_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

omit [Finite G] in
private theorem isElemAbelian_of_le {p : ℕ} {E F : Subgroup G} (hE : IsElemAbelian p E)
    (hFE : F ≤ E) : IsElemAbelian p F := CFSG.Open.IsElemAbelian.mono hE hFE

theorem ExtremalObstruction.inf_centralizer_le (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hD : ¬ IsMulCommutative D) {z : G}
    (hzZ : z ∈ (center D).map D.subtype) (hz1 : z ≠ 1) {E : Subgroup G}
    (hEP : E ≤ (P : Subgroup G)) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) {y : G}
    (hyE : y ∈ E) (hyz : y ∉ zpowers z) :
    centralizer ({z} : Set G) ⊓ centralizer ({y} : Set G) ≤ M := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  have hP3 := (sylow_le_of_isCoreMaxLocal hS hp hM).2
  have hzp : z ^ p = 1 :=
    (hext.pow_eq_one_and_commutator_mem hprime hodd).1 z (map_subtype_le _ hzZ)
  have hzP : z ∈ (P : Subgroup G) := hDP (map_subtype_le _ hzZ)
  have hzc : z ∈ centralizer ((P : Subgroup G) : Set G) :=
    hext.center_le_centralizer hprime hodd hD hzZ
  have hzE : z ∈ E := by
    by_contra hzE
    have hcomm : ∀ e ∈ E, e * z = z * e := fun e he => mem_centralizer_iff.mp hzc e (hEP he)
    have hcard : Nat.card ↥(E ⊔ zpowers z) = p ^ 4 := by
      rw [card_sup_zpowers hprime E hzp hzE hcomm, hEc, ← pow_succ]
    have hF : CFSG.IsElementaryAbelian p ↥(E ⊔ zpowers z) := by
      have : CFSG.IsElementaryAbelian p E :=
        (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).2 hE
      have : CFSG.IsElementaryAbelian p (zpowers z) :=
        CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hzp
      exact CFSG.IsElementaryAbelian.sup_of_le_centralizer
        (zpowers_le.mpr (mem_centralizer_iff.mpr hcomm))
    have h4 : 4 ≤ CFSG.Open.pRank p (P : Subgroup G) := by
      unfold CFSG.Open.pRank
      exact le_csSup (pRank_set_bddAbove p hprime.one_lt _) ⟨E ⊔ zpowers z,
        sup_le hEP (zpowers_le.mpr hzP),
        (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hF, hcard⟩
    omega
  have hyp : y ^ p = 1 := hE.2 y hyE
  have hzy : z * y = y * z := comm_of_isElemAbelian hE hzE hyE
  have hYE : zpowers z ⊔ zpowers y ≤ E := sup_le (zpowers_le.mpr hzE) (zpowers_le.mpr hyE)
  have hYc : Nat.card ↥(zpowers z ⊔ zpowers y) = p ^ 2 := by
    have hcommY : ∀ e ∈ zpowers z, e * y = y * e := fun e he =>
      mem_centralizer_singleton_iff.mp
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hzy) he)
    rw [card_sup_zpowers hprime (zpowers z) hyp hyz hcommY, Nat.card_zpowers,
      orderOf_eq_prime hzp hz1, pow_two]
  have hYe : IsElemAbelian p (zpowers z ⊔ zpowers y) := isElemAbelian_of_le hE hYE
  have hY2 : 2 ≤ CFSG.Open.pRank p (zpowers z ⊔ zpowers y) := by
    unfold CFSG.Open.pRank
    exact le_csSup (pRank_set_bddAbove p hprime.one_lt _) ⟨_, le_rfl, hYe, hYc⟩
  have hEY : E ≤ (P : Subgroup G) ⊓ centralizer ((zpowers z ⊔ zpowers y : Subgroup G) : Set G) :=
    le_inf hEP fun e he => mem_centralizer_iff.mpr fun a ha =>
      comm_of_isElemAbelian hE (hYE ha) he
  have h3 : 3 ≤ CFSG.Open.pRank p ((zpowers z ⊔ zpowers y) ⊔
      ((P : Subgroup G) ⊓ centralizer ((zpowers z ⊔ zpowers y : Subgroup G) : Set G))) := by
    unfold CFSG.Open.pRank
    exact le_csSup (pRank_set_bddAbove p hprime.one_lt _) ⟨E, hEY.trans le_sup_right, hE, hEc⟩
  have hNY : normalizer ((zpowers z ⊔ zpowers y : Subgroup G) : Set G) ≤ M :=
    (aschCore_normalizer_le 2 p (P : Subgroup G) _ (hYE.trans hEP) hY2 h3).trans hM.2
  intro g hg
  have hgY : zpowers z ⊔ zpowers y ≤ centralizer ({g} : Set G) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hg.1).symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hg.2).symm))
  exact hNY (centralizer_le_normalizer ((zpowers z ⊔ zpowers y : Subgroup G) : Set G)
    (mem_centralizer_iff.mpr fun a ha => mem_centralizer_singleton_iff.mp (hgY ha)))

@[expose] def CentralizerGeneration (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    (P : Subgroup G) ≤ normalizer (D : Set G) → ∀ z ∈ (center D).map D.subtype, z ≠ 1 →
      ¬ CFSG.RankThreeCoreUniqueness.Helpers.HasPrimeConstraint (G := centralizer ({z} : Set G)) p →
        ∀ E : Subgroup G, E ≤ (P : Subgroup G) → IsElemAbelian p E → Nat.card E = p ^ 3 →
          centralizer ({z} : Set G) ≤
            CFSG.ABGTheoremB.pPrimeCoreIn p (centralizer ({z} : Set G)) ⊔
              (⨆ (y : G) (_ : y ∈ E) (_ : y ∉ zpowers z),
                centralizer ({z} : Set G) ⊓ centralizer ({y} : Set G))

theorem signalizerCentralNonConstrained_of_generation (hS : Setting G)
    (h : CentralizerGeneration G) : SignalizerCentralNonConstrained G := by
  intro p hp P M D hext hPD z hzZ hz1 hcon K _ _ _
  exfalso
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hD := (hext.exists_normal_plane hS hp hPD).1
  obtain ⟨hM, -, -, -⟩ := hext.obstruction
  have hP3 := (sylow_le_of_isCoreMaxLocal hS hp hM).2
  obtain ⟨E, hEP, hE, hEc⟩ := pRank_attained p (P : Subgroup G) (by omega)
  rw [hP3] at hEc
  have hzc := hext.center_le_centralizer hprime hodd hD hzZ
  have hPC : (P : Subgroup G) ≤ centralizer ({z} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzc g hg)
  have h3 : 3 ≤ CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer ({z} : Set G)) := by
    rw [inf_eq_left.mpr hPC, hP3]
  refine hext.centralizer_not_le_of_mem_center hS hp hD hzZ hz1
    ((h p hp P M D hext hPD z hzZ hz1 hcon E hEP hE hEc).trans
      (sup_le (pPrimeCoreIn_centralizer_le hS hp hM h3) ?_))
  exact iSup_le fun y => iSup_le fun hyE => iSup_le fun hyz =>
    hext.inf_centralizer_le hS hp hD hzZ hz1 hEP hE hEc hyE hyz

end CFSG.LocalAnalysis.RankThreeTheoremC

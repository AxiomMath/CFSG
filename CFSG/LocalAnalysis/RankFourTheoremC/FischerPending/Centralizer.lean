module

public import CFSG.LocalAnalysis.RankFourTheoremC.FischerPending.Core
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionCentre
public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC
  CFSG.RankThree.PartOne.Planes Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ObstructionSetting.centralizer_not_le_of_mem_center (hS : ObstructionSetting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hD : ¬ IsMulCommutative D) {z : G}
    (hzZ : z ∈ (center D).map D.subtype) (hz1 : z ≠ 1) :
    ¬ centralizer ({z} : Set G) ≤ M := by
  classical
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hM, hDP, -, hDM⟩ := hext.obstruction
  have hZc : Nat.card ((center D).map D.subtype) = p := hext.card_center_eq hprime hodd hD
  have hzp : z ^ p = 1 :=
    (hext.pow_eq_one_and_commutator_mem hprime hodd).1 z (map_subtype_le _ hzZ)
  have hZeq : zpowers z = (center D).map D.subtype := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hzZ) ?_
    rw [hZc, Nat.card_zpowers, orderOf_eq_prime hzp hz1]
  have hzc : z ∈ centralizer ((P : Subgroup G) : Set G) :=
    hext.center_le_centralizer hprime hodd hD hzZ
  have hPC : (P : Subgroup G) ≤ centralizer ({z} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzc g hg)
  have hND : normalizer (D : Set G) ≤ normalizer ((zpowers z : Subgroup G) : Set G) := by
    rw [hZeq]
    exact normalizer_le_normalizer_characteristic_map D (center D) inferInstance
  intro hCM
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup G) (centralizer ({z} : Set G)) :=
    ⟨P.subtype hPC, by rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hPC]⟩
  have hNz : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M :=
    (le_sup_normalizer_of_isSylowOf (normalizer_zpowers_le_normalizer_centralizer z)
      hPsyl).trans (sup_le hCM (hS.normalizer_sylow_le hp hM))
  exact hDM (hND.trans hNz)

theorem ObstructionSetting.isMulCommutative_of_normalizer_le (hS : ObstructionSetting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D)
    (hN : ∀ z ∈ D, z ≠ 1 → z ∈ centralizer (P : Set G) → z ^ p = 1 →
      normalizer ((zpowers z : Subgroup G) : Set G) ≤ M) :
    IsMulCommutative D := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  by_contra hD
  have hZne : (center D).map D.subtype ≠ ⊥ := by
    intro h
    have hc := hext.card_center_eq hprime hodd hD
    rw [h, card_bot] at hc
    exact hprime.one_lt.ne hc
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzD : z ∈ D := map_subtype_le _ hzZ
  have hzc := hext.center_le_centralizer hprime hodd hD hzZ
  have hzp := (hext.pow_eq_one_and_commutator_mem hprime hodd).1 z hzD
  exact hS.centralizer_not_le_of_mem_center hp hext hD hzZ hz1'
    ((centralizer_singleton_le_normalizer_zpowers z).trans (hN z hzD hz1' hzc hzp))

theorem ObstructionSetting.mem_of_mem_centralizer_of_isMulCommutative (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hDab : IsMulCommutative D)
    (hCM : centralizer (D : Set G) ≤ M) {y : G} (hyC : y ∈ centralizer (D : Set G))
    (hyp : y ^ p = 1) : y ∈ D := by
  classical
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hM, hDP, hD2, hDM⟩ := hext.obstruction
  have hPp : IsPGroup p (P : Subgroup G) := P.isPGroup'
  have hiso := hext.isIsolatedPlane_of_isMulCommutative hprime hDab
  obtain ⟨hDe, hDc⟩ := hext.isElemAbelian_of_isMulCommutative hprime hDab
  by_contra hyD
  have hDy : ∀ d ∈ D, d * y = y * d := fun d hd => mem_centralizer_iff.mp hyC d hd
  have hEc : Nat.card ↥(D ⊔ zpowers y) = p ^ 3 := by
    rw [card_sup_zpowers hprime D hyp hyD hDy, hDc, ← pow_succ]
  have hDe' : CFSG.IsElementaryAbelian p D :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p D).2 hDe
  have hye : CFSG.IsElementaryAbelian p (zpowers y) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hyp
  have hEe : CFSG.IsElementaryAbelian p ↥(D ⊔ zpowers y) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hyC)
  have hEC : D ⊔ zpowers y ≤ centralizer (D : Set G) :=
    sup_le (le_centralizer_iff_isMulCommutative.mpr hDab) (zpowers_le.mpr hyC)
  have hEN : D ⊔ zpowers y ≤ normalizer (D : Set G) := hEC.trans (centralizer_le_normalizer _)
  have hEM : D ⊔ zpowers y ≤ M := hEC.trans hCM
  have hEp : IsPGroup p ↥(D ⊔ zpowers y) := CFSG.IsElementaryAbelian.isPGroup p _
  obtain ⟨Q₁, hQ₁⟩ := (hEp.comap_subtype (K := normalizer (D : Set G))).exists_le_sylow
  set S₁ : Subgroup G := (Q₁ : Subgroup (normalizer (D : Set G))).map
    (normalizer (D : Set G)).subtype with hS₁
  have hS₁syl : CFSG.ABGLocalTools.IsSylowOf p S₁ (normalizer (D : Set G)) := ⟨Q₁, rfl⟩
  have hES₁ : D ⊔ zpowers y ≤ S₁ := fun e he => ⟨⟨e, hEN he⟩, hQ₁ he, rfl⟩
  obtain ⟨P₂, hS₁P₂⟩ := hS₁syl.isPGroup.exists_le_sylow
  obtain ⟨M₂, hM₂, -⟩ := hS.exists_isCoreMaxLocal hp P₂
  have hDM₂ : ¬ normalizer (D : Set G) ≤ M₂ := by
    intro hN
    have h3 : 3 ≤ CFSG.Open.pRank p (M₂ ⊓ M) := by
      unfold CFSG.Open.pRank
      exact le_csSup (pRank_set_bddAbove p hprime.one_lt _) ⟨_, le_inf (hEN.trans hN) hEM,
        (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hEe, hEc⟩
    have hM₂M := le_of_three_le_pRank_inf hD1 hp hM hM₂.1.1 h3
    have heq : M = M₂ := hM₂.1.2 M hM.1.1 hM₂M
    exact hDM (heq ▸ hN)
  have hDP₂ : D ≤ (P₂ : Subgroup G) := (le_sup_left.trans hES₁).trans hS₁P₂
  have hcard := hext.maximal P₂ M₂ D ⟨hM₂, hDP₂, hD2, hDM₂⟩
  obtain ⟨Q₀, hQ₀⟩ := ((hPp.to_inf_left (K := normalizer (D : Set G))).comap_subtype
    (K := normalizer (D : Set G))).exists_le_sylow
  set S₀ : Subgroup G := (Q₀ : Subgroup (normalizer (D : Set G))).map
    (normalizer (D : Set G)).subtype with hS₀
  have hS₀syl : CFSG.ABGLocalTools.IsSylowOf p S₀ (normalizer (D : Set G)) := ⟨Q₀, rfl⟩
  have hPS₀ : (P : Subgroup G) ⊓ normalizer (D : Set G) ≤ S₀ := fun e he =>
    ⟨⟨e, he.2⟩, hQ₀ he, rfl⟩
  have hS₀eq : S₀ = (P : Subgroup G) ⊓ normalizer (D : Set G) := by
    refine (Subgroup.eq_of_le_of_card_ge hPS₀ ?_).symm
    calc Nat.card S₀ = Nat.card S₁ := by rw [hS₀syl.card_eq, hS₁syl.card_eq]
      _ ≤ Nat.card ↥((P₂ : Subgroup G) ⊓ normalizer (D : Set G)) :=
          card_le_of_le (le_inf hS₁P₂ hS₁syl.le)
      _ ≤ Nat.card ↥((P : Subgroup G) ⊓ normalizer (D : Set G)) := hcard
  obtain ⟨g, -, hconj⟩ := hS₀syl.exists_mem_conj hS₁syl
  have hE'le : (D ⊔ zpowers y).map (MulAut.conj g⁻¹).toMonoidHom ≤
      (P : Subgroup G) ⊓ normalizer (D : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    rw [← hS₀eq]
    have := (hconj e).mp (hES₁ he)
    simpa [MulAut.conj_apply] using this
  have hE'e : CFSG.IsElementaryAbelian p ↥((D ⊔ zpowers y).map (MulAut.conj g⁻¹).toMonoidHom) :=
    CFSG.IsElementaryAbelian.map _
  have hE'c : Nat.card ↥((D ⊔ zpowers y).map (MulAut.conj g⁻¹).toMonoidHom) = p ^ 3 := by
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective, hEc]
  exact not_elemAbelian_cube_le_normalizer_of_isIsolatedPlane hprime hPp hiso hE'le hE'e hE'c

theorem ObstructionSetting.exists_mem_normalizer_not_mem_centralizer (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hDab : IsMulCommutative D) (hCM : centralizer (D : Set G) ≤ M) :
    ∃ n ∈ (P : Subgroup G), n ∈ normalizer (D : Set G) ∧ n ∉ centralizer (D : Set G) := by
  have hprime := sigmaA_prime p hp
  obtain ⟨hDe, -⟩ := hext.isElemAbelian_of_isMulCommutative hprime hDab
  have hDP : D ≤ P := hext.obstruction.2.1
  by_contra h
  push Not at h
  set A : Subgroup G := (P : Subgroup G) ⊓ normalizer (D : Set G) with hA
  have hAP : A < P := lt_of_le_of_ne inf_le_left fun heq => hPD (by rw [← heq]; exact inf_le_right)
  obtain ⟨m, hmN, hmA⟩ := IsConcreteLE.exists_of_lt
    (pGroup_proper_subgroup_lt_internal_normalizer p hprime P A P.isPGroup' hAP)
  apply hmA
  refine ⟨hmN.1, ?_⟩
  have hmD : ∀ d ∈ D, m * d * m⁻¹ ∈ D := by
    intro d hd
    have hdA : d ∈ A := ⟨hDP hd, le_normalizer hd⟩
    have hconjA : m * d * m⁻¹ ∈ A := (mem_normalizer_iff.mp hmN.2 d).mp hdA
    have hpow : (m * d * m⁻¹) ^ p = 1 := by
      rw [conj_pow, hDe.2 d hd, mul_one, mul_inv_cancel]
    exact hS.mem_of_mem_centralizer_of_isMulCommutative hD1 hp hext hDab hCM
      (h _ hconjA.1 hconjA.2) hpow
  have hle : D.map (MulAut.conj m).toMonoidHom ≤ D := by
    rintro _ ⟨d, hd, rfl⟩
    exact hmD d hd
  exact mem_normalizer_iff_map_conj_eq.mpr
    (Subgroup.eq_of_le_of_card_ge hle (card_map_of_injective (MulAut.conj m).injective).ge)

end CFSG.LocalAnalysis.RankFourTheoremC

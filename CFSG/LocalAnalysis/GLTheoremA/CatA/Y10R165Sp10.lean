module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcEngine
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerLines
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp11
public import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj
public import CFSG.LocalAnalysis.GL83PartI.I_22_6
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KCSpFull
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

namespace SpEngine

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] [Finite (V ≃ₗ[F] V)]

structure SpBlockWitnessData (B : LinearMap.BilinForm F V) (p : ℕ)
    (Ã : Subgroup ↥(linIsometryGroup B)) (D U : Submodule F V)
    (xH zH : ↥(linIsometryGroup B)) where
  hD : (B.restrict D).Nondegenerate
  h6D : 6 ≤ Module.finrank F ↥(B.orthogonal D)
  hU : (B.restrict U).Nondegenerate
  h4U : 4 ≤ Module.finrank F ↥(B.orthogonal U)
  hxA : xH ∈ Ã
  hx1 : xH ≠ 1
  hzA : zH ∈ Ã
  hzx : zH ∉ Subgroup.zpowers xH
  hJq : CFSG.Open.IsQuasisimple ↥(pointwiseStab (linIsometryGroup B) D)
  hJx : pointwiseStab (linIsometryGroup B) D ≤
    Subgroup.centralizer ({xH} : Set ↥(linIsometryGroup B))
  hJn : ((pointwiseStab (linIsometryGroup B) D).subgroupOf
    (Subgroup.centralizer ({xH} : Set ↥(linIsometryGroup B)))).Normal
  hpJ : p ∣ Nat.card ↥(pointwiseStab (linIsometryGroup B) D)

structure SpBlockLayerData (B : LinearMap.BilinForm F V) (p : ℕ)
    (Ã : Subgroup ↥(linIsometryGroup B)) (D U : Submodule F V)
    (xH zH : ↥(linIsometryGroup B)) extends SpBlockWitnessData B p Ã D U xH zH where
  hPU : pointwiseStab (linIsometryGroup B) U ≤ pointwiseStab (linIsometryGroup B) D
  hPz : pointwiseStab (linIsometryGroup B) U ≤
    Subgroup.centralizer ({zH} : Set ↥(linIsometryGroup B))
  hPn : ((pointwiseStab (linIsometryGroup B) U).subgroupOf
    (pointwiseStab (linIsometryGroup B) D ⊓
      Subgroup.centralizer ({zH} : Set ↥(linIsometryGroup B)))).Normal
  hpP : p ∣ Nat.card ↥(pointwiseStab (linIsometryGroup B) U)

noncomputable def spBlockWitnessData {B : LinearMap.BilinForm F V} {p n : ℕ}
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hBalt : B.IsAlt) (hBnd : B.Nondegenerate)
    {A : Subgroup (V ≃ₗ[F] V)} [Fintype A] (hAe : IsElemAbelian p A)
    (hAinv : InvariantBilin A B) (hAH : A ≤ linIsometryGroup B)
    (hmax : CFSG.Open.pRank p (linIsometryGroup B) ≤ CFSG.Open.pRank p A)
    {Ã : Subgroup ↥(linIsometryGroup B)} (hAÃ : A = Ã.map (linIsometryGroup B).subtype)
    {t : Hyperplane A p → ↥A} (ht : ∀ D, t D ∉ D.1)
    (htH : ∀ D, blockEnd A hp hpF hAe t ht D ∈ linIsometryGroup B)
    {D E G : Hyperplane A p} (hDE : D ≠ E) (hDG : D ≠ G) (hEG : E ≠ G)
    (hD : blockSpace A D.1 ≠ ⊥) (hE : blockSpace A E.1 ≠ ⊥)
    (hDE' : Module.finrank F ↥(blockSpace A D.1) ≤ Module.finrank F ↥(blockSpace A E.1))
    (hEG' : Module.finrank F ↥(blockSpace A E.1) ≤ Module.finrank F ↥(blockSpace A G.1))
    (h9 : 9 ≤ Module.finrank F V) (h10 : 10 ≤ Module.finrank F V)
    (hn1 : 1 ≤ n) (hcardF : Nat.card F = 2 ^ n)
    (hm0 : 3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n) :
    SpBlockWitnessData B p Ã (blockSpace A D.1) (blockSpace A D.1 ⊔ blockSpace A E.1)
      ⟨blockEnd A hp hpF hAe t ht D, htH D⟩
      ⟨blockEnd A hp hpF hAe t ht E, htH E⟩ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let U : Submodule F V := blockSpace A D.1 ⊔ blockSpace A E.1
  let J : Subgroup ↥(linIsometryGroup B) :=
    pointwiseStab (linIsometryGroup B) (blockSpace A D.1)
  let xH : ↥(linIsometryGroup B) := ⟨blockEnd A hp hpF hAe t ht D, htH D⟩
  let zH : ↥(linIsometryGroup B) := ⟨blockEnd A hp hpF hAe t ht E, htH E⟩
  have hU : (B.restrict U).Nondegenerate := by
    refine nondegenerate_sup_of_orthogonal
      (blockSpace_nondegenerate A hp hpF hAe hBalt hAinv hBnd D)
      (blockSpace_nondegenerate A hp hpF hAe hBalt hAinv hBnd E) ?_ ?_
    · intro u hu v hv
      exact blockSpace_bilinear_orthogonal A hp hpF hAe B hAinv hDE hu hv
    · intro v hv u hu
      rw [← LinearMap.BilinForm.IsAlt.neg_eq hBalt]
      rw [blockSpace_bilinear_orthogonal A hp hpF hAe B hAinv hDE hu hv, neg_zero]
  have h6J : 6 ≤ Module.finrank F ↥(B.orthogonal (blockSpace A D.1)) :=
    six_le_finrank_orthogonal_blockSpace A hp hpF hAe hAinv hBnd t ht hDE hDG hEG hDE'
      (hDE'.trans hEG') h9
  have h4Q : 4 ≤ Module.finrank F ↥(B.orthogonal U) :=
    four_le_finrank_orthogonal_sup_blockSpace A hp hpF hAe hAinv hBnd hDE hDG hEG hDE' hEG'
      h10
  have hJq : CFSG.Open.IsQuasisimple ↥J := by
    have hq := isQuasisimple_pointwiseStab hBalt hBnd
      (blockSpace_nondegenerate A hp hpF hAe hBalt hAinv hBnd D) (by omega)
      (by
        rcases eq_or_ne (Nat.card F) 2 with h2F | h2F
        · exact Or.inr (Or.inr ⟨h2F, h6J⟩)
        · exact Or.inl (by
            rcases Nat.lt_or_ge n 2 with hn | hn
            · have hn1' : n = 1 := by omega
              exact absurd (by rw [hcardF, hn1']; norm_num : Nat.card F = 2) h2F
            · rw [hcardF]
              exact Nat.pow_le_pow_right (show 0 < 2 by norm_num) hn))
    exact ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hJleCx : J ≤ Subgroup.centralizer ({xH} : Set ↥(linIsometryGroup B)) := by
    have := pointwiseStab_le_centralizer_blockEnd A hp hpF hAe hBnd hAinv
      (fun g hg u v => mem_linIsometryGroup.mp hg u v) t ht D (htH D)
    simpa [J, xH] using this
  have hJn : (J.subgroupOf (Subgroup.centralizer ({xH} :
      Set ↥(linIsometryGroup B)))).Normal := by
    refine pointwiseStab_normal (H := linIsometryGroup B) (U := blockSpace A D.1) ?_
    intro g hg u hu
    have hcomm : ((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V) *
        blockEnd A hp hpF hAe t ht D =
        blockEnd A hp hpF hAe t ht D *
          ((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V) := by
      have h := Subgroup.mem_centralizer_iff.mp hg xH (Set.mem_singleton _)
      exact (congrArg Subtype.val h).symm
    exact mem_blockSpace_of_commute A hp hpF hAe hBalt hAinv hBnd t ht hcomm
      (fun u v => mem_linIsometryGroup.mp g.2 u v) hu
  have hpJ : p ∣ Nat.card ↥J := by
    have := dvd_card_pointwiseStab A hp hpF hAe t ht htH (D := D) (E := E) hDE.symm hE
    simpa [J] using this
  have hmemA : ∀ D, blockEnd A hp hpF hAe t ht D ∈ A := fun D =>
    blockEnd_mem_of_pRank_le (H := linIsometryGroup B) A hp hpF hAe t ht hAH hmax htH D
  have hmem : ∀ D, (⟨blockEnd A hp hpF hAe t ht D, htH D⟩ :
      ↥(linIsometryGroup B)) ∈ Ã := by
    intro D
    obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp
      (show blockEnd A hp hpF hAe t ht D ∈ Ã.map (linIsometryGroup B).subtype by
        rw [← hAÃ]
        exact hmemA D)
    have hax : a = (⟨blockEnd A hp hpF hAe t ht D, htH D⟩ :
        ↥(linIsometryGroup B)) := Subtype.ext haeq
    rwa [hax] at ha
  have hx1 : xH ≠ 1 := by
    intro h
    exact hD (eq_one_of_blockEnd_eq_one A hp hpF hAe t ht (congrArg Subtype.val h))
  have hzx : zH ∉ Subgroup.zpowers xH := by
    intro h
    apply blockEnd_not_mem_zpowers_of_ne A hp hpF hAe t ht (D := E) (E := D) hDE hE
    rcases Subgroup.mem_zpowers_iff.mp h with ⟨k, hk⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩
  exact
    { hD := blockSpace_nondegenerate A hp hpF hAe hBalt hAinv hBnd D
      h6D := h6J
      hU := hU
      h4U := h4Q
      hxA := hmem D
      hx1 := hx1
      hzA := hmem E
      hzx := hzx
      hJq := hJq
      hJx := hJleCx
      hJn := hJn
      hpJ := hpJ }

noncomputable def spBlockLayerData {B : LinearMap.BilinForm F V} {p n : ℕ}
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hBalt : B.IsAlt) (hBnd : B.Nondegenerate)
    {A : Subgroup (V ≃ₗ[F] V)} [Fintype A] (hAe : IsElemAbelian p A)
    (hAinv : InvariantBilin A B) (hAH : A ≤ linIsometryGroup B)
    (hmax : CFSG.Open.pRank p (linIsometryGroup B) ≤ CFSG.Open.pRank p A)
    {Ã : Subgroup ↥(linIsometryGroup B)} (hAÃ : A = Ã.map (linIsometryGroup B).subtype)
    {t : Hyperplane A p → ↥A} (ht : ∀ D, t D ∉ D.1)
    (htH : ∀ D, blockEnd A hp hpF hAe t ht D ∈ linIsometryGroup B)
    {D E G : Hyperplane A p} (hDE : D ≠ E) (hDG : D ≠ G) (hEG : E ≠ G)
    (hD : blockSpace A D.1 ≠ ⊥) (hE : blockSpace A E.1 ≠ ⊥) (hG : blockSpace A G.1 ≠ ⊥)
    (hDE' : Module.finrank F ↥(blockSpace A D.1) ≤ Module.finrank F ↥(blockSpace A E.1))
    (hEG' : Module.finrank F ↥(blockSpace A E.1) ≤ Module.finrank F ↥(blockSpace A G.1))
    (h9 : 9 ≤ Module.finrank F V) (h10 : 10 ≤ Module.finrank F V)
    (hn1 : 1 ≤ n) (hcardF : Nat.card F = 2 ^ n)
    (hm0 : 3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n) :
    SpBlockLayerData B p Ã (blockSpace A D.1) (blockSpace A D.1 ⊔ blockSpace A E.1)
      ⟨blockEnd A hp hpF hAe t ht D, htH D⟩
      ⟨blockEnd A hp hpF hAe t ht E, htH E⟩ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let w := spBlockWitnessData hp hpF hBalt hBnd hAe hAinv hAH hmax hAÃ ht htH
    hDE hDG hEG hD hE hDE' hEG' h9 h10 hn1 hcardF hm0
  let U : Submodule F V := blockSpace A D.1 ⊔ blockSpace A E.1
  let Dm : Submodule F V := blockSpace A D.1
  let xH : ↥(linIsometryGroup B) := ⟨blockEnd A hp hpF hAe t ht D, htH D⟩
  let zH : ↥(linIsometryGroup B) := ⟨blockEnd A hp hpF hAe t ht E, htH E⟩
  have hPU : pointwiseStab (linIsometryGroup B) U ≤
      pointwiseStab (linIsometryGroup B) Dm := pointwiseStab_mono le_sup_left
  have hPz : pointwiseStab (linIsometryGroup B) U ≤
      Subgroup.centralizer ({zH} : Set ↥(linIsometryGroup B)) := by
    refine (pointwiseStab_mono (H := linIsometryGroup B) le_sup_right).trans ?_
    have := pointwiseStab_le_centralizer_blockEnd A hp hpF hAe hBnd hAinv
      (fun g hg u v => mem_linIsometryGroup.mp hg u v) t ht E (htH E)
    simpa [zH] using this
  have hPn : ((pointwiseStab (linIsometryGroup B) U).subgroupOf
      (pointwiseStab (linIsometryGroup B) Dm ⊓
        Subgroup.centralizer ({zH} : Set ↥(linIsometryGroup B)))).Normal := by
    refine pointwiseStab_normal (H := linIsometryGroup B) (U := U) ?_
    intro g hg u hu
    obtain ⟨hgJ, hgC⟩ := Subgroup.mem_inf.mp hg
    change u ∈ blockSpace A D.1 ⊔ blockSpace A E.1 at hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    refine Submodule.mem_sup.mpr ⟨_, ?_, _, ?_, by rw [map_add]⟩
    · have hcomm : ((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V) *
          blockEnd A hp hpF hAe t ht D =
          blockEnd A hp hpF hAe t ht D *
            ((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V) := by
        have h := Subgroup.mem_centralizer_iff.mp (w.hJx hgJ) xH (Set.mem_singleton _)
        exact (congrArg Subtype.val h).symm
      exact mem_blockSpace_of_commute A hp hpF hAe hBalt hAinv hBnd t ht hcomm
        (fun u v => mem_linIsometryGroup.mp g.2 u v) ha
    · have hcomm : ((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V) *
          blockEnd A hp hpF hAe t ht E =
          blockEnd A hp hpF hAe t ht E *
            ((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V) := by
        have h := Subgroup.mem_centralizer_iff.mp hgC zH (Set.mem_singleton _)
        exact (congrArg Subtype.val h).symm
      exact mem_blockSpace_of_commute A hp hpF hAe hBalt hAinv hBnd t ht hcomm
        (fun u v => mem_linIsometryGroup.mp g.2 u v) hb
  have hpP : p ∣ Nat.card ↥(pointwiseStab (linIsometryGroup B) U) := by
    have htGP : (⟨blockEnd A hp hpF hAe t ht G, htH G⟩ :
        ↥(linIsometryGroup B)) ∈ pointwiseStab (linIsometryGroup B) U := by
      rw [mem_pointwiseStab]
      intro u hu
      change u ∈ blockSpace A D.1 ⊔ blockSpace A E.1 at hu
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      show blockEnd A hp hpF hAe t ht G (a + b) = a + b
      rw [map_add, blockEnd_apply_of_mem_block A hp hpF hAe t ht (D := G) (E := D) hDG ha,
        blockEnd_apply_of_mem_block A hp hpF hAe t ht (D := G) (E := E) hEG hb]
    have hord : orderOf (⟨blockEnd A hp hpF hAe t ht G, htH G⟩ :
        ↥(linIsometryGroup B)) = p := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (blockEnd_pow A hp hpF hAe t ht G)
        (fun h => hG (eq_one_of_blockEnd_eq_one A hp hpF hAe t ht h))
    have := orderOf_dvd_natCard (⟨⟨blockEnd A hp hpF hAe t ht G, htH G⟩, htGP⟩ :
      ↥(pointwiseStab (linIsometryGroup B) U))
    rw [Subgroup.orderOf_mk, hord] at this
    exact this
  exact
    { w with
      hPU := hPU
      hPz := hPz
      hPn := hPn
      hpP := hpP }

theorem exists_layer_pointwiseStab_of_two_le_or_six_le {B : LinearMap.BilinForm F V}
    (hBalt : B.IsAlt) (hBnd : B.Nondegenerate) {U : Submodule F V}
    (hU : (B.restrict U).Nondegenerate) (h4 : 4 ≤ Module.finrank F ↥(B.orthogonal U))
    {p n : ℕ} (hp : p.Prime) (hn1 : 1 ≤ n) (hcardF : Nat.card F = 2 ^ n)
    (hgen : 2 ≤ n ∨ 6 ≤ Module.finrank F ↥(B.orthogonal U))
    {J : Subgroup ↥(linIsometryGroup B)}
    (hPU : pointwiseStab (linIsometryGroup B) U ≤ J)
    {zH : ↥(linIsometryGroup B)}
    (hPz : pointwiseStab (linIsometryGroup B) U ≤
      Subgroup.centralizer ({zH} : Set ↥(linIsometryGroup B)))
    (hPn : ((pointwiseStab (linIsometryGroup B) U).subgroupOf
      (J ⊓ Subgroup.centralizer ({zH} : Set ↥(linIsometryGroup B)))).Normal)
    (hpP : p ∣ Nat.card ↥(pointwiseStab (linIsometryGroup B) U)) :
    ∃ Q : Subgroup ↥(linIsometryGroup B), Q ≤ J ∧
      Q ≤ Subgroup.centralizer ({zH} : Set ↥(linIsometryGroup B)) ∧
      (Q.subgroupOf (J ⊓ Subgroup.centralizer ({zH} :
        Set ↥(linIsometryGroup B)))).Normal ∧
      CFSG.Open.IsQuasisimple ↥Q ∧ p ∣ Nat.card ↥Q := by
  classical
  have hPq : CFSG.Open.IsQuasisimple ↥(pointwiseStab (linIsometryGroup B) U) := by
    have hq := isQuasisimple_pointwiseStab hBalt hBnd hU (by omega)
      (by
        rcases hgen with hn | h6
        · exact Or.inl (by
            rw [hcardF]
            exact Nat.pow_le_pow_right (show 0 < 2 by norm_num) hn)
        · rcases eq_or_ne (Nat.card F) 2 with h2F | h2F
          · exact Or.inr (Or.inr ⟨h2F, h6⟩)
          · exact Or.inl (by
              rcases Nat.lt_or_ge n 2 with hn | hn
              · have hn1' : n = 1 := by omega
                exact absurd (by rw [hcardF, hn1']; norm_num : Nat.card F = 2) h2F
              · rw [hcardF]
                exact Nat.pow_le_pow_right (show 0 < 2 by norm_num) hn))
    exact ⟨hq.1.commutator_eq_top, hq.2.1⟩
  exact ⟨pointwiseStab (linIsometryGroup B) U, hPU, hPz, hPn, hPq, hpP⟩

theorem concl165_of_spBlockLayerData {B : LinearMap.BilinForm F V}
    (hBalt : B.IsAlt) (hBnd : B.Nondegenerate) {p q n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Ã : Subgroup ↥(linIsometryGroup B)} (hÃe : IsElemAbelian p Ã)
    (hn1 : 1 ≤ n) (hcardF : Nat.card F = 2 ^ n)
    (hm0 : 3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n)
    {D U : Submodule F V} {xH zH : ↥(linIsometryGroup B)}
    (data : SpBlockLayerData B p Ã D U xH zH)
    (hqtor : ∃ Fq : Subgroup ↥(linIsometryGroup B), Fq ≤ pointwiseStab (linIsometryGroup B) D ∧
      IsElemAbelian q Fq ∧ 3 ≤ CFSG.Open.pRank q Fq) :
    Concl165 ↥(linIsometryGroup B) p q Ã := by
  classical
  have hlayer : ∃ Q : Subgroup ↥(linIsometryGroup B), Q ≤ pointwiseStab (linIsometryGroup B) D ∧
      Q ≤ Subgroup.centralizer ({zH} : Set ↥(linIsometryGroup B)) ∧
      (Q.subgroupOf (pointwiseStab (linIsometryGroup B) D ⊓
        Subgroup.centralizer ({zH} : Set ↥(linIsometryGroup B)))).Normal ∧
      CFSG.Open.IsQuasisimple ↥Q ∧ p ∣ Nat.card ↥Q := by
    by_cases hgen : 2 ≤ n ∨ 6 ≤ Module.finrank F ↥(B.orthogonal U)
    · exact exists_layer_pointwiseStab_of_two_le_or_six_le hBalt hBnd data.hU data.h4U hp
        hn1 hcardF hgen data.hPU data.hPz data.hPn data.hpP
    · push Not at hgen
      obtain ⟨hn2, hdim6⟩ := hgen
      have hn1' : n = 1 := by omega
      exact exists_commutator_pointwiseStab_sp4_two hBalt hBnd data.hU data.h4U hdim6 hp hp2
        hn1' hcardF hm0 data.hPU data.hPz data.hPn data.hpP
  obtain ⟨Q, hQJ, hQz, hQn, hQq, hpQ⟩ := hlayer
  obtain ⟨Fq, hFqle, hFqe, hFq3⟩ := hqtor
  have hFqCx : Fq ≤ Subgroup.centralizer ({xH} : Set ↥(linIsometryGroup B)) :=
    hFqle.trans data.hJx
  have hFqNJ : Fq ≤ Subgroup.normalizer
      ((pointwiseStab (linIsometryGroup B) D : Subgroup ↥(linIsometryGroup B)) :
        Set ↥(linIsometryGroup B)) := hFqle.trans Subgroup.le_normalizer
  exact concl165_of_layers hp hÃe data.hxA data.hzA data.hx1 data.hzx data.hJx data.hJn
    data.hJq data.hpJ hQJ hQz hQn hQq hpQ hFqe hFqCx hFqNJ hFq3

end SpEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F

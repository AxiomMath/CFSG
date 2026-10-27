module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
import CFSG.GroupTheory.CommutatorCentralizerInNormal
import CFSG.GroupTheory.Frattini.PSubgroupLift
import CFSG.GroupTheory.SylowInfNormal
import CFSG.Quasithin.Background.B2Factorization
import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open scoped Pointwise

private theorem isSylowTwoOf_inf_of_le_sup_gnC {X : Type} [Group X] [Finite X]
    {T P : Subgroup X} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    (hCP : gnC T ≤ P) (hP : P ≤ gnC T ⊔ T) :
    CFSG.QuasithinUnique.IsSylowTwoOf (P ⊓ T) P := by
  classical
  have hTC : T ≤ Subgroup.normalizer (gnC T : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  have hcoe : ((gnC T ⊔ T : Subgroup X) : Set X) =
      (gnC T : Set X) * (T : Set X) := by
    rw [sup_comm, Subgroup.coe_mul_of_left_le_normalizer_right T (gnC T) hTC]
    ext x
    constructor
    · rintro ⟨t, ht, c, hc, rfl⟩
      exact ⟨t * c * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hTC ht) c).mp hc, t, ht,
        by group⟩
    · rintro ⟨c, hc, t, ht, rfl⟩
      exact ⟨t, ht, t⁻¹ * c * t⁻¹⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hTC (T.inv_mem ht)) c).mp hc, by group⟩
  have hded : P = gnC T ⊔ (P ⊓ T) := by
    have h := CFSG.GroupTheory.sup_inf_eq_inf_sup_of_permutes (E := gnC T) (T := T)
      (L := P) hCP hcoe
    rw [inf_eq_right.mpr hP, inf_comm T P] at h
    exact h.symm
  have hCsyl : CFSG.QuasithinUnique.IsSylowTwoOf (gnC T ⊓ T) (gnC T) :=
    CFSG.isSylowTwoOf_inf_of_normal hT le_top (by
      rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance])
  refine ⟨inf_le_left, hT.2.1.to_le inf_le_right, ?_⟩
  have hrel : (P ⊓ T).relIndex P = (gnC T ⊓ T).relIndex (gnC T) := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := P ⊓ T) (K := gnC T) (by
        rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
        exact le_top)).1
    rw [sup_comm] at h
    rw [← hded] at h
    have h2 : (P ⊓ T) ⊓ gnC T = gnC T ⊓ T := by
      rw [inf_comm (P ⊓ T) (gnC T), ← inf_assoc, inf_eq_left.mpr hCP]
    rwa [h2] at h
  change ¬ 2 ∣ (P ⊓ T).relIndex P
  rw [hrel]
  exact hCsyl.2.2

private theorem comap_le_gnC_sup {X : Type} [Group X] {T : Subgroup X}
    {S : Subgroup (X ⧸ gnC T)} (hST : S ≤ gnImg T T) :
    S.comap (QuotientGroup.mk' (gnC T)) ≤ gnC T ⊔ T := by
  intro x hx
  have hxT : QuotientGroup.mk' (gnC T) x ∈ gnImg T T := hST hx
  rw [gnImg] at hxT
  obtain ⟨t, ht, hft⟩ := Subgroup.mem_map.mp hxT
  have hc : x * t⁻¹ ∈ gnC T := by
    refine (QuotientGroup.eq_one_iff (x * t⁻¹)).1 ?_
    change QuotientGroup.mk' (gnC T) (x * t⁻¹) = 1
    rw [map_mul, map_inv, hft, mul_inv_cancel]
  rw [show x = (x * t⁻¹) * t by group]
  exact Subgroup.mul_mem_sup hc ht

private theorem map_gnC_sup_eq {X : Type} [Group X] (T : Subgroup X) :
    (gnC T ⊔ T).map (QuotientGroup.mk' (gnC T)) = gnImg T T := by
  rw [Subgroup.map_sup, gnImg]
  have hmapC : (gnC T).map (QuotientGroup.mk' (gnC T)) = ⊥ :=
    (Subgroup.map_eq_bot_iff (gnC T)).mpr (le_of_eq (QuotientGroup.ker_mk' (gnC T)).symm)
  rw [hmapC, bot_sup_eq]

theorem normalizer_le_gnImg_normalizer {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) {W : Subgroup X} (hWT : W ≤ T)
    (hTW : T ≤ Subgroup.normalizer (W : Set X))
    (hR : ∀ R : Subgroup X, W ≤ R → R ≤ T →
      Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (W : Set X))
    {S : Subgroup (X ⧸ gnC T)} (hST : S ≤ gnImg T T) (hWS : gnImg T W ≤ S) :
    Subgroup.normalizer (S : Set (X ⧸ gnC T)) ≤ gnImg T (Subgroup.normalizer (W : Set X)) := by
  classical
  intro q hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  let P : Subgroup X := S.comap (QuotientGroup.mk' (gnC T))
  have hPle : P ≤ gnC T ⊔ T := comap_le_gnC_sup hST
  have hCP : gnC T ≤ P := by
    intro c hc
    change QuotientGroup.mk c ∈ S
    rw [(QuotientGroup.eq_one_iff c).2 hc]
    exact S.one_mem
  have hWP : W ≤ P := fun w hw =>
    hWS (Subgroup.mem_map_of_mem (QuotientGroup.mk' (gnC T)) hw)
  have hAsylOf : CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ T) P :=
    CFSG.ABGLocalTools.isSylowOf_iff.2 (isSylowTwoOf_inf_of_le_sup_gnC hT hCP hPle)
  obtain ⟨n, hnP, m, hmN, hgnm⟩ :=
    CFSG.GroupTheory.exists_mul_mem_comap_and_normalizer
      (p := 2) (f := QuotientGroup.mk' (gnC T)) (Astar := S) (A := P ⊓ T)
      inf_le_left hAsylOf hq
  have hfnT : QuotientGroup.mk' (gnC T) n ∈ gnImg T T := by
    rw [← map_gnC_sup_eq T]
    exact Subgroup.mem_map_of_mem _ (hPle hnP)
  have hfnN : QuotientGroup.mk' (gnC T) n ∈
      gnImg T (Subgroup.normalizer (W : Set X)) :=
    Subgroup.map_mono hTW hfnT
  have hfmN : QuotientGroup.mk' (gnC T) m ∈
      gnImg T (Subgroup.normalizer (W : Set X)) :=
    Subgroup.mem_map_of_mem _ (hR (P ⊓ T) (le_inf hWP hWT) inf_le_right hmN)
  rw [hgnm]
  change QuotientGroup.mk (n * m) ∈ gnImg T (Subgroup.normalizer (W : Set X))
  rw [QuotientGroup.mk_mul]
  exact (gnImg T (Subgroup.normalizer (W : Set X))).mul_mem hfnN hfmN

theorem normalizer_le_gnImg_normalizer_thompsonJ {X : Type} [Group X] [Finite X]
    {T : Subgroup X} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) {S : Subgroup (X ⧸ gnC T)}
    (hST : S ≤ gnImg T T) (hJS : gnImg T (CFSG.Quasithin.thompsonJ T) ≤ S) :
    Subgroup.normalizer (S : Set (X ⧸ gnC T)) ≤
      gnImg T (Subgroup.normalizer (CFSG.Quasithin.thompsonJ T : Set X)) :=
  normalizer_le_gnImg_normalizer hT (CFSG.Quasithin.C1GN.thompsonJ_le T)
    (Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ T))
    (fun R hWR hRT =>
      (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ R).trans
        (le_of_eq (congrArg (fun K : Subgroup X => Subgroup.normalizer (K : Set X))
          (CFSG.Quasithin.thompsonJ_eq_of_le hWR hRT).symm)))
    hST hJS

theorem normalizer_le_gnImg_normalizer_baum {X : Type} [Group X] [Finite X]
    {T : Subgroup X} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) {S : Subgroup (X ⧸ gnC T)}
    (hST : S ≤ gnImg T T) (hBS : gnImg T (CFSG.Quasithin.baum T) ≤ S) :
    Subgroup.normalizer (S : Set (X ⧸ gnC T)) ≤
      gnImg T (Subgroup.normalizer (CFSG.Quasithin.baum T : Set X)) :=
  normalizer_le_gnImg_normalizer hT (CFSG.Quasithin.C1GN.baum_le T)
    (Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_baum T))
    (fun R hWR hRT =>
      (CFSG.Quasithin.normalizer_le_normalizer_baum R).trans
        (le_of_eq (congrArg (fun K : Subgroup X => Subgroup.normalizer (K : Set X))
          (CFSG.Quasithin.baum_eq_of_le hWR hRT).symm)))
    hST hBS

end CFSG.LocalAnalysis.RankThreeUC.S15

end

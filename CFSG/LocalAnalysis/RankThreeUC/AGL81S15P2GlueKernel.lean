module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.NaturalOn
public import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeAux
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeA
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN CFSG.Quasithin
  CFSG.AGLEmbedding CFSG.Open

theorem normalizer_le_normalizer_oddHull {Y : Type} [Group Y] (P : Subgroup Y) :
    Subgroup.normalizer (P : Set Y) ≤ Subgroup.normalizer (oddHull P : Set Y) := by
  refine le_normalizer_of_closure_odd
    (Subgroup.closure_mono fun x hx => ⟨Subgroup.subset_closure hx, hx.2⟩)
    fun g hg x hx hodd => Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.1 hg x).1
      ((Subgroup.closure_le P).2 (fun y hy => hy.1) hx), ?_⟩
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa using this.symm ▸ hodd

theorem pCoreOf_le_gnImg_of_le_normalizer {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) {P : Subgroup (X ⧸ gnC T)}
    (hTP : gnImg T T ≤ Subgroup.normalizer (P : Set (X ⧸ gnC T))) :
    pCoreOf 2 P ≤ gnImg T T := by
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (gnImg T T) ⊤ :=
    isSylowTwoOf_map_top_of_surjective hT (QuotientGroup.mk'_surjective (gnC T))
  have hsup : IsPGroup 2 ↥(gnImg T T ⊔ pCoreOf 2 P) :=
    hSyl.2.1.to_sup_of_normal_right' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P)
      (hTP.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P))
  exact le_sup_right.trans (hSyl.eq_of_le le_sup_left le_top hsup).le

private theorem conj_comm_of_mem_pCoreOf {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) {P : Subgroup (X ⧸ gnC T)}
    (hTP : gnImg T T ≤ Subgroup.normalizer (P : Set (X ⧸ gnC T))) {x c z : X}
    (hx : toStar T x ∈ pCoreOf 2 P) (hc : c ∈ (oddHull P ⊔ gnImg T T).comap (toStar T))
    (hz : z ∈ omegaOneCenterOf T) : x * (c * z * c⁻¹) * x⁻¹ = c * z * c⁻¹ := by
  have hHN : oddHull P ⊔ gnImg T T ≤
      Subgroup.normalizer (pCoreOf 2 P : Set (X ⧸ gnC T)) := by
    refine sup_le ?_ ?_
    · have hodd : oddHull P ≤ P := (Subgroup.closure_le P).2 fun _ hy => hy.1
      exact hodd.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
    · exact hTP.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P)
  have hx' : toStar T (c⁻¹ * x * c) ∈ pCoreOf 2 P := by
    have h := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (pCoreOf 2 P : Set (X ⧸ gnC T))).inv_mem
        (hHN (Subgroup.mem_comap.mp hc))) (toStar T x)).1 hx
    simpa only [map_mul, map_inv, inv_inv] using h
  have hcomm : c⁻¹ * x * c * z * (c⁻¹ * x * c)⁻¹ = z :=
    CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.comm_of_mem_gnImg
      (pCoreOf_le_gnImg_of_le_normalizer hT hTP hx') hz
  calc x * (c * z * c⁻¹) * x⁻¹ = c * (c⁻¹ * x * c * z * (c⁻¹ * x * c)⁻¹) * c⁻¹ := by group
    _ = c * z * c⁻¹ := by rw [hcomm]

theorem mem_gnC_subgroupOf_of_mem_pCoreOf {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) {P : Subgroup (X ⧸ gnC T)}
    (hTP : gnImg T T ≤ Subgroup.normalizer (P : Set (X ⧸ gnC T)))
    (x : ↥((oddHull P ⊔ gnImg T T).comap (toStar T)))
    (hx : toStar T (x : X) ∈ pCoreOf 2 P) :
    x ∈ gnC (T.subgroupOf ((oddHull P ⊔ gnImg T T).comap (toStar T))) := by
  let M : Subgroup X := (oddHull P ⊔ gnImg T T).comap (toStar T)
  change x ∈ gnC (T.subgroupOf M)
  have hTM : T ≤ M := fun t ht =>
    Subgroup.mem_comap.mpr (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem (toStar T) ht))
  change x ∈ Subgroup.centralizer
    (Subgroup.normalClosure (omegaOneCenterOf (T.subgroupOf M) : Set ↥M) : Set ↥M)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  change y ∈ Subgroup.closure (Group.conjugatesOfSet
    (omegaOneCenterOf (T.subgroupOf M) : Set ↥M)) at hy
  have hgen : Group.conjugatesOfSet (omegaOneCenterOf (T.subgroupOf M) : Set ↥M) ⊆
      Subgroup.centralizer ({x} : Set ↥M) := by
    intro w hw
    obtain ⟨z, hz, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hw
    obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
    rw [omegaOneCenterOf_subgroupOf hTM] at hz
    change c * z * c⁻¹ ∈ Subgroup.centralizer ({x} : Set ↥M)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    apply mul_inv_eq_iff_eq_mul.mp
    exact Subtype.ext (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      conj_comm_of_mem_pCoreOf hT hTP hx c.2 (Subgroup.mem_subgroupOf.mp hz))
  have hy' : y ∈ Subgroup.centralizer ({x} : Set ↥M) :=
    (Subgroup.closure_le (Subgroup.centralizer ({x} : Set ↥M))).2 hgen hy
  exact (Subgroup.mem_centralizer_iff.mp hy' x (Set.mem_singleton x)).symm

end CFSG.LocalAnalysis.RankThreeUC.S15

end

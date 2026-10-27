module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOrig
public import CFSG.Quasithin.Background.C1GNNotation

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

variable {G : Type} [Group G] [Finite G]

theorem normal_L_sup_baum {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F]
    (hS : EvenSL2Setting (⊤ : Subgroup G) R M V n F) :
    (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R).Normal := by
  obtain ⟨-, -, hXLR, -, -⟩ := even_SL2_setting_basic hS
  set L := oddOrderSubgroup (⊤ : Subgroup G)
  have hLn : L.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    refine top_le_iff.mp fun g _ => normalizer_le_normalizer_oddOrderSubgroup (⊤ : Subgroup G)
      (?_ : g ∈ Subgroup.normalizer ((⊤ : Subgroup G) : Set G))
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp
  have hbR : baum R ≤ R := inf_le_left
  have hRbaum : R ≤ Subgroup.normalizer (baum R : Set G) := by
    have hchar : ((baum R).subgroupOf R).Characteristic := C1GN.characteristic_baum R
    have hnormal : ((baum R).subgroupOf R).Normal := inferInstance
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hbR).1 hnormal
  have hLR : L ⊔ R = ⊤ := hXLR.symm
  apply Subgroup.normalizer_eq_top_iff.mp
  refine top_le_iff.mp ?_
  rw [← hLR]
  refine sup_le (fun x hx => Subgroup.le_normalizer ((le_sup_left : L ≤ L ⊔ baum R) hx)) ?_
  intro r hr
  have := hLn
  have hrL : r ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top r
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hrL,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRbaum hr)]

end CFSG.QuasithinUnique.Setup.Lift

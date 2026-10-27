module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.CentralKer
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConfOf
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.ConclOf

public section

namespace CFSG.SectionRank.QTK.Insp443.Hyp

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Ch4
  CFSG.Quasithin.H13.Ch4.E443 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L B Tp VB K : Subgroup G}

theorem centralKer (h : Hyp G T M L B Tp VB K) (h37 : A37ForSQTK) (h39 : A39ForSQTK) :
    CentralKer ((perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))).subgroupOf K)
      (VB.subgroupOf K) := by
  classical
  let LB : Subgroup G := perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))
  let L' : Subgroup ↥K := LB.subgroupOf K
  let V' : Subgroup ↥K := VB.subgroupOf K
  have hG : ⁅LB ⊓ Subgroup.centralizer (VB : Set G), LB⁆ ≤ pCoreOf 2 LB :=
    commutator_le_pCoreOf_LB h.setting h37 h39 (N := LB ⊓ Subgroup.centralizer (VB : Set G))
      inf_le_left inf_le_right
  have hLmap : L'.map K.subtype = LB := Subgroup.map_subgroupOf_eq_of_le h.LB_le
  have hCmap : (Subgroup.centralizer (V' : Set ↥K)).map K.subtype =
      K ⊓ Subgroup.centralizer (VB : Set G) := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c.2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      simpa using congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp hc ⟨v, h.VB_le hv⟩ (Subgroup.mem_subgroupOf.mpr hv))
    · rintro ⟨hxK, hxC⟩
      refine ⟨⟨x, hxK⟩, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_, rfl⟩
      obtain ⟨v, hvK⟩ := y
      exact Subtype.ext
        (Subgroup.mem_centralizer_iff.mp hxC v (Subgroup.mem_subgroupOf.mp hy))
  have hNmap : (L' ⊓ Subgroup.centralizer (V' : Set ↥K)).map K.subtype =
      LB ⊓ Subgroup.centralizer (VB : Set G) := by
    rw [Subgroup.map_inf _ _ K.subtype K.subtype_injective, hLmap, hCmap, ← inf_assoc,
      inf_eq_left.mpr h.LB_le]
  have hpc : (pCoreOf 2 L').map K.subtype = pCoreOf 2 LB := by
    rw [← CFSG.Quasithin.H13.F431.AG.pCoreOf_map_injective K.subtype K.subtype_injective L',
      hLmap]
  show ⁅L' ⊓ Subgroup.centralizer (V' : Set ↥K), L'⁆ ≤ pCoreOf 2 L'
  rw [← Subgroup.map_le_map_iff_of_injective K.subtype_injective, Subgroup.map_commutator,
    hNmap, hLmap, hpc]
  exact hG

end CFSG.SectionRank.QTK.Insp443.Hyp

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Quasithin

theorem For.of_forKF (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {P : (S : Type) → [Group S] → Prop} (hF : ForKF P) : For P :=
  fun _ _ _ _ _ _ _ _ _ K hH hP =>
    hH.concl443B_of_conclK
      (hF ↥K _ _ _ (hH.kConf h37 h38 h39) (hH.centralKer h37 h39) hP)

end CFSG.SectionRank.QTK.Insp443

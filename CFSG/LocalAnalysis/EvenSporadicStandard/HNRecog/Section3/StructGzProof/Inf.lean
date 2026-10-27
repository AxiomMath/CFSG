module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeA

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem structGz_qzInf_eq_map {G : Type} [Group G] (z : G) (σ : ↥(Gx z)) :
    Qz z ⊓ Gx (σ : G) =
      (CFSG.pCore 2 ↥(Gx z) ⊓ Subgroup.centralizer ({σ} : Set ↥(Gx z))).map (Gx z).subtype := by
  ext g
  constructor
  · intro hg
    obtain ⟨hgQz, hgGx⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨q, hqQ, hqg⟩ := Subgroup.mem_map.mp hgQz
    refine Subgroup.mem_map.mpr ⟨q, Subgroup.mem_inf.mpr ⟨hqQ, ?_⟩, hqg⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, show (q : G) = g from hqg]
    exact (mem_Gx.mp hgGx).symm
  · rintro ⟨q, hq, hqg⟩
    obtain ⟨hqQ, hqcent⟩ := Subgroup.mem_inf.mp hq
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨q, hqQ, hqg⟩, ?_⟩
    rw [mem_Gx]
    have hcomm : (q : G) * (σ : G) = (σ : G) * (q : G) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hqcent)
    rw [← show (q : G) = g from hqg]
    exact hcomm.symm

theorem structGz_qzInf_eq_zpowers_iff {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    (σ : ↥(Gx z)) :
    CFSG.pCore 2 ↥(Gx z) ⊓ Subgroup.centralizer ({σ} : Set ↥(Gx z)) =
        centerOf (CFSG.pCore 2 ↥(Gx z)) ↔
      Qz z ⊓ Gx (σ : G) = Subgroup.zpowers z := by
  have hf : Function.Injective (Gx z).subtype := (Gx z).subtype_injective
  have hQ := isExtraspecialPlusByA5WrTwoWith_pCore h.cent_z
  have hc : centerOf (CFSG.pCore 2 ↥(Gx z)) = Subgroup.zpowers (GxSelf z) :=
    centerOf_eq_zpowers h.orderOf_z hQ
  have hzmap : (Subgroup.zpowers (GxSelf z)).map (Gx z).subtype = Subgroup.zpowers z := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [structGz_qzInf_eq_map z σ, ← hzmap, ← hc]
  exact (Subgroup.map_injective hf).eq_iff.symm

end CFSG.EvenSporadicStandard.HNRecog.Section3

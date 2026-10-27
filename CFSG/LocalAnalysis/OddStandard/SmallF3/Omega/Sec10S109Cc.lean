module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Cb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Bundles
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10BData

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10C_z_mem_secB [Finite G] (hf : Asc82Facts10) (hb : Asc82Basic10) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    z ∈ secB S L := by
  obtain ⟨-, -, hBC, -⟩ := sec10BData_of hb hf.b5 hctx.toSec10Z
  have hzL : z ∈ L := (hctx.pocket1.2.1 hctx.pocket1.1).1
  rw [← hBC]
  exact ⟨Subgroup.mem_centralizer_iff.mpr fun b hb' => hctx.central b (secB_le_S S L hb'), hzL⟩

theorem sec10C_type_i2p [Finite G] (hf : Asc82Facts10) (hb : Asc82Basic10) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {s : G}
    (hs : s ∈ S) (hs2 : s * s = 1) (hout : s ∉ L ⊔ centralizer (L : Set G))
    (hn1 : s ∈ normalizer (K1 : Set G)) : InducesTypeSome L s 5 1 2 1 := by
  obtain ⟨hpsp, -, -, -, hSN, -⟩ := hb G t L S z hctx.toSec10Z
  have hss : s * s ∈ centralizer (L : Set G) := by rw [hs2]; exact Subgroup.one_mem _
  rcases (hf.factsC.ty G L hpsp s (hSN hs) hss).mp hout with h | h
  · exact h
  · exfalso
    have hsw := hf.factsC.sw G L hpsp z K1 K2 hctx.toSec10Z.pocket hctx.pocket1 hctx.pocket2
      hctx.ne s (hctx.central s hs) h
    rw [sec10C_conjugate_eq_of_normalizer hn1] at hsw
    exact hctx.ne hsw

theorem sec10C_i4m_not_conj_z [Finite G] (h37 : Asc82Lemma37) (hf : Asc82Facts10)
    (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hctx : Sec10Ctx G t L S z K1 K2) {w : G} (hw : InducesTypeSome L w 5 1 4 (-1))
    (hwt : w ∈ centralizer ({t} : Set G)) (k : G) : k⁻¹ * z * k ≠ w := by
  intro hk
  have hpsp : IsPSp43 L := (hb G t L S z hctx.toSec10Z).1
  have h1 := h37 G t L hctx.toSec10Z.toSec10Setting.toSec3SettingLB z k hctx.toSec10Z.pocket
    (by rw [hk]; exact hwt)
  rw [hk] at h1
  exact hf.factsC.lay G L hpsp w hw h1

theorem sec10C_conjugate_mul (K : Subgroup G) (a b : G) :
    CFSG.conjugate (CFSG.conjugate K a) b = CFSG.conjugate K (a * b) := by
  ext x
  rw [mem_conjugate_iff', mem_conjugate_iff', mem_conjugate_iff']
  have e : a * (b * x * b⁻¹) * a⁻¹ = (a * b) * x * (a * b)⁻¹ := by group
  rw [e]

theorem sec10C_isSylow2Of_mono {S H K : Subgroup G} (h : IsSylow2Of S H) (hSK : S ≤ K)
    (hKH : K ≤ H) : IsSylow2Of S K := by
  refine ⟨hSK, h.2.1, fun hd => h.2.2 ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex S K H hSK hKH]
  exact Dvd.dvd.mul_right hd _

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Fink
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Conj

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem sec8s88_no_i3 (h87 : Asc82Lemma87) {G : Type} [Group G] [Finite G] {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hctx : Sec8Ctx G t L S z g B) :
    ∀ y : G, orderOf y = 2 → (∃ α : ℤˣ, InducesTypeSome L y 6 (-1) 3 α) → IsConj t y := by
  rintro y _ ⟨α, hα⟩
  exact absurd hα (h87 G t L S z g B hctx y α).2

theorem asc82Lemma88a_of (h36 : Asc82Lemma36) (h67b : Asc82Lemma67b) (h87 : Asc82Lemma87)
    (hH : ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G),
      Sec3SettingLB G t L → Asc82Hyp62 G) : Asc82Lemma88a := by
  intro G _ _ t L S z g B E hE y hy2 hyC hyz
  have hctx : Sec8Ctx G t L S z g B := hE.ctx
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hyN : y ∈ normalizer (L : Set G) := by
    have hconj : CFSG.conjugate L y = L := conjugate_eq_self_of_lemma36 h36 hS y hyC
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact (show x ∈ L ↔ x ∈ CFSG.conjugate L y from by rw [hconj]).trans
      (mem_conjugate_iff' (H := L) (g := y) (x := x))
  have hyz' : ∀ l ∈ L, l⁻¹ * z * l ≠ y := by
    intro l hl h
    exact hyz ⟨l⁻¹, L.inv_mem hl, by rw [← h]; group⟩
  exact (h67b G t L hS hctx.omega6m (hH G t L hS) E hE.elem z hctx.pocket.1 hctx.pocket.mem
    (sec8s88_no_i3 h87 hctx)).1 y hy2 hyN hyz'

theorem asc82Lemma88b_of (h67b : Asc82Lemma67b) (h87 : Asc82Lemma87)
    (hH : ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G),
      Sec3SettingLB G t L → Asc82Hyp62 G) : Asc82Lemma88b := by
  intro G _ _ t L S z g B E hE s hs y hy hy1
  have hctx : Sec8Ctx G t L S z g B := hE.ctx
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  exact (h67b G t L hS hctx.omega6m (hH G t L hS) E hE.elem z hctx.pocket.1 hctx.pocket.mem
    (sec8s88_no_i3 h87 hctx)).2 s hs y hy hy1

end CFSG.OddStandard.SmallF3.Omega

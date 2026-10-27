module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127A5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec127_normalizer_commutator {Y1 Y2 : Subgroup G} {g : G}
    (h1 : g ∈ normalizer (Y1 : Set G)) (h2 : g ∈ normalizer (Y2 : Set G)) :
    g ∈ normalizer ((⁅Y1, Y2⁆ : Subgroup G) : Set G) := by
  have key : ∀ {g : G}, g ∈ normalizer (Y1 : Set G) → g ∈ normalizer (Y2 : Set G) →
      ∀ x ∈ ⁅Y1, Y2⁆, g * x * g⁻¹ ∈ ⁅Y1, Y2⁆ := by
    intro g hg1 hg2 x hx
    have hmap : (⁅Y1, Y2⁆).map (MulAut.conj g).toMonoidHom ≤ ⁅Y1, Y2⁆ := by
      rw [Subgroup.map_commutator]
      refine Subgroup.commutator_mono ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hg1 y).mp hy
      · rintro _ ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hg2 y).mp hy
    simpa [MulAut.conj_apply] using hmap (Subgroup.mem_map_of_mem _ hx)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key h1 h2 x, fun hx => ?_⟩
  have hinv1 : g⁻¹ ∈ normalizer (Y1 : Set G) := (normalizer (Y1 : Set G)).inv_mem h1
  have hinv2 : g⁻¹ ∈ normalizer (Y2 : Set G) := (normalizer (Y2 : Set G)).inv_mem h2
  have h := key hinv1 hinv2 _ hx
  have h' : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
  rwa [h'] at h

theorem sec127_S_le_normalizer_ML [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G}
    {z : G} {K1 K2 E : Subgroup G} (hctx : Sec12Ctx G t L S z K1 K2 E) :
    S ≤ normalizer ((secM t S L ⊓ L : Subgroup G) : Set G) := by
  intro s hs
  have hsM : s ∈ secM t S L :=
    hp.r10.l109 G t L S z K1 K2 hctx.toSec10Ctx (Subgroup.le_normalizer hs)
  have hsL : s ∈ normalizer (L : Set G) := (hp.basic G t L S z hctx.toSec10Z).2.2.2.2.1 hs
  have hsM' : s ∈ normalizer ((secM t S L : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hsM
  rw [Subgroup.mem_normalizer_iff] at hsM' hsL ⊢
  intro x
  simp only [Subgroup.mem_inf, hsM' x, hsL x]

theorem sec127_ML_sup_S_le_normalizer [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G}
    {z : G} {K1 K2 E : Subgroup G} (hctx : Sec12Ctx G t L S z K1 K2 E) :
    (secM t S L ⊓ L) ⊔ S ≤ normalizer (secV t S L E : Set G) := by
  have hML : secM t S L ⊓ L ≤ normalizer (secV t S L E : Set G) := fun m hm =>
    sec127_normalizer_commutator (hctx.ML_norm hm) (Subgroup.le_normalizer hm)
  have hS : S ≤ normalizer (secV t S L E : Set G) := fun s hs =>
    sec127_normalizer_commutator (hctx.S_norm hs) (sec127_S_le_normalizer_ML hp hctx hs)
  exact sup_le hML hS

theorem sec127_ML_sup_S_le_centralizer [Finite G] {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 E : Subgroup G} (hctx : Sec12Ctx G t L S z K1 K2 E) :
    (secM t S L ⊓ L) ⊔ S ≤ centralizer ({t} : Set G) := by
  have hLt : L ≤ centralizer ({t} : Set G) := hctx.component.le
  exact sup_le (inf_le_right.trans hLt) hctx.sylow.1

theorem sec127_X_le [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 E X : Subgroup G} (hctx : Sec12Ctx G t L S z K1 K2 E) (hX : Sec12X t S L E X)
    (hA5 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) :
    X ≤ normalizer (secV t S L E : Set G) ∧ X ≤ centralizer ({t} : Set G) ∧ X ≤ L := by
  have hXle : X ≤ (secM t S L ⊓ L) ⊔ S := by
    have h1 : X ≤ X ⊔ secA t S L := le_sup_left
    rw [hX.sup] at h1
    exact h1
  refine ⟨hXle.trans (sec127_ML_sup_S_le_normalizer hp hctx),
    hXle.trans (sec127_ML_sup_S_le_centralizer hctx), ?_⟩
  exact (sec127_le_of_alt5_sup hctx.sylow.2.1 (sec127_S_le_normalizer_ML hp hctx) hA5 hXle).trans
    inf_le_right

end CFSG.OddStandard.SmallF3.Omega

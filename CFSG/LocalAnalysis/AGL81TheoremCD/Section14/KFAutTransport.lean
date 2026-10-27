module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAutAutomizer
public import CFSG.RankThree.PartOne.S12.InputsSec15
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAutStrongSup
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UIrr
import TauCeti.GroupTheory.SemidirectProduct

public section

noncomputable section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut

open CFSG.OddStandard.AltStdSec.SwapPartner (actQuot)

variable {X : Type} [Group X]

@[expose] noncomputable def autMap (F R : Subgroup X)
    (hRF : R ≤ Subgroup.normalizer (F : Set X)) :
    ↥(F ⊔ R) →* MulAut (↥F ⧸ Subgroup.center ↥F) :=
  (actQuot F).comp (Subgroup.inclusion (sup_le Subgroup.le_normalizer hRF))

theorem autMap_of_mem {F R : Subgroup X} (hRF : R ≤ Subgroup.normalizer (F : Set X))
    {g : ↥(F ⊔ R)} (hg : (g : X) ∈ F) :
    autMap F R hRF g = MulAut.conj (QuotientGroup.mk (⟨g, hg⟩ : ↥F)) := by
  rw [autMap, MonoidHom.comp_apply]
  exact actQuot_eq_conj_of_mem (F := F) (y := Subgroup.inclusion _ g) hg

theorem mem_centralizer_of_mem_ker_autMap {F R : Subgroup X}
    (hRF : R ≤ Subgroup.normalizer (F : Set X)) (hF : Group.IsPerfect ↥F)
    {g : ↥(F ⊔ R)} (hg : g ∈ (autMap F R hRF).ker) :
    (g : X) ∈ Subgroup.centralizer (F : Set X) :=
  mem_centralizer_of_actQuot_eq_one (F := F) hF (by
    simpa [autMap, MonoidHom.mem_ker] using hg)

theorem ker_autMap_le {F Y R : Subgroup X} (hRF : R ≤ Subgroup.normalizer (F : Set X))
    (hF : Group.IsPerfect ↥F) (hYF : Y ≤ F)
    (hRY : R ≤ Subgroup.normalizer (Y : Set X))
    (hFY : F ⊓ Subgroup.normalizer (Y : Set X) ≤ Y) :
    (autMap F R hRF).ker ≤ (Y ⊔ R).subgroupOf (F ⊔ R) := by
  intro g hg
  have hgC : (g : X) ∈ Subgroup.centralizer (F : Set X) :=
    mem_centralizer_of_mem_ker_autMap hRF hF hg
  obtain ⟨k, hkF, r, hrR, hgr⟩ :=
    (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := F) (K := R) hRF).mp g.2
  have hgN : (g : X) ∈ Subgroup.normalizer (Y : Set X) :=
    (Subgroup.centralizer_le_normalizer (Y : Set X)) ((Subgroup.centralizer_le hYF) hgC)
  have hkY : k ∈ Y := by
    refine hFY (Subgroup.mem_inf.mpr ⟨hkF, ?_⟩)
    have hrN : r⁻¹ ∈ Subgroup.normalizer (Y : Set X) := Subgroup.inv_mem _ (hRY hrR)
    have hkg : k = (g : X) * r⁻¹ := by rw [hgr]; group
    rw [hkg]
    exact Subgroup.mul_mem _ hgN hrN
  exact Subgroup.mem_subgroupOf.mpr (by
    rw [hgr]
    exact Subgroup.mul_mem_sup hkY hrR)

theorem not_dvd_card_ker_autMap {F R : Subgroup X} {p : ℕ} [Fact p.Prime] [Finite X]
    (hp3 : p ≠ 3)
    (hRF : R ≤ Subgroup.normalizer (F : Set X)) (hR3 : IsPGroup 3 R)
    (hF : Group.IsPerfect ↥F)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥F)) :
    ¬ p ∣ Nat.card (autMap F R hRF).ker := by
  intro hdiv
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' p hdiv
  let g : ↥(F ⊔ R) := x
  have hgker : g ∈ (autMap F R hRF).ker := x.2
  have hgord : orderOf g = p := (Subgroup.orderOf_coe x).trans hxord
  let D : Subgroup X := (Subgroup.zpowers g).map (F ⊔ R).subtype
  have hDcard : Nat.card (Subgroup.zpowers g) = p := by
    rw [Nat.card_zpowers, hgord]
  have hDp : IsPGroup p D :=
    (IsPGroup.of_card (n := 1) (by rw [hDcard, pow_one])).map (F ⊔ R).subtype
  have hDF : D ≤ F := isPGroup_le_of_le_sup hp3 hRF hR3 hDp (Subgroup.map_subtype_le _)
  have hgF : (g : X) ∈ F :=
    hDF (Subgroup.mem_map_of_mem (F ⊔ R).subtype (Subgroup.mem_zpowers g))
  have hgC : (g : X) ∈ Subgroup.centralizer (F : Set X) :=
    mem_centralizer_of_mem_ker_autMap hRF hF hgker
  have hcenter : (⟨(g : X), hgF⟩ : ↥F) ∈ Subgroup.center ↥F := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hgC (y : X) y.2
  have hpdvd : p ∣ Nat.card (Subgroup.center ↥F) := by
    have hord : orderOf (⟨(g : X), hgF⟩ : ↥F) = p := by
      rw [Subgroup.orderOf_mk]
      exact (Subgroup.orderOf_coe g).trans hgord
    have := orderOf_dvd_natCard
      (⟨⟨(g : X), hgF⟩, hcenter⟩ : ↥(Subgroup.center ↥F))
    rwa [Subgroup.orderOf_mk, hord] at this
  exact hZ hpdvd

theorem card_map_autMap_eq {F R : Subgroup X} (hRF : R ≤ Subgroup.normalizer (F : Set X))
    (hF : Group.IsPerfect ↥F)
    (hRC : R ⊓ Subgroup.centralizer (F : Set X) = ⊥) :
    Nat.card ((R.subgroupOf (F ⊔ R)).map (autMap F R hRF)) = Nat.card R := by
  let f := autMap F R hRF
  let H : Subgroup ↥(F ⊔ R) := R.subgroupOf (F ⊔ R)
  have hdisj : H ⊓ f.ker = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    have hxR : (x : X) ∈ R := Subgroup.mem_subgroupOf.mp hx.1
    have hxC : (x : X) ∈ Subgroup.centralizer (F : Set X) :=
      mem_centralizer_of_mem_ker_autMap hRF hF hx.2
    have hxbot : (x : X) ∈ (⊥ : Subgroup X) := by
      rw [← hRC]
      exact Subgroup.mem_inf.mpr ⟨hxR, hxC⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  have hker : f.ker.subgroupOf H = ⊥ := by
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_comm]
    exact hdisj
  have hφker : (f.subgroupMap H).ker = ⊥ := by
    rw [Subgroup.ker_subgroupMap, hker]
  have hφinj : Function.Injective (f.subgroupMap H) :=
    (MonoidHom.ker_eq_bot_iff (f.subgroupMap H)).mp hφker
  have hcardH : Nat.card (H.map f) = Nat.card H := by
    have h := Subgroup.card_map_of_injective (K := (⊤ : Subgroup ↥H))
      (f := f.subgroupMap H) hφinj
    rw [Subgroup.map_top_of_surjective _ (MonoidHom.subgroupMap_surjective f H),
      Subgroup.card_top, Subgroup.card_top] at h
    exact h
  change Nat.card (H.map f) = Nat.card R
  rw [hcardH]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv

theorem range_conj_le_range_autMap {F R : Subgroup X}
    (hRF : R ≤ Subgroup.normalizer (F : Set X)) :
    (MulAut.conj :
      (↥F ⧸ Subgroup.center ↥F) →* MulAut (↥F ⧸ Subgroup.center ↥F)).range ≤
      (autMap F R hRF).range := by
  rintro _ ⟨q, rfl⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  let g : ↥(F ⊔ R) := ⟨k, Subgroup.mem_sup_left k.2⟩
  refine ⟨g, ?_⟩
  have h := (autMap_of_mem hRF (g := g) k.2).symm
  rwa [← h]

theorem isStronglyPEmbedded_autMap_range {F Y R : Subgroup X} {p : ℕ} [Fact p.Prime]
    [Finite X] (hRF : R ≤ Subgroup.normalizer (F : Set X))
    (hY : CFSG.RankThree.PartOne.IsStronglyPEmbedded p ((Y ⊔ R).subgroupOf (F ⊔ R)))
    (hkY : (autMap F R hRF).ker ≤ (Y ⊔ R).subgroupOf (F ⊔ R))
    (hpk : ¬ p ∣ Nat.card (autMap F R hRF).ker) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p
      ((((Y ⊔ R).subgroupOf (F ⊔ R)).map (autMap F R hRF)).subgroupOf
        (autMap F R hRF).range) :=
  CFSG.LocalAnalysis.UniquenessCase.UC22.u81_isStronglyPEmbedded_subgroupOf_range
    hY (autMap F R hRF) hkY hpk

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut

end

end

module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63C1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ConjBasic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma exists_conjSub_inv_le_of_sylow {H T E : Subgroup G} (hT : IsSylowIn 2 H T)
    (hEH : E ≤ H) (hE : IsPGroup 2 E) : ∃ c ∈ H, conjSub c⁻¹ E ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsub_pg : IsPGroup 2 (T.subgroupOf H) := hT.2.1.comap_subtype
  have hTsub_ne : ¬ 2 ∣ (T.subgroupOf H).index := by
    simpa only [Subgroup.relIndex] using hT.2.2
  let P : Sylow 2 ↥H := hTsub_pg.toSylow hTsub_ne
  have hPcoe : (P : Subgroup ↥H) = T.subgroupOf H := rfl
  haveI : Finite (Sylow 2 ↥H) := Sylow.finite_of_finiteIndex P
  have hEsub_pg : IsPGroup 2 (E.subgroupOf H) := hE.comap_subtype
  obtain ⟨Q, hQ⟩ := hEsub_pg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (M := ↥H) P Q
  refine ⟨(c : G), c.2, ?_⟩
  intro x hx
  rw [conjSub, Subgroup.mem_map] at hx
  obtain ⟨e, he, rfl⟩ := hx
  have heH : e ∈ H := hEH he
  have heQ : (⟨e, heH⟩ : ↥H) ∈ (Q : Subgroup ↥H) :=
    hQ (Subgroup.mem_subgroupOf.mpr he)
  have hmem : (⟨e, heH⟩ : ↥H) ∈ ((c • P : Sylow 2 ↥H) : Subgroup ↥H) := by
    rw [hc]; exact heQ
  rw [Sylow.coe_subgroup_smul] at hmem
  have h2 := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hmem
  rw [hPcoe] at h2
  have h3 : (((MulAut.conj c)⁻¹ • (⟨e, heH⟩ : ↥H) : ↥H) : G) =
      (c : G)⁻¹ * e * (c : G) := by
    rw [MulAut.smul_def, MulAut.conj_inv_apply]
    simp
  have h4 : (c : G)⁻¹ * e * (c : G) ∈ T := h3 ▸ Subgroup.mem_subgroupOf.mp h2
  simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h4

private lemma y63_conjSub_mul (a b : G) (X : Subgroup G) :
    conjSub (a * b) X = conjSub a (conjSub b X) := by
  ext z
  rw [mem_conjSub, mem_conjSub]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨b * u * b⁻¹, mem_conjSub.mpr ⟨u, hu, rfl⟩, by group⟩
  · rintro ⟨v, hv, hz⟩
    obtain ⟨u, hu, rfl⟩ := mem_conjSub.mp hv
    exact ⟨u, hu, by rw [← hz]; group⟩

theorem y63_comm_T_le_S (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R = c.s.T) :
    ⁅c.s.T, c.s.T⁆ ≤ c.s.fr.S := by
  have hTeq : c.s.T = c.s.fr.S ⊔ zpowers c.s.t := hRT ▸ y5_R_eq hH
  have hcomm : ∀ x ∈ c.s.fr.S, ∀ y ∈ zpowers c.s.t, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (s3_comm_t_of_mem_L c.s (s3_S_le_L c.s hx)) k).eq
  rw [hTeq]
  refine Subgroup.commutator_le.mpr ?_
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨s₁, hs₁, u₁, hu₁, rfl⟩ :=
    CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_commute hcomm hg₁
  obtain ⟨s₂, hs₂, u₂, hu₂, rfl⟩ :=
    CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_commute hcomm hg₂
  have hsu₁ : Commute s₁ u₁ := (commute_iff_eq s₁ u₁).mpr (hcomm s₁ hs₁ u₁ hu₁)
  have hsu₂ : Commute s₁ u₂ := (commute_iff_eq s₁ u₂).mpr (hcomm s₁ hs₁ u₂ hu₂)
  have hu₁s₂ : Commute u₁ s₂ := (commute_iff_eq u₁ s₂).mpr (hcomm s₂ hs₂ u₁ hu₁).symm
  have hu₁u₂ : Commute u₁ u₂ := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu₁
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu₂
    exact Commute.zpow_zpow_self c.s.t i j
  have h1 : ⁅u₁, s₂ * u₂⁆ = 1 := by
    rw [commutatorElement_mul_right_eq_mul_conj, hu₁s₂.commutator_eq, hu₁u₂.commutator_eq]
    group
  have h2 : ⁅s₁, s₂ * u₂⁆ = ⁅s₁, s₂⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj, hsu₂.commutator_eq]
    group
  have h3 : ⁅s₁ * u₁, s₂ * u₂⁆ = ⁅s₁, s₂⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, h1, h2]
    group
  rw [h3, commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hs₁ hs₂)
    (Subgroup.inv_mem _ hs₁)) (Subgroup.inv_mem _ hs₂)

theorem y63_extr_cent {Q T : Subgroup G} {t x : G} (hQ : IsPGroup 2 ↥Q)
    (hT : IsSylowIn 2 (centralizer ({t} : Set G)) T) (hxt : IsConj t x)
    (hcard : Nat.card ↥T ≤ Nat.card ↥(centEl Q x)) :
    ∃ y : G, y * t * y⁻¹ = x ∧ centEl Q x = conjSub y T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y₀, hy₀⟩ := isConj_iff.mp hxt
  let D : Subgroup G := conjSub y₀⁻¹ (centEl Q x)
  have hDdef : D = conjSub y₀⁻¹ (centEl Q x) := rfl
  have hDH : D ≤ centralizer ({t} : Set G) := by
    intro g hg
    rw [hDdef] at hg
    obtain ⟨w, hw, rfl⟩ := mem_conjSub.mp hg
    simp only [inv_inv]
    rw [Subgroup.mem_centralizer_iff]
    intro σ hσ
    simp only [Set.mem_singleton_iff] at hσ
    rw [hσ]
    have hwcomm : x * w = w * x :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hw).2 x (by simp)
    have ht : t = y₀⁻¹ * x * y₀ := by rw [← hy₀]; group
    rw [ht]
    calc y₀⁻¹ * x * y₀ * (y₀⁻¹ * w * y₀) = y₀⁻¹ * (x * w) * y₀ := by group
      _ = y₀⁻¹ * (w * x) * y₀ := by rw [hwcomm]
      _ = (y₀⁻¹ * w * y₀) * (y₀⁻¹ * x * y₀) := by group
  have hDpg : IsPGroup 2 D := by
    rw [hDdef, conjSub]
    exact (hQ.to_le inf_le_left).map (MulAut.conj y₀⁻¹).toMonoidHom
  have hDcard : Nat.card ↥D = Nat.card ↥(centEl Q x) := by
    rw [hDdef, conjSub]
    exact Subgroup.card_map_of_injective (MulAut.conj y₀⁻¹).injective
  obtain ⟨c, hcH, hc⟩ :=
    exists_conjSub_inv_le_of_sylow (H := centralizer ({t} : Set G)) (E := D) hT hDH hDpg
  have hcard_le : Nat.card ↥T ≤ Nat.card ↥(conjSub c⁻¹ D) := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hDcard]
    exact hcard
  have heq : conjSub c⁻¹ D = T := Subgroup.eq_of_le_of_card_ge hc hcard_le
  have hD_eq : D = conjSub c T := by
    rw [← heq]
    exact (conjSub_conjSub_inv c D).symm
  refine ⟨y₀ * c, ?_, ?_⟩
  · have hct : c * t * c⁻¹ = t := by
      have htc : t * c = c * t := Subgroup.mem_centralizer_iff.mp hcH t (by simp)
      rw [← htc]; group
    calc (y₀ * c) * t * (y₀ * c)⁻¹ = y₀ * (c * t * c⁻¹) * y₀⁻¹ := by group
      _ = y₀ * t * y₀⁻¹ := by rw [hct]
      _ = x := hy₀
  · calc centEl Q x = conjSub y₀ D := (conjSub_conjSub_inv y₀ (centEl Q x)).symm
      _ = conjSub y₀ (conjSub c T) := by rw [hD_eq]
      _ = conjSub (y₀ * c) T := (y63_conjSub_mul y₀ c T).symm

theorem y63_not_mem_comm (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R = c.s.T) {x y : G}
    (hy : y * c.s.t * y⁻¹ = x) (hC : centEl (y63Q c) x = conjSub y c.s.T) :
    x ∉ ⁅centEl (y63Q c) x, centEl (y63Q c) x⁆ := by
  intro hx
  have hmap : conjSub y ⁅c.s.T, c.s.T⁆ = ⁅conjSub y c.s.T, conjSub y c.s.T⁆ :=
    Subgroup.map_commutator c.s.T c.s.T (MulAut.conj y).toMonoidHom
  have hx' : x ∈ conjSub y ⁅c.s.T, c.s.T⁆ := by
    rw [hmap]
    exact hC ▸ hx
  obtain ⟨a, ha, hay⟩ := mem_conjSub.mp hx'
  have ha_t : a = c.s.t := by
    have h1 : y * a * y⁻¹ = y * c.s.t * y⁻¹ := by rw [hay, hy]
    exact mul_left_cancel (mul_right_cancel h1)
  exact s3_t_not_mem_L c.s hH.h31 (s3_S_le_L c.s (y63_comm_T_le_S c hH hRT (ha_t ▸ ha)))

theorem y63_y_cent_z (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R = c.s.T) {x y : G} (hC : centEl (y63Q c) x = conjSub y c.s.T)
    (hz : c.s.fr.z ∈ ⁅centEl (y63Q c) x, centEl (y63Q c) x⁆) :
    y * c.s.fr.z * y⁻¹ = c.s.fr.z := by
  have hA : LFactsA c.s := lfactsA_of_setting hH.hS hH.hZ c.s
  let w : G := y⁻¹ * c.s.fr.z * y
  have hwdef : w = y⁻¹ * c.s.fr.z * y := rfl
  have hzw : y * w * y⁻¹ = c.s.fr.z := by rw [hwdef]; group
  have hmap : conjSub y ⁅c.s.T, c.s.T⁆ = ⁅conjSub y c.s.T, conjSub y c.s.T⁆ :=
    Subgroup.map_commutator c.s.T c.s.T (MulAut.conj y).toMonoidHom
  have hz' : c.s.fr.z ∈ conjSub y ⁅c.s.T, c.s.T⁆ := by
    rw [hmap]
    exact hC ▸ hz
  have hzw_comm : w ∈ ⁅c.s.T, c.s.T⁆ := by
    obtain ⟨a, ha, haz⟩ := mem_conjSub.mp hz'
    have hwa : w = a := by rw [hwdef, ← haz]; group
    exact hwa.symm ▸ ha
  have hwS : w ∈ c.s.fr.S := y63_comm_T_le_S c hH hRT hzw_comm
  have hwL : w ∈ L := s3_S_le_L c.s hwS
  have hzD : c.s.fr.z ∈ centEl (y63Q c) x := by
    have h := Subgroup.commutator_le_sup (centEl (y63Q c) x) (centEl (y63Q c) x) hz
    simpa using h
  have hwT : w ∈ c.s.T := by
    obtain ⟨a, ha, haz⟩ := mem_conjSub.mp (hC ▸ hzD)
    have hwa : w = a := by rw [hwdef, ← haz]; group
    exact hwa.symm ▸ ha
  have hwcen : w ∈ Subgroup.centralizer (c.s.T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro τ hτ
    have hv : y * τ * y⁻¹ ∈ centEl (y63Q c) x := by
      rw [hC]
      exact mem_conjSub.mpr ⟨τ, hτ, rfl⟩
    have hvQ : y * τ * y⁻¹ ∈ y63Q c := (Subgroup.mem_inf.mp hv).1
    have hzQ : c.s.fr.z ∈ cen (y63Q c) := y63_z_mem_cen_Q c hH hF hRT
    have hvcomm : (y * τ * y⁻¹) * c.s.fr.z = c.s.fr.z * (y * τ * y⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzQ).2 _ hvQ
    rw [← hzw] at hvcomm
    have h1 : y * (τ * w) * y⁻¹ = y * (w * τ) * y⁻¹ := by
      calc y * (τ * w) * y⁻¹ = (y * τ * y⁻¹) * (y * w * y⁻¹) := by group
        _ = (y * w * y⁻¹) * (y * τ * y⁻¹) := hvcomm
        _ = y * (w * τ) * y⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h1)
  have hwzt : w ∈ zt c.s := by
    have hcenT : cen c.s.T = zt c.s := by
      rw [← hRT]
      exact s3_cen_R_eq c.s hH.hS hH.hZ (s3_T_inf_centralizer c.s hH.h31)
    rw [← hcenT]
    exact Subgroup.mem_inf.mpr ⟨hwT, hwcen⟩
  rcases (s3_mem_zt_iff c.s hA).mp hwzt with h1 | hz1 | ht1 | hzt1
  · exfalso
    exact y54_z_ne_one (c := c.toCtx5) hH (by rw [← hzw, h1]; simp)
  · simpa [hz1] using hzw
  · exfalso
    rw [ht1] at hwS
    exact s3_t_not_mem_L c.s hH.h31 (s3_S_le_L c.s hwS)
  · exfalso
    apply s3_t_not_mem_L c.s hH.h31
    rw [hzt1] at hwL
    have ht : c.s.t = c.s.fr.z⁻¹ * (c.s.fr.z * c.s.t) := by group
    rw [ht]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (s3_z_mem_L c.s)) hwL

end CFSG.OddStandard.HigherRank.YamadaG23

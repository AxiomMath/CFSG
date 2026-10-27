module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBParts
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Base

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

section Generic

variable {G : Type*} [Group G]

theorem sec52_map_le_centralizer_map {X Y : Subgroup G} (φ : G →* G)
    (hXY : X ≤ centralizer (Y : Set G)) :
    X.map φ ≤ centralizer ((Y.map φ : Subgroup G) : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, mem_centralizer_iff.1 (hXY hx) y hy]

theorem sec52_map_map_conj (A : Subgroup G) (a b : G) :
    (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      A.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem sec52_sup_le_centralizer_sup {X₁ X₂ Y₁ Y₂ : Subgroup G}
    (h11 : X₁ ≤ centralizer (Y₁ : Set G)) (h12 : X₁ ≤ centralizer (Y₂ : Set G))
    (h21 : X₂ ≤ centralizer (Y₁ : Set G)) (h22 : X₂ ≤ centralizer (Y₂ : Set G)) :
    X₁ ⊔ X₂ ≤ centralizer ((Y₁ ⊔ Y₂ : Subgroup G) : Set G) := by
  refine sup_le ?_ ?_
  · rw [le_centralizer_iff]
    exact sup_le (le_centralizer_iff.1 h11) (le_centralizer_iff.1 h12)
  · rw [le_centralizer_iff]
    exact sup_le (le_centralizer_iff.1 h21) (le_centralizer_iff.1 h22)

theorem sec52_commute_aux {K : Subgroup G} {s t : G} (hs : s * s = 1) (hst : s * t = t * s)
    (hKt : K.map (MulAut.conj t).toMonoidHom ≤ centralizer (K : Set G))
    (h15 : K.map (MulAut.conj (s * t)).toMonoidHom ≤ centralizer (K : Set G)) :
    (K ⊔ K.map (MulAut.conj s).toMonoidHom).map (MulAut.conj t).toMonoidHom ≤
      centralizer ((K ⊔ K.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) := by
  have e1 : (K.map (MulAut.conj s).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      K.map (MulAut.conj (s * t)).toMonoidHom := by
    rw [sec52_map_map_conj, hst]
  have e2 : (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom =
      K.map (MulAut.conj (s * t)).toMonoidHom := sec52_map_map_conj K t s
  have e3 : (K.map (MulAut.conj (s * t)).toMonoidHom).map (MulAut.conj s).toMonoidHom =
      K.map (MulAut.conj t).toMonoidHom := by
    rw [sec52_map_map_conj, ← mul_assoc, hs, one_mul]
  rw [Subgroup.map_sup]
  refine sec52_sup_le_centralizer_sup hKt ?_ ?_ ?_
  · have := sec52_map_le_centralizer_map (MulAut.conj s).toMonoidHom h15
    rwa [e3] at this
  · rwa [e1]
  · rw [e1]
    have := sec52_map_le_centralizer_map (MulAut.conj s).toMonoidHom hKt
    rwa [e2] at this

end Generic

section Diagonal

variable {G : Type*} [Group G] {t : G}

theorem sec52_range_diag_le_of_le {A B : Subgroup G} (hBA : B ≤ A)
    (hA : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hB : ⁅B, B.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) :
    (Common.diagonalHom B t hB).range ≤ (Common.diagonalHom A t hA).range := by
  rintro _ ⟨b, rfl⟩
  exact ⟨⟨b, hBA b.2⟩, rfl⟩

theorem sec52_range_diag_sup {B C : Subgroup G}
    (hA : ⁅B ⊔ C, (B ⊔ C).map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hB : ⁅B, B.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hC : ⁅C, C.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) :
    (Common.diagonalHom (B ⊔ C) t hA).range =
      (Common.diagonalHom B t hB).range ⊔ (Common.diagonalHom C t hC).range := by
  refine le_antisymm ?_ (sup_le (sec52_range_diag_le_of_le le_sup_left hA hB)
    (sec52_range_diag_le_of_le le_sup_right hA hC))
  have hle : B ⊔ C ≤ (((Common.diagonalHom B t hB).range ⊔
      (Common.diagonalHom C t hC).range).comap (Common.diagonalHom (B ⊔ C) t hA)).map
        (B ⊔ C).subtype :=
    sup_le (fun b hb => ⟨⟨b, mem_sup_left hb⟩, mem_sup_left ⟨⟨b, hb⟩, rfl⟩, rfl⟩)
      (fun c hc => ⟨⟨c, mem_sup_right hc⟩, mem_sup_right ⟨⟨c, hc⟩, rfl⟩, rfl⟩)
  rintro _ ⟨a, rfl⟩
  obtain ⟨b, hb, hba⟩ := hle a.2
  rw [show b = a from Subtype.ext hba] at hb
  exact hb

theorem sec52_range_diag_conj {A : Subgroup G} {s : G} (hst : s * t = t * s)
    (hA : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hAs : ⁅A.map (MulAut.conj s).toMonoidHom,
      (A.map (MulAut.conj s).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) :
    (Common.diagonalHom (A.map (MulAut.conj s).toMonoidHom) t hAs).range =
      (Common.diagonalHom A t hA).range.map (MulAut.conj s).toMonoidHom := by
  have h1 : t⁻¹ * s = s * t⁻¹ := ((Commute.inv_right (show Commute s t from hst)).eq).symm
  have h2 : s⁻¹ * t = t * s⁻¹ := (Commute.inv_left (show Commute s t from hst)).eq
  have key : ∀ a : G, (s * a * s⁻¹) * (t⁻¹ * (s * a * s⁻¹) * t) =
      s * (a * (t⁻¹ * a * t)) * s⁻¹ := fun a => by
    calc (s * a * s⁻¹) * (t⁻¹ * (s * a * s⁻¹) * t)
        = (s * a * s⁻¹) * ((t⁻¹ * s) * a * (s⁻¹ * t)) := by group
      _ = (s * a * s⁻¹) * ((s * t⁻¹) * a * (t * s⁻¹)) := by rw [h1, h2]
      _ = s * (a * (t⁻¹ * a * t)) * s⁻¹ := by group
  ext y
  constructor
  · rintro ⟨⟨_, ⟨a, ha, rfl⟩⟩, rfl⟩
    exact ⟨_, ⟨⟨a, ha⟩, rfl⟩, (key a).symm⟩
  · rintro ⟨_, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
    exact ⟨⟨s * a * s⁻¹, a, ha, rfl⟩, key a⟩

theorem sec52_center_eq_ker {A : Subgroup G} (hA : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    {L : Subgroup G} (hL : (Common.diagonalHom A t hA).range = L) (hZ : center L = ⊥) :
    center A = (Common.diagonalHom A t hA).ker := by
  refine le_antisymm (fun z hz => ?_) (Common.ker_diagonalHom_le_center hA)
  rw [MonoidHom.mem_ker]
  have hzL : Common.diagonalHom A t hA z ∈ L := by
    rw [← hL]
    exact ⟨z, rfl⟩
  have hc : (⟨_, hzL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    rintro ⟨l, hl⟩
    rw [← hL] at hl
    obtain ⟨a, rfl⟩ := hl
    apply Subtype.ext
    change Common.diagonalHom A t hA a * Common.diagonalHom A t hA z =
      Common.diagonalHom A t hA z * Common.diagonalHom A t hA a
    rw [← map_mul, ← map_mul, mem_center_iff.1 hz a]
  rw [hZ, mem_bot] at hc
  exact congrArg Subtype.val hc

theorem sec52_isPerfect_sup_conj {K : Subgroup G} (s : G) (hK : ⁅K, K⁆ = K) :
    Group.IsPerfect (K ⊔ K.map (MulAut.conj s).toMonoidHom : Subgroup G) := by
  haveI : Group.IsPerfect K := (Common.isPerfect_subgroup_iff_commutator_eq K).2 hK
  haveI : Group.IsPerfect (K.map (MulAut.conj s).toMonoidHom) :=
    (Common.isPerfect_subgroup_iff_commutator_eq _).2 (by rw [← Subgroup.map_commutator, hK])
  exact Common.isPerfect_sup_of_isPerfect

end Diagonal

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

namespace CaseBData

theorem sec52_isSimpleGroup_L : IsSimpleGroup d.L :=
  d.e.isSimpleGroup_congr.2 (CFSG.Quasithin.H13.Sec53F.Unit.isSimpleGroup_hypPSU_five h)

theorem sec52_not_comm_L (hB : d.CaseBHyp) : ¬ ∀ x ∈ d.L, ∀ y ∈ d.L, x * y = y * x := by
  intro hcomm
  haveI : IsSimpleGroup d.L := sec52_isSimpleGroup_L
  obtain ⟨x, hx⟩ := exists_ne (1 : d.L)
  have hcen : x ∈ Subgroup.center d.L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcomm y y.2 x x.2)
  rw [hB.hyp.setting.center_eq_bot] at hcen
  exact hx (Subgroup.mem_bot.1 hcen)

theorem sec52 (hB : d.CaseBHyp) (c : d.CaseBData) (h15 : CaseBData.Sec52Comm c) :
    CaseBData.Sec52 c := by
  have ht : d.t * d.t = 1 := hB.hyp.t_mul_t
  have ht' : d.t⁻¹ = d.t := hB.hyp.t_inv'
  have hs : d.s * d.s = 1 := d.s_mul_s
  have hst : d.s * d.t = d.t * d.s :=
    mem_centralizer_singleton_iff.1 (hB.hyp.L_le_centralizer ((d.pull_le_L _) d.s_mem_N₂))
  have hKt : c.Kc.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (c.Kc : Set G) :=
    c.Kt_le_centralizer_Kc hB
  have hcomm : c.Nc.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (c.Nc : Set G) :=
    sec52_commute_aux hs hst hKt h15
  have hcomm' : ⁅c.Nc, c.Nc.map (MulAut.conj d.t⁻¹).toMonoidHom⁆ = ⊥ := by
    rw [ht']
    exact commutator_eq_bot_iff_le_centralizer.2 (le_centralizer_iff.1 hcomm)
  have hcommK := c.commutator_Kc_map_conj_t_inv hB
  have hcommKs : ⁅c.Kc.map (MulAut.conj d.s).toMonoidHom,
      (c.Kc.map (MulAut.conj d.s).toMonoidHom).map (MulAut.conj d.t⁻¹).toMonoidHom⁆ = ⊥ :=
    eq_bot_iff.2 ((Subgroup.commutator_mono le_sup_right
      (Subgroup.map_mono le_sup_right)).trans hcomm'.le)
  have hrange : (Common.diagonalHom c.Nc d.t hcomm').range = d.L := by
    have e1 : (Common.diagonalHom c.Nc d.t hcomm').range = (c.δ hB).range ⊔
        (Common.diagonalHom (c.Kc.map (MulAut.conj d.s).toMonoidHom) d.t hcommKs).range :=
      sec52_range_diag_sup hcomm' hcommK hcommKs
    have e2 : (Common.diagonalHom (c.Kc.map (MulAut.conj d.s).toMonoidHom) d.t hcommKs).range =
        (c.δ hB).range.map (MulAut.conj d.s).toMonoidHom :=
      sec52_range_diag_conj hst hcommK hcommKs
    rw [e1, e2, c.range_δ hB, hB.L₁_inf_centralizer_t]
    exact A₃N₁_sup_conj_s_eq_L d
  have hker : center c.Nc = (Common.diagonalHom c.Nc d.t hcomm').ker :=
    sec52_center_eq_ker hcomm' hrange hB.hyp.setting.center_eq_bot
  have hodd : Odd (Nat.card (Common.diagonalHom c.Nc d.t hcomm').ker) :=
    Common.odd_card_ker_diagonalHom_of_centralizer_le hcomm' ht
      (by rw [hrange]; exact hB.hyp.sec3_1'.1.le)
      (by
        rw [hrange]
        by_contra hne
        push Not at hne
        exact sec52_not_comm_L hB hne)
  have hIso : c.Nc ⧸ center c.Nc ≃* hypPSU h 2 1 :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      ((QuotientGroup.quotientKerEquivRange _).trans ((MulEquiv.subgroupCongr hrange).trans d.e))
  have hdiag : ∀ x (hx : x ∈ c.Nc), (Common.diagonalHom c.Nc d.t hcomm') ⟨x, hx⟩ =
      x * (d.t * x * d.t⁻¹) := fun x hx => by
    rw [Common.diagonalHom_apply]
    simp only [ht']
  refine ⟨⟨?_, ?_⟩, ?_, hcomm, ?_, ?_, ⟨hIso⟩⟩
  · haveI : Group.IsPerfect c.Nc := sec52_isPerfect_sup_conj d.s (c.commutator_Kc hB)
    exact Group.IsPerfect.commutator_eq_top
  · exact hIso.isSimpleGroup_congr.2
      (CFSG.Quasithin.H13.Sec53F.Unit.isSimpleGroup_hypPSU_five h)
  · rw [hker]
    exact hodd
  · intro x hx
    rw [← hdiag x hx, ← hrange]
    exact ⟨⟨x, hx⟩, rfl⟩
  · intro y hy
    rw [← hrange] at hy
    obtain ⟨⟨x, hx⟩, rfl⟩ := hy
    exact ⟨x, hx, (hdiag x hx).symm⟩

end CaseBData

end Data

namespace CaseBParts

theorem sec52 : Sec52Statement :=
  fun _ _ _ _ _ _ _ _ hB c h15 => Data.CaseBData.sec52 hB c h15

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5

module

public import CFSG.ClassicalInvolution.Asc77.AscThmA

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace AscThmA

open CFSG CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.LocalCores

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem centralizer_layer_eq_bot [Finite G]
    (hsolv : ∀ N : Subgroup G, N.Normal → Group.IsSolvable ↥N → N = ⊥) :
    Subgroup.centralizer (layer G : Set G) = ⊥ := by
  have hF : fittingSubgroup G = ⊥ := hsolv _ inferInstance inferInstance
  have hFE : generalizedFitting G = layer G := by
    rw [generalizedFitting, hF, bot_sup_eq]
  have hle : Subgroup.centralizer (layer G : Set G) ≤ layer G := by
    have := CFSG.centralizer_generalizedFitting_le G
    rwa [hFE] at this
  have hEn : (layer G).Normal := normal_layer
  have hCn : (Subgroup.centralizer (layer G : Set G)).Normal := Subgroup.normal_centralizer
  apply hsolv _ hCn
  refine Group.isSolvable_of_comm fun a b => ?_
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp a.2 b (hle b.2)).symm

theorem exists_component_not_commute [Finite G]
    (hC : Subgroup.centralizer (layer G : Set G) = ⊥) {z : G} (hz : z ≠ 1) :
    ∃ L : Subgroup G, IsComponent L ∧ ¬ ∀ y ∈ L, y * z = z * y := by
  by_contra hcon
  have hall : ∀ L : Subgroup G, IsComponent L → ∀ y ∈ L, y * z = z * y := by
    intro L hL
    by_contra h
    exact hcon ⟨L, hL, h⟩
  have hle : layer G ≤ Subgroup.centralizer ({z} : Set G) :=
    sSup_le fun L hL y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hall L hL y hy)
  have hzC : z ∈ Subgroup.centralizer (layer G : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle he)
  rw [hC, Subgroup.mem_bot] at hzC
  exact hz hzC

theorem normal_of_forall_le_normalizer {L : Subgroup G} (hgen : (⨆ J ∈ Ω, J) = ⊤)
    (h : ∀ J ∈ Ω, J ≤ Subgroup.normalizer (L : Set G)) : L.Normal := by
  have : (⨆ J ∈ Ω, J) ≤ Subgroup.normalizer (L : Set G) := iSup₂_le h
  rw [hgen, top_le_iff] at this
  exact Subgroup.normalizer_eq_top_iff.mp this

theorem mem_component_of_not_commutes [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    (h613 : Comm613On Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {L : Subgroup G} (hL : IsComponent L) (hLn : L.Normal)
    (hnc : ¬ ∀ y ∈ L, y * z = z * y) : z ∈ L := by
  by_contra hzL
  obtain ⟨V, hV, hVR, hzV⟩ := exists_sylow_mem_RSet hp hΩ hK hz
  have hVL : V ⊓ L = ⊥ := inf_eq_bot_of_uniqueInvolution_not_mem hz hV.1 hV.2.1 hzL
  have h2 : ⁅V, L⁆ = ⊥ :=
    commutator_eq_bot_of_le_oddCoreOf_component hL hLn (h613 V hVR L hLn hVL)
  exact hnc fun y hy =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2 hzV) y hy

structure Hyp173 (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) : Prop where
  hp : p ≠ 2
  hq : 5 ≤ p ^ f
  hΩ : HypOmegaMod p f Ω
  h613 : Comm613On Ω
  thmA : ThmAOn Ω
  hsolv : ∀ N : Subgroup G, N.Normal → Group.IsSolvable ↥N → N = ⊥
  hgen : (⨆ J ∈ Ω, J) = ⊤

namespace Hyp173

variable [Finite G] (S : Hyp173 p f Ω)
include S

theorem centralizer_layer : Subgroup.centralizer (layer G : Set G) = ⊥ :=
  centralizer_layer_eq_bot S.hsolv

omit [Finite G] in
theorem component_normal {L : Subgroup G} (hL : IsComponent L) : L.Normal :=
  normal_of_forall_le_normalizer S.hgen fun J hJ k hk =>
    mem_normalizer_iff_conjSub_eq.mpr (S.thmA J hJ L hL k hk)

theorem exists_normal_component {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) :
    ∃ L : Subgroup G, IsComponent L ∧ L.Normal ∧ z ∈ L ∧ ¬ ∀ y ∈ L, y * z = z * y := by
  obtain ⟨L, hL, hnc⟩ := exists_component_not_commute S.centralizer_layer hz.ne_one
  have hLn := S.component_normal hL
  exact ⟨L, hL, hLn, mem_component_of_not_commutes S.hp S.hΩ S.h613 hK hz hL hLn hnc, hnc⟩

theorem eq_one_of_central_in_component {L : Subgroup G} (hL : IsComponent L) {a : G} (ha : a ∈ L)
    (hcen : ∀ w ∈ L, w * a = a * w) : a = 1 := by
  have hle : layer G ≤ Subgroup.centralizer ({a} : Set G) := by
    refine sSup_le fun M hM y hy => Subgroup.mem_centralizer_singleton_iff.mpr ?_
    by_cases hML : M = L
    · subst hML
      exact hcen y hy
    · exact mul_comm_of_ne hM hL hML hy ha
  have hmem : a ∈ Subgroup.centralizer (layer G : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle he)
  rw [S.centralizer_layer, Subgroup.mem_bot] at hmem
  exact hmem

theorem commutes_of_not_mem {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) {z t : G}
    (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) {L : Subgroup G}
    (hL : IsComponent L) (hzL : z ∈ L) (hnc : ¬ ∀ y ∈ L, y * z = z * y) (htL : t ∉ L) :
    Commutes K J := by
  have hLn : L.Normal := S.component_normal hL
  obtain ⟨L', hL', hL'n, htL', -⟩ := S.exists_normal_component hJ ht
  have hne : L ≠ L' := fun h => htL (h ▸ htL')
  have htc : ∀ y ∈ L, y * t = t * y := fun y hy => mul_comm_of_ne hL hL' hne hy htL'
  have hzL' : z ∉ L' := fun h => hnc fun y hy => mul_comm_of_ne hL hL' hne hy h
  have hLle : L ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (htc x hx)
  have hJL : ∀ y ∈ J, ∀ x ∈ L, y * x = x * y := by
    rcases le_or_commutator_eq_bot_of_normal_component S.hp S.hq S.hΩ hJ ht hL hLn hLle with h | h
    · exact absurd (h ht.mem) htL
    · intro y hy x hx
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hy) x hx).symm
  have hL'le : L' ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (mul_comm_of_ne hL' hL hne.symm hx hzL)
  have hKL' : ∀ y ∈ K, ∀ x ∈ L', y * x = x * y := by
    rcases le_or_commutator_eq_bot_of_normal_component S.hp S.hq S.hΩ hK hz hL' hL'n hL'le with
      h | h
    · exact absurd (h hz.mem) hzL'
    · intro y hy x hx
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hy) x hx).symm
  have hKJ : K ≠ J := by
    intro h
    subst h
    exact htL (hz.eq ht ▸ hzL)
  have hJz : J ≤ Subgroup.centralizer ({z} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hJL y hy z hzL)
  have hKt : K ≤ Subgroup.centralizer ({t} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hKL' y hy t htL')
  have hJN : J ≤ Subgroup.normalizer (K : Set G) := by
    refine S.hΩ.le_of_forall_isSylow2In hJ fun V hV => ?_
    have h8 := S.hΩ.eight_le_of_mem_RSet S.hp (mem_RSet_of_isSylow2In hJ hV)
    exact S.hΩ.le_normalizer_of_le_centralizer S.hp S.hq hK hJ hKJ hz hV.1 hV.2.1 (by omega)
      (hV.1.trans hJz)
  have hKN : K ≤ Subgroup.normalizer (J : Set G) := by
    refine S.hΩ.le_of_forall_isSylow2In hK fun V hV => ?_
    have h8 := S.hΩ.eight_le_of_mem_RSet S.hp (mem_RSet_of_isSylow2In hK hV)
    exact S.hΩ.le_normalizer_of_le_centralizer S.hp S.hq hJ hK hKJ.symm ht hV.1 hV.2.1 (by omega)
      (hV.1.trans hKt)
  have hKJbot : K ⊓ J = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwK, hwJ⟩ := Subgroup.mem_inf.mp hw
    have hle : layer G ≤ Subgroup.centralizer ({w} : Set G) := by
      refine sSup_le fun M hM y hy => Subgroup.mem_centralizer_singleton_iff.mpr ?_
      by_cases hML : M = L
      · subst hML
        exact (hJL w hwJ y hy).symm
      · have hMn : M.Normal := S.component_normal hM
        have hMz : ∀ y ∈ M, y * z = z * y := fun y hy => mul_comm_of_ne hM hL hML hy hzL
        have hMle : M ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
          Subgroup.mem_centralizer_singleton_iff.mpr (hMz x hx)
        rcases le_or_commutator_eq_bot_of_normal_component S.hp S.hq S.hΩ hK hz hM hMn hMle with
          h | h
        · exact absurd (fun y hy => mul_comm_of_ne hL hM (Ne.symm hML) hy (h hz.mem)) hnc
        · exact Subgroup.mem_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hwK) y hy
    have hmem : w ∈ Subgroup.centralizer (layer G : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle he)
    rw [S.centralizer_layer, Subgroup.mem_bot] at hmem
    exact hmem
  intro x hx y hy
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ K ⊓ J := by
    constructor
    · have h2 : y * x⁻¹ * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hJN hy) x⁻¹).mp (K.inv_mem hx)
      have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [this]
      exact K.mul_mem hx h2
    · have h2 : x * y * x⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hKN hx) y).mp hy
      exact J.mul_mem h2 (J.inv_mem hy)
  rw [hKJbot, Subgroup.mem_bot] at h1
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

theorem simple_of_forall_mem {L : Subgroup G} (hL : IsComponent L)
    (hall : ∀ J ∈ Ω, ∀ t : G, IsUniqueInvolution J t → t ∈ L) :
    IsSimpleGroup ↥L ∧ Subgroup.centralizer (L : Set G) = ⊥ := by
  have hEL : layer G = L := by
    refine le_antisymm (sSup_le fun M hM => ?_) (component_le_layer hL)
    by_contra hML0
    have hML : M ≠ L := fun h => hML0 (h ▸ le_rfl)
    have hMn : M.Normal := S.component_normal hM
    have hJM : ∀ J ∈ Ω, J ≤ Subgroup.centralizer (M : Set G) := by
      intro J hJ
      obtain ⟨t, ht⟩ := S.hΩ.exists_uniqueInvolution S.hp S.hq hJ
      have htL : t ∈ L := hall J hJ t ht
      have hMle : M ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mpr (mul_comm_of_ne hM hL hML hx htL)
      rcases le_or_commutator_eq_bot_of_normal_component S.hp S.hq S.hΩ hJ ht hM hMn hMle with
        h | h
      · exfalso
        have htM : t ∈ M := h ht.mem
        exact ht.ne_one (S.eq_one_of_central_in_component hL htL fun w hw =>
          mul_comm_of_ne hL hM (Ne.symm hML) hw htM)
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer (M : Set G) := by
      rw [← S.hgen]
      exact iSup₂_le hJM
    have hM1 : M = ⊥ := by
      have hperf : ⁅M, M⁆ = M := Subgroup.isPerfect_iff.mp hM.1.1
      rw [← hperf, Subgroup.commutator_eq_bot_iff_le_centralizer.mpr]
      intro x hx
      exact htop (Subgroup.mem_top x)
    have : Nontrivial ↥M := isQuasisimple_nontrivial hM.1
    exact (Subgroup.nontrivial_iff_ne_bot M).mp this hM1
  have hC : Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [← hEL]
    exact S.centralizer_layer
  refine ⟨?_, hC⟩
  have hZ : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx1 : (x : G) = 1 := S.eq_one_of_central_in_component hL x.2 fun w hw =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨w, hw⟩)
    rw [Subgroup.mem_bot]
    exact Subtype.ext hx1
  have e : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
  exact e.symm.isSimpleGroup

theorem l17_3 {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) :
    ∃ L : Subgroup G, IsComponent L ∧ L.Normal ∧ z ∈ L ∧
      (∀ J ∈ Ω, ∀ t : G, IsUniqueInvolution J t → t ∉ L → Commutes K J) ∧
      (((∀ J ∈ Ω, ∃ g : G, conjSub g K = J) ∨
          ∀ J ∈ Ω, ∀ t : G, IsUniqueInvolution J t → t ∈ L) →
        IsSimpleGroup ↥L ∧ Subgroup.centralizer (L : Set G) = ⊥) := by
  obtain ⟨L, hL, hLn, hzL, hnc⟩ := S.exists_normal_component hK hz
  refine ⟨L, hL, hLn, hzL,
    fun J hJ t ht htL => S.commutes_of_not_mem hK hJ hz ht hL hzL hnc htL, ?_⟩
  rintro (htrans | hall)
  · refine S.simple_of_forall_mem hL fun J hJ t ht => ?_
    obtain ⟨g, rfl⟩ := htrans J hJ
    have h2 : t = g * z * g⁻¹ := ht.eq (hz.conj g)
    rw [h2]
    have := conj_mem_conjSub (n := g) hzL
    rwa [conjSub_eq_of_normal L g] at this
  · exact S.simple_of_forall_mem hL hall

end Hyp173

end AscThmA

open AscThmA in
theorem l17_3_of_thmA {p f : ℕ} [Fact p.Prime] (hA : LThmA p f) (h : L6_13 p f) : L17_3 p f := by
  intro hp hq G _ _ Ω hΩ hsolv hgen K hK z hz
  have S : Hyp173 p f Ω :=
    ⟨hp, hq, hΩ, comm613On_of_l6_13 h hp hq hΩ, fun J hJ L hL k hk =>
      hA hp hq G Ω hΩ J hJ L ((CFSG.isComponent_iff_open L).mp hL) k hk, hsolv, hgen⟩
  obtain ⟨L, hL, hLn, hzL, h2, h3⟩ := S.l17_3 hK hz
  exact ⟨L, (CFSG.isComponent_iff_open L).mp hL, hLn, hzL, h2, h3⟩

theorem l17_3_of_l6_13 {p f : ℕ} [Fact p.Prime] (h : L6_13 p f) : L17_3 p f :=
  l17_3_of_thmA (lThmA_of_l6_13 h) h

end CFSG.ClassicalInvolution.Asc77

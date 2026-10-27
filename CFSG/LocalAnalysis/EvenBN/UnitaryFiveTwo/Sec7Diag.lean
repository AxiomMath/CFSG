module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7Def
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSU42Sq
public import CFSG.LocalAnalysis.EvenBN.Common.Diagonal
public import CFSG.Adapters.LieModelSimple
public import CFSG.Adapters.LieModelOrders

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem Data.Hyp.isSimpleGroup_L (h : d.Hyp) : IsSimpleGroup d.L :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h.setting.model

theorem Data.Hyp.not_comm_L (h : d.Hyp) : ¬ ∀ x ∈ d.L, ∀ y ∈ d.L, x * y = y * x := by
  intro hc
  have hbot : ⁅d.L, d.L⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine commutator_le.2 fun x hx y hy => ?_
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hc x hx y hy
  have hS : d.S ≤ d.L := d.pull_le_L Ssub
  rw [(h.commutator_L).symm.trans hbot, le_bot_iff] at hS
  have h1 : Nat.card d.S = 1 := by rw [hS, Subgroup.card_bot]
  rw [d.card_S] at h1
  norm_num at h1

theorem Data.Hyp.even_card_L (h : d.Hyp) : Even (Nat.card d.L) := by
  have hdvd : Nat.card d.S ∣ Nat.card d.L := Subgroup.card_dvd_of_le (d.pull_le_L Ssub)
  rw [d.card_S] at hdvd
  exact even_iff_two_dvd.mpr ((dvd_pow_self 2 (by norm_num)).trans hdvd)

theorem t_conj_eq_of_comm {t g a : G} (hgt : t * g = g * t) :
    t * (g * a * g⁻¹) * t = g * (t * a * t) * g⁻¹ := by
  have hg' : g⁻¹ * t = t * g⁻¹ := (Commute.inv_left (show Commute g t from hgt.symm)).eq
  calc t * (g * a * g⁻¹) * t = (t * g) * a * (g⁻¹ * t) := by group
    _ = (g * t) * a * (t * g⁻¹) := by rw [hgt, hg']
    _ = g * (t * a * t) * g⁻¹ := by group

theorem Data.Hyp.mul_t_of_mem_L (h : d.Hyp) {l : G} (hl : l ∈ d.L) : l * d.t = d.t * l :=
  mem_centralizer_iff.mp h.t_mem l hl

theorem Data.Hyp.comm_inv (h : d.Hyp) {K₀ : Subgroup G}
    (hc : ⁅d.nclL K₀, (d.nclL K₀).map (MulAut.conj d.t).toMonoidHom⁆ = ⊥) :
    ⁅d.nclL K₀, (d.nclL K₀).map (MulAut.conj d.t⁻¹).toMonoidHom⁆ = ⊥ := by
  rw [h.t_inv]
  exact hc

section Nclosure

theorem map_conj_le_nclL {K₀ : Subgroup G} {l : G} (hl : l ∈ d.L) :
    K₀.map (MulAut.conj l).toMonoidHom ≤ d.nclL K₀ :=
  le_iSup₂ (f := fun l (_ : l ∈ d.L) => K₀.map (MulAut.conj l).toMonoidHom) l hl

theorem Data.mem_nclL_of_mem {K₀ : Subgroup G} {l x : G} (hl : l ∈ d.L) (hx : x ∈ K₀) :
    l * x * l⁻¹ ∈ d.nclL K₀ :=
  map_conj_le_nclL hl ⟨x, hx, rfl⟩

theorem Data.le_nclL (K₀ : Subgroup G) : K₀ ≤ d.nclL K₀ := fun x hx => by
  simpa using Data.mem_nclL_of_mem (K₀ := K₀) d.L.one_mem hx

theorem Data.nclL_le {K₀ M : Subgroup G}
    (hM : ∀ l ∈ d.L, K₀.map (MulAut.conj l).toMonoidHom ≤ M) : d.nclL K₀ ≤ M :=
  iSup₂_le fun l hl => hM l hl

theorem Data.nclL_perfect {K₀ : Subgroup G} (hK₀ : ⁅K₀, K₀⁆ = K₀) :
    ⁅d.nclL K₀, d.nclL K₀⁆ = d.nclL K₀ := by
  refine le_antisymm ((commutator_le_sup _ _).trans (le_of_eq (sup_idem _)))
    (Data.nclL_le fun l hl => ?_)
  have hmap : ⁅K₀.map (MulAut.conj l).toMonoidHom, K₀.map (MulAut.conj l).toMonoidHom⁆ =
      K₀.map (MulAut.conj l).toMonoidHom := by
    rw [← map_commutator, hK₀]
  calc K₀.map (MulAut.conj l).toMonoidHom
      = ⁅K₀.map (MulAut.conj l).toMonoidHom, K₀.map (MulAut.conj l).toMonoidHom⁆ := hmap.symm
    _ ≤ ⁅d.nclL K₀, d.nclL K₀⁆ := commutator_mono (map_conj_le_nclL hl) (map_conj_le_nclL hl)

theorem Data.conj_mem_nclL {K₀ : Subgroup G} {g x : G} (hg : g ∈ d.L) (hx : x ∈ d.nclL K₀) :
    g * x * g⁻¹ ∈ d.nclL K₀ := by
  have hM : d.nclL K₀ ≤ (d.nclL K₀).comap (MulAut.conj g).toMonoidHom := by
    refine Data.nclL_le fun l hl => ?_
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_comap]
    show g * (l * k * l⁻¹) * g⁻¹ ∈ d.nclL K₀
    rw [show g * (l * k * l⁻¹) * g⁻¹ = (g * l) * k * (g * l)⁻¹ by group]
    exact Data.mem_nclL_of_mem (mul_mem hg hl) hk
  exact hM hx

end Nclosure

theorem Data.IsUnitaryFactor.isSimpleGroup {K₀ : Subgroup G} (hK : d.IsUnitaryFactor K₀) :
    IsSimpleGroup K₀ :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hK.lieModel

theorem Data.IsUnitaryFactor.card_eq {K₀ : Subgroup G} (hK : d.IsUnitaryFactor K₀) :
    Nat.card K₀ = 25920 := by
  rw [hK.lieModel.card_eq_lieOrd (by norm_num)]
  decide

theorem Data.IsUnitaryFactor.not_comm {K₀ : Subgroup G} (hK : d.IsUnitaryFactor K₀) :
    ¬ ∀ x y : K₀, x * y = y * x := by
  intro hc
  haveI : IsMulCommutative K₀ := ⟨⟨hc⟩⟩
  have hp := Group.is_simple_iff_prime_card.mp hK.isSimpleGroup
  rw [hK.card_eq] at hp
  norm_num at hp

theorem Data.IsUnitaryFactor.commutator_eq {K₀ : Subgroup G} (hK : d.IsUnitaryFactor K₀) :
    ⁅K₀, K₀⁆ = K₀ := by
  haveI := hK.isSimpleGroup
  haveI : (commutator ↥K₀).Normal := by
    change (⁅(⊤ : Subgroup ↥K₀), (⊤ : Subgroup ↥K₀)⁆ : Subgroup ↥K₀).Normal
    infer_instance
  have hperf : Group.IsPerfect K₀ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥K₀) with hb | ht
    · exfalso
      apply hK.not_comm
      intro x y
      have hxy : ⁅x, y⁆ ∈ commutator ↥K₀ :=
        commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [hb, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hxy
      exact hxy
    · exact ⟨ht⟩
  exact (Common.isPerfect_subgroup_iff_commutator_eq K₀).mp hperf

theorem Data.IsUnitaryFactor.mul_conj_mem_L (h : d.Hyp) (hKU : d.KUnitary) {K₀ : Subgroup G}
    (hK : d.IsUnitaryFactor K₀) {k : G} (hk : k ∈ K₀) : k * (d.t * k * d.t⁻¹) ∈ d.L := by
  have hy : d.t * k * d.t⁻¹ ∈ K₀.map (MulAut.conj d.t).toMonoidHom := ⟨k, hk, rfl⟩
  have hkK : k ∈ d.K := by
    rw [hK.K_eq]
    exact mem_sup_left hk
  have hyK : d.t * k * d.t⁻¹ ∈ d.K := by
    rw [hK.K_eq]
    exact mem_sup_right hy
  have hcomm := Swap.comm_of_commutator_eq_bot hK.comm hk hk
  have hH : k * (d.t * k * d.t⁻¹) ∈ d.H := by
    show k * (d.t * k * d.t⁻¹) ∈ centralizer ({d.t} : Set G)
    rw [mem_centralizer_singleton_iff, h.t_inv]
    rw [h.t_inv] at hcomm
    calc k * (d.t * k * d.t) * d.t = k * d.t * k * (d.t * d.t) := by group
      _ = k * d.t * k := by rw [h.t_mul_t, mul_one]
      _ = d.t * (d.t * k * d.t) * k := by
          rw [show d.t * (d.t * k * d.t) * k = (d.t * d.t) * k * d.t * k by group, h.t_mul_t]
          group
      _ = d.t * (k * (d.t * k * d.t)) := by rw [hcomm]; group
  have hK3 : k * (d.t * k * d.t⁻¹) ∈ d.K₃ := by
    rw [← hKU.centralizer_eq]
    exact mem_inf.mpr ⟨mul_mem hkK hyK, hH⟩
  exact d.pull_le_L K₃sub hK3

theorem Data.mul_conj_mem_L_of_mem (h : d.Hyp) (hKU : d.KUnitary) {K₀ : Subgroup G}
    (hK : d.IsUnitaryFactor K₀) {l k : G} (hl : l ∈ d.L) (hk : k ∈ K₀) :
    (l * k * l⁻¹) * (d.t * (l * k * l⁻¹) * d.t) ∈ d.L := by
  have hkL : k * (d.t * k * d.t) ∈ d.L := by
    have := Data.IsUnitaryFactor.mul_conj_mem_L h hKU hK hk
    rwa [h.t_inv] at this
  rw [t_conj_eq_of_comm (h.mul_t_of_mem_L hl).symm]
  rw [show l * k * l⁻¹ * (l * (d.t * k * d.t) * l⁻¹) = l * (k * (d.t * k * d.t)) * l⁻¹ by group]
  exact mul_mem (mul_mem hl hkL) (inv_mem hl)

theorem Data.nclL_delta_mem_L (h : d.Hyp) (hKU : d.KUnitary) {K₀ : Subgroup G}
    (hK : d.IsUnitaryFactor K₀)
    (hc : ⁅d.nclL K₀, (d.nclL K₀).map (MulAut.conj d.t).toMonoidHom⁆ = ⊥) {x : G}
    (hx : x ∈ d.nclL K₀) : x * (d.t * x * d.t⁻¹) ∈ d.L := by
  have hAM : d.nclL K₀ ≤ (d.L.comap (Common.diagonalHom (d.nclL K₀) d.t (h.comm_inv hc))).map
      (d.nclL K₀).subtype := by
    refine Data.nclL_le fun l hl => ?_
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨⟨l * k * l⁻¹, Data.mem_nclL_of_mem hl hk⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Common.diagonalHom_apply, h.t_inv]
    exact Data.mul_conj_mem_L_of_mem h hKU hK hl hk
  obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp (hAM hx)
  rw [Subgroup.mem_comap, Common.diagonalHom_apply] at ha
  subst hax
  rw [h.t_inv] at ha
  rw [h.t_inv]
  exact ha

theorem Data.diagonalHom_mem_L (h : d.Hyp) (hKU : d.KUnitary) {K₀ : Subgroup G}
    (hK : d.IsUnitaryFactor K₀)
    (hc : ⁅d.nclL K₀, (d.nclL K₀).map (MulAut.conj d.t).toMonoidHom⁆ = ⊥)
    (a : d.nclL K₀) : Common.diagonalHom (d.nclL K₀) d.t (h.comm_inv hc) a ∈ d.L := by
  have h1 := Data.nclL_delta_mem_L h hKU hK hc a.2
  rw [Common.diagonalHom_apply, h.t_inv]
  rw [h.t_inv] at h1
  exact h1

theorem Data.diagonalHom_apply_of_mem {K₀ : Subgroup G} (h : d.Hyp)
    (hc : ⁅d.nclL K₀, (d.nclL K₀).map (MulAut.conj d.t).toMonoidHom⁆ = ⊥)
    (hK : d.IsUnitaryFactor K₀) {k : G} (hk : k ∈ K₀) :
    Common.diagonalHom (d.nclL K₀) d.t (h.comm_inv hc) ⟨k, Data.le_nclL K₀ hk⟩ =
      Swap.swapHom d.t K₀ hK.comm ⟨k, hk⟩ := by
  rw [Common.diagonalHom_apply, Swap.swapHom_apply, h.t_inv]

theorem Data.conj_mem_range (h : d.Hyp) (hKU : d.KUnitary) {K₀ : Subgroup G}
    (hK : d.IsUnitaryFactor K₀)
    (hc : ⁅d.nclL K₀, (d.nclL K₀).map (MulAut.conj d.t).toMonoidHom⁆ = ⊥) {g r : G}
    (hg : g ∈ d.L) (hr : r ∈ (Common.diagonalHom (d.nclL K₀) d.t (h.comm_inv hc)).range) :
    g * r * g⁻¹ ∈ (Common.diagonalHom (d.nclL K₀) d.t (h.comm_inv hc)).range := by
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hr
  refine MonoidHom.mem_range.mpr ⟨⟨g * a * g⁻¹, Data.conj_mem_nclL hg a.2⟩, ?_⟩
  rw [Common.diagonalHom_apply, Common.diagonalHom_apply, h.t_inv]
  show (g * a * g⁻¹) * (d.t * (g * a * g⁻¹) * d.t) = g * (a * (d.t * a * d.t)) * g⁻¹
  rw [t_conj_eq_of_comm (h.mul_t_of_mem_L hg).symm]
  group

theorem Data.nclL_range_delta (h : d.Hyp) (hKU : d.KUnitary) {K₀ : Subgroup G}
    (hK : d.IsUnitaryFactor K₀)
    (hc : ⁅d.nclL K₀, (d.nclL K₀).map (MulAut.conj d.t).toMonoidHom⁆ = ⊥) :
    (Common.diagonalHom (d.nclL K₀) d.t (h.comm_inv hc)).range = d.L := by
  haveI := h.isSimpleGroup_L
  haveI := hK.isSimpleGroup
  refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
    exact Data.diagonalHom_mem_L h hKU hK hc a
  · set δ := Common.diagonalHom (d.nclL K₀) d.t (h.comm_inv hc) with hδ
    set N : Subgroup d.L := δ.range.subgroupOf d.L with hN
    have hnorm : N.Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [hN, Subgroup.mem_subgroupOf] at hn
      rw [hN, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Data.conj_mem_range h hKU hK hc g.2 hn
    haveI := hnorm
    have hne : N ≠ ⊥ := by
      intro hb
      obtain ⟨k, hk1⟩ := exists_ne (1 : K₀)
      have hy0 : δ ⟨k, Data.le_nclL K₀ k.2⟩ ∈ d.L := Data.diagonalHom_mem_L h hKU hK hc _
      have hmem : (⟨δ ⟨k, Data.le_nclL K₀ k.2⟩, hy0⟩ : d.L) ∈ N := by
        rw [hN, Subgroup.mem_subgroupOf]
        exact MonoidHom.mem_range.mpr ⟨⟨k, Data.le_nclL K₀ k.2⟩, rfl⟩
      rw [hb, Subgroup.mem_bot] at hmem
      have h1 : δ ⟨k, Data.le_nclL K₀ k.2⟩ = 1 := congrArg Subtype.val hmem
      have h2 : Swap.swapHom d.t K₀ hK.comm ⟨k, k.2⟩ = 1 :=
        (Data.diagonalHom_apply_of_mem h hc hK k.2).symm.trans h1
      exact hk1 (Swap.swapHom_injective hK.comm hK.inf (h2.trans (map_one _).symm))
    have htop : N = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal N).resolve_left hne
    have hmem : (⟨y, hy⟩ : d.L) ∈ N := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [hN, Subgroup.mem_subgroupOf] at hmem
    exact hmem

theorem Data.nclL_delta_surj (h : d.Hyp) (hKU : d.KUnitary) {K₀ : Subgroup G}
    (hK : d.IsUnitaryFactor K₀)
    (hc : ⁅d.nclL K₀, (d.nclL K₀).map (MulAut.conj d.t).toMonoidHom⁆ = ⊥) :
    ∀ y ∈ d.L, ∃ x ∈ d.nclL K₀, x * (d.t * x * d.t⁻¹) = y := by
  intro y hy
  rw [← Data.nclL_range_delta h hKU hK hc] at hy
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hy
  refine ⟨(a : G), a.2, ?_⟩
  rw [← ha, Common.diagonalHom_apply, h.t_inv]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

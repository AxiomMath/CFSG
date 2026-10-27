module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalY
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalVTwoPrelim

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open CFSG.EvenSmallLie.UnitarySix.YamadaD (oTwo le_oTwo oTwo_le isPGroup_oTwo le_normalizer_oTwo)
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section LeviAct

variable {q : ℕ}

omit [Finite G] in
theorem conj_mem_L_of_mem_normalizer {E : Subgroup L} {x : G}
    (hx : x ∈ normalizer ((E.map L.subtype : Subgroup G) : Set G)) {l : L} (hl : l ∈ E) :
    x * (l : G) * x⁻¹ ∈ L :=
  map_subtype_le _ ((mem_normalizer_iff.1 hx _).1 ⟨l, hl, rfl⟩)

omit [Finite G] in
@[expose] noncomputable def conjN₀ (d : TrialityD4Data L q) (x : G)
    (hN : x ∈ normalizer (((d.D ⊔ d.leviShort).map L.subtype : Subgroup G) : Set G)) :
    (d.D ⊔ d.leviShort : Subgroup L) →* (d.D ⊔ d.leviShort : Subgroup L) where
  toFun n := ⟨⟨x * ((n : L) : G) * x⁻¹, conj_mem_L_of_mem_normalizer hN n.2⟩,
    coe_mem_map_subtype_iff_D4.1 ((mem_normalizer_iff.1 hN _).1 ⟨n, n.2, rfl⟩)⟩
  map_one' := Subtype.ext (Subtype.ext (by simp))
  map_mul' a b := Subtype.ext (Subtype.ext (by simp only [Subgroup.coe_mul]; group))

omit [Finite G] in
theorem conjN₀_le (d : TrialityD4Data L q) {x : G}
    (hN : x ∈ normalizer (((d.D ⊔ d.leviShort).map L.subtype : Subgroup G) : Set G))
    (hD : x ∈ normalizer ((d.D.map L.subtype : Subgroup G) : Set G)) :
    d.D.subgroupOf (d.D ⊔ d.leviShort) ≤
      (d.D.subgroupOf (d.D ⊔ d.leviShort)).comap (conjN₀ d x hN) := by
  intro n hn
  rw [mem_comap, mem_subgroupOf]
  rw [mem_subgroupOf] at hn
  exact coe_mem_map_subtype_iff_D4.1 ((mem_normalizer_iff.1 hD _).1 ⟨_, hn, rfl⟩)

omit [Finite G] in
@[expose] noncomputable def leviAct (d : TrialityD4Data L q) (x : G)
    (hN : x ∈ normalizer (((d.D ⊔ d.leviShort).map L.subtype : Subgroup G) : Set G))
    (hD : x ∈ normalizer ((d.D.map L.subtype : Subgroup G) : Set G)) :
    d.leviShort →* d.leviShort :=
  d.leviQuot.symm.toMonoidHom.comp ((QuotientGroup.map _ _ (conjN₀ d x hN)
    (conjN₀_le d hN hD)).comp d.leviQuot.toMonoidHom)

omit [Finite G] in
theorem leviAct_spec (d : TrialityD4Data L q) {x : G}
    (hN : x ∈ normalizer (((d.D ⊔ d.leviShort).map L.subtype : Subgroup G) : Set G))
    (hD : x ∈ normalizer ((d.D.map L.subtype : Subgroup G) : Set G)) (s : d.leviShort) :
    (((leviAct d x hN hD s : d.leviShort) : L) : G)⁻¹ * (x * ((s : L) : G) * x⁻¹) ∈
      d.D.map L.subtype := by
  have h1 : d.leviQuot (leviAct d x hN hD s) =
      QuotientGroup.map _ _ (conjN₀ d x hN) (conjN₀_le d hN hD) (d.leviQuot s) := by
    simp only [leviAct, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.apply_symm_apply]
  rw [TrialityD4Data.leviQuot_apply, TrialityD4Data.leviQuot_apply, QuotientGroup.map_mk,
    QuotientGroup.eq, mem_subgroupOf] at h1
  refine ⟨_, h1, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, coe_inclusion]
  rfl

omit [Finite G] in
theorem leviAct_eq_of_mem (d : TrialityD4Data L q) {x : G}
    (hN : x ∈ normalizer (((d.D ⊔ d.leviShort).map L.subtype : Subgroup G) : Set G))
    (hD : x ∈ normalizer ((d.D.map L.subtype : Subgroup G) : Set G)) (s s' : d.leviShort)
    (h : (((s' : L) : G))⁻¹ * (x * ((s : L) : G) * x⁻¹) ∈ d.D.map L.subtype) :
    leviAct d x hN hD s = s' := by
  have h1 := leviAct_spec d hN hD s
  have h2 : (((leviAct d x hN hD s : d.leviShort) : L) : G)⁻¹ * ((s' : L) : G) ∈
      d.D.map L.subtype := by
    have := mul_mem h1 (inv_mem h)
    rwa [show (((leviAct d x hN hD s : d.leviShort) : L) : G)⁻¹ * (x * ((s : L) : G) * x⁻¹) *
      ((((s' : L) : G))⁻¹ * (x * ((s : L) : G) * x⁻¹))⁻¹ =
        (((leviAct d x hN hD s : d.leviShort) : L) : G)⁻¹ * ((s' : L) : G) by group] at this
  obtain ⟨n, hn, hne⟩ := h2
  have h3 : n ∈ d.D ⊓ d.leviShort := by
    refine Subgroup.mem_inf.2 ⟨hn, ?_⟩
    have : n = ((leviAct d x hN hD s : d.leviShort) : L)⁻¹ * (s' : L) :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_inv]; exact hne)
    rw [this]
    exact mul_mem (inv_mem (leviAct d x hN hD s).2) s'.2
  rw [d.D_inf_leviShort, mem_bot] at h3
  have h4 : ((leviAct d x hN hD s : d.leviShort) : L)⁻¹ * (s' : L) = 1 := by
    rw [← h3]
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_inv]; exact hne.symm)
  exact Subtype.ext (inv_mul_eq_one.1 h4)

omit [Finite G] in
theorem leviAct_injective (d : TrialityD4Data L q) {x : G}
    (hN : x ∈ normalizer (((d.D ⊔ d.leviShort).map L.subtype : Subgroup G) : Set G))
    (hD : x ∈ normalizer ((d.D.map L.subtype : Subgroup G) : Set G)) :
    Function.Injective (leviAct d x hN hD) := by
  refine (injective_iff_map_eq_one _).2 fun s hs => ?_
  have h1 := leviAct_spec d hN hD s
  rw [hs] at h1
  simp only [OneMemClass.coe_one, inv_one, one_mul] at h1
  have h2 : ((s : L) : G) ∈ d.D.map L.subtype := by
    have := (mem_normalizer_iff.1 (inv_mem hD) _).1 h1
    rwa [show x⁻¹ * (x * ((s : L) : G) * x⁻¹) * x⁻¹⁻¹ = ((s : L) : G) by group] at this
  have h3 : (s : L) ∈ d.D ⊓ d.leviShort :=
    Subgroup.mem_inf.2 ⟨coe_mem_map_subtype_iff_D4.1 h2, s.2⟩
  rw [d.D_inf_leviShort, mem_bot] at h3
  exact Subtype.ext h3

end LeviAct

section Two

variable {q : ℕ}

omit [Finite G] in
theorem units_Γ₀_eq_one_of_two (d : TrialityD4Data L q) (hq : q = 2) (l : (d.Γ₀)ˣ) : l = 1 := by
  have h1 : Nat.card (d.Γ₀)ˣ = 1 := by rw [d.card_units_Γ₀, hq]
  have : Subsingleton (d.Γ₀)ˣ := (Nat.card_eq_one_iff_unique.1 h1).1
  exact Subsingleton.elim _ _

omit [Finite G] in
theorem eq_one_of_mem_J₁_of_two (d : TrialityD4Data L q) (hq : q = 2) {j : L}
    (hj : j ∈ d.J₁) : j = 1 := by
  obtain ⟨⟨l, m⟩, rfl, hm⟩ := d.mem_J₁.1 hj
  dsimp only at hm
  subst hm
  rw [units_Γ₀_eq_one_of_two d hq l]
  exact map_one d.torus

omit [Finite G] in
theorem J_le_centralizer_Y_of_two (d : TrialityD4Data L q) (hq : q = 2) :
    d.J ≤ centralizer (d.Y : Set L) := by
  rintro _ ⟨⟨l, m⟩, rfl⟩
  have hl := units_Γ₀_eq_one_of_two d hq l
  have hm : ((d.nmUnits m : (d.Γ₀)ˣ) : d.Γ₀) = 1 := by
    rw [units_Γ₀_eq_one_of_two d hq (d.nmUnits m)]
    rfl
  subst hl
  have h5 : ∀ a, d.torus (1, m) * d.x₅ a * (d.torus (1, m))⁻¹ = d.x₅ a := fun a => by
    rw [d.torus_x₅]
    congr 1
    change ((1 : (d.Γ₀)ˣ) : d.Γ₀) * ((d.nmUnits m : (d.Γ₀)ˣ) : d.Γ₀) * a = a
    rw [hm, Units.val_one, one_mul, one_mul]
  have h6 : ∀ a, d.torus (1, m) * d.x₆ a * (d.torus (1, m))⁻¹ = d.x₆ a := fun a => by
    rw [d.torus_x₆]
    congr 1
    change ((1 : (d.Γ₀)ˣ) : d.Γ₀) * ((1 : (d.Γ₀)ˣ) : d.Γ₀) *
      ((d.nmUnits m : (d.Γ₀)ˣ) : d.Γ₀) * a = a
    rw [hm, Units.val_one, one_mul, one_mul, one_mul]
  rw [mem_centralizer_iff]
  intro y hy
  have hy' : y ∈ Set.range d.yv := by rw [d.range_yv]; exact hy
  obtain ⟨w, rfl⟩ := hy'
  have e : d.torus (1, m) * d.yv w * (d.torus (1, m))⁻¹ = d.yv w := by
    simp only [TrialityD4Data.yv]
    rw [show d.torus (1, m) * (d.x₅ (w 0) * d.x₆ (w 1)) * (d.torus (1, m))⁻¹ =
      (d.torus (1, m) * d.x₅ (w 0) * (d.torus (1, m))⁻¹) *
        (d.torus (1, m) * d.x₆ (w 1) * (d.torus (1, m))⁻¹) by group, h5, h6]
  calc d.yv w * d.torus (1, m) = d.torus (1, m) * d.yv w * (d.torus (1, m))⁻¹ *
        d.torus (1, m) := by rw [e]
    _ = d.torus (1, m) * d.yv w := by group

theorem commutator_mem_tD_of_two (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hq : 2 ^ f = 2) {e : G}
    (he : e ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G))
    (htriv : ∀ y : L, y ∈ d.leviShort → e * (y : G) * e⁻¹ * (y : G)⁻¹ ∈ d.D.map L.subtype) :
    ∀ k ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ((d.V.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G),
      e * k * e⁻¹ * k⁻¹ ∈ d.D.map L.subtype ⊔ zpowers t := by
  have hNH := h.normalizer_tV_le_normalizer_N₀ d
  have hDH := h.normalizer_tV_le_normalizer_D d
  have hK : ∀ g ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G),
      ∀ y ∈ (d.D ⊔ d.leviShort).map L.subtype, g * y * g⁻¹ ∈ (d.D ⊔ d.leviShort).map L.subtype :=
    fun g hg y hy => (mem_normalizer_iff.1 (hNH hg) y).1 hy
  have hB : ∀ g ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G),
      ∀ b ∈ d.D.map L.subtype, g * b * g⁻¹ ∈ d.D.map L.subtype :=
    fun g hg b hb => (mem_normalizer_iff.1 (hDH hg) b).1 hb
  set E := Common.centralizerMod _ _ _ hK hB with hE
  have heE : e ∈ E := by
    refine ⟨he, fun y hy => ?_⟩
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    obtain ⟨n, hn, s, hs, rfl⟩ := d.exists_mul_of_mem_D_sup_leviShort hy₀
    have h1 := hB e he _ ⟨n, hn, rfl⟩
    have h2 := htriv s hs
    have h3 : (n : G)⁻¹ ∈ d.D.map L.subtype := ⟨n⁻¹, inv_mem hn, rfl⟩
    rw [show e * L.subtype (n * s) * e⁻¹ * (L.subtype (n * s))⁻¹ =
      (e * L.subtype n * e⁻¹) * (e * (s : G) * e⁻¹ * (s : G)⁻¹) * (n : G)⁻¹ by
        simp only [map_mul, Subgroup.coe_subtype]; group]
    exact mul_mem (mul_mem h1 h2) h3
  intro k hk
  have hwE : e * k * e⁻¹ * k⁻¹ ∈ E := by
    rw [show e * k * e⁻¹ * k⁻¹ = e * (k * e⁻¹ * k⁻¹) by group]
    exact mul_mem heE (Common.conj_mem_centralizerMod hk.1.1 (inv_mem heE))
  have hwK : e * k * e⁻¹ * k⁻¹ ∈
      normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ((d.V.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G) :=
    mul_mem ((h.cosetData_tV d).conj_mem_kernel he hk) (inv_mem hk)
  obtain ⟨hwC, hwV⟩ := h.kernel_V_le d hwK
  have hV : ∀ y ∈ d.V, h.act ⟨_, hwC⟩ y ∈ d.V := fun y hy => by
    rw [← h.conj_mem_map_iff hwC]
    exact (mem_normalizer_iff.1 hwV _).1 ⟨y, hy, rfl⟩
  have hα : ∀ y ∈ d.leviShort, h.act ⟨_, hwC⟩ y * y⁻¹ ∈ d.D := by
    intro y hy
    have h1 := hwE.2 _ ⟨y, mem_sup_right hy, rfl⟩
    rw [show (e * k * e⁻¹ * k⁻¹) * L.subtype y * (e * k * e⁻¹ * k⁻¹)⁻¹ * (L.subtype y)⁻¹ =
      ((h.act ⟨_, hwC⟩ y * y⁻¹ : L) : G) by
        rw [Subgroup.coe_mul, h.coe_act_apply, Subgroup.coe_inv]; rfl] at h1
    exact coe_mem_map_subtype_iff_D4.1 h1
  obtain ⟨n, hn, j, hj, hnj⟩ := d.eq_conj_of_trivial_mod_D hV hα
  rw [eq_one_of_mem_J₁_of_two d hq hj, mul_one] at hnj
  obtain ⟨c, hc, hwc⟩ := h.exists_mul_zpowers_of_act_eq_conj d hwC hnj
  rw [hwc]
  exact mul_mem (mem_sup_left ⟨n, hn, rfl⟩) (mem_sup_right hc)

theorem two_core_C₁_two (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hq : 2 ^ f = 2) :
    CoreC₁ d t := by
  obtain ⟨hL₂Y, hL₂C, hL₂tr, -⟩ := h.two_core_L₂ d
  have hVY : d.V.map L.subtype ≤ d.Y.map L.subtype := map_mono d.V_le_Y
  have hz : ((d.x₆ 1 : L) : G) ∈ d.V.map L.subtype := ⟨_, d.x₆_mem_V 1, rfl⟩
  obtain ⟨x, hxL₂, hxt⟩ := hL₂tr _ (hVY hz)
  have hxHY := yamadaL₂_le d t hxL₂
  have hxV : x ∈ centralizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
    Subgroup.centralizer_le hVY (hL₂Y hxL₂)
  have hzx : x * ((d.x₆ 1 : L) : G) * x⁻¹ = (d.x₆ 1 : L) := by
    rw [← mem_centralizer_iff.1 hxV _ hz, mul_inv_cancel_right]
  have hxt' : x * t * x⁻¹ = t * ((d.x₆ 1 : L) : G) := by
    have e1 : t = x * (t * ((d.x₆ 1 : L) : G)) * x⁻¹ := by rw [← hxt]; group
    have hz2 : ((d.x₆ 1 : L) : G) * ((d.x₆ 1 : L) : G) = 1 := by
      rw [← Subgroup.coe_mul, d.x₆_mul_self]; rfl
    calc x * t * x⁻¹ = x * t * x⁻¹ * (((d.x₆ 1 : L) : G) * ((d.x₆ 1 : L) : G)) := by
          rw [hz2, mul_one]
      _ = (x * (t * ((d.x₆ 1 : L) : G)) * x⁻¹) * ((d.x₆ 1 : L) : G) := by
          rw [show x * (t * ((d.x₆ 1 : L) : G)) * x⁻¹ = x * t * x⁻¹ *
            (x * ((d.x₆ 1 : L) : G) * x⁻¹) by group, hzx]
          group
      _ = t * ((d.x₆ 1 : L) : G) := by rw [← e1]
  have hxH : x ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) := by
    have hxtV : x * t * x⁻¹ ∈ d.V.map L.subtype ⊔ zpowers t := by
      rw [hxt']
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hz)
    refine mem_normalizer_fintype (conj_mem_sup (fun v hv => mem_sup_left ?_) fun n hn => ?_)
    · rw [← mem_centralizer_iff.1 hxV v hv, mul_inv_cancel_right]
      exact hv
    · obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
      rw [show x * t ^ k * x⁻¹ = (x * t * x⁻¹) ^ k by
        rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]]
      exact zpow_mem hxtV k
  have hN := h.normalizer_tV_le_normalizer_N₀ d hxH
  have hD := h.normalizer_tV_le_normalizer_D d hxH
  have hcommM : ∀ y : L, y ∈ d.D ⊔ d.leviShort → y ∈ centralizer (d.Y : Set L) →
      x * (y : G) * x⁻¹ * (y : G)⁻¹ ∈ d.M.map L.subtype := by
    intro y hyN hyY
    have hyC : (y : G) ∈ centralizer ({t} : Set G) := h.L_le_centralizer y.2
    have hyYg : (y : G) ∈ centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.1 hyY w hw)
    have hyK : (y : G) ∈ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G) :=
      ⟨⟨h.centralizer_inf_normalizer_Y_le d ⟨hyC, Subgroup.centralizer_le_normalizer _ hyYg⟩,
        hyYg⟩, hyC⟩
    have h1 : x * (y : G) * x⁻¹ * (y : G)⁻¹ ∈ yamadaL₂ d t := by
      rw [show x * (y : G) * x⁻¹ * (y : G)⁻¹ = x * ((y : G) * x⁻¹ * (y : G)⁻¹) by group]
      exact mul_mem hxL₂ ((mem_normalizer_iff.1 (le_normalizer_yamadaL₂ d t hyK.1.1) _).1
        (inv_mem hxL₂))
    have h2 : x * (y : G) * x⁻¹ * (y : G)⁻¹ ∈ centralizer ({t} : Set G) :=
      (mul_mem ((h.cosetData_tY d).conj_mem_kernel hxHY hyK) (inv_mem hyK)).2
    have h3 : x * (y : G) * x⁻¹ * (y : G)⁻¹ ∈ d.M.map L.subtype ⊔ zpowers t := by
      rw [← hL₂C]
      exact ⟨h1, h2⟩
    have h4 : x * (y : G) * x⁻¹ * (y : G)⁻¹ ∈ L :=
      mul_mem (conj_mem_L_of_mem_normalizer hN hyN) (inv_mem y.2)
    rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 h3 with h5 | h5
    · exact h5
    · exfalso
      refine h.t_not_mem_L ?_
      have := mul_mem (map_subtype_le _ h5) (inv_mem h4)
      rwa [mul_inv_cancel_right] at this
  have hconj : ∀ y : L, y ∈ d.D ⊔ d.leviShort → y ∈ centralizer (d.Y : Set L) →
      ∃ c : d.Γ, ∃ n ∈ d.F, x * (y : G) * x⁻¹ = ((d.x₁ c * n * y : L) : G) := by
    intro y hyN hyY
    obtain ⟨m, hm, hme⟩ := hcommM y hyN hyY
    obtain ⟨c, n, hn, rfl⟩ := d.mem_M_iff.1 hm
    refine ⟨c, n, hn, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    simp only [Subgroup.coe_subtype] at hme
    rw [← Subgroup.coe_mul, hme]
    group
  have hJY : d.J ≤ centralizer (d.Y : Set L) := J_le_centralizer_Y_of_two d hq
  set α := leviAct d x hN hD with hαdef
  have hU : ∀ a : d.Γ, ((α ⟨d.x₁ a, d.x₁_mem_leviShort a⟩ : d.leviShort) : L) ∈ d.U₁ := by
    intro a
    obtain ⟨c, n, hn, hcn⟩ := hconj (d.x₁ a) (mem_sup_right (d.x₁_mem_leviShort a))
      (d.M_le_centralizer_Y (d.U₁_le_M (d.x₁_mem_U₁ a)))
    have h1 := leviAct_eq_of_mem d hN hD ⟨d.x₁ a, d.x₁_mem_leviShort a⟩
      ⟨d.x₁ (c + a), d.x₁_mem_leviShort _⟩ (by
        change ((d.x₁ (c + a) : L) : G)⁻¹ * (x * ((d.x₁ a : L) : G) * x⁻¹) ∈ _
        rw [hcn, ← Subgroup.coe_inv, ← Subgroup.coe_mul]
        refine ⟨(d.x₁ (c + a))⁻¹ * (d.x₁ c * n * d.x₁ a), ?_, rfl⟩
        rw [d.x₁_add, show (d.x₁ c * d.x₁ a)⁻¹ * (d.x₁ c * n * d.x₁ a) =
          (d.x₁ a)⁻¹ * n * d.x₁ a by group]
        have := (mem_normalizer_iff.1 (d.leviShort_le_normalizer_D
          (inv_mem (d.x₁_mem_leviShort a))) n).1 (d.F_le_D hn)
        rwa [inv_inv] at this)
    rw [h1]
    exact d.x₁_mem_U₁ _
  have hJ : ∀ j (hj : j ∈ d.J₆),
      ((α ⟨j, d.J₆_le_leviShort hj⟩ : d.leviShort) : L) * j⁻¹ ∈ d.U₁ := by
    intro j hj
    obtain ⟨c, n, hn, hcn⟩ := hconj j (mem_sup_right (d.J₆_le_leviShort hj)) (hJY hj.1)
    have h1 := leviAct_eq_of_mem d hN hD ⟨j, d.J₆_le_leviShort hj⟩
      ⟨d.x₁ c * j, mul_mem (d.x₁_mem_leviShort c) (d.J₆_le_leviShort hj)⟩ (by
        change ((d.x₁ c * j : L) : G)⁻¹ * (x * ((j : L) : G) * x⁻¹) ∈ _
        rw [hcn, ← Subgroup.coe_inv, ← Subgroup.coe_mul]
        refine ⟨(d.x₁ c * j)⁻¹ * (d.x₁ c * n * j), ?_, rfl⟩
        rw [show (d.x₁ c * j)⁻¹ * (d.x₁ c * n * j) = j⁻¹ * n * j by group]
        have := (mem_normalizer_iff.1 (d.J_le_normalizer_D (inv_mem hj.1)) n).1 (d.F_le_D hn)
        rwa [inv_inv] at this)
    rw [h1]
    change d.x₁ c * j * j⁻¹ ∈ d.U₁
    rw [mul_inv_cancel_right]
    exact d.x₁_mem_U₁ c
  obtain ⟨s, hs, hsα⟩ := d.exists_conj_eq_of_trivial_on_borel α (leviAct_injective d hN hD) hU hJ
  set e := (s : G) * x with hedef
  have hsH : (s : G) ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
    (h.N₀_le_kernel_V d ⟨s, mem_sup_right hs, rfl⟩).1.1
  have heH : e ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
    mul_mem hsH hxH
  have heV : e ∈ centralizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
    mul_mem (h.N₀_le_kernel_V d ⟨s, mem_sup_right hs, rfl⟩).1.2 hxV
  have htriv : ∀ y : L, y ∈ d.leviShort → e * (y : G) * e⁻¹ * (y : G)⁻¹ ∈ d.D.map L.subtype := by
    intro y hy
    obtain ⟨n, hn, hne⟩ := leviAct_spec d hN hD ⟨y, hy⟩
    rw [← hαdef] at hne
    have h1 := hsα (y : L) hy
    have h2 : x * ((y : L) : G) * x⁻¹ = (((α ⟨y, hy⟩ : d.leviShort) : L) : G) * (n : G) := by
      simp only [Subgroup.coe_subtype] at hne
      rw [hne]
      group
    have h3 : (s : L) * n * (s : L)⁻¹ ∈ d.D :=
      (mem_normalizer_iff.1 (d.leviShort_le_normalizer_D hs) n).1 hn
    have h4 : y * ((s : L) * n * (s : L)⁻¹) * y⁻¹ ∈ d.D :=
      (mem_normalizer_iff.1 (d.leviShort_le_normalizer_D hy) _).1 h3
    refine ⟨_, h4, ?_⟩
    rw [hedef, show (s : G) * x * (y : G) * ((s : G) * x)⁻¹ * (y : G)⁻¹ =
      (s : G) * (x * (y : G) * x⁻¹) * (s : G)⁻¹ * (y : G)⁻¹ by group, h2]
    have h5 : (((s : L) * ((α ⟨y, hy⟩ : d.leviShort) : L) * (s : L)⁻¹ : L) : G) = (y : G) :=
      congrArg Subtype.val h1
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at h5 ⊢
    rw [show (s : G) * ((((α ⟨y, hy⟩ : d.leviShort) : L) : G) * (n : G)) * (s : G)⁻¹ *
      (y : G)⁻¹ = ((s : G) * (((α ⟨y, hy⟩ : d.leviShort) : L) : G) * (s : G)⁻¹) *
        ((s : G) * (n : G) * (s : G)⁻¹) * (y : G)⁻¹ by group, h5]
  have het : e⁻¹ * t * e = t * ((d.x₆ 1 : L) : G) := by
    have hst : (s : G) * t = t * (s : G) := mem_centralizer_iff.1 h.htL _ (s : L).2
    rw [hedef, show ((s : G) * x)⁻¹ * t * ((s : G) * x) = x⁻¹ * ((s : G)⁻¹ * (t * (s : G))) * x
      by group, ← hst, inv_mul_cancel_left, hxt]
  have hc := h.cosetData_tV d
  have hmax : ∀ R : Subgroup G,
      R ≤ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) →
      normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) ≤ normalizer (R : Set G) → IsPGroup 2 R →
          R ≤ d.D.map L.subtype ⊔ zpowers t := by
    intro R hR hN' hp
    rw [h.normalizer_tV_inf_centralizer d] at hR hN'
    exact h.le_tD_of_isPGroup d hR hN' hp
  have hQtr : ∀ y ∈ d.V.map L.subtype, ∃ q' ∈
      normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ((d.V.map L.subtype : Subgroup G) : Set G),
      (∀ k ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ((d.V.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G),
          q' * k * q'⁻¹ * k⁻¹ ∈ d.D.map L.subtype ⊔ zpowers t) ∧ q'⁻¹ * t * q' = t * y := by
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    by_cases ha : a = 0
    · refine ⟨1, one_mem _, fun k _ => ?_, ?_⟩
      · rw [one_mul, inv_one, mul_one, mul_inv_cancel]
        exact one_mem _
      · rw [ha, d.x₆_zero]
        simp
    · have ha1 : a = 1 := by
        have := units_Γ₀_eq_one_of_two d hq (Units.mk0 a ha)
        rw [← Units.val_mk0 ha, this, Units.val_one]
      subst ha1
      exact ⟨e, ⟨heH, heV⟩, h.commutator_mem_tD_of_two d hq heH htriv, het⟩
  obtain ⟨h1, -, h3, h4, h5⟩ := hc.two_core (h.isPGroup_tD d) (h.tD_le_kernel_V d)
    (h.normalizer_tV_le_normalizer_tD d) hmax hQtr
  rw [CoreC₁, yamadaC₁, pCoreOf_two_eq_oTwo_D4]
  refine ⟨h1, h3, h4, fun g hg => ?_⟩
  obtain ⟨c, hc', x', hx', rfl⟩ := h5 g hg
  rw [h.normalizer_tV_inf_centralizer d] at hc'
  exact ⟨c, hc', x', hx', rfl⟩

theorem two_core_C₁_all (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) : CoreC₁ d t := by
  rcases Nat.lt_or_ge f 2 with hf | hf
  · have hf1 : f = 1 := by have := h.one_le; omega
    exact h.two_core_C₁_two d (by rw [hf1]; rfl)
  · exact h.two_core_C₁ d (by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)

end Two

section All

theorem yamada_5_3_1_all (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) =
        yamadaC₁ d t ⊔ (centralizer ({t} : Set G) ⊓
          normalizer ((d.V.map L.subtype : Subgroup G) : Set G)) ∧
      ((normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) : Subgroup G) :
          Set G) = (yamadaC₁ d t : Set G) * ((centralizer ({t} : Set G) ⊓
            normalizer ((d.V.map L.subtype : Subgroup G) : Set G) : Subgroup G) : Set G) ∧
      normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ≤
        normalizer ((d.D.map L.subtype : Subgroup G) : Set G) ∧
      yamadaC₁ d t ⊓ centralizer ({t} : Set G) = d.D.map L.subtype ⊔ zpowers t ∧
      {x | ∃ c ∈ yamadaC₁ d t, c * t * c⁻¹ = x} =
        (fun v => t * v) '' ((d.V.map L.subtype : Subgroup G) : Set G) ∧
      yamadaC₁ d t ≤ centralizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
  h.yamada_5_3_1_of_core d (h.two_core_C₁_all d)

theorem yamada_5_3_1_module_all (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    ∃ _ : ((d.D.map L.subtype ⊔ zpowers t).subgroupOf (yamadaC₁ d t)).Normal,
      ∃ φ : yamadaC₁ d t ⧸ (d.D.map L.subtype ⊔ zpowers t).subgroupOf (yamadaC₁ d t) ≃*
          (d.V.map L.subtype : Subgroup G),
        (∀ x : yamadaC₁ d t, (φ (QuotientGroup.mk x) : G) = t * (x : G)⁻¹ * t * x) ∧
        ∀ c ∈ centralizer ({t} : Set G) ⊓ normalizer ((d.V.map L.subtype : Subgroup G) : Set G),
          ∀ x : yamadaC₁ d t, ∃ hx : c * x * c⁻¹ ∈ yamadaC₁ d t,
            (φ (QuotientGroup.mk ⟨c * x * c⁻¹, hx⟩) : G) = c * φ (QuotientGroup.mk x) * c⁻¹ :=
  h.yamada_5_3_1_module_of_core d (h.two_core_C₁_all d)

theorem yamada_5_3_3_all (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    normalizer (yamadaR d t : Set G) = yamadaC₁ d t ⊔
        (centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G)) ∧
      ((normalizer (yamadaR d t : Set G) : Subgroup G) : Set G) =
        (yamadaC₁ d t : Set G) * ((centralizer ({t} : Set G) ⊓
          normalizer ((d.S.map L.subtype : Subgroup G) : Set G) : Subgroup G) : Set G) ∧
      normalizer (yamadaR d t : Set G) ≤ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) :=
  h.yamada_5_3_3_of_core d (h.two_core_C₁_all d)

end All

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4

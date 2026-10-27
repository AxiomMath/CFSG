module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL3Five

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open scoped commutatorElement Pointwise

section Hyps

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

structure L6Hyps {f : ℕ} (d : TrialityD4Data L (2 ^ f)) (t : G) : Prop where
  hNH : NormalizerHyp d t
  h561 : yamadaC₁ d t = yamadaD₁ d t ⊔ zpowers t ∧ t ∉ yamadaD₁ d t ∧
    (normalizer (d.V : Set L)).map L.subtype ≤ normalizer (yamadaD₁ d t : Set G)
  h562 : IsElemAbelian 2 (yamadaV₁ d t) ∧ Nat.card (yamadaV₁ d t) = (2 ^ f) ^ 2 ∧
    yamadaV₁ d t ⊓ centralizer ({t} : Set G) = d.V.map L.subtype ∧ yamadaV₁ d t ≤ yamadaF₁ d t
  h591 : yamadaL₂ d t = yamadaM₂ d t ⊔ zpowers t ∧ t ∉ yamadaM₂ d t ∧
    yamadaR₂ d t = yamadaS₂ d t ⊔ zpowers t ∧ t ∉ yamadaS₂ d t
  h592 : yamadaV₁ d t ⊓ (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom = ⊥ ∧
    Nat.card (yamadaY₂ d t) = (2 ^ f) ^ 4 ∧ IsMulCommutative (yamadaY₂ d t) ∧
    yamadaM₂ d t ⊓ centralizer (yamadaM₂ d t : Set G) = yamadaY₂ d t ∧
    yamadaY₂ d t ⊓ centralizer ({t} : Set G) = d.Y.map L.subtype
  h593 : (Subgroup.upperCentralSeries (yamadaS₂ d t) 1).map (yamadaS₂ d t).subtype =
      yamadaV₁ d t ∧
    (Subgroup.upperCentralSeries (yamadaS₂ d t) 2).map (yamadaS₂ d t).subtype = yamadaY₂ d t
  h5101 : (Subgroup.upperCentralSeries (yamadaR₂ d t) 1).map (yamadaR₂ d t).subtype =
      d.V.map L.subtype ∧
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 2).map (yamadaR₂ d t).subtype = yamadaY₁ d t ∧
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 3).map (yamadaR₂ d t).subtype =
      yamadaW₂ d t ⊔ zpowers t ∧
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 4).map (yamadaR₂ d t).subtype =
      yamadaF₂ d t ⊔ zpowers t
  h5102 : CFSG.Open.thompsonSubgroup (yamadaF₂ d t ⊔ zpowers t) = yamadaF₂ d t
  h59e : yamadaY₂ d t = jZeroLayer d ⊓ yamadaL₂ d t
  h520 : yamadaC₅ d t = yamadaD₅ d t ⊔ zpowers t ∧ t ∉ yamadaD₅ d t ∧
    yamadaD₅ d t = yamadaD₃ d t ⊔ (yamadaD₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom ∧
    yamadaD₃ d t ⊓ (yamadaD₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom =
      yamadaD₁ d t ∧
    yamadaL₃ d t = yamadaM₃ d t ⊔ zpowers t ∧ t ∉ yamadaM₃ d t ∧
    yamadaR₃ d t = yamadaS₃ d t ⊔ zpowers t ∧ t ∉ yamadaS₃ d t
  h5221 : ((yamadaF₃ d t ⊔ zpowers t).subgroupOf (yamadaR₃ d t)).Characteristic ∧
    ((yamadaL₃ d t).subgroupOf (yamadaR₃ d t)).Characteristic ∧
    ⁅yamadaR₃ d t, yamadaR₃ d t⁆ = yamadaF₂ d t
  h521 : yamadaW₃ d t =
      yamadaF₃ d t ⊓ (yamadaF₃ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom ∧
    IsElemAbelian 2 (yamadaW₃ d t) ∧ Nat.card (yamadaW₃ d t) = (2 ^ f) ^ 10

end Hyps

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

theorem l6Hyps (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    L6Hyps d t :=
  ⟨h.normalizerHyp_of_layerHyp d hlay, h.yamada_5_6_1 d hlay, h.yamada_5_6_2 d hlay,
    h.yamada_5_9_1 d hlay, h.yamada_5_9_2 d hlay, h.yamada_5_9_3 d hlay,
    h.yamada_5_10_1 d hlay, h.yamada_5_10_2 d hlay, h.yamadaY₂_eq d hlay, h.yamada_5_20 d hlay,
    h.yamada_5_22_1 d hlay, h.yamada_5_21 d hlay⟩

section Normalizers

theorem coe_v_mul_self {q : ℕ} (d : TrialityD4Data L q) :
    ((d.v : L) : G) * ((d.v : L) : G) = 1 := by
  rw [← Subgroup.coe_mul, d.v_mul_self, OneMemClass.coe_one]

theorem normalizer_yamadaL₃_le_normalizer_yamadaW₂ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    normalizer (yamadaL₃ d t : Set G) ≤ normalizer (yamadaW₂ d t : Set G) := fun g hg => by
  have := mem_normalizer_commutator_D4 hg
  rwa [h.yamada_5_18 d hlay] at this

theorem normalizer_yamadaL₃_le_normalizer_yamadaW₃ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    normalizer (yamadaL₃ d t : Set G) ≤ normalizer (yamadaW₃ d t : Set G) := fun g hg =>
  mem_normalizer_inf_D4 hg (mem_normalizer_centralizer_D4
    (h.normalizer_yamadaL₃_le_normalizer_yamadaW₂ d hlay hg))

theorem yamadaW₂_le_yamadaW₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaW₂ d t ≤ yamadaW₃ d t := by
  rw [← h.yamadaM₂_inf_yamadaW₃ d hlay]
  exact inf_le_right

theorem yamadaL₃_le_normalizer_yamadaY₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaL₃ d t ≤ normalizer (yamadaY₂ d t : Set G) := fun g hg => by
  have hy := h.l6Hyps d hlay
  exact h.normalizer_yamadaV₂_le_normalizer_yamadaY₂ d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592
    hy.h593 hy.h5101 hy.h5102 (h.yamadaL₃_le_normalizer_yamadaV₂ d hy.hNH hy.h561 hy.h562 hy.h591
      hy.h592 hy.h593 hy.h5101 hy.h5102 hg)

theorem yamadaL₃_le_normalizer_yamadaM₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaL₃ d t ≤ normalizer (yamadaM₃ d t : Set G) := fun g hg =>
  mem_normalizer_inf_D4 (le_normalizer hg)
    (mem_normalizer_centralizer_D4 (h.yamadaL₃_le_normalizer_yamadaY₂ d hlay hg))

theorem centralizer_inf_normalizer_Y_le_normalizer_yamadaY₂_L6 (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaY₂ d t : Set G) := by
  have hy := h.l6Hyps d hlay
  exact h.centralizer_inf_normalizer_Y_le_normalizer_yamadaY₂ d hy.h592 hy.h5101 hy.h5102

theorem centralizer_inf_normalizer_Y_le_normalizer_yamadaM₃ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaM₃ d t : Set G) := fun g hg =>
  mem_normalizer_inf_D4 (h.centralizer_inf_normalizer_Y_le_normalizer_yamadaL₃ d hg)
    (mem_normalizer_centralizer_D4
      (h.centralizer_inf_normalizer_Y_le_normalizer_yamadaY₂_L6 d hlay hg))

theorem yamadaR₄_le_normalizer_yamadaL₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaR₄ d t ≤ normalizer (yamadaL₃ d t : Set G) := by
  have hy := h.l6Hyps d hlay
  have hchar := hy.h5221.2.1
  intro g hg
  have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    ((yamadaL₃ d t).subgroupOf (yamadaR₃ d t))
    ((h.yamada_5_14 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593).2.2.2.2.1.2 hg)
  rwa [Subgroup.map_subgroupOf_eq_of_le (h.yamadaL₃_le_yamadaR₃_D3 d hlay)] at h1

theorem yamadaR₄_le_normalizer_yamadaY₂_L6 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaR₄ d t ≤ normalizer (yamadaY₂ d t : Set G) := by
  have hy := h.l6Hyps d hlay
  exact h.yamadaR₄_le_normalizer_yamadaY₂ d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593
    hy.h5221

theorem yamadaR₄_le_normalizer_yamadaM₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaR₄ d t ≤ normalizer (yamadaM₃ d t : Set G) := fun g hg =>
  mem_normalizer_inf_D4 (h.yamadaR₄_le_normalizer_yamadaL₃ d hlay hg)
    (mem_normalizer_centralizer_D4 (h.yamadaR₄_le_normalizer_yamadaY₂_L6 d hlay hg))

theorem v_mem_centralizer_inf_normalizer_Y (h : Setup G L f t) {q : ℕ}
    (d : TrialityD4Data L q) :
    ((d.v : L) : G) ∈ centralizer ({t} : Set G) ⊓
      normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) :=
  ⟨h.L_le_centralizer d.v.2, coe_mem_normalizer_map (d.leviLong_le_normalizer_Y d.v_mem_leviLong)⟩

theorem v_mem_normalizer_yamadaM₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : ((d.v : L) : G) ∈ normalizer (yamadaM₃ d t : Set G) :=
  h.centralizer_inf_normalizer_Y_le_normalizer_yamadaM₃ d hlay
    (h.v_mem_centralizer_inf_normalizer_Y d)

theorem exists_conj_t_eq_mul_of_mem (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {g : G}
    (hg : g ∈ normalizer (yamadaL₃ d t : Set G) ⊓ normalizer (yamadaM₃ d t : Set G)) :
    ∃ m ∈ yamadaM₃ d t, g * t * g⁻¹ = t * m := by
  have htL₃ : t ∈ yamadaL₃ d t := by
    rw [h.yamadaL₃_eq_sup d hlay]
    exact mem_sup_right (mem_zpowers t)
  have htM₃ : t ∈ normalizer (yamadaM₃ d t : Set G) :=
    mem_normalizer_inf_D4 (le_normalizer htL₃)
      (mem_normalizer_centralizer_D4 (h.t_mem_normalizer_yamadaY₂_D1 d))
  have hgt : g * t * g⁻¹ ∈ yamadaL₃ d t := (mem_normalizer_iff.1 hg.1 t).1 htL₃
  rw [h.yamadaL₃_eq_sup d hlay, h.mem_sup_zpowers_iff_of_normalizer htM₃] at hgt
  rcases hgt with hgt | hgt
  · exfalso
    apply h.t_not_mem_yamadaM₃ d hlay
    have := (mem_normalizer_iff.1 (inv_mem hg.2) _).1 hgt
    rwa [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
  · refine ⟨t * (g * t * g⁻¹), hgt, ?_⟩
    rw [← mul_assoc, h.t_mul_t, one_mul]

end Normalizers

section MThree

theorem yamadaF₂_le_yamadaF₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaF₂ d t ≤ yamadaF₃ d t := by
  have hF₂M₂ : yamadaF₂ d t ≤ yamadaM₂ d t := sup_le_sup_right (map_mono d.F_le_M) _
  refine le_inf (hF₂M₂.trans (h.yamadaM₂_le_yamadaM₃ d hlay)) (le_inf (le_inf
    (h.yamadaF₂_le_yamadaR₃ d hlay) fun x hx => centralizer_le (yamadaV₁_le_yamadaY₂ d)
      (h.yamadaF₂_le_centralizer_yamadaY₂ d hlay hx)) ?_)
  exact le_sup_left.trans ((h.yamadaL₂_inf_yamadaC₅ d hlay).symm.le.trans inf_le_right)

theorem F_map_le_yamadaF₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : d.F.map L.subtype ≤ yamadaF₃ d t :=
  (le_sup_left : d.F.map L.subtype ≤ yamadaF₂ d t).trans (h.yamadaF₂_le_yamadaF₃ d hlay)

theorem yamadaY₂_le_yamadaF₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaY₂ d t ≤ yamadaF₃ d t :=
  (le_sup_right : yamadaY₂ d t ≤ yamadaF₂ d t).trans (h.yamadaF₂_le_yamadaF₃ d hlay)

theorem map_conj_yamadaF₃_le_yamadaM₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    (yamadaF₃ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom ≤ yamadaM₃ d t := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_normalizer_iff.1 (h.v_mem_normalizer_yamadaM₃ d hlay) x).1 (mem_inf.1 hx).1

theorem yamadaM₃_le_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaM₃ d t ≤ yamadaF₃ d t ⊔ (yamadaF₃ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom := by
  rw [← h.yamadaM₂_sup_yamadaW₃ d hlay]
  refine sup_le (sup_le ?_ ?_) ?_
  · rintro _ ⟨m, hm, rfl⟩
    obtain ⟨a, n, hn, rfl⟩ := d.mem_M_iff.1 hm
    have hx : ((d.x₁ a : L) : G) ∈
        (yamadaF₃ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom := by
      rw [mem_map_conj_iff_D4]
      have e : ((d.v : L) : G)⁻¹ * ((d.x₁ a : L) : G) * ((d.v : L) : G) = ((d.x₃ a : L) : G) := by
        have := congrArg Subtype.val (show d.v⁻¹ * d.x₁ a * d.v = d.x₃ a by
          rw [d.v_inv, d.v_x₁])
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
      rw [e]
      exact h.F_map_le_yamadaF₃ d hlay ⟨d.x₃ a, d.x₃_mem_F a, rfl⟩
    rw [map_mul]
    exact mul_mem (mem_sup_right hx) (mem_sup_left (h.F_map_le_yamadaF₃ d hlay ⟨n, hn, rfl⟩))
  · exact (h.yamadaY₂_le_yamadaF₃ d hlay).trans le_sup_left
  · exact (h.yamadaW₃_le_yamadaF₃ d hlay).trans le_sup_left

theorem yamadaM₃_eq_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaM₃ d t = yamadaF₃ d t ⊔ (yamadaF₃ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom :=
  le_antisymm (h.yamadaM₃_le_sup d hlay) (sup_le inf_le_left
    (h.map_conj_yamadaF₃_le_yamadaM₃ d hlay))

theorem yamadaM₃_le_normalizer_yamadaF₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaM₃ d t ≤ normalizer (yamadaF₃ d t : Set G) := fun m hm =>
  mem_normalizer_fintype fun a ha => by
    have h1 : m * a * m⁻¹ * a⁻¹ ∈ ⁅yamadaL₃ d t, yamadaL₃ d t⁆ := by
      rw [← commutatorElement_def]
      exact commutator_mem_commutator (mem_inf.1 hm).1 (mem_inf.1 (mem_inf.1 ha).1).1
    rw [h.yamada_5_18 d hlay] at h1
    have := mul_mem (h.yamadaW₃_le_yamadaF₃ d hlay (h.yamadaW₂_le_yamadaW₃ d hlay h1)) ha
    rwa [inv_mul_cancel_right] at this

theorem coe_yamadaM₃_eq_mul (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    ((yamadaM₃ d t : Subgroup G) : Set G) = (yamadaF₃ d t : Set G) *
      (((yamadaF₃ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom : Subgroup G) : Set G) := by
  rw [h.yamadaM₃_eq_sup d hlay]
  exact coe_mul_of_right_le_normalizer_left _ _ fun x hx =>
    h.yamadaM₃_le_normalizer_yamadaF₃ d hlay (h.map_conj_yamadaF₃_le_yamadaM₃ d hlay hx)

theorem commutator_mem_Y_of_mem_yamadaM₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {m w : G} (hm : m ∈ yamadaM₃ d t) (hw : w ∈ yamadaW₂ d t) :
    m * w * m⁻¹ * w⁻¹ ∈ d.Y.map L.subtype := by
  have hy := h.l6Hyps d hlay
  have hYY₂ : d.Y.map L.subtype ≤ yamadaY₂ d t := Y_le_yamadaY₂ d hy.h592
  have hY₂W₂ : yamadaY₂ d t ≤ yamadaW₂ d t := le_sup_right
  have hK : ∀ g ∈ normalizer (yamadaW₂ d t : Set G) ⊓ centralizer (yamadaY₂ d t : Set G),
      ∀ y ∈ yamadaW₂ d t, g * y * g⁻¹ ∈ yamadaW₂ d t := fun g hg y hy' =>
    (mem_normalizer_iff.1 hg.1 y).1 hy'
  have hB : ∀ g ∈ normalizer (yamadaW₂ d t : Set G) ⊓ centralizer (yamadaY₂ d t : Set G),
      ∀ b ∈ d.Y.map L.subtype, g * b * g⁻¹ ∈ d.Y.map L.subtype := fun g hg b hb => by
    rw [← mem_centralizer_iff.1 hg.2 b (hYY₂ hb), mul_inv_cancel_right]
    exact hb
  obtain ⟨Z, hZ⟩ : ∃ Z : Subgroup G, ∀ x, x ∈ Z ↔
      (x ∈ normalizer (yamadaW₂ d t : Set G) ⊓ centralizer (yamadaY₂ d t : Set G) ∧
        ∀ w ∈ yamadaW₂ d t, x * w * x⁻¹ * w⁻¹ ∈ d.Y.map L.subtype) :=
    ⟨Common.centralizerMod (normalizer (yamadaW₂ d t : Set G) ⊓ centralizer (yamadaY₂ d t : Set G))
      (yamadaW₂ d t) (d.Y.map L.subtype) hK hB, fun x => Iff.rfl⟩
  have hM₃Z : yamadaM₃ d t ≤ Z := by
    rw [← h.yamadaM₂_sup_yamadaW₃ d hlay]
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨m₀, hm₀, rfl⟩
      have hm₀S : L.subtype m₀ ∈ d.S.map L.subtype := ⟨m₀, d.M_le_S hm₀, rfl⟩
      refine (hZ _).2 ⟨⟨?_, ?_⟩, fun w hw => ?_⟩
      · exact (h.S_map_le_normalizer_yamadaW₃ d hlay hm₀S).1
      · exact mem_centralizer_iff.2 fun y hy' =>
          (commute_of_mem_M_of_mem_yamadaY₂ d hy.h592 ⟨m₀, hm₀, rfl⟩ hy').symm
      · have hw' : w ∈ ((d.W.map L.subtype ⊔ yamadaY₂ d t : Subgroup G) : Set G) := hw
        rw [coe_mul_of_right_le_normalizer_left _ _ (yamadaY₂_le_normalizer_W d hy.h592),
          Set.mem_mul] at hw'
        obtain ⟨_, ⟨a, ha, rfl⟩, y', hy', rfl⟩ := hw'
        have hmy : L.subtype m₀ * y' = y' * L.subtype m₀ :=
          commute_of_mem_M_of_mem_yamadaY₂ d hy.h592 ⟨m₀, hm₀, rfl⟩ hy'
        have hmy' : L.subtype m₀ * y' * (L.subtype m₀)⁻¹ = y' := by
          rw [hmy, mul_inv_cancel_right]
        have e : L.subtype m₀ * (L.subtype a * y') * (L.subtype m₀)⁻¹ * (L.subtype a * y')⁻¹ =
            L.subtype (m₀ * a * m₀⁻¹ * a⁻¹) := by
          rw [show L.subtype m₀ * (L.subtype a * y') * (L.subtype m₀)⁻¹ *
            (L.subtype a * y')⁻¹ = (L.subtype m₀ * L.subtype a * (L.subtype m₀)⁻¹) *
              (L.subtype m₀ * y' * (L.subtype m₀)⁻¹) * y'⁻¹ * (L.subtype a)⁻¹ by group, hmy']
          simp only [map_mul, map_inv]
          group
        rw [e]
        exact ⟨_, d.commutatorElement_mem_Y_of_mem_M hm₀ ha, rfl⟩
    · intro y hy'
      have hyW₂ : y ∈ yamadaW₂ d t := hY₂W₂ hy'
      refine (hZ y).2 ⟨⟨le_normalizer hyW₂, mem_centralizer_iff.2 fun y' hy'' =>
        yamadaY₂_mul_comm d hy.h592 hy'' hy'⟩, fun w hw => ?_⟩
      rw [yamadaW₂_mul_comm d hy.h592 hyW₂ hw, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    · intro z hz
      refine (hZ z).2 ⟨⟨?_, centralizer_le hY₂W₂ (mem_inf.1 hz).2⟩, fun w hw => ?_⟩
      · exact h.normalizer_yamadaL₃_le_normalizer_yamadaW₂ d hlay (le_normalizer (mem_inf.1 hz).1)
      · rw [← mem_centralizer_iff.1 (mem_inf.1 hz).2 w hw, mul_inv_cancel_right, mul_inv_cancel]
        exact one_mem _
  exact ((hZ m).1 (hM₃Z hm)).2 w hw

end MThree

end Setup

section TDef

variable {q : ℕ}

@[expose] noncomputable def yamadaT₆ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  Common.centralizerMod (normalizer (yamadaL₃ d t : Set G) ⊓ normalizer (yamadaM₃ d t : Set G) ⊓
      normalizer (yamadaW₂ d t : Set G) ⊓ normalizer (yamadaY₂ d t : Set G))
    (yamadaW₂ d t) (yamadaY₂ d t)
    (fun _ hg y hy => (mem_normalizer_iff.1 (mem_inf.1 (mem_inf.1 hg).1).2 y).1 hy)
    (fun _ hg y hy => (mem_normalizer_iff.1 (mem_inf.1 hg).2 y).1 hy) ⊓
    centralizer ((d.Y.map L.subtype : Subgroup G) : Set G)

theorem mem_normalizer_of_mem_yamadaT₆ {d : TrialityD4Data L q} {g : G}
    (hg : g ∈ yamadaT₆ d t) : g ∈ normalizer (yamadaL₃ d t : Set G) ⊓
      normalizer (yamadaM₃ d t : Set G) ⊓ normalizer (yamadaW₂ d t : Set G) ⊓
        normalizer (yamadaY₂ d t : Set G) :=
  (Common.mem_centralizerMod.1 (mem_inf.1 hg).1).1

theorem yamadaT₆_le_normalizer_yamadaL₃ (d : TrialityD4Data L q) (t : G) :
    yamadaT₆ d t ≤ normalizer (yamadaL₃ d t : Set G) := fun _ hg =>
  (mem_normalizer_of_mem_yamadaT₆ hg).1.1.1

theorem yamadaT₆_le_normalizer_yamadaM₃ (d : TrialityD4Data L q) (t : G) :
    yamadaT₆ d t ≤ normalizer (yamadaM₃ d t : Set G) := fun _ hg =>
  (mem_normalizer_of_mem_yamadaT₆ hg).1.1.2

theorem yamadaT₆_le_normalizer_yamadaW₂ (d : TrialityD4Data L q) (t : G) :
    yamadaT₆ d t ≤ normalizer (yamadaW₂ d t : Set G) := fun _ hg =>
  (mem_normalizer_of_mem_yamadaT₆ hg).1.2

theorem yamadaT₆_le_centralizer_Y (d : TrialityD4Data L q) (t : G) :
    yamadaT₆ d t ≤ centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) := fun _ hg =>
  (mem_inf.1 hg).2

theorem commutator_mem_yamadaY₂_of_mem_yamadaT₆ {d : TrialityD4Data L q} {g w : G}
    (hg : g ∈ yamadaT₆ d t) (hw : w ∈ yamadaW₂ d t) : g * w * g⁻¹ * w⁻¹ ∈ yamadaY₂ d t :=
  (Common.mem_centralizerMod.1 (mem_inf.1 hg).1).2 w hw

theorem mem_yamadaT₆_of {d : TrialityD4Data L q} {g : G}
    (hL₃ : g ∈ normalizer (yamadaL₃ d t : Set G)) (hM₃ : g ∈ normalizer (yamadaM₃ d t : Set G))
    (hW₂ : g ∈ normalizer (yamadaW₂ d t : Set G)) (hY₂ : g ∈ normalizer (yamadaY₂ d t : Set G))
    (hc : ∀ w ∈ yamadaW₂ d t, g * w * g⁻¹ * w⁻¹ ∈ yamadaY₂ d t)
    (hY : g ∈ centralizer ((d.Y.map L.subtype : Subgroup G) : Set G)) : g ∈ yamadaT₆ d t :=
  ⟨Common.mem_centralizerMod.2 ⟨⟨⟨⟨hL₃, hM₃⟩, hW₂⟩, hY₂⟩, hc⟩, hY⟩

end TDef

namespace Setup

section T

theorem conj_mem_yamadaT₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {c z : G}
    (hc : c ∈ centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G))
    (hz : z ∈ yamadaT₆ d t) : c * z * c⁻¹ ∈ yamadaT₆ d t := by
  have hcL₃ := h.centralizer_inf_normalizer_Y_le_normalizer_yamadaL₃ d hc
  have hcM₃ := h.centralizer_inf_normalizer_Y_le_normalizer_yamadaM₃ d hlay hc
  have hcY₂ := h.centralizer_inf_normalizer_Y_le_normalizer_yamadaY₂_L6 d hlay hc
  have hcW₂ := h.normalizer_yamadaL₃_le_normalizer_yamadaW₂ d hlay hcL₃
  have hcN : c ∈ normalizer (yamadaL₃ d t : Set G) ⊓ normalizer (yamadaM₃ d t : Set G) ⊓
      normalizer (yamadaW₂ d t : Set G) ⊓ normalizer (yamadaY₂ d t : Set G) :=
    ⟨⟨⟨hcL₃, hcM₃⟩, hcW₂⟩, hcY₂⟩
  refine ⟨Common.conj_mem_centralizerMod hcN (mem_inf.1 hz).1, ?_⟩
  refine mem_centralizer_iff.2 fun y hy => ?_
  have hy' : c⁻¹ * y * c ∈ d.Y.map L.subtype := by
    have := (mem_normalizer_iff.1 (inv_mem hc.2) y).1 hy
    rwa [inv_inv] at this
  have h1 := mem_centralizer_iff.1 (mem_inf.1 hz).2 _ hy'
  calc y * (c * z * c⁻¹) = c * ((c⁻¹ * y * c) * z) * c⁻¹ := by group
    _ = c * (z * (c⁻¹ * y * c)) * c⁻¹ := by rw [h1]
    _ = c * z * c⁻¹ * y := by group

theorem v_conj_mem_yamadaT₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {z : G} (hz : z ∈ yamadaT₆ d t) :
    ((d.v : L) : G) * z * ((d.v : L) : G)⁻¹ ∈ yamadaT₆ d t :=
  h.conj_mem_yamadaT₆ d hlay (h.v_mem_centralizer_inf_normalizer_Y d) hz

theorem yamadaL₃_le_yamadaT₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaL₃ d t ≤ yamadaT₆ d t := fun g hg => by
  have hy := h.l6Hyps d hlay
  have hgP : g ∈ translationsW₂ d t :=
    (h.yamadaL₃_eq_translationsW₂ d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101
      hy.h5102) ▸ hg
  have hgE := ((h.mem_translationsW₂_iff d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101
    hy.h5102).1 hgP).1
  exact mem_yamadaT₆_of (le_normalizer hg) (h.yamadaL₃_le_normalizer_yamadaM₃ d hlay hg)
    (h.normalizer_yamadaL₃_le_normalizer_yamadaW₂ d hlay (le_normalizer hg))
    (h.yamadaL₃_le_normalizer_yamadaY₂ d hlay hg)
    (((h.mem_centralizerW₂Y₂_iff d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101
      hy.h5102).1 hgE).2)
    (h.yamadaL₃_le_centralizer_Y d hy.h592 hy.h520 hg)

theorem commutator_mem_yamadaW₃_of_mem_yamadaT₆ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {g m : G} (hg : g ∈ yamadaT₆ d t)
    (hm : m ∈ yamadaM₃ d t) : g * m * g⁻¹ * m⁻¹ ∈ yamadaW₃ d t := by
  have hy := h.l6Hyps d hlay
  have hgL₃ : g ∈ normalizer (yamadaL₃ d t : Set G) := yamadaT₆_le_normalizer_yamadaL₃ d t hg
  have hgW₂ : g ∈ normalizer (yamadaW₂ d t : Set G) := yamadaT₆_le_normalizer_yamadaW₂ d t hg
  have hgY : g ∈ centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) :=
    yamadaT₆_le_centralizer_Y d t hg
  have hmL₃ : m ∈ yamadaL₃ d t := (mem_inf.1 hm).1
  have hmW₂ : m ∈ normalizer (yamadaW₂ d t : Set G) :=
    h.normalizer_yamadaL₃_le_normalizer_yamadaW₂ d hlay (le_normalizer hmL₃)
  have hmY₂ : m ∈ centralizer (yamadaY₂ d t : Set G) := (mem_inf.1 hm).2
  have hYY₂ : d.Y.map L.subtype ≤ yamadaY₂ d t := Y_le_yamadaY₂ d hy.h592
  have key : ∀ w ∈ yamadaW₂ d t, g * m * w * m⁻¹ * g⁻¹ = m * g * w * g⁻¹ * m⁻¹ := by
    intro w hw
    have he := h.commutator_mem_Y_of_mem_yamadaM₃ d hlay hm hw
    have hf := commutator_mem_yamadaY₂_of_mem_yamadaT₆ hg hw
    obtain ⟨e, he_def⟩ : ∃ e, e = m * w * m⁻¹ * w⁻¹ := ⟨_, rfl⟩
    obtain ⟨f', hf_def⟩ : ∃ f', f' = g * w * g⁻¹ * w⁻¹ := ⟨_, rfl⟩
    rw [← he_def] at he
    rw [← hf_def] at hf
    have h1 : m * w * m⁻¹ = e * w := by rw [he_def]; group
    have h2 : g * w * g⁻¹ = f' * w := by rw [hf_def]; group
    have h3 : g * e * g⁻¹ = e := by
      rw [← mem_centralizer_iff.1 hgY e he, mul_inv_cancel_right]
    have h4 : m * f' * m⁻¹ = f' := by
      rw [← mem_centralizer_iff.1 hmY₂ f' hf, mul_inv_cancel_right]
    have h5 : e * f' = f' * e := yamadaY₂_mul_comm d hy.h592 (hYY₂ he) hf
    calc g * m * w * m⁻¹ * g⁻¹ = g * (m * w * m⁻¹) * g⁻¹ := by group
      _ = g * (e * w) * g⁻¹ := by rw [h1]
      _ = (g * e * g⁻¹) * (g * w * g⁻¹) := by group
      _ = e * (f' * w) := by rw [h3, h2]
      _ = f' * (e * w) := by rw [← mul_assoc, h5, mul_assoc]
      _ = (m * f' * m⁻¹) * (m * w * m⁻¹) := by rw [h4, h1]
      _ = m * (f' * w) * m⁻¹ := by group
      _ = m * (g * w * g⁻¹) * m⁻¹ := by rw [h2]
      _ = m * g * w * g⁻¹ * m⁻¹ := by group
  refine mem_inf.2 ⟨mul_mem ((mem_normalizer_iff.1 hgL₃ m).1 hmL₃) (inv_mem hmL₃),
    mem_centralizer_iff.2 fun w hw => ?_⟩
  have hw₂ : m⁻¹ * w * m ∈ yamadaW₂ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hmW₂) w).1 hw
    rwa [inv_inv] at this
  have hw₃ : g⁻¹ * (m⁻¹ * w * m) * g ∈ yamadaW₂ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hgW₂) _).1 hw₂
    rwa [inv_inv] at this
  have hcw : (g * m * g⁻¹ * m⁻¹) * w * (g * m * g⁻¹ * m⁻¹)⁻¹ = w := by
    calc (g * m * g⁻¹ * m⁻¹) * w * (g * m * g⁻¹ * m⁻¹)⁻¹ =
          g * m * (g⁻¹ * (m⁻¹ * w * m) * g) * m⁻¹ * g⁻¹ := by group
      _ = m * g * (g⁻¹ * (m⁻¹ * w * m) * g) * g⁻¹ * m⁻¹ := key _ hw₃
      _ = w := by group
  exact (mul_inv_eq_iff_eq_mul.1 hcw).symm

end T

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4

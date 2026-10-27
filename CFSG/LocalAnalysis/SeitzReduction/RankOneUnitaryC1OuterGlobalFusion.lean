module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterMuOneCore
public import CFSG.RankThree.PartOne.K1214.Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem muOneCent_exists_conj_of_mem_W (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {w : G} (hwT : w ∈ T)
    (hw2 : w ^ 2 = 1) (hwS : w ∉ szT₁ L T ⊔ zpowers t) {W : Subgroup G}
    (hWcard : Nat.card W = (2 ^ f) ^ 2)
    (hWiff : ∀ y ∈ szT₁ L T, (y⁻¹ * (w * y * w⁻¹) ∈ szA₁ (szT₁ L T) ↔ y ∈ W)) {y : G}
    (hy : y ∈ W) : ∃ c ∈ szT₁ L T, c * w * c⁻¹ = y * w := by
  classical
  obtain ⟨hT₁card, hA₁card, -, hsqT, -, -, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨-, -, hCw, -⟩ := h.outer_facts_of_card_sylow hS2 hwT hw2 hwS
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  have hww : w * w = 1 := by rw [← sq, hw2]
  have hA₁T₁ : szA₁ (szT₁ L T) ≤ szT₁ L T := szA₁_le _
  have hδW : ∀ c ∈ szT₁ L T, c * w * c⁻¹ * w⁻¹ ∈ W := by
    intro c hc
    have hwc : w * c * w⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp (hTN₁ hwT) c).mp hc
    have hwc' : w * c⁻¹ * w⁻¹ ∈ szT₁ L T :=
      (mem_normalizer_iff.mp (hTN₁ hwT) c⁻¹).mp (inv_mem hc)
    have hδ : c * w * c⁻¹ * w⁻¹ ∈ szT₁ L T := by
      rw [show c * w * c⁻¹ * w⁻¹ = c * (w * c⁻¹ * w⁻¹) by group]
      exact mul_mem hc hwc'
    refine (hWiff _ hδ).mp ?_
    have e : (c * w * c⁻¹ * w⁻¹)⁻¹ * (w * (c * w * c⁻¹ * w⁻¹) * w⁻¹) =
        (w * c * w⁻¹ * c⁻¹) * (w * c * w⁻¹ * (w * w) * c⁻¹ * (w * w)⁻¹) := by group
    rw [e, hww, inv_one, mul_one, mul_one, ← sq]
    exact hsqT _ (mul_mem hwc (inv_mem hc))
  set A₁' := (szA₁ (szT₁ L T)).subgroupOf (szT₁ L T) with hA₁'def
  let φ : (szT₁ L T ⧸ A₁') → W := fun q =>
    ⟨((Quotient.out q : szT₁ L T) : G) * w * ((Quotient.out q : szT₁ L T) : G)⁻¹ * w⁻¹,
      hδW _ (Quotient.out q).2⟩
  have hφinj : Function.Injective φ := by
    intro q q' hqq'
    have e := congrArg Subtype.val hqq'
    simp only [φ] at e
    set a : szT₁ L T := Quotient.out q with ha
    set b : szT₁ L T := Quotient.out q' with hb
    have e' : (a : G) * w * (a : G)⁻¹ = (b : G) * w * (b : G)⁻¹ := mul_right_cancel e
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, ← ha, ← hb,
      mem_subgroupOf]
    have hab : ((a⁻¹ * b : szT₁ L T) : G) = (a : G)⁻¹ * (b : G) := by simp
    rw [hab]
    refine hCw _ (mul_mem (inv_mem a.2) b.2) ?_
    calc w * ((a : G)⁻¹ * (b : G)) = (a : G)⁻¹ * ((a : G) * w * (a : G)⁻¹) * (b : G) := by group
      _ = (a : G)⁻¹ * ((b : G) * w * (b : G)⁻¹) * (b : G) := by rw [e']
      _ = (a : G)⁻¹ * (b : G) * w := by group
  have hcardA' : Nat.card A₁' = 2 ^ f := by
    rw [← hA₁card]
    exact Nat.card_congr (subgroupOfEquivOfLe hA₁T₁).toEquiv
  have hidx := A₁'.card_mul_index
  rw [hcardA', hT₁card, Subgroup.index_eq_card] at hidx
  have hQcard : Nat.card (szT₁ L T ⧸ A₁') = Nat.card W := by
    rw [hWcard]
    have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
    apply Nat.eq_of_mul_eq_mul_left hq0
    rw [hidx]
    ring
  obtain ⟨q, hq⟩ := ((Nat.bijective_iff_injective_and_card φ).mpr ⟨hφinj, hQcard⟩).2 ⟨y, hy⟩
  have e := congrArg Subtype.val hq
  simp only [φ] at e
  refine ⟨((Quotient.out q : szT₁ L T) : G), (Quotient.out q).2, ?_⟩
  rw [← e]
  group

end U3Start

namespace U3C1OuterLevelData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G}

section Facts

variable (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1)
  (hL : U3C1OuterLevelData G L f t T D V U U₁ 1)
include hS hL

theorem muOneCent_conj_T₁_mem {u : G} (hu : u ∈ U) {y : G} (hy : y ∈ szT₁ L T) :
    u * y * u⁻¹ ∈ szT₁ L T := by
  rw [show u * y * u⁻¹ = y * (y⁻¹ * (u * y * u⁻¹)) by group]
  exact mul_mem hy (szA₁_le _ (hL.conj_T₁ u hu y hy))

theorem muOneCent_mem_V_of_comm_t_mem_szA₁ {z : G} (hz : z ∈ outerV₁ L T U₁)
    (hσ : z * t * z⁻¹ * t⁻¹ ∈ szA₁ (szT₁ L T)) : z ∈ V := by
  obtain ⟨hzU, hzC⟩ := mem_outerV₁.mp hz
  have hzTV := hL.muOne_mem_sup_of_comm_t_mem_szA₁ hS hzU hσ
  obtain ⟨y₁, hy₁, r, hr, hyr⟩ := ncyc_exists_mul_of_mem_sup (hL.muOne_T₁_le_normalizer hS) hzTV
  have hy₁A : y₁ ∈ szA₁ (szT₁ L T) := by
    refine mem_szA₁.mpr ⟨hy₁, mem_centralizer_iff.mpr fun y₀ hy₀ => ?_⟩
    have hz₀ := mem_centralizer_iff.mp hzC y₀ hy₀
    have hr₀ := hL.muOne_T₁_comm hS hy₀ hr
    rw [show y₁ = z * r⁻¹ by rw [← hyr]; group]
    calc y₀ * (z * r⁻¹) = (y₀ * z) * r⁻¹ := by group
      _ = z * y₀ * r⁻¹ := by rw [hz₀]
      _ = z * (y₀ * r⁻¹) := by group
      _ = z * (r⁻¹ * y₀) := by rw [(Commute.inv_right hr₀).eq]
      _ = z * r⁻¹ * y₀ := by group
  rw [← hyr]
  exact mul_mem (hS.conf.le hy₁A) hr

theorem muOneCent_conj_V₁ {w : G} (hwT : w ∈ T) (hwV : ∀ r ∈ V, w * r * w⁻¹ = r) {z : G}
    (hz : z ∈ outerV₁ L T U₁) : z⁻¹ * (w * z * w⁻¹) ∈ szA₁ (szT₁ L T) := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := hS.start.start_of_card_sylow hS.card_sylow
  have hwt : w * t = t * w := mem_centralizer_singleton_iff.mp (hS.start.le hwT)
  have hwtw : w * t * w⁻¹ = t := by rw [hwt, mul_inv_cancel_right]
  have hwz : w * z * w⁻¹ ∈ outerV₁ L T U₁ :=
    (mem_normalizer_iff.mp (mem_normalizer_outerV₁ (hL.T_le hwT) (hTN₁ hwT)) z).mp hz
  have hzU := (mem_outerV₁.mp hz).1
  obtain ⟨r, hrdef⟩ : ∃ r, r = w * z * w⁻¹ * z⁻¹ := ⟨_, rfl⟩
  have hrz : w * z * w⁻¹ = r * z := by rw [hrdef]; group
  have hrV₁ : r ∈ outerV₁ L T U₁ := by rw [hrdef]; exact mul_mem hwz (inv_mem hz)
  have hrU := (mem_outerV₁.mp hrV₁).1
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = z * t * z⁻¹ * t⁻¹ := ⟨_, rfl⟩
  have hσz : ρ ∈ V := by rw [hρ]; exact hL.muOne_comm_t_mem hS (hL.U₁_le hzU)
  have hσw : r * z * t * (r * z)⁻¹ * t⁻¹ = ρ := by
    rw [← hrz]
    calc w * z * w⁻¹ * t * (w * z * w⁻¹)⁻¹ * t⁻¹ =
          w * z * w⁻¹ * (w * t * w⁻¹) * (w * z * w⁻¹)⁻¹ * (w * t * w⁻¹)⁻¹ := by rw [hwtw]
      _ = w * (z * t * z⁻¹ * t⁻¹) * w⁻¹ := by group
      _ = ρ := by rw [← hρ]; exact hwV ρ hσz
  have e1 : ρ = r * ρ * r⁻¹ * (r * t * r⁻¹ * t⁻¹) := by
    have h := SzC1.comm_t_mul r z t
    rw [hσw, ← hρ] at h
    exact h
  have hχ : ρ⁻¹ * (r * ρ * r⁻¹) ∈ szA₁ (szT₁ L T) := hL.conj_V₁ r hrU ρ hσz
  have hσr : r * t * r⁻¹ * t⁻¹ ∈ szA₁ (szT₁ L T) := by
    have e2 : r * t * r⁻¹ * t⁻¹ = (ρ⁻¹ * (r * ρ * r⁻¹))⁻¹ := by
      calc r * t * r⁻¹ * t⁻¹ =
            (r * ρ * r⁻¹)⁻¹ * (r * ρ * r⁻¹ * (r * t * r⁻¹ * t⁻¹)) := by group
        _ = (r * ρ * r⁻¹)⁻¹ * ρ := by rw [← e1]
        _ = (ρ⁻¹ * (r * ρ * r⁻¹))⁻¹ := by group
    rw [e2]
    exact inv_mem hχ
  have hrV : r ∈ V := hL.muOneCent_mem_V_of_comm_t_mem_szA₁ hS hrV₁ hσr
  have hσr2 : r * t * r⁻¹ * t⁻¹ = r ^ 2 := SzC1.comm_eq_sq_of_inv (hS.conf.inv r hrV)
  have hrρ : r * ρ * r⁻¹ = ρ := by rw [hS.conf.comm r hrV ρ hσz, mul_inv_cancel_right]
  have hr2 : r ^ 2 = 1 := by
    have e3 := e1
    rw [hrρ, hσr2] at e3
    exact mul_left_cancel (e3.symm.trans (mul_one ρ).symm)
  have hrA : r ∈ szA₁ (szT₁ L T) := hS.conf.omega r hrV hr2
  rw [hrz, show z⁻¹ * (r * z) = z⁻¹ * r * z⁻¹⁻¹ by group,
    hL.muOne_conj_szA₁ hS (inv_mem hzU) hrA]
  exact hrA

theorem muOneCent_conj_U₁ {w : G} (hwT : w ∈ T) (hwV : ∀ r ∈ V, w * r * w⁻¹ = r) {u : G}
    (hu : u ∈ U₁) : u⁻¹ * (w * u * w⁻¹) ∈ szT₁ L T := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := hS.start.start_of_card_sylow hS.card_sylow
  have hlam := hL.lambda hS.start hS.card_sylow hS.conf
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have hV₁N : szT₁ L T ≤ normalizer (outerV₁ L T U₁ : Set G) := fun y hy =>
    mem_normalizer_outerV₁ (Subgroup.le_normalizer (hT₁U₁ hy)) (Subgroup.le_normalizer hy)
  rw [hlam] at hu
  obtain ⟨y, hy, z, hz, rfl⟩ := ncyc_exists_mul_of_mem_sup hV₁N hu
  have hzC := (mem_outerV₁.mp hz).2
  have hwy : w * y * w⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp (hTN₁ hwT) y).mp hy
  have hzA := hL.muOneCent_conj_V₁ hS hwT hwV hz
  have hc : z⁻¹ * (y⁻¹ * (w * y * w⁻¹)) = (y⁻¹ * (w * y * w⁻¹)) * z⁻¹ :=
    (mem_centralizer_iff.mp (inv_mem hzC) _ (mul_mem (inv_mem hy) hwy)).symm
  have e : (y * z)⁻¹ * (w * (y * z) * w⁻¹) =
      (y⁻¹ * (w * y * w⁻¹)) * (z⁻¹ * (w * z * w⁻¹)) := by
    calc (y * z)⁻¹ * (w * (y * z) * w⁻¹) =
          z⁻¹ * (y⁻¹ * (w * y * w⁻¹)) * (w * z * w⁻¹) := by group
      _ = (y⁻¹ * (w * y * w⁻¹)) * z⁻¹ * (w * z * w⁻¹) := by rw [hc]
      _ = _ := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem hy) hwy) (szA₁_le _ hzA)

end Facts

section Coords

variable (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1)
  (hL : U3C1OuterLevelData G L f t T D V U U₁ 1) {K : Type} [Field K] [Fintype K] [CharP K 2]
  {v : G → K} {μ : K} (hc : U3A₁Coords (szA₁ (szT₁ L T)) d v μ)
include hS hL hc

theorem muOneCent_false_of_commute (hμV : ¬ U₁ ≤ centralizer (V : Set G))
    (hK : Fintype.card K = 2 ^ f) (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) {w : G}
    (hwT : w ∈ T) (hwV : ∀ r ∈ V, w * r * w⁻¹ = r) {u : G} (hu : u ∈ U₁)
    (huTV : u ∉ szT₁ L T ⊔ V) {c : G} (hct : c * t⁻¹ ∈ U₁) (hcx : c * (u * w) = u * w * c) :
    False := by
  have hcommA := hL.muOne_comm_mem_szA₁ hS hc hμV hK hμ
  have hwt : w * t = t * w := mem_centralizer_singleton_iff.mp (hS.start.le hwT)
  have htw : t * w⁻¹ * t⁻¹ = w⁻¹ := by
    rw [show t * w⁻¹ = w⁻¹ * t from ((Commute.inv_left (show Commute w t from hwt)).eq).symm,
      mul_inv_cancel_right]
  obtain ⟨u', hu', rfl⟩ : ∃ u' ∈ U₁, u' * t = c := ⟨c * t⁻¹, hct, by group⟩
  have hb : t * u * t⁻¹ = u'⁻¹ * u * (w * u' * w⁻¹) := by
    calc t * u * t⁻¹ = u'⁻¹ * (u' * t * (u * w)) * w⁻¹ * t⁻¹ := by group
      _ = u'⁻¹ * (u * w * (u' * t)) * w⁻¹ * t⁻¹ := by rw [hcx]
      _ = u'⁻¹ * u * (w * u' * (t * w⁻¹ * t⁻¹)) := by group
      _ = u'⁻¹ * u * (w * u' * w⁻¹) := by rw [htw]
  have hT : u⁻¹ * (t * u * t⁻¹) ∈ szT₁ L T := by
    rw [hb, show u⁻¹ * (u'⁻¹ * u * (w * u' * w⁻¹)) =
        (u⁻¹ * u'⁻¹ * u⁻¹⁻¹ * u'⁻¹⁻¹) * (u'⁻¹ * (w * u' * w⁻¹)) by group]
    exact mul_mem (szA₁_le _ (hcommA _ (inv_mem hu) _ (inv_mem hu')))
      (hL.muOneCent_conj_U₁ hS hwT hwV hu')
  have hσV := hL.muOne_comm_t_mem hS (hL.U₁_le hu)
  have hσT : u * t * u⁻¹ * t⁻¹ ∈ szT₁ L T := by
    rw [show u * t * u⁻¹ * t⁻¹ = u * (u⁻¹ * (t * u * t⁻¹))⁻¹ * u⁻¹ by group]
    exact hL.muOneCent_conj_T₁_mem hS (hL.U₁_le hu) (inv_mem hT)
  exact huTV (hL.muOne_mem_sup_of_comm_t_mem_szA₁ hS hu
    (mem_szA₁.mpr ⟨hσT, hS.conf.le_centralizer hσV⟩))

theorem muOneCent_card_le (hμV : ¬ U₁ ≤ centralizer (V : Set G))
    (hK : Fintype.card K = 2 ^ f) (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) {w : G}
    (hwT : w ∈ T) (hw2 : w ^ 2 = 1) (hwS : w ∉ szT₁ L T ⊔ zpowers t)
    (hwV : ∀ r ∈ V, w * r * w⁻¹ = r) {u : G} (hu : u ∈ U₁) (huTV : u ∉ szT₁ L T ⊔ V) :
    Nat.card (U₁ ⊓ centralizer ({u * w} : Set G) : Subgroup G) ≤ (2 ^ f) ^ 3 := by
  obtain ⟨hT₁card, hA₁card, -, -, -, -, -⟩ := hS.start.facts_of_card_sylow hS.card_sylow
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := hS.start.start_of_card_sylow hS.card_sylow
  obtain ⟨W, hWT₁, hAW, hWcard, -, -, -, hWiff⟩ :=
    hS.start.exists_W_of_card_sylow hS.card_sylow hwT hw2 hwS
  have hlam := hL.lambda hS.start hS.card_sylow hS.conf
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have hV₁N : szT₁ L T ≤ normalizer (outerV₁ L T U₁ : Set G) := fun y hy =>
    mem_normalizer_outerV₁ (Subgroup.le_normalizer (hT₁U₁ hy)) (Subgroup.le_normalizer hy)
  have hA₁V₁ : szA₁ (szT₁ L T) ≤ outerV₁ L T U₁ := fun a ha =>
    mem_outerV₁.mpr ⟨hT₁U₁ (szA₁_le _ ha), (mem_szA₁.mp ha).2⟩
  have hinf : szT₁ L T ⊓ outerV₁ L T U₁ ≤ szA₁ (szT₁ L T) := fun y hy =>
    mem_szA₁.mpr ⟨(mem_inf.mp hy).1, (mem_outerV₁.mp (mem_inf.mp hy).2).2⟩
  have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
  have hUNT₁ : ∀ u₀ ∈ U, u₀ ∈ normalizer (szT₁ L T : Set G) := fun u₀ hu₀ =>
    mem_normalizer_of_forall_inv_mul_mul_mem fun y hy => by
      simpa using hL.muOneCent_conj_T₁_mem hS (inv_mem hu₀) hy
  set x := u * w with hxdef
  have hxN : x ∈ normalizer (szT₁ L T : Set G) := mul_mem (hUNT₁ u (hL.U₁_le hu)) (hTN₁ hwT)
  have hxNU₁ : x ∈ normalizer (U₁ : Set G) := mul_mem (Subgroup.le_normalizer hu) (hL.T_le hwT)
  have hxNV₁ : x ∈ normalizer (outerV₁ L T U₁ : Set G) := mem_normalizer_outerV₁ hxNU₁ hxN
  have hxT : ∀ y ∈ szT₁ L T, x * y * x⁻¹ ∈ szT₁ L T := fun y hy =>
    (mem_normalizer_iff.mp hxN y).mp hy
  have hxU : ∀ z ∈ outerV₁ L T U₁, x * z * x⁻¹ ∈ outerV₁ L T U₁ := fun z hz =>
    (mem_normalizer_iff.mp hxNV₁ z).mp hz
  have hW : ∀ y ∈ szT₁ L T, y⁻¹ * (x * y * x⁻¹) ∈ szA₁ (szT₁ L T) → y ∈ W := by
    intro y hy hyA
    have hwy : w * y * w⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp (hTN₁ hwT) y).mp hy
    have h1 := hL.conj_T₁ u (hL.U₁_le hu) _ hwy
    refine (hWiff y hy).mp ?_
    have e : y⁻¹ * (w * y * w⁻¹) = (y⁻¹ * (x * y * x⁻¹)) *
        ((w * y * w⁻¹)⁻¹ * (u * (w * y * w⁻¹) * u⁻¹))⁻¹ := by rw [hxdef]; group
    rw [e]
    exact mul_mem hyA (inv_mem h1)
  have hcomm : ∀ y ∈ szT₁ L T, ∀ z ∈ outerV₁ L T U₁, y * z = z * y := fun y hy z hz =>
    mem_centralizer_iff.mp (mem_outerV₁.mp hz).2 y hy
  have hncyc := ncyc_card_inf_centralizer_mul_le (T₁ := szT₁ L T) (U := outerV₁ L T U₁)
    (A₁ := szA₁ (szT₁ L T)) (W := W) (x := x) hcomm hinf hAW hWT₁ hA₁V₁ hxT hxU hW
  rw [← hlam, hA₁card, hWcard] at hncyc
  have hSu : v ((u * t * u⁻¹ * t⁻¹) ^ 2) ≠ 0 := fun h0 =>
    huTV (hL.muOne_mem_sup_of_S_eq_zero hS hc hu h0)
  set X := outerV₁ L T U₁ ⊓ centralizer ({x} : Set G) with hXdef
  have hVX : V ⊓ X ≤ szA₁ (szT₁ L T) := by
    intro r hr
    obtain ⟨hrV, hrX⟩ := mem_inf.mp hr
    have hrx : r * x = x * r := mem_centralizer_singleton_iff.mp (mem_inf.mp hrX).2
    have hwr : w * r = r * w := by
      calc w * r = w * r * w⁻¹ * w := by group
        _ = r * w := by rw [hwV r hrV]
    have h1 : r * u * w = u * r * w := by
      calc r * u * w = r * x := by rw [hxdef]; group
        _ = x * r := hrx
        _ = u * (w * r) := by rw [hxdef]; group
        _ = u * r * w := by rw [hwr]; group
    exact hL.muOne_mem_szA₁_of_commute hS hc hμV hK hμ hu hSu hrV (mul_right_cancel h1).symm
  have hV₁card : Nat.card (outerV₁ L T U₁) ≤ (2 ^ f) ^ 3 := by
    have hp := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := outerV₁ L T U₁) (B := szT₁ L T) hV₁N
    rw [sup_comm, ← hlam, hL.muOne_card_U₁ hS, hT₁card] at hp
    have hle : Nat.card (outerV₁ L T U₁ ⊓ szT₁ L T : Subgroup G) ≤ 2 ^ f := by
      rw [← hA₁card]
      exact Subgroup.card_le_of_le fun y hy =>
        hinf (mem_inf.mpr ⟨(mem_inf.mp hy).2, (mem_inf.mp hy).1⟩)
    by_contra hgt
    push Not at hgt
    have h1 : (2 ^ f) ^ 3 * (2 ^ f) ^ 3 < Nat.card (outerV₁ L T U₁) * (2 ^ f) ^ 3 :=
      Nat.mul_lt_mul_of_pos_right hgt (pow_pos hq0 3)
    have h2 : (2 ^ f) ^ 5 * Nat.card (outerV₁ L T U₁ ⊓ szT₁ L T : Subgroup G) ≤
        (2 ^ f) ^ 5 * 2 ^ f := Nat.mul_le_mul_left _ hle
    have h3 : (2 ^ f) ^ 5 * 2 ^ f = (2 ^ f) ^ 3 * (2 ^ f) ^ 3 := by ring
    rw [hp, h3] at h2
    exact absurd (h1.trans_le h2) (lt_irrefl _)
  have hXN : X ≤ normalizer (V : Set G) := fun z hz =>
    mem_normalizer_of_forall_inv_mul_mul_mem fun r hr => by
      simpa using hL.muOne_conj_V hS (inv_mem (mem_outerV₁.mp (mem_inf.mp hz).1).1) hr
  have hXcard : Nat.card X ≤ (2 ^ f) ^ 2 := by
    have hp := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := V) (B := X) hXN
    rw [hS.conf.card] at hp
    have h1 : Nat.card (V ⊔ X : Subgroup G) ≤ (2 ^ f) ^ 3 :=
      (Subgroup.card_le_of_le (sup_le (hL.V_le_V₁ hS.conf) inf_le_left)).trans hV₁card
    have h2 : Nat.card (V ⊓ X : Subgroup G) ≤ 2 ^ f := by
      rw [← hA₁card]
      exact Subgroup.card_le_of_le hVX
    by_contra hgt
    push Not at hgt
    have h3 : (2 ^ f) ^ (1 + 1) * Nat.card X ≤ (2 ^ f) ^ 3 * 2 ^ f := by
      rw [← hp]
      exact Nat.mul_le_mul h1 h2
    have h4 : (2 ^ f) ^ (1 + 1) * (2 ^ f) ^ 2 < (2 ^ f) ^ (1 + 1) * Nat.card X :=
      Nat.mul_lt_mul_of_pos_left hgt (pow_pos hq0 _)
    have h5 : (2 ^ f) ^ 3 * 2 ^ f = (2 ^ f) ^ (1 + 1) * (2 ^ f) ^ 2 := by ring
    rw [h5] at h3
    exact absurd (h4.trans_le h3) (lt_irrefl _)
  by_contra hgt
  push Not at hgt
  have h1 : (2 ^ f) ^ 3 * 2 ^ f <
      Nat.card (U₁ ⊓ centralizer ({x} : Set G) : Subgroup G) * 2 ^ f :=
    Nat.mul_lt_mul_of_pos_right hgt hq0
  have h2 : (2 ^ f) ^ 2 * Nat.card X ≤ (2 ^ f) ^ 2 * (2 ^ f) ^ 2 :=
    Nat.mul_le_mul_left _ hXcard
  have h3 : (2 ^ f) ^ 2 * (2 ^ f) ^ 2 = (2 ^ f) ^ 3 * 2 ^ f := by ring
  rw [h3] at h2
  exact absurd (h1.trans_le (hncyc.trans h2)) (lt_irrefl _)

theorem muOneCent_exists_conj_eq (hμV : ¬ U₁ ≤ centralizer (V : Set G))
    (hK : Fintype.card K = 2 ^ f) (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) {w : G}
    (hwT : w ∈ T) (hw2 : w ^ 2 = 1) (hwS : w ∉ szT₁ L T ⊔ zpowers t)
    (hwV : ∀ r ∈ V, w * r * w⁻¹ = r) {g : G} (hgT : ∀ s ∈ T, g * s * g⁻¹ ∈ U ⊔ T)
    (hx : g * t * g⁻¹ * w⁻¹ ∈ U₁) : ∃ c ∈ szT₁ L T, c * (g * t * g⁻¹) * c⁻¹ = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hT₁card, -, -, hsqT, -, -, -⟩ := hS.start.facts_of_card_sylow hS.card_sylow
  obtain ⟨htT, -, -, hTN₁, -, -, -⟩ := hS.start.start_of_card_sylow hS.card_sylow
  obtain ⟨W, -, hAW, hWcard, -, hWinv, -, hWiff⟩ :=
    hS.start.exists_W_of_card_sylow hS.card_sylow hwT hw2 hwS
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
  set x := g * t * g⁻¹ with hxdef
  set u := x * w⁻¹ with hudef
  have hxu : x = u * w := by rw [hudef]; group
  have hu : u ∈ U₁ := hx
  have htt : t * t = 1 := by rw [← sq, hS.start.sq_eq_one]
  have hxx : x * x = 1 := by
    rw [hxdef, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, htt, mul_one,
      mul_inv_cancel]
  have huTV : u ∈ szT₁ L T ⊔ V := by
    by_contra huTV
    set Kg : Subgroup G := T.map (MulAut.conj g).toMonoidHom with hKgdef
    have hKmem : ∀ k ∈ Kg, ∃ s ∈ T, k = g * s * g⁻¹ := by
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨s, hs, by simp [MulAut.conj_apply]⟩
    have hKcard : Nat.card Kg = Nat.card T := card_map_of_injective (MulAut.conj g).injective
    set H := (U ⊔ T) ⊓ centralizer ({x} : Set G) with hHdef
    have hKH : Kg ≤ H := by
      intro k hk
      obtain ⟨s, hs, rfl⟩ := hKmem k hk
      refine mem_inf.mpr ⟨hgT s hs, mem_centralizer_singleton_iff.mpr ?_⟩
      have hst := mem_centralizer_singleton_iff.mp (hS.start.le hs)
      calc g * s * g⁻¹ * x = g * (s * t) * g⁻¹ := by rw [hxdef]; group
        _ = g * (t * s) * g⁻¹ := by rw [hst]
        _ = x * (g * s * g⁻¹) := by rw [hxdef]; group
    have hTH : Nat.card T ≤ Nat.card H := hKcard ▸ Subgroup.card_le_of_le hKH
    have hHN : H ≤ normalizer (U₁ : Set G) := inf_le_left.trans (hL.muOne_sup_le_normalizer hS)
    have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := U₁) (B := H) hHN
    rw [hL.muOne_card_U₁ hS] at hprod
    have hinf : Nat.card (U₁ ⊓ H : Subgroup G) ≤ (2 ^ f) ^ 3 := by
      refine (Subgroup.card_le_of_le ?_).trans
        (hL.muOneCent_card_le hS hc hμV hK hμ hwT hw2 hwS hwV hu huTV)
      intro y hy
      refine mem_inf.mpr ⟨(mem_inf.mp hy).1, ?_⟩
      rw [← hxu]
      exact (mem_inf.mp (mem_inf.mp hy).2).2
    have htnot : t ∉ U₁ ⊔ H := by
      intro htH
      rw [sup_comm] at htH
      obtain ⟨h, hh, u₀, hu₀, hhu⟩ := ncyc_exists_mul_of_mem_sup hHN htH
      have hct : h * t⁻¹ ∈ U₁ := by
        rw [show h * t⁻¹ = t * u₀⁻¹ * t⁻¹ by rw [← hhu]; group]
        exact (mem_normalizer_iff.mp (hL.T_le htT) _).mp (inv_mem hu₀)
      have hcx : h * (u * w) = u * w * h := by
        rw [← hxu]
        exact mem_centralizer_singleton_iff.mp (mem_inf.mp hh).2
      exact hL.muOneCent_false_of_commute hS hc hμV hK hμ hwT hwV hu huTV hct hcx
    have hle : U₁ ⊔ H ≤ U ⊔ T := sup_le (hL.U₁_le.trans le_sup_left) inf_le_left
    have hri := relIndex_mul_card (U₁ ⊔ H) (U ⊔ T)
    rw [inf_of_le_left hle] at hri
    have hri2 : 2 ≤ (U₁ ⊔ H).relIndex (U ⊔ T) := by
      by_contra hlt
      push Not at hlt
      have h01 : (U₁ ⊔ H).relIndex (U ⊔ T) = 0 ∨ (U₁ ⊔ H).relIndex (U ⊔ T) = 1 := by omega
      rcases h01 with h0 | h1
      · rw [h0, zero_mul] at hri
        exact (Nat.card_pos (α := (U ⊔ T : Subgroup G))).ne' hri.symm
      · exact htnot (relIndex_eq_one.mp h1 (mem_sup_right htT))
    have hSU : U ⊔ T = U₁ ⊔ T := by rw [hL.muOne_sup_eq hS, sup_comm]
    have hprodT := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := U₁) (B := T) hL.T_le
    have hU₁T : U₁ ⊓ T = szT₁ L T :=
      le_antisymm (fun z hz => hL.muOne_mem_T₁_of_mem_T hS (mem_inf.mp hz).1 (mem_inf.mp hz).2)
        (le_inf hT₁U₁ (szT₁_le_left L T))
    rw [hU₁T, hT₁card, hL.muOne_card_U₁ hS, ← hSU] at hprodT
    have hHpos : 0 < Nat.card H := Nat.card_pos
    have e1 : (2 ^ f) ^ 5 * Nat.card H ≤ Nat.card (U₁ ⊔ H : Subgroup G) * (2 ^ f) ^ 3 := by
      rw [← hprod]
      exact Nat.mul_le_mul_left _ hinf
    have e2 : 2 * Nat.card (U₁ ⊔ H : Subgroup G) ≤ Nat.card (U ⊔ T : Subgroup G) := by
      rw [← hri]
      exact Nat.mul_le_mul_right _ hri2
    have e3 : 2 * ((2 ^ f) ^ 5 * Nat.card H) ≤ (2 ^ f) ^ 5 * Nat.card H := by
      calc 2 * ((2 ^ f) ^ 5 * Nat.card H) ≤
            2 * (Nat.card (U₁ ⊔ H : Subgroup G) * (2 ^ f) ^ 3) := Nat.mul_le_mul_left _ e1
        _ = (2 * Nat.card (U₁ ⊔ H : Subgroup G)) * (2 ^ f) ^ 3 := by ring
        _ ≤ Nat.card (U ⊔ T : Subgroup G) * (2 ^ f) ^ 3 := Nat.mul_le_mul_right _ e2
        _ = (2 ^ f) ^ 5 * Nat.card T := hprodT
        _ ≤ (2 ^ f) ^ 5 * Nat.card H := Nat.mul_le_mul_left _ hTH
    have e4 : 0 < (2 ^ f) ^ 5 * Nat.card H := Nat.mul_pos (pow_pos hq0 5) hHpos
    omega
  obtain ⟨y, hy, r, hr, hyr⟩ := ncyc_exists_mul_of_mem_sup (hL.muOne_T₁_le_normalizer hS) huTV
  have hwr : w * r = r * w := by
    calc w * r = w * r * w⁻¹ * w := by group
      _ = r * w := by rw [hwV r hr]
  have hwy : w * y * w⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp (hTN₁ hwT) y).mp hy
  have hww : w * w = 1 := by rw [← sq, hw2]
  have hx2 : x * x = (y * (w * y * w⁻¹)) * r ^ 2 := by
    rw [hxu, ← hyr]
    have c1 := hL.muOne_T₁_comm hS hwy hr
    calc y * r * w * (y * r * w) = y * r * (w * y * w⁻¹) * (w * r) * w := by group
      _ = y * r * (w * y * w⁻¹) * (r * w) * w := by rw [hwr]
      _ = y * (r * (w * y * w⁻¹)) * r * (w * w) := by group
      _ = y * ((w * y * w⁻¹) * r) * r * (w * w) := by rw [← c1]
      _ = (y * (w * y * w⁻¹)) * r ^ 2 := by rw [hww, sq]; group
  rw [hxx] at hx2
  have hr2A := hL.muOne_sq_mem_szA₁_of_mem_V hS hr
  have hyyA : y * (w * y * w⁻¹) ∈ szA₁ (szT₁ L T) := by
    rw [eq_inv_of_mul_eq_one_left hx2.symm]
    exact inv_mem hr2A
  have hyW : y ∈ W := by
    refine (hWiff y hy).mp ?_
    rw [show y⁻¹ * (w * y * w⁻¹) = (y ^ 2)⁻¹ * (y * (w * y * w⁻¹)) by rw [sq]; group]
    exact mul_mem (inv_mem (hsqT y hy)) hyyA
  have hr2 : r ^ 2 = 1 := by
    rw [hWinv y hyW, mul_inv_cancel, one_mul] at hx2
    exact hx2.symm
  have hrA : r ∈ szA₁ (szT₁ L T) := hS.conf.omega r hr hr2
  have huW : u ∈ W := by rw [← hyr]; exact mul_mem hyW (hAW hrA)
  obtain ⟨c, hcT, hcw⟩ :=
    hS.start.muOneCent_exists_conj_of_mem_W hS.card_sylow hwT hw2 hwS hWcard hWiff huW
  refine ⟨c⁻¹, inv_mem hcT, ?_⟩
  rw [hxu, ← hcw]
  group

end Coords

end U3C1OuterLevelData

end CFSG.SeitzReduction.RankOne

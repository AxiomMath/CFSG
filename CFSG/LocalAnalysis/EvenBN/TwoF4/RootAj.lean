module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootAi

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

section Generic

variable {X : Type*} [Group X]

theorem card_sup_mul_card_inf_of_normal' (A L : Subgroup X) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup X) * Nat.card (A ⊓ L : Subgroup X) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf_of_le_normalizer' {A B : Subgroup X}
    (hB : B ≤ normalizer (A : Set X)) :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) = Nat.card A * Nat.card B := by
  set N := normalizer (A : Set X)
  have hAN : A ≤ N := le_normalizer
  have : (A.subgroupOf N).Normal := normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal' (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ Y : Subgroup X, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (subgroupOfEquivOfLe hY).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

variable [Finite X]

theorem inf_center_ne_bot_of_normalized' {T N : Subgroup X} (hT : IsPGroup 2 T)
    (hNT : N ≤ T) (hn : T ≤ normalizer (N : Set X)) (hN : N ≠ ⊥) :
    N ⊓ (T ⊓ centralizer (T : Set X)) ≠ ⊥ := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (N.subgroupOf T).Normal := normal_subgroupOf_of_le_normalizer hn
  have hne : N.subgroupOf T ≠ ⊥ := by
    intro h
    apply hN
    rw [← map_subgroupOf_eq_of_le hNT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : X) ∈ centralizer (T : Set X) := by
    rw [mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : X) ∈ N ⊓ (T ⊓ centralizer (T : Set X)) := ⟨hy.1, y.2, hyC⟩
  rw [h, mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

end Generic

section Model

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem rootV1_inf_radR (hK : Nat.card K = 2 ^ (2 * a + 1)) : rootV K a .i1 ⊓ radR K a = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hg1, hgR⟩ := mem_inf.1 hg
  have h1 : g ∈ (rootV K a .i1 : Set (ModGL F4.tag K)) := hg1
  have hR : g ∈ (radR K a : Set (ModGL F4.tag K)) := hgR
  rw [coe_rootV hK] at h1
  rw [(radR_spec hK).2.1] at hR
  obtain ⟨x, hx, rfl⟩ := h1
  obtain ⟨z, hz, hzx⟩ := hR
  have hxz := (bijOn_sylowVec (m := a) (K := K) hK).injOn (Set.mem_univ _) (Set.mem_univ _) hzx
  have hx0 : x = 0 := by
    funext n
    by_cases hn : n ∈ Idx.i1.coords
    · have : n = 1 ∨ n = 2 := by simpa [Idx.coords, Idx.isSz, Idx.coord, Idx.center] using hn
      rcases this with rfl | rfl
      · rw [← hxz]
        exact hz 1 (by decide)
      · rw [← hxz]
        exact hz 2 (by decide)
    · exact hx n hn
  rw [mem_bot, hx0]
  have := (rootElt_eq_sylowVec (a := a) (K := K) .i2 0).symm
  rw [rootElt_zero] at this
  rw [← this]
  simp

end Model

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable (h : Setup G)

theorem V1_inf_R : h.V .i1 ⊓ h.R = ⊥ := by
  rw [Setup.V, Setup.R, ← h.pull_inf, rootV1_inf_radR h.card_K, h.pull_bot]

theorem V1_le_J : h.V .i1 ≤ h.J :=
  (h.V_le_P .i1).trans (le_sup_left.trans h.P_sup_Tsyl_le_J_Kp.1)

theorem isPGroup_V1_sup_t : IsPGroup 2 (h.V .i1 ⊔ zpowers h.t : Subgroup G) :=
  (h.isPGroup_V .i1).to_sup_of_normal_left' h.isPGroup_zpowers_t (zpowers_le.2
    (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun _ hv =>
      (h.t_commute_L (h.pull_le_L _ hv)).symm)))

theorem V1_sup_t_le_C : h.V .i1 ⊔ zpowers h.t ≤ h.C :=
  sup_le (fun _ hv => mem_centralizer_singleton_iff.2 (h.t_commute_L (h.pull_le_L _ hv)).symm)
    (zpowers_le.2 h.t_mem_C)

theorem eq_one_of_mem_V1_sup_t_of_mem_R {x : G} (hx : x ∈ h.V .i1 ⊔ zpowers h.t)
    (hxR : x ∈ h.R) : x = 1 := by
  have hVt : zpowers h.t ≤ normalizer (h.V .i1 : Set G) :=
    zpowers_le.2 (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun _ hv =>
      (h.t_commute_L (h.pull_le_L _ hv)).symm))
  have hx' : x ∈ ((h.V .i1 ⊔ zpowers h.t : Subgroup G) : Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left _ _ hVt, Set.mem_mul] at hx'
  obtain ⟨v, hv, c, hc, rfl⟩ := hx'
  rcases eq_one_or_eq_of_mem_zpowers h.t_mul_t hc with rfl | rfl
  · rw [mul_one] at hxR ⊢
    have : v ∈ h.V .i1 ⊓ h.R := mem_inf.2 ⟨hv, hxR⟩
    rwa [h.V1_inf_R, mem_bot] at this
  · exfalso
    apply h.t_not_mem_L
    have e : h.t = v⁻¹ * (v * h.t) := by group
    rw [e]
    exact mul_mem (inv_mem (h.pull_le_L _ hv)) (h.R_le_L hxR)

end Setup

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

theorem mem_W2_iff {y : G} : y ∈ d.W2 ↔ h.s * y * h.s⁻¹ ∈ d.WA .i4 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h.s_inv]
    rw [show h.s * (h.s * z * h.s) * h.s = (h.s * h.s) * z * (h.s * h.s) by group,
      h.r_mul_self_s_mul_self.2, one_mul, mul_one]
    exact hz
  · intro hy
    refine ⟨h.s * y * h.s⁻¹, hy, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h.s_inv,
      show h.s * (h.s * y * h.s) * h.s = (h.s * h.s) * y * (h.s * h.s) by group,
      h.r_mul_self_s_mul_self.2, one_mul, mul_one]

theorem isPGroup_W2 : IsPGroup 2 d.W2 := d.isPGroup_B4.to_le d.W2_le_B4

theorem conj_mem_WA4 {g z : G} (hgA : g ∈ normalizer (d.A1 : Set G)) (hgH : g ∈ h.CH .i4)
    (hz : z ∈ d.WA .i4) : g * z * g⁻¹ ∈ d.WA .i4 :=
  ⟨(mem_normalizer_iff.1 hgA z).1 hz.1,
    (h.CH .i4).mul_mem ((h.CH .i4).mul_mem hgH hz.2) ((h.CH .i4).inv_mem hgH)⟩

theorem V1_le_normalizer_W2 : h.V .i1 ≤ normalizer (d.W2 : Set G) := by
  have key : ∀ {v : G}, v ∈ h.V .i1 → ∀ y ∈ d.W2, v * y * v⁻¹ ∈ d.W2 := by
    intro v hv y hy
    rw [d.mem_W2_iff] at hy ⊢
    have hv4 : h.s * v * h.s⁻¹ ∈ h.V .i4 := h.conj_s_mem_V (i := .i1) (by decide) hv
    rw [show h.s * (v * y * v⁻¹) * h.s⁻¹ =
      (h.s * v * h.s⁻¹) * (h.s * y * h.s⁻¹) * (h.s * v * h.s⁻¹)⁻¹ by group]
    exact d.conj_mem_WA4 (d.J_le_normalizer_A1 (h.R_le_J ((h.V_le_R (by decide)) hv4)))
      (h.V_le_CH (by decide) (Or.inl rfl) hv4) hy
  intro v hv
  refine mem_normalizer_of_conj_mem (key hv) fun y hy => ?_
  have := key (inv_mem hv) y hy
  rwa [inv_inv] at this

theorem t_mem_normalizer_W2 : h.t ∈ normalizer (d.W2 : Set G) := by
  have key : ∀ y ∈ d.W2, h.t * y * h.t⁻¹ ∈ d.W2 := by
    intro y hy
    rw [d.mem_W2_iff] at hy ⊢
    have e : h.s * (h.t * y * h.t⁻¹) * h.s⁻¹ = h.t * (h.s * y * h.s⁻¹) * h.t⁻¹ := by
      have h1 := h.s_comm_t
      calc h.s * (h.t * y * h.t⁻¹) * h.s⁻¹ = (h.s * h.t) * y * (h.s * h.t)⁻¹ := by group
        _ = (h.t * h.s) * y * (h.t * h.s)⁻¹ := by rw [h1]
        _ = h.t * (h.s * y * h.s⁻¹) * h.t⁻¹ := by group
    rw [e]
    exact d.conj_mem_WA4 (d.J_le_normalizer_A1 h.t_mem_J) (h.t_mem_CH .i4) hy
  refine mem_normalizer_of_conj_mem key fun y hy => ?_
  have := key y hy
  rw [h.t_inv] at this ⊢
  exact this

theorem mem_V1_of_mem_W2_of_commute {w : G} (hw : w ∈ d.W2) (hwt : w * h.t = h.t * w) :
    w ∈ h.V .i1 := by
  rw [d.mem_W2_iff] at hw
  have hst : (h.s * w * h.s⁻¹) * h.t = h.t * (h.s * w * h.s⁻¹) := by
    have h1 := h.s_comm_t
    have h2 : h.s⁻¹ * h.t = h.t * h.s⁻¹ := (Commute.inv_left (show Commute h.s h.t from h1)).eq
    calc h.s * w * h.s⁻¹ * h.t = h.s * w * (h.s⁻¹ * h.t) := by group
      _ = h.s * (w * h.t) * h.s⁻¹ := by rw [h2]; group
      _ = h.s * (h.t * w) * h.s⁻¹ := by rw [hwt]
      _ = (h.s * h.t) * w * h.s⁻¹ := by group
      _ = h.t * (h.s * w * h.s⁻¹) := by rw [h1]; group
  have hR := d.mem_R₁_of_mem_A1 hw.1 (commutatorElement_eq_one_iff_mul_comm.2 hst)
  have h8 : h.s * w * h.s⁻¹ ∈ h.V .i8 := h.mem_V_of_mem_R₁_of_mem_CH (i := .i4) (k := .i8)
    (by decide) (by decide) hR hw.2
  have h2 := h.conj_s_mem_V (i := .i8) (by decide) h8
  rw [show h.s * (h.s * w * h.s⁻¹) * h.s⁻¹ = (h.s * h.s) * w * (h.s⁻¹ * h.s⁻¹) by group,
    h.r_mul_self_s_mul_self.2, one_mul, ← mul_inv_rev, h.r_mul_self_s_mul_self.2, inv_one,
    mul_one] at h2
  exact h.V_center_le .i1 h2

theorem exists_mem_W2_comm_ne_one : ∃ w ∈ d.W2, ⁅w, h.t⁆ ≠ 1 := by
  obtain ⟨x, hx, hxt⟩ := d.exists_WA_comm_t (i := .i4) (k := .i8) (h.V_le_R₁ (by decide))
    (h.V_le_CH (by decide) (Or.inr rfl)) (h.elt_rootElt_mem_V .i8 1)
  refine ⟨h.s * x * h.s⁻¹, ?_, fun h1 => ?_⟩
  · rw [d.mem_W2_iff, show h.s * (h.s * x * h.s⁻¹) * h.s⁻¹ = (h.s * h.s) * x * (h.s⁻¹ * h.s⁻¹)
      by group, h.r_mul_self_s_mul_self.2, one_mul, ← mul_inv_rev, h.r_mul_self_s_mul_self.2,
      inv_one, mul_one]
    exact hx
  · have hst : h.s * h.t * h.s⁻¹ = h.t := by rw [h.s_comm_t, mul_inv_cancel_right]
    have e : ⁅h.s * x * h.s⁻¹, h.t⁆ = h.s * ⁅x, h.t⁆ * h.s⁻¹ := by
      conv_lhs => rw [← hst]
      exact (conjugate_commutatorElement x h.t h.s).symm
    rw [e] at h1
    have h3 : ⁅x, h.t⁆ = 1 := by
      calc ⁅x, h.t⁆ = h.s⁻¹ * (h.s * ⁅x, h.t⁆ * h.s⁻¹) * h.s := by group
        _ = 1 := by rw [h1]; group
    rw [hxt] at h3
    exact h.elt_rootElt_one_ne_one .i8 h3

@[expose] def Ystar : Subgroup G := d.W2 ⊔ (h.V .i1 ⊔ zpowers h.t)

theorem V1_sup_t_le_normalizer_W2 : h.V .i1 ⊔ zpowers h.t ≤ normalizer (d.W2 : Set G) :=
  sup_le d.V1_le_normalizer_W2 (zpowers_le.2 d.t_mem_normalizer_W2)

theorem isPGroup_Ystar : IsPGroup 2 d.Ystar :=
  d.isPGroup_W2.to_sup_of_normal_left' h.isPGroup_V1_sup_t d.V1_sup_t_le_normalizer_W2

theorem t_mem_Ystar : h.t ∈ d.Ystar := mem_sup_right (mem_sup_right (mem_zpowers _))

theorem Ystar_le_normalizer_D : d.Ystar ≤ normalizer (d.D : Set G) :=
  sup_le (d.W2_le_B4.trans d.B4_le_normalizer_D)
    (sup_le (h.V1_le_J.trans d.J_le_normalizer_D) (zpowers_le.2 (d.J_le_normalizer_D h.t_mem_J)))

theorem mem_V1_sup_t_of_mem_Ystar {y : G} (hy : y ∈ d.Ystar) (hyt : y * h.t = h.t * y) :
    y ∈ h.V .i1 ⊔ zpowers h.t := by
  have hy' : y ∈ ((d.W2 ⊔ (h.V .i1 ⊔ zpowers h.t) : Subgroup G) : Set G) := hy
  rw [coe_mul_of_right_le_normalizer_left d.W2 (h.V .i1 ⊔ zpowers h.t)
    d.V1_sup_t_le_normalizer_W2, Set.mem_mul] at hy'
  obtain ⟨w, hw, u, hu, rfl⟩ := hy'
  have hut : u * h.t = h.t * u := mem_centralizer_singleton_iff.1 (h.V1_sup_t_le_C hu)
  have hwt : w * h.t = h.t * w := by
    have : w * u * h.t = h.t * (w * u) := hyt
    calc w * h.t = w * u * h.t * u⁻¹ := by rw [mul_assoc w u, hut]; group
      _ = h.t * (w * u) * u⁻¹ := by rw [this]
      _ = h.t * w := by group
  exact mul_mem (mem_sup_left (d.mem_V1_of_mem_W2_of_commute hw hwt)) hu

theorem Ystar_inf_D : d.Ystar ⊓ d.D = ⊥ := by
  by_contra hne
  have hn : d.Ystar ≤ normalizer ((d.Ystar ⊓ d.D : Subgroup G) : Set G) := fun y hy =>
    mem_normalizer_inf (le_normalizer hy) (d.Ystar_le_normalizer_D hy)
  have h1 := inf_center_ne_bot_of_normalized' d.isPGroup_Ystar inf_le_left hn hne
  obtain ⟨⟨z, hz⟩, hz1⟩ := ne_bot_iff_exists_ne_one.mp h1
  have hz1' : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  have hzY : z ∈ d.Ystar := hz.1.1
  have hzD : z ∈ d.D := hz.1.2
  have hzc : z ∈ centralizer (d.Ystar : Set G) := hz.2.2
  have hzt : z * h.t = h.t * z := (mem_centralizer_iff.1 hzc h.t d.t_mem_Ystar).symm
  exact hz1' (h.eq_one_of_mem_V1_sup_t_of_mem_R (d.mem_V1_sup_t_of_mem_Ystar hzY hzt)
    (d.mem_R_of_mem_D_of_commute hzD hzt))

theorem card_Ystar : 2 * Nat.card (h.V .i1 ⊔ zpowers h.t : Subgroup G) ≤ Nat.card d.Ystar := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : h.V .i1 ⊔ zpowers h.t ≤ d.Ystar := le_sup_right
  obtain ⟨w, hw, hwt⟩ := d.exists_mem_W2_comm_ne_one
  have hlt : h.V .i1 ⊔ zpowers h.t < d.Ystar := by
    refine lt_of_le_of_ne hle fun heq => hwt ?_
    have hwY : w ∈ d.Ystar := mem_sup_left hw
    rw [← heq] at hwY
    have hwC := h.V1_sup_t_le_C hwY
    exact commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_singleton_iff.1 hwC)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 d.isPGroup_Ystar
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 h.isPGroup_V1_sup_t
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hk, hm] at hdvd
  have hmk : m ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  have hne : m ≠ k := by
    rintro rfl
    exact hlt.ne (Subgroup.eq_of_le_of_card_ge hle (by rw [hk, hm]))
  rw [hk, hm, ← pow_succ']
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem exists_le_normalizer_A : ∃ S : Subgroup G, S ≤ normalizer (d.A : Set G) ∧
    IsPGroup 2 S ∧ d.A ≤ S ∧ Nat.card d.Ystar * Nat.card d.A ≤ Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := d.D ⊔ d.Ystar with hX
  have hXN : X ≤ normalizer (d.D : Set G) := sup_le le_normalizer d.Ystar_le_normalizer_D
  have htA : h.t ∈ normalizer (d.A : Set G) := d.J_le_normalizer_A h.t_mem_J
  have hAt2 : IsPGroup 2 (d.A ⊔ zpowers h.t : Subgroup G) :=
    d.isPGroup_A.to_sup_of_normal_left' h.isPGroup_zpowers_t (zpowers_le.2 htA)
  have hAtX : d.A ⊔ zpowers h.t ≤ X :=
    sup_le (d.A_le_D.trans le_sup_left) (zpowers_le.2 (mem_sup_right d.t_mem_Ystar))
  obtain ⟨S₁, hS₁, hAtS₁⟩ := exists_isSylowOf_ge hAtX hAt2
  have htS₁ : h.t ∈ S₁ := hAtS₁ (mem_sup_right (mem_zpowers _))
  have hS₁D : S₁ ⊓ d.D = d.A := d.eq_A_of_le_D inf_le_right (hS₁.isPGroup.to_le inf_le_left)
    (le_inf (le_sup_left.trans hAtS₁) d.A_le_D)
    (mem_normalizer_inf (le_normalizer htS₁) (d.J_le_normalizer_D h.t_mem_J))
  have hS₁N : S₁ ≤ normalizer (d.A : Set G) := fun x hx => by
    rw [← hS₁D]
    exact mem_normalizer_inf (le_normalizer hx) (hXN (hS₁.le hx))
  refine ⟨S₁, hS₁N, hS₁.isPGroup, le_sup_left.trans hAtS₁, ?_⟩
  obtain ⟨S₂, hS₂, hYS₂⟩ := exists_isSylowOf_ge (le_sup_right : d.Ystar ≤ X) d.isPGroup_Ystar
  obtain ⟨k, hkX, hk⟩ := exists_conj_le_of_isSylowOf hS₂ hS₁.le hS₁.isPGroup
  have hcardA : Nat.card d.A ≤ Nat.card (S₂ ⊓ d.D : Subgroup G) := by
    let f : d.A → (S₂ ⊓ d.D : Subgroup G) := fun a => ⟨k⁻¹ * a * k,
      hk a (le_sup_left.trans hAtS₁ a.2), by
        have := (mem_normalizer_iff.1 (inv_mem (hXN hkX)) (a : G)).1 (d.A_le_D a.2)
        rwa [inv_inv] at this⟩
    have hf : Function.Injective f := fun a b hab => by
      have : k⁻¹ * (a : G) * k = k⁻¹ * (b : G) * k := congrArg Subtype.val hab
      exact Subtype.ext (mul_left_cancel (mul_right_cancel this))
    exact Nat.card_le_card_of_injective f hf
  have hYN : d.Ystar ≤ normalizer ((S₂ ⊓ d.D : Subgroup G) : Set G) := fun y hy =>
    mem_normalizer_inf (le_normalizer (hYS₂ hy)) (d.Ystar_le_normalizer_D hy)
  have hcard := card_sup_mul_card_inf_of_le_normalizer' hYN
  have hinf : (S₂ ⊓ d.D) ⊓ d.Ystar = ⊥ := by
    rw [eq_bot_iff, ← d.Ystar_inf_D]
    exact fun x hx => ⟨hx.2, hx.1.2⟩
  rw [hinf, Subgroup.card_bot, mul_one] at hcard
  have hle : (S₂ ⊓ d.D) ⊔ d.Ystar ≤ S₂ := sup_le inf_le_left hYS₂
  calc Nat.card d.Ystar * Nat.card d.A ≤ Nat.card d.Ystar * Nat.card (S₂ ⊓ d.D : Subgroup G) :=
        Nat.mul_le_mul_left _ hcardA
    _ = Nat.card ((S₂ ⊓ d.D) ⊔ d.Ystar : Subgroup G) := by rw [hcard, mul_comm]
    _ ≤ Nat.card S₂ := Subgroup.card_le_of_le hle
    _ = Nat.card S₁ := by rw [hS₂.card_eq, hS₁.card_eq]

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4

module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootW12Tools
public import CFSG.LocalAnalysis.EvenBN.TwoF4.GMSWrapper

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

section Generic

variable {X : Type*} [Group X]

theorem mem_normalizer_commutator_of {A B : Subgroup X} {g : X}
    (hA : g ∈ normalizer (A : Set X)) (hB : g ∈ normalizer (B : Set X)) :
    g ∈ normalizer ((⁅A, B⁆ : Subgroup X) : Set X) := by
  have key : ∀ {g : X}, g ∈ normalizer (A : Set X) → g ∈ normalizer (B : Set X) →
      ∀ x ∈ ⁅A, B⁆, g * x * g⁻¹ ∈ ⁅A, B⁆ := by
    intro g hA hB x hx
    have hA' : A.map (MulAut.conj g).toMonoidHom ≤ A := by
      rintro _ ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.1 hA y).1 hy
    have hB' : B.map (MulAut.conj g).toMonoidHom ≤ B := by
      rintro _ ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.1 hB y).1 hy
    have hx' : (MulAut.conj g).toMonoidHom x ∈ ⁅A, B⁆.map (MulAut.conj g).toMonoidHom :=
      mem_map_of_mem _ hx
    rw [map_commutator] at hx'
    exact commutator_mono hA' hB' hx'
  refine mem_normalizer_iff.2 fun x => ⟨key hA hB x, fun hx => ?_⟩
  have := key (inv_mem hA) (inv_mem hB) _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem commutatorElement_mul_left_eq (x y r : X) :
    ⁅x * y, r⁆ = x * ⁅y, r⁆ * x⁻¹ * ⁅x, r⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mul_right_eq (z x y : X) :
    ⁅z, x * y⁆ = ⁅z, x⁆ * (x * ⁅z, y⁆ * x⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_conj_of_commute {z b x : X} (hzb : z * b = b * z) :
    ⁅z, b * x * b⁻¹⁆ = b * ⁅z, x⁆ * b⁻¹ := by
  have e2 : b⁻¹ * z⁻¹ = z⁻¹ * b⁻¹ := by rw [← mul_inv_rev, hzb, mul_inv_rev]
  simp only [commutatorElement_def]
  calc z * (b * x * b⁻¹) * z⁻¹ * (b * x * b⁻¹)⁻¹ =
      (z * b) * x * (b⁻¹ * z⁻¹) * b * x⁻¹ * b⁻¹ := by group
    _ = (b * z) * x * (z⁻¹ * b⁻¹) * b * x⁻¹ * b⁻¹ := by rw [hzb, e2]
    _ = b * (z * x * z⁻¹ * x⁻¹) * b⁻¹ := by group

theorem mem_normalizer_inf {A B : Subgroup X} {g : X} (hA : g ∈ normalizer (A : Set X))
    (hB : g ∈ normalizer (B : Set X)) : g ∈ normalizer ((A ⊓ B : Subgroup X) : Set X) :=
  mem_normalizer_iff.2 fun x => ⟨fun hx => ⟨(mem_normalizer_iff.1 hA x).1 hx.1,
    (mem_normalizer_iff.1 hB x).1 hx.2⟩, fun hx => ⟨(mem_normalizer_iff.1 hA x).2 hx.1,
    (mem_normalizer_iff.1 hB x).2 hx.2⟩⟩

theorem mem_normalizer_centralizer {A : Subgroup X} {g : X} (hA : g ∈ normalizer (A : Set X)) :
    g ∈ normalizer ((centralizer (A : Set X) : Subgroup X) : Set X) := by
  have key : ∀ {g : X}, g ∈ normalizer (A : Set X) → ∀ x ∈ centralizer (A : Set X),
      g * x * g⁻¹ ∈ centralizer (A : Set X) := by
    intro g hA x hx
    refine mem_centralizer_iff.2 fun a ha => ?_
    have ha' : g⁻¹ * a * g ∈ A := by
      have := (mem_normalizer_iff.1 (inv_mem hA) a).1 ha
      rwa [inv_inv] at this
    have hc := mem_centralizer_iff.1 hx _ ha'
    calc a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [hc]
      _ = g * x * g⁻¹ * a := by group
  refine mem_normalizer_iff.2 fun x => ⟨key hA x, fun hx => ?_⟩
  have := key (inv_mem hA) _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

end Generic

variable {G : Type} [Group G] [Finite G]

structure LevelOneData (h : Setup G) where
  Y : Subgroup G
  isPGroup_Y : IsPGroup 2 Y
  RT_le_Y : h.RT ≤ Y
  Y_le_X : Y ≤ h.X
  conj_mem_Y : ∀ n ∈ normalizer (h.E : Set G), ∀ y ∈ Y, n * y * n⁻¹ ∈ Y
  Y_inf_C : Y ⊓ h.C = h.RT
  Y_le_centralizer_V12 : Y ≤ centralizer (h.V .i12 : Set G)
  exists_conj_t : ∀ v ∈ h.V .i12, ∃ y ∈ Y, y * h.t * y⁻¹ = h.t * v
  W : Subgroup G
  W_le_CH : W ≤ h.CH .i5
  bender : BenderSylow W h.t (h.V .i5) W
  le_W_sup : ∀ S : Subgroup G, S ≤ h.CH .i5 → IsPGroup 2 S → h.V .i5 ⊔ zpowers h.t ≤ S →
    S ≤ W ⊔ zpowers h.t
  conj_mem_W : ∀ x ∈ h.CH .i5, x * h.t = h.t * x → x ∈ normalizer (h.V .i5 : Set G) →
    ∀ w ∈ W, x * w * x⁻¹ ∈ W

theorem Setup.nonempty_levelOneData (h : Setup G)
    (hGMS : GMSK.GMSSuzukiSharpKRankOneStatement)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) : Nonempty (LevelOneData h) := by
  obtain ⟨Y, hY2, hRTY, hYX, hYN, hYC, hYV, hYt⟩ := h.sec3_3
  obtain ⟨W, hWC, hB, hWu, hWn⟩ := h.sec3_2_five hGMS hK
  exact ⟨⟨Y, hY2, hRTY, hYX, hYN, hYC, hYV, hYt, W, hWC, hB, hWu, hWn⟩⟩

theorem Setup.zIn_V (h : Setup G) {i : Idx} (hi : i.isSz = true) :
    zIn (h.V i) = h.V i.center := by
  have hA : ((rootV h.K h.a i).subgroupOf (F4.reeGamma h.K h.a)).map
      (F4.reeGamma h.K h.a).subtype = rootV h.K h.a i := by
    rw [subgroupOf_map_subtype, inf_eq_left.2 (rootV_le_reeGamma h.card_K i)]
  have h1 : (zIn ((rootV h.K h.a i).subgroupOf (F4.reeGamma h.K h.a))).map
      (F4.reeGamma h.K h.a).subtype = rootV h.K h.a i.center := by
    rw [map_zIn (F4.reeGamma h.K h.a).subtype_injective, hA, zIn_rootV h.one_le_a h.card_K hi]
  have h2 : zIn ((rootV h.K h.a i).subgroupOf (F4.reeGamma h.K h.a)) =
      (rootV h.K h.a i.center).subgroupOf (F4.reeGamma h.K h.a) := by
    rw [← h1]
    exact (comap_map_eq_self_of_injective (F4.reeGamma h.K h.a).subtype_injective _).symm
  rw [Setup.V, Setup.V, Setup.pull, Setup.pull, ← map_zIn h.emb_injective, h2]

theorem Setup.V5_le_R (h : Setup G) : h.V .i5 ≤ h.R := h.pull_mono (rootV_le_rootJoin (by decide))

theorem Setup.t_mem_RT (h : Setup G) : h.t ∈ h.RT := mem_sup_right (mem_zpowers _)

theorem Setup.RT_le_C (h : Setup G) : h.RT ≤ h.C :=
  sup_le (h.R_le_L.trans h.L_le_C) h.zpowers_t_le_C

theorem Setup.CE_le_N0 (h : Setup G) : h.CE ≤ normalizer (h.E : Set G) := by
  rw [h.CE_eq_centralizer]
  exact Subgroup.centralizer_le_normalizer (h.E : Set G)

theorem Setup.P_le_N0 (h : Setup G) : h.P ≤ normalizer (h.E : Set G) :=
  h.P_le_CE.trans h.CE_le_N0

theorem Setup.R_le_N0 (h : Setup G) : h.R ≤ normalizer (h.E : Set G) := h.R_le_P.trans h.P_le_N0

theorem Setup.zIn_V5 (h : Setup G) : zIn (h.V .i5) = h.V .i12 := h.zIn_V (i := .i5) rfl

theorem Setup.RT_le_normalizer_R (h : Setup G) : h.RT ≤ normalizer (h.R : Set G) :=
  sup_le (le_normalizer) ((zpowers_le (H := normalizer (h.R : Set G))).2
    (Subgroup.centralizer_le_normalizer (h.R : Set G) (mem_centralizer_iff.2 fun _ hx =>
      (h.mul_t_comm (h.R_le_L hx)))))

theorem Setup.mul_t_not_mem_R (h : Setup G) {r : G} (hr : r ∈ h.R) : r * h.t ∉ h.R := fun hrt =>
  h.t_not_mem_L (h.R_le_L (by
    have := mul_mem (inv_mem hr) hrt
    rwa [inv_mul_cancel_left] at this))

theorem Setup.mul_mem_R_iff (h : Setup G) {x y : G} (hx : x ∈ h.RT) (hy : y ∈ h.RT) :
    x * y ∈ h.R ↔ (x ∈ h.R ↔ y ∈ h.R) := by
  obtain ⟨a, ha, hxa⟩ := h.exists_mul_of_mem_sup_zpowers_t h.R_le_L hx
  obtain ⟨b, hb, hyb⟩ := h.exists_mul_of_mem_sup_zpowers_t h.R_le_L hy
  rcases hxa with rfl | rfl
  · rcases hyb with rfl | rfl
    · simp [mul_mem ha hb, ha, hb]
    · have hab : x * (b * h.t) ∉ h.R := by
        rw [← mul_assoc]
        exact h.mul_t_not_mem_R (mul_mem ha hb)
      simp [hab, ha, h.mul_t_not_mem_R hb]
  · rcases hyb with rfl | rfl
    · have hab : a * h.t * y ∉ h.R := by
        rw [mul_assoc, ← h.mul_t_comm (h.R_le_L hb), ← mul_assoc]
        exact h.mul_t_not_mem_R (mul_mem ha hb)
      simp [hab, hb, h.mul_t_not_mem_R ha]
    · have e : a * h.t * (b * h.t) = a * b := by
        rw [mul_assoc a, ← mul_assoc h.t b, ← h.mul_t_comm (h.R_le_L hb), mul_assoc b, h.t_mul_t,
          mul_one]
      rw [e]
      simp [mul_mem ha hb, h.mul_t_not_mem_R ha, h.mul_t_not_mem_R hb]

theorem Setup.R₁_mul_self (h : Setup G) {x : G} (hx : x ∈ h.R₁) : x * x = 1 := by
  rw [← h.elt_r1Elt_r1c hx, ← h.elt_mul' (h.R1_le_reeGamma (r1Elt_mem _))
    (h.R1_le_reeGamma (r1Elt_mem _)), r1Elt_mul_self h.card_K, h.elt_one']

theorem Setup.R₁_comm (h : Setup G) {x y : G} (hx : x ∈ h.R₁) (hy : y ∈ h.R₁) :
    x * y = y * x := by
  rw [← h.elt_r1Elt_r1c hx, ← h.elt_r1Elt_r1c hy,
    h.commute_elt_iff (h.R1_le_reeGamma (r1Elt_mem _)) (h.R1_le_reeGamma (r1Elt_mem _))]
  exact commute_of_mem_R1 h.card_K (r1Elt_mem _) (r1Elt_mem _)

theorem Setup.V12_le_R₁ (h : Setup G) : h.V .i12 ≤ h.R₁ :=
  h.pull_mono (rootV_le_rootJoin (by decide))

theorem Setup.R₁_ne_bot (h : Setup G) : h.R₁ ≠ ⊥ := fun hb => h.e_ne_one (by
  have := h.V12_le_R₁ h.e_f_mem_orderOf.1
  rwa [hb, mem_bot] at this)

theorem Setup.conj_V12_eq (h : Setup G) {x v : G} (hx : x ∈ h.P) (hv : v ∈ h.V .i12) :
    x * v * x⁻¹ = v := by
  rw [← mem_centralizer_iff.1 (h.P_le_centralizer_V12 hx) v hv, mul_inv_cancel_right]

theorem Setup.conj_V5_eq (h : Setup G) {b v : G} (hb : b ∈ h.Ht .i5) (hv : v ∈ h.V .i5) :
    b * v * b⁻¹ = v := by
  rw [mem_centralizer_iff.1 (h.V_le_centralizer_Ht rfl hv) b hb, mul_inv_cancel_right]

theorem Setup.mem_R₁_of_mem_R_of_commute (h : Setup G) {r : G} (hr : r ∈ h.R)
    (hrc : r ∈ centralizer ((h.R₁ ⊔ h.V .i5 : Subgroup G) : Set G)) : r ∈ h.R₁ := by
  have hrc1 : r ∈ centralizer (h.R₁ : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hrc
  have hr' : r ∈ h.V .i5 ⊔ h.R₁ := by
    rw [← h.R_inf_centralizer_R₁]
    exact mem_inf.2 ⟨hr, hrc1⟩
  have hR5 : h.R₁ ≤ centralizer (h.V .i5 : Set G) :=
    le_centralizer_iff.1 (le_sup_left.trans (h.R_inf_centralizer_R₁ ▸ inf_le_right))
  obtain ⟨v, hv, x, hx, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hR5 hr'
  refine mul_mem (h.V12_le_R₁ ?_) hx
  rw [← h.zIn_V5]
  refine mem_zIn.mpr ⟨fun w hw => ?_, hv⟩
  have h1 := mem_centralizer_iff.1 hrc w (mem_sup_right hw)
  have h2 := mem_centralizer_iff.1 (hR5 hx) w hw
  calc w * v = w * (v * x) * x⁻¹ := by group
    _ = v * x * w * x⁻¹ := by rw [h1]
    _ = v * (x * w) * x⁻¹ := by group
    _ = v * (w * x) * x⁻¹ := by rw [h2]
    _ = v * w := by group

theorem Setup.H_comm (h : Setup G) {x y : G} (hx : x ∈ h.H) (hy : y ∈ h.H) : x * y = y * x := by
  obtain ⟨g, hg, hgΓ, rfl⟩ := h.mem_pull_iff_elt.1 hx
  obtain ⟨g', hg', hg'Γ, rfl⟩ := h.mem_pull_iff_elt.1 hy
  exact (h.commute_elt_iff hgΓ hg'Γ).2 (torusH_mul_comm hg hg')

theorem Setup.V12_comm (h : Setup G) {v w : G} (hv : v ∈ h.V .i12) (hw : w ∈ h.V .i12) :
    v * w = w * v := h.R₁_comm (h.V12_le_R₁ hv) (h.V12_le_R₁ hw)

theorem Setup.elt_rootElt_mul_of_isSz (h : Setup G) {k : Idx} (hk : k.isSz = true) (c e : h.K) :
    h.elt (rootElt h.K h.a k c) * h.elt (rootElt h.K h.a k e) =
      h.elt (rootElt h.K h.a k (c + e)) *
        h.elt (rootElt h.K h.a k.center (largeReeSigma h.a c * e)) := by
  have hcz : k.center.isCenter = true ∧ k.center.fourIdx = k.fourIdx := by
    cases k <;> simp_all [Idx.isSz, Idx.center, Idx.isCenter, Idx.fourIdx]
  have hm : rootElt h.K h.a k c * rootElt h.K h.a k e =
      rootElt h.K h.a k (c + e) * rootElt h.K h.a k.center (largeReeSigma h.a c * e) := by
    rw [(rootElt_eq_coord k c).1 hk, (rootElt_eq_coord k e).1 hk, (rootElt_eq_coord k _).1 hk,
      (rootElt_eq_coord _ _).2.1 hcz.1, hcz.2, fourCoordG_mul_fourCoordG h.card_K,
      ← fourCoordG_eq_mul h.card_K, zero_add, zero_add]
  have hΓ : ∀ j c, rootElt h.K h.a j c ∈ F4.reeGamma h.K h.a := fun j c =>
    rootV_le_reeGamma h.card_K j (rootElt_mem_rootV _ _)
  rw [← h.elt_mul' (hΓ _ _) (hΓ _ _), ← h.elt_mul' (hΓ _ _) (hΓ _ _), hm]

theorem Setup.elt_rootElt_mem_R (h : Setup G) {k : Idx}
    (hk : k ∈ ({.i3, .i4, .i5, .i6, .i7, .i9, .i10} : Finset Idx)) (c : h.K) :
    h.elt (rootElt h.K h.a k c) ∈ h.R :=
  h.pull_mono (rootV_le_rootJoin hk) (h.elt_rootElt_mem_V k c)

theorem Setup.elt_rootElt_mem_R₁ (h : Setup G) {k : Idx} (hk : k.isR1 = true) (c : h.K) :
    h.elt (rootElt h.K h.a k c) ∈ h.R₁ :=
  (h.elt_mem_pull (rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _))).2
    (rootElt_mem_R1 hk c)

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

@[expose] def W12 : Subgroup G := zIn d.W

theorem t_mem_Y : h.t ∈ d.Y := d.RT_le_Y h.t_mem_RT

theorem R_le_Y : h.R ≤ d.Y := (le_sup_left : h.R ≤ h.RT).trans d.RT_le_Y

theorem Y_le_N0 : d.Y ≤ normalizer (h.E : Set G) := d.Y_le_X.trans h.X_le_N₀

theorem Y_le_normalizer_RT : d.Y ≤ normalizer (h.RT : Set G) := fun _ hy =>
  h.mem_normalizer_RT (d.Y_le_N0 hy)

theorem N0_le_normalizer_Y : normalizer (h.E : Set G) ≤ normalizer (d.Y : Set G) := fun n hn =>
  mem_normalizer_iff.2 fun y => ⟨d.conj_mem_Y n hn y, fun hy => by
    have := d.conj_mem_Y n⁻¹ (inv_mem hn) _ hy
    rwa [show n⁻¹ * (n * y * n⁻¹) * n⁻¹⁻¹ = y by group] at this⟩

theorem W12_le_W : d.W12 ≤ d.W := zIn_le _

theorem W12_le_CH : d.W12 ≤ h.CH .i5 := d.W12_le_W.trans d.W_le_CH

theorem V12_le_W12 : h.V .i12 ≤ d.W12 := by
  rw [← h.zIn_V5]
  exact d.bender.zIn_V_le

theorem conj_t_mem_W12 {z : G} (hz : z ∈ d.W12) : h.t⁻¹ * z * h.t ∈ d.W12 :=
  (mem_normalizer_iff''.mp (mem_normalizer_zIn d.bender.mem_normalizer) z).mp hz

theorem W12_comm {z z' : G} (hz : z ∈ d.W12) (hz' : z' ∈ d.W12) : z * z' = z' * z :=
  ((mem_zIn.mp hz).1 z' (d.W12_le_W hz')).symm

theorem W12_comm_W {z w : G} (hz : z ∈ d.W12) (hw : w ∈ d.W) : z * w = w * z :=
  ((mem_zIn.mp hz).1 w hw).symm

theorem W12_comm_V5 {z v : G} (hz : z ∈ d.W12) (hv : v ∈ h.V .i5) : z * v = v * z :=
  d.W12_comm_W hz (d.bender.le hv)

theorem W12_mul_self {z : G} (hz : z ∈ d.W12) : z * z = 1 := d.bender.center_mul_self z hz

theorem kappa_mem {z : G} (hz : z ∈ d.W12) : z⁻¹ * (h.t⁻¹ * z * h.t) ∈ h.V .i12 := by
  rw [← h.zIn_V5]
  exact d.bender.center_comm_mem z hz

theorem conj_t_eq {z : G} (hz : z ∈ d.W12) :
    z * h.t * z⁻¹ = h.t * (z⁻¹ * (h.t⁻¹ * z * h.t)) := by
  have hc : (h.t⁻¹ * z * h.t) * z⁻¹ = z⁻¹ * (h.t⁻¹ * z * h.t) :=
    d.W12_comm (d.conj_t_mem_W12 hz) (inv_mem hz)
  calc z * h.t * z⁻¹ = h.t * ((h.t⁻¹ * z * h.t) * z⁻¹) := by group
    _ = h.t * (z⁻¹ * (h.t⁻¹ * z * h.t)) := by rw [hc]

theorem exists_W12_conj {v : G} (hv : v ∈ h.V .i12) :
    ∃ z ∈ d.W12, z * h.t * z⁻¹ = h.t * v := by
  rw [← h.zIn_V5] at hv
  obtain ⟨z, hz, rfl⟩ := d.bender.exists_center_comm v hv
  exact ⟨z, hz, d.conj_t_eq hz⟩

theorem mem_V5_of_commute {w : G} (hw : w ∈ d.W) (hwt : w * h.t = h.t * w) : w ∈ h.V .i5 := by
  rw [← d.bender.inf_centralizer]
  exact mem_inf.2 ⟨hw, mem_centralizer_singleton_iff.2 hwt⟩

theorem mem_V12_of_commute {z : G} (hz : z ∈ d.W12) (hzt : z * h.t = h.t * z) :
    z ∈ h.V .i12 := by
  rw [← h.zIn_V5]
  exact mem_zIn.mpr ⟨fun v hv => (d.W12_comm_V5 hz hv).symm, d.mem_V5_of_commute
    (d.W12_le_W hz) hzt⟩

theorem t_not_mem_W : h.t ∉ d.W := d.bender.not_mem_W

theorem exists_mem_CH5_conj {v : G} (hv : v ∈ h.V .i12) :
    ∃ y ∈ d.Y, y ∈ h.CH .i5 ∧ y * h.t * y⁻¹ = h.t * v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHY : h.Ht .i5 ≤ normalizer (d.Y : Set G) := fun b hb =>
    d.N0_le_normalizer_Y (h.Ht5_le_normalizer_E hb)
  have hbt : ∀ b ∈ h.Ht .i5, b ∈ normalizer ((zpowers h.t : Subgroup G) : Set G) := by
    intro b hb
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun y hy => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (show Commute h.t b from
      (mem_centralizer_iff.1 (h.t_mem_CH .i5) b hb).symm) k).eq
  have hHRT : h.Ht .i5 ≤ normalizer (h.RT : Set G) := fun b hb =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _
      (mem_inf.2 ⟨h.H_le_normalizer_R (h.Ht_le_H .i5 hb), hbt b hb⟩)
  obtain ⟨y₀, hy₀Y, hy₀⟩ := d.exists_conj_t v hv
  let _ : MulDistribMulAction (h.Ht .i5) d.Y :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (h.Ht .i5) d.Y hHY
  set N : Subgroup d.Y := h.RT.subgroupOf d.Y with hNdef
  have : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer d.Y_le_normalizer_RT
  have hNinv : CFSG.IsInvariant (h.Ht .i5) d.Y N :=
    CFSG.SolvableHall.isInvariant_of_forall_smul_mem fun b z hz => by
      rw [mem_subgroupOf] at hz ⊢
      exact (mem_normalizer_iff.1 (hHRT b.2) z).1 hz
  have hN2 : IsPGroup 2 N :=
    (d.isPGroup_Y.to_le d.RT_le_Y).of_equiv (subgroupOfEquivOfLe d.RT_le_Y).symm
  have hNsolv : Group.IsSolvable N := by
    have := hN2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card (h.Ht .i5)) (Nat.card N) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hN2
    rw [hk, h.card_Ht]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2
      (Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one))
  have hcoset : ∀ b : h.Ht .i5, (⟨y₀, hy₀Y⟩ : d.Y)⁻¹ * (b • (⟨y₀, hy₀Y⟩ : d.Y)) ∈ N := by
    intro b
    have hsmul : ((b • (⟨y₀, hy₀Y⟩ : d.Y) : d.Y) : G) = (b : G) * y₀ * (b : G)⁻¹ := rfl
    rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hsmul]
    have hbt' : (b : G) * h.t = h.t * b := mem_centralizer_iff.1 (h.t_mem_CH .i5) b b.2
    have hbv : (b : G) * v = v * b := by
      have hv5 : v ∈ h.CH .i5 := h.V_le_centralizer_Ht rfl (h.V_center_le .i5 hv)
      exact mem_centralizer_iff.1 hv5 b b.2
    have hmemY : y₀⁻¹ * ((b : G) * y₀ * (b : G)⁻¹) ∈ d.Y :=
      mul_mem (inv_mem hy₀Y) ((mem_normalizer_iff.1 (hHY b.2) y₀).1 hy₀Y)
    rw [← d.Y_inf_C]
    refine mem_inf.2 ⟨hmemY, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : (b : G) * y₀ * (b : G)⁻¹ * h.t * ((b : G) * y₀ * (b : G)⁻¹)⁻¹ = h.t * v := by
      have hbt'' : (b : G)⁻¹ * h.t * b = h.t := by
        calc (b : G)⁻¹ * h.t * b = (b : G)⁻¹ * (h.t * b) := by group
          _ = (b : G)⁻¹ * (b * h.t) := by rw [hbt']
          _ = h.t := by group
      calc (b : G) * y₀ * (b : G)⁻¹ * h.t * ((b : G) * y₀ * (b : G)⁻¹)⁻¹ =
          (b : G) * (y₀ * ((b : G)⁻¹ * h.t * b) * y₀⁻¹) * (b : G)⁻¹ := by group
        _ = (b : G) * (h.t * v) * (b : G)⁻¹ := by rw [hbt'', hy₀]
        _ = h.t * v := by
          rw [show (b : G) * (h.t * v) * (b : G)⁻¹ = (b * h.t) * v * (b : G)⁻¹ by group, hbt',
            mul_assoc h.t, hbv]
          group
    calc y₀⁻¹ * ((b : G) * y₀ * (b : G)⁻¹) * h.t =
        y₀⁻¹ * ((b : G) * y₀ * (b : G)⁻¹ * h.t * ((b : G) * y₀ * (b : G)⁻¹)⁻¹) *
          ((b : G) * y₀ * (b : G)⁻¹) := by group
      _ = y₀⁻¹ * (h.t * v) * ((b : G) * y₀ * (b : G)⁻¹) := by rw [h1]
      _ = h.t * (y₀⁻¹ * ((b : G) * y₀ * (b : G)⁻¹)) := by
        rw [← hy₀]
        group
  obtain ⟨c, hc, hcN⟩ := CFSG.SolvableHall.exists_fixed_of_coset_fixed N hNinv hNsolv hcop
    ⟨y₀, hy₀Y⟩ hcoset
  have hcH : (c : G) ∈ h.CH .i5 := by
    refine mem_centralizer_iff.2 fun b hb => ?_
    have := congrArg Subtype.val (hc ⟨b, hb⟩)
    have hsmul : (((⟨b, hb⟩ : h.Ht .i5) • c : d.Y) : G) = b * (c : G) * b⁻¹ := rfl
    rw [hsmul] at this
    calc b * (c : G) = b * c * b⁻¹ * b := by group
      _ = c * b := by rw [this]
  have hm : ((c : G))⁻¹ * y₀ ∈ h.C := by
    have h1 : ((c⁻¹ * ⟨y₀, hy₀Y⟩ : d.Y) : G) ∈ h.RT := mem_subgroupOf.1 hcN
    rw [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    exact h.RT_le_C h1
  have hmt := mem_centralizer_singleton_iff.1 hm
  refine ⟨c, c.2, hcH, ?_⟩
  have e : y₀ * h.t * y₀⁻¹ = (c : G) * h.t * (c : G)⁻¹ := by
    calc y₀ * h.t * y₀⁻¹ =
        (c : G) * (((c : G)⁻¹ * y₀) * h.t) * ((c : G)⁻¹ * y₀)⁻¹ * (c : G)⁻¹ := by group
      _ = (c : G) * (h.t * ((c : G)⁻¹ * y₀)) * ((c : G)⁻¹ * y₀)⁻¹ * (c : G)⁻¹ := by rw [hmt]
      _ = (c : G) * h.t * (c : G)⁻¹ := by group
  rw [← e, hy₀]

theorem W12_le_Y : d.W12 ≤ d.Y := by
  intro z₀ hz₀
  obtain ⟨y, hyY, hyH, hyt⟩ := d.exists_mem_CH5_conj (d.kappa_mem hz₀)
  have hS : d.Y ⊓ h.CH .i5 ≤ d.W ⊔ zpowers h.t := d.le_W_sup _ inf_le_right
    (d.isPGroup_Y.to_le inf_le_left)
    (le_inf (sup_le (h.V5_le_R.trans d.R_le_Y) ((zpowers_le (H := d.Y)).2 d.t_mem_Y))
      (sup_le (h.V_le_centralizer_Ht rfl) ((zpowers_le (H := h.CH .i5)).2 (h.t_mem_CH .i5))))
  obtain ⟨w, hw, hyw⟩ : ∃ w ∈ d.W, w ∈ d.Y ∧ w * h.t * w⁻¹ = h.t * (z₀⁻¹ * (h.t⁻¹ * z₀ * h.t)) := by
    obtain ⟨w, hw, hyw | hyw⟩ := exists_eq_or_eq_mul_of_mem_sup h.t_mul_t d.bender.mem_normalizer
      (hS (mem_inf.2 ⟨hyY, hyH⟩))
    · rw [hyw] at hyY hyt
      exact ⟨w, hw, hyY, hyt⟩
    · rw [hyw] at hyY hyt
      refine ⟨w, hw, ?_, ?_⟩
      · have := mul_mem hyY (inv_mem d.t_mem_Y)
        rwa [mul_inv_cancel_right] at this
      · have e : w * h.t * w⁻¹ = (w * h.t) * h.t * (w * h.t)⁻¹ := by
          rw [mul_inv_rev, h.t_inv, mul_assoc (w * h.t) h.t, ← mul_assoc h.t h.t, h.t_mul_t,
            one_mul]
        rw [e]
        exact hyt
  obtain ⟨hwY, hwt⟩ := hyw
  rw [← d.conj_t_eq hz₀] at hwt
  have hwz : w⁻¹ * z₀ ∈ h.V .i5 := by
    refine d.mem_V5_of_commute (mul_mem (inv_mem hw) (d.W12_le_W hz₀)) ?_
    calc w⁻¹ * z₀ * h.t = w⁻¹ * (z₀ * h.t * z₀⁻¹) * z₀ := by group
      _ = w⁻¹ * (w * h.t * w⁻¹) * z₀ := by rw [hwt]
      _ = h.t * (w⁻¹ * z₀) := by group
  have e : z₀ = w * (w⁻¹ * z₀) := by group
  rw [e]
  exact mul_mem hwY (h.V5_le_R.trans d.R_le_Y hwz)

theorem exists_mul_of_mem_Y {y : G} (hy : y ∈ d.Y) : ∃ z ∈ d.W12, ∃ x ∈ h.RT, y = z * x := by
  obtain ⟨v, hv, hyt⟩ := h.conj_mem_tV12 (d.Y_le_N0 hy) (one_mem (h.V .i12))
  rw [mul_one] at hyt
  obtain ⟨z, hz, hzt⟩ := d.exists_W12_conj hv
  refine ⟨z, hz, z⁻¹ * y, ?_, by group⟩
  rw [← d.Y_inf_C]
  refine mem_inf.2 ⟨mul_mem (inv_mem (d.W12_le_Y hz)) hy, mem_centralizer_singleton_iff.2 ?_⟩
  calc z⁻¹ * y * h.t = z⁻¹ * (y * h.t * y⁻¹) * y := by group
    _ = z⁻¹ * (z * h.t * z⁻¹) * y := by rw [hyt, hzt]
    _ = h.t * (z⁻¹ * y) := by group

theorem W12_comm_H5 {z b : G} (hz : z ∈ d.W12) (hb : b ∈ h.Ht .i5) : z * b = b * z :=
  (mem_centralizer_iff.1 (d.W12_le_CH hz) b hb).symm

theorem comm_mem_R {z : G} (hz : z ∈ d.W12) {r : G} (hr : r ∈ h.R) : ⁅z, r⁆ ∈ h.R := by
  classical
  have hzN : z ∈ normalizer (h.RT : Set G) := d.Y_le_normalizer_RT (d.W12_le_Y hz)
  have hRT : ∀ x ∈ h.R, ⁅z, x⁆ ∈ h.RT := fun x hx => by
    rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.1 hzN x).1 (le_sup_left (a := h.R) hx))
      (inv_mem (le_sup_left (a := h.R) hx))
  let f : G → G := fun x => if ⁅z, x⁆ ∈ h.R then 1 else h.t
  have hf1 : ∀ x, f x = 1 → ⁅z, x⁆ ∈ h.R := fun x hx => by
    by_contra hn
    simp only [f, ite_eq_right hn] at hx
    exact h.t_ne_one hx
  have key := h.eq_one_of_H5_invariant_R (f := f)
    (fun x hx y hy => by
      have hxy : ⁅z, x * y⁆ ∈ h.R ↔ (⁅z, x⁆ ∈ h.R ↔ ⁅z, y⁆ ∈ h.R) := by
        rw [commutatorElement_mul_right_eq,
          h.mul_mem_R_iff (hRT x hx) (mul_mem (mul_mem (le_sup_left (a := h.R) hx) (hRT y hy))
            (inv_mem (le_sup_left (a := h.R) hx)))]
        rw [show (x * ⁅z, y⁆ * x⁻¹ ∈ h.R ↔ ⁅z, y⁆ ∈ h.R) from
          (mem_normalizer_iff.1 (le_normalizer hx) _).symm]
      simp only [f]
      by_cases h1 : ⁅z, x⁆ ∈ h.R <;> by_cases h2 : ⁅z, y⁆ ∈ h.R <;>
        simp [h1, h2, hxy, h.t_mul_t])
    (fun b hb x hx => by
      simp only [f]
      rw [commutatorElement_conj_of_commute (d.W12_comm_H5 hz hb),
        show (b * ⁅z, x⁆ * b⁻¹ ∈ h.R ↔ ⁅z, x⁆ ∈ h.R) from
          (mem_normalizer_iff.1 (h.H_le_normalizer_R (h.Ht_le_H .i5 hb)) _).symm])
    (fun v hv => by
      simp only [f]
      rw [commutatorElement_eq_one_iff_mul_comm.2 (d.W12_comm_V5 hz hv), ite_eq_left (one_mem _)])
  exact hf1 r (key r hr)

theorem W12_le_normalizer_R : d.W12 ≤ normalizer (h.R : Set G) := fun z hz =>
  mem_normalizer_iff.2 fun r => ⟨fun hr => by
    have e : z * r * z⁻¹ = ⁅z, r⁆ * r := by simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem (d.comm_mem_R hz hr) hr, fun hr => by
    have e : r = ⁅z⁻¹, z * r * z⁻¹⁆ * (z * r * z⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem (d.comm_mem_R (inv_mem hz) hr) hr⟩

include d in
theorem N0_le_normalizer_R : normalizer (h.E : Set G) ≤ normalizer (h.R : Set G) := by
  have hY : d.Y ≤ normalizer (h.R : Set G) := fun y hy => by
    obtain ⟨z, hz, x, hx, rfl⟩ := d.exists_mul_of_mem_Y hy
    exact mul_mem (d.W12_le_normalizer_R hz) (h.RT_le_normalizer_R hx)
  intro n hn
  obtain ⟨v, hv, hnt⟩ := h.conj_mem_tV12 hn (one_mem (h.V .i12))
  rw [mul_one] at hnt
  obtain ⟨y, hy, hyt⟩ := d.exists_conj_t v hv
  have hmC : y⁻¹ * n ∈ h.C := mem_centralizer_singleton_iff.2 (by
    calc y⁻¹ * n * h.t = y⁻¹ * (n * h.t * n⁻¹) * n := by group
      _ = y⁻¹ * (y * h.t * y⁻¹) * n := by rw [hnt, hyt]
      _ = h.t * (y⁻¹ * n) := by group)
  have hmN : y⁻¹ * n ∈ normalizer (h.E : Set G) := mul_mem (inv_mem (d.Y_le_N0 hy)) hn
  have hmR : y⁻¹ * n ∈ normalizer (h.R : Set G) := by
    rw [← h.RT_inf_L]
    exact mem_normalizer_inf (h.mem_normalizer_RT hmN) (h.centralizer_le_normalizer hmC)
  have e : n = y * (y⁻¹ * n) := by group
  rw [e]
  exact mul_mem (hY hy) hmR

include d in
theorem N0_le_normalizer_R₁ : normalizer (h.E : Set G) ≤ normalizer (h.R₁ : Set G) := by
  intro n hn
  rw [← h.commutator_R_R]
  exact mem_normalizer_commutator (d.N0_le_normalizer_R hn)

theorem commutator_R₁_Y_le : ⁅h.R₁, d.Y⁆ ≤ h.V .i12 := by
  have hN : ∀ n ∈ normalizer (h.E : Set G), n ∈ normalizer ((⁅h.R₁, d.Y⁆ : Subgroup G) : Set G) :=
    fun n hn => mem_normalizer_commutator_of (d.N0_le_normalizer_R₁ hn) (d.N0_le_normalizer_Y hn)
  refine h.le_V12_of_invariant ((commutator_le).2 fun x hx y hy => ?_)
    (fun b hb => hN b (h.H_le_N₀ hb))
    (hN _ (h.P_le_N0 (h.V_le_P .i1 (h.elt_rootElt_mem_V .i1 1))))
    (hN _ (h.CE_le_N0 (h.N1_le_CE h.r_mem_N_s_mem_N.1)))
    (commutator_ne_of_isPGroup d.isPGroup_Y (h.R₁_le_R.trans d.R_le_Y) h.R₁_ne_bot)
  have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact mul_mem hx ((mem_normalizer_iff.1 (d.N0_le_normalizer_R₁ (d.Y_le_N0 hy)) _).1
    (inv_mem hx))

theorem comm_R₁_mem_V12 {z : G} (hz : z ∈ d.W12) {x : G} (hx : x ∈ h.R₁) :
    ⁅z, x⁆ ∈ h.V .i12 := by
  rw [← commutatorElement_inv]
  exact inv_mem (d.commutator_R₁_Y_le (commutator_mem_commutator hx (d.W12_le_Y hz)))

theorem W12_le_centralizer_R₁ : d.W12 ≤ centralizer (h.R₁ : Set G) := by
  intro z hz
  have key := h.eq_one_of_H5_invariant_R₁ (f := fun x => ⁅z, x⁆)
    (fun x hx y hy => by
      rw [commutatorElement_mul_right_eq,
        h.conj_V12_eq (h.R₁_le_R.trans h.R_le_P hx) (d.comm_R₁_mem_V12 hz hy)])
    (fun b hb x hx => by
      rw [commutatorElement_conj_of_commute (d.W12_comm_H5 hz hb),
        h.conj_V5_eq hb (h.V_center_le .i5 (d.comm_R₁_mem_V12 hz hx))])
    (fun v hv => commutatorElement_eq_one_iff_mul_comm.2 (d.W12_comm hz (d.V12_le_W12 hv)))
  exact mem_centralizer_iff.2 fun x hx => (commutatorElement_eq_one_iff_mul_comm.1 (key x hx)).symm

theorem W12_comm_R₁ {z x : G} (hz : z ∈ d.W12) (hx : x ∈ h.R₁) : z * x = x * z :=
  (mem_centralizer_iff.1 (d.W12_le_centralizer_R₁ hz) x hx).symm

@[expose] def A0 : Subgroup G := h.R₁ ⊔ d.W12

theorem exists_mul_of_mem_A0 {x : G} (hx : x ∈ d.A0) : ∃ r ∈ h.R₁, ∃ z ∈ d.W12, x = r * z :=
  exists_mul_of_mem_sup_of_le_centralizer (fun _ hz => d.W12_le_centralizer_R₁ hz) hx

theorem mem_R₁_of_mem_A0_of_commute {x : G} (hx : x ∈ d.A0) (hxt : x * h.t = h.t * x) :
    x ∈ h.R₁ := by
  obtain ⟨r, hr, z, hz, rfl⟩ := d.exists_mul_of_mem_A0 hx
  have hrt := h.mul_t_comm (h.pull_le_L _ hr)
  have hzt : z * h.t = h.t * z := by
    have : r * (z * h.t) = r * (h.t * z) := by
      calc r * (z * h.t) = r * z * h.t := (mul_assoc _ _ _).symm
        _ = h.t * (r * z) := hxt
        _ = (h.t * r) * z := (mul_assoc _ _ _).symm
        _ = (r * h.t) * z := by rw [hrt]
        _ = r * (h.t * z) := mul_assoc _ _ _
    exact mul_left_cancel this
  exact mul_mem hr (h.V12_le_R₁ (d.mem_V12_of_commute hz hzt))

theorem t_not_mem_A0 : h.t ∉ d.A0 := fun ht =>
  h.t_not_mem_L (h.pull_le_L _ (d.mem_R₁_of_mem_A0_of_commute ht rfl))

theorem A0_mul_self {x : G} (hx : x ∈ d.A0) : x * x = 1 := by
  obtain ⟨r, hr, z, hz, rfl⟩ := d.exists_mul_of_mem_A0 hx
  calc r * z * (r * z) = r * (z * r) * z := by group
    _ = r * (r * z) * z := by rw [d.W12_comm_R₁ hz hr]
    _ = (r * r) * (z * z) := by group
    _ = 1 := by rw [h.R₁_mul_self hr, d.W12_mul_self hz, one_mul]

theorem mem_R₁_of_mem_R_of_mem_A0 {x : G} (hxR : x ∈ h.R) (hx : x ∈ d.A0) : x ∈ h.R₁ :=
  d.mem_R₁_of_mem_A0_of_commute hx (h.mul_t_comm (h.R_le_L hxR))

theorem mem_A0_of_mem_Y_of_commute {y : G} (hy : y ∈ d.Y)
    (hyc : y ∈ centralizer ((h.R₁ ⊔ h.V .i5 : Subgroup G) : Set G)) :
    y ∈ d.A0 ∨ y * h.t ∈ d.A0 := by
  obtain ⟨z, hz, x, hx, rfl⟩ := d.exists_mul_of_mem_Y hy
  have hzc : z ∈ centralizer ((h.R₁ ⊔ h.V .i5 : Subgroup G) : Set G) := by
    have : h.R₁ ⊔ h.V .i5 ≤ centralizer ({z} : Set G) := sup_le
      (fun x hx => mem_centralizer_singleton_iff.2 (d.W12_comm_R₁ hz hx).symm)
      (fun v hv => mem_centralizer_singleton_iff.2 (d.W12_comm_V5 hz hv).symm)
    exact mem_centralizer_iff.2 fun w hw => mem_centralizer_singleton_iff.1 (this hw)
  have hxc : x ∈ centralizer ((h.R₁ ⊔ h.V .i5 : Subgroup G) : Set G) := by
    have := mul_mem (inv_mem hzc) hyc
    rwa [inv_mul_cancel_left] at this
  have htc : h.t ∈ centralizer ((h.R₁ ⊔ h.V .i5 : Subgroup G) : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 (sup_le (h.pull_le_L _) (h.pull_le_L _))) h.htL
  obtain ⟨r, hr, rfl | rfl⟩ := h.exists_mul_of_mem_sup_zpowers_t h.R_le_L hx
  · exact Or.inl (mul_mem (mem_sup_right hz) (mem_sup_left (h.mem_R₁_of_mem_R_of_commute hr hxc)))
  · have hrc : r ∈ centralizer ((h.R₁ ⊔ h.V .i5 : Subgroup G) : Set G) := by
      have := mul_mem hxc (inv_mem htc)
      rwa [mul_inv_cancel_right] at this
    refine Or.inr ?_
    rw [mul_assoc, mul_assoc, h.t_mul_t, mul_one]
    exact mul_mem (mem_sup_right hz) (mem_sup_left (h.mem_R₁_of_mem_R_of_commute hr hrc))

theorem conj_mem_A0 {n : G} (hn : n ∈ normalizer (h.E : Set G)) {a : G} (ha : a ∈ d.A0) :
    n * a * n⁻¹ ∈ d.A0 := by
  have hN5 : n ∈ normalizer ((h.R₁ ⊔ h.V .i5 : Subgroup G) : Set G) := by
    rw [sup_comm, ← h.R_inf_centralizer_R₁]
    exact mem_normalizer_inf (d.N0_le_normalizer_R hn)
      (mem_normalizer_centralizer (d.N0_le_normalizer_R₁ hn))
  have hac : a ∈ centralizer ((h.R₁ ⊔ h.V .i5 : Subgroup G) : Set G) := by
    obtain ⟨r, hr, z, hz, rfl⟩ := d.exists_mul_of_mem_A0 ha
    refine mul_mem ?_ ?_
    · have : h.R₁ ⊔ h.V .i5 ≤ centralizer ({r} : Set G) := sup_le
        (fun x hx => mem_centralizer_singleton_iff.2 (h.R₁_comm hx hr))
        (fun v hv => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1
          (le_centralizer_iff.1 (le_sup_left.trans (h.R_inf_centralizer_R₁ ▸ inf_le_right)) hr)
            v hv))
      exact mem_centralizer_iff.2 fun w hw => mem_centralizer_singleton_iff.1 (this hw)
    · have : h.R₁ ⊔ h.V .i5 ≤ centralizer ({z} : Set G) := sup_le
        (fun x hx => mem_centralizer_singleton_iff.2 (d.W12_comm_R₁ hz hx).symm)
        (fun v hv => mem_centralizer_singleton_iff.2 (d.W12_comm_V5 hz hv).symm)
      exact mem_centralizer_iff.2 fun w hw => mem_centralizer_singleton_iff.1 (this hw)
  have haY : a ∈ d.Y := by
    obtain ⟨r, hr, z, hz, rfl⟩ := d.exists_mul_of_mem_A0 ha
    exact mul_mem (h.R₁_le_R.trans d.R_le_Y hr) (d.W12_le_Y hz)
  set x := n * a * n⁻¹ with hxdef
  have hxY : x ∈ d.Y := d.conj_mem_Y n hn a haY
  have hxc : x ∈ centralizer ((h.R₁ ⊔ h.V .i5 : Subgroup G) : Set G) :=
    (mem_normalizer_iff.1 (mem_normalizer_centralizer hN5) a).1 hac
  have hx2 : x * x = 1 := by
    rw [hxdef, show n * a * n⁻¹ * (n * a * n⁻¹) = n * (a * a) * n⁻¹ by group, d.A0_mul_self ha]
    group
  rcases d.mem_A0_of_mem_Y_of_commute hxY hxc with hx | hxt
  · exact hx
  · exfalso
    set a' := x * h.t with ha'
    have hxa : x = a' * h.t := by rw [ha', mul_assoc, h.t_mul_t, mul_one]
    have ha't : a' * h.t = h.t * a' := by
      have h1 : a' * h.t * (a' * h.t) = 1 := by rw [← hxa]; exact hx2
      have h2 : a' * a' = 1 := d.A0_mul_self hxt
      calc a' * h.t = a' * h.t * (a' * h.t) * (h.t⁻¹ * a'⁻¹) := by group
        _ = h.t⁻¹ * a'⁻¹ := by rw [h1, one_mul]
        _ = h.t * a' := by rw [h.t_inv, inv_eq_of_mul_eq_one_right h2]
    have ha'R : a' ∈ h.R₁ := d.mem_R₁_of_mem_A0_of_commute hxt ha't
    obtain ⟨v, hv, hnt⟩ := h.conj_mem_tV12 (inv_mem hn) (one_mem (h.V .i12))
    rw [mul_one, inv_inv] at hnt
    have hae : a = (n⁻¹ * a' * n) * (h.t * v) := by
      rw [← hnt, show n⁻¹ * a' * n * (n⁻¹ * h.t * n) = n⁻¹ * (a' * h.t) * n by group, ← hxa,
        hxdef]
      group
    have hr' : n⁻¹ * a' * n ∈ h.R₁ := by
      have := (mem_normalizer_iff.1 (inv_mem (d.N0_le_normalizer_R₁ hn)) a').1 ha'R
      rwa [inv_inv] at this
    apply d.t_not_mem_A0
    have e : h.t = (n⁻¹ * a' * n)⁻¹ * a * v⁻¹ := by
      rw [hae]
      group
    rw [e]
    exact mul_mem (mul_mem (mem_sup_left (inv_mem hr')) ha) (mem_sup_left (inv_mem
      (h.V12_le_R₁ hv)))

theorem comm_R_mem_R₁ {z : G} (hz : z ∈ d.W12) {r : G} (hr : r ∈ h.R) : ⁅z, r⁆ ∈ h.R₁ := by
  refine d.mem_R₁_of_mem_R_of_mem_A0 (d.comm_mem_R hz hr) ?_
  have e : ⁅z, r⁆ = z * (r * z⁻¹ * r⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact mul_mem (mem_sup_right hz) (d.conj_mem_A0 (h.R_le_N0 hr) (mem_sup_right (inv_mem hz)))

theorem exists_of_mem_Y_CH5 {y : G} (hy : y ∈ d.Y) (hyH : y ∈ h.CH .i5) :
    ∃ w ∈ h.V .i5 ⊔ d.W12, y = w ∨ y = w * h.t := by
  have hS : d.Y ⊓ h.CH .i5 ≤ d.W ⊔ zpowers h.t := d.le_W_sup _ inf_le_right
    (d.isPGroup_Y.to_le inf_le_left)
    (le_inf (sup_le (h.V5_le_R.trans d.R_le_Y) ((zpowers_le (H := d.Y)).2 d.t_mem_Y))
      (sup_le (h.V_le_centralizer_Ht rfl) ((zpowers_le (H := h.CH .i5)).2 (h.t_mem_CH .i5))))
  obtain ⟨w, hw, hyw⟩ := exists_eq_or_eq_mul_of_mem_sup h.t_mul_t d.bender.mem_normalizer
    (hS (mem_inf.2 ⟨hy, hyH⟩))
  have hwY : w ∈ d.Y := by
    rcases hyw with rfl | rfl
    · exact hy
    · have := mul_mem hy (inv_mem d.t_mem_Y)
      rwa [mul_inv_cancel_right] at this
  obtain ⟨v, hv, hwt⟩ := h.conj_mem_tV12 (d.Y_le_N0 hwY) (one_mem (h.V .i12))
  rw [mul_one] at hwt
  have hmem : w⁻¹ ∈ h.V .i5 ⊔ zIn d.W := d.bender.mem_sup_zIn_of_conj_mem (inv_mem hw) (by
    rw [inv_inv, hwt]
    exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (h.V_center_le .i5 hv)))
  have hw' := inv_mem hmem
  rw [inv_inv] at hw'
  exact ⟨w, hw', hyw⟩

theorem mem_W12_of_mem_sup_of_commute {w : G} (hw : w ∈ h.V .i5 ⊔ d.W12)
    (hwc : ∀ v ∈ h.V .i5, v * w = w * v) : w ∈ d.W12 := by
  obtain ⟨v, hv, z, hz, rfl⟩ := exists_mul_of_mem_sup_zIn d.bender.le hw
  refine mul_mem (d.V12_le_W12 ?_) hz
  rw [← h.zIn_V5]
  refine mem_zIn.mpr ⟨fun u hu => ?_, hv⟩
  have h1 := hwc u hu
  have h2 := d.W12_comm_V5 hz hu
  calc u * v = u * (v * z) * z⁻¹ := by group
    _ = v * z * u * z⁻¹ := by rw [h1]
    _ = v * (z * u) * z⁻¹ := by group
    _ = v * (u * z) * z⁻¹ := by rw [h2]
    _ = v * u := by group

theorem conj_mem_W12_of {b : G} (hbC : b ∈ h.C) (hbV : b ∈ normalizer (h.V .i12 : Set G))
    {z : G} (hz : z ∈ d.W12) (hcase : b * z * b⁻¹ ∈ d.W12 ∨ b * z * b⁻¹ * h.t ∈ d.W12) :
    b * z * b⁻¹ ∈ d.W12 := by
  rcases hcase with h1 | h1
  · exact h1
  · exfalso
    set x := b * z * b⁻¹ with hxdef
    set z' := x * h.t with hz'
    have hx2 : x * x = 1 := by
      rw [hxdef, show b * z * b⁻¹ * (b * z * b⁻¹) = b * (z * z) * b⁻¹ by group,
        d.W12_mul_self hz]
      group
    have hxz : x = z' * h.t := by rw [hz', mul_assoc, h.t_mul_t, mul_one]
    have hz't : z' * h.t = h.t * z' := by
      have e1 : z' * h.t * (z' * h.t) = 1 := by rw [← hxz]; exact hx2
      have e2 : z' * z' = 1 := d.W12_mul_self h1
      calc z' * h.t = z' * h.t * (z' * h.t) * (h.t⁻¹ * z'⁻¹) := by group
        _ = h.t⁻¹ * z'⁻¹ := by rw [e1, one_mul]
        _ = h.t * z' := by rw [h.t_inv, inv_eq_of_mul_eq_one_right e2]
    have hz'V : z' ∈ h.V .i12 := d.mem_V12_of_commute h1 hz't
    have hbt : b⁻¹ * h.t * b = h.t := by
      rw [mul_assoc, ← mem_centralizer_singleton_iff.1 hbC]
      group
    have hz_eq : z = (b⁻¹ * z' * b) * h.t := by
      calc z = b⁻¹ * x * b := by rw [hxdef]; group
        _ = b⁻¹ * (z' * h.t) * b := by rw [← hxz]
        _ = (b⁻¹ * z' * b) * (b⁻¹ * h.t * b) := by group
        _ = (b⁻¹ * z' * b) * h.t := by rw [hbt]
    have hv : b⁻¹ * z' * b ∈ h.V .i12 := by
      have := (mem_normalizer_iff.1 (inv_mem hbV) z').1 hz'V
      rwa [inv_inv] at this
    apply d.t_not_mem_W
    have e : h.t = (b⁻¹ * z' * b)⁻¹ * z := by
      rw [hz_eq]
      group
    rw [e]
    exact mul_mem (inv_mem (d.W12_le_W (d.V12_le_W12 hv))) (d.W12_le_W hz)

theorem conj_H_mem_W12 {b : G} (hb : b ∈ h.H) {z : G} (hz : z ∈ d.W12) :
    b * z * b⁻¹ ∈ d.W12 := by
  have hbL := h.H_le_L hb
  refine d.conj_mem_W12_of (h.L_le_C hbL) (h.H_le_normalizer_V .i12 hb) hz ?_
  have hxY : b * z * b⁻¹ ∈ d.Y := d.conj_mem_Y b (h.H_le_N₀ hb) z (d.W12_le_Y hz)
  have hxH : b * z * b⁻¹ ∈ h.CH .i5 := by
    refine mem_centralizer_iff.2 fun c hc => ?_
    have hcb := h.H_comm (h.Ht_le_H .i5 hc) hb
    have hcz := (d.W12_comm_H5 hz hc).symm
    have hcb' : c * b⁻¹ = b⁻¹ * c := by
      calc c * b⁻¹ = b⁻¹ * (b * c) * b⁻¹ := by group
        _ = b⁻¹ * (c * b) * b⁻¹ := by rw [hcb]
        _ = b⁻¹ * c := by group
    calc c * (b * z * b⁻¹) = (c * b) * z * b⁻¹ := by group
      _ = (b * c) * z * b⁻¹ := by rw [hcb]
      _ = b * (c * z) * b⁻¹ := by group
      _ = b * (z * c) * b⁻¹ := by rw [hcz]
      _ = b * z * (c * b⁻¹) := by group
      _ = b * z * (b⁻¹ * c) := by rw [hcb']
      _ = b * z * b⁻¹ * c := by group
  have hxV : ∀ v ∈ h.V .i5, v * (b * z * b⁻¹) = (b * z * b⁻¹) * v := by
    intro v hv
    have hv' : b⁻¹ * v * b ∈ h.V .i5 := by
      have := (mem_normalizer_iff.1 (inv_mem (h.H_le_normalizer_V .i5 hb)) v).1 hv
      rwa [inv_inv] at this
    have hc := d.W12_comm_V5 hz hv'
    calc v * (b * z * b⁻¹) = b * ((b⁻¹ * v * b) * z) * b⁻¹ := by group
      _ = b * (z * (b⁻¹ * v * b)) * b⁻¹ := by rw [hc]
      _ = b * z * b⁻¹ * v := by group
  obtain ⟨w, hw, hxw | hxw⟩ := d.exists_of_mem_Y_CH5 hxY hxH
  · left
    rw [hxw] at hxV ⊢
    exact d.mem_W12_of_mem_sup_of_commute hw hxV
  · right
    have htV : ∀ v ∈ h.V .i5, v * h.t = h.t * v := fun v hv =>
      h.mul_t_comm (h.pull_le_L _ hv)
    have hwV : ∀ v ∈ h.V .i5, v * w = w * v := by
      intro v hv
      have h1 := hxV v hv
      rw [hxw] at h1
      have h2 := htV v hv
      calc v * w = v * (w * h.t) * h.t⁻¹ := by group
        _ = w * h.t * v * h.t⁻¹ := by rw [h1]
        _ = w * (h.t * v) * h.t⁻¹ := by group
        _ = w * (v * h.t) * h.t⁻¹ := by rw [h2]
        _ = w * v := by group
    rw [hxw, mul_assoc, h.t_mul_t, mul_one]
    exact d.mem_W12_of_mem_sup_of_commute hw hwV

@[expose] def zc (c : h.K) : G := (d.exists_W12_conj (h.elt_rootElt_mem_V .i12 c)).choose

theorem zc_mem (c : h.K) : d.zc c ∈ d.W12 :=
  (d.exists_W12_conj (h.elt_rootElt_mem_V .i12 c)).choose_spec.1

theorem zc_conj (c : h.K) :
    d.zc c * h.t * (d.zc c)⁻¹ = h.t * h.elt (rootElt h.K h.a .i12 c) :=
  (d.exists_W12_conj (h.elt_rootElt_mem_V .i12 c)).choose_spec.2

theorem mul_inv_mem_V12_of_conj_eq {z z' : G} (hz : z ∈ d.W12) (hz' : z' ∈ d.W12)
    (he : z * h.t * z⁻¹ = z' * h.t * z'⁻¹) : z * z'⁻¹ ∈ h.V .i12 := by
  have hzz : z'⁻¹ * z ∈ h.V .i12 := by
    refine d.mem_V12_of_commute (mul_mem (inv_mem hz') hz) ?_
    calc z'⁻¹ * z * h.t = z'⁻¹ * (z * h.t * z⁻¹) * z := by group
      _ = z'⁻¹ * (z' * h.t * z'⁻¹) * z := by rw [he]
      _ = h.t * (z'⁻¹ * z) := by group
  rw [show z * z'⁻¹ = z'⁻¹ * z by
    rw [d.W12_comm hz (inv_mem hz')]]
  exact hzz

theorem zc_add (c e : h.K) : d.zc (c + e) * (d.zc c * d.zc e)⁻¹ ∈ h.V .i12 := by
  refine d.mul_inv_mem_V12_of_conj_eq (d.zc_mem _) (mul_mem (d.zc_mem c) (d.zc_mem e)) ?_
  have hv := h.elt_rootElt_mem_V .i12 e
  have hc : d.zc c * h.elt (rootElt h.K h.a .i12 e) = h.elt (rootElt h.K h.a .i12 e) * d.zc c :=
    d.W12_comm (d.zc_mem c) (d.V12_le_W12 hv)
  have hΓ : ∀ c, rootElt h.K h.a .i12 c ∈ F4.reeGamma h.K h.a := fun c =>
    rootV_le_reeGamma h.card_K _ (rootElt_mem_rootV _ _)
  calc d.zc (c + e) * h.t * (d.zc (c + e))⁻¹ = h.t * h.elt (rootElt h.K h.a .i12 (c + e)) :=
        d.zc_conj _
    _ = h.t * h.elt (rootElt h.K h.a .i12 c) * h.elt (rootElt h.K h.a .i12 e) := by
        rw [rootElt_add h.card_K rfl, h.elt_mul' (hΓ _) (hΓ _), mul_assoc]
    _ = d.zc c * h.t * (d.zc c)⁻¹ * h.elt (rootElt h.K h.a .i12 e) := by rw [d.zc_conj]
    _ = d.zc c * (h.t * h.elt (rootElt h.K h.a .i12 e)) * (d.zc c)⁻¹ := by
        rw [show d.zc c * (h.t * h.elt (rootElt h.K h.a .i12 e)) * (d.zc c)⁻¹ =
          d.zc c * h.t * (d.zc c)⁻¹ * (d.zc c * h.elt (rootElt h.K h.a .i12 e) * (d.zc c)⁻¹)
          by group, hc, mul_inv_cancel_right]
    _ = d.zc c * (d.zc e * h.t * (d.zc e)⁻¹) * (d.zc c)⁻¹ := by rw [d.zc_conj]
    _ = d.zc c * d.zc e * h.t * (d.zc c * d.zc e)⁻¹ := by group

theorem zc_torus (t : h.Kˣ × h.Kˣ) (c : h.K) :
    h.elt (torusPair h.a t) * d.zc c * (h.elt (torusPair h.a t))⁻¹ *
      (d.zc ((rootChar h.K h.a .i12 t : h.K) * c))⁻¹ ∈ h.V .i12 := by
  have hb := h.elt_torusPair_mem_H t
  refine d.mul_inv_mem_V12_of_conj_eq (d.conj_H_mem_W12 hb (d.zc_mem c)) (d.zc_mem _) ?_
  have hbt : h.elt (torusPair h.a t) * h.t = h.t * h.elt (torusPair h.a t) :=
    h.mul_t_comm (h.H_le_L hb)
  rw [d.zc_conj, ← h.elt_torusPair_conj_rootElt]
  calc h.elt (torusPair h.a t) * d.zc c * (h.elt (torusPair h.a t))⁻¹ * h.t *
      (h.elt (torusPair h.a t) * d.zc c * (h.elt (torusPair h.a t))⁻¹)⁻¹ =
      h.elt (torusPair h.a t) * (d.zc c * ((h.elt (torusPair h.a t))⁻¹ * h.t *
        h.elt (torusPair h.a t)) * (d.zc c)⁻¹) * (h.elt (torusPair h.a t))⁻¹ := by group
    _ = h.elt (torusPair h.a t) * (d.zc c * h.t * (d.zc c)⁻¹) * (h.elt (torusPair h.a t))⁻¹ := by
        rw [show (h.elt (torusPair h.a t))⁻¹ * h.t * h.elt (torusPair h.a t) = h.t by
          rw [mul_assoc, ← hbt]; group]
    _ = h.elt (torusPair h.a t) * (h.t * h.elt (rootElt h.K h.a .i12 c)) *
        (h.elt (torusPair h.a t))⁻¹ := by rw [d.zc_conj]
    _ = h.t * (h.elt (torusPair h.a t) * h.elt (rootElt h.K h.a .i12 c) *
        (h.elt (torusPair h.a t))⁻¹) := by rw [← mul_assoc, hbt]; group

theorem comm_mul_V12 {y : G} (hy : y ∈ h.R) {v : G} (hv : v ∈ h.V .i12) {z : G}
    (hz : z ∈ d.W12) : ⁅y, v * z⁆ = ⁅y, z⁆ := by
  have h1 : ⁅y, v⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
    (mem_centralizer_iff.1 (h.P_le_centralizer_V12 (h.R_le_P hy)) v hv).symm
  have hyz : ⁅y, z⁆ ∈ h.R₁ := by
    rw [← commutatorElement_inv]
    exact inv_mem (d.comm_R_mem_R₁ hz hy)
  rw [commutatorElement_mul_right_eq, h1, one_mul,
    show v * ⁅y, z⁆ * v⁻¹ = ⁅y, z⁆ by rw [h.R₁_comm (h.V12_le_R₁ hv) hyz, mul_inv_cancel_right]]

theorem comm_mul_W12 {y : G} (hy : y ∈ h.R) {z z' : G} (hz : z ∈ d.W12) (hz' : z' ∈ d.W12) :
    ⁅y, z * z'⁆ = ⁅y, z⁆ * ⁅y, z'⁆ := by
  have hyz : ⁅y, z'⁆ ∈ h.R₁ := by
    rw [← commutatorElement_inv]
    exact inv_mem (d.comm_R_mem_R₁ hz' hy)
  rw [commutatorElement_mul_right_eq,
    show z * ⁅y, z'⁆ * z⁻¹ = ⁅y, z'⁆ by rw [d.W12_comm_R₁ hz hyz, mul_inv_cancel_right]]

theorem r1c_comm_eq_zero_left {k : Idx} (hk : k ∈ ({.i3, .i4, .i6, .i7} : Finset Idx))
    (s : h.K) {z : G} (hz : z ∈ d.W12) {l : Idx} (hl : l.isR1 = true) (hl12 : l ≠ .i12)
    (hb : Idx.brace k .i12 ≠ Idx.brace k l) :
    h.r1c ⁅h.elt (rootElt h.K h.a k s), z⁆ l = 0 := by
  have hkR : k ∈ ({.i3, .i4, .i5, .i6, .i7, .i9, .i10} : Finset Idx) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢
    rcases hk with rfl | rfl | rfl | rfl <;> simp
  have hkc : k.isCenter = false := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> rfl
  set y := h.elt (rootElt h.K h.a k s) with hydef
  have hyR : y ∈ h.R := h.elt_rootElt_mem_R hkR s
  have hR₁ : ∀ {z : G}, z ∈ d.W12 → ⁅y, z⁆ ∈ h.R₁ := fun hz => by
    rw [← commutatorElement_inv]
    exact inv_mem (d.comm_R_mem_R₁ hz hyR)
  have key := h.r1c_eq_zero_of_brace_ne (i := k) (j := .i12) hkc (Ψ := fun c => ⁅y, d.zc c⁆)
    (fun c e l hl hl12 => by
      have e1 : d.zc (c + e) = (d.zc (c + e) * (d.zc c * d.zc e)⁻¹) * (d.zc c * d.zc e) := by
        group
      show h.r1c ⁅y, d.zc (c + e)⁆ l = h.r1c ⁅y, d.zc c⁆ l + h.r1c ⁅y, d.zc e⁆ l
      rw [e1, d.comm_mul_V12 hyR (d.zc_add c e) (mul_mem (d.zc_mem c) (d.zc_mem e)),
        d.comm_mul_W12 hyR (d.zc_mem c) (d.zc_mem e),
        h.r1c_mul (hR₁ (d.zc_mem c)) (hR₁ (d.zc_mem e)) hl])
    (fun t ht c l hl hl12 => by
      show h.r1c ⁅y, d.zc ((rootChar h.K h.a .i12 t : h.K) * c)⁆ l =
        (rootChar h.K h.a l t : h.K) * h.r1c ⁅y, d.zc c⁆ l
      have hb' : h.elt (torusPair h.a t) ∈ h.Ht k := (h.elt_torusPair_mem_Ht_iff t).2 ht
      have hyb : y * h.elt (torusPair h.a t) = h.elt (torusPair h.a t) * y :=
        (mem_centralizer_iff.1 (h.V_le_centralizer_Ht hkc (h.elt_rootElt_mem_V k s)) _ hb').symm
      set b := h.elt (torusPair h.a t)
      have e1 : d.zc ((rootChar h.K h.a .i12 t : h.K) * c) =
          (b * d.zc c * b⁻¹ * (d.zc ((rootChar h.K h.a .i12 t : h.K) * c))⁻¹)⁻¹ *
            (b * d.zc c * b⁻¹) := by group
      rw [e1, d.comm_mul_V12 hyR (inv_mem (d.zc_torus t c))
        (d.conj_H_mem_W12 (h.elt_torusPair_mem_H t) (d.zc_mem c)),
        commutatorElement_conj_of_commute hyb, h.r1c_torus (hR₁ (d.zc_mem c)) t hl])
    hl hl12 hb
  obtain ⟨c, hc⟩ := h.exists_eq_elt_rootElt (i := .i12) rfl (d.kappa_mem hz)
  have hzc : z * (d.zc c)⁻¹ ∈ h.V .i12 := by
    refine d.mul_inv_mem_V12_of_conj_eq hz (d.zc_mem c) ?_
    rw [d.conj_t_eq hz, hc, d.zc_conj]
  have e1 : z = (z * (d.zc c)⁻¹) * d.zc c := by group
  rw [e1, d.comm_mul_V12 hyR hzc (d.zc_mem c)]
  exact key c

theorem r1c_comm_eq_zero_right {k : Idx} (hk : k = .i4 ∨ k = .i6) {z : G} (hz : z ∈ d.W12)
    (s : h.K) {l : Idx} (hl : l.isR1 = true) (hl12 : l ≠ .i12)
    (hb : Idx.brace .i5 k ≠ Idx.brace .i5 l) :
    h.r1c ⁅z, h.elt (rootElt h.K h.a k s)⁆ l = 0 := by
  have hkR : k ∈ ({.i3, .i4, .i5, .i6, .i7, .i9, .i10} : Finset Idx) := by
    rcases hk with rfl | rfl <;> decide
  have hks : k.isSz = true := by rcases hk with rfl | rfl <;> rfl
  have hkc : k.center.isR1 = true := by rcases hk with rfl | rfl <;> rfl
  have hR₁ : ∀ c, ⁅z, h.elt (rootElt h.K h.a k c)⁆ ∈ h.R₁ := fun c =>
    d.comm_R_mem_R₁ hz (h.elt_rootElt_mem_R hkR c)
  refine h.r1c_eq_zero_of_brace_ne (i := .i5) (j := k) rfl
    (Ψ := fun c => ⁅z, h.elt (rootElt h.K h.a k c)⁆) (fun c e l hl hl12 => ?_)
    (fun t ht c l hl hl12 => ?_) hl hl12 hb s
  · show h.r1c ⁅z, h.elt (rootElt h.K h.a k (c + e))⁆ l =
      h.r1c ⁅z, h.elt (rootElt h.K h.a k c)⁆ l + h.r1c ⁅z, h.elt (rootElt h.K h.a k e)⁆ l
    have h1 : ⁅z, h.elt (rootElt h.K h.a k c) * h.elt (rootElt h.K h.a k e)⁆ =
        ⁅z, h.elt (rootElt h.K h.a k (c + e))⁆ := by
      rw [h.elt_rootElt_mul_of_isSz hks, commutatorElement_mul_right_eq,
        commutatorElement_eq_one_iff_mul_comm.2 (d.W12_comm_R₁ hz (h.elt_rootElt_mem_R₁ hkc _)),
        mul_one, mul_inv_cancel, mul_one]
    have hconj : h.elt (rootElt h.K h.a k c) * ⁅z, h.elt (rootElt h.K h.a k e)⁆ *
        (h.elt (rootElt h.K h.a k c))⁻¹ ∈ h.R₁ :=
      (mem_normalizer_iff.1 (d.N0_le_normalizer_R₁ (h.R_le_N0 (h.elt_rootElt_mem_R hkR c))) _).1
        (hR₁ e)
    rw [← h1, commutatorElement_mul_right_eq, h.r1c_mul (hR₁ c) hconj hl,
      h.r1c_conj_R (h.elt_rootElt_mem_R hkR c) (hR₁ e) hl hl12]
  · show h.r1c ⁅z, h.elt (rootElt h.K h.a k ((rootChar h.K h.a k t : h.K) * c))⁆ l =
      (rootChar h.K h.a l t : h.K) * h.r1c ⁅z, h.elt (rootElt h.K h.a k c)⁆ l
    have hb' : h.elt (torusPair h.a t) ∈ h.Ht .i5 := (h.elt_torusPair_mem_Ht_iff t).2 ht
    rw [← h.elt_torusPair_conj_rootElt, commutatorElement_conj_of_commute
      (d.W12_comm_H5 hz hb'), h.r1c_torus (hR₁ c) t hl]

theorem r1c_comm_rootElt_eq_zero {z : G} (hz : z ∈ d.W12) {k : Idx}
    (hk : k ∈ ({.i3, .i4, .i6, .i7} : Finset Idx)) (s : h.K) {l : Idx}
    (hl : l = .i9 ∨ l = .i10) : h.r1c ⁅z, h.elt (rootElt h.K h.a k s)⁆ l = 0 := by
  have hlR : l.isR1 = true := by rcases hl with rfl | rfl <;> rfl
  have hl12 : l ≠ .i12 := by rcases hl with rfl | rfl <;> decide
  have hkR : k ∈ ({.i3, .i4, .i5, .i6, .i7, .i9, .i10} : Finset Idx) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢
    rcases hk with rfl | rfl | rfl | rfl <;> simp
  have hinv : h.r1c ⁅z, h.elt (rootElt h.K h.a k s)⁆ l =
      h.r1c ⁅h.elt (rootElt h.K h.a k s), z⁆ l := by
    rw [← commutatorElement_inv, h.r1c_inv _ hlR]
    rw [← commutatorElement_inv]
    exact inv_mem (d.comm_R_mem_R₁ hz (h.elt_rootElt_mem_R hkR s))
  have left : Idx.brace k .i12 ≠ Idx.brace k l →
      h.r1c ⁅z, h.elt (rootElt h.K h.a k s)⁆ l = 0 := fun hb => by
    rw [hinv]
    exact d.r1c_comm_eq_zero_left hk s hz hlR hl12 hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> rcases hl with rfl | rfl
  · exact left (by decide)
  · exact left (by decide)
  · exact left (by decide)
  · exact d.r1c_comm_eq_zero_right (Or.inl rfl) hz s rfl (by decide) (by decide)
  · exact d.r1c_comm_eq_zero_right (Or.inr rfl) hz s rfl (by decide) (by decide)
  · exact left (by decide)
  · exact left (by decide)
  · exact left (by decide)

theorem r1c_comm_R_eq_zero {z : G} (hz : z ∈ d.W12) {r : G} (hr : r ∈ h.R) {l : Idx}
    (hl : l = .i9 ∨ l = .i10) : h.r1c ⁅z, r⁆ l = 0 := by
  have hlR : l.isR1 = true := by rcases hl with rfl | rfl <;> rfl
  have hl12 : l ≠ .i12 := by rcases hl with rfl | rfl <;> decide
  have hRΓ := h.radR_le_reeGamma
  have hR : ∀ {x}, x ∈ radR h.K h.a → h.elt x ∈ h.R := fun hx => (h.elt_mem_pull (hRΓ hx)).2 hx
  have key : ∀ g ∈ radR h.K h.a, h.r1c ⁅z, h.elt g⁆ l = 0 := by
    intro g hg
    have hg' := hg
    rw [radR_eq_closure] at hg'
    induction hg' using closure_induction with
    | mem x hx =>
      simp only [Set.mem_iUnion, Set.mem_range] at hx
      obtain ⟨k, hk, c, rfl⟩ := hx
      have triv : ⁅z, h.elt (rootElt h.K h.a k c)⁆ = 1 →
          h.r1c ⁅z, h.elt (rootElt h.K h.a k c)⁆ l = 0 :=
        fun h1 => by rw [h1, h.r1c_one hlR]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact d.r1c_comm_rootElt_eq_zero hz (by decide) c hl
      · exact d.r1c_comm_rootElt_eq_zero hz (by decide) c hl
      · exact triv (commutatorElement_eq_one_iff_mul_comm.2 (d.W12_comm_V5 hz
          (h.elt_rootElt_mem_V _ c)))
      · exact d.r1c_comm_rootElt_eq_zero hz (by decide) c hl
      · exact d.r1c_comm_rootElt_eq_zero hz (by decide) c hl
      · exact triv (commutatorElement_eq_one_iff_mul_comm.2 (d.W12_comm_R₁ hz
          (h.elt_rootElt_mem_R₁ rfl c)))
      · exact triv (commutatorElement_eq_one_iff_mul_comm.2 (d.W12_comm_R₁ hz
          (h.elt_rootElt_mem_R₁ rfl c)))
    | one => rw [h.elt_one', commutatorElement_one_right, h.r1c_one hlR]
    | mul x y hx hy ihx ihy =>
      have hxR : x ∈ radR h.K h.a := by rw [radR_eq_closure]; exact hx
      have hyR : y ∈ radR h.K h.a := by rw [radR_eq_closure]; exact hy
      have h1 := d.comm_R_mem_R₁ hz (hR hxR)
      have h2 := d.comm_R_mem_R₁ hz (hR hyR)
      have h3 : h.elt x * ⁅z, h.elt y⁆ * (h.elt x)⁻¹ ∈ h.R₁ :=
        (mem_normalizer_iff.1 (d.N0_le_normalizer_R₁ (h.R_le_N0 (hR hxR))) _).1 h2
      rw [h.elt_mul' (hRΓ hxR) (hRΓ hyR), commutatorElement_mul_right_eq, h.r1c_mul h1 h3 hlR,
        h.r1c_conj_R (hR hxR) h2 hlR hl12, ihx hxR, ihy hyR, add_zero]
    | inv x hx ihx =>
      have hxR : x ∈ radR h.K h.a := by rw [radR_eq_closure]; exact hx
      have h1 := d.comm_R_mem_R₁ hz (hR hxR)
      have e : ⁅z, (h.elt x)⁻¹⁆ = (h.elt x)⁻¹ * ⁅z, h.elt x⁆⁻¹ * (h.elt x)⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [h.elt_inv' (hRΓ hxR), e, h.r1c_conj_R (inv_mem (hR hxR)) (inv_mem h1) hlR hl12,
        h.r1c_inv h1 hlR, ihx hxR]
  obtain ⟨g, hg, -, rfl⟩ := h.mem_pull_iff_elt.1 hr
  exact key g hg

theorem commutator_A0_R_le_rootJoin :
    ⁅d.A0, h.R⁆ ≤ h.pull (rootJoin h.K h.a {.i8, .i11, .i12}) := by
  refine (commutator_le).2 fun a ha r hr => ?_
  obtain ⟨x, hx, z, hz, rfl⟩ := d.exists_mul_of_mem_A0 ha
  have hzr : ⁅z, r⁆ ∈ h.R₁ := d.comm_R_mem_R₁ hz hr
  have hxr : ⁅x, r⁆ ∈ h.V .i12 := by
    rw [← commutatorElement_inv]
    exact inv_mem (h.comm_mem_V12 hr hx)
  have hc1 : x * ⁅z, r⁆ * x⁻¹ = ⁅z, r⁆ := by rw [h.R₁_comm hx hzr, mul_inv_cancel_right]
  rw [commutatorElement_mul_left_eq, hc1]
  refine h.mem_of_r1c_eq_zero (mul_mem hzr (h.V12_le_R₁ hxr)) fun k hk hkS => ?_
  have hk' : k = .i9 ∨ k = .i10 := by
    cases k <;> simp_all [Idx.isR1]
  have hk12 : k ≠ .i12 := by rcases hk' with rfl | rfl <;> decide
  rw [h.r1c_mul hzr (h.V12_le_R₁ hxr) hk, h.r1c_eq_zero_of_mem_V12 hxr hk hk12, add_zero]
  exact d.r1c_comm_R_eq_zero hz hr hk'

theorem _root_.CFSG.LocalAnalysis.EvenBN.TwoF4.Setup.pull_rootJoin_le_R₁ (h : Setup G) :
    h.pull (rootJoin h.K h.a {.i8, .i11, .i12}) ≤ h.R₁ :=
  h.pull_mono (rootJoin_mono (by decide))

theorem commutator_A0_R_le : ⁅d.A0, h.R⁆ ≤ h.V .i12 := by
  have hA0N : ∀ n ∈ normalizer (h.E : Set G), n ∈ normalizer (d.A0 : Set G) := fun n hn =>
    mem_normalizer_iff.2 fun a => ⟨d.conj_mem_A0 hn, fun ha => by
      have := d.conj_mem_A0 (inv_mem hn) ha
      rwa [show n⁻¹ * (n * a * n⁻¹) * n⁻¹⁻¹ = a by group] at this⟩
  have hN : ∀ n ∈ normalizer (h.E : Set G),
      n ∈ normalizer ((⁅d.A0, h.R⁆ : Subgroup G) : Set G) := fun n hn =>
    mem_normalizer_commutator_of (hA0N n hn) (d.N0_le_normalizer_R hn)
  have hQ := d.commutator_A0_R_le_rootJoin
  refine h.le_V12_of_invariant (hQ.trans h.pull_rootJoin_le_R₁) (fun b hb => hN b (h.H_le_N₀ hb))
    (hN _ (h.P_le_N0 (h.V_le_P .i1 (h.elt_rootElt_mem_V .i1 1))))
    (hN _ (h.CE_le_N0 (h.N1_le_CE h.r_mem_N_s_mem_N.1))) fun heq => ?_
  have h9 := h.elt_rootElt_mem_R₁ (k := .i9) rfl 1
  rw [← heq] at h9
  have hmem : h.elt (rootElt h.K h.a .i9 1) ∈ h.pull (rootJoin h.K h.a {.i8, .i11, .i12}) :=
    hQ h9
  have hS : ∀ l ∈ ({.i8, .i11, .i12} : Finset Idx), l.isR1 = true := by decide
  have hkS : Idx.i9 ∉ ({.i8, .i11, .i12} : Finset Idx) := by decide
  have h0 : h.r1c (h.elt (rootElt h.K h.a .i9 1)) .i9 = 0 :=
    h.r1c_eq_zero_of_mem hS hmem (k := .i9) rfl hkS
  have h1 : h.r1c (h.elt (rootElt h.K h.a .i9 1)) .i9 = 1 := by
    rw [rootElt_eq_r1Elt (k := .i9) rfl, h.r1c_elt_r1Elt _ rfl, Pi.single_eq_same]
  rw [h1] at h0
  exact one_ne_zero h0

theorem comm_R_mem_V12 {z : G} (hz : z ∈ d.W12) {r : G} (hr : r ∈ h.R) : ⁅z, r⁆ ∈ h.V .i12 :=
  d.commutator_A0_R_le (commutator_mem_commutator (mem_sup_right hz) hr)

theorem W12_le_centralizer_R : d.W12 ≤ centralizer (h.R : Set G) := by
  intro z hz
  have key := h.eq_one_of_H5_invariant_R (f := fun x => ⁅z, x⁆)
    (fun x hx y hy => by
      rw [commutatorElement_mul_right_eq, h.conj_V12_eq (h.R_le_P hx) (d.comm_R_mem_V12 hz hy)])
    (fun b hb x hx => by
      rw [commutatorElement_conj_of_commute (d.W12_comm_H5 hz hb),
        h.conj_V5_eq hb (h.V_center_le .i5 (d.comm_R_mem_V12 hz hx))])
    (fun v hv => commutatorElement_eq_one_iff_mul_comm.2 (d.W12_comm_V5 hz hv))
  exact mem_centralizer_iff.2 fun x hx => (commutatorElement_eq_one_iff_mul_comm.1 (key x hx)).symm

theorem J_le_normalizer_W12 : h.J ≤ normalizer (d.W12 : Set G) := by
  have key : ∀ j ∈ h.J, ∀ z ∈ d.W12, j * z * j⁻¹ ∈ d.W12 := by
    intro j hj z hz
    obtain ⟨hjC, hjR⟩ := mem_inf.1 hj
    have hjV : j ∈ normalizer (h.V .i12 : Set G) := by
      rw [← h.commutator_R_R₁, ← h.commutator_R_R]
      exact mem_normalizer_commutator_of hjR (mem_normalizer_commutator hjR)
    have hjT : j ∈ normalizer ((zpowers h.t : Subgroup G) : Set G) := by
      refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun y hy => ?_)
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      exact (Commute.zpow_left (show Commute h.t j from
        (mem_centralizer_singleton_iff.1 hjC).symm) k).eq
    have hjE : j ∈ normalizer (h.E : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_sup _ _ (mem_inf.2 ⟨hjT, hjV⟩)
    refine d.conj_mem_W12_of hjC hjV hz ?_
    set x := j * z * j⁻¹ with hxdef
    have hxY : x ∈ d.Y := d.conj_mem_Y j hjE z (d.W12_le_Y hz)
    have hxR : x ∈ centralizer (h.R : Set G) :=
      (mem_normalizer_iff.1 (mem_normalizer_centralizer hjR) z).1 (d.W12_le_centralizer_R hz)
    have hxc : x ∈ centralizer ((h.R₁ ⊔ h.V .i5 : Subgroup G) : Set G) :=
      centralizer_le (SetLike.coe_subset_coe.2 (sup_le h.R₁_le_R h.V5_le_R)) hxR
    have htR : h.t ∈ centralizer (h.R : Set G) :=
      centralizer_le (SetLike.coe_subset_coe.2 h.R_le_L) h.htL
    have hA : ∀ a ∈ d.A0, a ∈ centralizer (h.R : Set G) → a ∈ d.W12 := fun a ha haR => by
      obtain ⟨r, hr, w, hw, rfl⟩ := d.exists_mul_of_mem_A0 ha
      have hrR : r ∈ centralizer (h.R : Set G) := by
        have := mul_mem haR (inv_mem (d.W12_le_centralizer_R hw))
        rwa [mul_inv_cancel_right] at this
      exact mul_mem (d.V12_le_W12 (h.R₁_inf_centralizer_R_le (mem_inf.2 ⟨hr, hrR⟩))) hw
    rcases d.mem_A0_of_mem_Y_of_commute hxY hxc with h1 | h1
    · exact Or.inl (hA x h1 hxR)
    · exact Or.inr (hA _ h1 (mul_mem hxR htR))
  intro j hj
  refine mem_normalizer_iff.2 fun z => ⟨key j hj z, fun hz => ?_⟩
  have := key j⁻¹ (inv_mem hj) _ hz
  rwa [show j⁻¹ * (j * z * j⁻¹) * j⁻¹⁻¹ = z by group] at this

theorem W12_le_centralizer_N1 : d.W12 ≤ centralizer (h.N .i1 : Set G) := by
  intro z hz
  have hNJ : h.N .i1 ≤ h.J := fun n hn => mem_inf.2 ⟨h.L_le_C (h.N_le_L _ hn),
    h.N1_le_normalizer_R hn⟩
  have hNV : ∀ {n v : G}, n ∈ h.N .i1 → v ∈ h.V .i12 → n * v = v * n := fun {n v} hn hv =>
    (mem_centralizer_iff.1 (h.R_sup_N1_le_centralizer_V12 (mem_sup_right hn)) v hv).symm
  let f : G → G := fun n => n * z * n⁻¹ * z⁻¹
  have hf : ∀ {n : G}, n ∈ h.N .i1 → f n ∈ h.V .i12 := by
    intro n hn
    have hnz : n * z * n⁻¹ ∈ d.W12 := (mem_normalizer_iff.1 (d.J_le_normalizer_W12 (hNJ hn)) z).1 hz
    have hnt : n * h.t = h.t * n := mem_centralizer_singleton_iff.1 (h.L_le_C (h.N_le_L _ hn))
    have hk := d.kappa_mem hz
    have e1 : n * z * n⁻¹ * h.t * (n * z * n⁻¹)⁻¹ = z * h.t * z⁻¹ := by
      calc n * z * n⁻¹ * h.t * (n * z * n⁻¹)⁻¹ = n * (z * (n⁻¹ * h.t * n) * z⁻¹) * n⁻¹ := by
            group
        _ = n * (z * h.t * z⁻¹) * n⁻¹ := by
            rw [show n⁻¹ * h.t * n = h.t by rw [mul_assoc, ← hnt]; group]
        _ = n * (h.t * (z⁻¹ * (h.t⁻¹ * z * h.t))) * n⁻¹ := by rw [d.conj_t_eq hz]
        _ = h.t * (n * (z⁻¹ * (h.t⁻¹ * z * h.t)) * n⁻¹) := by rw [← mul_assoc n, hnt]; group
        _ = h.t * (z⁻¹ * (h.t⁻¹ * z * h.t)) := by rw [hNV hn hk, mul_inv_cancel_right]
        _ = z * h.t * z⁻¹ := (d.conj_t_eq hz).symm
    exact d.mul_inv_mem_V12_of_conj_eq hnz hz e1
  have hfm : ∀ {n m : G}, n ∈ h.N .i1 → m ∈ h.N .i1 → f (n * m) = f n * f m := by
    intro n m hn hm
    have e : f (n * m) = n * f m * n⁻¹ * f n := by simp only [f]; group
    rw [e, hNV hn (hf hm), mul_inv_cancel_right, h.V12_comm (hf hm) (hf hn)]
  have hf1 : ∀ {n : G}, n ∈ h.N .i1 → f n = 1 → n * z = z * n := fun {n} hn h1 => by
    have : n * z * n⁻¹ * z⁻¹ = 1 := h1
    calc n * z = n * z * n⁻¹ * z⁻¹ * z * n := by group
      _ = z * n := by rw [this, one_mul]
  have hcomm : ⁅h.N .i1, h.N .i1⁆ ≤ centralizer ({z} : Set G) := by
    refine (commutator_le).2 fun a ha b hb => mem_centralizer_singleton_iff.2 ?_
    have hfi : ∀ {n : G}, n ∈ h.N .i1 → f n⁻¹ = (f n)⁻¹ := fun {n} hn => by
      have e := hfm hn (inv_mem hn)
      rw [mul_inv_cancel] at e
      have e1 : f 1 = 1 := by simp [f]
      rw [e1] at e
      exact eq_inv_of_mul_eq_one_right e.symm
    have hc : f ⁅a, b⁆ = 1 := by
      rw [commutatorElement_def, hfm (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb),
        hfm (mul_mem ha hb) (inv_mem ha), hfm ha hb, hfi ha, hfi hb,
        h.V12_comm (hf ha) (hf hb)]
      group
    have hab : ⁅a, b⁆ ∈ h.N .i1 := by
      rw [← h.commutator_N .i1]
      exact commutator_mem_commutator ha hb
    exact hf1 hab hc
  refine mem_centralizer_iff.2 fun n hn => ?_
  have hn' : n ∈ ⁅h.N .i1, h.N .i1⁆ := by rw [h.commutator_N .i1]; exact hn
  exact mem_centralizer_singleton_iff.1 (hcomm hn')

theorem W12_le_centralizer_P : d.W12 ≤ centralizer (h.P : Set G) := by
  rw [le_centralizer_iff]
  refine h.P_le_R_sup_V1.trans (sup_le (le_centralizer_iff.1 d.W12_le_centralizer_R)
    ((h.V_le_N .i1).trans (le_centralizer_iff.1 d.W12_le_centralizer_N1)))

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4

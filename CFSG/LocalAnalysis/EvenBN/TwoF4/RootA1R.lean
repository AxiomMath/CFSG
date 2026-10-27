module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootA1

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable (h : Setup G)

theorem V_le_of_forall_elt_mem {k : Idx} {X : Subgroup G}
    (hX : ∀ c : h.K, h.elt (rootElt h.K h.a k c) ∈ X) : h.V k ≤ X := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := h.mem_pull.1 hx
  let Y : Subgroup (ModGL F4.tag h.K) := (X.comap h.emb).map (F4.reeGamma h.K h.a).subtype
  have hY : rootV h.K h.a k ≤ Y := by
    rw [rootV, closure_le]
    rintro _ ⟨c, rfl⟩
    have hΓ : rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a :=
      rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
    refine ⟨⟨_, hΓ⟩, ?_, rfl⟩
    show h.emb ⟨_, hΓ⟩ ∈ X
    rw [← h.elt_of_mem hΓ]
    exact hX c
  obtain ⟨g', hg', hgg'⟩ := hY hg
  have e : g' = g := Subtype.ext hgg'
  subst e
  exact hg'

theorem pull_rootJoin_le {S : Finset Idx} {X : Subgroup G} (hX : ∀ k ∈ S, h.V k ≤ X) :
    h.pull (rootJoin h.K h.a S) ≤ X := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := h.mem_pull.1 hx
  let Y : Subgroup (ModGL F4.tag h.K) := (X.comap h.emb).map (F4.reeGamma h.K h.a).subtype
  have hY : rootJoin h.K h.a S ≤ Y := by
    refine iSup₂_le fun k hk y hy => ?_
    have hΓ : y ∈ F4.reeGamma h.K h.a := rootV_le_reeGamma h.card_K k hy
    exact ⟨⟨y, hΓ⟩, hX k hk (h.emb_mem_pull.2 hy), rfl⟩
  obtain ⟨g', hg', hgg'⟩ := hY hg
  have e : g' = g := Subtype.ext hgg'
  subst e
  exact hg'

theorem elt_comm_one_four (c : h.K) :
    ⁅h.elt (rootElt h.K h.a .i1 1), h.elt (rootElt h.K h.a .i4 c)⁆ =
      h.elt (rootElt h.K h.a .i6 c) * h.elt (rootElt h.K h.a .i7 c) *
        h.elt (rootElt h.K h.a .i5 (largeReeSigma h.a c)) *
        h.elt (rootElt h.K h.a .i9 (c * largeReeSigma h.a c)) *
        h.elt (rootElt h.K h.a .i11 (c * largeReeSigma h.a c)) := by
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  rw [← h.elt_commutator (hΓ _ _) (hΓ _ _), rootElt_comm_1_4 h.card_K, largeReeSigma_one]
  simp only [mul_one, one_mul]
  rw [h.elt_mul' (mul_mem (mul_mem (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _)) (hΓ _ _)) (hΓ _ _),
    h.elt_mul' (mul_mem (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _)) (hΓ _ _),
    h.elt_mul' (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _), h.elt_mul' (hΓ _ _) (hΓ _ _)]

theorem rootChar_twelve_eq (t : h.Kˣ × h.Kˣ) :
    rootChar h.K h.a .i12 t = rootChar h.K h.a .i4 t * rootChar h.K h.a .i10 t := by
  obtain ⟨u, v⟩ := t
  obtain ⟨-, -, -, ⟨e40, e41⟩, -, -, -, -, -, ⟨e100, e101⟩, -, ⟨e120, e121⟩⟩ :=
    torusExp_leadRoot (2 ^ h.a : ℤ)
  simp only [rootChar, CFSG.LieType.Ree.LargeReeCover.torusWeight_apply, e40, e41, e100, e101,
    e120, e121]
  rw [zpow_zero, zpow_zero, one_mul, mul_one, mul_assoc, ← zpow_add,
    show (2 ^ h.a : ℤ) - 1 + (1 - 2 ^ h.a) = 0 by ring, zpow_zero, mul_one]

theorem elt_comm_four_ten (s u : h.K) :
    ⁅h.elt (rootElt h.K h.a .i4 s), h.elt (rootElt h.K h.a .i10 u)⁆ =
      h.elt (rootElt h.K h.a .i12 (s * u)) := by
  rw [← h.elt_commutator (rootV_le_reeGamma h.card_K _ (rootElt_mem_rootV _ _))
    (rootV_le_reeGamma h.card_K _ (rootElt_mem_rootV _ _)), rootElt_comm_4_10 h.card_K]

theorem elt_comm_four_nine (s u : h.K) :
    ⁅h.elt (rootElt h.K h.a .i4 s), h.elt (rootElt h.K h.a .i9 u)⁆ = 1 := by
  rw [← h.elt_commutator (rootV_le_reeGamma h.card_K _ (rootElt_mem_rootV _ _))
    (rootV_le_reeGamma h.card_K _ (rootElt_mem_rootV _ _)), rootElt_comm_4_9 h.card_K,
    h.elt_one']

theorem V4_le_R : h.V .i4 ≤ h.R := h.pull_mono (rootV_le_rootJoin (by decide))

theorem R_le_J : h.R ≤ h.J := fun _ hg => mem_inf.2 ⟨h.L_le_C (h.R_le_L hg), le_normalizer hg⟩

theorem comm_V4_V9 {g v : G} (hg : g ∈ h.V .i4) (hv : v ∈ h.V .i9) : g * v = v * g := by
  obtain ⟨u, rfl⟩ := h.exists_eq_elt_rootElt (i := .i9) rfl hv
  have hle : h.V .i4 ≤ centralizer ({h.elt (rootElt h.K h.a .i9 u)} : Set G) :=
    h.V_le_of_forall_elt_mem fun s => mem_centralizer_singleton_iff.2
      (commutatorElement_eq_one_iff_mul_comm.1 (h.elt_comm_four_nine s u))
  exact mem_centralizer_singleton_iff.1 (hle hg)

theorem comm_V4_V10_mem {g v : G} (hg : g ∈ h.V .i4) (hv : v ∈ h.V .i10) :
    ⁅g, v⁆ ∈ h.V .i12 := by
  obtain ⟨u, rfl⟩ := h.exists_eq_elt_rootElt (i := .i10) rfl hv
  set w := h.elt (rootElt h.K h.a .i10 u) with hw
  let X : Subgroup G :=
    { carrier := {g | g ∈ h.P ∧ ⁅g, w⁆ ∈ h.V .i12}
      mul_mem' := fun {g g'} hg hg' => ⟨mul_mem hg.1 hg'.1, by
        rw [commutatorElement_mul_left_eq, ← mem_centralizer_iff.1
          (h.P_le_centralizer_V12 hg.1) _ hg'.2, mul_inv_cancel_right]
        exact mul_mem hg'.2 hg.2⟩
      one_mem' := ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
      inv_mem' := fun {g} hg => ⟨inv_mem hg.1, by
        have e : ⁅g⁻¹, w⁆ = g⁻¹ * ⁅g, w⁆⁻¹ * g := by
          simp only [commutatorElement_def]; group
        rw [e, mul_assoc, mem_centralizer_iff.1 (h.P_le_centralizer_V12 hg.1) _ (inv_mem hg.2),
          inv_mul_cancel_left]
        exact inv_mem hg.2⟩ }
  have hle : h.V .i4 ≤ X := h.V_le_of_forall_elt_mem fun s =>
    ⟨h.V_le_P .i4 (h.elt_rootElt_mem_V .i4 s), by
      rw [hw, h.elt_comm_four_ten]
      exact h.elt_rootElt_mem_V .i12 _⟩
  exact (hle hg).2

theorem elt_weylR : h.elt (weylR h.K) = h.r := h.elt_of_mem weylR_mem_reeGamma

theorem r_inv : h.r⁻¹ = h.r := inv_eq_of_mul_eq_one_right h.r_mul_self_s_mul_self.1

theorem conj_r_mem_V {i : Idx} (hi1 : i ≠ .i1) (hi2 : i ≠ .i2) {v : G} (hv : v ∈ h.V i) :
    h.r * v * h.r⁻¹ ∈ h.V i.rPerm := by
  have e := h.pull_map_conj (rootV h.K h.a i) (weylR_mem_reeGamma (K := h.K) (a := h.a))
  rw [map_conj_weylR_rootV hi1 hi2, h.elt_weylR] at e
  change h.r * v * h.r⁻¹ ∈ h.pull (rootV h.K h.a i.rPerm)
  rw [e]
  exact ⟨v, hv, rfl⟩

theorem conj_r_mem_CH {i : Idx} (hi1 : i ≠ .i1) (hi2 : i ≠ .i2) {x : G} (hx : x ∈ h.CH i) :
    h.r * x * h.r⁻¹ ∈ h.CH i.rPerm := by
  have e : h.Ht i.rPerm = (h.Ht i).map (MulAut.conj h.r).toMonoidHom := by
    show h.pull (torusHi h.K h.a i.rPerm) = (h.pull (torusHi h.K h.a i)).map _
    rw [← map_conj_weylR_torusHi h.card_K hi1 hi2, h.pull_map_conj _ weylR_mem_reeGamma,
      h.elt_weylR]
  show h.r * x * h.r⁻¹ ∈ centralizer (h.Ht i.rPerm : Set G)
  rw [e]
  refine mem_centralizer_iff.2 ?_
  rintro _ ⟨c, hc, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hcx := mem_centralizer_iff.1 hx c hc
  calc h.r * c * h.r⁻¹ * (h.r * x * h.r⁻¹) = h.r * (c * x) * h.r⁻¹ := by group
    _ = h.r * (x * c) * h.r⁻¹ := by rw [hcx]
    _ = h.r * x * h.r⁻¹ * (h.r * c * h.r⁻¹) := by group

theorem r_mem_J : h.r ∈ h.J := h.N1_le_J h.r_mem_N_s_mem_N.1

theorem r1c_mul_V12 {x u : G} (hx : x ∈ h.R₁) (hu : u ∈ h.V .i12) {m : Idx}
    (hm : m.isR1 = true) (hm12 : m ≠ .i12) : h.r1c (x * u) m = h.r1c x m := by
  rw [h.r1c_mul hx (h.V12_le_R₁ hu) hm, h.r1c_eq_zero_of_mem_V12 hu hm hm12, add_zero]

theorem r1c_V12_mul {x u : G} (hx : x ∈ h.R₁) (hu : u ∈ h.V .i12) {m : Idx}
    (hm : m.isR1 = true) (hm12 : m ≠ .i12) : h.r1c (u * x) m = h.r1c x m := by
  rw [h.r1c_mul (h.V12_le_R₁ hu) hx hm, h.r1c_eq_zero_of_mem_V12 hu hm hm12, zero_add]

end Setup

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

theorem conj_r_mem_W11 {x : G} (hx : x ∈ d.WA .i4) : h.r * x * h.r⁻¹ ∈ d.W11 := by
  rw [← d.WA_six_eq]
  exact ⟨d.conj_J_mem_A1 h.r_mem_J hx.1, h.conj_r_mem_CH (i := .i4) (by decide) (by decide) hx.2⟩

theorem comm_V4_WA4 {g x : G} (hg : g ∈ h.V .i4) (hx : x ∈ d.WA .i4) : ⁅g, x⁆ = 1 := by
  have hg' : h.r * g * h.r⁻¹ ∈ h.V .i6 := h.conj_r_mem_V (i := .i4) (by decide) (by decide) hg
  have hc : (h.r * g * h.r⁻¹) * (h.r * x * h.r⁻¹) = (h.r * x * h.r⁻¹) * (h.r * g * h.r⁻¹) :=
    mem_centralizer_iff.1 (d.W11_le_centralizer_S (d.conj_r_mem_W11 hx)) _
      (h.V_le_S (by decide) hg')
  have e1 : h.r * (g * x) * h.r⁻¹ = h.r * (x * g) * h.r⁻¹ := by
    calc h.r * (g * x) * h.r⁻¹ = (h.r * g * h.r⁻¹) * (h.r * x * h.r⁻¹) := by group
      _ = (h.r * x * h.r⁻¹) * (h.r * g * h.r⁻¹) := hc
      _ = h.r * (x * g) * h.r⁻¹ := by group
  exact commutatorElement_eq_one_iff_mul_comm.2 (mul_left_cancel (mul_right_cancel e1))

theorem comm_J_A1 {g z : G} (hg : g ∈ h.J) (hz : z ∈ d.A1) :
    ⁅g, z⁆ ∈ d.A1 ∧ ⁅⁅g, z⁆, h.t⁆ = ⁅g, ⁅z, h.t⁆⁆ := by
  have hgz := d.conj_J_mem_A1 hg hz
  have hgt : g * h.t * g⁻¹ = h.t := by
    rw [mem_centralizer_singleton_iff.1 (mem_inf.1 hg).1, mul_inv_cancel_right]
  refine ⟨by rw [commutatorElement_def]; exact mul_mem hgz (inv_mem hz), ?_⟩
  rw [commutatorElement_def g z, d.comm_t_mul_A1 hgz (inv_mem hz), d.comm_t_inv_A1 hz]
  have e : ⁅g * z * g⁻¹, h.t⁆ = g * ⁅z, h.t⁆ * g⁻¹ := by
    conv_lhs => rw [← hgt]
    simp only [commutatorElement_def]; group
  rw [e]
  exact (commutatorElement_def g ⁅z, h.t⁆).symm

theorem _root_.CFSG.LocalAnalysis.EvenBN.TwoF4.commutatorElement_conj_left_of_commute
    {X : Type*} [Group X] {b y x : X} (hxb : x * b = b * x) :
    ⁅b * y * b⁻¹, x⁆ = b * ⁅y, x⁆ * b⁻¹ := by
  have e2 : b⁻¹ * x * b = x := by rw [mul_assoc, hxb, inv_mul_cancel_left]
  have e3 : b⁻¹ * x⁻¹ * b = x⁻¹ := by
    have := congrArg (·⁻¹) e2
    simpa [mul_assoc] using this
  calc ⁅b * y * b⁻¹, x⁆ = b * y * (b⁻¹ * x * b) * y⁻¹ * (b⁻¹ * x⁻¹ * b) * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = b * y * x * y⁻¹ * x⁻¹ * b⁻¹ := by rw [e2, e3]
    _ = b * ⁅y, x⁆ * b⁻¹ := by simp only [commutatorElement_def]; group

theorem comm_V4_WA9 {g x : G} (hg : g ∈ h.V .i4) (hx : x ∈ d.WA .i9) : ⁅g, x⁆ = 1 := by
  classical
  have hbr9 : ∀ m : Idx, m.isR1 = true → m ≠ .i9 → Idx.brace .i9 m ≠ 0 := by decide
  have hex : ∀ c : h.K, ∃ z ∈ d.WA .i9, ⁅z, h.t⁆ = h.elt (rootElt h.K h.a .i9 c) := fun c =>
    d.exists_WA_comm_t (h.V_le_R₁ (by decide)) (h.V_le_CH rfl (Or.inl rfl))
      (h.elt_rootElt_mem_V .i9 c)
  choose lam hlam hlamt using hex
  have hR : ∀ {g z : G}, g ∈ h.V .i4 → z ∈ d.WA .i9 → ⁅g, z⁆ ∈ h.R₁ := fun {g z} hg hz => by
    obtain ⟨hA, ht⟩ := d.comm_J_A1 (h.R_le_J (h.V4_le_R hg)) hz.1
    refine d.mem_R₁_of_mem_A1 hA ?_
    rw [ht, commutatorElement_eq_one_iff_mul_comm.2
      (h.comm_V4_V9 hg (d.comm_t_mem_V_of_mem_WA rfl hbr9 hz))]
  have hmod : ∀ {z : G}, z ∈ d.WA .i9 → ∀ {c : h.K},
      ⁅z, h.t⁆ = h.elt (rootElt h.K h.a .i9 c) → z * (lam c)⁻¹ ∈ h.V .i9 := fun {z} hz {c} hzc =>
    d.mem_V_of_mem_WA rfl hbr9 (mul_mem hz (inv_mem (hlam c))) (by
      rw [d.comm_t_mul_A1 hz.1 (inv_mem (hlam c)).1, d.comm_t_inv_A1 (hlam c).1, hzc, hlamt,
        mul_inv_cancel])
  have hred : ∀ {g v z : G}, g ∈ h.V .i4 → v ∈ h.V .i9 → z ∈ d.WA .i9 →
      ⁅g, v * z⁆ = ⁅g, z⁆ := fun {g v z} hg hv hz => by
    rw [commutatorElement_mul_right_eq,
      commutatorElement_eq_one_iff_mul_comm.2 (h.comm_V4_V9 hg hv), one_mul,
      h.R₁_comm (h.V_le_R₁ (by decide) hv) (hR hg hz), mul_inv_cancel_right]
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  have h4side : ∀ (e : h.K) (m : Idx), m.isR1 = true →
      Idx.brace .i4 .i9 ≠ Idx.brace .i4 m → ∀ c,
        h.r1c ⁅h.elt (rootElt h.K h.a .i4 e), lam c⁆ m = 0 := by
    intro e m hm hb c
    have hg := h.elt_rootElt_mem_V .i4 e
    refine h.r1c_eq_zero_of_brace_ne' (i := .i4) (j := .i9) rfl
      (Ψ := fun c => ⁅h.elt (rootElt h.K h.a .i4 e), lam c⁆) (fun c c' l hl => ?_)
      (fun t ht c l hl => ?_) hm hb c
    · show h.r1c ⁅h.elt (rootElt h.K h.a .i4 e), lam (c + c')⁆ l =
        h.r1c ⁅h.elt (rootElt h.K h.a .i4 e), lam c⁆ l +
          h.r1c ⁅h.elt (rootElt h.K h.a .i4 e), lam c'⁆ l
      have hz : lam c * lam c' ∈ d.WA .i9 := mul_mem (hlam c) (hlam c')
      have hzc : ⁅lam c * lam c', h.t⁆ = h.elt (rootElt h.K h.a .i9 (c + c')) := by
        rw [d.comm_t_mul_A1 (hlam c).1 (hlam c').1, hlamt, hlamt, rootElt_add h.card_K rfl,
          h.elt_mul' (hΓ _ _) (hΓ _ _)]
      have hv : lam (c + c') * (lam c * lam c')⁻¹ ∈ h.V .i9 := by
        have := inv_mem (hmod hz hzc)
        rwa [mul_inv_rev, inv_inv] at this
      have e1 : lam (c + c') = (lam (c + c') * (lam c * lam c')⁻¹) * (lam c * lam c') := by
        group
      rw [e1, hred hg hv hz, commutatorElement_mul_right_eq, ← mem_centralizer_iff.1
        (d.A1_le_centralizer_R₁ (hlam c).1) _ (hR hg (hlam c')), mul_inv_cancel_right,
        h.r1c_mul (hR hg (hlam c)) (hR hg (hlam c')) hl]
    · set b := h.elt (torusPair h.a t) with hbdef
      have hb : b ∈ h.Ht .i4 := (h.elt_torusPair_mem_Ht_iff t).2 ht
      have hbH := h.Ht_le_H .i4 hb
      have hgb : h.elt (rootElt h.K h.a .i4 e) * b = b * h.elt (rootElt h.K h.a .i4 e) :=
        (mem_centralizer_iff.1 (h.V_le_CH (i := .i4) rfl (Or.inl rfl) hg) b hb).symm
      have hz : b * lam c * b⁻¹ ∈ d.WA .i9 := d.conj_H_mem_WA hbH (hlam c)
      have hbt : b * h.t * b⁻¹ = h.t := by
        rw [h.mul_t_comm (h.H_le_L hbH), mul_inv_cancel_right]
      have hzc : ⁅b * lam c * b⁻¹, h.t⁆ =
          h.elt (rootElt h.K h.a .i9 ((rootChar h.K h.a .i9 t : h.K) * c)) := by
        rw [← h.elt_torusPair_conj_rootElt, ← hlamt c, ← hbdef]
        conv_lhs => rw [← hbt]
        simp only [commutatorElement_def]; group
      have hv : lam ((rootChar h.K h.a .i9 t : h.K) * c) * (b * lam c * b⁻¹)⁻¹ ∈ h.V .i9 := by
        have := inv_mem (hmod hz hzc)
        rwa [mul_inv_rev, inv_inv] at this
      have e1 : lam ((rootChar h.K h.a .i9 t : h.K) * c) =
          (lam ((rootChar h.K h.a .i9 t : h.K) * c) * (b * lam c * b⁻¹)⁻¹) *
            (b * lam c * b⁻¹) := by group
      show h.r1c ⁅h.elt (rootElt h.K h.a .i4 e), lam ((rootChar h.K h.a .i9 t : h.K) * c)⁆ l =
        (rootChar h.K h.a l t : h.K) * h.r1c ⁅h.elt (rootElt h.K h.a .i4 e), lam c⁆ l
      rw [e1, hred hg hv hz, commutatorElement_conj_of_commute hgb, hbdef,
        h.r1c_torus (hR hg (hlam c)) t hl]
  have h9side : ∀ (m : Idx), m.isR1 = true → m ≠ .i12 → Idx.brace .i9 .i4 ≠ Idx.brace .i9 m →
      ∀ e, h.r1c ⁅h.elt (rootElt h.K h.a .i4 e), x⁆ m = 0 := by
    intro m hm hm12 hb e
    refine h.r1c_eq_zero_of_brace_ne (i := .i9) (j := .i4) rfl
      (Ψ := fun e => ⁅h.elt (rootElt h.K h.a .i4 e), x⁆) (fun e e' l hl hl12 => ?_)
      (fun t ht e l hl hl12 => ?_) hm hm12 hb e
    · show h.r1c ⁅h.elt (rootElt h.K h.a .i4 (e + e')), x⁆ l =
        h.r1c ⁅h.elt (rootElt h.K h.a .i4 e), x⁆ l + h.r1c ⁅h.elt (rootElt h.K h.a .i4 e'), x⁆ l
      have hmul := h.elt_rootElt_mul_of_isSz (k := .i4) rfl e e'
      have h8 : h.elt (rootElt h.K h.a Idx.i4.center (largeReeSigma h.a e * e')) ∈ h.R₁ :=
        h.elt_rootElt_mem_R₁ rfl _
      have hc8 : ⁅h.elt (rootElt h.K h.a Idx.i4.center (largeReeSigma h.a e * e')), x⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.2
          (mem_centralizer_iff.1 (d.A1_le_centralizer_R₁ hx.1) _ h8)
      have e1 : ⁅h.elt (rootElt h.K h.a .i4 (e + e')), x⁆ =
          ⁅h.elt (rootElt h.K h.a .i4 e) * h.elt (rootElt h.K h.a .i4 e'), x⁆ := by
        rw [hmul, commutatorElement_mul_left_eq, hc8, mul_one, mul_inv_cancel, one_mul]
      have he := h.elt_rootElt_mem_V .i4 e
      have he' := h.elt_rootElt_mem_V .i4 e'
      have hconj : h.elt (rootElt h.K h.a .i4 e) * ⁅h.elt (rootElt h.K h.a .i4 e'), x⁆ *
          (h.elt (rootElt h.K h.a .i4 e))⁻¹ ∈ h.R₁ :=
        (mem_normalizer_iff.1 (h.J_le_normalizer_R₁ (h.R_le_J (h.V4_le_R he))) _).1 (hR he' hx)
      rw [e1, commutatorElement_mul_left_eq, h.r1c_mul hconj (hR he hx) hl,
        h.r1c_conj_R (h.V4_le_R he) (hR he' hx) hl hl12, add_comm]
    · set b := h.elt (torusPair h.a t) with hbdef
      have hb : b ∈ h.Ht .i9 := (h.elt_torusPair_mem_Ht_iff t).2 ht
      have hxb : x * b = b * x := (mem_centralizer_iff.1 hx.2 b hb).symm
      show h.r1c ⁅h.elt (rootElt h.K h.a .i4 ((rootChar h.K h.a .i4 t : h.K) * e)), x⁆ l =
        (rootChar h.K h.a l t : h.K) * h.r1c ⁅h.elt (rootElt h.K h.a .i4 e), x⁆ l
      rw [← h.elt_torusPair_conj_rootElt, ← hbdef, commutatorElement_conj_left_of_commute hxb,
        hbdef, h.r1c_torus (hR (h.elt_rootElt_mem_V .i4 e) hx) t hl]
  have hb4 : ∀ m : Idx, m.isR1 = true → m ≠ .i9 → Idx.brace .i4 .i9 ≠ Idx.brace .i4 m := by
    decide
  have hkey : ∀ e, ⁅h.elt (rootElt h.K h.a .i4 e), x⁆ = 1 := by
    intro e
    obtain ⟨c, hc⟩ := h.exists_eq_elt_rootElt (i := .i9) rfl
      (d.comm_t_mem_V_of_mem_WA rfl hbr9 hx)
    have e2 : ⁅h.elt (rootElt h.K h.a .i4 e), x⁆ = ⁅h.elt (rootElt h.K h.a .i4 e), lam c⁆ := by
      rw [show x = (x * (lam c)⁻¹) * lam c by group,
        hred (h.elt_rootElt_mem_V .i4 e) (hmod hx hc) (hlam c)]
    refine h.eq_of_r1c_eq (hR (h.elt_rootElt_mem_V .i4 e) hx) (one_mem _) fun m hm => ?_
    rw [h.r1c_one hm]
    by_cases hm9 : m = .i9
    · subst hm9
      exact h9side .i9 rfl (by decide) (by decide) e
    · rw [e2]
      exact h4side e m hm (hb4 m hm hm9) c
  have hle : h.V .i4 ≤ centralizer ({x} : Set G) := h.V_le_of_forall_elt_mem fun e =>
    mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.1 (hkey e))
  exact commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_singleton_iff.1 (hle hg))

theorem A1_comm_R₁_mul_W12 {a y z : G} (ha : a ∈ d.A1) (hy : y ∈ h.R₁) (hz : z ∈ d.W12) :
    a * (y * z) = (y * z) * a := by
  have h1 : y * a = a * y := mem_centralizer_iff.1 (d.A1_le_centralizer_R₁ ha) y hy
  have h2 : z * a = a * z := mem_centralizer_iff.1 ha.2.1 z hz
  calc a * (y * z) = (a * y) * z := by group
    _ = y * (a * z) := by rw [← h1]; group
    _ = y * (z * a) := by rw [h2]
    _ = (y * z) * a := by group

theorem comm_V4_WA10_mem {g x : G} (hg : g ∈ h.V .i4) (hx : x ∈ d.WA .i10) :
    ⁅g, x⁆ ∈ d.W12 := by
  classical
  have hbr10 : ∀ m : Idx, m.isR1 = true → m ≠ .i10 → Idx.brace .i10 m ≠ 0 := by decide
  have hex : ∀ c : h.K, ∃ z ∈ d.WA .i10, ⁅z, h.t⁆ = h.elt (rootElt h.K h.a .i10 c) := fun c =>
    d.exists_WA_comm_t (h.V_le_R₁ (by decide)) (h.V_le_CH rfl (Or.inl rfl))
      (h.elt_rootElt_mem_V .i10 c)
  choose lam hlam hlamt using hex
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  have hR : ∀ {e c : h.K} {z : G}, z ∈ d.A1 → ⁅z, h.t⁆ = h.elt (rootElt h.K h.a .i10 c) →
      ⁅h.elt (rootElt h.K h.a .i4 e), z⁆ * (d.zc (e * c))⁻¹ ∈ h.R₁ := fun {e c z} hz hzc => by
    obtain ⟨hA, ht⟩ := d.comm_J_A1 (h.R_le_J (h.V4_le_R (h.elt_rootElt_mem_V .i4 e))) hz
    refine d.mul_inv_mem_R₁_of_comm_eq hA (d.W12_le_A1 (d.zc_mem _)) ?_
    rw [ht, hzc, h.elt_comm_four_ten, d.zc_comm]
  have hA1 : ∀ {e : h.K} {z : G}, z ∈ d.A1 → ⁅h.elt (rootElt h.K h.a .i4 e), z⁆ ∈ d.A1 :=
    fun {e z} hz => (d.comm_J_A1 (h.R_le_J (h.V4_le_R (h.elt_rootElt_mem_V .i4 e))) hz).1
  have hdec : ∀ {e c : h.K} {z : G}, z ∈ d.A1 → ⁅z, h.t⁆ = h.elt (rootElt h.K h.a .i10 c) →
      ⁅h.elt (rootElt h.K h.a .i4 e), z⁆ =
        (⁅h.elt (rootElt h.K h.a .i4 e), z⁆ * (d.zc (e * c))⁻¹) * d.zc (e * c) :=
    fun _ _ => by group
  have hmod : ∀ {z : G}, z ∈ d.WA .i10 → ∀ {c : h.K},
      ⁅z, h.t⁆ = h.elt (rootElt h.K h.a .i10 c) → z * (lam c)⁻¹ ∈ h.V .i10 := fun {z} hz {c} hzc =>
    d.mem_V_of_mem_WA rfl hbr10 (mul_mem hz (inv_mem (hlam c))) (by
      rw [d.comm_t_mul_A1 hz.1 (inv_mem (hlam c)).1, d.comm_t_inv_A1 (hlam c).1, hzc, hlamt,
        mul_inv_cancel])
  have hred : ∀ {e : h.K} {v z : G}, v ∈ h.V .i10 → z ∈ d.A1 →
      ⁅h.elt (rootElt h.K h.a .i4 e), v * z⁆ =
        ⁅h.elt (rootElt h.K h.a .i4 e), v⁆ * ⁅h.elt (rootElt h.K h.a .i4 e), z⁆ :=
    fun {e v z} hv hz => by
      rw [commutatorElement_mul_right_eq, mem_centralizer_iff.1
        (d.A1_le_centralizer_R₁ (hA1 hz)) v (h.V_le_R₁ (by decide) hv), mul_inv_cancel_right]
  have hv12 : ∀ {e : h.K} {v : G}, v ∈ h.V .i10 → ⁅h.elt (rootElt h.K h.a .i4 e), v⁆ ∈ h.V .i12 :=
    fun hv => h.comm_V4_V10_mem (h.elt_rootElt_mem_V .i4 _) hv
  have hχ4 : ∀ t : h.Kˣ × h.Kˣ, torusPair h.a t ∈ torusHi h.K h.a .i4 →
      (rootChar h.K h.a .i12 t : h.K) = rootChar h.K h.a .i10 t := fun t ht => by
    rw [h.rootChar_twelve_eq, (mem_torusHi_iff h.card_K .i4 t).1 ht, one_mul]
  have hχ10 : ∀ t : h.Kˣ × h.Kˣ, torusPair h.a t ∈ torusHi h.K h.a .i10 →
      (rootChar h.K h.a .i12 t : h.K) = rootChar h.K h.a .i4 t := fun t ht => by
    rw [h.rootChar_twelve_eq, (mem_torusHi_iff h.card_K .i10 t).1 ht, mul_one]
  have hb4 : ∀ m : Idx, m.isR1 = true → m ≠ .i12 → m ≠ .i10 → m ≠ .i11 →
      Idx.brace .i4 .i10 ≠ Idx.brace .i4 m := by decide
  have h4side : ∀ (e : h.K) (m : Idx), m.isR1 = true → m ≠ .i12 →
      Idx.brace .i4 .i10 ≠ Idx.brace .i4 m → ∀ c,
        h.r1c (⁅h.elt (rootElt h.K h.a .i4 e), lam c⁆ * (d.zc (e * c))⁻¹) m = 0 := by
    intro e m hm hm12 hb c
    have hg := h.elt_rootElt_mem_V .i4 e
    refine h.r1c_eq_zero_of_brace_ne (i := .i4) (j := .i10) rfl
      (Ψ := fun c => ⁅h.elt (rootElt h.K h.a .i4 e), lam c⁆ *
        (d.zc (e * c))⁻¹) (fun c c' l hl hl12 => ?_)
      (fun t ht c l hl hl12 => ?_) hm hm12 hb c
    · show h.r1c (⁅h.elt (rootElt h.K h.a .i4 e), lam (c + c')⁆ * (d.zc (e * (c + c')))⁻¹) l =
        h.r1c (⁅h.elt (rootElt h.K h.a .i4 e), lam c⁆ * (d.zc (e * c))⁻¹) l +
          h.r1c (⁅h.elt (rootElt h.K h.a .i4 e), lam c'⁆ * (d.zc (e * c'))⁻¹) l
      have hz : lam c * lam c' ∈ d.WA .i10 := mul_mem (hlam c) (hlam c')
      have hzc : ⁅lam c * lam c', h.t⁆ = h.elt (rootElt h.K h.a .i10 (c + c')) := by
        rw [d.comm_t_mul_A1 (hlam c).1 (hlam c').1, hlamt, hlamt, rootElt_add h.card_K rfl,
          h.elt_mul' (hΓ _ _) (hΓ _ _)]
      have hvmem : lam (c + c') * (lam c * lam c')⁻¹ ∈ h.V .i10 := by
        have := inv_mem (hmod hz hzc)
        rwa [mul_inv_rev, inv_inv] at this
      obtain ⟨v, hv, e1⟩ : ∃ v ∈ h.V .i10, lam (c + c') = v * (lam c * lam c') :=
        ⟨_, hvmem, by group⟩
      obtain ⟨w₁, hw₁R, hc1⟩ : ∃ w ∈ h.R₁,
          ⁅h.elt (rootElt h.K h.a .i4 e), lam c⁆ = w * d.zc (e * c) :=
        ⟨_, hR (e := e) (hlam c).1 (hlamt c), by group⟩
      obtain ⟨w₂, hw₂R, hc2⟩ : ∃ w ∈ h.R₁,
          ⁅h.elt (rootElt h.K h.a .i4 e), lam c'⁆ = w * d.zc (e * c') :=
        ⟨_, hR (e := e) (hlam c').1 (hlamt c'), by group⟩
      obtain ⟨u, huV, hu⟩ : ∃ u ∈ h.V .i12,
          d.zc (e * c + e * c') = u * (d.zc (e * c) * d.zc (e * c')) :=
        ⟨_, d.zc_add (e * c) (e * c'), by group⟩
      have hcomm : lam c * ⁅h.elt (rootElt h.K h.a .i4 e), lam c'⁆ * (lam c)⁻¹ =
          ⁅h.elt (rootElt h.K h.a .i4 e), lam c'⁆ := by
        rw [hc2, d.A1_comm_R₁_mul_W12 (hlam c).1 hw₂R (d.zc_mem _), mul_inv_cancel_right]
      have hzw : d.zc (e * c) * w₂ = w₂ * d.zc (e * c) :=
        (mem_centralizer_iff.1 (d.W12_le_centralizer_R₁ (d.zc_mem _)) w₂ hw₂R).symm
      have key : ⁅h.elt (rootElt h.K h.a .i4 e), lam (c + c')⁆ * (d.zc (e * (c + c')))⁻¹ =
          ⁅h.elt (rootElt h.K h.a .i4 e), v⁆ * (w₁ * w₂) * u⁻¹ := by
        rw [e1, hred hv hz.1, commutatorElement_mul_right_eq, hcomm, mul_add, hu, hc1, hc2]
        calc ⁅h.elt (rootElt h.K h.a .i4 e), v⁆ * (w₁ * d.zc (e * c) * (w₂ * d.zc (e * c'))) *
              (u * (d.zc (e * c) * d.zc (e * c')))⁻¹ =
            ⁅h.elt (rootElt h.K h.a .i4 e), v⁆ * w₁ * (d.zc (e * c) * w₂) * d.zc (e * c') *
              ((d.zc (e * c'))⁻¹ * (d.zc (e * c))⁻¹) * u⁻¹ := by group
          _ = ⁅h.elt (rootElt h.K h.a .i4 e), v⁆ * w₁ * (w₂ * d.zc (e * c)) * d.zc (e * c') *
              ((d.zc (e * c'))⁻¹ * (d.zc (e * c))⁻¹) * u⁻¹ := by rw [hzw]
          _ = ⁅h.elt (rootElt h.K h.a .i4 e), v⁆ * (w₁ * w₂) * u⁻¹ := by group
      rw [key, h.r1c_mul_V12 (mul_mem (h.V12_le_R₁ (hv12 hv)) (mul_mem hw₁R hw₂R)) (inv_mem huV)
        hl hl12, h.r1c_V12_mul (mul_mem hw₁R hw₂R) (hv12 hv) hl hl12, h.r1c_mul hw₁R hw₂R hl,
        hc1, hc2, mul_inv_cancel_right, mul_inv_cancel_right]
    · set b := h.elt (torusPair h.a t) with hbdef
      have hb : b ∈ h.Ht .i4 := (h.elt_torusPair_mem_Ht_iff t).2 ht
      have hbH := h.Ht_le_H .i4 hb
      have hgb : h.elt (rootElt h.K h.a .i4 e) * b = b * h.elt (rootElt h.K h.a .i4 e) :=
        (mem_centralizer_iff.1 (h.V_le_CH (i := .i4) rfl (Or.inl rfl) hg) b hb).symm
      have hz : b * lam c * b⁻¹ ∈ d.WA .i10 := d.conj_H_mem_WA hbH (hlam c)
      have hbt : b * h.t * b⁻¹ = h.t := by
        rw [h.mul_t_comm (h.H_le_L hbH), mul_inv_cancel_right]
      have hzc : ⁅b * lam c * b⁻¹, h.t⁆ =
          h.elt (rootElt h.K h.a .i10 ((rootChar h.K h.a .i10 t : h.K) * c)) := by
        rw [← h.elt_torusPair_conj_rootElt, ← hlamt c, ← hbdef]
        conv_lhs => rw [← hbt]
        simp only [commutatorElement_def]; group
      have hvmem : lam ((rootChar h.K h.a .i10 t : h.K) * c) * (b * lam c * b⁻¹)⁻¹ ∈
          h.V .i10 := by
        have := inv_mem (hmod hz hzc)
        rwa [mul_inv_rev, inv_inv] at this
      obtain ⟨v, hv, e1⟩ : ∃ v ∈ h.V .i10,
          lam ((rootChar h.K h.a .i10 t : h.K) * c) = v * (b * lam c * b⁻¹) :=
        ⟨_, hvmem, by group⟩
      obtain ⟨w, hwR, hcw⟩ : ∃ w ∈ h.R₁,
          ⁅h.elt (rootElt h.K h.a .i4 e), lam c⁆ = w * d.zc (e * c) :=
        ⟨_, hR (e := e) (hlam c).1 (hlamt c), by group⟩
      have hzt := d.zc_torus t (e * c)
      rw [← hbdef, hχ4 t ht] at hzt
      obtain ⟨u, huV, hu⟩ : ∃ u ∈ h.V .i12, b * d.zc (e * c) * b⁻¹ =
          u * d.zc ((rootChar h.K h.a .i10 t : h.K) * (e * c)) := ⟨_, hzt, by group⟩
      have hbw : b * w * b⁻¹ ∈ h.R₁ :=
        (mem_normalizer_iff.1 (h.J_le_normalizer_R₁ (h.H_le_J hbH)) w).1 hwR
      have key : ⁅h.elt (rootElt h.K h.a .i4 e), lam ((rootChar h.K h.a .i10 t : h.K) * c)⁆ *
            (d.zc (e * ((rootChar h.K h.a .i10 t : h.K) * c)))⁻¹ =
          ⁅h.elt (rootElt h.K h.a .i4 e), v⁆ * (b * w * b⁻¹) * u := by
        have e2 : d.zc (e * ((rootChar h.K h.a .i10 t : h.K) * c)) =
            u⁻¹ * (b * d.zc (e * c) * b⁻¹) := by
          rw [hu, show e * ((rootChar h.K h.a .i10 t : h.K) * c) =
            (rootChar h.K h.a .i10 t : h.K) * (e * c) by ring]
          group
        rw [e1, hred hv hz.1, commutatorElement_conj_of_commute hgb, e2, hcw]
        group
      show h.r1c (⁅h.elt (rootElt h.K h.a .i4 e), lam ((rootChar h.K h.a .i10 t : h.K) * c)⁆ *
          (d.zc (e * ((rootChar h.K h.a .i10 t : h.K) * c)))⁻¹) l =
        (rootChar h.K h.a l t : h.K) *
          h.r1c (⁅h.elt (rootElt h.K h.a .i4 e), lam c⁆ * (d.zc (e * c))⁻¹) l
      rw [key, h.r1c_mul_V12 (mul_mem (h.V12_le_R₁ (hv12 hv)) hbw) huV hl hl12,
        h.r1c_V12_mul hbw (hv12 hv) hl hl12, hbdef, h.r1c_torus hwR t hl, hcw,
        mul_inv_cancel_right]
  obtain ⟨cx, hcx⟩ := h.exists_eq_elt_rootElt (i := .i10) rfl
    (d.comm_t_mem_V_of_mem_WA rfl hbr10 hx)
  have h10side : ∀ (m : Idx), m.isR1 = true → m ≠ .i12 →
      Idx.brace .i10 .i4 ≠ Idx.brace .i10 m → ∀ e,
        h.r1c (⁅h.elt (rootElt h.K h.a .i4 e), x⁆ * (d.zc (e * cx))⁻¹) m = 0 := by
    intro m hm hm12 hb e
    refine h.r1c_eq_zero_of_brace_ne (i := .i10) (j := .i4) rfl
      (Ψ := fun e => ⁅h.elt (rootElt h.K h.a .i4 e), x⁆ * (d.zc (e * cx))⁻¹)
      (fun e e' l hl hl12 => ?_) (fun t ht e l hl hl12 => ?_) hm hm12 hb e
    · show h.r1c (⁅h.elt (rootElt h.K h.a .i4 (e + e')), x⁆ * (d.zc ((e + e') * cx))⁻¹) l =
        h.r1c (⁅h.elt (rootElt h.K h.a .i4 e), x⁆ * (d.zc (e * cx))⁻¹) l +
          h.r1c (⁅h.elt (rootElt h.K h.a .i4 e'), x⁆ * (d.zc (e' * cx))⁻¹) l
      have hmul := h.elt_rootElt_mul_of_isSz (k := .i4) rfl e e'
      have h8 : h.elt (rootElt h.K h.a Idx.i4.center (largeReeSigma h.a e * e')) ∈ h.R₁ :=
        h.elt_rootElt_mem_R₁ rfl _
      have hc8 : ⁅h.elt (rootElt h.K h.a Idx.i4.center (largeReeSigma h.a e * e')), x⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.2
          (mem_centralizer_iff.1 (d.A1_le_centralizer_R₁ hx.1) _ h8)
      have e1 : ⁅h.elt (rootElt h.K h.a .i4 (e + e')), x⁆ =
          ⁅h.elt (rootElt h.K h.a .i4 e) * h.elt (rootElt h.K h.a .i4 e'), x⁆ := by
        rw [hmul, commutatorElement_mul_left_eq, hc8, mul_one, mul_inv_cancel, one_mul]
      set a₁ := h.elt (rootElt h.K h.a .i4 e) with ha₁
      have ha₁R : a₁ ∈ h.R := h.V4_le_R (h.elt_rootElt_mem_V .i4 e)
      set w₁ := ⁅a₁, x⁆ * (d.zc (e * cx))⁻¹ with hw₁
      set w₂ := ⁅h.elt (rootElt h.K h.a .i4 e'), x⁆ * (d.zc (e' * cx))⁻¹ with hw₂
      have hw₁R : w₁ ∈ h.R₁ := hR (e := e) hx.1 hcx
      have hw₂R : w₂ ∈ h.R₁ := hR (e := e') hx.1 hcx
      set u := d.zc (e * cx + e' * cx) * (d.zc (e * cx) * d.zc (e' * cx))⁻¹ with hu
      have huV : u ∈ h.V .i12 := d.zc_add _ _
      have hzR : ∀ {c : h.K}, a₁ * d.zc c = d.zc c * a₁ := fun {c} =>
        mem_centralizer_iff.1 (d.W12_le_centralizer_R (d.zc_mem c)) a₁ ha₁R
      have hconj : a₁ * w₂ * a₁⁻¹ ∈ h.R₁ :=
        (mem_normalizer_iff.1 (h.J_le_normalizer_R₁ (h.R_le_J ha₁R)) w₂).1 hw₂R
      have hzw : d.zc (e' * cx) * w₁ = w₁ * d.zc (e' * cx) :=
        (mem_centralizer_iff.1 (d.W12_le_centralizer_R₁ (d.zc_mem _)) w₁ hw₁R).symm
      have key : ⁅h.elt (rootElt h.K h.a .i4 (e + e')), x⁆ * (d.zc ((e + e') * cx))⁻¹ =
          (a₁ * w₂ * a₁⁻¹) * w₁ * u⁻¹ := by
        rw [e1, commutatorElement_mul_left_eq, add_mul, hu]
        have h1 : ⁅h.elt (rootElt h.K h.a .i4 e'), x⁆ = w₂ * d.zc (e' * cx) := by
          rw [hw₂]; group
        have h2 : ⁅a₁, x⁆ = w₁ * d.zc (e * cx) := by rw [hw₁]; group
        rw [h1, h2]
        calc a₁ * (w₂ * d.zc (e' * cx)) * a₁⁻¹ * (w₁ * d.zc (e * cx)) *
              (d.zc (e * cx + e' * cx))⁻¹ =
            a₁ * w₂ * a₁⁻¹ * (a₁ * d.zc (e' * cx)) * a₁⁻¹ * (w₁ * d.zc (e * cx)) *
              (d.zc (e * cx + e' * cx))⁻¹ := by group
          _ = a₁ * w₂ * a₁⁻¹ * (d.zc (e' * cx) * w₁) * d.zc (e * cx) *
              (d.zc (e * cx + e' * cx))⁻¹ := by rw [hzR]; group
          _ = a₁ * w₂ * a₁⁻¹ * w₁ * (d.zc (e' * cx) * d.zc (e * cx)) *
              (d.zc (e * cx + e' * cx))⁻¹ := by rw [hzw]; group
          _ = a₁ * w₂ * a₁⁻¹ * w₁ * (d.zc (e * cx + e' * cx) *
              (d.zc (e * cx) * d.zc (e' * cx))⁻¹)⁻¹ := by
            rw [d.W12_comm (d.zc_mem (e' * cx)) (d.zc_mem (e * cx))]; group
      rw [key, h.r1c_mul_V12 (mul_mem hconj hw₁R) (inv_mem huV) hl hl12,
        h.r1c_mul hconj hw₁R hl, h.r1c_conj_R ha₁R hw₂R hl hl12, add_comm]
    · set b := h.elt (torusPair h.a t) with hbdef
      have hb : b ∈ h.Ht .i10 := (h.elt_torusPair_mem_Ht_iff t).2 ht
      have hbH := h.Ht_le_H .i10 hb
      have hxb : x * b = b * x := (mem_centralizer_iff.1 hx.2 b hb).symm
      set w := ⁅h.elt (rootElt h.K h.a .i4 e), x⁆ * (d.zc (e * cx))⁻¹ with hwdef
      have hwR : w ∈ h.R₁ := hR (e := e) hx.1 hcx
      have hzt := d.zc_torus t (e * cx)
      rw [← hbdef, hχ10 t ht] at hzt
      set u := b * d.zc (e * cx) * b⁻¹ * (d.zc ((rootChar h.K h.a .i4 t : h.K) * (e * cx)))⁻¹
        with hudef
      have hbw : b * w * b⁻¹ ∈ h.R₁ :=
        (mem_normalizer_iff.1 (h.J_le_normalizer_R₁ (h.H_le_J hbH)) w).1 hwR
      have key : ⁅h.elt (rootElt h.K h.a .i4 ((rootChar h.K h.a .i4 t : h.K) * e)), x⁆ *
            (d.zc ((rootChar h.K h.a .i4 t : h.K) * e * cx))⁻¹ = (b * w * b⁻¹) * u := by
        rw [← h.elt_torusPair_conj_rootElt, ← hbdef, commutatorElement_conj_left_of_commute hxb,
          hwdef, hudef, show (rootChar h.K h.a .i4 t : h.K) * e * cx =
            (rootChar h.K h.a .i4 t : h.K) * (e * cx) by ring]
        group
      show h.r1c (⁅h.elt (rootElt h.K h.a .i4 ((rootChar h.K h.a .i4 t : h.K) * e)), x⁆ *
          (d.zc ((rootChar h.K h.a .i4 t : h.K) * e * cx))⁻¹) l =
        (rootChar h.K h.a l t : h.K) * h.r1c w l
      rw [key, h.r1c_mul_V12 hbw hzt hl hl12, hbdef, h.r1c_torus hwR t hl]
  have hkey : ∀ e, ⁅h.elt (rootElt h.K h.a .i4 e), x⁆ ∈ d.W12 := by
    intro e
    have hY := hR (e := e) hx.1 hcx
    have e2 : ⁅h.elt (rootElt h.K h.a .i4 e), x⁆ * (d.zc (e * cx))⁻¹ =
        ⁅h.elt (rootElt h.K h.a .i4 e), x * (lam cx)⁻¹⁆ *
          (⁅h.elt (rootElt h.K h.a .i4 e), lam cx⁆ * (d.zc (e * cx))⁻¹) := by
      rw [show ⁅h.elt (rootElt h.K h.a .i4 e), x⁆ = ⁅h.elt (rootElt h.K h.a .i4 e),
        (x * (lam cx)⁻¹) * lam cx⁆ by group, hred (hmod hx hcx) (hlam cx).1]
      group
    have hYV : ⁅h.elt (rootElt h.K h.a .i4 e), x⁆ * (d.zc (e * cx))⁻¹ ∈ h.V .i12 := by
      rw [← h.pull_rootJoin_singleton]
      refine h.mem_of_r1c_eq_zero hY fun m hm hm12 => ?_
      have hm12' : m ≠ .i12 := by simpa using hm12
      by_cases hm9 : m = .i9
      · subst hm9
        rw [e2, h.r1c_V12_mul (hR (e := e) (hlam cx).1 (hlamt cx)) (hv12 (hmod hx hcx)) rfl
          (by decide)]
        exact h4side e .i9 rfl (by decide) (by decide) cx
      · exact h10side m hm hm12' (by revert hm hm9 hm12'; revert m; decide) e
    have e3 : ⁅h.elt (rootElt h.K h.a .i4 e), x⁆ =
        (⁅h.elt (rootElt h.K h.a .i4 e), x⁆ * (d.zc (e * cx))⁻¹) * d.zc (e * cx) := by group
    rw [e3]
    exact mul_mem (d.V12_le_W12 hYV) (d.zc_mem _)
  let X : Subgroup G :=
    { carrier := {g | g ∈ h.R ∧ ⁅g, x⁆ ∈ d.W12}
      mul_mem' := fun {g g'} hg hg' => ⟨mul_mem hg.1 hg'.1, by
        rw [commutatorElement_mul_left_eq, mem_centralizer_iff.1
          (d.W12_le_centralizer_R hg'.2) g hg.1, mul_inv_cancel_right]
        exact mul_mem hg'.2 hg.2⟩
      one_mem' := ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
      inv_mem' := fun {g} hg => ⟨inv_mem hg.1, by
        have e : ⁅g⁻¹, x⁆ = g⁻¹ * ⁅g, x⁆⁻¹ * g := by
          simp only [commutatorElement_def]; group
        rw [e, mul_assoc, ← mem_centralizer_iff.1 (d.W12_le_centralizer_R (inv_mem hg.2)) g hg.1,
          inv_mul_cancel_left]
        exact inv_mem hg.2⟩ }
  have hle : h.V .i4 ≤ X := h.V_le_of_forall_elt_mem fun e =>
    ⟨h.V4_le_R (h.elt_rootElt_mem_V .i4 e), hkey e⟩
  exact (hle hg).2

theorem comm_V4_A1_mem {g a : G} (hg : g ∈ h.V .i4) (ha : a ∈ d.A1) : ⁅g, a⁆ ∈ d.W12 := by
  let M : Subgroup G :=
    { carrier := {a | a ∈ d.A1 ∧ ⁅g, a⁆ ∈ d.W12}
      mul_mem' := fun {a a'} ha ha' => ⟨mul_mem ha.1 ha'.1, by
        rw [commutatorElement_mul_right_eq, ← mem_centralizer_iff.1 ha.1.2.1 _ ha'.2,
          mul_inv_cancel_right]
        exact mul_mem ha.2 ha'.2⟩
      one_mem' := ⟨one_mem _, by rw [commutatorElement_one_right]; exact one_mem _⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        have e : ⁅g, a⁻¹⁆ = a⁻¹ * ⁅g, a⁆⁻¹ * a := by simp only [commutatorElement_def]; group
        rw [e, mul_assoc, mem_centralizer_iff.1 ha.1.2.1 _ (inv_mem ha.2), inv_mul_cancel_left]
        exact inv_mem ha.2⟩ }
  have h1 : ∀ {y : G}, y ∈ d.A1 → ⁅g, y⁆ = 1 → y ∈ M := fun {y} hy h1 =>
    ⟨hy, by rw [h1]; exact one_mem _⟩
  have hgS : g ∈ h.S := h.V_le_S (by decide) hg
  have hle : d.A1 ≤ M := d.A1_le_sup.trans (sup_le (sup_le (sup_le (sup_le
    (fun y hy => h1 hy.1 (d.comm_V4_WA4 hg hy))
    (fun y hy => h1 hy.1 (by
      rw [d.WA_six_eq] at hy
      exact commutatorElement_eq_one_iff_mul_comm.2
        (mem_centralizer_iff.1 (d.W11_le_centralizer_S hy) g hgS))))
    (fun y hy => h1 hy.1 (by
      rw [d.WA_five_eq] at hy
      exact commutatorElement_eq_one_iff_mul_comm.2
        (mem_centralizer_iff.1 (d.W12_le_centralizer_P hy) g (h.V_le_P .i4 hg)))))
    (fun y hy => h1 hy.1 (d.comm_V4_WA9 hg hy)))
    (fun y hy => ⟨hy.1, d.comm_V4_WA10_mem hg hy⟩))
  exact (hle ha).2

theorem commutator_R_A1_le : ⁅h.R, d.A1⁆ ≤ d.W12 := by
  let X : Subgroup G :=
    { carrier := {g | g ∈ h.R ∧ ∀ a ∈ d.A1, ⁅g, a⁆ ∈ d.W12}
      mul_mem' := fun {g g'} hg hg' => ⟨mul_mem hg.1 hg'.1, fun a ha => by
        rw [commutatorElement_mul_left_eq, mem_centralizer_iff.1
          (d.W12_le_centralizer_R (hg'.2 a ha)) g hg.1, mul_inv_cancel_right]
        exact mul_mem (hg'.2 a ha) (hg.2 a ha)⟩
      one_mem' := ⟨one_mem _, fun a _ => by rw [commutatorElement_one_left]; exact one_mem _⟩
      inv_mem' := fun {g} hg => ⟨inv_mem hg.1, fun a ha => by
        have e : ⁅g⁻¹, a⁆ = g⁻¹ * ⁅g, a⁆⁻¹ * g := by simp only [commutatorElement_def]; group
        rw [e, mul_assoc, ← mem_centralizer_iff.1 (d.W12_le_centralizer_R (inv_mem (hg.2 a ha)))
          g hg.1, inv_mul_cancel_left]
        exact inv_mem (hg.2 a ha)⟩ }
  have hXJ : ∀ {j : G}, j ∈ h.J → ∀ {g : G}, g ∈ X → j * g * j⁻¹ ∈ X := fun {j} hj {g} hg =>
    ⟨(mem_normalizer_iff.1 (mem_inf.1 hj).2 g).1 hg.1, fun a ha => by
      have ha' : j⁻¹ * a * j ∈ d.A1 := by
        have := d.conj_J_mem_A1 (inv_mem hj) ha
        rwa [inv_inv] at this
      have e : ⁅j * g * j⁻¹, a⁆ = j * ⁅g, j⁻¹ * a * j⁆ * j⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (mem_normalizer_iff.1 (d.J_le_normalizer_W12 hj) _).1 (hg.2 _ ha')⟩
  have h1 : ∀ {g : G}, g ∈ h.R → (∀ a ∈ d.A1, ⁅g, a⁆ = 1) → g ∈ X := fun {g} hg h1 =>
    ⟨hg, fun a ha => by rw [h1 a ha]; exact one_mem _⟩
  have h4 : h.V .i4 ≤ X := fun g hg => ⟨h.V4_le_R hg, fun a ha => d.comm_V4_A1_mem hg ha⟩
  have h5 : h.V .i5 ≤ X := fun g hg => h1 (h.V5_le_R hg) fun a ha =>
    commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_iff.1 (d.A1_le_centralizer_V5 ha) g hg)
  have hR₁ : h.R₁ ≤ X := fun g hg => h1 (h.R₁_le_R hg) fun a ha =>
    commutatorElement_eq_one_iff_mul_comm.2
      (mem_centralizer_iff.1 (d.A1_le_centralizer_R₁ ha) g hg)
  have hconj : ∀ {i : Idx}, i ≠ .i1 → i ≠ .i2 → h.V i ≤ X → h.V i.rPerm ≤ X :=
    fun {i} hi1 hi2 hi g hg => by
      have hrr := h.r_inv
      have hg' : h.r * g * h.r⁻¹ ∈ h.V i.rPerm.rPerm :=
        h.conj_r_mem_V (i := i.rPerm) (by cases i <;> simp_all [Idx.rPerm])
          (by cases i <;> simp_all [Idx.rPerm]) hg
      have hrr' : i.rPerm.rPerm = i := by cases i <;> simp_all [Idx.rPerm]
      rw [hrr'] at hg'
      have := hXJ h.r_mem_J (hi hg')
      rwa [show h.r * (h.r * g * h.r⁻¹) * h.r⁻¹ = g by
        rw [hrr, show h.r * (h.r * g * h.r) * h.r = (h.r * h.r) * g * (h.r * h.r) by group,
          h.r_mul_self_s_mul_self.1, one_mul, mul_one]] at this
  have h6 : h.V .i6 ≤ X := hconj (i := .i4) (by decide) (by decide) h4
  have h7 : h.V .i7 ≤ X := h.V_le_of_forall_elt_mem fun c => by
    have h1N : h.elt (rootElt h.K h.a .i1 1) ∈ h.J :=
      h.N1_le_J (h.V_le_N .i1 (h.elt_rootElt_mem_V .i1 1))
    have hc : ⁅h.elt (rootElt h.K h.a .i1 1), h.elt (rootElt h.K h.a .i4 c)⁆ ∈ X := by
      rw [commutatorElement_def]
      exact mul_mem (hXJ h1N (h4 (h.elt_rootElt_mem_V .i4 c)))
        (inv_mem (h4 (h.elt_rootElt_mem_V .i4 c)))
    rw [h.elt_comm_one_four] at hc
    have h6c := h6 (h.elt_rootElt_mem_V .i6 c)
    have h5c := h5 (h.elt_rootElt_mem_V .i5 (largeReeSigma h.a c))
    have h9c := hR₁ (h.elt_rootElt_mem_R₁ (k := .i9) rfl (c * largeReeSigma h.a c))
    have h11c := hR₁ (h.elt_rootElt_mem_R₁ (k := .i11) rfl (c * largeReeSigma h.a c))
    have := mul_mem (mul_mem (inv_mem h6c) hc) (inv_mem (mul_mem (mul_mem h5c h9c) h11c))
    convert this using 1
    group
  have h3 : h.V .i3 ≤ X := hconj (i := .i7) (by decide) (by decide) h7
  have hRX : h.R ≤ X := h.pull_rootJoin_le fun k hk => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact (h.V_le_R₁ (by decide)).trans hR₁
    · exact (h.V_le_R₁ (by decide)).trans hR₁
  exact (commutator_le).2 fun g hg a ha => (hRX hg).2 a ha

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4

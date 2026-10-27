module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootB4W

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

theorem exists_eq_elt_rootElt_mul_of_isSz {i : Idx} (hi : i.isSz = true) {w : G}
    (hw : w ∈ h.V i) : ∃ c e : h.K,
      w = h.elt (rootElt h.K h.a i c) * h.elt (rootElt h.K h.a i.center e) := by
  obtain ⟨g, hg, -, rfl⟩ := (h.mem_pull_iff_elt).1 hw
  have hg' : g ∈ (rootV h.K h.a i : Set (ModGL F4.tag h.K)) := hg
  rw [coe_rootV h.card_K] at hg'
  obtain ⟨x, hx, rfl⟩ := hg'
  have hcz : i.center.isCenter = true ∧ i.center.fourIdx = i.fourIdx := by
    cases i <;> simp_all [Idx.isSz, Idx.center, Idx.isCenter, Idx.fourIdx]
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  refine ⟨x i.coord, x i.center.coord, ?_⟩
  rw [(sylowVec_eq_of_supp i hx).1 hi, fourCoordG_eq_mul h.card_K,
    ← (rootElt_eq_coord i _).1 hi, ← hcz.2, ← (rootElt_eq_coord _ _).2.1 hcz.1,
    h.elt_mul' (hΓ _ _) (hΓ _ _)]

end Setup

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

@[expose] def IsLift5 (x : G) (c : h.K) : Prop :=
  x ∈ d.W ∧ (h.elt (rootElt h.K h.a .i5 c))⁻¹ * ⁅x, h.t⁆ ∈ d.W12

theorem W12_mul_comm {z w : G} (hz : z ∈ d.W12) (hw : w ∈ d.W) : z * w = w * z :=
  ((mem_zIn.1 hz).1 w hw).symm

theorem mem_V5_sup_W12_of_comm {u : G} (hu : u ∈ d.W) (hut : ⁅u, h.t⁆ ∈ d.W12) :
    u ∈ h.V .i5 ⊔ d.W12 := by
  have h1 := d.bender.mem_of_comm u⁻¹ (inv_mem hu) (by
    have e : u⁻¹⁻¹ * (h.t⁻¹ * u⁻¹ * h.t) = ⁅u, h.t⁆ := by
      rw [inv_inv, commutatorElement_def, h.t_inv]
      group
    rw [e]
    exact hut)
  have := inv_mem h1
  rwa [inv_inv] at this

theorem exists_isLift5 {w : G} (hw : w ∈ d.W) : ∃ c : h.K, d.IsLift5 w c := by
  obtain ⟨v, hv, z, hz, hwt⟩ := exists_mul_of_mem_sup_zIn d.bender.le (d.comm_t_mem_V5_sup_W12 hw)
  obtain ⟨c, e, rfl⟩ := h.exists_eq_elt_rootElt_mul_of_isSz (i := .i5) rfl hv
  refine ⟨c, hw, ?_⟩
  rw [hwt, show (h.elt (rootElt h.K h.a .i5 c))⁻¹ * (h.elt (rootElt h.K h.a .i5 c) *
    h.elt (rootElt h.K h.a Idx.i5.center e) * z) = h.elt (rootElt h.K h.a Idx.i5.center e) * z
      by group]
  exact mul_mem (d.V12_le_W12 (h.elt_rootElt_mem_V Idx.i5.center e)) hz

theorem inv_mul_mem_of_isLift5 {x x' : G} {c : h.K} (hx : d.IsLift5 x c) (hx' : d.IsLift5 x' c) :
    x⁻¹ * x' ∈ h.V .i5 ⊔ d.W12 := by
  refine d.mem_V5_sup_W12_of_comm (mul_mem (inv_mem hx.1) hx'.1) ?_
  set v := h.elt (rootElt h.K h.a .i5 c)
  have hvW : v ∈ d.W := d.bender.le (h.elt_rootElt_mem_V .i5 c)
  have e : ⁅x⁻¹ * x', h.t⁆ =
      x⁻¹ * (v * ((v⁻¹ * ⁅x', h.t⁆) * (v⁻¹ * ⁅x, h.t⁆)⁻¹) * v⁻¹) * x⁻¹⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  refine (mem_normalizer_iff.1 (le_normalizer_zIn d.W (inv_mem hx.1)) _).1 ?_
  exact (mem_normalizer_iff.1 (le_normalizer_zIn d.W hvW) _).1 (mul_mem hx'.2 (inv_mem hx.2))

theorem isLift5_mul {x x' : G} {c e : h.K} (hx : d.IsLift5 x c) (hx' : d.IsLift5 x' e) :
    d.IsLift5 (x * x') (c + e) := by
  refine ⟨mul_mem hx.1 hx'.1, ?_⟩
  set v := h.elt (rootElt h.K h.a .i5 c)
  set v' := h.elt (rootElt h.K h.a .i5 e)
  have hvW : v ∈ d.W := d.bender.le (h.elt_rootElt_mem_V .i5 c)
  have hv'W : v' ∈ d.W := d.bender.le (h.elt_rootElt_mem_V .i5 e)
  set z := v⁻¹ * ⁅x, h.t⁆ with hz
  set z' := v'⁻¹ * ⁅x', h.t⁆ with hz'
  have hxt : ⁅x, h.t⁆ = v * z := by rw [hz]; group
  have hxt' : ⁅x', h.t⁆ = v' * z' := by rw [hz']; group
  set β := ⁅x, v'⁆ with hβ
  have hβW : β ∈ d.W12 := d.comm_W_mem_W12 hx.1 hv'W
  have hmul := h.elt_rootElt_mul_of_isSz (k := .i5) rfl e c
  set w12 := h.elt (rootElt h.K h.a Idx.i5.center (largeReeSigma h.a e * c)) with hw12
  have hw12W : w12 ∈ d.W12 := d.V12_le_W12 (h.elt_rootElt_mem_V .i12 _)
  have e1 : ⁅x * x', h.t⁆ = β * v' * z' * v * z := by
    rw [commutatorElement_mul_left_eq, hxt', hxt, hβ]
    simp only [commutatorElement_def]
    have hz'c : x * z' = z' * x := (d.W12_mul_comm hx'.2 hx.1).symm
    calc x * (v' * z') * x⁻¹ * (v * z) = x * v' * (z' * x⁻¹) * (v * z) := by group
      _ = x * v' * (x⁻¹ * z') * (v * z) := by
        rw [show z' * x⁻¹ = x⁻¹ * z' from by
          calc z' * x⁻¹ = x⁻¹ * (x * z') * x⁻¹ := by group
            _ = x⁻¹ * (z' * x) * x⁻¹ := by rw [hz'c]
            _ = x⁻¹ * z' := by group]
      _ = x * v' * x⁻¹ * v'⁻¹ * v' * z' * v * z := by group
  have hcomm : ∀ {a : G}, a ∈ d.W12 → ∀ {b : G}, b ∈ d.W → a * b = b * a :=
    fun ha _ hb => d.W12_mul_comm ha hb
  have e2 : (h.elt (rootElt h.K h.a .i5 (c + e)))⁻¹ * ⁅x * x', h.t⁆ =
      β * z' * z * ((h.elt (rootElt h.K h.a .i5 (e + c)))⁻¹ * (v' * v)) := by
    rw [e1, add_comm c e]
    have hz'v : z' * v = v * z' := hcomm hx'.2 hvW
    set u := h.elt (rootElt h.K h.a .i5 (e + c)) with hu
    have huW : u ∈ d.W := d.bender.le (h.elt_rootElt_mem_V .i5 _)
    have hβu : u⁻¹ * β = β * u⁻¹ := (hcomm hβW (inv_mem huW)).symm
    calc u⁻¹ * (β * v' * z' * v * z) = u⁻¹ * β * v' * (z' * v) * z := by group
      _ = β * u⁻¹ * v' * (v * z') * z := by rw [hβu, hz'v]
      _ = β * (u⁻¹ * v' * v) * z' * z := by
        rw [show β * u⁻¹ * v' * (v * z') * z = β * (u⁻¹ * v' * v) * (z' * z) by group]
        group
      _ = β * z' * z * (u⁻¹ * (v' * v)) := by
        have h1 : (u⁻¹ * v' * v) * z' = z' * (u⁻¹ * v' * v) :=
          (hcomm hx'.2 (mul_mem (mul_mem (inv_mem huW) hv'W) hvW)).symm
        have h2 : (u⁻¹ * v' * v) * z = z * (u⁻¹ * v' * v) :=
          (hcomm hx.2 (mul_mem (mul_mem (inv_mem huW) hv'W) hvW)).symm
        calc β * (u⁻¹ * v' * v) * z' * z = β * ((u⁻¹ * v' * v) * z') * z := by group
          _ = β * (z' * (u⁻¹ * v' * v)) * z := by rw [h1]
          _ = β * z' * ((u⁻¹ * v' * v) * z) := by group
          _ = β * z' * (z * (u⁻¹ * v' * v)) := by rw [h2]
          _ = β * z' * z * (u⁻¹ * (v' * v)) := by group
  rw [e2, hmul]
  rw [show (h.elt (rootElt h.K h.a .i5 (e + c)))⁻¹ * (h.elt (rootElt h.K h.a .i5 (e + c)) * w12)
    = w12 by group]
  exact mul_mem (mul_mem (mul_mem hβW hx'.2) hx.2) hw12W

theorem isLift5_conj {x : G} {c : h.K} (hx : d.IsLift5 x c) (τ : h.Kˣ × h.Kˣ) :
    d.IsLift5 (h.elt (torusPair h.a τ) * x * (h.elt (torusPair h.a τ))⁻¹)
      ((rootChar h.K h.a .i5 τ : h.K) * c) := by
  set b := h.elt (torusPair h.a τ) with hb
  have hbH : b ∈ h.H := h.elt_torusPair_mem_H τ
  refine ⟨(mem_normalizer_iff.1 (d.H_le_normalizer_W hbH) x).1 hx.1, ?_⟩
  have hbt : b * h.t * b⁻¹ = h.t := by rw [h.mul_t_comm (h.H_le_L hbH), mul_inv_cancel_right]
  have e1 : ⁅b * x * b⁻¹, h.t⁆ = b * ⁅x, h.t⁆ * b⁻¹ := by
    simp only [commutatorElement_def]
    conv_lhs => rw [← hbt]
    group
  rw [e1, ← h.elt_torusPair_conj_rootElt τ .i5 c, ← hb,
    show (b * h.elt (rootElt h.K h.a .i5 c) * b⁻¹)⁻¹ * (b * ⁅x, h.t⁆ * b⁻¹) =
      b * ((h.elt (rootElt h.K h.a .i5 c))⁻¹ * ⁅x, h.t⁆) * b⁻¹ by group]
  exact d.conj_H_mem_W12 hbH hx.2

theorem r1c_eq_zero_of_W_hom {i : Idx} (hi : i.isCenter = false) {ψ : G → G}
    (hψR : ∀ x ∈ d.W, ψ x ∈ h.R₁)
    (hmul : ∀ x ∈ d.W, ∀ x' ∈ d.W, ψ (x * x') = ψ x * ψ x')
    (hconst : ∀ x ∈ d.W, ∀ u ∈ h.V .i5 ⊔ d.W12, ψ (x * u) = ψ x)
    (hequiv : ∀ τ : h.Kˣ × h.Kˣ, torusPair h.a τ ∈ torusHi h.K h.a i → ∀ x ∈ d.W,
      ψ (h.elt (torusPair h.a τ) * x * (h.elt (torusPair h.a τ))⁻¹) =
        h.elt (torusPair h.a τ) * ψ x * (h.elt (torusPair h.a τ))⁻¹)
    {k : Idx} (hk : k.isR1 = true) (hb : Idx.brace i .i5 ≠ Idx.brace i k) {x : G}
    (hx : x ∈ d.W) : h.r1c (ψ x) k = 0 := by
  classical
  have hlift : ∀ c : h.K, ∃ y, d.IsLift5 y c := fun c => by
    obtain ⟨y, hyW, -, hy⟩ := d.exists_W_B4_comm_t (h.elt_rootElt_mem_V .i5 c)
    exact ⟨y, hyW, hy⟩
  choose L hL using hlift
  have hwd : ∀ {y : G} {c : h.K}, d.IsLift5 y c → ψ y = ψ (L c) := fun {y c} hy => by
    have e : y = L c * ((L c)⁻¹ * y) := by group
    rw [e, hconst _ (hL c).1 _ (d.inv_mul_mem_of_isLift5 (hL c) hy)]
  set φ : h.K → h.K := fun c => h.r1c (ψ (L c)) k with hφ
  have hadd : ∀ c e : h.K, φ (c + e) = φ c + φ e := fun c e => by
    simp only [hφ]
    rw [← hwd (d.isLift5_mul (hL c) (hL e)), hmul _ (hL c).1 _ (hL e).1,
      h.r1c_mul (hψR _ (hL c).1) (hψR _ (hL e).1) hk]
  have hequiv' : ∀ τ : h.Kˣ × h.Kˣ, torusPair h.a τ ∈ torusHi h.K h.a i → ∀ c : h.K,
      φ ((rootChar h.K h.a .i5 τ : h.K) * c) = (rootChar h.K h.a k τ : h.K) * φ c := by
    intro τ hτ c
    simp only [hφ]
    rw [← hwd (d.isLift5_conj (hL c) τ), hequiv τ hτ _ (hL c).1,
      h.r1c_torus (hψR _ (hL c).1) τ hk]
  obtain ⟨c, hc⟩ := d.exists_isLift5 hx
  rw [hwd hc]
  exact miyamoto_2_1 h.one_le_a h.card_K hi hb hadd hequiv' c

theorem V5_sup_W12_le_centralizer_B1 : h.V .i5 ⊔ d.W12 ≤ centralizer (d.B1 : Set G) :=
  sup_le (fun v hv => mem_centralizer_iff.2 fun y hy =>
      (mem_centralizer_iff.1 (d.B1_le_centralizer_S hy) v
        (h.V_le_S (k := .i5) (by decide) hv)).symm)
    fun z hz => mem_centralizer_iff.2 fun y hy => d.B1_comm hy (d.W12_le_B1 hz)

theorem comm_W_W11 {x y : G} (hx : x ∈ d.W) (hy : y ∈ d.W11) : ⁅x, y⁆ = 1 := by
  have hyB : y ∈ d.B2 := mem_sup_right (d.W11_le_B1 hy)
  have hS1 : ∀ {z : G}, z ∈ d.W → ⁅z, y⁆ ∈ h.S₁ := fun hz => (d.W_le_B4 hz).2.2.2.1 y hyB
  have hS12 : h.S₁ ≤ h.S₂ := h.S₁_le_S₂_le_S₃_le_S₄_le_S.1
  have hmul : ∀ z ∈ d.W, ∀ z' ∈ d.W, ⁅z * z', y⁆ = ⁅z, y⁆ * ⁅z', y⁆ := fun z hz z' hz' => by
    rw [commutatorElement_mul_left_eq, ← mem_centralizer_iff.1 (d.W_le_B4 hz).2.1 _
      (hS12 (hS1 hz')), mul_inv_cancel_right]
    exact h.R₁_comm (h.S₁_le_R₁ (hS1 hz')) (h.S₁_le_R₁ (hS1 hz))
  have hconst : ∀ z ∈ d.W, ∀ u ∈ h.V .i5 ⊔ d.W12, ⁅z * u, y⁆ = ⁅z, y⁆ := fun z _ u hu => by
    rw [commutatorElement_mul_left_eq, commutatorElement_eq_one_iff_mul_comm.2
      (mem_centralizer_iff.1 (d.V5_sup_W12_le_centralizer_B1 hu) y (d.W11_le_B1 hy)).symm]
    group
  have hequiv : ∀ τ : h.Kˣ × h.Kˣ, torusPair h.a τ ∈ torusHi h.K h.a .i6 → ∀ z ∈ d.W,
      ⁅h.elt (torusPair h.a τ) * z * (h.elt (torusPair h.a τ))⁻¹, y⁆ =
        h.elt (torusPair h.a τ) * ⁅z, y⁆ * (h.elt (torusPair h.a τ))⁻¹ := fun τ hτ z _ => by
    have hbH : h.elt (torusPair h.a τ) ∈ h.Ht .i6 := (h.elt_torusPair_mem_Ht_iff τ).2 hτ
    have hby : h.elt (torusPair h.a τ) * y * (h.elt (torusPair h.a τ))⁻¹ = y := by
      rw [mem_centralizer_iff.1 (d.W11_le_CH6 hy) _ hbH, mul_inv_cancel_right]
    simp only [commutatorElement_def]
    conv_lhs => rw [← hby]
    group
  have hR : ∀ z ∈ d.W, ⁅z, y⁆ ∈ h.R₁ := fun z hz => h.S₁_le_R₁ (hS1 hz)
  have h11 := d.r1c_eq_zero_of_W_hom (i := .i6) rfl hR hmul hconst hequiv (k := .i11) rfl
    (by decide) hx
  have h12 := d.r1c_eq_zero_of_W_hom (i := .i6) rfl hR hmul hconst hequiv (k := .i12) rfl
    (by decide) hx
  have hS : ∀ l ∈ ({.i11, .i12} : Finset Idx), l.isR1 = true := by decide
  have hx' : ⁅x, y⁆ ∈ h.pull (rootJoin h.K h.a {.i11, .i12}) := hS1 hx
  have h0 : ∀ l : Idx, l.isR1 = true → l ∉ (∅ : Finset Idx) → h.r1c ⁅x, y⁆ l = 0 := by
    intro l hl _
    by_cases hl11 : l = .i11
    · rw [hl11]; exact h11
    by_cases hl12 : l = .i12
    · rw [hl12]; exact h12
    exact h.r1c_eq_zero_of_mem hS hx' hl (by simp [hl11, hl12])
  have hmem := h.mem_of_r1c_eq_zero (hR x hx) h0
  have hbot : rootJoin h.K h.a (∅ : Finset Idx) = ⊥ := by simp [rootJoin]
  rw [hbot, h.pull_bot] at hmem
  exact (mem_bot).1 hmem

theorem W_le_centralizer_B1 : d.W ≤ centralizer (d.B1 : Set G) := fun x hx => by
  have hle : d.B1 ≤ centralizer ({x} : Set G) :=
    sup_le (fun y hy => mem_centralizer_singleton_iff.2
      (commutatorElement_eq_one_iff_mul_comm.1 (d.comm_W_W11 hx hy)).symm)
      fun z hz => mem_centralizer_singleton_iff.2 (d.W12_mul_comm hz hx)
  exact mem_centralizer_iff.2 fun b hb => mem_centralizer_singleton_iff.1 (hle hb)

theorem Kp_le_normalizer_imIn {M : Subgroup G} (hM : M ≤ d.B4)
    (hMK : h.Kp ≤ normalizer (M : Set G)) : h.Kp ≤ normalizer (d.imIn M hM : Set G) := by
  have key : ∀ {k : G}, k ∈ h.Kp → ∀ v ∈ d.imIn M hM, k * v * k⁻¹ ∈ d.imIn M hM := by
    intro k hk v hv
    obtain ⟨x, hx, b, hb, rfl⟩ := hv
    have hkt : k * h.t * k⁻¹ = h.t := by
      rw [mem_centralizer_singleton_iff.1 hk.1, mul_inv_cancel_right]
    refine ⟨k * x * k⁻¹, (mem_normalizer_iff.1 (hMK hk) x).1 hx, k * b * k⁻¹,
      (mem_normalizer_iff.1 (d.Kp_le_normalizer_B2 hk) b).1 hb, ?_⟩
    simp only [commutatorElement_def]
    conv_rhs => rw [← hkt]
    group
  intro k hk
  refine mem_normalizer_of_conj_mem (key hk) fun v hv => ?_
  have := key (inv_mem hk) v hv
  rwa [inv_inv] at this

theorem eq_B4_of_S₄_le_imIn {M : Subgroup G} (hM : M ≤ d.B4) (hQ : d.Q4 ≤ M)
    (hS : h.S₄ ≤ d.imIn M hM) : M = d.B4 := by
  refine le_antisymm hM fun x hx => ?_
  obtain ⟨v, hv, b, hb, hvb⟩ : ∃ v ∈ h.S₄, ∃ b ∈ d.B2, ⁅x, h.t⁆ = v * b := by
    have hxQ : ⁅x, h.t⁆ ∈ ((h.S₄ ⊔ d.B2 : Subgroup G) : Set G) := hx.2.2.2.2
    rw [coe_mul_of_left_le_normalizer_right _ _ (h.S₄_le_Kp.trans d.Kp_le_normalizer_B2),
      Set.mem_mul] at hxQ
    obtain ⟨v, hv, b, hb, e⟩ := hxQ
    exact ⟨v, hv, b, hb, e.symm⟩
  obtain ⟨m, hm, b', hb', hmv⟩ := hS hv
  have hq : m⁻¹ * x ∈ d.Q4 := d.inv_mul_mem_Q4_of_comm (hM hm) hx (by
    have e : ⁅m, h.t⁆⁻¹ * ⁅x, h.t⁆ = b' * b := by
      rw [hvb, hmv]
      group
    rw [e]
    exact mul_mem hb' hb)
  have e : x = m * (m⁻¹ * x) := by group
  rw [e]
  exact mul_mem hm (hQ hq)

theorem B4_le_centralizer_B1 : d.B4 ≤ centralizer (d.B1 : Set G) := by
  set Z := d.B4 ⊓ centralizer (d.B1 : Set G) with hZ
  have hZB : Z ≤ d.B4 := inf_le_left
  have hZK : h.Kp ≤ normalizer (Z : Set G) := fun k hk =>
    mem_normalizer_inf (d.Kp_le_normalizer_B4 hk)
      (mem_normalizer_centralizer (d.Kp_le_normalizer_B1 hk))
  have hS4B1 : h.S₄ ≤ centralizer (d.B1 : Set G) :=
    (h.S₂_le_S₃_le_S₄_le_S.2.2.1).trans (le_centralizer_iff.1 d.B1_le_centralizer_S)
  have hB2B1 : d.B2 ≤ centralizer (d.B1 : Set G) := fun b hb =>
    mem_centralizer_iff.2 fun y hy => d.B2_comm (mem_sup_right hy) hb
  have hQ : d.Q4 ≤ Z := le_inf d.Q4_le_B4 (sup_le hS4B1 hB2B1)
  have hW : d.W ≤ Z := le_inf d.W_le_B4 d.W_le_centralizer_B1
  have himK := d.Kp_le_normalizer_imIn hZB hZK
  have hS : h.S₄ ≤ d.imIn Z hZB := by
    refine h.S₄_le_of_V5 (fun v hv => ?_) (fun u hu => ?_)
      (fun c => himK (h.elt_rootElt_three_mem_Kp c)) (himK h.s_mem_Kp)
    · obtain ⟨b, hb, hbt⟩ := d.exists_B2_comm_t hv
      exact ⟨b, hQ (d.B2_le_Q4 hb), 1, one_mem _, by rw [mul_one, hbt]⟩
    · obtain ⟨c, hcW, -, hc⟩ := d.exists_W_B4_comm_t hu
      exact ⟨c, hW hcW, (u⁻¹ * ⁅c, h.t⁆)⁻¹, inv_mem (mem_sup_right (d.W12_le_B1 hc)), by group⟩
  have := d.eq_B4_of_S₄_le_imIn hZB hQ hS
  rw [← this]
  exact inf_le_right

theorem eq_A1_of_le {E : Subgroup G} (hEA : E ≤ d.A1) (hR : h.R₁ ≤ E) (hW : d.W11 ≤ E)
    (hJ : ∀ j ∈ h.J, j ∈ normalizer (E : Set G)) : E = d.A1 := by
  let M : Subgroup G :=
    { carrier := {v | v ∈ h.R₁ ∧ ∃ x ∈ E, ⁅x, h.t⁆ = v}
      mul_mem' := fun {v v'} hv hv' => by
        obtain ⟨hvR, x, hx, rfl⟩ := hv
        obtain ⟨hvR', x', hx', rfl⟩ := hv'
        exact ⟨mul_mem hvR hvR', x * x', mul_mem hx hx',
          d.comm_t_mul_A1 (hEA hx) (hEA hx')⟩
      one_mem' := ⟨one_mem _, 1, one_mem _, commutatorElement_one_left _⟩
      inv_mem' := fun {v} hv => by
        obtain ⟨hvR, x, hx, rfl⟩ := hv
        exact ⟨inv_mem hvR, x⁻¹, inv_mem hx, d.comm_t_inv_A1 (hEA hx)⟩ }
  have hMR : M ≤ h.R₁ := fun v hv => hv.1
  have hconj : ∀ {j : G}, j ∈ h.J → ∀ v ∈ M, j * v * j⁻¹ ∈ M := by
    intro j hj v hv
    obtain ⟨hvR, x, hx, rfl⟩ := hv
    have hjt : j * h.t * j⁻¹ = h.t := by
      rw [mem_centralizer_singleton_iff.1 hj.1, mul_inv_cancel_right]
    refine ⟨(mem_normalizer_iff.1 (h.J_le_normalizer_R₁ hj) _).1 hvR, j * x * j⁻¹,
      (mem_normalizer_iff.1 (hJ j hj) x).1 hx, ?_⟩
    simp only [commutatorElement_def]
    conv_lhs => rw [← hjt]
    group
  have hnorm : ∀ {j : G}, j ∈ h.J → j ∈ normalizer (M : Set G) := fun {j} hj =>
    mem_normalizer_of_conj_mem (hconj hj) fun v hv => by
      have := hconj (inv_mem hj) v hv
      rwa [inv_inv] at this
  have h1J : h.elt (rootElt h.K h.a .i1 1) ∈ h.J :=
    h.P_sup_Tsyl_le_J_Kp.1 (mem_sup_left (h.V_le_P .i1 (h.elt_rootElt_mem_V .i1 1)))
  have hMeq : M = h.R₁ := by
    by_contra hne
    have hle := h.le_V12_of_invariant hMR (fun b hb => hnorm (h.H_le_J hb)) (hnorm h1J)
      (hnorm h.r_mem_J) hne
    obtain ⟨y, hy, hyt⟩ := d.exists_W11_comm_t (h.elt_rootElt_mem_V .i11 1)
    have hmem : h.elt (rootElt h.K h.a .i11 1) ∈ M :=
      ⟨h.V_le_R₁ (by decide) (h.elt_rootElt_mem_V .i11 1), y, hW hy, hyt⟩
    exact h.elt_rootElt_one_ne_one .i11
      (h.eq_one_of_mem_V11_of_mem_V12 (h.elt_rootElt_mem_V .i11 1) (hle hmem))
  refine le_antisymm hEA fun x hx => ?_
  have hxM : ⁅x, h.t⁆ ∈ M := by rw [hMeq]; exact hx.2.2
  obtain ⟨-, e, he, het⟩ := hxM
  have hr : e⁻¹ * x ∈ h.R₁ := d.mem_R₁_of_mem_A1 (mul_mem (inv_mem (hEA he)) hx) (by
    rw [d.comm_t_mul_A1 (inv_mem (hEA he)) hx, d.comm_t_inv_A1 (hEA he), het, inv_mul_cancel])
  have e2 : x = e * (e⁻¹ * x) := by group
  rw [e2]
  exact mul_mem he (hR hr)

theorem A1_le_centralizer_A1 : d.A1 ≤ centralizer (d.A1 : Set G) := by
  have hE := d.eq_A1_of_le (E := d.A1 ⊓ centralizer (d.A1 : Set G)) inf_le_left
    (le_inf d.R₁_le_A1 (le_centralizer_iff.1 d.A1_le_centralizer_R₁))
    (le_inf d.W11_le_A1 fun y hy => mem_centralizer_iff.2 fun x hx =>
      (mem_centralizer_iff.1 (d.B4_le_centralizer_B1 (d.A1_le_B4 hx)) y (d.W11_le_B1 hy)).symm)
    fun j hj => mem_normalizer_inf (d.J_le_normalizer_A1 hj)
      (mem_normalizer_centralizer (d.J_le_normalizer_A1 hj))
  exact fun x hx => (hE.ge hx).2

theorem A1_comm {x y : G} (hx : x ∈ d.A1) (hy : y ∈ d.A1) : x * y = y * x :=
  mem_centralizer_iff.1 (d.A1_le_centralizer_A1 hy) x hx

theorem A1_mul_self {x : G} (hx : x ∈ d.A1) : x * x = 1 := by
  let E : Subgroup G :=
    { carrier := {y | y ∈ d.A1 ∧ y * y = 1}
      mul_mem' := fun {y y'} hy hy' => ⟨mul_mem hy.1 hy'.1, by
        rw [show y * y' * (y * y') = y * (y' * y) * y' by group, ← d.A1_comm hy.1 hy'.1,
          show y * (y * y') * y' = (y * y) * (y' * y') by group, hy.2, hy'.2, one_mul]⟩
      one_mem' := ⟨one_mem _, mul_one 1⟩
      inv_mem' := fun {y} hy => ⟨inv_mem hy.1, by rw [← mul_inv_rev, hy.2, inv_one]⟩ }
  have hE := d.eq_A1_of_le (E := E) (fun y hy => hy.1)
    (fun y hy => ⟨d.R₁_le_A1 hy, h.R₁_mul_self hy⟩)
    (fun y hy => ⟨d.W11_le_A1 hy, d.W11_mul_self hy⟩)
    fun j hj => mem_normalizer_of_conj_mem
      (fun y hy => ⟨d.conj_J_mem_A1 hj hy.1, by
        rw [show j * y * j⁻¹ * (j * y * j⁻¹) = j * (y * y) * j⁻¹ by group, hy.2]; group⟩)
      fun y hy => ⟨by simpa using d.conj_J_mem_A1 (inv_mem hj) hy.1, by
        rw [show j⁻¹ * y * j * (j⁻¹ * y * j) = j⁻¹ * (y * y) * j by group, hy.2]; group⟩
  exact (hE.ge hx).2

theorem _root_.CFSG.LocalAnalysis.EvenBN.TwoF4.Setup.eq_one_of_mem_V10_of_conj_mem
    (h : Setup G) {z : G} (hz : z ∈ h.V .i10)
    (hc : h.elt (rootElt h.K h.a .i1 1) * z * (h.elt (rootElt h.K h.a .i1 1))⁻¹ ∈ h.V .i10) :
    z = 1 := by
  obtain ⟨c, rfl⟩ := h.exists_eq_elt_rootElt (i := .i10) rfl hz
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  have h1 : ⁅h.elt (rootElt h.K h.a .i1 1), h.elt (rootElt h.K h.a .i10 c)⁆ =
      h.elt (rootElt h.K h.a .i11 c) := by
    rw [← h.elt_commutator (hΓ _ _) (hΓ _ _), rootElt_comm_1_10 h.card_K, one_mul]
  have e : h.elt (rootElt h.K h.a .i1 1) * h.elt (rootElt h.K h.a .i10 c) *
      (h.elt (rootElt h.K h.a .i1 1))⁻¹ =
        h.elt (rootElt h.K h.a .i11 c) * h.elt (rootElt h.K h.a .i10 c) := by
    rw [← h1, commutatorElement_def]
    group
  rw [e] at hc
  have h11 : h.elt (rootElt h.K h.a .i11 c) ∈ h.V .i10 := by
    have := mul_mem hc (inv_mem (h.elt_rootElt_mem_V .i10 c))
    rwa [mul_inv_cancel_right] at this
  have hS : ∀ l ∈ ({.i10} : Finset Idx), l.isR1 = true := by decide
  have h11' : h.elt (rootElt h.K h.a .i11 c) ∈ h.pull (rootJoin h.K h.a {.i10}) := by
    rw [h.pull_rootJoin_singleton]
    exact h11
  have hr := h.r1c_eq_zero_of_mem hS h11' (k := .i11) rfl (by decide)
  rw [h.r1c_elt_rootElt rfl c rfl, Pi.single_eq_same] at hr
  rw [hr, rootElt_zero, h.elt_one']

theorem W7_comm_WA10 {x y : G} (hx : x ∈ d.W7) (hy : y ∈ d.WA .i10) : x * y = y * x := by
  have h1 := d.A1_comm ((d.mem_W7_iff).1 hx).1 (d.conj_s_mem_WA10 hy).1
  have e : x * y = h.s⁻¹ * ((h.s * x * h.s⁻¹) * (h.s * y * h.s⁻¹)) * h.s := by group
  rw [e, h1]
  group

theorem B3_le_centralizer_B2 : d.B3 ≤ centralizer (d.B2 : Set G) := by
  rw [d.B3_eq]
  refine sup_le (sup_le (fun x hx => ?_) fun x hx => ?_) d.B2_le_centralizer_B2
  · have hle : d.B2 ≤ centralizer ({x} : Set G) :=
      sup_le (fun y hy => mem_centralizer_singleton_iff.2 (d.W7_comm_WA10 hx hy).symm)
        fun y hy => mem_centralizer_singleton_iff.2
          (mem_centralizer_iff.1 (d.W7_le_B3 hx).2.1 y hy)
    exact mem_centralizer_iff.2 fun b hb => mem_centralizer_singleton_iff.1 (hle hb)
  · exact mem_centralizer_iff.2 fun b hb => d.A1_comm (d.B2_le_A1 hb) hx.1

theorem comm_B3_mem_V10 {u v : G} (hu : u ∈ d.B3) (hv : v ∈ d.B3) : ⁅u, v⁆ ∈ h.V .i10 := by
  have hN : ∀ {x : G}, x ∈ d.B3 → x ∈ normalizer (h.V .i10 : Set G) := fun {x} hx =>
    Subgroup.centralizer_le_normalizer _
      (centralizer_le (SetLike.coe_subset_coe.2 (h.V_le_S₃ (k := .i10) (by decide))) hx.1)
  have one : ∀ {x y : G}, x * y = y * x → ⁅x, y⁆ ∈ h.V .i10 := fun hxy => by
    rw [commutatorElement_eq_one_iff_mul_comm.2 hxy]
    exact one_mem _
  have h7 : ∀ x ∈ d.W7, d.B3 ≤ commRightIn x (h.V .i10) := by
    intro x hx
    rw [d.B3_eq]
    refine sup_le (sup_le (fun y hy => ?_) fun y hy => ?_) fun y hy => ?_
    · exact mem_commRightIn.2 ⟨hN (d.W7_le_B3 hy), one (d.W7_comm hx hy)⟩
    · exact mem_commRightIn.2 ⟨hN (d.WA_le_B3 (Or.inl rfl) hy), d.comm_W7_WA9_mem_V10 hx hy⟩
    · exact mem_commRightIn.2 ⟨hN (d.B2_le_B3 hy),
        one (mem_centralizer_iff.1 (d.B3_le_centralizer_B2 (d.W7_le_B3 hx)) y hy).symm⟩
  have h9 : ∀ x ∈ d.WA .i9, d.B3 ≤ commRightIn x (h.V .i10) := by
    intro x hx
    rw [d.B3_eq]
    refine sup_le (sup_le (fun y hy => ?_) fun y hy => ?_) fun y hy => ?_
    · refine mem_commRightIn.2 ⟨hN (d.W7_le_B3 hy), ?_⟩
      rw [← commutatorElement_inv]
      exact inv_mem (d.comm_W7_WA9_mem_V10 hy hx)
    · exact mem_commRightIn.2 ⟨hN (d.WA_le_B3 (Or.inl rfl) hy), one (d.A1_comm hx.1 hy.1)⟩
    · exact mem_commRightIn.2 ⟨hN (d.B2_le_B3 hy), one (d.A1_comm hx.1 (d.B2_le_A1 hy))⟩
  have h2 : ∀ x ∈ d.B2, d.B3 ≤ commRightIn x (h.V .i10) := fun x hx y hy =>
    mem_commRightIn.2 ⟨hN hy, one (mem_centralizer_iff.1 (d.B3_le_centralizer_B2 hy) x hx)⟩
  have hle : d.B3 ≤ commLeftIn v (h.V .i10) := by
    rw [d.B3_eq]
    refine sup_le (sup_le (fun x hx => ?_) fun x hx => ?_) fun x hx => ?_
    · exact mem_commLeftIn.2 ⟨hN (d.W7_le_B3 hx), (mem_commRightIn.1 (h7 x hx hv)).2⟩
    · exact mem_commLeftIn.2 ⟨hN (d.WA_le_B3 (Or.inl rfl) hx), (mem_commRightIn.1 (h9 x hx hv)).2⟩
    · exact mem_commLeftIn.2 ⟨hN (d.B2_le_B3 hx), (mem_commRightIn.1 (h2 x hx hv)).2⟩
  exact (mem_commLeftIn.1 (hle hu)).2

theorem B3_comm {u v : G} (hu : u ∈ d.B3) (hv : v ∈ d.B3) : u * v = v * u := by
  set k := h.elt (rootElt h.K h.a .i1 1) with hk
  have hkK : k ∈ h.Kp := h.S₂_le_S₃_le_S₄_le_S.2.2.2.2
    (h.S₂_le_S₃_le_S₄_le_S.2.2.2.1 (h.V_le_S (k := .i1) (by decide) (h.elt_rootElt_mem_V _ _)))
  have h1 := d.comm_B3_mem_V10 hu hv
  have h2 := d.comm_B3_mem_V10 (d.conj_Kp_mem_B3 hkK hu) (d.conj_Kp_mem_B3 hkK hv)
  have e : ⁅k * u * k⁻¹, k * v * k⁻¹⁆ = k * ⁅u, v⁆ * k⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e] at h2
  exact commutatorElement_eq_one_iff_mul_comm.1 (h.eq_one_of_mem_V10_of_conj_mem h1 h2)

theorem B3_mul_self {x : G} (hx : x ∈ d.B3) : x * x = 1 := by
  let E : Subgroup G :=
    { carrier := {y | y ∈ d.B3 ∧ y * y = 1}
      mul_mem' := fun {y y'} hy hy' => ⟨mul_mem hy.1 hy'.1, by
        rw [show y * y' * (y * y') = y * (y' * y) * y' by group, ← d.B3_comm hy.1 hy'.1,
          show y * (y * y') * y' = (y * y) * (y' * y') by group, hy.2, hy'.2, one_mul]⟩
      one_mem' := ⟨one_mem _, mul_one 1⟩
      inv_mem' := fun {y} hy => ⟨inv_mem hy.1, by rw [← mul_inv_rev, hy.2, inv_one]⟩ }
  have hle : d.B3 ≤ E := by
    rw [d.B3_eq]
    refine sup_le (sup_le (fun y hy => ⟨d.W7_le_B3 hy, ?_⟩) fun y hy =>
      ⟨d.WA_le_B3 (Or.inl rfl) hy, d.A1_mul_self hy.1⟩) fun y hy =>
        ⟨d.B2_le_B3 hy, d.B2_mul_self hy⟩
    have h1 := d.A1_mul_self ((d.mem_W7_iff).1 hy).1
    calc y * y = h.s⁻¹ * ((h.s * y * h.s⁻¹) * (h.s * y * h.s⁻¹)) * h.s := by group
      _ = 1 := by rw [h1]; group
  exact (hle hx).2

theorem B4_le_centralizer_B2 : d.B4 ≤ centralizer (d.B2 : Set G) := by
  set Z := d.B4 ⊓ centralizer (d.B2 : Set G) with hZ
  have hZB : Z ≤ d.B4 := inf_le_left
  have hZK : h.Kp ≤ normalizer (Z : Set G) := fun k hk =>
    mem_normalizer_inf (d.Kp_le_normalizer_B4 hk)
      (mem_normalizer_centralizer (d.Kp_le_normalizer_B2 hk))
  have hQ : d.Q4 ≤ Z := le_inf d.Q4_le_B4
    (sup_le (le_centralizer_iff.1 d.B2_le_centralizer_S₄) d.B2_le_centralizer_B2)
  have hA : d.A1 ≤ Z := le_inf d.A1_le_B4 fun x hx =>
    mem_centralizer_iff.2 fun b hb => d.A1_comm (d.B2_le_A1 hb) hx
  have himK := d.Kp_le_normalizer_imIn hZB hZK
  have hV : ∀ {i k : Idx}, i.isCenter = false → k = i ∨ k = i.center →
      k ∈ ({.i8, .i9, .i10, .i11, .i12} : Finset Idx) → h.V k ≤ d.imIn Z hZB := by
    intro i k hi hk hkR v hv
    obtain ⟨w, hw, hwt⟩ := d.exists_WA_comm_t (i := i) (h.V_le_R₁ hkR) (h.V_le_CH hi hk) hv
    exact ⟨w, hA hw.1, 1, one_mem _, by rw [mul_one, hwt]⟩
  have hS : h.S₄ ≤ d.imIn Z hZB := by
    refine h.S₄_le_of_V8_V9 (fun v hv => ?_) (hV (i := .i4) rfl (Or.inr rfl) (by decide))
      (hV (i := .i9) rfl (Or.inl rfl) (by decide))
      (fun c => himK (h.elt_rootElt_three_mem_Kp c)) (himK h.s_mem_Kp)
      fun b hb => himK (h.H_le_Kp hb)
    obtain ⟨b, hb, hbt⟩ := d.exists_B2_comm_t hv
    exact ⟨b, hQ (d.B2_le_Q4 hb), 1, one_mem _, by rw [mul_one, hbt]⟩
  have := d.eq_B4_of_S₄_le_imIn hZB hQ hS
  rw [← this]
  exact inf_le_right

theorem zIn_B4 : zIn d.B4 = d.B2 := by
  have hZ : ∀ {q : G}, q ∈ d.Q4 → q ∈ centralizer (h.S₄ : Set G) → q ∈ d.B2 := by
    intro q hq hqc
    have hqQ : q ∈ ((h.S₄ ⊔ d.B2 : Subgroup G) : Set G) := hq
    rw [coe_mul_of_left_le_normalizer_right _ _ (h.S₄_le_Kp.trans d.Kp_le_normalizer_B2),
      Set.mem_mul] at hqQ
    obtain ⟨v, hv, b, hb, rfl⟩ := hqQ
    have hvc : v ∈ centralizer (h.S₄ : Set G) := by
      have := mul_mem hqc (inv_mem (d.B2_le_centralizer_S₄ hb))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (d.S₂_le_B2 (h.mem_S₂_of_commute hv fun w hw =>
      mem_centralizer_iff.1 hvc w hw)) hb
  refine le_antisymm (fun x hx => ?_) (le_inf (le_centralizer_iff.1 d.B4_le_centralizer_B2)
    (d.B2_le_Q4.trans d.Q4_le_B4))
  obtain ⟨hxc, hxB⟩ := mem_inf.1 hx
  have hxS : x ∈ centralizer (h.S₄ : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 (d.S₄_le_Q4.trans d.Q4_le_B4)) hxc
  have htS : h.t ∈ centralizer (h.S₄ : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 (h.pull_le_L _)) h.htL
  have hxt : ⁅x, h.t⁆ ∈ d.B2 := hZ hxB.2.2.2.2 (by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hxS htS) (inv_mem hxS)) (inv_mem htS))
  exact hZ (d.mem_Q4_of_comm_mem_B2 hxB hxt) hxS

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4

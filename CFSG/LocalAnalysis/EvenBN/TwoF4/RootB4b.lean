module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootB4a

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Generic

variable {X : Type*} [Group X]

@[expose] def commRightIn (x : X) (N : Subgroup X) : Subgroup X where
  carrier := {y | y ∈ normalizer (N : Set X) ∧ ⁅x, y⁆ ∈ N}
  mul_mem' := fun {y y'} hy hy' => ⟨mul_mem hy.1 hy'.1, by
    rw [commutatorElement_mul_right_eq]
    exact mul_mem hy.2 ((mem_normalizer_iff.1 hy.1 _).1 hy'.2)⟩
  one_mem' := ⟨one_mem _, by rw [commutatorElement_one_right]; exact one_mem _⟩
  inv_mem' := fun {y} hy => ⟨inv_mem hy.1, by
    have e : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (mem_normalizer_iff.1 (inv_mem hy.1) _).1 (inv_mem hy.2)⟩

@[expose] def commLeftIn (y : X) (N : Subgroup X) : Subgroup X where
  carrier := {x | x ∈ normalizer (N : Set X) ∧ ⁅x, y⁆ ∈ N}
  mul_mem' := fun {x x'} hx hx' => ⟨mul_mem hx.1 hx'.1, by
    rw [commutatorElement_mul_left_eq]
    exact mul_mem ((mem_normalizer_iff.1 hx.1 _).1 hx'.2) hx.2⟩
  one_mem' := ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by
    have e : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (mem_normalizer_iff.1 (inv_mem hx.1) _).1 (inv_mem hx.2)⟩

theorem mem_commRightIn {x y : X} {N : Subgroup X} :
    y ∈ commRightIn x N ↔ y ∈ normalizer (N : Set X) ∧ ⁅x, y⁆ ∈ N := Iff.rfl

theorem mem_commLeftIn {x y : X} {N : Subgroup X} :
    x ∈ commLeftIn y N ↔ x ∈ normalizer (N : Set X) ∧ ⁅x, y⁆ ∈ N := Iff.rfl

end Generic

namespace Setup

variable (h : Setup G)

theorem comm_V_V_mem {j k : Idx} {N : Subgroup G} (hj : h.V j ≤ normalizer (N : Set G))
    (hk : h.V k ≤ normalizer (N : Set G))
    (hc : ∀ c e : h.K, ⁅h.elt (rootElt h.K h.a j c), h.elt (rootElt h.K h.a k e)⁆ ∈ N)
    {v w : G} (hv : v ∈ h.V j) (hw : w ∈ h.V k) : ⁅v, w⁆ ∈ N := by
  have h1 : ∀ e : h.K, h.V j ≤ commLeftIn (h.elt (rootElt h.K h.a k e)) N := fun e =>
    h.V_le_of_forall_elt_mem fun c => ⟨hj (h.elt_rootElt_mem_V j c), hc c e⟩
  have h2 : h.V k ≤ commRightIn v N :=
    h.V_le_of_forall_elt_mem fun e => ⟨hk (h.elt_rootElt_mem_V k e), (h1 e hv).2⟩
  exact (h2 hw).2

theorem comm_V2_R₁_mem {v r : G} (hv : v ∈ h.V .i2) (hr : r ∈ h.R₁) : ⁅v, r⁆ ∈ h.S₂ := by
  have hSN : h.S ≤ normalizer (h.S₂ : Set G) :=
    h.S₂_le_S₃_le_S₄_le_S.2.2.2.1.trans
      (h.S₂_le_S₃_le_S₄_le_S.2.2.2.2.trans h.Kp_le_normalizer_S₂_S₃_S₄.1)
  have hR₁S : h.R₁ ≤ h.S := le_sup_right.trans h.V5_sup_R₁_le_S
  have hV2S : h.V .i2 ≤ h.S := (h.V_center_le .i1).trans (h.V_le_S (k := .i1) (by decide))
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  have hS2 : ∀ k ∈ ({.i10, .i11, .i12} : Finset Idx), ∀ c : h.K,
      h.elt (rootElt h.K h.a k c) ∈ h.S₂ := fun k hk c =>
    h.pull_mono (rootV_le_rootJoin hk) (h.elt_rootElt_mem_V k c)
  have hle : h.R₁ ≤ commRightIn v h.S₂ := h.pull_rootJoin_le fun k hk => by
    have hk' : h.V k ≤ normalizer (h.S₂ : Set G) := ((h.V_le_R₁ hk).trans hR₁S).trans hSN
    intro w hw
    refine mem_commRightIn.2 ⟨hk' hw, h.comm_V_V_mem (hV2S.trans hSN) hk' (fun c e => ?_) hv hw⟩
    rw [← h.elt_commutator (hΓ _ _) (hΓ _ _)]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · rw [rootElt_comm_2_8 h.card_K, h.elt_mul' (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _),
        h.elt_mul' (hΓ _ _) (hΓ _ _)]
      exact mul_mem (mul_mem (hS2 .i10 (by decide) _) (hS2 .i11 (by decide) _))
        (hS2 .i12 (by decide) _)
    · rw [rootElt_comm_2_9 h.card_K]
      exact hS2 .i11 (by decide) _
    · rw [rootElt_comm_2_10 h.card_K, h.elt_one']
      exact one_mem _
    · rw [rootElt_comm_2_11 h.card_K, h.elt_one']
      exact one_mem _
    · rw [rootElt_comm_2_12 h.card_K, h.elt_one']
      exact one_mem _
  exact (mem_commRightIn.1 (hle hr)).2


theorem S₂_le_R₁ : h.S₂ ≤ h.R₁ := h.pull_mono (S1_le_S2_le_S3_le_S4_le_radS h.card_K).2.2.2.2.2

theorem r1c_eq_zero_of_mem_S₂ {x : G} (hx : x ∈ h.S₂) {k : Idx} (hk : k = .i8 ∨ k = .i9) :
    h.r1c x k = 0 := by
  have hS : ∀ l ∈ ({.i10, .i11, .i12} : Finset Idx), l.isR1 = true := by decide
  have hx' : x ∈ h.pull (rootJoin h.K h.a {.i10, .i11, .i12}) := hx
  rcases hk with rfl | rfl
  · exact h.r1c_eq_zero_of_mem hS hx' rfl (by decide)
  · exact h.r1c_eq_zero_of_mem hS hx' rfl (by decide)

theorem mem_S₂_of_r1c_eq_zero {x : G} (hx : x ∈ h.R₁) (h8 : h.r1c x .i8 = 0)
    (h9 : h.r1c x .i9 = 0) : x ∈ h.S₂ := by
  have h0 : ∀ k : Idx, k.isR1 = true → k ∉ ({.i10, .i11, .i12} : Finset Idx) →
      h.r1c x k = 0 := by
    intro k hk hkS
    have hk' : k = .i8 ∨ k = .i9 := by
      cases k <;> simp_all [Idx.isR1]
    rcases hk' with rfl | rfl
    · exact h8
    · exact h9
  have := h.mem_of_r1c_eq_zero hx h0
  exact this

theorem r1c_conj_V2 {v r : G} (hv : v ∈ h.V .i2) (hr : r ∈ h.R₁) {k : Idx}
    (hk : k = .i8 ∨ k = .i9) : h.r1c (v * r * v⁻¹) k = h.r1c r k := by
  have hc := h.comm_V2_R₁_mem hv hr
  have e : v * r * v⁻¹ = ⁅v, r⁆ * r := by simp only [commutatorElement_def]; group
  have hkR : k.isR1 = true := by rcases hk with rfl | rfl <;> rfl
  rw [e, h.r1c_mul (h.S₂_le_R₁ hc) hr hkR, h.r1c_eq_zero_of_mem_S₂ hc hk, zero_add]

theorem r1c_eight_eq_zero_of_mem_S₃ {x : G} (hx : x ∈ h.S₃) (hxR : x ∈ h.R₁) :
    h.r1c x .i8 = 0 := by
  obtain ⟨v₁₁, h11, v₁₂, h12, v₇, h7, v₉, h9, v₁₀, h10, rfl⟩ := h.exists_mul_of_mem_S₃ hx
  have hR : ∀ k ∈ ({.i8, .i9, .i10, .i11, .i12} : Finset Idx), ∀ {v : G}, v ∈ h.V k →
      v ∈ h.R₁ := fun k hk v hv => h.V_le_R₁ hk hv
  have r11 := hR .i11 (by decide) h11
  have r12 := hR .i12 (by decide) h12
  have r9 := hR .i9 (by decide) h9
  have r10 := hR .i10 (by decide) h10
  have h7R : v₇ ∈ h.R₁ := by
    have e : v₇ = (v₁₁ * v₁₂)⁻¹ * (v₁₁ * v₁₂ * v₇ * v₉ * v₁₀) * (v₉ * v₁₀)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (mul_mem r11 r12)) hxR) (inv_mem (mul_mem r9 r10))
  rw [h.eq_one_of_mem_V7_of_mem_R₁ h7 h7R, mul_one]
  have z : ∀ k, k ≠ Idx.i8 → k.isR1 = true → ∀ {v : G}, v ∈ h.V k → h.r1c v .i8 = 0 :=
    fun k hk8 hk v hv => h.r1c_eq_zero_of_mem (S := {k}) (by simpa using hk)
      (by rw [h.pull_rootJoin_singleton]; exact hv) rfl (by simpa using hk8.symm)
  rw [h.r1c_mul (mul_mem (mul_mem r11 r12) r9) r10 rfl,
    h.r1c_mul (mul_mem r11 r12) r9 rfl, h.r1c_mul r11 r12 rfl,
    z .i11 (by decide) rfl h11, z .i12 (by decide) rfl h12, z .i9 (by decide) rfl h9,
    z .i10 (by decide) rfl h10]
  simp

end Setup

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

theorem B2_le_A1 : d.B2 ≤ d.A1 := sup_le inf_le_left d.B1_le_A1

theorem A1_le_normalizer_B2 : d.A1 ≤ normalizer (d.B2 : Set G) := by
  have hV : h.V .i12 ≤ d.B2 := (d.V12_le_W12.trans d.W12_le_B1).trans le_sup_right
  have key : ∀ {x : G}, x ∈ d.A1 → ∀ b ∈ d.B2, x * b * x⁻¹ ∈ d.B2 := fun {x} hx b hb => by
    have e : x * b * x⁻¹ = ⁅x, b⁆ * b := by simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem (hV (d.comm_A1_mem_V12 hx (d.B2_le_A1 hb))) hb
  intro x hx
  refine mem_normalizer_of_conj_mem (key hx) fun b hb => ?_
  have := key (inv_mem hx) b hb
  rwa [inv_inv] at this

theorem exists_R₁_mul_B2 {x : G} (hx : x ∈ d.A1) (hxt : ⁅x, h.t⁆ ∈ h.S₂) :
    ∃ r ∈ h.R₁, ∃ b ∈ d.B2, x = r * b := by
  obtain ⟨b, hb, hbt⟩ := d.exists_B2_comm_t hxt
  have hbA := d.B2_le_A1 hb
  refine ⟨x * b⁻¹, d.mem_R₁_of_mem_A1 (mul_mem hx (inv_mem hbA)) ?_, b, hb, by group⟩
  rw [d.comm_t_mul_A1 hx (inv_mem hbA), d.comm_t_inv_A1 hbA, hbt, mul_inv_cancel]

theorem r1c_eq_of_mul_eq {r r' b b' : G} (hr : r ∈ h.R₁) (hr' : r' ∈ h.R₁) (hb : b ∈ d.B2)
    (hb' : b' ∈ d.B2) (e : r * b = r' * b') {k : Idx} (hk : k = .i8 ∨ k = .i9) :
    h.r1c r k = h.r1c r' k := by
  have hm : r⁻¹ * r' = b * b'⁻¹ := by
    calc r⁻¹ * r' = r⁻¹ * (r' * b') * b'⁻¹ := by group
      _ = r⁻¹ * (r * b) * b'⁻¹ := by rw [e]
      _ = b * b'⁻¹ := by group
  have hR : r⁻¹ * r' ∈ h.R₁ := mul_mem (inv_mem hr) hr'
  have hS : r⁻¹ * r' ∈ h.S₂ := by
    refine d.mem_S₂_of_mem_B2 (hm ▸ mul_mem hb (inv_mem hb')) ?_
    exact commutatorElement_eq_one_iff_mul_comm.2 (h.mul_t_comm (h.R₁_le_R.trans h.R_le_L hR))
  have hkR : k.isR1 = true := by rcases hk with rfl | rfl <;> rfl
  have e2 : r' = r * (r⁻¹ * r') := by group
  rw [e2, h.r1c_mul hr hR hkR, h.r1c_eq_zero_of_mem_S₂ hS hk, add_zero]

theorem r1c_eq_zero_of_comm_V2 {i : Idx} (hi : i.isCenter = false) {w : G}
    (hwH : w ∈ h.CH i)
    (hdec : ∀ c : h.K, ∃ r ∈ h.R₁, ∃ b ∈ d.B2, ⁅h.elt (rootElt h.K h.a .i2 c), w⁆ = r * b)
    {k : Idx} (hk : k = .i8 ∨ k = .i9) (hbr : Idx.brace i .i2 ≠ Idx.brace i k) {c : h.K}
    {r b : G} (hr : r ∈ h.R₁) (hb : b ∈ d.B2)
    (e : ⁅h.elt (rootElt h.K h.a .i2 c), w⁆ = r * b) : h.r1c r k = 0 := by
  classical
  choose R hR B hB hRB using hdec
  have hkR : k.isR1 = true := by rcases hk with rfl | rfl <;> rfl
  set v : h.K → G := fun c => h.elt (rootElt h.K h.a .i2 c) with hvdef
  have hvV : ∀ c, v c ∈ h.V .i2 := fun c => h.elt_rootElt_mem_V _ c
  have hvJ : ∀ c, v c ∈ h.J := fun c =>
    h.P_sup_Tsyl_le_J_Kp.1 (mem_sup_left (h.V_le_P .i2 (hvV c)))
  have hvK : ∀ c, v c ∈ h.Kp := fun c =>
    h.P_sup_Tsyl_le_J_Kp.2 (mem_sup_left (h.V_le_P .i2 (hvV c)))
  have huniq : ∀ {c : h.K} {r b : G}, r ∈ h.R₁ → b ∈ d.B2 → ⁅v c, w⁆ = r * b →
      h.r1c r k = h.r1c (R c) k := fun hr hb e =>
    d.r1c_eq_of_mul_eq hr (hR _) hb (hB _) (e.symm.trans (hRB _)) hk
  set φ : h.K → h.K := fun c => h.r1c (R c) k with hφdef
  have hadd : ∀ c e : h.K, φ (c + e) = φ c + φ e := by
    intro c e
    have hve : v (c + e) = v c * v e := by
      simp only [hvdef]
      rw [rootElt_add h.card_K (i := .i2) rfl, h.elt_mul'
        (rootV_le_reeGamma h.card_K _ (rootElt_mem_rootV _ _))
        (rootV_le_reeGamma h.card_K _ (rootElt_mem_rootV _ _))]
    have hR' : v c * R e * (v c)⁻¹ ∈ h.R₁ :=
      (mem_normalizer_iff.1 (h.J_le_normalizer_R₁ (hvJ c)) _).1 (hR e)
    have hB' : v c * B e * (v c)⁻¹ ∈ d.B2 :=
      (mem_normalizer_iff.1 (d.Kp_le_normalizer_B2 (hvK c)) _).1 (hB e)
    have hcomm : v c * B e * (v c)⁻¹ * R c = R c * (v c * B e * (v c)⁻¹) :=
      (mem_centralizer_iff.1 (d.A1_le_centralizer_R₁ (d.B2_le_A1 hB')) _ (hR c)).symm
    have e2 : ⁅v (c + e), w⁆ = (v c * R e * (v c)⁻¹ * R c) * (v c * B e * (v c)⁻¹ * B c) := by
      rw [hve, commutatorElement_mul_left_eq, hRB e, hRB c]
      calc v c * (R e * B e) * (v c)⁻¹ * (R c * B c) =
          v c * R e * (v c)⁻¹ * (v c * B e * (v c)⁻¹ * R c) * B c := by group
        _ = v c * R e * (v c)⁻¹ * (R c * (v c * B e * (v c)⁻¹)) * B c := by rw [hcomm]
        _ = _ := by group
    have h1 := huniq (mul_mem hR' (hR c)) (mul_mem hB' (hB c)) e2
    simp only [hφdef]
    rw [← h1, h.r1c_mul hR' (hR c) hkR, h.r1c_conj_V2 (hvV c) (hR e) hk, add_comm]
  have hequiv : ∀ t : h.Kˣ × h.Kˣ, torusPair h.a t ∈ torusHi h.K h.a i → ∀ c : h.K,
      φ ((rootChar h.K h.a .i2 t : h.K) * c) = (rootChar h.K h.a k t : h.K) * φ c := by
    intro t ht c
    set g := h.elt (torusPair h.a t) with hg
    have hgH : g ∈ h.Ht i := (h.elt_torusPair_mem_Ht_iff t).2 ht
    have hgH' : g ∈ h.H := h.Ht_le_H i hgH
    have hgw : g * w * g⁻¹ = w := by
      rw [mem_centralizer_iff.1 hwH g hgH, mul_inv_cancel_right]
    have hgv : g * v c * g⁻¹ = v ((rootChar h.K h.a .i2 t : h.K) * c) := by
      simp only [hvdef, hg]
      exact h.elt_torusPair_conj_rootElt t .i2 c
    have hR' : g * R c * g⁻¹ ∈ h.R₁ :=
      (mem_normalizer_iff.1 (h.J_le_normalizer_R₁ (h.H_le_J hgH')) _).1 (hR c)
    have hB' : g * B c * g⁻¹ ∈ d.B2 :=
      (mem_normalizer_iff.1 (d.Kp_le_normalizer_B2 (h.H_le_Kp hgH')) _).1 (hB c)
    have e2 : ⁅v ((rootChar h.K h.a .i2 t : h.K) * c), w⁆ =
        (g * R c * g⁻¹) * (g * B c * g⁻¹) := by
      rw [← hgv]
      conv_lhs => rw [← hgw]
      rw [show ⁅g * v c * g⁻¹, g * w * g⁻¹⁆ = g * ⁅v c, w⁆ * g⁻¹ by
        simp only [commutatorElement_def]; group, hRB c]
      group
    simp only [hφdef]
    rw [← huniq hR' hB' e2, hg, h.r1c_torus (hR c) t hkR]
  have h0 := miyamoto_2_1 h.one_le_a h.card_K hi hbr hadd hequiv c
  rw [huniq hr hb e]
  exact h0

theorem exists_R₁_mul_B2_comm_V2 {w : G} (hwA : w ∈ d.A1) {j : Idx}
    (hj : j ∈ ({.i8, .i9, .i10, .i11, .i12} : Finset Idx)) (hwt : ⁅w, h.t⁆ ∈ h.V j) (c : h.K) :
    ∃ r ∈ h.R₁, ∃ b ∈ d.B2, ⁅h.elt (rootElt h.K h.a .i2 c), w⁆ = r * b := by
  set v := h.elt (rootElt h.K h.a .i2 c) with hvdef
  have hvV : v ∈ h.V .i2 := h.elt_rootElt_mem_V _ c
  have hvJ : v ∈ h.J := h.P_sup_Tsyl_le_J_Kp.1 (mem_sup_left (h.V_le_P .i2 hvV))
  have hvC : v ∈ h.C := h.P_le_C (h.V_le_P .i2 hvV)
  have hvwA : v * w * v⁻¹ ∈ d.A1 := d.conj_J_mem_A1 hvJ hwA
  have hxA : ⁅v, w⁆ ∈ d.A1 := by
    rw [commutatorElement_def]
    exact mul_mem hvwA (inv_mem hwA)
  refine d.exists_R₁_mul_B2 hxA ?_
  have hvt : v * h.t = h.t * v := mem_centralizer_singleton_iff.1 hvC
  have e1 : ⁅v * w * v⁻¹, h.t⁆ = v * ⁅w, h.t⁆ * v⁻¹ := by
    have hvt' : v⁻¹ * h.t = h.t * v⁻¹ := by
      calc v⁻¹ * h.t = v⁻¹ * (h.t * v) * v⁻¹ := by group
        _ = v⁻¹ * (v * h.t) * v⁻¹ := by rw [hvt]
        _ = h.t * v⁻¹ := by group
    simp only [commutatorElement_def]
    calc v * w * v⁻¹ * h.t * (v * w * v⁻¹)⁻¹ * h.t⁻¹ =
        v * w * (v⁻¹ * h.t) * v * w⁻¹ * v⁻¹ * h.t⁻¹ := by group
      _ = v * w * (h.t * v⁻¹) * v * w⁻¹ * v⁻¹ * h.t⁻¹ := by rw [hvt']
      _ = v * (w * h.t * w⁻¹) * (v⁻¹ * h.t⁻¹) := by group
      _ = v * (w * h.t * w⁻¹) * (h.t⁻¹ * v⁻¹) := by
        rw [show v⁻¹ * h.t⁻¹ = (h.t * v)⁻¹ by group, ← hvt]
        group
      _ = v * (w * h.t * w⁻¹ * h.t⁻¹) * v⁻¹ := by group
  have e2 : ⁅⁅v, w⁆, h.t⁆ = ⁅v, ⁅w, h.t⁆⁆ := by
    rw [show ⁅v, w⁆ = v * w * v⁻¹ * w⁻¹ from commutatorElement_def v w,
      d.comm_t_mul_A1 hvwA (inv_mem hwA), e1, d.comm_t_inv_A1 hwA]
    exact (commutatorElement_def _ _).symm
  rw [e2]
  exact h.comm_V2_R₁_mem hvV (h.V_le_R₁ hj hwt)

theorem comm_V2_WA4_mem {v w : G} (hv : v ∈ h.V .i2) (hw : w ∈ d.WA .i4) : ⁅v, w⁆ ∈ d.B2 := by
  have hwt : ⁅w, h.t⁆ ∈ h.V .i8 := d.comm_t_mem_V_of_mem_WA (i := .i4) rfl (by decide) hw
  have hdec := d.exists_R₁_mul_B2_comm_V2 hw.1 (j := .i8) (by decide) hwt
  have hle : h.V .i2 ≤ commLeftIn w d.B2 := h.V_le_of_forall_elt_mem fun c => by
    refine mem_commLeftIn.2 ⟨d.Kp_le_normalizer_B2 (h.P_sup_Tsyl_le_J_Kp.2
      (mem_sup_left (h.V_le_P .i2 (h.elt_rootElt_mem_V _ c)))), ?_⟩
    obtain ⟨r, hr, b, hb, e⟩ := hdec c
    have h8 := d.r1c_eq_zero_of_comm_V2 (i := .i4) rfl hw.2 hdec (k := .i8) (Or.inl rfl)
      (by decide) hr hb e
    have h9 := d.r1c_eq_zero_of_comm_V2 (i := .i4) rfl hw.2 hdec (k := .i9) (Or.inr rfl)
      (by decide) hr hb e
    rw [e]
    exact mul_mem (d.S₂_le_B2 (h.mem_S₂_of_r1c_eq_zero hr h8 h9)) hb
  exact (mem_commLeftIn.1 (hle hv)).2

theorem comm_V2_WA9_mem {v w : G} (hv : v ∈ h.V .i2) (hw : w ∈ d.WA .i9) : ⁅v, w⁆ ∈ d.B2 := by
  have hwt : ⁅w, h.t⁆ ∈ h.V .i9 := d.comm_t_mem_V_of_mem_WA (i := .i9) rfl (by decide) hw
  have hdec := d.exists_R₁_mul_B2_comm_V2 hw.1 (j := .i9) (by decide) hwt
  have hle : h.V .i2 ≤ commLeftIn w d.B2 := h.V_le_of_forall_elt_mem fun c => by
    have hvK : h.elt (rootElt h.K h.a .i2 c) ∈ h.Kp := h.P_sup_Tsyl_le_J_Kp.2
      (mem_sup_left (h.V_le_P .i2 (h.elt_rootElt_mem_V _ c)))
    refine mem_commLeftIn.2 ⟨d.Kp_le_normalizer_B2 hvK, ?_⟩
    obtain ⟨r, hr, b, hb, e⟩ := hdec c
    have h9 := d.r1c_eq_zero_of_comm_V2 (i := .i9) rfl hw.2 hdec (k := .i9) (Or.inr rfl)
      (by decide) hr hb e
    have hwB : w ∈ d.B3 := d.WA_le_B3 (Or.inl rfl) hw
    have hxB : ⁅h.elt (rootElt h.K h.a .i2 c), w⁆ ∈ d.B3 := by
      rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.1 (d.Kp_le_normalizer_B3 hvK) w).1 hwB) (inv_mem hwB)
    have hrB : r ∈ d.B3 := by
      have e' : r = ⁅h.elt (rootElt h.K h.a .i2 c), w⁆ * b⁻¹ := by rw [e]; group
      rw [e']
      exact mul_mem hxB (inv_mem (d.B2_le_B3 hb))
    have hrS : r ∈ h.S₃ := d.mem_S₃_of_mem_B3 hrB
      (commutatorElement_eq_one_iff_mul_comm.2 (h.mul_t_comm (h.R₁_le_R.trans h.R_le_L hr)))
    have h8 := h.r1c_eight_eq_zero_of_mem_S₃ hrS hr
    rw [e]
    exact mul_mem (d.S₂_le_B2 (h.mem_S₂_of_r1c_eq_zero hr h8 h9)) hb
  exact (mem_commLeftIn.1 (hle hv)).2

theorem comm_A1_V2_mem {x v : G} (hx : x ∈ d.A1) (hv : v ∈ h.V .i2) : ⁅x, v⁆ ∈ d.B2 := by
  have hvK : v ∈ h.Kp := h.P_sup_Tsyl_le_J_Kp.2 (mem_sup_left (h.V_le_P .i2 hv))
  have hvN := d.Kp_le_normalizer_B2 hvK
  have hB : ∀ y ∈ d.B2, ⁅y, v⁆ ∈ d.B2 := fun y hy => by
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine mul_mem hy ?_
    rw [← mul_assoc]
    exact (mem_normalizer_iff.1 hvN _).1 (inv_mem hy)
  have hsym : ∀ {y : G}, ⁅v, y⁆ ∈ d.B2 → ⁅y, v⁆ ∈ d.B2 := fun hy => by
    rw [← commutatorElement_inv]
    exact inv_mem hy
  have hle : d.A1 ≤ commLeftIn v d.B2 := by
    refine d.A1_le_sup.trans (sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_)
    · exact fun y hy => mem_commLeftIn.2 ⟨d.A1_le_normalizer_B2 hy.1,
        hsym (d.comm_V2_WA4_mem hv hy)⟩
    · exact fun y hy => mem_commLeftIn.2 ⟨d.A1_le_normalizer_B2 hy.1,
        hB y (mem_sup_right (d.W11_le_B1 (d.WA_six_eq ▸ hy)))⟩
    · exact fun y hy => mem_commLeftIn.2 ⟨d.A1_le_normalizer_B2 hy.1,
        hB y (mem_sup_right (d.W12_le_B1 (d.WA_five_eq ▸ hy)))⟩
    · exact fun y hy => mem_commLeftIn.2 ⟨d.A1_le_normalizer_B2 hy.1,
        hsym (d.comm_V2_WA9_mem hv hy)⟩
    · exact fun y hy => mem_commLeftIn.2 ⟨d.A1_le_normalizer_B2 hy.1, hB y (mem_sup_left hy)⟩
  exact (mem_commLeftIn.1 (hle hx)).2

theorem comm_A1_S₄_mem {x v : G} (hx : x ∈ d.A1) (hv : v ∈ h.S₄) : ⁅x, v⁆ ∈ d.B2 := by
  have hS4N : h.S₄ ≤ normalizer (d.B2 : Set G) := h.S₂_le_S₃_le_S₄_le_S.2.2.1.trans
    (h.S₂_le_S₃_le_S₄_le_S.2.2.2.1.trans (h.S₂_le_S₃_le_S₄_le_S.2.2.2.2.trans
      d.Kp_le_normalizer_B2))
  have hR : ∀ {w : G}, w ∈ h.R → ⁅x, w⁆ ∈ d.B2 := fun {w} hw => by
    have h1 := d.commutator_R_A1_le (commutator_mem_commutator hw hx)
    rw [← commutatorElement_inv]
    exact inv_mem (mem_sup_right (d.W12_le_B1 h1))
  have hR1 : ∀ {w : G}, w ∈ h.R₁ → ⁅x, w⁆ ∈ d.B2 := fun {w} hw => by
    rw [commutatorElement_eq_one_iff_mul_comm.2
      (mem_centralizer_iff.1 (d.A1_le_centralizer_R₁ hx) w hw).symm]
    exact one_mem _
  have hle : h.S₄ ≤ commRightIn x d.B2 := h.pull_rootJoin_le fun k hk => by
    intro w hw
    have hwS : w ∈ h.S₄ := h.pull_mono (rootV_le_rootJoin hk) hw
    refine mem_commRightIn.2 ⟨hS4N hwS, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact d.comm_A1_V2_mem hx hw
    · exact hR (h.V_le_R (k := .i5) (by decide) hw)
    · exact hR (h.V_le_R (k := .i6) (by decide) hw)
    · exact hR1 (h.V_le_R₁ (k := .i8) (by decide) hw)
    · exact hR (h.V_le_R (k := .i7) (by decide) hw)
    · exact hR1 (h.V_le_R₁ (k := .i9) (by decide) hw)
    · exact hR1 (h.V_le_R₁ (k := .i10) (by decide) hw)
    · exact hR1 (h.V_le_R₁ (k := .i11) (by decide) hw)
    · exact hR1 (h.V_le_R₁ (k := .i12) (by decide) hw)
  exact (mem_commRightIn.1 (hle hv)).2

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4

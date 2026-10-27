module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootAb
public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootB4d

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

theorem mem_of_equivariant_V7_sup {N : Subgroup G} (h7N : h.V .i7 ≤ normalizer (N : Set G))
    (hHN : h.Ht .i7 ≤ normalizer (N : Set G)) (hdis : ∀ v ∈ h.V .i7, v ∈ N → v = 1)
    {j : Idx} (hj : Idx.brace .i7 j ≠ 0) {Ψ : h.K → G}
    (hΨ : ∀ c, Ψ c ∈ h.V .i7 ⊔ N) (hadd : ∀ c e, (Ψ c * Ψ e)⁻¹ * Ψ (c + e) ∈ N)
    (hequiv : ∀ t : h.Kˣ × h.Kˣ, torusPair h.a t ∈ torusHi h.K h.a .i7 → ∀ c,
      (h.elt (torusPair h.a t) * Ψ c * (h.elt (torusPair h.a t))⁻¹)⁻¹ *
        Ψ ((rootChar h.K h.a j t : h.K) * c) ∈ N)
    (c : h.K) : Ψ c ∈ N := by
  classical
  have hdec : ∀ c, ∃ p ∈ h.V .i7, ∃ r ∈ N, Ψ c = p * r := fun c => by
    have hc : Ψ c ∈ ((h.V .i7 ⊔ N : Subgroup G) : Set G) := hΨ c
    rw [coe_mul_of_left_le_normalizer_right _ _ h7N, Set.mem_mul] at hc
    obtain ⟨p, hp, r, hr, e⟩ := hc
    exact ⟨p, hp, r, hr, e.symm⟩
  choose p hp r hr hpr using hdec
  have huniq : ∀ {p p' r r' : G}, p ∈ h.V .i7 → p' ∈ h.V .i7 → r ∈ N → r' ∈ N →
      p * r = p' * r' → p = p' := by
    intro p p' r r' hp hp' hr hr' e
    have hm : p'⁻¹ * p = r' * r⁻¹ := by
      calc p'⁻¹ * p = p'⁻¹ * (p * r) * r⁻¹ := by group
        _ = p'⁻¹ * (p' * r') * r⁻¹ := by rw [e]
        _ = r' * r⁻¹ := by group
    have h1 : p'⁻¹ * p = 1 :=
      hdis _ (mul_mem (inv_mem hp') hp) (hm ▸ mul_mem hr' (inv_mem hr))
    exact (inv_mul_eq_one.1 h1).symm
  have hpadd : ∀ c e, p (c + e) = p c * p e := by
    intro c e
    set ρ := (Ψ c * Ψ e)⁻¹ * Ψ (c + e) with hρdef
    have hρ : ρ ∈ N := hadd c e
    have hre : (p e)⁻¹ * r c * p e ∈ N := by
      have := (mem_normalizer_iff.1 (h7N (inv_mem (hp e))) (r c)).1 (hr c)
      simpa using this
    refine huniq (hp (c + e)) (mul_mem (hp c) (hp e)) (hr (c + e))
      (mul_mem (mul_mem hre (hr e)) hρ) ?_
    rw [← hpr]
    calc Ψ (c + e) = Ψ c * Ψ e * ρ := by rw [hρdef]; group
      _ = p c * r c * (p e * r e) * ρ := by rw [hpr, hpr]
      _ = p c * p e * ((p e)⁻¹ * r c * p e * r e * ρ) := by group
  have hpconst : ∀ c e : h.K, c ≠ 0 → e ≠ 0 → p c = p e := by
    intro c e hc he
    obtain ⟨t, ht, htc⟩ := exists_torusHi_rootChar_mul_eq h.card_K (i := .i7) rfl hj hc he
    set b := h.elt (torusPair h.a t) with hbdef
    have hb : b ∈ h.Ht .i7 := (h.elt_torusPair_mem_Ht_iff t).2 ht
    have hbp : b * p c * b⁻¹ = p c := by
      rw [mem_centralizer_iff.1 (h.V_le_CH (i := .i7) rfl (Or.inl rfl) (hp c)) b hb,
        mul_inv_cancel_right]
    have hbr : b * r c * b⁻¹ ∈ N := (mem_normalizer_iff.1 (hHN hb) _).1 (hr c)
    have hρ := hequiv t ht c
    rw [htc] at hρ
    set ρ := (b * Ψ c * b⁻¹)⁻¹ * Ψ e with hρdef
    refine huniq (hp c) (hp e) (mul_mem hbr hρ) (hr e) ?_
    rw [← hpr e]
    calc p c * (b * r c * b⁻¹ * ρ) = (b * p c * b⁻¹) * (b * r c * b⁻¹) * ρ := by rw [hbp]; group
      _ = b * (p c * r c) * b⁻¹ * ρ := by group
      _ = Ψ e := by rw [← hpr c, hρdef]; group
  obtain ⟨μ, hμ, hμ1⟩ := h.exists_ne_zero_add_one_ne_zero
  have hp1 := eq_one_of_add_of_const hμ hμ1 hpadd hpconst c
  rw [hpr c, hp1, one_mul]
  exact hr c

theorem V_le_Kp_of_three_four {k : Idx} (hk : k = .i3 ∨ k = .i4) : h.V k ≤ h.Kp := by
  rcases hk with rfl | rfl
  · exact h.V_le_of_forall_elt_mem fun c => h.elt_rootElt_three_mem_Kp c
  · exact (h.V_le_S (k := .i4) (by decide)).trans (h.S₂_le_S₃_le_S₄_le_S.2.2.2.1.trans
      h.S₂_le_S₃_le_S₄_le_S.2.2.2.2)

end Setup

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

theorem B3_le_normalizer_A1 : d.B3 ≤ normalizer (d.A1 : Set G) := by
  have key : ∀ {y : G}, y ∈ d.B3 → ∀ a ∈ d.A1, y * a * y⁻¹ ∈ d.A1 := by
    intro y hy a ha
    have h1 := d.comm_B4_B3_mem_B1 (d.A1_le_B4 ha) hy
    have e : y * a * y⁻¹ = ⁅a, y⁆⁻¹ * a := by simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem (inv_mem (d.B1_le_A1 h1)) ha
  intro y hy
  refine mem_normalizer_of_conj_mem (key hy) fun a ha => ?_
  have := key (inv_mem hy) a ha
  rwa [inv_inv] at this

theorem eq_one_of_mem_V7_of_mem_A1 {v : G} (h7 : v ∈ h.V .i7) (hA : v ∈ d.A1) : v = 1 :=
  h.eq_one_of_mem_V7_of_mem_R₁ h7 (d.mem_R₁_of_mem_A1 hA
    (commutatorElement_eq_one_iff_mul_comm.2 (h.mul_t_comm (h.pull_le_L _ h7))))

theorem mem_V7_sup_A1_of_mem_B3 {z : G} (hz : z ∈ d.B3) (hzt : ⁅z, h.t⁆ ∈ h.R₁) :
    z ∈ h.V .i7 ⊔ d.A1 := by
  have hW : d.WA .i9 ⊔ d.B2 ≤ d.A1 := sup_le inf_le_left (d.B2_le_A1)
  have hN : d.W7 ≤ normalizer ((d.WA .i9 ⊔ d.B2 : Subgroup G) : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun w hw =>
      d.B3_comm (sup_le (d.WA_le_B3 (Or.inl rfl)) d.B2_le_B3 hw) (d.W7_le_B3 hx))
  have hz' : z ∈ ((d.W7 ⊔ (d.WA .i9 ⊔ d.B2) : Subgroup G) : Set G) := by
    rw [← sup_assoc, ← d.B3_eq]
    exact hz
  rw [coe_mul_of_left_le_normalizer_right _ _ hN, Set.mem_mul] at hz'
  obtain ⟨x, hx, w, hw, rfl⟩ := hz'
  have hxB := d.W7_le_B3 hx
  have hwB : w ∈ d.B3 := sup_le (d.WA_le_B3 (Or.inl rfl)) d.B2_le_B3 hw
  have hwt : ⁅w, h.t⁆ ∈ h.R₁ := (hW hw).2.2
  have hxt : ⁅x, h.t⁆ ∈ h.R₁ := by
    have e : ⁅x, h.t⁆ = ⁅x * w, h.t⁆ * ⁅w, h.t⁆⁻¹ := by
      rw [d.comm_t_mul_B3 hxB hwB, mul_inv_cancel_right]
    rw [e]
    exact mul_mem hzt (inv_mem hwt)
  have hx1 := h.eq_one_of_mem_V7_of_mem_R₁ (d.comm_t_mem_V7_of_mem_W7 hx) hxt
  exact mul_mem (mem_sup_left (d.mem_V7_of_mem_W7 hx hx1)) (mem_sup_right (hW hw))

theorem comm_V_W7_mem_V7_sup_A1 {k : Idx} (hk : k = .i3 ∨ k = .i4) {v x : G} (hv : v ∈ h.V k)
    (hx : x ∈ d.W7) : ⁅v, x⁆ ∈ h.V .i7 ⊔ d.A1 := by
  have hvK := h.V_le_Kp_of_three_four hk hv
  have hxB := d.W7_le_B3 hx
  have hvxB : v * x * v⁻¹ ∈ d.B3 := d.conj_Kp_mem_B3 hvK hxB
  have hzB : ⁅v, x⁆ ∈ d.B3 := by
    rw [commutatorElement_def]
    exact mul_mem hvxB (inv_mem hxB)
  refine d.mem_V7_sup_A1_of_mem_B3 hzB ?_
  have hvt : v * h.t = h.t * v := mem_centralizer_singleton_iff.1 hvK.1
  have hconj : ⁅v * x * v⁻¹, h.t⁆ = v * ⁅x, h.t⁆ * v⁻¹ := by
    have hvt' : v * h.t * v⁻¹ = h.t := by rw [hvt, mul_inv_cancel_right]
    simp only [commutatorElement_def]
    conv_lhs => rw [← hvt']
    group
  have e : ⁅⁅v, x⁆, h.t⁆ = ⁅v, ⁅x, h.t⁆⁆ := by
    rw [commutatorElement_def v x, d.comm_t_mul_B3 hvxB (inv_mem hxB), d.comm_t_inv_B3 hxB,
      hconj, commutatorElement_def v]
  rw [e]
  have hR : ∀ {l : Idx}, l ∈ ({.i3, .i4, .i7} : Finset Idx) → h.V l ≤ normalizer (h.R₁ : Set G) :=
    fun hl => fun w hw => h.J_le_normalizer_R₁ (h.R_le_J (h.pull_mono (rootV_le_rootJoin
      (by simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢; rcases hl with rfl | rfl |
        rfl <;> simp)) hw))
  have hΓ : ∀ l c, rootElt h.K h.a l c ∈ F4.reeGamma h.K h.a := fun l c =>
    rootV_le_reeGamma h.card_K l (rootElt_mem_rootV _ _)
  have hR₁ : ∀ {l : Idx}, l.isR1 = true → ∀ c, h.elt (rootElt h.K h.a l c) ∈ h.R₁ :=
    fun hl c => h.elt_rootElt_mem_R₁ hl c
  refine h.comm_V_V_mem (j := k) (k := .i7) (hR (by rcases hk with rfl | rfl <;> decide))
    (hR (by decide)) (fun c e => ?_) hv (d.comm_t_mem_V7_of_mem_W7 hx)
  rw [← h.elt_commutator (hΓ _ _) (hΓ _ _)]
  rcases hk with rfl | rfl
  · rw [rootElt_comm_3_7 h.card_K, h.elt_mul' (hΓ _ _) (hΓ _ _)]
    exact mul_mem (hR₁ rfl _) (hR₁ rfl _)
  · rw [rootElt_comm_4_7 h.card_K, h.elt_mul' (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _),
      h.elt_mul' (hΓ _ _) (hΓ _ _)]
    exact mul_mem (mul_mem (hR₁ rfl _) (hR₁ rfl _)) (hR₁ rfl _)

theorem comm_V_W7_mem_A1 {k : Idx} (hk : k = .i3 ∨ k = .i4) {v x : G} (hv : v ∈ h.V k)
    (hx : x ∈ d.W7) : ⁅v, x⁆ ∈ d.A1 := by
  have hΓ : ∀ l c, rootElt h.K h.a l c ∈ F4.reeGamma h.K h.a := fun l c =>
    rootV_le_reeGamma h.card_K l (rootElt_mem_rootV _ _)
  have hkR : h.V k ≤ h.R := h.V_le_R (by rcases hk with rfl | rfl <;> decide)
  have hRA : ∀ {g : G}, g ∈ h.R → g ∈ normalizer (d.A1 : Set G) := fun hg =>
    d.R_le_normalizer_A1 hg
  have hsup : h.V .i7 ⊔ d.A1 ≤ d.RA1 :=
    sup_le ((h.V_le_R (by decide)).trans d.R_le_RA1) le_sup_right
  have hroot : ∀ c : h.K, ⁅h.elt (rootElt h.K h.a k c), x⁆ ∈ d.A1 := by
    refine h.mem_of_equivariant_V7_sup (N := d.A1) (fun w hw => hRA (h.V_le_R (by decide) hw))
      (fun b hb => d.J_le_normalizer_A1 (h.H_le_J (h.Ht_le_H .i7 hb)))
      (fun w hw hA => d.eq_one_of_mem_V7_of_mem_A1 hw hA) (j := k)
      (by rcases hk with rfl | rfl <;> decide)
      (Ψ := fun c => ⁅h.elt (rootElt h.K h.a k c), x⁆)
      (fun c => d.comm_V_W7_mem_V7_sup_A1 hk (h.elt_rootElt_mem_V k c) hx) (fun c e => ?_)
      (fun t ht c => ?_)
    ·
      set a := h.elt (rootElt h.K h.a k c) with ha
      set b := h.elt (rootElt h.K h.a k e) with hb
      have haR : a ∈ h.R := hkR (h.elt_rootElt_mem_V k c)
      have hbR : b ∈ h.R := hkR (h.elt_rootElt_mem_V k e)
      set u := ⁅a, x⁆ with hu
      set w := ⁅b, x⁆ with hw
      have huR : u ∈ d.RA1 := hsup (d.comm_V_W7_mem_V7_sup_A1 hk (h.elt_rootElt_mem_V k c) hx)
      have hwR : w ∈ d.RA1 := hsup (d.comm_V_W7_mem_V7_sup_A1 hk (h.elt_rootElt_mem_V k e) hx)
      have hγ : ⁅a, w⁆ ∈ d.A1 := d.comm_A_RA1_mem (d.R_le_A haR) hwR
      have huw : (u * w)⁻¹ ∈ normalizer (d.A1 : Set G) :=
        (d.RA1_le_A (inv_mem (mul_mem huR hwR))).1
      have key : (u * w)⁻¹ * (a * w * a⁻¹ * u) ∈ d.A1 := by
        have e1 : (u * w)⁻¹ * (a * w * a⁻¹ * u) =
            ((u * w)⁻¹ * ⁅a, w⁆ * (u * w)⁻¹⁻¹) * ⁅w⁻¹, u⁻¹⁆ := by
          simp only [commutatorElement_def]; group
        rw [e1]
        exact mul_mem ((mem_normalizer_iff.1 huw _).1 hγ)
          (d.comm_RA1_RA1_mem (inv_mem hwR) (inv_mem huR))
      show (u * w)⁻¹ * ⁅h.elt (rootElt h.K h.a k (c + e)), x⁆ ∈ d.A1
      rcases hk with rfl | rfl
      · have e2 : h.elt (rootElt h.K h.a .i3 (c + e)) = a * b := by
          rw [rootElt_add h.card_K (by decide), h.elt_mul' (hΓ _ _) (hΓ _ _)]
        rw [e2, commutatorElement_mul_left_eq]
        exact key
      · set f := h.elt (rootElt h.K h.a .i8 (largeReeSigma h.a c * e)) with hf
        have e1 := h.elt_rootElt_mul_of_isSz (k := .i4) rfl c e
        have e2 : h.elt (rootElt h.K h.a .i4 (c + e)) = a * b * f⁻¹ := by
          rw [ha, hb, e1, hf]
          exact (mul_inv_cancel_right _ _).symm
        have hfx : ⁅f⁻¹, x⁆ ∈ d.A1 := by
          rw [← commutatorElement_inv]
          exact inv_mem (d.W12_le_A1 (d.comm_W7_V8_mem_W12 hx
            (inv_mem (h.elt_rootElt_mem_V .i8 _))))
        have habN : a * b ∈ normalizer (d.A1 : Set G) := hRA (mul_mem haR hbR)
        have e3 : ⁅a * b * f⁻¹, x⁆ = (a * b * ⁅f⁻¹, x⁆ * (a * b)⁻¹) * (a * w * a⁻¹ * u) := by
          rw [commutatorElement_mul_left_eq (a * b) f⁻¹ x, commutatorElement_mul_left_eq a b x]
        rw [e2, e3]
        have e4 : (u * w)⁻¹ * ((a * b * ⁅f⁻¹, x⁆ * (a * b)⁻¹) * (a * w * a⁻¹ * u)) =
            ((u * w)⁻¹ * (a * b * ⁅f⁻¹, x⁆ * (a * b)⁻¹) * (u * w)⁻¹⁻¹) *
              ((u * w)⁻¹ * (a * w * a⁻¹ * u)) := by group
        rw [e4]
        exact mul_mem ((mem_normalizer_iff.1 huw _).1 ((mem_normalizer_iff.1 habN _).1 hfx)) key
    ·
      set τ := h.elt (torusPair h.a t) with hτ
      have hτH : τ ∈ h.Ht .i7 := (h.elt_torusPair_mem_Ht_iff t).2 ht
      have hτx : τ * x * τ⁻¹ = x := by
        rw [mem_centralizer_iff.1 (d.W7_le_CH7 hx) τ hτH, mul_inv_cancel_right]
      have e : τ * ⁅h.elt (rootElt h.K h.a k c), x⁆ * τ⁻¹ =
          ⁅h.elt (rootElt h.K h.a k ((rootChar h.K h.a k t : h.K) * c)), x⁆ := by
        rw [← h.elt_torusPair_conj_rootElt t k c, ← hτ]
        conv_rhs => rw [← hτx]
        simp only [commutatorElement_def]
        group
      show (τ * ⁅h.elt (rootElt h.K h.a k c), x⁆ * τ⁻¹)⁻¹ *
        ⁅h.elt (rootElt h.K h.a k ((rootChar h.K h.a k t : h.K) * c)), x⁆ ∈ d.A1
      rw [e, inv_mul_cancel]
      exact one_mem _
  have hle : h.V k ≤ commLeftIn x d.A1 :=
    h.V_le_of_forall_elt_mem fun c => mem_commLeftIn.2
      ⟨hRA (hkR (h.elt_rootElt_mem_V k c)), hroot c⟩
  exact (mem_commLeftIn.1 (hle hv)).2

theorem comm_W7_R_mem_A1 {x r : G} (hx : x ∈ d.W7) (hr : r ∈ h.R) : ⁅x, r⁆ ∈ d.A1 := by
  have hle : h.pull (rootJoin h.K h.a {.i3, .i4, .i5, .i6, .i7, .i9, .i10}) ≤
      commRightIn x d.A1 := h.pull_rootJoin_le fun k hk => by
    intro v hv
    refine mem_commRightIn.2 ⟨d.R_le_normalizer_A1 (h.V_le_R hk hv), ?_⟩
    have hB : ∀ (hk' : k ∈ ({.i2, .i5, .i6, .i8, .i7, .i9, .i10, .i11, .i12} : Finset Idx)),
        ⁅x, v⁆ ∈ d.A1 := fun hk' =>
      d.B2_le_A1 ((d.B3_le_B4 (d.W7_le_B3 hx)).2.2.1 v (h.V_le_S₄ hk' hv))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [← commutatorElement_inv]
      exact inv_mem (d.comm_V_W7_mem_A1 (Or.inl rfl) hv hx)
    · rw [← commutatorElement_inv]
      exact inv_mem (d.comm_V_W7_mem_A1 (Or.inr rfl) hv hx)
    all_goals exact hB (by decide)
  exact (mem_commRightIn.1 (hle hr)).2

theorem comm_W7_A1_mem_W12 {x a : G} (hx : x ∈ d.W7) (ha : a ∈ d.A1) : ⁅x, a⁆ ∈ d.W12 := by
  have hxB := d.W7_le_B3 hx
  have hN : ∀ {y : G}, y ∈ d.A1 → y ∈ normalizer (d.W12 : Set G) := fun hy =>
    Subgroup.centralizer_le_normalizer _ hy.2.1
  have hB3 : ∀ {M : Subgroup G}, M ≤ d.A1 → M ≤ d.B3 → M ≤ commRightIn x d.W12 :=
    fun hMA hMB y hy => mem_commRightIn.2 ⟨hN (hMA hy), by
      rw [commutatorElement_eq_one_iff_mul_comm.2 (d.B3_comm hxB (hMB hy))]
      exact one_mem _⟩
  have hle : d.WA .i4 ⊔ d.WA .i6 ⊔ d.WA .i5 ⊔ d.WA .i9 ⊔ d.WA .i10 ≤ commRightIn x d.W12 := by
    refine sup_le (sup_le (sup_le (sup_le (fun y hy => mem_commRightIn.2
      ⟨hN hy.1, d.comm_W7_WA4_mem_W12 hx hy⟩) ?_) ?_) ?_) ?_
    · rw [d.WA_six_eq]
      exact hB3 d.W11_le_A1 d.W11_le_B3
    · rw [d.WA_five_eq]
      exact hB3 d.W12_le_A1 d.W12_le_B3
    · exact hB3 inf_le_left (d.WA_le_B3 (Or.inl rfl))
    · exact hB3 inf_le_left (d.WA_le_B3 (Or.inr rfl))
  exact (mem_commRightIn.1 (hle (d.A1_le_sup ha))).2

theorem W7_le_A : d.W7 ≤ d.A := fun x hx =>
  ⟨d.B3_le_normalizer_A1 (d.W7_le_B3 hx),
    centralizer_le (SetLike.coe_subset_coe.2 d.W12_le_B1) (d.W7_le_B3 hx).2.1,
    fun _ hr => d.comm_W7_R_mem_A1 hx hr, fun _ ha => d.comm_W7_A1_mem_W12 hx ha,
    d.R_le_RA1 (h.V_le_R (by decide) (d.comm_t_mem_V7_of_mem_W7 hx))⟩

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4

module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootS3

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

section Model

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem rootV_seven_inf_R1 (hK : Nat.card K = 2 ^ (2 * a + 1)) : rootV K a .i7 ⊓ R1 K a = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hg7, hgR⟩ := mem_inf.1 hg
  have h2 : g ∈ (rootV K a .i7 : Set (ModGL F4.tag K)) := hg7
  have hR : g ∈ (R1 K a : Set (ModGL F4.tag K)) := hgR
  rw [coe_rootV hK] at h2
  rw [(R1_spec hK).2.1] at hR
  obtain ⟨x, hx, rfl⟩ := h2
  obtain ⟨z, hz, hzx⟩ := hR
  have hxz := (bijOn_sylowVec (m := a) (K := K) hK).injOn (Set.mem_univ _) (Set.mem_univ _) hzx
  have hx0 : x = 0 := by
    funext n
    by_cases hn : n ∈ Idx.i7.coords
    · have : n = 9 := by simpa [Idx.coords, Idx.isSz, Idx.coord] using hn
      subst this
      rw [← hxz]
      exact hz 9 (by decide)
    · exact hx n hn
  rw [mem_bot, hx0]
  have := (rootElt_eq_sylowVec (a := a) (K := K) .i7 0).symm
  rw [rootElt_zero] at this
  rw [← this]
  simp

theorem sylowVec_eq_of_mem_S3 (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : Fin 12 → K}
    (hx : ∀ n ∈ ({0, 1, 2, 3, 4, 5, 7} : Finset (Fin 12)), x n = 0) :
    sylowVec a K x = rootElt K a .i11 (x 6) * rootElt K a .i12 (x 8) * rootElt K a .i7 (x 9) *
      rootElt K a .i9 (x 10) * rootElt K a .i10 (x 11) := by
  rw [sylowVec_eq_prod_rootElt hK, hx 0 (by decide), hx 1 (by decide), hx 2 (by decide),
    hx 3 (by decide), hx 4 (by decide), hx 5 (by decide), hx 7 (by decide)]
  simp only [rootElt_zero, one_mul, mul_one]

end Model

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable (h : Setup G)

theorem S₂_le_S₃_le_S₄_le_S :
    h.S₂ ≤ h.S₃ ∧ h.S₃ ≤ h.S₄ ∧ h.S₄ ≤ h.S ∧ h.S ≤ h.P ∧ h.P ≤ h.Kp := by
  obtain ⟨-, h23, h34, h4S, -⟩ := h.S₁_le_S₂_le_S₃_le_S₄_le_S
  exact ⟨h23, h34, h4S, h.S_le_P, le_sup_left.trans h.P_sup_Tsyl_le_J_Kp.2⟩

theorem eq_one_of_mem_V7_of_mem_R₁ {v : G} (h7 : v ∈ h.V .i7) (hR : v ∈ h.R₁) : v = 1 := by
  have hmem : v ∈ h.pull (rootV h.K h.a .i7 ⊓ R1 h.K h.a) := by
    rw [h.pull_inf]
    exact ⟨h7, hR⟩
  rw [rootV_seven_inf_R1 h.card_K, h.pull_bot] at hmem
  exact (mem_bot).1 hmem

theorem exists_mul_of_mem_S₃ {x : G} (hx : x ∈ h.S₃) :
    ∃ v₁₁ ∈ h.V .i11, ∃ v₁₂ ∈ h.V .i12, ∃ v₇ ∈ h.V .i7, ∃ v₉ ∈ h.V .i9, ∃ v₁₀ ∈ h.V .i10,
      x = v₁₁ * v₁₂ * v₇ * v₉ * v₁₀ := by
  obtain ⟨g, hg, hgΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hx
  have hg' : g ∈ (S3 h.K h.a : Set (ModGL F4.tag h.K)) := hg
  rw [(S3_spec h.card_K).2.1] at hg'
  obtain ⟨y, hy, rfl⟩ := hg'
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  refine ⟨_, h.elt_rootElt_mem_V .i11 (y 6), _, h.elt_rootElt_mem_V .i12 (y 8), _,
    h.elt_rootElt_mem_V .i7 (y 9), _, h.elt_rootElt_mem_V .i9 (y 10), _,
    h.elt_rootElt_mem_V .i10 (y 11), ?_⟩
  rw [sylowVec_eq_of_mem_S3 h.card_K hy,
    h.elt_mul' (mul_mem (mul_mem (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _)) (hΓ _ _)) (hΓ _ _),
    h.elt_mul' (mul_mem (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _)) (hΓ _ _),
    h.elt_mul' (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _), h.elt_mul' (hΓ _ _) (hΓ _ _)]

theorem exists_mul_of_mem_S₂ {x : G} (hx : x ∈ h.S₂) :
    ∃ v₁₁ ∈ h.V .i11, ∃ v₁₂ ∈ h.V .i12, ∃ v₁₀ ∈ h.V .i10, x = v₁₁ * v₁₂ * v₁₀ := by
  obtain ⟨g, hg, hgΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hx
  have hg' : g ∈ (S2 h.K h.a : Set (ModGL F4.tag h.K)) := hg
  rw [(S2_spec h.card_K).2.1] at hg'
  obtain ⟨y, hy, rfl⟩ := hg'
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  refine ⟨_, h.elt_rootElt_mem_V .i11 (y 6), _, h.elt_rootElt_mem_V .i12 (y 8), _,
    h.elt_rootElt_mem_V .i10 (y 11), ?_⟩
  rw [sylowVec_eq_of_mem_S2 h.card_K hy, h.elt_mul' (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _),
    h.elt_mul' (hΓ _ _) (hΓ _ _)]

theorem V_le_S₄ {k : Idx}
    (hk : k ∈ ({.i2, .i5, .i6, .i8, .i7, .i9, .i10, .i11, .i12} : Finset Idx)) :
    h.V k ≤ h.S₄ :=
  h.pull_mono (rootV_le_rootJoin hk)

theorem s_conj_elt_rootElt {i : Idx} (hi : i ≠ .i3) (c : h.K) :
    h.s * h.elt (rootElt h.K h.a i c) * h.s⁻¹ = h.elt (rootElt h.K h.a i.sPerm c) := by
  rw [← h.elt_weylS, ← h.elt_conj' weylS_mem_reeGamma
    (rootV_le_reeGamma h.card_K i (rootElt_mem_rootV _ _)), weylS_conj_rootElt hi]

theorem conj_s_mem_CH {i : Idx} (hi : i ≠ .i3) {x : G} (hx : x ∈ h.CH i) :
    h.s * x * h.s⁻¹ ∈ h.CH i.sPerm := by
  have e : h.Ht i.sPerm = (h.Ht i).map (MulAut.conj h.s).toMonoidHom := by
    show h.pull (torusHi h.K h.a i.sPerm) = (h.pull (torusHi h.K h.a i)).map _
    rw [← map_conj_weylS_torusHi h.card_K hi, h.pull_map_conj _ weylS_mem_reeGamma,
      h.elt_weylS]
  show h.s * x * h.s⁻¹ ∈ centralizer (h.Ht i.sPerm : Set G)
  rw [e]
  refine mem_centralizer_iff.2 ?_
  rintro _ ⟨c, hc, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hcx := mem_centralizer_iff.1 hx c hc
  calc h.s * c * h.s⁻¹ * (h.s * x * h.s⁻¹) = h.s * (c * x) * h.s⁻¹ := by group
    _ = h.s * (x * c) * h.s⁻¹ := by rw [hcx]
    _ = h.s * x * h.s⁻¹ * (h.s * c * h.s⁻¹) := by group

theorem mem_V_of_mem_P_of_mem_CH {i : Idx} (hi : i.isCenter = false) {x : G} (hxP : x ∈ h.P)
    (hxc : x ∈ h.CH i) : x ∈ h.V i := by
  have hHΓ : torusHi h.K h.a i ≤ F4.reeGamma h.K h.a :=
    (torusHi_le_torusH i).trans (torusH_le_reeGamma h.card_K)
  have hx : x ∈ h.L ⊓ centralizer (h.pull (torusHi h.K h.a i) : Set G) := ⟨h.P_le_L hxP, hxc⟩
  rw [← h.pull_centralizer_subgroup hHΓ] at hx
  obtain ⟨g, hg, hgΓ, rfl⟩ := h.mem_pull_iff_elt.1 hx
  have hgP : g ∈ F4.reeFixedPosUnipotent h.K h.a := (h.elt_mem_pull hgΓ).1 hxP
  have hmem := mem_inf.2 ⟨hgP, hg⟩
  rw [sylowP_inf_centralizer_torusHi h.one_le_a h.card_K hi] at hmem
  exact (h.elt_mem_pull hgΓ).2 hmem

theorem eq_of_r1c_eight_twelve {z : G} (hz : z ∈ h.R₁) (h8 : h.r1c z .i8 = 0)
    (h12 : h.r1c z .i12 = 0) :
    z = h.elt (rootElt h.K h.a .i11 (h.r1c z .i11)) * h.elt (rootElt h.K h.a .i9 (h.r1c z .i9)) *
      h.elt (rootElt h.K h.a .i10 (h.r1c z .i10)) := by
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  conv_lhs => rw [← h.elt_r1Elt_r1c hz]
  rw [r1Elt, h8, h12, rootElt_zero, rootElt_zero, one_mul, mul_one,
    h.elt_mul' (mul_mem (hΓ _ _) (hΓ _ _)) (hΓ _ _), h.elt_mul' (hΓ _ _) (hΓ _ _)]

theorem r1c_elt_rootElt {k : Idx} (hk : k.isR1 = true) (c : h.K) {l : Idx}
    (hl : l.isR1 = true) :
    h.r1c (h.elt (rootElt h.K h.a k c)) l = (Pi.single k c : Idx → h.K) l := by
  rw [rootElt_eq_r1Elt hk, h.r1c_elt_r1Elt _ hl]

theorem mem_R₁_of_equivariant_S₃ {j : Idx} (hj : Idx.brace .i7 j ≠ 0) {Ψ : h.K → G}
    (hΨ : ∀ c, Ψ c ∈ h.S₃) (hadd : ∀ c d, Ψ (c + d) = Ψ c * Ψ d)
    (hequiv : ∀ t : h.Kˣ × h.Kˣ, torusPair h.a t ∈ torusHi h.K h.a .i7 → ∀ c,
      Ψ ((rootChar h.K h.a j t : h.K) * c) =
        h.elt (torusPair h.a t) * Ψ c * (h.elt (torusPair h.a t))⁻¹)
    (c : h.K) : Ψ c ∈ h.R₁ := by
  classical
  have hdec : ∀ c, ∃ p ∈ h.V .i7, ∃ r ∈ h.R₁, r ∈ h.S₃ ∧ Ψ c = p * r := by
    intro c
    obtain ⟨v₁₁, h11, v₁₂, h12, v₇, h7, v₉, h9, v₁₀, h10, hΨc⟩ := h.exists_mul_of_mem_S₃ (hΨ c)
    have hs : v₁₁ * v₁₂ ∈ h.S₃ :=
      mul_mem (h.V_le_S₃ (by decide) h11) (h.V_le_S₃ (by decide) h12)
    refine ⟨v₇, h7, v₁₁ * v₁₂ * v₉ * v₁₀, mul_mem (mul_mem (mul_mem (h.V_le_R₁ (by decide) h11)
      (h.V_le_R₁ (by decide) h12)) (h.V_le_R₁ (by decide) h9)) (h.V_le_R₁ (by decide) h10),
      mul_mem (mul_mem hs (h.V_le_S₃ (by decide) h9)) (h.V_le_S₃ (by decide) h10), ?_⟩
    have c1 : v₁₁ * v₁₂ * v₇ = v₇ * (v₁₁ * v₁₂) := h.S₃_comm hs (h.V_le_S₃ (by decide) h7)
    rw [hΨc, c1]
    group
  choose p hp r hr hrS hpr using hdec
  have huniq : ∀ {p p' r r' : G}, p ∈ h.V .i7 → p' ∈ h.V .i7 → r ∈ h.R₁ → r' ∈ h.R₁ →
      p * r = p' * r' → p = p' := by
    intro p p' r r' hp hp' hr hr' e
    have hm : p'⁻¹ * p = r' * r⁻¹ := by
      calc p'⁻¹ * p = p'⁻¹ * (p * r) * r⁻¹ := by group
        _ = p'⁻¹ * (p' * r') * r⁻¹ := by rw [e]
        _ = r' * r⁻¹ := by group
    have h1 : p'⁻¹ * p = 1 := h.eq_one_of_mem_V7_of_mem_R₁ (mul_mem (inv_mem hp') hp)
      (hm ▸ mul_mem hr' (inv_mem hr))
    exact (inv_mul_eq_one.1 h1).symm
  have hpadd : ∀ c d, p (c + d) = p c * p d := by
    intro c d
    refine huniq (hp (c + d)) (mul_mem (hp c) (hp d)) (hr (c + d)) (mul_mem (hr c) (hr d)) ?_
    rw [← hpr, hadd, hpr, hpr]
    have hc : r c * p d = p d * r c := h.S₃_comm (hrS c) (h.V_le_S₃ (by decide) (hp d))
    calc p c * r c * (p d * r d) = p c * (r c * p d) * r d := by group
      _ = p c * (p d * r c) * r d := by rw [hc]
      _ = p c * p d * (r c * r d) := by group
  have hpconst : ∀ c d : h.K, c ≠ 0 → d ≠ 0 → p c = p d := by
    intro c d hc hd
    obtain ⟨t, ht, htc⟩ := exists_torusHi_rootChar_mul_eq h.card_K (i := .i7) rfl hj hc hd
    set b := h.elt (torusPair h.a t) with hbdef
    have hb : b ∈ h.Ht .i7 := (h.elt_torusPair_mem_Ht_iff t).2 ht
    have hbH := h.Ht_le_H .i7 hb
    have hbp : b * p c * b⁻¹ = p c := by
      rw [mem_centralizer_iff.1 (h.V_le_CH (i := .i7) rfl (Or.inl rfl) (hp c)) b hb,
        mul_inv_cancel_right]
    have hbr : b * r c * b⁻¹ ∈ h.R₁ :=
      (mem_normalizer_iff.1 (h.J_le_normalizer_R₁ (h.H_le_J hbH)) _).1 (hr c)
    have e := hequiv t ht c
    rw [htc, hpr, hpr] at e
    have e2 : p c * (b * r c * b⁻¹) = p d * r d := by
      rw [e]
      calc p c * (b * r c * b⁻¹) = (b * p c * b⁻¹) * (b * r c * b⁻¹) := by rw [hbp]
        _ = b * (p c * r c) * b⁻¹ := by group
    exact huniq (hp c) (hp d) hbr (hr d) e2
  obtain ⟨μ, hμ, hμ1⟩ := h.exists_ne_zero_add_one_ne_zero
  have hp1 := eq_one_of_add_of_const hμ hμ1 hpadd hpconst c
  rw [hpr c, hp1, one_mul]
  exact hr c

end Setup

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

@[expose] def B3 : Subgroup G where
  carrier := {x | x ∈ centralizer (h.S₃ : Set G) ∧ x ∈ centralizer (d.B1 : Set G) ∧
    ⁅x, h.t⁆ ∈ h.S₃}
  mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, mul_mem hx.2.1 hy.2.1, by
    rw [commutatorElement_mul_left_eq]
    have hc : x * ⁅y, h.t⁆ * x⁻¹ = ⁅y, h.t⁆ := by
      rw [← mem_centralizer_iff.1 hx.1 _ hy.2.2, mul_inv_cancel_right]
    rw [hc]
    exact mul_mem hy.2.2 hx.2.2⟩
  one_mem' := ⟨one_mem _, one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, inv_mem hx.2.1, by
    have e : ⁅x⁻¹, h.t⁆ = x⁻¹ * ⁅x, h.t⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, inv_inv, mul_assoc, mem_centralizer_iff.1 hx.1 _ (inv_mem hx.2.2),
      inv_mul_cancel_left]
    exact inv_mem hx.2.2⟩

theorem comm_t_mul_B3 {x y : G} (hx : x ∈ d.B3) (hy : y ∈ d.B3) :
    ⁅x * y, h.t⁆ = ⁅x, h.t⁆ * ⁅y, h.t⁆ := by
  rw [commutatorElement_mul_left_eq, ← mem_centralizer_iff.1 hx.1 _ hy.2.2,
    mul_inv_cancel_right, h.S₃_comm hy.2.2 hx.2.2]

theorem comm_t_inv_B3 {x : G} (hx : x ∈ d.B3) : ⁅x⁻¹, h.t⁆ = ⁅x, h.t⁆⁻¹ := by
  have e := d.comm_t_mul_B3 hx (inv_mem hx)
  rw [mul_inv_cancel, commutatorElement_one_left] at e
  exact eq_inv_of_mul_eq_one_right e.symm

theorem S₃_le_centralizer_B1 : h.S₃ ≤ centralizer (d.B1 : Set G) := fun v hv =>
  mem_centralizer_iff.2 fun _ hb => (mem_centralizer_iff.1 (d.B1_le_centralizer_S hb) v
    (h.S₂_le_S₃_le_S₄_le_S.2.1.trans h.S₂_le_S₃_le_S₄_le_S.2.2.1 hv)).symm

theorem t_not_mem_centralizer_B1 : h.t ∉ centralizer (d.B1 : Set G) := fun ht =>
  d.t_not_mem_centralizer_W12 (centralizer_le (SetLike.coe_subset_coe.2 d.W12_le_B1) ht)

theorem S₃_le_B3 : h.S₃ ≤ d.B3 := fun v hv =>
  ⟨mem_centralizer_iff.2 fun _ hu => h.S₃_comm hu hv, d.S₃_le_centralizer_B1 hv, by
    rw [commutatorElement_eq_one_iff_mul_comm.2 (h.mul_t_comm (h.pull_le_L _ hv))]
    exact one_mem _⟩

theorem mem_S₃_of_mem_B3 {x : G} (hx : x ∈ d.B3) (hxt : ⁅x, h.t⁆ = 1) : x ∈ h.S₃ := by
  have hxC : x ∈ h.C := mem_centralizer_singleton_iff.2
    (commutatorElement_eq_one_iff_mul_comm.1 hxt)
  obtain ⟨m, hm, rfl | rfl⟩ := h.exists_mul_of_mem_sup_zpowers_t (h.pull_le_L _)
    (h.C_inf_centralizer_S₃_le (mem_inf.2 ⟨hxC, hx.1⟩))
  · exact hm
  · exfalso
    apply d.t_not_mem_centralizer_B1
    have := mul_mem (inv_mem (d.S₃_le_centralizer_B1 hm)) hx.2.1
    rwa [inv_mul_cancel_left] at this

theorem mul_inv_mem_S₃_of_comm_eq {x y : G} (hx : x ∈ d.B3) (hy : y ∈ d.B3)
    (hxy : ⁅x, h.t⁆ = ⁅y, h.t⁆) : x * y⁻¹ ∈ h.S₃ :=
  d.mem_S₃_of_mem_B3 (mul_mem hx (inv_mem hy)) (by
    rw [d.comm_t_mul_B3 hx (inv_mem hy), d.comm_t_inv_B3 hy, hxy, mul_inv_cancel])

theorem comm_mem_S₃ {x y : G} (hx : x ∈ d.B3) (hy : y ∈ d.B3) : ⁅x, y⁆ ∈ h.S₃ := by
  refine d.mem_S₃_of_mem_B3 (by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)) ?_
  have e : ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := commutatorElement_def x y
  rw [e, d.comm_t_mul_B3 (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy),
    d.comm_t_mul_B3 (mul_mem hx hy) (inv_mem hx), d.comm_t_mul_B3 hx hy, d.comm_t_inv_B3 hx,
    d.comm_t_inv_B3 hy, h.S₃_comm hx.2.2 hy.2.2]
  group

theorem conj_Kp_mem_B3 {k : G} (hk : k ∈ h.Kp) {x : G} (hx : x ∈ d.B3) :
    k * x * k⁻¹ ∈ d.B3 := by
  obtain ⟨hkC, -⟩ := mem_inf.1 hk
  have hk3 := h.Kp_le_normalizer_S₂_S₃_S₄.2.1 hk
  have hk1 := d.Kp_le_normalizer_B1 hk
  have hkt : k * h.t * k⁻¹ = h.t := by
    rw [mem_centralizer_singleton_iff.1 hkC, mul_inv_cancel_right]
  refine ⟨(mem_normalizer_iff.1 (mem_normalizer_centralizer hk3) x).1 hx.1,
    (mem_normalizer_iff.1 (mem_normalizer_centralizer hk1) x).1 hx.2.1, ?_⟩
  have e : ⁅k * x * k⁻¹, h.t⁆ = k * ⁅x, h.t⁆ * k⁻¹ := by
    calc ⁅k * x * k⁻¹, h.t⁆ = ⁅k * x * k⁻¹, k * h.t * k⁻¹⁆ := by rw [hkt]
      _ = k * ⁅x, h.t⁆ * k⁻¹ := by simp only [commutatorElement_def]; group
  rw [e]
  exact (mem_normalizer_iff.1 hk3 _).1 hx.2.2

theorem Kp_le_normalizer_B3 : h.Kp ≤ normalizer (d.B3 : Set G) := fun k hk =>
  mem_normalizer_iff.2 fun b => ⟨d.conj_Kp_mem_B3 hk, fun hb => by
    have := d.conj_Kp_mem_B3 (inv_mem hk) hb
    rwa [show k⁻¹ * (k * b * k⁻¹) * k⁻¹⁻¹ = b by group] at this⟩

theorem W12_le_B3 : d.W12 ≤ d.B3 := fun z hz =>
  ⟨centralizer_le (SetLike.coe_subset_coe.2
      (h.S₂_le_S₃_le_S₄_le_S.2.1.trans h.S₂_le_S₃_le_S₄_le_S.2.2.1)) (d.W12_le_centralizer_S hz),
    mem_centralizer_iff.2 fun _ hb => d.B1_comm hb (d.W12_le_B1 hz),
    h.V_le_S₃ (k := .i12) (by decide) (d.comm_t_W12_mem hz)⟩

theorem W11_le_B3 : d.W11 ≤ d.B3 := fun y hy =>
  ⟨centralizer_le (SetLike.coe_subset_coe.2
      (h.S₂_le_S₃_le_S₄_le_S.2.1.trans h.S₂_le_S₃_le_S₄_le_S.2.2.1)) (d.W11_le_centralizer_S hy),
    mem_centralizer_iff.2 fun _ hb => d.B1_comm hb (d.W11_le_B1 hy),
    h.V_le_S₃ (k := .i11) (by decide) (d.comm_t_W11_mem hy)⟩

theorem WA_le_B3 {j : Idx} (hj : j = .i9 ∨ j = .i10) : d.WA j ≤ d.B3 := by
  intro x hx
  obtain ⟨h79, h710, -⟩ := d.comm_V7_WA9_WA10
  have hjj : IsWPair j j := by
    rcases hj with rfl | rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have h7 : ∀ g ∈ h.V .i7, Commute g x := fun g hg => by
    rcases hj with rfl | rfl
    · exact (commutatorElement_eq_one_iff_mul_comm.1 (h79 g hg x hx))
    · exact (commutatorElement_eq_one_iff_mul_comm.1 (h710 g hg x hx))
  have hR : ∀ g ∈ h.R₁, Commute g x := fun g hg =>
    mem_centralizer_iff.1 (d.A1_le_centralizer_R₁ hx.1) g hg
  refine ⟨mem_centralizer_iff.2 fun v hv => ?_, mem_centralizer_iff.2 fun b hb => ?_, ?_⟩
  · obtain ⟨v₁₁, h11, v₁₂, h12, v₇, h7', v₉, h9, v₁₀, h10, rfl⟩ := h.exists_mul_of_mem_S₃ hv
    exact ((((hR _ (h.V_le_R₁ (by decide) h11)).mul_left
      (hR _ (h.V_le_R₁ (by decide) h12))).mul_left (h7 _ h7')).mul_left
      (hR _ (h.V_le_R₁ (by decide) h9))).mul_left (hR _ (h.V_le_R₁ (by decide) h10)) |>.eq
  · obtain ⟨y, hy, z, hz, rfl⟩ := d.exists_mul_of_mem_B1 hb
    have hy' : y ∈ d.WA .i6 := by rw [d.WA_six_eq]; exact hy
    have hz' : z ∈ d.WA .i5 := by rw [d.WA_five_eq]; exact hz
    have c1 : Commute y x := (commutatorElement_eq_one_iff_mul_comm.1
      (d.comm_WA_eq_one hjj (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) (by
        rcases hj with rfl | rfl <;> decide) hx hy')).symm
    have c2 : Commute z x := (commutatorElement_eq_one_iff_mul_comm.1
      (d.comm_WA_eq_one hjj (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))) (by
        rcases hj with rfl | rfl <;> decide) hx hz')).symm
    exact (c1.mul_left c2).eq
  · exact h.V_le_S₃ (by rcases hj with rfl | rfl <;> decide)
      (d.comm_t_mem_V_of_mem_WA hjj.isCenter hjj.brace hx)

theorem B3_inf_CH_le_WA {j : Idx} (hj : j = .i9 ∨ j = .i10) : d.B3 ⊓ h.CH j ≤ d.WA j := by
  rintro x ⟨hx, hxc⟩
  have hjj : IsWPair j j := by
    rcases hj with rfl | rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have hjS3 : j ∈ ({.i7, .i9, .i10, .i11, .i12} : Finset Idx) := by
    rcases hj with rfl | rfl <;> decide
  have hS3P : h.S₃ ≤ h.P := h.S₂_le_S₃_le_S₄_le_S.2.1.trans
    (h.S₂_le_S₃_le_S₄_le_S.2.2.1.trans h.S₂_le_S₃_le_S₄_le_S.2.2.2.1)
  have hct : ⁅x, h.t⁆ ∈ h.CH j := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hxc (h.t_mem_CH j)) (inv_mem hxc)) (inv_mem (h.t_mem_CH j))
  have hv : ⁅x, h.t⁆ ∈ h.V j := h.mem_V_of_mem_P_of_mem_CH hjj.isCenter (hS3P hx.2.2) hct
  obtain ⟨w, hw, hwt⟩ := d.exists_WA_comm_t (h.V_le_R₁ hjj.mem)
    (h.V_le_CH hjj.isCenter (Or.inl rfl)) hv
  have hwB := d.WA_le_B3 hj hw
  have hr := d.mul_inv_mem_S₃_of_comm_eq hx hwB hwt.symm
  have hrc : x * w⁻¹ ∈ h.CH j := mul_mem hxc (inv_mem hw.2)
  have hrV : x * w⁻¹ ∈ h.V j := h.mem_V_of_mem_P_of_mem_CH hjj.isCenter (hS3P hr) hrc
  have e : x = (x * w⁻¹) * w := by group
  rw [e]
  exact mul_mem (d.V_le_WA (h.V_le_R₁ hjj.mem) (h.V_le_CH hjj.isCenter (Or.inl rfl)) hrV) hw

theorem conj_s_mem_WA10 {y : G} (hy : y ∈ d.WA .i10) : h.s * y * h.s⁻¹ ∈ d.WA .i10 :=
  d.B3_inf_CH_le_WA (Or.inr rfl) ⟨d.conj_Kp_mem_B3 h.s_mem_Kp (d.WA_le_B3 (Or.inr rfl) hy),
    h.conj_s_mem_CH (i := .i10) (by decide) hy.2⟩

@[expose] def W7 : Subgroup G := (d.WA .i9).map (MulAut.conj h.s).toMonoidHom

theorem mem_W7_iff {y : G} : y ∈ d.W7 ↔ h.s * y * h.s⁻¹ ∈ d.WA .i9 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have e : h.s * (MulAut.conj h.s).toMonoidHom z * h.s⁻¹ = z := by
      change h.s * (h.s * z * h.s⁻¹) * h.s⁻¹ = z
      rw [h.s_inv, show h.s * (h.s * z * h.s) * h.s = (h.s * h.s) * z * (h.s * h.s) by group,
        h.r_mul_self_s_mul_self.2, one_mul, mul_one]
    rw [e]
    exact hz
  · intro hy
    refine ⟨h.s * y * h.s⁻¹, hy, ?_⟩
    change h.s * (h.s * y * h.s⁻¹) * h.s⁻¹ = y
    rw [h.s_inv, show h.s * (h.s * y * h.s) * h.s = (h.s * h.s) * y * (h.s * h.s) by group,
      h.r_mul_self_s_mul_self.2, one_mul, mul_one]

theorem conj_s_mem_W7 {z : G} (hz : z ∈ d.WA .i9) : h.s * z * h.s⁻¹ ∈ d.W7 := ⟨z, hz, rfl⟩

theorem W7_le_B3 : d.W7 ≤ d.B3 := by
  rintro _ ⟨z, hz, rfl⟩
  exact d.conj_Kp_mem_B3 h.s_mem_Kp (d.WA_le_B3 (Or.inl rfl) hz)

theorem W7_le_CH7 : d.W7 ≤ h.CH .i7 := by
  rintro _ ⟨z, hz, rfl⟩
  exact h.conj_s_mem_CH (i := .i9) (by decide) hz.2

theorem exists_W7_comm_t {v : G} (hv : v ∈ h.V .i7) : ∃ w ∈ d.W7, ⁅w, h.t⁆ = v := by
  have hv' : h.s * v * h.s⁻¹ ∈ h.V .i9 := h.conj_s_mem_V (i := .i7) (by decide) hv
  obtain ⟨z, hz, hzt⟩ := d.exists_WA_comm_t (h.V_le_R₁ (by decide))
    (h.V_le_CH rfl (Or.inl rfl)) hv'
  refine ⟨h.s * z * h.s⁻¹, d.conj_s_mem_W7 hz, ?_⟩
  have e : ⁅h.s * z * h.s⁻¹, h.t⁆ = h.s * ⁅z, h.t⁆ * h.s⁻¹ := by
    conv_lhs => rw [← h.s_conj_t']
    simp only [commutatorElement_def]; group
  rw [e, hzt, h.s_inv, show h.s * (h.s * v * h.s) * h.s = (h.s * h.s) * v * (h.s * h.s) by group,
    h.r_mul_self_s_mul_self.2, one_mul, mul_one]

theorem mem_V7_of_mem_W7 {y : G} (hy : y ∈ d.W7) (hyt : ⁅y, h.t⁆ = 1) : y ∈ h.V .i7 := by
  have hbr9 : ∀ m : Idx, m.isR1 = true → m ≠ .i9 → Idx.brace .i9 m ≠ 0 := by decide
  have hz := (d.mem_W7_iff).1 hy
  have hzt : ⁅h.s * y * h.s⁻¹, h.t⁆ = 1 := by
    have e : ⁅h.s * y * h.s⁻¹, h.t⁆ = h.s * ⁅y, h.t⁆ * h.s⁻¹ := by
      conv_lhs => rw [← h.s_conj_t']
      simp only [commutatorElement_def]; group
    rw [e, hyt, mul_one, mul_inv_cancel]
  have hv := h.conj_s_mem_V (i := .i9) (by decide) (d.mem_V_of_mem_WA rfl hbr9 hz hzt)
  rwa [h.s_inv, show h.s * (h.s * y * h.s) * h.s = (h.s * h.s) * y * (h.s * h.s) by group,
    h.r_mul_self_s_mul_self.2, one_mul, mul_one] at hv

theorem V7_le_W7 : h.V .i7 ≤ d.W7 := fun v hv => (d.mem_W7_iff).2
  (d.V_le_WA (h.V_le_R₁ (by decide)) (h.V_le_CH rfl (Or.inl rfl))
    (h.conj_s_mem_V (i := .i7) (by decide) hv))

theorem comm_t_mem_V7_of_mem_W7 {y : G} (hy : y ∈ d.W7) : ⁅y, h.t⁆ ∈ h.V .i7 := by
  have hc := h.V_le_CH (i := .i7) rfl (Or.inl rfl)
  have hyB := d.W7_le_B3 hy
  have hct : ⁅y, h.t⁆ ∈ h.CH .i7 := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (d.W7_le_CH7 hy) (h.t_mem_CH _)) (inv_mem (d.W7_le_CH7 hy)))
      (inv_mem (h.t_mem_CH _))
  have hS3P : h.S₃ ≤ h.P := h.S₂_le_S₃_le_S₄_le_S.2.1.trans
    (h.S₂_le_S₃_le_S₄_le_S.2.2.1.trans h.S₂_le_S₃_le_S₄_le_S.2.2.2.1)
  exact h.mem_V_of_mem_P_of_mem_CH rfl (hS3P hyB.2.2) hct

theorem W7_comm {x y : G} (hx : x ∈ d.W7) (hy : y ∈ d.W7) : x * y = y * x := by
  have h1 := d.WA_comm' (Or.inr (Or.inl ⟨rfl, rfl⟩)) ((d.mem_W7_iff).1 hx) ((d.mem_W7_iff).1 hy)
  have e : h.s * (x * y) * h.s⁻¹ = h.s * (y * x) * h.s⁻¹ := by
    calc h.s * (x * y) * h.s⁻¹ = (h.s * x * h.s⁻¹) * (h.s * y * h.s⁻¹) := by group
      _ = (h.s * y * h.s⁻¹) * (h.s * x * h.s⁻¹) := h1
      _ = h.s * (y * x) * h.s⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel e)

theorem comm_W7_WA9_mem {x y : G} (hx : x ∈ d.W7) (hy : y ∈ d.WA .i9) :
    ⁅x, y⁆ ∈ h.R₁ ∧ h.r1c ⁅x, y⁆ .i8 = 0 ∧ h.r1c ⁅x, y⁆ .i12 = 0 := by
  classical
  have hbr9 : ∀ m : Idx, m.isR1 = true → m ≠ .i9 → Idx.brace .i9 m ≠ 0 := by decide
  have hex : ∀ c : h.K, ∃ z ∈ d.WA .i9, ⁅z, h.t⁆ = h.elt (rootElt h.K h.a .i9 c) := fun c =>
    d.exists_WA_comm_t (h.V_le_R₁ (by decide)) (h.V_le_CH rfl (Or.inl rfl))
      (h.elt_rootElt_mem_V .i9 c)
  choose lam hlam hlamt using hex
  have hxB := d.W7_le_B3 hx
  have hlB : ∀ c, lam c ∈ d.B3 := fun c => d.WA_le_B3 (Or.inl rfl) (hlam c)
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  have hmod : ∀ {z : G}, z ∈ d.WA .i9 → ∀ {c : h.K},
      ⁅z, h.t⁆ = h.elt (rootElt h.K h.a .i9 c) → z * (lam c)⁻¹ ∈ h.V .i9 := fun {z} hz {c} hzc =>
    d.mem_V_of_mem_WA rfl hbr9 (mul_mem hz (inv_mem (hlam c))) (by
      rw [d.comm_t_mul_A1 hz.1 (inv_mem (hlam c)).1, d.comm_t_inv_A1 (hlam c).1, hzc, hlamt,
        mul_inv_cancel])
  have hred : ∀ {v z : G}, v ∈ h.S₃ → z ∈ d.B3 → ⁅x, v * z⁆ = ⁅x, z⁆ := fun {v z} hv hz => by
    rw [commutatorElement_mul_right_eq, commutatorElement_eq_one_iff_mul_comm.2
      (mem_centralizer_iff.1 hxB.1 v hv).symm, one_mul,
      h.S₃_comm hv (d.comm_mem_S₃ hxB hz), mul_inv_cancel_right]
  have hΨ : ∀ c, ⁅x, lam c⁆ ∈ h.S₃ := fun c => d.comm_mem_S₃ hxB (hlB c)
  have hadd : ∀ c c', ⁅x, lam (c + c')⁆ = ⁅x, lam c⁆ * ⁅x, lam c'⁆ := by
    intro c c'
    have hz : lam c * lam c' ∈ d.WA .i9 := mul_mem (hlam c) (hlam c')
    have hzc : ⁅lam c * lam c', h.t⁆ = h.elt (rootElt h.K h.a .i9 (c + c')) := by
      rw [d.comm_t_mul_A1 (hlam c).1 (hlam c').1, hlamt, hlamt, rootElt_add h.card_K rfl,
        h.elt_mul' (hΓ _ _) (hΓ _ _)]
    have hv : lam (c + c') * (lam c * lam c')⁻¹ ∈ h.V .i9 := by
      have := inv_mem (hmod hz hzc)
      rwa [mul_inv_rev, inv_inv] at this
    have e1 : lam (c + c') = (lam (c + c') * (lam c * lam c')⁻¹) * (lam c * lam c') := by group
    rw [e1, hred (h.V_le_S₃ (by decide) hv) (mul_mem (hlB c) (hlB c')),
      commutatorElement_mul_right_eq, ← mem_centralizer_iff.1 (hlB c).1 _ (hΨ c'),
      mul_inv_cancel_right]
  have hequiv : ∀ t : h.Kˣ × h.Kˣ, torusPair h.a t ∈ torusHi h.K h.a .i7 → ∀ c,
      ⁅x, lam ((rootChar h.K h.a .i9 t : h.K) * c)⁆ =
        h.elt (torusPair h.a t) * ⁅x, lam c⁆ * (h.elt (torusPair h.a t))⁻¹ := by
    intro t ht c
    set b := h.elt (torusPair h.a t) with hbdef
    have hb : b ∈ h.Ht .i7 := (h.elt_torusPair_mem_Ht_iff t).2 ht
    have hbH := h.Ht_le_H .i7 hb
    have hxb : x * b = b * x := (mem_centralizer_iff.1 (d.W7_le_CH7 hx) b hb).symm
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
    rw [e1, hred (h.V_le_S₃ (by decide) hv) (d.WA_le_B3 (Or.inl rfl) hz),
      commutatorElement_conj_of_commute hxb]
  have hΨR : ∀ c, ⁅x, lam c⁆ ∈ h.R₁ :=
    h.mem_R₁_of_equivariant_S₃ (j := .i9) (by decide) hΨ hadd hequiv
  have hrow : ∀ {k : Idx}, k.isR1 = true → Idx.brace .i7 .i9 ≠ Idx.brace .i7 k → ∀ c,
      h.r1c ⁅x, lam c⁆ k = 0 := fun {k} hk hb c =>
    h.r1c_eq_zero_of_brace_ne' (i := .i7) (j := .i9) rfl (Ψ := fun c => ⁅x, lam c⁆)
      (fun c c' l hl => by
        show h.r1c ⁅x, lam (c + c')⁆ l = h.r1c ⁅x, lam c⁆ l + h.r1c ⁅x, lam c'⁆ l
        rw [hadd, h.r1c_mul (hΨR c) (hΨR c') hl])
      (fun t ht c l hl => by
        show h.r1c ⁅x, lam ((rootChar h.K h.a .i9 t : h.K) * c)⁆ l =
          (rootChar h.K h.a l t : h.K) * h.r1c ⁅x, lam c⁆ l
        rw [hequiv t ht c, h.r1c_torus (hΨR c) t hl])
      hk hb c
  obtain ⟨c, hc⟩ := h.exists_eq_elt_rootElt (i := .i9) rfl
    (d.comm_t_mem_V_of_mem_WA rfl hbr9 hy)
  have e2 : ⁅x, y⁆ = ⁅x, lam c⁆ := by
    rw [show y = (y * (lam c)⁻¹) * lam c by group,
      hred (h.V_le_S₃ (by decide) (hmod hy hc)) (hlB c)]
  rw [e2]
  exact ⟨hΨR c, hrow (k := .i8) rfl (by decide) c, hrow (k := .i12) rfl (by decide) c⟩

theorem comm_W7_WA9_mem_V10 {x y : G} (hx : x ∈ d.W7) (hy : y ∈ d.WA .i9) :
    ⁅x, y⁆ ∈ h.V .i10 := by
  obtain ⟨hR, h8, h12⟩ := d.comm_W7_WA9_mem hx hy
  obtain ⟨hR', -, h12'⟩ := d.comm_W7_WA9_mem (d.conj_s_mem_W7 hy) ((d.mem_W7_iff).1 hx)
  have e : ⁅h.s * y * h.s⁻¹, h.s * x * h.s⁻¹⁆ = (h.s * ⁅x, y⁆ * h.s⁻¹)⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e] at hR' h12'
  have hR'' : h.s * ⁅x, y⁆ * h.s⁻¹ ∈ h.R₁ := by
    have := inv_mem hR'
    rwa [inv_inv] at this
  have h12'' : h.r1c (h.s * ⁅x, y⁆ * h.s⁻¹) .i12 = 0 := by
    rw [← h.r1c_inv hR'' rfl]
    exact h12'
  have hzeq := h.eq_of_r1c_eight_twelve hR h8 h12
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  obtain ⟨u, hu⟩ : ∃ u, u = h.r1c ⁅x, y⁆ := ⟨_, rfl⟩
  rw [← hu] at hzeq
  have hsz : h.s * ⁅x, y⁆ * h.s⁻¹ = h.elt (rootElt h.K h.a .i12 (u .i11)) *
      h.elt (rootElt h.K h.a .i7 (u .i9)) * h.elt (rootElt h.K h.a .i10 (u .i10)) := by
    rw [hzeq, show h.s * (h.elt (rootElt h.K h.a .i11 (u .i11)) *
        h.elt (rootElt h.K h.a .i9 (u .i9)) * h.elt (rootElt h.K h.a .i10 (u .i10))) * h.s⁻¹ =
        (h.s * h.elt (rootElt h.K h.a .i11 (u .i11)) * h.s⁻¹) *
          (h.s * h.elt (rootElt h.K h.a .i9 (u .i9)) * h.s⁻¹) *
          (h.s * h.elt (rootElt h.K h.a .i10 (u .i10)) * h.s⁻¹) by group,
      h.s_conj_elt_rootElt (i := .i11) (by decide), h.s_conj_elt_rootElt (i := .i9) (by decide),
      h.s_conj_elt_rootElt (i := .i10) (by decide)]
    rfl
  have h7 : h.elt (rootElt h.K h.a .i7 (u .i9)) = 1 := by
    refine h.eq_one_of_mem_V7_of_mem_R₁ (h.elt_rootElt_mem_V .i7 _) ?_
    have h1 := h.elt_rootElt_mem_R₁ (k := .i12) rfl (u .i11)
    have h2 := h.elt_rootElt_mem_R₁ (k := .i10) rfl (u .i10)
    have := mul_mem (mul_mem (inv_mem h1) hR'') (inv_mem h2)
    rwa [hsz, show (h.elt (rootElt h.K h.a .i12 (u .i11)))⁻¹ *
      (h.elt (rootElt h.K h.a .i12 (u .i11)) * h.elt (rootElt h.K h.a .i7 (u .i9)) *
        h.elt (rootElt h.K h.a .i10 (u .i10))) * (h.elt (rootElt h.K h.a .i10 (u .i10)))⁻¹ =
      h.elt (rootElt h.K h.a .i7 (u .i9)) by group] at this
  have hu9 : u .i9 = 0 := by
    have e7 : h.elt (rootElt h.K h.a .i7 (u .i9)) = h.elt (rootElt h.K h.a .i7 0) := by
      rw [h7, rootElt_zero, h.elt_one']
    exact rootElt_injective h.card_K .i7 (h.elt_injOn (hΓ _ _) (hΓ _ _) e7)
  have hu11 : u .i11 = 0 := by
    rw [hsz, hu9, rootElt_zero, h.elt_one', mul_one,
      h.r1c_mul (h.elt_rootElt_mem_R₁ rfl _) (h.elt_rootElt_mem_R₁ rfl _) rfl,
      h.r1c_elt_rootElt (k := .i12) rfl _ rfl, h.r1c_elt_rootElt (k := .i10) rfl _ rfl,
      Pi.single_eq_same, Pi.single_eq_of_ne (by decide), add_zero] at h12''
    exact h12''
  rw [hzeq, hu9, hu11, rootElt_zero, rootElt_zero, h.elt_one', one_mul, one_mul]
  exact h.elt_rootElt_mem_V .i10 _

theorem comm_W7_WA10_mem {x y : G} (hx : x ∈ d.W7) (hy : y ∈ d.WA .i10) :
    ⁅x, y⁆ ∈ h.V .i11 := by
  have h1 : ⁅h.s * x * h.s⁻¹, h.s * y * h.s⁻¹⁆ ∈ h.V .i12 :=
    d.commutator_A1_le (commutator_mem_commutator ((d.mem_W7_iff).1 hx).1
      (d.conj_s_mem_WA10 hy).1)
  have e : ⁅h.s * x * h.s⁻¹, h.s * y * h.s⁻¹⁆ = h.s * ⁅x, y⁆ * h.s⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e] at h1
  have h2 := h.conj_s_V12 h1
  rwa [h.s_inv, show h.s * (h.s * ⁅x, y⁆ * h.s) * h.s = (h.s * h.s) * ⁅x, y⁆ * (h.s * h.s) by
    group, h.r_mul_self_s_mul_self.2, one_mul, mul_one] at h2

theorem sec3_7_two :
    (∀ x ∈ d.W7, ∀ y ∈ d.WA .i9, ⁅x, y⁆ ∈ h.V .i10) ∧
      (∀ x ∈ d.W7, ∀ y ∈ d.WA .i10, ⁅x, y⁆ ∈ h.V .i11) ∧
      (∀ x ∈ d.WA .i9, ∀ y ∈ d.WA .i10, ⁅x, y⁆ ∈ h.V .i12) ∧
      (∀ x ∈ d.W7, ∀ y ∈ d.W7, ⁅x, y⁆ = 1) ∧ (∀ x ∈ d.WA .i9, ∀ y ∈ d.WA .i9, ⁅x, y⁆ = 1) ∧
      (∀ x ∈ d.WA .i10, ∀ y ∈ d.WA .i10, ⁅x, y⁆ = 1) ∧ (∀ x ∈ d.B3, ∀ y ∈ d.B1, ⁅x, y⁆ = 1) :=
  ⟨fun _ hx _ hy => d.comm_W7_WA9_mem_V10 hx hy, fun _ hx _ hy => d.comm_W7_WA10_mem hx hy,
    fun _ hx _ hy => d.commutator_A1_le (commutator_mem_commutator hx.1 hy.1),
    fun _ hx _ hy => commutatorElement_eq_one_iff_mul_comm.2 (d.W7_comm hx hy),
    fun _ hx _ hy => commutatorElement_eq_one_iff_mul_comm.2
      (d.WA_comm' (Or.inr (Or.inl ⟨rfl, rfl⟩)) hx hy),
    fun _ hx _ hy => commutatorElement_eq_one_iff_mul_comm.2
      (d.WA_comm' (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hx hy),
    fun _ hx _ hy => commutatorElement_eq_one_iff_mul_comm.2
      (mem_centralizer_iff.1 hx.2.1 _ hy).symm⟩

@[expose] def B2 : Subgroup G := d.WA .i10 ⊔ d.B1

theorem B2_le_B3 : d.B2 ≤ d.B3 :=
  sup_le (d.WA_le_B3 (Or.inr rfl)) (sup_le d.W11_le_B3 d.W12_le_B3)

theorem exists_B3_comm_t {v : G} (hv : v ∈ h.S₃) :
    ∃ w ∈ d.W7 ⊔ d.WA .i9 ⊔ d.B2, ⁅w, h.t⁆ = v := by
  set M := d.W7 ⊔ d.WA .i9 ⊔ d.B2 with hM
  have h7 : d.W7 ≤ M := le_sup_left.trans le_sup_left
  have h9 : d.WA .i9 ≤ M := le_sup_right.trans le_sup_left
  have h10 : d.WA .i10 ≤ M := le_sup_left.trans le_sup_right
  have h11 : d.W11 ≤ M := (le_sup_left.trans le_sup_right).trans le_sup_right
  have h12 : d.W12 ≤ M := (le_sup_right.trans le_sup_right).trans le_sup_right
  have hMB : M ≤ d.B3 := sup_le (sup_le d.W7_le_B3 (d.WA_le_B3 (Or.inl rfl))) d.B2_le_B3
  obtain ⟨v₁₁, hv11, v₁₂, hv12, v₇, hv7, v₉, hv9, v₁₀, hv10, rfl⟩ := h.exists_mul_of_mem_S₃ hv
  obtain ⟨w₁₁, hw11, e11⟩ := d.exists_W11_comm_t hv11
  obtain ⟨w₁₂, hw12, e12⟩ := d.exists_W12_conj hv12
  obtain ⟨w₇, hw7, e7⟩ := d.exists_W7_comm_t hv7
  obtain ⟨w₉, hw9, e9⟩ := d.exists_WA_comm_t (h.V_le_R₁ (by decide))
    (h.V_le_CH rfl (Or.inl rfl)) hv9
  obtain ⟨w₁₀, hw10, e10⟩ := d.exists_WA_comm_t (h.V_le_R₁ (by decide))
    (h.V_le_CH rfl (Or.inl rfl)) hv10
  have e12' : ⁅w₁₂, h.t⁆ = v₁₂ := by
    rw [commutatorElement_def, e12, ← h.mul_t_comm (h.V12_le_L hv12), mul_inv_cancel_right]
  refine ⟨w₁₁ * w₁₂ * w₇ * w₉ * w₁₀,
    mul_mem (mul_mem (mul_mem (mul_mem (h11 hw11) (h12 hw12)) (h7 hw7)) (h9 hw9)) (h10 hw10), ?_⟩
  have hB := fun {z} (hz : z ∈ M) => hMB hz
  rw [d.comm_t_mul_B3 (hB (mul_mem (mul_mem (mul_mem (h11 hw11) (h12 hw12)) (h7 hw7)) (h9 hw9)))
      (hB (h10 hw10)),
    d.comm_t_mul_B3 (hB (mul_mem (mul_mem (h11 hw11) (h12 hw12)) (h7 hw7))) (hB (h9 hw9)),
    d.comm_t_mul_B3 (hB (mul_mem (h11 hw11) (h12 hw12))) (hB (h7 hw7)),
    d.comm_t_mul_B3 (hB (h11 hw11)) (hB (h12 hw12)), e11, e12', e7, e9, e10]

theorem B3_eq : d.B3 = d.W7 ⊔ d.WA .i9 ⊔ d.B2 := by
  have hMB : d.W7 ⊔ d.WA .i9 ⊔ d.B2 ≤ d.B3 :=
    sup_le (sup_le d.W7_le_B3 (d.WA_le_B3 (Or.inl rfl))) d.B2_le_B3
  refine le_antisymm (fun x hx => ?_) hMB
  have hS3M : h.S₃ ≤ d.W7 ⊔ d.WA .i9 ⊔ d.B2 := by
    show h.pull (rootJoin h.K h.a {.i7, .i9, .i10, .i11, .i12}) ≤ _
    refine h.pull_rootJoin_le fun k hk => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact d.V7_le_W7.trans (le_sup_left.trans le_sup_left)
    · exact (d.V_le_WA (h.V_le_R₁ (by decide)) (h.V_le_CH rfl (Or.inl rfl))).trans
        (le_sup_right.trans le_sup_left)
    · exact (d.V_le_WA (h.V_le_R₁ (by decide)) (h.V_le_CH rfl (Or.inl rfl))).trans
        (le_sup_left.trans le_sup_right)
    · exact d.V11_le_W11.trans ((le_sup_left.trans le_sup_right).trans le_sup_right)
    · exact d.V12_le_W12.trans ((le_sup_right.trans le_sup_right).trans le_sup_right)
  obtain ⟨w, hw, hwt⟩ := d.exists_B3_comm_t hx.2.2
  have hr := d.mul_inv_mem_S₃_of_comm_eq hx (hMB hw) hwt.symm
  have e : x = (x * w⁻¹) * w := by group
  rw [e]
  exact mul_mem (hS3M hr) hw

theorem WA10_le_centralizer_S₄ : d.WA .i10 ≤ centralizer (h.S₄ : Set G) := by
  intro x hx
  have hxB := d.WA_le_B3 (Or.inr rfl) hx
  have hR : ∀ g ∈ h.R₁, g * x = x * g := fun g hg =>
    mem_centralizer_iff.1 (d.A1_le_centralizer_R₁ hx.1) g hg
  have hle : h.S₄ ≤ centralizer ({x} : Set G) := by
    show h.pull (rootJoin h.K h.a {.i2, .i5, .i6, .i8, .i7, .i9, .i10, .i11, .i12}) ≤ _
    refine h.pull_rootJoin_le fun k hk v hv => mem_centralizer_singleton_iff.2 ?_
    by_cases hk3 : k ∈ ({.i7, .i9, .i10, .i11, .i12} : Finset Idx)
    · exact mem_centralizer_iff.1 hxB.1 v (h.V_le_S₃ hk3 hv)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | hk
    ·
      have hv8 : h.s * v * h.s⁻¹ ∈ h.V .i8 := h.conj_s_mem_V (i := .i2) (by decide) hv
      have hc := hR _ (h.V_le_R₁ (by decide) hv8)
      have hx' := d.conj_s_mem_WA10 hx
      have hc' : (h.s * v * h.s⁻¹) * (h.s * x * h.s⁻¹) = (h.s * x * h.s⁻¹) * (h.s * v * h.s⁻¹) :=
        mem_centralizer_iff.1 (d.A1_le_centralizer_R₁ hx'.1) _ (h.V_le_R₁ (by decide) hv8)
      have e : h.s * (v * x) * h.s⁻¹ = h.s * (x * v) * h.s⁻¹ := by
        calc h.s * (v * x) * h.s⁻¹ = (h.s * v * h.s⁻¹) * (h.s * x * h.s⁻¹) := by group
          _ = (h.s * x * h.s⁻¹) * (h.s * v * h.s⁻¹) := hc'
          _ = h.s * (x * v) * h.s⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel e)
    · exact mem_centralizer_iff.1 (d.A1_le_centralizer_V5 hx.1) v hv
    · exact commutatorElement_eq_one_iff_mul_comm.1 (d.comm_V7_WA9_WA10.2.2 v hv x hx)
    · exact hR v (h.V_le_R₁ (by decide) hv)
    · exact absurd (by simpa using hk) hk3
  exact mem_centralizer_iff.2 fun g hg => mem_centralizer_singleton_iff.1 (hle hg)

theorem B2_le_centralizer_S₄ : d.B2 ≤ centralizer (h.S₄ : Set G) :=
  sup_le d.WA10_le_centralizer_S₄ fun _ hb =>
    centralizer_le (SetLike.coe_subset_coe.2 h.S₂_le_S₃_le_S₄_le_S.2.2.1)
      (d.B1_le_centralizer_S hb)

theorem S₂_le_B2 : h.S₂ ≤ d.B2 := by
  show h.pull (rootJoin h.K h.a {.i10, .i11, .i12}) ≤ _
  refine h.pull_rootJoin_le fun k hk => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl
  · exact (d.V_le_WA (h.V_le_R₁ (by decide)) (h.V_le_CH rfl (Or.inl rfl))).trans le_sup_left
  · exact d.V11_le_W11.trans (d.W11_le_B1.trans le_sup_right)
  · exact d.V12_le_W12.trans (d.W12_le_B1.trans le_sup_right)

theorem B3_inf_centralizer_S₄ : d.B3 ⊓ centralizer (h.S₄ : Set G) = d.B2 := by
  refine le_antisymm ?_ (le_inf d.B2_le_B3 d.B2_le_centralizer_S₄)
  rintro x ⟨hx, hxc⟩
  have h34 := h.S₂_le_S₃_le_S₄_le_S.2.1
  have hZ : ∀ {v : G}, v ∈ h.S₃ → v ∈ centralizer (h.S₄ : Set G) → v ∈ h.S₂ := fun {v} hv hvc =>
    h.mem_S₂_of_commute (h34 hv) fun w hw => mem_centralizer_iff.1 hvc w hw
  have htS4 : h.t ∈ centralizer (h.S₄ : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 (h.pull_le_L _)) h.htL
  have hxt : ⁅x, h.t⁆ ∈ h.S₂ := hZ hx.2.2 (by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hxc htS4) (inv_mem hxc)) (inv_mem htS4))
  obtain ⟨v₁₁, hv11, v₁₂, hv12, v₁₀, hv10, hve⟩ := h.exists_mul_of_mem_S₂ hxt
  obtain ⟨w₁₁, hw11, e11⟩ := d.exists_W11_comm_t hv11
  obtain ⟨w₁₂, hw12, e12⟩ := d.exists_W12_conj hv12
  obtain ⟨w₁₀, hw10, e10⟩ := d.exists_WA_comm_t (h.V_le_R₁ (by decide))
    (h.V_le_CH rfl (Or.inl rfl)) hv10
  have e12' : ⁅w₁₂, h.t⁆ = v₁₂ := by
    rw [commutatorElement_def, e12, ← h.mul_t_comm (h.V12_le_L hv12), mul_inv_cancel_right]
  have h11B : w₁₁ ∈ d.B2 := mem_sup_right (d.W11_le_B1 hw11)
  have h12B : w₁₂ ∈ d.B2 := mem_sup_right (d.W12_le_B1 hw12)
  have h10B : w₁₀ ∈ d.B2 := mem_sup_left hw10
  have hwB : w₁₁ * w₁₂ * w₁₀ ∈ d.B2 := mul_mem (mul_mem h11B h12B) h10B
  have hB := fun {z} (hz : z ∈ d.B2) => d.B2_le_B3 hz
  have hwt : ⁅w₁₁ * w₁₂ * w₁₀, h.t⁆ = ⁅x, h.t⁆ := by
    rw [d.comm_t_mul_B3 (hB (mul_mem h11B h12B)) (hB h10B), d.comm_t_mul_B3 (hB h11B) (hB h12B),
      e11, e12', e10, hve]
  have hr := d.mul_inv_mem_S₃_of_comm_eq hx (hB hwB) hwt.symm
  have hrc : x * (w₁₁ * w₁₂ * w₁₀)⁻¹ ∈ centralizer (h.S₄ : Set G) :=
    mul_mem hxc (inv_mem (d.B2_le_centralizer_S₄ hwB))
  have e : x = (x * (w₁₁ * w₁₂ * w₁₀)⁻¹) * (w₁₁ * w₁₂ * w₁₀) := by group
  rw [e]
  exact mul_mem (d.S₂_le_B2 (hZ hr hrc)) hwB

theorem Kp_le_normalizer_B2 : h.Kp ≤ normalizer (d.B2 : Set G) := fun k hk => by
  rw [← d.B3_inf_centralizer_S₄]
  exact mem_normalizer_inf (d.Kp_le_normalizer_B3 hk)
    (mem_normalizer_centralizer (h.Kp_le_normalizer_S₂_S₃_S₄.2.2 hk))

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4

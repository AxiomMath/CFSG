module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootB4c

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem Idx.eq_of_isR1_of_ne_twelve : ∀ l : Idx, l.isR1 = true → l ≠ .i12 →
    l = .i8 ∨ l = .i9 ∨ l = .i10 ∨ l = .i11 := by decide

namespace Setup

variable (h : Setup G)

theorem S₃_le_R : h.S₃ ≤ h.R := h.pull_mono (rootJoin_le_rootJoin h.card_K (by decide))

theorem mem_R₁_of_equivariant_S₃' {j : Idx} (hj : Idx.brace .i7 j ≠ 0) {Ψ : h.K → G}
    (hΨ : ∀ c, Ψ c ∈ h.S₃) (hadd : ∀ c e, (Ψ c * Ψ e)⁻¹ * Ψ (c + e) ∈ h.R₁)
    (hequiv : ∀ t : h.Kˣ × h.Kˣ, torusPair h.a t ∈ torusHi h.K h.a .i7 → ∀ c,
      (h.elt (torusPair h.a t) * Ψ c * (h.elt (torusPair h.a t))⁻¹)⁻¹ *
        Ψ ((rootChar h.K h.a j t : h.K) * c) ∈ h.R₁)
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
  have hpadd : ∀ c e, p (c + e) = p c * p e := by
    intro c e
    have hρ := hadd c e
    set ρ := (Ψ c * Ψ e)⁻¹ * Ψ (c + e) with hρdef
    refine huniq (hp (c + e)) (mul_mem (hp c) (hp e)) (hr (c + e))
      (mul_mem (mul_mem (hr c) (hr e)) hρ) ?_
    rw [← hpr]
    have hc : r c * p e = p e * r c := h.S₃_comm (hrS c) (h.V_le_S₃ (by decide) (hp e))
    calc Ψ (c + e) = Ψ c * Ψ e * ρ := by rw [hρdef]; group
      _ = p c * r c * (p e * r e) * ρ := by rw [hpr, hpr]
      _ = p c * (r c * p e) * r e * ρ := by group
      _ = p c * (p e * r c) * r e * ρ := by rw [hc]
      _ = p c * p e * (r c * r e * ρ) := by group
  have hpconst : ∀ c e : h.K, c ≠ 0 → e ≠ 0 → p c = p e := by
    intro c e hc he
    obtain ⟨t, ht, htc⟩ := exists_torusHi_rootChar_mul_eq h.card_K (i := .i7) rfl hj hc he
    set b := h.elt (torusPair h.a t) with hbdef
    have hb : b ∈ h.Ht .i7 := (h.elt_torusPair_mem_Ht_iff t).2 ht
    have hbH := h.Ht_le_H .i7 hb
    have hbp : b * p c * b⁻¹ = p c := by
      rw [mem_centralizer_iff.1 (h.V_le_CH (i := .i7) rfl (Or.inl rfl) (hp c)) b hb,
        mul_inv_cancel_right]
    have hbr : b * r c * b⁻¹ ∈ h.R₁ :=
      (mem_normalizer_iff.1 (h.J_le_normalizer_R₁ (h.H_le_J hbH)) _).1 (hr c)
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

end Setup

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

theorem eq_B4_of_A1_le {Z : Subgroup G} (hZB : Z ≤ d.B4) (hA : d.A1 ≤ Z)
    (hZK : h.Kp ≤ normalizer (Z : Set G)) : Z = d.B4 := by
  have hR₁Z : h.R₁ ≤ Z := d.R₁_le_A1.trans hA
  have hS4Z : h.S₄ ≤ Z := h.S₄_le_of_V8_V9 (h.S₂_le_R₁.trans hR₁Z)
    ((h.V_le_R₁ (by decide)).trans hR₁Z) ((h.V_le_R₁ (by decide)).trans hR₁Z)
    (fun c => hZK (h.elt_rootElt_three_mem_Kp c)) (hZK h.s_mem_Kp) fun b hb => hZK (h.H_le_Kp hb)
  have hQ : d.Q4 ≤ Z := sup_le hS4Z (d.B2_le_A1.trans hA)
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
  exact d.eq_B4_of_S₄_le_imIn hZB hQ hS

theorem comm_A1_S₃_sup_B2_mem {a z : G} (ha : a ∈ d.A1) (hz : z ∈ h.S₃ ⊔ d.B2) :
    ⁅a, z⁆ ∈ d.W12 := by
  have hle : h.S₃ ⊔ d.B2 ≤ commRightIn a d.W12 := by
    refine sup_le (fun v hv => mem_commRightIn.2 ⟨?_, ?_⟩) fun b hb => mem_commRightIn.2 ⟨?_, ?_⟩
    · exact Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun z hz =>
        (mem_centralizer_iff.1 (d.W12_le_centralizer_S hz) v
          (h.S₂_le_S₃_le_S₄_le_S.2.1.trans h.S₂_le_S₃_le_S₄_le_S.2.2.1 hv)).symm)
    · rw [← commutatorElement_inv]
      exact inv_mem (d.commutator_R_A1_le (commutator_mem_commutator (h.S₃_le_R hv) ha))
    · exact Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun z hz =>
        d.B2_comm (mem_sup_right (d.W12_le_B1 hz)) hb)
    · rw [commutatorElement_eq_one_iff_mul_comm.2 (d.A1_comm ha (d.B2_le_A1 hb))]
      exact one_mem _
  exact (mem_commRightIn.1 (hle hz)).2

theorem B4_le_normalizer_S₃_sup_B1 : d.B4 ≤ normalizer ((h.S₃ ⊔ d.B1 : Subgroup G) : Set G) := by
  set M : Subgroup G := h.S₃ ⊔ d.B1 with hM
  have hKM : h.Kp ≤ normalizer (M : Set G) := fun k hk => by
    have h3 := h.Kp_le_normalizer_S₂_S₃_S₄.2.1 hk
    have h1 := d.Kp_le_normalizer_B1 hk
    have key : ∀ {k : G}, k ∈ normalizer (h.S₃ : Set G) → k ∈ normalizer (d.B1 : Set G) →
        ∀ m ∈ M, k * m * k⁻¹ ∈ M := fun {k} h3 h1 m hm => by
      have hle : M ≤ M.comap (MulAut.conj k).toMonoidHom :=
        sup_le (fun v hv => mem_sup_left ((mem_normalizer_iff.1 h3 v).1 hv))
          (fun b hb => mem_sup_right ((mem_normalizer_iff.1 h1 b).1 hb))
      exact hle hm
    refine mem_normalizer_of_conj_mem (key h3 h1) fun m hm => ?_
    have := key (inv_mem h3) (inv_mem h1) m hm
    rwa [inv_inv] at this
  have hAM : ∀ {a : G}, a ∈ d.A1 → ∀ m ∈ M, a * m * a⁻¹ ∈ M := fun {a} ha m hm => by
    have hle : M ≤ M.comap (MulAut.conj a).toMonoidHom := by
      refine sup_le (fun v hv => ?_) fun b hb => ?_
      · change a * v * a⁻¹ ∈ M
        have e : a * v * a⁻¹ = ⁅a, v⁆ * v := by simp only [commutatorElement_def]; group
        rw [e]
        exact mul_mem (mem_sup_right (d.W12_le_B1
          (d.comm_A1_S₃_sup_B2_mem ha (mem_sup_left hv)))) (mem_sup_left hv)
      · change a * b * a⁻¹ ∈ M
        rw [← mem_centralizer_iff.1 (d.B4_le_centralizer_B1 (d.A1_le_B4 ha)) b hb,
          mul_inv_cancel_right]
        exact mem_sup_right hb
    exact hle hm
  set Z := d.B4 ⊓ normalizer (M : Set G) with hZ
  have hZK : h.Kp ≤ normalizer (Z : Set G) := fun k hk =>
    mem_normalizer_inf (d.Kp_le_normalizer_B4 hk) (le_normalizer (hKM hk))
  have hAZ : d.A1 ≤ Z := fun a ha => mem_inf.2 ⟨d.A1_le_B4 ha,
    mem_normalizer_of_conj_mem (hAM ha) fun m hm => by
      have := hAM (inv_mem ha) m hm
      rwa [inv_inv] at this⟩
  have := d.eq_B4_of_A1_le inf_le_left hAZ hZK
  rw [← this]
  exact inf_le_right

theorem B3_eq_B4_inf : d.B3 = d.B4 ⊓ centralizer (h.S₃ : Set G) := by
  have hZ : ∀ {q : G}, q ∈ d.Q4 → q ∈ centralizer (h.S₃ : Set G) →
      ∃ v ∈ h.S₃, ∃ b ∈ d.B2, q = v * b := by
    intro q hq hqc
    have hqQ : q ∈ ((h.S₄ ⊔ d.B2 : Subgroup G) : Set G) := hq
    rw [coe_mul_of_left_le_normalizer_right _ _ (h.S₄_le_Kp.trans d.Kp_le_normalizer_B2),
      Set.mem_mul] at hqQ
    obtain ⟨v, hv, b, hb, rfl⟩ := hqQ
    have hvc : v ∈ centralizer (h.S₃ : Set G) := by
      have := mul_mem hqc (inv_mem ((d.B2_le_B3 hb).1))
      rwa [mul_inv_cancel_right] at this
    exact ⟨v, h.L_inf_centralizer_S₃_le (mem_inf.2 ⟨h.pull_le_L _ hv, hvc⟩), b, hb, rfl⟩
  refine le_antisymm (le_inf d.B3_le_B4 fun x hx => hx.1) fun x hx => ?_
  obtain ⟨hxB, hxc⟩ := mem_inf.1 hx
  have htS : h.t ∈ centralizer (h.S₃ : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 (h.pull_le_L _)) h.htL
  obtain ⟨v, hv, b, hb, hvb⟩ := hZ hxB.2.2.2.2 (by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hxc htS) (inv_mem hxc)) (inv_mem htS))
  obtain ⟨y, hy, hyt⟩ := d.exists_B3_comm_t hv
  have hyB3 : y ∈ d.B3 := d.B3_eq ▸ hy
  have hq : y⁻¹ * x ∈ d.Q4 := d.inv_mul_mem_Q4_of_comm (d.B3_le_B4 hyB3) hxB (by
    rw [hyt, hvb]
    group
    exact hb)
  obtain ⟨v', hv', b', hb', e⟩ := hZ hq (mul_mem (inv_mem hyB3.1) hxc)
  have e2 : x = y * (v' * b') := by rw [← e]; group
  rw [e2]
  exact mul_mem hyB3 (mul_mem (d.S₃_le_B3 hv') (d.B2_le_B3 hb'))

theorem B4_le_normalizer_B3 : d.B4 ≤ normalizer (d.B3 : Set G) := by
  have key : ∀ {y : G}, y ∈ d.B4 → ∀ x ∈ d.B3, y * x * y⁻¹ ∈ d.B3 := by
    intro y hy x hx
    rw [d.B3_eq_B4_inf]
    refine mem_inf.2 ⟨mul_mem (mul_mem hy (d.B3_le_B4 hx)) (inv_mem hy), ?_⟩
    have hxc : x ∈ centralizer ((h.S₃ ⊔ d.B1 : Subgroup G) : Set G) := by
      have hle : h.S₃ ⊔ d.B1 ≤ centralizer ({x} : Set G) :=
        sup_le (fun v hv => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hx.1 v hv))
          fun b hb => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hx.2.1 b hb)
      exact mem_centralizer_iff.2 fun m hm => mem_centralizer_singleton_iff.1 (hle hm)
    have := (mem_normalizer_iff.1 (mem_normalizer_centralizer
      (d.B4_le_normalizer_S₃_sup_B1 hy)) x).1 hxc
    exact centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) this
  intro y hy
  refine mem_normalizer_of_conj_mem (key hy) fun x hx => ?_
  have := key (inv_mem hy) x hx
  rwa [inv_inv] at this

theorem B2_le_normalizer_S₃ : d.B2 ≤ normalizer (h.S₃ : Set G) := fun _ hb =>
  Subgroup.centralizer_le_normalizer _ (d.B2_le_B3 hb).1

theorem exists_mul_of_mem_S₃_sup_B2 {z : G} (hz : z ∈ h.S₃ ⊔ d.B2) :
    ∃ v ∈ h.S₃, ∃ b ∈ d.B2, z = v * b := by
  have hzQ : z ∈ ((h.S₃ ⊔ d.B2 : Subgroup G) : Set G) := hz
  rw [coe_mul_of_right_le_normalizer_left _ _ d.B2_le_normalizer_S₃, Set.mem_mul] at hzQ
  obtain ⟨v, hv, b, hb, rfl⟩ := hzQ
  exact ⟨v, hv, b, hb, rfl⟩

theorem comm_t_mem_S₂_of_mem_S₃_sup_B2 {z : G} (hz : z ∈ h.S₃ ⊔ d.B2) : ⁅z, h.t⁆ ∈ h.S₂ := by
  obtain ⟨v, hv, b, hb, rfl⟩ := d.exists_mul_of_mem_S₃_sup_B2 hz
  have hbt : ⁅b, h.t⁆ ∈ h.S₂ := by
    have h1 : ⁅b, h.t⁆ ∈ h.S₃ := (d.B2_le_B3 hb).2.2
    exact d.mem_S₂_of_mem_B2 (d.comm_t_mem_B2_of_mem_Q4 (d.B2_le_Q4 hb))
      (commutatorElement_eq_one_iff_mul_comm.2 (h.mul_t_comm (h.pull_le_L _ h1)))
  rw [commutatorElement_mul_left_eq, commutatorElement_eq_one_iff_mul_comm.2
    (h.mul_t_comm (h.pull_le_L _ hv)), mul_one, h.S₃_comm hv (h.S₂_le_S₃_le_S₄_le_S.1 hbt),
    mul_inv_cancel_right]
  exact hbt

theorem comm_B4_mem_Q4 {x y : G} (hx : x ∈ d.B4) (hy : y ∈ d.B4) : ⁅x, y⁆ ∈ d.Q4 := by
  have hhom := d.sec3_8_one.2.2.2.2.1
  have key : ∀ {x y : G}, x ∈ d.B4 → y ∈ d.B4 → x⁻¹ * y⁻¹ * x * y ∈ d.Q4 := by
    intro x y hx hy
    have e : x⁻¹ * y⁻¹ * x * y = (y * x)⁻¹ * (x * y) := by group
    rw [e]
    refine d.inv_mul_mem_Q4_of_comm (mul_mem hy hx) (mul_mem hx hy) ?_
    have h1 := hhom x hx y hy
    have h2 := hhom y hy x hx
    set a := ⁅x, h.t⁆
    set a' := ⁅y, h.t⁆
    have haQ : a ∈ d.Q4 := hx.2.2.2.2
    have haQ' : a' ∈ d.Q4 := hy.2.2.2.2
    set β := ⁅x * y, h.t⁆ * (a * a')⁻¹
    set β' := ⁅y * x, h.t⁆ * (a' * a)⁻¹
    have e1 : ⁅y * x, h.t⁆⁻¹ * ⁅x * y, h.t⁆ =
        (a' * a)⁻¹ * (β'⁻¹ * β) * (a' * a)⁻¹⁻¹ * ⁅a⁻¹, a'⁻¹⁆ := by
      simp only [β, β', commutatorElement_def]
      group
    rw [e1]
    exact mul_mem ((mem_normalizer_iff.1 (d.Q4_le_normalizer_B2 (inv_mem
      (mul_mem haQ' haQ))) _).1 (mul_mem (inv_mem h2) h1))
      (d.comm_Q4_Q4_mem (inv_mem haQ) (inv_mem haQ'))
  have := key (inv_mem hx) (inv_mem hy)
  rwa [inv_inv, inv_inv, ← commutatorElement_def] at this

theorem B3_inf_Q4_le : d.B3 ⊓ d.Q4 ≤ h.S₃ ⊔ d.B2 := by
  rintro c ⟨hc3, hcQ⟩
  have hct : ⁅c, h.t⁆ ∈ h.S₂ := d.mem_S₂_of_mem_B2 (d.comm_t_mem_B2_of_mem_Q4 hcQ)
    (commutatorElement_eq_one_iff_mul_comm.2 (h.mul_t_comm (h.pull_le_L _ hc3.2.2)))
  obtain ⟨b, hb, hbt⟩ := d.exists_B2_comm_t hct
  have hbB := d.B2_le_B3 hb
  have hs : b⁻¹ * c ∈ h.S₃ := d.mem_S₃_of_mem_B3 (mul_mem (inv_mem hbB) hc3) (by
    rw [d.comm_t_mul_B3 (inv_mem hbB) hc3, d.comm_t_inv_B3 hbB, hbt, inv_mul_cancel])
  have e : c = b * (b⁻¹ * c) := by group
  rw [e]
  exact mul_mem (mem_sup_right hb) (mem_sup_left hs)

theorem mem_V12_of_mem_W12_of_mem_S₃ {w : G} (hw : w ∈ d.W12) (hwS : w ∈ h.S₃) :
    w ∈ h.V .i12 :=
  d.mem_V12_of_commute hw (h.mul_t_comm (h.pull_le_L _ hwS))

theorem exists_W12_comm_t {v : G} (hv : v ∈ h.V .i12) : ∃ z ∈ d.W12, ⁅z, h.t⁆ = v := by
  obtain ⟨z, hz, e⟩ := d.exists_W12_conj hv
  exact ⟨z, hz, by rw [commutatorElement_def, e, ← h.mul_t_comm (h.V12_le_L hv),
    mul_inv_cancel_right]⟩

theorem mem_W12_of_equivariant {j : Idx} (hj0 : Idx.brace .i7 j ≠ 0)
    (hj9 : Idx.brace .i7 j ≠ Idx.brace .i7 .i9) (hj10 : Idx.brace .i7 j ≠ Idx.brace .i7 .i10)
    (hj11 : Idx.brace .i7 j ≠ Idx.brace .i7 .i11)
    {Ψ : h.K → G} (hΨ : ∀ c, Ψ c ∈ h.S₃ ⊔ d.B2)
    (hadd : ∀ c e, (Ψ c * Ψ e)⁻¹ * Ψ (c + e) ∈ d.W12)
    (hequiv : ∀ τ : h.Kˣ × h.Kˣ, torusPair h.a τ ∈ torusHi h.K h.a .i7 → ∀ c,
      (h.elt (torusPair h.a τ) * Ψ c * (h.elt (torusPair h.a τ))⁻¹)⁻¹ *
        Ψ ((rootChar h.K h.a j τ : h.K) * c) ∈ d.W12) (c : h.K) : Ψ c ∈ d.W12 := by
  classical
  have hB3 : ∀ c, Ψ c ∈ d.B3 := fun c => (sup_le d.S₃_le_B3 d.B2_le_B3) (hΨ c)
  have hκS : ∀ c, ⁅Ψ c, h.t⁆ ∈ h.S₂ := fun c => d.comm_t_mem_S₂_of_mem_S₃_sup_B2 (hΨ c)
  have hκR : ∀ c, ⁅Ψ c, h.t⁆ ∈ h.R₁ := fun c => h.S₂_le_R₁ (hκS c)
  have hbB3 : ∀ τ : h.Kˣ × h.Kˣ, ∀ {x : G}, x ∈ d.B3 →
      h.elt (torusPair h.a τ) * x * (h.elt (torusPair h.a τ))⁻¹ ∈ d.B3 := fun τ _ hx =>
    d.conj_Kp_mem_B3 (h.H_le_Kp (h.elt_torusPair_mem_H τ)) hx
  have hbt : ∀ τ : h.Kˣ × h.Kˣ, ∀ x : G,
      ⁅h.elt (torusPair h.a τ) * x * (h.elt (torusPair h.a τ))⁻¹, h.t⁆ =
        h.elt (torusPair h.a τ) * ⁅x, h.t⁆ * (h.elt (torusPair h.a τ))⁻¹ := fun τ x => by
    have hbt' : h.elt (torusPair h.a τ) * h.t * (h.elt (torusPair h.a τ))⁻¹ = h.t := by
      rw [h.mul_t_comm (h.H_le_L (h.elt_torusPair_mem_H τ)), mul_inv_cancel_right]
    simp only [commutatorElement_def]
    conv_lhs => rw [← hbt']
    group
  have hrow : ∀ k : Idx, k.isR1 = true → k ≠ .i12 → Idx.brace .i7 j ≠ Idx.brace .i7 k →
      ∀ c, h.r1c ⁅Ψ c, h.t⁆ k = 0 := by
    intro k hkR hk12 hb c
    refine miyamoto_2_1 (i := .i7) h.one_le_a h.card_K rfl hb
      (φ := fun c => h.r1c ⁅Ψ c, h.t⁆ k) (fun c e => ?_) (fun τ hτ c => ?_) c
    · have hρ := hadd c e
      have e1 : Ψ (c + e) = Ψ c * Ψ e * ((Ψ c * Ψ e)⁻¹ * Ψ (c + e)) := by group
      rw [e1, d.comm_t_mul_B3 (mul_mem (hB3 c) (hB3 e)) (d.W12_le_B3 hρ),
        d.comm_t_mul_B3 (hB3 c) (hB3 e),
        h.r1c_mul (mul_mem (hκR c) (hκR e)) (h.V12_le_R₁ (d.comm_t_W12_mem hρ)) hkR,
        h.r1c_mul (hκR c) (hκR e) hkR, h.r1c_eq_zero_of_mem_V12 (d.comm_t_W12_mem hρ) hkR hk12,
        add_zero]
    · have hρ := hequiv τ hτ c
      set b := h.elt (torusPair h.a τ)
      have e1 : Ψ ((rootChar h.K h.a j τ : h.K) * c) =
          b * Ψ c * b⁻¹ * ((b * Ψ c * b⁻¹)⁻¹ * Ψ ((rootChar h.K h.a j τ : h.K) * c)) := by group
      rw [e1, d.comm_t_mul_B3 (hbB3 τ (hB3 c)) (d.W12_le_B3 hρ), hbt,
        h.r1c_mul (by exact (mem_normalizer_iff.1 (h.J_le_normalizer_R₁ (h.H_le_J
          (h.elt_torusPair_mem_H τ))) _).1 (hκR c))
          (h.V12_le_R₁ (d.comm_t_W12_mem hρ)) hkR,
        h.r1c_eq_zero_of_mem_V12 (d.comm_t_W12_mem hρ) hkR hk12, add_zero,
        h.r1c_torus (hκR c) τ hkR]
  have hκ12 : ∀ c, ⁅Ψ c, h.t⁆ ∈ h.V .i12 := fun c => by
    have h0 : ∀ l : Idx, l.isR1 = true → l ∉ ({.i12} : Finset Idx) →
        h.r1c ⁅Ψ c, h.t⁆ l = 0 := by
      intro l hl hlS
      have hl' := Idx.eq_of_isR1_of_ne_twelve l hl (Finset.notMem_singleton.1 hlS)
      rcases hl' with rfl | rfl | rfl | rfl
      · exact h.r1c_eq_zero_of_mem_S₂ (hκS c) (Or.inl rfl)
      · exact h.r1c_eq_zero_of_mem_S₂ (hκS c) (Or.inr rfl)
      · exact hrow .i10 rfl (by decide) hj10 c
      · exact hrow .i11 rfl (by decide) hj11 c
    have := h.mem_of_r1c_eq_zero (hκR c) h0
    rwa [h.pull_rootJoin_singleton] at this
  have hz : ∀ c, ∃ z ∈ d.W12, ⁅z, h.t⁆ = ⁅Ψ c, h.t⁆ := fun c => d.exists_W12_comm_t (hκ12 c)
  choose z hzW hzt using hz
  set σ : h.K → G := fun c => (z c)⁻¹ * Ψ c with hσ
  have hσS : ∀ c, σ c ∈ h.S₃ := fun c => d.mem_S₃_of_mem_B3
    (mul_mem (inv_mem (d.W12_le_B3 (hzW c))) (hB3 c)) (by
      rw [d.comm_t_mul_B3 (inv_mem (d.W12_le_B3 (hzW c))) (hB3 c),
        d.comm_t_inv_B3 (d.W12_le_B3 (hzW c)), hzt, inv_mul_cancel])
  have hcomm : ∀ {x y : G}, x ∈ d.B3 → y ∈ d.B3 → x * y = y * x := fun hx hy => d.B3_comm hx hy
  have hσadd : ∀ c e, (σ c * σ e)⁻¹ * σ (c + e) ∈ h.V .i12 := by
    intro c e
    have hρ := hadd c e
    set ρ := (Ψ c * Ψ e)⁻¹ * Ψ (c + e)
    have hzc := d.W12_le_B3 (hzW c)
    have hze := d.W12_le_B3 (hzW e)
    have hzce := d.W12_le_B3 (hzW (c + e))
    have hw : z c * z e * (z (c + e))⁻¹ * ρ ∈ d.W12 :=
      mul_mem (mul_mem (mul_mem (hzW c) (hzW e)) (inv_mem (hzW (c + e)))) hρ
    have e1 : (σ c * σ e)⁻¹ * σ (c + e) = z c * z e * (z (c + e))⁻¹ * ρ := by
      simp only [hσ]
      have h1 : z e * (Ψ c)⁻¹ = (Ψ c)⁻¹ * z e := hcomm hze (inv_mem (hB3 c))
      have h2 : (z (c + e))⁻¹ * Ψ (c + e) = Ψ (c + e) * (z (c + e))⁻¹ :=
        hcomm (inv_mem hzce) (hB3 (c + e))
      have h3 : z c * z e * Ψ (c + e) = Ψ (c + e) * (z c * z e) :=
        hcomm (mul_mem hzc hze) (hB3 (c + e))
      have h4 : (Ψ e)⁻¹ * (Ψ c)⁻¹ * (z c * z e) = z c * z e * ((Ψ e)⁻¹ * (Ψ c)⁻¹) :=
        hcomm (mul_mem (inv_mem (hB3 e)) (inv_mem (hB3 c))) (mul_mem hzc hze)
      have h5 : (z (c + e))⁻¹ * ((Ψ e)⁻¹ * (Ψ c)⁻¹) = ((Ψ e)⁻¹ * (Ψ c)⁻¹) * (z (c + e))⁻¹ :=
        hcomm (inv_mem hzce) (mul_mem (inv_mem (hB3 e)) (inv_mem (hB3 c)))
      calc ((z c)⁻¹ * Ψ c * ((z e)⁻¹ * Ψ e))⁻¹ * ((z (c + e))⁻¹ * Ψ (c + e)) =
          (Ψ e)⁻¹ * (z e * (Ψ c)⁻¹) * z c * ((z (c + e))⁻¹ * Ψ (c + e)) := by group
        _ = (Ψ e)⁻¹ * ((Ψ c)⁻¹ * z e) * z c * (Ψ (c + e) * (z (c + e))⁻¹) := by rw [h1, h2]
        _ = (Ψ e)⁻¹ * (Ψ c)⁻¹ * (z e * z c) * Ψ (c + e) * (z (c + e))⁻¹ := by group
        _ = (Ψ e)⁻¹ * (Ψ c)⁻¹ * (z c * z e) * Ψ (c + e) * (z (c + e))⁻¹ := by
          rw [hcomm hze hzc]
        _ = z c * z e * ((Ψ e)⁻¹ * (Ψ c)⁻¹) * Ψ (c + e) * (z (c + e))⁻¹ := by rw [h4]
        _ = z c * z e * (((Ψ e)⁻¹ * (Ψ c)⁻¹) * (Ψ (c + e) * (z (c + e))⁻¹)) := by group
        _ = z c * z e * (((Ψ e)⁻¹ * (Ψ c)⁻¹) * ((z (c + e))⁻¹ * Ψ (c + e))) := by rw [h2]
        _ = z c * z e * ((z (c + e))⁻¹ * ((Ψ e)⁻¹ * (Ψ c)⁻¹) * Ψ (c + e)) := by
          rw [show ((Ψ e)⁻¹ * (Ψ c)⁻¹) * ((z (c + e))⁻¹ * Ψ (c + e)) =
            (((Ψ e)⁻¹ * (Ψ c)⁻¹) * (z (c + e))⁻¹) * Ψ (c + e) by group, ← h5]
        _ = z c * z e * (z (c + e))⁻¹ * ρ := by simp only [ρ]; group
    rw [e1]
    have hS : z c * z e * (z (c + e))⁻¹ * ρ ∈ h.S₃ := by
      rw [← e1]
      exact mul_mem (inv_mem (mul_mem (hσS c) (hσS e))) (hσS (c + e))
    exact d.mem_V12_of_mem_W12_of_mem_S₃ hw hS
  have hσequiv : ∀ τ : h.Kˣ × h.Kˣ, torusPair h.a τ ∈ torusHi h.K h.a .i7 → ∀ c,
      (h.elt (torusPair h.a τ) * σ c * (h.elt (torusPair h.a τ))⁻¹)⁻¹ *
        σ ((rootChar h.K h.a j τ : h.K) * c) ∈ h.V .i12 := by
    intro τ hτ c
    set b := h.elt (torusPair h.a τ) with hb
    set c' := (rootChar h.K h.a j τ : h.K) * c with hc'
    have hbH : b ∈ h.H := h.elt_torusPair_mem_H τ
    have hρ := hequiv τ hτ c
    set ρ := (b * Ψ c * b⁻¹)⁻¹ * Ψ c' with hρdef
    set X := b * Ψ c * b⁻¹ with hX
    have hXB : X ∈ d.B3 := hbB3 τ (hB3 c)
    have hz' : b * z c * b⁻¹ ∈ d.W12 := d.conj_H_mem_W12 hbH (hzW c)
    have hY : b * z c * b⁻¹ * (z c')⁻¹ ∈ d.W12 := mul_mem hz' (inv_mem (hzW c'))
    have hcY : X⁻¹ * (b * z c * b⁻¹ * (z c')⁻¹) = (b * z c * b⁻¹ * (z c')⁻¹) * X⁻¹ :=
      hcomm (inv_mem hXB) (d.W12_le_B3 hY)
    have e1 : (b * σ c * b⁻¹)⁻¹ * σ c' = b * z c * b⁻¹ * (z c')⁻¹ * ρ := by
      calc (b * σ c * b⁻¹)⁻¹ * σ c' = X⁻¹ * (b * z c * b⁻¹ * (z c')⁻¹) * (X * ρ) := by
            simp only [hσ, hX, hρdef]
            group
        _ = (b * z c * b⁻¹ * (z c')⁻¹) * X⁻¹ * (X * ρ) := by rw [hcY]
        _ = b * z c * b⁻¹ * (z c')⁻¹ * ρ := by group
    have hw : b * z c * b⁻¹ * (z c')⁻¹ * ρ ∈ d.W12 := mul_mem hY hρ
    have hS : b * z c * b⁻¹ * (z c')⁻¹ * ρ ∈ h.S₃ := by
      rw [← e1]
      exact mul_mem (inv_mem ((mem_normalizer_iff.1 (h.Kp_le_normalizer_S₂_S₃_S₄.2.1
        (h.H_le_Kp hbH)) _).1 (hσS c))) (hσS c')
    rw [e1]
    exact d.mem_V12_of_mem_W12_of_mem_S₃ hw hS
  have hσR : ∀ c, σ c ∈ h.R₁ := h.mem_R₁_of_equivariant_S₃' hj0 hσS
    (fun c e => h.V12_le_R₁ (hσadd c e)) fun τ hτ c => h.V12_le_R₁ (hσequiv τ hτ c)
  have hσrow : ∀ k : Idx, k.isR1 = true → k ≠ .i12 → Idx.brace .i7 j ≠ Idx.brace .i7 k →
      ∀ c, h.r1c (σ c) k = 0 := by
    intro k hkR hk12 hb c
    refine miyamoto_2_1 (i := .i7) h.one_le_a h.card_K rfl hb
      (φ := fun c => h.r1c (σ c) k) (fun c e => ?_) (fun τ hτ c => ?_) c
    · have e1 : σ (c + e) = σ c * σ e * ((σ c * σ e)⁻¹ * σ (c + e)) := by group
      rw [e1, h.r1c_mul (mul_mem (hσR c) (hσR e)) (h.V12_le_R₁ (hσadd c e)) hkR,
        h.r1c_mul (hσR c) (hσR e) hkR, h.r1c_eq_zero_of_mem_V12 (hσadd c e) hkR hk12, add_zero]
    · set b := h.elt (torusPair h.a τ)
      have e1 : σ ((rootChar h.K h.a j τ : h.K) * c) =
          b * σ c * b⁻¹ * ((b * σ c * b⁻¹)⁻¹ * σ ((rootChar h.K h.a j τ : h.K) * c)) := by
        group
      rw [e1, h.r1c_mul (by exact (mem_normalizer_iff.1 (h.J_le_normalizer_R₁ (h.H_le_J
          (h.elt_torusPair_mem_H τ))) _).1 (hσR c))
          (h.V12_le_R₁ (hσequiv τ hτ c)) hkR,
        h.r1c_eq_zero_of_mem_V12 (hσequiv τ hτ c) hkR hk12, add_zero,
        h.r1c_torus (hσR c) τ hkR]
  have hσ12 : σ c ∈ h.V .i12 := by
    have h0 : ∀ l : Idx, l.isR1 = true → l ∉ ({.i12} : Finset Idx) → h.r1c (σ c) l = 0 := by
      intro l hl hlS
      have hl' := Idx.eq_of_isR1_of_ne_twelve l hl (Finset.notMem_singleton.1 hlS)
      rcases hl' with rfl | rfl | rfl | rfl
      · exact h.r1c_eight_eq_zero_of_mem_S₃ (hσS c) (hσR c)
      · exact hσrow .i9 rfl (by decide) hj9 c
      · exact hσrow .i10 rfl (by decide) hj10 c
      · exact hσrow .i11 rfl (by decide) hj11 c
    have := h.mem_of_r1c_eq_zero (hσR c) h0
    rwa [h.pull_rootJoin_singleton] at this
  have e : Ψ c = z c * σ c := by simp only [hσ]; group
  rw [e]
  exact mul_mem (hzW c) (d.V12_le_W12 hσ12)

theorem comm_B3_B4_mem {x y : G} (hx : x ∈ d.B3) (hy : y ∈ d.B4) : ⁅x, y⁆ ∈ h.S₃ ⊔ d.B2 := by
  refine d.B3_inf_Q4_le (mem_inf.2 ⟨?_, d.comm_B4_mem_Q4 (d.B3_le_B4 hx) hy⟩)
  rw [commutatorElement_def, mul_assoc, mul_assoc]
  refine mul_mem hx ?_
  rw [← mul_assoc]
  exact (mem_normalizer_iff.1 (d.B4_le_normalizer_B3 hy) _).1 (inv_mem hx)

theorem comm_W7_V8_mem_W12 {x v : G} (hx : x ∈ d.W7) (hv : v ∈ h.V .i8) : ⁅x, v⁆ ∈ d.W12 := by
  have hxB4 : x ∈ d.B4 := d.B3_le_B4 (d.W7_le_B3 hx)
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  have h8S : ∀ c, h.elt (rootElt h.K h.a .i8 c) ∈ h.S₄ := fun c =>
    h.V_le_S₄ (k := .i8) (by decide) (h.elt_rootElt_mem_V _ c)
  have hW : ∀ c, ⁅x, h.elt (rootElt h.K h.a .i8 c)⁆ ∈ d.W12 := by
    refine d.mem_W12_of_equivariant (j := .i8) (by decide) (by decide) (by decide) (by decide)
      (fun c => mem_sup_right (hxB4.2.2.1 _ (h8S c))) (fun c e => ?_) (fun τ hτ c => ?_)
    · rw [rootElt_add h.card_K (i := .i8) rfl, h.elt_mul' (hΓ _ _) (hΓ _ _),
        commutatorElement_mul_right_eq, mem_centralizer_iff.1 (d.B2_le_centralizer_S₄
          (hxB4.2.2.1 _ (h8S e))) _ (h8S c), mul_inv_cancel_right, inv_mul_cancel]
      exact one_mem _
    · have hb : h.elt (torusPair h.a τ) ∈ h.Ht .i7 := (h.elt_torusPair_mem_Ht_iff τ).2 hτ
      have hbx : h.elt (torusPair h.a τ) * x * (h.elt (torusPair h.a τ))⁻¹ = x := by
        rw [mem_centralizer_iff.1 (d.W7_le_CH7 hx) _ hb, mul_inv_cancel_right]
      have e3 : ⁅x, h.elt (torusPair h.a τ) * h.elt (rootElt h.K h.a .i8 c) *
          (h.elt (torusPair h.a τ))⁻¹⁆ = h.elt (torusPair h.a τ) *
            ⁅x, h.elt (rootElt h.K h.a .i8 c)⁆ * (h.elt (torusPair h.a τ))⁻¹ := by
        conv_lhs => rw [← hbx]
        simp only [commutatorElement_def]
        group
      rw [← h.elt_torusPair_conj_rootElt τ .i8 c, e3, inv_mul_cancel]
      exact one_mem _
  have hle : h.V .i8 ≤ commRightIn x d.W12 := h.V_le_of_forall_elt_mem fun c =>
    mem_commRightIn.2 ⟨Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun z hz =>
      (mem_centralizer_iff.1 (d.W12_le_centralizer_S hz) _
        (h.S₂_le_S₃_le_S₄_le_S.2.2.1 (h8S c))).symm), hW c⟩
  exact (mem_commRightIn.1 (hle hv)).2

theorem comm_W7_WA4_mem_W12 {x y : G} (hx : x ∈ d.W7) (hy : y ∈ d.WA .i4) :
    ⁅x, y⁆ ∈ d.W12 := by
  classical
  have hxB3 : x ∈ d.B3 := d.W7_le_B3 hx
  have hS : ∀ {y : G}, y ∈ d.WA .i4 → ⁅x, y⁆ ∈ h.S₃ ⊔ d.B2 := fun hy =>
    d.comm_B3_B4_mem hxB3 (d.A1_le_B4 hy.1)
  have hSB3 : ∀ {z : G}, z ∈ h.S₃ ⊔ d.B2 → z ∈ d.B3 := fun hz =>
    (sup_le d.S₃_le_B3 d.B2_le_B3) hz
  have hAW : ∀ {a w : G}, a ∈ d.A1 → w ∈ d.W12 → a * w * a⁻¹ = w := fun ha hw => by
    rw [← mem_centralizer_iff.1 ha.2.1 _ hw, mul_inv_cancel_right]
  have hprod : ∀ {y y' : G}, y ∈ d.WA .i4 → y' ∈ d.WA .i4 →
      (⁅x, y⁆ * ⁅x, y'⁆)⁻¹ * ⁅x, y * y'⁆ ∈ d.W12 := by
    intro y y' hy hy'
    have hw := d.comm_A1_S₃_sup_B2_mem hy.1 (hS hy')
    have e : (⁅x, y⁆ * ⁅x, y'⁆)⁻¹ * ⁅x, y * y'⁆ = ⁅x, y'⁆⁻¹ * ⁅y, ⁅x, y'⁆⁆ * ⁅x, y'⁆ := by
      rw [commutatorElement_mul_right_eq]
      simp only [commutatorElement_def]
      group
    rw [e, ← mul_inv_cancel_right (⁅y, ⁅x, y'⁆⁆) ⁅x, y'⁆,
      d.B3_comm (d.W12_le_B3 hw) (hSB3 (hS hy'))]
    rw [show ⁅x, y'⁆⁻¹ * (⁅x, y'⁆ * ⁅y, ⁅x, y'⁆⁆ * ⁅x, y'⁆⁻¹) * ⁅x, y'⁆ = ⁅y, ⁅x, y'⁆⁆ by group]
    exact hw
  have hV8 : ∀ {y : G} {v : G}, y ∈ d.WA .i4 → v ∈ h.V .i8 → ⁅x, y⁆⁻¹ * ⁅x, y * v⁆ ∈ d.W12 := by
    intro y v hy hv
    rw [commutatorElement_mul_right_eq, ← mul_assoc, inv_mul_cancel, one_mul,
      hAW hy.1 (d.comm_W7_V8_mem_W12 hx hv)]
    exact d.comm_W7_V8_mem_W12 hx hv
  have hcos : ∀ {y y' : G}, y ∈ d.WA .i4 → y' ∈ d.WA .i4 → ⁅y, h.t⁆ = ⁅y', h.t⁆ →
      y⁻¹ * y' ∈ h.V .i8 := fun hy hy' e =>
    d.mem_V_of_mem_WA (i := .i4) rfl (by decide) (mul_mem (inv_mem hy) hy') (by
      rw [d.comm_t_mul_A1 (inv_mem hy.1) hy'.1, d.comm_t_inv_A1 hy.1, e, inv_mul_cancel])
  have hlift : ∀ c : h.K, ∃ w ∈ d.WA .i4, ⁅w, h.t⁆ = h.elt (rootElt h.K h.a .i8 c) := fun c =>
    d.exists_WA_comm_t (i := .i4) (h.V_le_R₁ (by decide)) (h.V_le_CH rfl (Or.inr rfl))
      (h.elt_rootElt_mem_V .i8 c)
  choose Y hY hYt using hlift
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  have hW : ∀ c, ⁅x, Y c⁆ ∈ d.W12 := by
    refine d.mem_W12_of_equivariant (j := .i8) (by decide) (by decide) (by decide) (by decide)
      (fun c => hS (hY c)) (fun c e => ?_) (fun τ hτ c => ?_)
    · have hYY : Y c * Y e ∈ d.WA .i4 := mul_mem (hY c) (hY e)
      have hv := hcos hYY (hY (c + e)) (by
        rw [d.comm_t_mul_A1 (hY c).1 (hY e).1, hYt, hYt, hYt, rootElt_add h.card_K (i := .i8) rfl,
          h.elt_mul' (hΓ _ _) (hΓ _ _)])
      have e1 : Y (c + e) = Y c * Y e * ((Y c * Y e)⁻¹ * Y (c + e)) := by group
      have h1 := hprod (hY c) (hY e)
      have h2 := hV8 hYY hv
      rw [← e1] at h2
      have e2 : (⁅x, Y c⁆ * ⁅x, Y e⁆)⁻¹ * ⁅x, Y (c + e)⁆ =
          ((⁅x, Y c⁆ * ⁅x, Y e⁆)⁻¹ * ⁅x, Y c * Y e⁆) * (⁅x, Y c * Y e⁆⁻¹ * ⁅x, Y (c + e)⁆) := by
        group
      rw [e2]
      exact mul_mem h1 h2
    · set b := h.elt (torusPair h.a τ) with hbdef
      have hbH : b ∈ h.H := h.elt_torusPair_mem_H τ
      have hb : b ∈ h.Ht .i7 := (h.elt_torusPair_mem_Ht_iff τ).2 hτ
      have hbx : b * x * b⁻¹ = x := by
        rw [mem_centralizer_iff.1 (d.W7_le_CH7 hx) _ hb, mul_inv_cancel_right]
      have hbY : b * Y c * b⁻¹ ∈ d.WA .i4 := d.conj_H_mem_WA hbH (hY c)
      have hbt : b * h.t * b⁻¹ = h.t := by
        rw [h.mul_t_comm (h.H_le_L hbH), mul_inv_cancel_right]
      have hv := hcos hbY (hY ((rootChar h.K h.a .i8 τ : h.K) * c)) (by
        rw [hYt, ← h.elt_torusPair_conj_rootElt τ .i8 c, ← hYt c, ← hbdef]
        simp only [commutatorElement_def]
        conv_lhs => rw [← hbt]
        group)
      have h2 := hV8 hbY hv
      rw [show b * Y c * b⁻¹ * ((b * Y c * b⁻¹)⁻¹ * Y ((rootChar h.K h.a .i8 τ : h.K) * c)) =
        Y ((rootChar h.K h.a .i8 τ : h.K) * c) by group] at h2
      have e3 : ⁅x, b * Y c * b⁻¹⁆ = b * ⁅x, Y c⁆ * b⁻¹ := by
        conv_lhs => rw [← hbx]
        simp only [commutatorElement_def]
        group
      rw [e3] at h2
      exact h2
  obtain ⟨c, hc⟩ := h.exists_eq_elt_rootElt (i := .i8) rfl
    (d.comm_t_mem_V_of_mem_WA (i := .i4) rfl (by decide) hy)
  have hv := hcos (hY c) hy (by rw [hYt, hc])
  have h2 := hV8 (hY c) hv
  rw [show Y c * ((Y c)⁻¹ * y) = y by group] at h2
  have e : ⁅x, y⁆ = ⁅x, Y c⁆ * (⁅x, Y c⁆⁻¹ * ⁅x, y⁆) := by group
  rw [e]
  exact mul_mem (hW c) h2

theorem comm_A1_B3_mem_B1 {a y : G} (ha : a ∈ d.A1) (hy : y ∈ d.B3) : ⁅a, y⁆ ∈ d.B1 := by
  have hN : ∀ {z : G}, z ∈ d.B3 → z ∈ normalizer (d.B1 : Set G) := fun hz =>
    Subgroup.centralizer_le_normalizer _ hz.2.1
  have one : ∀ {x y : G}, x * y = y * x → ⁅x, y⁆ ∈ d.B1 := fun hxy => by
    rw [commutatorElement_eq_one_iff_mul_comm.2 hxy]
    exact one_mem _
  have h7 : ∀ w ∈ d.W7, ⁅a, w⁆ ∈ d.B1 := by
    intro w hw
    have hwB := d.W7_le_B3 hw
    have hle : d.A1 ≤ commLeftIn w d.B1 := by
      refine d.A1_le_sup.trans (sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_)
      · refine fun x hx => mem_commLeftIn.2 ⟨Subgroup.centralizer_le_normalizer _
          ((d.B4_le_centralizer_B1 (d.A1_le_B4 hx.1))), ?_⟩
        rw [← commutatorElement_inv]
        exact inv_mem (d.W12_le_B1 (d.comm_W7_WA4_mem_W12 hw hx))
      · refine fun x hx => mem_commLeftIn.2 ⟨Subgroup.centralizer_le_normalizer _
          ((d.B4_le_centralizer_B1 (d.A1_le_B4 hx.1))), one ?_⟩
        exact (mem_centralizer_iff.1 hwB.2.1 x (d.W11_le_B1 (d.WA_six_eq ▸ hx)))
      · refine fun x hx => mem_commLeftIn.2 ⟨Subgroup.centralizer_le_normalizer _
          ((d.B4_le_centralizer_B1 (d.A1_le_B4 hx.1))), one ?_⟩
        exact (mem_centralizer_iff.1 hwB.2.1 x (d.W12_le_B1 (d.WA_five_eq ▸ hx)))
      · exact fun x hx => mem_commLeftIn.2 ⟨Subgroup.centralizer_le_normalizer _
          ((d.B4_le_centralizer_B1 (d.A1_le_B4 hx.1))),
          one (d.B3_comm (d.WA_le_B3 (Or.inl rfl) hx) hwB)⟩
      · exact fun x hx => mem_commLeftIn.2 ⟨Subgroup.centralizer_le_normalizer _
          ((d.B4_le_centralizer_B1 (d.A1_le_B4 hx.1))), one (d.W7_comm_WA10 hw hx).symm⟩
    exact (mem_commLeftIn.1 (hle ha)).2
  have hle : d.B3 ≤ commRightIn a d.B1 := by
    rw [d.B3_eq]
    refine sup_le (sup_le (fun w hw => mem_commRightIn.2 ⟨hN (d.W7_le_B3 hw), h7 w hw⟩)
      fun w hw => mem_commRightIn.2 ⟨hN (d.WA_le_B3 (Or.inl rfl) hw),
        one (d.A1_comm ha hw.1)⟩) fun w hw => mem_commRightIn.2 ⟨hN (d.B2_le_B3 hw),
          one (d.A1_comm ha (d.B2_le_A1 hw))⟩
  exact (mem_commRightIn.1 (hle hy)).2

theorem comm_B4_B3_mem_B1 {x y : G} (hx : x ∈ d.B4) (hy : y ∈ d.B3) : ⁅x, y⁆ ∈ d.B1 := by
  let Z : Subgroup G :=
    { carrier := {x | x ∈ d.B4 ∧ ∀ y ∈ d.B3, ⁅x, y⁆ ∈ d.B1}
      mul_mem' := fun {x x'} hx hx' => ⟨mul_mem hx.1 hx'.1, fun y hy => by
        rw [commutatorElement_mul_left_eq, ← mem_centralizer_iff.1 (d.B4_le_centralizer_B1 hx.1)
          _ (hx'.2 y hy), mul_inv_cancel_right]
        exact mul_mem (hx'.2 y hy) (hx.2 y hy)⟩
      one_mem' := ⟨one_mem _, fun y _ => by rw [commutatorElement_one_left]; exact one_mem _⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, fun y hy => by
        have e : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e, ← mem_centralizer_iff.1 (inv_mem (d.B4_le_centralizer_B1 hx.1)) _
          (inv_mem (hx.2 y hy)), mul_inv_cancel_right]
        exact inv_mem (hx.2 y hy)⟩ }
  have hZK : h.Kp ≤ normalizer (Z : Set G) := by
    have key : ∀ {k : G}, k ∈ h.Kp → ∀ x ∈ Z, k * x * k⁻¹ ∈ Z := by
      intro k hk x hx
      refine ⟨d.conj_Kp_mem_B4 hk hx.1, fun y hy => ?_⟩
      have hy' : k⁻¹ * y * k⁻¹⁻¹ ∈ d.B3 := d.conj_Kp_mem_B3 (inv_mem hk) hy
      have e : ⁅k * x * k⁻¹, y⁆ = k * ⁅x, k⁻¹ * y * k⁻¹⁻¹⁆ * k⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (mem_normalizer_iff.1 (d.Kp_le_normalizer_B1 hk) _).1 (hx.2 _ hy')
    intro k hk
    refine mem_normalizer_of_conj_mem (key hk) fun x hx => ?_
    have := key (inv_mem hk) x hx
    rwa [inv_inv] at this
  have hZ := d.eq_B4_of_A1_le (Z := Z) (fun x hx => hx.1)
    (fun a ha => ⟨d.A1_le_B4 ha, fun y hy => d.comm_A1_B3_mem_B1 ha hy⟩) hZK
  have hxZ : x ∈ Z := hZ.ge hx
  exact hxZ.2 y hy

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4

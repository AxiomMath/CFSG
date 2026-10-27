module

public import CFSG.CGT.PushingUpLit.A78L3.Semi
public import CFSG.CGT.PushingUpLit.CGT6.EmbEightFive

public section

namespace CFSG.CGT.PushingUpLit.A78L3

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.ABGLocalTools
open Matrix

section Helpers

variable {G : Type} [Group G]

theorem le_normalizer_of_conj {M K : Subgroup G} (h : ∀ g ∈ M, ∀ k ∈ K, g * k * g⁻¹ ∈ K) :
    M ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨fun hk => h g hg k hk, fun hk => ?_⟩
  have := h g⁻¹ (inv_mem hg) _ hk
  simpa [mul_assoc] using this

theorem exists_pow_mul_eq {L T : Subgroup G} (hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L)
    {l t : G} (hl : l ∈ L) (ht : t ∈ T) (n : ℕ) : ∃ l' ∈ L, (l * t) ^ n = l' * t ^ n := by
  induction n with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨l', hl', hpow⟩ := ih
    refine ⟨l' * (t ^ n * l * (t ^ n)⁻¹), mul_mem hl' ?_, ?_⟩
    · have hT : ∀ m : ℕ, ∀ x ∈ L, t ^ m * x * (t ^ m)⁻¹ ∈ L := by
        intro m
        induction m with
        | zero => intro x hx; simpa using hx
        | succ m ihm =>
          intro x hx
          have := ihm _ (hTL t ht x hx)
          rw [pow_succ]
          simpa [mul_assoc] using this
      exact hT n l hl
    · rw [pow_succ, hpow, pow_succ]
      group

end Helpers

section CStar

variable {G : Type} [Group G] [Finite G] {L T J : Subgroup G} {e : ℕ}

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Side.inf_centralizer_le_V (h : A78Side G L T J e) :
    T ⊓ Subgroup.centralizer (oTwoIn (L ⊔ T) : Set G) ≤ oTwoIn (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := oTwoIn (L ⊔ T) with hV
  set K := (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) with hK
  have hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L := fun t ht l hl =>
    conj_mem_of_mem_normalizer (h.sylow.le ht) hl
  obtain ⟨n, hn⟩ := h.sylow.isPGroup.exists_card_eq
  have hK2 : IsPGroup 2 K := by
    rintro ⟨k, hk⟩
    obtain ⟨hkLT, hkC⟩ := Subgroup.mem_inf.1 hk
    obtain ⟨l, hl, t, ht, rfl⟩ := (mem_sup_iff_of_normalizes hTL).1 hkLT
    obtain ⟨l', hl', hpow⟩ := exists_pow_mul_eq hTL hl ht (2 ^ n)
    have ht1 : t ^ 2 ^ n = 1 := by
      have := pow_card_eq_one' (G := T) (x := ⟨t, ht⟩)
      rw [hn] at this
      exact congrArg Subtype.val this
    rw [ht1, mul_one] at hpow
    have hpC : (l * t) ^ 2 ^ n ∈ Subgroup.centralizer (V : Set G) := pow_mem hkC _
    rw [hpow] at hpC
    have hl'V : l' ∈ V := by
      have : l' ∈ L ⊓ Subgroup.centralizer (V : Set G) := ⟨hl', hpC⟩
      rw [← h.inf_V_eq_centralizer] at this
      exact this.2
    refine ⟨n + 1, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_succ, pow_mul, hpow, pow_two]
    exact (elemAb2_of_isElemAbelian h.elem l' hl'V l' hl'V).2
  have hKn : L ⊔ T ≤ Subgroup.normalizer (K : Set G) := by
    refine le_normalizer_of_conj fun g hg k hk => Subgroup.mem_inf.2
      ⟨mul_mem (mul_mem hg (Subgroup.mem_inf.1 hk).1) (inv_mem hg), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : g⁻¹ * v * g⁻¹⁻¹ ∈ V :=
      conj_mem_of_mem_normalizer (h.sup_le_normalizer_V (inv_mem hg)) hv
    have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hk).2 _ hv'
    rw [inv_inv] at h1 hv'
    calc v * (g * k * g⁻¹) = g * ((g⁻¹ * v * g) * k) * g⁻¹ := by group
      _ = g * (k * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
      _ = g * k * g⁻¹ * v := by group
  have hKle : K ≤ V := CGT6.le_oTwoIn_of_normal inf_le_left hKn hK2
  rintro x ⟨hxT, hxC⟩
  exact hKle ⟨Subgroup.mem_sup_right hxT, hxC⟩

end CStar

structure L3Side (G : Type) [Group G] [Finite G] (L V W T : Subgroup G) (e : ℕ) : Prop where
  jst : JStructure G (V ⊔ W) V W e
  nat : Nonempty (NatCoord G L V (GaloisField 2 e))
  V_le_L : V ≤ L
  sylowJ : IsSylowOf 2 (V ⊔ W) L
  J_le_T : V ⊔ W ≤ T
  pT : IsPGroup 2 T
  T_le_L : T ≤ Subgroup.normalizer (L : Set G)
  T_le_V : T ≤ Subgroup.normalizer (V : Set G)
  T_le_W : T ≤ Subgroup.normalizer (W : Set G)
  cent : T ⊓ Subgroup.centralizer (V : Set G) ≤ V

section Sides

variable {G : Type} [Group G] [Finite G] {L₁ L₂ T : Subgroup G} {e : ℕ}

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.l3Side₁ (h : A78Cfg G L₁ L₂ T e)
    (hZ : oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G) = ⊥) :
    L3Side G L₁ (oTwoIn (L₁ ⊔ T)) (oTwoIn (L₂ ⊔ T)) T e := by
  obtain ⟨D⟩ := h.side₁.nonempty_natCoord hZ
  have hVL : oTwoIn (L₁ ⊔ T) ≤ L₁ := D.le fun v hv l hl =>
    conj_mem_of_mem_normalizer (h.side₁.sylow.le (h.hyg.V₁_le hv)) hl
  exact
    { jst := h.jStructure
      nat := ⟨D⟩
      V_le_L := hVL
      sylowJ := by
        have := h.side₁.sylowJ
        rwa [sup_eq_left.2 hVL] at this
      J_le_T := h.hyg.J_le
      pT := h.side₁.sylow.isPGroup
      T_le_L := h.side₁.sylow.le
      T_le_V := le_sup_right.trans h.hyg.sup₁
      T_le_W := le_sup_right.trans h.hyg.sup₂
      cent := h.side₁.inf_centralizer_le_V }

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.l3Side₂ (h : A78Cfg G L₁ L₂ T e)
    (hZ : oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G) = ⊥) :
    L3Side G L₂ (oTwoIn (L₂ ⊔ T)) (oTwoIn (L₁ ⊔ T)) T e :=
  h.symm.l3Side₁ (h.inf_centralizer_V₂_eq_bot hZ)

end Sides

namespace L3Side

variable {G : Type} [Group G] [Finite G] {L V W T : Subgroup G} {e : ℕ}

theorem two_le (h : L3Side G L V W T e) : 2 ≤ e := h.jst.two_le

theorem J_le_L (h : L3Side G L V W T e) : V ⊔ W ≤ L := h.sylowJ.le

theorem W_le_L (h : L3Side G L V W T e) : W ≤ L := le_sup_right.trans h.J_le_L

theorem V_le_T (h : L3Side G L V W T e) : V ≤ T := le_sup_left.trans h.J_le_T

theorem W_le_T (h : L3Side G L V W T e) : W ≤ T := le_sup_right.trans h.J_le_T

theorem card_V (h : L3Side G L V W T e) : Nat.card V = 2 ^ (2 * e) := by
  obtain ⟨D⟩ := h.nat
  rw [D.card_V, GaloisField.card 2 e (by have := h.two_le; omega)]
  ring

theorem card_Z (h : L3Side G L V W T e) : Nat.card ↥(V ⊓ W) = 2 ^ e := by
  have h1 := h.jst.card_V_eq
  rw [h.card_V] at h1
  have hpos : 0 < 2 ^ e := by positivity
  have : 2 ^ e * 2 ^ e = 2 ^ e * Nat.card ↥(V ⊓ W) := by
    rw [← h1, ← pow_add]; ring_nf
  exact (Nat.eq_of_mul_eq_mul_left hpos this).symm

theorem exists_Z_ne_one (h : L3Side G L V W T e) : ∃ z ∈ V ⊓ W, z ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : V ⊓ W = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
  have := h.card_Z
  rw [hbot, Subgroup.card_bot] at this
  have h2 : 2 ≤ 2 ^ e := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by have := h.two_le; omega)
  omega

theorem exists_W_not_V (h : L3Side G L V W T e) : ∃ w ∈ W, w ∉ V := by
  by_contra hcon
  push Not at hcon
  exact h.jst.not_le_V hcon

theorem cent_L (h : L3Side G L V W T e) {z : G} (hz : z ∈ V ⊓ W) (hz1 : z ≠ 1) :
    L ⊓ Subgroup.centralizer ({z} : Set G) = V ⊔ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D⟩ := h.nat
  have hle : V ⊔ W ≤ L ⊓ Subgroup.centralizer ({z} : Set G) := by
    intro j hj
    refine ⟨h.J_le_L hj, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact ((h.jst.commute_of_mem_inf hz hj).eq).symm
  exact h.sylowJ.eq_of_le hle inf_le_left
    (D.isPGroup_inf_centralizer (fun x hx => h.jst.sq_V x hx) hz.1 hz1)

theorem mem_Z_of_comm (h : L3Side G L V W T e) {v : G} (hv : v ∈ V)
    (hc : ∀ w ∈ W, w * v = v * w) : v ∈ V ⊓ W := by
  obtain ⟨w, hw, hwV⟩ := h.exists_W_not_V
  have : v ∈ V ⊓ Subgroup.centralizer ({w} : Set G) :=
    ⟨hv, Subgroup.mem_centralizer_singleton_iff.2 (hc w hw).symm⟩
  rwa [h.jst.inf_centralizer_eq hw hwV] at this

theorem mem_Z_iff (h : L3Side G L V W T e) (D : NatCoord G L V (GaloisField 2 e)) {z₀ : G}
    (hz₀ : z₀ ∈ V ⊓ W) (hz₀1 : z₀ ≠ 1) {v : G} (hv : v ∈ V) :
    v ∈ V ⊓ W ↔ ∃ c : GaloisField 2 e, D.κ v = c • D.κ z₀ := by
  have hline : ∀ (u : G), u ∈ V → ∀ c : GaloisField 2 e, D.κ u = c • D.κ z₀ → u ∈ V ⊓ W := by
    intro u hu c hc
    refine h.mem_Z_of_comm hu fun w hw => ?_
    have hwL : w ∈ L := h.W_le_L hw
    have hwz : w * z₀ * w⁻¹ = z₀ := by
      rw [(h.jst.abelian_V₂ w hw z₀ hz₀.2).eq]
      group
    have h1 : D.κ (w * u * w⁻¹) = D.κ u := by
      rw [D.conj w hwL u hu, hc, mulVec_smul, ← D.conj w hwL z₀ hz₀.1, hwz]
    have h2 := D.κ_inj _ (D.norm w hwL u hu) u hu h1
    calc w * u = w * u * w⁻¹ * w := by group
      _ = u * w := by rw [h2]
  constructor
  · intro hvZ
    have hx₀ : D.κ z₀ ≠ 0 := D.κ_ne_zero hz₀.1 hz₀1
    let f : GaloisField 2 e → ↥(V ⊓ W) := fun c =>
      ⟨D.sec (c • D.κ z₀), hline _ (D.sec_mem _) c (D.κ_sec _)⟩
    have hf : Function.Injective f := by
      intro c c' hcc
      have h1 := congrArg (fun x : ↥(V ⊓ W) => D.κ (x : G)) hcc
      simp only [f, D.κ_sec] at h1
      exact smul_left_injective _ hx₀ h1
    have hcard : Nat.card ↥(V ⊓ W) ≤ Nat.card (GaloisField 2 e) := by
      rw [h.card_Z, GaloisField.card 2 e (by have := h.two_le; omega)]
    have hbij := hf.bijective_of_nat_card_le hcard
    obtain ⟨c, hc⟩ := hbij.2 ⟨v, hvZ⟩
    refine ⟨c, ?_⟩
    have h1 := congrArg (fun x : ↥(V ⊓ W) => D.κ (x : G)) hc
    simp only [f, D.κ_sec] at h1
    exact h1.symm
  · rintro ⟨c, hc⟩
    exact hline v hv c hc

end L3Side

end CFSG.CGT.PushingUpLit.A78L3

module

public import CFSG.CGT.PushingUpLit.A78G0.Cliques
public import CFSG.CGT.PushingUpLit.A78G0.Linear
public import CFSG.CGT.PushingUpLit.A78S4.SideRec

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.Timmesfeld.ARS CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
  CFSG.CGT.PushingUpLit.A78S4 CFSG.ABGLocalTools Matrix
open scoped commutatorElement

section Generic

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj_le' [Finite G] {K : Subgroup G} {g : G}
    (h : ∀ k ∈ K, g * k * g⁻¹ ∈ K) : g ∈ Subgroup.normalizer (K : Set G) := by
  apply mem_normalizer_of_cs_eq
  apply Subgroup.eq_of_le_of_card_ge
  · rintro x ⟨k, hk, rfl⟩
    simpa [MulAut.conj_apply] using h k hk
  · rw [card_cs]

theorem comm_conj_eq_of_central {a c v l : G}
    (hcl : c * (l * v⁻¹ * l⁻¹) = (l * v⁻¹ * l⁻¹) * c)
    (ha : a * (v * c * l * v⁻¹) = (v * c * l * v⁻¹) * a) :
    a * v * (c * l) * (a * v)⁻¹ * (c * l)⁻¹ = v * l * v⁻¹ * l⁻¹ := by
  have h1 : a * v * (c * l) * (a * v)⁻¹ * (c * l)⁻¹ =
      a * (v * c * l * v⁻¹) * a⁻¹ * (l⁻¹ * c⁻¹) := by group
  have h2 : a * (v * c * l * v⁻¹) * a⁻¹ = v * c * l * v⁻¹ := by
    rw [ha]; group
  rw [h1, h2]
  have h3 : v * c * l * v⁻¹ * (l⁻¹ * c⁻¹) = v * (c * (l * v⁻¹ * l⁻¹)) * c⁻¹ := by group
  rw [h3, hcl]
  group

end Generic

structure Torus₀ {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}
    (_h : G0Core G L₁ L₂ V W Z Z₂ e) (y : G) : Prop where
  mem_V : y ∈ Subgroup.normalizer (V : Set G)
  comm_L : ∀ l ∈ L₁, y * l * y⁻¹ * l⁻¹ ∈ V
  cent_V : ∀ v ∈ V, y * v * y⁻¹ = v → v = 1

structure IsTorus {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}
    (_h : G0Core G L₁ L₂ V W Z Z₂ e) (y : G) : Prop extends Torus₀ _h y where
  mem_W : y ∈ Subgroup.normalizer (W : Set G)
  coord : ∃ (D : NatCoordK G L₁ V Z (GaloisField 2 e)) (lam : GaloisField 2 e),
    lam ≠ 0 ∧ lam ≠ 1 ∧ ∀ w, D.act y w = lam • w

namespace G0Core

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}
  (h : G0Core G L₁ L₂ V W Z Z₂ e)

include h

theorem ex_ne_one_Z₂ : ∃ z ∈ Z₂, z ≠ 1 := by
  by_contra hcon
  push Not at hcon
  exact h.Z₂_ne_bot ((Subgroup.eq_bot_iff_forall _).2 hcon)

theorem not_mem_Z_of_mem_Z₂ {z : G} (hz : z ∈ Z₂) (hz1 : z ≠ 1) : z ∉ Z := by
  intro hZ
  have h1 : z ∈ Z ⊓ Z₂ := ⟨hZ, hz⟩
  rw [h.inf_Z] at h1
  exact hz1 (Subgroup.mem_bot.1 h1)

theorem exists_Z₂_κ_eq (D : NatCoordK G L₁ V Z (GaloisField 2 e)) (c : GaloisField 2 e) {z₂ : G}
    (hz₂ : z₂ ∈ Z₂) : ∃ z ∈ Z₂, D.κ z = c • D.κ z₂ := by
  obtain ⟨fr⟩ := h.pair.side₁.exists_frame D
  obtain ⟨n, hn, hnc⟩ := fr.c_surj (c * fr.c z₂)
  obtain ⟨z, hz, z', hz', hzz'⟩ := h.pair.exists_decomp h.hZ hn
  have hc : fr.c n = fr.c z' := by
    rw [← hzz', fr.c_mul (h.Z_le_V hz) (h.Z₂_le_V hz'), fr.c_of_mem_Z hz, zero_add]
  refine ⟨z', hz', ?_⟩
  rw [fr.κ_eq_c (h.Z₂_le_N hz'), fr.κ_eq_c (h.Z₂_le_N hz₂), ← hc, hnc, mul_smul]

theorem exists_x₂ : ∃ x : G, x ∈ L₂ ∧ (∀ v ∈ V, x * v * x⁻¹ ∈ V) ∧
    (∀ z ∈ Z₂, x * z * x⁻¹ = z) ∧ (∀ z ∈ Z, x * z * x⁻¹ = z → z = 1) := by
  obtain ⟨t, ht0, ht1⟩ := h.pair.exists_ne_zero_one
  obtain ⟨D₂⟩ := h.pair.side₂.nat
  obtain ⟨fr₂⟩ := h.pair.side₂.exists_frame D₂
  obtain ⟨x, hxL, -, hxV, -, hxN⟩ := fr₂.torus ht0
  refine ⟨x, hxL, hxV, fun z hz => ?_, fun z hz hfix => ?_⟩
  · have hc := Subgroup.mem_centralizer_iff.1 (h.pair.side₂.Z_cent hz) x hxL
    rw [hc, mul_inv_cancel_right]
  · have hzN : z ∈ W ⊓ V := by
      rw [inf_comm]
      exact h.Z_le_N hz
    have h1 := (hxN z hzN).2
    rw [hfix] at h1
    have h2 : (1 - t) * fr₂.c z = 0 := by
      rw [sub_mul, one_mul]
      exact sub_eq_zero.2 h1
    have h3 : fr₂.c z = 0 := by
      rcases mul_eq_zero.1 h2 with h4 | h4
      · exact absurd (sub_eq_zero.1 h4).symm ht1
      · exact h4
    have h4 : z ∈ Z₂ := (fr₂.c_eq_zero_iff hzN).1 h3
    have h5 : z ∈ Z ⊓ Z₂ := ⟨hz, h4⟩
    rw [h.inf_Z] at h5
    exact Subgroup.mem_bot.1 h5

theorem cent_comm_of_trivial {y : G} (hL : ∀ l ∈ L₁, y * l * y⁻¹ * l⁻¹ ∈ V)
    (hV : ∀ v ∈ V, y * v * y⁻¹ * v⁻¹ ∈ Z) :
    ⁅V, L₁⁆ ≤ Subgroup.centralizer ({y} : Set G) := by
  rw [Subgroup.commutator_le]
  intro v hv l hl
  rw [Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨a, ha, hav⟩ : ∃ a ∈ Z, y * v * y⁻¹ = a * v :=
    ⟨y * v * y⁻¹ * v⁻¹, hV v hv, by group⟩
  obtain ⟨c, hc, hcl⟩ : ∃ c ∈ V, y * l * y⁻¹ = c * l :=
    ⟨y * l * y⁻¹ * l⁻¹, hL l hl, by group⟩
  have hlv : l * v⁻¹ * l⁻¹ ∈ V := conj_mem_of_mem_normalizer' (h.L_le_M hl) (inv_mem hv)
  have hX : v * c * l * v⁻¹ ∈ L₁ :=
    mul_mem (mul_mem (mul_mem (h.V_le_L hv) (h.V_le_L hc)) hl) (inv_mem (h.V_le_L hv))
  have key : y * ⁅v, l⁆ * y⁻¹ = ⁅v, l⁆ := by
    have e1 : y * ⁅v, l⁆ * y⁻¹ = (y * v * y⁻¹) * (y * l * y⁻¹) * (y * v * y⁻¹)⁻¹ *
        (y * l * y⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e1, hav, hcl, commutatorElement_def]
    refine comm_conj_eq_of_central (h.jst.abelian_V c hc _ hlv).eq ?_
    exact (Subgroup.mem_centralizer_iff.1 (h.pair.side₁.Z_cent ha) _ hX).symm
  calc ⁅v, l⁆ * y = (y * ⁅v, l⁆ * y⁻¹) * y := by rw [key]
    _ = y * ⁅v, l⁆ := by group

theorem V_le_comm : V ≤ ⁅V, L₁⁆ := by
  have hZ : Z ≤ ⁅V, L₁⁆ :=
    (h.pair.Z_le_comm h.hZ).trans (Subgroup.commutator_mono le_rfl h.pair.side₁.W_le_L)
  exact h.pair.le_comm_sup.trans (sup_le le_rfl hZ)

theorem exists_isTorus : ∃ y : G, IsTorus h y := by
  obtain ⟨x, hxL, hxV, hxZ₂, hxZ⟩ := h.exists_x₂
  obtain ⟨D⟩ := h.pair.side₁.nat
  have hxM : x ∈ Subgroup.normalizer (V : Set G) := mem_normalizer_of_conj_le' hxV
  have hxN : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G) :=
    ⟨hxM, by rw [h.normalizer_Z_eq]; exact hxM⟩
  have hxNL : x ∈ Subgroup.normalizer (L₁ : Set G) := h.M_le_normalizer_L hxM
  obtain ⟨z₂, hz₂, hz₂1⟩ := h.ex_ne_one_Z₂
  have hz₂Z : z₂ ∉ Z := h.not_mem_Z_of_mem_Z₂ hz₂ hz₂1
  have hw₀ : D.κ z₂ ≠ 0 := fun h0 => hz₂Z ((D.κ_eq_zero z₂ (h.Z₂_le_V hz₂)).1 h0)
  have hfix : ∀ c : GaloisField 2 e, D.act x (c • D.κ z₂) = c • D.κ z₂ := by
    intro c
    obtain ⟨z, hz, hzc⟩ := h.exists_Z₂_κ_eq D c hz₂
    rw [← hzc, NatCoordK.act_κ hxN (h.Z₂_le_V hz), hxZ₂ z hz]
  have hlin := act_smul_of_fixed_line D hxNL hxN hw₀ hfix
  obtain ⟨l₀, hl₀, lam, hlam0, hact⟩ := exists_scalar_elem D hxN hlin
  have hinv : (D.ρ l₀⁻¹ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ z₂ =
      lam • D.κ z₂ := by
    have h1 := hact (D.κ z₂)
    rw [NatCoordK.act_mul hxN (D.le_normVK (inv_mem hl₀)),
      NatCoordK.act_of_mem_L (inv_mem hl₀)] at h1
    have h2 : D.act x (lam • D.κ z₂) = lam • D.κ z₂ := hfix lam
    apply (D.actPerm x hxN).injective
    rw [NatCoordK.actPerm_apply hxN, NatCoordK.actPerm_apply hxN, h1, h2]
  have hfwd : (D.ρ l₀ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ z₂ =
      lam⁻¹ • D.κ z₂ := by
    have h1 : D.κ z₂ = (D.ρ l₀ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ
        ((D.ρ l₀⁻¹ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ z₂) := by
      rw [← D.ρ_mulVec_mul hl₀ (inv_mem hl₀), mul_inv_cancel, D.ρ_one]
      simp
    rw [hinv, Matrix.mulVec_smul] at h1
    calc (D.ρ l₀ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ z₂ =
        lam⁻¹ • (lam • ((D.ρ l₀ : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ z₂)) := by
          rw [smul_smul, inv_mul_cancel₀ hlam0, one_smul]
      _ = lam⁻¹ • D.κ z₂ := by rw [← h1]
  have hl₀J : l₀ ∈ Subgroup.normalizer ((V ⊔ W : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conj_le'
    intro j hj
    have hjL : j ∈ L₁ := h.J_le_L hj
    have hcL : l₀ * j * l₀⁻¹ ∈ L₁ := mul_mem (mul_mem hl₀ hjL) (inv_mem hl₀)
    have hjfix := (h.pair.side₁.mem_J_iff D (h.Z₂_le_N hz₂) hz₂Z hjL).1 hj
    rw [h.pair.side₁.mem_J_iff D (h.Z₂_le_N hz₂) hz₂Z hcL,
      D.ρ_mulVec_mul (mul_mem hl₀ hjL) (inv_mem hl₀), D.ρ_mulVec_mul hl₀ hjL, hinv,
      Matrix.mulVec_smul, hjfix, Matrix.mulVec_smul, hfwd, smul_smul, mul_inv_cancel₀ hlam0,
      one_smul]
  have hl₀W : l₀ ∈ Subgroup.normalizer (W : Set G) := h.normalizer_J_le_W hl₀J
  have hxW : x ∈ Subgroup.normalizer (W : Set G) := h.symm.L_le_M hxL
  have key : ∀ y : G, y = x * l₀⁻¹ → IsTorus h y := by
    intro y hy
    rw [← hy] at hact
    have hyV : y ∈ Subgroup.normalizer (V : Set G) := by
      rw [hy]
      exact mul_mem hxM (inv_mem (h.L_le_M hl₀))
    have hyW : y ∈ Subgroup.normalizer (W : Set G) := by
      rw [hy]
      exact mul_mem hxW (inv_mem hl₀W)
    have hyN : y ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G) :=
      ⟨hyV, by rw [h.normalizer_Z_eq]; exact hyV⟩
    have hyNL : y ∈ Subgroup.normalizer (L₁ : Set G) := h.M_le_normalizer_L hyV
    have hcommL : ∀ l ∈ L₁, y * l * y⁻¹ * l⁻¹ ∈ V := fun l hl =>
      comm_mem_V_of_scalar D hyNL hyN hlam0 hact hl
    have hcentZ : ∀ z ∈ Z, y * z * y⁻¹ = z → z = 1 := by
      intro z hz hfixz
      apply hxZ z hz
      have hc := Subgroup.mem_centralizer_iff.1 (h.pair.side₁.Z_cent hz) l₀⁻¹ (inv_mem hl₀)
      have e1 : y * z * y⁻¹ = x * z * x⁻¹ := by
        calc y * z * y⁻¹ = x * (l₀⁻¹ * z) * l₀ * x⁻¹ := by rw [hy]; group
          _ = x * (z * l₀⁻¹) * l₀ * x⁻¹ := by rw [hc]
          _ = x * z * x⁻¹ := by group
      exact e1.symm.trans hfixz
    have hlam1 : lam ≠ 1 := by
      intro hl1
      have hV' : ∀ v ∈ V, y * v * y⁻¹ * v⁻¹ ∈ Z := fun v hv =>
        comm_mem_K_of_one D hyN (fun w => by rw [hact w, hl1]) hv
      have hcent := h.cent_comm_of_trivial hcommL hV'
      obtain ⟨z, hz, hz1⟩ := h.ex_ne_one_Z
      have hzc := hcent (h.V_le_comm (h.Z_le_V hz))
      rw [Subgroup.mem_centralizer_singleton_iff] at hzc
      apply hz1
      apply hcentZ z hz
      rw [← hzc]
      group
    exact ⟨⟨hyV, hcommL, fun v hv hyv =>
      hcentZ v (mem_K_of_centralizes D hyN hlam1 hact hv hyv) hyv⟩, hyW, D, lam, hlam0, hlam1,
      hact⟩
  exact ⟨_, key _ rfl⟩

end G0Core

end CFSG.CGT.PushingUpLit.A78G0

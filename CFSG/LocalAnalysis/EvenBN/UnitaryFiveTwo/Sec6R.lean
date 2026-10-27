module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6Syl
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6Q
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S5E

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

section C7


namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem card_T (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) :
    Nat.card ↥(d.P ⊔ zpowers d.t) = 2 ^ 21 := by
  have hN : zpowers d.t ≤ normalizer (d.P : Set G) := zpowers_le.2 h.t_mem_normalizer_P
  have e := PGrp.card_sup_mul_card_inf hN
  have hinf : zpowers d.t ⊓ d.P = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxt, hxP⟩ := Subgroup.mem_inf.1 hx
    rcases h.eq_one_or_eq_t hxt with rfl | rfl
    · exact one_mem _
    · exact absurd hxP (h.t_not_mem_P hK hKY)
  rw [hinf, Subgroup.card_bot, mul_one, sup_comm, h.card_zpowers_t, h.card_P hK hKY] at e
  rw [e]
  norm_num

theorem isSylowOf_T (h : d.Hyp) (hKl : d.KLinear) (hH : d.H ≤ d.L ⊔ zpowers d.t) :
    CFSG.ABGLocalTools.IsSylowOf 2 (d.P ⊔ zpowers d.t) (normalizer (d.R₃ : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := h.comm_M_V₂_mem_W_linear hKl
  have hKY := h.M_le_normalizer_Y_linear hKl
  set Nh : Subgroup G := normalizer (d.S : Set G) ⊓ d.H with hNh
  have hX := h.normalizer_R₃_eq hK hKY
  have hcT := h.card_T hK hKY
  have hT₂ : IsPGroup 2 ↥(d.P ⊔ zpowers d.t) := IsPGroup.of_card hcT
  have htNh : d.t ∈ Nh := by
    refine Subgroup.mem_inf.2 ⟨mem_normalizer_fintype fun x hx => ?_, h.t_mem_H⟩
    have e : d.t * x * d.t⁻¹ = x := by
      rw [h.t_comm_of_mem_S hx]
      group
    rw [e]
    exact hx
  have hTX : d.P ⊔ zpowers d.t ≤ normalizer (d.R₃ : Set G) := by
    rw [hX]
    exact sup_le le_sup_right (zpowers_le.2 (mem_sup_left htNh))
  have hNhP : Nh ⊓ d.P = d.S := by
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨⟨_, hxH⟩, hxP⟩ := Subgroup.mem_inf.1 hx
      rw [← h.P_inf_H hK hKY]
      exact Subgroup.mem_inf.2 ⟨hxP, hxH⟩
    · have hxPH : x ∈ d.P ⊓ d.H := by
        rw [h.P_inf_H hK hKY]
        exact hx
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨d.S.le_normalizer hx, hxPH.2⟩, hxPH.1⟩
  have hcardX : Nat.card ↥(normalizer (d.R₃ : Set G)) * Nat.card ↥d.S =
      Nat.card ↥Nh * Nat.card ↥d.P := by
    have e := PGrp.card_sup_mul_card_inf (A := Nh) (B := d.P)
      (fun x hx => h.NHS_le_normalizer_P hx)
    rwa [hNhP, ← hX] at e
  rw [d.card_S, h.card_P hK hKY] at hcardX
  have hrel := Subgroup.relIndex_mul_card (d.P ⊔ zpowers d.t) (normalizer (d.R₃ : Set G))
  rw [inf_eq_left.2 hTX, hcT] at hrel
  set r : ℕ := (d.P ⊔ zpowers d.t).relIndex (normalizer (d.R₃ : Set G)) with hr
  have hNhcard : Nat.card ↥Nh = 2 ^ 11 * r := by
    have h1 : Nat.card ↥Nh * 2 ^ 20 = (2 ^ 11 * r) * 2 ^ 20 := by
      calc Nat.card ↥Nh * 2 ^ 20 = Nat.card ↥(normalizer (d.R₃ : Set G)) * 2 ^ 10 := hcardX.symm
        _ = (r * 2 ^ 21) * 2 ^ 10 := by rw [← hrel]
        _ = (2 ^ 11 * r) * 2 ^ 20 := by ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have hHeq : d.H = d.L ⊔ zpowers d.t :=
    le_antisymm hH (sup_le h.L_le_H (zpowers_le.2 h.t_mem_H))
  have hLN : zpowers d.t ≤ normalizer (d.L : Set G) :=
    zpowers_le.2 (mem_normalizer_fintype fun x hx => by
      have e : d.t * x * d.t⁻¹ = x := by
        rw [← mem_centralizer_iff.1 h.t_mem x hx]
        group
      rw [e]
      exact hx)
  have hinfL : zpowers d.t ⊓ d.L = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxt, hxL⟩ := Subgroup.mem_inf.1 hx
    rcases h.eq_one_or_eq_t hxt with rfl | rfl
    · exact one_mem _
    · exact absurd hxL h.t_not_mem_L
  have hLcard := PGrp.card_sup_mul_card_inf hLN
  rw [hinfL, Subgroup.card_bot, mul_one, h.card_zpowers_t] at hLcard
  have hL : Nat.card ↥d.L = 13685760 := by rw [Nat.card_congr d.η.toEquiv, card_SU52.1]
  have hHcard : Nat.card ↥d.H = 2 * 13685760 := by
    rw [hHeq, sup_comm, hLcard, hL]
  have hodd : ¬ 2 ∣ r := by
    intro h2
    have hdvd : Nat.card ↥Nh ∣ Nat.card ↥d.H := Subgroup.card_dvd_of_le inf_le_right
    rw [hNhcard, hHcard] at hdvd
    have h12 : 2 ^ 12 ∣ 2 ^ 11 * r := by
      obtain ⟨k, hk⟩ := h2
      exact ⟨k, by rw [hk]; ring⟩
    have := h12.trans hdvd
    norm_num at this
  exact CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hTX, hT₂, hodd⟩

theorem S₃_inf_centralizer_commutator_S₃ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    d.S₃ ⊓ centralizer ((⁅d.S₃, d.S₃⁆ : Subgroup G) : Set G) = d.Y := by
  refine le_antisymm (fun x hx => ?_) (fun y hy => ?_)
  · obtain ⟨hxS, hxC⟩ := Subgroup.mem_inf.1 hx
    rw [← h.S₃_inf_centralizer_commutator_S]
    refine Subgroup.mem_inf.2 ⟨hxS, mem_centralizer_iff.2 fun k hk => ?_⟩
    exact mem_centralizer_iff.1 hxC k (Subgroup.commutator_mono h.S_le_S₃ h.S_le_S₃ hk)
  · refine Subgroup.mem_inf.2 ⟨h.Y_le_S₃ hy, mem_centralizer_iff.2 fun k hk => ?_⟩
    have hkV : k ∈ d.V₃ :=
      (Subgroup.commutator_le).2 (fun a ha b hb => h.commutator_mem_V₃_of_mem_S₃ hK ha hb) hk
    exact D₂_comm_Y' (h.V₃_le_D₂ hK hkV) hy

theorem commutator_T_le_S₃ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) :
    ⁅d.P ⊔ zpowers d.t, d.P ⊔ zpowers d.t⁆ ≤ d.S₃ := by
  have hPeq := h.P_eq_P₀ hK hKY
  obtain ⟨-, -, hP₀S₃⟩ := h.P₀_eq_and_card hK hKY
  have hPS₃ : ∀ x ∈ d.P, ∀ y ∈ d.P, x * y * x⁻¹ * y⁻¹ ∈ d.S₃ := by
    rw [hPeq]
    exact hP₀S₃
  have hS₃P : d.S₃ ≤ d.P := by
    rw [hPeq]
    exact h.S₃_le_P₀ hK
  have hPN : d.P ≤ normalizer (d.S₃ : Set G) := fun x hx => mem_normalizer_fintype fun s hs => by
    have e : x * s * x⁻¹ = (x * s * x⁻¹ * s⁻¹) * s := by group
    rw [e]
    exact mul_mem (hPS₃ x hx s (hS₃P hs)) hs
  have htN : d.t ∈ normalizer (d.S₃ : Set G) := mem_normalizer_fintype fun k hk => by
    rw [h.t_inv]
    exact h.t_conj_mem_S₃ hk
  refine commutator_sup_le_of hPN (zpowers_le.2 htN) hPS₃ (fun b hb b' hb' => ?_)
    (fun a ha b hb => ?_)
  · have : ⁅b, b'⁆ = 1 := by
      rcases h.eq_one_or_eq_t hb with rfl | rfl <;>
        rcases h.eq_one_or_eq_t hb' with rfl | rfl <;> simp [commutatorElement_def]
    rw [this]
    exact one_mem _
  · rcases h.eq_one_or_eq_t hb with rfl | rfl
    · have : ⁅a, (1 : G)⁆ = 1 := by simp [commutatorElement_def]
      rw [this]
      exact one_mem _
    · rw [commutatorElement_def, h.t_inv]
      exact h.theta_mem_S₃ (hPeq ▸ ha)

theorem commutator_T_eq_S₃ (h : d.Hyp) (hKl : d.KLinear) :
    ⁅d.P ⊔ zpowers d.t, d.P ⊔ zpowers d.t⁆ = d.S₃ :=
  le_antisymm (h.commutator_T_le_S₃ (h.comm_M_V₂_mem_W_linear hKl)
    (h.M_le_normalizer_Y_linear hKl)) (h.S₃_le_commutator_T hKl)

theorem mem_normalizer_S₃_of_T (h : d.Hyp) (hKl : d.KLinear) {n : G}
    (hn : n ∈ normalizer ((d.P ⊔ zpowers d.t : Subgroup G) : Set G)) :
    n ∈ normalizer (d.S₃ : Set G) := by
  refine mem_normalizer_fintype fun x hx => ?_
  rw [← h.commutator_T_eq_S₃ hKl] at hx ⊢
  exact conj_mem_commutator_self_of_mem_normalizer hn hx

theorem mem_normalizer_Y_of_T (h : d.Hyp) (hKl : d.KLinear) {n : G}
    (hn : n ∈ normalizer ((d.P ⊔ zpowers d.t : Subgroup G) : Set G)) :
    n ∈ normalizer (d.Y : Set G) := by
  have hK := h.comm_M_V₂_mem_W_linear hKl
  have hnSN := h.mem_normalizer_S₃_of_T hKl hn
  have hYeq := h.S₃_inf_centralizer_commutator_S₃ hK
  refine mem_normalizer_fintype fun y hy => ?_
  have hyC : y ∈ centralizer ((⁅d.S₃, d.S₃⁆ : Subgroup G) : Set G) := by
    have : y ∈ d.S₃ ⊓ centralizer ((⁅d.S₃, d.S₃⁆ : Subgroup G) : Set G) := by
      rw [hYeq]
      exact hy
    exact (Subgroup.mem_inf.1 this).2
  rw [← hYeq]
  refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 hnSN y).1 (h.Y_le_S₃ hy),
    mem_centralizer_iff.2 fun r hr => ?_⟩
  have hr' : n⁻¹ * r * n ∈ ⁅d.S₃, d.S₃⁆ := by
    have := conj_mem_commutator_self_of_mem_normalizer (inv_mem hnSN) hr
    rwa [inv_inv] at this
  have hyc := mem_centralizer_iff.1 hyC _ hr'
  calc r * (n * y * n⁻¹) = n * ((n⁻¹ * r * n) * y) * n⁻¹ := by group
    _ = n * (y * (n⁻¹ * r * n)) * n⁻¹ := by rw [hyc]
    _ = (n * y * n⁻¹) * r := by group

theorem mem_normalizer_V₃_of_T (h : d.Hyp) (hKl : d.KLinear) {n : G}
    (hn : n ∈ normalizer ((d.P ⊔ zpowers d.t : Subgroup G) : Set G)) :
    n ∈ normalizer (d.V₃ : Set G) :=
  h.mem_normalizer_V₃ (h.mem_normalizer_S₃_of_T hKl hn) (h.mem_normalizer_Y_of_T hKl hn)

theorem map_conj_P_eq_P (h : d.Hyp) (hKl : d.KLinear) {n : G}
    (hn : n ∈ normalizer ((d.P ⊔ zpowers d.t : Subgroup G) : Set G)) :
    d.P.map (MulAut.conj n).toMonoidHom = d.P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := h.comm_M_V₂_mem_W_linear hKl
  have hKY := h.M_le_normalizer_Y_linear hKl
  obtain ⟨hQ1c, -⟩ := h.P_comm_sq_mem_V₃ hKl
  have hnV := h.mem_normalizer_V₃_of_T hKl hn
  have hnV' : ∀ x ∈ d.V₃, n * x * n⁻¹ ∈ d.V₃ := fun x hx => (mem_normalizer_iff.1 hnV x).1 hx
  have hPV : d.P ≤ normalizer (d.V₃ : Set G) :=
    sup_le (h.D₁_le_normalizer_V₃ hKY) h.D₂_le_normalizer_V₃
  have hPeq := h.P_eq_P₀ hK hKY
  have hcT := h.card_T hK hKY
  have hPT : d.P ≤ d.P ⊔ zpowers d.t := le_sup_left
  have hTn : ∀ x ∈ d.P ⊔ zpowers d.t, n * x * n⁻¹ ∈ d.P ⊔ zpowers d.t := fun x hx =>
    (mem_normalizer_iff.1 hn x).1 hx
  have hTn' : ∀ x ∈ d.P ⊔ zpowers d.t, n⁻¹ * x * n ∈ d.P ⊔ zpowers d.t := fun x hx => by
    have := (mem_normalizer_iff.1 (inv_mem hn) x).1 hx
    rwa [inv_inv] at this
  have hTP : d.P ⊔ zpowers d.t ≤ normalizer (d.P : Set G) :=
    sup_le d.P.le_normalizer (zpowers_le.2 h.t_mem_normalizer_P)
  set P' : Subgroup G := d.P.map (MulAut.conj n).toMonoidHom with hP'def
  have hP'T : P' ≤ d.P ⊔ zpowers d.t := by
    rintro _ ⟨x, hx, rfl⟩
    exact hTn x (hPT hx)
  have hcardP' : Nat.card ↥P' = 2 ^ 20 := by
    rw [hP'def, Subgroup.card_map_of_injective (MulAut.conj n).injective, h.card_P hK hKY]
  have hle : P' ≤ d.P := by
    by_contra hcon
    obtain ⟨y, hyP', hyP⟩ := SetLike.not_le_iff_exists.1 hcon
    obtain ⟨z, hz, rfl⟩ := hyP'
    have hyT : (MulAut.conj n).toMonoidHom z ∈ d.P ⊔ zpowers d.t := hP'T ⟨z, hz, rfl⟩
    set y : G := (MulAut.conj n).toMonoidHom z with hydef
    have hzy : y = n * z * n⁻¹ := rfl
    have hpP : y * d.t ∈ d.P := by
      rcases (mem_sup_zpowers_iff h.t_mul_t fun k hk => h.t_conj_mem_P hk).1 hyT with h1 | h1
      · exact absurd h1 hyP
      · exact h1
    obtain ⟨p, hpdef⟩ : ∃ p : G, p = y * d.t := ⟨_, rfl⟩
    rw [← hpdef] at hpP
    have ht1 : d.t = p⁻¹ * y := by
      have : p⁻¹ * y = d.t⁻¹ := by rw [hpdef]; group
      rw [this, h.t_inv]
    have ht2 : d.t = y⁻¹ * p := by
      have : y⁻¹ * p = d.t := by rw [hpdef]; group
      exact this.symm
    have hinf : d.P ⊓ P' ≤ d.S₃ := by
      intro x hx
      obtain ⟨hxP, hxP'⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨x₀, hx₀, rfl⟩ := hxP'
      set x : G := (MulAut.conj n).toMonoidHom x₀ with hxdef
      have hxy : x * y * x⁻¹ * y⁻¹ ∈ d.V₃ := by
        have e : x * y * x⁻¹ * y⁻¹ = n * (x₀ * z * x₀⁻¹ * z⁻¹) * n⁻¹ := by
          rw [hxdef, hydef]
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [e]
        exact hnV' _ (hQ1c x₀ hx₀ z hz)
      have hc1 : x * p⁻¹ * x⁻¹ * p ∈ d.V₃ := by
        have := hQ1c x hxP p⁻¹ (inv_mem hpP)
        rwa [inv_inv] at this
      have hc2 : p⁻¹ * (x * y * x⁻¹ * y⁻¹) * p ∈ d.V₃ := by
        have := (mem_normalizer_iff.1 (hPV (inv_mem hpP)) _).1 hxy
        rwa [inv_inv] at this
      have hθ : x * d.t * x⁻¹ * d.t ∈ d.V₃ := by
        have e : x * d.t * x⁻¹ * d.t =
            (x * p⁻¹ * x⁻¹ * p) * (p⁻¹ * (x * y * x⁻¹ * y⁻¹) * p) := by
          calc x * d.t * x⁻¹ * d.t = x * (p⁻¹ * y) * x⁻¹ * (y⁻¹ * p) := by
                rw [← ht1, ← ht2]
            _ = _ := by group
        rw [e]
        exact mul_mem hc1 hc2
      exact h.mem_S₃_of_theta_mem_V₃ hK (hPeq ▸ hxP) hθ
    have hPN' : d.P ≤ normalizer (P' : Set G) := fun x hx => by
      refine mem_normalizer_fintype fun w hw => ?_
      obtain ⟨w₀, hw₀, rfl⟩ := hw
      have hxT : n⁻¹ * x * n ∈ d.P ⊔ zpowers d.t := hTn' x (hPT hx)
      have hc := (mem_normalizer_iff.1 (hTP hxT) w₀).1 hw₀
      refine ⟨(n⁻¹ * x * n) * w₀ * (n⁻¹ * x * n)⁻¹, hc, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have e := PGrp.card_sup_mul_card_inf hPN'
    rw [h.card_P hK hKY, hcardP'] at e
    have h1 : Nat.card ↥(d.P ⊔ P') ≤ 2 ^ 21 :=
      hcT ▸ Subgroup.card_le_of_le (sup_le hPT hP'T)
    have h2 : Nat.card ↥(d.P ⊓ P') ≤ 2 ^ 16 :=
      h.card_S₃ ▸ Subgroup.card_le_of_le hinf
    have h3 := Nat.mul_le_mul h1 h2
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardP', h.card_P hK hKY])

theorem normalizer_T_le_normalizer_R₃ (h : d.Hyp) (hKl : d.KLinear) :
    normalizer ((d.P ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (d.R₃ : Set G) := by
  intro n hn
  have hK := h.comm_M_V₂_mem_W_linear hKl
  have hKY := h.M_le_normalizer_Y_linear hKl
  obtain ⟨-, hQ1s⟩ := h.P_comm_sq_mem_V₃ hKl
  have hPeq := h.P_eq_P₀ hK hKY
  have hPmap := h.map_conj_P_eq_P hKl hn
  have hnS₃ := h.mem_normalizer_S₃_of_T hKl hn
  have htT : d.t ∈ d.P ⊔ zpowers d.t := mem_sup_right (mem_zpowers _)
  have hutT : n * d.t * n⁻¹ ∈ d.P ⊔ zpowers d.t := (mem_normalizer_iff.1 hn d.t).1 htT
  have hnP : n * d.t * n⁻¹ ∉ d.P := by
    intro hP
    rw [← hPmap] at hP
    obtain ⟨z, hz, hzeq⟩ := hP
    have : z = d.t := by
      have h1 : n * z * n⁻¹ = n * d.t * n⁻¹ := hzeq
      exact mul_left_cancel (mul_right_cancel h1)
    exact h.t_not_mem_P hK hKY (this ▸ hz)
  have hpP : (n * d.t * n⁻¹) * d.t ∈ d.P := by
    rcases (mem_sup_zpowers_iff h.t_mul_t fun k hk => h.t_conj_mem_P hk).1 hutT with h1 | h1
    · exact absurd h1 hnP
    · exact h1
  obtain ⟨p, hpdef⟩ : ∃ p : G, p = (n * d.t * n⁻¹) * d.t := ⟨_, rfl⟩
  rw [← hpdef] at hpP
  have hu : n * d.t * n⁻¹ = p * d.t := by
    rw [hpdef, mul_assoc (n * d.t * n⁻¹) d.t d.t, h.t_mul_t, mul_one]
  have hu2 : (p * d.t) * (p * d.t) = 1 := by
    rw [← hu, show n * d.t * n⁻¹ * (n * d.t * n⁻¹) = n * (d.t * d.t) * n⁻¹ by group, h.t_mul_t]
    group
  have e1 : d.t * p⁻¹ = p * d.t := by
    calc d.t * p⁻¹ = (p * d.t)⁻¹ := by rw [mul_inv_rev, h.t_inv]
      _ = p * d.t := inv_eq_of_mul_eq_one_right hu2
  have hθ : p * d.t * p⁻¹ * d.t = p * p := by
    calc p * d.t * p⁻¹ * d.t = p * (d.t * p⁻¹) * d.t := by group
      _ = p * (p * d.t) * d.t := by rw [e1]
      _ = p * p * (d.t * d.t) := by group
      _ = p * p := by rw [h.t_mul_t, mul_one]
  have hpS₃ : p ∈ d.S₃ :=
    h.mem_S₃_of_theta_mem_V₃ hK (hPeq ▸ hpP) (hθ ▸ hQ1s p hpP)
  have hutR : n * d.t * n⁻¹ ∈ d.R₃ := by
    rw [hu, h.R₃_eq_S₃_sup]
    exact mul_mem (mem_sup_left hpS₃) (mem_sup_right (mem_zpowers _))
  refine mem_normalizer_fintype fun x hx => ?_
  rw [h.R₃_eq_S₃_sup] at hx ⊢
  rcases (mem_sup_zpowers_iff h.t_mul_t fun k hk => h.t_conj_mem_S₃ hk).1 hx with h1 | h1
  · exact mem_sup_left ((mem_normalizer_iff.1 hnS₃ x).1 h1)
  · have e : n * x * n⁻¹ = (n * (x * d.t) * n⁻¹) * (n * d.t * n⁻¹) := by
      calc n * x * n⁻¹ = n * (x * d.t * d.t) * n⁻¹ := by
            rw [mul_assoc x d.t d.t, h.t_mul_t, mul_one]
        _ = _ := by group
    rw [e]
    refine mul_mem (mem_sup_left ((mem_normalizer_iff.1 hnS₃ _).1 h1)) ?_
    have := hutR
    rwa [h.R₃_eq_S₃_sup] at this

theorem exists_sylow_T (h : d.Hyp) (hKl : d.KLinear) (hH : d.H ≤ d.L ⊔ zpowers d.t) :
    ∃ S₂ : Sylow 2 G, (S₂ : Subgroup G) = d.P ⊔ zpowers d.t := by
  have hK := h.comm_M_V₂_mem_W_linear hKl
  have hKY := h.M_le_normalizer_Y_linear hKl
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_sylow_of_normalizer_le (IsPGroup.of_card (h.card_T hK hKY))
    (h.isSylowOf_T hKl hH) (h.normalizer_T_le_normalizer_R₃ hKl)

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

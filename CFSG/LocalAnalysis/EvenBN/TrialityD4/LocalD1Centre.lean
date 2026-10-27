module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalD1

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem commutator_commute_of_conj_D4 {y g j : G} (hyj : j * y = y * j)
    (hgj : j * (g⁻¹ * y * g) = g⁻¹ * y * g * j) :
    g * j * g⁻¹ * j⁻¹ * y = y * (g * j * g⁻¹ * j⁻¹) := by
  have h1 : j⁻¹ * y = y * j⁻¹ := by
    calc j⁻¹ * y = j⁻¹ * (y * j) * j⁻¹ := by group
      _ = j⁻¹ * (j * y) * j⁻¹ := by rw [hyj]
      _ = y * j⁻¹ := by group
  calc g * j * g⁻¹ * j⁻¹ * y = g * j * g⁻¹ * (j⁻¹ * y) := by group
    _ = g * j * g⁻¹ * (y * j⁻¹) := by rw [h1]
    _ = g * (j * (g⁻¹ * y * g)) * g⁻¹ * j⁻¹ := by group
    _ = g * (g⁻¹ * y * g * j) * g⁻¹ * j⁻¹ := by rw [hgj]
    _ = y * (g * j * g⁻¹ * j⁻¹) := by group

theorem mem_normalizer_map_conj_D4 [Finite G] {A : Subgroup G} {g x : G}
    (hx : x ∈ normalizer (A : Set G)) (hgx : g * x = x * g) :
    x ∈ normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
  mem_normalizer_fintype fun y hy => by
    rw [SetLike.mem_coe, mem_map_conj_iff_D4] at hy ⊢
    have h1 : g⁻¹ * x = x * g⁻¹ := by
      calc g⁻¹ * x = g⁻¹ * (x * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * x) * g⁻¹ := by rw [hgx]
        _ = x * g⁻¹ := by group
    have h2 : x⁻¹ * g = g * x⁻¹ := by
      calc x⁻¹ * g = x⁻¹ * (g * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * g) * x⁻¹ := by rw [hgx]
        _ = g * x⁻¹ := by group
    have e : g⁻¹ * (x * y * x⁻¹) * g = x * (g⁻¹ * y * g) * x⁻¹ := by
      calc g⁻¹ * (x * y * x⁻¹) * g = (g⁻¹ * x) * y * (x⁻¹ * g) := by group
        _ = (x * g⁻¹) * y * (g * x⁻¹) := by rw [h1, h2]
        _ = x * (g⁻¹ * y * g) * x⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 hx _).1 hy

end Generic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

section Seven

theorem mem_sup_zpowers_iff_of_normalizer (h : Setup G L f t) {A : Subgroup G}
    (htA : t ∈ normalizer (A : Set G)) {x : G} :
    x ∈ A ⊔ zpowers t ↔ x ∈ A ∨ t * x ∈ A := by
  have hset := coe_mul_of_right_le_normalizer_left A (zpowers t) ((zpowers_le).2 htA)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  constructor
  · intro hx
    have hx' : x ∈ ((A ⊔ zpowers t : Subgroup G) : Set G) := hx
    rw [hset] at hx'
    obtain ⟨a, ha, s, hs, hx⟩ := hx'
    have hx2 : a * s = x := hx
    rw [← hx2]
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hs
    rcases h.zpow_eq_one_or_eq k with h1 | h1
    · left
      rw [h1, mul_one]
      exact ha
    · right
      rw [h1]
      have := (mem_normalizer_iff.1 htA a).1 ha
      rw [htinv] at this
      rw [← mul_assoc]
      exact this
  · rintro (hx | hx)
    · exact mem_sup_left hx
    · have : x = t * (t * x) := by rw [← mul_assoc, h.t_mul_t, one_mul]
      rw [this]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hx)

omit [Finite G] in
theorem yamadaV₁_le_yamadaD₁_D1 {q : ℕ} (d : TrialityD4Data L q) : yamadaV₁ d t ≤ yamadaD₁ d t :=
  inf_le_left

omit [Finite G] in
theorem yamadaD₁_le_centralizer_yamadaV₁ {q : ℕ} (d : TrialityD4Data L q) :
    yamadaD₁ d t ≤ centralizer (yamadaV₁ d t : Set G) :=
  le_centralizer_iff.1 inf_le_right

theorem yamadaV₁_le_centralizer_J₀ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaV₁ d t ≤ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) := by
  obtain ⟨X, hX, htX, hQX⟩ := h.exists_isSylowOf_jZeroLayer_yamadaD₁ d hlay
  rw [h.yamadaV₁_eq_center d hlay hX htX hQX]
  exact inf_le_left.trans (hX.le.trans (jZeroLayer_le_centralizer_J₀ d))

theorem yamadaD₁_eq_sup_D1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaD₁ d t = yamadaV₁ d t ⊔ d.D.map L.subtype := by
  obtain ⟨X, hX, htX, hQX⟩ := h.exists_isSylowOf_jZeroLayer_yamadaD₁ d hlay
  have hQ := h.yamadaD₁_inf_centralizer_J₀_eq_sup d hlay hX htX hQX
  rw [← h.yamadaV₁_eq_center d hlay hX htX hQX, h.yamadaD₁_inf_centralizer_J₀ d hlay]
    at hQ
  refine le_antisymm (sup_le ?_ le_sup_right) (sup_le (yamadaV₁_le_yamadaD₁_D1 d)
    (D_map_le_yamadaD₁ d))
  rw [hQ]
  exact sup_le ((sylowJ₀_map_le_D_map d).trans le_sup_right) le_sup_left

theorem S_map_le_normalizer_yamadaD₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    d.S.map L.subtype ≤ normalizer (yamadaD₁ d t : Set G) :=
  (map_mono d.S_le_normalizer_V).trans (h.map_normalizer_V_le_normalizer_yamadaD₁ d)

theorem normalizer_yamadaD₁_le_normalizer_yamadaV₁_D1 {q : ℕ} (d : TrialityD4Data L q) :
    normalizer (yamadaD₁ d t : Set G) ≤ normalizer (yamadaV₁ d t : Set G) := fun _ hg =>
  mem_normalizer_inf_D4 hg (mem_normalizer_centralizer_D4 hg)

theorem x₁_mem_centralizer_yamadaV₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) (a : d.Γ) :
    ((d.x₁ a : L) : G) ∈ centralizer (yamadaV₁ d t : Set G) := by
  obtain ⟨m, hm1, hm⟩ := d.exists_mem_ker_nmUnits_ne_one
  have hj : ((d.torus (1, m) : L) : G) ∈ d.J₀.map L.subtype := ⟨_, d.torus_one_mem_J₀ hm1, rfl⟩
  have hV₁H := h.yamadaV₁_le_centralizer_J₀ d hlay
  have hN : ∀ c : d.Γ, ((d.x₁ c : L) : G) ∈ normalizer (yamadaV₁ d t : Set G) := fun c =>
    normalizer_yamadaD₁_le_normalizer_yamadaV₁_D1 d
      (h.S_map_le_normalizer_yamadaD₁ d ⟨_, d.U₁_le_S (d.x₁_mem_U₁ c), rfl⟩)
  have hcomm : ∀ c : d.Γ, ((d.x₁ c : L) : G) * ((d.torus (1, m) : L) : G) *
      ((d.x₁ c : L) : G)⁻¹ * ((d.torus (1, m) : L) : G)⁻¹ = ((d.x₁ ((1 + (m : d.Γ)) * c) : L) :
        G) := fun c => by
    have e1 := d.torus_x₁ (1, m) c
    have e2 : (d.x₁ c)⁻¹ = d.x₁ c := inv_eq_of_mul_eq_one_right (d.x₁_mul_self c)
    have e3 : d.x₁ c * d.torus (1, m) * (d.x₁ c)⁻¹ * (d.torus (1, m))⁻¹ =
        d.x₁ ((1 + (m : d.Γ)) * c) := by
      calc d.x₁ c * d.torus (1, m) * (d.x₁ c)⁻¹ * (d.torus (1, m))⁻¹ =
          d.x₁ c * (d.torus (1, m) * (d.x₁ c)⁻¹ * (d.torus (1, m))⁻¹) := by group
        _ = d.x₁ c * (d.torus (1, m) * d.x₁ c * (d.torus (1, m))⁻¹) := by rw [e2]
        _ = d.x₁ c * d.x₁ ((m : d.Γ) * c) := by rw [e1]
        _ = d.x₁ ((1 + (m : d.Γ)) * c) := by rw [← d.x₁_add, add_mul, one_mul]
    rw [← e3]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hν : (1 : d.Γ) + (m : d.Γ) ≠ 0 := by
    intro h0
    have h1 : (m : d.Γ) = 1 := add_left_cancel (h0.trans (CharTwo.add_self_eq_zero (1 : d.Γ)).symm)
    exact hm (Units.ext (by rw [Units.val_one]; exact h1))
  have ha : a = (1 + (m : d.Γ)) * ((1 + (m : d.Γ))⁻¹ * a) := by
    rw [← mul_assoc, mul_inv_cancel₀ hν, one_mul]
  rw [mem_centralizer_iff]
  intro y hy
  rw [ha, ← hcomm]
  refine (commutator_commute_of_conj_D4 (mem_centralizer_iff.1 (hV₁H hy) _ hj) ?_).symm
  have hy' : ((d.x₁ ((1 + (m : d.Γ))⁻¹ * a) : L) : G)⁻¹ * y *
      ((d.x₁ ((1 + (m : d.Γ))⁻¹ * a) : L) : G) ∈ yamadaV₁ d t :=
    (mem_normalizer_iff''.1 (hN _) y).1 hy
  exact mem_centralizer_iff.1 (hV₁H hy') _ hj

theorem S_map_le_centralizer_yamadaV₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    d.S.map L.subtype ≤ centralizer (yamadaV₁ d t : Set G) := by
  rw [d.S_eq_sup, Subgroup.map_sup]
  refine sup_le ?_ ((D_map_le_yamadaD₁ d).trans (yamadaD₁_le_centralizer_yamadaV₁ d))
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  exact h.x₁_mem_centralizer_yamadaV₁ d hlay a

theorem yamadaS₁_eq_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaS₁ d t = d.S.map L.subtype ⊔ yamadaV₁ d t := by
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left
    ((yamadaV₁_le_yamadaD₁_D1 d).trans le_sup_right))
  rw [h.yamadaD₁_eq_sup_D1 d hlay]
  exact sup_le le_sup_right ((map_mono d.D_le_S).trans le_sup_left)

theorem yamada_5_7 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaS₁ d t ⊓ centralizer (yamadaS₁ d t : Set G) = yamadaV₁ d t := by
  have hSV := h.S_map_le_centralizer_yamadaV₁ d hlay
  have hV₁c : yamadaV₁ d t ≤ centralizer (yamadaS₁ d t : Set G) := by
    rw [le_centralizer_iff, h.yamadaS₁_eq_sup d hlay]
    exact sup_le hSV (le_centralizer_iff.1 ((yamadaV₁_le_yamadaD₁_D1 d).trans
      (le_centralizer_iff.1 inf_le_right)))
  refine le_antisymm (fun z hz => ?_) (le_inf ((yamadaV₁_le_yamadaD₁_D1 d).trans le_sup_right)
    hV₁c)
  obtain ⟨hzS, hzc⟩ := Subgroup.mem_inf.1 hz
  have hzS' : z ∈ ((yamadaS₁ d t : Subgroup G) : Set G) := hzS
  rw [h.yamadaS₁_eq_sup d hlay, coe_mul_of_right_le_normalizer_left _ _
    ((le_centralizer_iff.1 hSV).trans (Subgroup.centralizer_le_normalizer _))] at hzS'
  obtain ⟨s, hs, w, hw, rfl⟩ := hzS'
  have hsc : s ∈ centralizer (yamadaS₁ d t : Set G) := by
    have := mul_mem hzc (inv_mem (hV₁c hw))
    rwa [mul_inv_cancel_right] at this
  have hsV : s ∈ d.V.map L.subtype := by
    rw [← map_inf_centralizer_map d.S_inf_centralizer_S]
    exact Subgroup.mem_inf.2 ⟨hs, mem_centralizer_iff.2 fun y hy =>
      mem_centralizer_iff.1 hsc y (le_sup_left (a := d.S.map L.subtype) hy)⟩
  have hVV₁ : d.V.map L.subtype ≤ yamadaV₁ d t := by
    rw [← (h.yamada_5_6_2 d hlay).2.2.1]
    exact inf_le_left
  exact mul_mem (hVV₁ hsV) hw

end Seven

section Nine

theorem v_mul_t (h : Setup G L f t) {q : ℕ} (d : TrialityD4Data L q) :
    ((d.v : L) : G) * t = t * (d.v : G) :=
  mem_centralizer_iff.1 h.htL _ d.v.2

theorem v_mem_normalizer_yamadaL₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    ((d.v : L) : G) ∈ normalizer (yamadaL₂ d t : Set G) :=
  le_normalizer_yamadaL₂ d t (h.centralizer_inf_normalizer_Y_le d
    (Subgroup.mem_inf.2 ⟨h.L_le_centralizer d.v.2, coe_mem_normalizer_map d.v_mem_normalizer_Y⟩))

theorem v_mem_normalizer_jZeroLayer {q : ℕ} (d : TrialityD4Data L q) :
    ((d.v : L) : G) ∈ normalizer (jZeroLayer d : Set G) :=
  normalizer_le_normalizer_jZeroLayer d (coe_mem_normalizer_map d.v_mem_normalizer_J₀)

theorem t_mem_yamadaL₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) : t ∈ yamadaL₂ d t :=
  h.tM_le_yamadaL₂ d (mem_sup_right (mem_zpowers t))

theorem card_yamadaL₂_inf_centralizer_J₀ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    Nat.card (yamadaL₂ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :
      Subgroup G) = 2 * (2 ^ f) ^ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : ¬ 2 ∣ Nat.card (d.J₀.map L.subtype : Subgroup G) := by
    rw [card_map_of_injective L.subtype_injective]
    exact d.odd_card_J₀.not_two_dvd_nat
  rw [card_inf_centralizer_eq_of_coprime_D4 (P := yamadaL₂ d t) (h.tM_le_yamadaL₂ d)
    (h.yamadaL₂_le_normalizer_tM d) (h.J₀_map_le_normalizer_yamadaL₂ d)
    (h.J₀_map_le_normalizer_tM d) (h.isPGroup_tM d) hA
    (fun a ha x hx => h.inv_mul_conj_mem_tM_of_mem_yamadaL₂ d ha hx),
    h.tM_inf_centralizer_J₀ d, h.card_sup_zpowers (map_subtype_le _),
    card_map_of_injective L.subtype_injective, d.card_Y, h.relIndex_tM_yamadaL₂ d]
  ring

theorem card_jZeroLayer_inf_yamadaL₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    Nat.card (jZeroLayer d ⊓ yamadaL₂ d t : Subgroup G) = (2 ^ f) ^ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 (yamadaR₂ d t ⊓
      centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) : Subgroup G) :=
    (h.isPGroup_yamadaR₂ d).to_le inf_le_left
  have hP₀ : d.sylowJ₀.map L.subtype ⊔ zpowers t ≤ yamadaR₂ d t ⊓
      centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
    sup_le (le_inf (((sylowJ₀_map_le_D_map d).trans (map_mono d.D_le_S)).trans le_sup_right)
      (sylowJ₀_map_le_centralizer_J₀ d))
      ((zpowers_le).2 (Subgroup.mem_inf.2 ⟨le_sup_left (a := yamadaL₂ d t) (h.t_mem_yamadaL₂ d),
        h.t_mem_centralizer_J₀ d⟩))
  have h1 := h.card_le_two_mul_card_inf_jZeroLayer d hlay
    (P := yamadaL₂ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))
    (inf_le_inf_right _ le_sup_left) inf_le_right hQ hP₀
  rw [h.card_yamadaL₂_inf_centralizer_J₀ d, inf_assoc,
    inf_eq_right.2 (jZeroLayer_le_centralizer_J₀ d), inf_comm (yamadaL₂ d t)] at h1
  have htB : t ∈ normalizer ((jZeroLayer d ⊓ yamadaL₂ d t : Subgroup G) : Set G) :=
    mem_normalizer_inf_D4 (le_normalizer_jZeroLayer d (h.t_mem_centralizer_J₀ d))
      (le_normalizer (h.t_mem_yamadaL₂ d))
  have htB' : t ∉ jZeroLayer d ⊓ yamadaL₂ d t :=
    fun ht => h.t_not_mem_jZeroLayer d hlay (Subgroup.mem_inf.1 ht).1
  have hle : (jZeroLayer d ⊓ yamadaL₂ d t) ⊔ zpowers t ≤
      yamadaL₂ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
    sup_le (le_inf inf_le_right (inf_le_left.trans (jZeroLayer_le_centralizer_J₀ d)))
      ((zpowers_le).2 (Subgroup.mem_inf.2 ⟨h.t_mem_yamadaL₂ d, h.t_mem_centralizer_J₀ d⟩))
  have h2 := card_le_of_le hle
  rw [h.card_sup_zpowers_of_not_mem htB htB', h.card_yamadaL₂_inf_centralizer_J₀ d] at h2
  exact le_antisymm (Nat.le_of_mul_le_mul_left h2 (by norm_num))
    (Nat.le_of_mul_le_mul_left h1 (by norm_num))

theorem exists_isSylowOf_jZeroLayer_yamadaR₂ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    ∃ X : Subgroup G, IsSylowOf 2 X (jZeroLayer d) ∧ yamadaV₁ d t = X ⊓ centralizer (X : Set G) ∧
      d.sylowJ₀.map L.subtype ≤ X ∧ jZeroLayer d ⊓ yamadaL₂ d t ≤ X ∧
      ∀ x ∈ X, x * x ∈ yamadaV₁ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, hX, htX, hQX⟩ := exists_isSylowOf_jZeroLayer d
    (Q := yamadaR₂ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) inf_le_right
    ((h.isPGroup_yamadaR₂ d).to_le inf_le_left)
    (Subgroup.mem_inf.2 ⟨le_sup_left (a := yamadaL₂ d t) (h.t_mem_yamadaL₂ d),
      h.t_mem_centralizer_J₀ d⟩)
  have hD₁X : yamadaD₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ≤ X := by
    rw [h.yamadaD₁_inf_centralizer_J₀ d hlay]
    exact le_trans (le_inf (le_inf (inf_le_left.trans (h.yamadaC₁_le_yamadaR₂ d))
      (inf_le_right.trans (jZeroLayer_le_centralizer_J₀ d))) inf_le_right) hQX
  obtain ⟨hV, hsq, -⟩ := h.yamada_5_6_3 d hlay X hX htX hD₁X
  refine ⟨X, hX, hV, ?_, ?_, hsq⟩
  · exact (le_inf ((sylowJ₀_map_le_D_map d).trans (D_map_le_yamadaD₁ d))
      (sylowJ₀_map_le_centralizer_J₀ d)).trans hD₁X
  · exact le_trans (le_inf (le_inf (inf_le_right.trans le_sup_left)
      (inf_le_left.trans (jZeroLayer_le_centralizer_J₀ d))) inf_le_left) hQX

theorem yamadaY₂_le_center (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaY₂ d t ≤ (jZeroLayer d ⊓ yamadaL₂ d t) ⊓
      centralizer ((jZeroLayer d ⊓ yamadaL₂ d t : Subgroup G) : Set G) := by
  obtain ⟨X, hX, hV, -, hBX, -⟩ := h.exists_isSylowOf_jZeroLayer_yamadaR₂ d hlay
  have hV₁B : yamadaV₁ d t ≤ (jZeroLayer d ⊓ yamadaL₂ d t) ⊓
      centralizer ((jZeroLayer d ⊓ yamadaL₂ d t : Subgroup G) : Set G) := by
    refine le_inf (le_inf ?_ (h.yamadaV₁_le_yamadaL₂ d)) ?_
    · rw [hV]
      exact inf_le_left.trans hX.le
    · rw [hV]
      exact fun z hz => mem_centralizer_iff.2 fun b hb =>
        mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 b (hBX hb)
  have hvB : ((d.v : L) : G) ∈
      normalizer ((jZeroLayer d ⊓ yamadaL₂ d t : Subgroup G) : Set G) :=
    mem_normalizer_inf_D4 (v_mem_normalizer_jZeroLayer d) (h.v_mem_normalizer_yamadaL₂ d)
  have hvZ := mem_normalizer_inf_D4 hvB (mem_normalizer_centralizer_D4 hvB)
  refine sup_le hV₁B ?_
  rintro _ ⟨z, hz, rfl⟩
  exact (mem_normalizer_iff.1 hvZ z).1 (hV₁B hz)

omit [Finite G] in
theorem yamadaV₁_le_yamadaY₂ {q : ℕ} (d : TrialityD4Data L q) : yamadaV₁ d t ≤ yamadaY₂ d t :=
  le_sup_left

omit [Finite G] in
theorem yamadaV₁_conj_le_yamadaY₂ {q : ℕ} (d : TrialityD4Data L q) :
    (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom ≤ yamadaY₂ d t :=
  le_sup_right

theorem mul_comm_of_mem_yamadaY₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {a b : G}
    (ha : a ∈ yamadaY₂ d t) (hb : b ∈ yamadaY₂ d t) : a * b = b * a :=
  (mem_centralizer_iff.1 (Subgroup.mem_inf.1 (h.yamadaY₂_le_center d hlay ha)).2 b
    (Subgroup.mem_inf.1 (h.yamadaY₂_le_center d hlay hb)).1).symm

theorem yamadaY₂_le_centralizer_yamadaV₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaY₂ d t ≤ centralizer (yamadaV₁ d t : Set G) := fun _ hy =>
  mem_centralizer_iff.2 fun _ hw =>
    h.mul_comm_of_mem_yamadaY₂ d hlay (yamadaV₁_le_yamadaY₂ d hw) hy

theorem coe_yamadaY₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    ((yamadaY₂ d t : Subgroup G) : Set G) = (yamadaV₁ d t : Set G) *
      ((yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom : Set G) :=
  coe_mul_of_right_le_normalizer_left _ _ fun _ hy => Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun _ hw =>
      h.mul_comm_of_mem_yamadaY₂ d hlay (yamadaV₁_le_yamadaY₂ d hw)
        (yamadaV₁_conj_le_yamadaY₂ d hy))

omit [Finite G] in
theorem mem_U₅_of_mem_V_map_conj {q : ℕ} (d : TrialityD4Data L q) {y : G}
    (hy : y ∈ (d.V.map L.subtype).map (MulAut.conj ((d.v : L) : G)).toMonoidHom) :
    y ∈ d.U₅.map L.subtype := by
  obtain ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, rfl⟩ := hy
  refine ⟨d.x₅ a, d.x₅_mem_U₅ a, ?_⟩
  rw [← d.v_conj_x₆ a]
  simp

omit [Finite G] in
theorem V_map_inf_U₅_map {q : ℕ} (d : TrialityD4Data L q) :
    d.V.map L.subtype ⊓ d.U₅.map L.subtype = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨_, ⟨a, rfl⟩, rfl⟩, ⟨_, ⟨b, rfl⟩, hb⟩⟩
  have e : d.x₅ b * d.x₆ 0 = d.x₅ 0 * d.x₆ a := by
    rw [d.x₆_zero, d.x₅_zero, mul_one, one_mul]
    exact Subtype.ext hb
  obtain ⟨-, ha⟩ := d.x₅_mul_x₆_inj e
  rw [mem_bot, ← ha, d.x₆_zero, map_one]

theorem t_mem_normalizer_yamadaV₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    t ∈ normalizer (yamadaV₁ d t : Set G) :=
  normalizer_yamadaD₁_le_normalizer_yamadaV₁_D1 d (h.t_mem_normalizer_yamadaD₁_D1 d)

theorem t_mem_normalizer_yamadaV₁_conj (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    t ∈ normalizer (((yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom :
      Subgroup G) : Set G) :=
  mem_normalizer_map_conj_D4 (h.t_mem_normalizer_yamadaV₁ d) (h.v_mul_t d)

theorem V_map_le_yamadaV₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    d.V.map L.subtype ≤ yamadaV₁ d t := by
  rw [← (h.yamada_5_6_2 d hlay).2.2.1]
  exact inf_le_left

theorem mem_U₅_of_mem_yamadaV₁_conj (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {y : G}
    (hy : y ∈ (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom)
    (hyt : t * y = y * t) : y ∈ d.U₅.map L.subtype := by
  have hvt := h.v_mul_t d
  apply mem_U₅_of_mem_V_map_conj d
  rw [mem_map_conj_iff_D4] at hy ⊢
  rw [← (h.yamada_5_6_2 d hlay).2.2.1]
  refine Subgroup.mem_inf.2 ⟨hy, mem_centralizer_singleton_iff.2 ?_⟩
  calc ((d.v : L) : G)⁻¹ * y * (d.v : G) * t = ((d.v : L) : G)⁻¹ * y * ((d.v : G) * t) := by
        group
    _ = ((d.v : L) : G)⁻¹ * y * (t * (d.v : G)) := by rw [hvt]
    _ = ((d.v : L) : G)⁻¹ * (y * t) * (d.v : G) := by group
    _ = ((d.v : L) : G)⁻¹ * (t * y) * (d.v : G) := by rw [hyt]
    _ = ((d.v : L) : G)⁻¹ * (t * (d.v : G)) * ((d.v : L) : G)⁻¹ * y * (d.v : G) := by group
    _ = ((d.v : L) : G)⁻¹ * ((d.v : G) * t) * ((d.v : L) : G)⁻¹ * y * (d.v : G) := by rw [hvt]
    _ = t * (((d.v : L) : G)⁻¹ * y * (d.v : G)) := by group

theorem yamadaV₁_inf_conj_v (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaV₁ d t ⊓ (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom = ⊥ := by
  have h562 := h.yamada_5_6_2 d hlay
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  have hfix : ∀ y ∈ yamadaV₁ d t, y ∈ (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom →
      t * y = y * t → y = 1 := by
    intro y hy hy' hyt
    have hyV : y ∈ d.V.map L.subtype := by
      rw [← h562.2.2.1]
      exact Subgroup.mem_inf.2 ⟨hy, mem_centralizer_singleton_iff.2 hyt.symm⟩
    have := (V_map_inf_U₅_map d).le (Subgroup.mem_inf.2
      ⟨hyV, h.mem_U₅_of_mem_yamadaV₁_conj d hlay hy' hyt⟩)
    exact (mem_bot.1 this)
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.1 hw
  have htw1 : t * w * t ∈ yamadaV₁ d t := by
    have := (mem_normalizer_iff.1 (h.t_mem_normalizer_yamadaV₁ d) w).1 hw1
    rwa [htinv] at this
  have htw2 : t * w * t ∈ (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom := by
    have := (mem_normalizer_iff.1 (h.t_mem_normalizer_yamadaV₁_conj d) w).1 hw2
    rwa [htinv] at this
  have hcomm : w * (t * w * t) = t * w * t * w :=
    mem_centralizer_iff.1 (Subgroup.mem_inf.1 htw1).2 w (Subgroup.mem_inf.1 hw1).1
  have h1 : w * (t * w * t) = 1 := by
    refine hfix _ (mul_mem hw1 htw1) (mul_mem hw2 htw2) ?_
    calc t * (w * (t * w * t)) = t * w * t * w * t := by group
      _ = w * (t * w * t) * t := by rw [← hcomm]
  have hw2' : w * w = 1 := by
    have := h562.1.2 w hw1
    rwa [sq] at this
  have h2 : t * w * t = w := by
    calc t * w * t = (w * w) * (t * w * t) := by rw [hw2', one_mul]
      _ = w * (w * (t * w * t)) := by group
      _ = w := by rw [h1, mul_one]
  rw [mem_bot]
  refine hfix w hw1 hw2 ?_
  calc t * w = t * w * t * t := by rw [mul_assoc (t * w), h.t_mul_t, mul_one]
    _ = w * t := by rw [h2]

theorem Y_map_le_yamadaY₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    d.Y.map L.subtype ≤ yamadaY₂ d t := by
  have hVV₁ := h.V_map_le_yamadaV₁ d hlay
  show (d.U₅ ⊔ d.V).map L.subtype ≤ _
  rw [Subgroup.map_sup]
  refine sup_le ?_ (hVV₁.trans le_sup_left)
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  refine le_sup_right (a := yamadaV₁ d t) ⟨_, hVV₁ ⟨d.x₆ a, d.x₆_mem_V a, rfl⟩, ?_⟩
  rw [← d.v_conj_x₆ a]
  simp

theorem card_yamadaY₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    Nat.card (yamadaY₂ d t) = (2 ^ f) ^ 4 := by
  have h1 := ncard_mul_mul_card_inf (yamadaV₁ d t)
    ((yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom)
  rw [h.yamadaV₁_inf_conj_v d hlay, card_bot, mul_one, ← h.coe_yamadaY₂ d hlay,
    ← Nat.card_coe_set_eq, card_map_of_injective (MulAut.conj _).injective,
    (h.yamada_5_6_2 d hlay).2.1] at h1
  exact h1.trans (by ring)

theorem yamadaY₂_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaY₂ d t = jZeroLayer d ⊓ yamadaL₂ d t :=
  eq_of_le_of_card_ge ((h.yamadaY₂_le_center d hlay).trans inf_le_left)
    (by rw [h.card_jZeroLayer_inf_yamadaL₂ d hlay, h.card_yamadaY₂ d hlay])

theorem yamadaY₂_inf_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaY₂ d t ⊓ centralizer ({t} : Set G) = d.Y.map L.subtype := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  refine le_antisymm (fun z hz => ?_) (le_inf (h.Y_map_le_yamadaY₂ d hlay)
    ((map_subtype_le _).trans h.L_le_centralizer))
  obtain ⟨hzY, hzt⟩ := Subgroup.mem_inf.1 hz
  have hzY' : z ∈ ((yamadaY₂ d t : Subgroup G) : Set G) := hzY
  rw [h.coe_yamadaY₂ d hlay] at hzY'
  obtain ⟨w, hw, w', hw', hz'⟩ := hzY'
  have hz'' : w * w' = z := hz'
  subst hz''
  have htw : t * w * t ∈ yamadaV₁ d t := by
    have := (mem_normalizer_iff.1 (h.t_mem_normalizer_yamadaV₁ d) w).1 hw
    rwa [htinv] at this
  have htw' : t * w' * t ∈ (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom := by
    have := (mem_normalizer_iff.1 (h.t_mem_normalizer_yamadaV₁_conj d) w').1 hw'
    rwa [htinv] at this
  have hfix : (t * w * t) * (t * w' * t) = w * w' := by
    have e := mem_centralizer_singleton_iff.1 hzt
    calc (t * w * t) * (t * w' * t) = t * (w * w') * t := by
          rw [show t * w * t * (t * w' * t) = t * w * (t * t) * w' * t by group, h.t_mul_t,
            mul_one]
          group
      _ = w * w' * t * t := by rw [← e]
      _ = w * w' := by rw [mul_assoc (w * w'), h.t_mul_t, mul_one]
  have hinf : w⁻¹ * (t * w * t) = w' * (t * w' * t)⁻¹ := by
    calc w⁻¹ * (t * w * t) = w⁻¹ * ((t * w * t) * (t * w' * t)) * (t * w' * t)⁻¹ := by group
      _ = w⁻¹ * (w * w') * (t * w' * t)⁻¹ := by rw [hfix]
      _ = w' * (t * w' * t)⁻¹ := by group
  have h1 : w⁻¹ * (t * w * t) = 1 := by
    have := (h.yamadaV₁_inf_conj_v d hlay).le (Subgroup.mem_inf.2
      ⟨mul_mem (inv_mem hw) htw, hinf ▸ mul_mem hw' (inv_mem htw')⟩)
    exact mem_bot.1 this
  have h2 : t * w * t = w := by
    rw [← mul_left_cancel_iff (a := w⁻¹), h1, inv_mul_cancel]
  have h3 : t * w' * t = w' := by
    have : w' * (t * w' * t)⁻¹ = 1 := hinf ▸ h1
    rw [mul_inv_eq_one] at this
    exact this.symm
  have hwt : t * w = w * t := by
    calc t * w = t * w * t * t := by rw [mul_assoc (t * w), h.t_mul_t, mul_one]
      _ = w * t := by rw [h2]
  have hw't : t * w' = w' * t := by
    calc t * w' = t * w' * t * t := by rw [mul_assoc (t * w'), h.t_mul_t, mul_one]
      _ = w' * t := by rw [h3]
  have hwV : w ∈ d.V.map L.subtype := by
    rw [← (h.yamada_5_6_2 d hlay).2.2.1]
    exact Subgroup.mem_inf.2 ⟨hw, mem_centralizer_singleton_iff.2 hwt.symm⟩
  have hw'U : w' ∈ d.U₅.map L.subtype := h.mem_U₅_of_mem_yamadaV₁_conj d hlay hw' hw't
  show w * w' ∈ (d.U₅ ⊔ d.V).map L.subtype
  rw [Subgroup.map_sup]
  exact mul_mem (mem_sup_right hwV) (mem_sup_left hw'U)

theorem M_map_le_centralizer_yamadaY₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    d.M.map L.subtype ≤ centralizer (yamadaY₂ d t : Set G) := by
  have hMV : d.M.map L.subtype ≤ centralizer (yamadaV₁ d t : Set G) :=
    (map_mono d.M_le_S).trans (h.S_map_le_centralizer_yamadaV₁ d hlay)
  refine le_centralizer_iff.2 (sup_le (le_centralizer_iff.1 hMV) ?_)
  rintro _ ⟨w, hw, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨m, hm, rfl⟩
  have hm' : ((d.v⁻¹ * m * d.v : L) : G) ∈ d.M.map L.subtype :=
    ⟨_, (mem_normalizer_iff''.1 d.v_mem_normalizer_M m).1 hm, rfl⟩
  have hc : w * ((d.v⁻¹ * m * d.v : L) : G) = ((d.v⁻¹ * m * d.v : L) : G) * w :=
    mem_centralizer_iff.1 (hMV hm') w hw
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
  calc (m : G) * ((d.v : G) * w * ((d.v : L) : G)⁻¹) =
      (d.v : G) * (((d.v : L) : G)⁻¹ * m * (d.v : G) * w) * ((d.v : L) : G)⁻¹ := by group
    _ = (d.v : G) * (w * (((d.v : L) : G)⁻¹ * m * (d.v : G))) * ((d.v : L) : G)⁻¹ := by rw [hc]
    _ = (d.v : G) * w * ((d.v : L) : G)⁻¹ * m := by group

theorem yamadaM₂_inf_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaM₂ d t ⊓ centralizer (yamadaM₂ d t : Set G) = yamadaY₂ d t := by
  have hMY := h.M_map_le_centralizer_yamadaY₂ d hlay
  have hYY : yamadaY₂ d t ≤ centralizer (yamadaY₂ d t : Set G) := fun _ ha =>
    mem_centralizer_iff.2 fun _ hb => h.mul_comm_of_mem_yamadaY₂ d hlay hb ha
  have hYc : yamadaY₂ d t ≤ centralizer (yamadaM₂ d t : Set G) :=
    le_centralizer_iff.1 (sup_le hMY hYY)
  refine le_antisymm (fun z hz => ?_) (le_inf le_sup_right hYc)
  obtain ⟨hzM, hzc⟩ := Subgroup.mem_inf.1 hz
  have hzM' : z ∈ ((d.M.map L.subtype ⊔ yamadaY₂ d t : Subgroup G) : Set G) := hzM
  rw [coe_mul_of_right_le_normalizer_left _ _
    ((le_centralizer_iff.1 hMY).trans (Subgroup.centralizer_le_normalizer _))] at hzM'
  obtain ⟨m, hm, y, hy, hmy⟩ := hzM'
  have hmy' : m * y = z := hmy
  have hmc : m ∈ centralizer (yamadaM₂ d t : Set G) := by
    have e : m = z * y⁻¹ := by rw [← hmy', mul_inv_cancel_right]
    rw [e]
    exact mul_mem hzc (inv_mem (hYc hy))
  have hmY : m ∈ d.Y.map L.subtype := by
    rw [← map_inf_centralizer_map d.M_inf_centralizer_M]
    exact Subgroup.mem_inf.2 ⟨hm, mem_centralizer_iff.2 fun x hx =>
      mem_centralizer_iff.1 hmc x (le_sup_left (a := d.M.map L.subtype) hx)⟩
  rw [← hmy']
  exact mul_mem (h.Y_map_le_yamadaY₂ d hlay hmY) hy

theorem t_not_mem_centralizer_yamadaV₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    t ∉ centralizer (yamadaV₁ d t : Set G) := by
  intro ht
  have h562 := h.yamada_5_6_2 d hlay
  have hle : yamadaV₁ d t ≤ centralizer ({t} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht w hw)
  have e := h562.2.2.1
  rw [inf_eq_left.2 hle] at e
  have hc := h562.2.1
  rw [e, card_map_of_injective L.subtype_injective, d.card_V] at hc
  have hq : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h.one_le)
  nlinarith

theorem yamadaM₂_le_centralizer_yamadaV₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaM₂ d t ≤ centralizer (yamadaV₁ d t : Set G) :=
  sup_le ((map_mono d.M_le_S).trans (h.S_map_le_centralizer_yamadaV₁ d hlay))
    (h.yamadaY₂_le_centralizer_yamadaV₁ d hlay)

theorem yamadaS₂_le_centralizer_yamadaV₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaS₂ d t ≤ centralizer (yamadaV₁ d t : Set G) :=
  sup_le (h.S_map_le_centralizer_yamadaV₁ d hlay) (h.yamadaY₂_le_centralizer_yamadaV₁ d hlay)

theorem t_mem_normalizer_yamadaY₂_D1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    t ∈ normalizer (yamadaY₂ d t : Set G) :=
  mem_normalizer_sup (h.t_mem_normalizer_yamadaV₁ d) (h.t_mem_normalizer_yamadaV₁_conj d)

theorem yamadaY₂_le_yamadaL₂_D1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaY₂ d t ≤ yamadaL₂ d t := by
  rw [h.yamadaY₂_eq d hlay]
  exact inf_le_right

theorem S_map_le_normalizer_yamadaY₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    d.S.map L.subtype ≤ normalizer (yamadaY₂ d t : Set G) := by
  have hMY := h.M_map_le_centralizer_yamadaY₂ d hlay
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff_x₂.1 hs
  rw [map_mul]
  refine mul_mem ?_ (Subgroup.centralizer_le_normalizer _ (hMY ⟨n, hn, rfl⟩))
  rw [h.yamadaY₂_eq d hlay]
  exact mem_normalizer_inf_D4
    (le_normalizer_jZeroLayer d (coe_mem_centralizer_of_mem (d.x₂_mem_centralizer_J₀ a)))
    (le_normalizer_yamadaL₂ d t (h.S_le_normalizer_tY d ⟨_, d.D_le_S (d.x₂_mem_D a), rfl⟩))

theorem map_inf_yamadaY₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {E : Subgroup L}
    (hYE : d.Y ≤ E) : E.map L.subtype ⊓ yamadaY₂ d t = d.Y.map L.subtype := by
  refine le_antisymm ?_ (le_inf (map_mono hYE) (h.Y_map_le_yamadaY₂ d hlay))
  rw [← h.yamadaY₂_inf_centralizer d hlay]
  exact le_inf inf_le_right (inf_le_left.trans ((map_subtype_le _).trans h.L_le_centralizer))

theorem card_yamadaL₂_and (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    Nat.card (yamadaL₂ d t) = 2 * (2 ^ f) ^ 13 ∧ Nat.card (yamadaR₂ d t) = 2 * (2 ^ f) ^ 14 := by
  have h1 := Subgroup.relIndex_mul_card (d.M.map L.subtype ⊔ zpowers t) (yamadaL₂ d t)
  rw [inf_eq_left.2 (h.tM_le_yamadaL₂ d), h.relIndex_tM_yamadaL₂ d,
    h.card_sup_zpowers (map_subtype_le _), card_map_of_injective L.subtype_injective,
    d.card_M] at h1
  have h2 := Subgroup.relIndex_mul_card (d.M.map L.subtype ⊔ zpowers t) (yamadaR₂ d t)
  have e : (d.M.map L.subtype ⊔ zpowers t) ⊓ yamadaR₂ d t = d.M.map L.subtype ⊔ zpowers t :=
    inf_eq_left.2 ((h.tM_le_yamadaL₂ d).trans le_sup_left)
  rw [e, h.relIndex_tM_yamadaR₂ d,
    h.card_sup_zpowers (map_subtype_le _), card_map_of_injective L.subtype_injective,
    d.card_M] at h2
  exact ⟨by rw [← h1]; ring, by rw [← h2]; ring⟩

theorem card_yamadaM₂_and (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    Nat.card (yamadaM₂ d t) = (2 ^ f) ^ 13 ∧ Nat.card (yamadaS₂ d t) = (2 ^ f) ^ 14 := by
  have hMN : yamadaY₂ d t ≤ normalizer ((d.M.map L.subtype : Subgroup G) : Set G) :=
    (le_centralizer_iff.1 (h.M_map_le_centralizer_yamadaY₂ d hlay)).trans
      (Subgroup.centralizer_le_normalizer _)
  have h1 := ncard_mul_mul_card_inf (d.M.map L.subtype) (yamadaY₂ d t)
  rw [h.map_inf_yamadaY₂ d hlay (d.Y_le_W.trans (d.W_le_F.trans d.F_le_M)),
    ← coe_mul_of_right_le_normalizer_left _ _ hMN, ← Nat.card_coe_set_eq,
    card_map_of_injective L.subtype_injective, card_map_of_injective L.subtype_injective,
    d.card_M, d.card_Y, h.card_yamadaY₂ d hlay] at h1
  have h2 := ncard_mul_mul_card_inf (d.S.map L.subtype) (yamadaY₂ d t)
  rw [h.map_inf_yamadaY₂ d hlay (d.Y_le_W.trans (d.W_le_F.trans (d.F_le_D.trans d.D_le_S))),
    ← coe_mul_of_left_le_normalizer_right _ _ (h.S_map_le_normalizer_yamadaY₂ d hlay),
    ← Nat.card_coe_set_eq, card_map_of_injective L.subtype_injective,
    card_map_of_injective L.subtype_injective, d.card_S, d.card_Y,
    h.card_yamadaY₂ d hlay] at h2
  have hpos : 0 < (2 ^ f) ^ 2 := by positivity
  exact ⟨Nat.eq_of_mul_eq_mul_right hpos (h1.trans (by ring)),
    Nat.eq_of_mul_eq_mul_right hpos (h2.trans (by ring))⟩

theorem yamada_5_9_1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaL₂ d t = yamadaM₂ d t ⊔ zpowers t ∧ t ∉ yamadaM₂ d t ∧
      yamadaR₂ d t = yamadaS₂ d t ⊔ zpowers t ∧ t ∉ yamadaS₂ d t := by
  have htV := h.t_not_mem_centralizer_yamadaV₁ d hlay
  have htM : t ∉ yamadaM₂ d t := fun ht => htV (h.yamadaM₂_le_centralizer_yamadaV₁ d hlay ht)
  have htS : t ∉ yamadaS₂ d t := fun ht => htV (h.yamadaS₂_le_centralizer_yamadaV₁ d hlay ht)
  have hY₂L₂ := h.yamadaY₂_le_yamadaL₂_D1 d hlay
  have htNY := h.t_mem_normalizer_yamadaY₂_D1 d
  obtain ⟨hcL, hcR⟩ := h.card_yamadaL₂_and d
  obtain ⟨hcM, hcS⟩ := h.card_yamadaM₂_and d hlay
  have hML : yamadaM₂ d t ⊔ zpowers t ≤ yamadaL₂ d t :=
    sup_le (sup_le (le_sup_left.trans (h.tM_le_yamadaL₂ d)) hY₂L₂)
      ((zpowers_le).2 (h.t_mem_yamadaL₂ d))
  have hSR : yamadaS₂ d t ⊔ zpowers t ≤ yamadaR₂ d t :=
    sup_le (sup_le le_sup_right (hY₂L₂.trans le_sup_left))
      ((zpowers_le).2 (le_sup_left (a := yamadaL₂ d t) (h.t_mem_yamadaL₂ d)))
  refine ⟨(eq_of_le_of_card_ge hML ?_).symm, htM, (eq_of_le_of_card_ge hSR ?_).symm, htS⟩
  · rw [h.card_sup_zpowers_of_not_mem (A := yamadaM₂ d t)
      (mem_normalizer_sup (h.t_mem_normalizer_map_D1 d.M) htNY) htM, hcL, hcM]
  · rw [h.card_sup_zpowers_of_not_mem (A := yamadaS₂ d t)
      (mem_normalizer_sup (h.t_mem_normalizer_map_D1 d.S) htNY) htS, hcR, hcS]

theorem yamada_5_9_2 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaV₁ d t ⊓ (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom = ⊥ ∧
      Nat.card (yamadaY₂ d t) = (2 ^ f) ^ 4 ∧ IsMulCommutative (yamadaY₂ d t) ∧
      yamadaM₂ d t ⊓ centralizer (yamadaM₂ d t : Set G) = yamadaY₂ d t ∧
      yamadaY₂ d t ⊓ centralizer ({t} : Set G) = d.Y.map L.subtype :=
  ⟨h.yamadaV₁_inf_conj_v d hlay, h.card_yamadaY₂ d hlay,
    ⟨⟨fun a b => Subtype.ext (h.mul_comm_of_mem_yamadaY₂ d hlay a.2 b.2)⟩⟩,
    h.yamadaM₂_inf_centralizer d hlay, h.yamadaY₂_inf_centralizer d hlay⟩

theorem commutator_mem_yamadaV₁_of_mem_yamadaY₂ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {y s : G}
    (hy : y ∈ yamadaY₂ d t) (hs : s ∈ d.S.map L.subtype) : y * s * y⁻¹ * s⁻¹ ∈ yamadaV₁ d t := by
  obtain ⟨X, -, hV, hPX, hBX, hsq⟩ := h.exists_isSylowOf_jZeroLayer_yamadaR₂ d hlay
  have hMY := h.M_map_le_centralizer_yamadaY₂ d hlay
  have hyX : y ∈ X := hBX ((h.yamadaY₂_eq d hlay) ▸ hy)
  obtain ⟨s', hs', rfl⟩ := hs
  obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff_x₂.1 hs'
  have hx₂ : ((d.x₂ a : L) : G) ∈ X :=
    hPX ⟨_, d.mem_sylowJ₀_iff.2 ⟨a, 0, 0, by rw [d.x₅_zero, d.x₆_zero, mul_one, mul_one]⟩, rfl⟩
  have hny : y * (n : G) = n * y := mem_centralizer_iff.1 (hMY ⟨n, hn, rfl⟩) y hy
  have hny' : (n : G) * y⁻¹ = y⁻¹ * n := by
    calc (n : G) * y⁻¹ = y⁻¹ * (y * n) * y⁻¹ := by group
      _ = y⁻¹ * (n * y) * y⁻¹ := by rw [hny]
      _ = y⁻¹ * n := by group
  have e : y * L.subtype (d.x₂ a * n) * y⁻¹ * (L.subtype (d.x₂ a * n))⁻¹ =
      y * (d.x₂ a : G) * y⁻¹ * ((d.x₂ a : L) : G)⁻¹ := by
    rw [map_mul, Subgroup.coe_subtype]
    calc y * ((d.x₂ a : G) * n) * y⁻¹ * ((d.x₂ a : G) * n)⁻¹ =
        y * (d.x₂ a : G) * ((n : G) * y⁻¹) * (n : G)⁻¹ * ((d.x₂ a : L) : G)⁻¹ := by group
      _ = y * (d.x₂ a : G) * (y⁻¹ * n) * (n : G)⁻¹ * ((d.x₂ a : L) : G)⁻¹ := by rw [hny']
      _ = y * (d.x₂ a : G) * y⁻¹ * ((d.x₂ a : L) : G)⁻¹ := by group
  rw [e]
  exact commutator_mem_of_mul_self_mem_D4 (hV.le.trans inf_le_right) hsq hyX hx₂

theorem yamadaR₂_inf_normalizer_S_le (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaR₂ d t ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ≤ yamadaR₁ d t := by
  have hR := yamadaR_eq_of_eq d (h.centralizer_L_inf_of_data d)
  have hYS : d.Y.map L.subtype ⊔ zpowers t ≤ d.S.map L.subtype ⊔ zpowers t :=
    sup_le_sup_right (map_mono (d.Y_le_W.trans (d.W_le_F.trans (d.F_le_D.trans d.D_le_S)))) _
  have hRR₁ : d.S.map L.subtype ⊔ zpowers t ≤ yamadaR₁ d t :=
    sup_le le_sup_right ((zpowers_le).2 (le_sup_left (a := yamadaC₁ d t) (h.t_mem_yamadaC₁_D1 d)))
  intro n hn
  obtain ⟨hnR₂, hnS⟩ := Subgroup.mem_inf.1 hn
  have hle : d.S.map L.subtype ⊔ zpowers t ≤
      (d.S.map L.subtype ⊔ zpowers t).comap (MulAut.conj n).toMonoidHom := by
    refine sup_le (fun s hs => ?_) ((zpowers_le).2 ?_)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mem_sup_left ((mem_normalizer_iff.1 hnS s).1 hs)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hYS ((mem_normalizer_iff.1 (h.yamadaR₂_le_normalizer_tY d hnR₂) t).1
        (mem_sup_right (mem_zpowers t)))
  have hnR : n ∈ ((normalizer (yamadaR d t : Set G) : Subgroup G) : Set G) := by
    rw [SetLike.mem_coe, hR]
    refine mem_normalizer_fintype fun x hx => ?_
    have := hle hx
    rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  rw [(h.yamada_5_3_3_all d).2.1] at hnR
  obtain ⟨c, hc, x, hx, hcx⟩ := hnR
  have hcx' : c * x = n := hcx
  have hxR₂ : x ∈ yamadaR₂ d t := by
    have e : x = c⁻¹ * n := by rw [← hcx', inv_mul_cancel_left]
    rw [e]
    exact mul_mem (inv_mem (h.yamadaC₁_le_yamadaR₂ d hc)) hnR₂
  have hxR : x ∈ yamadaR d t := by
    rw [← h.yamadaR₂_inf_centralizer d]
    exact Subgroup.mem_inf.2 ⟨hxR₂, (Subgroup.mem_inf.1 hx).1⟩
  rw [hR] at hxR
  rw [← hcx']
  exact mul_mem (le_sup_left (a := yamadaC₁ d t) hc) (hRR₁ hxR)

theorem yamadaR₁_eq_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaR₁ d t = yamadaS₁ d t ⊔ zpowers t := by
  have hC := (h.yamada_5_6_1 d hlay).1
  apply le_antisymm
  · refine sup_le ?_ ((le_sup_left : d.S.map L.subtype ≤ yamadaS₁ d t).trans le_sup_left)
    rw [hC]
    exact sup_le_sup_right le_sup_right _
  · exact sup_le (sup_le le_sup_right ((h.yamadaD₁_le_yamadaC₁_D1 d).trans le_sup_left))
      ((zpowers_le).2 (le_sup_left (a := yamadaC₁ d t) (h.t_mem_yamadaC₁_D1 d)))

theorem yamadaS₂_inf_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaS₂ d t ⊓ centralizer (yamadaS₂ d t : Set G) = yamadaV₁ d t := by
  have hV₁S₂ : yamadaV₁ d t ≤ yamadaS₂ d t := (yamadaV₁_le_yamadaY₂ d).trans le_sup_right
  have hV₁c : yamadaV₁ d t ≤ centralizer (yamadaS₂ d t : Set G) :=
    le_centralizer_iff.1 (h.yamadaS₂_le_centralizer_yamadaV₁ d hlay)
  refine le_antisymm (fun z hz => ?_) (le_inf hV₁S₂ hV₁c)
  obtain ⟨hzS, hzc⟩ := Subgroup.mem_inf.1 hz
  have hzN : z ∈ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun s hs =>
      mem_centralizer_iff.1 hzc s (le_sup_left (a := d.S.map L.subtype) hs))
  have hS₂R₂ : yamadaS₂ d t ≤ yamadaR₂ d t :=
    sup_le le_sup_right ((h.yamadaY₂_le_yamadaL₂_D1 d hlay).trans le_sup_left)
  have hzR₁ := h.yamadaR₂_inf_normalizer_S_le d (Subgroup.mem_inf.2 ⟨hS₂R₂ hzS, hzN⟩)
  have htS₁ : t ∈ normalizer (yamadaS₁ d t : Set G) :=
    mem_normalizer_sup (h.t_mem_normalizer_map_D1 d.S) (h.t_mem_normalizer_yamadaD₁_D1 d)
  rw [h.yamadaR₁_eq_sup d hlay, h.mem_sup_zpowers_iff_of_normalizer htS₁] at hzR₁
  have hS₁S₂ : yamadaS₁ d t ≤ yamadaS₂ d t := by
    rw [h.yamadaS₁_eq_sup d hlay]
    exact sup_le le_sup_left hV₁S₂
  rcases hzR₁ with h1 | h1
  · rw [← h.yamada_5_7 d hlay]
    exact Subgroup.mem_inf.2 ⟨h1, mem_centralizer_iff.2 fun y hy =>
      mem_centralizer_iff.1 hzc y (hS₁S₂ hy)⟩
  · exfalso
    apply (h.yamada_5_9_1 d hlay).2.2.2
    have := mul_mem (hS₁S₂ h1) (inv_mem hzS)
    rwa [mul_inv_cancel_right] at this

theorem mem_yamadaY₂_iff (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} :
    x ∈ yamadaY₂ d t ↔ x ∈ yamadaS₂ d t ∧ ∀ y ∈ yamadaS₂ d t, ⁅x, y⁆ ∈ yamadaV₁ d t := by
  have hset : ((yamadaS₂ d t : Subgroup G) : Set G) =
      ((d.S.map L.subtype : Subgroup G) : Set G) * (yamadaY₂ d t : Set G) :=
    coe_mul_of_left_le_normalizer_right _ _ (h.S_map_le_normalizer_yamadaY₂ d hlay)
  constructor
  · intro hx
    refine ⟨le_sup_right (a := d.S.map L.subtype) hx, fun y hy => ?_⟩
    have hy' : y ∈ ((yamadaS₂ d t : Subgroup G) : Set G) := hy
    rw [hset] at hy'
    obtain ⟨s, hs, y', hy', e⟩ := hy'
    have e' : s * y' = y := e
    subst e'
    have hxy' : y' * x⁻¹ = x⁻¹ * y' := by
      have h1 := h.mul_comm_of_mem_yamadaY₂ d hlay hx hy'
      calc y' * x⁻¹ = x⁻¹ * (x * y') * x⁻¹ := by group
        _ = x⁻¹ * (y' * x) * x⁻¹ := by rw [h1]
        _ = x⁻¹ * y' := by group
    rw [commutatorElement_def]
    have e2 : x * (s * y') * x⁻¹ * (s * y')⁻¹ = x * s * x⁻¹ * s⁻¹ := by
      calc x * (s * y') * x⁻¹ * (s * y')⁻¹ = x * s * (y' * x⁻¹) * y'⁻¹ * s⁻¹ := by group
        _ = x * s * (x⁻¹ * y') * y'⁻¹ * s⁻¹ := by rw [hxy']
        _ = x * s * x⁻¹ * s⁻¹ := by group
    rw [e2]
    exact h.commutator_mem_yamadaV₁_of_mem_yamadaY₂ d hlay hx hs
  · rintro ⟨hx, hc⟩
    have hx' : x ∈ ((yamadaS₂ d t : Subgroup G) : Set G) := hx
    rw [hset] at hx'
    obtain ⟨s, hs, y₀, hy₀, e⟩ := hx'
    have e' : s * y₀ = x := e
    subst e'
    obtain ⟨s₀, hs₀, hs₀e⟩ := hs
    have hs₀e' : (s₀ : G) = s := hs₀e
    subst hs₀e'
    have hSN : d.S.map L.subtype ≤ normalizer (yamadaV₁ d t : Set G) :=
      (h.S_map_le_centralizer_yamadaV₁ d hlay).trans (Subgroup.centralizer_le_normalizer _)
    have hs₀Y : s₀ ∈ d.Y := by
      refine d.mem_Y_iff_forall.2 ⟨hs₀, fun s' hs' => ?_⟩
      have h1 := hc (s' : G) (le_sup_left (a := d.S.map L.subtype) ⟨s', hs', rfl⟩)
      rw [commutatorElement_def] at h1
      have h2 := h.commutator_mem_yamadaV₁_of_mem_yamadaY₂ d hlay hy₀ ⟨s', hs', rfl⟩
      have h3 : (s₀ : G) * (y₀ * L.subtype s' * y₀⁻¹ * (L.subtype s')⁻¹) * (s₀ : G)⁻¹ ∈
          yamadaV₁ d t := (mem_normalizer_iff.1 (hSN ⟨s₀, hs₀, rfl⟩) _).1 h2
      have h4 : ((⁅s₀, s'⁆ : L) : G) ∈ yamadaV₁ d t := by
        have e3 : ((⁅s₀, s'⁆ : L) : G) =
            ((s₀ : G) * (y₀ * L.subtype s' * y₀⁻¹ * (L.subtype s')⁻¹) * (s₀ : G)⁻¹)⁻¹ *
              ((s₀ : G) * y₀ * L.subtype s' * ((s₀ : G) * y₀)⁻¹ * (L.subtype s')⁻¹) := by
          rw [commutatorElement_def]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype]
          group
        rw [e3]
        exact mul_mem (inv_mem h3) h1
      have h5 : ((⁅s₀, s'⁆ : L) : G) ∈ d.V.map L.subtype := by
        rw [← (h.yamada_5_6_2 d hlay).2.2.1]
        exact Subgroup.mem_inf.2 ⟨h4, h.L_le_centralizer (⁅s₀, s'⁆ : L).2⟩
      obtain ⟨v, hv, hv'⟩ := h5
      have e4 : v = ⁅s₀, s'⁆ := Subtype.ext hv'
      rw [← e4]
      exact hv
    exact mul_mem (h.Y_map_le_yamadaY₂ d hlay ⟨s₀, hs₀Y, rfl⟩) hy₀

theorem yamada_5_9_3 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    (Subgroup.upperCentralSeries (yamadaS₂ d t) 1).map (yamadaS₂ d t).subtype = yamadaV₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaS₂ d t) 2).map (yamadaS₂ d t).subtype = yamadaY₂ d t := by
  have h1 : (Subgroup.upperCentralSeries (yamadaS₂ d t) 1).map (yamadaS₂ d t).subtype =
      yamadaV₁ d t := map_upperCentralSeries_succ (map_upperCentralSeries_zero _) fun x => by
      rw [← h.yamadaS₂_inf_centralizer d hlay, mem_inf_centralizer_iff]
      simp only [mem_bot]
  exact ⟨h1, map_upperCentralSeries_succ h1 fun _ => h.mem_yamadaY₂_iff d hlay⟩

end Nine

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4

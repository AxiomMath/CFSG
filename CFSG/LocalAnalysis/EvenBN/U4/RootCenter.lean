module

public import CFSG.LocalAnalysis.EvenBN.U4.FusionOrbit
public import CFSG.LocalAnalysis.EvenBN.U4.Model.Centroid
public import CFSG.LocalAnalysis.EvenBN.U4.Model.AutCenter
public import CFSG.LocalAnalysis.EvenBN.U4.Prelim.Semilinear
public import CFSG.LocalAnalysis.EvenBN.Common.CosetFactorization
public import CFSG.LocalAnalysis.EvenBN.Common.Endgames

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common (CosetData RegularNormalData)
open scoped commutatorElement

section ModelFacts

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem mem_A2_of_mem_P_of_conj_mem_P {g : GL (Fin 4) K} (hg : g ∈ miyamotoP h)
    (hg' : (miyamotoR2 K)⁻¹ * g * miyamotoR2 K ∈ miyamotoP h) : g ∈ miyamotoA2 h := by
  obtain ⟨a, b, c, d, hb, hd, rfl⟩ := (mem_P h).1 hg
  obtain ⟨a', b', c', d', -, -, e⟩ := (mem_P h).1 hg'
  have e12 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 1 2) e
  simp [miyamotoR2, miyamotoX, Matrix.mul_apply, Fin.sum_univ_four] at e12
  exact (miyamotoXGL_mem_A2 h).2 ⟨e12, hd⟩

theorem row_zero_mul {A B : Matrix (Fin 4) (Fin 4) K} (hA : ∀ j, j ≠ 0 → A 0 j = 0)
    (hB : ∀ j, j ≠ 0 → B 0 j = 0) :
    (A * B) 0 0 = A 0 0 * B 0 0 ∧ ∀ j, j ≠ 0 → (A * B) 0 j = 0 := by
  have key : ∀ j, (A * B) 0 j = A 0 0 * B 0 j := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_four, hA 1 (by decide), hA 2 (by decide),
      hA 3 (by decide)]
    ring
  exact ⟨key 0, fun j hj => by rw [key, hB j hj, mul_zero]⟩

theorem miyamotoX_row_zero (a b c d : K) :
    miyamotoX h a b c d 0 0 = 1 ∧ ∀ j, j ≠ 0 → miyamotoX h a b c d 0 j = 0 := by
  refine ⟨rfl, fun j hj => ?_⟩
  fin_cases j
  · exact absurd rfl hj
  all_goals rfl

theorem diagonal_row_zero (v : Fin 4 → K) : ∀ j, j ≠ 0 → Matrix.diagonal v 0 j = 0 :=
  fun _ hj => Matrix.diagonal_apply_ne _ (Ne.symm hj)

theorem glAut_miyamotoI2Hom (φ : K ≃+* K) (b : Kˣ) :
    glAut φ (miyamotoI2Hom h b) = miyamotoI2Hom h (Units.map (φ : K →* K) b) := by
  apply Units.ext
  rw [coe_glAut_miyamotoI2Hom, coe_miyamotoI2Hom]
  rfl

theorem not_mem_A2_of_bar [CharP K 2] {a i n : GL (Fin 4) K} (ha : a ∈ miyamotoA2 h)
    (hi : i ∈ miyamotoI2 h) (hn : n ∈ miyamotoN2 h) {b : Kˣ} (hb : (b : K) * h.bar b = 1)
    (hb1 : b ≠ 1) :
    a * (i * n) * glAut (miyamotoBarEquiv h) (miyamotoI2Hom h b) * (a * (i * n))⁻¹ *
      (miyamotoI2Hom h b)⁻¹ ∉ miyamotoA2 h := by
  set b' : Kˣ := Units.map ((miyamotoBarEquiv h : K ≃+* K) : K →* K) b with hb'
  rw [glAut_miyamotoI2Hom]
  set D' := miyamotoI2Hom h b'
  have hc1 : i * D' = D' * i := miyamotoI2_commute' h hi ⟨b', rfl⟩
  have hc2 : n * D' = D' * n := (miyamotoI2_commute_N2 h ⟨b', rfl⟩ hn).symm
  have e : a * (i * n) * D' * (a * (i * n))⁻¹ * (miyamotoI2Hom h b)⁻¹ =
      a * D' * a⁻¹ * (miyamotoI2Hom h b)⁻¹ := by
    calc a * (i * n) * D' * (a * (i * n))⁻¹ * (miyamotoI2Hom h b)⁻¹
        = a * (i * (n * D')) * n⁻¹ * i⁻¹ * a⁻¹ * (miyamotoI2Hom h b)⁻¹ := by group
      _ = a * ((i * D') * n) * n⁻¹ * i⁻¹ * a⁻¹ * (miyamotoI2Hom h b)⁻¹ := by rw [hc2]; group
      _ = a * ((D' * i) * n) * n⁻¹ * i⁻¹ * a⁻¹ * (miyamotoI2Hom h b)⁻¹ := by rw [hc1]
      _ = a * D' * a⁻¹ * (miyamotoI2Hom h b)⁻¹ := by group
  rw [e]
  intro hmem
  obtain ⟨a₁, c₁, d₁, -, e₁⟩ := (mem_A2 h).1 hmem
  obtain ⟨a₀, c₀, d₀, -, rfl⟩ := (mem_A2 h).1 ha
  have e00 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 0 0) e₁
  rw [miyamotoXGL_inv h (map_zero _), ← map_inv] at e00
  simp only [Units.val_mul, coe_miyamotoXGL, D', coe_miyamotoI2Hom] at e00
  obtain ⟨r1, r1'⟩ := miyamotoX_row_zero h a₀ 0 c₀ d₀
  obtain ⟨r3, r3'⟩ := miyamotoX_row_zero h a₀ 0 (c₀ + 0 * a₀)
    (d₀ + a₀ * h.bar c₀ + h.bar a₀ * c₀)
  obtain ⟨s12, s12'⟩ := row_zero_mul r1' (diagonal_row_zero _)
  obtain ⟨s123, s123'⟩ := row_zero_mul s12' r3'
  obtain ⟨s1234, -⟩ := row_zero_mul s123' (diagonal_row_zero _)
  rw [s1234, s123, s12, r1, r3, (miyamotoX_row_zero h a₁ 0 c₁ d₁).1] at e00
  simp only [Matrix.diagonal_apply_eq, Matrix.cons_val_zero, one_mul, mul_one] at e00
  have hb0 : (b : K) ≠ 0 := b.ne_zero
  have hbar : h.bar (b : K) = (b : K)⁻¹ := eq_inv_of_mul_eq_one_right hb
  have hb'v : ((b' : Kˣ) : K) = (b : K)⁻¹ := by
    rw [hb', Units.coe_map]
    exact hbar
  rw [hb'v, Units.val_inv_eq_inv_val] at e00
  have h4 : (b : K) ^ 4 = 1 := by
    field_simp at e00
    linear_combination -e00
  exact hb1 (Units.ext (eq_one_of_pow_four_eq_one h4))

end ModelFacts

section Generic

variable {G : Type*} [Group G]

theorem mem_centralizer_sup {A B : Subgroup G} {x : G} (hA : x ∈ centralizer (A : Set G))
    (hB : x ∈ centralizer (B : Set G)) : x ∈ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hle : A ⊔ B ≤ centralizer ({x} : Set G) :=
    sup_le (fun a ha => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hA a ha))
      (fun b hb => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hB b hb))
  exact mem_centralizer_iff.2 fun y hy => mem_centralizer_singleton_iff.1 (hle hy)

theorem mem_normalizer_centralizer {A : Subgroup G} {g : G} (hg : g ∈ normalizer (A : Set G)) :
    g ∈ normalizer (centralizer (A : Set G) : Set G) := by
  have key : ∀ g' ∈ normalizer (A : Set G), ∀ k ∈ centralizer (A : Set G),
      g' * k * g'⁻¹ ∈ centralizer (A : Set G) := by
    intro g' hg' k hk
    refine mem_centralizer_iff.2 fun a ha => ?_
    have ha' : g'⁻¹ * a * g' ∈ A := by
      have := (mem_normalizer_iff.1 (inv_mem hg') a).1 ha
      rwa [inv_inv] at this
    have e := mem_centralizer_iff.1 hk _ ha'
    calc a * (g' * k * g'⁻¹) = g' * ((g'⁻¹ * a * g') * k) * g'⁻¹ := by group
      _ = g' * (k * (g'⁻¹ * a * g')) * g'⁻¹ := by rw [e]
      _ = g' * k * g'⁻¹ * a := by group
  rw [mem_normalizer_iff]
  intro k
  refine ⟨key g hg k, fun hk => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hk
  rwa [show g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ = k by group] at this

theorem mem_normalizer_zpowers_of_comm {t g : G} (hg : g * t = t * g) :
    g ∈ normalizer (zpowers t : Set G) := by
  refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun y hy => ?_)
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  exact (Commute.zpow_left (hg : Commute g t).symm k).eq

theorem le_normalizer_centerIn (H : Subgroup G) : H ≤ normalizer (CFSG.centerIn H : Set G) :=
  le_normalizer.trans (normalizer_le_normalizer_centerIn H)

theorem le_centralizer_centerIn (H : Subgroup G) : H ≤ centralizer (CFSG.centerIn H : Set G) :=
  fun x hx => mem_centralizer_iff.2 fun _ hz => (mem_centralizer_iff.1 hz.2 x hx).symm

end Generic

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem ZP_le_L (_hS : Setting h L η t Q T) : miyamotoZG h L η ≤ L :=
  miyamotoPull_le h L η _

theorem ZP_le_A2 (_hS : Setting h L η t Q T) : miyamotoZG h L η ≤ miyamotoA2G h L η := by
  have : CharP K 2 := h.charP
  exact miyamotoPull_mono h L η ((miyamotoZ_le_Z2 h).trans (miyamotoZ2_le_A2 h))

theorem ZP_le_A1 (_hS : Setting h L η t Q T) : miyamotoZG h L η ≤ miyamotoA1G h L η := by
  have : CharP K 2 := h.charP
  exact miyamotoPull_mono h L η ((miyamotoZ_le_Z2 h).trans (miyamotoZ2_le_A1 h))

theorem isElementaryAbelian_ZP (_hS : Setting h L η t Q T) :
    CFSG.IsElementaryAbelian 2 (miyamotoZG h L η) := by
  have : CharP K 2 := h.charP
  have := isElementaryAbelian_miyamotoZ h
  exact isElementaryAbelian_miyamotoPull h L η

theorem ZP_le_centralizer_t (hS : Setting h L η t Q T) :
    miyamotoZG h L η ≤ centralizer ({t} : Set G) :=
  hS.ZP_le_L.trans hS.L_le_centralizer

theorem t_not_mem_ZP (hS : Setting h L η t Q T) : t ∉ miyamotoZG h L η :=
  fun ht => hS.t_not_mem_L (hS.ZP_le_L ht)

theorem card_ZP (_hS : Setting h L η t Q T) : Nat.card (miyamotoZG h L η) = 2 ^ f :=
  card_miyamotoZG h L η

theorem centerIn_Q' (hS : Setting h L η t Q T) :
    CFSG.centerIn Q = miyamotoZG h L η ⊔ zpowers t := by
  rw [hS.centerIn_Q, sup_comm]

theorem ZP_le_centerIn_Q (hS : Setting h L η t Q T) :
    miyamotoZG h L η ≤ CFSG.centerIn Q := by
  rw [hS.centerIn_Q']
  exact le_sup_left

theorem t_mem_centerIn_Q (hS : Setting h L η t Q T) : t ∈ CFSG.centerIn Q := by
  rw [hS.centerIn_Q']
  exact mem_sup_right (mem_zpowers t)

theorem mem_centerIn_Q_iff (hS : Setting h L η t Q T) {x : G} :
    x ∈ CFSG.centerIn Q ↔ x ∈ miyamotoZG h L η ∨ x * t ∈ miyamotoZG h L η := by
  rw [hS.centerIn_Q']
  exact CFSG.EvenSmallLie.UnitarySix.YamadaD.mem_sup_zpowers_iff hS.t_mul_t
    fun b hb => mem_centralizer_singleton_iff.1 (hS.ZP_le_centralizer_t hb)

theorem isElementaryAbelian_centerIn_Q (hS : Setting h L η t Q T) :
    CFSG.IsElementaryAbelian 2 (CFSG.centerIn Q) := by
  have := hS.isElementaryAbelian_ZP
  have : CFSG.IsElementaryAbelian 2 (zpowers t) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [← hS.t_two, pow_orderOf_eq_one])
  rw [hS.centerIn_Q']
  refine CFSG.IsElementaryAbelian.sup_of_le_centralizer ?_
  rw [zpowers_le, mem_centralizer_iff]
  intro z hz
  exact mem_centralizer_singleton_iff.1 (hS.ZP_le_centralizer_t hz)

theorem exists_conj_eq_mul_ZP (hS : Setting h L η t Q T) {z : G}
    (hz : z ∈ miyamotoZG h L η) : ∃ g : G, g⁻¹ * t * g = t * z := by
  have hmem : t * z ∈ {x | ∃ a ∈ miyamotoA1G h L η, x = t * a} := ⟨z, hS.ZP_le_A1 hz, rfl⟩
  rw [← hS.conj_inter_B1] at hmem
  obtain ⟨⟨g, hg⟩, -⟩ := hmem
  exact ⟨g, hg.symm⟩

theorem H_le_normalizer_ZP (hS : Setting h L η t Q T) :
    normalizer (CFSG.centerIn Q : Set G) ≤ normalizer (miyamotoZG h L η : Set G) := by
  intro g hg
  refine mem_normalizer_of_conj_le fun z hz => ?_
  have hzQ : g * z * g⁻¹ ∈ CFSG.centerIn Q :=
    (mem_normalizer_iff.1 hg z).1 (hS.ZP_le_centerIn_Q hz)
  rcases hS.mem_centerIn_Q_iff.1 hzQ with h1 | h1
  · exact h1
  · exfalso
    set y := g * z * g⁻¹ with hy
    have hyt : y = t * (y * t) := by
      have hc : (y * t) * t = t * (y * t) :=
        mem_centralizer_singleton_iff.1 (hS.ZP_le_centralizer_t h1)
      rw [← hc, mul_assoc, hS.t_mul_t, mul_one]
    obtain ⟨k, hk⟩ := hS.exists_conj_eq_mul_ZP h1
    apply hS.conj_not_mem_L (k * g)
    have e : (k * g)⁻¹ * t * (k * g) = z := by
      calc (k * g)⁻¹ * t * (k * g) = g⁻¹ * (k⁻¹ * t * k) * g := by group
        _ = g⁻¹ * y * g := by rw [hk, ← hyt]
        _ = z := by rw [hy]; group
    rw [e]
    exact hS.ZP_le_L hz

theorem crossed_mem_ZP (hS : Setting h L η t Q T) {g : G}
    (hg : g ∈ normalizer (CFSG.centerIn Q : Set G)) : g⁻¹ * t * g * t ∈ miyamotoZG h L η := by
  have h1 : g⁻¹ * t * g ∈ CFSG.centerIn Q := by
    have := (mem_normalizer_iff.1 (inv_mem hg) t).1 hS.t_mem_centerIn_Q
    rwa [inv_inv] at this
  rcases hS.mem_centerIn_Q_iff.1 h1 with h2 | h2
  · exact absurd (hS.ZP_le_L h2) (hS.conj_not_mem_L g)
  · exact h2

theorem cosetData (hS : Setting h L η t Q T) :
    CosetData (normalizer (CFSG.centerIn Q : Set G)) (miyamotoZG h L η) t :=
  ⟨hS.t_mul_t, hS.ZP_le_centralizer_t, hS.isElementaryAbelian_ZP, hS.H_le_normalizer_ZP,
    fun _ hg => hS.crossed_mem_ZP hg⟩

omit [Finite G] in
theorem mem_centralizer_zpowers_of_comm {x : G} (hx : x * t = t * x) :
    x ∈ centralizer (zpowers t : Set G) := by
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  exact (Commute.zpow_left (show Commute t x from hx.symm) k).eq

theorem centralizer_centerIn_Q_eq (hS : Setting h L η t Q T) :
    normalizer (CFSG.centerIn Q : Set G) ⊓ centralizer (miyamotoZG h L η : Set G) ⊓
      centralizer ({t} : Set G) = centralizer (CFSG.centerIn Q : Set G) := by
  apply le_antisymm
  · rintro x ⟨⟨-, hxZ⟩, hxt⟩
    rw [hS.centerIn_Q']
    exact mem_centralizer_sup hxZ (mem_centralizer_zpowers_of_comm
      (mem_centralizer_singleton_iff.1 hxt))
  · intro x hx
    refine ⟨⟨Subgroup.centralizer_le_normalizer _ hx, ?_⟩, ?_⟩
    · exact centralizer_le (SetLike.coe_subset_coe.2 hS.ZP_le_centerIn_Q) hx
    · exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hx t hS.t_mem_centerIn_Q).symm

theorem K0_le_C (hS : Setting h L η t Q T) :
    centralizer (CFSG.centerIn Q : Set G) ≤ centralizer ({t} : Set G) := by
  rw [← hS.centralizer_centerIn_Q_eq]
  exact inf_le_right

theorem K0_le_centralizer_ZP (hS : Setting h L η t Q T) :
    centralizer (CFSG.centerIn Q : Set G) ≤ centralizer (miyamotoZG h L η : Set G) := by
  rw [← hS.centralizer_centerIn_Q_eq]
  exact inf_le_left.trans inf_le_right

theorem K0_le_H (_hS : Setting h L η t Q T) :
    centralizer (CFSG.centerIn Q : Set G) ≤ normalizer (CFSG.centerIn Q : Set G) :=
  Subgroup.centralizer_le_normalizer _

theorem L_inf_centralizer_ZP_le_K0 (hS : Setting h L η t Q T) :
    L ⊓ centralizer (miyamotoZG h L η : Set G) ≤ centralizer (CFSG.centerIn Q : Set G) := by
  rintro x ⟨hxL, hxZ⟩
  rw [hS.centerIn_Q']
  exact mem_centralizer_sup hxZ (mem_centralizer_zpowers_of_comm (hS.comm_t_of_mem_L hxL))

theorem Q_le_K0 (_hS : Setting h L η t Q T) : Q ≤ centralizer (CFSG.centerIn Q : Set G) :=
  le_centralizer_centerIn Q

theorem t_mem_K0 (hS : Setting h L η t Q T) : t ∈ centralizer (CFSG.centerIn Q : Set G) :=
  hS.Q_le_K0 hS.t_mem_Q

theorem Q_le_H (_hS : Setting h L η t Q T) : Q ≤ normalizer (CFSG.centerIn Q : Set G) :=
  le_normalizer_centerIn Q

theorem L_inf_centralizer_ZP (_hS : Setting h L η t Q T) :
    L ⊓ centralizer (miyamotoZG h L η : Set G) = miyamotoPull h L η
      (gramSU h (miyamotoJ4 K) ⊓ centralizer (miyamotoZ h : Set (GL (Fin 4) K))) := by
  have : CharP K 2 := h.charP
  have hZ : miyamotoZ h ≤ gramSU h (miyamotoJ4 K) :=
    (miyamotoZ_le_P h).trans (miyamotoUnipotent_le_SU h false false)
  rw [miyamotoPull_inf_centralizer h L η _ hZ, miyamotoPull_gramSU]

theorem L_inf_centralizer_ZP_le_normalizer_A2 (_hS : Setting h L η t Q T) :
    L ⊓ centralizer (miyamotoZG h L η : Set G) ≤ normalizer (miyamotoA2G h L η : Set G) := by
  have : CharP K 2 := h.charP
  intro x hx
  have hx' : x ∈ L ⊓ normalizer (miyamotoZG h L η : Set G) :=
    ⟨hx.1, Subgroup.centralizer_le_normalizer _ hx.2⟩
  rw [normalizer_miyamotoZG] at hx'
  exact hx'.2

theorem A2_le_centralizer_ZP (_hS : Setting h L η t Q T) :
    miyamotoA2G h L η ≤ centralizer (miyamotoZG h L η : Set G) := by
  have : CharP K 2 := h.charP
  intro a ha
  rw [mem_centralizer_iff]
  intro z hz
  have hz' : z ∈ CFSG.centerIn (miyamotoA2G h L η) := by
    rw [centerIn_miyamotoPull h L η (miyamotoUnipotent_le_SU h false true), centerIn_miyamotoA2]
    exact hz
  exact (mem_centralizer_iff.1 hz'.2 a ha).symm

theorem isPGroup_A2 (_hS : Setting h L η t Q T) : IsPGroup 2 (miyamotoA2G h L η) :=
  IsPGroup.of_card (n := 5 * f) (by rw [card_miyamotoA2G, ← pow_mul, mul_comm])

theorem isPGroup_B2 (hS : Setting h L η t Q T) : IsPGroup 2 (miyamotoB2 h L η t) :=
  IsPGroup.of_card (n := 5 * f + 1) (by rw [hS.card_B2]; ring)

theorem le_A2_of_isPGroup (hS : Setting h L η t Q T) {X : Subgroup G}
    (hXL : X ≤ L ⊓ centralizer (miyamotoZG h L η : Set G))
    (hXn : L ⊓ centralizer (miyamotoZG h L η : Set G) ≤ normalizer (X : Set G))
    (hX : IsPGroup 2 X) : X ≤ miyamotoA2G h L η := by
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPC : miyamotoPG h L η ≤ L ⊓ centralizer (miyamotoZG h L η : Set G) := by
    refine le_inf (miyamotoPull_le h L η _) fun p hp => mem_centralizer_iff.2 fun z hz => ?_
    have hz' : z ∈ CFSG.centerIn (miyamotoPG h L η) := by
      rw [centerIn_miyamotoPG]
      exact hz
    exact (mem_centralizer_iff.1 hz'.2 p hp).symm
  have hXP : X ≤ miyamotoPG h L η := by
    have h2 : IsPGroup 2 (X ⊔ miyamotoPG h L η : Subgroup G) :=
      hX.to_sup_of_normal_left' hS.isSylowOf_P.isPGroup (hPC.trans hXn)
    have e := hS.isSylowOf_P.eq_of_le le_sup_right
      (sup_le (hXL.trans inf_le_left) (miyamotoPull_le h L η _)) h2
    rw [← e]
    exact le_sup_left
  have hr2S := miyamotoR2_mem_gramSU h
  set r : G := ((η.symm ⟨miyamotoR2 K, hr2S⟩ : L) : G) with hr
  have hrC : r ∈ L ⊓ centralizer (miyamotoZG h L η : Set G) := by
    rw [hS.L_inf_centralizer_ZP]
    refine (symm_mem_miyamotoPull_iff h L η).2 ⟨hr2S, mem_centralizer_iff.2 fun z hz => ?_⟩
    obtain ⟨d, -, rfl⟩ := (mem_Z h).1 hz
    have e := miyamotoR2_conj_Z h d
    calc miyamotoXGL h 0 0 0 d * miyamotoR2 K =
        miyamotoR2 K * ((miyamotoR2 K)⁻¹ * miyamotoXGL h 0 0 0 d * miyamotoR2 K) := by group
      _ = miyamotoR2 K * miyamotoXGL h 0 0 0 d := by rw [e]
  intro x hx
  have hx' : r⁻¹ * x * r ∈ X := by
    have := (mem_normalizer_iff.1 (inv_mem (hXn hrC)) x).1 hx
    rwa [inv_inv] at this
  have h2 := hXP hx'
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 (hXP hx)
  have e : r⁻¹ * ((η.symm g : L) : G) * r = ((η.symm ((⟨miyamotoR2 K, hr2S⟩ :
      gramSU h (miyamotoJ4 K))⁻¹ * g * ⟨miyamotoR2 K, hr2S⟩) : L) : G) := by
    simp only [hr, map_mul, map_inv, L.coe_mul, L.coe_inv]
  rw [e, symm_mem_miyamotoPull_iff, coe_mul, coe_mul, coe_inv] at h2
  exact (symm_mem_miyamotoPull_iff h L η).2 (mem_A2_of_mem_P_of_conj_mem_P h hg h2)

theorem K0_le_normalizer_A2 (hS : Setting h L η t Q T) :
    centralizer (CFSG.centerIn Q : Set G) ≤ normalizer (miyamotoA2G h L η : Set G) := by
  intro x hx
  have hxL : x ∈ normalizer (L : Set G) := hS.centralizer_le_normalizer (hS.K0_le_C hx)
  have hxZ : x ∈ normalizer (miyamotoZG h L η : Set G) :=
    Subgroup.centralizer_le_normalizer _ (hS.K0_le_centralizer_ZP hx)
  have hNC : x ∈ normalizer ((L ⊓ centralizer (miyamotoZG h L η : Set G) : Subgroup G) :
      Set G) :=
    CFSG.LocalAnalysis.EvenBN.Common.mem_normalizer_inf hxL (mem_normalizer_centralizer hxZ)
  have hA2C : miyamotoA2G h L η ≤ L ⊓ centralizer (miyamotoZG h L η : Set G) :=
    le_inf (miyamotoPull_le h L η _) hS.A2_le_centralizer_ZP
  set X := (miyamotoA2G h L η).map (MulAut.conj x).toMonoidHom with hX
  have hXL : X ≤ L ⊓ centralizer (miyamotoZG h L η : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    exact (mem_normalizer_iff.1 hNC a).1 (hA2C ha)
  have hXn : L ⊓ centralizer (miyamotoZG h L η : Set G) ≤ normalizer (X : Set G) := by
    intro y hy
    refine mem_normalizer_of_conj_le ?_
    rintro _ ⟨a, ha, rfl⟩
    have hy' : x⁻¹ * y * x ∈ L ⊓ centralizer (miyamotoZG h L η : Set G) := by
      have := (mem_normalizer_iff.1 (inv_mem hNC) y).1 hy
      rwa [inv_inv] at this
    have ha' := (mem_normalizer_iff.1 (hS.L_inf_centralizer_ZP_le_normalizer_A2 hy') a).1 ha
    refine ⟨(x⁻¹ * y * x) * a * (x⁻¹ * y * x)⁻¹, ha', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hle := hS.le_A2_of_isPGroup hXL hXn (hS.isPGroup_A2.map _)
  exact mem_normalizer_of_conj_le fun a ha => hle ⟨a, ha, rfl⟩

theorem K0_le_normalizer_B2 (hS : Setting h L η t Q T) :
    centralizer (CFSG.centerIn Q : Set G) ≤ normalizer (miyamotoB2 h L η t : Set G) := by
  intro x hx
  rw [miyamotoB2]
  exact CFSG.LocalAnalysis.EvenBN.Common.mem_normalizer_sup
    (mem_normalizer_zpowers_of_comm (mem_centralizer_singleton_iff.1 (hS.K0_le_C hx)))
    (hS.K0_le_normalizer_A2 hx)

theorem exists_act_eq_conj_of_commutator (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ centralizer (CFSG.centerIn Q : Set G)) (hxt : x ∈ centralizer ({t} : Set G))
    (hcomm : ∀ d ∈ miyamotoPull h L η (miyamotoI2Norm1 h),
      x * d * x⁻¹ * d⁻¹ ∈ miyamotoA2G h L η) :
    ∃ s : gramSU h (miyamotoJ4 K), hS.act ⟨x, hxt⟩ = MulAut.conj s := by
  have : CharP K 2 := h.charP
  have hfix : ∀ g : gramSU h (miyamotoJ4 K), (g : GL (Fin 4) K) ∈ miyamotoZ h →
      hS.act ⟨x, hxt⟩ g = g := fun g hg => by
    rw [act_apply]
    exact miyamotoAct_apply_of_mem_centralizer h L η _ (hS.K0_le_centralizer_ZP hx) hg
  obtain ⟨s, ⟨a, ha, i, hi, n, hn, hs⟩, φ, hφ, hact⟩ := (fixes_miyamotoZ_iff h _).1 hfix
  rcases hφ with rfl | hφ
  · exact ⟨s, by rw [hact, miyamotoFieldAut_refl, mul_one]⟩
  exfalso
  have hφeq : φ = miyamotoBarEquiv h := RingEquiv.ext fun c => by
    rw [hφ, miyamotoBarEquiv_apply]
  obtain ⟨b, hbN, hb1⟩ : ∃ b ∈ (Units.map h.normHom).ker, b ≠ 1 := by
    have : Finite K := h.finite
    have hcard := h.card_ker_normUnits_and_surjective.1
    have h1 : 1 < Nat.card (Units.map h.normHom).ker := by
      rw [hcard]
      have := Nat.one_le_two_pow (n := f)
      omega
    obtain ⟨⟨b, hb⟩, hb1⟩ := (ne_bot_iff_exists_ne_one).1
      ((one_lt_card_iff_ne_bot _).1 h1)
    exact ⟨b, hb, fun e => hb1 (Subtype.ext e)⟩
  have hbn : (b : K) * h.bar b = 1 := (UnitaryFieldData.mem_ker_normUnits h).1 hbN
  have hD : miyamotoI2Hom h b ∈ miyamotoI2Norm1 h :=
    (mem_miyamotoI2Norm1 h).2 ⟨b, (UnitaryFieldData.mem_ker_normUnits h).1 hbN, rfl⟩
  have hDS : miyamotoI2Hom h b ∈ gramSU h (miyamotoJ4 K) := miyamotoI2Hom_mem_gramSU h b
  set DS : gramSU h (miyamotoJ4 K) := ⟨miyamotoI2Hom h b, hDS⟩
  have hc := hcomm _ ((symm_mem_miyamotoPull_iff h L η (g := DS)).2 hD)
  have e : x * ((η.symm DS : L) : G) * x⁻¹ * ((η.symm DS : L) : G)⁻¹ =
      ((η.symm (hS.act ⟨x, hxt⟩ DS * DS⁻¹) : L) : G) := by
    rw [map_mul, L.coe_mul, hS.coe_symm_act_apply, map_inv, L.coe_inv]
  rw [e, symm_mem_miyamotoPull_iff, coe_mul, coe_inv, hact, MulAut.mul_apply, MulAut.conj_apply,
    coe_mul, coe_mul, coe_inv, coe_miyamotoFieldAut_apply, hs, hφeq] at hc
  have hiI : i ∈ miyamotoI2 h := by
    obtain ⟨b', -, rfl⟩ := (mem_miyamotoI2Norm1 h).1 hi
    exact ⟨b', rfl⟩
  exact not_mem_A2_of_bar h ha hiI hn hbn hb1 hc

theorem le_B2_of_isPGroup (hS : Setting h L η t Q T) {R : Subgroup G}
    (hRK : R ≤ centralizer (CFSG.centerIn Q : Set G))
    (hRn : centralizer (CFSG.centerIn Q : Set G) ≤ normalizer (R : Set G))
    (hR : IsPGroup 2 R) : R ≤ miyamotoB2 h L η t := by
  have : CharP K 2 := h.charP
  set K₀ := centralizer (CFSG.centerIn Q : Set G) with hK₀
  have ht2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [hS.card_zpowers_t, pow_one])
  have hRt : R ≤ normalizer (zpowers t : Set G) := fun r hr =>
    mem_normalizer_zpowers_of_comm (mem_centralizer_singleton_iff.1 (hS.K0_le_C (hRK hr)))
  set R' := R ⊔ zpowers t with hR'
  have hR'2 : IsPGroup 2 R' := hR.to_sup_of_normal_right' ht2 hRt
  have hR'K : R' ≤ K₀ := sup_le hRK ((zpowers_le).2 hS.t_mem_K0)
  have hR'n : K₀ ≤ normalizer (R' : Set G) := fun y hy =>
    CFSG.LocalAnalysis.EvenBN.Common.mem_normalizer_sup (hRn hy)
      (mem_normalizer_zpowers_of_comm (mem_centralizer_singleton_iff.1 (hS.K0_le_C hy)))
  have hX : R' ⊓ L ≤ miyamotoA2G h L η := by
    refine hS.le_A2_of_isPGroup (le_inf inf_le_right
      (inf_le_left.trans (hR'K.trans hS.K0_le_centralizer_ZP))) (fun y hy => ?_)
      (hR'2.to_le inf_le_left)
    exact CFSG.LocalAnalysis.EvenBN.Common.mem_normalizer_inf
      (hR'n (hS.L_inf_centralizer_ZP_le_K0 hy)) (le_normalizer hy.1)
  intro r hr
  have hrK := hRK hr
  have hrC := hS.K0_le_C hrK
  have hcomm : ∀ d ∈ miyamotoPull h L η (miyamotoI2Norm1 h),
      r * d * r⁻¹ * d⁻¹ ∈ miyamotoA2G h L η := by
    intro d hd
    have hdL : d ∈ L := miyamotoPull_le h L η _ hd
    have hdK : d ∈ K₀ := by
      refine hS.L_inf_centralizer_ZP_le_K0 ⟨hdL, mem_centralizer_iff.2 fun z hz => ?_⟩
      obtain ⟨D, hD, rfl⟩ := (mem_miyamotoPull h L η).1 hd
      obtain ⟨Z, hZ, rfl⟩ := (mem_miyamotoPull h L η).1 hz
      have e : D * Z = Z * D := Subtype.ext (miyamotoI2Norm1_commute_Z h hD hZ)
      rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, e]
    refine hX ⟨mem_sup_left ?_, ?_⟩
    · have h1 : d * r⁻¹ * d⁻¹ ∈ R := by
        have := (mem_normalizer_iff.1 (hRn hdK) r⁻¹).1 (inv_mem hr)
        exact this
      rw [show r * d * r⁻¹ * d⁻¹ = r * (d * r⁻¹ * d⁻¹) by group]
      exact mul_mem hr h1
    · exact L.mul_mem ((mem_normalizer_iff.1 (hS.centralizer_le_normalizer hrC) d).1 hdL)
        (L.inv_mem hdL)
  obtain ⟨s, hs⟩ := hS.exists_act_eq_conj_of_commutator hrK hrC hcomm
  rw [act_apply] at hs
  obtain ⟨c, hcL, hrc⟩ := exists_eq_mul_of_miyamotoAct_eq_conj h L η _ s hs
  have hrc' : r = ((η.symm s : L) : G) * c := hrc
  have hsC : ((η.symm s : L) : G) ∈ centralizer ({t} : Set G) :=
    hS.L_le_centralizer (η.symm s).2
  have hcC : c ∈ centralizer ({t} : Set G) := by
    have := mul_mem (inv_mem hsC) hrC
    rwa [hrc', inv_mul_cancel_left] at this
  have hct : c ∈ zpowers t := by
    rw [← hS.kernel_eq_zpowers']
    exact ⟨hcL, hcC⟩
  have hsA : ((η.symm s : L) : G) ∈ miyamotoA2G h L η := by
    refine hX ⟨?_, (η.symm s).2⟩
    have : ((η.symm s : L) : G) = r * c⁻¹ := by rw [hrc', mul_inv_cancel_right]
    rw [this]
    exact mul_mem (mem_sup_left hr) (mem_sup_right (inv_mem hct))
  rw [hrc', miyamotoB2]
  exact mul_mem (mem_sup_right hsA) (mem_sup_left hct)

theorem H_le_normalizer_B2 (hS : Setting h L η t Q T) :
    normalizer (CFSG.centerIn Q : Set G) ≤ normalizer (miyamotoB2 h L η t : Set G) := by
  intro g hg
  have hgK := mem_normalizer_centralizer hg
  set X := (miyamotoB2 h L η t).map (MulAut.conj g).toMonoidHom with hX
  have hB2K : miyamotoB2 h L η t ≤ centralizer (CFSG.centerIn Q : Set G) :=
    hS.B2_le_Q.trans hS.Q_le_K0
  have hXK : X ≤ centralizer (CFSG.centerIn Q : Set G) := by
    rintro _ ⟨b, hb, rfl⟩
    exact (mem_normalizer_iff.1 hgK b).1 (hB2K hb)
  have hXn : centralizer (CFSG.centerIn Q : Set G) ≤ normalizer (X : Set G) := by
    intro k hk
    refine mem_normalizer_of_conj_le ?_
    rintro _ ⟨b, hb, rfl⟩
    have hk' : g⁻¹ * k * g ∈ centralizer (CFSG.centerIn Q : Set G) := by
      have := (mem_normalizer_iff.1 (inv_mem hgK) k).1 hk
      rwa [inv_inv] at this
    have hb' := (mem_normalizer_iff.1 (hS.K0_le_normalizer_B2 hk') b).1 hb
    refine ⟨(g⁻¹ * k * g) * b * (g⁻¹ * k * g)⁻¹, hb', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hle := hS.le_B2_of_isPGroup hXK hXn (hS.isPGroup_B2.map _)
  exact mem_normalizer_of_conj_le fun b hb => hle ⟨b, hb, rfl⟩

theorem B2_le_C (hS : Setting h L η t Q T) : miyamotoB2 h L η t ≤ centralizer ({t} : Set G) :=
  hS.B2_le_Q.trans hS.Q_le_centralizer

theorem exists_of_mem_B2 (hS : Setting h L η t Q T) {b : G} (hb : b ∈ miyamotoB2 h L η t) :
    ∃ u ∈ zpowers t, ∃ a ∈ miyamotoA2G h L η, b = u * a :=
  exists_mul_of_mem_sup_of_commute (hS.zpowers_comm_of_le_L (miyamotoPull_le h L η _)) hb

theorem act_mem_range_conj (hS : Setting h L η t Q T) (b : miyamotoB2 h L η t) :
    hS.act ⟨b, hS.B2_le_C b.2⟩ ∈
      (MulAut.conj : gramSU h (miyamotoJ4 K) →* MulAut (gramSU h (miyamotoJ4 K))).range := by
  obtain ⟨b, hb⟩ := b
  obtain ⟨u, hu, a, ha, rfl⟩ := hS.exists_of_mem_B2 hb
  have haL : a ∈ L := miyamotoPull_le h L η _ ha
  have huC : u ∈ centralizer ({t} : Set G) := (zpowers_le).2 hS.t_mem_centralizer hu
  have e : (⟨u * a, hS.B2_le_C hb⟩ : centralizer ({t} : Set G)) =
      ⟨u, huC⟩ * ⟨a, hS.L_le_centralizer haL⟩ := rfl
  rw [e, map_mul, (hS.act_eq_one_iff _).2 ((zpowers_le).2 hS.t_mem hu), one_mul,
    hS.act_of_mem haL]
  exact ⟨_, rfl⟩

noncomputable def piB2 (hS : Setting h L η t Q T) : miyamotoB2 h L η t →* GL (Fin 4) K :=
  (gramSU h (miyamotoJ4 K)).subtype.comp ((MonoidHom.ofInjective
    (f := (MulAut.conj : gramSU h (miyamotoJ4 K) →* MulAut (gramSU h (miyamotoJ4 K))))
    fun _ _ e => (conj_inj h).1 e).symm.toMonoidHom.comp
      ((hS.act.comp (inclusion hS.B2_le_C)).codRestrict _ hS.act_mem_range_conj))

theorem exists_act_eq_conj_piB2 (hS : Setting h L η t Q T) (b : miyamotoB2 h L η t) :
    ∃ s : gramSU h (miyamotoJ4 K), (s : GL (Fin 4) K) = hS.piB2 b ∧
      hS.act ⟨b, hS.B2_le_C b.2⟩ = MulAut.conj s := by
  set e := MonoidHom.ofInjective
    (f := (MulAut.conj : gramSU h (miyamotoJ4 K) →* MulAut (gramSU h (miyamotoJ4 K))))
    fun _ _ e => (conj_inj h).1 e
  refine ⟨e.symm ⟨_, hS.act_mem_range_conj b⟩, rfl, ?_⟩
  have := MonoidHom.ofInjective_apply (f := (MulAut.conj : gramSU h (miyamotoJ4 K) →*
    MulAut (gramSU h (miyamotoJ4 K)))) (fun _ _ e => (conj_inj h).1 e)
    (x := e.symm ⟨_, hS.act_mem_range_conj b⟩)
  rw [MulEquiv.apply_symm_apply] at this
  exact this

theorem piB2_of_mem_A2 (hS : Setting h L η t Q T) {a : G} (ha : a ∈ miyamotoA2G h L η)
    (hb : a ∈ miyamotoB2 h L η t) :
    hS.piB2 ⟨a, hb⟩ = ((η ⟨a, miyamotoPull_le h L η _ ha⟩ : gramSU h (miyamotoJ4 K)) :
      GL (Fin 4) K) := by
  obtain ⟨s, hs, hact⟩ := hS.exists_act_eq_conj_piB2 ⟨a, hb⟩
  rw [← hs]
  have e : hS.act ⟨a, hS.B2_le_C hb⟩ = MulAut.conj (η ⟨a, miyamotoPull_le h L η _ ha⟩) :=
    hS.act_of_mem (miyamotoPull_le h L η _ ha)
  rw [e] at hact
  exact congrArg Subtype.val ((conj_inj h).1 hact).symm

theorem piB2_of_mem_zpowers (hS : Setting h L η t Q T) {u : G} (hu : u ∈ zpowers t)
    (hb : u ∈ miyamotoB2 h L η t) : hS.piB2 ⟨u, hb⟩ = 1 := by
  obtain ⟨s, hs, hact⟩ := hS.exists_act_eq_conj_piB2 ⟨u, hb⟩
  rw [← hs, (hS.act_eq_one_iff _).2 ((zpowers_le).2 hS.t_mem hu)] at *
  have := (conj_eq_one_iff h s).1 hact.symm
  rw [this, OneMemClass.coe_one]

theorem range_piB2 (hS : Setting h L η t Q T) : hS.piB2.range = miyamotoA2 h := by
  have : CharP K 2 := h.charP
  apply le_antisymm
  · rintro _ ⟨⟨b, hb⟩, rfl⟩
    obtain ⟨u, hu, a, ha, rfl⟩ := hS.exists_of_mem_B2 hb
    have hub : u ∈ miyamotoB2 h L η t := by rw [miyamotoB2]; exact mem_sup_left hu
    have hab : a ∈ miyamotoB2 h L η t := by rw [miyamotoB2]; exact mem_sup_right ha
    have e : (⟨u * a, hb⟩ : miyamotoB2 h L η t) = ⟨u, hub⟩ * ⟨a, hab⟩ := rfl
    rw [e, map_mul, hS.piB2_of_mem_zpowers hu hub, one_mul, hS.piB2_of_mem_A2 ha hab]
    obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 ha
    simpa using hg
  · intro g hg
    have hgS : g ∈ gramSU h (miyamotoJ4 K) := miyamotoUnipotent_le_SU h false true hg
    have ha : ((η.symm ⟨g, hgS⟩ : L) : G) ∈ miyamotoA2G h L η :=
      (symm_mem_miyamotoPull_iff h L η).2 hg
    have hab : ((η.symm ⟨g, hgS⟩ : L) : G) ∈ miyamotoB2 h L η t := by
      rw [miyamotoB2]
      exact mem_sup_right ha
    refine ⟨⟨_, hab⟩, ?_⟩
    rw [hS.piB2_of_mem_A2 ha hab]
    simp

theorem commutator_B2 (hS : Setting h L η t Q T) :
    ⁅miyamotoB2 h L η t, miyamotoB2 h L η t⁆ = miyamotoZG h L η := by
  apply le_antisymm
  · rw [commutator_le]
    intro b hb b' hb'
    obtain ⟨u, hu, a, ha, rfl⟩ := hS.exists_of_mem_B2 hb
    obtain ⟨u', hu', a', ha', rfl⟩ := hS.exists_of_mem_B2 hb'
    have hc := hS.zpowers_comm_of_le_L (miyamotoPull_le h L η (miyamotoA2 h))
    have hZ : ⁅miyamotoA2G h L η, miyamotoA2G h L η⁆ = miyamotoZG h L η :=
      commutator_miyamotoA2G h L η
    rw [hc u hu a ha, hc u' hu' a' ha', commutatorElement_mul_mul_eq_of_commute
      (hc u hu a' ha') (hS.zpowers_comm hu hu') (hc u' hu' a ha), ← hZ]
    exact commutator_mem_commutator ha ha'
  · have hZ : ⁅miyamotoA2G h L η, miyamotoA2G h L η⁆ = miyamotoZG h L η :=
      commutator_miyamotoA2G h L η
    rw [← hZ]
    have hle : miyamotoA2G h L η ≤ miyamotoB2 h L η t := by rw [miyamotoB2]; exact le_sup_right
    exact commutator_mono hle hle

theorem ZP_le_B2 (hS : Setting h L η t Q T) : miyamotoZG h L η ≤ miyamotoB2 h L η t :=
  hS.commutator_B2 ▸ commutator_le_self _

theorem mem_commutator_B2_iff (hS : Setting h L η t Q T) (z : miyamotoB2 h L η t) :
    z ∈ commutator (miyamotoB2 h L η t) ↔ (z : G) ∈ miyamotoZG h L η := by
  have e : (commutator (miyamotoB2 h L η t)).map (miyamotoB2 h L η t).subtype =
      miyamotoZG h L η := by
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype,
      hS.commutator_B2]
  rw [← e]
  exact (mem_map_iff_mem (miyamotoB2 h L η t).subtype_injective).symm

theorem ker_piB2_inf_commutator (hS : Setting h L η t Q T) :
    hS.piB2.ker ⊓ commutator (miyamotoB2 h L η t) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzk, hzc⟩ := mem_inf.1 hz
  have hzZ := (hS.mem_commutator_B2_iff z).1 hzc
  obtain ⟨s, hs, hact⟩ := hS.exists_act_eq_conj_piB2 z
  rw [MonoidHom.mem_ker] at hzk
  rw [hzk] at hs
  have hs1 : s = 1 := Subtype.ext hs
  rw [hs1, map_one, hS.act_eq_one_iff] at hact
  have hmem : (z : G) ∈ L ⊓ centralizer (L : Set G) := ⟨hS.ZP_le_L hzZ, hact⟩
  rw [hS.inf_centralizer_eq_bot, mem_bot] at hmem
  exact (mem_bot).2 (Subtype.ext hmem)

theorem exists_semilinear_conj (hS : Setting h L η t Q T)
    (g : normalizer (CFSG.centerIn Q : Set G)) :
    ∃ (σ : h.fixedField →+* h.fixedField) (μ : K), h.bar μ = μ ∧ μ ≠ 0 ∧
      ∀ z : miyamotoB2 h L η t, (z : G) ∈ miyamotoZG h L η → ∀ s : h.fixedField,
        hS.piB2 z = miyamotoXGL h 0 0 0 s →
          hS.piB2 (normalizerMonoidHom (miyamotoB2 h L η t) ⟨g, hS.H_le_normalizer_B2 g.2⟩ z) =
            miyamotoXGL h 0 0 0 (μ * σ s) := by
  have : CharP K 2 := h.charP
  obtain ⟨σ, μ, hμ, hμ0, hθ⟩ := exists_semilinear_of_mulEquiv h hS.piB2 hS.range_piB2
    hS.ker_piB2_inf_commutator (normalizerMonoidHom _ ⟨g, hS.H_le_normalizer_B2 g.2⟩)
  exact ⟨σ, μ, hμ, hμ0, fun z hz s hs => hθ z ((hS.mem_commutator_B2_iff z).2 hz) s hs⟩

theorem IG_le_C (hS : Setting h L η t Q T) : miyamotoIG h L η ≤ centralizer ({t} : Set G) :=
  (miyamotoPull_le h L η _).trans hS.L_le_centralizer

theorem IG_le_H (hS : Setting h L η t Q T) :
    miyamotoIG h L η ≤ normalizer (CFSG.centerIn Q : Set G) := by
  have : CharP K 2 := h.charP
  intro i hi
  have hiN : i ∈ normalizer (miyamotoPG h L η : Set G) := by
    have hi' : i ∈ L ⊓ normalizer (miyamotoPG h L η : Set G) := by
      rw [normalizer_miyamotoPG]
      exact mem_sup_right hi
    exact hi'.2
  have hiZ : i ∈ normalizer (miyamotoZG h L η : Set G) := by
    have := normalizer_le_normalizer_centerIn _ hiN
    rwa [centerIn_miyamotoPG] at this
  rw [hS.centerIn_Q']
  exact CFSG.LocalAnalysis.EvenBN.Common.mem_normalizer_sup hiZ
    (mem_normalizer_zpowers_of_comm (hS.comm_t_of_mem_L (miyamotoPull_le h L η _ hi)))

theorem IG_transitive (hS : Setting h L η t Q T) {z z' : G} (hz : z ∈ miyamotoZG h L η)
    (hz' : z' ∈ miyamotoZG h L η) (hz1 : z ≠ 1) (hz1' : z' ≠ 1) :
    ∃ i ∈ miyamotoIG h L η, i * z * i⁻¹ = z' := by
  have : CharP K 2 := h.charP
  have htr := (miyamoto_two_one_threeG h L η hS.two_le).2.2.2
  rw [(miyamoto_two_one_two_centralizersG h L η hS.two_le).2.2.2] at htr
  obtain ⟨g, hg, e⟩ := htr z hz z' hz' hz1 hz1'
  exact ⟨g⁻¹, inv_mem hg, by rw [inv_inv]; exact e⟩

theorem exists_rho (hS : Setting h L η t Q T) :
    ∃ ρ : normalizer (CFSG.centerIn Q : Set G) →* AddMonoid.End h.fixedField,
      (∀ g, ∃ σ : h.fixedField →+* h.fixedField, ∃ μ : h.fixedField, μ ≠ 0 ∧
        ∀ s, ρ g s = μ * σ s) ∧
      (∀ g, ρ g = 1 → (g : G) ∈ centralizer (miyamotoZG h L η : Set G)) ∧
      ∀ ω : h.fixedField, ω ≠ 0 → ∃ g : normalizer (CFSG.centerIn Q : Set G),
        (g : G) ∈ miyamotoIG h L η ∧ ∀ s, ρ g s = ω * s := by
  have : CharP K 2 := h.charP
  have hZS : miyamotoZ h ≤ gramSU h (miyamotoJ4 K) :=
    (miyamotoZ_le_P h).trans (miyamotoUnipotent_le_SU h false false)
  have hzmem : ∀ s : h.fixedField, miyamotoXGL h 0 0 0 (s : K) ∈ miyamotoZ h :=
    fun s => ⟨s, s.2, rfl⟩
  set z : h.fixedField → G := fun s =>
    ((η.symm ⟨miyamotoXGL h 0 0 0 s, hZS (hzmem s)⟩ : L) : G) with hzdef
  have hzZ : ∀ s, z s ∈ miyamotoZG h L η := fun s =>
    (symm_mem_miyamotoPull_iff h L η).2 (hzmem s)
  have hzadd : ∀ s s', z (s + s') = z s * z s' := by
    intro s s'
    simp only [hzdef]
    rw [← L.coe_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    rw [coe_mul, miyamotoXGL_mul h (map_zero _), miyamotoXGL_inj]
    simp
  have hzinj : Function.Injective z := by
    intro s s' e
    have e' := congrArg Subtype.val (η.symm.injective (Subtype.ext e))
    exact Subtype.ext ((miyamotoXGL_inj h).1 e').2.2.2
  have hzsurj : ∀ y ∈ miyamotoZG h L η, ∃ s, z s = y := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hy
    obtain ⟨d, hd, e⟩ := (mem_Z h).1 hg
    refine ⟨⟨d, hd⟩, ?_⟩
    simp only [hzdef]
    congr 2
    exact Subtype.ext e.symm
  have hηz : ∀ s, ((η ⟨z s, hS.ZP_le_L (hzZ s)⟩ : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) =
      miyamotoXGL h 0 0 0 s := fun s => by
    simp only [hzdef, Subtype.coe_eta, MulEquiv.apply_symm_apply]
  have hconj : ∀ (g : normalizer (CFSG.centerIn Q : Set G)) (s : h.fixedField),
      ∃ s', z s' = (g : G) * z s * (g : G)⁻¹ := fun g s =>
    hzsurj _ ((mem_normalizer_iff.1 (hS.H_le_normalizer_ZP g.2) _).1 (hzZ s))
  choose c hc using hconj
  let ρ : normalizer (CFSG.centerIn Q : Set G) →* AddMonoid.End h.fixedField :=
    { toFun := fun g => AddMonoidHom.mk' (c g) fun s s' => hzinj (by
        rw [hc, hzadd, hzadd, hc, hc]
        group)
      map_one' := by
        refine AddMonoidHom.ext fun s => hzinj ?_
        change z (c 1 s) = z s
        rw [hc]
        simp
      map_mul' := fun g g' => by
        refine AddMonoidHom.ext fun s => hzinj ?_
        change z (c (g * g') s) = z (c g (c g' s))
        rw [hc, hc, hc, coe_mul]
        group }
  have hρ : ∀ g s, ρ g s = c g s := fun _ _ => rfl
  refine ⟨ρ, fun g => ?_, fun g hg => ?_, fun ω hω => ?_⟩
  ·
    obtain ⟨σ, μ, hμ, hμ0, hθ⟩ := hS.exists_semilinear_conj g
    refine ⟨σ, ⟨μ, hμ⟩, fun e => hμ0 (congrArg Subtype.val e), fun s => Subtype.ext ?_⟩
    have hzB : z s ∈ miyamotoB2 h L η t := hS.ZP_le_B2 (hzZ s)
    have h1 := hθ ⟨z s, hzB⟩ (hzZ s) s
      (by rw [hS.piB2_of_mem_A2 (hS.ZP_le_A2 (hzZ s)) hzB, hηz])
    have hzB' : z (c g s) ∈ miyamotoB2 h L η t := hS.ZP_le_B2 (hzZ _)
    have e2 : (normalizerMonoidHom (miyamotoB2 h L η t) ⟨g, hS.H_le_normalizer_B2 g.2⟩
        ⟨z s, hzB⟩ : miyamotoB2 h L η t) = ⟨z (c g s), hzB'⟩ := Subtype.ext (hc g s).symm
    rw [e2, hS.piB2_of_mem_A2 (hS.ZP_le_A2 (hzZ _)) hzB', hηz, miyamotoXGL_inj] at h1
    rw [hρ]
    exact h1.2.2.2
  ·
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨s, rfl⟩ := hzsurj y hy
    have e : c g s = s := by
      have := congrArg (fun φ : AddMonoid.End h.fixedField => φ s) hg
      exact this
    have e' := hc g s
    rw [e] at e'
    calc z s * g = ((g : G) * z s * (g : G)⁻¹) * g := by rw [← e']
      _ = g * z s := by group
  ·
    obtain ⟨α, hα⟩ := exists_unit_norm_eq h (s := ((ω : K))⁻¹)
      (by rw [map_inv₀, (h.mem_fixedField).1 ω.2]) (inv_ne_zero fun e => hω (Subtype.ext e))
    have hDI : miyamotoIHom h (α, α⁻¹) ∈ miyamotoI h :=
      (miyamotoIHom_mem_miyamotoI_iff h _).2 ((miyamotoIParam_eq_one_iff h _).2 (by simp))
    have hDS : miyamotoIHom h (α, α⁻¹) ∈ gramSU h (miyamotoJ4 K) := miyamotoI_le_gramSU h hDI
    set i : G := ((η.symm ⟨_, hDS⟩ : L) : G) with hi
    have hiI : i ∈ miyamotoIG h L η := (symm_mem_miyamotoPull_iff h L η).2 hDI
    refine ⟨⟨i, hS.IG_le_H hiI⟩, hiI, fun s => ?_⟩
    rw [hρ]
    apply hzinj
    rw [hc]
    have hD : miyamotoIHom h (α, α⁻¹) * miyamotoXGL h 0 0 0 s * (miyamotoIHom h (α, α⁻¹))⁻¹ =
        miyamotoXGL h 0 0 0 (ω * s) := by
      have e := miyamotoIHom_conj_Z h (α⁻¹, α) s
      have hinv : miyamotoIHom h (α⁻¹, α) = (miyamotoIHom h (α, α⁻¹))⁻¹ := by
        rw [← map_inv, Prod.inv_mk, inv_inv]
      rw [hinv, inv_inv] at e
      rw [e, coe_miyamotoWeightZ]
      congr 1
      have hα0 : (α : K) ≠ 0 := α.ne_zero
      have hbα : h.bar (α : K) = ((ω : K) * α)⁻¹ := by
        rw [mul_inv, ← hα]
        field_simp
      simp only [Units.val_inv_eq_inv_val, map_inv₀, hbα, inv_inv]
      field_simp
    change i * z s * i⁻¹ = z (ω * s)
    simp only [hzdef, hi]
    rw [← L.coe_inv, ← L.coe_mul, ← L.coe_mul, ← map_inv η.symm, ← map_mul η.symm,
      ← map_mul η.symm]
    congr 2
    apply Subtype.ext
    rw [coe_mul, coe_mul, coe_inv]
    exact hD

theorem T_le_normalizer_B1 (hS : Setting h L η t Q T) :
    T ≤ normalizer (miyamotoB1 h L η t : Set G) := by
  have := hS.characteristic_B1
  exact (normal_subgroupOf_iff_le_normalizer hS.B1_le_T).1 inferInstance

theorem card_conj_set_B1 (hS : Setting h L η t Q T) :
    Nat.card {x | ∃ n ∈ normalizer (miyamotoB1 h L η t : Set G), x = n⁻¹ * t * n} =
      (2 ^ f) ^ 4 := by
  rw [hS.conj_set_B1_eq]
  have e : {x | ∃ a ∈ miyamotoA1G h L η, x = t * a} =
      (fun a => t * a) '' (miyamotoA1G h L η : Set G) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
  rw [e, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ (mul_right_injective t),
    ← Nat.card_coe_set_eq]
  exact card_miyamotoA1G h L η

theorem not_isSylow_T (hS : Setting h L η t Q T) : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T := by
  rintro ⟨S, hST⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (miyamotoB1 h L η t : Set G) with hN
  have hTN := hS.T_le_normalizer_B1
  have hidx : (centralizer ({t} : Set G)).relIndex N = (2 ^ f) ^ 4 := by
    rw [← card_conj_set_eq_relIndex, hS.card_conj_set_B1]
  have h1 := relIndex_mul_relIndex T (centralizer ({t} : Set G) ⊓ N) N (le_inf hS.T_le hTN)
    inf_le_right
  rw [inf_relIndex_right, hidx] at h1
  have h2 : 2 ∣ T.relIndex N := by
    rw [← h1]
    exact Dvd.dvd.mul_left (dvd_pow (dvd_pow_self 2 (by have := hS.two_le; omega))
      (by norm_num)) _
  have h4 : ¬ 2 ∣ T.index := by
    rw [← hST]
    exact S.not_dvd_index
  exact h4 (h2.trans (relIndex_dvd_index_of_le hTN))

theorem exists_mem_H_conj_ne (hS : Setting h L η t Q T) :
    ∃ g ∈ normalizer (CFSG.centerIn Q : Set G), g⁻¹ * t * g ≠ t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  apply hS.not_isSylow_T
  refine CFSG.LocalAnalysis.EvenBN.Common.exists_sylow_eq_of_isSylowOf_of_normalizer_le
    hS.T_sylow fun x hx => ?_
  have hxH : x ∈ normalizer (CFSG.centerIn Q : Set G) :=
    normalizer_le_normalizer_centerIn Q (hS.normalizer_T_le_normalizer_Q hx)
  have e := hcon x hxH
  refine mem_centralizer_singleton_iff.2 ?_
  calc x * t = x * (x⁻¹ * t * x) := by rw [e]
    _ = t * x := by group

theorem conj_set_H_eq (hS : Setting h L η t Q T) :
    {x | ∃ g ∈ normalizer (CFSG.centerIn Q : Set G), x = g⁻¹ * t * g} =
      {x | ∃ z ∈ miyamotoZG h L η, x = t * z} := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hz := hS.crossed_mem_ZP hg
    refine ⟨_, hz, ?_⟩
    have hc : (g⁻¹ * t * g * t) * t = t * (g⁻¹ * t * g * t) :=
      mem_centralizer_singleton_iff.1 (hS.ZP_le_centralizer_t hz)
    calc g⁻¹ * t * g = g⁻¹ * t * g * t * t := by rw [mul_assoc (g⁻¹ * t * g), hS.t_mul_t, mul_one]
      _ = t * (g⁻¹ * t * g * t) := hc
  · rintro ⟨z, hz, rfl⟩
    by_cases hz1 : z = 1
    · exact ⟨1, one_mem _, by rw [hz1]; group⟩
    obtain ⟨g₀, hg₀, hne⟩ := hS.exists_mem_H_conj_ne
    have hz₀ := hS.crossed_mem_ZP hg₀
    have e1 : g₀⁻¹ * t * g₀ = (g₀⁻¹ * t * g₀ * t) * t := by
      rw [mul_assoc (g₀⁻¹ * t * g₀), hS.t_mul_t, mul_one]
    have hz₀1 : g₀⁻¹ * t * g₀ * t ≠ 1 := fun e => hne (by rw [e1, e, one_mul])
    obtain ⟨i, hi, hiz⟩ := hS.IG_transitive hz₀ hz hz₀1 hz1
    refine ⟨g₀ * i⁻¹, mul_mem hg₀ (inv_mem (hS.IG_le_H hi)), ?_⟩
    have hit : i * t * i⁻¹ = t := by
      rw [hS.comm_t_of_mem_L (miyamotoPull_le h L η _ hi), mul_inv_cancel_right]
    have hzt : z * t = t * z := mem_centralizer_singleton_iff.1 (hS.ZP_le_centralizer_t hz)
    calc t * z = z * t := hzt.symm
      _ = (i * (g₀⁻¹ * t * g₀ * t) * i⁻¹) * (i * t * i⁻¹) := by rw [hiz, hit]
      _ = i * ((g₀⁻¹ * t * g₀ * t) * t) * i⁻¹ := by group
      _ = i * (g₀⁻¹ * t * g₀) * i⁻¹ := by rw [← e1]
      _ = (g₀ * i⁻¹)⁻¹ * t * (g₀ * i⁻¹) := by group

theorem card_conj_set_H (hS : Setting h L η t Q T) :
    Nat.card {x | ∃ g ∈ normalizer (CFSG.centerIn Q : Set G), x = g⁻¹ * t * g} = 2 ^ f := by
  rw [hS.conj_set_H_eq]
  have e : {x | ∃ z ∈ miyamotoZG h L η, x = t * z} =
      (fun z => t * z) '' (miyamotoZG h L η : Set G) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  rw [e, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ (mul_right_injective t),
    ← Nat.card_coe_set_eq]
  exact hS.card_ZP

theorem not_le_centralizer_t (hS : Setting h L η t Q T) :
    ¬ (normalizer (CFSG.centerIn Q : Set G) ⊓ centralizer (miyamotoZG h L η : Set G) ≤
      centralizer ({t} : Set G)) := by
  intro hle
  have : Finite K := h.finite
  obtain ⟨ρ, hρ, hρ1, -⟩ := hS.exists_rho
  refine not_two_pow_dvd_card_conj_set (F := h.fixedField) (W := h.fixedField)
    (UnitaryFieldData.card_fixedField h) (Module.finrank_self _) ρ (fun g => ?_)
    (fun g hg => mem_centralizer_singleton_iff.1 (hle ⟨g.2, hρ1 g hg⟩))
    (by rw [hS.card_conj_set_H])
  obtain ⟨σ, μ, -, hρg⟩ := hρ g
  refine ⟨σ, fun c w => ?_⟩
  rw [smul_eq_mul, smul_eq_mul, hρg, hρg, map_mul]
  ring

theorem regularNormalData (hS : Setting h L η t Q T) :
    RegularNormalData (normalizer (CFSG.centerIn Q : Set G)) (CFSG.centerIn Q) (miyamotoZG h L η)
      (normalizer (CFSG.centerIn Q : Set G) ⊓ centralizer (miyamotoZG h L η : Set G)) t := by
  rcases crossed_image_trivial_or_top hS.isElementaryAbelian_centerIn_Q hS.centerIn_Q'.symm
    hS.t_not_mem_ZP le_rfl hS.H_le_normalizer_ZP (le_inf hS.IG_le_H hS.IG_le_C)
    (fun _ he he1 _ he' he1' => hS.IG_transitive he he' he1 he1') with h1 | h1
  · exact absurd h1 hS.not_le_centralizer_t
  · exact h1

theorem centralizer_ZP_transitive (hS : Setting h L η t Q T) :
    ∀ y ∈ miyamotoZG h L η, ∃ v ∈ normalizer (CFSG.centerIn Q : Set G) ⊓
      centralizer (miyamotoZG h L η : Set G), v⁻¹ * t * v = t * y := by
  intro y hy
  refine hS.regularNormalData.exists_inf_centralizer_conj_eq
    (mul_mem hS.t_mem_centerIn_Q (hS.ZP_le_centerIn_Q hy)) fun hty => hS.t_not_mem_ZP ?_
  have := mul_mem hty (inv_mem hy)
  rwa [mul_inv_cancel_right] at this

theorem le_centralizer_ZP_of_isPGroup (hS : Setting h L η t Q T) {R : Subgroup G}
    (hRH : R ≤ normalizer (CFSG.centerIn Q : Set G))
    (hRI : ∀ i ∈ miyamotoIG h L η, ∀ r ∈ R, i * r * i⁻¹ ∈ R) (hR : IsPGroup 2 R) :
    R ≤ centralizer (miyamotoZG h L η : Set G) := by
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := h.finite
  obtain ⟨ρ, hρ, hρ1, hρI⟩ := hS.exists_rho
  have h2pow : ∀ x : normalizer (CFSG.centerIn Q : Set G), (x : G) ∈ R →
      ∃ k : ℕ, x ^ 2 ^ k = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hR ⟨x, hx⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  have hpow : ∀ (φ : AddMonoid.End h.fixedField) (κ : h.fixedField), (∀ s, φ s = κ * s) →
      ∀ n s, (φ ^ n) s = κ ^ n * s := by
    intro φ κ hφ n
    induction n with
    | zero => intro s; rw [pow_zero, pow_zero, one_mul]; rfl
    | succ n ih =>
      intro s
      rw [pow_succ, pow_succ, show (φ ^ n * φ) s = (φ ^ n) (φ s) from rfl, hφ, ih]
      ring
  have hfrob : ∀ (κ : h.fixedField) (k : ℕ), κ ^ 2 ^ k = 1 → κ = 1 := by
    intro κ k hk
    have hk' : (κ : K) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have e : ((κ : K) - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, hk', one_pow, sub_self]
    exact Subtype.ext (sub_eq_zero.1 ((pow_eq_zero_iff (by positivity)).1 e))
  intro r hr
  set rH : normalizer (CFSG.centerIn Q : Set G) := ⟨r, hRH hr⟩
  obtain ⟨σ, μ, hμ0, hρr⟩ := hρ rH
  have hsurj : Function.Surjective (ρ rH) := by
    have hinj : Function.Injective (ρ rH) := by
      intro s s' e
      rw [hρr, hρr] at e
      exact σ.injective (mul_left_cancel₀ hμ0 e)
    exact Finite.injective_iff_surjective.1 hinj
  have hσ : ∀ ω : h.fixedField, σ ω = ω := by
    intro ω
    by_cases hω : ω = 0
    · rw [hω, map_zero]
    obtain ⟨i, hiI, hi⟩ := hρI ω hω
    have hcR : ((i * rH * i⁻¹ * rH⁻¹ : normalizer (CFSG.centerIn Q : Set G)) : G) ∈ R :=
      mul_mem (hRI _ hiI r hr) (inv_mem hr)
    have hiinv : ∀ s, ρ i⁻¹ s = ω⁻¹ * s := by
      intro s
      have e : ρ i (ρ i⁻¹ s) = s := by
        rw [← show (ρ i * ρ i⁻¹) s = ρ i (ρ i⁻¹ s) from rfl, ← map_mul, mul_inv_cancel, map_one]
        rfl
      rw [hi] at e
      calc ρ i⁻¹ s = ω⁻¹ * (ω * ρ i⁻¹ s) := by rw [← mul_assoc, inv_mul_cancel₀ hω, one_mul]
        _ = ω⁻¹ * s := by rw [e]
    have hσω : σ ω ≠ 0 := (map_ne_zero σ).2 hω
    have hκ : ∀ y, ρ (i * rH * i⁻¹ * rH⁻¹) y = (ω * (σ ω)⁻¹) * y := by
      intro y
      obtain ⟨s, rfl⟩ := hsurj y
      have e : ρ (i * rH * i⁻¹ * rH⁻¹) (ρ rH s) = ρ (i * rH * i⁻¹) s := by
        rw [← show (ρ (i * rH * i⁻¹ * rH⁻¹) * ρ rH) s =
          ρ (i * rH * i⁻¹ * rH⁻¹) (ρ rH s) from rfl, ← map_mul, inv_mul_cancel_right]
      rw [e, map_mul, map_mul]
      change ρ i (ρ rH (ρ i⁻¹ s)) = _
      rw [hiinv, hρr, hi, hρr, map_mul, map_inv₀]
      field_simp
    obtain ⟨k, hk⟩ := h2pow _ hcR
    have e := hpow _ _ hκ (2 ^ k) 1
    rw [← map_pow, hk, map_one ρ, mul_one] at e
    have hκ1 := hfrob _ k e.symm
    rw [mul_inv_eq_one₀ hσω] at hκ1
    exact hκ1.symm
  have hρr' : ∀ s, ρ rH s = μ * s := fun s => by rw [hρr, hσ]
  obtain ⟨k, hk⟩ := h2pow rH hr
  have e := hpow (ρ rH) μ hρr' (2 ^ k) 1
  rw [← map_pow, hk, map_one ρ, mul_one] at e
  have hμ1 := hfrob μ k e.symm
  refine hρ1 rH (DFunLike.ext _ _ fun s => ?_)
  rw [hρr', hμ1, one_mul]
  rfl

omit [Finite G] in
theorem glAut_eq_of_mem_Cu {φ : K ≃+* K} (hφ : φ = RingEquiv.refl K ∨ ∀ c, φ c = h.bar c)
    {g : GL (Fin 4) K} (hg : g ∈ miyamotoCu h) : glAut φ g = g := by
  apply Units.ext
  rw [coe_glAut]
  rcases hφ with rfl | hφ
  · ext i j
    rfl
  · rw [show (g : Matrix (Fin 4) (Fin 4) K).map φ = (g : Matrix (Fin 4) (Fin 4) K).map h.bar from
      Matrix.ext fun i j => hφ _]
    exact (mem_miyamotoCu h).1 hg

omit [Finite G] in
theorem miyamotoI2Hom_mem_Cu {c : Kˣ} (hc : h.bar c = c) : miyamotoI2Hom h c ∈ miyamotoCu h := by
  rw [mem_miyamotoCu, coe_miyamotoI2Hom, Matrix.diagonal_map (map_zero _)]
  congr 1
  ext i
  fin_cases i <;> simp [hc, map_inv₀]

theorem A0_le (hS : Setting h L η t Q T) :
    miyamotoPull h L η (miyamotoI2 h ⊓ miyamotoCu h) ≤
      normalizer (CFSG.centerIn Q : Set G) ⊓ centralizer ({t} : Set G) := by
  have hle : miyamotoPull h L η (miyamotoI2 h ⊓ miyamotoCu h) ≤ miyamotoIG h L η :=
    miyamotoPull_mono h L η (inf_le_left.trans (miyamotoI2_le_I h))
  exact le_inf (hle.trans hS.IG_le_H) (hle.trans hS.IG_le_C)

theorem A0_commutator_mem_B2 (hS : Setting h L η t Q T) {a k : G}
    (ha : a ∈ miyamotoPull h L η (miyamotoI2 h ⊓ miyamotoCu h))
    (hk : k ∈ normalizer (CFSG.centerIn Q : Set G) ⊓ centralizer (miyamotoZG h L η : Set G) ⊓
      centralizer ({t} : Set G)) :
    a * k * a⁻¹ * k⁻¹ ∈ miyamotoB2 h L η t := by
  have : CharP K 2 := h.charP
  rw [hS.centralizer_centerIn_Q_eq] at hk
  have hkt := hS.K0_le_C hk
  obtain ⟨D, ⟨hDI, hDC⟩, rfl⟩ := (mem_miyamotoPull h L η).1 ha
  have haL := (η.symm D).2
  have haC : ((η.symm D : L) : G) ∈ centralizer ({t} : Set G) := hS.L_le_centralizer haL
  have hfix : ∀ g : gramSU h (miyamotoJ4 K), (g : GL (Fin 4) K) ∈ miyamotoZ h →
      hS.act ⟨k, hkt⟩ g = g := fun g hg => by
    rw [act_apply]
    exact miyamotoAct_apply_of_mem_centralizer h L η _ (hS.K0_le_centralizer_ZP hk) hg
  obtain ⟨s, ⟨a', ha', i, hi, n, hn, hs⟩, φ, hφ, hact⟩ := (fixes_miyamotoZ_iff h _).1 hfix
  have hφD : miyamotoFieldAut h φ D⁻¹ = D⁻¹ := by
    apply Subtype.ext
    rw [coe_miyamotoFieldAut_apply]
    exact glAut_eq_of_mem_Cu hφ (inv_mem hDC)
  set x : centralizer ({t} : Set G) := ⟨_, haC⟩ * ⟨k, hkt⟩ * (⟨_, haC⟩)⁻¹ * (⟨k, hkt⟩)⁻¹ with hx
  have e1 : hS.act ⟨((η.symm D : L) : G), haC⟩ = MulAut.conj D := by
    rw [hS.act_of_mem haL]
    simp
  have hactx : hS.act x = MulAut.conj (D * s * D⁻¹ * s⁻¹) := by
    rw [hx, map_mul, map_mul, map_mul, map_inv, map_inv, e1, hact]
    have e2 := miyamotoFieldAut_mul_conj_mul_inv h φ D⁻¹
    rw [hφD] at e2
    calc MulAut.conj D * (MulAut.conj s * miyamotoFieldAut h φ) * (MulAut.conj D)⁻¹ *
          (MulAut.conj s * miyamotoFieldAut h φ)⁻¹ =
        MulAut.conj D * MulAut.conj s * (miyamotoFieldAut h φ * MulAut.conj D⁻¹ *
          (miyamotoFieldAut h φ)⁻¹) * (MulAut.conj s)⁻¹ := by rw [map_inv]; group
      _ = MulAut.conj (D * s * D⁻¹ * s⁻¹) := by rw [e2]; simp only [map_mul, map_inv]
  have hiI : i ∈ miyamotoI2 h := by
    obtain ⟨b', -, rfl⟩ := (mem_miyamotoI2Norm1 h).1 hi
    exact ⟨b', rfl⟩
  have hc1 : (D : GL (Fin 4) K) * i = i * D := miyamotoI2_commute' h hDI hiI
  have hc2 : (D : GL (Fin 4) K) * n = n * D := miyamotoI2_commute_N2 h hDI hn
  have hy : ((D * s * D⁻¹ * s⁻¹ : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) ∈ miyamotoA2 h := by
    rw [coe_mul, coe_mul, coe_mul, coe_inv, coe_inv, hs]
    have e : (D : GL (Fin 4) K) * (a' * (i * n)) * (D : GL (Fin 4) K)⁻¹ * (a' * (i * n))⁻¹ =
        ((D : GL (Fin 4) K) * a' * (D : GL (Fin 4) K)⁻¹) * a'⁻¹ := by
      calc (D : GL (Fin 4) K) * (a' * (i * n)) * (D : GL (Fin 4) K)⁻¹ * (a' * (i * n))⁻¹ =
          (D : GL (Fin 4) K) * a' * (i * (n * (D : GL (Fin 4) K)⁻¹)) * n⁻¹ * i⁻¹ * a'⁻¹ := by
            group
        _ = (D : GL (Fin 4) K) * a' * (i * ((D : GL (Fin 4) K)⁻¹ * n)) * n⁻¹ * i⁻¹ * a'⁻¹ := by
            rw [show n * (D : GL (Fin 4) K)⁻¹ = (D : GL (Fin 4) K)⁻¹ * n by
              rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hc2, ← mul_assoc, inv_mul_cancel,
                one_mul]]
        _ = (D : GL (Fin 4) K) * a' * ((i * (D : GL (Fin 4) K)⁻¹) * n) * n⁻¹ * i⁻¹ * a'⁻¹ := by
            group
        _ = (D : GL (Fin 4) K) * a' * (((D : GL (Fin 4) K)⁻¹ * i) * n) * n⁻¹ * i⁻¹ * a'⁻¹ := by
            rw [show i * (D : GL (Fin 4) K)⁻¹ = (D : GL (Fin 4) K)⁻¹ * i by
              rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hc1, ← mul_assoc, inv_mul_cancel,
                one_mul]]
        _ = ((D : GL (Fin 4) K) * a' * (D : GL (Fin 4) K)⁻¹) * a'⁻¹ := by group
    rw [e]
    exact mul_mem ((mem_normalizer_iff.1 (miyamotoI_le_normalizer_unipotent h false true
      ((miyamotoI2_le_I h) hDI)) a').1 ha') (inv_mem ha')
  rw [act_apply] at hactx
  obtain ⟨c, hcL, hxc⟩ := exists_eq_mul_of_miyamotoAct_eq_conj h L η _ _ hactx
  have hxc' : ((η.symm D : L) : G) * k * ((η.symm D : L) : G)⁻¹ * k⁻¹ =
      ((η.symm (D * s * D⁻¹ * s⁻¹) : L) : G) * c := hxc
  have hyC : ((η.symm (D * s * D⁻¹ * s⁻¹) : L) : G) ∈ centralizer ({t} : Set G) :=
    hS.L_le_centralizer (η.symm _).2
  have hxC : ((η.symm D : L) : G) * k * ((η.symm D : L) : G)⁻¹ * k⁻¹ ∈
      centralizer ({t} : Set G) := (x.2 : _)
  have hcC : c ∈ centralizer ({t} : Set G) := by
    have := mul_mem (inv_mem hyC) hxC
    rwa [hxc', inv_mul_cancel_left] at this
  have hct : c ∈ zpowers t := by
    rw [← hS.kernel_eq_zpowers']
    exact ⟨hcL, hcC⟩
  rw [hxc', miyamotoB2]
  exact mul_mem (mem_sup_right ((symm_mem_miyamotoPull_iff h L η).2 hy)) (mem_sup_left hct)

theorem A0_transitive (_hS : Setting h L η t Q T) {y y' : G} (hy : y ∈ miyamotoZG h L η)
    (hy' : y' ∈ miyamotoZG h L η) (hy1 : y ≠ 1) (hy1' : y' ≠ 1) :
    ∃ a ∈ miyamotoPull h L η (miyamotoI2 h ⊓ miyamotoCu h), a * y * a⁻¹ = y' := by
  have : CharP K 2 := h.charP
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hy
  obtain ⟨g', hg', rfl⟩ := (mem_miyamotoPull h L η).1 hy'
  obtain ⟨d, hd, hgd⟩ := (mem_Z h).1 hg
  obtain ⟨d', hd', hgd'⟩ := (mem_Z h).1 hg'
  have hd0 : d ≠ 0 := fun e => hy1 (by
    have : g = 1 := Subtype.ext (by rw [hgd, e, miyamotoXGL_zero, OneMemClass.coe_one])
    rw [this, map_one, OneMemClass.coe_one])
  have hd0' : d' ≠ 0 := fun e => hy1' (by
    have : g' = 1 := Subtype.ext (by rw [hgd', e, miyamotoXGL_zero, OneMemClass.coe_one])
    rw [this, map_one, OneMemClass.coe_one])
  obtain ⟨e₁, he₁, he₁F⟩ := exists_sq_eq_of_charTwo h (d' / d)
  obtain ⟨e, he, heF⟩ := exists_sq_eq_of_charTwo h e₁
  have hδF : h.bar (d' / d) = d' / d := by rw [map_div₀, hd, hd']
  have he₁F' := he₁F hδF
  have heF' := heF he₁F'
  have he0 : e ≠ 0 := by
    rintro rfl
    apply hd0'
    have : d' / d = 0 := by rw [← he₁, ← he]; ring
    rwa [div_eq_zero_iff, or_iff_left hd0] at this
  set c : Kˣ := Units.mk0 e he0
  have hcF : h.bar (c : K) = c := heF'
  have hDI : (miyamotoI2Hom h c)⁻¹ ∈ miyamotoI2 h ⊓ miyamotoCu h :=
    inv_mem ⟨⟨c, rfl⟩, miyamotoI2Hom_mem_Cu hcF⟩
  have hDS : (miyamotoI2Hom h c)⁻¹ ∈ gramSU h (miyamotoJ4 K) :=
    inv_mem (miyamotoI2Hom_mem_gramSU h c)
  refine ⟨((η.symm ⟨_, hDS⟩ : L) : G), (symm_mem_miyamotoPull_iff h L η).2 hDI, ?_⟩
  rw [← L.coe_inv, ← L.coe_mul, ← L.coe_mul, ← map_inv η.symm, ← map_mul η.symm,
    ← map_mul η.symm]
  congr 2
  apply Subtype.ext
  rw [coe_mul, coe_mul, coe_inv, inv_inv, hgd, hgd', miyamotoI2Hom_conj, miyamotoXGL_inj]
  refine ⟨by simp, rfl, by simp, ?_⟩
  have hd4 : (c : K) ^ 2 * h.bar ((c : K) ^ 2) = d' / d := by
    rw [map_pow, hcF, ← pow_add, ← he₁, ← he]
    simp only [c, Units.val_mk0]
    ring
  rw [hd4]
  field_simp

theorem miyamotoM0_eq (_hS : Setting h L η t Q T) :
    miyamotoM0 Q = CFSG.EvenSmallLie.UnitarySix.YamadaD.oTwo
      (normalizer (CFSG.centerIn Q : Set G)) :=
  CFSG.LocalAnalysis.EvenBN.Common.pCore_map_eq_oTwo _

theorem two_core_M (hS : Setting h L η t Q T) :
    miyamotoM0 Q ≤ centralizer (miyamotoZG h L η : Set G) ∧
      (∀ d ∈ miyamotoM0 Q, ∀ k ∈ normalizer (CFSG.centerIn Q : Set G) ⊓
        centralizer (miyamotoZG h L η : Set G) ⊓ centralizer ({t} : Set G),
        d * k * d⁻¹ * k⁻¹ ∈ miyamotoB2 h L η t) ∧
      miyamotoM0 Q ⊓ centralizer ({t} : Set G) = miyamotoB2 h L η t ∧
      (∀ y ∈ miyamotoZG h L η, ∃ d ∈ miyamotoM0 Q, d⁻¹ * t * d = t * y) ∧
      ∀ g ∈ normalizer (CFSG.centerIn Q : Set G), ∃ c ∈ normalizer (CFSG.centerIn Q : Set G) ⊓
        centralizer ({t} : Set G), ∃ d ∈ miyamotoM0 Q, g = c * d := by
  have hc := hS.cosetData
  rw [hS.miyamotoM0_eq]
  refine hc.two_core hS.isPGroup_B2 ?_ hS.H_le_normalizer_B2 ?_ ?_
  · rw [hS.centralizer_centerIn_Q_eq]
    exact hS.B2_le_Q.trans hS.Q_le_K0
  · intro R hR hRn hR2
    have hRZ := hS.le_centralizer_ZP_of_isPGroup (hR.trans inf_le_left)
      (fun i hi r hr => (mem_normalizer_iff.1 (hRn ⟨hS.IG_le_H hi, hS.IG_le_C hi⟩) r).1 hr) hR2
    have hRK : R ≤ centralizer (CFSG.centerIn Q : Set G) := by
      rw [← hS.centralizer_centerIn_Q_eq]
      exact fun r hr => ⟨⟨(hR hr).1, hRZ hr⟩, (hR hr).2⟩
    exact hS.le_B2_of_isPGroup hRK (fun k hk => hRn ⟨hS.K0_le_H hk, hS.K0_le_C hk⟩) hR2
  · have hY : 2 < Nat.card (miyamotoZG h L η) := by
      rw [hS.card_ZP]
      have := hS.four_le
      omega
    exact hc.transitive_of_transitive hS.H_le_normalizer_B2 hS.A0_le
      (fun a ha k hk => hS.A0_commutator_mem_B2 ha hk)
      (fun y hy y' hy' hy1 hy1' => hS.A0_transitive hy hy' hy1 hy1') hY
      hS.centralizer_ZP_transitive

omit [Finite G] in
theorem centerIn_sup_zpowers {X : Subgroup G} {u : G} (hc : ∀ x ∈ X, x * u = u * x) :
    CFSG.centerIn (X ⊔ zpowers u) = CFSG.centerIn X ⊔ zpowers u := by
  have hcomm : ∀ x ∈ X, ∀ y ∈ zpowers u, x * y = y * x := fun x hx y hy => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_right (show Commute x u from hc x hx) k).eq
  refine le_antisymm (fun z hz => ?_) (sup_le (fun z hz => ?_) fun z hz => ?_)
  · obtain ⟨hzX, hzC⟩ := mem_inf.1 hz
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hzX
    refine mul_mem (mem_sup_left (mem_inf.2 ⟨ha, mem_centralizer_iff.2 fun x hx => ?_⟩))
      (mem_sup_right hb)
    have h1 := mem_centralizer_iff.1 hzC x (mem_sup_left hx)
    have h2 : b * x = x * b := (hcomm x hx b hb).symm
    have h3 : x * a * b = a * x * b := by
      calc x * a * b = x * (a * b) := by group
        _ = a * b * x := h1
        _ = a * (b * x) := by group
        _ = a * (x * b) := by rw [h2]
        _ = a * x * b := by group
    exact mul_right_cancel h3
  · obtain ⟨hzX, hzC⟩ := mem_inf.1 hz
    refine mem_inf.2 ⟨mem_sup_left hzX, mem_centralizer_iff.2 fun y hy => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hy
    have h1 : a * z = z * a := mem_centralizer_iff.1 hzC a ha
    have h2 : b * z = z * b := (hcomm z hzX b hb).symm
    calc a * b * z = a * (b * z) := by group
      _ = a * (z * b) := by rw [h2]
      _ = a * z * b := by group
      _ = z * a * b := by rw [h1]
      _ = z * (a * b) := by group
  · refine mem_inf.2 ⟨mem_sup_right hz, mem_centralizer_iff.2 fun y hy => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hy
    have h1 : a * z = z * a := hcomm a ha z hz
    have h2 : b * z = z * b := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
      obtain ⟨l, rfl⟩ := mem_zpowers_iff.1 hz
      rw [← zpow_add, ← zpow_add, add_comm]
    calc a * b * z = a * (b * z) := by group
      _ = a * (z * b) := by rw [h2]
      _ = a * z * b := by group
      _ = z * a * b := by rw [h1]
      _ = z * (a * b) := by group

theorem centerIn_B2 (hS : Setting h L η t Q T) :
    CFSG.centerIn (miyamotoB2 h L η t) = CFSG.centerIn Q := by
  have : CharP K 2 := h.charP
  have hA2 : CFSG.centerIn (miyamotoA2G h L η) = miyamotoZG h L η := by
    rw [miyamotoA2G, centerIn_miyamotoPull h L η (miyamotoUnipotent_le_SU h false true)]
    exact congrArg (miyamotoPull h L η) (centerIn_miyamotoA2 h)
  have hc : ∀ x ∈ miyamotoA2G h L η, x * t = t * x := fun x hx =>
    mem_centralizer_singleton_iff.1 (hS.L_le_centralizer (miyamotoPull_le h L η _ hx))
  rw [miyamotoB2, sup_comm, centerIn_sup_zpowers hc, hA2, hS.centerIn_Q']

theorem M_le_H (hS : Setting h L η t Q T) :
    miyamotoM0 Q ≤ normalizer (CFSG.centerIn Q : Set G) := by
  rw [hS.miyamotoM0_eq]
  exact CFSG.EvenSmallLie.UnitarySix.YamadaD.oTwo_le _

theorem conj_set_M (hS : Setting h L η t Q T) :
    {x | ∃ g ∈ miyamotoM0 Q, x = g⁻¹ * t * g} =
      (fun y => t * y) '' (miyamotoZG h L η : Set G) := by
  obtain ⟨-, -, -, hMt, -⟩ := hS.two_core_M
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hy := hS.crossed_mem_ZP (hS.M_le_H hg)
    refine ⟨g⁻¹ * t * g * t, hy, ?_⟩
    have hyt : (g⁻¹ * t * g * t) * t = t * (g⁻¹ * t * g * t) :=
      mem_centralizer_singleton_iff.1 (hS.ZP_le_centralizer_t hy)
    calc t * (g⁻¹ * t * g * t) = g⁻¹ * t * g * t * t := hyt.symm
      _ = g⁻¹ * t * g * (t * t) := by group
      _ = g⁻¹ * t * g := by rw [hS.t_mul_t, mul_one]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨d, hd, hdt⟩ := hMt y hy
    exact ⟨d, hd, hdt.symm⟩

theorem card_M (hS : Setting h L η t Q T) : Nat.card (miyamotoM0 Q) = 2 * (2 ^ f) ^ 6 := by
  obtain ⟨-, -, hMC, -, -⟩ := hS.two_core_M
  have h1 := card_conj_set_eq_relIndex (miyamotoM0 Q) t
  rw [hS.conj_set_M, Nat.card_image_of_injective (mul_right_injective t), SetLike.coe_sort_coe,
    hS.card_ZP] at h1
  have h2 := relIndex_mul_card (centralizer ({t} : Set G)) (miyamotoM0 Q)
  rw [← h1, inf_comm, hMC, hS.card_B2] at h2
  rw [← h2]
  ring

theorem M_le_normalizer_Q (hS : Setting h L η t Q T) :
    miyamotoM0 Q ≤ normalizer (Q : Set G) := by
  obtain ⟨-, hMK, -, -, -⟩ := hS.two_core_M
  intro m hm
  have hK : ∀ k ∈ Q, k ∈ normalizer (CFSG.centerIn Q : Set G) ⊓
      centralizer (miyamotoZG h L η : Set G) ⊓ centralizer ({t} : Set G) := fun k hk => by
    rw [hS.centralizer_centerIn_Q_eq]
    exact hS.Q_le_K0 hk
  refine mem_normalizer_fintype fun x hx => ?_
  have hc := hS.B2_le_Q (hMK m hm x (hK x hx))
  have e : m * x * m⁻¹ = (m * x * m⁻¹ * x⁻¹) * x := by group
  rw [e]
  exact mul_mem hc hx

theorem sec3_2 (hS : Setting h L η t Q T) :
    (∀ g ∈ normalizer (CFSG.centerIn Q : Set G), ∃ c ∈ normalizer (CFSG.centerIn Q : Set G) ⊓
        centralizer ({t} : Set G), ∃ d ∈ miyamotoM0 Q, g = c * d) ∧
      Nat.card (miyamotoM0 Q) = 2 * (2 ^ f) ^ 6 ∧
      miyamotoM0 Q ≤ normalizer (Q : Set G) ∧
      (∀ g ∈ normalizer (Q : Set G), ∃ c ∈ normalizer (Q : Set G) ⊓ centralizer ({t} : Set G),
        ∃ d ∈ miyamotoM0 Q, g = c * d) ∧
      normalizer (miyamotoB2 h L η t : Set G) = normalizer (CFSG.centerIn Q : Set G) := by
  obtain ⟨-, -, -, -, hH⟩ := hS.two_core_M
  refine ⟨hH, hS.card_M, hS.M_le_normalizer_Q, fun g hg => ?_, ?_⟩
  · obtain ⟨c, hc, d, hd, rfl⟩ := hH g (normalizer_le_normalizer_centerIn Q hg)
    have hcN : c ∈ normalizer (Q : Set G) := by
      have := mul_mem hg (inv_mem (hS.M_le_normalizer_Q hd))
      rwa [mul_inv_cancel_right] at this
    exact ⟨c, mem_inf.2 ⟨hcN, (mem_inf.1 hc).2⟩, d, hd, rfl⟩
  · refine le_antisymm (fun g hg => ?_) hS.H_le_normalizer_B2
    rw [← hS.centerIn_B2]
    exact normalizer_le_normalizer_centerIn _ hg

end Setting

end CFSG.LocalAnalysis.EvenBN.U4

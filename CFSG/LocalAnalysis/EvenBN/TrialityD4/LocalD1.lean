module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalJZeroLayerSylow
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalD1Defs

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)
open scoped Pointwise commutatorElement

theorem commutator_mem_of_mul_self_mem_D4 {G : Type*} [Group G] {X N : Subgroup G}
    (hN : N ≤ centralizer (X : Set G)) (hX : ∀ x ∈ X, x * x ∈ N) {a b : G} (ha : a ∈ X)
    (hb : b ∈ X) : a * b * a⁻¹ * b⁻¹ ∈ N := by
  have hza := hX a ha
  have hzb := hX b hb
  have hzab := hX _ (mul_mem ha hb)
  have h1 : a⁻¹ = (a * a)⁻¹ * a := by group
  have h2 : b⁻¹ = (b * b)⁻¹ * b := by group
  have hc1 : (a * a)⁻¹ * (a * b) = a * b * (a * a)⁻¹ :=
    (mem_centralizer_iff.1 (hN (inv_mem hza)) _ (mul_mem ha hb)).symm
  have hc2 : (b * b)⁻¹ * (a * b * a) = a * b * a * (b * b)⁻¹ :=
    (mem_centralizer_iff.1 (hN (inv_mem hzb)) _ (mul_mem (mul_mem ha hb) ha)).symm
  have e : a * b * a⁻¹ * b⁻¹ = (a * a)⁻¹ * (b * b)⁻¹ * (a * b * (a * b)) := by
    calc a * b * a⁻¹ * b⁻¹ = a * b * ((a * a)⁻¹ * a) * ((b * b)⁻¹ * b) := by rw [← h1, ← h2]
      _ = (a * b * (a * a)⁻¹) * a * (b * b)⁻¹ * b := by group
      _ = ((a * a)⁻¹ * (a * b)) * a * (b * b)⁻¹ * b := by rw [hc1]
      _ = (a * a)⁻¹ * ((a * b * a) * (b * b)⁻¹) * b := by group
      _ = (a * a)⁻¹ * ((b * b)⁻¹ * (a * b * a)) * b := by rw [hc2]
      _ = (a * a)⁻¹ * (b * b)⁻¹ * (a * b * (a * b)) := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem hza) (inv_mem hzb)) hzab

section Normalizers

variable {G : Type*} [Group G] [Finite G]

theorem mem_normalizer_inf_D4 {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) :=
  mem_normalizer_fintype fun x hx => Subgroup.mem_inf.2
    ⟨(mem_normalizer_iff.1 hA x).1 (Subgroup.mem_inf.1 hx).1,
      (mem_normalizer_iff.1 hB x).1 (Subgroup.mem_inf.1 hx).2⟩

theorem mem_normalizer_centralizer_D4 {A : Subgroup G} {g : G}
    (hg : g ∈ normalizer (A : Set G)) :
    g ∈ normalizer ((centralizer (A : Set G) : Subgroup G) : Set G) :=
  mem_normalizer_fintype fun c hc => by
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro a ha
    have ha' : g⁻¹ * a * g ∈ A := by
      have := (mem_normalizer_iff.1 (inv_mem hg) a).1 ha
      rwa [inv_inv] at this
    have hac := mem_centralizer_iff.1 hc _ ha'
    calc a * (g * c * g⁻¹) = g * ((g⁻¹ * a * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * a * g)) * g⁻¹ := by rw [hac]
      _ = g * c * g⁻¹ * a := by group

theorem inf_centralizer_le_normalizer_D4 {X P : Subgroup G} (hPX : P ≤ X) :
    X ⊓ centralizer (X : Set G) ≤ normalizer (P : Set G) := fun z hz =>
  mem_normalizer_fintype fun p hp => by
    rw [← mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 p (hPX hp), mul_inv_cancel_right]
    exact hp

theorem center_sup_center_D4 {X P : Subgroup G} (hPX : P ≤ X)
    (hP : P ⊓ centralizer (P : Set G) ≤ X ⊓ centralizer (X : Set G)) :
    (P ⊔ (X ⊓ centralizer (X : Set G))) ⊓
        centralizer ((P ⊔ (X ⊓ centralizer (X : Set G)) : Subgroup G) : Set G) =
      X ⊓ centralizer (X : Set G) := by
  have hQX : P ⊔ (X ⊓ centralizer (X : Set G)) ≤ X := sup_le hPX inf_le_left
  have hset := coe_mul_of_right_le_normalizer_left P (X ⊓ centralizer (X : Set G))
    (inf_centralizer_le_normalizer_D4 hPX)
  apply le_antisymm
  · intro z hz
    obtain ⟨hzQ, hzc⟩ := Subgroup.mem_inf.1 hz
    have hzQ' : z ∈ ((P ⊔ (X ⊓ centralizer (X : Set G)) : Subgroup G) : Set G) := hzQ
    rw [hset] at hzQ'
    obtain ⟨p, hp, w, hw, rfl⟩ := hzQ'
    have hwc : w ∈ centralizer ((P ⊔ (X ⊓ centralizer (X : Set G)) : Subgroup G) : Set G) :=
      mem_centralizer_iff.2 fun y hy =>
        mem_centralizer_iff.1 (Subgroup.mem_inf.1 hw).2 y (hQX hy)
    have hpc : p ∈ centralizer ((P ⊔ (X ⊓ centralizer (X : Set G)) : Subgroup G) : Set G) := by
      have := mul_mem hzc (inv_mem hwc)
      rwa [mul_inv_cancel_right] at this
    have hpZ : p ∈ X ⊓ centralizer (X : Set G) :=
      hP (Subgroup.mem_inf.2 ⟨hp, mem_centralizer_iff.2 fun y hy =>
        mem_centralizer_iff.1 hpc y (mem_sup_left hy)⟩)
    exact mul_mem hpZ hw
  · intro z hz
    refine Subgroup.mem_inf.2 ⟨mem_sup_right hz, mem_centralizer_iff.2 fun y hy => ?_⟩
    exact mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 y (hQX hy)

end Normalizers

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem u_mem_normalizer_J₀ : d.u ∈ normalizer (d.J₀ : Set X) := by
  have := d.finite
  refine mem_normalizer_fintype fun j hj => ?_
  obtain ⟨h, rfl⟩ := hj
  obtain ⟨h', hh'⟩ := d.u_torus h
  refine ⟨h', ?_⟩
  change d.torus (h' ^ (q - 1)) = d.u * d.torus (h ^ (q - 1)) * d.u⁻¹
  rw [map_pow, map_pow, ← conj_pow, d.u_inv, hh']

theorem v_mem_normalizer_J₀ : d.v ∈ normalizer (d.J₀ : Set X) := by
  have := d.finite
  refine mem_normalizer_fintype fun j hj => ?_
  obtain ⟨h, rfl⟩ := hj
  obtain ⟨h', hh'⟩ := d.v_torus h
  refine ⟨h', ?_⟩
  change d.torus (h' ^ (q - 1)) = d.v * d.torus (h ^ (q - 1)) * d.v⁻¹
  rw [map_pow, map_pow, ← conj_pow, d.v_inv, hh']

theorem S_inf_centralizer_Y : d.S ⊓ centralizer (d.Y : Set X) = d.M := by
  apply le_antisymm
  · rintro s ⟨hs, hsc⟩
    obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff_x₂.1 hs
    have hnY := d.M_le_centralizer_Y hn
    have h5 : d.x₂ a * d.x₅ 1 = d.x₅ 1 * d.x₂ a := by
      have e1 := mem_centralizer_iff.1 hsc _ (d.x₅_mem_Y 1)
      have e2 := mem_centralizer_iff.1 hnY _ (d.x₅_mem_Y 1)
      have : d.x₅ 1 * d.x₂ a * n = d.x₂ a * d.x₅ 1 * n := by
        calc d.x₅ 1 * d.x₂ a * n = d.x₅ 1 * (d.x₂ a * n) := mul_assoc _ _ _
          _ = d.x₂ a * n * d.x₅ 1 := e1
          _ = d.x₂ a * (n * d.x₅ 1) := mul_assoc _ _ _
          _ = d.x₂ a * (d.x₅ 1 * n) := by rw [e2]
          _ = d.x₂ a * d.x₅ 1 * n := (mul_assoc _ _ _).symm
      exact (mul_right_cancel this).symm
    have ha : a = 0 := by
      have e := d.comm₂₅ a 1
      rw [commutatorElement_eq_one_iff_commute.2 h5, mul_one] at e
      exact d.x₆_eq_one_iff.1 e.symm
    rw [ha, d.x₂_zero, one_mul]
    exact hn
  · exact le_inf d.M_le_S d.M_le_centralizer_Y

theorem D_le_sup_conj_W : d.D ≤ d.W ⊔ d.W.map (MulAut.conj d.u).toMonoidHom := by
  have hW' : ∀ w ∈ d.W, d.u * w * d.u ∈ d.W.map (MulAut.conj d.u).toMonoidHom := fun w hw =>
    ⟨w, hw, by simp [d.u_inv]⟩
  show d.U₂ ⊔ (d.U₃ ⊔ d.W) ≤ _
  refine sup_le ?_ (sup_le ?_ le_sup_left)
  · rintro _ ⟨a, rfl⟩
    exact mem_sup_right (d.u_x₅ a ▸ hW' _ (d.x₅_mem_W a))
  · rintro _ ⟨a, rfl⟩
    have e := d.u_conj_x₄_eq_x₃ a
    rw [d.u_inv] at e
    exact mem_sup_right (e ▸ hW' _ (d.x₄_mem_W a))

theorem torus_one_conj_x₄ {m : d.Γˣ} (hm : d.nmUnits m = 1) (a : d.Γ) :
    d.torus (1, m) * d.x₄ a * (d.torus (1, m))⁻¹ = d.x₄ ((m : d.Γ)⁻¹ * a) := by
  rw [d.torus_x₄]
  congr 1
  have hN : (m : d.Γ) * (d.σ m * d.σ (d.σ m)) = 1 := by
    have := congrArg (fun x : (d.Γ₀)ˣ => ((x : d.Γ₀) : d.Γ)) hm
    simp only [coe_coe_nmUnits, Units.val_one, OneMemClass.coe_one] at this
    rw [← mul_assoc]
    exact this
  show (((1 : d.Γ₀ˣ) : d.Γ₀) : d.Γ) * d.σ m * d.σ (d.σ m) * a = (m : d.Γ)⁻¹ * a
  rw [Units.val_one, OneMemClass.coe_one, one_mul, eq_inv_of_mul_eq_one_right hN]

end TrialityD4Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

section Inclusions

omit [Finite G] in
theorem coe_mem_normalizer_map {E : Subgroup L} {l : L} (hl : l ∈ normalizer (E : Set L)) :
    (l : G) ∈ normalizer ((E.map L.subtype : Subgroup G) : Set G) :=
  map_le_normalizer_map ((zpowers_le).2 hl) ⟨l, mem_zpowers l, rfl⟩

theorem t_mem_normalizer_map_D1 (h : Setup G L f t) (E : Subgroup L) :
    t ∈ normalizer ((E.map L.subtype : Subgroup G) : Set G) :=
  mem_normalizer_fintype fun x hx => by
    rw [← mem_centralizer_iff.1 h.htL x (map_subtype_le E hx), mul_inv_cancel_right]
    exact hx

omit [Finite G] in
theorem map_inf_centralizer_map {E N : Subgroup L} (hE : E ⊓ centralizer (E : Set L) = N) :
    E.map L.subtype ⊓ centralizer ((E.map L.subtype : Subgroup G) : Set G) =
      N.map L.subtype := by
  rw [← hE]
  apply le_antisymm
  · rintro x ⟨⟨p, hp, rfl⟩, hpc⟩
    exact ⟨p, Subgroup.mem_inf.2 ⟨hp, mem_centralizer_of_coe_mem hpc⟩, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact Subgroup.mem_inf.2 ⟨⟨p, (Subgroup.mem_inf.1 hp).1, rfl⟩,
      coe_mem_centralizer_of_mem (Subgroup.mem_inf.1 hp).2⟩

omit [Finite G] in
theorem mul_self_eq_one_of_mem_V_map {q : ℕ} (d : TrialityD4Data L q) {v : G}
    (hv : v ∈ d.V.map L.subtype) : v * v = 1 := by
  obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hv
  change ((d.x₆ a * d.x₆ a : L) : G) = 1
  rw [d.x₆_mul_self]
  rfl

theorem yamadaC₁_le_normalizer_D_D1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaC₁ d t ≤ normalizer ((d.D.map L.subtype : Subgroup G) : Set G) :=
  (yamadaC₁_le d t).trans (h.yamada_5_3_1_all d).2.2.1

theorem t_mem_yamadaC₁_D1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) : t ∈ yamadaC₁ d t :=
  h.tD_le_yamadaC₁ d (mem_sup_right (mem_zpowers t))

theorem D_map_le_yamadaC₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    d.D.map L.subtype ≤ yamadaC₁ d t :=
  le_sup_left.trans (h.tD_le_yamadaC₁ d)

omit [Finite G] in
theorem sylowJ₀_map_le_D_map {q : ℕ} (d : TrialityD4Data L q) :
    d.sylowJ₀.map L.subtype ≤ d.D.map L.subtype := by
  rw [← D_map_inf_centralizer_J₀ d]
  exact inf_le_left

omit [Finite G] in
theorem sylowJ₀_map_le_centralizer_J₀ {q : ℕ} (d : TrialityD4Data L q) :
    d.sylowJ₀.map L.subtype ≤ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) := by
  rw [← D_map_inf_centralizer_J₀ d]
  exact inf_le_right

omit [Finite G] in
theorem jZeroLayer_le_centralizer_J₀ {q : ℕ} (d : TrialityD4Data L q) :
    jZeroLayer d ≤ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
  map_subtype_le _

theorem sylowJ₀_map_le_jZeroLayer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    d.sylowJ₀.map L.subtype ≤ jZeroLayer d :=
  (map_mono d.sylowJ₀_le_leviJ₀).trans (h.leviJ₀_map_le_jZeroLayer d hlay)

theorem D_map_inf_jZeroLayer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    d.D.map L.subtype ⊓ jZeroLayer d = d.sylowJ₀.map L.subtype := by
  apply le_antisymm
  · rw [← D_map_inf_centralizer_J₀ d]
    exact inf_le_inf_left _ (jZeroLayer_le_centralizer_J₀ d)
  · exact le_inf (sylowJ₀_map_le_D_map d) (h.sylowJ₀_map_le_jZeroLayer d hlay)

omit [Finite G] in
theorem J_map_le_centralizer_J₀ {q : ℕ} (d : TrialityD4Data L q) :
    d.J.map L.subtype ≤ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) := by
  have e : ∀ x y : (d.Γ₀)ˣ × d.Γˣ, d.torus x * d.torus y = d.torus y * d.torus x :=
    fun x y => by rw [← map_mul, ← map_mul, mul_comm]
  rintro _ ⟨j, ⟨a, rfl⟩, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨j₀, ⟨b, rfl⟩, rfl⟩
  exact congrArg Subtype.val (e ((powMonoidHom (q - 1)) b) a)

omit [Finite G] in
theorem D_map_le_yamadaD₁ {q : ℕ} (d : TrialityD4Data L q) :
    d.D.map L.subtype ≤ yamadaD₁ d t :=
  le_sup_right

theorem yamadaD₁_le_yamadaC₁_D1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaD₁ d t ≤ yamadaC₁ d t :=
  sup_le inf_le_left (h.D_map_le_yamadaC₁ d)

theorem coe_yamadaD₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    ((yamadaD₁ d t : Subgroup G) : Set G) =
      ((yamadaC₁ d t ⊓ jZeroLayer d : Subgroup G) : Set G) *
        ((d.D.map L.subtype : Subgroup G) : Set G) :=
  coe_mul_of_left_le_normalizer_right _ _ (inf_le_left.trans (h.yamadaC₁_le_normalizer_D_D1 d))

end Inclusions

section Six

theorem card_sup_zpowers_of_not_mem (h : Setup G L f t) {A : Subgroup G}
    (htA : t ∈ normalizer (A : Set G)) (ht : t ∉ A) :
    Nat.card (A ⊔ zpowers t : Subgroup G) = 2 * Nat.card A := by
  have hAt : A ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 (Subgroup.mem_inf.1 hy).2
    rcases h.zpow_eq_one_or_eq k with h1 | h1
    · rw [h1]
      exact one_mem _
    · exact absurd (h1 ▸ (Subgroup.mem_inf.1 hy).1) ht
  have hset := coe_mul_of_right_le_normalizer_left A (zpowers t) ((zpowers_le).2 htA)
  have h1 := ncard_mul_mul_card_inf A (zpowers t)
  rw [hAt, card_bot, mul_one, h.card_zpowers_t, ← hset, ← Nat.card_coe_set_eq] at h1
  exact h1.trans (mul_comm _ _)

theorem card_yamadaC₁_D1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    Nat.card (yamadaC₁ d t) = 2 * (2 ^ f) ^ 10 := by
  have h1 := Subgroup.relIndex_mul_card (d.D.map L.subtype ⊔ zpowers t) (yamadaC₁ d t)
  rw [inf_eq_left.2 (h.tD_le_yamadaC₁ d), h.relIndex_tD_yamadaC₁ d,
    h.card_sup_zpowers (map_subtype_le _), card_map_of_injective L.subtype_injective,
    d.card_D] at h1
  rw [← h1]
  ring

theorem le_card_yamadaC₁_inf_jZeroLayer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    (2 ^ f) ^ 4 ≤ Nat.card (yamadaC₁ d t ⊓ jZeroLayer d : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 (yamadaC₁ d t ⊓
      centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) : Subgroup G) :=
    ((h.isPGroup_yamadaR₁ d).to_le le_sup_left).to_le inf_le_left
  have hP₀ : d.sylowJ₀.map L.subtype ⊔ zpowers t ≤ yamadaC₁ d t ⊓
      centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
    sup_le (le_inf ((sylowJ₀_map_le_D_map d).trans (h.D_map_le_yamadaC₁ d))
      (sylowJ₀_map_le_centralizer_J₀ d))
      ((zpowers_le).2 (Subgroup.mem_inf.2 ⟨h.t_mem_yamadaC₁_D1 d, h.t_mem_centralizer_J₀ d⟩))
  have h1 := h.card_le_two_mul_card_inf_jZeroLayer d hlay le_rfl inf_le_right hQ hP₀
  rw [h.card_yamadaC₁_inf_centralizer_J₀ d, inf_assoc,
    inf_eq_right.2 (jZeroLayer_le_centralizer_J₀ d)] at h1
  exact Nat.le_of_mul_le_mul_left h1 (by norm_num)

theorem t_not_mem_yamadaD₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : t ∉ yamadaD₁ d t := by
  intro ht
  have ht' : t ∈ ((yamadaD₁ d t : Subgroup G) : Set G) := ht
  rw [h.coe_yamadaD₁ d] at ht'
  obtain ⟨e, he, n, hn, hen⟩ := ht'
  have heE : e ∈ jZeroLayer d := (Subgroup.mem_inf.1 he).2
  have hnH : n ∈ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) := by
    have e1 : n = e⁻¹ * t := by rw [← hen, inv_mul_cancel_left]
    rw [e1]
    exact mul_mem (inv_mem (jZeroLayer_le_centralizer_J₀ d heE)) (h.t_mem_centralizer_J₀ d)
  have hnE : n ∈ jZeroLayer d :=
    h.sylowJ₀_map_le_jZeroLayer d hlay
      ((D_map_inf_centralizer_J₀ d).le (Subgroup.mem_inf.2 ⟨hn, hnH⟩))
  apply h.t_not_mem_jZeroLayer d hlay
  rw [← hen]
  exact mul_mem heE hnE

theorem t_mem_normalizer_yamadaD₁_D1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    t ∈ normalizer (yamadaD₁ d t : Set G) :=
  mem_normalizer_sup (mem_normalizer_inf_D4 (le_normalizer (h.t_mem_yamadaC₁_D1 d))
    (le_normalizer_jZeroLayer d (h.t_mem_centralizer_J₀ d))) (h.t_mem_normalizer_map_D1 d.D)

theorem card_yamadaD₁_mul (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    Nat.card (yamadaD₁ d t) * (2 ^ f) ^ 3 =
      Nat.card (yamadaC₁ d t ⊓ jZeroLayer d : Subgroup G) * (2 ^ f) ^ 9 := by
  have h1 := ncard_mul_mul_card_inf (yamadaC₁ d t ⊓ jZeroLayer d) (d.D.map L.subtype)
  have hinf : yamadaC₁ d t ⊓ jZeroLayer d ⊓ d.D.map L.subtype = d.sylowJ₀.map L.subtype := by
    rw [inf_comm (yamadaC₁ d t ⊓ jZeroLayer d), ← inf_assoc,
      inf_eq_left.2 (h.D_map_le_yamadaC₁ d), h.D_map_inf_jZeroLayer d hlay]
  rw [hinf, ← h.coe_yamadaD₁ d, ← Nat.card_coe_set_eq,
    card_map_of_injective L.subtype_injective, card_map_of_injective L.subtype_injective,
    d.card_sylowJ₀, d.card_D] at h1
  exact h1

theorem card_yamadaD₁_and (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    Nat.card (yamadaD₁ d t) = (2 ^ f) ^ 10 ∧
      Nat.card (yamadaC₁ d t ⊓ jZeroLayer d : Subgroup G) = (2 ^ f) ^ 4 ∧
      yamadaC₁ d t = yamadaD₁ d t ⊔ zpowers t := by
  have h1 := h.card_yamadaD₁_mul d hlay
  have h2 := h.le_card_yamadaC₁_inf_jZeroLayer d hlay
  have hle : yamadaD₁ d t ⊔ zpowers t ≤ yamadaC₁ d t :=
    sup_le (h.yamadaD₁_le_yamadaC₁_D1 d) ((zpowers_le).2 (h.t_mem_yamadaC₁_D1 d))
  have hcardt := h.card_sup_zpowers_of_not_mem (h.t_mem_normalizer_yamadaD₁_D1 d)
    (h.t_not_mem_yamadaD₁ d hlay)
  have h3 := card_le_of_le hle
  rw [hcardt, h.card_yamadaC₁_D1 d] at h3
  have hpos3 : 0 < (2 ^ f) ^ 3 := by positivity
  have hpos9 : 0 < (2 ^ f) ^ 9 := by positivity
  have h4 : Nat.card (yamadaD₁ d t) ≤ (2 ^ f) ^ 10 := Nat.le_of_mul_le_mul_left h3 (by norm_num)
  have h5 : (2 ^ f) ^ 10 ≤ Nat.card (yamadaD₁ d t) := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos3
    calc (2 ^ f) ^ 10 * (2 ^ f) ^ 3 = (2 ^ f) ^ 4 * (2 ^ f) ^ 9 := by ring
      _ ≤ Nat.card (yamadaC₁ d t ⊓ jZeroLayer d : Subgroup G) * (2 ^ f) ^ 9 :=
          Nat.mul_le_mul_right _ h2
      _ = Nat.card (yamadaD₁ d t) * (2 ^ f) ^ 3 := h1.symm
  have hn := le_antisymm h4 h5
  refine ⟨hn, ?_, ?_⟩
  · refine Nat.eq_of_mul_eq_mul_right hpos9 ?_
    rw [← h1, hn]
    ring
  · refine (eq_of_le_of_card_ge hle ?_).symm
    rw [hcardt, h.card_yamadaC₁_D1 d, hn]

theorem card_yamadaC₁_inf_jZeroLayer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    Nat.card (yamadaC₁ d t ⊓ jZeroLayer d : Subgroup G) = (2 ^ f) ^ 4 :=
  (h.card_yamadaD₁_and d hlay).2.1

theorem map_normalizer_V_le_normalizer_yamadaD₁ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) :
    (normalizer (d.V : Set L)).map L.subtype ≤ normalizer (yamadaD₁ d t : Set G) := by
  set K := (normalizer (yamadaD₁ d t : Set G)).comap L.subtype with hK
  have hNC : ∀ l : L, l ∈ normalizer (d.V : Set L) →
      (l : G) ∈ normalizer ((yamadaC₁ d t : Subgroup G) : Set G) := fun l hl =>
    le_normalizer_yamadaC₁ d t (h.centralizer_inf_normalizer_V_le d
      (Subgroup.mem_inf.2 ⟨h.L_le_centralizer l.2, coe_mem_normalizer_map hl⟩))
  have hS : d.S ≤ K := by
    intro s hs
    show (s : G) ∈ normalizer (yamadaD₁ d t : Set G)
    refine mem_normalizer_fintype fun x hx => ?_
    have h1 := h.commutator_mem_D_of_core d (h.two_core_C₁_all d) (h.yamadaD₁_le_yamadaC₁_D1 d hx)
      (⟨s, S_le_N₀ d hs, rfl⟩ : (s : G) ∈ (d.D ⊔ d.leviShort).map L.subtype)
    have e : (s : G) * x * (s : G)⁻¹ = (x * s * x⁻¹ * (s : G)⁻¹)⁻¹ * x := by group
    rw [e]
    exact mul_mem (inv_mem (D_map_le_yamadaD₁ d h1)) hx
  have hJ : d.J ≤ K := by
    intro j hj
    show (j : G) ∈ normalizer (yamadaD₁ d t : Set G)
    exact mem_normalizer_sup (mem_normalizer_inf_D4 (hNC j (d.J_le_normalizer_V hj))
      (le_normalizer_jZeroLayer d (J_map_le_centralizer_J₀ d ⟨j, hj, rfl⟩)))
      (coe_mem_normalizer_map (d.J_le_normalizer_D hj))
  have hu : d.u ∈ K := by
    show (d.u : G) ∈ normalizer (yamadaD₁ d t : Set G)
    exact mem_normalizer_sup (mem_normalizer_inf_D4 (hNC d.u d.u_mem_normalizer_V)
      (normalizer_le_normalizer_jZeroLayer d (coe_mem_normalizer_map d.u_mem_normalizer_J₀)))
      (coe_mem_normalizer_map d.u_mem_normalizer_D)
  rintro _ ⟨g, hg, rfl⟩
  show g ∈ K
  rcases d.normalizer_V_cases hg with hB | ⟨x, hx, j, hj, y, hy, rfl⟩
  · exact (sup_le hS hJ : d.S ⊔ d.J ≤ K) hB
  · exact mul_mem (mul_mem (mul_mem (hS hx) (hJ hj)) hu) (hS (d.U₁_le_S hy))

theorem yamada_5_6_1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaC₁ d t = yamadaD₁ d t ⊔ zpowers t ∧ t ∉ yamadaD₁ d t ∧
      (normalizer (d.V : Set L)).map L.subtype ≤ normalizer (yamadaD₁ d t : Set G) :=
  ⟨(h.card_yamadaD₁_and d hlay).2.2, h.t_not_mem_yamadaD₁ d hlay,
    h.map_normalizer_V_le_normalizer_yamadaD₁ d⟩

end Six

section Center

theorem yamadaD₁_inf_centralizer_J₀ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaD₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) =
      yamadaC₁ d t ⊓ jZeroLayer d := by
  have hle : yamadaC₁ d t ⊓ jZeroLayer d ≤
      yamadaD₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
    le_inf le_sup_left (inf_le_right.trans (jZeroLayer_le_centralizer_J₀ d))
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [h.card_yamadaC₁_inf_jZeroLayer d hlay]
  have htQ : t ∈ normalizer ((yamadaD₁ d t ⊓
      centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf_D4 (h.t_mem_normalizer_yamadaD₁_D1 d)
      (le_normalizer (h.t_mem_centralizer_J₀ d))
  have htQ' : t ∉ yamadaD₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
    fun ht => h.t_not_mem_yamadaD₁ d hlay (Subgroup.mem_inf.1 ht).1
  have hle' : (yamadaD₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) ⊔
      zpowers t ≤ yamadaC₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
    sup_le (inf_le_inf_right _ (h.yamadaD₁_le_yamadaC₁_D1 d))
      ((zpowers_le).2 (Subgroup.mem_inf.2 ⟨h.t_mem_yamadaC₁_D1 d, h.t_mem_centralizer_J₀ d⟩))
  have h1 := card_le_of_le hle'
  rw [h.card_sup_zpowers_of_not_mem htQ htQ', h.card_yamadaC₁_inf_centralizer_J₀ d] at h1
  exact Nat.le_of_mul_le_mul_left h1 (by norm_num)

theorem exists_isSylowOf_jZeroLayer (d : TrialityD4Data L (2 ^ f)) {Q : Subgroup G}
    (hQH : Q ≤ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) (hQ : IsPGroup 2 Q)
    (htQ : t ∈ Q) :
    ∃ X : Subgroup G, IsSylowOf 2 X (jZeroLayer d) ∧ t ∈ normalizer (X : Set G) ∧
      Q ⊓ jZeroLayer d ≤ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := centralizer ((d.J₀.map L.subtype : Subgroup G) :
    Set G))).exists_le_sylow
  have hT : IsSylowOf 2 ((S : Subgroup _).map (centralizer ((d.J₀.map L.subtype : Subgroup G) :
      Set G)).subtype) (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) := ⟨S, rfl⟩
  have hQT : Q ≤ (S : Subgroup _).map
      (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)).subtype :=
    fun x hx => ⟨⟨x, hQH hx⟩, hS hx, rfl⟩
  refine ⟨_ ⊓ jZeroLayer d, hT.inf_of_le_normalizer (jZeroLayer_le_centralizer_J₀ d)
    (le_normalizer_jZeroLayer d), ?_, inf_le_inf_right _ hQT⟩
  have htT := hQT htQ
  exact mem_normalizer_fintype fun x hx => Subgroup.mem_inf.2
    ⟨mul_mem (mul_mem htT (Subgroup.mem_inf.1 hx).1) (inv_mem htT),
      (mem_normalizer_iff.1 (le_normalizer_jZeroLayer d (hQH htQ)) x).1 (Subgroup.mem_inf.1 hx).2⟩

theorem yamadaD₁_inf_centralizer_J₀_eq_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {X : Subgroup G}
    (hX : IsSylowOf 2 X (jZeroLayer d)) (htX : t ∈ normalizer (X : Set G))
    (hQX : yamadaD₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ≤ X) :
    yamadaD₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) =
      d.sylowJ₀.map L.subtype ⊔ (X ⊓ centralizer (X : Set G)) := by
  have hPQ : d.sylowJ₀.map L.subtype ≤
      yamadaD₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
    le_inf ((sylowJ₀_map_le_D_map d).trans (D_map_le_yamadaD₁ d))
      (sylowJ₀_map_le_centralizer_J₀ d)
  have hPX := hPQ.trans hQX
  obtain ⟨hCt, hsh⟩ := h.sylowShape_of_isSylowOf_jZeroLayer d hlay hX htX hPX
  have hZt := h.center_inf_centralizer_eq_V d hlay hX htX hPX
  have hcardZ : Nat.card (X ⊓ centralizer (X : Set G) : Subgroup G) =
      Nat.card (X ⊓ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2 := by
    rw [hZt, card_map_of_injective L.subtype_injective, d.card_V, hsh.card_center]
  have hCP : X ⊓ centralizer ((X ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ≤
      X ⊓ centralizer (X : Set G) := by
    rw [hCt]
    exact hsh.inf_centralizer_le
  have hN := inf_normalizer_le_sup_center_D4 h.t_mul_t htX hsh.center_mul_self hcardZ hCP
  rw [hCt] at hN
  have hQN : yamadaD₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ≤
      X ⊓ normalizer ((d.sylowJ₀.map L.subtype : Subgroup G) : Set G) := by
    intro x hx
    refine Subgroup.mem_inf.2 ⟨hQX hx, ?_⟩
    rw [← D_map_inf_centralizer_J₀ d]
    exact mem_normalizer_inf_D4
      (h.yamadaC₁_le_normalizer_D_D1 d (h.yamadaD₁_le_yamadaC₁_D1 d (Subgroup.mem_inf.1 hx).1))
      (le_normalizer (Subgroup.mem_inf.1 hx).2)
  have hinf : d.sylowJ₀.map L.subtype ⊓ (X ⊓ centralizer (X : Set G)) = d.V.map L.subtype := by
    rw [← hZt, ← hCt]
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  have hcard : Nat.card (d.sylowJ₀.map L.subtype ⊔ (X ⊓ centralizer (X : Set G)) :
      Subgroup G) = (2 ^ f) ^ 4 := by
    have h1 := ncard_mul_mul_card_inf (d.sylowJ₀.map L.subtype) (X ⊓ centralizer (X : Set G))
    rw [hinf, ← coe_mul_of_right_le_normalizer_left _ _ (inf_centralizer_le_normalizer_D4 hPX),
      ← Nat.card_coe_set_eq, card_map_of_injective L.subtype_injective,
      card_map_of_injective L.subtype_injective, d.card_sylowJ₀, d.card_V,
      hsh.card_center] at h1
    exact Nat.eq_of_mul_eq_mul_right (by positivity) (h1.trans (by ring))
  have hQcard : Nat.card (yamadaD₁ d t ⊓
      centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) : Subgroup G) = (2 ^ f) ^ 4 := by
    rw [h.yamadaD₁_inf_centralizer_J₀ d hlay]
    exact h.card_yamadaC₁_inf_jZeroLayer d hlay
  exact eq_of_le_of_card_ge (hQN.trans hN) (le_of_eq (by rw [hcard, hQcard]))

theorem commute_x₄_of_mem_yamadaC₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {b : G}
    (hb : b ∈ yamadaC₁ d t)
    (hbH : b ∈ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) (a : d.Γ) :
    b * (d.x₄ a : G) = d.x₄ a * b := by
  have hVC : d.V.map L.subtype ≤ centralizer ((yamadaC₁ d t : Subgroup G) : Set G) :=
    le_centralizer_iff.1 (h.yamada_5_3_1_all d).2.2.2.2.2
  have hsq : ∀ x ∈ yamadaC₁ d t, x * x ∈ d.V.map L.subtype := fun x hx => by
    rw [← h.yamada_5_3_5 d, ← sq]
    exact sq_mem_mhoOne hx
  have hx₄C : ∀ c : d.Γ, ((d.x₄ c : L) : G) ∈ yamadaC₁ d t := fun c =>
    h.D_map_le_yamadaC₁ d ⟨_, d.F_le_D (d.W_le_F (d.x₄_mem_W c)), rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : d.Γ → G, ∀ c, ψ c = b * (d.x₄ c : G) * b⁻¹ * ((d.x₄ c : L) : G)⁻¹ :=
    ⟨_, fun _ => rfl⟩
  have hψV : ∀ c, ψ c ∈ d.V.map L.subtype := fun c => by
    rw [hψ]
    exact commutator_mem_of_mul_self_mem_D4 hVC hsq hb (hx₄C c)
  have hψadd : ∀ c c', ψ (c + c') = ψ c * ψ c' := fun c c' => by
    have hcomm : ((d.x₄ c : L) : G) * ψ c' = ψ c' * (d.x₄ c : G) :=
      mem_centralizer_iff.1 (hVC (hψV c')) _ (hx₄C c)
    calc ψ (c + c') = b * (d.x₄ c : G) * b⁻¹ * ψ c' * ((d.x₄ c : L) : G)⁻¹ := by
          rw [hψ, hψ, d.x₄_add, Subgroup.coe_mul]
          group
      _ = b * (d.x₄ c : G) * b⁻¹ * ((d.x₄ c : L) : G)⁻¹ * (((d.x₄ c : L) : G) * ψ c') *
          ((d.x₄ c : L) : G)⁻¹ := by group
      _ = b * (d.x₄ c : G) * b⁻¹ * ((d.x₄ c : L) : G)⁻¹ * (ψ c' * (d.x₄ c : G)) *
          ((d.x₄ c : L) : G)⁻¹ := by rw [hcomm]
      _ = ψ c * ψ c' := by rw [hψ c]; group
  obtain ⟨m, hm1, hm⟩ := d.exists_mem_ker_nmUnits_ne_one
  have hj : ((d.torus (1, m) : L) : G) ∈ d.J₀.map L.subtype := ⟨_, d.torus_one_mem_J₀ hm1, rfl⟩
  have hjb : ((d.torus (1, m) : L) : G) * b * ((d.torus (1, m) : L) : G)⁻¹ = b := by
    rw [mem_centralizer_iff.1 hbH _ hj, mul_inv_cancel_right]
  have hconj : ∀ c, ((d.torus (1, m) : L) : G) * (d.x₄ c : G) * ((d.torus (1, m) : L) : G)⁻¹ =
      (d.x₄ ((m : d.Γ)⁻¹ * c) : G) := fun c => by
    rw [← d.torus_one_conj_x₄ hm1 c]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hψν : ∀ c, ψ ((m : d.Γ)⁻¹ * c) = ψ c := fun c => by
    have hjψ : ((d.torus (1, m) : L) : G) * ψ c * ((d.torus (1, m) : L) : G)⁻¹ = ψ c := by
      rw [← mem_centralizer_iff.1 (J₀_map_le_centralizer_Y d hj) _ (map_mono d.V_le_Y (hψV c)),
        mul_inv_cancel_right]
    rw [← hjψ]
    calc ψ ((m : d.Γ)⁻¹ * c) = (((d.torus (1, m) : L) : G) * b * ((d.torus (1, m) : L) : G)⁻¹) *
          (((d.torus (1, m) : L) : G) * (d.x₄ c : G) * ((d.torus (1, m) : L) : G)⁻¹) *
          (((d.torus (1, m) : L) : G) * b * ((d.torus (1, m) : L) : G)⁻¹)⁻¹ *
          (((d.torus (1, m) : L) : G) * (d.x₄ c : G) * ((d.torus (1, m) : L) : G)⁻¹)⁻¹ := by
          rw [hjb, hconj, hψ]
      _ = ((d.torus (1, m) : L) : G) * ψ c * ((d.torus (1, m) : L) : G)⁻¹ := by rw [hψ]; group
  have hν : (1 : d.Γ) + (m : d.Γ)⁻¹ ≠ 0 := by
    intro h0
    have h1 : (m : d.Γ)⁻¹ = 1 :=
      add_left_cancel (h0.trans (CharTwo.add_self_eq_zero (1 : d.Γ)).symm)
    exact hm (Units.ext (by rw [Units.val_one]; exact inv_eq_one.1 h1))
  have hc : a * (1 + (m : d.Γ)⁻¹)⁻¹ + (m : d.Γ)⁻¹ * (a * (1 + (m : d.Γ)⁻¹)⁻¹) = a := by
    rw [show a * (1 + (m : d.Γ)⁻¹)⁻¹ + (m : d.Γ)⁻¹ * (a * (1 + (m : d.Γ)⁻¹)⁻¹) =
      a * ((1 + (m : d.Γ)⁻¹)⁻¹ * (1 + (m : d.Γ)⁻¹)) by ring, inv_mul_cancel₀ hν, mul_one]
  have hψa : ψ a = 1 := by
    rw [← hc, hψadd, hψν]
    exact mul_self_eq_one_of_mem_V_map d (hψV _)
  rw [hψ] at hψa
  have := mul_inv_eq_one.1 hψa
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

theorem yamadaV₁_eq_center (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {X : Subgroup G}
    (hX : IsSylowOf 2 X (jZeroLayer d)) (htX : t ∈ normalizer (X : Set G))
    (hQX : yamadaD₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ≤ X) :
    yamadaV₁ d t = X ⊓ centralizer (X : Set G) := by
  have hQ := h.yamadaD₁_inf_centralizer_J₀_eq_sup d hlay hX htX hQX
  have hPQ : d.sylowJ₀.map L.subtype ≤
      yamadaD₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
    le_inf ((sylowJ₀_map_le_D_map d).trans (D_map_le_yamadaD₁ d))
      (sylowJ₀_map_le_centralizer_J₀ d)
  have hPX := hPQ.trans hQX
  have hZt := h.center_inf_centralizer_eq_V d hlay hX htX hPX
  have hVB : d.V.map L.subtype ≤ X ⊓ centralizer (X : Set G) := by
    rw [← hZt]
    exact inf_le_left
  have hBQ : X ⊓ centralizer (X : Set G) ≤
      yamadaD₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) := by
    rw [hQ]
    exact le_sup_right
  have hEX : yamadaC₁ d t ⊓ jZeroLayer d ≤ X := by
    rw [← h.yamadaD₁_inf_centralizer_J₀ d hlay]
    exact hQX
  have hcen : (yamadaD₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) ⊓
      centralizer ((yamadaD₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :
        Subgroup G) : Set G) = X ⊓ centralizer (X : Set G) := by
    rw [hQ]
    refine center_sup_center_D4 hPX ?_
    rw [map_inf_centralizer_map d.sylowJ₀_inf_centralizer]
    exact hVB
  have hu : ∀ z ∈ X ⊓ centralizer (X : Set G),
      ((d.u : L) : G)⁻¹ * z * (d.u : G) ∈ X ⊓ centralizer (X : Set G) := by
    have huQ : ((d.u : L) : G) ∈ normalizer ((yamadaD₁ d t ⊓
        centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) : Subgroup G) : Set G) :=
      mem_normalizer_inf_D4 (h.map_normalizer_V_le_normalizer_yamadaD₁ d
        ⟨d.u, d.u_mem_normalizer_V, rfl⟩)
        (mem_normalizer_centralizer_D4 (coe_mem_normalizer_map d.u_mem_normalizer_J₀))
    have huZ := mem_normalizer_inf_D4 huQ (mem_normalizer_centralizer_D4 huQ)
    rw [hcen] at huZ
    exact fun z hz => (mem_normalizer_iff''.1 huZ z).1 hz
  have hBW : ∀ z ∈ X ⊓ centralizer (X : Set G), d.W ≤ (centralizer ({z} : Set G)).comap
      L.subtype := by
    intro z hz
    have hzC : z ∈ yamadaC₁ d t :=
      h.yamadaD₁_le_yamadaC₁_D1 d (Subgroup.mem_inf.1 (hBQ hz)).1
    have hzH := (Subgroup.mem_inf.1 (hBQ hz)).2
    refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      exact mem_centralizer_singleton_iff.2 (h.commute_x₄_of_mem_yamadaC₁ d hzC hzH a).symm
    · intro y hy
      have hyX : (y : G) ∈ X := hPX ⟨y, le_inf (d.Y_le_W.trans (d.W_le_F.trans
        (d.F_le_D.trans d.D_le_S))) d.Y_le_centralizer_J₀ hy, rfl⟩
      exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 _ hyX)
  have hBD : ∀ z ∈ X ⊓ centralizer (X : Set G), d.D ≤ (centralizer ({z} : Set G)).comap
      L.subtype := by
    intro z hz
    refine d.D_le_sup_conj_W.trans (sup_le (hBW z hz) ?_)
    rintro _ ⟨w, hw, rfl⟩
    have hc : (w : G) * (((d.u : L) : G)⁻¹ * z * (d.u : G)) =
        (((d.u : L) : G)⁻¹ * z * (d.u : G)) * w :=
      mem_centralizer_singleton_iff.1 (hBW _ (hu z hz) hw)
    rw [mem_comap, mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype,
      Subgroup.coe_mul, Subgroup.coe_inv]
    calc (d.u : G) * w * ((d.u : L) : G)⁻¹ * z =
        (d.u : G) * ((w : G) * (((d.u : L) : G)⁻¹ * z * (d.u : G))) * ((d.u : L) : G)⁻¹ := by
          group
      _ = (d.u : G) * ((((d.u : L) : G)⁻¹ * z * (d.u : G)) * w) * ((d.u : L) : G)⁻¹ := by
          rw [hc]
      _ = z * ((d.u : G) * w * ((d.u : L) : G)⁻¹) := by group
  have hBc : ∀ z ∈ X ⊓ centralizer (X : Set G), yamadaD₁ d t ≤ centralizer ({z} : Set G) := by
    intro z hz
    refine sup_le (fun x hx => mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 x (hEX hx))) ?_
    rintro _ ⟨n, hn, rfl⟩
    exact hBD z hz hn
  have hBV : X ⊓ centralizer (X : Set G) ≤ yamadaV₁ d t := fun z hz =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (hBQ hz)).1, mem_centralizer_iff.2 fun x hx =>
      mem_centralizer_singleton_iff.1 (hBc z hz hx)⟩
  refine le_antisymm (fun z hz => ?_) hBV
  obtain ⟨hzD, hzc⟩ := Subgroup.mem_inf.1 hz
  have hBN : X ⊓ centralizer (X : Set G) ≤
      normalizer ((d.D.map L.subtype : Subgroup G) : Set G) := fun b hb =>
    mem_normalizer_fintype fun n hn => by
      rw [← mem_centralizer_singleton_iff.1 (hBc b hb (D_map_le_yamadaD₁ d hn)),
        mul_inv_cancel_right]
      exact hn
  have hD₁ : yamadaD₁ d t ≤ (X ⊓ centralizer (X : Set G)) ⊔ d.D.map L.subtype := by
    refine sup_le ?_ le_sup_right
    rw [← h.yamadaD₁_inf_centralizer_J₀ d hlay, hQ]
    exact sup_le ((sylowJ₀_map_le_D_map d).trans le_sup_right) le_sup_left
  have hzBD : z ∈ (((X ⊓ centralizer (X : Set G)) ⊔ d.D.map L.subtype : Subgroup G) :
      Set G) := hD₁ hzD
  rw [coe_mul_of_left_le_normalizer_right _ _ hBN] at hzBD
  obtain ⟨b, hb, n, hn, rfl⟩ := hzBD
  have hbc : b ∈ centralizer (yamadaD₁ d t : Set G) := (Subgroup.mem_inf.1 (hBV hb)).2
  have hnc : n ∈ centralizer (yamadaD₁ d t : Set G) := by
    have := mul_mem (inv_mem hbc) hzc
    rwa [inv_mul_cancel_left] at this
  have hnV : n ∈ d.V.map L.subtype := by
    rw [← map_inf_centralizer_map d.D_inf_centralizer_D]
    exact Subgroup.mem_inf.2 ⟨hn, mem_centralizer_iff.2 fun y hy =>
      mem_centralizer_iff.1 hnc y (D_map_le_yamadaD₁ d hy)⟩
  exact mul_mem hb (hVB hnV)

theorem yamada_5_6_3 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) (X : Subgroup G)
    (hX : IsSylowOf 2 X (jZeroLayer d)) (htX : t ∈ normalizer (X : Set G))
    (hQX : yamadaD₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ≤ X) :
    yamadaV₁ d t = X ⊓ centralizer (X : Set G) ∧ (∀ x ∈ X, x * x ∈ yamadaV₁ d t) ∧
      ∃ _ : ((yamadaV₁ d t).subgroupOf X).Normal,
        IsElemAbelian 2 (⊤ : Subgroup (X ⧸ (yamadaV₁ d t).subgroupOf X)) := by
  have hV := h.yamadaV₁_eq_center d hlay hX htX hQX
  have hPX : d.sylowJ₀.map L.subtype ≤ X :=
    (le_inf ((sylowJ₀_map_le_D_map d).trans (D_map_le_yamadaD₁ d))
      (sylowJ₀_map_le_centralizer_J₀ d)).trans hQX
  obtain ⟨-, hsh⟩ := h.sylowShape_of_isSylowOf_jZeroLayer d hlay hX htX hPX
  have hsq : ∀ x ∈ X, x * x ∈ yamadaV₁ d t := fun x hx => by
    rw [hV]
    exact hsh.mul_self_mem x hx
  have hN : ((yamadaV₁ d t).subgroupOf X).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    rw [hV] at hn ⊢
    have hc := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hn).2 _ g.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hc, mul_inv_cancel_right]
    exact hn⟩
  have hcomm : ∀ p r : X ⧸ (yamadaV₁ d t).subgroupOf X, p * r = r * p := by
    intro p r
    induction p using QuotientGroup.induction_on with
    | H x =>
    induction r using QuotientGroup.induction_on with
    | H y =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    have := commutator_mem_center_D4 hsh.mul_self_mem (inv_mem y.2) (inv_mem x.2)
    rw [inv_inv, inv_inv] at this
    rw [hV]
    simpa [mul_assoc] using this
  refine ⟨hV, hsq, hN, ⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x _ => ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hcomm _ _
  · induction x using QuotientGroup.induction_on with
    | H x =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, Subgroup.coe_pow, sq]
    exact hsq x x.2

theorem yamadaV₁_le_yamadaL₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaV₁ d t ≤ yamadaL₂ d t := by
  intro z hz
  obtain ⟨hzD, hzc⟩ := Subgroup.mem_inf.1 hz
  have hzR : z ∈ ((yamadaR₂ d t : Subgroup G) : Set G) :=
    h.yamadaC₁_le_yamadaR₂ d (h.yamadaD₁_le_yamadaC₁_D1 d hzD)
  rw [h.coe_yamadaR₂ d] at hzR
  obtain ⟨l, hl, s, hs, rfl⟩ := hzR
  have hzY : l * s ∈ centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) :=
    mem_centralizer_iff.2 fun y hy => mem_centralizer_iff.1 hzc y (D_map_le_yamadaD₁ d
      (map_mono (d.Y_le_W.trans (d.W_le_F.trans d.F_le_D)) hy))
  have hlY := (h.yamada_5_3_2 d).2.2.2.2.2.2 hl
  have hsY : s ∈ centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
    have := mul_mem (inv_mem hlY) hzY
    rwa [inv_mul_cancel_left] at this
  have hsM : s ∈ d.M.map L.subtype := by
    obtain ⟨s', hs', rfl⟩ := hs
    refine ⟨s', ?_, rfl⟩
    rw [← d.S_inf_centralizer_Y]
    exact Subgroup.mem_inf.2 ⟨hs', mem_centralizer_of_coe_mem hsY⟩
  exact mul_mem hl (h.tM_le_yamadaL₂ d (mem_sup_left hsM))

theorem exists_isSylowOf_jZeroLayer_yamadaD₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    ∃ X : Subgroup G, IsSylowOf 2 X (jZeroLayer d) ∧ t ∈ normalizer (X : Set G) ∧
      yamadaD₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ≤ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (yamadaC₁ d t ⊓
      centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) : Subgroup G) :=
    ((h.isPGroup_yamadaR₁ d).to_le le_sup_left).to_le inf_le_left
  obtain ⟨X, hX, htX, hQX⟩ := exists_isSylowOf_jZeroLayer d inf_le_right hQ2
    (Subgroup.mem_inf.2 ⟨h.t_mem_yamadaC₁_D1 d, h.t_mem_centralizer_J₀ d⟩)
  refine ⟨X, hX, htX, ?_⟩
  rw [h.yamadaD₁_inf_centralizer_J₀ d hlay]
  exact le_trans (le_inf (le_inf inf_le_left (inf_le_right.trans
    (jZeroLayer_le_centralizer_J₀ d))) inf_le_right) hQX

theorem yamada_5_6_2 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    IsElemAbelian 2 (yamadaV₁ d t) ∧ Nat.card (yamadaV₁ d t) = (2 ^ f) ^ 2 ∧
      yamadaV₁ d t ⊓ centralizer ({t} : Set G) = d.V.map L.subtype ∧
      yamadaV₁ d t ≤ yamadaF₁ d t := by
  obtain ⟨X, hX, htX, hQX⟩ := h.exists_isSylowOf_jZeroLayer_yamadaD₁ d hlay
  have hV := h.yamadaV₁_eq_center d hlay hX htX hQX
  have hPX : d.sylowJ₀.map L.subtype ≤ X :=
    (le_inf ((sylowJ₀_map_le_D_map d).trans (D_map_le_yamadaD₁ d))
      (sylowJ₀_map_le_centralizer_J₀ d)).trans hQX
  obtain ⟨-, hsh⟩ := h.sylowShape_of_isSylowOf_jZeroLayer d hlay hX htX hPX
  refine ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_, ?_, ?_⟩
  · exact (mem_centralizer_iff.1 (Subgroup.mem_inf.1 a.2).2 _ (Subgroup.mem_inf.1 b.2).1).symm
  · rw [hV] at hx
    rw [sq]
    exact hsh.center_mul_self x hx
  · rw [hV]
    exact hsh.card_center
  · rw [hV]
    exact h.center_inf_centralizer_eq_V d hlay hX htX hPX
  · exact le_inf (le_inf (h.yamadaV₁_le_yamadaL₂ d) (inf_le_left.trans le_sup_right))
      inf_le_left

end Center

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4

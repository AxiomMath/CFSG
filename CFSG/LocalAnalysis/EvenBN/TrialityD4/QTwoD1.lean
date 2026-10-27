module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Four
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.QTwoThomas

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Fusion

variable (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
  (h561 : yamadaC₁ d t = yamadaD₁ d t ⊔ zpowers t ∧ t ∉ yamadaD₁ d t ∧
    (normalizer (d.V : Set L)).map L.subtype ≤ normalizer (yamadaD₁ d t : Set G))
  (h562 : IsElemAbelian 2 (yamadaV₁ d t) ∧ Nat.card (yamadaV₁ d t) = (2 ^ f) ^ 2 ∧
    yamadaV₁ d t ⊓ centralizer ({t} : Set G) = d.V.map L.subtype ∧ yamadaV₁ d t ≤ yamadaF₁ d t)
  (h591 : yamadaL₂ d t = yamadaM₂ d t ⊔ zpowers t ∧ t ∉ yamadaM₂ d t ∧
    yamadaR₂ d t = yamadaS₂ d t ⊔ zpowers t ∧ t ∉ yamadaS₂ d t)
  (h592 : yamadaV₁ d t ⊓ (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom = ⊥ ∧
    Nat.card (yamadaY₂ d t) = (2 ^ f) ^ 4 ∧ IsMulCommutative (yamadaY₂ d t) ∧
    yamadaM₂ d t ⊓ centralizer (yamadaM₂ d t : Set G) = yamadaY₂ d t ∧
    yamadaY₂ d t ⊓ centralizer ({t} : Set G) = d.Y.map L.subtype)
  (h593 : (Subgroup.upperCentralSeries (yamadaS₂ d t) 1).map (yamadaS₂ d t).subtype =
      yamadaV₁ d t ∧
    (Subgroup.upperCentralSeries (yamadaS₂ d t) 2).map (yamadaS₂ d t).subtype = yamadaY₂ d t)

omit [Finite G] in
include h562 in
theorem mul_self_of_mem_yamadaV₁ {a : G} (ha : a ∈ yamadaV₁ d t) : a * a = 1 := by
  rw [← sq]
  exact h562.1.2 a ha

include h h561 h562 in
theorem conj_t_not_mem_yamadaD₁ (hW₂ : ∀ g : G, g * t * g⁻¹ ∉ yamadaW₂ d t) (g : G) :
    g * t * g⁻¹ ∉ yamadaD₁ d t := by
  intro hy
  obtain ⟨n, hn, a, ha, hna⟩ := h.exists_mul_of_mem_yamadaD₁ d h561 h562 hy
  obtain ⟨n₀, hn₀, rfl⟩ := hn
  change g * t * g⁻¹ = (n₀ : G) * a at hna
  have hy2 : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, h.t_mul_t, mul_one,
      mul_inv_cancel]
  have hca : (n₀ : G) * a = a * n₀ :=
    commute_of_mem_yamadaV₁ d t ha (D_le_yamadaD₁ d t ⟨n₀, hn₀, rfl⟩)
  have ha2 := mul_self_of_mem_yamadaV₁ d h562 ha
  rw [hna] at hy2
  have hn₀2 : n₀ * n₀ = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, OneMemClass.coe_one]
    calc (n₀ : G) * n₀ = n₀ * n₀ * (a * a) := by rw [ha2, mul_one]
      _ = n₀ * (n₀ * a) * a := by group
      _ = n₀ * (a * n₀) * a := by rw [hca]
      _ = n₀ * a * (n₀ * a) := by group
      _ = 1 := hy2
  obtain ⟨m, hm, hmW⟩ := d.exists_conj_mem_W_of_mem_D hn₀ hn₀2
  have hmD₁ : (m : G) ∈ normalizer (yamadaD₁ d t : Set G) := h561.2.2 ⟨m, hm, rfl⟩
  have hmV₁ := normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t hmD₁
  apply hW₂ ((m : G) * g)
  have e : (m : G) * g * t * ((m : G) * g)⁻¹ =
      ((m : G) * n₀ * (m : G)⁻¹) * ((m : G) * a * (m : G)⁻¹) := by
    rw [show (m : G) * g * t * ((m : G) * g)⁻¹ = (m : G) * (g * t * g⁻¹) * (m : G)⁻¹ by group,
      hna]
    group
  rw [e]
  exact mul_mem (mem_sup_left ⟨m * n₀ * m⁻¹, hmW, by simp⟩)
    (mem_sup_right (mem_sup_left ((mem_normalizer_iff.1 hmV₁ a).1 ha)))

include h h562 in
theorem exists_conj_eq_t_mul_of_mem_V {v : G} (hv : v ∈ d.V.map L.subtype) :
    ∃ b ∈ yamadaV₁ d t, b * t * b⁻¹ = t * v := by
  classical
  have htV₁ : t ∈ normalizer (yamadaV₁ d t : Set G) :=
    normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (h.t_mem_normalizer_yamadaD₁ d)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  have hcomm : ∀ a ∈ yamadaV₁ d t, ∀ b ∈ yamadaV₁ d t, a * b = b * a := fun a ha b hb =>
    commute_of_mem_yamadaV₁ d t hb (yamadaV₁_le_yamadaD₁ d t ha)
  have htb : ∀ b ∈ yamadaV₁ d t, t * b * t ∈ yamadaV₁ d t := fun b hb => by
    have := (mem_normalizer_iff.1 htV₁ b).1 hb
    rwa [htinv] at this
  have hinv : ∀ b ∈ yamadaV₁ d t, b⁻¹ = b := fun b hb =>
    inv_eq_of_mul_eq_one_right (mul_self_of_mem_yamadaV₁ d h562 hb)
  let φ : yamadaV₁ d t →* yamadaV₁ d t :=
    { toFun := fun b => ⟨b * (t * b * t), mul_mem b.2 (htb b b.2)⟩
      map_one' := Subtype.ext (by
        change (1 : G) * (t * 1 * t) = 1
        rw [one_mul, mul_one, h.t_mul_t])
      map_mul' := fun a b => Subtype.ext (by
        change (a : G) * b * (t * (a * b) * t) = a * (t * a * t) * (b * (t * b * t))
        have e : t * ((a : G) * b) * t = (t * a * t) * (t * b * t) := by
          rw [show (t * a * t) * (t * b * t) = t * a * (t * t) * b * t by group, h.t_mul_t]
          group
        rw [e]
        have h1 := hcomm _ b.2 _ (htb a a.2)
        calc (a : G) * b * ((t * a * t) * (t * b * t)) = a * (b * (t * a * t)) * (t * b * t) := by
              group
          _ = a * ((t * a * t) * b) * (t * b * t) := by rw [h1]
          _ = a * (t * a * t) * (b * (t * b * t)) := by group) }
  have hφ : ∀ b : yamadaV₁ d t, ((φ b : yamadaV₁ d t) : G) = b * (t * b * t) := fun b => rfl
  have hφV : ∀ b : yamadaV₁ d t, ((φ b : yamadaV₁ d t) : G) ∈ d.V.map L.subtype := fun b => by
    rw [← h562.2.2.1, hφ]
    refine mem_inf.2 ⟨mul_mem b.2 (htb b b.2), mem_centralizer_singleton_iff.2 ?_⟩
    have h3 := hcomm _ b.2 _ (htb b b.2)
    calc (b : G) * (t * b * t) * t = b * t * b * (t * t) := by group
      _ = b * t * b := by rw [h.t_mul_t, mul_one]
      _ = t * ((t * b * t) * b) := by
        rw [show t * ((t * b * t) * b) = (t * t) * b * t * b by group, h.t_mul_t, one_mul]
      _ = t * (b * (t * b * t)) := by rw [h3]
  have hker : φ.ker = (d.V.map L.subtype).subgroupOf (yamadaV₁ d t) := by
    ext b
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← h562.2.2.1, mem_inf, Subtype.ext_iff, hφ,
      OneMemClass.coe_one, mem_centralizer_singleton_iff]
    constructor
    · intro h1
      refine ⟨b.2, ?_⟩
      have h2 : t * b * t = b := by
        rw [eq_inv_of_mul_eq_one_right h1, hinv b b.2]
      calc (b : G) * t = t * (t * b * t) := by
            rw [show t * (t * b * t) = (t * t) * b * t by group, h.t_mul_t, one_mul]
        _ = t * b := by rw [h2]
    · rintro ⟨-, h1⟩
      rw [show (b : G) * (t * b * t) = b * (t * b) * t by group, ← h1,
        show (b : G) * (b * t) * t = (b * b) * (t * t) by group,
        mul_self_of_mem_yamadaV₁ d h562 b.2, h.t_mul_t, one_mul]
  have hVcard : Nat.card (d.V.map L.subtype) = 2 ^ f := by
    rw [card_map_of_injective L.subtype_injective, d.card_V]
  have hVle : d.V.map L.subtype ≤ yamadaV₁ d t := V_le_yamadaV₁ d h562
  have hkercard : Nat.card φ.ker = 2 ^ f := by
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe hVle).toEquiv, hVcard]
  have hrange : Nat.card φ.range = 2 ^ f := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hkercard, h562.2.1] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ f) (by rw [h1]; ring)
  have himg : (φ.range).map (yamadaV₁ d t).subtype = d.V.map L.subtype := by
    refine eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
      exact hφV b
    · rw [card_map_of_injective (yamadaV₁ d t).subtype_injective, hrange, hVcard]
  rw [← himg] at hv
  obtain ⟨_, ⟨b, rfl⟩, hbv⟩ := hv
  refine ⟨b, b.2, ?_⟩
  rw [← hbv]
  change (b : G) * t * (b : G)⁻¹ = t * ((φ b : yamadaV₁ d t) : G)
  rw [hφ, hinv b b.2]
  have h3 := hcomm _ b.2 _ (htb b b.2)
  calc (b : G) * t * b = t * (t * b * t) * b := by
        rw [show t * (t * b * t) * b = (t * t) * b * t * b by group, h.t_mul_t, one_mul]
    _ = t * ((t * b * t) * b) := by group
    _ = t * (b * (t * b * t)) := by rw [h3]

include h h562 in
theorem exists_conj_eq_of_mul_self
    (hsurj : ∀ δ ∈ yamadaD₁ d t, ∃ x : G, ∃ v ∈ yamadaV₁ d t, x * t * x⁻¹ = t * δ * v)
    {δ : G} (hδ : δ ∈ yamadaD₁ d t) (h2 : t * δ * (t * δ) = 1) :
    ∃ g : G, g * t * g⁻¹ = t * δ := by
  obtain ⟨y, v, hv, hy⟩ := hsurj δ hδ
  have hvδ : δ * v = v * δ := commute_of_mem_yamadaV₁ d t hv hδ
  have hv2 : v * v = 1 := mul_self_of_mem_yamadaV₁ d h562 hv
  have hs'2 : t * δ * v * (t * δ * v) = 1 := by
    rw [← hy, show y * t * y⁻¹ * (y * t * y⁻¹) = y * (t * t) * y⁻¹ by group, h.t_mul_t, mul_one,
      mul_inv_cancel]
  have hsv : t * δ * v = v * (t * δ) := by
    have hsinv : (t * δ)⁻¹ = t * δ := inv_eq_of_mul_eq_one_right h2
    have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
    have h3 : t * δ * v * (t * δ) = v⁻¹ := by
      have := eq_inv_of_mul_eq_one_left hs'2
      calc t * δ * v * (t * δ) = (t * δ * v) * (t * δ * v) * v⁻¹ := by group
        _ = v⁻¹ := by rw [hs'2, one_mul]
    calc t * δ * v = t * δ * v * (t * δ) * (t * δ)⁻¹ := by group
      _ = v * (t * δ) := by rw [h3, hvinv, hsinv]
  have hvt : v * t = t * v := by
    have h4 : t * v * δ = v * t * δ := by
      calc t * v * δ = t * (δ * v) := by rw [mul_assoc, hvδ]
        _ = t * δ * v := by group
        _ = v * (t * δ) := hsv
        _ = v * t * δ := by group
    exact (mul_right_cancel h4).symm
  have hvV : v ∈ d.V.map L.subtype := by
    rw [← h562.2.2.1]
    exact mem_inf.2 ⟨hv, mem_centralizer_singleton_iff.2 hvt⟩
  obtain ⟨b, hb, hbt⟩ := h.exists_conj_eq_t_mul_of_mem_V d h562 hvV
  have hbδ : b * δ * b⁻¹ = δ := by
    rw [← commute_of_mem_yamadaV₁ d t hb hδ, mul_inv_cancel_right]
  have hbv : b * v * b⁻¹ = v := by
    rw [commute_of_mem_yamadaV₁ d t hv (yamadaV₁_le_yamadaD₁ d t hb), mul_inv_cancel_right]
  refine ⟨b * y, ?_⟩
  calc b * y * t * (b * y)⁻¹ = b * (y * t * y⁻¹) * b⁻¹ := by group
    _ = (b * t * b⁻¹) * (b * δ * b⁻¹) * (b * v * b⁻¹) := by rw [hy]; group
    _ = t * v * δ * v := by rw [hbt, hbδ, hbv]
    _ = t * δ * (v * v) := by rw [mul_assoc t v δ, ← hvδ]; group
    _ = t * δ := by rw [hv2, mul_one]

include h h561 h562 in
theorem normalizer_yamadaC₁_le_of_fusion (hD₁ : ∀ g : G, g * t * g⁻¹ ∉ yamadaD₁ d t)
    (hfus : ∀ δ ∈ yamadaD₁ d t, t * δ * (t * δ) = 1 → ∃ g : G, g * t * g⁻¹ = t * δ) :
    normalizer (yamadaC₁ d t : Set G) ≤ normalizer (yamadaD₁ d t : Set G) := by
  intro x hx
  set P : Subgroup G := (yamadaD₁ d t).comap (MulAut.conj x).toMonoidHom with hP
  have hmemP : ∀ y, y ∈ P ↔ x * y * x⁻¹ ∈ yamadaD₁ d t := fun y => by
    rw [hP, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hPC : P ≤ yamadaC₁ d t := fun y hy => by
    have h1 := h.yamadaD₁_le_yamadaC₁ d ((hmemP y).1 hy)
    have := (mem_normalizer_iff.1 (inv_mem hx) _).1 h1
    rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at this
  have hnotP : ∀ g : G, g * t * g⁻¹ ∉ P := fun g hg => hD₁ (x * g) (by
    rw [hmemP] at hg
    rwa [show x * g * t * (x * g)⁻¹ = x * (g * t * g⁻¹) * x⁻¹ by group])
  have hPcard : Nat.card P = Nat.card (yamadaD₁ d t) := by
    refine Nat.card_congr ((MulAut.conj x).toEquiv.subtypeEquiv fun y => ?_)
    rw [hmemP]
    simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulAut.conj_apply]
  have hidx : (P.subgroupOf (yamadaC₁ d t)).index = 2 := by
    have h1 := Subgroup.card_mul_index (P.subgroupOf (yamadaC₁ d t))
    rw [Nat.card_congr (subgroupOfEquivOfLe hPC).toEquiv, hPcard, h.card_yamadaC₁ d,
      h.card_yamadaD₁ d h561] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < (2 ^ f) ^ 10) (by rw [h1]; ring)
  have htC : t ∈ yamadaC₁ d t := h.t_mem_yamadaC₁ d
  have htP : t ∉ P := by simpa using hnotP 1
  have key : ∀ s ∈ yamadaC₁ d t, s ∉ P → t * s ∈ P := fun s hs hsP => by
    have h1 := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨t, htC⟩) (b := ⟨s, hs⟩)).2
      (by rw [mem_subgroupOf, mem_subgroupOf]; exact iff_of_false htP hsP)
    rwa [mem_subgroupOf] at h1
  have hC₁ : ∀ δ ∈ yamadaD₁ d t, t * δ ∈ yamadaC₁ d t := fun δ hδ =>
    mul_mem htC (h.yamadaD₁_le_yamadaC₁ d hδ)
  have hDP : ∀ n ∈ d.D.map L.subtype, n * n = 1 → n ∈ P := fun n hn hn2 => by
    have hnD₁ := D_le_yamadaD₁ d t hn
    have hnt : n * t = t * n := mem_centralizer_iff.1 h.htL n (map_subtype_le _ hn)
    have htn : t * n * (t * n) = 1 := by
      rw [show t * n * (t * n) = t * (n * t) * n by group, hnt,
        show t * (t * n) * n = (t * t) * (n * n) by group, h.t_mul_t, hn2, one_mul]
    obtain ⟨g, hg⟩ := hfus n hnD₁ htn
    have h1 := key (t * n) (hC₁ n hnD₁) (hg ▸ hnotP g)
    rwa [← mul_assoc, h.t_mul_t, one_mul] at h1
  have hrt : ∀ z : L, z ∈ d.D → z * z = 1 → (z : G) ∈ P := fun z hz hz2 =>
    hDP _ ⟨z, hz, rfl⟩ (by rw [← Subgroup.coe_mul, hz2, OneMemClass.coe_one])
  have hD : d.D.map L.subtype ≤ P := by
    rw [map_le_iff_le_comap]
    have hU₂ : d.U₂ ≤ P.comap L.subtype := by
      rintro _ ⟨a, rfl⟩
      exact hrt _ (d.x₂_mem_D a) (d.x₂_mul_self a)
    have hU₃ : d.U₃ ≤ P.comap L.subtype := by
      rintro _ ⟨a, rfl⟩
      exact hrt _ (d.x₃_mem_D a) (d.x₃_mul_self a)
    have hU₄ : d.U₄ ≤ P.comap L.subtype := by
      rintro _ ⟨a, rfl⟩
      exact hrt _ (d.x₄_mem_D a) (d.x₄_mul_self a)
    have hU₅ : d.U₅ ≤ P.comap L.subtype := by
      rintro _ ⟨a, rfl⟩
      exact hrt _ (d.x₅_mem_D a) (d.x₅_mul_self a)
    have hU₆ : d.U₆ ≤ P.comap L.subtype := by
      rintro _ ⟨a, rfl⟩
      exact hrt _ (d.x₆_mem_D a) (d.x₆_mul_self a)
    exact sup_le hU₂ (sup_le hU₃ (sup_le hU₄ (sup_le hU₅ hU₆)))
  have htV₁ : t ∈ normalizer (yamadaV₁ d t : Set G) :=
    normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (h.t_mem_normalizer_yamadaD₁ d)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  have hV₁ : yamadaV₁ d t ≤ P := fun a ha => by
    have hta : t * a * t ∈ yamadaV₁ d t := by
      have := (mem_normalizer_iff.1 htV₁ a).1 ha
      rwa [htinv] at this
    have hw₁ : t * a * t * a ∈ yamadaV₁ d t := mul_mem hta ha
    have hcomm := commute_of_mem_yamadaV₁ d t ha (yamadaV₁_le_yamadaD₁ d t hta)
    have hwC : t * a * t * a ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc t * a * t * a * t = t * (a * (t * a * t)) := by group
        _ = t * ((t * a * t) * a) := by rw [hcomm]
        _ = t * (t * a * t * a) := by group
    have hwV : t * a * t * a ∈ d.V.map L.subtype := by
      rw [← h562.2.2.1]
      exact mem_inf.2 ⟨hw₁, hwC⟩
    obtain ⟨w₀, ⟨γ, rfl⟩, hw₀⟩ := hwV
    change ((d.x₆ γ : L) : G) = t * a * t * a at hw₀
    set n : L := d.x₂ 1 * d.x₅ γ with hn
    have hnD : (n : G) ∈ d.D.map L.subtype :=
      ⟨n, mul_mem (d.x₂_mem_D 1) (d.x₅_mem_D γ), rfl⟩
    have hn2 : n * n = d.x₆ γ := by
      rw [hn, show d.x₆ γ = d.x₆ (1 * γ) by rw [one_mul], ← d.comm₂₅, commutatorElement_def,
        d.x₂_inv, d.x₅_inv]
      group
    have hnD₁ := D_le_yamadaD₁ d t hnD
    have hna : (n : G) * a = a * n := commute_of_mem_yamadaV₁ d t ha hnD₁
    have hnt : (n : G) * t = t * n := mem_centralizer_iff.1 h.htL n n.2
    have hw2 : t * a * t * a * (t * a * t * a) = 1 := by
      rw [← hw₀, ← Subgroup.coe_mul, ← d.x₆_add, d.add_self_Γ₀, d.x₆_zero, OneMemClass.coe_one]
    have hs2 : t * (a * n) * (t * (a * n)) = 1 := by
      calc t * (a * n) * (t * (a * n)) = t * a * ((n : G) * t) * a * n := by group
        _ = t * a * t * ((n : G) * a) * n := by rw [hnt]; group
        _ = t * a * t * a * ((n : G) * n) := by rw [hna]; group
        _ = t * a * t * a * (t * a * t * a) := by
          rw [← Subgroup.coe_mul, hn2, hw₀]
        _ = 1 := hw2
    obtain ⟨g, hg⟩ := hfus (a * n) (mul_mem (yamadaV₁_le_yamadaD₁ d t ha) hnD₁) hs2
    have h1 := key (t * (a * n)) (hC₁ _ (mul_mem (yamadaV₁_le_yamadaD₁ d t ha) hnD₁))
      (hg ▸ hnotP g)
    rw [← mul_assoc, ← mul_assoc, h.t_mul_t, one_mul] at h1
    have := mul_mem h1 (inv_mem (hD hnD))
    rwa [mul_inv_cancel_right] at this
  have hD₁P : yamadaD₁ d t ≤ P := by
    rw [h.yamadaD₁_eq_sup d h561 h562]
    exact sup_le hD hV₁
  exact mem_normalizer_fintype fun δ hδ => (hmemP δ).1 (hD₁P hδ)

include h h562 in
theorem normalizer_tV₁_le_of_fusion (hD₁ : ∀ g : G, g * t * g⁻¹ ∉ yamadaD₁ d t) :
    normalizer ((yamadaV₁ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) := by
  intro x hx
  have htV₁ : t ∈ normalizer (yamadaV₁ d t : Set G) :=
    normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (h.t_mem_normalizer_yamadaD₁ d)
  have htV : t ∈ normalizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
    h.t_mem_normalizer_map d.V
  have hnot : ∀ g : G, g * t * g⁻¹ ∉ yamadaV₁ d t := fun g hg =>
    hD₁ g (yamadaV₁_le_yamadaD₁ d t hg)
  have hinvV : ∀ w ∈ yamadaV₁ d t, w * t * (w * t) = 1 → w ∈ d.V.map L.subtype := by
    intro w hw h2
    have hw2 : w * w = 1 := mul_self_of_mem_yamadaV₁ d h562 hw
    have h3 : t * w * t = w := by
      rw [eq_inv_of_mul_eq_one_right (show w * (t * w * t) = 1 by rw [← h2]; group),
        inv_eq_of_mul_eq_one_right hw2]
    rw [← h562.2.2.1]
    refine mem_inf.2 ⟨hw, mem_centralizer_singleton_iff.2 ?_⟩
    calc w * t = t * (t * w * t) := by
          rw [show t * (t * w * t) = (t * t) * w * t by group, h.t_mul_t, one_mul]
      _ = t * w := by rw [h3]
  have hconjV : ∀ w ∈ d.V.map L.subtype, ∃ g : G, g * t * g⁻¹ = w * t := fun w hw => by
    obtain ⟨b, -, hbt⟩ := h.exists_conj_eq_t_mul_of_mem_V d h562 hw
    have hwt : w * t = t * w := mem_centralizer_iff.1 h.htL w (map_subtype_le _ hw)
    exact ⟨b, by rw [hbt, hwt]⟩
  have hxinv : ∀ z : G, z * z = 1 → x * z * x⁻¹ * (x * z * x⁻¹) = 1 := fun z hz => by
    rw [show x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ by group, hz, mul_one,
      mul_inv_cancel]
  have hxV₁ : x ∈ normalizer (yamadaV₁ d t : Set G) := mem_normalizer_fintype fun b hb => by
    have hz : x * b * x⁻¹ ∈ yamadaV₁ d t ⊔ zpowers t :=
      (mem_normalizer_iff.1 hx b).1 (mem_sup_left hb)
    rcases (mem_sup_zpowers_iff_of_D4 h.t_mul_t htV₁).1 hz with h1 | ⟨w, hw, h1⟩
    · exact h1
    · exfalso
      have hb2 := hxinv b (mul_self_of_mem_yamadaV₁ d h562 hb)
      rw [h1] at hb2
      obtain ⟨g, hg⟩ := hconjV w (hinvV w hw hb2)
      apply hnot (x⁻¹ * g)
      rw [show x⁻¹ * g * t * (x⁻¹ * g)⁻¹ = x⁻¹ * (g * t * g⁻¹) * x by group, hg, ← h1,
        show x⁻¹ * (x * b * x⁻¹) * x = b by group]
      exact hb
  have hz : x * t * x⁻¹ ∈ yamadaV₁ d t ⊔ zpowers t :=
    (mem_normalizer_iff.1 hx t).1 (mem_sup_right (mem_zpowers t))
  obtain ⟨w, hwV, hxtw⟩ : ∃ w ∈ d.V.map L.subtype, x * t * x⁻¹ = w * t := by
    rcases (mem_sup_zpowers_iff_of_D4 h.t_mul_t htV₁).1 hz with h1 | ⟨w, hw, h1⟩
    · exact absurd h1 (hnot x)
    · refine ⟨w, hinvV w hw ?_, h1⟩
      rw [← h1]
      exact hxinv t h.t_mul_t
  have hwV₁ : w ∈ yamadaV₁ d t := V_le_yamadaV₁ d h562 hwV
  have hxV : ∀ v ∈ d.V.map L.subtype, x * v * x⁻¹ ∈ d.V.map L.subtype := fun v hv => by
    have hvV₁ : v ∈ yamadaV₁ d t := V_le_yamadaV₁ d h562 hv
    have h1 : x * v * x⁻¹ ∈ yamadaV₁ d t := (mem_normalizer_iff.1 hxV₁ v).1 hvV₁
    have hvt : v * t = t * v := mem_centralizer_iff.1 h.htL v (map_subtype_le _ hv)
    have h2 : (x * v * x⁻¹) * (w * t) = (w * t) * (x * v * x⁻¹) := by
      rw [← hxtw]
      calc x * v * x⁻¹ * (x * t * x⁻¹) = x * (v * t) * x⁻¹ := by group
        _ = x * (t * v) * x⁻¹ := by rw [hvt]
        _ = x * t * x⁻¹ * (x * v * x⁻¹) := by group
    have h3 : (x * v * x⁻¹) * w = w * (x * v * x⁻¹) :=
      commute_of_mem_yamadaV₁ d t hwV₁ (yamadaV₁_le_yamadaD₁ d t h1)
    rw [← h562.2.2.1]
    refine mem_inf.2 ⟨h1, mem_centralizer_singleton_iff.2 ?_⟩
    calc x * v * x⁻¹ * t = w⁻¹ * ((x * v * x⁻¹) * (w * t)) := by
          rw [← mul_assoc (x * v * x⁻¹), h3]; group
      _ = w⁻¹ * ((w * t) * (x * v * x⁻¹)) := by rw [h2]
      _ = t * (x * v * x⁻¹) := by group
  refine mem_normalizer_fintype fun z hz => ?_
  rcases (mem_sup_zpowers_iff_of_D4 h.t_mul_t htV).1 hz with hz | ⟨v, hv, rfl⟩
  · exact mem_sup_left (hxV z hz)
  · rw [show x * (v * t) * x⁻¹ = x * v * x⁻¹ * (x * t * x⁻¹) by group, hxtw, ← mul_assoc]
    exact mul_mem (mul_mem (mem_sup_left (hxV v hv)) (mem_sup_left hwV))
      (mem_sup_right (mem_zpowers t))

include h h561 h562 in
theorem yamada_5_12_two (hW₂ : ∀ g : G, g * t * g⁻¹ ∉ yamadaW₂ d t)
    (hsurj : ∀ δ ∈ yamadaD₁ d t, ∃ x : G, ∃ v ∈ yamadaV₁ d t, x * t * x⁻¹ = t * δ * v) :
    (∀ g : G, g * t * g⁻¹ ∉ yamadaD₁ d t) ∧
      normalizer (yamadaC₁ d t : Set G) ≤ normalizer (yamadaD₁ d t : Set G) ∧
      normalizer ((yamadaV₁ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
        normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) := by
  have hD₁ := h.conj_t_not_mem_yamadaD₁ d h561 h562 hW₂
  exact ⟨hD₁, h.normalizer_yamadaC₁_le_of_fusion d h561 h562 hD₁
    fun δ hδ h2 => h.exists_conj_eq_of_mul_self d h562 hsurj hδ h2,
    h.normalizer_tV₁_le_of_fusion d h562 hD₁⟩

include h h561 h562 h591 h592 h593 in
theorem exists_mem_yamadaQ₅_conj_eq_of_mem_D_all {n : G} (hn : n ∈ d.D.map L.subtype) :
    ∃ x ∈ yamadaQ₅ d t, ∃ v ∈ yamadaV₁ d t, x * t * x⁻¹ = t * n * v := by
  let T : Subgroup L :=
    { carrier := {m | m ∈ d.D ∧ ∃ x ∈ yamadaQ₅ d t, ∃ v ∈ yamadaV₁ d t,
        x * t * x⁻¹ = t * (m : G) * v}
      mul_mem' := by
        rintro a b ⟨ha, x, hx, u, hu, e⟩ ⟨hb, y, hy, u', hu', e'⟩
        obtain ⟨v, hv, e''⟩ := conj_mul_eq_of_mem_yamadaQ₅ d hx
          (D_le_yamadaD₁ d t ⟨b, hb, rfl⟩) hu hu' e e'
        exact ⟨mul_mem ha hb, x * y, mul_mem hx hy, v, hv, by rw [e'', Subgroup.coe_mul]; rfl⟩
      one_mem' := ⟨one_mem _, 1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, x, hx, u, hu, e⟩
        obtain ⟨v, hv, e'⟩ := conj_inv_eq_of_mem_yamadaQ₅ d hx ⟨a, ha, rfl⟩ hu e
        exact ⟨inv_mem ha, x⁻¹, inv_mem hx, v, hv, by rw [e', Subgroup.coe_inv]; rfl⟩ }
  have hTD : T ≤ d.D := fun m hm => hm.1
  have hVT : d.V ≤ T := by
    intro m hm
    obtain ⟨x, hx, e⟩ := (h.two_core_C₁_all d).2.2.1 (m : G) ⟨m, hm, rfl⟩
    refine ⟨d.V_le_Y.trans (d.Y_le_W.trans (d.W_le_F.trans d.F_le_D)) hm, x⁻¹,
      h.yamadaC₁_le_yamadaQ₅ d h561 h562 (inv_mem hx), 1, one_mem _, ?_⟩
    rw [inv_inv, mul_one, e]
  have hYT : d.Y ≤ T := by
    intro m hm
    obtain ⟨a, ha, e⟩ := h.exists_mem_yamadaY₂_conj_eq d h591 h592 ⟨m, hm, rfl⟩
    exact ⟨(d.Y_le_W.trans (d.W_le_F.trans d.F_le_D)) hm, a,
      h.yamadaY₂_le_yamadaQ₅ d h561 h562 h591 h593 ha, 1, one_mem _, by rw [mul_one, e]; rfl⟩
  have hTn : d.leviShort ≤ normalizer (T : Set L) := by
    intro s hs
    have hsC : (s : G) ∈ centralizer ({t} : Set G) := h.L_le_centralizer s.2
    have hsV : (s : G) ∈ normalizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
      map_le_normalizer_map d.leviShort_le_normalizer_V ⟨s, hs, rfl⟩
    have hsC₁ : (s : G) ∈ normalizer (yamadaC₁ d t : Set G) :=
      le_normalizer_yamadaC₁ d t (h.centralizer_inf_normalizer_V_le d ⟨hsC, hsV⟩)
    have hsD₁ : (s : G) ∈ normalizer (yamadaD₁ d t : Set G) :=
      h561.2.2 ⟨s, d.leviShort_le_normalizer_V hs, rfl⟩
    have hsV₁ := normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t hsD₁
    have hst : (s : G) * t = t * s := mem_centralizer_singleton_iff.1 hsC
    refine mem_normalizer_fintype fun m hm => ?_
    obtain ⟨hmD, x, hx, v, hv, e⟩ := hm
    refine ⟨(mem_normalizer_iff.1 (d.leviShort_le_normalizer_D hs) m).1 hmD, s * x * s⁻¹,
      Common.conj_mem_centralizerMod (mem_inf.2 ⟨hsC₁, hsD₁⟩) hx, s * v * s⁻¹,
      (mem_normalizer_iff.1 hsV₁ v).1 hv, ?_⟩
    have hst' : (s : G)⁻¹ * t * s = t := by rw [mul_assoc, ← hst, inv_mul_cancel_left]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    calc (s : G) * x * (s : G)⁻¹ * t * ((s : G) * x * (s : G)⁻¹)⁻¹ =
        s * x * ((s : G)⁻¹ * t * s) * x⁻¹ * (s : G)⁻¹ := by group
      _ = s * (x * t * x⁻¹) * (s : G)⁻¹ := by rw [hst']; group
      _ = s * (t * m * v) * (s : G)⁻¹ := by rw [e]
      _ = (s * t) * m * v * (s : G)⁻¹ := by group
      _ = (t * s) * m * v * (s : G)⁻¹ := by rw [hst]
      _ = t * ((s : G) * m * (s : G)⁻¹) * ((s : G) * v * (s : G)⁻¹) := by group
  rcases d.leviShort_irreducible_D_mod_V hVT hTD hTn with h1 | h1
  · exfalso
    have h2 := Subgroup.card_le_of_le (hYT.trans h1.le)
    rw [d.card_Y, d.card_V] at h2
    have hq2 : 2 ≤ 2 ^ f := d.two_le_q
    have h3 : 2 ^ f < (2 ^ f) ^ 2 := by nlinarith
    omega
  · obtain ⟨m, hm, rfl⟩ := hn
    exact (h1 ▸ hm : m ∈ T).2

include h h561 h562 h591 h592 h593 in
theorem exists_mem_yamadaQ₅_conj_eq_all {δ : G} (hδ : δ ∈ yamadaD₁ d t) :
    ∃ x ∈ yamadaQ₅ d t, ∃ v ∈ yamadaV₁ d t, x * t * x⁻¹ = t * δ * v := by
  obtain ⟨n, hn, w, hw, rfl⟩ := h.exists_mul_of_mem_yamadaD₁ d h561 h562 hδ
  obtain ⟨x, hx, v, hv, e⟩ := h.exists_mem_yamadaQ₅_conj_eq_of_mem_D_all d h561 h562 h591 h592
    h593 hn
  exact ⟨x, hx, w⁻¹ * v, mul_mem (inv_mem hw) hv, by rw [e]; group⟩

include h h561 h562 h591 h592 h593 in
theorem normalizer_yamadaC₁_le_all :
    normalizer (yamadaC₁ d t : Set G) ≤ normalizer (yamadaD₁ d t : Set G) :=
  (h.yamada_5_12_two d h561 h562 (h.conj_t_not_mem_yamadaW₂ d h562 h592) fun δ hδ => by
    obtain ⟨x, -, v, hv, e⟩ := h.exists_mem_yamadaQ₅_conj_eq_all d h561 h562 h591 h592 h593 hδ
    exact ⟨x, v, hv, e⟩).2.1

include h h561 h562 h591 h592 h593 in
theorem normalizer_tV₁_le_all :
    normalizer ((yamadaV₁ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
  (h.yamada_5_12_two d h561 h562 (h.conj_t_not_mem_yamadaW₂ d h562 h592) fun δ hδ => by
    obtain ⟨x, -, v, hv, e⟩ := h.exists_mem_yamadaQ₅_conj_eq_all d h561 h562 h591 h592 h593 hδ
    exact ⟨x, v, hv, e⟩).2.2

include h h561 h562 h591 h592 h593 in
theorem normalizerHyp_all : NormalizerHyp d t :=
  ⟨h.normalizer_yamadaC₁_le_all d h561 h562 h591 h592 h593,
    h.normalizer_tV₁_le_all d h561 h562 h591 h592 h593⟩

end Fusion

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4

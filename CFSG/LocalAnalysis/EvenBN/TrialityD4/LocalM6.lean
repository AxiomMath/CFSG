module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL3Four
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Ten
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Nine

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open scoped commutatorElement Pointwise

section Generic

variable {G : Type*} [Group G] [Finite G]

private theorem conj_mul_mul_inv_aux {g a z : G} (ha : a * g = g * a) :
    g * (a * z) * g⁻¹ * (a * z)⁻¹ = a * (g * z * g⁻¹ * z⁻¹) * a⁻¹ := by
  calc g * (a * z) * g⁻¹ * (a * z)⁻¹ = (g * a) * z * g⁻¹ * z⁻¹ * a⁻¹ := by group
    _ = (a * g) * z * g⁻¹ * z⁻¹ * a⁻¹ := by rw [ha]
    _ = a * (g * z * g⁻¹ * z⁻¹) * a⁻¹ := by group

private theorem conj_mul_mul_inv_aux' {g n b : G} (hb : b * g = g * b) :
    g * (n * b) * g⁻¹ * (n * b)⁻¹ = g * n * g⁻¹ * n⁻¹ := by
  have hb' : b * g⁻¹ * b⁻¹ = g⁻¹ := by
    rw [show b * g⁻¹ * b⁻¹ = (b * g * b⁻¹)⁻¹ by group, hb, mul_inv_cancel_right]
  calc g * (n * b) * g⁻¹ * (n * b)⁻¹ = g * n * (b * g⁻¹ * b⁻¹) * n⁻¹ := by group
    _ = g * n * g⁻¹ * n⁻¹ := by rw [hb']

private theorem mem_centralizerModNC9_iff {Z : Subgroup G} {K : Set G} {x : G} :
    x ∈ centralizerModNC9 Z K ↔ x ∈ normalizer (Z : Set G) ∧ ∀ a ∈ K, x * a * x⁻¹ * a⁻¹ ∈ Z :=
  Iff.rfl

private theorem mem_normalizer_centralizerModNC9 {Z W : Subgroup G} {x : G}
    (hZ : x ∈ normalizer (Z : Set G)) (hW : x ∈ normalizer (W : Set G)) :
    x ∈ normalizer ((centralizerModNC9 Z (W : Set G) : Subgroup G) : Set G) := by
  refine mem_normalizer_fintype fun a ha => ?_
  obtain ⟨haZ, ha⟩ :=
    mem_centralizerModNC9_iff.1 (show a ∈ centralizerModNC9 Z (W : Set G) from ha)
  show x * a * x⁻¹ ∈ centralizerModNC9 Z (W : Set G)
  refine mem_centralizerModNC9_iff.2 ⟨mul_mem (mul_mem hZ haZ) (inv_mem hZ), fun w hw => ?_⟩
  have hw' : x⁻¹ * w * x ∈ W := by
    have := (mem_normalizer_iff.1 (inv_mem hW) w).1 hw
    rwa [inv_inv] at this
  have h1 := (mem_normalizer_iff.1 hZ _).1 (ha _ hw')
  rwa [show x * (a * (x⁻¹ * w * x) * a⁻¹ * (x⁻¹ * w * x)⁻¹) * x⁻¹ =
    x * a * x⁻¹ * w * (x * a * x⁻¹)⁻¹ * w⁻¹ by group] at h1

private theorem exists_mul_eq_of_coprime {p : ℕ} [Fact p.Prime] {P K A : Subgroup G}
    (hKP : K ≤ P) (hPK : P ≤ normalizer (K : Set G)) (hAP : A ≤ normalizer (P : Set G))
    (hAK : A ≤ normalizer (K : Set G)) (hK : IsPGroup p K) (hA : ¬ p ∣ Nat.card A)
    (htriv : ∀ a ∈ A, ∀ x ∈ P, x⁻¹ * (a * x * a⁻¹) ∈ K) {x : G} (hx : x ∈ P) :
    ∃ n ∈ K, ∃ c ∈ P ⊓ centralizer (A : Set G), n * c = x := by
  have hcard := card_inf_centralizer_eq_of_coprime_D4 hKP hPK hAP hAK hK hA htriv
  have hBK : P ⊓ centralizer (A : Set G) ≤ normalizer (K : Set G) := inf_le_left.trans hPK
  have h1 := card_sup_mul_card_inf_eq_D4 hBK
  have hinf : K ⊓ (P ⊓ centralizer (A : Set G)) = K ⊓ centralizer (A : Set G) := by
    rw [← inf_assoc, inf_eq_left.2 hKP]
  have hrel := Subgroup.relIndex_mul_card K P
  rw [inf_eq_left.2 hKP] at hrel
  have hpos : 0 < Nat.card (K ⊓ centralizer (A : Set G) : Subgroup G) := Nat.card_pos
  have hsup : Nat.card (K ⊔ (P ⊓ centralizer (A : Set G)) : Subgroup G) = Nat.card P := by
    rw [hinf, hcard] at h1
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h1, ← hrel]
    ring
  have hKB : K ⊔ (P ⊓ centralizer (A : Set G)) = P :=
    eq_of_le_of_card_ge (sup_le hKP inf_le_left) hsup.ge
  have hx' : x ∈ ((K ⊔ (P ⊓ centralizer (A : Set G)) : Subgroup G) : Set G) := by
    rw [hKB]
    exact hx
  rw [coe_mul_of_right_le_normalizer_left _ _ hBK] at hx'
  obtain ⟨n, hn, c, hc, e⟩ := hx'
  exact ⟨n, hn, c, hc, e⟩

private theorem commutator_mem_of_fixed_mem {P Z W : Subgroup G} {g : G}
    (hPZ : P ≤ normalizer (Z : Set G)) (hPW : P ≤ normalizer (W : Set G))
    (hWZ : W ≤ normalizer (Z : Set G)) (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hgP : g ∈ normalizer (P : Set G)) (hgZ : g ∈ normalizer (Z : Set G))
    (hgW : g ∈ normalizer (W : Set G)) (hgc : ∀ w ∈ W, g * w * g⁻¹ * w⁻¹ ∈ Z)
    (hP : IsPGroup 2 P) (hg3 : Nat.card (zpowers g) = 3)
    (hfix : ∀ c ∈ P, g * c = c * g → c ∈ W) {m w : G} (hm : m ∈ P) (hw : w ∈ W) :
    m * w * m⁻¹ * w⁻¹ ∈ Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNC : ∀ x, x ∈ normalizer (Z : Set G) → x ∈ normalizer (W : Set G) →
      x ∈ normalizer ((centralizerModNC9 Z (W : Set G) : Subgroup G) : Set G) :=
    fun x hx hx' => mem_normalizer_centralizerModNC9 hx hx'
  have hgC : g ∈ centralizerModNC9 Z (W : Set G) := mem_centralizerModNC9_iff.2 ⟨hgZ, hgc⟩
  have hAC : zpowers g ≤ centralizerModNC9 Z (W : Set G) := (zpowers_le).2 hgC
  have hWC : W ≤ centralizerModNC9 Z (W : Set G) := fun x hx =>
    mem_centralizerModNC9_iff.2 ⟨hWZ hx, fun a ha => by
      have : x * a * x⁻¹ * a⁻¹ = 1 := by rw [hWc x hx a ha]; group
      rw [this]
      exact one_mem Z⟩
  have hKP : P ⊓ centralizerModNC9 Z (W : Set G) ≤ P := inf_le_left
  have hPK : P ≤ normalizer ((P ⊓ centralizerModNC9 Z (W : Set G) : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_inf_D4 (le_normalizer hx) (hNC x (hPZ hx) (hPW hx))
  have hAP : zpowers g ≤ normalizer (P : Set G) := (zpowers_le).2 hgP
  have hAK : zpowers g ≤
      normalizer ((P ⊓ centralizerModNC9 Z (W : Set G) : Subgroup G) : Set G) :=
    (zpowers_le).2 (mem_normalizer_inf_D4 hgP (hNC g hgZ hgW))
  have hKp : IsPGroup 2 (P ⊓ centralizerModNC9 Z (W : Set G) : Subgroup G) := hP.to_le hKP
  have hA : ¬ 2 ∣ Nat.card (zpowers g) := by
    rw [hg3]
    norm_num
  have htriv : ∀ a ∈ zpowers g, ∀ x ∈ P,
      x⁻¹ * (a * x * a⁻¹) ∈ P ⊓ centralizerModNC9 Z (W : Set G) := by
    intro a ha x hx
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hx) ((mem_normalizer_iff.1 (hAP ha) x).1 hx), ?_⟩
    have h1 : x⁻¹ * a * x⁻¹⁻¹ ∈ centralizerModNC9 Z (W : Set G) :=
      (mem_normalizer_iff.1 (hNC x⁻¹ (inv_mem (hPZ hx)) (inv_mem (hPW hx))) a).1 (hAC ha)
    have h2 := mul_mem h1 (inv_mem (hAC ha))
    rwa [show x⁻¹ * a * x⁻¹⁻¹ * a⁻¹ = x⁻¹ * (a * x * a⁻¹) by group] at h2
  obtain ⟨n, hn, c, hc, e⟩ := exists_mul_eq_of_coprime (p := 2) hKP hPK hAP hAK hKp hA htriv hm
  obtain ⟨hcP, hcg⟩ := Subgroup.mem_inf.1 hc
  have hcW : c ∈ W := hfix c hcP (mem_centralizer_iff.1 hcg g (mem_zpowers g))
  have hmK : m ∈ P ⊓ centralizerModNC9 Z (W : Set G) := by
    rw [← e]
    exact mul_mem hn (Subgroup.mem_inf.2 ⟨hcP, hWC hcW⟩)
  exact (mem_centralizerModNC9_iff.1 (Subgroup.mem_inf.1 hmK).2).2 w hw

end Generic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

private theorem yamadaL₆_le_normalizer_yamadaW₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaL₆ d t ≤ normalizer (yamadaW₃ d t : Set G) := fun x hx => by
  have hxL₃ : x ∈ normalizer (yamadaL₃ d t : Set G) :=
    (Subgroup.mem_inf.1 (yamadaL₆_le d t hx)).1
  have hxW₂ : x ∈ normalizer (yamadaW₂ d t : Set G) := by
    have := normalizer_le_normalizer_commutator_C8 (yamadaL₃ d t) hxL₃
    rwa [h.yamada_5_18 d hlay] at this
  exact mem_normalizer_inf_D4 hxL₃ (mem_normalizer_centralizer_D4 hxW₂)

private theorem leviThree_commutator_mem_yamadaY₂_of_mem_yamadaW₂ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {x : G} (hx : x ∈ yamadaW₂ d t) :
    ((d.leviThree : L) : G) * x * ((d.leviThree : L) : G)⁻¹ * x⁻¹ ∈ yamadaY₂ d t := by
  have h592 := h.yamada_5_9_2 d hlay
  have hgY₂ : ((d.leviThree : L) : G) ∈ normalizer (yamadaY₂ d t : Set G) :=
    h.leviLong_map_le_normalizer_yamadaY₂ d hlay ⟨_, d.leviThree_mem_leviLong, rfl⟩
  have hx' : x ∈ ((d.W.map L.subtype ⊔ yamadaY₂ d t : Subgroup G) : Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left _ _ (yamadaY₂_le_normalizer_W d h592)] at hx'
  obtain ⟨_, ⟨w₀, hw₀, rfl⟩, y, hy, e⟩ := hx'
  obtain ⟨c, n, hn, rfl⟩ := d.mem_W_iff.1 hw₀
  have hz : ((n : L) : G) * y ∈ yamadaY₂ d t := mul_mem (Y_le_yamadaY₂ d h592 ⟨n, hn, rfl⟩) hy
  have hgx₄ : ((d.x₄ c : L) : G) * ((d.leviThree : L) : G) =
      ((d.leviThree : L) : G) * ((d.x₄ c : L) : G) :=
    mem_centralizer_iff.1 (leviLong_map_le_centralizer_U₄ d ⟨_, d.leviThree_mem_leviLong, rfl⟩)
      _ ⟨d.x₄ c, d.x₄_mem_U₄ c, rfl⟩
  have hx₄ : ((d.x₄ c : L) : G) ∈ normalizer (yamadaY₂ d t : Set G) :=
    M_le_normalizer_yamadaY₂ d h592 ⟨d.x₄ c, (d.W_le_F.trans d.F_le_M) (d.x₄_mem_W c), rfl⟩
  have e1 : x = ((d.x₄ c : L) : G) * (((n : L) : G) * y) := by
    rw [← e]
    simp only [map_mul, Subgroup.coe_subtype, mul_assoc]
  have hu : ((d.leviThree : L) : G) * (((n : L) : G) * y) * ((d.leviThree : L) : G)⁻¹ *
      (((n : L) : G) * y)⁻¹ ∈ yamadaY₂ d t :=
    mul_mem ((mem_normalizer_iff.1 hgY₂ _).1 hz) (inv_mem hz)
  have hu' := (mem_normalizer_iff.1 hx₄ _).1 hu
  rw [e1, conj_mul_mul_inv_aux hgx₄]
  exact hu'

private theorem leviThree_commutator_mem_yamadaY₂_of_mem_yamadaW₃ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {x : G} (hx : x ∈ yamadaW₃ d t) :
    ((d.leviThree : L) : G) * x * ((d.leviThree : L) : G)⁻¹ * x⁻¹ ∈ yamadaY₂ d t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have h5171 := h.yamada_5_17_1 d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hBN : yamadaM₃ d t ⊓ centralizer ((zpowers ((d.leviThree : L) : G) : Subgroup G) :
      Set G) ≤ normalizer (yamadaM₂ d t : Set G) := fun y hy =>
    h5171.2.2.1 (yamadaL₃_le_normalizer_yamadaL₂ d (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hy).1).1)
  have hxM₃ : x ∈ ((yamadaM₂ d t ⊔ (yamadaM₃ d t ⊓
      centralizer ((zpowers ((d.leviThree : L) : G) : Subgroup G) : Set G)) : Subgroup G) :
        Set G) := by
    rw [h.yamadaM₂_sup_centralizer_leviThree d hlay]
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1,
      centralizer_le (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) (Subgroup.mem_inf.1 hx).2⟩
  rw [coe_mul_of_right_le_normalizer_left _ _ hBN] at hxM₃
  obtain ⟨n, hn, b, hb, e⟩ := hxM₃
  have hbg : b * ((d.leviThree : L) : G) = ((d.leviThree : L) : G) * b :=
    (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hb).2 _ (mem_zpowers _)).symm
  have hbW₃ := h.mem_yamadaW₃_of_mem_yamadaM₃ d hlay (Subgroup.mem_inf.1 hb).1 hbg
  have hnW₂ : n ∈ yamadaW₂ d t := by
    rw [← h.yamadaM₂_inf_yamadaW₃ d hlay]
    refine Subgroup.mem_inf.2 ⟨hn, ?_⟩
    have := mul_mem hx (inv_mem hbW₃)
    rwa [← e, mul_inv_cancel_right] at this
  rw [← e, conj_mul_mul_inv_aux' hbg]
  exact leviThree_commutator_mem_yamadaY₂_of_mem_yamadaW₂ h d hlay hnW₂

private theorem mem_yamadaW₃_of_mem_yamadaM₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hκ : ∀ x ∈ yamadaL₆ d t, ∃ m ∈ yamadaM₃ d t, x * t * x⁻¹ = t * m)
    (hker : yamadaL₆ d t ⊓ normalizer ((yamadaW₃ d t ⊔ zpowers t : Subgroup G) : Set G) =
      yamadaL₃ d t)
    {c : G} (hc : c ∈ yamadaM₆ d t)
    (hcg : ((d.leviThree : L) : G) * c = c * ((d.leviThree : L) : G)) :
    c ∈ yamadaW₃ d t := by
  have hcL₆ : c ∈ yamadaL₆ d t := (Subgroup.mem_inf.1 hc).1
  have hcY₂ : c ∈ centralizer (yamadaY₂ d t : Set G) := (Subgroup.mem_inf.1 hc).2
  obtain ⟨m, hmM₃, hm⟩ := hκ c hcL₆
  have hgt : Commute ((d.leviThree : L) : G) t :=
    mem_centralizer_singleton_iff.1 (h.L_le_centralizer d.leviThree.2)
  have hgc : Commute ((d.leviThree : L) : G) c := hcg
  have hmg : m * ((d.leviThree : L) : G) = ((d.leviThree : L) : G) * m := by
    have hm' : m = t⁻¹ * (c * t * c⁻¹) := by
      rw [hm]
      group
    have hgm : Commute ((d.leviThree : L) : G) (t⁻¹ * (c * t * c⁻¹)) :=
      hgt.inv_right.mul_right ((hgc.mul_right hgt).mul_right hgc.inv_right)
    rw [hm']
    exact hgm.symm.eq
  have hmW₃ : m ∈ yamadaW₃ d t := h.mem_yamadaW₃_of_mem_yamadaM₃ d hlay hmM₃ hmg
  have htL₃ : t ∈ yamadaL₃ d t := by
    rw [h.yamadaL₃_eq_sup d hlay]
    exact mem_sup_right (mem_zpowers t)
  have htW₃ : t ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaL₃_le_normalizer_yamadaW₃ d hlay htL₃
  have hcN : c ∈ normalizer ((yamadaW₃ d t ⊔ zpowers t : Subgroup G) : Set G) :=
    h.mem_normalizer_sup_zpowers_D3 htW₃ (yamadaL₆_le_normalizer_yamadaW₃ h d hlay hcL₆) (by
      rw [hm]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hmW₃))
  have hcL₃ : c ∈ yamadaL₃ d t := hker.le (Subgroup.mem_inf.2 ⟨hcL₆, hcN⟩)
  have hcM₃ : c ∈ yamadaM₃ d t := Subgroup.mem_inf.2 ⟨hcL₃, hcY₂⟩
  exact h.mem_yamadaW₃_of_mem_yamadaM₃ d hlay hcM₃ hcg.symm

theorem commutator_mem_yamadaY₂_of_mem_yamadaM₆ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    (hNCY : centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaL₃ d t : Set G) ⊓ normalizer (yamadaM₃ d t : Set G))
    (hκ : ∀ x ∈ yamadaL₆ d t, ∃ m ∈ yamadaM₃ d t, x * t * x⁻¹ = t * m)
    (hker : yamadaL₆ d t ⊓ normalizer ((yamadaW₃ d t ⊔ zpowers t : Subgroup G) : Set G) =
      yamadaL₃ d t)
    {m w : G} (hm : m ∈ yamadaM₆ d t) (hw : w ∈ yamadaW₃ d t) :
    m * w * m⁻¹ * w⁻¹ ∈ yamadaY₂ d t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h521 := h.yamada_5_21 d hlay
  have hgNY : ((d.leviThree : L) : G) ∈ centralizer ({t} : Set G) ⊓
      normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) :=
    Subgroup.mem_inf.2 ⟨h.L_le_centralizer d.leviThree.2,
      coe_mem_normalizer_map (d.leviLong_le_normalizer_Y d.leviThree_mem_leviLong)⟩
  have hgNN := hNCY hgNY
  have hgY₂ : ((d.leviThree : L) : G) ∈ normalizer (yamadaY₂ d t : Set G) :=
    h.leviLong_map_le_normalizer_yamadaY₂ d hlay ⟨_, d.leviThree_mem_leviLong, rfl⟩
  have hgW₂ : ((d.leviThree : L) : G) ∈ normalizer (yamadaW₂ d t : Set G) :=
    mem_normalizer_sup (coe_mem_normalizer_map
      (d.leviLong_le_normalizer_W d.leviThree_mem_leviLong)) hgY₂
  have hgW₃ : ((d.leviThree : L) : G) ∈ normalizer (yamadaW₃ d t : Set G) :=
    mem_normalizer_inf_D4 (Subgroup.mem_inf.1 hgNN).1 (mem_normalizer_centralizer_D4 hgW₂)
  have hgM₆ : ((d.leviThree : L) : G) ∈ normalizer (yamadaM₆ d t : Set G) :=
    mem_normalizer_inf_D4 (le_normalizer_yamadaL₆ d t hgNN)
      (mem_normalizer_centralizer_D4 hgY₂)
  have hPZ : yamadaM₆ d t ≤ normalizer (yamadaY₂ d t : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.1 hx).2
  have hPW : yamadaM₆ d t ≤ normalizer (yamadaW₃ d t : Set G) := fun x hx =>
    yamadaL₆_le_normalizer_yamadaW₃ h d hlay (yamadaM₆_le_yamadaL₆ d t hx)
  have hWZ : yamadaW₃ d t ≤ normalizer (yamadaY₂ d t : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _
      (centralizer_le (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) (Subgroup.mem_inf.1 hx).2)
  have hWc : ∀ a ∈ yamadaW₃ d t, ∀ b ∈ yamadaW₃ d t, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h521.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hP : IsPGroup 2 (yamadaM₆ d t) :=
    (isPGroup_yamadaL₆ d t).to_le (yamadaM₆_le_yamadaL₆ d t)
  have hg3 : Nat.card (zpowers ((d.leviThree : L) : G)) = 3 := by
    rw [Nat.card_zpowers]
    refine orderOf_eq_prime ?_ fun h1 => d.leviThree_ne_one (Subtype.ext h1)
    have := congrArg Subtype.val d.leviThree_pow_three
    rwa [Subgroup.coe_pow, OneMemClass.coe_one] at this
  exact commutator_mem_of_fixed_mem hPZ hPW hWZ hWc hgM₆ hgY₂ hgW₃
    (fun w hw => leviThree_commutator_mem_yamadaY₂_of_mem_yamadaW₃ h d hlay hw) hP hg3
    (fun c hc hcg => mem_yamadaW₃_of_mem_yamadaM₆ h d hlay hκ hker hc hcg) hm hw

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4

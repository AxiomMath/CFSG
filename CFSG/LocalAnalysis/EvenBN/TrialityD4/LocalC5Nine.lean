module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Eight

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open scoped commutatorElement Pointwise

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem M_inf_centralizer_W_C9 : d.M ⊓ centralizer (d.W : Set X) = d.W := by
  refine le_antisymm (fun m hm => ?_) (le_inf (d.W_le_F.trans d.F_le_M) fun w hw =>
    mem_centralizer_iff.2 fun w' hw' => d.mul_comm_of_mem_W hw' hw)
  obtain ⟨hmM, hmC⟩ := mem_inf.1 hm
  obtain ⟨a, c, w, hw, rfl⟩ := d.mem_M_iff_x₁_x₃.1 hmM
  have key : ∀ b, d.x₆ (fixedTrace d.σ_cube (c * b)) * d.x₅ (fixedTrace d.σ_cube (a * b)) = 1 := by
    intro b
    have h1 : d.x₄ b * (d.x₁ a * d.x₃ c * w) = (d.x₁ a * d.x₃ c * w) * d.x₄ b :=
      mem_centralizer_iff.1 hmC (d.x₄ b) (d.x₄_mem_W b)
    have hwx : w * d.x₄ b * w⁻¹ = d.x₄ b := by
      rw [d.mul_comm_of_mem_W hw (d.x₄_mem_W b), mul_inv_cancel_right]
    have e1 : d.x₃ c * d.x₄ b * (d.x₃ c)⁻¹ = d.x₆ (fixedTrace d.σ_cube (c * b)) * d.x₄ b := by
      rw [← d.comm₃₄ c b, commutatorElement_def]
      group
    have e2 : d.x₁ a * d.x₄ b * (d.x₁ a)⁻¹ = d.x₅ (fixedTrace d.σ_cube (a * b)) * d.x₄ b := by
      rw [← d.comm₁₄ a b, commutatorElement_def]
      group
    have e3 : d.x₁ a * d.x₆ (fixedTrace d.σ_cube (c * b)) * (d.x₁ a)⁻¹ =
        d.x₆ (fixedTrace d.σ_cube (c * b)) := by
      rw [(d.commute₁₆ a _).eq, mul_inv_cancel_right]
    have h2 : (d.x₁ a * d.x₃ c * w) * d.x₄ b * (d.x₁ a * d.x₃ c * w)⁻¹ = d.x₄ b := by
      rw [← h1, mul_inv_cancel_right]
    have h3 : (d.x₁ a * d.x₃ c * w) * d.x₄ b * (d.x₁ a * d.x₃ c * w)⁻¹ =
        d.x₆ (fixedTrace d.σ_cube (c * b)) * d.x₅ (fixedTrace d.σ_cube (a * b)) * d.x₄ b := by
      calc (d.x₁ a * d.x₃ c * w) * d.x₄ b * (d.x₁ a * d.x₃ c * w)⁻¹ =
            d.x₁ a * (d.x₃ c * (w * d.x₄ b * w⁻¹) * (d.x₃ c)⁻¹) * (d.x₁ a)⁻¹ := by group
        _ = d.x₁ a * (d.x₆ (fixedTrace d.σ_cube (c * b)) * d.x₄ b) * (d.x₁ a)⁻¹ := by
            rw [hwx, e1]
        _ = (d.x₁ a * d.x₆ (fixedTrace d.σ_cube (c * b)) * (d.x₁ a)⁻¹) *
            (d.x₁ a * d.x₄ b * (d.x₁ a)⁻¹) := by group
        _ = _ := by rw [e3, e2, mul_assoc]
    rw [h3] at h2
    exact mul_right_cancel (h2.trans (one_mul _).symm)
  have h5 : ∀ b, fixedTrace d.σ_cube (a * b) = 0 := fun b => by
    have h6 : d.x₅ (fixedTrace d.σ_cube (a * b)) ∈ d.V := by
      rw [eq_inv_of_mul_eq_one_right (key b)]
      exact inv_mem (d.x₆_mem_V _)
    exact d.x₅_mem_V_iff.1 h6
  have h7 : ∀ b, fixedTrace d.σ_cube (c * b) = 0 := fun b => by
    have := key b
    rw [h5 b, d.x₅_zero, mul_one] at this
    exact d.x₆_eq_one_iff.1 this
  rw [d.eq_zero_of_forall_tr_mul h5, d.eq_zero_of_forall_tr_mul h7, d.x₁_zero, d.x₃_zero,
    one_mul, one_mul]
  exact hw

end TrialityD4Data

section Generic

variable {G : Type*} [Group G]

@[expose] def centralizerModNC9 (N : Subgroup G) (K : Set G) : Subgroup G where
  carrier := {g | g ∈ normalizer (N : Set G) ∧ ∀ a ∈ K, g * a * g⁻¹ * a⁻¹ ∈ N}
  mul_mem' := by
    rintro g h ⟨hg, hga⟩ ⟨hh, hha⟩
    refine ⟨mul_mem hg hh, fun a ha => ?_⟩
    have := mul_mem ((mem_normalizer_iff.1 hg _).1 (hha a ha)) (hga a ha)
    rwa [show g * (h * a * h⁻¹ * a⁻¹) * g⁻¹ * (g * a * g⁻¹ * a⁻¹) =
      g * h * a * (g * h)⁻¹ * a⁻¹ by group] at this
  one_mem' := ⟨one_mem _, fun a _ => by
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]
    exact one_mem N⟩
  inv_mem' := by
    rintro g ⟨hg, hga⟩
    refine ⟨inv_mem hg, fun a ha => ?_⟩
    have := (mem_normalizer_iff.1 (inv_mem hg) _).1 (inv_mem (hga a ha))
    rwa [show g⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * g⁻¹⁻¹ = g⁻¹ * a * g⁻¹⁻¹ * a⁻¹ by group] at this

theorem commutator_sup_le_of_le_C9 {A B N : Subgroup G} (hA : A ≤ normalizer (N : Set G))
    (hB : B ≤ normalizer (N : Set G)) (hAA : ⁅A, A⁆ ≤ N) (hBB : ⁅B, B⁆ ≤ N) (hAB : ⁅A, B⁆ ≤ N) :
    ⁅A ⊔ B, A ⊔ B⁆ ≤ N := by
  have hBA : ⁅B, A⁆ ≤ N := by
    rw [commutator_comm]
    exact hAB
  have h1 : ∀ K : Subgroup G, ⁅A, K⁆ ≤ N → ⁅B, K⁆ ≤ N →
      A ⊔ B ≤ centralizerModNC9 N (K : Set G) := fun K hAK hBK =>
    sup_le (fun a ha => ⟨hA ha, fun k hk => hAK (commutator_mem_commutator ha hk)⟩)
      (fun b hb => ⟨hB hb, fun k hk => hBK (commutator_mem_commutator hb hk)⟩)
  have hHA := h1 A hAA hBA
  have hHB := h1 B hAB hBB
  rw [commutator_le]
  intro x hx y hy
  have hle : A ⊔ B ≤ centralizerModNC9 N {x} := by
    refine sup_le (fun a ha => ⟨hA ha, fun k hk => ?_⟩) (fun b hb => ⟨hB hb, fun k hk => ?_⟩)
    · rw [Set.mem_singleton_iff.1 hk]
      have := inv_mem ((hHA hx).2 a ha)
      rwa [show (x * a * x⁻¹ * a⁻¹)⁻¹ = a * x * a⁻¹ * x⁻¹ by group] at this
    · rw [Set.mem_singleton_iff.1 hk]
      have := inv_mem ((hHB hx).2 b hb)
      rwa [show (x * b * x⁻¹ * b⁻¹)⁻¹ = b * x * b⁻¹ * x⁻¹ by group] at this
  have := inv_mem ((hle hy).2 x rfl)
  rw [show (y * x * y⁻¹ * x⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ by group] at this
  rw [commutatorElement_def]
  exact this

end Generic

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Main

variable (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hNH : NormalizerHyp d t)
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
  (h5101 : (Subgroup.upperCentralSeries (yamadaR₂ d t) 1).map (yamadaR₂ d t).subtype =
      d.V.map L.subtype ∧
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 2).map (yamadaR₂ d t).subtype = yamadaY₁ d t ∧
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 3).map (yamadaR₂ d t).subtype =
      yamadaW₂ d t ⊔ zpowers t ∧
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 4).map (yamadaR₂ d t).subtype =
      yamadaF₂ d t ⊔ zpowers t)
  (h5102 : CFSG.Open.thompsonSubgroup (yamadaF₂ d t ⊔ zpowers t) = yamadaF₂ d t)
  (h59e : yamadaY₂ d t = jZeroLayer d ⊓ yamadaL₂ d t)
  (h520 : yamadaC₅ d t = yamadaD₅ d t ⊔ zpowers t ∧ t ∉ yamadaD₅ d t ∧
    yamadaD₅ d t = yamadaD₃ d t ⊔ (yamadaD₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom ∧
    yamadaD₃ d t ⊓ (yamadaD₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom =
      yamadaD₁ d t ∧
    yamadaL₃ d t = yamadaM₃ d t ⊔ zpowers t ∧ t ∉ yamadaM₃ d t ∧
    yamadaR₃ d t = yamadaS₃ d t ⊔ zpowers t ∧ t ∉ yamadaS₃ d t)
  (h5221 : ((yamadaF₃ d t ⊔ zpowers t).subgroupOf (yamadaR₃ d t)).Characteristic ∧
    ((yamadaL₃ d t).subgroupOf (yamadaR₃ d t)).Characteristic ∧
    ⁅yamadaR₃ d t, yamadaR₃ d t⁆ = yamadaF₂ d t)
  (h521 : yamadaW₃ d t =
      yamadaF₃ d t ⊓ (yamadaF₃ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom ∧
    IsElemAbelian 2 (yamadaW₃ d t) ∧ Nat.card (yamadaW₃ d t) = (2 ^ f) ^ 10)

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem W_map_le_yamadaW₃_C9 : d.W.map L.subtype ≤ yamadaW₃ d t := by
  have hWL₃ : d.W.map L.subtype ≤ yamadaL₃ d t :=
    (map_mono (d.W_le_F.trans d.F_le_M)).trans ((le_sup_left.trans (h.tM_le_yamadaL₂ d)).trans
      (h.yamadaL₂_le_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101 h5102))
  refine le_inf hWL₃ (le_centralizer_iff.1 (sup_le ?_ ?_))
  · rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (d.mul_comm_of_mem_W hb ha)
  · intro y hy
    rw [mem_centralizer_iff]
    intro w hw
    exact (commute_of_mem_M_of_mem_yamadaY₂ d h592 (map_mono (d.W_le_F.trans d.F_le_M) hw) hy)

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem yamadaV₁_le_yamadaW₃_C9 : yamadaV₁ d t ≤ yamadaW₃ d t := by
  refine le_inf ((le_sup_left : yamadaV₁ d t ≤ yamadaY₂ d t).trans
    ((yamadaY₂_le_yamadaL₂ d h591).trans
      (h.yamadaL₂_le_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101 h5102)))
    (le_centralizer_iff.1 (sup_le ?_ ?_))
  · rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    intro v hv
    exact (mul_comm_of_mem_S_of_mem_yamadaV₁ d h593 ⟨a, d.W_le_S ha, rfl⟩ hv).symm
  · intro y hy
    rw [mem_centralizer_iff]
    intro v hv
    exact mul_comm_of_isMulCommutative_D4 h592.2.2.1 v (le_sup_left (a := yamadaV₁ d t) hv) y hy

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem t_mem_normalizer_yamadaW₃_C9 : t ∈ normalizer (yamadaW₃ d t : Set G) := by
  have htL₃ : t ∈ yamadaL₃ d t := h.yamadaL₂_le_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101
    h5102 (h.tM_le_yamadaL₂ d (mem_sup_right (mem_zpowers t)))
  have htW₂ : t ∈ normalizer (yamadaW₂ d t : Set G) :=
    (h.normalizer_yamadaV₂_le d h562 h592).1 (le_normalizer (mem_sup_right (mem_zpowers t)))
  exact Common.mem_normalizer_inf (le_normalizer htL₃) (mem_normalizer_centralizer_C8 htW₂)

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem yamadaW₃_inf_centralizer_C9 :
    yamadaW₃ d t ⊓ centralizer ({t} : Set G) = d.W.map L.subtype := by
  refine le_antisymm (fun x hx => ?_) (le_inf (h.W_map_le_yamadaW₃_C9 d hNH h561 h562 h591 h592 h593
    h5101 h5102) ((map_subtype_le _).trans h.L_le_centralizer))
  obtain ⟨hxW₃, hxC⟩ := mem_inf.1 hx
  obtain ⟨hxL₃, hxW₂⟩ := mem_inf.1 hxW₃
  have h1 : x ∈ d.M.map L.subtype ⊔ zpowers t := by
    rw [← h.yamadaL₃_inf_centralizer d hNH h561 h562 h591 h592 h593 h5101 h5102]
    exact mem_inf.2 ⟨hxL₃, hxC⟩
  have hY₂C : x ∈ centralizer (yamadaY₂ d t : Set G) :=
    centralizer_le (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) hxW₂
  rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 h1 with h2 | h2
  · obtain ⟨m, hm, rfl⟩ := h2
    have hmW : m ∈ d.M ⊓ centralizer (d.W : Set L) := mem_inf.2 ⟨hm, mem_centralizer_iff.2
      fun w hw => Subtype.ext (mem_centralizer_iff.1 hxW₂ (w : G)
        ((le_sup_left : d.W.map L.subtype ≤ yamadaW₂ d t) ⟨w, hw, rfl⟩))⟩
    rw [d.M_inf_centralizer_W_C9] at hmW
    exact ⟨m, hmW, rfl⟩
  · exfalso
    have hmC : t * x ∈ centralizer (yamadaY₂ d t : Set G) :=
      mem_centralizer_iff.2 fun a ha => (commute_of_mem_M_of_mem_yamadaY₂ d h592 h2 ha).symm
    have := mul_mem hmC (inv_mem hY₂C)
    rw [mul_inv_cancel_right] at this
    exact t_not_mem_centralizer_yamadaY₂ d h592 this

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h521 in
theorem exists_mem_yamadaW₃_crossed_eq_C9 {w : G} (hw : w ∈ d.W.map L.subtype) :
    ∃ x ∈ yamadaW₃ d t, t * x * t * x⁻¹ = w := by
  have hWc := mul_comm_of_isMulCommutative_D4 h521.2.1.1
  have htN := h.t_mem_normalizer_yamadaW₃_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  have htx : ∀ x ∈ yamadaW₃ d t, t * x * t ∈ yamadaW₃ d t := fun x hx => by
    have := (mem_normalizer_iff.1 htN x).1 hx
    rwa [htinv] at this
  let φ : yamadaW₃ d t →* yamadaW₃ d t := MonoidHom.mk'
    (fun x => ⟨t * x * t * (x : G)⁻¹, mul_mem (htx _ x.2) (inv_mem x.2)⟩) fun x y => by
      apply Subtype.ext
      show t * ((x : G) * y) * t * ((x : G) * y)⁻¹ =
        (t * x * t * (x : G)⁻¹) * (t * y * t * (y : G)⁻¹)
      have hm : t * y * t * (y : G)⁻¹ ∈ yamadaW₃ d t := mul_mem (htx _ y.2) (inv_mem y.2)
      have hc : (t * y * t * (y : G)⁻¹) * (x : G)⁻¹ = (x : G)⁻¹ * (t * y * t * (y : G)⁻¹) :=
        hWc _ hm _ (inv_mem x.2)
      calc t * ((x : G) * y) * t * ((x : G) * y)⁻¹ =
            t * x * (t * t) * y * t * (y : G)⁻¹ * (x : G)⁻¹ := by rw [h.t_mul_t]; group
        _ = t * x * t * ((t * y * t * (y : G)⁻¹) * (x : G)⁻¹) := by group
        _ = t * x * t * ((x : G)⁻¹ * (t * y * t * (y : G)⁻¹)) := by rw [hc]
        _ = (t * x * t * (x : G)⁻¹) * (t * y * t * (y : G)⁻¹) := by group
  have hker : φ.ker.map (yamadaW₃ d t).subtype = d.W.map L.subtype := by
    rw [← h.yamadaW₃_inf_centralizer_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : t * y * t * (y : G)⁻¹ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hy)
      refine mem_inf.2 ⟨y.2, mem_centralizer_singleton_iff.2 ?_⟩
      calc (y : G) * t = (t * t) * y * t * (y : G)⁻¹ * y := by rw [h.t_mul_t]; group
        _ = t * (t * y * t * (y : G)⁻¹) * y := by group
        _ = t * y := by rw [hy', mul_one]
    · intro hx
      obtain ⟨hxW₃, hxC⟩ := mem_inf.1 hx
      refine ⟨⟨x, hxW₃⟩, MonoidHom.mem_ker.2 (Subtype.ext ?_), rfl⟩
      show t * x * t * x⁻¹ = 1
      rw [mul_assoc t, mem_centralizer_singleton_iff.1 hxC, ← mul_assoc, h.t_mul_t, one_mul,
        mul_inv_cancel]
  have hcardker : Nat.card φ.ker = (2 ^ f) ^ 5 := by
    rw [← card_map_of_injective (yamadaW₃ d t).subtype_injective, hker,
      card_map_of_injective L.subtype_injective, d.card_W]
  have hcard := card_ker_mul_card_range φ
  rw [hcardker, h521.2.2] at hcard
  have hrange : Nat.card φ.range = (2 ^ f) ^ 5 := by
    have h0 : 0 < (2 ^ f) ^ 5 := by positivity
    have : (2 ^ f) ^ 5 * Nat.card φ.range = (2 ^ f) ^ 5 * (2 ^ f) ^ 5 := by rw [hcard]; ring
    exact Nat.eq_of_mul_eq_mul_left h0 this
  have hL₃V := h.yamadaL₃_le_normalizer_yamadaV₂ d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hle : φ.range.map (yamadaW₃ d t).subtype ≤ d.W.map L.subtype := by
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact h.crossed_mem_W d h562 h592 (hL₃V (mem_inf.1 y.2).1)
  have heq : φ.range.map (yamadaW₃ d t).subtype = d.W.map L.subtype := by
    refine eq_of_le_of_card_ge hle ?_
    rw [card_map_of_injective (yamadaW₃ d t).subtype_injective, hrange,
      card_map_of_injective L.subtype_injective, d.card_W]
  rw [← heq] at hw
  obtain ⟨_, ⟨y, rfl⟩, rfl⟩ := hw
  exact ⟨y, y.2, rfl⟩

include h h561 h592 in
theorem yamadaC₁_inf_centralizer_yamadaV₁_le_C9 :
    yamadaC₁ d t ⊓ centralizer (yamadaV₁ d t : Set G) ≤ yamadaD₁ d t := by
  intro x hx
  obtain ⟨hxC₁, hxV₁⟩ := mem_inf.1 hx
  rw [h561.1] at hxC₁
  rcases (mem_sup_zpowers_iff_of_D4 h.t_mul_t (h.t_mem_normalizer_yamadaD₁ d)).1 hxC₁ with
    h1 | ⟨a, ha, rfl⟩
  · exact h1
  · exfalso
    have haV₁ : a ∈ centralizer (yamadaV₁ d t : Set G) :=
      mem_centralizer_iff.2 fun v hv => (commute_of_mem_yamadaV₁ d t hv ha).symm
    have := mul_mem (inv_mem haV₁) hxV₁
    rw [inv_mul_cancel_left] at this
    exact h.t_not_mem_centralizer_yamadaV₁_C8 d h592 this

omit [Finite G] in
include h521 in
theorem yamadaW₃_le_yamadaD₃_C9 : yamadaW₃ d t ≤ yamadaD₃ d t := by
  rw [h521.1]
  exact inf_le_left.trans inf_le_right

include h hNH h561 h562 h591 h592 h593 in
theorem yamadaD₁_le_yamadaD₃_C9 : yamadaD₁ d t ≤ yamadaD₃ d t := by
  have hD₁C₁ := h.yamadaD₁_le_yamadaC₁ d
  refine le_inf (le_inf ((hD₁C₁.trans (h.yamadaC₁_le_yamadaR₂ d)).trans
    (h.yamada_5_14 d hNH h561 h562 h591 h592 h593).2.2.2.1.1) fun δ hδ =>
      mem_centralizer_iff.2 fun v hv => (commute_of_mem_yamadaV₁ d t hv hδ).symm)
    (hD₁C₁.trans (yamadaC₁_le_yamadaC₅ d t))

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h521 in
theorem yamadaD₃_eq_sup_C9 : yamadaD₃ d t = yamadaW₃ d t ⊔ yamadaD₁ d t := by
  refine le_antisymm (fun x hx => ?_) (sup_le (yamadaW₃_le_yamadaD₃_C9 d h521)
    (h.yamadaD₁_le_yamadaD₃_C9 d hNH h561 h562 h591 h592 h593))
  obtain ⟨hxS₃, hxC₅⟩ := mem_inf.1 hx
  obtain ⟨hxR₃, -⟩ := mem_inf.1 hxS₃
  obtain ⟨w₁, hw₁, e⟩ := (h.yamada_5_14 d hNH h561 h562 h591 h592 h593).1.1 x hxR₃
  have hVW : yamadaV₁ d t ≤ normalizer ((d.W.map L.subtype : Subgroup G) : Set G) :=
    fun v hv => mem_normalizer_fintype fun w hw => by
      obtain ⟨w', hw', rfl⟩ := hw
      rw [SetLike.mem_coe, ← mul_comm_of_mem_S_of_mem_yamadaV₁ d h593 ⟨w', d.W_le_S hw', rfl⟩ hv,
        mul_inv_cancel_right]
      exact ⟨w', hw', rfl⟩
  rw [show yamadaW₁ d t = d.W.map L.subtype ⊔ yamadaV₁ d t from rfl, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left _ _ hVW, Set.mem_mul] at hw₁
  obtain ⟨w, hw, v, hv, rfl⟩ := hw₁
  obtain ⟨y, hy, hκy⟩ := h.exists_mem_yamadaW₃_crossed_eq_C9 d hNH h561 h562 h591 h592 h593 h5101
    h5102 h521 hw
  have hyD₃ := yamadaW₃_le_yamadaD₃_C9 d h521 hy
  have hyC₅ : y ∈ yamadaC₅ d t := (mem_inf.1 hyD₃).2
  have hwt : w * t = t * w := mem_centralizer_singleton_iff.1 (h.L_le_centralizer
    (map_subtype_le _ hw))
  have hww : w * w = 1 := by
    obtain ⟨w', hw', rfl⟩ := hw
    exact congrArg Subtype.val (d.mul_self_eq_one_of_mem_W hw')
  have ey : y * t * y⁻¹ = t * w := by
    rw [← hκy, show t * (t * y * t * y⁻¹) = (t * t) * y * t * y⁻¹ by group, h.t_mul_t, one_mul]
  have hz : t * (y⁻¹ * x) * t * (y⁻¹ * x)⁻¹ = y⁻¹ * v * y := by
    have e1 : t * y⁻¹ = y⁻¹ * (t * w) := by
      rw [← ey]
      group
    calc t * (y⁻¹ * x) * t * (y⁻¹ * x)⁻¹ = (t * y⁻¹) * (x * t * x⁻¹) * y := by group
      _ = y⁻¹ * (t * w) * (t * (w * v)) * y := by rw [e1, e]
      _ = y⁻¹ * ((w * t) * t * w) * v * y := by rw [hwt]; group
      _ = y⁻¹ * v * y := by rw [mul_assoc w, h.t_mul_t, mul_one, hww, mul_one]
  have hyV₁ : y ∈ normalizer (yamadaV₁ d t : Set G) :=
    normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t
      ((h.yamada_5_12 d hNH h561 h562 h591 h592 h593).1.2.2.1 (yamadaC₅_le d t hyC₅))
  have hzV₁ : y⁻¹ * v * y ∈ yamadaV₁ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hyV₁) v).1 hv
    rwa [inv_inv] at this
  have hzQ : y⁻¹ * x ∈ yamadaQ₅ d t := by
    rw [← h.yamadaC₅_eq_yamadaQ₅ d hNH h561 h562 h591 h592 h593]
    exact mul_mem (inv_mem hyC₅) hxC₅
  have hzC₁ := h.mem_yamadaC₁_of_crossed_mem d hNH h561 h562 hzQ (hz ▸ hzV₁)
  have hzD₁ : y⁻¹ * x ∈ yamadaD₁ d t := by
    refine h.yamadaC₁_inf_centralizer_yamadaV₁_le_C9 d h561 h592
      (mem_inf.2 ⟨hzC₁, ?_⟩)
    exact mul_mem (inv_mem (mem_inf.1 (mem_inf.1 hyD₃).1).2) (mem_inf.1 hxS₃).2
  have := mul_mem (mem_sup_left hy : y ∈ yamadaW₃ d t ⊔ yamadaD₁ d t) (mem_sup_right hzD₁)
  rwa [mul_inv_cancel_left] at this

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer_C9 {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  refine le_antisymm ?_ fun x hx => ⟨g⁻¹ * x * g, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hg x).1 hx
  · have := (mem_normalizer_iff.1 (inv_mem hg) x).1 hx
    rwa [inv_inv] at this
  · show g * (g⁻¹ * x * g) * g⁻¹ = x
    group

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h520 h521 in
theorem yamadaD₅_eq_sup_C9 :
    yamadaD₅ d t = yamadaW₃ d t ⊔ (yamadaW₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom := by
  set ug : G := ((d.u : L) : G) with hug
  have hD₁u : (yamadaD₁ d t).map (MulAut.conj ug).toMonoidHom = yamadaD₁ d t :=
    map_conj_eq_of_mem_normalizer_C9 (u_mem_normalizer_yamadaD₁ d h561)
  have hD₃ := h.yamadaD₃_eq_sup_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102 h521
  have hD₁le : yamadaD₁ d t ≤ yamadaW₃ d t ⊔ (yamadaW₃ d t).map (MulAut.conj ug).toMonoidHom := by
    rw [h.yamadaD₁_eq_sup_yamadaW₁ d h561 h562]
    have hW₁ : yamadaW₁ d t ≤ yamadaW₃ d t :=
      sup_le (h.W_map_le_yamadaW₃_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102)
        (h.yamadaV₁_le_yamadaW₃_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102)
    exact sup_le_sup hW₁ (map_mono hW₁)
  rw [h520.2.2.1, hD₃, Subgroup.map_sup, hD₁u]
  refine le_antisymm (sup_le (sup_le le_sup_left hD₁le) (sup_le le_sup_right hD₁le))
    (sup_le_sup le_sup_left le_sup_left)

include h hNH h561 h562 h591 h592 h593 in
theorem commutator_yamadaC₅_le_yamadaC₁_C9 : ⁅yamadaC₅ d t, yamadaC₅ d t⁆ ≤ yamadaC₁ d t := by
  obtain ⟨hN₁, hN₂, φ, -, -⟩ := h.yamada_5_12_module d hNH h561 h562 h591 h592 h593
  have hab : ∀ a b : (d.D.map L.subtype : Subgroup G) ⧸
      (d.V.map L.subtype).subgroupOf (d.D.map L.subtype), a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    have hc : ⁅((b⁻¹ : (d.D.map L.subtype : Subgroup G)) : G), ((a⁻¹ : (d.D.map L.subtype :
        Subgroup G)) : G)⁆ ∈ d.V.map L.subtype := by
      rw [← d.commutator_D_eq, Subgroup.map_commutator]
      exact commutator_mem_commutator (b⁻¹).2 (a⁻¹).2
    rw [commutatorElement_def] at hc
    rw [show (((a * b)⁻¹ * (b * a) : (d.D.map L.subtype : Subgroup G)) : G) =
      ((b⁻¹ : (d.D.map L.subtype : Subgroup G)) : G) *
        ((a⁻¹ : (d.D.map L.subtype : Subgroup G)) : G) *
        ((b⁻¹ : (d.D.map L.subtype : Subgroup G)) : G)⁻¹ *
        ((a⁻¹ : (d.D.map L.subtype : Subgroup G)) : G)⁻¹ by push_cast; group]
    exact hc
  rw [commutator_le]
  intro x hx y hy
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩ : yamadaC₅ d t)⁻¹ *
      (⟨y, hy⟩ : yamadaC₅ d t)⁻¹) : yamadaC₅ d t ⧸ (yamadaC₁ d t).subgroupOf (yamadaC₅ d t)) =
      1 := by
    apply φ.injective
    rw [map_one, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv, map_mul, map_mul, map_mul, map_inv, map_inv,
      hab (φ _) (φ _)]
    group
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
  exact h1

include h h561 in
theorem coe_mem_normalizer_yamadaD₅_C9 {l : L} (hl : l ∈ normalizer (d.V : Set L)) :
    (l : G) ∈ normalizer (yamadaC₅ d t : Set G) ∧ (l : G) ∈ normalizer (yamadaV₁ d t : Set G) ∧
      (l : G) ∈ normalizer (yamadaD₅ d t : Set G) := by
  have hC₁ : (l : G) ∈ normalizer (yamadaC₁ d t : Set G) := le_normalizer_yamadaC₁ d t
    (h.centralizer_inf_normalizer_V_le d ⟨h.L_le_centralizer l.2, coe_mem_normalizer_map hl⟩)
  have hC₅ := le_normalizer_yamadaC₅ d t hC₁
  have hV₁ := normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (h561.2.2 ⟨l, hl, rfl⟩)
  exact ⟨hC₅, hV₁, Common.mem_normalizer_inf hC₅ (mem_normalizer_centralizer_C8 hV₁)⟩

include h hNH h561 h562 h591 h592 h593 in
theorem commutator_yamadaD₅_le_yamadaD₁_C9 : ⁅yamadaD₅ d t, yamadaD₅ d t⁆ ≤ yamadaD₁ d t := by
  have hD₅C₅ : yamadaD₅ d t ≤ yamadaC₅ d t := inf_le_left
  exact (le_inf ((commutator_mono hD₅C₅ hD₅C₅).trans
    (h.commutator_yamadaC₅_le_yamadaC₁_C9 d hNH h561 h562 h591 h592 h593))
    ((commutator_le_of_le le_rfl le_rfl).trans inf_le_right)).trans
    (h.yamadaC₁_inf_centralizer_yamadaV₁_le_C9 d h561 h592)

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 in
theorem yamadaD₅_le_normalizer_yamadaF₃_C9 : yamadaD₅ d t ≤ normalizer (yamadaF₃ d t : Set G) := by
  intro x hx
  have hxR₅ : x ∈ yamadaR₅ d t := mem_sup_left (mem_inf.1 hx).1
  have h1 := normalizer_le_normalizer_commutator_C8 (yamadaR₄ d t)
    ((h.yamada_5_14 d hNH h561 h562 h591 h592 h593).2.2.2.2.2.2 hxR₅)
  rwa [(h.yamada_5_24 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221).2.2] at h1

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem yamadaF₃_inf_yamadaD₁_le_C9 : yamadaF₃ d t ⊓ yamadaD₁ d t ≤ yamadaF₁ d t := by
  intro x hx
  obtain ⟨hxF₃, hxD₁⟩ := mem_inf.1 hx
  have hxL₃ : x ∈ yamadaL₃ d t := (mem_inf.1 (mem_inf.1 hxF₃).1).1
  have hVD : yamadaV₁ d t ≤ normalizer ((d.D.map L.subtype : Subgroup G) : Set G) :=
    fun v hv => mem_normalizer_fintype fun δ hδ => by
      obtain ⟨δ', hδ', rfl⟩ := hδ
      rw [SetLike.mem_coe, ← mul_comm_of_mem_S_of_mem_yamadaV₁ d h593 ⟨δ', d.D_le_S hδ', rfl⟩ hv,
        mul_inv_cancel_right]
      exact ⟨δ', hδ', rfl⟩
  rw [h.yamadaD₁_eq_sup d h561 h562, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left _ _ hVD, Set.mem_mul] at hxD₁
  obtain ⟨_, ⟨δ, hδ, rfl⟩, v, hv, rfl⟩ := hxD₁
  have hvL₃ : v ∈ yamadaL₃ d t :=
    (mem_inf.1 (h.yamadaV₁_le_yamadaW₃_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102 hv)).1
  have hδL₃ : L.subtype δ ∈ yamadaL₃ d t := by
    have := mul_mem hxL₃ (inv_mem hvL₃)
    rwa [mul_inv_cancel_right] at this
  have hδM : L.subtype δ ∈ d.M.map L.subtype ⊔ zpowers t := by
    rw [← h.yamadaL₃_inf_centralizer d hNH h561 h562 h591 h592 h593 h5101 h5102]
    exact mem_inf.2 ⟨hδL₃, h.L_le_centralizer δ.2⟩
  rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 hδM with h1 | h1
  · rw [mem_map_iff_mem L.subtype_injective] at h1
    rw [h.yamadaF₁_eq_sup d h561 h562]
    exact mul_mem (mem_sup_left ⟨δ, d.M_inf_D_le_F ⟨h1, hδ⟩, rfl⟩) (mem_sup_right hv)
  · exfalso
    have := mul_mem (map_subtype_le _ h1) (inv_mem δ.2)
    rw [Subgroup.coe_subtype, mul_inv_cancel_right] at this
    exact h.t_not_mem_L this

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521 in
theorem commutator_yamadaW₃_conj_le_C9 :
    ⁅yamadaW₃ d t, (yamadaW₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom⁆ ≤
      yamadaF₁ d t := by
  have hD₅ := h.yamadaD₅_eq_sup_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102 h520 h521
  rw [commutator_le]
  intro x hx y hy
  have hxF₃ : x ∈ yamadaF₃ d t := by
    rw [h521.1] at hx
    exact (mem_inf.1 hx).1
  have hxD₅ : x ∈ yamadaD₅ d t := by
    rw [hD₅]
    exact mem_sup_left hx
  have hyD₅ : y ∈ yamadaD₅ d t := by
    rw [hD₅]
    exact mem_sup_right hy
  have h1 : ⁅x, y⁆ ∈ yamadaF₃ d t := by
    rw [commutatorElement_def, show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
    exact mul_mem hxF₃ ((mem_normalizer_iff.1 (h.yamadaD₅_le_normalizer_yamadaF₃_C9 d hNH h561 h562
      h591 h592 h593 h5101 h5102 h59e h520 h5221 hyD₅) x⁻¹).1 (inv_mem hxF₃))
  have h2 : ⁅x, y⁆ ∈ yamadaD₁ d t := h.commutator_yamadaD₅_le_yamadaD₁_C9 d hNH h561 h562 h591 h592
    h593 (commutator_mem_commutator hxD₅ hyD₅)
  exact h.yamadaF₃_inf_yamadaD₁_le_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102 (mem_inf.2 ⟨h1,
    h2⟩)

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521 in
theorem commutator_yamadaD₅_le_yamadaF₁_C9 : ⁅yamadaD₅ d t, yamadaD₅ d t⁆ ≤ yamadaF₁ d t := by
  set ug : G := ((d.u : L) : G) with hug
  have hC₅F₁ : yamadaC₅ d t ≤ normalizer (yamadaF₁ d t : Set G) :=
    (le_sup_left : yamadaC₅ d t ≤ yamadaR₅ d t).trans
      (h.yamadaR₅_le_normalizer_yamadaF₁ d hNH h561 h562 h591 h592 h593)
  have hW₃C₅ : yamadaW₃ d t ≤ yamadaC₅ d t := fun x hx =>
    (mem_inf.1 (yamadaW₃_le_yamadaD₃_C9 d h521 hx)).2
  have huC₅ := (h.coe_mem_normalizer_yamadaD₅_C9 d h561 d.u_mem_normalizer_V).1
  have hW₃uC₅ : (yamadaW₃ d t).map (MulAut.conj ug).toMonoidHom ≤ yamadaC₅ d t := by
    rw [← map_conj_eq_of_mem_normalizer_C9 huC₅]
    exact map_mono hW₃C₅
  have hW₃ab : ⁅yamadaW₃ d t, yamadaW₃ d t⁆ = ⊥ := commutator_self_eq_bot_iff.2 h521.2.1.1
  rw [h.yamadaD₅_eq_sup_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102 h520 h521]
  refine commutator_sup_le_of_le_C9 (hW₃C₅.trans hC₅F₁) (hW₃uC₅.trans hC₅F₁)
    (hW₃ab.le.trans bot_le) ?_ (h.commutator_yamadaW₃_conj_le_C9 d hNH h561 h562 h591 h592 h593
    h5101
      h5102 h59e h520 h5221 h521)
  rw [← map_commutator, hW₃ab, Subgroup.map_bot]
  exact bot_le

include h h561 h562 h593 in
theorem mem_of_coe_mem_yamadaD₁_C9 {x : L} :
    ((x : G) ∈ yamadaD₁ d t → x ∈ d.D) ∧ ((x : G) ∈ yamadaF₁ d t → x ∈ d.F) := by
  have key : ∀ {A : Subgroup L}, d.V ≤ A → A ≤ d.S →
      (x : G) ∈ A.map L.subtype ⊔ yamadaV₁ d t → x ∈ A := by
    intro A hVA hAS hx
    have hVN : yamadaV₁ d t ≤ normalizer ((A.map L.subtype : Subgroup G) : Set G) :=
      fun v hv => mem_normalizer_fintype fun a ha => by
        obtain ⟨a', ha', rfl⟩ := ha
        rw [SetLike.mem_coe, ← mul_comm_of_mem_S_of_mem_yamadaV₁ d h593 ⟨a', hAS ha', rfl⟩ hv,
          mul_inv_cancel_right]
        exact ⟨a', ha', rfl⟩
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hVN, Set.mem_mul] at hx
    obtain ⟨_, ⟨a, ha, rfl⟩, v, hv, e⟩ := hx
    have hvL : v ∈ L := by
      have := mul_mem (inv_mem a.2) (e ▸ x.2 : L.subtype a * v ∈ L)
      rwa [Subgroup.coe_subtype, inv_mul_cancel_left] at this
    have hvV : v ∈ d.V.map L.subtype := by
      rw [← h562.2.2.1]
      exact mem_inf.2 ⟨hv, h.L_le_centralizer hvL⟩
    obtain ⟨v', hv', rfl⟩ := hvV
    have : x = a * v' := L.subtype_injective (by rw [map_mul]; exact e.symm)
    rw [this]
    exact mul_mem ha (hVA hv')
  refine ⟨fun hx => key (d.V_le_Y.trans (d.Y_le_W.trans (d.W_le_F.trans d.F_le_D))) d.D_le_S ?_,
    fun hx => key (d.V_le_Y.trans (d.Y_le_W.trans d.W_le_F)) d.F_le_S ?_⟩
  · rwa [← h.yamadaD₁_eq_sup d h561 h562]
  · rwa [← h.yamadaF₁_eq_sup d h561 h562]

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521 in
theorem commutator_yamadaD₅_le_yamadaV₁_C9 : ⁅yamadaD₅ d t, yamadaD₅ d t⁆ ≤ yamadaV₁ d t := by
  set P := ⁅yamadaD₅ d t, yamadaD₅ d t⁆ with hP
  have hPD₁ := h.commutator_yamadaD₅_le_yamadaD₁_C9 d hNH h561 h562 h591 h592 h593
  have hPF₁ := h.commutator_yamadaD₅_le_yamadaF₁_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e
    h520 h5221 h521
  have hVV₁ : d.V.map L.subtype ≤ yamadaV₁ d t := by
    rw [← h562.2.2.1]
    exact inf_le_left
  have hmem := fun {x : L} => h.mem_of_coe_mem_yamadaD₁_C9 d h561 h562 h593 (x := x)
  set T : Subgroup L := (P ⊔ yamadaV₁ d t).comap L.subtype with hT
  have hVT : d.V ≤ T := fun v hv => mem_sup_right (hVV₁ ⟨v, hv, rfl⟩)
  have hTD : T ≤ d.D := fun x hx => (hmem).1 (sup_le hPD₁ (yamadaV₁_le_yamadaD₁ d t) hx)
  have hTF : T ≤ d.F := fun x hx => (hmem).2 (sup_le hPF₁ h562.2.2.2 hx)
  have hTN : d.leviShort ≤ normalizer (T : Set L) := by
    intro s hs
    obtain ⟨-, hsV₁, hsD₅⟩ :=
      h.coe_mem_normalizer_yamadaD₅_C9 d h561 (d.leviShort_le_normalizer_V hs)
    have hsP : (s : G) ∈ normalizer (P : Set G) := normalizer_le_normalizer_commutator_C8 _ hsD₅
    have hsPV : (s : G) ∈ normalizer ((P ⊔ yamadaV₁ d t : Subgroup G) : Set G) :=
      Common.mem_normalizer_sup hsP hsV₁
    refine mem_normalizer_fintype fun x hx => ?_
    show ((s * x * s⁻¹ : L) : G) ∈ P ⊔ yamadaV₁ d t
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (mem_normalizer_iff.1 hsPV x).1 hx
  rcases d.leviShort_irreducible_D_mod_V hVT hTD hTN with hTV | hTD'
  · intro z hz
    have hzD₁ := hPD₁ hz
    have hVD : yamadaV₁ d t ≤ normalizer ((d.D.map L.subtype : Subgroup G) : Set G) :=
      fun v hv => mem_normalizer_fintype fun δ hδ => by
        obtain ⟨δ', hδ', rfl⟩ := hδ
        rw [SetLike.mem_coe, ← mul_comm_of_mem_S_of_mem_yamadaV₁ d h593 ⟨δ', d.D_le_S hδ', rfl⟩
          hv, mul_inv_cancel_right]
        exact ⟨δ', hδ', rfl⟩
    rw [h.yamadaD₁_eq_sup d h561 h562, ← SetLike.mem_coe,
      coe_mul_of_right_le_normalizer_left _ _ hVD, Set.mem_mul] at hzD₁
    obtain ⟨_, ⟨δ, -, rfl⟩, v, hv, rfl⟩ := hzD₁
    have hδT : δ ∈ T := by
      show L.subtype δ ∈ P ⊔ yamadaV₁ d t
      have := mul_mem (mem_sup_left hz : _ ∈ P ⊔ yamadaV₁ d t) (inv_mem (mem_sup_right hv))
      rwa [mul_inv_cancel_right] at this
    rw [hTV] at hδT
    exact mul_mem (hVV₁ ⟨δ, hδT, rfl⟩) hv
  · exfalso
    have hDF : d.D ≤ d.F := hTD' ▸ hTF
    have hc := Subgroup.card_le_of_le hDF
    rw [d.card_D, d.card_F] at hc
    have h2 : 2 ≤ 2 ^ f := d.two_le_q
    have : (2 ^ f) ^ 8 < (2 ^ f) ^ 9 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521 in
theorem yamadaV₁_le_commutator_yamadaD₅ : yamadaV₁ d t ≤ ⁅yamadaD₅ d t, yamadaD₅ d t⁆ := by
  set P := ⁅yamadaD₅ d t, yamadaD₅ d t⁆ with hP
  have hPV₁ := h.commutator_yamadaD₅_le_yamadaV₁_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e
    h520 h5221 h521
  have hD₁C₅ : yamadaD₁ d t ≤ yamadaC₅ d t :=
    (h.yamadaD₁_le_yamadaC₁ d).trans (yamadaC₁_le_yamadaC₅ d t)
  have hDD₅ : d.D.map L.subtype ≤ yamadaD₅ d t := le_inf ((D_le_yamadaD₁ d t).trans hD₁C₅)
    fun δ hδ => mem_centralizer_iff.2 fun v hv =>
      (mul_comm_of_mem_S_of_mem_yamadaV₁ d h593 (map_mono d.D_le_S hδ) hv).symm
  have hVP : d.V.map L.subtype ≤ P := by
    rw [← d.commutator_D_eq, Subgroup.map_commutator]
    exact commutator_mono hDD₅ hDD₅
  have hY₂D₅ : yamadaY₂ d t ≤ yamadaD₅ d t :=
    le_inf (h.yamada_5_12 d hNH h561 h562 h591 h592 h593).2.2.1 fun a ha =>
      mem_centralizer_iff.2 fun v hv =>
        mul_comm_of_isMulCommutative_D4 h592.2.2.1 v (le_sup_left (a := yamadaV₁ d t) hv) a ha
  obtain ⟨z, hzP, hzV⟩ : ∃ z ∈ P, z ∉ d.V.map L.subtype := by
    obtain ⟨a, ha, e⟩ := h.exists_mem_yamadaY₂_conj_eq d h591 h592 (y := ((d.x₅ 1 : L) : G))
      ⟨_, d.x₅_mem_Y 1, rfl⟩
    by_contra hcon
    push Not at hcon
    set y₀ : G := ((d.x₅ 1 : L) : G) with hy₀
    have htat : t * a * t = y₀ * a := by
      calc t * a * t = t * (a * t * a⁻¹) * a := by group
        _ = y₀ * a := by rw [e, ← mul_assoc, h.t_mul_t, one_mul]
    have key : ∀ δ ∈ d.D, d.x₅ 1 * δ = δ * d.x₅ 1 := by
      intro δ hδ
      have hc := hcon _ (commutator_mem_commutator (hY₂D₅ ha) (hDD₅ ⟨δ, hδ, rfl⟩))
      rw [commutatorElement_def] at hc
      have hδt : (δ : G) * t = t * δ :=
        mem_centralizer_singleton_iff.1 (h.L_le_centralizer δ.2)
      have hcC : a * (δ : G) * a⁻¹ * (δ : G)⁻¹ ∈ centralizer ({t} : Set G) :=
        h.L_le_centralizer (map_subtype_le _ hc)
      have hct : t * (a * (δ : G) * a⁻¹ * (δ : G)⁻¹) * t = a * (δ : G) * a⁻¹ * (δ : G)⁻¹ := by
        rw [mul_assoc, mem_centralizer_singleton_iff.1 hcC, ← mul_assoc, h.t_mul_t, one_mul]
      have htδt : t * (δ : G) * t = δ := by
        rw [mul_assoc, hδt, ← mul_assoc, h.t_mul_t, one_mul]
      have htinv' : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
      have h2 : t * (a * (δ : G) * a⁻¹ * (δ : G)⁻¹) * t =
          (y₀ * a) * δ * (y₀ * a)⁻¹ * (δ : G)⁻¹ := by
        have e1 : t * (a * (δ : G) * a⁻¹ * (δ : G)⁻¹) * t =
            (t * a * t) * (t * (δ : G) * t) * (t * a * t)⁻¹ * (t * (δ : G) * t)⁻¹ := by
          rw [show (t * a * t)⁻¹ = t⁻¹ * a⁻¹ * t⁻¹ by group,
            show (t * (δ : G) * t)⁻¹ = t⁻¹ * (δ : G)⁻¹ * t⁻¹ by group, htinv']
          calc t * (a * (δ : G) * a⁻¹ * (δ : G)⁻¹) * t =
                t * a * (t * t) * (δ : G) * (t * t) * a⁻¹ * (t * t) * (δ : G)⁻¹ * t := by
                rw [h.t_mul_t]; group
            _ = _ := by group
        rw [e1, htat, htδt]
      have h3 : (y₀ * a) * δ * (y₀ * a)⁻¹ * (δ : G)⁻¹ = a * δ * a⁻¹ * (δ : G)⁻¹ :=
        h2.symm.trans hct
      have hcy : (a * (δ : G) * a⁻¹ * (δ : G)⁻¹) * y₀ = y₀ * (a * (δ : G) * a⁻¹ * (δ : G)⁻¹) := by
        obtain ⟨c', hc', hc'e⟩ := hc
        have hc'e' : (c' : G) = a * (δ : G) * a⁻¹ * (δ : G)⁻¹ := hc'e
        rw [← hc'e']
        exact congrArg Subtype.val (mem_centralizer_iff.1
          (d.S_le_centralizer_V (d.Y_le_S (d.x₅_mem_Y 1))) c' hc')
      have h4 : y₀ * (a * δ * a⁻¹) * y₀⁻¹ = a * δ * a⁻¹ := by
        calc y₀ * (a * δ * a⁻¹) * y₀⁻¹ = (y₀ * a) * δ * (y₀ * a)⁻¹ * (δ : G)⁻¹ * δ := by group
          _ = a * δ * a⁻¹ := by rw [h3]; group
      have h5 : (a * (δ : G) * a⁻¹ * (δ : G)⁻¹) * (y₀ * δ * y₀⁻¹) =
          (a * (δ : G) * a⁻¹ * (δ : G)⁻¹) * δ := by
        calc (a * (δ : G) * a⁻¹ * (δ : G)⁻¹) * (y₀ * δ * y₀⁻¹) =
              ((a * (δ : G) * a⁻¹ * (δ : G)⁻¹) * y₀) * δ * y₀⁻¹ := by group
          _ = y₀ * ((a * (δ : G) * a⁻¹ * (δ : G)⁻¹) * δ) * y₀⁻¹ := by rw [hcy]; group
          _ = y₀ * (a * δ * a⁻¹) * y₀⁻¹ := by group
          _ = (a * (δ : G) * a⁻¹ * (δ : G)⁻¹) * δ := by rw [h4]; group
      have h6 : y₀ * δ * y₀⁻¹ = δ := mul_left_cancel h5
      apply Subtype.ext
      show y₀ * δ = δ * y₀
      calc y₀ * δ = y₀ * δ * y₀⁻¹ * y₀ := by group
        _ = δ * y₀ := by rw [h6]
    have hx₅ : d.x₅ 1 ∈ d.D ⊓ centralizer (d.D : Set L) :=
      mem_inf.2 ⟨d.F_le_D (d.W_le_F (d.Y_le_W (d.x₅_mem_Y 1))),
        mem_centralizer_iff.2 fun δ hδ => (key δ hδ).symm⟩
    rw [d.D_inf_centralizer_D] at hx₅
    exact one_ne_zero (d.x₅_mem_V_iff.1 hx₅)
  have hV₁sq : ∀ v ∈ yamadaV₁ d t, v * v = 1 := fun v hv => by
    rw [← sq]
    exact h562.1.2 v hv
  have hV₁c := mul_comm_of_isMulCommutative_D4 h562.1.1
  have htV₁ : t ∈ normalizer (yamadaV₁ d t : Set G) :=
    normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (h.t_mem_normalizer_yamadaD₁ d)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  have htvt : ∀ v ∈ yamadaV₁ d t, t * v * t ∈ yamadaV₁ d t := fun v hv => by
    have := (mem_normalizer_iff.1 htV₁ v).1 hv
    rwa [htinv] at this
  have hκV : ∀ v ∈ yamadaV₁ d t, t * v * t * v⁻¹ ∈ d.V.map L.subtype := by
    intro v hv
    have h2 : t * v * t * v⁻¹ ∈ yamadaV₁ d t := mul_mem (htvt v hv) (inv_mem hv)
    rw [← h562.2.2.1]
    refine mem_inf.2 ⟨h2, mem_centralizer_singleton_iff.2 ?_⟩
    have h3 : t * (t * v * t * v⁻¹) * t = (t * v * t * v⁻¹)⁻¹ := by
      rw [show (t * v * t * v⁻¹)⁻¹ = v * t⁻¹ * v⁻¹ * t⁻¹ by group, htinv,
        show t * (t * v * t * v⁻¹) * t = (t * t) * v * t * v⁻¹ * t by group, h.t_mul_t, one_mul]
    have h4 : (t * v * t * v⁻¹)⁻¹ = t * v * t * v⁻¹ :=
      inv_eq_of_mul_eq_one_right (hV₁sq _ h2)
    calc (t * v * t * v⁻¹) * t = t * (t * (t * v * t * v⁻¹) * t) := by
          rw [← mul_assoc, ← mul_assoc, h.t_mul_t, one_mul]
      _ = t * (t * v * t * v⁻¹) := by rw [h3, h4]
  have hκ1 : ∀ v ∈ yamadaV₁ d t, t * v * t * v⁻¹ = 1 → v ∈ d.V.map L.subtype := by
    intro v hv e
    rw [← h562.2.2.1]
    refine mem_inf.2 ⟨hv, mem_centralizer_singleton_iff.2 ?_⟩
    have e' : t * v * t = v := by
      calc t * v * t = t * v * t * v⁻¹ * v := by group
        _ = v := by rw [e, one_mul]
    calc v * t = t * v * t * t := by rw [e']
      _ = t * v := by rw [mul_assoc (t * v), h.t_mul_t, mul_one]
  intro w hw
  by_cases hwV : w ∈ d.V.map L.subtype
  · exact hVP hwV
  have hzV₁ := hPV₁ hzP
  obtain ⟨z', hz', hz'e⟩ := hκV z hzV₁
  obtain ⟨w', hw', hw'e⟩ := hκV w hw
  have hz'1 : z' ≠ 1 := fun e => hzV (hκ1 z hzV₁ (by rw [← hz'e, e, map_one]))
  have hw'1 : w' ≠ 1 := fun e => hwV (hκ1 w hw (by rw [← hw'e, e, map_one]))
  obtain ⟨j, hj, hjz⟩ := (d.yamada_three_five_five.2.2.2.2.1).2 z' hz' hz'1 w' hw' hw'1
  have hjJ : j ∈ d.J := (inf_le_left : d.J₂ ≤ d.J) hj
  have hjD₅ := (h.coe_mem_normalizer_yamadaD₅_C9 d h561 (d.J_le_normalizer_V hjJ)).2.2
  have hjP : (j : G) ∈ normalizer (P : Set G) := normalizer_le_normalizer_commutator_C8 _ hjD₅
  have hjt : (j : G) * t = t * j := mem_centralizer_singleton_iff.1 (h.L_le_centralizer j.2)
  have hjt' : (j : G)⁻¹ * t * j = t := by rw [mul_assoc, ← hjt, inv_mul_cancel_left]
  set r := (j : G) * z * (j : G)⁻¹ with hr
  have hrP : r ∈ P := (mem_normalizer_iff.1 hjP z).1 hzP
  have hκr : t * r * t * r⁻¹ = t * w * t * w⁻¹ := by
    calc t * r * t * r⁻¹ = t * j * z * ((j : G)⁻¹ * t * j) * z⁻¹ * (j : G)⁻¹ := by
          rw [hr]; group
      _ = j * (t * z * t * z⁻¹) * (j : G)⁻¹ := by rw [hjt', ← hjt]; group
      _ = t * w * t * w⁻¹ := by
          rw [← hz'e, ← hw'e, ← hjz]
          simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
  have hrw : r⁻¹ * w ∈ d.V.map L.subtype := by
    rw [← h562.2.2.1]
    refine mem_inf.2 ⟨mul_mem (inv_mem (hPV₁ hrP)) hw, mem_centralizer_singleton_iff.2 ?_⟩
    have e1 : t * r * t = (t * w * t * w⁻¹) * r := by rw [← hκr]; group
    have e2 : t * w * t = (t * w * t * w⁻¹) * w := by group
    calc r⁻¹ * w * t = t * (t * r⁻¹ * t) * (t * w * t) := by
          rw [show t * (t * r⁻¹ * t) * (t * w * t) = (t * t) * r⁻¹ * (t * t) * w * t by group,
            h.t_mul_t]
          group
      _ = t * (t * r * t)⁻¹ * (t * w * t) := by
          rw [show (t * r * t)⁻¹ = t⁻¹ * r⁻¹ * t⁻¹ by group, htinv]
      _ = t * (r⁻¹ * w) := by rw [e1, e2]; group
  have := mul_mem hrP (hVP hrw)
  rwa [mul_inv_cancel_left] at this

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521 in
theorem commutator_yamadaD₅_eq : ⁅yamadaD₅ d t, yamadaD₅ d t⁆ = yamadaV₁ d t :=
  le_antisymm (h.commutator_yamadaD₅_le_yamadaV₁_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e
    h520 h5221 h521) (h.yamadaV₁_le_commutator_yamadaD₅ d hNH h561 h562 h591 h592 h593 h5101 h5102
      h59e h520 h5221 h521)

include h in
theorem t_mem_normalizer_yamadaD₅_C9 : t ∈ normalizer (yamadaD₅ d t : Set G) :=
  Common.mem_normalizer_inf (le_normalizer (yamadaC₁_le_yamadaC₅ d t (h.t_mem_yamadaC₁ d)))
    (mem_normalizer_centralizer_C8
      (normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (h.t_mem_normalizer_yamadaD₁ d)))

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521 in
theorem commutator_yamadaC₅_eq : ⁅yamadaC₅ d t, yamadaC₅ d t⁆ = yamadaD₁ d t := by
  have htC₅ : t ∈ yamadaC₅ d t := yamadaC₁_le_yamadaC₅ d t (h.t_mem_yamadaC₁ d)
  apply le_antisymm
  · have hD₅ : ⁅yamadaC₅ d t, yamadaC₅ d t⁆ ≤ yamadaD₅ d t := by
      rw [h520.1]
      refine commutator_sup_le_C8 ((zpowers_le).2 (h.t_mem_normalizer_yamadaD₅_C9 d)) ?_
      rw [commutator_le]
      intro x hx y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      obtain ⟨k', rfl⟩ := mem_zpowers_iff.1 hy
      rw [commutatorElement_eq_one_iff_mul_comm.2 (zpow_mul_comm t k k')]
      exact one_mem _
    exact (le_inf (h.commutator_yamadaC₅_le_yamadaC₁_C9 d hNH h561 h562 h591 h592 h593)
      (hD₅.trans inf_le_right)).trans (h.yamadaC₁_inf_centralizer_yamadaV₁_le_C9 d h561 h592)
  · rw [h.yamadaD₁_eq_sup d h561 h562]
    refine sup_le (fun δ hδ => ?_) ((h.yamadaV₁_le_commutator_yamadaD₅ d hNH h561 h562 h591 h592
      h593 h5101 h5102 h59e h520 h5221 h521).trans (commutator_mono inf_le_left inf_le_left))
    obtain ⟨x, hx, v, hv, e⟩ := (h.yamada_5_12 d hNH h561 h562 h591 h592 h593).2.1.2.1 δ
      (D_le_yamadaD₁ d t hδ)
    have h1 : ⁅t, x⁆ ∈ ⁅yamadaC₅ d t, yamadaC₅ d t⁆ := commutator_mem_commutator htC₅ hx
    have h2 : ⁅t, x⁆ = δ * v := by
      rw [commutatorElement_def, inv_eq_of_mul_eq_one_right h.t_mul_t,
        show t * x * t * x⁻¹ = t * (x * t * x⁻¹) by group, e, ← mul_assoc, ← mul_assoc,
        h.t_mul_t, one_mul]
    have hvC : v ∈ ⁅yamadaC₅ d t, yamadaC₅ d t⁆ :=
      (h.yamadaV₁_le_commutator_yamadaD₅ d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520
        h5221 h521).trans (commutator_mono inf_le_left inf_le_left) hv
    have := mul_mem h1 (inv_mem hvC)
    rwa [h2, mul_inv_cancel_right] at this

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521 in
theorem yamadaD₅_le_normalizer_yamadaW₃ :
    yamadaD₅ d t ≤ normalizer (yamadaW₃ d t : Set G) ∧
      yamadaD₅ d t ≤ normalizer
        ((yamadaW₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom : Set G) := by
  have hP := h.commutator_yamadaD₅_eq d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221
    h521
  have hD₅ := h.yamadaD₅_eq_sup_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102 h520 h521
  have hV₁W₃ := h.yamadaV₁_le_yamadaW₃_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102
  have huV₁ := (h.coe_mem_normalizer_yamadaD₅_C9 d h561 d.u_mem_normalizer_V).2.1
  have hV₁W₃u : yamadaV₁ d t ≤ (yamadaW₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom := by
    rw [← map_conj_eq_of_mem_normalizer_C9 huV₁]
    exact map_mono hV₁W₃
  have key : ∀ K : Subgroup G, yamadaV₁ d t ≤ K → K ≤ yamadaD₅ d t →
      yamadaD₅ d t ≤ normalizer (K : Set G) := fun K hVK hKD g hg =>
    mem_normalizer_fintype fun w hw => by
      have h1 : g * w * g⁻¹ * w⁻¹ ∈ yamadaV₁ d t := by
        rw [← hP]
        exact commutator_mem_commutator hg (hKD hw)
      have := mul_mem (hVK h1) hw
      rwa [inv_mul_cancel_right] at this
  exact ⟨key _ hV₁W₃ (hD₅ ▸ le_sup_left), key _ hV₁W₃u (hD₅ ▸ le_sup_right)⟩

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521 in
theorem mul_self_mem_yamadaV₁_of_mem_yamadaD₅ {x : G} (hx : x ∈ yamadaD₅ d t) :
    x * x ∈ yamadaV₁ d t := by
  have hP := h.commutator_yamadaD₅_eq d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221
    h521
  have hD₅ := h.yamadaD₅_eq_sup_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102 h520 h521
  have hN := (h.yamadaD₅_le_normalizer_yamadaW₃ d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e
    h520 h5221 h521).1
  have hW₃uD₅ : (yamadaW₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom ≤ yamadaD₅ d t :=
    hD₅ ▸ le_sup_right
  have hW₃D₅ : yamadaW₃ d t ≤ yamadaD₅ d t := hD₅ ▸ le_sup_left
  rw [hD₅, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ (hW₃uD₅.trans hN),
    Set.mem_mul] at hx
  obtain ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩ := hx
  set ug : G := ((d.u : L) : G) with hug
  have hbD₅ : (MulAut.conj ug).toMonoidHom b ∈ yamadaD₅ d t := hW₃uD₅ ⟨b, hb, rfl⟩
  have hc : (MulAut.conj ug).toMonoidHom b * a * ((MulAut.conj ug).toMonoidHom b)⁻¹ * a⁻¹ ∈
      yamadaV₁ d t := by
    rw [← hP]
    exact commutator_mem_commutator hbD₅ (hW₃D₅ ha)
  have hac : a * ((MulAut.conj ug).toMonoidHom b * a * ((MulAut.conj ug).toMonoidHom b)⁻¹ * a⁻¹) =
      ((MulAut.conj ug).toMonoidHom b * a * ((MulAut.conj ug).toMonoidHom b)⁻¹ * a⁻¹) * a :=
    (mem_centralizer_iff.1 (mem_inf.1 (hW₃D₅ ha)).2 _ hc).symm
  have ha2 : a * a = 1 := by
    rw [← sq]
    exact h521.2.1.2 a ha
  have hb2 : (MulAut.conj ug).toMonoidHom b * (MulAut.conj ug).toMonoidHom b = 1 := by
    rw [← map_mul, show b * b = 1 by rw [← sq]; exact h521.2.1.2 b hb, map_one]
  generalize (MulAut.conj ug).toMonoidHom b = b' at hc hac hb2
  have e : a * b' * (a * b') = b' * a * b'⁻¹ * a⁻¹ := by
    calc a * b' * (a * b') = (a * (b' * a * b'⁻¹ * a⁻¹)) * a * (b' * b') := by group
      _ = b' * a * b'⁻¹ * a⁻¹ := by rw [hac, mul_assoc _ a a, ha2, hb2, mul_one, mul_one]
  rw [e]
  exact hc

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521 in
theorem normalizer_yamadaC₅_eq :
    normalizer (yamadaC₅ d t : Set G) = yamadaC₅ d t ⊔ (centralizer ({t} : Set G) ⊓
      normalizer ((d.V.map L.subtype : Subgroup G) : Set G)) := by
  have hN := (h.yamada_5_12 d hNH h561 h562 h591 h592 h593).1.1
  refine le_antisymm (fun g hg => ?_) (sup_le le_normalizer fun c hc =>
    le_normalizer_yamadaC₅ d t (by rw [hN]; exact mem_sup_right hc))
  rw [← hN]
  have hgD₁ : g ∈ normalizer (yamadaD₁ d t : Set G) := by
    rw [← h.commutator_yamadaC₅_eq d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521]
    exact normalizer_le_normalizer_commutator_C8 _ hg
  have hgV₁ := normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t hgD₁
  have hgD₅ : g ∈ normalizer (yamadaD₅ d t : Set G) :=
    Common.mem_normalizer_inf hg (mem_normalizer_centralizer_C8 hgV₁)
  have htC₅ : t ∈ yamadaC₅ d t := yamadaC₁_le_yamadaC₅ d t (h.t_mem_yamadaC₁ d)
  have hgt : g * t * g⁻¹ ∈ yamadaC₅ d t := (mem_normalizer_iff.1 hg t).1 htC₅
  rw [h520.1] at hgt
  rcases (mem_sup_zpowers_iff_of_D4 h.t_mul_t (h.t_mem_normalizer_yamadaD₅_C9 d)).1 hgt with
    h1 | ⟨a, ha, e⟩
  · exfalso
    apply h520.2.1
    have := (mem_normalizer_iff.1 (inv_mem hgD₅) _).1 h1
    rwa [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
  · have hsq : (a * t) * (a * t) = 1 := by
      rw [← e, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, h.t_mul_t]
      group
    have hκ : t * a * t * a⁻¹ ∈ yamadaV₁ d t := by
      have h2 : t * a * t = a⁻¹ := by
        calc t * a * t = a⁻¹ * ((a * t) * (a * t)) := by group
          _ = a⁻¹ := by rw [hsq, mul_one]
      rw [h2, show a⁻¹ * a⁻¹ = (a * a)⁻¹ by group]
      exact inv_mem (h.mul_self_mem_yamadaV₁_of_mem_yamadaD₅ d hNH h561 h562 h591 h592 h593 h5101
        h5102 h59e h520 h5221 h521 ha)
    have haQ : a ∈ yamadaQ₅ d t := by
      rw [← h.yamadaC₅_eq_yamadaQ₅ d hNH h561 h562 h591 h592 h593]
      exact (mem_inf.1 ha).1
    have haD₁ : a ∈ yamadaD₁ d t := h.yamadaC₁_inf_centralizer_yamadaV₁_le_C9 d h561 h592
      (mem_inf.2 ⟨h.mem_yamadaC₁_of_crossed_mem d hNH h561 h562 haQ hκ, (mem_inf.1 ha).2⟩)
    rw [h561.1]
    refine mem_normalizer_fintype fun n hn => ?_
    rcases (mem_sup_zpowers_iff_of_D4 h.t_mul_t (h.t_mem_normalizer_yamadaD₁ d)).1 hn with
      h2 | ⟨b, hb, rfl⟩
    · exact mem_sup_left ((mem_normalizer_iff.1 hgD₁ n).1 h2)
    · rw [show g * (b * t) * g⁻¹ = (g * b * g⁻¹) * (g * t * g⁻¹) by group, e, ← mul_assoc]
      exact mul_mem (mem_sup_left (mul_mem ((mem_normalizer_iff.1 hgD₁ b).1 hb) haD₁))
        (mem_sup_right (mem_zpowers t))

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem yamadaW₃_inf_yamadaD₁_le_C9 : yamadaW₃ d t ⊓ yamadaD₁ d t ≤ yamadaW₁ d t := by
  intro x hx
  obtain ⟨hxW₃, hxD₁⟩ := mem_inf.1 hx
  have hVD : yamadaV₁ d t ≤ normalizer ((d.D.map L.subtype : Subgroup G) : Set G) :=
    fun v hv => mem_normalizer_fintype fun δ hδ => by
      obtain ⟨δ', hδ', rfl⟩ := hδ
      rw [SetLike.mem_coe, ← mul_comm_of_mem_S_of_mem_yamadaV₁ d h593 ⟨δ', d.D_le_S hδ', rfl⟩ hv,
        mul_inv_cancel_right]
      exact ⟨δ', hδ', rfl⟩
  rw [h.yamadaD₁_eq_sup d h561 h562, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left _ _ hVD, Set.mem_mul] at hxD₁
  obtain ⟨_, ⟨δ, -, rfl⟩, v, hv, rfl⟩ := hxD₁
  have hvW₃ := h.yamadaV₁_le_yamadaW₃_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102 hv
  have hδW₃ : L.subtype δ ∈ yamadaW₃ d t := by
    have := mul_mem hxW₃ (inv_mem hvW₃)
    rwa [mul_inv_cancel_right] at this
  have hδW : L.subtype δ ∈ d.W.map L.subtype := by
    rw [← h.yamadaW₃_inf_centralizer_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102]
    exact mem_inf.2 ⟨hδW₃, h.L_le_centralizer δ.2⟩
  exact mul_mem (mem_sup_left hδW) (mem_sup_right hv)

include h h561 h562 in
theorem yamadaW₁_inf_conj_le_C9 :
    yamadaW₁ d t ⊓ (yamadaW₁ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom ≤
      yamadaV₁ d t := by
  obtain ⟨hW₁D₁, hW₁c, -⟩ := h.yamadaW₁_spec d h562
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
  refine mem_inf.2 ⟨hW₁D₁ hx1, ?_⟩
  rw [h.yamadaD₁_eq_sup_yamadaW₁ d h561 h562]
  refine mem_centralizer_iff.2 fun y hy => mem_centralizer_singleton_iff.1
    ((sup_le (fun w hw => mem_centralizer_singleton_iff.2 (hW₁c w hw x hx1)) ?_ :
      _ ≤ centralizer ({x} : Set G)) hy)
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨x', hx', rfl⟩ := hx2
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hW₁c w hw x' hx']

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h520 h521 in
theorem yamadaW₃_inf_conj_eq_C9 :
    yamadaW₃ d t ⊓ (yamadaW₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom =
      yamadaV₁ d t := by
  set ug : G := ((d.u : L) : G) with hug
  have huD₁ : ug ∈ normalizer (yamadaD₁ d t : Set G) := u_mem_normalizer_yamadaD₁ d h561
  have huV₁ : ug ∈ normalizer (yamadaV₁ d t : Set G) :=
    normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t huD₁
  have hV₁W₃ := h.yamadaV₁_le_yamadaW₃_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hV₁W₃u : yamadaV₁ d t ≤ (yamadaW₃ d t).map (MulAut.conj ug).toMonoidHom := by
    rw [← map_conj_eq_of_mem_normalizer_C9 huV₁]
    exact map_mono hV₁W₃
  have hW₃D₁ := h.yamadaW₃_inf_yamadaD₁_le_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102
  refine le_antisymm (fun x hx => ?_) (le_inf hV₁W₃ hV₁W₃u)
  obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
  have hxD₁ : x ∈ yamadaD₁ d t := by
    rw [← h520.2.2.2.1]
    exact mem_inf.2 ⟨yamadaW₃_le_yamadaD₃_C9 d h521 hx1,
      map_mono (yamadaW₃_le_yamadaD₃_C9 d h521) hx2⟩
  have hxW₁ : x ∈ yamadaW₁ d t := hW₃D₁ (mem_inf.2 ⟨hx1, hxD₁⟩)
  have hxW₁u : x ∈ (yamadaW₁ d t).map (MulAut.conj ug).toMonoidHom := by
    obtain ⟨y, hy, rfl⟩ := hx2
    have hyD₁ : y ∈ yamadaD₁ d t := by
      have := (mem_normalizer_iff.1 (inv_mem huD₁) _).1 hxD₁
      rwa [show ug⁻¹ * (MulAut.conj ug).toMonoidHom y * ug⁻¹⁻¹ = y by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group] at this
    exact ⟨y, hW₃D₁ (mem_inf.2 ⟨hy, hyD₁⟩), rfl⟩
  exact h.yamadaW₁_inf_conj_le_C9 d h561 h562 (mem_inf.2 ⟨hxW₁, hxW₁u⟩)

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521 in
theorem yamada_5_25 :
    ⁅yamadaD₅ d t, yamadaD₅ d t⁆ = yamadaV₁ d t ∧
      ⁅yamadaC₅ d t, yamadaC₅ d t⁆ = yamadaD₁ d t ∧
      normalizer (yamadaC₅ d t : Set G) = yamadaC₅ d t ⊔ (centralizer ({t} : Set G) ⊓
        normalizer ((d.V.map L.subtype : Subgroup G) : Set G)) ∧
      (yamadaD₅ d t =
          yamadaW₃ d t ⊔ (yamadaW₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom ∧
        yamadaW₃ d t ⊓ (yamadaW₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom =
          yamadaV₁ d t ∧
        yamadaD₅ d t ≤ normalizer (yamadaW₃ d t : Set G) ∧
        yamadaD₅ d t ≤ normalizer
          ((yamadaW₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom : Set G)) :=
  ⟨h.commutator_yamadaD₅_eq d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521,
    h.commutator_yamadaC₅_eq d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521,
    h.normalizer_yamadaC₅_eq d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521,
    h.yamadaD₅_eq_sup_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102 h520 h521,
    h.yamadaW₃_inf_conj_eq_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102 h520 h521,
    h.yamadaD₅_le_normalizer_yamadaW₃ d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221
      h521⟩

end Main

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4

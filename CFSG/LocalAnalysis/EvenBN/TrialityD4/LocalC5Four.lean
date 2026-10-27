module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Two

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open scoped commutatorElement Pointwise

section Defs

variable {G : Type} [Group G] {L : Subgroup G} {q : ℕ}

@[expose] noncomputable def yamadaL₃ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  pCoreOf 2 (normalizer (yamadaL₂ d t : Set G))

end Defs

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem commutatorElement_mem_Y_of_mem_M {m w : X} (hm : m ∈ d.M) (hw : w ∈ d.W) :
    m * w * m⁻¹ * w⁻¹ ∈ d.Y := by
  have := inv_mem ((d.mem_W_iff_forall_M.1 hw).2 m hm)
  rwa [commutatorElement_def, show (w * m * w⁻¹ * m⁻¹)⁻¹ = m * w * m⁻¹ * w⁻¹ by group] at this

theorem commutatorElement_mem_Y_of_mem_S {s w : X} (hs : s ∈ d.S) (hw : w ∈ d.W) :
    s * w * s⁻¹ * w⁻¹ ∈ d.Y := by
  have := d.commutator_S_W (commutator_mem_commutator hs hw)
  rwa [commutatorElement_def] at this

theorem commutatorElement_mem_Y_of_mem_leviLong {s w : X} (hs : s ∈ d.leviLong) (hw : w ∈ d.W) :
    s * w * s⁻¹ * w⁻¹ ∈ d.Y := by
  have hWN : d.leviLong ≤ normalizer (d.W : Set X) := by
    rw [← d.normalizer_Y_eq_normalizer_W_and_M.1]
    exact d.leviLong_le_normalizer_Y
  have hU₄Y : d.U₄ ≤ normalizer (d.Y : Set X) := d.U₄_le_S.trans d.S_le_normalizer_Y
  have hle : d.leviLong ≤ Common.centralizerMod (normalizer (d.W : Set X) ⊓
      normalizer (d.Y : Set X)) d.W d.Y
      (fun _ hg y hy => (mem_normalizer_iff.1 (mem_inf.1 hg).1 y).1 hy)
      (fun _ hg b hb => (mem_normalizer_iff.1 (mem_inf.1 hg).2 b).1 hb) := by
    refine (closure_le _).2 (Set.union_subset (fun u hu => ?_) (Set.singleton_subset_iff.2 ?_))
    · have huS : u ∈ d.S := d.U₂_le_S hu
      exact ⟨mem_inf.2 ⟨d.S_le_normalizer_W huS, d.S_le_normalizer_Y huS⟩,
        fun w hw => d.commutatorElement_mem_Y_of_mem_S huS hw⟩
    · refine ⟨mem_inf.2 ⟨hWN d.v_mem_leviLong, d.leviLong_le_normalizer_Y d.v_mem_leviLong⟩,
        fun w hw => ?_⟩
      rw [show d.W = d.U₄ ⊔ d.Y from rfl, ← SetLike.mem_coe,
        coe_mul_of_left_le_normalizer_right _ _ hU₄Y, Set.mem_mul] at hw
      obtain ⟨_, ⟨b, rfl⟩, y, hy, rfl⟩ := hw
      have hvy : d.v * y * d.v⁻¹ ∈ d.Y :=
        (mem_normalizer_iff.1 (d.leviLong_le_normalizer_Y d.v_mem_leviLong) y).1 hy
      have hvx : d.v * d.x₄ b * d.v⁻¹ = d.x₄ b := by rw [d.v_inv]; exact d.v_x₄ b
      have e : d.v * (d.x₄ b * y) * d.v⁻¹ * (d.x₄ b * y)⁻¹ =
          d.x₄ b * ((d.v * y * d.v⁻¹) * y⁻¹) * (d.x₄ b)⁻¹ := by
        calc d.v * (d.x₄ b * y) * d.v⁻¹ * (d.x₄ b * y)⁻¹ =
            (d.v * d.x₄ b * d.v⁻¹) * (d.v * y * d.v⁻¹) * y⁻¹ * (d.x₄ b)⁻¹ := by group
          _ = _ := by rw [hvx]; group
      rw [e]
      exact (mem_normalizer_iff.1 (hU₄Y ⟨b, rfl⟩) _).1 (mul_mem hvy (inv_mem hy))
  exact (Common.mem_centralizerMod.1 (hle hs)).2 w hw

theorem φ_pow_mem_W (k : ℕ) {y : X} (hy : y ∈ d.W) : (d.φ ^ k) y ∈ d.W := by
  have hle : d.W ≤ d.W.comap (d.φ ^ k).toMonoidHom := by
    show d.U₄ ⊔ d.Y ≤ _
    refine sup_le (fun _ hu => ?_) fun z hz => d.Y_le_W (d.φ_pow_mem_Y k hz)
    obtain ⟨a, rfl⟩ := hu
    show (d.φ ^ k) (d.x₄ a) ∈ d.W
    rw [d.φ_pow_x₄]
    exact d.x₄_mem_W _
  exact hle hy

theorem eq_conj_of_trivial_W_mod_Y {α : MulAut X} (hY : ∀ y ∈ d.Y, α y ∈ d.Y)
    (hW : ∀ w ∈ d.W, α w * w⁻¹ ∈ d.Y) :
    ∃ m ∈ d.M, ∃ s ∈ d.leviLong, α = MulAut.conj (m * s) := by
  obtain ⟨g, k, rfl⟩ := d.aut_eq α
  obtain ⟨m, hm, s, hs, j, hj, rfl⟩ :=
    d.exists_mul_of_mem_normalizer_Y (d.mem_normalizer_Y_of_conj_mul_φ_pow hY)
  obtain ⟨⟨l, μ⟩, rfl, hl⟩ := d.mem_J₂.1 hj
  dsimp only at hl
  subst hl
  have hms : ∀ w ∈ d.W, m * s * w * (m * s)⁻¹ * w⁻¹ ∈ d.Y := by
    intro w hw
    have hsw : s * w * s⁻¹ ∈ d.W := (mem_normalizer_iff.1 (by
      rw [← d.normalizer_Y_eq_normalizer_W_and_M.1]
      exact d.leviLong_le_normalizer_Y hs) w).1 hw
    have h1 := d.commutatorElement_mem_Y_of_mem_M hm hsw
    have h2 := d.commutatorElement_mem_Y_of_mem_leviLong hs hw
    have e : m * s * w * (m * s)⁻¹ * w⁻¹ =
        (m * (s * w * s⁻¹) * m⁻¹ * (s * w * s⁻¹)⁻¹) * (s * w * s⁻¹ * w⁻¹) := by group
    rw [e]
    exact mul_mem h1 h2
  have hcoord : ∀ a : d.Γ, d.σ (μ : d.Γ) * d.σ (d.σ (μ : d.Γ)) * a ^ 2 ^ k = a := by
    intro a
    set b := d.σ (μ : d.Γ) * d.σ (d.σ (μ : d.Γ)) * a ^ 2 ^ k with hb
    have h1 := hW (d.x₄ a) (d.x₄_mem_W a)
    have hjx : d.torus (1, μ) * d.x₄ (a ^ 2 ^ k) * (d.torus (1, μ))⁻¹ = d.x₄ b := by
      rw [d.torus_x₄]
      congr 1
      simp [hb, mul_assoc]
    rw [MulAut.mul_apply, d.φ_pow_x₄, MulAut.conj_apply,
      show m * s * d.torus (1, μ) * d.x₄ (a ^ 2 ^ k) * (m * s * d.torus (1, μ))⁻¹ =
        m * s * (d.torus (1, μ) * d.x₄ (a ^ 2 ^ k) * (d.torus (1, μ))⁻¹) * (m * s)⁻¹ by group,
      hjx] at h1
    have h2 := hms (d.x₄ b) (d.x₄_mem_W b)
    have h3 : d.x₄ b * (d.x₄ a)⁻¹ ∈ d.Y := by
      have := mul_mem (inv_mem h2) h1
      rwa [show (m * s * d.x₄ b * (m * s)⁻¹ * (d.x₄ b)⁻¹)⁻¹ *
        (m * s * d.x₄ b * (m * s)⁻¹ * (d.x₄ a)⁻¹) = d.x₄ b * (d.x₄ a)⁻¹ by group] at this
    rw [d.x₄_inv, ← d.x₄_add] at h3
    exact (eq_neg_of_add_eq_zero_left (d.x₄_mem_Y_iff.1 h3)).trans (CharTwo.neg_eq a)
  have hj1 : d.torus (1, μ) = 1 := by
    have hreg := (d.yamada_three_five_five.2.2.1).2 (d.x₄ 1) (d.x₄_mem_U₄ 1)
      (fun e => one_ne_zero (d.x₄_injective (e.trans d.x₄_zero.symm)))
      (d.x₄ 1) (d.x₄_mem_U₄ 1)
      (fun e => one_ne_zero (d.x₄_injective (e.trans d.x₄_zero.symm)))
    refine hreg.unique ⟨hj, ?_⟩ ⟨one_mem _, by group⟩
    rw [d.torus_x₄]
    congr 1
    have := hcoord 1
    simpa using this
  have hk : ∀ c : d.Γ, c ^ 2 ^ k = c := by
    intro c
    have h1 := hcoord c
    have hμ : d.σ (μ : d.Γ) * d.σ (d.σ (μ : d.Γ)) = 1 := by simpa using hcoord 1
    rwa [hμ, one_mul] at h1
  rw [d.φ_pow_eq_one_of_forall hk, hj1, mul_one, mul_one]
  exact ⟨m, hm, s, hs, rfl⟩

theorem eq_one_of_mem_leviLong_of_commute {s : X} (hs : s ∈ d.leviLong)
    (hc : ∀ s' ∈ d.leviLong, s * s' = s' * s) : s = 1 := by
  have h1 : d.leviLongEquiv ⟨s, hs⟩ ∈ center (Matrix.SpecialLinearGroup (Fin 2) d.Γ₀) :=
    mem_center_iff.2 fun A => by
      obtain ⟨s', rfl⟩ := d.leviLongEquiv.surjective A
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (hc s' s'.2).symm)
  rw [center_SL_two_eq_bot_D4, mem_bot] at h1
  exact congrArg Subtype.val (d.leviLongEquiv.injective (h1.trans (map_one _).symm))

theorem exists_φ_pow_eq_of_mem_W (k : ℕ) {w : X} (hw : w ∈ d.W) :
    ∃ w' ∈ d.W, (d.φ ^ k) w' = w := by
  have := d.finite
  let φW : d.W → d.W := fun y => ⟨(d.φ ^ k) y, d.φ_pow_mem_W k y.2⟩
  have hinj : Function.Injective φW := fun a b hab =>
    Subtype.ext ((d.φ ^ k).injective (congrArg Subtype.val hab))
  obtain ⟨w', hw'⟩ := Finite.surjective_of_injective hinj ⟨w, hw⟩
  exact ⟨w', w'.2, congrArg Subtype.val hw'⟩

end TrialityD4Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section NormalizerW

theorem centralizer_inf_normalizer_Y_eq_W (h : Setup G L f t) {q : ℕ}
    (d : TrialityD4Data L q) :
    centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) =
      centralizer ({t} : Set G) ⊓ normalizer ((d.W.map L.subtype : Subgroup G) : Set G) := by
  have hYW := d.normalizer_Y_eq_normalizer_W_and_M.1
  apply le_antisymm
  · rintro c ⟨hcC, hcY⟩
    obtain ⟨g, k, hgk⟩ := d.aut_eq (h.act ⟨c, hcC⟩)
    have hg : g ∈ normalizer (d.W : Set L) := by
      rw [← hYW]
      exact d.mem_normalizer_Y_of_conj_mul_φ_pow fun y hy => hgk ▸ h.act_mem_Y d hcC hcY y hy
    refine ⟨hcC, mem_normalizer_fintype fun z hz => ?_⟩
    obtain ⟨w, hw, rfl⟩ := hz
    rw [SetLike.mem_coe, Subgroup.coe_subtype, h.conj_mem_map_iff hcC, hgk, MulAut.mul_apply,
      MulAut.conj_apply]
    exact (mem_normalizer_iff.1 hg _).1 (d.φ_pow_mem_W k hw)
  · rintro c ⟨hcC, hcW⟩
    obtain ⟨g, k, hgk⟩ := d.aut_eq (h.act ⟨c, hcC⟩)
    have hact : ∀ w ∈ d.W, h.act ⟨c, hcC⟩ w ∈ d.W := fun w hw => by
      rw [← h.conj_mem_map_iff hcC]
      exact (mem_normalizer_iff.1 hcW _).1 ⟨w, hw, rfl⟩
    have hg : g ∈ normalizer (d.Y : Set L) := by
      rw [hYW]
      refine mem_normalizer_fintype fun w hw => ?_
      obtain ⟨w', hw', rfl⟩ := d.exists_φ_pow_eq_of_mem_W k hw
      have := hact w' hw'
      rwa [hgk, MulAut.mul_apply, MulAut.conj_apply] at this
    refine ⟨hcC, mem_normalizer_fintype fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hz
    rw [SetLike.mem_coe, Subgroup.coe_subtype, h.conj_mem_map_iff hcC, hgk, MulAut.mul_apply,
      MulAut.conj_apply]
    exact (mem_normalizer_iff.1 hg _).1 (d.φ_pow_mem_Y k hy)

end NormalizerW

section Main

variable (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
  (h562 : IsElemAbelian 2 (yamadaV₁ d t) ∧ Nat.card (yamadaV₁ d t) = (2 ^ f) ^ 2 ∧
    yamadaV₁ d t ⊓ centralizer ({t} : Set G) = d.V.map L.subtype ∧ yamadaV₁ d t ≤ yamadaF₁ d t)
  (h591 : yamadaL₂ d t = yamadaM₂ d t ⊔ zpowers t ∧ t ∉ yamadaM₂ d t ∧
    yamadaR₂ d t = yamadaS₂ d t ⊔ zpowers t ∧ t ∉ yamadaS₂ d t)
  (h592 : yamadaV₁ d t ⊓ (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom = ⊥ ∧
    Nat.card (yamadaY₂ d t) = (2 ^ f) ^ 4 ∧ IsMulCommutative (yamadaY₂ d t) ∧
    yamadaM₂ d t ⊓ centralizer (yamadaM₂ d t : Set G) = yamadaY₂ d t ∧
    yamadaY₂ d t ⊓ centralizer ({t} : Set G) = d.Y.map L.subtype)

omit [Finite G] in
include h592 in
theorem commute_of_mem_M_of_mem_yamadaY₂ {m a : G} (hm : m ∈ d.M.map L.subtype)
    (ha : a ∈ yamadaY₂ d t) : m * a = a * m := by
  rw [← h592.2.2.2.1] at ha
  exact mem_centralizer_iff.1 (mem_inf.1 ha).2 m (mem_sup_left hm)

omit [Finite G] in
include h592 in
theorem yamadaY₂_mul_comm {a b : G} (ha : a ∈ yamadaY₂ d t) (hb : b ∈ yamadaY₂ d t) :
    a * b = b * a :=
  mul_comm_of_isMulCommutative_D4 h592.2.2.1 a ha b hb

include h562 h592 in
theorem yamadaY₂_mul_self {a : G} (ha : a ∈ yamadaY₂ d t) : a * a = 1 := by
  have hV : yamadaV₁ d t ≤ normalizer
      ((yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom : Set G) := fun x hx =>
    mem_normalizer_fintype fun y hy => by
      rw [yamadaY₂_mul_comm d h592 (mem_sup_left hx) (mem_sup_right hy), mul_inv_cancel_right]
      exact hy
  rw [show yamadaY₂ d t = yamadaV₁ d t ⊔
      (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom from rfl, ← SetLike.mem_coe,
    coe_mul_of_left_le_normalizer_right _ _ hV, Set.mem_mul] at ha
  obtain ⟨b, hb, c, hc, rfl⟩ := ha
  have hb2 : b * b = 1 := by
    rw [← sq]
    exact h562.1.2 b hb
  have hc2 : c * c = 1 := by
    obtain ⟨c', hc', rfl⟩ := hc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 : c' * c' = 1 := by
      rw [← sq]
      exact h562.1.2 c' hc'
    rw [show ((d.v : L) : G) * c' * ((d.v : L) : G)⁻¹ * (((d.v : L) : G) * c' *
      ((d.v : L) : G)⁻¹) = ((d.v : L) : G) * (c' * c') * ((d.v : L) : G)⁻¹ by group, h1,
      mul_one, mul_inv_cancel]
  have hbc := yamadaY₂_mul_comm d h592 (mem_sup_left hb) (mem_sup_right hc)
  calc b * c * (b * c) = b * (c * b) * c := by group
    _ = b * (b * c) * c := by rw [hbc]
    _ = (b * b) * (c * c) := by group
    _ = 1 := by rw [hb2, hc2, one_mul]

omit [Finite G] in
include h592 in
theorem Y_le_yamadaY₂ : d.Y.map L.subtype ≤ yamadaY₂ d t :=
  h592.2.2.2.2.symm.le.trans inf_le_left

include h h592 in
theorem W_inf_yamadaY₂ : d.W.map L.subtype ⊓ yamadaY₂ d t = d.Y.map L.subtype := by
  refine le_antisymm (fun x hx => ?_) (le_inf (map_mono d.Y_le_W) (Y_le_yamadaY₂ d h592))
  rw [← h592.2.2.2.2]
  exact mem_inf.2 ⟨(mem_inf.1 hx).2, h.L_le_centralizer (map_subtype_le _ (mem_inf.1 hx).1)⟩

omit [Finite G] in
include h592 in
theorem yamadaY₂_le_normalizer_W [Finite G] :
    yamadaY₂ d t ≤ normalizer ((d.W.map L.subtype : Subgroup G) : Set G) := fun a ha =>
  mem_normalizer_fintype fun w hw => by
    rw [← commute_of_mem_M_of_mem_yamadaY₂ d h592 (map_mono (d.W_le_F.trans d.F_le_M) hw) ha,
      mul_inv_cancel_right]
    exact hw

omit [Finite G] in
include h592 in
theorem yamadaW₂_mul_comm {a b : G} (ha : a ∈ yamadaW₂ d t) (hb : b ∈ yamadaW₂ d t) :
    a * b = b * a := by
  have hWc : ∀ x ∈ d.W.map L.subtype, ∀ y ∈ d.W.map L.subtype, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (d.mul_comm_of_mem_W hx hy)
  exact mul_comm_of_mem_sup_D4 hWc (fun x hx y hy => yamadaY₂_mul_comm d h592 hx hy)
    (fun x hx y hy => commute_of_mem_M_of_mem_yamadaY₂ d h592
      (map_mono (d.W_le_F.trans d.F_le_M) hx) hy) a ha b hb

include h562 h592 in
theorem yamadaW₂_mul_self {a : G} (ha : a ∈ yamadaW₂ d t) : a * a = 1 := by
  rw [show yamadaW₂ d t = d.W.map L.subtype ⊔ yamadaY₂ d t from rfl, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left _ _ (yamadaY₂_le_normalizer_W d h592),
    Set.mem_mul] at ha
  obtain ⟨w, hw, y, hy, rfl⟩ := ha
  have hw2 : w * w = 1 := by
    obtain ⟨w', hw', rfl⟩ := hw
    exact congrArg Subtype.val (d.mul_self_eq_one_of_mem_W hw')
  have hwy : w * y = y * w := commute_of_mem_M_of_mem_yamadaY₂ d h592
    (map_mono (d.W_le_F.trans d.F_le_M) hw) hy
  calc w * y * (w * y) = w * (y * w) * y := by group
    _ = w * (w * y) * y := by rw [hwy]
    _ = (w * w) * (y * y) := by group
    _ = 1 := by rw [hw2, yamadaY₂_mul_self d h562 h592 hy, one_mul]

include h h592 in
theorem yamadaW₂_inf_centralizer :
    yamadaW₂ d t ⊓ centralizer ({t} : Set G) = d.W.map L.subtype := by
  have hWC : d.W.map L.subtype ≤ centralizer ({t} : Set G) :=
    (map_subtype_le _).trans h.L_le_centralizer
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left hWC)
  obtain ⟨hx₁, hx₂⟩ := mem_inf.1 hx
  rw [show yamadaW₂ d t = d.W.map L.subtype ⊔ yamadaY₂ d t from rfl, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left _ _ (yamadaY₂_le_normalizer_W d h592),
    Set.mem_mul] at hx₁
  obtain ⟨w, hw, y, hy, rfl⟩ := hx₁
  have hyC : y ∈ centralizer ({t} : Set G) := by
    have := mul_mem (inv_mem (hWC hw)) hx₂
    rwa [inv_mul_cancel_left] at this
  have hyY : y ∈ d.Y.map L.subtype := by
    rw [← h592.2.2.2.2]
    exact mem_inf.2 ⟨hy, hyC⟩
  exact mul_mem hw (map_mono d.Y_le_W hyY)

include h h592 in
theorem card_yamadaW₂ : Nat.card (yamadaW₂ d t) = (2 ^ f) ^ 7 := by
  have hcomm : ∀ x ∈ d.W.map L.subtype, ∀ y ∈ yamadaY₂ d t, x * y = y * x := fun x hx y hy =>
    commute_of_mem_M_of_mem_yamadaY₂ d h592 (map_mono (d.W_le_F.trans d.F_le_M) hx) hy
  have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  rw [h.W_inf_yamadaY₂ d h592, card_map_of_injective L.subtype_injective, d.card_Y,
    card_map_of_injective L.subtype_injective, d.card_W, h592.2.1] at h1
  show Nat.card (d.W.map L.subtype ⊔ yamadaY₂ d t : Subgroup G) = _
  have hq : 0 < (2 ^ f) ^ 2 := by positivity
  have h2 : Nat.card (d.W.map L.subtype ⊔ yamadaY₂ d t : Subgroup G) * (2 ^ f) ^ 2 =
      (2 ^ f) ^ 7 * (2 ^ f) ^ 2 := by rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_right hq h2

include h in
theorem t_mem_normalizer_yamadaW₂ : t ∈ normalizer (yamadaW₂ d t : Set G) :=
  Common.mem_normalizer_sup (h.t_mem_normalizer_map d.W) (h.t_mem_normalizer_yamadaY₂ d)

include h h592 in
theorem t_not_mem_yamadaW₂ : t ∉ yamadaW₂ d t := fun ht =>
  h.t_not_mem_L (map_subtype_le _ ((h.yamadaW₂_inf_centralizer d h592).le
    (mem_inf.2 ⟨ht, mem_centralizer_singleton_iff.2 rfl⟩)))

include h h562 h592 in
theorem conj_t_not_mem_yamadaW₂ (g : G) : g * t * g⁻¹ ∉ yamadaW₂ d t := by
  intro hg
  set E := (yamadaW₂ d t).map (MulAut.conj g⁻¹).toMonoidHom with hEdef
  have hmem : ∀ x ∈ E, ∃ w ∈ yamadaW₂ d t, x = g⁻¹ * w * g := fun x hx => by
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨w, hw, by simp⟩
  have hEC : E ≤ centralizer ({t} : Set G) := fun x hx => by
    obtain ⟨w, hw, rfl⟩ := hmem x hx
    rw [mem_centralizer_singleton_iff]
    have hwt : (g * t * g⁻¹) * w = w * (g * t * g⁻¹) := yamadaW₂_mul_comm d h592 hg hw
    calc g⁻¹ * w * g * t = g⁻¹ * (w * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * w) * g := by rw [hwt]
      _ = t * (g⁻¹ * w * g) := by group
  have hEab : IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨u, hu, hua⟩ := hmem a a.2
      obtain ⟨v, hv, hvb⟩ := hmem b b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hua, hvb]
      have huv : u * v = v * u := yamadaW₂_mul_comm d h592 hu hv
      calc g⁻¹ * u * g * (g⁻¹ * v * g) = g⁻¹ * (u * v) * g := by group
        _ = g⁻¹ * (v * u) * g := by rw [huv]
        _ = g⁻¹ * v * g * (g⁻¹ * u * g) := by group
    · obtain ⟨u, hu, rfl⟩ := hmem x hx
      rw [sq, show g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g by group,
        yamadaW₂_mul_self d h562 h592 hu, mul_one, inv_mul_cancel]
  have hcard : Nat.card E = (2 ^ f) ^ 7 := by
    rw [hEdef, card_map_of_injective (MulAut.conj g⁻¹).injective, h.card_yamadaW₂ d h592]
  obtain ⟨h1, h2⟩ := h.card_le_of_isElemAbelian d hEC hEab
  rw [hcard] at h1
  have h3 : (2 ^ f) ^ 7 ≤ 2 * (2 ^ f) ^ 5 := h1.trans (Nat.mul_le_mul_left 2 h2)
  have h4 : 2 * (2 ^ f) ^ 5 < (2 ^ f) ^ 7 := by
    have h2f : 2 ≤ 2 ^ f := d.two_le_q
    have : 2 < (2 ^ f) ^ 2 := by nlinarith
    calc 2 * (2 ^ f) ^ 5 < (2 ^ f) ^ 2 * (2 ^ f) ^ 5 :=
          Nat.mul_lt_mul_of_pos_right this (by positivity)
      _ = (2 ^ f) ^ 7 := by ring
  omega

include h h562 h592 in
theorem normalizer_yamadaV₂_le :
    normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
        normalizer (yamadaW₂ d t : Set G) ∧
      normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
        normalizer ((d.W.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ∧
      normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
        normalizer ((d.W.map L.subtype : Subgroup G) : Set G) := by
  have htt := h.t_mul_t
  have htN := h.t_mem_normalizer_yamadaW₂ d
  have htW₂ := h.t_not_mem_yamadaW₂ d h592
  have hab : ∀ a ∈ yamadaW₂ d t, ∀ b ∈ yamadaW₂ d t, a * b = b * a := fun a ha b hb =>
    yamadaW₂_mul_comm d h592 ha hb
  have hcard : 2 * Nat.card (yamadaW₂ d t ⊓ centralizer ({t} : Set G) : Subgroup G) <
      Nat.card (yamadaW₂ d t) := by
    rw [h.yamadaW₂_inf_centralizer d h592, card_map_of_injective L.subtype_injective, d.card_W,
      h.card_yamadaW₂ d h592]
    have h2f : 2 ≤ 2 ^ f := d.two_le_q
    have : 2 < (2 ^ f) ^ 2 := by nlinarith
    calc 2 * (2 ^ f) ^ 5 < (2 ^ f) ^ 2 * (2 ^ f) ^ 5 :=
          Nat.mul_lt_mul_of_pos_right this (by positivity)
      _ = (2 ^ f) ^ 7 := by ring
  have h1 := normalizer_sup_zpowers_le_D4 htt htN hab hcard
  have h2 : normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((d.W.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) := by
    have := normalizer_sup_zpowers_le_inf_D4 htt htN htW₂ hab
      (fun a ha => yamadaW₂_mul_self d h562 h592 ha) hcard
    rwa [h.yamadaW₂_inf_centralizer d h592] at this
  have hWeq : yamadaW₂ d t ⊓ (d.W.map L.subtype ⊔ zpowers t) = d.W.map L.subtype := by
    refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left le_sup_left)
    obtain ⟨hx₁, hx₂⟩ := mem_inf.1 hx
    rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 hx₂ with h3 | h3
    · exact h3
    · exfalso
      have := mul_mem ((le_sup_left : d.W.map L.subtype ≤ yamadaW₂ d t) h3) (inv_mem hx₁)
      rw [mul_inv_cancel_right] at this
      exact htW₂ this
  refine ⟨h1, h2, fun g hg => ?_⟩
  rw [← hWeq]
  exact Common.mem_normalizer_inf (h1 hg) (h2 hg)

include h h562 h592 in
theorem crossed_mem_W {g : G}
    (hg : g ∈ normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G)) :
    t * g * t * g⁻¹ ∈ d.W.map L.subtype := by
  obtain ⟨-, h2, h3⟩ := h.normalizer_yamadaV₂_le d h562 h592
  have hgt : g * t * g⁻¹ ∈ d.W.map L.subtype ⊔ zpowers t :=
    (mem_normalizer_iff.1 (h2 hg) t).1 (mem_sup_right (mem_zpowers t))
  rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 hgt with h4 | h4
  · exfalso
    have := (mem_normalizer_iff.1 (inv_mem (h3 hg)) _).1 h4
    rw [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
    exact h.t_not_mem_L (map_subtype_le _ this)
  · rwa [show t * g * t * g⁻¹ = t * (g * t * g⁻¹) by group]

include h h591 h592 in
theorem exists_mul_of_mem_yamadaL₂ {x : G} (hx : x ∈ yamadaL₂ d t) :
    ∃ m ∈ d.M.map L.subtype, ∃ a ∈ yamadaY₂ d t, ∃ τ ∈ zpowers t, x = m * a * τ := by
  have htM₂ : t ∈ normalizer (yamadaM₂ d t : Set G) :=
    Common.mem_normalizer_sup (h.t_mem_normalizer_map d.M) (h.t_mem_normalizer_yamadaY₂ d)
  rw [h591.1, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ ((zpowers_le).2 htM₂),
    Set.mem_mul] at hx
  obtain ⟨m₂, hm₂, τ, hτ, rfl⟩ := hx
  rw [show yamadaM₂ d t = d.M.map L.subtype ⊔ yamadaY₂ d t from rfl,
    coe_mul_of_left_le_normalizer_right _ _ (M_le_normalizer_yamadaY₂ d h592),
    Set.mem_mul] at hm₂
  obtain ⟨m, hm, a, ha, rfl⟩ := hm₂
  exact ⟨m, hm, a, ha, τ, hτ, rfl⟩

include h in
theorem commute_zpowers_of_mem_L {y τ : G} (hy : y ∈ L) (hτ : τ ∈ zpowers t) : y * τ = τ * y := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
  exact (Commute.zpow_right (mem_centralizer_iff.1 h.htL y hy : Commute y t) k).eq

include h h591 h592 in
theorem yamadaL₂_inf_centralizer :
    yamadaL₂ d t ⊓ centralizer (yamadaL₂ d t : Set G) = d.Y.map L.subtype := by
  have hYM : d.Y.map L.subtype ≤ d.M.map L.subtype :=
    map_mono (d.Y_le_W.trans (d.W_le_F.trans d.F_le_M))
  have hML₂ : d.M.map L.subtype ≤ yamadaL₂ d t := le_sup_left.trans (h.tM_le_yamadaL₂ d)
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d (mem_sup_right (mem_zpowers t))
  apply le_antisymm
  · intro z hz
    obtain ⟨hzL₂, hzC⟩ := mem_inf.1 hz
    have hzt : z ∈ centralizer ({t} : Set G) :=
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hzC t htL₂).symm
    have h1 : z ∈ yamadaL₂ d t ⊓ centralizer ({t} : Set G) := mem_inf.2 ⟨hzL₂, hzt⟩
    rw [(h.yamada_5_3_2 d).2.2.2.2.1] at h1
    rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 h1 with h2 | h2
    · obtain ⟨z', hz', rfl⟩ := h2
      refine ⟨z', ?_, rfl⟩
      rw [← d.M_inf_centralizer_M]
      refine mem_inf.2 ⟨hz', mem_centralizer_iff.2 fun y hy => Subtype.ext ?_⟩
      exact mem_centralizer_iff.1 hzC (y : G) (hML₂ ⟨y, hy, rfl⟩)
    · exfalso
      have hz' : z = t * (t * z) := by rw [← mul_assoc, h.t_mul_t, one_mul]
      have hY₂C : yamadaY₂ d t ≤ centralizer ({t} : Set G) := fun a ha => by
        rw [mem_centralizer_singleton_iff]
        have e1 : a * z = z * a := mem_centralizer_iff.1 hzC a (yamadaY₂_le_yamadaL₂ d h591 ha)
        have e2 : (t * z) * a = a * (t * z) := commute_of_mem_M_of_mem_yamadaY₂ d h592 h2 ha
        rw [hz'] at e1
        have : a * t * (t * z) = t * a * (t * z) := by
          calc a * t * (t * z) = a * (t * (t * z)) := by group
            _ = t * (t * z) * a := e1
            _ = t * ((t * z) * a) := by group
            _ = t * (a * (t * z)) := by rw [e2]
            _ = t * a * (t * z) := by group
        exact mul_right_cancel this
      have heq : yamadaY₂ d t = d.Y.map L.subtype := by
        rw [← h592.2.2.2.2]
        exact (inf_eq_left.2 hY₂C).symm
      have h3 := congrArg (fun H : Subgroup G => Nat.card H) heq
      simp only [h592.2.1, card_map_of_injective L.subtype_injective, d.card_Y] at h3
      have h2f : 2 ≤ 2 ^ f := d.two_le_q
      have : (2 ^ f) ^ 2 < (2 ^ f) ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      omega
  · refine le_inf (hYM.trans hML₂) ((Subgroup.le_centralizer_iff).2 fun x hx => ?_)
    obtain ⟨m, hm, a, ha, τ, hτ, rfl⟩ := h.exists_mul_of_mem_yamadaL₂ d h591 h592 hx
    rw [mem_centralizer_iff]
    intro y hy
    have hym : y * m = m * y := by
      obtain ⟨y', hy', rfl⟩ := hy
      obtain ⟨m', hm', rfl⟩ := hm
      exact congrArg Subtype.val (mem_centralizer_iff.1 (d.M_le_centralizer_Y hm') y' hy')
    have hya : y * a = a * y := commute_of_mem_M_of_mem_yamadaY₂ d h592 (hYM hy) ha
    have hyτ : y * τ = τ * y := h.commute_zpowers_of_mem_L (map_subtype_le _ hy) hτ
    calc y * (m * a * τ) = (y * m) * a * τ := by group
      _ = m * (y * a) * τ := by rw [hym]; group
      _ = m * a * (y * τ) := by rw [hya]; group
      _ = m * a * τ * y := by rw [hyτ]; group

include h h591 h592 in
theorem commutatorElement_mem_Y_of_mem_yamadaV₂ {x l : G} (hx : x ∈ yamadaW₂ d t ⊔ zpowers t)
    (hl : l ∈ yamadaL₂ d t) : x * l * x⁻¹ * l⁻¹ ∈ d.Y.map L.subtype := by
  have hWM : d.W.map L.subtype ≤ d.M.map L.subtype := map_mono (d.W_le_F.trans d.F_le_M)
  have hML₂ : d.M.map L.subtype ≤ yamadaL₂ d t := le_sup_left.trans (h.tM_le_yamadaL₂ d)
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d (mem_sup_right (mem_zpowers t))
  have hY₂L₂ := yamadaY₂_le_yamadaL₂ d h591
  have hset := (h.yamada_5_3_2 d).2.2.2.2.2.1
  have hcomm_t : ∀ l ∈ yamadaL₂ d t, t * l * t⁻¹ * l⁻¹ ∈ d.Y.map L.subtype := by
    intro l hl
    have hmem : l * t * l⁻¹ ∈ {x | ∃ c ∈ yamadaL₂ d t, c * t * c⁻¹ = x} := ⟨l, hl, rfl⟩
    rw [hset] at hmem
    obtain ⟨y, hy, e⟩ := hmem
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
    rw [show t * l * t⁻¹ * l⁻¹ = t * (l * t⁻¹ * l⁻¹) by group, htinv, ← e, ← mul_assoc,
      h.t_mul_t, one_mul]
    exact hy
  have hW : ∀ l ∈ yamadaL₂ d t, ∀ w ∈ d.W.map L.subtype,
      l * w * l⁻¹ * w⁻¹ ∈ d.Y.map L.subtype := by
    intro l hl w hw
    obtain ⟨m, hm, a, ha, τ, hτ, rfl⟩ := h.exists_mul_of_mem_yamadaL₂ d h591 h592 hl
    have haw : a * w = w * a := (commute_of_mem_M_of_mem_yamadaY₂ d h592 (hWM hw) ha).symm
    have hτw : τ * w = w * τ := (h.commute_zpowers_of_mem_L (map_subtype_le _ hw) hτ).symm
    have e : m * a * τ * w * (m * a * τ)⁻¹ * w⁻¹ = m * w * m⁻¹ * w⁻¹ := by
      calc m * a * τ * w * (m * a * τ)⁻¹ * w⁻¹ = m * a * (τ * w) * τ⁻¹ * a⁻¹ * m⁻¹ * w⁻¹ := by
            group
        _ = m * (a * w) * a⁻¹ * m⁻¹ * w⁻¹ := by rw [hτw]; group
        _ = m * w * m⁻¹ * w⁻¹ := by rw [haw]; group
    rw [e]
    obtain ⟨m', hm', rfl⟩ := hm
    obtain ⟨w', hw', rfl⟩ := hw
    exact mem_map_of_mem L.subtype (d.commutatorElement_mem_Y_of_mem_M hm' hw')
  have hY₂ : ∀ l ∈ yamadaL₂ d t, ∀ b ∈ yamadaY₂ d t, l * b * l⁻¹ * b⁻¹ ∈ d.Y.map L.subtype := by
    intro l hl b hb
    obtain ⟨m, hm, a, ha, τ, hτ, rfl⟩ := h.exists_mul_of_mem_yamadaL₂ d h591 h592 hl
    have htb : τ * b * τ⁻¹ * b⁻¹ ∈ d.Y.map L.subtype := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
      rcases h.zpow_eq_one_or_eq k with hk | hk
      · rw [hk, one_mul, inv_one, mul_one, mul_inv_cancel]
        exact one_mem _
      · rw [hk]
        exact hcomm_t b (hY₂L₂ hb)
    have hb' : τ * b * τ⁻¹ ∈ yamadaY₂ d t := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
      exact (mem_normalizer_iff.1 (zpow_mem (h.t_mem_normalizer_yamadaY₂ d) k) b).1 hb
    have hmb : m * (τ * b * τ⁻¹) = (τ * b * τ⁻¹) * m :=
      commute_of_mem_M_of_mem_yamadaY₂ d h592 hm hb'
    have hab : a * (τ * b * τ⁻¹) = (τ * b * τ⁻¹) * a := yamadaY₂_mul_comm d h592 ha hb'
    have e : m * a * τ * b * (m * a * τ)⁻¹ * b⁻¹ = τ * b * τ⁻¹ * b⁻¹ := by
      calc m * a * τ * b * (m * a * τ)⁻¹ * b⁻¹ = m * (a * (τ * b * τ⁻¹)) * a⁻¹ * m⁻¹ * b⁻¹ := by
            group
        _ = m * (τ * b * τ⁻¹) * m⁻¹ * b⁻¹ := by rw [hab]; group
        _ = τ * b * τ⁻¹ * b⁻¹ := by rw [hmb]; group
    rw [e]
    exact htb
  have hle : yamadaW₂ d t ⊔ zpowers t ≤ Common.centralizerMod
      (normalizer (yamadaL₂ d t : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G))
      (yamadaL₂ d t) (d.Y.map L.subtype)
      (fun _ hg y hy => (mem_normalizer_iff.1 (mem_inf.1 hg).1 y).1 hy)
      (fun _ hg b hb => (mem_normalizer_iff.1 (mem_inf.1 hg).2 b).1 hb) := by
    have hYN : yamadaL₂ d t ≤ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
      intro g hg
      rw [← h.yamadaL₂_inf_centralizer d h591 h592]
      exact Common.mem_normalizer_inf (le_normalizer hg) (mem_normalizer_fintype fun c hc =>
        mem_centralizer_iff.2 fun l hl => by
          have h1 := mem_centralizer_iff.1 hc (g⁻¹ * l * g) (mul_mem (mul_mem (inv_mem hg) hl) hg)
          calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
            _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
            _ = g * c * g⁻¹ * l := by group)
    have hmem : ∀ x ∈ yamadaL₂ d t, (∀ l ∈ yamadaL₂ d t,
        l * x * l⁻¹ * x⁻¹ ∈ d.Y.map L.subtype) → x ∈ Common.centralizerMod
        (normalizer (yamadaL₂ d t : Set G) ⊓
          normalizer ((d.Y.map L.subtype : Subgroup G) : Set G))
        (yamadaL₂ d t) (d.Y.map L.subtype)
        (fun _ hg y hy => (mem_normalizer_iff.1 (mem_inf.1 hg).1 y).1 hy)
        (fun _ hg b hb => (mem_normalizer_iff.1 (mem_inf.1 hg).2 b).1 hb) := fun x hx hc =>
      ⟨mem_inf.2 ⟨le_normalizer hx, hYN hx⟩, fun l hl => by
        have := inv_mem (hc l hl)
        rwa [show (l * x * l⁻¹ * x⁻¹)⁻¹ = x * l * x⁻¹ * l⁻¹ by group] at this⟩
    refine sup_le (sup_le (fun w hw => hmem w (hML₂ (hWM hw)) fun l hl => hW l hl w hw)
      (fun b hb => hmem b (hY₂L₂ hb) fun l hl => hY₂ l hl b hb)) ((zpowers_le).2 ?_)
    exact ⟨mem_inf.2 ⟨le_normalizer htL₂, hYN htL₂⟩, hcomm_t⟩
  exact (Common.mem_centralizerMod.1 (hle hx)).2 l hl

include h h591 h592 in
theorem mem_yamadaV₂_of_forall {x : G} (hx : x ∈ yamadaL₂ d t)
    (hc : ∀ l ∈ yamadaL₂ d t, x * l * x⁻¹ * l⁻¹ ∈ d.Y.map L.subtype) :
    x ∈ yamadaW₂ d t ⊔ zpowers t := by
  have hML₂ : d.M.map L.subtype ≤ yamadaL₂ d t := le_sup_left.trans (h.tM_le_yamadaL₂ d)
  obtain ⟨m, hm, a, ha, τ, hτ, rfl⟩ := h.exists_mul_of_mem_yamadaL₂ d h591 h592 hx
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  have hmW : m₀ ∈ d.W := by
    refine d.mem_W_iff_forall_M.2 ⟨hm₀, fun y hy => ?_⟩
    have h1 := hc (y : G) (hML₂ ⟨y, hy, rfl⟩)
    have hτy : τ * y = y * τ := (h.commute_zpowers_of_mem_L y.2 hτ).symm
    have hay : a * y = y * a := (commute_of_mem_M_of_mem_yamadaY₂ d h592 ⟨y, hy, rfl⟩ ha).symm
    have e : L.subtype m₀ * a * τ * y * (L.subtype m₀ * a * τ)⁻¹ * (y : G)⁻¹ =
        (m₀ : G) * y * (m₀ : G)⁻¹ * (y : G)⁻¹ := by
      calc L.subtype m₀ * a * τ * y * (L.subtype m₀ * a * τ)⁻¹ * (y : G)⁻¹ =
          (m₀ : G) * a * (τ * y) * τ⁻¹ * a⁻¹ * (m₀ : G)⁻¹ * (y : G)⁻¹ := by
            simp only [coe_subtype]; group
        _ = (m₀ : G) * (a * y) * a⁻¹ * (m₀ : G)⁻¹ * (y : G)⁻¹ := by rw [hτy]; group
        _ = (m₀ : G) * y * (m₀ : G)⁻¹ * (y : G)⁻¹ := by rw [hay]; group
    rw [e] at h1
    rw [commutatorElement_def]
    have h2 : ((m₀ * y * m₀⁻¹ * y⁻¹ : L) : G) = (m₀ : G) * y * (m₀ : G)⁻¹ * (y : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← h2] at h1
    exact coe_mem_map_subtype_iff_D4.1 h1
  exact mul_mem (mul_mem (mem_sup_left (mem_sup_left ⟨m₀, hmW, rfl⟩))
    (mem_sup_left (mem_sup_right ha))) (mem_sup_right hτ)

include h h591 h592 in
theorem normalizer_yamadaL₂_le :
    normalizer (yamadaL₂ d t : Set G) ≤
      normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) := by
  intro g hg
  have hWM : d.W.map L.subtype ≤ d.M.map L.subtype := map_mono (d.W_le_F.trans d.F_le_M)
  have hML₂ : d.M.map L.subtype ≤ yamadaL₂ d t := le_sup_left.trans (h.tM_le_yamadaL₂ d)
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d (mem_sup_right (mem_zpowers t))
  have hVL₂ : yamadaW₂ d t ⊔ zpowers t ≤ yamadaL₂ d t :=
    sup_le (sup_le (hWM.trans hML₂) (yamadaY₂_le_yamadaL₂ d h591)) ((zpowers_le).2 htL₂)
  have hgY : g ∈ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
    rw [← h.yamadaL₂_inf_centralizer d h591 h592]
    exact Common.mem_normalizer_inf hg (mem_normalizer_fintype fun c hc =>
      mem_centralizer_iff.2 fun l hl => by
        have hl' : g⁻¹ * l * g ∈ yamadaL₂ d t := by
          have := (mem_normalizer_iff.1 (inv_mem hg) l).1 hl
          rwa [inv_inv] at this
        have h1 := mem_centralizer_iff.1 hc _ hl'
        calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
          _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
          _ = g * c * g⁻¹ * l := by group)
  refine mem_normalizer_fintype fun x hx => ?_
  refine h.mem_yamadaV₂_of_forall d h591 h592 ((mem_normalizer_iff.1 hg x).1 (hVL₂ hx))
    fun l hl => ?_
  have hl' : g⁻¹ * l * g ∈ yamadaL₂ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hg) l).1 hl
    rwa [inv_inv] at this
  have h1 := h.commutatorElement_mem_Y_of_mem_yamadaV₂ d h591 h592 hx hl'
  have := (mem_normalizer_iff.1 hgY _).1 h1
  rwa [show g * (x * (g⁻¹ * l * g) * x⁻¹ * (g⁻¹ * l * g)⁻¹) * g⁻¹ =
    g * x * g⁻¹ * l * (g * x * g⁻¹)⁻¹ * l⁻¹ by group] at this

include h h591 h592 in
theorem normalizer_tY_le_normalizer_yamadaV₂ :
    normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) :=
  (le_normalizer_yamadaL₂ d t).trans (h.normalizer_yamadaL₂_le d h591 h592)

end Main

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4

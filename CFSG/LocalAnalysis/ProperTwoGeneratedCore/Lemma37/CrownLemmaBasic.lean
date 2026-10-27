module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

variable {G : Type*} [Group G]

structure CrownSetting (S W : Subgroup G) (y : G) : Prop where
  le : W ≤ S
  relIndex_eq : W.relIndex S = 2
  sq_eq_one : ∀ w ∈ W, w ^ 2 = 1
  mem : y ∈ S
  not_mem : y ∉ W
  sq_y : y ^ 2 = 1

namespace CrownSetting

variable {S W : Subgroup G} {y : G}

theorem inv_eq_of_mem (h : CrownSetting S W y) {w : G} (hw : w ∈ W) : w⁻¹ = w :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h.sq_eq_one w hw)

theorem inv_y (h : CrownSetting S W y) : y⁻¹ = y :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h.sq_y)

theorem comm (h : CrownSetting S W y) {a b : G} (ha : a ∈ W) (hb : b ∈ W) : a * b = b * a := by
  have hab := h.inv_eq_of_mem (W.mul_mem ha hb)
  rw [mul_inv_rev, h.inv_eq_of_mem ha, h.inv_eq_of_mem hb] at hab
  exact hab.symm

theorem mul_mem_iff (h : CrownSetting S W y) {a b : G} (ha : a ∈ S) (hb : b ∈ S) :
    a * b ∈ W ↔ (a ∈ W ↔ b ∈ W) := by
  have := Subgroup.mul_mem_iff_of_index_two (H := W.subgroupOf S) h.relIndex_eq
    (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] using this

theorem mul_y_mem (h : CrownSetting S W y) {s : G} (hs : s ∈ S) (hsW : s ∉ W) : s * y ∈ W :=
  (h.mul_mem_iff hs h.mem).2 (iff_of_false hsW h.not_mem)

theorem conj_mem (h : CrownSetting S W y) {w : G} (hw : w ∈ W) : y * w * y⁻¹ ∈ W := by
  have hyw : y * w ∉ W := fun hyw => h.not_mem (((h.mul_mem_iff h.mem (h.le hw)).1 hyw).2 hw)
  rw [h.inv_y]
  exact (h.mul_mem_iff (S.mul_mem h.mem (h.le hw)) h.mem).2 (iff_of_false hyw h.not_mem)

theorem commutator_mem_axis_of_mem (h : CrownSetting S W y) {w : G} (hw : w ∈ W) :
    w * y * w⁻¹ * y⁻¹ ∈ W ⊓ Subgroup.centralizer {y} := by
  have hc : w * y * w⁻¹ * y⁻¹ ∈ W := by
    have := W.mul_mem hw (h.conj_mem (W.inv_mem hw))
    simpa only [mul_assoc] using this
  refine Subgroup.mem_inf.2 ⟨hc, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hv : y * w * y ∈ W := by simpa only [h.inv_y] using h.conj_mem hw
  have hcomm := h.comm hv hw
  rw [h.inv_eq_of_mem hw, h.inv_y]
  calc w * y * w * y * y = w * (y * w * y) * y := by group
    _ = y * w * y * w * y := by rw [← hcomm]
    _ = y * (w * y * w * y) := by group

theorem axis_comm (h : CrownSetting S W y) {δ s : G} (hδ : δ ∈ W ⊓ Subgroup.centralizer {y})
    (hs : s ∈ S) : δ * s = s * δ := by
  obtain ⟨hδW, hδy⟩ := Subgroup.mem_inf.1 hδ
  rw [Subgroup.mem_centralizer_singleton_iff] at hδy
  by_cases hsW : s ∈ W
  · exact h.comm hδW hsW
  · have hsy := h.comm hδW (h.mul_y_mem hs hsW)
    calc δ * s = δ * (s * y) * y⁻¹ := by group
      _ = s * y * δ * y⁻¹ := by rw [hsy]
      _ = s * (y * δ) * y⁻¹ := by group
      _ = s * (δ * y) * y⁻¹ := by rw [hδy]
      _ = s * δ := by group

theorem exists_conj_eq_mul (h : CrownSetting S W y) {s : G} (hs : s ∈ S) :
    ∃ c ∈ W ⊓ Subgroup.centralizer {y}, s * y * s⁻¹ = c * y := by
  by_cases hsW : s ∈ W
  · exact ⟨_, h.commutator_mem_axis_of_mem hsW, by group⟩
  · exact ⟨_, h.commutator_mem_axis_of_mem (h.mul_y_mem hs hsW), by group⟩

theorem y_mem (h : CrownSetting S W y) : y ∈ S ⊓ Subgroup.centralizer {y} :=
  Subgroup.mem_inf.2 ⟨h.mem, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem axis_le (h : CrownSetting S W y) :
    W ⊓ Subgroup.centralizer {y} ≤ S ⊓ Subgroup.centralizer {y} :=
  inf_le_inf_right _ h.le

theorem mem_axis_or (h : CrownSetting S W y) {e : G} (he : e ∈ S ⊓ Subgroup.centralizer {y}) :
    e ∈ W ⊓ Subgroup.centralizer {y} ∨ e * y ∈ W ⊓ Subgroup.centralizer {y} := by
  obtain ⟨heS, hey⟩ := Subgroup.mem_inf.1 he
  by_cases heW : e ∈ W
  · exact Or.inl (Subgroup.mem_inf.2 ⟨heW, hey⟩)
  · refine Or.inr (Subgroup.mem_inf.2 ⟨h.mul_y_mem heS heW, ?_⟩)
    exact Subgroup.mul_mem _ hey (Subgroup.mem_centralizer_singleton_iff.2 rfl)

theorem card_le (h : CrownSetting S W y) :
    Nat.card (S ⊓ Subgroup.centralizer {y} : Subgroup G) ≤
      2 * Nat.card (W ⊓ Subgroup.centralizer {y} : Subgroup G) := by
  set E : Subgroup G := S ⊓ Subgroup.centralizer {y} with hE
  have h1 : W ⊓ E = W ⊓ Subgroup.centralizer {y} := by rw [hE, ← inf_assoc, inf_of_le_left h.le]
  have h2 : W.relIndex E ≤ 2 := h.relIndex_eq ▸
    Subgroup.relIndex_le_of_le_right inf_le_left (by rw [h.relIndex_eq]; norm_num)
  have h3 := Subgroup.relIndex_mul_relIndex ⊥ (W ⊓ E) E bot_le inf_le_right
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right,
    h1] at h3
  rw [← h3, mul_comm]
  exact Nat.mul_le_mul_right _ h2

theorem conj_mem_centralizer (h : CrownSetting S W y) {s e : G} (hs : s ∈ S)
    (he : e ∈ S ⊓ Subgroup.centralizer {y}) : s * e * s⁻¹ ∈ S ⊓ Subgroup.centralizer {y} := by
  obtain ⟨heS, hey⟩ := Subgroup.mem_inf.1 he
  rw [Subgroup.mem_centralizer_singleton_iff] at hey
  refine Subgroup.mem_inf.2 ⟨S.mul_mem (S.mul_mem hs heS) (S.inv_mem hs), ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨c, hc, hcs⟩ := h.exists_conj_eq_mul (S.inv_mem hs)
  rw [inv_inv] at hcs
  have hce : c * e = e * c := h.axis_comm hc heS
  have key : e * (s⁻¹ * y * s) = s⁻¹ * y * s * e := by
    rw [hcs]
    calc e * (c * y) = e * c * y := (mul_assoc _ _ _).symm
      _ = c * e * y := by rw [hce]
      _ = c * (e * y) := mul_assoc _ _ _
      _ = c * (y * e) := by rw [hey]
      _ = c * y * e := (mul_assoc _ _ _).symm
  calc s * e * s⁻¹ * y = s * (e * (s⁻¹ * y * s)) * s⁻¹ := by group
    _ = s * (s⁻¹ * y * s * e) * s⁻¹ := by rw [key]
    _ = y * (s * e * s⁻¹) := by group

theorem le_normalizer (h : CrownSetting S W y) :
    S ≤ Subgroup.normalizer ((S ⊓ Subgroup.centralizer {y} : Subgroup G) : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro e
  refine ⟨h.conj_mem_centralizer hs, fun he => ?_⟩
  have := h.conj_mem_centralizer (S.inv_mem hs) he
  rwa [show s⁻¹ * (s * e * s⁻¹) * s⁻¹⁻¹ = e by group] at this

theorem mem_axis_of_commute (h : CrownSetting S W y) {s e : G} (hs : s ∈ S)
    (hsE : s ∉ S ⊓ Subgroup.centralizer {y}) (he : e ∈ S ⊓ Subgroup.centralizer {y})
    (hse : s * e = e * s) : e ∈ W ⊓ Subgroup.centralizer {y} := by
  rcases h.mem_axis_or he with heΔ | heyΔ
  · exact heΔ
  · refine absurd (Subgroup.mem_inf.2 ⟨hs, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩) hsE
    have h1 : Commute s e⁻¹ := (show Commute s e from hse).inv_right
    have h2 : Commute s (e * y) := (show Commute (e * y) s from h.axis_comm heyΔ hs).symm
    have h3 := h1.mul_right h2
    rw [inv_mul_cancel_left] at h3
    exact h3.eq

theorem exists_conj_eq [Finite G] (h : CrownSetting S W y)
    (hW : Nat.card W = Nat.card (W ⊓ Subgroup.centralizer {y} : Subgroup G) ^ 2)
    {ℓ : G} (hℓ : ℓ ∈ W ⊓ Subgroup.centralizer {y}) : ∃ w ∈ W, w * y * w⁻¹ = y * ℓ := by
  set Δ : Subgroup G := W ⊓ Subgroup.centralizer {y} with hΔ
  have hc : ∀ w : W, (w : G) * y * (w : G)⁻¹ * y⁻¹ ∈ W := fun w =>
    (Subgroup.mem_inf.1 (h.commutator_mem_axis_of_mem w.2)).1
  let f : W →* W :=
    { toFun := fun w => ⟨w * y * (w : G)⁻¹ * y⁻¹, hc w⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show (a : G) * b * y * ((a : G) * b)⁻¹ * y⁻¹ =
          (a : G) * y * (a : G)⁻¹ * y⁻¹ * ((b : G) * y * (b : G)⁻¹ * y⁻¹)
        have h1 : (b : G) * y * (b : G)⁻¹ * y⁻¹ * a = a * ((b : G) * y * (b : G)⁻¹ * y⁻¹) :=
          h.axis_comm (h.commutator_mem_axis_of_mem b.2) (h.le a.2)
        calc (a : G) * b * y * ((a : G) * b)⁻¹ * y⁻¹ =
            a * ((b : G) * y * (b : G)⁻¹ * y⁻¹) * (y * (a : G)⁻¹ * y⁻¹) := by group
          _ = (b : G) * y * (b : G)⁻¹ * y⁻¹ * a * (y * (a : G)⁻¹ * y⁻¹) := by rw [h1]
          _ = (b : G) * y * (b : G)⁻¹ * y⁻¹ * ((a : G) * y * (a : G)⁻¹ * y⁻¹) := by group
          _ = (a : G) * y * (a : G)⁻¹ * y⁻¹ * ((b : G) * y * (b : G)⁻¹ * y⁻¹) :=
            h.comm (hc b) (hc a)) }
  have hker : f.ker = Δ.subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hΔ, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hw
      have hw' : (w : G) * y * (w : G)⁻¹ * y⁻¹ = 1 := congrArg Subtype.val hw
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hw'
      exact ⟨w.2, hw'⟩
    · rintro ⟨-, hwy⟩
      refine Subtype.ext ?_
      show (w : G) * y * (w : G)⁻¹ * y⁻¹ = 1
      rw [hwy]
      group
  have hrange : f.range ≤ Δ.subgroupOf W := by
    intro z hz
    obtain ⟨w, rfl⟩ := MonoidHom.mem_range.1 hz
    exact Subgroup.mem_subgroupOf.2 (h.commutator_mem_axis_of_mem w.2)
  have hcardΔ : Nat.card (Δ.subgroupOf W) = Nat.card Δ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcard : Nat.card f.ker * Nat.card f.range = Nat.card W := by
    rw [← Subgroup.index_ker f]
    exact Subgroup.card_mul_index f.ker
  rw [hker, hcardΔ, hW, sq] at hcard
  have hrange_card : Nat.card f.range = Nat.card Δ :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos hcard
  have heq : f.range = Δ.subgroupOf W :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [hcardΔ, hrange_card])
  have hmem : (⟨ℓ, (Subgroup.mem_inf.1 hℓ).1⟩ : W) ∈ f.range := by
    rw [heq]
    exact Subgroup.mem_subgroupOf.2 hℓ
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.1 hmem
  refine ⟨w, w.2, ?_⟩
  have hw' : (w : G) * y * (w : G)⁻¹ * y⁻¹ = ℓ := congrArg Subtype.val hw
  have hℓy : ℓ * y = y * ℓ :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hℓ).2
  rw [← hℓy, ← hw']
  group

theorem inv_conj_mem (h : CrownSetting S W y) {n x : G}
    (hnN : n ∈ Subgroup.normalizer ((S ⊓ Subgroup.centralizer {y} : Subgroup G) : Set G))
    (hx : x ∈ W ⊓ Subgroup.centralizer {y}) : n⁻¹ * x * n ∈ S ⊓ Subgroup.centralizer {y} :=
  (Subgroup.mem_normalizer_iff.1 hnN _).2
    (by rw [show n * (n⁻¹ * x * n) * n⁻¹ = x by group]; exact h.axis_le hx)

theorem exists_ne_one_mem_axis (h : CrownSetting S W y)
    (hΔ : 2 < Nat.card (W ⊓ Subgroup.centralizer {y} : Subgroup G)) {n : G}
    (hnN : n ∈ Subgroup.normalizer ((S ⊓ Subgroup.centralizer {y} : Subgroup G) : Set G))
    (hy₁ : n * y * n⁻¹ ∈ W ⊓ Subgroup.centralizer {y}) :
    ∃ ℓ ∈ W ⊓ Subgroup.centralizer {y}, ℓ ≠ 1 ∧ n * ℓ * n⁻¹ ∈ W ⊓ Subgroup.centralizer {y} := by
  set Δ : Subgroup G := W ⊓ Subgroup.centralizer {y}
  obtain ⟨δ, hδΔ, hδ1, hδy⟩ : ∃ δ ∈ Δ, δ ≠ 1 ∧ δ ≠ n * y * n⁻¹ := by
    by_contra hcon
    push Not at hcon
    have hsub : (Δ : Set G) ⊆ {1, n * y * n⁻¹} := fun x hx => by
      by_cases h1 : x = 1
      · exact Or.inl h1
      · exact Or.inr (hcon x hx h1)
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at h2
    have h3 := Set.ncard_insert_le (1 : G) {n * y * n⁻¹}
    rw [Set.ncard_singleton] at h3
    omega
  rcases h.mem_axis_or (h.inv_conj_mem hnN hδΔ) with hp | hp
  · refine ⟨_, hp, fun h1 => hδ1 ?_, by rwa [show n * (n⁻¹ * δ * n) * n⁻¹ = δ by group]⟩
    rw [show δ = n * (n⁻¹ * δ * n) * n⁻¹ by group, h1]
    group
  · refine ⟨_, hp, fun h1 => hδy ?_, ?_⟩
    · rw [show δ = n * (n⁻¹ * δ * n * y) * y⁻¹ * n⁻¹ by group, h1, h.inv_y]
      group
    · rw [show n * (n⁻¹ * δ * n * y) * n⁻¹ = δ * (n * y * n⁻¹) by group]
      exact Δ.mul_mem hδΔ hy₁

theorem conj_mem_axis (h : CrownSetting S W y) {n τ ℓ : G}
    (hnN : n ∈ Subgroup.normalizer ((S ⊓ Subgroup.centralizer {y} : Subgroup G) : Set G))
    (hτW : τ ∈ W) (hτ : τ * y * τ⁻¹ = y * ℓ) (hnℓ : n * ℓ * n⁻¹ ∈ W ⊓ Subgroup.centralizer {y})
    {x : G} (hx : x ∈ W ⊓ Subgroup.centralizer {y}) :
    n * τ * n⁻¹ * x * (n * τ * n⁻¹)⁻¹ ∈ W ⊓ Subgroup.centralizer {y} := by
  have hy2 : y * y = 1 := by rw [← sq]; exact h.sq_y
  rcases h.mem_axis_or (h.inv_conj_mem hnN hx) with hp | hp
  · have hc : n⁻¹ * x * n * τ = τ * (n⁻¹ * x * n) := h.axis_comm hp (h.le hτW)
    rw [show n * τ * n⁻¹ * x * (n * τ * n⁻¹)⁻¹ = n * (τ * (n⁻¹ * x * n)) * τ⁻¹ * n⁻¹ by group,
      ← hc, show n * (n⁻¹ * x * n * τ) * τ⁻¹ * n⁻¹ = x by group]
    exact hx
  · have hc : n⁻¹ * x * n * y * τ = τ * (n⁻¹ * x * n * y) := h.axis_comm hp (h.le hτW)
    rw [show n * τ * n⁻¹ * x * (n * τ * n⁻¹)⁻¹ =
        n * (τ * (n⁻¹ * x * n * y)) * y⁻¹ * τ⁻¹ * n⁻¹ by group, ← hc, h.inv_y,
      show n * (n⁻¹ * x * n * y * τ) * y * τ⁻¹ * n⁻¹ =
        n * (n⁻¹ * x * n * y) * (τ * y * τ⁻¹) * n⁻¹ by group, hτ,
      show n * (n⁻¹ * x * n * y) * (y * ℓ) * n⁻¹ = x * n * (y * y) * ℓ * n⁻¹ by group, hy2,
      show x * n * 1 * ℓ * n⁻¹ = x * (n * ℓ * n⁻¹) by group]
    exact (W ⊓ Subgroup.centralizer {y}).mul_mem hx hnℓ

end CrownSetting

end CFSG.ProperTwoGeneratedCore.Lemma37

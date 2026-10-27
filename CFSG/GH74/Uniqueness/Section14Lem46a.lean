module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.Uniqueness.Section12Aux
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section General

variable {G : Type*} [Group G]

@[expose] def stabCoset (V : Subgroup G) (u : G) : Subgroup G where
  carrier := {g | g ∈ centralizer (V : Set G) ∧ g * u * g⁻¹ * u⁻¹ ∈ V}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have e : a * b * u * (a * b)⁻¹ * u⁻¹ =
        (a * (b * u * b⁻¹ * u⁻¹) * a⁻¹) * (a * u * a⁻¹ * u⁻¹) := by group
    have h1 : a * (b * u * b⁻¹ * u⁻¹) * a⁻¹ = b * u * b⁻¹ * u⁻¹ := by
      rw [← (mem_centralizer_iff.mp ha) _ hb', mul_inv_cancel_right]
    rw [e, h1]
    exact mul_mem hb' ha'
  one_mem' := ⟨one_mem _, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    set c := a * u * a⁻¹ * u⁻¹ with hc
    have hac : Commute a c := ((mem_centralizer_iff.mp ha) c ha').symm
    have e : a⁻¹ * u * a⁻¹⁻¹ * u⁻¹ = a⁻¹ * c⁻¹ * a := by rw [hc]; group
    rw [e, mul_assoc, ← hac.inv_right.eq, ← mul_assoc, inv_mul_cancel, one_mul]
    exact inv_mem ha'

theorem mem_stabCoset_iff {V : Subgroup G} {u g : G} :
    g ∈ stabCoset V u ↔ g ∈ centralizer (V : Set G) ∧ g * u * g⁻¹ * u⁻¹ ∈ V := Iff.rfl

@[expose] def stabCosetHom (V : Subgroup G) (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (u : G) :
    ↥(stabCoset V u) →* ↥V where
  toFun g := ⟨(g : G) * u * (g : G)⁻¹ * u⁻¹, g.2.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := by
    apply Subtype.ext
    have ha := a.2.1
    have ha' := a.2.2
    have hb' := b.2.2
    show (a : G) * b * u * ((a : G) * b)⁻¹ * u⁻¹ =
      ((a : G) * u * (a : G)⁻¹ * u⁻¹) * ((b : G) * u * (b : G)⁻¹ * u⁻¹)
    have e : (a : G) * b * u * ((a : G) * b)⁻¹ * u⁻¹ =
        ((a : G) * ((b : G) * u * (b : G)⁻¹ * u⁻¹) * (a : G)⁻¹) *
          ((a : G) * u * (a : G)⁻¹ * u⁻¹) := by group
    have h1 : (a : G) * ((b : G) * u * (b : G)⁻¹ * u⁻¹) * (a : G)⁻¹ =
        (b : G) * u * (b : G)⁻¹ * u⁻¹ := by
      rw [← (mem_centralizer_iff.mp ha) _ hb', mul_inv_cancel_right]
    rw [e, h1]
    exact hV _ hb' _ ha'

theorem stabCosetHom_apply {V : Subgroup G} {hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a} {u : G}
    (g : ↥(stabCoset V u)) :
    ((stabCosetHom V hV u g : ↥V) : G) = (g : G) * u * (g : G)⁻¹ * u⁻¹ := rfl

theorem stabCosetHom_eq_one_iff {V : Subgroup G} {hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a} {u : G}
    (g : ↥(stabCoset V u)) : stabCosetHom V hV u g = 1 ↔ (g : G) * u = u * g := by
  constructor
  · intro h1
    have := congrArg Subtype.val h1
    rw [stabCosetHom_apply] at this
    have h2 : (g : G) * u * (g : G)⁻¹ = u := by
      have := congrArg (· * u) this
      simpa using this
    calc (g : G) * u = (g : G) * u * (g : G)⁻¹ * g := by group
      _ = u * g := by rw [h2]
  · intro h1
    apply Subtype.ext
    rw [stabCosetHom_apply, h1]
    simp

theorem exists_mem_central_mod [Finite G] {S V W : Subgroup G} (hS : IsPGroup 2 S)
    (hWS : W ≤ S) (hSV : S ≤ centralizer (V : Set G)) (hSW : S ≤ normalizer (W : Set G))
    {w₀ : G} (hw₀ : w₀ ∈ W) (hw₀V : w₀ ∉ V) :
    ∃ w ∈ W, w ∉ V ∧ ∀ s ∈ S, s * w * s⁻¹ * w⁻¹ ∈ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V' : Subgroup ↥S := V.subgroupOf S with hV'
  have hV'n : V'.Normal := by
    refine ⟨fun v hv g => ?_⟩
    rw [hV', mem_subgroupOf] at hv ⊢
    have h1 := (mem_centralizer_iff.mp (hSV g.2)) _ hv
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← h1, mul_inv_cancel_right]
    exact hv
  set W' : Subgroup ↥S := W.subgroupOf S with hW'
  have hW'n : W'.Normal := by
    refine ⟨fun w hw g => ?_⟩
    rw [hW', mem_subgroupOf] at hw ⊢
    exact (mem_normalizer_iff.mp (hSW g.2) w).mp hw
  set π := QuotientGroup.mk' V' with hπ
  set H := W'.map π with hH
  have hHn : H.Normal := hW'n.map π (QuotientGroup.mk'_surjective V')
  have hH1 : H ≠ ⊥ := by
    intro hbot
    have hmem : π ⟨w₀, hWS hw₀⟩ ∈ H := mem_map_of_mem π (mem_subgroupOf.mpr hw₀)
    rw [hbot, mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hV',
      mem_subgroupOf] at hmem
    exact hw₀V hmem
  have hQ : IsPGroup 2 (↥S ⧸ V') := hS.to_quotient V'
  have hnil : Group.IsNilpotent (↥S ⧸ V') := hQ.isNilpotent
  obtain ⟨h, hh1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hH1)
  obtain ⟨hhH, hhC⟩ := mem_inf.mp h.2
  obtain ⟨w, hwW, hwh⟩ := mem_map.mp hhH
  refine ⟨w, mem_subgroupOf.mp hwW, ?_, ?_⟩
  · intro hwV
    apply hh1
    apply Subtype.ext
    rw [← hwh, OneMemClass.coe_one, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hV',
      mem_subgroupOf]
    exact hwV
  · intro s hs
    have h1 := mem_center_iff.mp hhC (π ⟨s, hs⟩)
    rw [← hwh] at h1
    have h2 : π (⟨s, hs⟩ * w * (⟨s, hs⟩ : ↥S)⁻¹ * w⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hV', mem_subgroupOf] at h2
    simpa using h2

theorem commute_of_odd_of_commutator_mem {g w : G} (hg : Odd (orderOf g))
    (hcg : g * (g * w * g⁻¹ * w⁻¹) = (g * w * g⁻¹ * w⁻¹) * g)
    (hc2 : (g * w * g⁻¹ * w⁻¹) * (g * w * g⁻¹ * w⁻¹) = 1) : g * w = w * g := by
  set c := g * w * g⁻¹ * w⁻¹ with hc
  have hgw : g * w * g⁻¹ = c * w := by rw [hc]; group
  have hpow : ∀ k : ℕ, g ^ k * w * (g ^ k)⁻¹ = c ^ k * w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hcomm : ∀ j : ℕ, g * c ^ j = c ^ j * g := fun j => (Commute.pow_right hcg j).eq
      calc g ^ (k + 1) * w * (g ^ (k + 1))⁻¹ = g * (g ^ k * w * (g ^ k)⁻¹) * g⁻¹ := by
            rw [pow_succ']; group
        _ = g * (c ^ k * w) * g⁻¹ := by rw [ih]
        _ = c ^ k * (g * w * g⁻¹) := by rw [← mul_assoc g, hcomm k]; group
        _ = c ^ (k + 1) * w := by rw [hgw, pow_succ]; group
  obtain ⟨m, hm⟩ := hg
  have h1 := hpow (orderOf g)
  rw [pow_orderOf_eq_one, inv_one, one_mul, mul_one, hm, pow_succ, pow_mul,
    show c ^ 2 = 1 by rw [sq]; exact hc2, one_pow, one_mul] at h1
  have h2 : c = 1 := by
    have := congrArg (· * w⁻¹) h1
    simp only [mul_inv_cancel] at this
    rw [mul_assoc, mul_inv_cancel, mul_one] at this
    exact this.symm
  have : g * w * g⁻¹ * w⁻¹ = 1 := h2
  calc g * w = g * w * g⁻¹ * w⁻¹ * w * g := by group
    _ = w * g := by rw [this, one_mul]

theorem mem_normalizer_commutator {T : Subgroup G} {g : G} (hg : g ∈ normalizer (T : Set G)) :
    g ∈ normalizer ((⁅T, T⁆ : Subgroup G) : Set G) := by
  have hT : ∀ h ∈ normalizer (T : Set G), T.map (MulAut.conj h).toMonoidHom = T := by
    intro h hh
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.mp hh y).mp hy
    · intro hx
      refine ⟨h⁻¹ * x * h, ?_, by simp [mul_assoc]⟩
      have := (mem_normalizer_iff.mp (inv_mem hh) x).mp hx
      simpa using this
  have hTT : ∀ h ∈ normalizer (T : Set G),
      (⁅T, T⁆ : Subgroup G).map (MulAut.conj h).toMonoidHom = ⁅T, T⁆ := by
    intro h hh
    rw [map_commutator, hT h hh]
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : g * x * g⁻¹ ∈ (⁅T, T⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom :=
      ⟨x, hx, by simp⟩
    rwa [hTT g hg] at this
  · intro hx
    rw [← hTT g hg] at hx
    obtain ⟨y, hy, hye⟩ := hx
    have : y = x := by
      have := congrArg (fun w => g⁻¹ * w * g) hye
      simpa [mul_assoc] using this
    rwa [← this]

end General

end CFSG.GH74.Uniqueness

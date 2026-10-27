module

public import CFSG.CGT.PushingUpLit.LIT.A4.Setup
public import CFSG.RankThree.PartOne.SolD3.Block

public section

namespace CFSG.CGT.PushingUpLit.A4.L34

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.SolK
  CFSG.RankThree.PartOne.SolD3 CFSG.CGT.PushingUpLit.A4
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_iff_conjSub {k : G} {X : Subgroup G} :
    k ∈ Subgroup.normalizer (X : Set G) ↔ conjSub k X = X := by
  constructor
  · intro hk
    ext z
    rw [mem_conjSub_iff]
    have h1 := Subgroup.mem_normalizer_iff.1 hk (k⁻¹ * z * k)
    have e : k * (k⁻¹ * z * k) * k⁻¹ = z := by group
    rw [e] at h1
    exact h1
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have h2 : k * z * k⁻¹ ∈ conjSub k X := conj_mem_conjSub hz
      rwa [h] at h2
    · intro hz
      have h3 : k * z * k⁻¹ ∈ conjSub k X := by rw [h]; exact hz
      have := mem_conjSub_iff.1 h3
      simpa [mul_assoc] using this

theorem conjSub_mono {g : G} {H K : Subgroup G} (h : H ≤ K) : conjSub g H ≤ conjSub g K :=
  Subgroup.map_mono h

theorem pCoreOf_conjSub_le (g : G) (X : Subgroup G) :
    conjSub g (pCoreOf 2 X) ≤ pCoreOf 2 (conjSub g X) := by
  refine le_pCoreOf_of_normalized (conjSub_mono (pCoreOf_le_self X)) ?_ ?_
  · intro h hh x hx
    rw [mem_conjSub_iff] at hh hx ⊢
    have := pCoreOf_normalized X hh hx
    have e : g⁻¹ * (h * x * h⁻¹) * g = (g⁻¹ * h * g) * (g⁻¹ * x * g) * (g⁻¹ * h * g)⁻¹ := by
      group
    rw [e]
    exact this
  · have : IsPGroup 2 ↥((pCoreOf 2 X).map (MulAut.conj g).toMonoidHom) :=
      (isPGroup_pCoreOf' X).map _
    exact this

theorem pCoreOf_conjSub (g : G) (X : Subgroup G) :
    pCoreOf 2 (conjSub g X) = conjSub g (pCoreOf 2 X) := by
  apply le_antisymm
  · have h := pCoreOf_conjSub_le g⁻¹ (conjSub g X)
    rw [conjSub_conjSub, inv_mul_cancel, conjSub_one] at h
    have h2 := conjSub_mono (g := g) h
    rwa [conjSub_inv_self] at h2
  · exact pCoreOf_conjSub_le g X

theorem conj_mem_pCoreOf {k : G} {X : Subgroup G} (h : conjSub k X = X) {w : G}
    (hw : w ∈ pCoreOf 2 X) : k * w * k⁻¹ ∈ pCoreOf 2 X := by
  have h1 : k * w * k⁻¹ ∈ conjSub k (pCoreOf 2 X) := conj_mem_conjSub hw
  rwa [← pCoreOf_conjSub, h] at h1

theorem conjSub_inv_conjSub (g : G) (H : Subgroup G) : conjSub g⁻¹ (conjSub g H) = H := by
  rw [conjSub_conjSub, inv_mul_cancel, conjSub_one]

theorem conjSub_injective (g : G) : Function.Injective (conjSub g : Subgroup G → Subgroup G) := by
  intro H K h
  have h2 := congrArg (conjSub g⁻¹) h
  rwa [conjSub_conjSub, inv_mul_cancel, conjSub_one, conjSub_conjSub, inv_mul_cancel,
    conjSub_one] at h2

theorem Blk3.conj {X : Subgroup G} {a : G} (h : Blk3 X a) (g : G) :
    Blk3 (conjSub g X) (g * a * g⁻¹) where
  mem := conj_mem_conjSub h.mem
  cube := by rw [conj_pow, h.cube]; group
  dec := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    obtain ⟨y, hy, j, hj⟩ := h.dec _ hx
    refine ⟨g * y * g⁻¹, ?_, j, ?_⟩
    · rw [pCoreOf_conjSub]
      exact conj_mem_conjSub hy
    · rw [conj_pow]
      have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      rw [this, hj]
      group
  comm := by
    intro y hy y' hy'
    rw [pCoreOf_conjSub, mem_conjSub_iff] at hy hy'
    have := h.comm _ hy _ hy'
    calc y * y' = g * ((g⁻¹ * y * g) * (g⁻¹ * y' * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y' * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = y' * y := by group
  sq := by
    intro y hy
    rw [pCoreOf_conjSub, mem_conjSub_iff] at hy
    have := h.sq _ hy
    calc y * y = g * ((g⁻¹ * y * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  card := by
    rw [pCoreOf_conjSub]
    have hc : Nat.card ↥(conjSub g (pCoreOf 2 X)) = Nat.card ↥(pCoreOf 2 X) :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    rw [hc]
    exact h.card
  fix := by
    intro y hy hfix
    rw [pCoreOf_conjSub, mem_conjSub_iff] at hy
    have h1 : a * (g⁻¹ * y * g) * a⁻¹ = g⁻¹ * y * g := by
      have e : a * (g⁻¹ * y * g) * a⁻¹ =
          g⁻¹ * ((g * a * g⁻¹) * y * (g * a * g⁻¹)⁻¹) * g := by group
      rw [e, hfix]
    have h2 := h.fix _ hy h1
    have : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [this, h2]
    group

namespace Blk3

variable {X : Subgroup G} {a : G} (h : Blk3 X a)
include h

theorem inv_eq {w : G} (hw : w ∈ pCoreOf 2 X) : w⁻¹ = w :=
  inv_eq_of_mul_eq_one_right (h.sq w hw)

theorem exists_conj_of_ne_one [Finite G] {w w' : G} (hw : w ∈ pCoreOf 2 X) (hw1 : w ≠ 1)
    (hw' : w' ∈ pCoreOf 2 X) (hw'1 : w' ≠ 1) : ∃ x ∈ X, x * w * x⁻¹ = w' := by
  classical
  have hp1 : a * w * a⁻¹ ∈ pCoreOf 2 X := h.conj_mem hw
  have hp2 : a * (a * w * a⁻¹) * a⁻¹ ∈ pCoreOf 2 X := h.conj_mem hp1
  have hne1 : a * w * a⁻¹ ≠ w := fun e => hw1 (h.fix w hw e)
  have hne1' : a * w * a⁻¹ ≠ 1 := fun e => hw1 (conj_eq_one_iff.1 e)
  have hne2' : a * (a * w * a⁻¹) * a⁻¹ ≠ 1 := fun e => hne1' (conj_eq_one_iff.1 e)
  have hne12 : a * (a * w * a⁻¹) * a⁻¹ ≠ a * w * a⁻¹ := fun e =>
    hne1' (h.fix (a * w * a⁻¹) hp1 e)
  have hne02 : a * (a * w * a⁻¹) * a⁻¹ ≠ w := fun e => hne1 (by
    have h3 := h.conj_cube w
    rw [e] at h3
    exact h3)
  have : Fintype (Wn X) := Fintype.ofFinite _
  have hcard : Fintype.card (Wn X) = 3 := by rw [← Nat.card_eq_fintype_card]; exact card_Wn h
  let e₀ : Wn X := ⟨w, hw, hw1⟩
  let e₁ : Wn X := ⟨a * w * a⁻¹, hp1, hne1'⟩
  let e₂ : Wn X := ⟨a * (a * w * a⁻¹) * a⁻¹, hp2, hne2'⟩
  let e' : Wn X := ⟨w', hw', hw'1⟩
  have d01 : e₀ ≠ e₁ := fun e => hne1 (congrArg Subtype.val e).symm
  have d02 : e₀ ≠ e₂ := fun e => hne02 (congrArg Subtype.val e).symm
  have d12 : e₁ ≠ e₂ := fun e => hne12 (congrArg Subtype.val e).symm
  have key : e' = e₀ ∨ e' = e₁ ∨ e' = e₂ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c0, c1, c2⟩ := hcon
    have hsub : ({e₀, e₁, e₂, e'} : Finset (Wn X)) ⊆ Finset.univ := Finset.subset_univ _
    have hc := Finset.card_le_card hsub
    rw [Finset.card_univ, hcard] at hc
    have h4 : ({e₀, e₁, e₂, e'} : Finset (Wn X)).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
      · simpa using c2.symm
      · simp [d12, c1.symm]
      · simp [d01, d02, c0.symm]
    omega
  rcases key with e | e | e
  · exact ⟨1, one_mem _, by have := congrArg Subtype.val e; simpa [e₀] using this.symm⟩
  · exact ⟨a, h.mem, by have := congrArg Subtype.val e; simpa [e₁] using this.symm⟩
  · refine ⟨a * a, mul_mem h.mem h.mem, ?_⟩
    have := congrArg Subtype.val e
    simp only [e', e₂] at this
    rw [this]
    group

theorem exists_fixed [Finite G] {S : Subgroup G} (hS : IsPGroup 2 S)
    (hSn : ∀ s ∈ S, ∀ w ∈ pCoreOf 2 X, s * w * s⁻¹ ∈ pCoreOf 2 X) {v : G} (hv : v ∈ S) :
    ∃ c ∈ pCoreOf 2 X, c ≠ 1 ∧ v * c * v⁻¹ = c := by
  by_cases hc : ∀ w ∈ pCoreOf 2 X, v * w * v⁻¹ = w
  · obtain ⟨c, hcV, hc1⟩ := h.exists_ne_one
    exact ⟨c, hcV, hc1, hc c hcV⟩
  · obtain ⟨c, hcV, hc1, hfix, -⟩ := exists_fixed_of_not_centralizes h hS hSn hv hc
    exact ⟨c, hcV, hc1, hfix⟩

theorem exists_correction {k : G} (hk : conjSub k X = X)
    (hkV : ∀ w ∈ pCoreOf 2 X, k * w = w * k) :
    ∃ w ∈ pCoreOf 2 X, ∀ x ∈ X, (w * k) * x = x * (w * k) := by
  have hka : k * a * k⁻¹ ∈ X := by
    have := conj_mem_conjSub (g := k) h.mem
    rwa [hk] at this
  obtain ⟨y, hyV, j, hj⟩ := h.dec _ hka
  have hkconj : ∀ u ∈ pCoreOf 2 X, (k * a * k⁻¹) * u * (k * a * k⁻¹)⁻¹ = a * u * a⁻¹ := by
    intro u hu
    have h1 : k⁻¹ * u * k = u := by
      have := hkV u hu
      calc k⁻¹ * u * k = k⁻¹ * (u * k) := by group
        _ = k⁻¹ * (k * u) := by rw [this]
        _ = u := by group
    have h2 : k * (a * u * a⁻¹) * k⁻¹ = a * u * a⁻¹ := by
      have := hkV _ (h.conj_mem hu)
      calc k * (a * u * a⁻¹) * k⁻¹ = (k * (a * u * a⁻¹)) * k⁻¹ := by group
        _ = ((a * u * a⁻¹) * k) * k⁻¹ := by rw [this]
        _ = a * u * a⁻¹ := by group
    calc (k * a * k⁻¹) * u * (k * a * k⁻¹)⁻¹
        = k * (a * (k⁻¹ * u * k) * a⁻¹) * k⁻¹ := by group
      _ = a * u * a⁻¹ := by rw [h1]; exact h2
  have hyconj : ∀ u ∈ pCoreOf 2 X,
      (y * a ^ j) * u * (y * a ^ j)⁻¹ = a ^ j * u * (a ^ j)⁻¹ := by
    intro u hu
    have hu' : a ^ j * u * (a ^ j)⁻¹ ∈ pCoreOf 2 X :=
      pCoreOf_normalized X (pow_mem h.mem j) hu
    have := h.comm _ hyV _ hu'
    calc (y * a ^ j) * u * (y * a ^ j)⁻¹ = y * (a ^ j * u * (a ^ j)⁻¹) * y⁻¹ := by group
      _ = (a ^ j * u * (a ^ j)⁻¹) * y * y⁻¹ := by rw [this]
      _ = a ^ j * u * (a ^ j)⁻¹ := by group
  have hjeq : ∀ u ∈ pCoreOf 2 X, a ^ j * u * (a ^ j)⁻¹ = a * u * a⁻¹ := by
    intro u hu
    rw [← hyconj u hu, ← hj]
    exact hkconj u hu
  have hj1 : a ^ j = a := by
    have hmod : a ^ j = a ^ (j % 3) := pow_eq_pow_mod j h.cube
    obtain ⟨u, huV, hu1⟩ := h.exists_ne_one
    rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h0 | h1 | h2
    · exfalso
      have e := hjeq u huV
      rw [hmod, h0] at e
      simp only [pow_zero, one_mul, inv_one, mul_one] at e
      exact hu1 (h.fix u huV e.symm)
    · rw [hmod, h1, pow_one]
    · exfalso
      have e := hjeq u huV
      rw [hmod, h2] at e
      simp only [pow_two, mul_inv_rev] at e
      have e2 : a * (a * u * a⁻¹) * a⁻¹ = a * u * a⁻¹ := by
        calc a * (a * u * a⁻¹) * a⁻¹ = a * a * u * (a⁻¹ * a⁻¹) := by group
          _ = a * u * a⁻¹ := e
      exact hu1 (conj_eq_one_iff.1 (h.fix _ (h.conj_mem huV) e2))
  rw [hj1] at hj
  have hka' : k * a = y * a * k := by
    calc k * a = (k * a * k⁻¹) * k := by group
      _ = y * a * k := by rw [hj]
  have hwV : a * y * a⁻¹ ∈ pCoreOf 2 X := h.conj_mem hyV
  have hy₂V : a * (a * y * a⁻¹) * a⁻¹ ∈ pCoreOf 2 X := h.conj_mem hwV
  have hnorm := h.norm_eq_one hyV
  have hwy : (a * y * a⁻¹) * y = a * (a * y * a⁻¹) * a⁻¹ := by
    have h1 : y * (a * y * a⁻¹) = (a * y * a⁻¹) * y := h.comm _ hyV _ hwV
    have h2 : (y * (a * y * a⁻¹)) * (a * (a * y * a⁻¹) * a⁻¹) = 1 := hnorm
    have h3 := eq_inv_of_mul_eq_one_left h2
    rw [← h1, h3, Blk3.inv_eq h hy₂V]
  refine ⟨a * y * a⁻¹, hwV, fun x hx => ?_⟩
  obtain ⟨u, huV, j', rfl⟩ := h.dec x hx
  have hcu : Commute ((a * y * a⁻¹) * k) u := by
    show ((a * y * a⁻¹) * k) * u = u * ((a * y * a⁻¹) * k)
    calc ((a * y * a⁻¹) * k) * u = (a * y * a⁻¹) * (k * u) := by group
      _ = (a * y * a⁻¹) * (u * k) := by rw [hkV u huV]
      _ = ((a * y * a⁻¹) * u) * k := by group
      _ = (u * (a * y * a⁻¹)) * k := by rw [h.comm _ hwV _ huV]
      _ = u * ((a * y * a⁻¹) * k) := by group
  have hca : Commute ((a * y * a⁻¹) * k) a := by
    show ((a * y * a⁻¹) * k) * a = a * ((a * y * a⁻¹) * k)
    calc ((a * y * a⁻¹) * k) * a = (a * y * a⁻¹) * (k * a) := by group
      _ = (a * y * a⁻¹) * (y * a * k) := by rw [hka']
      _ = ((a * y * a⁻¹) * y) * a * k := by group
      _ = (a * (a * y * a⁻¹) * a⁻¹) * a * k := by rw [hwy]
      _ = a * ((a * y * a⁻¹) * k) := by group
  exact (hcu.mul_right (hca.pow_right j')).eq

end Blk3

end CFSG.CGT.PushingUpLit.A4.L34

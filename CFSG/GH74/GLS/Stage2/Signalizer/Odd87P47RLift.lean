module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cILift

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup
open scoped commutatorElement

section Join

variable {A : Type} [Group A]

theorem exists_mul_of_mem_sup_of_comm_rl {V U : Subgroup A} (h : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    {g : A} (hg : g ∈ V ⊔ U) : ∃ v ∈ V, ∃ u ∈ U, g = v * u := by
  let P : Subgroup A :=
    { carrier := {x | ∃ v ∈ V, ∃ u ∈ U, x = v * u}
      mul_mem' := by
        rintro _ _ ⟨v, hv, u, hu, rfl⟩ ⟨v', hv', u', hu', rfl⟩
        refine ⟨v * v', V.mul_mem hv hv', u * u', U.mul_mem hu hu', ?_⟩
        calc v * u * (v' * u') = v * (u * v') * u' := by group
          _ = v * (v' * u) * u' := by rw [h u hu v' hv']
          _ = v * v' * (u * u') := by group
      one_mem' := ⟨1, V.one_mem, 1, U.one_mem, (one_mul 1).symm⟩
      inv_mem' := by
        rintro _ ⟨v, hv, u, hu, rfl⟩
        refine ⟨v⁻¹, V.inv_mem hv, u⁻¹, U.inv_mem hu, ?_⟩
        have hc : Commute v u := (h u hu v hv).symm
        rw [mul_inv_rev]
        exact hc.inv_inv.eq.symm }
  have hVP : V ≤ P := fun v hv => ⟨v, hv, 1, U.one_mem, (mul_one v).symm⟩
  have hUP : U ≤ P := fun u hu => ⟨1, V.one_mem, u, hu, (one_mul u).symm⟩
  exact (sup_le hVP hUP) hg

theorem isPGroup_sup_of_comm {p : ℕ} {V U : Subgroup A} (hV : IsPGroup p ↥V) (hU : IsPGroup p ↥U)
    (h : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) : IsPGroup p ↥(V ⊔ U) := by
  intro g
  obtain ⟨v, hv, u, hu, hg⟩ := exists_mul_of_mem_sup_of_comm_rl h g.2
  obtain ⟨a, ha⟩ := hV ⟨v, hv⟩
  obtain ⟨b, hb⟩ := hU ⟨u, hu⟩
  refine ⟨a + b, Subtype.ext ?_⟩
  have hva : v ^ (p ^ a) = 1 := congrArg Subtype.val ha
  have hub : u ^ (p ^ b) = 1 := congrArg Subtype.val hb
  have hc : Commute v u := (h u hu v hv).symm
  have h1 : v ^ (p ^ (a + b)) = 1 := by
    rw [pow_add, pow_mul, hva, one_pow]
  have h2 : u ^ (p ^ (a + b)) = 1 := by
    rw [add_comm, pow_add, pow_mul, hub, one_pow]
  show (g : A) ^ (p ^ (a + b)) = 1
  rw [hg, hc.mul_pow, h1, h2, one_mul]

theorem mem_normalizer_sup_of_comm {V U : Subgroup A} (h : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) {x : A}
    (hxV : x ∈ normalizer (V : Set A)) (hxU : ∀ u ∈ U, x * u = u * x) :
    x ∈ normalizer ((V ⊔ U : Subgroup A) : Set A) := by
  have key : ∀ y : A, y ∈ normalizer (V : Set A) → (∀ u ∈ U, y * u = u * y) →
      ∀ g ∈ V ⊔ U, y * g * y⁻¹ ∈ V ⊔ U := by
    intro y hyV hyU g hg
    obtain ⟨v, hv, u, hu, rfl⟩ := exists_mul_of_mem_sup_of_comm_rl h hg
    have h1 : y * v * y⁻¹ ∈ V := (mem_normalizer_iff.mp hyV v).mp hv
    have h2 : y * u * y⁻¹ = u := by rw [hyU u hu]; group
    have : y * (v * u) * y⁻¹ = (y * v * y⁻¹) * u := by
      calc y * (v * u) * y⁻¹ = (y * v * y⁻¹) * (y * u * y⁻¹) := by group
        _ = (y * v * y⁻¹) * u := by rw [h2]
    rw [this]
    exact (V ⊔ U).mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hu)
  rw [mem_normalizer_iff]
  intro g
  constructor
  · exact key x hxV hxU g
  · intro hg
    have hxV' : x⁻¹ ∈ normalizer (V : Set A) := (normalizer (V : Set A)).inv_mem hxV
    have hxU' : ∀ u ∈ U, x⁻¹ * u = u * x⁻¹ := by
      intro u hu
      calc x⁻¹ * u = x⁻¹ * (u * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * u) * x⁻¹ := by rw [← hxU u hu]
        _ = u * x⁻¹ := by group
    have := key x⁻¹ hxV' hxU' _ hg
    simpa [mul_assoc] using this

end Join

section Lift

variable {M : Type} [Group M] [Finite M] (N : Subgroup M) [N.Normal]

theorem exists_lift_four_cent (hN : Odd (Nat.card N)) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (V U X₁ : Subgroup (M ⧸ N)) (hV : IsPGroup 2 ↥V) (hU : IsPGroup 2 ↥U) (hX : IsPGroup p ↥X₁)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hXV : X₁ ≤ normalizer (V : Set (M ⧸ N)))
    (hXU : ∀ x ∈ X₁, ∀ u ∈ U, x * u = u * x) (hUsq : ∀ g ∈ U, g * g = 1)
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hVX₁ : ⁅V, X₁⁆ = V) :
    ∃ V' U' X' : Subgroup M, IsPGroup 2 ↥V' ∧ IsPGroup 2 ↥U' ∧ IsPGroup p ↥X' ∧
      V'.map (QuotientGroup.mk' N) = V ∧ U'.map (QuotientGroup.mk' N) = U ∧
      X'.map (QuotientGroup.mk' N) = X₁ ∧ V' ⊓ N = ⊥ ∧ U' ⊓ N = ⊥ ∧
      (∀ u ∈ U', ∀ v ∈ V', u * v = v * u) ∧ X' ≤ normalizer (V' : Set M) ∧
      (∀ x ∈ X', ∀ u ∈ U', x * u = u * x) ∧ (∀ g ∈ U', g * g = 1) ∧
      (∀ a ∈ U', ∀ b ∈ U', a * b = b * a) ∧
      ⁅V', X'⁆ = V' ∧ Nat.card ↥U' = Nat.card ↥U := by
  have hW2 : IsPGroup 2 ↥(V ⊔ U) := isPGroup_sup_of_comm hV hU hUV
  have hXW : X₁ ≤ normalizer ((V ⊔ U : Subgroup (M ⧸ N)) : Set (M ⧸ N)) :=
    fun x hx => mem_normalizer_sup_of_comm hUV (hXV hx) (hXU x hx)
  obtain ⟨W', X', hW'2, hX'p, hW'map, hX'map, hX'N, hW'N⟩ :=
    exists_two_p_lift N hN hp (V ⊔ U) X₁ hW2 hX hXW
  set π := QuotientGroup.mk' N with hπ
  have hinj := fun {a b : M} (ha : a ∈ W') (hb : b ∈ W') (hab : π a = π b) =>
    mk_inj_of_inf_eq_bot N hW'N ha hb hab
  have hmemW : ∀ w ∈ W', π w ∈ V ⊔ U := fun w hw => by rw [← hW'map]; exact ⟨w, hw, rfl⟩
  have hmemX : ∀ x ∈ X', π x ∈ X₁ := fun x hx => by rw [← hX'map]; exact ⟨x, hx, rfl⟩
  set V' : Subgroup M := W' ⊓ V.comap π with hV'
  set U' : Subgroup M := W' ⊓ U.comap π with hU'
  have hV'W' : V' ≤ W' := inf_le_left
  have hU'W' : U' ≤ W' := inf_le_left
  have hmemV : ∀ v ∈ V', π v ∈ V := fun v hv => (Subgroup.mem_inf.mp hv).2
  have hmemU : ∀ u ∈ U', π u ∈ U := fun u hu => (Subgroup.mem_inf.mp hu).2
  have hV'map : V'.map π = V := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact hmemV v hv
    · intro y hy
      have hyW : y ∈ W'.map π := by rw [hW'map]; exact Subgroup.mem_sup_left hy
      obtain ⟨w, hw, rfl⟩ := hyW
      exact ⟨w, Subgroup.mem_inf.mpr ⟨hw, hy⟩, rfl⟩
  have hU'map : U'.map π = U := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact hmemU u hu
    · intro y hy
      have hyW : y ∈ W'.map π := by rw [hW'map]; exact Subgroup.mem_sup_right hy
      obtain ⟨w, hw, rfl⟩ := hyW
      exact ⟨w, Subgroup.mem_inf.mpr ⟨hw, hy⟩, rfl⟩
  have hV'N : V' ⊓ N = ⊥ := eq_bot_iff.mpr ((inf_le_inf_right N hV'W').trans hW'N.le)
  have hU'N : U' ⊓ N = ⊥ := eq_bot_iff.mpr ((inf_le_inf_right N hU'W').trans hW'N.le)
  have hUV' : ∀ u ∈ U', ∀ v ∈ V', u * v = v * u := by
    intro u hu v hv
    have h1 : π u * π v = π v * π u := hUV _ (hmemU u hu) _ (hmemV v hv)
    exact comm_of_map_comm N hW'N (hU'W' hu) (Subgroup.le_normalizer (hV'W' hv)) h1
  have hXU' : ∀ x ∈ X', ∀ u ∈ U', x * u = u * x := by
    intro x hx u hu
    have h1 : π u * π x = π x * π u := (hXU _ (hmemX x hx) _ (hmemU u hu)).symm
    exact (comm_of_map_comm N hW'N (hU'W' hu) (hX'N hx) h1).symm
  have hkey : ∀ x ∈ X', ∀ v ∈ V', x * v * x⁻¹ ∈ V' := by
    intro x hx v hv
    have hxW : x * v * x⁻¹ ∈ W' := by
      have := (Subgroup.mem_normalizer_iff.mp (hX'N hx) v).mp (hV'W' hv)
      exact this
    refine Subgroup.mem_inf.mpr ⟨hxW, ?_⟩
    show π (x * v * x⁻¹) ∈ V
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hXV (hmemX x hx)) (π v)).mp (hmemV v hv)
  have hX'V' : X' ≤ normalizer (V' : Set M) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact hkey x hx g
    · intro hg
      have := hkey x⁻¹ (X'.inv_mem hx) _ hg
      simpa [mul_assoc] using this
  have hUsq' : ∀ g ∈ U', g * g = 1 := by
    intro g hg
    have h1 : g * g ∈ U' := U'.mul_mem hg hg
    have h2 : π (g * g) = π 1 := by
      rw [map_mul, map_one]
      exact hUsq _ (hmemU g hg)
    exact mk_inj_of_inf_eq_bot N hU'N h1 U'.one_mem h2
  have hUc' : ∀ a ∈ U', ∀ b ∈ U', a * b = b * a := by
    intro a ha b hb
    have h1 : a * b ∈ U' := U'.mul_mem ha hb
    have h2 : b * a ∈ U' := U'.mul_mem hb ha
    have h3 : π (a * b) = π (b * a) := by
      rw [map_mul, map_mul]
      exact hUc _ (hmemU a ha) _ (hmemU b hb)
    exact mk_inj_of_inf_eq_bot N hU'N h1 h2 h3
  have hcomm'' : ⁅V', X'⁆ = V' := by
    have hle : ⁅V', X'⁆ ≤ V' := (Subgroup.le_normalizer_iff_commutator_le_left).mp hX'V'
    refine le_antisymm hle fun v hv => ?_
    have hmap : (⁅V', X'⁆).map π = ⁅V, X₁⁆ := by
      rw [Subgroup.map_commutator, hV'map, hX'map]
    have : π v ∈ (⁅V', X'⁆).map π := by rw [hmap, hVX₁, ← hV'map]; exact ⟨v, hv, rfl⟩
    obtain ⟨c, hc, hcv⟩ := this
    rw [← mk_inj_of_inf_eq_bot N hV'N (hle hc) hv hcv]
    exact hc
  refine ⟨V', U', X', hW'2.to_le hV'W', hW'2.to_le hU'W', hX'p, hV'map, hU'map, hX'map, hV'N, hU'N,
    hUV', hX'V', hXU', hUsq', hUc', hcomm'', ?_⟩
  rw [← hU'map]
  exact (card_map_of_inf_eq_bot N hU'N).symm

end Lift

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

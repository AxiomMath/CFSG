module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpLift

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup
open scoped commutatorElement

section Lift

variable {M : Type} [Group M] (N : Subgroup M) [N.Normal]

theorem mk_inj_of_inf_eq_bot {V : Subgroup M} (hV : V ⊓ N = ⊥) {a b : M} (ha : a ∈ V) (hb : b ∈ V)
    (hab : QuotientGroup.mk' N a = QuotientGroup.mk' N b) : a = b := by
  have hN1 : a⁻¹ * b ∈ N := by
    have : QuotientGroup.mk' N (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp this
  have h1 : a⁻¹ * b ∈ V ⊓ N := Subgroup.mem_inf.mpr ⟨V.mul_mem (V.inv_mem ha) hb, hN1⟩
  rw [hV, Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.mp h1

theorem eq_of_map_eq {V S₁ S₂ : Subgroup M} (hV : V ⊓ N = ⊥) (h₁ : S₁ ≤ V) (h₂ : S₂ ≤ V)
    (h : S₁.map (QuotientGroup.mk' N) = S₂.map (QuotientGroup.mk' N)) : S₁ = S₂ := by
  apply le_antisymm
  · intro a ha
    have h1 : QuotientGroup.mk' N a ∈ S₂.map (QuotientGroup.mk' N) := by
      rw [← h]; exact ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hba⟩ := h1
    have h2 := mk_inj_of_inf_eq_bot N hV (h₂ hb) (h₁ ha) hba
    rw [← h2]
    exact hb
  · intro a ha
    have h1 : QuotientGroup.mk' N a ∈ S₁.map (QuotientGroup.mk' N) := by
      rw [h]; exact ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hba⟩ := h1
    have h2 := mk_inj_of_inf_eq_bot N hV (h₁ hb) (h₂ ha) hba
    rw [← h2]
    exact hb

theorem comm_of_map_comm {V : Subgroup M} (hV : V ⊓ N = ⊥) {a b : M} (ha : a ∈ V)
    (hb : b ∈ normalizer (V : Set M))
    (h : QuotientGroup.mk' N a * QuotientGroup.mk' N b =
      QuotientGroup.mk' N b * QuotientGroup.mk' N a) :
    a * b = b * a := by
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ V := by
    have hba : b * a⁻¹ * b⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hb a⁻¹).mp (V.inv_mem ha)
    have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [e]
    exact V.mul_mem ha hba
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [h]
    group
  have h3 : a * b * a⁻¹ * b⁻¹ ∈ V ⊓ N := Subgroup.mem_inf.mpr ⟨h1, h2⟩
  rw [hV, Subgroup.mem_bot] at h3
  exact commutatorElement_eq_one_iff_mul_comm.mp h3

theorem card_map_of_inf_eq_bot {V : Subgroup M} (hV : V ⊓ N = ⊥) :
    Nat.card ↥(V.map (QuotientGroup.mk' N)) = Nat.card ↥V := by
  symm
  refine Nat.card_congr (Equiv.ofBijective ((QuotientGroup.mk' N).subgroupMap V)
    ⟨?_, (QuotientGroup.mk' N).subgroupMap_surjective V⟩)
  intro a b hab
  have h1 : QuotientGroup.mk' N (a : M) = QuotientGroup.mk' N (b : M) :=
    congrArg Subtype.val hab
  exact Subtype.ext (mk_inj_of_inf_eq_bot N hV a.2 b.2 h1)

theorem nonempty_equiv_map_of_inf_eq_bot {V : Subgroup M} (hV : V ⊓ N = ⊥) :
    Nonempty (↥V ≃* ↥(V.map (QuotientGroup.mk' N))) :=
  ⟨MulEquiv.ofBijective ((QuotientGroup.mk' N).subgroupMap V)
    ⟨fun a b hab => Subtype.ext
      (mk_inj_of_inf_eq_bot N hV a.2 b.2 (congrArg Subtype.val hab)),
      (QuotientGroup.mk' N).subgroupMap_surjective V⟩⟩

theorem commutator_self_le (V : Subgroup M) : ⁅V, V⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact V.mul_mem (V.mul_mem (V.mul_mem ha hb) (V.inv_mem ha)) (V.inv_mem hb)

theorem map_inf_centralizer_eq {V Y : Subgroup M} (hV : V ⊓ N = ⊥)
    (hY : Y ≤ normalizer (V : Set M)) :
    (V ⊓ centralizer (Y : Set M)).map (QuotientGroup.mk' N) =
      V.map (QuotientGroup.mk' N) ⊓
        centralizer ((Y.map (QuotientGroup.mk' N) : Subgroup (M ⧸ N)) : Set (M ⧸ N)) := by
  ext y
  constructor
  · rintro ⟨w', hw', rfl⟩
    obtain ⟨hw'V, hw'C⟩ := Subgroup.mem_inf.mp hw'
    refine Subgroup.mem_inf.mpr ⟨⟨w', hw'V, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro v ⟨v', hv', rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hw'C v' hv']
  · intro hy
    obtain ⟨hyV, hyC⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨w', hw', rfl⟩ := hyV
    refine ⟨w', Subgroup.mem_inf.mpr ⟨hw', ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v' hv'
    have h1 : QuotientGroup.mk' N w' * QuotientGroup.mk' N v' =
        QuotientGroup.mk' N v' * QuotientGroup.mk' N w' :=
      (Subgroup.mem_centralizer_iff.mp hyC (QuotientGroup.mk' N v') ⟨v', hv', rfl⟩).symm
    exact (comm_of_map_comm N hV hw' (hY hv') h1).symm

theorem orderOf_eq_four_of_map {V : Subgroup M} (hV : V ⊓ N = ⊥) {a : M} (ha : a ∈ V)
    (h4 : orderOf (QuotientGroup.mk' N a) = 4) : orderOf a = 4 := by
  have h1 : 4 ∣ orderOf a := by
    rw [← h4]
    exact orderOf_map_dvd (QuotientGroup.mk' N) a
  have h2 : orderOf a ∣ 4 := by
    apply orderOf_dvd_of_pow_eq_one
    have hmem : a ^ 4 ∈ V ⊓ N := by
      refine Subgroup.mem_inf.mpr ⟨V.pow_mem ha 4, ?_⟩
      have : QuotientGroup.mk' N (a ^ 4) = 1 := by
        rw [map_pow, ← h4]
        exact pow_orderOf_eq_one _
      exact (QuotientGroup.eq_one_iff _).mp this
    rw [hV, Subgroup.mem_bot] at hmem
    exact hmem
  exact Nat.dvd_antisymm h2 h1

theorem relIndex_centralizer_map {V X' : Subgroup M} (hV : V ⊓ N = ⊥)
    (hX : X' ≤ normalizer (V : Set M)) :
    (centralizer ((V.map (QuotientGroup.mk' N) : Subgroup (M ⧸ N)) : Set (M ⧸ N))).relIndex
        (X'.map (QuotientGroup.mk' N)) = (centralizer (V : Set M)).relIndex X' := by
  set π := QuotientGroup.mk' N with hπ
  let ρ : ↥X' →* ↥(X'.map π) := π.subgroupMap X'
  have hρ : Function.Surjective ρ := π.subgroupMap_surjective X'
  have h1 : ((centralizer ((V.map π : Subgroup (M ⧸ N)) : Set (M ⧸ N))).subgroupOf
      (X'.map π)).comap ρ = (centralizer (V : Set M)).subgroupOf X' := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    change π (x : M) ∈ centralizer ((V.map π : Subgroup (M ⧸ N)) : Set (M ⧸ N)) ↔
      (x : M) ∈ centralizer (V : Set M)
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h v hv
      have h2 := h (π v) ⟨v, hv, rfl⟩
      exact comm_of_map_comm N hV hv (hX x.2) h2
    · intro h y hy
      obtain ⟨v, hv, rfl⟩ := hy
      rw [← map_mul, ← map_mul, h v hv]
  unfold Subgroup.relIndex
  rw [← h1]
  exact (Subgroup.index_comap_of_surjective _ hρ).symm

theorem exists_lift_l34 [Finite M] (hN : Odd (Nat.card N)) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (W X U₀ : Subgroup (M ⧸ N)) (hW : IsPGroup 2 ↥W) (hX : IsPGroup p ↥X)
    (hXW : X ≤ normalizer (W : Set (M ⧸ N))) (hcomm : ⁅W, X⁆ = W)
    (hUW : U₀ ≤ W) (hUc : U₀ ≤ centralizer (W : Set (M ⧸ N)))
    (hXU : X ≤ centralizer (U₀ : Set (M ⧸ N))) (hU₀sq : ∀ g ∈ U₀, g * g = 1)
    (hZfix : W ⊓ centralizer (W : Set (M ⧸ N)) = W ⊓ centralizer (X : Set (M ⧸ N)))
    (hZder : W ⊓ centralizer (W : Set (M ⧸ N)) = ⁅W, W⁆) :
    ∃ W' X' U' : Subgroup M, IsPGroup 2 ↥W' ∧ IsPGroup p ↥X' ∧
      W'.map (QuotientGroup.mk' N) = W ∧ X'.map (QuotientGroup.mk' N) = X ∧
      U'.map (QuotientGroup.mk' N) = U₀ ∧ W' ⊓ N = ⊥ ∧ X' ≤ normalizer (W' : Set M) ∧
      ⁅W', X'⁆ = W' ∧ U' ≤ W' ∧ U' ≤ centralizer (W' : Set M) ∧ X' ≤ centralizer (U' : Set M) ∧
      (∀ g ∈ U', g * g = 1) ∧ Nat.card ↥U' = Nat.card ↥U₀ ∧
      W' ⊓ centralizer (W' : Set M) = W' ⊓ centralizer (X' : Set M) ∧
      W' ⊓ centralizer (W' : Set M) = ⁅W', W'⁆ := by
  obtain ⟨W', X', hW'2, hX'p, hW'map, hX'map, hX'N, hW'N⟩ :=
    exists_two_p_lift N hN hp W X hW hX hXW
  set π := QuotientGroup.mk' N with hπ
  have hinj := fun {a b : M} (ha : a ∈ W') (hb : b ∈ W') (hab : π a = π b) =>
    mk_inj_of_inf_eq_bot N hW'N ha hb hab
  have hmemW : ∀ w ∈ W', π w ∈ W := fun w hw => by rw [← hW'map]; exact ⟨w, hw, rfl⟩
  have hmemX : ∀ x ∈ X', π x ∈ X := fun x hx => by rw [← hX'map]; exact ⟨x, hx, rfl⟩
  set U' : Subgroup M := W' ⊓ U₀.comap π with hU'
  have hU'W' : U' ≤ W' := inf_le_left
  have hmemU : ∀ u ∈ U', π u ∈ U₀ := fun u hu => (Subgroup.mem_inf.mp hu).2
  have hU'map : U'.map π = U₀ := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact hmemU u hu
    · intro y hy
      have hyW : y ∈ W'.map π := by rw [hW'map]; exact hUW hy
      obtain ⟨w, hw, rfl⟩ := hyW
      exact ⟨w, Subgroup.mem_inf.mpr ⟨hw, hy⟩, rfl⟩
  have hUcent : U' ≤ centralizer (W' : Set M) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 : π u * π w = π w * π u :=
      (Subgroup.mem_centralizer_iff.mp (hUc (hmemU u hu)) (π w) (hmemW w hw)).symm
    exact (comm_of_map_comm N hW'N (hU'W' hu) (Subgroup.le_normalizer hw) h1).symm
  have hXcent : X' ≤ centralizer (U' : Set M) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 : π u * π x = π x * π u :=
      Subgroup.mem_centralizer_iff.mp (hXU (hmemX x hx)) (π u) (hmemU u hu)
    exact comm_of_map_comm N hW'N (hU'W' hu) (hX'N hx) h1
  have hcomm' : ⁅W', X'⁆ = W' := by
    have hle : ⁅W', X'⁆ ≤ W' := (Subgroup.le_normalizer_iff_commutator_le_left).mp hX'N
    refine le_antisymm hle fun v hv => ?_
    have hmap : (⁅W', X'⁆).map π = W := by
      rw [Subgroup.map_commutator, hW'map, hX'map, hcomm]
    have : π v ∈ (⁅W', X'⁆).map π := by rw [hmap, ← hW'map]; exact ⟨v, hv, rfl⟩
    obtain ⟨c, hc, hcv⟩ := this
    rw [← hinj (hle hc) hv hcv]
    exact hc
  have hsq : ∀ g ∈ U', g * g = 1 := by
    intro g hg
    have h1 : g * g ∈ W' := W'.mul_mem (hU'W' hg) (hU'W' hg)
    have h2 : π (g * g) = π 1 := by
      rw [map_mul, map_one]
      exact hU₀sq _ (hmemU g hg)
    exact hinj h1 W'.one_mem h2
  have hTc : (W' ⊓ centralizer (W' : Set M)).map π = W ⊓ centralizer (W : Set (M ⧸ N)) := by
    rw [map_inf_centralizer_eq N hW'N Subgroup.le_normalizer, hW'map]
  have hTx : (W' ⊓ centralizer (X' : Set M)).map π = W ⊓ centralizer (X : Set (M ⧸ N)) := by
    rw [map_inf_centralizer_eq N hW'N hX'N, hW'map, hX'map]
  refine ⟨W', X', U', hW'2, hX'p, hW'map, hX'map, hU'map, hW'N, hX'N, hcomm', hU'W', hUcent, hXcent,
    hsq, ?_, ?_, ?_⟩
  · rw [← hU'map]
    exact (card_map_of_inf_eq_bot N
      (eq_bot_iff.mpr ((inf_le_inf_right N hU'W').trans hW'N.le))).symm
  · exact eq_of_map_eq N hW'N inf_le_left inf_le_left (by rw [hTc, hTx]; exact hZfix)
  · exact eq_of_map_eq N hW'N inf_le_left (commutator_self_le W')
      (by rw [hTc, Subgroup.map_commutator, hW'map]; exact hZder)

end Lift

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

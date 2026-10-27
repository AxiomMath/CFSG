module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47RAut
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47RCoset
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47RLift

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.GH74.GLS.Stage1.Main
open scoped commutatorElement

section Abs

theorem commutator_mem_centralizer {A : Type} [Group A] {V : Subgroup A} {u x : A}
    (hx : x ∈ normalizer (V : Set A)) (hu : ∀ v ∈ V, u * v = v * u) :
    u * x * u⁻¹ * x⁻¹ ∈ centralizer (V : Set A) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hw : x⁻¹ * v * x ∈ V := by
    have hxi : x⁻¹ ∈ normalizer (V : Set A) := (normalizer (V : Set A)).inv_mem hx
    have := (mem_normalizer_iff.mp hxi v).mp hv
    simpa using this
  have hw2 : u * (x⁻¹ * v * x) = (x⁻¹ * v * x) * u := hu _ hw
  have h2 : u⁻¹ * (x⁻¹ * v * x) = (x⁻¹ * v * x) * u⁻¹ := by
    calc u⁻¹ * (x⁻¹ * v * x) = u⁻¹ * ((x⁻¹ * v * x) * u) * u⁻¹ := by group
      _ = u⁻¹ * (u * (x⁻¹ * v * x)) * u⁻¹ := by rw [hw2]
      _ = (x⁻¹ * v * x) * u⁻¹ := by group
  have h3 : u * v = v * u := hu v hv
  have h4 : x * (x⁻¹ * v * x) = v * x := by group
  calc v * (u * x * u⁻¹ * x⁻¹) = (v * u) * x * u⁻¹ * x⁻¹ := by group
    _ = (u * v) * x * u⁻¹ * x⁻¹ := by rw [h3]
    _ = u * (v * x) * u⁻¹ * x⁻¹ := by group
    _ = u * (x * (x⁻¹ * v * x)) * u⁻¹ * x⁻¹ := by rw [h4]
    _ = u * x * ((x⁻¹ * v * x) * u⁻¹) * x⁻¹ := by group
    _ = u * x * (u⁻¹ * (x⁻¹ * v * x)) * x⁻¹ := by rw [h2]
    _ = u * x * u⁻¹ * x⁻¹ * v := by group

theorem conj_mem_centralizer_of_normalizer {A : Type} [Group A] {V : Subgroup A} {x y : A}
    (hx : x ∈ normalizer (V : Set A)) (hy : y ∈ centralizer (V : Set A)) :
    x * y * x⁻¹ ∈ centralizer (V : Set A) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hw : x⁻¹ * v * x ∈ V := by
    have hxi : x⁻¹ ∈ normalizer (V : Set A) := (normalizer (V : Set A)).inv_mem hx
    have := (mem_normalizer_iff.mp hxi v).mp hv
    simpa using this
  have h1 : (x⁻¹ * v * x) * y = y * (x⁻¹ * v * x) := Subgroup.mem_centralizer_iff.mp hy _ hw
  calc v * (x * y * x⁻¹) = x * ((x⁻¹ * v * x) * y) * x⁻¹ := by group
    _ = x * (y * (x⁻¹ * v * x)) * x⁻¹ := by rw [h1]
    _ = (x * y * x⁻¹) * v := by group

theorem exists_q8_config {G : Type} [Group G] [Finite G] (H : Subgroup G) (N : Subgroup ↥H) [N.Normal]
    (hN : Odd (Nat.card N)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {V X E : Subgroup (↥H ⧸ N)} (e : ↥V ≃* QuaternionGroup 2) (hV2 : IsPGroup 2 ↥V)
    (hXp : IsPGroup p ↥X) (hXV : X ≤ normalizer (V : Set (↥H ⧸ N)))
    (hEV : E ≤ normalizer (V : Set (↥H ⧸ N))) (hEX : E ≤ normalizer (X : Set (↥H ⧸ N)))
    (hcard : Nat.card (actOnKHom V X hXV).range = 3) (hVX : ⁅V, X⁆ = V)
    (hE2 : ∀ g ∈ E, g * g = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE8 : 8 ≤ Nat.card ↥E) :
    ∃ U' V' X' : Subgroup G, IVK.IsFourSubgroup U' ∧ IsPGroup 2 ↥V' ∧
      Nonempty (↥V' ≃* QuaternionGroup 2) ∧ IsPGroup p ↥X' ∧ (∀ u ∈ U', ∀ v ∈ V', u * v = v * u) ∧
      X' ≤ normalizer (V' : Set G) ∧ (∀ x ∈ X', ∀ u ∈ U', x * u = u * x) ∧ ⁅V', X'⁆ = V' := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hKE, hKV, hK4⟩ := exists_four_cent_aut e hXV hEV hEX hcard hE2 hEc hE8
  have hK2 : IsPGroup 2 ↥K := IsPGroup.of_card (n := 2) (by rw [hK4]; norm_num)
  have hKsq : ∀ g ∈ K, g * g = 1 := fun g hg => hE2 g (hKE hg)
  have hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := fun a ha b hb => hEc a (hKE ha) b (hKE hb)
  have hKV' : ∀ u ∈ K, ∀ v ∈ V, u * v = v * u := fun u hu v hv =>
    (Subgroup.mem_centralizer_iff.mp (hKV hu) v hv).symm
  have hKX : K ≤ normalizer (X : Set (↥H ⧸ N)) := fun g hg => hEX (hKE hg)
  set X₀ : Subgroup (↥H ⧸ N) := X ⊓ centralizer (V : Set (↥H ⧸ N)) with hX₀
  have hX₀n : ∀ x ∈ X, ∀ y ∈ X₀, x * y * x⁻¹ ∈ X₀ := by
    intro x hx y hy
    refine Subgroup.mem_inf.mpr ⟨?_, conj_mem_centralizer_of_normalizer (hXV hx)
      (Subgroup.mem_inf.mp hy).2⟩
    have hyX : y ∈ X := (Subgroup.mem_inf.mp hy).1
    exact X.mul_mem (X.mul_mem hx hyX) (X.inv_mem hx)
  have hUtriv : ∀ u ∈ K, ∀ x ∈ X, u * x * u⁻¹ * x⁻¹ ∈ X₀ := by
    intro u hu x hx
    refine Subgroup.mem_inf.mpr ⟨?_, commutator_mem_centralizer (hXV hx) (hKV' u hu)⟩
    have h1 : u * x * u⁻¹ ∈ X := (mem_normalizer_iff.mp (hKX hu) x).mp hx
    exact X.mul_mem h1 (X.inv_mem hx)
  have hcos : ∀ x ∈ X, ∃ y ∈ X ⊓ centralizer (K : Set (↥H ⧸ N)), x⁻¹ * y ∈ X₀ := by
    intro x hx
    obtain ⟨y, hyX, hyX₀, hyc⟩ := exists_mem_coset_centralized hp2 (X := X) (X₀ := X₀) (U := K)
      hXp inf_le_left hX₀n hK2 hKX hUtriv hx
    exact ⟨y, Subgroup.mem_inf.mpr ⟨hyX, Subgroup.mem_centralizer_iff.mpr fun u hu => hyc u hu⟩,
      hyX₀⟩
  set X₁ : Subgroup (↥H ⧸ N) := X ⊓ centralizer (K : Set (↥H ⧸ N)) with hX₁
  have hX₁V : X₁ ≤ normalizer (V : Set (↥H ⧸ N)) := inf_le_left.trans hXV
  have hX₁K : ∀ x ∈ X₁, ∀ u ∈ K, x * u = u * x := fun x hx u hu =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 u hu).symm
  have hX₁comm : ⁅V, X₁⁆ = V := by
    apply le_antisymm ((Subgroup.le_normalizer_iff_commutator_le_left).mp hX₁V)
    calc V = ⁅V, X⁆ := hVX.symm
      _ ≤ ⁅V, X₁⁆ := by
        rw [Subgroup.commutator_le]
        intro v hv x hx
        obtain ⟨y, hyX₁, hyX₀⟩ := hcos x hx
        have hwC : x⁻¹ * y ∈ centralizer (V : Set (↥H ⧸ N)) := (Subgroup.mem_inf.mp hyX₀).2
        have hvw : v * (x⁻¹ * y) = (x⁻¹ * y) * v := Subgroup.mem_centralizer_iff.mp hwC v hv
        have hcx : ⁅v, x⁆ = ⁅v, y⁆ := by
          have hy : y = x * (x⁻¹ * y) := by group
          have hc : Commute v (x⁻¹ * y) := hvw
          have hc' : (x⁻¹ * y) * v⁻¹ = v⁻¹ * (x⁻¹ * y) := (hc.inv_left).eq.symm
          calc ⁅v, x⁆ = v * x * v⁻¹ * x⁻¹ := by simp [commutatorElement_def]
            _ = v * x * ((x⁻¹ * y) * v⁻¹ * (x⁻¹ * y)⁻¹) * x⁻¹ := by
              rw [hc']; group
            _ = ⁅v, y⁆ := by
              simp only [commutatorElement_def]
              conv_rhs => rw [hy]
              group
        rw [hcx]
        exact Subgroup.commutator_mem_commutator hv hyX₁
  obtain ⟨V', U', X', hV'2, hU'2, hX'p, hV'map, hU'map, hX'map, hV'N, hU'N, hUV', hX'V', hXU',
    hU'sq, hU'c, hcomm', hcardU'⟩ := exists_lift_four_cent N hN hp2 V K X₁ hV2 hK2
      (hXp.to_le inf_le_left) hKV' hX₁V hX₁K hKsq hKc hX₁comm
  set f : ↥H →* G := H.subtype with hf
  have hfinj : Function.Injective f := H.subtype_injective
  refine ⟨U'.map f, V'.map f, X'.map f, ⟨?_, ?_⟩, hV'2.map f, ?_, hX'p.map f, ?_, ?_, ?_, ?_⟩
  · refine (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).mpr
      ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      show (a : G) * b = b * a
      rw [← ha, ← hb]
      exact congrArg Subtype.val (hU'c a' ha' b' hb')
    · obtain ⟨x', hx', rfl⟩ := hx
      have h1 : (x' * x' : ↥H) = 1 := hU'sq x' hx'
      have h2 := congrArg f h1
      rw [map_mul, map_one] at h2
      rw [pow_two]
      exact h2
  · rw [Subgroup.card_map_of_injective hfinj, hcardU', hK4]
  · obtain ⟨φ⟩ := nonempty_equiv_map_of_inf_eq_bot N hV'N
    exact ⟨((V'.equivMapOfInjective f hfinj).symm.trans
      (φ.trans ((MulEquiv.subgroupCongr hV'map).trans e))) |>.symm.symm⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    exact congrArg Subtype.val (hUV' u hu v hv)
  · exact (Subgroup.map_mono hX'V').trans (Subgroup.le_normalizer_map _)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨u, hu, rfl⟩
    exact congrArg Subtype.val (hXU' x hx u hu)
  · rw [← Subgroup.map_commutator, hcomm']

end Abs

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

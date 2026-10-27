module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Quotient

open Subgroup in
theorem exists_mem_centralizer_coset {M : Type} [Group M] [Finite M] (N : Subgroup M) [N.Normal]
    (hN : Odd (Nat.card N)) (W' : Subgroup M) (hW' : IsPGroup 2 ↥W') (c : M)
    (hc : ∀ w ∈ W', QuotientGroup.mk' N w * QuotientGroup.mk' N c =
      QuotientGroup.mk' N c * QuotientGroup.mk' N w) :
    ∃ x : M, QuotientGroup.mk' N x = QuotientGroup.mk' N c ∧ x ∈ centralizer (W' : Set M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : Type := {x : M // QuotientGroup.mk' N x = QuotientGroup.mk' N c}
  have hmem : ∀ (w : ↥W') (x : T),
      QuotientGroup.mk' N (w.1 * x.1 * w.1⁻¹) = QuotientGroup.mk' N c := by
    intro w x
    rw [map_mul, map_mul, map_inv, x.2, hc w.1 w.2, mul_assoc, mul_inv_cancel, mul_one]
  let _ : SMul ↥W' T := ⟨fun w x => ⟨w.1 * x.1 * w.1⁻¹, hmem w x⟩⟩
  have hsmul : ∀ (w : ↥W') (x : T), (w • x).1 = w.1 * x.1 * w.1⁻¹ := fun _ _ => rfl
  let _ : MulAction ↥W' T :=
    { one_smul := fun x => Subtype.ext (by rw [hsmul]; simp)
      mul_smul := fun w₁ w₂ x => Subtype.ext (by simp only [hsmul]; simp [mul_assoc]) }
  have hcard : Nat.card T = Nat.card N := by
    refine Nat.card_congr
      { toFun := fun x => ⟨c⁻¹ * x.1, ?_⟩
        invFun := fun n => ⟨c * n.1, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have h : QuotientGroup.mk' N (c⁻¹ * x.1) = 1 := by
        rw [map_mul, map_inv, x.2, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h
    · have h : QuotientGroup.mk' N n.1 = 1 := (QuotientGroup.eq_one_iff n.1).mpr n.2
      show QuotientGroup.mk' N (c * n.1) = QuotientGroup.mk' N c
      rw [map_mul, h, mul_one]
    · intro x
      exact Subtype.ext (by simp)
    · intro n
      exact Subtype.ext (by simp)
  have hnd : ¬ 2 ∣ Nat.card T := by
    rw [hcard]
    exact hN.not_two_dvd_nat
  obtain ⟨x, hx⟩ := hW'.nonempty_fixed_point_of_prime_not_dvd_card T hnd
  refine ⟨x.1, x.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h2 : w * x.1 * w⁻¹ = x.1 := congrArg Subtype.val (hx ⟨w, hw⟩)
  rw [mul_inv_eq_iff_eq_mul] at h2
  exact h2

open Subgroup in
theorem centralizer_map_two_lift {M : Type} [Group M] [Finite M] (N : Subgroup M) [N.Normal]
    (hN : Odd (Nat.card N)) (W' : Subgroup M) (hW' : IsPGroup 2 ↥W') (hWN : W' ⊓ N = ⊥) :
    centralizer ((W'.map (QuotientGroup.mk' N) : Subgroup (M ⧸ N)) : Set (M ⧸ N)) =
      (centralizer (W' : Set M)).map (QuotientGroup.mk' N) := by
  have _ := hWN
  ext y
  constructor
  · intro hy
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨x, hx, hxc⟩ := exists_mem_centralizer_coset N hN W' hW' c fun w hw =>
      Subgroup.mem_centralizer_iff.mp hy _ (Subgroup.mem_map_of_mem _ hw)
    exact Subgroup.mem_map.mpr ⟨x, hxc, hx⟩
  · rintro ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hg
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, hg w hw]

theorem isSylowOf_map_mk_of_odd {M : Type} [Group M] [Finite M] (N : Subgroup M) [N.Normal]
    (hN : Odd (Nat.card N)) {P D : Subgroup M}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P D) :
    CFSG.ABGLocalTools.IsSylowOf 2 (P.map (QuotientGroup.mk' N)) (D.map (QuotientGroup.mk' N)) := by
  have _ := hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := hP
  let f : ↥D →* ↥(D.map (QuotientGroup.mk' N)) :=
    ((QuotientGroup.mk' N).comp D.subtype).codRestrict _ fun x => ⟨x.1, x.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨Q.mapSurjective hf, ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

end Quotient

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

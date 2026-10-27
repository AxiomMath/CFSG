module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Reduce
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup GrSLit.L34Facts

section Odd

variable {X : Type} [Group X] [Finite X]

theorem exists_fixed_lift (β : MulAut X) (hβ : ∀ y, β (β y) = y) {N : Subgroup X}
    (hN : ∀ n ∈ N, β n ∈ N) (hodd : Odd (Nat.card N)) (x : X) (hx : x⁻¹ * β x ∈ N) :
    ∃ y : X, β y = y ∧ x⁻¹ * y ∈ N := by
  classical
  have : Fintype X := Fintype.ofFinite X
  have hmapS : ∀ y : X, x⁻¹ * y ∈ N → x⁻¹ * β y ∈ N := by
    intro y hy
    have h1 : β (x⁻¹ * y) ∈ N := hN _ hy
    rw [map_mul, map_inv] at h1
    have h2 : x⁻¹ * β y = (x⁻¹ * β x) * ((β x)⁻¹ * β y) := by group
    rw [h2]
    exact N.mul_mem hx h1
  let σ : Equiv.Perm {y : X // x⁻¹ * y ∈ N} :=
    { toFun := fun y => ⟨β y.1, hmapS y.1 y.2⟩
      invFun := fun y => ⟨β y.1, hmapS y.1 y.2⟩
      left_inv := fun y => Subtype.ext (hβ y.1)
      right_inv := fun y => Subtype.ext (hβ y.1) }
  have hσ2 : σ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    ext y
    exact hβ y.1
  have hS : Fintype.card {y : X // x⁻¹ * y ∈ N} = Nat.card N := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun y => ⟨x⁻¹ * y.1, y.2⟩
        invFun := fun n => ⟨x * n.1, by simp [n.2]⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp) }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 2) (n := 1) hσ2
  rw [hS] at hmod
  obtain ⟨y, hy⟩ : σ.supportᶜ.Nonempty := by
    rw [← Finset.card_pos]
    by_contra h0
    have h0' : σ.supportᶜ.card = 0 := by omega
    rw [h0'] at hmod
    obtain ⟨k, hk⟩ := hodd
    unfold Nat.ModEq at hmod
    omega
  rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hy
  exact ⟨y.1, congrArg Subtype.val hy, y.2⟩

omit [Finite X] in
@[expose] noncomputable def oddAut (β : MulAut X) : MulAut (X ⧸ pPrimeCore 2 X) :=
  QuotientGroup.congr (pPrimeCore 2 X) (pPrimeCore 2 X) β (pPrimeCore_map_iso 2 β)

omit [Finite X] in
theorem oddAut_mk (β : MulAut X) (x : X) :
    oddAut β (QuotientGroup.mk x) = QuotientGroup.mk (β x) :=
  QuotientGroup.congr_mk _ _ _ _ x

theorem fixedPoints_oddAut (β : MulAut X) (hβ : ∀ y, β (β y) = y) :
    fixedPoints (oddAut β) = (fixedPoints β).map (QuotientGroup.mk' (pPrimeCore 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : x⁻¹ * β x ∈ pPrimeCore 2 X := by
      have h1 : oddAut β (QuotientGroup.mk x) = QuotientGroup.mk x := hq
      rw [oddAut_mk] at h1
      exact QuotientGroup.eq.mp h1.symm
    have hN : ∀ n ∈ pPrimeCore 2 X, β n ∈ pPrimeCore 2 X := fun n hn => by
      have h1 : β n ∈ (pPrimeCore 2 X).map β.toMonoidHom := ⟨n, hn, rfl⟩
      rwa [pPrimeCore_map_iso] at h1
    have hodd : Odd (Nat.card (pPrimeCore 2 X)) :=
      Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
        (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card))
    obtain ⟨y, hy, hxy⟩ := exists_fixed_lift β hβ hN hodd x hx
    exact ⟨y, hy, (QuotientGroup.eq.mpr hxy).symm⟩
  · rintro _ ⟨x, hx, rfl⟩
    show oddAut β (QuotientGroup.mk x) = QuotientGroup.mk x
    rw [oddAut_mk, (mem_fixedPoints.mp hx)]

theorem isSubnormal_map_oddAut (β : MulAut X) (hβ : ∀ y, β (β y) = y) {L : Subgroup X}
    (hL : L ≤ fixedPoints β) (hsub : (L.subgroupOf (fixedPoints β)).IsSubnormal) :
    ((L.map (QuotientGroup.mk' (pPrimeCore 2 X))).subgroupOf
      (fixedPoints (oddAut β))).IsSubnormal := by
  let ψ : ↥(fixedPoints β) →* ↥(fixedPoints (oddAut β)) :=
    ((QuotientGroup.mk' (pPrimeCore 2 X)).domRestrict (fixedPoints β)).codRestrict _ fun x => by
      rw [fixedPoints_oddAut β hβ]
      exact ⟨x, x.2, rfl⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    rw [fixedPoints_oddAut β hβ] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨⟨x, hx⟩, rfl⟩
  have hmap : (L.subgroupOf (fixedPoints β)).map ψ =
      (L.map (QuotientGroup.mk' (pPrimeCore 2 X))).subgroupOf (fixedPoints (oddAut β)) := by
    ext y
    rw [mem_map, mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, hL hx⟩, hx, Subtype.ext hxy⟩
  rw [← hmap]
  exact hsub.map hψ

end Odd

section Center

variable {Y : Type} [Group Y]

theorem isSubnormal_map_quotAut (τ : MulAut Y) {L : Subgroup Y} (hL : L ≤ fixedPoints τ)
    (hsub : (L.subgroupOf (fixedPoints τ)).IsSubnormal) :
    ((L.map (QuotientGroup.mk' (center Y))).subgroupOf
      (fixedPoints (quotAut τ))).IsSubnormal := by
  set ψ := N36.fixHom τ
  have hmap : (L.subgroupOf (fixedPoints τ)).map ψ =
      (L.map (QuotientGroup.mk' (center Y))).subgroupOf (fixedPoints (quotAut τ)) := by
    ext y
    rw [mem_map, mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, hL hx⟩, hx, Subtype.ext hxy⟩
  have hsub' : ((L.subgroupOf (fixedPoints τ)).map ψ.rangeRestrict).IsSubnormal :=
    hsub.map ψ.rangeRestrict_surjective
  have hrange : ψ.range.IsSubnormal := by
    rw [N36.range_fixHom]
    exact (N36.barFix_subgroupOf_normal τ).isSubnormal
  have hle' : (L.subgroupOf (fixedPoints τ)).map ψ ≤ ψ.range := map_le_range ψ _
  have heq : ((L.subgroupOf (fixedPoints τ)).map ψ).subgroupOf ψ.range =
      (L.subgroupOf (fixedPoints τ)).map ψ.rangeRestrict := by
    ext y
    rw [mem_subgroupOf, mem_map, mem_map]
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, Subtype.ext hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [← hmap]
  exact IsSubnormal.trans hle' (heq ▸ hsub') hrange

end Center

end CFSG.ComponentClassification.HarrisLit.L35

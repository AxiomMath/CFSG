module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCSymplecticCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.CriticalDefinition
public import CFSG.GroupTheory.FrattiniQuotient

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup)
open scoped IsMulCommutative commutatorElement

theorem critical_cyclic_center_faithful_symplectic_action {H : Type*} [Group H] [Finite H]
    (hH : IsCharacteristicP 2 H) (hQ : pCore 2 H ≠ ⊥) {D : Subgroup H}
    (hDQ : D ≤ pCore 2 H)
    (hcrit : CFSG.SectionRank.Ccomm.ThompsonCritical (D.subgroupOf (pCore 2 H)))
    [IsCyclic (center D)] :
    center D ≠ ⊥ ∧
    ∃ z : D, z ∈ center D ∧ orderOf z = 2 ∧ (∀ z' ∈ center D, orderOf z' = 2 → z' = z) ∧
    ∃ _ : IsElementaryAbelian 2 (D ⧸ center D),
    ∃ b : LinearMap.BilinForm (ZMod 2) (Additive (D ⧸ center D)),
      (∀ x y : D, ⁅x, y⁆ = z ^ (b (Additive.ofMul (x : D ⧸ center D))
        (Additive.ofMul (y : D ⧸ center D))).val) ∧
      (∀ b' : LinearMap.BilinForm (ZMod 2) (Additive (D ⧸ center D)),
        (∀ x y : D, ⁅x, y⁆ = z ^ (b' (Additive.ofMul (x : D ⧸ center D))
          (Additive.ofMul (y : D ⧸ center D))).val) → b' = b) ∧
      b.IsAlt ∧ b.Nondegenerate ∧
      (∃ w : ℕ, Module.finrank (ZMod 2) (Additive (D ⧸ center D)) = 2 * w ∧
        (∀ w' : ℕ, Module.finrank (ZMod 2) (Additive (D ⧸ center D)) = 2 * w' → w' = w) ∧
        (w = 0 ↔ IsCyclic D) ∧ (w = 0 → pCore 2 H = ⊤) ∧
        (1 ≤ w → commutator D = zpowers z)) ∧
      ∃ ρ : H →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive (D ⧸ center D)),
        (∀ (h : H) (x y : D), (y : H) = h * x * h⁻¹ →
          ((ρ h : LinearMap.GeneralLinearGroup (ZMod 2) (Additive (D ⧸ center D))) :
            Module.End (ZMod 2) (Additive (D ⧸ center D)))
              (Additive.ofMul (x : D ⧸ center D)) = Additive.ofMul (y : D ⧸ center D)) ∧
        ρ.ker = pCore 2 H ∧ (∀ h, ρ h ∈ bilinIsometryGroup b) ∧
        (∃ ι : H ⧸ pCore 2 H →* bilinIsometryGroup b, Function.Injective ι ∧
          ∀ h : H, ((ι (h : H ⧸ pCore 2 H) : bilinIsometryGroup b) :
            LinearMap.GeneralLinearGroup (ZMod 2) (Additive (D ⧸ center D))) = ρ h) ∧
        ∀ K : Subgroup H, Odd (Nat.card K) → Function.Injective (ρ.comp K.subtype) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCore 2 H with hQdef
  have hQp : IsPGroup 2 Q := pCore_isPGroup
  have hDp : IsPGroup 2 D := hQp.to_le hDQ
  obtain ⟨hchar, hfrat, hcomm, hcent⟩ := hcrit
  set C := D.subgroupOf Q with hC
  have hmemC : ∀ {x : H} (hx : x ∈ Q), (⟨x, hx⟩ : Q) ∈ C ↔ x ∈ D := fun hx => mem_subgroupOf
  have hDn : D.Normal := by
    refine ⟨fun d hd h => ?_⟩
    have hmap := characteristic_iff_map_eq.mp hchar (MulAut.conjNormal h)
    have h1 : (MulAut.conjNormal h ⟨d, hDQ hd⟩ : Q) ∈ C := by
      rw [← hmap]
      exact mem_map_of_mem _ ((hmemC (hDQ hd)).mpr hd)
    have h2 := (hmemC (MulAut.conjNormal h ⟨d, hDQ hd⟩).2).mp h1
    rwa [MulAut.conjNormal_apply] at h2
  have hQD : ∀ q ∈ Q, ∀ d d' : D, ⁅q, (d : H)⁆ * d' = d' * ⁅q, (d : H)⁆ := by
    intro q hq d d'
    have h1 : ⁅(⟨q, hq⟩ : Q), (⟨d, hDQ d.2⟩ : Q)⁆ ∈ ⁅(⊤ : Subgroup Q), C⁆ :=
      commutator_mem_commutator (mem_top _) ((hmemC (hDQ d.2)).mpr d.2)
    have h2 := mem_centralizer_iff.mp (mem_inf.mp (hcomm h1)).2 ⟨d', hDQ d'.2⟩
      ((hmemC (hDQ d'.2)).mpr d'.2)
    have h3 := congrArg Subtype.val h2
    have hc : ((⁅(⟨q, hq⟩ : Q), (⟨d, hDQ d.2⟩ : Q)⁆ : Q) : H) = ⁅q, (d : H)⁆ :=
      map_commutatorElement Q.subtype _ _
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc] at h3
    exact h3.symm
  have hCQ : ∀ q ∈ Q, (∀ d : D, q * d = d * q) → q ∈ D := by
    intro q hq hqD
    have h1 : (⟨q, hq⟩ : Q) ∈ centralizer (C : Set Q) := by
      rw [mem_centralizer_iff]
      intro c hc
      apply Subtype.ext
      have hcD := (hmemC c.2).mp hc
      exact (hqD ⟨c, hcD⟩).symm
    rw [hcent] at h1
    exact (hmemC hq).mp (mem_inf.mp h1).1
  have hsqZ : ∀ x : D, x ^ 2 ∈ center D := by
    intro x
    have hCp : IsPGroup 2 C := hQp.to_subgroup C
    obtain ⟨-, -, hpow, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hCp
    let c : C := ⟨⟨x, hDQ x.2⟩, (hmemC (hDQ x.2)).mpr x.2⟩
    have h1 : c ^ 2 ∈ frattini C := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hpow _
    have h2 := (mem_inf.mp (hfrat (mem_map_of_mem C.subtype h1))).2
    rw [mem_center_iff]
    intro y
    have h3 := mem_centralizer_iff.mp h2 ⟨y, hDQ y.2⟩ ((hmemC (hDQ y.2)).mpr y.2)
    apply Subtype.ext
    have h4 := congrArg Subtype.val h3
    simpa [c] using h4
  have hcommZ : ∀ x y : D, ⁅x, y⁆ ∈ center D := by
    intro x y
    rw [mem_center_iff]
    intro d'
    apply Subtype.ext
    have h1 := hQD x (hDQ x.2) y d'
    have hc : ((⁅x, y⁆ : D) : H) = ⁅(x : H), (y : H)⁆ := map_commutatorElement D.subtype _ _
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
    exact h1.symm
  have hEA : IsElementaryAbelian 2 (D ⧸ center D) := by
    refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      rw [h1]
      exact hcommZ _ _
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hsqZ x
  have hD1 : D ≠ ⊥ := by
    intro hbot
    apply hQ
    rw [eq_bot_iff]
    intro q hq
    have h1 := hCQ q hq fun d => by
      have hd : (d : H) = 1 := mem_bot.mp (hbot.le d.2)
      rw [hd, one_mul, mul_one]
    rw [hbot] at h1
    exact h1
  have hDnt : Nontrivial D := by
    obtain ⟨⟨d, hd⟩, hne⟩ := ne_bot_iff_exists_ne_one.mp hD1
    exact ⟨⟨⟨d, hd⟩, 1, fun h => hne (Subtype.ext (congrArg Subtype.val h))⟩⟩
  have hYne : center D ≠ ⊥ := by
    have := hDp.center_nontrivial
    intro hbot
    obtain ⟨⟨y, hy⟩, hne⟩ := exists_ne (1 : center D)
    rw [hbot, mem_bot] at hy
    exact hne (Subtype.ext hy)
  obtain ⟨z, hzZ, hz, huniq⟩ := exists_unique_involution_center hDp
  obtain ⟨hzz, b, hrule, hba, hbn, hker, hiso, hι, hodd⟩ :=
    symplectic_core hH hDQ hQD hCQ hzZ hz
  obtain ⟨w, hw, hwu⟩ := existsUnique_finrank_eq_two_mul hba hbn
  have hw0 : w = 0 ↔ ∀ x : D, x ∈ center D := by
    rw [← finrank_eq_zero_iff_forall_mem_center, hw]
    omega
  refine ⟨hYne, z, hzZ, hz, huniq, hEA, b, hrule,
    fun b' hb' => bilinForm_eq_of_commutator_rule hz hrule hb', hba, hbn,
    ⟨w, hw, fun w' hw' => hwu w' hw', ?_, ?_, ?_⟩,
    centerQuotientConjGL D, ?_, hker, hiso, hι, hodd⟩
  ·
    rw [hw0]
    constructor
    · intro hall
      have hsurj : Function.Surjective (center D).subtype := fun x => ⟨⟨x, hall x⟩, rfl⟩
      exact isCyclic_of_surjective _ hsurj
    · intro hcyc x
      rw [mem_center_iff]
      intro y
      exact (IsCyclic.commGroup.mul_comm y x)
  ·
    intro hw00
    have hall : ∀ v : Additive (D ⧸ center D), v = 0 := by
      have : Module.Finite (ZMod 2) (Additive (D ⧸ center D)) := Module.Finite.of_finite
      have h0 : Module.finrank (ZMod 2) (Additive (D ⧸ center D)) = 0 := by rw [hw, hw00]
      exact (_root_.finrank_zero_iff_forall_zero).mp h0
    rw [← hker, eq_top_iff]
    intro h _
    rw [MonoidHom.mem_ker]
    apply Units.ext
    apply LinearMap.ext
    intro v
    rw [hall v, map_zero, map_zero]
  ·
    intro hw1
    have hnab : ∃ x : D, x ∉ center D := by
      by_contra hcon
      have h0 := hw0.mpr fun x => by
        by_contra hx
        exact hcon ⟨x, hx⟩
      omega
    obtain ⟨x, hx⟩ := hnab
    have hx' : ∃ y : D, y * x ≠ x * y := by
      by_contra hcon
      apply hx
      rw [mem_center_iff]
      intro y
      by_contra hne
      exact hcon ⟨y, hne⟩
    obtain ⟨y, hxy⟩ := hx'
    have hxy' : ⁅y, x⁆ ≠ 1 := fun h => hxy (commutatorElement_eq_one_iff_mul_comm.mp h)
    exact commutator_eq_zpowers_of_exists hzz hxy'
  · intro h x y hy
    rw [centerQuotientConjGL_apply]
    congr 2
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, hy]

end CFSG.LocalAnalysis.GorensteinLyons

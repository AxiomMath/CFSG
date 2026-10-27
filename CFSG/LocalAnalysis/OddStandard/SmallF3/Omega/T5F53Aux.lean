module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cover

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

open scoped Pointwise

abbrev omgGroup {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} (hQ : Q.Nondegenerate) : Type := ↥(omegaGroup hQ)

theorem t5_f53_center_mono {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}
    {P₀ : Subgroup (OGroup Q)} (hP₀le : P₀ ≤ omegaGroup hQ) {z₀ : OGroup Q} (hz₀P₀ : z₀ ∈ P₀)
    (hpiP₀ : piOrth Q ∈ P₀)
    (hcent₀ : ∀ g ∈ P₀, (∀ h ∈ P₀, g * h = h * g) ↔
      (g = 1 ∨ g = z₀ ∨ g = piOrth Q * z₀ ∨ g = piOrth Q)) :
    ∀ y : (omgGroup hQ), y ∈ P₀.subgroupOf (omegaGroup hQ) →
      ((∀ z ∈ P₀.subgroupOf (omegaGroup hQ), y * z = z * y) ↔
        (y = 1 ∨ y = (⟨z₀, hP₀le hz₀P₀⟩ : (omgGroup hQ)) ∨
          y = (⟨piOrth Q, hP₀le hpiP₀⟩ : (omgGroup hQ)) * ⟨z₀, hP₀le hz₀P₀⟩ ∨
          y = ⟨piOrth Q, hP₀le hpiP₀⟩)) := by
  intro y hy
  have hyP : (y : OGroup Q) ∈ P₀ := Subgroup.mem_subgroupOf.mp hy
  have hiff : (∀ z ∈ P₀.subgroupOf (omegaGroup hQ), y * z = z * y) ↔
      ∀ h ∈ P₀, (y : OGroup Q) * h = h * (y : OGroup Q) := by
    constructor
    · intro hc h hh
      have hz : (⟨h, hP₀le hh⟩ : (omgGroup hQ)) ∈ P₀.subgroupOf (omegaGroup hQ) :=
        Subgroup.mem_subgroupOf.mpr hh
      exact congrArg Subtype.val (hc ⟨h, hP₀le hh⟩ hz)
    · intro hc z hz
      apply Subtype.ext
      exact hc (z : OGroup Q) (Subgroup.mem_subgroupOf.mp hz)
  rw [hiff]
  constructor
  · intro h
    rcases (hcent₀ (y : OGroup Q) hyP).mp h with h1 | h1 | h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Or.inl (Subtype.ext h1))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext h1)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext h1)))
  · intro h
    apply (hcent₀ (y : OGroup Q) hyP).mpr
    rcases h with h1 | h1 | h1 | h1
    · exact Or.inl (congrArg Subtype.val h1)
    · exact Or.inr (Or.inl (congrArg Subtype.val h1))
    · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h1)))
    · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h1)))

theorem t5_f53_inj_card {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate} {φ : ↥L →* omegaGroup hQ}
    (h : IsCoverMap L φ) (hL : IsOm6Z2 L) {P : Subgroup G} (hP : IsSylow2Of P L) :
    Function.Injective (φ.comp (Subgroup.inclusion hP.1)) ∧
      Nat.card (φ.comp (Subgroup.inclusion hP.1)).range = 2 ^ 8 := by
  classical
  have hO : OddCentralCover φ := h.oddCentralCover hL
  have hdim : Module.finrank (ZMod 3) V = 6 := h.finrank_eq
  have hsgn : quadSign Q = -1 := h.quadSign_eq
  have hPpg : IsPGroup 2 P := hP.2.1
  let ψ : ↥P →* omegaGroup hQ := φ.comp (Subgroup.inclusion hP.1)
  have hψ_inj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    rw [Subgroup.mem_bot]
    have hpker : Subgroup.inclusion hP.1 p ∈ φ.ker :=
      MonoidHom.mem_ker.mpr
        (show φ (Subgroup.inclusion hP.1 p) = 1 from MonoidHom.mem_ker.mp hp)
    obtain ⟨k, hk⟩ := hPpg.exists_orderOf_dvd_pow p
    have hord : orderOf (Subgroup.inclusion hP.1 p) = orderOf p := by
      rw [← Subgroup.orderOf_coe (Subgroup.inclusion hP.1 p), ← Subgroup.orderOf_coe p]
      rfl
    have hodd : orderOf p ∣ Nat.card φ.ker := hord ▸ Subgroup.orderOf_dvd_natCard φ.ker hpker
    have hcop : Nat.Coprime (2 ^ k) (Nat.card φ.ker) :=
      (Nat.coprime_two_left.mpr hO.odd_card_ker).pow_left k
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hk hodd)
  refine ⟨hψ_inj, ?_⟩
  let ψb : ↥P ≃* ↥ψ.range := MonoidHom.ofInjective hψ_inj
  obtain ⟨Q2, hQ2map⟩ := hP.exists_sylow
  have hcardP : Nat.card P = 2 ^ 8 := by
    have hcardL : Nat.card ↥L = Nat.card (omegaGroup hQ) * Nat.card φ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker]
      congr 1
      exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ h.surjective).toEquiv
    have hker_odd : Nat.factorization (Nat.card φ.ker) 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun hd => hO.odd_card_ker.not_two_dvd_nat hd)
    have homega : Nat.factorization (Nat.card (omegaGroup hQ)) 2 = 8 := by
      rw [natCard_omegaGroup_six_minus hQ hdim hsgn]; decide +kernel
    have hLfact : Nat.factorization (Nat.card ↥L) 2 = 8 := by
      rw [hcardL, Nat.factorization_mul (Nat.card_pos (α := omegaGroup hQ)).ne'
        (Nat.card_pos (α := φ.ker)).ne', Finsupp.add_apply, homega, hker_odd, add_zero]
    have hQ2card : Nat.card (Q2 : Subgroup ↥L) = 2 ^ 8 := by
      rw [Sylow.card_eq_multiplicity Q2, hLfact]
    have hQ2 : Nat.card P = Nat.card (Q2 : Subgroup ↥L) := by
      rw [← hQ2map]; exact Subgroup.card_subtype L (Q2 : Subgroup ↥L)
    rw [hQ2, hQ2card]
  show Nat.card ψ.range = 2 ^ 8
  rw [(Nat.card_congr ψb.toEquiv).symm, hcardP]

theorem t5_f53_conj_center {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate} {φ : ↥L →* omegaGroup hQ}
    (h : IsCoverMap L φ) (hL : IsOm6Z2 L) {P : Subgroup G} (hP : IsSylow2Of P L)
    {P₀ : Subgroup (OGroup Q)} (hP₀le : P₀ ≤ omegaGroup hQ) (hP₀card : Nat.card P₀ = 2 ^ 8)
    {z₀ : OGroup Q} (hz₀P₀ : z₀ ∈ P₀) (hpiP₀ : piOrth Q ∈ P₀)
    (hcent₀ : ∀ g ∈ P₀, (∀ h ∈ P₀, g * h = h * g) ↔
      (g = 1 ∨ g = z₀ ∨ g = piOrth Q * z₀ ∨ g = piOrth Q)) :
    ∃ g : (omgGroup hQ),
      (∀ x : (omgGroup hQ),
        x ∈ (φ.comp (Subgroup.inclusion hP.1)).range ↔
        g⁻¹ * x * g ∈ P₀.subgroupOf (omegaGroup hQ)) ∧
      (∀ x : (omgGroup hQ), x ∈ (φ.comp (Subgroup.inclusion hP.1)).range →
        (∀ y ∈ (φ.comp (Subgroup.inclusion hP.1)).range, x * y = y * x) →
        (x = 1 ∨ x = g * (⟨z₀, hP₀le hz₀P₀⟩ : (omgGroup hQ)) * g⁻¹ ∨
          x = (⟨piOrth Q, hP₀le hpiP₀⟩ : (omgGroup hQ)) *
            (g * (⟨z₀, hP₀le hz₀P₀⟩ : (omgGroup hQ)) * g⁻¹) ∨
          x = ⟨piOrth Q, hP₀le hpiP₀⟩)) := by
  classical
  have hdim : Module.finrank (ZMod 3) V = 6 := h.finrank_eq
  have hsgn : quadSign Q = -1 := h.quadSign_eq
  let ψ : ↥P →* omegaGroup hQ := φ.comp (Subgroup.inclusion hP.1)
  let Pb : Subgroup (omgGroup hQ) := ψ.range
  obtain ⟨hψ_inj, hcardPb⟩ := t5_f53_inj_card h hL hP
  let z₀' : (omgGroup hQ) := ⟨z₀, hP₀le hz₀P₀⟩
  let π' : (omgGroup hQ) := ⟨piOrth Q, hP₀le hpiP₀⟩
  let P₀' : Subgroup (omgGroup hQ) := P₀.subgroupOf (omegaGroup hQ)
  have hcardP₀' : Nat.card P₀' = 2 ^ 8 := by
    have h1 : Nat.card P₀ = Nat.card P₀' := by
      have hh := Subgroup.card_subtype (omegaGroup hQ) P₀'
      rw [Subgroup.map_subgroupOf_eq_of_le hP₀le] at hh
      exact hh
    rw [← h1, hP₀card]
  have hGcard : Nat.card (omgGroup hQ) = 6531840 := natCard_omegaGroup_six_minus hQ hdim hsgn
  have hGfact : Nat.factorization (Nat.card (omgGroup hQ)) 2 = 8 := by rw [hGcard]; decide +kernel
  have hcardsPb : Nat.card Pb = 2 ^ (Nat.card (omgGroup hQ)).factorization 2 := by
    rw [hcardPb, hGfact]
  have hcardsP₀ : Nat.card P₀' = 2 ^ (Nat.card (omgGroup hQ)).factorization 2 := by
    rw [hcardP₀', hGfact]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let PbS : Sylow 2 (omgGroup hQ) := Sylow.ofCard Pb hcardsPb
  let P₀S : Sylow 2 (omgGroup hQ) := Sylow.ofCard P₀' hcardsP₀
  haveI : Finite (Sylow 2 (omgGroup hQ)) := Sylow.finite_of_finiteIndex PbS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M := (omgGroup hQ)) P₀S PbS
  have hgsub : (MulAut.conj g) • P₀' = Pb := by
    have h1 : ((g • P₀S : Sylow 2 (omgGroup hQ)) : Subgroup (omgGroup hQ)) =
        (PbS : Subgroup (omgGroup hQ)) :=
      congrArg (fun S : Sylow 2 (omgGroup hQ) => (S : Subgroup (omgGroup hQ))) hg
    rw [Sylow.coe_subgroup_smul] at h1
    exact h1
  have hmem : ∀ x : (omgGroup hQ), x ∈ Pb ↔ g⁻¹ * x * g ∈ P₀' := by
    intro x
    rw [← hgsub, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [MulAut.smul_def, MulAut.conj_inv_apply]
  let zb' : (omgGroup hQ) := g * z₀' * g⁻¹
  have hπ'_central : ∀ a : (omgGroup hQ), π' * a = a * π' := by
    intro a
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) (a : OGroup Q)).symm
  have hZ₀ := t5_f53_center_mono hP₀le hz₀P₀ hpiP₀ hcent₀
  have hZb_forward : ∀ x : (omgGroup hQ), x ∈ Pb → (∀ y ∈ Pb, x * y = y * x) →
      (x = 1 ∨ x = zb' ∨ x = π' * zb' ∨ x = π') := by
    intro x hx hxc
    have hx₀ : g⁻¹ * x * g ∈ P₀' := (hmem x).mp hx
    have hxc₀ : ∀ z ∈ P₀', (g⁻¹ * x * g) * z = z * (g⁻¹ * x * g) := by
      intro w hw
      have hw' : g * w * g⁻¹ ∈ Pb := (hmem (g * w * g⁻¹)).mpr (by
        rw [show g⁻¹ * (g * w * g⁻¹) * g = w from by group]
        exact hw)
      have h := hxc (g * w * g⁻¹) hw'
      calc (g⁻¹ * x * g) * w = g⁻¹ * (x * (g * w * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * w * g⁻¹) * x) * g := by rw [h]
        _ = w * (g⁻¹ * x * g) := by group
    rcases (hZ₀ (g⁻¹ * x * g) hx₀).mp hxc₀ with h1 | h1 | h1 | h1
    · left
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = g * 1 * g⁻¹ := by rw [h1]
        _ = 1 := by group
    · right; left
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = g * z₀' * g⁻¹ := by rw [h1]
    · right; right; left
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = g * (π' * z₀') * g⁻¹ := by rw [h1]
        _ = π' * (g * z₀' * g⁻¹) := by
              calc g * (π' * z₀') * g⁻¹ = (g * π') * z₀' * g⁻¹ := by group
                _ = (π' * g) * z₀' * g⁻¹ := by rw [← hπ'_central g]
                _ = π' * (g * z₀' * g⁻¹) := by group
    · right; right; right
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = g * π' * g⁻¹ := by rw [h1]
        _ = π' := by
              calc g * π' * g⁻¹ = (g * π') * g⁻¹ := by group
                _ = (π' * g) * g⁻¹ := by rw [← hπ'_central g]
                _ = π' := by group
  refine ⟨g, fun x => hmem x, fun x hx hxc => hZb_forward x hx hxc⟩

end CFSG.OddStandard.SmallF3.Omega

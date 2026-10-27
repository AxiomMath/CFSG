module

public import CFSG.GH74.GLS.IVK.L2.ExistOdd
public import CFSG.GH74.GLS.IVK.L2.ExistCyclic
public import CFSG.GH74.GLS.IVK.L2.SylowAux
public import CFSG.GH74.GLS.IVK.L2.NotationTransport
public import CFSG.GH74.GLS.IVK.L2.GroupAux
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter

section Data

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] (e : K ≃* L2 F)

theorem exists_even_data (hev : Even (Nat.card (fieldAutSub e))) :
    ∃ (g₀ : MulAut K) (a m : ℕ), g₀ ∈ fieldAutSub e ∧
      (∀ φ ∈ fieldAutSub e, ∃ k : ℤ, φ = g₀ ^ k) ∧ 1 ≤ a ∧ Odd m ∧ orderOf g₀ = 2 ^ a * m := by
  have hcyc : IsCyclic ↥(fieldAutSub e) := isCyclic_fieldAutSub e
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := ↥(fieldAutSub e))
  have hord : orderOf γ = Nat.card ↥(fieldAutSub e) := orderOf_eq_card_of_forall_mem_zpowers hγ
  obtain ⟨a, m, hm, hnm⟩ :=
    Nat.exists_eq_two_pow_mul_odd (n := Nat.card ↥(fieldAutSub e)) Nat.card_pos.ne'
  have ha : 1 ≤ a := by
    by_contra h
    have h0 : a = 0 := by omega
    subst h0
    rw [pow_zero, one_mul] at hnm
    rw [hnm] at hev
    exact (Nat.not_even_iff_odd.mpr hm) hev
  refine ⟨(γ : MulAut K), a, m, γ.2, ?_, ha, hm, ?_⟩
  · intro φ hφ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hγ ⟨φ, hφ⟩)
    exact ⟨k, (congrArg Subtype.val hk).symm⟩
  · rw [Subgroup.orderOf_coe γ, hord, hnm]

end Data

section Normalizer

theorem mem_normalizer_centralizer_inf {G : Type*} [Group G] (D : Subgroup G) [hD : D.Normal] (z ψ : G)
    (h : ψ * z = z * ψ) :
    ψ ∈ normalizer ((centralizer ({z} : Set G) ⊓ D : Subgroup G) : Set G) := by
  have key : ∀ c : G, c * z = z * c → ∀ y : G, y ∈ centralizer ({z} : Set G) ⊓ D →
      c * y * c⁻¹ ∈ centralizer ({z} : Set G) ⊓ D := by
    intro c hc y ⟨hy1, hy2⟩
    refine ⟨?_, hD.conj_mem y hy2 c⟩
    have hy : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hy1
    have hc' : c⁻¹ * z = z * c⁻¹ := (Commute.inv_left (show Commute c z from hc)).eq
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc c * y * c⁻¹ * z = c * y * (c⁻¹ * z) := by group
      _ = c * y * (z * c⁻¹) := by rw [hc']
      _ = c * (y * z) * c⁻¹ := by group
      _ = c * (z * y) * c⁻¹ := by rw [hy]
      _ = (c * z) * y * c⁻¹ := by group
      _ = (z * c) * y * c⁻¹ := by rw [hc]
      _ = z * (c * y * c⁻¹) := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key ψ h x
  · intro hx
    have hc' : ψ⁻¹ * z = z * ψ⁻¹ := (Commute.inv_left (show Commute ψ z from h)).eq
    have := key ψ⁻¹ hc' _ hx
    simpa [mul_assoc] using this

end Normalizer

section FourGroup

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] (e : K ≃* L2 F)

noncomputable def centralizerEquivPGL (σ : F ≃+* F) :
    ↥(centralizer ({fieldAutHom e σ} : Set (MulAut K)) ⊓ innDiagSub e) ≃* PGL2 ↥(fixedField σ) :=
  (MulEquiv.subgroupCongr (centralizer_fieldAut_eq_map e σ)).trans
    ((Subgroup.equivMapOfInjective _ (innDiagHom e) (innDiagHom_injective e)).symm.trans
      (MonoidHom.ofInjective (pgl2Incl_injective σ)).symm)

theorem isFourSubgroup_of_isKleinFour {G : Type} [Group G] {V : Subgroup G} (hV : IsKleinFour ↥V) :
    IsFourSubgroup V := by
  have hEA : IsElementaryAbelian 2 ↥V :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [hV.exponent_two] }
  exact ⟨hEA, hV.card_four⟩

theorem exists_fourSubgroup_centralizer (hF : L2Field F) (σ : F ≃+* F) :
    ∃ U : Subgroup (MulAut K), IsFourSubgroup U ∧
      U ≤ centralizer ({fieldAutHom e σ} : Set (MulAut K)) ⊓ innDiagSub e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card ↥(fixedField σ)) := odd_card_fixedField σ hF.1
  have : Finite (PGL2 ↥(fixedField σ)) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 2) ↥(fixedField σ) →* PGL2 ↥(fixedField σ))
      Matrix.ProjGenLinGroup.mk_surjective
  have hdih : HasDihedralSylowTwo (PGL2 ↥(fixedField σ)) :=
    pgl2_odd_hasDihedralSylowTwo_model _ (isOddPrimePower_of_odd_card hodd)
  have hdihC := hasDihedralSylowTwo_of_equiv (centralizerEquivPGL e σ).symm hdih
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(centralizer ({fieldAutHom e σ} : Set (MulAut K)) ⊓ innDiagSub e)) :=
    Sylow.nonempty
  obtain ⟨m, hm, ⟨d⟩⟩ := hdihC S
  obtain ⟨V, hVle, hV⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv _ hm d
  obtain ⟨hcV, hsV⟩ := isFourSubgroup_props (isFourSubgroup_of_isKleinFour hV)
  have hV4 := (isFourSubgroup_of_isKleinFour hV).2
  refine ⟨V.map (centralizer ({fieldAutHom e σ} : Set (MulAut K)) ⊓ innDiagSub e).subtype,
    isFourSubgroup_of ?_ ?_ ?_, Subgroup.map_subtype_le _⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hcV a ha b hb)
  · rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (hsV a ha)
  · rw [Subgroup.card_map_of_injective Subtype.val_injective]
    exact hV4

end FourGroup

section Arith

theorem padicValNat_two_of_odd {x : ℕ} (hx : Odd x) : padicValNat 2 x = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  exact hx.not_two_dvd_nat

end Arith

section TwoParts

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] (e : K ≃* L2 F)

theorem factorization_card_centralizer_even (hF : L2Field F) (σ : F ≃+* F) {m : ℕ} (hm : Odd m)
    (hσ : orderOf σ = 2 * m) :
    (Nat.card ↥(centralizer ({fieldAutHom e σ} : Set (MulAut K)) ⊓ innDiagSub e)).factorization 2 =
      (Nat.card K).factorization 2 := by
  have hq₁odd : Odd (Nat.card ↥(fixedField σ)) := odd_card_fixedField σ hF.1
  have hq₁1 : 1 < Nat.card ↥(fixedField σ) := one_lt_card_fixedField σ
  have hq : Nat.card ↥(fixedField σ) ^ (2 * m) = Nat.card F := hσ ▸ fixedField_card_pow σ
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hq2 : Nat.card F ^ 2 - 1 ≠ 0 := by
    have := hF.2
    have : 1 < Nat.card F ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hq₁2 : Nat.card ↥(fixedField σ) ^ 2 - 1 ≠ 0 := by
    have : 1 < Nat.card ↥(fixedField σ) ^ 2 := Nat.one_lt_pow (by norm_num) hq₁1
    omega
  have h1 := padicValNat_card_even hq₁odd hq₁1 hm
  rw [hq] at h1
  have h2 : 2 * Nat.card K = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← card_innDiagSub e hF, card_innDiagSub_q e hF]
  have h3 := congrArg (padicValNat 2) h2
  rw [padicValNat.mul (by norm_num) hKpos.ne', padicValNat.mul Nat.card_pos.ne' hq2,
    padicValNat_two_of_odd hF.1, zero_add, padicValNat.self (by norm_num : 1 < 2)] at h3
  rw [card_centralizer_fieldAut e σ, Nat.factorization_def _ Nat.prime_two,
    Nat.factorization_def _ Nat.prime_two,
    padicValNat.mul (by omega : Nat.card ↥(fixedField σ) ≠ 0) hq₁2, padicValNat_two_of_odd hq₁odd,
    zero_add]
  omega

omit [Finite K] in
theorem factorization_card_centralizer_odd (hF : L2Field F) (σ : F ≃+* F) (hσ : Odd (orderOf σ)) :
    (Nat.card ↥(centralizer ({fieldAutHom e σ} : Set (MulAut K)) ⊓ innDiagSub e)).factorization 2 =
      (Nat.card ↥(innDiagSub e)).factorization 2 := by
  have hq₁odd : Odd (Nat.card ↥(fixedField σ)) := odd_card_fixedField σ hF.1
  have hq₁1 : 1 < Nat.card ↥(fixedField σ) := one_lt_card_fixedField σ
  have hq : Nat.card ↥(fixedField σ) ^ orderOf σ = Nat.card F := fixedField_card_pow σ
  have h1 := padicValNat_card_odd hq₁odd hq₁1 hσ
  rw [hq] at h1
  rw [card_centralizer_fieldAut e σ, card_innDiagSub_q e hF, Nat.factorization_def _ Nat.prime_two,
    Nat.factorization_def _ Nat.prime_two]
  exact h1.symm

end TwoParts

end CFSG.GH74.GLS.IVK

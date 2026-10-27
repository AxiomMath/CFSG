module

public import CFSG.GH74.GLS.IVK.L2.NotationTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Four
public import CFSG.Dihedral.Glauberman.DicksonMaxTables

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG

section Abstract

variable {G : Type*} [Group G]

theorem klein_normalizer_a4_or_s4 {N U A : Subgroup G} [Finite N]
    (hUN : U ≤ N) (hnorm : ∀ n ∈ N, ∀ u ∈ U, n * u * n⁻¹ ∈ U) (hU4 : Nat.card U = 4)
    (hsq : ∀ x ∈ U, x * x = 1) (hC : ∀ g ∈ N, (∀ u ∈ U, g * u = u * g) → g ∈ U)
    (hAN : A ≤ N) (hA : Nonempty (↥A ≃* alternatingGroup (Fin 4))) :
    Nonempty (↥N ≃* alternatingGroup (Fin 4)) ∨ Nonempty (↥N ≃* Equiv.Perm (Fin 4)) := by
  classical
  obtain ⟨eA⟩ := hA
  let F : Subgroup N := U.subgroupOf N
  have : F.Normal := ⟨fun x hx n => by
    have hx' : (x : G) ∈ U := hx
    show ((n * x * n⁻¹ : N) : G) ∈ U
    simpa using hnorm n n.2 x hx'⟩
  have hFcard : Nat.card F = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv]
    exact hU4
  have hFexp : ∀ x ∈ F, x * x = 1 := fun x hx => Subtype.ext (hsq x hx)
  have hCF : ∀ g : N, (∀ f ∈ F, g * f = f * g) → g ∈ F := fun g hg =>
    hC g g.2 (fun u hu => congrArg Subtype.val (hg ⟨u, hUN hu⟩ hu))
  have hA12 : Nat.card A = 12 := by
    rw [Nat.card_congr eA.toEquiv, CFSG.Glauberman.Dickson.QuatTable.card_alternatingFour]
  have h12 : 12 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le hAN
    rwa [hA12] at this
  have hle := CFSG.QuasithinUnique.Unc25Small.card_le_24_of_klein F hFcard hCF
  have hpos : 0 < Nat.card N := Nat.card_pos
  by_cases h24 : 24 ∣ Nat.card N
  · exact Or.inr (CFSG.QuasithinUnique.Unc25Small.perm_four_of_klein F hFcard hFexp hCF h24)
  · left
    have hN : Nat.card N = 12 := by
      obtain ⟨k, hk⟩ := h12
      omega
    have hAeq : A = N := Subgroup.eq_of_le_of_card_ge hAN (by rw [hN, hA12])
    exact ⟨(MulEquiv.subgroupCongr hAeq).symm.trans eA⟩

theorem exists_conj_le_sylow_inf [Finite G] (T : Sylow 2 G) (I : Subgroup G) [I.Normal]
    {U : Subgroup G} (hUI : U ≤ I) (hU : IsPGroup 2 ↥U) :
    ∃ g ∈ I, ∀ u ∈ U, g⁻¹ * u * g ∈ (T : Subgroup G) ⊓ I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := CFSG.Glauberman.sylow_inf_normal (p := 2) T (N := I)
  have hU' : IsPGroup 2 ↥(U.subgroupOf I) :=
    hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUI).symm
  obtain ⟨Q, hQ⟩ := hU'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq I P Q
  refine ⟨g, g.2, fun u hu => ?_⟩
  have h1 : (⟨u, hUI hu⟩ : I) ∈ (Q : Subgroup I) :=
    hQ (show (⟨u, hUI hu⟩ : I) ∈ U.subgroupOf I from hu)
  rw [← hg] at h1
  have h2 := (mem_sylow_smul P g ⟨u, hUI hu⟩).mp h1
  rw [hP] at h2
  exact h2

theorem conj_mem_normalizer {A V U : Subgroup G} (d : G)
    (hd : V.map (MulAut.conj d).toMonoidHom = U) (hAV : ∀ a ∈ A, ∀ x, x ∈ V ↔ a * x * a⁻¹ ∈ V)
    (a : G) (ha : a ∈ A) : d * a * d⁻¹ ∈ normalizer (U : Set G) := by
  have hU : ∀ y, y ∈ U ↔ d⁻¹ * y * d ∈ V := by
    intro y
    rw [← hd]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have : d⁻¹ * (d * v * d⁻¹) * d = v := by group
      rw [show (MulAut.conj d).toMonoidHom v = d * v * d⁻¹ from rfl, this]
      exact hv
    · intro h
      exact ⟨_, h, by show d * (d⁻¹ * y * d) * d⁻¹ = y; group⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [hU, hU, hAV a ha]
  have : d⁻¹ * (d * a * d⁻¹ * h * (d * a * d⁻¹)⁻¹) * d = a * (d⁻¹ * h * d) * a⁻¹ := by group
  rw [this]

end Abstract

end CFSG.GH74.GLS.IVK

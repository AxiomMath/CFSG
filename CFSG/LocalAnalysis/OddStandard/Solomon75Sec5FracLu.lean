module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ}

omit [Finite X] in
theorem cover_form_of_eq_sup {L E : Subgroup X} (hEL : E ≤ L) (h : L = pPrimeCoreOf 2 L ⊔ E) :
    ∀ c ∈ L, ∃ a ∈ E, ∃ o ∈ oddCoreOf L, c = a * o := by
  intro c hc
  have hc' : c ∈ pPrimeCoreOf 2 L ⊔ E := h.le hc
  obtain ⟨o, ho, a, ha, hoa⟩ := (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing
    (pPrimeCoreOf 2 L) E (fun x hx => le_normalizer_oddCoreOf L (hEL hx)) c).1 hc'
  refine ⟨a, ha, a⁻¹ * o * a, ?_, ?_⟩
  · have hn1 := Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf L (hEL (inv_mem ha))) o
    have := hn1.1 ho
    simpa [mul_assoc] using this
  · rw [← hoa]
    group

theorem IsIntrinsicIn.exists_Lu {H L : Subgroup X} {u : X} (h : IsIntrinsicIn X H L u)
    (hLn : IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n) :
    ∃ Lu : Subgroup X, IsPCompIn 2 (centralizer ({u} : Set X)) Lu ∧
      oTwoPrimeOf (L ⊓ centralizer ({u} : Set X)) ≤ Lu ∧
      IsTwoGenQuasi ↥(oTwoPrimeOf (L ⊓ centralizer ({u} : Set X))) ∧
      (∀ c ∈ L, ∃ a ∈ oTwoPrimeOf (L ⊓ centralizer ({u} : Set X)), ∃ o ∈ oddCoreOf L,
        c = a * o) ∧
      (∀ c ∈ Lu, ∃ a ∈ oTwoPrimeOf (L ⊓ centralizer ({u} : Set X)), ∃ o ∈ oddCoreOf Lu,
        c = a * o) ∧
      IsDoubleCoverOfAlt (↥Lu ⧸ pPrimeCore 2 ↥Lu) n := by
  obtain ⟨hu, huL, ⟨hLH, hLpc⟩, hLeq, Lu, hLuI, hLuEq⟩ := h
  set Cu : Subgroup X := centralizer ({u} : Set X) with hCu
  set E : Subgroup X := oTwoPrimeOf (L ⊓ Cu) with hE
  rw [oPrimeResidualOf_two_eq_oTwoPrimeOf] at hLeq hLuEq
  have hEL : E ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hELu : E ≤ Lu := by
    rw [hLuEq]
    exact le_sup_right
  have hEgen : primeResidual 2 ↥E = ⊤ := primeResidual_oTwoPrimeOf _
  have hLuCu : IsPCompIn 2 Cu Lu := ⟨hLuI.1, hLuI.2.2.1⟩
  have hLq : IsTwoGenQuasi ↥Lu :=
    (isTwoGenQuasi_subgroupOf_iff hLuCu.1).1 (isPComponent_two_iff.1 hLuCu.2).2
  have hcovL : E.subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤ := by
    rw [covers_subgroupOf_iff hEL, sup_comm]
    exact hLeq.symm
  have hcovLu : E.subgroupOf Lu ⊔ pPrimeCore 2 ↥Lu = ⊤ := by
    rw [covers_subgroupOf_iff hELu, sup_comm]
    exact hLuEq.symm
  have hLun : IsDoubleCoverOfAlt (↥Lu ⧸ pPrimeCore 2 ↥Lu) n :=
    (isDoubleCoverOfAlt_quot_iff_of_covers hELu hcovLu n).1
      ((isDoubleCoverOfAlt_quot_iff_of_covers hEL hcovL n).2 hLn)
  exact ⟨Lu, hLuCu, hELu, isTwoGenQuasi_of_covers hELu hcovLu hEgen hLq,
    cover_form_of_eq_sup hEL hLeq, cover_form_of_eq_sup hELu hLuEq, hLun⟩

omit [Finite X] in
theorem mem_oTwoPrimeOf_inf_centralizer {L : Subgroup X} {u : X} (huL : u ∈ L) (hu2 : u * u = 1) :
    u ∈ oTwoPrimeOf (L ⊓ centralizer ({u} : Set X)) :=
  mem_oTwoPrimeOf ⟨huL, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ 1
    (by simpa [pow_two] using hu2)

omit [Finite X] in
theorem normalizer_oTwoPrimeOf_inf {L : Subgroup X} {u s : X}
    (hsL : s ∈ normalizer (L : Set X)) (hus : s * u = u * s) :
    s ∈ normalizer ((oTwoPrimeOf (L ⊓ centralizer ({u} : Set X)) : Subgroup X) : Set X) := by
  set φ : X ≃* X := MulAut.conj s with hφ
  have hsCu : s ∈ centralizer ({u} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hus
  have hLφ : L.map φ.toMonoidHom = L := map_conj_eq_of_mem_normalizer hsL
  have hCφ : (centralizer ({u} : Set X)).map φ.toMonoidHom = centralizer ({u} : Set X) :=
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hsCu)
  have hinf : (L ⊓ centralizer ({u} : Set X)).map φ.toMonoidHom =
      L ⊓ centralizer ({u} : Set X) := by
    rw [Subgroup.map_inf_eq _ _ φ.toMonoidHom φ.injective, hLφ, hCφ]
  have h1 := map_oTwoPrimeOf_le (L ⊓ centralizer ({u} : Set X)) φ.toMonoidHom
  have h2 := oTwoPrimeOf_map_le (L ⊓ centralizer ({u} : Set X)) φ.toMonoidHom φ.injective
  rw [hinf] at h1 h2
  exact mem_normalizer_of_map_conj_eq (le_antisymm h1 h2)

theorem mem_normalizer_of_covers_of_normalizes {u s : X} {Lu E : Subgroup X}
    (hus : s * u = u * s) (hLu : IsPCompIn 2 (centralizer ({u} : Set X)) Lu) (hEL : E ≤ Lu)
    (hEs : s ∈ normalizer (E : Set X)) (hEq : IsTwoGenQuasi ↥E) :
    s ∈ normalizer (Lu : Set X) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cu : Subgroup X := centralizer ({u} : Set X) with hCu
  have hsCu : s ∈ Cu := Subgroup.mem_centralizer_singleton_iff.2 hus
  set φ : X ≃* X := MulAut.conj s with hφ
  have hCuφ : Cu.map φ.toMonoidHom = Cu :=
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hsCu)
  have hLuφ : IsPComponent 2 ((Lu.map φ.toMonoidHom).subgroupOf Cu) := by
    have := (isPComponent_subgroupOf_map_iff 2 φ.toMonoidHom φ.injective hLu.1).2 hLu.2
    rwa [hCuφ] at this
  have hLuφle : Lu.map φ.toMonoidHom ≤ Cu := by
    rw [← hCuφ]
    exact Subgroup.map_mono hLu.1
  have hEφ : E ≤ Lu.map φ.toMonoidHom := by
    intro x hx
    refine ⟨s⁻¹ * x * s, hEL ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (inv_mem hEs) x).1 hx
      simpa using this
    · show s * (s⁻¹ * x * s) * s⁻¹ = x
      group
  have heq : Lu = Lu.map φ.toMonoidHom := eq_of_isPCompIn_of_le hLu ⟨hLuφle, hLuφ⟩ hEL hEφ hEq
  exact mem_normalizer_of_map_conj_eq heq.symm

end CFSG.OddStandard.Solomon75

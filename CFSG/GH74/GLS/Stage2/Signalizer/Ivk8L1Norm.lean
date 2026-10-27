module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1Act
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1Zc

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

section Norm

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb : Subgroup A}

theorem isElementaryAbelian_of_comm_sq {M : Type*} [Group M] (E : Subgroup M)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1) :
    IsElementaryAbelian 2 ↥E :=
  { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (fun a => by
      apply Subtype.ext
      simpa [sq] using hs a a.2) }

theorem exists_elemAbelian_aut_of_normalizes (hfr : AFrame A zb Sb Vb) {J : Subgroup A}
    (hJ : IsComponent J) (hsw : Sb ≤ normalizer (J : Set A)) :
    ∃ E : Subgroup (MulAut (↥J ⧸ center ↥J)), IsElementaryAbelian 2 ↥E ∧ 16 ≤ Nat.card ↥E := by
  have hperf : Group.IsPerfect ↥J := hJ.1.1
  let φ : ↥Sb →* MulAut ↥J := actOn J hsw
  let ψ : ↥Sb →* MulAut (↥J ⧸ center ↥J) :=
    (ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥J).comp φ
  have hψ : ∀ s : ↥Sb, ψ s = 1 → (s : A) = 1 ∨ (s : A) = zb := by
    intro s hs
    have hφ : φ s = 1 := by
      apply ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥J
      rw [map_one]
      exact hs
    have hcen : (s : A) ∈ Sb ⊓ centralizer (J : Set A) :=
      Subgroup.mem_inf.mpr ⟨s.2, mem_centralizer_of_actOn_eq_one J hsw hφ⟩
    exact small_normal_cases hfr inf_le_left (inf_centralizer_normal hsw)
      (card_centralizer_le_two hfr hJ hsw) _ hcen
  obtain ⟨E, hEc, hEs, hEcard⟩ := exists_elemAbelian_image hfr ψ hψ
  exact ⟨E, isElementaryAbelian_of_comm_sq E hEc hEs, hEcard⟩

end Norm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

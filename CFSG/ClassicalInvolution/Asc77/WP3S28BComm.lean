module

public import CFSG.ClassicalInvolution.Asc77.AscE186CentA
public import CFSG.ClassicalInvolution.SmallCases.DSplitChain


public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.AscE186
open scoped commutatorElement

section Comm

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Fact p.Prime] in
theorem commutes_of_commutator_le_oddCoreOf_of_quasi {V K : Subgroup G}
    (hK : CFSG.Open.IsQuasisimple K) (hVN : V ≤ Subgroup.normalizer (K : Set G))
    (h : ⁅V, K⁆ ≤ oddCoreOf K) : Commutes V K := fun v hv k hk =>
  centralizes_of_actsTrivOnQuot_of_isQuasisimple hK (a := v)
    ⟨hVN hv, fun _ hx => h (Subgroup.commutator_mem_commutator hv hx)⟩ k hk

theorem commutes_of_mem_omegaNbr_quasi (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hqs : ∀ M ∈ Ω, CFSG.Open.IsQuasisimple M) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ omegaNbr Ω K) : Commutes K J := by
  obtain ⟨R, T, hR, hTsyl, hTN, hcomm⟩ := exists_commuting_sylow_pair hp hq hΩ hK hJ
  obtain ⟨hJΩ, hne, -⟩ := hJ
  have hT2 : IsPGroup 2 ↥T := hTsyl.2.1
  have hTK : Commutes T K :=
    commutes_of_commutator_le_oddCoreOf_of_quasi (hqs K hK) hTN
      (lemma_3_3_member hp hq hΩ hK hR hT2 hTN hcomm.symm)
  obtain ⟨t, ht⟩ := hΩ.exists_uniqueInvolution hp hq hJΩ
  have h8T : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hJΩ hTsyl)
  have htT : t ∈ T := AscL62.mem_of_uniqueInvolution_of_pGroup ht hTsyl.1 hT2 (by omega)
  have hKJ : K ≤ Subgroup.centralizer (J : Set G) := by
    refine AscQuot.le_of_forall_isSylow2In hp hq hΩ hK (M := Subgroup.centralizer (J : Set G)) ?_
    intro V hV
    have h8V := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hV)
    have hVc : V ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hTK t htT x (hV.1 hx)).symm
    have hVN : V ≤ Subgroup.normalizer (J : Set G) :=
      hΩ.le_normalizer_of_le_centralizer hp hq hJΩ hK hne ht hV.1 hV.2.1 (by omega) hVc
    have hVT : Commutes V T := fun x hx y hy => (hTK y hy x (hV.1 hx)).symm
    have := commutes_of_commutator_le_oddCoreOf_of_quasi (hqs J hJΩ) hVN
      (lemma_3_3_member hp hq hΩ hJΩ hTsyl hV.2.1 hVN hVT)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (this x hx y hy).symm
  intro k hk j hj
  exact (Subgroup.mem_centralizer_iff.mp (hKJ hk) j hj).symm

theorem commutes_of_centralizes_involution (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hqs : ∀ M ∈ Ω, CFSG.Open.IsQuasisimple M) {J J' : Subgroup G}
    {z : G} (hJ : J ∈ Ω) (hJ' : J' ∈ Ω) (hne : J' ≠ J) (hz : IsUniqueInvolution J z)
    (h1 : ∀ x ∈ J', z * x = x * z) : Commutes J J' :=
  commutes_of_mem_omegaNbr_quasi hp hq hΩ hqs hJ
    (mem_omegaNbr_of_le_centralizer hp hq hΩ hJ hJ' hne hz fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (h1 x hx).symm)

end Comm

end CFSG.ClassicalInvolution.Asc77.S28B

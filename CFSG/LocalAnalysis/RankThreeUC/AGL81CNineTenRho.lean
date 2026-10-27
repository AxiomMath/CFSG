module

import CFSG.RankThree.PartTwo.Sec13.Item135CritProof
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalPerfectLifts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeB
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Quasithin.Background.F6NoncyclicCore
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

theorem exists_hom_GL23_of_pRank_le_two {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y)
    [R.Normal] (hR : IsPGroup 3 R) (hrank : CFSG.Open.pRank 3 R ≤ 2) :
    ∃ ρ : Y →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3),
      IsPGroup 3 ↥(ρ.ker.map (MulAut.conjNormal (H := R))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨C, -, -, -, -, hDchar, -, -, hDexp, -, hDdet⟩ :=
    CFSG.RankThree.PartTwo.Sec13.CritProof.exists_isThompsonCritical_omega (P := ↥R) (p := 3)
      (by norm_num) hR
  let D : Subgroup ↥R := CFSG.RankThree.PartTwo.Sec13.CritProof.omegaOneIn 3 C
  haveI : D.Characteristic := hDchar
  have hDp : IsPGroup 3 ↥D := hR.to_subgroup D
  have hr : CFSG.Open.pRank 3 (⊤ : Subgroup ↥D) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup D]
    exact (CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) R.subtype R.subtype_injective
        D).trans ((CFSG.SectionRank.pRank_mono (p := 3) (by norm_num)
        (Subgroup.map_subtype_le D)).trans hrank)
  obtain ⟨ψ, hψ⟩ := CFSG.Quasithin.F6.exists_hom_GL_ker_eq (P := R) (X₀ := D) hR hDexp hr
  refine ⟨ψ, ?_⟩
  refine CFSG.SectionRank.Ccomm.isPGroup_of_forall_prime_orderOf (p := 3) ?_
  intro α ℓ hℓ hord
  by_contra hℓne
  have hαmem : (α : MulAut ↥R) ∈ ψ.ker.map (MulAut.conjNormal (H := R)) := α.2
  obtain ⟨y, hy, hyconj⟩ := Subgroup.mem_map.1 hαmem
  have hyk : y ∈ (CFSG.Quasithin.F6.frattiniConj R D).ker := by
    rw [← hψ]
    exact hy
  set β : MulAut ↥D := MulAut.characteristic D (MulAut.conjNormal (H := R) y) with hβdef
  have hβker : β ∈ (CFSG.SectionRank.Ccomm.autQuotient (frattini ↥D)).ker := by
    rw [MonoidHom.mem_ker]
    exact MonoidHom.mem_ker.mp hyk
  have hℓcop : Nat.Coprime ℓ 3 :=
    (Nat.Prime.coprime_iff_not_dvd hℓ).mpr fun hdvd =>
      hℓne ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp hdvd)
  have hβdvd : orderOf β ∣ ℓ := by
    have h1 : orderOf β ∣ orderOf (MulAut.conjNormal (H := R) y) := by
      rw [hβdef]
      exact orderOf_map_dvd (MulAut.characteristic D) (MulAut.conjNormal (H := R) y)
    rw [hyconj, Subgroup.orderOf_coe α, hord] at h1
    exact h1
  have hβ1 : β = 1 := by
    obtain ⟨k, hk⟩ := CFSG.SectionRank.Ccomm.isPGroup_ker_autQuotient_frattini hDp ⟨β, hβker⟩
    have hk' : β ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (hℓcop.pow_right k) hβdvd (orderOf_dvd_of_pow_eq_one hk'))
  have hconj1 : MulAut.conjNormal (H := R) y = 1 := by
    refine hDdet (MulAut.conjNormal (H := R) y) ?_ ?_
    · rw [hyconj, Subgroup.orderOf_coe α, hord]
      exact hℓcop
    · intro x hx
      have h1 : MulAut.characteristic D (MulAut.conjNormal (H := R) y) ⟨x, hx⟩ = ⟨x, hx⟩ := by
        have := congrArg (fun σ : MulAut ↥D => σ ⟨x, hx⟩) hβ1
        simpa [hβdef] using this
      have h2 := congrArg (fun w : ↥D => (w : ↥R)) h1
      simpa [MulAut.characteristic_apply_apply_coe] using h2
  have hα1 : α = 1 := Subtype.ext (by rw [← hyconj]; exact hconj1)
  rw [hα1] at hord
  simp only [orderOf_one] at hord
  exact hℓ.one_lt.ne hord

end CFSG.LocalAnalysis.RankThreeUC.AGL81C

module

public import CFSG.GH74.Generic.BProg.B3.S3T4H175
public import CFSG.Dihedral.DisconnectedInvolutionGraph.CyclicTwoTransfer

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank

section CertifiedLeaf


theorem leaf514Fam_g2 : Leaf514Fam (fun X _ => B2.PuG2Odd X) := by
  intro N _ _ H L v w _ hP _ _ _ hsv hsw hsvw
  have hnorm : H.Normal := hsv.normal
  obtain ⟨f, hf3, -, hm⟩ := hP
  have hnot : ∀ t : N, B2.ShapeInCent H t L → t ∉ H := fun t hs ht =>
    B2.PumpupTableExc.pumpupIn_g2 3 f Nat.prime_three (by norm_num) (by omega) N H t L hs ht hm
  have hY : ChevalleyExceptionalModel ↥H .G2 3 f := by
    rcases hm with ⟨hc, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd hc (by decide)
    · exact h
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨-, K, _, _, hKcard, ⟨ψ⟩⟩ := hY
  have hcenter : Subgroup.center ↥(Chevalley.adjointGroup Chevalley.Tag.G2 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let ψ' : ↥H ≃* ↥(Chevalley.adjointGroup Chevalley.Tag.G2 K) :=
    ψ.trans ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot)
  obtain ⟨-, C, _, hcyc, Θ, hΘ⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.g2_aut_facts Nat.prime_three (by norm_num) (by omega) K
      hKcard
  let ρ : N →* C := Θ.comp ((MulAut.congr ψ').toMonoidHom.comp MulAut.conjNormal)
  have hker : ∀ t : N, ρ t = 1 → t ∈ H := by
    intro t ht
    have h1 : MulAut.congr ψ' (MulAut.conjNormal t : MulAut ↥H) ∈ Θ.ker := ht
    rw [hΘ] at h1
    obtain ⟨x, hx⟩ := h1
    apply B2.T4.T4OutCore.mem_of_conjNormal_mem_inner hsv.faithful
    refine ⟨ψ'.symm x, ?_⟩
    apply (MulAut.congr ψ').injective
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    exact hx
  have hinv : ∀ t : N, B2.ShapeInCent H t L → orderOf (ρ.rangeRestrict t) = 2 := by
    intro t hs
    have ht2 : t ^ 2 = 1 := by
      have := pow_orderOf_eq_one t
      rwa [hs.inv] at this
    refine orderOf_eq_prime (by rw [← map_pow, ht2, map_one]) fun h1 => hnot t hs (hker t ?_)
    exact congrArg Subtype.val h1
  have : IsCyclic C := hcyc
  have : Finite ↥ρ.range := Finite.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hvw : ρ.rangeRestrict v = ρ.rangeRestrict w := congrArg Subtype.val
    (CFSG.DisconnectedInvolutionGraph.Helpers.cyclic_involutions_unique
      ⟨_, hinv v hsv⟩ ⟨_, hinv w hsw⟩)
  apply hnot (v * w) hsvw (hker _ _)
  have h2 : ρ.rangeRestrict (v * w) = 1 := by
    rw [map_mul, hvw, ← pow_two, ← orderOf_dvd_iff_pow_eq_one, hinv w hsw]
  exact congrArg Subtype.val h2

end CertifiedLeaf

end CFSG.GH74.Generic.BProg.B3

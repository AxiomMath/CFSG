module

public import CFSG.CGT.PushingUpLit.BHS6.BlockFixed
public import CFSG.CGT.PushingUpLit.BHS6.SixEleven
public import CFSG.CGT.PushingUpLit.BHS6.OffenderNormalizes

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

@[expose] def baumG (G T : Subgroup Γ) : Subgroup Γ :=
  ⨆ x ∈ G, baum (A1b.conjSub x T)

theorem baum_conjSub_le_baumG {G T : Subgroup Γ} {x : Γ} (hx : x ∈ G) :
    baum (A1b.conjSub x T) ≤ baumG G T :=
  le_iSup₂_of_le x hx le_rfl

theorem isSubnormal_conjSub {G E : Subgroup Γ} {y : Γ} (hy : y ∈ G)
    (h : CFSG.Open.IsSubnormal E G) : CFSG.Open.IsSubnormal (A1b.conjSub y E) G := by
  have h1 := Quasithin.A3.subnormal_map (MulAut.conj y).toMonoidHom h
  have h2 : G.map (MulAut.conj y).toMonoidHom = G := BHS.conjSub_eq_of_mem_normalizer
    (Subgroup.le_normalizer hy)
  rwa [h2] at h1

section Finite

variable [Finite Γ] {G T E S : Subgroup Γ}

theorem baum_le_normalizer_of_subnormal (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : IsBTBlock G T E) (hsub : CFSG.Open.IsSubnormal E G) (hS : IsSylowOf 2 S G) :
    baum S ≤ Subgroup.normalizer (E : Set Γ) := by
  have hJ := thompsonJ_le_normalizer_of_isBTBlock hG hT hE hsub hS
  obtain ⟨w, hwW, hwE, hwJ⟩ := exists_fixed_noncentral hG hT hE hS hJ
  intro y hy
  have hyS : y ∈ S := hy.1
  have hyG : y ∈ G := hS.1 hyS
  have hwcy : y * w = w * y := Subgroup.mem_centralizer_iff.mp hy.2 w hwJ |>.symm
  have hEmem : E ∈ btBlocksG G T := mem_btBlocksG_of_isBTBlock hE
  have hEy : A1b.conjSub y E ∈ btBlocksG G T := conjSub_mem_btBlocksG hEmem hyG
  rcases six_eleven hG hEmem hEy hsub (isSubnormal_conjSub hyG hsub) with h | h
  · exact BHS.mem_normalizer_of_conjSub_eq h.symm
  · exfalso
    apply hwE
    have hwEy : w ∈ A1b.conjSub y E := by
      rw [A1b.mem_conjSub_iff]
      have : y⁻¹ * w * y = w := by
        calc y⁻¹ * w * y = y⁻¹ * (w * y) := by group
          _ = y⁻¹ * (y * w) := by rw [← hwcy]
          _ = w := by group
      rw [this]
      exact CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 E hwW
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have := Subgroup.commutator_mem_commutator he hwEy
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this

theorem six_twelve_a (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : E ∈ btBlocksG G T)
    (hsub : CFSG.Open.IsSubnormal E G) :
    E ≤ baumG G T ∧ baumG G T ≤ Subgroup.normalizer (E : Set Γ) := by
  obtain ⟨g, hg, hEb⟩ := hE
  have hT' : IsSylowOf 2 (A1b.conjSub g T) G :=
    isSylowOf_of_isSylowTwoOf (isSylowTwoOf_conjSub_of_mem (isSylowTwoOf_of_isSylowOf hT) hg)
  refine ⟨?_, iSup₂_le fun x hx => ?_⟩
  · rw [← hEb.commutator]
    refine Subgroup.commutator_le.mpr fun e he b hb => ?_
    have hbe : e * b * e⁻¹ ∈ baumG G T := by
      have h1 : e * b * e⁻¹ ∈ baum (A1b.conjSub (e * g) T) := by
        have : baum (A1b.conjSub (e * g) T) = A1b.conjSub e (baum (A1b.conjSub g T)) := by
          rw [A1b.conjSub_mul, baum_conjSub]
        rw [this, A1b.mem_conjSub_iff]
        have h3 : e⁻¹ * (e * b * e⁻¹) * e = b := by group
        rw [h3]
        exact hb
      exact baum_conjSub_le_baumG (G.mul_mem (hEb.le he) hg) h1
    have hb' : b ∈ baumG G T := baum_conjSub_le_baumG hg hb
    have : ⁅e, b⁆ = (e * b * e⁻¹) * b⁻¹ := rfl
    rw [this]
    exact (baumG G T).mul_mem hbe ((baumG G T).inv_mem hb')
  · exact baum_le_normalizer_of_subnormal hG hT' hEb hsub
      (isSylowOf_of_isSylowTwoOf (isSylowTwoOf_conjSub_of_mem (isSylowTwoOf_of_isSylowOf hT) hx))

end Finite

end CFSG.CGT.PushingUpLit.BHS6

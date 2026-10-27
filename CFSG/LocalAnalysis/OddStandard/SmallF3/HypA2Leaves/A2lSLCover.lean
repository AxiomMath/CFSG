module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.SectionCard
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Lift

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.ComponentClassification

theorem a2l_isSLTwoOver_commutator_of_cover (hGA : TBLit.GriessMultipliersOdd)
    {G H : Type} [Group G] [Finite G] [Group H] {q₀ : ℕ} (hodd : Odd q₀) (h5 : 5 ≤ q₀)
    (hH : HarrisLit.IsSLTwoOver q₀ H) (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ center G) (h2 : IsPGroup 2 f.ker) :
    HarrisLit.IsSLTwoOver q₀ ↥(commutator G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite H := Finite.of_surjective f hf
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff q₀).1 (HypA2.isPrimePow_of_isSLTwoOver hH)
  subst hpk
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (Even.pow_of_ne_zero even_two hk.ne')
  obtain ⟨hHq, hZH, hmH, -⟩ := HarrisLit.Lemma47.sl2_facts hp hp2 hk h5 hH
  haveI : Group.IsPerfect H := hHq.1
  have hDq : CFSG.IsQuasisimple (commutator G) :=
    (AssemblyBPredicates.isQuasisimple_iff_native _).1
      (CentralExtensions.derived_quasisimple
        ((AssemblyBPredicates.isQuasisimple_iff_native H).2 hHq) f hf hker)
  haveI : Group.IsPerfect (commutator G) := hDq.1
  let ψ : ↥(commutator G) →* H := f.domRestrict (commutator G)
  have hψ : Function.Surjective ψ := by
    intro h
    have hmem : h ∈ (commutator G).map f := by
      rw [CentralExtensions.derived_map_eq_top f hf]
      exact Subgroup.mem_top _
    obtain ⟨g, hg, hgh⟩ := Subgroup.mem_map.mp hmem
    exact ⟨⟨g, hg⟩, hgh⟩
  have hψker : ψ.ker ≤ center ↥(commutator G) := fun x hx => by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hker hx)) y.val)
  obtain ⟨eC⟩ := LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hDq ψ hψ
    hψker
  have hmD : Blueprint.LieModel (↥(commutator G) ⧸ center ↥(commutator G)) .PSL 2 p k :=
    hmH.of_mulEquiv eC.symm
  have hcen : (center H).comap ψ = center ↥(commutator G) :=
    Quasisimple.center_comap_of_central_kernel ψ hψ hψker
  have hZ2 : IsPGroup 2 ↥(center H) := IsPGroup.of_card (n := 1) (by rw [hZH, pow_one])
  have hker2 : IsPGroup 2 ↥ψ.ker := by
    refine h2.of_injective (⟨⟨fun x => ⟨x.1.1, x.2⟩, rfl⟩, fun x y => rfl⟩ : ↥ψ.ker →* ↥f.ker) ?_
    intro x y hxy
    have h1 := Subtype.ext_iff.1 hxy
    exact Subtype.ext (Subtype.ext h1)
  have hD2 : IsPGroup 2 ↥(center ↥(commutator G)) := by
    rw [← hcen]
    exact hZ2.comap_of_ker_isPGroup ψ hker2
  have hDZ : center ↥(commutator G) ≠ ⊥ := by
    have hZne : center H ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot _).1 (by rw [hZH]; norm_num)
    obtain ⟨h, hh1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZne
    obtain ⟨d, hd⟩ := hψ (h : H)
    have hdc : d ∈ center ↥(commutator G) := by
      rw [← hcen]
      show ψ d ∈ center H
      rw [hd]
      exact h.2
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hdc
    apply hh1
    apply Subtype.ext
    rw [← hd, hdc, map_one]
    rfl
  exact HarrisLit.T1.isSLTwoOver_of_psl2Cover hGA hp hp2 hDq hD2 hDZ hmD

end CFSG.OddStandard.SmallF3.HypA2Leaves

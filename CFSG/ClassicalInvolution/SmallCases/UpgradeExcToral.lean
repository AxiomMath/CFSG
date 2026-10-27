module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeExcRoots
public import CFSG.ClassicalInvolution.SmallCases.UpgradeParamsBasic
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalToral

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

variable {τ : Tag} {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]

theorem card_eq_of_isClassicalMember_toral (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hK : Odd (Nat.card K)) (b : Fin τ.rank → Kˣ) (hb : ∀ i, b i = 1 ∨ b i = -1)
    {L : Subgroup ↥(adjointGroup τ K)} {z : ↥(adjointGroup τ K)}
    (hz : (z : ModGL τ K) = rootDiagUnit τ b) (h : IsClassicalMember p f L z) :
    Nat.card K = p ^ f := by
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  have : Finite (ModGL τ K) := finite_modGL
  have hK2 : ringChar K ≠ 2 := ringChar_ne_two_of_odd_card hK
  set χ := maskChar (signTupleBits b) with hχ
  have hCz := centralizer_eq_subgroupOf_toralCentralizer b z hz
  have hXC := toralCentralizer_le_adjointGroup (K := K) (τ := τ) b
  let e : ↥(Subgroup.centralizer ({z} : Set ↥(adjointGroup τ K))) ≃*
      ↥(toralCentralizer τ K b) :=
    (MulEquiv.subgroupCongr hCz).trans (Subgroup.subgroupOfEquivOfLe hXC)
  have hLCz : L ≤ Subgroup.centralizer ({z} : Set ↥(adjointGroup τ K)) :=
    isSubnormal_le h.subnormal
  have hP := isPComponent_two_of_isClassicalMember (by omega) h
  set Jx : Subgroup ↥(toralCentralizer τ K b) :=
    (L.subgroupOf (Subgroup.centralizer ({z} : Set ↥(adjointGroup τ K)))).map
      e.toMonoidHom with hJx
  have hJxP : CFSG.IsPComponent 2 Jx := isPComponent_map_of_isPComponent 2 e hP
  have hLJ : L.map (adjointGroup τ K).subtype = Jx.map (toralCentralizer τ K b).subtype := by
    ext y
    simp only [hJx, Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨e ⟨g, hLCz hg⟩, ⟨⟨g, hLCz hg⟩, hg, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨g.1, hg, rfl⟩
  set JM := Jx.map (toralCentralizer τ K b).subtype with hJM
  obtain ⟨hSX, hnormX, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction τ K hK2 b hb
  have hJX : JM.subgroupOf (toralCentralizer τ K b) = Jx :=
    Subgroup.comap_map_eq_self_of_injective (toralCentralizer τ K b).subtype_injective Jx
  have h1 : JM ≤ toralCentralizer τ K b ∧
      CFSG.IsPComponent 2 (JM.subgroupOf (toralCentralizer τ K b)) :=
    ⟨Subgroup.map_subtype_le Jx, by rw [hJX]; exact hJxP⟩
  obtain ⟨hJS, hJS'⟩ :=
    (CFSG.LieType.AlgebraicGroups.isPComponent_subgroupOf_iff_of_isSolvable hSX 2
      Nat.prime_two JM).1 h1
  have hSeq : rootSpan τ K (rootCharKernel b) =
      rootSpan τ K (kernelRoots (maskChar (signTupleBits b))) := by
    rw [rootCharKernel_eq_kernelRoots hK2 hb]
  rw [hSeq] at hJS hJS'
  obtain ⟨i, hi⟩ := exists_le_componentRootSpan_of_isPComponent JM hJS hJS'
  have hcomp := CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_of_le
    (p := 2) hi (componentRootSpan_le K i) hJS'
  have hJeq : CFSG.IsQuasisimple (componentRootSpan K χ i) → JM = componentRootSpan K χ i := by
    intro hqs
    have htop := eq_top_of_isPComponent_of_isQuasisimple hqs hcomp
    exact le_antisymm hi (Subgroup.subgroupOf_eq_top.1 htop)
  have huniq : JM = componentRootSpan K χ i → ∀ a ∈ componentRootSpan K χ i, a * a = 1 →
      a ≠ 1 → a = rootDiagUnit τ b := by
    intro hJS2 a ha ha2 ha1
    rw [← hJS2, ← hLJ] at ha
    obtain ⟨ℓ, hℓ, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨eY⟩ := h.nonempty_equiv
    have hz2 : z * z = 1 := by
      have := pow_orderOf_eq_one z
      rwa [h.orderOf_eq_two, pow_two] at this
    have hℓ2 : ℓ * ℓ = 1 := Subtype.ext ha2
    have hℓ1 : ℓ ≠ 1 := fun h' => ha1 (by rw [h']; rfl)
    have hcomm : ℓ * z = z * ℓ := Subgroup.mem_centralizer_singleton_iff.mp (hLCz hℓ)
    have heq : (⟨ℓ, hℓ⟩ : ↥L) = ⟨z, h.mem⟩ := by
      by_contra hne
      refine false_of_two_commuting_involutions_sl2 hodd eY (a := ⟨ℓ, hℓ⟩) (b := ⟨z, h.mem⟩)
        ?_ ?_ ?_ hne
      · exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hℓ2)
          (fun h' => hℓ1 (congrArg Subtype.val h'))
      · exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hz2)
          (fun h' => h.ne_one (congrArg Subtype.val h'))
      · exact Subtype.ext hcomm
    have hℓz : ℓ = z := congrArg Subtype.val heq
    show ((ℓ : ↥(adjointGroup τ K)) : ModGL τ K) = _
    rw [hℓz, hz]
  by_cases hrank : 2 < (componentRoots χ i).ncard
  · exfalso
    have hqs := (odd_sign_root_component_quasisimple τ K χ i).2.2 hK2 hrank
    exact not_two_lt_ncard_componentRoots hK b hb i (huniq (hJeq hqs)) hrank
  · obtain ⟨γ, hγ, hSi⟩ := exists_componentRootSpan_eq_pair (K := K) i (not_lt.mp hrank)
    obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 hγ
    obtain ⟨eγ, -⟩ := exists_mulEquiv_rootSubgroup_sup hK2 hw
    subst hw
    by_cases hsmall : Nat.card K < 4
    · exfalso
      have : Group.IsSolvable ↥(componentRootSpan K χ i) := by
        have := isSolvable_sl_two_of_card_lt (F := K) hsmall
        rw [hSi]
        exact Group.isSolvable_of_surjective (f := eγ.toMonoidHom) eγ.surjective
      exact CFSG.ComponentClassification.CatalogueBGeneralLinear.no_pComponent_of_solvable 2 _
        hcomp
    · have h5K : 5 ≤ Nat.card K := by
        obtain ⟨k, hk⟩ := hK
        omega
      have hqs := isQuasisimple_componentRootSpan_of_five_le hK2 h5K χ i
      have hJS := hJeq hqs
      have hLS : L.map (adjointGroup τ K).subtype =
          rootSubgroup τ K (w • (Pi.single j 1 : Fin τ.rank → ℤ)) ⊔
            rootSubgroup τ K (-(w • (Pi.single j 1 : Fin τ.rank → ℤ))) := by
        rw [hLJ, hJS, hSi]
      let eL : SL(2, K) ≃* ↥L :=
        eγ.trans ((MulEquiv.subgroupCongr hLS.symm).trans
          (L.equivMapOfInjective (adjointGroup τ K).subtype
            (adjointGroup τ K).subtype_injective).symm)
      exact card_eq_of_isClassicalMember_equiv_sl2' h hq eL

end CFSG.ClassicalInvolution.Upgrade

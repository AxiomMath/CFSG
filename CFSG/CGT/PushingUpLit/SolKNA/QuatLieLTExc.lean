module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLT0Basic
public import CFSG.LieType.HighestRoot.CentChevalleyData
public import CFSG.ClassicalInvolution.Q3.Q3ExcAdj

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

theorem map_centralizer_singleton_mulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    (a : G) :
    (Subgroup.centralizer ({a} : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ a} : Set H) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp (SetLike.mem_coe.mp hy)
    rw [Subgroup.mem_centralizer_singleton_iff]
    show φ y * φ a = φ a * φ y
    rw [← map_mul, ← map_mul, hy']
  · intro hx
    have hx' : x * φ a = φ a * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    refine ⟨φ.symm x, ?_, by simp⟩
    show φ.symm x ∈ Subgroup.centralizer ({a} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hx'

theorem isQuasisimple_open_quotient_oddCore {E : Type*} [Group E] [Finite E]
    (h : CFSG.IsQuasisimple E) :
    CFSG.Open.IsQuasisimple (E ⧸ CFSG.Open.classicalInvolutionOddCore E) := by
  have h' : CFSG.Open.IsQuasisimple E := ⟨h.1.commutator_eq_top, h.2.1⟩
  exact CFSG.ComponentClassification.Quasisimple.central_quotient h' _
    (CFSG.ClassicalInvolution.Balance.oddCore_le_center_of_isQuasisimple h')

section Chev


theorem chev_exists_component (τ : Tag) (i : Fin τ.rank) (wit : List ℕ)
    (hc : isolatedCheck τ i wit = true) (hsym : ∀ j, τ.symmetrizer j j ≤ τ.symmetrizer i i)
    (j : Fin τ.rank) (hji : j ≠ i) (hcart : τ.cartan i j = 0) :
    ∃ E : Subgroup (ModGL τ (GaloisField 3 1)),
      E ≤ toralCentralizer τ (GaloisField 3 1) (signTuple τ (GaloisField 3 1) i) ∧
      CFSG.Open.IsSubnormal E
        (toralCentralizer τ (GaloisField 3 1) (signTuple τ (GaloisField 3 1) i)) ∧
      CFSG.IsQuasisimple ↥E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 : Nat.card (GaloisField 3 1) = 3 :=
    CFSG.ClassicalInvolution.Q3.exc3_natCard_galoisField_three
  have hK : ringChar (GaloisField 3 1) ≠ 2 := ringChar_ne_two_of_card_eq_three hK3
  have hker := rootCharKernel_signTuple_eq (τ := τ) (K := GaloisField 3 1) (i := i) hK
  have hlong := iform_le_of_symmetrizer_le (τ := τ) hsym
  have hγ : (Pi.single i 1 : Fin τ.rank → ℤ) ∈
      kernelRoots (signChar τ (GaloisField 3 1) i) := by
    rw [← hker]
    exact single_mem_rootCharKernel_signTuple hK i
  have hjk : (Pi.single j 1 : Fin τ.rank → ℤ) ∈
      kernelRoots (signChar τ (GaloisField 3 1) i) := by
    rw [← hker, mem_rootCharKernel_signTuple hK]
    refine ⟨isRoot_single τ j, ?_⟩
    simp [Pi.single_apply, hcart]
  have hk : (⟦⟨Pi.single j 1, hjk⟩⟧ : KernelComponent (signChar τ (GaloisField 3 1) i)) ≠
      ⟦⟨Pi.single i 1, hγ⟩⟧ := by
    intro h
    have h1 := (mem_pair_iff_of_mk_eq hK hlong h).2 (Or.inl rfl)
    rcases h1 with h1 | h1
    · have := congrFun h1 j
      simp [hji] at this
    · have := congrFun h1 j
      simp [hji] at this
  have hbig := two_lt_ncard_componentRoots hK hc hγ hk
  have hq := isQuasisimple_componentRootSpan hK hbig
  set χ := signChar τ (GaloisField 3 1) i with hχ
  set k : KernelComponent χ := ⟦⟨Pi.single j 1, hjk⟩⟧ with hkdef
  have hES : componentRootSpan (GaloisField 3 1) χ k ≤
      rootSpan τ (GaloisField 3 1) (kernelRoots χ) := componentRootSpan_le _ k
  have hSX : rootSpan τ (GaloisField 3 1) (kernelRoots χ) ≤
      toralCentralizer τ (GaloisField 3 1) (signTuple τ (GaloisField 3 1) i) := by
    rw [← hker]
    exact rootSpan_rootCharKernel_le_toralCentralizer _
  have hEn : ((componentRootSpan (GaloisField 3 1) χ k).subgroupOf
      (rootSpan τ (GaloisField 3 1) (kernelRoots χ))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hES).mpr (rootSpan_le_normalizer _ k)
  have hSn : ((rootSpan τ (GaloisField 3 1) (kernelRoots χ)).subgroupOf
      (toralCentralizer τ (GaloisField 3 1) (signTuple τ (GaloisField 3 1) i))).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hSX).mpr ?_
    rw [← hker]
    exact toralCentralizer_le_normalizer_rootSpan _
  exact ⟨componentRootSpan (GaloisField 3 1) χ k, hES.trans hSX,
    CFSG.Open.IsSubnormal.step hES hEn
      (CFSG.Open.IsSubnormal.step hSX hSn (CFSG.Open.IsSubnormal.refl _)), hq⟩

theorem kill_adjoint (τ : Tag) (i : Fin τ.rank) (wit : List ℕ)
    (hc : isolatedCheck τ i wit = true) (hsym : ∀ j, τ.symmetrizer j j ≤ τ.symmetrizer i i)
    (hj : ∃ j : Fin τ.rank, j ≠ i ∧ τ.cartan i j = 0)
    {X : Type} [Group X] [Finite X] (ψ : ↥(adjointGroup τ (GaloisField 3 1)) →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center _)
    {R : Subgroup ↥(adjointGroup τ (GaloisField 3 1))} {g : ↥(adjointGroup τ (GaloisField 3 1))}
    (hR : rankOneGroup (adjDatum (rootOperatorFamily τ) (GaloisField 3 1)) (Pi.single i 1) =
      R.map (MulAut.conj g).toMonoidHom)
    {t : X} (ht : t ∈ R.map ψ) (ht2 : orderOf t = 2) :
    ∃ E : Subgroup X, CFSG.Open.IsSubnormal E (Subgroup.centralizer ({t} : Set X)) ∧
      CFSG.Open.IsQuasisimple (E ⧸ CFSG.Open.classicalInvolutionOddCore E) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 : Nat.card (GaloisField 3 1) = 3 :=
    CFSG.ClassicalInvolution.Q3.exc3_natCard_galoisField_three
  have hK : ringChar (GaloisField 3 1) ≠ 2 := ringChar_ne_two_of_card_eq_three hK3
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact le_bot_iff.mp (hker.trans center_adjointGroup_eq_bot.le)
  have hroot : IsRoot τ (Pi.single i 1 : Fin τ.rank → ℤ) := isRoot_single τ i
  obtain ⟨r, hrR, hrt⟩ := Subgroup.mem_map.mp ht
  have hz₀R : g * r * g⁻¹ ∈ rankOneGroup (adjDatum (rootOperatorFamily τ) (GaloisField 3 1))
      (Pi.single i 1) := by
    rw [hR]
    exact Subgroup.mem_map.mpr ⟨r, hrR, by simp [MulAut.conj_apply]⟩
  have hz₀2 : orderOf (g * r * g⁻¹) = 2 := by
    have h1 : orderOf (g * r * g⁻¹) = orderOf r := MulEquiv.orderOf_eq (MulAut.conj g) r
    have h2 : orderOf (ψ r) = orderOf r := orderOf_injective ψ hinj r
    rw [h1, ← h2, hrt, ht2]
  have hz₀mem : ((g * r * g⁻¹ : ↥(adjointGroup τ (GaloisField 3 1))) : ModGL τ (GaloisField 3 1)) ∈
      rootSubgroup τ (GaloisField 3 1) (Pi.single i 1) ⊔
        rootSubgroup τ (GaloisField 3 1) (-Pi.single i 1) := by
    have := hz₀R
    rw [rankOneGroup_adjDatum _ hroot] at this
    exact Subgroup.mem_subgroupOf.mp this
  have hz₀ord : orderOf ((g * r * g⁻¹ : ↥(adjointGroup τ (GaloisField 3 1))) :
      ModGL τ (GaloisField 3 1)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hz₀2
  have hz₀d : ((g * r * g⁻¹ : ↥(adjointGroup τ (GaloisField 3 1))) : ModGL τ (GaloisField 3 1)) =
      rootDiagUnit τ (signTuple τ (GaloisField 3 1) i) := by
    rw [← torusElt_neg_one_eq]
    exact eq_torusElt_neg_one hK i hz₀mem hz₀ord
  obtain ⟨j, hji, hcart⟩ := hj
  obtain ⟨E₀, hE₀X, hE₀sub, hE₀q⟩ := chev_exists_component τ i wit hc hsym j hji hcart
  have hE₀A : E₀ ≤ adjointGroup τ (GaloisField 3 1) :=
    hE₀X.trans (CFSG.ClassicalInvolution.ModelFacts.toralCentralizer_le_adjointGroup _)
  have hCz := CFSG.ClassicalInvolution.ModelFacts.centralizer_eq_subgroupOf_toralCentralizer
    (signTuple τ (GaloisField 3 1) i) (g * r * g⁻¹) hz₀d
  have hE₁sub : CFSG.Open.IsSubnormal (E₀.subgroupOf (adjointGroup τ (GaloisField 3 1)))
      (Subgroup.centralizer ({g * r * g⁻¹} : Set ↥(adjointGroup τ (GaloisField 3 1)))) := by
    rw [hCz]
    exact CFSG.ClassicalInvolution.isSubnormal_subgroupOf hE₀sub _
  let φ : ↥(adjointGroup τ (GaloisField 3 1)) ≃* X :=
    (MulEquiv.ofBijective ψ ⟨hinj, hψ⟩).trans (MulAut.conj (ψ g)⁻¹)
  have hφz : φ (g * r * g⁻¹) = t := by
    show (MulAut.conj (ψ g)⁻¹) (ψ (g * r * g⁻¹)) = t
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hrt]
    group
  refine ⟨(E₀.subgroupOf (adjointGroup τ (GaloisField 3 1))).map φ.toMonoidHom, ?_, ?_⟩
  · have := CFSG.ComponentClassification.Components.chain_map φ.toMonoidHom hE₁sub
    rwa [map_centralizer_singleton_mulEquiv φ (g * r * g⁻¹), hφz] at this
  · have hq1 : CFSG.IsQuasisimple ↥(E₀.subgroupOf (adjointGroup τ (GaloisField 3 1))) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hE₀A).symm hE₀q
    exact isQuasisimple_open_quotient_oddCore (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((E₀.subgroupOf (adjointGroup τ (GaloisField 3 1))).equivMapOfInjective φ.toMonoidHom
        φ.injective) hq1)

end Chev

section Models


theorem kill3At_E8 : Kill3At .E8 0 := by
  intro X _ _ ψ hψ hker R hR t ht ht2 _
  right
  have hadm : StatedLieAdmissible .E8 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl⟩
  have hlong := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .E8 0 3 1
    Nat.prime_three trivial hadm
  have hR₀ : rankOneGroup (adjDatum (rootOperatorFamily .E8) (GaloisField 3 1))
      (Pi.single (idx0 .E8) 1) ∈
        fundamentalSubgroups .E8 (modelUniv .E8 0 3 1 Nat.prime_three).D :=
    ⟨1, Pi.single (idx0 .E8) 1, Or.inl (hlong (idx0 .E8) trivial), (conjSub_one _).symm⟩
  obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .E8 0 3 1
    Nat.prime_three trivial hadm (by decide) (by decide) R hR _ hR₀
  exact kill_adjoint .E8 (idx0 .E8) witE8 isolatedCheck_E8 (symmetrizer_le_one .E8 rfl _)
    (by decide) ψ hψ hker.le hg ht ht2

theorem kill3At_F4 : Kill3At .F4 0 := by
  intro X _ _ ψ hψ hker R hR t ht ht2 _
  right
  have hadm : StatedLieAdmissible .F4 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl⟩
  have hlong := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .F4 0 3 1
    Nat.prime_three trivial hadm
  have hR₀ : rankOneGroup (adjDatum (rootOperatorFamily .F4) (GaloisField 3 1))
      (Pi.single (idx0 .F4) 1) ∈
        fundamentalSubgroups .F4 (modelUniv .F4 0 3 1 Nat.prime_three).D :=
    ⟨1, Pi.single (idx0 .F4) 1, Or.inl (hlong (idx0 .F4) Nat.zero_lt_two), (conjSub_one _).symm⟩
  obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .F4 0 3 1
    Nat.prime_three trivial hadm (by decide) (by decide) R hR _ hR₀
  exact kill_adjoint .F4 (idx0 .F4) witF4 isolatedCheck_F4 symmetrizer_le_F4
    (by decide) ψ hψ hker.le hg ht ht2

end Models

end CFSG.CGT.PushingUpLit.SolKNA

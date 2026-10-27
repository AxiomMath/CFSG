module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Lemma42Class
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericQuasisimple3NoBM
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Lemma42Generic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup CFSG.AGLEmbedding

theorem genericComponentClass_of_inputs_noBM {G : Type} [Group G] [Finite G] (hS : Setting G)
    (hU0 : FullCoreLocal G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (K2 : StronglyEmbeddedCyclicOuterKFact) (K3 : KFactOutCyclic) (K4 : KF1At G)
    (hno : NoExcludedSection3 G) :
    GenericComponentClass G := by
  intro p hp P M hM hfail hIH x hgen hp5
  have hprime := sigmaA_prime p hp
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨S, hSmap, hsh⟩ := exists_genericShadow hS hU0 hp hp5 hM hgen
  have hCtop : centralizer ({x} : Set G) ≠ ⊤ := fun htop => hS.normalizer_zpowers_ne_top
    hgen.2.1.2.1 (eq_top_iff.2 (htop ▸ centralizer_singleton_le_normalizer_zpowers x))
  have hK4 : KF1On (centralizer ({x} : Set G) ⧸
      primeComplementCore (G := centralizer ({x} : Set G)) p) :=
    fun q hq hq5 L hL hcat hpg hdvd => K4 q hq hq5 _ hCtop _ L hL hcat hpg hdvd
  have hBM : ∀ L : Subgroup (GenericReduced p x), IsComponentOf L ⊤ → NotBM ↥L :=
    fun L hL => notBM_of_notSecExcl3
      (notSecExcl3_of_noExcludedSection3 hno hL.2.2 (hsh.center_eq_bot hK4 hL))
  obtain ⟨Lb, hLbc, hLbn, huniq, hLbZ, hLbΓ, hLblist⟩ :=
    hsh.exists_main_noBM hK4 K1 K2 K3 hBM
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) p with hO
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπ
  have : Lb.Normal := hLbn
  have hLbperf : ⁅Lb, Lb⁆ = Lb := Subgroup.isPerfect_iff.mp ⟨hLbc.2.2.1⟩
  obtain ⟨hLsimple, -, -⟩ := hsh.simple_nonab_catalog hK4 hLbc
  have hLb_ne : Lb ≠ ⊥ := by
    intro h
    have := hLsimple.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot Lb).mp this h
  set J : Subgroup C := perfectCore (Lb.comap π) with hJ
  have hJn : J.Normal := normal_perfectCore _
  have hJperf : ⁅J, J⁆ = J := commutator_perfectCore _
  have hJmap : J.map π = Lb :=
    map_perfectCore_comap π (QuotientGroup.mk'_surjective O) Lb hLbperf
  set JG : Subgroup G := J.map C.subtype with hJG
  have hJGC : JG ≤ C := Subgroup.map_subtype_le J
  have hCJG : C ≤ normalizer (JG : Set G) := le_normalizer_map_subtype J
  have hJGperf : ⁅JG, JG⁆ = JG := commutator_map_subtype J hJperf
  have hsimple : IsSimpleGroup ↥(J.map π) := by rw [hJmap]; exact hLsimple
  obtain ⟨hxP, ⟨hxM, hx1, hxp, hx3, hCM⟩, hsyl, hrk⟩ := hgen
  have hnot : ¬ JG ≤ M := by
    intro hle
    apply hLbΓ
    have hJ' : J ≤ (C ⊓ M).subgroupOf C := fun j hj =>
      Subgroup.mem_subgroupOf.mpr ⟨j.2, hle ⟨j, hj, rfl⟩⟩
    rw [← hJmap]
    exact Subgroup.map_mono hJ'
  have hlt : rankThreePrimeCore p JG < JG :=
    rankThreePrimeCore_map_subtype_lt J (by rw [hJmap]; exact hLb_ne)
  let e : J ≃* JG := J.equivMapOfInjective C.subtype C.subtype_injective
  let ψ₀ : J →* J.map π := (π.comp J.subtype).codRestrict (J.map π)
    fun j => Subgroup.mem_map_of_mem π j.2
  let ψ₁ : JG →* J.map π := ψ₀.comp e.symm.toMonoidHom
  have hψ₁ : Function.Surjective ψ₁ := by
    rintro ⟨_, j, hj, rfl⟩
    exact ⟨e ⟨j, hj⟩, by simp [ψ₁, ψ₀]⟩
  have hcoe : ∀ a : JG, (((e.symm a : J) : C) : G) = (a : G) := by
    intro a
    conv_rhs => rw [← e.apply_symm_apply a]
    rfl
  have hker₁ : ψ₁.ker = (rankThreePrimeCore p JG).subgroupOf JG := by
    ext a
    constructor
    · intro ha
      have h1 : π ((e.symm a : J) : C) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
        simpa [ψ₁, ψ₀] using this
      have h2 : ((e.symm a : J) : C) ∈ O := by
        rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have h3 : (a : G) ∈ rankThreePrimeCore p (J.map C.subtype) := by
        rw [rankThreePrimeCore_map_subtype]
        exact ⟨((e.symm a : J) : C), ⟨(e.symm a).2, h2⟩, hcoe a⟩
      exact h3
    · intro ha
      have h3 : (a : G) ∈ rankThreePrimeCore p (J.map C.subtype) := ha
      rw [rankThreePrimeCore_map_subtype] at h3
      obtain ⟨c, ⟨hcJ, hcO⟩, hca⟩ := h3
      have hce : (e.symm a : J) = ⟨c, hcJ⟩ := by
        apply Subtype.ext
        apply Subtype.ext
        rw [hcoe a]
        exact hca.symm
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      have : π ((e.symm a : J) : C) = 1 := by
        rw [hce]
        exact (QuotientGroup.eq_one_iff c).mpr hcO
      simpa [ψ₁, ψ₀] using this
  let eL : ↥(J.map π) ≃* ↥Lb := MulEquiv.subgroupCongr hJmap
  let ψ : JG →* Lb := eL.toMonoidHom.comp ψ₁
  have hψ : Function.Surjective ψ := eL.surjective.comp hψ₁
  have hker : ψ.ker = (rankThreePrimeCore p JG).subgroupOf JG := by
    rw [← hker₁]
    ext a
    simp only [MonoidHom.mem_ker]
    exact ⟨fun h => eL.injective (h.trans (map_one eL).symm), fun h => by simp [ψ, h]⟩
  have hFi : ¬ Nonempty (↥Lb ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group) :=
    notSecExcl3_of_noExcludedSection3 hno hLbc.2.2 hLbZ .Fi22 (by simp [sectionExcludedNames3])
  have hlist := isRankTwoSEGroupE3_of_isRankTwoSEGroup hS hp hp5 ψ hψ hFi hLblist
  exact ⟨JG, hJGC, hCJG, Subgroup.isPerfect_iff.mpr hJGperf, hlt,
    fun N hN hn hON => eq_or_eq_of_normal J hsimple N hN hn hON, hnot, ↥Lb, inferInstance, ψ, hψ,
    hker, hlist, hFi⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

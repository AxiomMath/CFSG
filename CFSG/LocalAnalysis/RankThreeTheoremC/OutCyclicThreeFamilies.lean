module

import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.OrthOdd
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.RankThree.PartOne.OutStructure

open CFSG.GorensteinWalter CFSG.Assembly.LowTwoRank

theorem mem_of_pow_mem_of_index_eq_two {G : Type*} [Group G] {H : Subgroup G} (hH : H.index = 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {g : G} {k : ℕ} (h : g ^ (p ^ k) ∈ H) : g ∈ H := by
  have : H.Normal := Subgroup.normal_of_index_eq_two hH
  have hcard : Nat.card (G ⧸ H) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hH
  have hxk : (g : G ⧸ H) ^ (p ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact h
  have hdvd1 : orderOf (g : G ⧸ H) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hxk
  have hdvd2 : orderOf (g : G ⧸ H) ∣ 2 := hcard ▸ orderOf_dvd_natCard _
  have hn : ¬ p ∣ 2 := fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
  have hcop : Nat.Coprime (p ^ k) 2 :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn)
  have hx1 : orderOf (g : G ⧸ H) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  exact (QuotientGroup.eq_one_iff g).mp (orderOf_eq_one_iff.mp hx1)

theorem outPNice_PSL2_field_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (K : Type) [Field K]
    [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] (hKcard : Nat.card K = ℓ ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) : OutPNice p (PSL2 K) := by
  classical
  have hinj := pGammaL2ToMulAutPSL2_injective K hK hcard
  have hsurj := pGammaL2ToMulAutPSL2_surjective K hKcard hK hcard
  let Ψe : PGammaL2 K ≃* MulAut (PSL2 K) :=
    MulEquiv.ofBijective (pGammaL2ToMulAutPSL2 K hK hcard) ⟨hinj, hsurj⟩
  have : Finite (PGammaL2 K) := Finite.of_equiv (MulAut (PSL2 K)) Ψe.symm.toEquiv
  have : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let N : Subgroup (PGammaL2 K) := (SemidirectProduct.inl : PGL2 K →* PGammaL2 K).range
  have hcyc : IsCyclic (PGammaL2 K ⧸ N) := pGammaL2_quotient_pgl_isCyclic K hK
  let Θ : MulAut (PSL2 K) →* PGammaL2 K ⧸ N :=
    (QuotientGroup.mk' N).comp Ψe.symm.toMonoidHom
  have hΨinl : ∀ g : PGL2 K, Ψe (SemidirectProduct.inl g) = pgl2InnerAutPSL2 K hK hcard g :=
    fun g => pGammaL2ToMulAutPSL2_inl K hK hcard g
  have hker : ∀ δ ∈ Θ.ker, ∃ g : PGL2 K, δ = pgl2InnerAutPSL2 K hK hcard g := by
    intro δ hδ
    have h1 : Ψe.symm δ ∈ N := (QuotientGroup.eq_one_iff _).mp hδ
    obtain ⟨g, hg⟩ := h1
    refine ⟨g, ?_⟩
    rw [← hΨinl, hg, MulEquiv.apply_symm_apply]
  refine outPNice_of_hom Θ (fun x y => IsMulCommutative.is_comm.comm x y) ?_ ?_
    (pChain_of_isCyclic hp)
  · rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    have : (MulAut.conj y : MulAut (PSL2 K)) =
        Ψe (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y)) := by
      rw [hΨinl, pgl2InnerAutPSL2_toPGL]
    change (QuotientGroup.mk' N) (Ψe.symm (MulAut.conj y)) = 1
    rw [this, MulEquiv.symm_apply_apply]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨_, rfl⟩
  · intro δ hδ k hk
    obtain ⟨g, rfl⟩ := hker δ hδ
    obtain ⟨y, hy⟩ := hk
    have hy' : pgl2InnerAutPSL2 K hK hcard (g ^ (p ^ k)) =
        pgl2InnerAutPSL2 K hK hcard (Matrix.ProjectiveSpecialLinearGroup.toPGL y) := by
      rw [pgl2InnerAutPSL2_toPGL, map_pow]
      exact hy.symm
    have hgp : g ^ (p ^ k) ∈
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
      ⟨y, (pgl2InnerAutPSL2_injective K hK hcard hy').symm⟩
    have hgH := mem_of_pow_mem_of_index_eq_two (pgl2_psl2Range_index_eq_two K hK) hp hp2 hgp
    obtain ⟨y', hy'⟩ := hgH
    exact ⟨y', by rw [← hy', pgl2InnerAutPSL2_toPGL]⟩

theorem outPNice_PSL_two_odd_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    {ℓ f : ℕ} (hℓ2 : ℓ ≠ 2) (h : StatedClassicalModel X .PSL 2 ℓ f) : OutPNice p X := by
  obtain ⟨⟨hℓ, hf, -, hne2, hne3⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have hK' : IsOddPrimePower (Nat.card K) := ⟨ℓ, f, hℓ, hodd, hf, hK⟩
  have hcard : 3 < Nat.card K := by
    rw [hK]
    have h1 : 3 ≤ ℓ ^ f := by
      calc 3 ≤ ℓ := by
            have := hℓ.two_le
            omega
        _ ≤ ℓ ^ f := Nat.le_self_pow (by omega) ℓ
    have h2 : ℓ ^ f ≠ 3 := fun h3 => hne3 (by rw [h3])
    have h4 : ℓ ^ f ≠ 4 := fun h4 => by
      have := (hodd.pow (n := f))
      rw [h4] at this
      exact absurd this (by decide)
    omega
  have e' : X ≃* PSL2 K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  exact OutPNice.of_mulEquiv e' (outPNice_PSL2_field_of_ne_two hp hp2 K hK hK' hcard)

open Matrix Subgroup QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open scoped commutatorElement

section Models

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.Automorphisms
open scoped Pointwise

theorem outPNice_POmegaOdd_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    {n r m : ℕ} (h : StatedClassicalModel X .POmegaOdd n r m) : OutPNice p X :=
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_POmegaOdd_all hp hp2 h

theorem outPNice_POmegaPlus_ge_five_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type}
    [Group X] {n r m : ℕ} (hn : 5 ≤ n) (h : StatedClassicalModel X .POmegaPlus n r m) :
    OutPNice p X :=
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_POmegaPlus_all_ge_five hp hp2 hn h

theorem outPNice_POmegaMinus_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    {n r m : ℕ} (h : StatedClassicalModel X .POmegaMinus n r m) : OutPNice p X :=
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_POmegaMinus_all hp hp2 h

end Models

end CFSG.LocalAnalysis.RankThreeTheoremC

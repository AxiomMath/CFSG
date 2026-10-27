module

public import CFSG.ClassicalInvolution.RouteD.NonClassicalLocal
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectBridge

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.Open (classicalInvolutionOddCore)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

section Layer

variable [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem visible_equiv_layer (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    {i : Fin D.card}
    (hsc : FundamentalSingleClass (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    (hperf : FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    {K : Subgroup G} {R₀ : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hK : Corr Ω x D i K R₀) {z : G} (hz : z ∈ K) {k : (modelUniv
      (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hk : D.hom i k = locMk Ω x ⟨z, le_centralizingLayer hK.1 hz⟩) :
    ∃ e : {N : compMembers Ω x D i // N.1 ∈ centralizingMembers Ω {x, z}} ≃
        {R : compFund D i // R.1 ≤ Subgroup.centralizer ({k} : Set _)},
      ∀ N N', Commutes N.1.1 N'.1.1 ↔ Commutes (e N).1.1 (e N').1.1 := by
  obtain ⟨e₀, he₀⟩ := exists_compMembersEquiv hΩ hex hP1 D hsc hperf
  refine ⟨Equiv.subtypeEquiv e₀ (fun N => ?_), fun N N' => ?_⟩
  · exact visible_iff_corr hΩ hP1 hperf hK (he₀ N) hz hk
  · exact corr_commutes hΩ hP1 hperf (he₀ N.1) (he₀ N'.1)

end Layer

theorem componentFacts_of_no_exotic {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) (hp2 : p ≠ 2) (hq : 4 ≤ p ^ f)
    (hD : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4) :
    (∀ i, FundamentalSingleClass (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D) ∧
    ∀ i, FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D :=
  ⟨fun i => fundamentalSingleClass_of_ne D i (hD i).1 (hD i).2,
    fun i => D.fundPerfect hp2 hq (fun j hj => absurd hj (hD j).2) i⟩

@[expose] def PerpTable (p : ℕ) [Fact p.Prime] {P : Type} (rel : P → P → Prop)
    (tY : StatedLieTag) (nY : ℕ) : Prop :=
  ∀ (t : StatedLieTag) (n e : ℕ), IsFundTag t → StatedLieAdmissible t n p e →
    ∀ k : (modelUniv t n p e Fact.out).K, k ≠ 1 →
      k ^ 2 ∈ Subgroup.center (modelUniv t n p e Fact.out).K →
      (∃ R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, k ∈ R₀) →
      ∀ φ : {R : Subgroup (modelUniv t n p e Fact.out).K //
          R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D ∧
            R ≤ Subgroup.centralizer ({k} : Set (modelUniv t n p e Fact.out).K)} ≃ P,
        (∀ R R', Commutes R.1 R'.1 ↔ rel (φ R) (φ R')) → t = tY ∧ n = nY

theorem PerpTable.of_equiv {P P' : Type} {rel : P → P → Prop} {rel' : P' → P' → Prop}
    {tY : StatedLieTag} {nY : ℕ} (h : PerpTable p rel tY nY) (e : P ≃ P')
    (he : ∀ a b, rel a b ↔ rel' (e a) (e b)) : PerpTable p rel' tY nY := by
  intro t n e' ht hadm k hk1 hk2 hk φ hφ
  refine h t n e' ht hadm k hk1 hk2 hk (φ.trans e.symm) fun R R' => ?_
  rw [hφ R R', he]
  simp

section Shape

variable [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem shape_of_perpTable (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    (hsc : ∀ i, FundamentalSingleClass (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    (hperf : ∀ i, FundPerfect (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    {K : Subgroup G} (hK : K ∈ centralizingMembers Ω {x}) {z : G}
    (hz : IsClassicalMember p f K z)
    (hlink : ∀ R ∈ centralizingMembers Ω {x, z}, Linked Ω x K R)
    {P : Type} (rel : P → P → Prop) (φP : {N : Subgroup G // N ∈ centralizingMembers Ω {x, z}} ≃ P)
    (hφP : ∀ N N', Commutes N.1 N'.1 ↔ rel (φP N) (φP N'))
    {tY : StatedLieTag} {nY : ℕ} (hTable : PerpTable p rel tY nY) :
    D.card = 1 ∧ ∃ i₁ : Fin D.card, D.tag i₁ = tY ∧ D.rank i₁ = nY ∧
      ∃ R : Subgroup (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K,
        Corr Ω x D i₁ K R := by
  have hcard : D.card = 1 := card_eq_one_of_linked hΩ hex hP1 D hK hz.mem hlink
  obtain ⟨i₁, R₀, hR₀⟩ := exists_corr_of_mem hΩ hex D hK
  refine ⟨hcard, i₁, ?_⟩
  have hKc : K ∈ compMembers Ω x D i₁ := ⟨hK, hR₀.2.2 ▸ Subgroup.map_le_range _ _⟩
  obtain ⟨k, hkR, hk⟩ := exists_model_elt hR₀ hz.mem
  obtain ⟨e, he⟩ := visible_equiv_layer hΩ hex hP1 D (hsc i₁) (hperf i₁) hR₀ hz.mem hk
  have hsub : Subsingleton (Fin D.card) := Fin.subsingleton_iff_le_one.mpr hcard.le
  have hall : ∀ N ∈ centralizingMembers Ω {x}, N ∈ compMembers Ω x D i₁ := by
    intro N hN
    obtain ⟨j, hj⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
    exact ⟨hN, hsub.elim j i₁ ▸ hj⟩
  let ι : {N : Subgroup G // N ∈ centralizingMembers Ω {x, z}} ≃
      {N : compMembers Ω x D i₁ // N.1 ∈ centralizingMembers Ω {x, z}} :=
    { toFun := fun N => ⟨⟨N.1, hall N.1 (mem_centralizingMembers_pair.mp N.2).1⟩, N.2⟩
      invFun := fun N => ⟨N.1.1, N.2⟩
      left_inv := fun N => rfl
      right_inv := fun N => rfl }
  have hk2 : k ^ 2 ∈ Subgroup.center
      (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K := by
    refine D.ker_le_center i₁ ?_
    rw [MonoidHom.mem_ker, map_pow, hk]
    have hzz : z * z = 1 := by
      rw [← pow_two]
      have := pow_orderOf_eq_one z
      rwa [hz.orderOf_eq_two] at this
    have : (⟨z, le_centralizingLayer hK hz.mem⟩ : ↥(locLayer Ω x)) ^ 2 = 1 :=
      Subtype.ext (by rw [pow_two]; exact hzz)
    rw [← map_pow, this, map_one]
  have hk1 : k ≠ 1 := by
    rintro rfl
    set zY : ↥(locLayer Ω x) := ⟨z, le_centralizingLayer hK hz.mem⟩ with hzYdef
    have hzY : zY ∈ classicalInvolutionOddCore ↥(locLayer Ω x) := by
      rw [← QuotientGroup.eq_one_iff]
      exact hk.symm.trans (map_one _)
    have h2 : orderOf zY = 2 := by
      rw [hzYdef, Subgroup.orderOf_mk]; exact hz.orderOf_eq_two
    have h3 : orderOf (⟨zY, hzY⟩ : classicalInvolutionOddCore ↥(locLayer Ω x)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact h2
    have h4 := orderOf_dvd_natCard (⟨zY, hzY⟩ : classicalInvolutionOddCore ↥(locLayer Ω x))
    rw [h3] at h4
    exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card _))
      (even_iff_two_dvd.mpr h4)
  let ι2 := Equiv.subtypeSubtypeEquivSubtypeInter
    (fun R : Subgroup (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K =>
      R ∈ compFund D i₁) (fun R => R ≤ Subgroup.centralizer ({k} : Set _))
  let φ := ι2.symm.trans (e.symm.trans (ι.symm.trans φP))
  have hφ : ∀ R R', Commutes R.1 R'.1 ↔ rel (φ R) (φ R') := by
    intro R R'
    have h1 := he (e.symm (ι2.symm R)) (e.symm (ι2.symm R'))
    have h2 := hφP (ι.symm (e.symm (ι2.symm R))) (ι.symm (e.symm (ι2.symm R')))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
    exact h1.symm.trans h2
  obtain ⟨ht, hn⟩ := hTable (D.tag i₁) (D.rank i₁) (D.exp i₁) (D.isFundTag i₁)
    (D.admissible i₁) k hk1 hk2 ⟨R₀, hR₀.2.1, hkR⟩ φ hφ
  exact ⟨ht, hn, R₀, hR₀⟩

theorem localShapeT_zero_of_perpTable (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    (hsc : ∀ i, FundamentalSingleClass (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    (hperf : ∀ i, FundPerfect (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    {K : Subgroup G} (hK : K ∈ centralizingMembers Ω {x}) {z : G}
    (hz : IsClassicalMember p f K z)
    (hlink : ∀ R ∈ centralizingMembers Ω {x, z}, Linked Ω x K R)
    {P : Type} (rel : P → P → Prop) (φP : {N : Subgroup G // N ∈ centralizingMembers Ω {x, z}} ≃ P)
    (hφP : ∀ N N', Commutes N.1 N'.1 ↔ rel (φP N) (φP N'))
    {tY : StatedLieTag} {nY : ℕ} (hTable : PerpTable p rel tY nY) :
    LocalShapeT p f 0 tY nY Ω x := by
  obtain ⟨hcard, i₁, ht, hn, -⟩ :=
    shape_of_perpTable hΩ hex hP1 D hsc hperf hK hz hlink rel φP hφP hTable
  have := localShapeT_zero_of_card_eq_one D hcard i₁
  rwa [ht, hn] at this

end Shape

end CFSG.ClassicalInvolution.RouteD.NonClassical

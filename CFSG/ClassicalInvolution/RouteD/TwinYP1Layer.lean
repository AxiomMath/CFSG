module

public import CFSG.ClassicalInvolution.RouteD.ExoticShapes

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.Exotic
open scoped commutatorElement MatrixGroups

section Facts

variable {p f : ℕ} [Fact p.Prime]

private theorem exists_fund_of_eq {tY : StatedLieTag} {nY : ℕ} (t : StatedLieTag) (n e : ℕ)
    (ht : t = tY) (hn : n = nY) (he : e = f)
    {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) :
    ∃ R', R' ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D := by
  subst ht hn he
  exact ⟨R, hR⟩

structure TwinRowFacts (p f : ℕ) [Fact p.Prime] (tY : StatedLieTag) (nY : ℕ) : Prop where
  fsc : FundamentalSingleClass tY (modelUniv tY nY p f Fact.out).D
  perf : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D, R ≤ ⁅R, R⁆
  nonempty : ∃ R, R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D
  nc : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
    ∃ S ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D, S ≠ R ∧ ¬ Commutes S R

theorem LocalShapeT.twinRowFacts {G : Type} [Group G] {a : ℕ} {tY : StatedLieTag} {nY : ℕ}
    {Ω : Set (Subgroup G)} {x : G} (h : LocalShapeT p f a tY nY Ω x) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hG2 : tY ≠ .G2) (hD4 : tY ≠ .trialityD4)
    (hnA1 : ¬ (tY = .PSL ∧ nY = 2)) : TwinRowFacts p f tY nY := by
  obtain ⟨hfund, hadm⟩ := admissible_of_localShapeT h hD4
  have hfund' : CFSG.ClassicalInvolution.ModelFacts.IsFundTag tY := by
    cases tY <;> trivial
  have hq4 : 4 ≤ p ^ f := by omega
  refine ⟨CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass tY nY p f Fact.out hfund'
    hadm hG2 hD4, fundPerfect_modelUniv hp2 hfund hadm hq4, ?_,
    fun R hR => exists_fund_not_commuting hfund hadm hnA1 hR⟩
  obtain ⟨D, -, i₁, ht, hr, -⟩ := h
  have hexp : D.exp i₁ = f := by
    rcases D.exp_eq i₁ with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h
      exact absurd h hD4
  obtain ⟨R, hR, -⟩ := D.meets i₁
  exact exists_fund_of_eq _ _ _ ht hr hexp hR

end Facts

section Members

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  {tY : StatedLieTag} {nY : ℕ}

omit [Finite G] in
theorem members_cases (d : ShapeDictT2 p f tY nY Ω z) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {z}) :
    locImg Ω z L ≤ d.Q₀ ∨ locImg Ω z L ≤ d.Q₁ ∨
      ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
        locImg Ω z L = R.map d.ψ :=
  d.fam_cases _ (mem_locFamily_iff.mpr ⟨L, hL, rfl⟩)

theorem eq_of_le_Q (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {z})
    {Q : Subgroup (locQuot Ω z)} (hQ : Nat.card Q ≤ Nat.card SL(2, GaloisField p f))
    {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) (h : locImg Ω z L ≤ Q) (h' : locImg Ω z L' ≤ Q) :
    L = L' := by
  have e1 : locImg Ω z L = Q :=
    Subgroup.eq_of_le_of_card_ge h (by rw [card_locImg hΩ hex hL]; exact hQ)
  have e2 : locImg Ω z L' = Q :=
    Subgroup.eq_of_le_of_card_ge h' (by rw [card_locImg hΩ hex hL']; exact hQ)
  exact locImg_injOn hΩ hP1 hL hL' (e1.trans e2.symm)

theorem commutes_iff_fund (hΩ : InClass p f Ω) (hP1 : LocalOddCentral Ω {z})
    (rf : TwinRowFacts p f tY nY) (d : ShapeDictT2 p f tY nY Ω z) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {z}) (hL' : L' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hLR : locImg Ω z L = R.map d.ψ) (hLR' : locImg Ω z L' = R'.map d.ψ) :
    Commutes L L' ↔ Commutes R R' := by
  constructor
  · intro h
    have h1 := commutes_locImg_of_commutes (x := z) (Ω := Ω) h
    rw [hLR, hLR'] at h1
    exact commutes_of_commutes_map d.ψ d.ker_le (perfect_of_le_commutator (rf.perf R hR)) h1
  · intro h
    refine commutes_of_commutes_locImg hΩ hP1 hL hL' ?_
    rw [hLR, hLR']
    exact commutes_map _ h

theorem not_isolated_of_fund (hΩ : InClass p f Ω) (hP1 : LocalOddCentral Ω {z})
    (rf : TwinRowFacts p f tY nY) (d : ShapeDictT2 p f tY nY Ω z) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {z})
    {R : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (h : locImg Ω z L = R.map d.ψ) :
    ∃ L' ∈ centralizingMembers Ω {z}, L' ≠ L ∧ ¬ Commutes L L' := by
  obtain ⟨S', hS', hne, hnc⟩ := rf.nc R hR
  obtain ⟨L', hL', hL'S⟩ := mem_locFamily_iff.mp (d.mem_fam S' hS')
  refine ⟨L', hL', ?_, fun hc => hnc (commutes_symm ?_)⟩
  · rintro rfl
    exact hne (eq_of_map_eq_of_central d.ψ d.ker_le (rf.perf S' hS') (rf.perf R hR)
      (hL'S.symm.trans h))
  · exact (commutes_iff_fund hΩ hP1 rf d hL hL' hR h hL'S).mp hc

theorem not_fund_of_isolated (hΩ : InClass p f Ω) (hP1 : LocalOddCentral Ω {z})
    (rf : TwinRowFacts p f tY nY) (d : ShapeDictT2 p f tY nY Ω z) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {z})
    (hiso : ∀ L' ∈ centralizingMembers Ω {z}, L' ≠ L → Commutes L L')
    {R : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (h : locImg Ω z L = R.map d.ψ) : False := by
  obtain ⟨S', hS', hne, hnc⟩ := rf.nc R hR
  obtain ⟨L', hL', hL'S⟩ := mem_locFamily_iff.mp (d.mem_fam S' hS')
  have hLL' : L' ≠ L := by
    rintro rfl
    exact hne (eq_of_map_eq_of_central d.ψ d.ker_le (rf.perf S' hS') (rf.perf R hR)
      (hL'S.symm.trans h))
  exact hnc (commutes_symm ((commutes_iff_fund hΩ hP1 rf d hL hL' hR h hL'S).mp
    (hiso L' hL' hLL')))

theorem big_of_ne (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {z})
    (rf : TwinRowFacts p f tY nY) (d : ShapeDictT2 p f tY nY Ω z) {K T L : Subgroup G}
    (hK : K ∈ centralizingMembers Ω {z}) (hT : T ∈ centralizingMembers Ω {z}) (hKT : K ≠ T)
    (hKiso : ∀ L' ∈ centralizingMembers Ω {z}, L' ≠ K → Commutes K L')
    (hTiso : ∀ L' ∈ centralizingMembers Ω {z}, L' ≠ T → Commutes T L')
    (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) (hLT : L ≠ T) :
    ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      locImg Ω z L = R.map d.ψ := by
  have h0 : locImg Ω z L ≤ d.Q₀ → False := by
    intro hLQ
    have hK' : ¬ locImg Ω z K ≤ d.Q₀ := fun h => hLK (eq_of_le_Q hΩ hex hP1 d.card_le₀ hL hK hLQ h)
    have hT' : ¬ locImg Ω z T ≤ d.Q₀ := fun h => hLT (eq_of_le_Q hΩ hex hP1 d.card_le₀ hL hT hLQ h)
    rcases members_cases d hK with hk0 | hk1 | ⟨R, hR, hkR⟩
    · exact hK' hk0
    · rcases members_cases d hT with ht0 | ht1 | ⟨R, hR, htR⟩
      · exact hT' ht0
      · exact hKT (eq_of_le_Q hΩ hex hP1 d.card_le₁ hK hT hk1 ht1)
      · exact not_fund_of_isolated hΩ hP1 rf d hT hTiso hR htR
    · exact not_fund_of_isolated hΩ hP1 rf d hK hKiso hR hkR
  have h1 : locImg Ω z L ≤ d.Q₁ → False := by
    intro hLQ
    have hK' : ¬ locImg Ω z K ≤ d.Q₁ := fun h => hLK (eq_of_le_Q hΩ hex hP1 d.card_le₁ hL hK hLQ h)
    have hT' : ¬ locImg Ω z T ≤ d.Q₁ := fun h => hLT (eq_of_le_Q hΩ hex hP1 d.card_le₁ hL hT hLQ h)
    rcases members_cases d hK with hk0 | hk1 | ⟨R, hR, hkR⟩
    · rcases members_cases d hT with ht0 | ht1 | ⟨R, hR, htR⟩
      · exact hKT (eq_of_le_Q hΩ hex hP1 d.card_le₀ hK hT hk0 ht0)
      · exact hT' ht1
      · exact not_fund_of_isolated hΩ hP1 rf d hT hTiso hR htR
    · exact hK' hk1
    · exact not_fund_of_isolated hΩ hP1 rf d hK hKiso hR hkR
  rcases members_cases d hL with h | h | h
  · exact (h0 h).elim
  · exact (h1 h).elim
  · exact h

theorem exists_noncomm_of_ne (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {z}) (rf : TwinRowFacts p f tY nY) (d : ShapeDictT2 p f tY nY Ω z)
    {K T L : Subgroup G} (hK : K ∈ centralizingMembers Ω {z})
    (hT : T ∈ centralizingMembers Ω {z}) (hKT : K ≠ T)
    (hKiso : ∀ L' ∈ centralizingMembers Ω {z}, L' ≠ K → Commutes K L')
    (hTiso : ∀ L' ∈ centralizingMembers Ω {z}, L' ≠ T → Commutes T L')
    (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) (hLT : L ≠ T) :
    ∃ L' ∈ centralizingMembers Ω {z}, L' ≠ L ∧ ¬ Commutes L L' := by
  obtain ⟨R, hR, hLR⟩ := big_of_ne hΩ hex hP1 rf d hK hT hKT hKiso hTiso hL hLK hLT
  exact not_isolated_of_fund hΩ hP1 rf d hL hR hLR

theorem link_big (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {z})
    (rf : TwinRowFacts p f tY nY) (d : ShapeDictT2 p f tY nY Ω z) {K T L L' : Subgroup G}
    (hK : K ∈ centralizingMembers Ω {z}) (hT : T ∈ centralizingMembers Ω {z}) (hKT : K ≠ T)
    (hKiso : ∀ L'' ∈ centralizingMembers Ω {z}, L'' ≠ K → Commutes K L'')
    (hTiso : ∀ L'' ∈ centralizingMembers Ω {z}, L'' ≠ T → Commutes T L'')
    (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) (hLT : L ≠ T)
    (hL' : L' ∈ centralizingMembers Ω {z}) (hL'K : L' ≠ K) (hL'T : L' ≠ T) :
    ∃ y : G, y ∈ locLayer Ω z ∧ conjSub y L = L' := by
  obtain ⟨R, hR, hLR⟩ := big_of_ne hΩ hex hP1 rf d hK hT hKT hKiso hTiso hL hLK hLT
  obtain ⟨R', hR', hLR'⟩ := big_of_ne hΩ hex hP1 rf d hK hT hKT hKiso hTiso hL' hL'K hL'T
  obtain ⟨g, hg⟩ := rf.fsc R hR R' hR'
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (d.ψ g)
  have hyx : (y : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    centralizingLayer_le_centralizer Ω {z} y.2
  have hconj : conjSub (y : G) L ∈ centralizingMembers Ω {z} := by
    refine ⟨hΩ.conjInvariant _ L hL.1, fun a ha => ?_⟩
    rw [mem_conjSub_iff] at ha
    have hx' := hL.2 ha
    have : a = (y : G) * ((y : G)⁻¹ * a * (y : G)) * (y : G)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyx hx') ((Subgroup.inv_mem _) hyx)
  refine ⟨(y : G), y.2, locImg_injOn hΩ hP1 hconj hL' ?_⟩
  rw [locImg_conjSub_layer, hLR, hLR', show locMk Ω z y = d.ψ g from hy, hg]
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp

omit [Finite G] in
theorem exists_big_member_aux (rf : TwinRowFacts p f tY nY) (d : ShapeDictT2 p f tY nY Ω z) :
    ∃ J ∈ centralizingMembers Ω {z}, ∃ R ∈ fundamentalSubgroups tY
      (modelUniv tY nY p f Fact.out).D, locImg Ω z J = R.map d.ψ := by
  obtain ⟨R, hR⟩ := rf.nonempty
  obtain ⟨J, hJ, hJR⟩ := mem_locFamily_iff.mp (d.mem_fam R hR)
  exact ⟨J, hJ, R, hR, hJR⟩

theorem exists_big_member (hΩ : InClass p f Ω) (hP1 : LocalOddCentral Ω {z})
    (rf : TwinRowFacts p f tY nY) (d : ShapeDictT2 p f tY nY Ω z) {K T : Subgroup G}
    (hKiso : ∀ L' ∈ centralizingMembers Ω {z}, L' ≠ K → Commutes K L')
    (hTiso : ∀ L' ∈ centralizingMembers Ω {z}, L' ≠ T → Commutes T L') :
    ∃ J ∈ centralizingMembers Ω {z}, J ≠ K ∧ J ≠ T := by
  obtain ⟨J, hJ, R, hR, hJR⟩ := exists_big_member_aux rf d
  refine ⟨J, hJ, fun h => ?_, fun h => ?_⟩
  · subst h
    exact not_fund_of_isolated hΩ hP1 rf d hJ hKiso hR hJR
  · subst h
    exact not_fund_of_isolated hΩ hP1 rf d hJ hTiso hR hJR

end Members

end CFSG.ClassicalInvolution.RouteD.TwinY

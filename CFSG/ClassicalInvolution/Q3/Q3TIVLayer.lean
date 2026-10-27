module

public import CFSG.ClassicalInvolution.Q3.Q3TIVDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIV

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TP
open scoped MatrixGroups commutatorElement


structure TwinLoc3 (tY : StatedLieTag) (nY : ℕ) {G : Type} [Group G] (Ω : Set (Subgroup G))
    (z : G) where
  hΩ : InClass3 Ω
  hex : ExactMembers3 Ω
  hP1 : LocalOddCentral Ω {z}
  hO3 : LocalOddThreeFree3 Ω z
  rf : TwinRowFacts3 tY nY
  d : ShapeDictT2 3 1 tY nY Ω z

namespace TwinLoc3

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag} {nY : ℕ}
  (c : TwinLoc3 tY nY Ω z)

include c

theorem ker_cop : ∀ n ∈ c.d.ψ.ker, ¬ 3 ∣ orderOf n := fun n hn => c.rf.y.cop n (c.d.ker_le hn)

theorem card_Q₀_le : Nat.card c.d.Q₀ ≤ 24 := by
  have h := c.d.card_le₀
  rwa [card_sl2_gf3] at h

theorem card_Q₁_le : Nat.card c.d.Q₁ ≤ 24 := by
  have h := c.d.card_le₁
  rwa [card_sl2_gf3] at h

variable [Finite G]

theorem eq_of_le_Q {Q : Subgroup (locQuot Ω z)} (hQ : Nat.card Q ≤ 24) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {z}) (hL' : L' ∈ centralizingMembers Ω {z})
    (h : locImg Ω z L ≤ Q) (h' : locImg Ω z L' ≤ Q) : L = L' := by
  have hcL := card_locImg3 c.hΩ c.hex hL
  have hcL' := card_locImg3 c.hΩ c.hex hL'
  have e1 : locImg Ω z L = Q := Subgroup.eq_of_le_of_card_ge h (by rw [hcL]; exact hQ)
  have e2 : locImg Ω z L' = Q := Subgroup.eq_of_le_of_card_ge h' (by rw [hcL']; exact hQ)
  exact locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hL hL' (e1.trans e2.symm)

omit [Finite G] in
theorem members_cases {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) :
    locImg Ω z L ≤ c.d.Q₀ ∨ locImg Ω z L ≤ c.d.Q₁ ∨
      ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
        locImg Ω z L = R.map c.d.ψ :=
  c.d.fam_cases _ (mem_locFamily_iff.mpr ⟨L, hL, rfl⟩)

omit [Finite G] in
theorem commutes_of_commutes_map {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (h : Commutes (R.map c.d.ψ) (R'.map c.d.ψ)) : Commutes R R' := by
  intro a ha b hb
  exact (commutes_of_map_commute_exponent3 c.d.ψ (hker := c.d.ker_le) c.ker_cop
    (A := R') (L := R) (c.rf.y.pow3 R hR)
    (fun a' ha' l' hl' => (h _ ⟨l', hl', rfl⟩ _ ⟨a', ha', rfl⟩).symm) b hb a ha).symm

theorem commutes_iff_fund {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ) :
    Commutes L L' ↔ Commutes R R' := by
  constructor
  · intro h
    have h1 := commutes_locImg_of_commutes (x := z) (Ω := Ω) h
    rw [hLR, hLR'] at h1
    exact c.commutes_of_commutes_map hR h1
  · intro h
    refine commutes_of_commutes_locImg3 c.hΩ c.hex c.hP1 c.hO3 hL hL' ?_
    rw [hLR, hLR']
    exact commutes_map_of_commutes _ h

theorem not_isolated_of_fund {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (h : locImg Ω z L = R.map c.d.ψ) :
    ∃ L' ∈ centralizingMembers Ω {z}, L' ≠ L ∧ ¬ Commutes L L' := by
  obtain ⟨S', hS', hne, hnc⟩ := c.rf.nc R hR
  obtain ⟨L', hL', hL'S⟩ := mem_locFamily_iff.mp (c.d.mem_fam S' hS')
  refine ⟨L', hL', ?_, fun hc => hnc (Commutes.symm ?_)⟩
  · rintro rfl
    exact hne (eq_of_map_eq_of_pow3 c.d.ψ c.d.ker_le c.ker_cop (c.rf.y.pow3 S' hS')
      (c.rf.y.pow3 R hR) (hL'S.symm.trans h))
  · exact (c.commutes_iff_fund hL hL' hR h hL'S).mp hc

theorem not_fund_of_isolated {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hiso : ∀ L' ∈ centralizingMembers Ω {z}, L' ≠ L → Commutes L L')
    {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (h : locImg Ω z L = R.map c.d.ψ) : False := by
  obtain ⟨S', hS', hne, hnc⟩ := c.rf.nc R hR
  obtain ⟨L', hL', hL'S⟩ := mem_locFamily_iff.mp (c.d.mem_fam S' hS')
  have hLL' : L' ≠ L := by
    rintro rfl
    exact hne (eq_of_map_eq_of_pow3 c.d.ψ c.d.ker_le c.ker_cop (c.rf.y.pow3 S' hS')
      (c.rf.y.pow3 R hR) (hL'S.symm.trans h))
  exact hnc (Commutes.symm ((c.commutes_iff_fund hL hL' hR h hL'S).mp (hiso L' hL' hLL')))

theorem big_of_ne {K T L : Subgroup G} (hK : K ∈ centralizingMembers Ω {z})
    (hT : T ∈ centralizingMembers Ω {z}) (hKT : K ≠ T)
    (hKiso : ∀ L' ∈ centralizingMembers Ω {z}, L' ≠ K → Commutes K L')
    (hTiso : ∀ L' ∈ centralizingMembers Ω {z}, L' ≠ T → Commutes T L')
    (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) (hLT : L ≠ T) :
    ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      locImg Ω z L = R.map c.d.ψ := by
  have h0 : locImg Ω z L ≤ c.d.Q₀ → False := by
    intro hLQ
    have hK' : ¬ locImg Ω z K ≤ c.d.Q₀ := fun h => hLK (c.eq_of_le_Q c.card_Q₀_le hL hK hLQ h)
    have hT' : ¬ locImg Ω z T ≤ c.d.Q₀ := fun h => hLT (c.eq_of_le_Q c.card_Q₀_le hL hT hLQ h)
    rcases c.members_cases hK with hk0 | hk1 | ⟨R, hR, hkR⟩
    · exact hK' hk0
    · rcases c.members_cases hT with ht0 | ht1 | ⟨R, hR, htR⟩
      · exact hT' ht0
      · exact hKT (c.eq_of_le_Q c.card_Q₁_le hK hT hk1 ht1)
      · exact c.not_fund_of_isolated hT hTiso hR htR
    · exact c.not_fund_of_isolated hK hKiso hR hkR
  have h1 : locImg Ω z L ≤ c.d.Q₁ → False := by
    intro hLQ
    have hK' : ¬ locImg Ω z K ≤ c.d.Q₁ := fun h => hLK (c.eq_of_le_Q c.card_Q₁_le hL hK hLQ h)
    have hT' : ¬ locImg Ω z T ≤ c.d.Q₁ := fun h => hLT (c.eq_of_le_Q c.card_Q₁_le hL hT hLQ h)
    rcases c.members_cases hK with hk0 | hk1 | ⟨R, hR, hkR⟩
    · rcases c.members_cases hT with ht0 | ht1 | ⟨R, hR, htR⟩
      · exact hKT (c.eq_of_le_Q c.card_Q₀_le hK hT hk0 ht0)
      · exact hT' ht1
      · exact c.not_fund_of_isolated hT hTiso hR htR
    · exact hK' hk1
    · exact c.not_fund_of_isolated hK hKiso hR hkR
  rcases c.members_cases hL with h | h | h
  · exact (h0 h).elim
  · exact (h1 h).elim
  · exact h

theorem exists_noncomm_of_ne {K T L : Subgroup G} (hK : K ∈ centralizingMembers Ω {z})
    (hT : T ∈ centralizingMembers Ω {z}) (hKT : K ≠ T)
    (hKiso : ∀ L' ∈ centralizingMembers Ω {z}, L' ≠ K → Commutes K L')
    (hTiso : ∀ L' ∈ centralizingMembers Ω {z}, L' ≠ T → Commutes T L')
    (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) (hLT : L ≠ T) :
    ∃ L' ∈ centralizingMembers Ω {z}, L' ≠ L ∧ ¬ Commutes L L' := by
  obtain ⟨R, hR, hLR⟩ := c.big_of_ne hK hT hKT hKiso hTiso hL hLK hLT
  exact c.not_isolated_of_fund hL hR hLR

theorem link_big {K T L L' : Subgroup G} (hK : K ∈ centralizingMembers Ω {z})
    (hT : T ∈ centralizingMembers Ω {z}) (hKT : K ≠ T)
    (hKiso : ∀ L'' ∈ centralizingMembers Ω {z}, L'' ≠ K → Commutes K L'')
    (hTiso : ∀ L'' ∈ centralizingMembers Ω {z}, L'' ≠ T → Commutes T L'')
    (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) (hLT : L ≠ T)
    (hL' : L' ∈ centralizingMembers Ω {z}) (hL'K : L' ≠ K) (hL'T : L' ≠ T) :
    ∃ y : G, y ∈ locLayer Ω z ∧ conjSub y L = L' := by
  obtain ⟨R, hR, hLR⟩ := c.big_of_ne hK hT hKT hKiso hTiso hL hLK hLT
  obtain ⟨R', hR', hLR'⟩ := c.big_of_ne hK hT hKT hKiso hTiso hL' hL'K hL'T
  obtain ⟨g, hg⟩ := c.rf.y.sc R hR R' hR'
  have hg' : R' = R.map (MulAut.conj g).toMonoidHom := hg
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (c.d.ψ g)
  have hyx : (y : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    centralizingLayer_le_centralizer Ω {z} y.2
  have hconj : conjSub (y : G) L ∈ centralizingMembers Ω {z} := by
    refine ⟨c.hΩ.conjInvariant _ L hL.1, fun a ha => ?_⟩
    rw [mem_conjSub_iff] at ha
    have hx' := hL.2 ha
    have : a = (y : G) * ((y : G)⁻¹ * a * (y : G)) * (y : G)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyx hx') ((Subgroup.inv_mem _) hyx)
  refine ⟨(y : G), y.2, locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hconj hL' ?_⟩
  rw [Gaps.locImg_conjSub_layer, hLR, hLR', show Gaps.locMk Ω z y = c.d.ψ g from hy, hg']
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp

theorem exists_big_member {K T : Subgroup G}
    (hKiso : ∀ L' ∈ centralizingMembers Ω {z}, L' ≠ K → Commutes K L')
    (hTiso : ∀ L' ∈ centralizingMembers Ω {z}, L' ≠ T → Commutes T L') :
    ∃ J ∈ centralizingMembers Ω {z}, J ≠ K ∧ J ≠ T := by
  obtain ⟨R, hR⟩ := c.rf.nonempty
  obtain ⟨J, hJ, hJR⟩ := mem_locFamily_iff.mp (c.d.mem_fam R hR)
  refine ⟨J, hJ, fun h => ?_, fun h => ?_⟩
  · subst h
    exact c.not_fund_of_isolated hJ hKiso hR hJR
  · subst h
    exact c.not_fund_of_isolated hJ hTiso hR hJR

end TwinLoc3

theorem TwinLoc3.of_setup {tY : StatedLieTag} {nY : ℕ} (rf : TwinRowFacts3 tY nY)
    (h3 : OddThreeFreeInput) {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G}
    {z : G} (hR : RouteD3Setup K z)
    (hshape : LocalShapeC3 2 (CompData.model tY nY) (conjClass3 K) z) :
    Nonempty (TwinLoc3 tY nY (conjClass3 K) z) := by
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨d⟩ := Q3TC.LocalShapeC3.nonempty_dictT2 rf.y.sc hR.inClass hK hR.cls hshape
  exact ⟨{
    hΩ := hR.inClass
    hex := hR.setup.1
    hP1 := hR.setup.2
    hO3 := h3 G K z hR
    rf := rf
    d := d }⟩

end CFSG.ClassicalInvolution.Q3.Q3TIV

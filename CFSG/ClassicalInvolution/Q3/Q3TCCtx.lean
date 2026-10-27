module

public import CFSG.ClassicalInvolution.Q3.Q3TCDict
public import CFSG.ClassicalInvolution.Q3.Q3WARow
public import CFSG.ClassicalInvolution.Q3.Q3WANoA1

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TC

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement


theorem not_locImg_eq_map_fund3 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
    {tY : StatedLieTag} {nY : ℕ} (hY : YData3 tY nY) {K : Subgroup G}
    (hKz : K ∈ centralizingMembers Ω {z}) (hz : IsClassicalMember3 K z)
    (ψ : (modelUniv tY nY 3 1 Nat.prime_three).K →* locQuot Ω z)
    (hker : ψ.ker ≤ Subgroup.center _)
    {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (h : locImg Ω z K = R.map ψ) : False := by
  have hzY : z ∈ locLayer Ω z := le_centralizingLayer hKz hz.mem
  have hzK : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) ⟨z, hzY⟩ ∈
      locImg Ω z K := ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩
  rw [h] at hzK
  obtain ⟨r, hrR, hr⟩ := hzK
  have hrc : r ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K := by
    have := hY.perfK
    refine mem_center_of_comm_mem_center fun s => hker ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, hr]
    rw [commutatorElement_def, ← mk_involution_central3 Ω z hzY (ψ s), mul_inv_cancel_right,
      mul_inv_cancel]
  have hr1 : r = 1 := hY.central R hR r hrR hrc
  rw [hr1, map_one] at hr
  exact mk_involution_ne_one3 Ω hz.orderOf_eq_two hzY hr.symm

theorem exists_dictT2_of_member3 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
    {tY : StatedLieTag} {nY : ℕ} (hY : YData3 tY nY) {K : Subgroup G} (hK : K ∈ Ω)
    (hz : IsClassicalMember3 K z) (d : ShapeDictT2 3 1 tY nY Ω z) :
    ∃ d' : ShapeDictT2 3 1 tY nY Ω z, locImg Ω z K ≤ d'.Q₀ := by
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, isSubnormal_le hz.subnormal⟩
  have hmem : locImg Ω z K ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨K, hKz, rfl⟩
  rcases d.fam_cases _ hmem with h | h | ⟨R, hR, hRK⟩
  · exact ⟨d, h⟩
  · exact ⟨d.swap, h⟩
  · exact (not_locImg_eq_map_fund3 hY hKz hz d.ψ d.ker_le hR hRK).elim

structure TCtx3 (tY : StatedLieTag) (nY : ℕ) {G : Type} [Group G] (Ω : Set (Subgroup G))
    (K : Subgroup G) (z : G) where
  hΩ : InClass3 Ω
  hex : ExactMembers3 Ω
  hK : K ∈ Ω
  hz : IsClassicalMember3 K z
  hP1 : LocalOddCentral Ω {z}
  hO3 : LocalOddThreeFree3 Ω z
  d : ShapeDictT2 3 1 tY nY Ω z
  hQ₀ : locImg Ω z K ≤ d.Q₀
  hY : YData3 tY nY

namespace TCtx3

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag} {nY : ℕ}
  {K : Subgroup G} (c : TCtx3 tY nY Ω K z)

include c

theorem hKz : K ∈ centralizingMembers Ω {z} := ⟨c.hK, isSubnormal_le c.hz.subnormal⟩

theorem ker_cop : ∀ n ∈ c.d.ψ.ker, ¬ 3 ∣ orderOf n := fun n hn => c.hY.cop n (c.d.ker_le hn)

variable [Finite G]

theorem eq_of_locImg_le_Q₀ {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hLQ : locImg Ω z L ≤ c.d.Q₀) : L = K := by
  have hcL := card_locImg3 c.hΩ c.hex hL
  have hcK := card_locImg3 c.hΩ c.hex c.hKz
  have hcard := c.d.card_le₀
  rw [card_sl2_gf3] at hcard
  have e1 : locImg Ω z L = c.d.Q₀ := Subgroup.eq_of_le_of_card_ge hLQ (by rw [hcL]; exact hcard)
  have e2 : locImg Ω z K = c.d.Q₀ :=
    Subgroup.eq_of_le_of_card_ge c.hQ₀ (by rw [hcK]; exact hcard)
  exact locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hL c.hKz (e1.trans e2.symm)

theorem eq_of_locImg_le_Q₁ {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) (h : locImg Ω z L ≤ c.d.Q₁)
    (h' : locImg Ω z L' ≤ c.d.Q₁) : L = L' := by
  have hcL := card_locImg3 c.hΩ c.hex hL
  have hcL' := card_locImg3 c.hΩ c.hex hL'
  have hcard := c.d.card_le₁
  rw [card_sl2_gf3] at hcard
  have e1 : locImg Ω z L = c.d.Q₁ := Subgroup.eq_of_le_of_card_ge h (by rw [hcL]; exact hcard)
  have e2 : locImg Ω z L' = c.d.Q₁ := Subgroup.eq_of_le_of_card_ge h' (by rw [hcL']; exact hcard)
  exact locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hL hL' (e1.trans e2.symm)

omit [Finite G] in
theorem exists_twin : ∃ T ∈ centralizingMembers Ω {z}, locImg Ω z T = c.d.Q₁ :=
  mem_locFamily_iff.mp c.d.mem₁

theorem twin_ne {T : Subgroup G} (hT : T ∈ centralizingMembers Ω {z})
    (hTQ : locImg Ω z T ≤ c.d.Q₁) : T ≠ K := by
  intro hTK
  subst hTK
  have h1 : Commutes (locImg Ω z T) (locImg Ω z T) := fun a ha b hb =>
    c.d.comm₀₁ a (c.hQ₀ ha) b (hTQ hb)
  exact not_commutes_self3 c.hz (commutes_of_commutes_locImg3 c.hΩ c.hex c.hP1 c.hO3 hT hT h1)

theorem exists_fund_of_ne {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K)
    (hLQ : ¬ locImg Ω z L ≤ c.d.Q₁) :
    ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      locImg Ω z L = R.map c.d.ψ := by
  have hmem : locImg Ω z L ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨L, hL, rfl⟩
  rcases c.d.fam_cases _ hmem with h | h | h
  · exact absurd (c.eq_of_locImg_le_Q₀ hL h) hLK
  · exact absurd h hLQ
  · exact h

theorem exists_member_of_fund {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D) :
    ∃ L ∈ centralizingMembers Ω {z}, L ≠ K ∧ ¬ locImg Ω z L ≤ c.d.Q₁ ∧
      locImg Ω z L = R.map c.d.ψ := by
  obtain ⟨L, hL, hLR⟩ := mem_locFamily_iff.mp (c.d.mem_fam R hR)
  have hne : ∀ Q : Subgroup (locQuot Ω z), Commutes Q c.d.ψ.range → locImg Ω z L ≤ Q → False := by
    intro Q hQ hLQ
    have h1 : Commutes (locImg Ω z L) (locImg Ω z L) := by
      intro a ha b hb
      have hb' : b ∈ c.d.ψ.range := by
        rw [hLR] at hb
        obtain ⟨x, _, rfl⟩ := hb
        exact ⟨x, rfl⟩
      exact hQ a (hLQ ha) b hb'
    obtain ⟨zL, hzL⟩ := c.hΩ.classical L hL.1
    exact not_commutes_self3 hzL (commutes_of_commutes_locImg3 c.hΩ c.hex c.hP1 c.hO3 hL hL h1)
  refine ⟨L, hL, fun hLK => ?_, fun hLQ => hne _ c.d.comm₁ hLQ, hLR⟩
  subst hLK
  exact hne _ c.d.comm₀ c.hQ₀

theorem commutes_K_of_ne {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) :
    Commutes K L := by
  have hmem : locImg Ω z L ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨L, hL, rfl⟩
  refine commutes_of_commutes_locImg3 c.hΩ c.hex c.hP1 c.hO3 c.hKz hL ?_
  intro a ha b hb
  rcases c.d.fam_cases _ hmem with h | h | ⟨R, hR, hLR⟩
  · exact absurd (c.eq_of_locImg_le_Q₀ hL h) hLK
  · exact c.d.comm₀₁ a (c.hQ₀ ha) b (h hb)
  · rw [hLR] at hb
    exact c.d.comm₀ a (c.hQ₀ ha) b (by obtain ⟨x, _, rfl⟩ := hb; exact ⟨x, rfl⟩)

theorem commutes_T_of_ne {T L : Subgroup G} (hT : T ∈ centralizingMembers Ω {z})
    (hTQ : locImg Ω z T ≤ c.d.Q₁) (hL : L ∈ centralizingMembers Ω {z}) (hLT : L ≠ T) :
    Commutes T L := by
  have hmem : locImg Ω z L ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨L, hL, rfl⟩
  refine commutes_of_commutes_locImg3 c.hΩ c.hex c.hP1 c.hO3 hT hL ?_
  intro a ha b hb
  rcases c.d.fam_cases _ hmem with h | h | ⟨R, hR, hLR⟩
  · exact (c.d.comm₀₁ b (h hb) a (hTQ ha)).symm
  · exact absurd (c.eq_of_locImg_le_Q₁ hL hT h hTQ) hLT
  · rw [hLR] at hb
    exact c.d.comm₁ a (hTQ ha) b (by obtain ⟨x, _, rfl⟩ := hb; exact ⟨x, rfl⟩)

theorem locLayer_le_normalizer : locLayer Ω z ≤ Subgroup.normalizer (K : Set G) := by
  refine iSup₂_le fun L hL => ?_
  by_cases hLK : L = K
  · subst hLK
    exact Subgroup.le_normalizer
  · refine le_trans (fun x hx => ?_) (Subgroup.centralizer_le_normalizer (K : Set G))
    exact Subgroup.mem_centralizer_iff.mpr fun k hk => c.commutes_K_of_ne hL hLK k hk x hx

theorem eq_of_locImg_eq {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) (h : locImg Ω z L = locImg Ω z L') : L = L' :=
  locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hL hL' h

omit [Finite G] in
theorem commutes_of_commutes_map {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (h : Commutes (R.map c.d.ψ) (R'.map c.d.ψ)) : Commutes R R' := by
  intro a ha b hb
  exact (commutes_of_map_commute_exponent3 c.d.ψ (hker := c.d.ker_le) c.ker_cop
    (A := R') (L := R) (c.hY.pow3 R hR)
    (fun a' ha' l hl => (h _ ⟨l, hl, rfl⟩ _ ⟨a', ha', rfl⟩).symm) b hb a ha).symm

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

theorem stdPair_of_fund {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z})
    {R R' W : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hW : LinearBlockStandardPair (GaloisField 3 1) W R R')
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ) :
    ∃ W' : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W' L L' := by
  have := linearBlockStandardPair_map_central hW c.d.ψ c.d.ker_le
  rw [← hLR, ← hLR'] at this
  exact linearBlockStandardPair_of_locImg3' c.hΩ c.hex c.hP1 c.hO3 hL hL' this

end TCtx3


theorem nonempty_tctx3 {tY : StatedLieTag} {nY : ℕ} (hY : YData3 tY nY) (h3 : OddThreeFreeInput)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
    (hR : RouteD3Setup K z) (hshape : LocalShapeC3 2 (CompData.model tY nY) (conjClass3 K) z) :
    Nonempty (TCtx3 tY nY (conjClass3 K) K z) := by
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨d⟩ := LocalShapeC3.nonempty_dictT2 hY.sc hR.inClass hK hR.cls hshape
  obtain ⟨d', hQ⟩ := exists_dictT2_of_member3 hY hK hR.cls d
  exact ⟨{
    hΩ := hR.inClass
    hex := hR.setup.1
    hK := hK
    hz := hR.cls
    hP1 := hR.setup.2
    hO3 := h3 G K z hR
    d := d'
    hQ₀ := hQ
    hY := hY }⟩

section DictConj

variable {G : Type} [Group G] {tY : StatedLieTag} {nY : ℕ}

noncomputable def ShapeDictT2.conj3 {Ω : Set (Subgroup G)} {z : G} (hΩ : ConjInvariant Ω) (g : G)
    (d : ShapeDictT2 3 1 tY nY Ω z) : ShapeDictT2 3 1 tY nY Ω (g * z * g⁻¹) where
  ψ := (Gaps.locQuotConj hΩ g z).toMonoidHom.comp d.ψ
  ker_le := by
    intro x hx
    refine d.ker_le ?_
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (Gaps.locQuotConj hΩ g z).injective (by simpa using hx)
  Q₀ := d.Q₀.map (Gaps.locQuotConj hΩ g z).toMonoidHom
  Q₁ := d.Q₁.map (Gaps.locQuotConj hΩ g z).toMonoidHom
  comm₀₁ := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := d.comm₀₁ a ha b hb
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, this]
  comm₀ := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨y, rfl⟩
    have := d.comm₀ a ha (d.ψ y) ⟨y, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, this]
  comm₁ := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨y, rfl⟩
    have := d.comm₁ a ha (d.ψ y) ⟨y, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, this]
  mem₀ := by
    rw [← Gaps.locFamily_conj hΩ g z]
    exact ⟨d.Q₀, d.mem₀, rfl⟩
  mem₁ := by
    rw [← Gaps.locFamily_conj hΩ g z]
    exact ⟨d.Q₁, d.mem₁, rfl⟩
  mem_fam := fun R hR => by
    rw [← Gaps.locFamily_conj hΩ g z]
    exact ⟨R.map d.ψ, d.mem_fam R hR, Subgroup.map_map _ _ _⟩
  fam_cases := fun K' hK' => by
    rw [← Gaps.locFamily_conj hΩ g z] at hK'
    obtain ⟨K'', hK'', rfl⟩ := hK'
    rcases d.fam_cases K'' hK'' with h | h | ⟨R, hR, rfl⟩
    · exact Or.inl (Subgroup.map_mono h)
    · exact Or.inr (Or.inl (Subgroup.map_mono h))
    · exact Or.inr (Or.inr ⟨R, hR, Subgroup.map_map _ _ _⟩)
  card_le₀ := by
    refine le_trans (le_of_eq ?_) d.card_le₀
    exact Nat.card_congr (d.Q₀.equivMapOfInjective (Gaps.locQuotConj hΩ g z).toMonoidHom
      (Gaps.locQuotConj hΩ g z).injective).toEquiv.symm
  card_le₁ := by
    refine le_trans (le_of_eq ?_) d.card_le₁
    exact Nat.card_congr (d.Q₁.equivMapOfInjective (Gaps.locQuotConj hΩ g z).toMonoidHom
      (Gaps.locQuotConj hΩ g z).injective).toEquiv.symm

end DictConj

end CFSG.ClassicalInvolution.Q3.Q3TC

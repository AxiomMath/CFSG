module

public import CFSG.ClassicalInvolution.Q3.Q3ZModel
public import CFSG.ClassicalInvolution.Q3.Q3ZLiftCover
public import CFSG.ClassicalInvolution.Q3.Q3ZFrbModel
public import CFSG.ClassicalInvolution.Q3.Q3TCDict
public import CFSG.ClassicalInvolution.Q3.Q3WAComp
public import CFSG.ClassicalInvolution.Q3.Q3WARow

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TP

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement


structure YData3S (tY : StatedLieTag) (nY : ℕ) : Prop where
  sc : FundamentalSingleClass tY (modelUniv tY nY 3 1 Nat.prime_three).D
  perfK : Group.IsPerfect (modelUniv tY nY 3 1 Nat.prime_three).K
  pow3 : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D, Pow3 R
  central : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
    ∀ r ∈ R, r ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K → r = 1
  cop : ∀ w ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K, ¬ 3 ∣ orderOf w

theorem not_locImg_eq_map_fund3S {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
    {tY : StatedLieTag} {nY : ℕ} (hY : YData3S tY nY) {K : Subgroup G}
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

theorem exists_dictT2_of_member3S {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
    {tY : StatedLieTag} {nY : ℕ} (hY : YData3S tY nY) {K : Subgroup G} (hK : K ∈ Ω)
    (hz : IsClassicalMember3 K z) (d : ShapeDictT2 3 1 tY nY Ω z) :
    ∃ d' : ShapeDictT2 3 1 tY nY Ω z, locImg Ω z K ≤ d'.Q₀ := by
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, isSubnormal_le hz.subnormal⟩
  have hmem : locImg Ω z K ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨K, hKz, rfl⟩
  rcases d.fam_cases _ hmem with h | h | ⟨R, hR, hRK⟩
  · exact ⟨d, h⟩
  · exact ⟨d.swap, h⟩
  · exact (not_locImg_eq_map_fund3S hY hKz hz d.ψ d.ker_le hR hRK).elim

structure TCtxS3 (tY : StatedLieTag) (nY : ℕ) {G : Type} [Group G] (Ω : Set (Subgroup G))
    (K : Subgroup G) (z : G) where
  hΩ : InClass3 Ω
  hex : ExactMembers3 Ω
  hK : K ∈ Ω
  hz : IsClassicalMember3 K z
  hP1 : LocalOddCentral Ω {z}
  hO3 : LocalOddThreeFree3 Ω z
  d : ShapeDictT2 3 1 tY nY Ω z
  hQ₀ : locImg Ω z K ≤ d.Q₀
  hY : YData3S tY nY

namespace TCtxS3

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag} {nY : ℕ}
  {K : Subgroup G} (c : TCtxS3 tY nY Ω K z)

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

end TCtxS3


theorem nonempty_tctxS3 {tY : StatedLieTag} {nY : ℕ} (hY : YData3S tY nY) (h3 : OddThreeFreeInput)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
    (hR : RouteD3Setup K z) (hshape : LocalShapeC3 2 (CompData.model tY nY) (conjClass3 K) z) :
    Nonempty (TCtxS3 tY nY (conjClass3 K) K z) := by
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨d⟩ := Q3TC.LocalShapeC3.nonempty_dictT2 hY.sc hR.inClass hK hR.cls hshape
  obtain ⟨d', hQ⟩ := exists_dictT2_of_member3S hY hK hR.cls d
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

section PSp


open CFSG.ClassicalInvolution.Models.SymplecticPairs (IsHyperbolicPlane planeGroup stdPlane form
  isHyperbolicPlane_stdPlane mem_fundamentalSubgroups_PSp_iff form_single_inl_inr
  mem_stdPlane_iff)

theorem yData3S_psp2 : YData3S .PSp 2 := by
  have hadmP := Q3Z.statedLieAdmissible_psp2
  have hpc := powCop3_model (t := .PSp) (n := 2) trivial hadmP (by decide) (by decide)
  refine ⟨Q3Z.fundamentalSingleClass_psp2, Q3Z.isPerfect_sp4_three, hpc.pow3, ?_, hpc.cop⟩
  intro R hR r hr hc
  obtain ⟨P, hP, rfl⟩ := (mem_fundamentalSubgroups_PSp_iff hadmP R).mp hR
  exact Q3Z.planeGroup_central_eq_one hP hr hc

theorem exists_noncommuting_fund_psp2 :
    ∃ R ∈ fundamentalSubgroups .PSp (modelUniv .PSp 2 3 1 Nat.prime_three).D,
      ∃ R' ∈ fundamentalSubgroups .PSp (modelUniv .PSp 2 3 1 Nat.prime_three).D,
        R ≠ R' ∧ ¬ Commutes R R' := by
  have hadmP := Q3Z.statedLieAdmissible_psp2
  have h2 : (2 : GaloisField 3 1) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  set e₀ : Fin 2 ⊕ Fin 2 → GaloisField 3 1 := Pi.single (Sum.inl 0) 1 with he₀
  set e₁ : Fin 2 ⊕ Fin 2 → GaloisField 3 1 := Pi.single (Sum.inl 1) 1 with he₁
  set f₀ : Fin 2 ⊕ Fin 2 → GaloisField 3 1 := Pi.single (Sum.inr 0) 1 with hf₀
  have hform : form (e₀ + e₁) f₀ = 1 := by
    rw [hf₀, Models.SymplecticPairs.form_single_right]
    simp [he₀, he₁]
  have hP₀ : IsHyperbolicPlane (stdPlane (GaloisField 3 1) 2 0) := isHyperbolicPlane_stdPlane 0
  have hP' : IsHyperbolicPlane (Submodule.span (GaloisField 3 1) {e₀ + e₁, f₀}) :=
    ⟨_, _, hform, rfl⟩
  have hne : stdPlane (GaloisField 3 1) 2 0 ≠ Submodule.span (GaloisField 3 1) {e₀ + e₁, f₀} := by
    intro h
    have hmem : e₀ + e₁ ∈ stdPlane (GaloisField 3 1) 2 0 := by
      rw [h]
      exact Submodule.subset_span (by simp)
    have := (mem_stdPlane_iff (K := GaloisField 3 1) (n := 2) 0).mp hmem (Sum.inl 1)
      (by simp [CFSG.ClassicalInvolution.Models.SymplecticPairs.coords])
    simp [he₀, he₁] at this
  refine ⟨planeGroup (stdPlane (GaloisField 3 1) 2 0),
    (mem_fundamentalSubgroups_PSp_iff hadmP _).mpr ⟨_, hP₀, rfl⟩,
    planeGroup (Submodule.span (GaloisField 3 1) {e₀ + e₁, f₀}),
    (mem_fundamentalSubgroups_PSp_iff hadmP _).mpr ⟨_, hP', rfl⟩, ?_, ?_⟩
  · intro h
    exact hne (RouteD.Exotic.planeGroup_injective h2 hP₀ hP' h)
  · intro hc
    have := (RouteD.Exotic.commutes_planeGroup_iff h2 hP₀ hP' hne).mp hc e₀
      (Submodule.subset_span (by simp [he₀])) f₀
      (Submodule.subset_span (by simp))
    rw [hf₀, he₀, form_single_inl_inr] at this
    exact one_ne_zero this

end PSp

end CFSG.ClassicalInvolution.Q3.Q3TP

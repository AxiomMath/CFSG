module

public import CFSG.ClassicalInvolution.RouteD.TypeELocal
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Standard

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime]

structure ShapeDictT2 (p f : ℕ) [Fact p.Prime] (tY : StatedLieTag) (nY : ℕ) {G : Type} [Group G]
    (Ω : Set (Subgroup G)) (z : G) where
  ψ : (modelUniv tY nY p f Fact.out).K →* locQuot Ω z
  ker_le : ψ.ker ≤ Subgroup.center _
  Q₀ : Subgroup (locQuot Ω z)
  Q₁ : Subgroup (locQuot Ω z)
  comm₀₁ : Commutes Q₀ Q₁
  comm₀ : Commutes Q₀ ψ.range
  comm₁ : Commutes Q₁ ψ.range
  mem₀ : Q₀ ∈ locFamily Ω z
  mem₁ : Q₁ ∈ locFamily Ω z
  mem_fam : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
    R.map ψ ∈ locFamily Ω z
  fam_cases : ∀ K ∈ locFamily Ω z, K ≤ Q₀ ∨ K ≤ Q₁ ∨
    ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D, K = R.map ψ
  card_le₀ : Nat.card Q₀ ≤ Nat.card SL(2, GaloisField p f)
  card_le₁ : Nat.card Q₁ ≤ Nat.card SL(2, GaloisField p f)

@[expose] def ShapeDictT2.swap {tY : StatedLieTag} {nY : ℕ} {G : Type} [Group G]
    {Ω : Set (Subgroup G)} {z : G} (d : ShapeDictT2 p f tY nY Ω z) :
    ShapeDictT2 p f tY nY Ω z where
  ψ := d.ψ
  ker_le := d.ker_le
  Q₀ := d.Q₁
  Q₁ := d.Q₀
  comm₀₁ := d.comm₀₁.symm
  comm₀ := d.comm₁
  comm₁ := d.comm₀
  mem₀ := d.mem₁
  mem₁ := d.mem₀
  mem_fam := d.mem_fam
  fam_cases := fun K hK => by
    rcases d.fam_cases K hK with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  card_le₀ := d.card_le₁
  card_le₁ := d.card_le₀

section Dict

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem range_mem_of_A1 (D : LieSystemData p f X Φ) (i : Fin D.card) (ht : D.tag i = .PSL)
    (hr : D.rank i = 2) : (D.hom i).range ∈ Φ := by
  obtain ⟨R, hR, hmem⟩ := D.meets i
  have key : ∀ (t : StatedLieTag) (n e : ℕ) (_ : t = .PSL) (_ : n = 2)
      (hadm : StatedLieAdmissible t n p e) (φ : (modelUniv t n p e Fact.out).K →* X)
      (R : Subgroup (modelUniv t n p e Fact.out).K),
      R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D → R.map φ ∈ Φ → φ.range ∈ Φ := by
    intro t n e hT hN hadm φ R hR hmem
    subst hT hN
    have : R = ⊤ := CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups_eq_top_PSL_two p e
      Fact.out hadm R hR
    rw [this, Subgroup.map_top] at hmem
    exact hmem
  exact key _ _ _ ht hr (D.admissible i) (D.hom i) R hR hmem

theorem exists_three_indices {c : ℕ} (hc : c = 3) (i₁ : Fin c) :
    ∃ i₀ i₂ : Fin c, i₀ ≠ i₁ ∧ i₂ ≠ i₁ ∧ i₀ ≠ i₂ ∧ ∀ i, i = i₀ ∨ i = i₁ ∨ i = i₂ := by
  subst hc
  fin_cases i₁
  · exact ⟨1, 2, by decide, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide, by decide⟩

end Dict

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G}

theorem LocalShapeT.nonempty_dictT2 [Finite G] {tY : StatedLieTag} {nY : ℕ}
    (hY : tY ≠ .trialityD4) (hsc : FundamentalSingleClass tY (modelUniv tY nY p f Fact.out).D)
    (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω) (hz : IsClassicalMember p f K z)
    (h : LocalShapeT p f 2 tY nY Ω z) : Nonempty (ShapeDictT2 p f tY nY Ω z) := by
  obtain ⟨D, hcard, i₁, ht, hr, hrest⟩ := h
  obtain ⟨i₀, i₂, h₀, h₂, h₀₂, hall⟩ := exists_three_indices (c := D.card) hcard i₁
  obtain ⟨ht₀, hr₀⟩ := hrest i₀ h₀
  obtain ⟨ht₂, hr₂⟩ := hrest i₂ h₂
  obtain ⟨ψ, hker, hrange, hfund⟩ := exists_hom_of_comp D i₁ ht hr hY
  obtain ⟨ψ₀, -, hrange₀, -⟩ := exists_psl_hom D i₀ ht₀ (k := 1) hr₀
  obtain ⟨ψ₂, -, hrange₂, -⟩ := exists_psl_hom D i₂ ht₂ (k := 1) hr₂
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hΦ : ConjInvariant (locFamily Ω z) :=
    conjInvariant_oddQuotientFamily (inClass_local hΩ {z} ⟨K, hKz⟩).conjInvariant
  have hsingle := singleClass_of_comp D i₁ ht hr hY hsc
  refine ⟨{
    ψ := ψ
    ker_le := hker
    Q₀ := (D.hom i₀).range
    Q₁ := (D.hom i₂).range
    comm₀₁ := ?_
    comm₀ := ?_
    comm₁ := ?_
    mem₀ := range_mem_of_A1 D i₀ ht₀ hr₀
    mem₁ := range_mem_of_A1 D i₂ ht₂ hr₂
    mem_fam := ?_
    fam_cases := ?_
    card_le₀ := ?_
    card_le₁ := ?_ }⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i₀ i₂ h₀₂ a b
  · rw [hrange]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i₀ i₁ h₀ a b
  · rw [hrange]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i₂ i₁ h₂ a b
  · intro R hR
    obtain ⟨R', hR', hRR'⟩ := (hfund (R.map ψ)).mpr ⟨R, hR, rfl⟩
    rw [hRR']
    exact D.map_mem_of_single_class hΦ i₁ hsingle hR'
  · intro K' hK'
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental K' hK'
    rcases hall i with rfl | rfl | rfl
    · exact Or.inl (Subgroup.map_le_range _ _)
    · obtain ⟨R', hR', hRR'⟩ := (hfund _).mp ⟨R, hR, rfl⟩
      exact Or.inr (Or.inr ⟨R', hR', hRR'⟩)
    · exact Or.inr (Or.inl (Subgroup.map_le_range _ _))
  · show Nat.card (D.hom i₀).range ≤ _
    rw [← hrange₀]
    exact Nat.card_le_card_of_surjective ψ₀.rangeRestrict ψ₀.rangeRestrict_surjective
  · show Nat.card (D.hom i₂).range ≤ _
    rw [← hrange₂]
    exact Nat.card_le_card_of_surjective ψ₂.rangeRestrict ψ₂.rangeRestrict_surjective

section Involution

variable [Finite G]

theorem not_locImg_eq_map_fund {tY : StatedLieTag} {nY : ℕ} (hY : YData p f tY nY)
    {K : Subgroup G} (hKz : K ∈ centralizingMembers Ω {z}) (hz : IsClassicalMember p f K z)
    (ψ : (modelUniv tY nY p f Fact.out).K →* locQuot Ω z) (hker : ψ.ker ≤ Subgroup.center _)
    {R : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (h : locImg Ω z K = R.map ψ) : False := by
  let zY : ↥(locLayer Ω z) := ⟨z, le_centralizingLayer hKz hz.mem⟩
  have hzK : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY ∈
      locImg Ω z K := ⟨zY, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩
  rw [h] at hzK
  obtain ⟨r, hrR, hr⟩ := hzK
  have hcentral : ∀ w : locQuot Ω z,
      w * QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY * w := by
    intro w
    obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective _ w
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} w'.2)
  have hrc : r ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K := by
    have := hY.perfK
    refine mem_center_of_comm_mem_center fun s => hker ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, hr]
    rw [commutatorElement_def, ← hcentral (ψ s), mul_inv_cancel_right, mul_inv_cancel]
  have hr1 : r = 1 := hY.central R hR r hrR hrc
  rw [hr1, map_one] at hr
  have hO : zY ∈ classicalInvolutionOddCore ↥(locLayer Ω z) :=
    (QuotientGroup.eq_one_iff _).mp hr.symm
  have h2 : orderOf zY = 2 := by
    rw [Subgroup.orderOf_mk]; exact hz.orderOf_eq_two
  have h3 := orderOf_dvd_natCard (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z))
  have h4 : orderOf (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z)) = 2 := by
    rw [Subgroup.orderOf_mk]; exact h2
  rw [h4] at h3
  have := CFSG.ComponentClassification.OddCore.odd_card (↥(locLayer Ω z))
  exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h3)

theorem exists_dictT2_of_member {tY : StatedLieTag} {nY : ℕ} (hY : YData p f tY nY)
    {K : Subgroup G} (hK : K ∈ Ω) (hz : IsClassicalMember p f K z)
    (d : ShapeDictT2 p f tY nY Ω z) :
    ∃ d' : ShapeDictT2 p f tY nY Ω z, locImg Ω z K ≤ d'.Q₀ := by
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hmem : locImg Ω z K ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨K, hKz, rfl⟩
  rcases d.fam_cases _ hmem with h | h | ⟨R, hR, hRK⟩
  · exact ⟨d, h⟩
  · exact ⟨d.swap, h⟩
  · exact (not_locImg_eq_map_fund hY hKz hz d.ψ d.ker_le hR hRK).elim

end Involution

structure TCtx (p f : ℕ) [Fact p.Prime] (tY : StatedLieTag) (nY : ℕ) {G : Type} [Group G]
    (Ω : Set (Subgroup G)) (K : Subgroup G) (z : G) where
  hp2 : p ≠ 2
  hq : 5 ≤ p ^ f
  hΩ : InClass p f Ω
  hex : ExactMembers Ω
  hK : K ∈ Ω
  hz : IsClassicalMember p f K z
  hP1 : LocalOddCentral Ω {z}
  d : ShapeDictT2 p f tY nY Ω z
  hQ₀ : locImg Ω z K ≤ d.Q₀
  hY : YData p f tY nY

namespace TCtx

variable {tY : StatedLieTag} {nY : ℕ} {K : Subgroup G} (c : TCtx p f tY nY Ω K z)

include c

theorem hf : f ≠ 0 := by
  rintro rfl
  have := c.hq
  simp at this

theorem card_eq : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f c.hf

theorem hodd : Odd (Nat.card (GaloisField p f)) := by
  rw [c.card_eq]
  exact (Nat.Prime.odd_of_ne_two Fact.out c.hp2).pow

theorem h4 : 4 ≤ Nat.card (GaloisField p f) := by
  have := c.hq
  rw [c.card_eq]
  omega

theorem hKz : K ∈ centralizingMembers Ω {z} :=
  ⟨c.hK, le_centralizer_of_isClassicalMember c.hz⟩

variable [Finite G]

theorem eq_of_locImg_le_Q₀ {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hLQ : locImg Ω z L ≤ c.d.Q₀) : L = K := by
  have hcL := card_locImg c.hΩ c.hex hL
  have hcK := card_locImg c.hΩ c.hex c.hKz
  have e1 : locImg Ω z L = c.d.Q₀ :=
    Subgroup.eq_of_le_of_card_ge hLQ (by rw [hcL]; exact c.d.card_le₀)
  have e2 : locImg Ω z K = c.d.Q₀ :=
    Subgroup.eq_of_le_of_card_ge c.hQ₀ (by rw [hcK]; exact c.d.card_le₀)
  exact locImg_injOn c.hΩ c.hP1 hL c.hKz (e1.trans e2.symm)

theorem eq_of_locImg_le_Q₁ {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) (h : locImg Ω z L ≤ c.d.Q₁)
    (h' : locImg Ω z L' ≤ c.d.Q₁) : L = L' := by
  have hcL := card_locImg c.hΩ c.hex hL
  have hcL' := card_locImg c.hΩ c.hex hL'
  have e1 : locImg Ω z L = c.d.Q₁ :=
    Subgroup.eq_of_le_of_card_ge h (by rw [hcL]; exact c.d.card_le₁)
  have e2 : locImg Ω z L' = c.d.Q₁ :=
    Subgroup.eq_of_le_of_card_ge h' (by rw [hcL']; exact c.d.card_le₁)
  exact locImg_injOn c.hΩ c.hP1 hL hL' (e1.trans e2.symm)

omit [Finite G] in
theorem exists_twin : ∃ T ∈ centralizingMembers Ω {z}, locImg Ω z T = c.d.Q₁ :=
  mem_locFamily_iff.mp c.d.mem₁

theorem twin_ne {T : Subgroup G} (hT : T ∈ centralizingMembers Ω {z})
    (hTQ : locImg Ω z T ≤ c.d.Q₁) : T ≠ K := by
  intro hTK
  subst hTK
  have h1 : Commutes (locImg Ω z T) (locImg Ω z T) := fun a ha b hb =>
    c.d.comm₀₁ a (c.hQ₀ ha) b (hTQ hb)
  exact not_commutes_self_of_mem c.hΩ c.hK ((commutes_iff_locImg c.hΩ c.hP1 hT hT).mpr h1)

theorem exists_fund_of_ne {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K)
    (hLQ : ¬ locImg Ω z L ≤ c.d.Q₁) :
    ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      locImg Ω z L = R.map c.d.ψ := by
  have hmem : locImg Ω z L ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨L, hL, rfl⟩
  rcases c.d.fam_cases _ hmem with h | h | h
  · exact absurd (c.eq_of_locImg_le_Q₀ hL h) hLK
  · exact absurd h hLQ
  · exact h

theorem exists_member_of_fund {R : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) :
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
    exact not_commutes_self_of_mem c.hΩ (hL.1)
      ((commutes_iff_locImg c.hΩ c.hP1 hL hL).mpr h1)
  refine ⟨L, hL, fun hLK => ?_, fun hLQ => hne _ c.d.comm₁ hLQ, hLR⟩
  subst hLK
  exact hne _ c.d.comm₀ c.hQ₀

theorem commutes_K_of_ne {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) :
    Commutes K L := by
  have hmem : locImg Ω z L ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨L, hL, rfl⟩
  refine commutes_of_commutes_locImg c.hΩ c.hP1 c.hKz hL ?_
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
  refine commutes_of_commutes_locImg c.hΩ c.hP1 hT hL ?_
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
  locImg_injOn c.hΩ c.hP1 hL hL' h

theorem commutes_iff_fund {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ) :
    Commutes L L' ↔ Commutes R R' := by
  constructor
  · intro h
    have h1 := commutes_locImg_of_commutes (x := z) (Ω := Ω) h
    rw [hLR, hLR'] at h1
    exact commutes_of_commutes_map c.d.ψ c.d.ker_le
      (perfect_of_le_commutator (c.hY.perfR R hR)) h1
  · intro h
    refine commutes_of_commutes_locImg c.hΩ c.hP1 hL hL' ?_
    rw [hLR, hLR']
    exact commutes_map _ h

omit [Finite G] in
theorem hF : OddCoverSL3 (GaloisField p f) := by
  have hf : f ≠ 0 := c.hf
  exact CFSG.ClassicalInvolution.ModelFacts.OddCover.noCover_odd_sl3.{0} (GaloisField.card p f hf)
    c.hq

theorem stdPair_of_fund {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z})
    {R R' W : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hW : LinearBlockStandardPair (GaloisField p f) W R R')
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ) :
    ∃ W' : Subgroup G, LinearBlockStandardPair (GaloisField p f) W' L L' := by
  have := linearBlockStandardPair_map_central hW c.d.ψ c.d.ker_le
  rw [← hLR, ← hLR'] at this
  exact linearBlockStandardPair_of_locImg (by have := c.hq; omega) c.hF c.hΩ c.hP1 hL hL' this

theorem exists_nodes {r : ℕ} (R : Fin r → Subgroup (modelUniv tY nY p f Fact.out).K)
    (hR : ∀ a, R a ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (adj : Fin r → Fin r → Prop)
    (hcomm : ∀ a b, a ≠ b → ¬ adj a b → ¬ adj b a → Commutes (R a) (R b))
    (hstd : ∀ a b, adj a b → ∃ W : Subgroup (modelUniv tY nY p f Fact.out).K,
      LinearBlockStandardPair (GaloisField p f) W (R a) (R b)) :
    ∃ j : Fin r → Subgroup G, (∀ a, j a ∈ centralizingMembers Ω {z} ∧ j a ≠ K ∧
        ¬ locImg Ω z (j a) ≤ c.d.Q₁ ∧ locImg Ω z (j a) = (R a).map c.d.ψ) ∧
      (∀ a b, a ≠ b → ¬ adj a b → ¬ adj b a → Commutes (j a) (j b)) ∧
      (∀ a b, adj a b → ∃ W : Subgroup G,
        LinearBlockStandardPair (GaloisField p f) W (j a) (j b)) ∧
      (∀ a, Commutes K (j a)) := by
  choose j hj using fun a => c.exists_member_of_fund (hR a)
  refine ⟨j, fun a => ⟨(hj a).1, (hj a).2.1, (hj a).2.2.1, (hj a).2.2.2⟩, ?_, ?_, ?_⟩
  · intro a b hab h1 h2
    exact (c.commutes_iff_fund (hj a).1 (hj b).1 (hR a) (hj a).2.2.2 (hj b).2.2.2).mpr
      (hcomm a b hab h1 h2)
  · intro a b hadj
    obtain ⟨W, hW⟩ := hstd a b hadj
    exact c.stdPair_of_fund (hj a).1 (hj b).1 hW (hj a).2.2.2 (hj b).2.2.2
  · intro a
    exact c.commutes_K_of_ne (hj a).1 (hj a).2.1

end TCtx

end CFSG.ClassicalInvolution.RouteD

module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalance
public import CFSG.ClassicalInvolution.Asc77.AscIHHelp

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ComponentClassification
open scoped commutatorElement

section Perfect

variable {K X : Type} [Group K] [Group X]

theorem ih8_le_of_map_le (ψ : K →* X) (hker : ψ.ker ≤ Subgroup.center K) {R S : Subgroup K}
    (hR : R ≤ ⁅R, R⁆) (h : R.map ψ ≤ S.map ψ) : R ≤ S := by
  refine hR.trans (Subgroup.commutator_le.mpr fun x hx y hy => ?_)
  obtain ⟨s, hs, hsx⟩ := h (Subgroup.mem_map_of_mem ψ hx)
  obtain ⟨s', hs', hsy⟩ := h (Subgroup.mem_map_of_mem ψ hy)
  obtain ⟨c₁, hc₁⟩ : ∃ c, c = s⁻¹ * x := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c, c = s'⁻¹ * y := ⟨_, rfl⟩
  have hk₁ : c₁ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hc₁, map_mul, map_inv, hsx, inv_mul_cancel]
  have hk₂ : c₂ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hc₂, map_mul, map_inv, hsy, inv_mul_cancel]
  have h1 : ∀ g, g * c₁ = c₁ * g := Subgroup.mem_center_iff.mp (hker hk₁)
  have h2 : ∀ g, g * c₂ = c₂ * g := Subgroup.mem_center_iff.mp (hker hk₂)
  have ex : x = c₁ * s := by
    have e0 : s * c₁ = x := by rw [hc₁]; group
    rw [← e0]
    exact h1 s
  have ey : y = c₂ * s' := by
    have e0 : s' * c₂ = y := by rw [hc₂]; group
    rw [← e0]
    exact h2 s'
  rw [commutatorElement_def, ex, ey,
    CFSG.ClassicalInvolution.Balance.StrongBalance.aux_central_commutator c₁ c₂ s s' h1 h2]
  exact S.mul_mem (S.mul_mem (S.mul_mem hs hs') (S.inv_mem hs)) (S.inv_mem hs')

theorem ih8_eq_of_map_eq (ψ : K →* X) (hker : ψ.ker ≤ Subgroup.center K) {R S : Subgroup K}
    (hR : R ≤ ⁅R, R⁆) (hS : S ≤ ⁅S, S⁆) (h : R.map ψ = S.map ψ) : R = S :=
  le_antisymm (ih8_le_of_map_le ψ hker hR h.le) (ih8_le_of_map_le ψ hker hS h.ge)

theorem ih8_commutes_of_commutes_map (ψ : K →* X) (hker : ψ.ker ≤ Subgroup.center K)
    {R S : Subgroup K} (hR : R ≤ ⁅R, R⁆) (h : Commutes (R.map ψ) (S.map ψ)) : Commutes R S := by
  intro r hr s hs
  have key : ∀ s ∈ S, ∀ r ∈ R, s * r = r * s := by
    intro s hs
    refine
      CFSG.ClassicalInvolution.Balance.StrongBalance.commute_of_perfect_of_commutator_mem_center
      (r := s) hR ?_
    intro r hr
    apply hker
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [← h _ (Subgroup.mem_map_of_mem ψ hr) _ (Subgroup.mem_map_of_mem ψ hs)]
    group
  exact (key s hs r hr).symm

end Perfect

section Lie

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem ih8_inClass_restrict_omegaGen {Ω : Set (Subgroup G)} (hconj : ConjInvariant Ω)
    (hcl : ∀ L ∈ Ω, ∃ z : G, IsClassicalMember p f L z) (hne : Ω.Nonempty) :
    InClass p f (restrictFamily Ω (omegaGen Ω)) := by
  refine inClass_of_isClassicalMemberIn hne (fun L hL => le_omegaGen hL)
    (fun n _ L hL => hconj n L hL) rfl ?_
  intro L hL
  obtain ⟨z, hz⟩ := hcl L hL
  have hsec : IsSectionMember p f (omegaGen Ω) L z :=
    { le := le_omegaGen hL
      orderOf_eq_two := hz.orderOf_eq_two
      mem := hz.mem
      perfect := hz.perfect
      subnormal := by
        have := isSubnormal_inf hz.subnormal (omegaGen Ω)
        rwa [inf_eq_left.mpr (le_omegaGen hL)] at this
      nonempty_equiv := hz.nonempty_equiv }
  exact ⟨z, hsec.toIn⟩

theorem ih8_exists_omegaLie [Finite G] {n : ℕ} (hn : CITBelowU p f n) {Ω : Set (Subgroup G)}
    (hconj : ConjInvariant Ω) (hcl : ∀ L ∈ Ω, ∃ z : G, IsClassicalMember p f L z)
    (hne : Ω.Nonempty) (hO : classicalInvolutionOddCore G = ⊥) (hlt : Nat.card G < n) :
    Nonempty (OmegaLie p f Ω) := by
  set Y := omegaGen Ω with hY
  have : Y.Normal := omegaGen_normal hconj
  have hYO : classicalInvolutionOddCore ↥Y = ⊥ := oddCore_normal_eq_bot Y hO
  have hcard : Nat.card ↥Y < n := lt_of_le_of_lt (Subgroup.card_le_card_group Y) hlt
  have hLS : LieSystemMod p f (restrictFamily Ω Y) :=
    hn ↥Y hcard _ (ih8_inClass_restrict_omegaGen hconj hcl hne)
  obtain ⟨D⟩ := hLS
  let ε : (↥Y ⧸ classicalInvolutionOddCore ↥Y) ≃* ↥Y :=
    (QuotientGroup.quotientMulEquivOfEq hYO).trans QuotientGroup.quotientBot
  let g : (↥Y ⧸ classicalInvolutionOddCore ↥Y) →* G := Y.subtype.comp ε.toMonoidHom
  have hginj : Function.Injective g := Y.subtype_injective.comp ε.injective
  have hgmk : ∀ L ∈ Ω, ((L.subgroupOf Y).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y))).map g = L := by
    intro L hL
    rw [Subgroup.map_map]
    have : g.comp (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) = Y.subtype := by
      ext y
      rfl
    rw [this]
    exact Subgroup.map_subgroupOf_eq_of_le (le_omegaGen hL)
  have hrange : g.range = Y := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact (ε q).2
    · intro hx
      obtain ⟨q, hq⟩ := ε.surjective ⟨x, hx⟩
      exact ⟨q, by simp [g, hq]⟩
  have hfund : ∀ L' ∈ oddQuotientFamily (restrictFamily Ω Y), ∃ L ∈ Ω, L'.map g = L := by
    rintro _ ⟨_, ⟨L, hL, -, rfl⟩, rfl⟩
    exact ⟨L, hL, hgmk L hL⟩
  refine ⟨{ card := D.card
            tag := D.tag
            rank := D.rank
            exp := D.exp
            hom := fun i => g.comp (D.hom i)
            isFundTag := D.isFundTag
            admissible := D.admissible
            exp_eq := D.exp_eq
            ker_le_center := ?_
            commute := ?_
            generate := ?_
            fundamental := ?_
            meets := ?_ }⟩
  · intro i x hx
    have : D.hom i x = 1 := hginj (by simpa using hx)
    exact D.ker_le_center i this
  · intro i j hij x y
    simp only [MonoidHom.comp_apply, ← map_mul]
    rw [D.commute i j hij x y]
  · simp only [MonoidHom.range_comp]
    rw [← Subgroup.map_iSup, D.generate, Subgroup.map_top, hrange]
  · intro L hL
    obtain ⟨i, R, hR, hLR⟩ := D.fundamental _ ⟨_, ⟨L, hL, le_omegaGen hL, rfl⟩, rfl⟩
    refine ⟨i, R, hR, ?_⟩
    rw [← Subgroup.map_map, ← hLR]
    exact (hgmk L hL).symm
  · intro i
    obtain ⟨R, hR, hmem⟩ := D.meets i
    obtain ⟨L, hL, hLR⟩ := hfund _ hmem
    refine ⟨R, hR, ?_⟩
    rw [Subgroup.map_map] at hLR
    simpa [Subgroup.map_map, hLR] using hL

theorem ih8_oddCore_eq_bot_of_simple [Finite G] [IsSimpleGroup G] {z : G} (hz : orderOf z = 2) :
    classicalInvolutionOddCore G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (classicalInvolutionOddCore G) with h | h
  · exact h
  · exfalso
    have hodd : Odd (Nat.card (classicalInvolutionOddCore G)) :=
      CFSG.ComponentClassification.OddCore.odd_card G
    rw [h, Subgroup.card_top] at hodd
    have h2 : 2 ∣ Nat.card G := hz ▸ orderOf_dvd_natCard z
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem ih8_member_ne_bot {L : Subgroup G} {z : G} (hz : IsClassicalMember p f L z) : L ≠ ⊥ := by
  intro h
  have h1 := hz.mem
  rw [h, Subgroup.mem_bot] at h1
  have h2 := hz.orderOf_eq_two
  rw [h1, orderOf_one] at h2
  omega

theorem ih8_exists_noncomm {L : Subgroup G} {z : G} (hz : IsClassicalMember p f L z) :
    ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x := by
  by_contra h
  push Not at h
  have hperf := hz.perfect.commutator_eq_top
  have h1 : (⊤ : Subgroup ↥L) ≤ ⊥ := by
    rw [← hperf]
    show ⁅(⊤ : Subgroup ↥L), ⊤⁆ ≤ ⊥
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (h a a.2 b b.2)
  have h2 : (⟨z, hz.mem⟩ : ↥L) ∈ (⊥ : Subgroup ↥L) := h1 (Subgroup.mem_top _)
  have h3 : z = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp h2)
  have h4 := hz.orderOf_eq_two
  rw [h3, orderOf_one] at h4
  omega

theorem ih8_omegaGen_eq_top [IsSimpleGroup G] {Ω : Set (Subgroup G)} (hconj : ConjInvariant Ω)
    {K : Subgroup G} (hK : K ∈ Ω) (hKne : K ≠ ⊥) : omegaGen Ω = ⊤ := by
  have := omegaGen_normal hconj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (omegaGen Ω) with h | h
  · exact absurd (eq_bot_iff.mpr (h ▸ le_omegaGen hK)) hKne
  · exact h

namespace OmegaLie

variable {Ω : Set (Subgroup G)} (D : OmegaLie p f Ω)

theorem comp_eq_top_of_simple [IsSimpleGroup G] (hconj : ConjInvariant Ω)
    (hcl : ∀ L ∈ Ω, ∃ z : G, IsClassicalMember p f L z) (hne : Ω.Nonempty)
    (i : Fin D.card) : D.comp i = ⊤ := by
  obtain ⟨K, hK⟩ := hne
  obtain ⟨z, hz⟩ := hcl K hK
  have htop : omegaGen Ω = ⊤ := ih8_omegaGen_eq_top hconj hK (ih8_member_ne_bot hz)
  have hnorm : (D.comp i).Normal :=
    ⟨fun x hx g => D.mem_comp_conj (htop ▸ Subgroup.mem_top g) hx⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.comp i) with h | h
  · exfalso
    obtain ⟨R, hR, hmem⟩ := D.meets i
    obtain ⟨z', hz'⟩ := hcl _ hmem
    apply ih8_member_ne_bot hz'
    rw [eq_bot_iff]
    calc R.map (D.hom i) ≤ D.comp i := Subgroup.map_le_range _ _
      _ ≤ ⊥ := h.le
  · exact h

theorem card_eq_one_of_simple [IsSimpleGroup G] (hconj : ConjInvariant Ω)
    (hcl : ∀ L ∈ Ω, ∃ z : G, IsClassicalMember p f L z) (hne : Ω.Nonempty) : D.card = 1 := by
  obtain ⟨K, hK⟩ := hne
  obtain ⟨z, hz⟩ := hcl K hK
  obtain ⟨i₀, -⟩ := D.exists_comp_of_mem hK
  have hpos : 0 < D.card := i₀.pos
  by_contra hne1
  have h1 : 1 < D.card := by omega
  have hij : (⟨0, hpos⟩ : Fin D.card) ≠ ⟨1, h1⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hc := D.comp_commute hij
  rw [D.comp_eq_top_of_simple hconj hcl ⟨K, hK⟩, D.comp_eq_top_of_simple hconj hcl ⟨K, hK⟩] at hc
  obtain ⟨x, hx, y, hy, hxy⟩ := ih8_exists_noncomm hz
  exact hxy (hc x (Subgroup.mem_top x) y (Subgroup.mem_top y))

theorem index_eq (hcard : D.card = 1) (i j : Fin D.card) : i = j :=
  Fin.ext (by have := i.2; have := j.2; omega)

theorem hom_surjective_of_simple [IsSimpleGroup G] (hconj : ConjInvariant Ω)
    (hcl : ∀ L ∈ Ω, ∃ z : G, IsClassicalMember p f L z) (hne : Ω.Nonempty)
    (i : Fin D.card) : Function.Surjective (D.hom i) :=
  MonoidHom.range_eq_top.mp (D.comp_eq_top_of_simple hconj hcl hne i)

@[expose] def cls (i : Fin D.card) : Set (Subgroup (D.model i).K) :=
  {R | R ∈ fundamentalSubgroups (D.tag i) (D.model i).D ∧ R.map (D.hom i) ∈ Ω}

theorem cls_subset (i : Fin D.card) {R : Subgroup (D.model i).K} (hR : R ∈ D.cls i) :
    R ∈ fundamentalSubgroups (D.tag i) (D.model i).D :=
  hR.1

theorem mem_iff_exists_cls (hcard : D.card = 1) (i : Fin D.card) {L : Subgroup G} :
    L ∈ Ω ↔ ∃ R ∈ D.cls i, L = R.map (D.hom i) := by
  constructor
  · intro hL
    obtain ⟨j, R, hR, hLR⟩ := D.fundamental L hL
    obtain rfl : j = i := D.index_eq hcard j i
    exact ⟨R, ⟨hR, hLR ▸ hL⟩, hLR⟩
  · rintro ⟨R, hR, rfl⟩
    exact hR.2

theorem fund_conj {K : Type} [Group K] {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {D' : CFSG.LieType.Universal.UniversalRootDatum K} {A : Subgroup K}
    (hA : A ∈ fundamentalSubgroups t D') (g : K) : conjSub g A ∈ fundamentalSubgroups t D' := by
  obtain ⟨g₀, γ, hγ, rfl⟩ := hA
  exact ⟨g * g₀, γ, hγ, (conjSub_mul g g₀ _).symm⟩

theorem cls_conj (hconj : ConjInvariant Ω) (i : Fin D.card) {R : Subgroup (D.model i).K}
    (hR : R ∈ D.cls i) (k : (D.model i).K) : conjSub k R ∈ D.cls i := by
  refine ⟨fund_conj hR.1 k, ?_⟩
  have := map_conj_eq_conjSub_map (D.hom i) k R
  change Subgroup.map (D.hom i) (conjSub k R) ∈ Ω
  rw [show Subgroup.map (D.hom i) (conjSub k R) = conjSub (D.hom i k) (R.map (D.hom i)) from this]
  exact hconj _ _ hR.2

theorem cls_single (i : Fin D.card) (hsurj : Function.Surjective (D.hom i))
    (htrans : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    (hperf : ∀ R ∈ D.cls i, R ≤ ⁅R, R⁆) (hconj : ConjInvariant Ω)
    {R S : Subgroup (D.model i).K} (hR : R ∈ D.cls i) (hS : S ∈ D.cls i) :
    ∃ k : (D.model i).K, S = conjSub k R := by
  obtain ⟨g, hg⟩ := htrans _ hR.2 _ hS.2
  obtain ⟨k, rfl⟩ := hsurj g
  refine ⟨k, (ih8_eq_of_map_eq (D.hom i) (D.ker_le_center i) (hperf _ (D.cls_conj hconj i hR k))
    (hperf S hS) ?_).symm⟩
  have := map_conj_eq_conjSub_map (D.hom i) k R
  rw [show Subgroup.map (D.hom i) (conjSub k R) = conjSub (D.hom i k) (R.map (D.hom i)) from this]
  exact hg

end OmegaLie

end Lie

end CFSG.ClassicalInvolution.Asc77

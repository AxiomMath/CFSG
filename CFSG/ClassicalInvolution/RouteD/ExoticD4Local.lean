module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4Graph
public import CFSG.ClassicalInvolution.RouteD.ExoticD4Model
public import CFSG.ClassicalInvolution.RouteD.ExoticShapes
public import CFSG.ClassicalInvolution.RouteD.MultiStarComp
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.RouteD.Multi

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

@[expose] def commAdj (Ω : Set (Subgroup G)) (u v : ↥Ω) : Prop := Commutes u.1 v.1

omit [Finite G] in
theorem commAdj_symm (Ω : Set (Subgroup G)) {u v : ↥Ω} (h : commAdj Ω u v) : commAdj Ω v u :=
  commutes_symm h

section Basic

variable {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω)

include hΩ hex in
theorem mem_centralizingMembers_iff {N : Subgroup G} {w : G} (hw : IsClassicalMember p f N w)
    (hN : N ∈ Ω) (hP1 : LocalOddCentral Ω {w})
    (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)) {L : Subgroup G} (hL : L ∈ Ω) :
    L ∈ centralizingMembers Ω {w} ↔ (L = N ∨ Commutes L N) := by
  have hNw : N ∈ centralizingMembers Ω {w} := ⟨hN, le_centralizer_of_isClassicalMember hw⟩
  constructor
  · intro hLw
    rcases commutes_or_eq_of_involution (Gaps.fundNoncentral p) hΩ hex hP1 D hNw hLw hw with h | h
    · exact Or.inr (commutes_symm h)
    · exact Or.inl h
  · rintro (rfl | h)
    · exact hNw
    · exact mem_centralizingMembers_of_commutes hL hw.mem h

include hΩ hex in
theorem closedNbhd_eq {N : Subgroup G} {w : G} (hw : IsClassicalMember p f N w) (hN : N ∈ Ω)
    (hP1 : LocalOddCentral Ω {w}) (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)) :
    closedNbhd (commAdj Ω) (⟨N, hN⟩ : ↥Ω) = {L : ↥Ω | L.1 ∈ centralizingMembers Ω {w}} := by
  ext L
  have h := mem_centralizingMembers_iff hΩ hex hw hN hP1 D L.2
  show (L = ⟨N, hN⟩ ∨ Commutes L.1 N) ↔ L.1 ∈ centralizingMembers Ω {w}
  rw [h, Subtype.ext_iff]

include hΩ hex in
theorem closedNbhd_whole (hp2 : p ≠ 2) (hf : 0 < f) {N : Subgroup G} {w : G}
    (hw : IsClassicalMember p f N w) (hP1 : LocalOddCentral Ω {w})
    (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w))
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g N) {T : Subgroup G} (hT : T ∈ Ω)
    (hTw : T ∈ centralizingMembers Ω {w}) {i : Fin D.card}
    (hi : locImg Ω w T = (D.hom i).range) :
    closedNbhd (commAdj Ω) (⟨T, hT⟩ : ↥Ω) = {L : ↥Ω | L.1 ∈ centralizingMembers Ω {w}} := by
  obtain ⟨wT, hwT⟩ := hΩ.classical T hT
  have hcomm : ∀ N' ∈ centralizingMembers Ω {w}, N' ≠ T → Commutes T N' := fun N' hN' hne =>
    (commutes_or_eq_of_whole hΩ hex hP1 D hTw hN' hi).resolve_right hne
  have hΩw : centralizingMembers Ω {wT} = centralizingMembers Ω {w} :=
    centralizingMembers_eq_of_twin hp2 hf hΩ hw hwT (hsingle T hT) hTw hcomm
  ext L
  constructor
  · rintro (h | h)
    · have : L.1 = T := congrArg Subtype.val h
      show L.1 ∈ centralizingMembers Ω {w}
      rw [this]
      exact hTw
    · have hL : L.1 ∈ centralizingMembers Ω {wT} :=
        mem_centralizingMembers_of_commutes L.2 hwT.mem h
      rw [hΩw] at hL
      exact hL
  · intro hL
    rcases commutes_or_eq_of_whole hΩ hex hP1 D hTw hL hi with h | h
    · exact Or.inr (commutes_symm h)
    · exact Or.inl (Subtype.ext h)

include hΩ hex in
theorem closedNbhd_ne_of_comp (hp2 : p ≠ 2) (hq4 : 4 ≤ p ^ f) {N : Subgroup G} {w : G}
    (hw : IsClassicalMember p f N w) (hN : N ∈ Ω) (hP1 : LocalOddCentral Ω {w})
    (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)) {i₁ : Fin D.card}
    (ht : D.tag i₁ = .POmegaPlus) (hr : D.rank i₁ = 4)
    (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2) {L : Subgroup G}
    (hL : L ∈ compMembers Ω w D i₁) (hLΩ : L ∈ Ω) :
    closedNbhd (commAdj Ω) (⟨L, hLΩ⟩ : ↥Ω) ≠ closedNbhd (commAdj Ω) (⟨N, hN⟩ : ↥Ω) := by
  intro heq
  have hsc := fundamentalSingleClass_of_ne D i₁ (by rw [ht]; decide) (by rw [ht]; decide)
  have hperf := D.fundPerfect hp2 hq4
    (trialityD4_vacuous D (by decide : StatedLieTag.POmegaPlus ≠ .trialityD4) ht hrest) i₁
  obtain ⟨R, hR⟩ := exists_corr_left hΩ hex D hL
  obtain ⟨S, hS, hSne, hSnc⟩ := exists_fund_not_commuting (D.isFundTag i₁) (D.admissible i₁)
    (by rw [ht, hr]; decide) hR.2.1
  obtain ⟨L', hL'⟩ := exists_corr_right hΩ D hsc hS
  have hmem : (⟨L', hL'.1.1⟩ : ↥Ω) ∈ closedNbhd (commAdj Ω) (⟨N, hN⟩ : ↥Ω) := by
    rw [closedNbhd_eq hΩ hex hw hN hP1 D]
    exact hL'.1
  rw [← heq] at hmem
  rcases hmem with h | h
  · have hLL : L' = L := congrArg Subtype.val h
    rw [hLL] at hL'
    exact hSne (corr_unique_left hperf hL' hR)
  · exact hSnc ((corr_commutes hΩ hP1 hperf hL' hR).mp h)

end Basic

section Data

theorem cliqueFour_fund_of_eq (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {t : StatedLieTag} {n e : ℕ}
    (ht : t = .POmegaPlus) (hn : n = 4) (he : e = f) (hadm : StatedLieAdmissible t n p e) :
    CliqueFour (fun R R' : ↥(fundamentalSubgroups t (modelUniv t n p e Fact.out).D) =>
      Commutes R.1 R'.1) := by
  subst ht hn he
  exact cliqueFour_fund_plus_four hp2 hq hadm

variable {Ω : Set (Subgroup G)}

theorem exists_localData (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hf : 0 < f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {N : Subgroup G} {w : G} (hw : IsClassicalMember p f N w)
    (hN : N ∈ Ω) (hP1 : LocalOddCentral Ω {w})
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g N)
    (D : LieSystemData p f (locQuot Ω w) (locFamily Ω w)) {a : ℕ} {i₁ : Fin D.card}
    (hcard : D.card = a + 1) (ht : D.tag i₁ = .POmegaPlus) (hr : D.rank i₁ = 4)
    (hrest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2) :
    (∃ s : Finset ↥Ω, s.card = a ∧ ∀ u : ↥Ω,
        u ∈ s ↔ closedNbhd (commAdj Ω) u = closedNbhd (commAdj Ω) (⟨N, hN⟩ : ↥Ω)) ∧
      ∃ (F : Type) (fadj : F → F → Prop), CliqueFour fadj ∧ Nonempty F ∧
        ∃ e : ↥(outerNbhd (commAdj Ω) (⟨N, hN⟩ : ↥Ω)) ≃ F,
          ∀ u u' : ↥(outerNbhd (commAdj Ω) (⟨N, hN⟩ : ↥Ω)), u ≠ u' →
            (commAdj Ω u.1 u'.1 ↔ fadj (e u) (e u')) := by
  classical
  have hq4 : 4 ≤ p ^ f := by omega
  have hclN := closedNbhd_eq hΩ hex hw hN hP1 D
  choose T hTw hTimg using fun i : {i : Fin D.card // i ≠ i₁} =>
    exists_member_of_a1 (Ω := Ω) D (hrest i.1 i.2)
  have hTΩ : ∀ i, T i ∈ Ω := fun i => (hTw i).1
  have hclT : ∀ i, closedNbhd (commAdj Ω) (⟨T i, hTΩ i⟩ : ↥Ω) =
      {L : ↥Ω | L.1 ∈ centralizingMembers Ω {w}} := fun i =>
    closedNbhd_whole hΩ hex hp2 hf hw hP1 D hsingle (hTΩ i) (hTw i) (hTimg i)
  have hTmem : ∀ i, T i ∈ compMembers Ω w D i.1 := fun i => ⟨hTw i, (hTimg i).le⟩
  have hclass : ∀ u : ↥Ω, u.1 ∈ centralizingMembers Ω {w} →
      u.1 ∈ compMembers Ω w D i₁ ∨ ∃ i : {i : Fin D.card // i ≠ i₁}, u.1 = T i := by
    intro u hu
    obtain ⟨j, hj, -⟩ := exists_unique_comp hΩ hex D hu
    by_cases hji : j = i₁
    · subst hji
      exact Or.inl hj
    · refine Or.inr ⟨⟨j, hji⟩, ?_⟩
      exact eq_of_mem_compMembers_a1 hΩ hex hP1 (hrest j hji) hj (hTmem ⟨j, hji⟩)
  have htwin : ∀ u : ↥Ω, closedNbhd (commAdj Ω) u = closedNbhd (commAdj Ω) (⟨N, hN⟩ : ↥Ω) ↔
      ∃ i : {i : Fin D.card // i ≠ i₁}, u.1 = T i := by
    intro u
    constructor
    · intro h
      have hu : u.1 ∈ centralizingMembers Ω {w} := by
        have hmem : u ∈ closedNbhd (commAdj Ω) u := Or.inl rfl
        rw [h, hclN] at hmem
        exact hmem
      rcases hclass u hu with hc | ⟨i, hi⟩
      · exact absurd h (closedNbhd_ne_of_comp hΩ hex hp2 hq4 hw hN hP1 D ht hr hrest hc u.2)
      · exact ⟨i, hi⟩
    · rintro ⟨i, hi⟩
      have : u = ⟨T i, hTΩ i⟩ := Subtype.ext hi
      rw [this, hclT i, hclN]
  refine ⟨?_, ?_⟩
  ·
    have hinj : Function.Injective (fun i : {i : Fin D.card // i ≠ i₁} =>
        (⟨T i, hTΩ i⟩ : ↥Ω)) := by
      intro i j hij
      have hTij : T i = T j := congrArg Subtype.val hij
      exact Subtype.ext (eq_of_locImg_le_range hΩ hex D (hTw i) (hTimg i).le
        (by rw [hTij]; exact (hTimg j).le))
    refine ⟨Finset.univ.image (fun i : {i : Fin D.card // i ≠ i₁} => (⟨T i, hTΩ i⟩ : ↥Ω)), ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
      simp [Fintype.card_subtype_compl, hcard]
    · intro u
      rw [htwin u, Finset.mem_image]
      constructor
      · rintro ⟨i, -, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, Finset.mem_univ _, Subtype.ext hi.symm⟩
  ·
    have hsc := fundamentalSingleClass_of_ne D i₁ (by rw [ht]; decide) (by rw [ht]; decide)
    have hperf := D.fundPerfect hp2 hq4
      (trialityD4_vacuous D (by decide : StatedLieTag.POmegaPlus ≠ .trialityD4) ht hrest) i₁
    have hexp : D.exp i₁ = f := by
      rcases D.exp_eq i₁ with h | ⟨h, -⟩
      · exact h
      · rw [ht] at h
        exact absurd h (by decide)
    have hout : ∀ u : ↥Ω, u ∈ outerNbhd (commAdj Ω) (⟨N, hN⟩ : ↥Ω) ↔
        u.1 ∈ compMembers Ω w D i₁ := by
      intro u
      constructor
      · rintro ⟨hu1, hu2⟩
        have hu : u.1 ∈ centralizingMembers Ω {w} := by
          rw [hclN] at hu1
          exact hu1
        rcases hclass u hu with hc | ⟨i, hi⟩
        · exact hc
        · exact absurd ((htwin u).mpr ⟨i, hi⟩) hu2
      · intro hc
        refine ⟨?_, closedNbhd_ne_of_comp hΩ hex hp2 hq4 hw hN hP1 D ht hr hrest hc u.2⟩
        rw [hclN]
        exact hc.1
    obtain ⟨e₀, he₀⟩ := exists_compMembersEquiv hΩ hex hP1 D hsc hperf
    let φ : ↥(outerNbhd (commAdj Ω) (⟨N, hN⟩ : ↥Ω)) ≃ compMembers Ω w D i₁ :=
      { toFun := fun u => ⟨u.1.1, (hout u.1).mp u.2⟩
        invFun := fun L => ⟨⟨L.1, L.2.1.1⟩, (hout _).mpr L.2⟩
        left_inv := fun u => rfl
        right_inv := fun L => rfl }
    refine ⟨↥(compFund D i₁), fun R R' => Commutes R.1 R'.1,
      cliqueFour_fund_of_eq hp2 hq ht hr hexp (D.admissible i₁), ?_, φ.trans e₀, ?_⟩
    · obtain ⟨R, hR, -⟩ := D.meets i₁
      exact ⟨⟨R, hR⟩⟩
    · intro u u' _
      exact corr_commutes hΩ hP1 hperf (he₀ (φ u)) (he₀ (φ u'))

end Data

section Row

theorem rowExoticD4_three : RowPiece p f (fun a t n => ShapeExoticD4 a t n ∧ a = 3) := by
  rintro a t n ⟨⟨-, ht, hn, -, -⟩, ha⟩ G _ _ _ hnab K z S hloc
  subst ht hn ha
  exfalso
  have hΩ := S.inClass
  have hex := S.exact
  have hq5 := S.five
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0] at hq5
      simp at hq5
    · exact h0
  have hsingle : ∀ L ∈ conjClass K, ∃ g : G, L = conjSub g K := single_class K
  have hdata : ∀ v : ↥(conjClass K),
      (∃ s : Finset ↥(conjClass K), s.card = 3 ∧ ∀ u : ↥(conjClass K),
          u ∈ s ↔ closedNbhd (commAdj (conjClass K)) u =
            closedNbhd (commAdj (conjClass K)) v) ∧
        ∃ (F : Type) (fadj : F → F → Prop), CliqueFour fadj ∧ Nonempty F ∧
          ∃ e : ↥(outerNbhd (commAdj (conjClass K)) v) ≃ F,
            ∀ u u' : ↥(outerNbhd (commAdj (conjClass K)) v), u ≠ u' →
              (commAdj (conjClass K) u.1 u'.1 ↔ fadj (e u) (e u')) := by
    intro v
    obtain ⟨g, hg⟩ := hsingle v.1 v.2
    have hw : IsClassicalMember p f v.1 (g * z * g⁻¹) := by
      rw [hg]
      exact S.cls.conj g
    have hP1 : LocalOddCentral (conjClass K) {g * z * g⁻¹} :=
      localOddCentral_conj hΩ.conjInvariant g z S.p1
    obtain ⟨D, hcard, i₁, ht, hr, hrest⟩ :=
      LocalShapeT.conj (p := p) (f := f) hΩ.conjInvariant g hloc
    have hsingle' : ∀ L ∈ conjClass K, ∃ g' : G, L = conjSub g' v.1 := by
      intro L hL
      obtain ⟨g₁, hg₁⟩ := hsingle L hL
      refine ⟨g₁ * g⁻¹, ?_⟩
      rw [conjSub_mul, hg, conjSub_inv_conjSub, hg₁]
    exact exists_localData S.odd S.five hf hΩ hex hw v.2 hP1 hsingle' D hcard ht hr hrest
  exact false_of_three_twins (V := ↥(conjClass K)) (adj := commAdj (conjClass K))
    (fun u v h => commAdj_symm _ h) (fun v => (hdata v).1) (fun v => (hdata v).2)

@[expose] def ExoticD4Four (p f : ℕ) [Fact p.Prime] : Prop :=
  RowPiece p f (fun a t n => ShapeExoticD4 a t n ∧ a = 4)

theorem rowExoticD4_of_four (h : ExoticD4Four p f) : RowPiece p f ShapeExoticD4 := by
  intro a t n hshape
  have h2 : a ≠ 2 := by
    rintro rfl
    exact hshape.1.2.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl ⟨rfl, hshape.2.1, by have := hshape.2.2.1; omega⟩)))))))))))
  by_cases ha : a = 3
  · exact rowExoticD4_three a t n ⟨hshape, ha⟩
  · have ha4 : a = 4 := by
      have h1 := hshape.2.2.2.1
      have h3 := hshape.2.2.2.2
      omega
    exact h a t n ⟨hshape, ha4⟩

end Row

end CFSG.ClassicalInvolution.RouteD.Exotic

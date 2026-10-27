module

public import CFSG.ClassicalInvolution.Q3.Q3EXD4Model
public import CFSG.ClassicalInvolution.Q3.Q3EXTwin
public import CFSG.ClassicalInvolution.Q3.Q3WShape
public import CFSG.ClassicalInvolution.Q3.Q3WARow
public import CFSG.ClassicalInvolution.RouteD.ExoticD4Local
public import CFSG.ClassicalInvolution.Q3.Q3WAEDict
public import CFSG.ClassicalInvolution.Q3.Q3WMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic


variable {G : Type} [Group G] [Finite G] {ι : Type} {Ω : Set (Subgroup G)}

theorem mem_centralizingMembers_iff3 (hMFZ : RouteD.Gaps.FundNoncentral 3) (hΩ : InClass3 Ω)
    (hex : ExactMembers3 Ω) {N : Subgroup G} {w : G} (hw : IsClassicalMember3 N w) (hN : N ∈ Ω)
    (hP1 : LocalOddCentral Ω {w}) (hO3 : LocalOddThreeFree3 Ω w)
    (D : LieSystemData3 ι (locQuot Ω w) (locFamily Ω w)) {L : Subgroup G} (hL : L ∈ Ω) :
    L ∈ centralizingMembers Ω {w} ↔ (L = N ∨ Commutes L N) := by
  have hNw : N ∈ centralizingMembers Ω {w} := ⟨hN, isSubnormal_le hw.subnormal⟩
  constructor
  · intro hLw
    rcases commutes_or_eq_of_involution3 hMFZ hΩ hex hP1 hO3 D hNw hLw hw with h | h
    · exact Or.inr h.symm
    · exact Or.inl h
  · rintro (rfl | h)
    · exact hNw
    · exact mem_centralizingMembers_of_commutes hL hw.mem h

theorem closedNbhd_eq3 (hMFZ : RouteD.Gaps.FundNoncentral 3) (hΩ : InClass3 Ω)
    (hex : ExactMembers3 Ω) {N : Subgroup G} {w : G} (hw : IsClassicalMember3 N w) (hN : N ∈ Ω)
    (hP1 : LocalOddCentral Ω {w}) (hO3 : LocalOddThreeFree3 Ω w)
    (D : LieSystemData3 ι (locQuot Ω w) (locFamily Ω w)) :
    closedNbhd (commAdj Ω) (⟨N, hN⟩ : ↥Ω) = {L : ↥Ω | L.1 ∈ centralizingMembers Ω {w}} := by
  ext L
  have h := mem_centralizingMembers_iff3 hMFZ hΩ hex hw hN hP1 hO3 D L.2
  show (L = ⟨N, hN⟩ ∨ Commutes L.1 N) ↔ L.1 ∈ centralizingMembers Ω {w}
  rw [h, Subtype.ext_iff]

theorem closedNbhd_whole3 (hΩ : InClass3 Ω) {N : Subgroup G} {w : G}
    (hw : IsClassicalMember3 N w) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g N)
    {T : Subgroup G} (hT : T ∈ Ω) (hTw : T ∈ centralizingMembers Ω {w})
    (hu : Universal3 Ω w T) :
    closedNbhd (commAdj Ω) (⟨T, hT⟩ : ↥Ω) = {L : ↥Ω | L.1 ∈ centralizingMembers Ω {w}} := by
  obtain ⟨wT, hwT⟩ := hΩ.classical T hT
  have hΩw : centralizingMembers Ω {wT} = centralizingMembers Ω {w} :=
    centralizingMembers_eq_of_twin3 hΩ hw hwT (hsingle T hT) hTw hu
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
    by_cases hLT : L.1 = T
    · exact Or.inl (Subtype.ext hLT)
    · exact Or.inr (hu L.1 hL hLT).symm

theorem closedNbhd_ne_of_comp3 {t : StatedLieTag} {n : ℕ} (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {N : Subgroup G} {w : G}
    (hw : IsClassicalMember3 N w) (hN : N ∈ Ω) (hP1 : LocalOddCentral Ω {w})
    (hO3 : LocalOddThreeFree3 Ω w) (D : LieSystemData3 ι (locQuot Ω w) (locFamily Ω w)) {i₁ : ι}
    (hk : D.kind i₁ = CompData.model t n) {L : Subgroup G} (hL : L ∈ compMembers3 Ω w D i₁)
    (hLΩ : L ∈ Ω) :
    closedNbhd (commAdj Ω) (⟨L, hLΩ⟩ : ↥Ω) ≠ closedNbhd (commAdj Ω) (⟨N, hN⟩ : ↥Ω) := by
  intro heq
  have hMFZ := RouteD.Gaps.fundNoncentral 3
  have hnA1 := not_psl_two_of_admissible3 hadm
  have hsc := singleClass_of_kind hk hfund hadm hG2 hD4
  have hpc := powCop3_of_kind hk hfund hadm hG2 hD4
  obtain ⟨R, hR⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hL
  obtain ⟨S, hS, hSne, hSnc⟩ := exists_fund_not_commuting_of_kind hk hfund hadm hnA1 hR.2.1
  obtain ⟨L', hL'⟩ := exists_corr_right3 hΩ D hsc hS
  have hmem : (⟨L', hL'.1.1⟩ : ↥Ω) ∈ closedNbhd (commAdj Ω) (⟨N, hN⟩ : ↥Ω) := by
    rw [closedNbhd_eq3 hMFZ hΩ hex hw hN hP1 hO3 D]
    exact hL'.1
  rw [← heq] at hmem
  rcases hmem with h | h
  · have hLL : L' = L := congrArg Subtype.val h
    rw [hLL] at hL'
    exact hSne (corr_unique_left3 hpc hL' hR)
  · exact hSnc ((corr_commutes3 hΩ hex hP1 hO3 hpc hL' hR).mp h)

theorem exists_compMembersEquiv3 {x : G} (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {i : ι}
    (hsc : ∀ R ∈ (D.kind i).fund, ∀ R' ∈ (D.kind i).fund, ∃ g, R' = conjSub g R)
    (hk : PowCop3 (D.kind i)) :
    ∃ e : compMembers3 Ω x D i ≃ ↥(D.kind i).fund, ∀ N : compMembers3 Ω x D i,
      Corr3 Ω x D i N.1 (e N).1 := by
  choose g hg using fun N : compMembers3 Ω x D i => exists_corr_left3 hΩ hex hP1 hO3 D N.2
  have hinj : Function.Injective
      (fun N : compMembers3 Ω x D i => (⟨g N, (hg N).2.1⟩ : ↥(D.kind i).fund)) := by
    intro N N' h
    have h1 : g N = g N' := congrArg Subtype.val h
    exact Subtype.ext (corr_unique_right3 hΩ hex hP1 hO3 (hg N) (h1 ▸ hg N'))
  have hsurj : Function.Surjective
      (fun N : compMembers3 Ω x D i => (⟨g N, (hg N).2.1⟩ : ↥(D.kind i).fund)) := by
    rintro ⟨R, hR⟩
    obtain ⟨N, hN⟩ := exists_corr_right3 hΩ D hsc hR
    refine ⟨⟨N, hN.1, hN.2.2 ▸ Subgroup.map_le_range _ _⟩, Subtype.ext ?_⟩
    exact corr_unique_left3 hk (hg ⟨N, hN.1, hN.2.2 ▸ Subgroup.map_le_range _ _⟩) hN
  exact ⟨Equiv.ofBijective _ ⟨hinj, hsurj⟩, fun N => hg N⟩

theorem exists_localData3 [Finite ι] (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {N : Subgroup G}
    {w : G} (hw : IsClassicalMember3 N w) (hN : N ∈ Ω) (hP1 : LocalOddCentral Ω {w})
    (hO3 : LocalOddThreeFree3 Ω w) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g N)
    (D : LieSystemData3 ι (locQuot Ω w) (locFamily Ω w)) {a : ℕ} {i₁ : ι}
    (hcard : Nat.card ι = a + 1) (hk : D.kind i₁ = CompData.model .POmegaPlus 4)
    (hrest : ∀ i, i ≠ i₁ → D.kind i = CompData.sl23) :
    (∃ s : Finset ↥Ω, s.card = a ∧ ∀ u : ↥Ω,
        u ∈ s ↔ closedNbhd (commAdj Ω) u = closedNbhd (commAdj Ω) (⟨N, hN⟩ : ↥Ω)) ∧
      ∃ (F : Type) (fadj : F → F → Prop), CliqueFour fadj ∧ Nonempty F ∧
        ∃ e : ↥(outerNbhd (commAdj Ω) (⟨N, hN⟩ : ↥Ω)) ≃ F,
          ∀ u u' : ↥(outerNbhd (commAdj Ω) (⟨N, hN⟩ : ↥Ω)), u ≠ u' →
            (commAdj Ω u.1 u'.1 ↔ fadj (e u) (e u')) := by
  classical
  have := Fintype.ofFinite ι
  have hMFZ := RouteD.Gaps.fundNoncentral 3
  have hfund : IsFundTag (.POmegaPlus : StatedLieTag) := trivial
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hG2 : (.POmegaPlus : StatedLieTag) ≠ .G2 := by decide
  have hD4 : (.POmegaPlus : StatedLieTag) ≠ .trialityD4 := by decide
  have hclN := closedNbhd_eq3 hMFZ hΩ hex hw hN hP1 hO3 D
  choose T hT using fun i : {i : ι // i ≠ i₁} => exists_mem_compMembers3 (D := D) i.1
  have hTw : ∀ i : {i : ι // i ≠ i₁}, T i ∈ centralizingMembers Ω {w} := fun i => (hT i).1
  have hTΩ : ∀ i : {i : ι // i ≠ i₁}, T i ∈ Ω := fun i => (hT i).1.1
  have hu : ∀ i : {i : ι // i ≠ i₁}, Universal3 Ω w (T i) := fun i =>
    universal3_of_a1comp hΩ hex hP1 hO3 D (hrest i.1 i.2) (hT i)
  have hclT : ∀ i : {i : ι // i ≠ i₁}, closedNbhd (commAdj Ω) (⟨T i, hTΩ i⟩ : ↥Ω) =
      {L : ↥Ω | L.1 ∈ centralizingMembers Ω {w}} := fun i =>
    closedNbhd_whole3 hΩ hw hsingle (hTΩ i) (hTw i) (hu i)
  have hclass : ∀ u : ↥Ω, u.1 ∈ centralizingMembers Ω {w} →
      u.1 ∈ compMembers3 Ω w D i₁ ∨ ∃ i : {i : ι // i ≠ i₁}, u.1 = T i := by
    intro u hu'
    obtain ⟨j, hj, -⟩ := exists_unique_comp3 hΩ hex hP1 hO3 D hu'
    by_cases hji : j = i₁
    · subst hji
      exact Or.inl hj
    · refine Or.inr ⟨⟨j, hji⟩, ?_⟩
      exact eq_of_mem_compMembers_a13 hΩ hex hP1 hO3 (hrest j hji) hj (hT ⟨j, hji⟩)
  have htwin : ∀ u : ↥Ω, closedNbhd (commAdj Ω) u = closedNbhd (commAdj Ω) (⟨N, hN⟩ : ↥Ω) ↔
      ∃ i : {i : ι // i ≠ i₁}, u.1 = T i := by
    intro u
    constructor
    · intro h
      have hu' : u.1 ∈ centralizingMembers Ω {w} := by
        have hmem : u ∈ closedNbhd (commAdj Ω) u := Or.inl rfl
        rw [h, hclN] at hmem
        exact hmem
      rcases hclass u hu' with hc | ⟨i, hi⟩
      · exact absurd h (closedNbhd_ne_of_comp3 hfund hadm hG2 hD4 hΩ hex hw hN hP1 hO3 D hk hc u.2)
      · exact ⟨i, hi⟩
    · rintro ⟨i, hi⟩
      have : u = ⟨T i, hTΩ i⟩ := Subtype.ext hi
      rw [this, hclT i, hclN]
  refine ⟨?_, ?_⟩
  ·
    have hinj : Function.Injective (fun i : {i : ι // i ≠ i₁} => (⟨T i, hTΩ i⟩ : ↥Ω)) := by
      intro i j hij
      have hTij : T i = T j := congrArg Subtype.val hij
      exact Subtype.ext (eq_of_locImg_le_range3 hΩ hex hP1 hO3 D (hTw i) (hT i).2
        (by rw [hTij]; exact (hT j).2))
    refine ⟨Finset.univ.image (fun i : {i : ι // i ≠ i₁} => (⟨T i, hTΩ i⟩ : ↥Ω)), ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
      have h1 : Fintype.card {i : ι // i ≠ i₁} = Fintype.card ι - 1 := by
        simp [Fintype.card_subtype_compl]
      rw [h1, ← Nat.card_eq_fintype_card, hcard]
      rfl
    · intro u
      rw [htwin u, Finset.mem_image]
      constructor
      · rintro ⟨i, -, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, Finset.mem_univ _, Subtype.ext hi.symm⟩
  ·
    have hsc := singleClass_of_kind hk hfund hadm hG2 hD4
    have hpc := powCop3_of_kind hk hfund hadm hG2 hD4
    have hout : ∀ u : ↥Ω, u ∈ outerNbhd (commAdj Ω) (⟨N, hN⟩ : ↥Ω) ↔
        u.1 ∈ compMembers3 Ω w D i₁ := by
      intro u
      constructor
      · rintro ⟨hu1, hu2⟩
        have hu' : u.1 ∈ centralizingMembers Ω {w} := by
          rw [hclN] at hu1
          exact hu1
        rcases hclass u hu' with hc | ⟨i, hi⟩
        · exact hc
        · exact absurd ((htwin u).mpr ⟨i, hi⟩) hu2
      · intro hc
        refine ⟨?_, closedNbhd_ne_of_comp3 hfund hadm hG2 hD4 hΩ hex hw hN hP1 hO3 D hk hc u.2⟩
        rw [hclN]
        exact hc.1
    obtain ⟨e₀, he₀⟩ := exists_compMembersEquiv3 hΩ hex hP1 hO3 D hsc hpc
    let φ : ↥(outerNbhd (commAdj Ω) (⟨N, hN⟩ : ↥Ω)) ≃ compMembers3 Ω w D i₁ :=
      { toFun := fun u => ⟨u.1.1, (hout u.1).mp u.2⟩
        invFun := fun L => ⟨⟨L.1, L.2.1.1⟩, (hout _).mpr L.2⟩
        left_inv := fun u => rfl
        right_inv := fun L => rfl }
    refine ⟨↥(D.kind i₁).fund, fun R R' => Commutes R.1 R'.1, cliqueFour_of_kind hk, ?_,
      φ.trans e₀, ?_⟩
    · obtain ⟨R, hR, -⟩ := D.meets i₁
      exact ⟨⟨R, hR⟩⟩
    · intro u u' _
      exact corr_commutes3 hΩ hex hP1 hO3 hpc (he₀ (φ u)) (he₀ (φ u'))

theorem false_of_d4_three3 {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
    (hR : RouteD3Setup K z) (h3 : LocalOddThreeFree3 (conjClass3 K) z)
    (hloc : LocalShapeC3 3 (CompData.model .POmegaPlus 4) (conjClass3 K) z) : False := by
  classical
  have hΩ := hR.inClass
  obtain ⟨hex, hP1⟩ := hR.setup
  have : Nonempty ↥(conjClass3 K) := ⟨⟨K, ⟨1, conjSub_one K⟩⟩⟩
  obtain ⟨ι, hι, D, hcard, i₁, hk, hrest⟩ := hloc
  have hdata : ∀ v : ↥(conjClass3 K),
      (∃ s : Finset ↥(conjClass3 K), s.card = 3 ∧ ∀ u : ↥(conjClass3 K),
          u ∈ s ↔ closedNbhd (commAdj (conjClass3 K)) u =
            closedNbhd (commAdj (conjClass3 K)) v) ∧
        ∃ (F : Type) (fadj : F → F → Prop), CliqueFour fadj ∧ Nonempty F ∧
          ∃ e : ↥(outerNbhd (commAdj (conjClass3 K)) v) ≃ F,
            ∀ u u' : ↥(outerNbhd (commAdj (conjClass3 K)) v), u ≠ u' →
              (commAdj (conjClass3 K) u.1 u'.1 ↔ fadj (e u) (e u')) := by
    intro v
    obtain ⟨g, hg⟩ := single_class3 K v.1 v.2
    have hw : IsClassicalMember3 v.1 (g * z * g⁻¹) := by
      rw [hg]
      exact hR.cls.conj g
    have hP1' : LocalOddCentral (conjClass3 K) {g * z * g⁻¹} :=
      RouteD.Gaps.localOddCentral_conj hΩ.conjInvariant g z hP1
    have hO3' : LocalOddThreeFree3 (conjClass3 K) (g * z * g⁻¹) :=
      localOddThreeFree3_conj hΩ.conjInvariant g z h3
    obtain ⟨D', hD'⟩ := exists_lieSystemData3_conj hΩ.conjInvariant g z D
    have hsingle' : ∀ L ∈ conjClass3 K, ∃ g' : G, L = conjSub g' v.1 := by
      intro L hL
      obtain ⟨g₁, hg₁⟩ := single_class3 K L hL
      refine ⟨g₁ * g⁻¹, ?_⟩
      rw [conjSub_mul, hg, conjSub_inv_conjSub, hg₁]
    have hk' : D'.kind i₁ = CompData.model .POmegaPlus 4 := by
      rw [hD']
      exact hk
    have hrest' : ∀ i, i ≠ i₁ → D'.kind i = CompData.sl23 := by
      intro i hi
      rw [hD']
      exact hrest i hi
    exact exists_localData3 hΩ hex hw v.2 hP1' hO3' hsingle' D' hcard hk' hrest'
  exact false_of_three_twins (V := ↥(conjClass3 K)) (adj := commAdj (conjClass3 K))
    (fun u v h => commAdj_symm _ h) (fun v => (hdata v).1) (fun v => (hdata v).2)

end CFSG.ClassicalInvolution.Q3.Q3W.EX

namespace CFSG.ClassicalInvolution.Q3.Q3W


theorem shapePiece3_d4_three (h3 : OddThreeFreeInput) :
    ShapePiece3 3 (CompData.model .POmegaPlus 4) := by
  intro G _ _ _ hnab K z hR hshape
  exact (EX.false_of_d4_three3 hR (h3 G K z hR) hshape).elim

end CFSG.ClassicalInvolution.Q3.Q3W

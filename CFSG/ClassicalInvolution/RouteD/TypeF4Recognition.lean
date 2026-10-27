module

public import CFSG.ClassicalInvolution.RouteD.TypeF4Model
public import CFSG.ClassicalInvolution.RouteD.TypeCRecognition

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  isHyperbolicPlane_stdPlane longBlock SymplecticBlockStandardPair)
open CFSG.LieType CFSG.LieType.Universal CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Adjoint
  CFSG.Blueprint.Chevalley
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

section Planes

theorem planeGroup_perfect {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) {n : ℕ}
    (hn : 1 ≤ n) {P : Submodule F (Fin n ⊕ Fin n → F)} (hP : IsHyperbolicPlane P) :
    planeGroup P ≤ ⁅planeGroup P, planeGroup P⁆ := by
  obtain ⟨g, hg⟩ := Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock hP (⟨0, hn⟩ : Fin n)
  have hperf : Group.IsPerfect SL(2, F) := CFSG.ClassicalInvolution.sl2_isPerfect h4
  have h1 : ⁅(⊤ : Subgroup SL(2, F)), (⊤ : Subgroup SL(2, F))⁆ = ⊤ := by
    rw [← commutator_def]
    exact hperf.commutator_eq_top
  rw [hg, ← Subgroup.map_commutator]
  refine Subgroup.map_mono ?_
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h1]

theorem injOn_map_planeGroupSet {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) {n : ℕ}
    (hn : 1 ≤ n) {X : Type} [Group X] (φ : StatedSp n F →* X)
    (hker : φ.ker ≤ Subgroup.center (StatedSp n F)) :
    Set.InjOn (fun R : Subgroup (StatedSp n F) => R.map φ) (planeGroupSet F n) := by
  rintro _ ⟨P, hP, rfl⟩ _ ⟨P', hP', rfl⟩ h
  exact eq_of_map_eq_of_perfect_ker_central φ hker (planeGroup_perfect h4 hn hP)
    (planeGroup_perfect h4 hn hP') h

end Planes

section C3Chain

theorem exists_psiC_of_f4chain (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (U : Fin 4 → Subgroup G)
    (hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 4, i.val + 1 = j.val → i.val ≠ 1 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j))
    (hsp : ∃ W, SymplecticBlockStandardPair (GaloisField p f) W (U 1) (U 2)) :
    ∃ ψC : StatedSp 3 (GaloisField p f) →* G,
      ψC.ker ≤ Subgroup.center (StatedSp 3 (GaloisField p f)) ∧
      (∀ N : Subgroup G, Commutes (U 1) N → Commutes (U 2) N → Commutes (U 3) N →
        Commutes ψC.range N) ∧ ψC.range ≤ ⨆ k, U k ∧
      (longBlock (GaloisField p f) 3 (Fin.last 2)).range.map ψC = U 1 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hadm : StatedLieAdmissible .PSp 3 p f := by
    refine ⟨Fact.out, by omega, by omega, ?_⟩
    intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  let U' : Fin 3 → Subgroup G := ![U 3, U 2, U 1]
  have hcomm' : ∀ i j : Fin 3, i.val + 1 < j.val → ∀ a ∈ U' i, ∀ b ∈ U' j, a * b = b * a := by
    intro i j hij a ha b hb
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert hij; simp; done) | skip
    exact (hcomm 1 3 (by decide) b hb a ha).symm
  have hpair' : ∀ i j : Fin 3, i.val + 1 = j.val → j.val + 1 < 3 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U' i) (U' j) := by
    intro i j hij hj
    fin_cases i <;> fin_cases j <;>
      first | (exfalso; revert hij; simp; done) | (exfalso; revert hj; simp; done) | skip
    obtain ⟨W, hW⟩ := hpair 2 3 (by decide) (by decide)
    exact ⟨W, hW.symm⟩
  have hsp' : ∀ i j : Fin 3, i.val + 1 = 3 → j.val + 2 = 3 →
      ∃ W, SymplecticBlockStandardPair (GaloisField p f) W (U' i) (U' j) := by
    intro i j hi hj
    fin_cases i <;> fin_cases j <;>
      first | (exfalso; revert hi; simp; done) | (exfalso; revert hj; simp; done) | skip
    exact hsp
  obtain ⟨ψ, hker, hrange, -, -, hblk⟩ := Models.SymplecticPairs.weakCT_symplectic_subgroup hadm
    (le_refl 3) hp2 hF (by omega) U' hcomm' hpair' hsp'
  have hlast : (longBlock (GaloisField p f) 3 (Fin.last 2)).range.map ψ = U 1 := by
    rw [Models.SymplecticPairs.range_longBlock_eq_rankOne (by show ¬ 2 + 1 < 3; omega)]
    exact hblk (Fin.last 2)
  refine ⟨ψ, hker, ?_, ?_, hlast⟩
  · intro N h1 h2 h3
    rw [hrange]
    refine commutes_iSup_of_forall fun k => ?_
    fin_cases k
    · exact h3
    · exact h2
    · exact h1
  · rw [hrange]
    exact iSup_le fun k => by
      fin_cases k
      · exact le_iSup U 3
      · exact le_iSup U 2
      · exact le_iSup U 1

end C3Chain

section Closing

theorem exists_lieSystemData_of_fundF4 (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (Ψ : adjointGroup .F4 (GaloisField p f) →* G) (hsurj : Function.Surjective Ψ)
    (hker : Ψ.ker ≤ Subgroup.center (adjointGroup .F4 (GaloisField p f)))
    (hΩ : ∀ L : Subgroup G, L ∈ Ω ↔
      ∃ R ∈ fundamentalSubgroups .F4 (f4Datum (GaloisField p f)), L = R.map Ψ) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .F4 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hadm : StatedLieAdmissible .F4 0 p f := ⟨Fact.out, by omega, rfl⟩
  refine ⟨{
    card := 1
    tag := fun _ => .F4
    rank := fun _ => 0
    exp := fun _ => f
    hom := fun _ => Ψ
    isFundTag := fun _ => trivial
    admissible := fun _ => hadm
    exp_eq := fun _ => Or.inl rfl
    ker_le_center := fun _ => hker
    commute := fun i j h => absurd (Subsingleton.elim i j) h
    generate := ?_
    fundamental := ?_
    meets := ?_ }, rfl, 0, rfl⟩
  · rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := hsurj x
    exact Subgroup.mem_iSup_of_mem (0 : Fin 1) ⟨y, rfl⟩
  · intro L hL
    obtain ⟨R, hR, hLR⟩ := (hΩ L).mp hL
    exact ⟨0, R, hR, hLR⟩
  · intro i
    exact ⟨CurtisTits.rankOne (f4Datum (GaloisField p f)).rootGroup ⟨0, show 0 < 4 by decide⟩,
      rankOne_mem_fund Nat.zero_lt_two, (hΩ _).mpr ⟨_, rankOne_mem_fund Nat.zero_lt_two, rfl⟩⟩

end Closing

section Main

theorem routeD_typeF4_of_chain [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeC p f 3 Ω z)
    (hP1 : LocalOddCentral Ω {z}) (U : Fin 4 → Subgroup G) (hU0 : U 0 ∈ Ω)
    (hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 4, i.val + 1 = j.val → i.val ≠ 1 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j))
    (hsp : ∃ W, SymplecticBlockStandardPair (GaloisField p f) W (U 1) (U 2)) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .F4 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hadm : StatedLieAdmissible .F4 0 p f := ⟨Fact.out, by omega, rfl⟩
  obtain ⟨Ψ, hker, hrange, hblk⟩ := weakCT_f4_subgroup hadm hp2 hF (by omega) U hcomm hpair hsp
  obtain ⟨ψC, hkerC, hCcomm, hCrange, hlast⟩ := exists_psiC_of_f4chain hp2 hq U hcomm hpair hsp
  set F := GaloisField p f with hFdef
  set 𝔖 : Set (Subgroup G) :=
    {L | ∃ R ∈ fundamentalSubgroups .F4 (f4Datum F), L = R.map Ψ} with h𝔖
  have hsingleF : ∀ R ∈ fundamentalSubgroups .F4 (f4Datum F),
      ∀ R' ∈ fundamentalSubgroups .F4 (f4Datum F), ∃ g, R' = conjSub g R :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .F4 0 p f Fact.out trivial hadm
      (by decide) (by decide)
  have hconjF : ∀ (h : adjointGroup .F4 F) R, R ∈ fundamentalSubgroups .F4 (f4Datum F) →
      conjSub h R ∈ fundamentalSubgroups .F4 (f4Datum F) := by
    rintro h R ⟨g, γ, hγ, rfl⟩
    exact ⟨h * g, γ, hγ, (conjSub_mul h g _).symm⟩
  have hr0 : (CurtisTits.rankOne (f4Datum F).rootGroup ⟨0, show 0 < 4 by decide⟩).map Ψ = U 0 :=
    hblk _
  have hr1 : (CurtisTits.rankOne (f4Datum F).rootGroup ⟨1, show 1 < 4 by decide⟩).map Ψ = U 1 :=
    hblk _
  have hr2 : (CurtisTits.rankOne (f4Datum F).rootGroup ⟨2, show 2 < 4 by decide⟩).map Ψ = U 2 :=
    hblk _
  have hr3 : (CurtisTits.rankOne (f4Datum F).rootGroup ⟨3, show 3 < 4 by decide⟩).map Ψ = U 3 :=
    hblk _
  have hΩ𝔖 : 𝔖 ⊆ Ω := by
    rintro _ ⟨R, hR, rfl⟩
    obtain ⟨g, hg⟩ := hsingleF _ (rankOne_mem_fund (F := F) (k := ⟨0, show 0 < 4 by decide⟩)
      Nat.zero_lt_two) R hR
    rw [hg, map_conjSub_eq, hr0]
    exact hΩ.conjInvariant _ _ hU0
  set N₀ : Subgroup G := (rankOneHiF4 F).map Ψ with hN₀
  have hN₀𝔖 : N₀ ∈ 𝔖 := ⟨_, rankOneHiF4_mem_fund, rfl⟩
  have hcommU : ∀ (j : Fin 4) (hj : j.val ≠ 0), Commutes (U j) N₀ := by
    intro j hj
    rw [← hblk j]
    exact (commutes_map_hom Ψ (commutes_rankOneHiF4 hj)).symm
  have hcommC : Commutes ψC.range N₀ :=
    hCcomm N₀ (hcommU 1 (by decide)) (hcommU 2 (by decide)) (hcommU 3 (by decide))
  set 𝓡 : Set (Subgroup G) := (fun R => R.map ψC) '' planeGroupSet F 3 with h𝓡
  have h𝓡𝔖 : 𝓡 ⊆ 𝔖 := by
    rintro _ ⟨_, ⟨P, hP, rfl⟩, rfl⟩
    obtain ⟨g, hg⟩ := Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock hP (Fin.last 2)
    have hg' : ψC g ∈ Ψ.range := by
      rw [hrange]
      exact hCrange ⟨g, rfl⟩
    obtain ⟨h, hh⟩ := hg'
    refine ⟨conjSub h (CurtisTits.rankOne (f4Datum F).rootGroup ⟨1, show 1 < 4 by decide⟩),
      hconjF h _ (rankOne_mem_fund (by show 1 < 2; omega)), ?_⟩
    rw [map_conjSub_eq, hr1, hh, hg]
    show Subgroup.map ψC (conjSub g _) = _
    rw [map_conjSub_eq, hlast]
  have hcommR : ∀ R ∈ 𝓡, Commutes R N₀ := by
    rintro _ ⟨R, -, rfl⟩ x ⟨y, -, rfl⟩ n hn
    exact hcommC _ ⟨y, rfl⟩ n hn
  have hcard : (centralizingMembers Ω {z}).ncard ≤ 1 + 𝓡.ncard := by
    rw [h𝓡, (injOn_map_planeGroupSet (by rw [hF]; omega) (by omega) ψC hkerC).ncard_image,
      ncard_centralizingMembers_eq hΩ hP1]
    exact hshape.ncard_locFamily_le
  have hH : ∀ N ∈ 𝔖, ∃ g ∈ Ψ.range, N = conjSub g N₀ := by
    rintro _ ⟨R, hR, rfl⟩
    obtain ⟨g, hg⟩ := hsingleF _ rankOneHiF4_mem_fund R hR
    exact ⟨Ψ g, ⟨g, rfl⟩, by rw [hg, map_conjSub_eq]⟩
  have hinv : ∀ g ∈ Ψ.range, ∀ M ∈ 𝔖, conjSub g M ∈ 𝔖 := by
    rintro _ ⟨h, rfl⟩ _ ⟨R, hR, rfl⟩
    exact ⟨conjSub h R, hconjF h R hR, by rw [map_conjSub_eq]⟩
  have hcl := adj_closed_of_base_members hΩ hK hsingle hz hΩ𝔖 hN₀𝔖 h𝓡𝔖 hcommR hcard hH hinv
  have hΩsub : Ω ⊆ 𝔖 := subset_of_adj_closed hconn hΩ𝔖 ⟨N₀, hN₀𝔖⟩ hcl
  refine exists_lieSystemData_of_fundF4 hq Ψ ?_ hker (fun L => ⟨fun hL => hΩsub hL, fun hL =>
    hΩ𝔖 hL⟩)
  refine MonoidHom.range_eq_top.mp (eq_top_iff.mpr ?_)
  calc (⊤ : Subgroup G) = ⨆ L ∈ Ω, L := hΩ.generated.symm
    _ ≤ Ψ.range := iSup₂_le fun L hL => by
      obtain ⟨R, -, rfl⟩ := hΩsub hL
      exact Subgroup.map_le_range Ψ R

end Main

end CFSG.ClassicalInvolution.RouteD

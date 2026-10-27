module

public import CFSG.CGT.PushingUpLit.BHS.FourFiveF

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def NonComm (A B : Subgroup (MulAut V)) : Prop :=
  ∃ a ∈ A, ∃ b ∈ B, a * b ≠ b * a

@[expose] def dOut (P : Subgroup (MulAut V)) (D : Set (Subgroup (MulAut V)))
    (M : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {A | A ∈ D ∧ A ∉ dCore P D M}

@[expose] def NCOut (P : Subgroup (MulAut V)) (D : Set (Subgroup (MulAut V)))
    (M : Subgroup (MulAut V)) (A B : Subgroup (MulAut V)) : Prop :=
  A ∈ dOut P D M ∧ B ∈ dOut P D M ∧ NonComm A B

@[expose] def compOf (P : Subgroup (MulAut V)) (D : Set (Subgroup (MulAut V)))
    (M A : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {B | Relation.ReflTransGen (NCOut P D M) A B}

@[expose] def compGen (P : Subgroup (MulAut V)) (D : Set (Subgroup (MulAut V)))
    (M A : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  ⨆ B ∈ compOf P D M A, B

section Basic

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))} {M A B : Subgroup (MulAut V)}

omit [Finite V] in
theorem mem_compOf_self : A ∈ compOf P D M A := Relation.ReflTransGen.refl

omit [Finite V] in
theorem le_compGen : A ≤ compGen P D M A :=
  le_iSup₂_of_le (f := fun (X : Subgroup (MulAut V)) (_ : X ∈ compOf P D M A) => X) A
    mem_compOf_self le_rfl

omit [Finite V] in
theorem compOf_subset (hA : A ∈ dOut P D M) (hB : B ∈ compOf P D M A) : B ∈ dOut P D M := by
  rcases Relation.ReflTransGen.cases_tail hB with rfl | ⟨C, -, hC⟩
  · exact hA
  · exact hC.2.1

theorem Hyp41.comm_of_mem_dCore (h : Hyp41 P D) {C X : Subgroup (MulAut V)}
    (hC : C ∈ dCore P D M) (hX : X ∈ dOut P D M) : ∀ c ∈ C, ∀ x ∈ X, c * x = x * c := by
  rcases h.four_eight_conj hC.1 hX.1 with hc | ⟨g, hg, hXg⟩
  · exact hc
  · exfalso
    have hgP : g ∈ P := (sup_le (h.le C hC.1) (h.le X hX.1)) hg
    have : X = conjSub g C := hXg
    exact hX.2 (this ▸ h.conjSub_mem_dCore hC hgP)

omit [Finite V] in
theorem comm_of_not_mem_compOf {A B : Subgroup (MulAut V)} (hA : A ∈ dOut P D M)
    (hB : B ∈ dOut P D M) (hAB : B ∉ compOf P D M A) : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, b, hb, hne⟩ := hcon
  exact hAB (Relation.ReflTransGen.single ⟨hA, hB, a, ha, b, hb, hne⟩)

end Basic

section Generators

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))} {M : Subgroup (MulAut V)}

omit [Finite V] in
theorem comm_of_iSup_comm {S S' : Set (Subgroup (MulAut V))}
    (h : ∀ X ∈ S, ∀ Y ∈ S', ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    ∀ x ∈ (⨆ X ∈ S, X : Subgroup (MulAut V)), ∀ y ∈ (⨆ Y ∈ S', Y : Subgroup (MulAut V)),
      x * y = y * x := by
  have h1 : ∀ y, (∃ Y ∈ S', y ∈ Y) → ∀ x ∈ (⨆ X ∈ S, X : Subgroup (MulAut V)), x * y = y * x := by
    rintro y ⟨Y, hY, hy⟩
    have : (⨆ X ∈ S, X : Subgroup (MulAut V)) ≤ Subgroup.centralizer ({y} : Set (MulAut V)) :=
      iSup₂_le fun X hX x hx =>
        Subgroup.mem_centralizer_singleton_iff.2 (h X hX Y hY x hx y hy)
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (this hx)
  intro x hx y hy
  have : (⨆ Y ∈ S', Y : Subgroup (MulAut V)) ≤ Subgroup.centralizer ({x} : Set (MulAut V)) :=
    iSup₂_le fun Y hY y hy =>
      Subgroup.mem_centralizer_singleton_iff.2 (h1 y ⟨Y, hY, hy⟩ x hx).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (this hy)).symm

omit [Finite V] in
theorem commV_iSup_le_fixV {S S' : Set (Subgroup (MulAut V))}
    (h : ∀ X ∈ S, ∀ Y ∈ S', commV X ≤ fixV Y) :
    commV (⨆ X ∈ S, X : Subgroup (MulAut V)) ≤ fixV (⨆ Y ∈ S', Y : Subgroup (MulAut V)) := by
  rw [B19.commV_le_iff]
  refine iSup₂_le fun X hX => ?_
  rw [← B19.commV_le_iff]
  intro v hv g hg
  have : (⨆ Y ∈ S', Y : Subgroup (MulAut V)) ≤ cenIn ⊤ (commV X) :=
    iSup₂_le fun Y hY y hy => ⟨Subgroup.mem_top _, fun u hu => h X hX Y hY hu y hy⟩
  exact (this hg).2 v hv

theorem IsSLNatSection.nonComm_of_sylow_ne {L : Subgroup (MulAut V)} {n : ℕ}
    (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n) {A A' : Subgroup (MulAut V)}
    (hA : IsSylowOf 2 A L) (hA' : IsSylowOf 2 A' L) (hne : A ≠ A') (hbot : A ≠ ⊥) :
    NonComm A A' := by
  by_contra hcon
  have hcomm : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a := by
    intro a ha b hb
    by_contra hne2
    exact hcon ⟨a, ha, b, hb, hne2⟩
  have hel := isElemAbelian2_sup (h.sylow_isElemAbelian2 hn hA) (h.sylow_isElemAbelian2 hn hA')
    hcomm
  rw [h.sylow_sup_eq hn hA hA' hne] at hel
  apply hbot
  rw [eq_bot_iff]
  intro a ha
  exact Subgroup.mem_bot.2 (h.center_eq_bot hn (hA.1 ha) fun y hy => hel.1 y hy a (hA.1 ha))

theorem exists_sl_comp {T : Subgroup (MulAut V)}
    (h : Hyp43 P D T M) (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (hA : A ∈ dOut P D M) (hqA : 3 ≤ Nat.card A) :
    ∃ L ∈ lamSet P D M, A ≤ L ∧ ∀ B ∈ compOf P D M A, B ≤ L := by
  obtain ⟨g, hg, L, hL, hAL, -, -⟩ := four_twelve h.toHyp42 hV hA.1 hA.2
  refine ⟨L, hL, hAL, fun B hB => ?_⟩
  have hL' := hL
  obtain ⟨-, ⟨n, hn1, hSL⟩, hΛ2, -⟩ := hL'
  have hq' : ∀ X ∈ dInter D L, 3 ≤ Nat.card X := by
    intro X hX
    have hA2 : Nat.card A = 2 ^ n := hSL.sylow_card hn1 ((hΛ2 A).1 ⟨hA.1, hAL⟩)
    have hX2 : Nat.card X = 2 ^ n := hSL.sylow_card hn1 ((hΛ2 X).1 hX)
    rw [hX2, ← hA2]
    exact hqA
  induction hB with
  | refl => exact hAL
  | tail _ hbc ih =>
    rcases four_seventeen h hV hL hq' hbc.2.1.1 with hcL | hcomm
    · exact hcL
    · exfalso
      obtain ⟨a, ha, x, hx, hne⟩ := hbc.2.2
      exact hne (hcomm a (ih ha) x hx)

theorem compGen_eq {T : Subgroup (MulAut V)} (h : Hyp43 P D T M)
    {A L : Subgroup (MulAut V)} (hA : A ∈ dOut P D M) (hL : L ∈ lamSet P D M) (hAL : A ≤ L)
    (hall : ∀ B ∈ compOf P D M A, B ≤ L) : compGen P D M A = L := by
  refine le_antisymm (iSup₂_le hall) ?_
  have hL' := hL
  obtain ⟨-, ⟨n, hn1, hSL⟩, hΛ2, -⟩ := hL'
  have hAsyl : IsSylowOf 2 A L := (hΛ2 A).1 ⟨hA.1, hAL⟩
  obtain ⟨A', hA', hne⟩ := hSL.exists_sylow_ne hn1 hAsyl
  have hA'D : A' ∈ D := ((hΛ2 A').2 hA').1
  have hA'out : A' ∈ dOut P D M := ⟨hA'D, not_mem_dCore_of_sylow h.toHyp41 hL hA'⟩
  have hnc : NonComm A A' :=
    hSL.nonComm_of_sylow_ne hn1 hAsyl hA' hne.symm (h.ne_bot A hA.1)
  have hA'mem : A' ∈ compOf P D M A := Relation.ReflTransGen.single ⟨hA, hA'out, hnc⟩
  rw [← hSL.sylow_sup_eq hn1 hAsyl hA' hne.symm]
  exact sup_le le_compGen
    (le_iSup₂_of_le (f := fun (X : Subgroup (MulAut V)) (_ : X ∈ compOf P D M A) => X) A'
      hA'mem le_rfl)

omit [Finite V] in
theorem NCOut.symm {A B : Subgroup (MulAut V)} (h : NCOut P D M A B) : NCOut P D M B A :=
  ⟨h.2.1, h.1, by
    obtain ⟨a, ha, b, hb, hne⟩ := h.2.2
    exact ⟨b, hb, a, ha, fun e => hne e.symm⟩⟩

omit [Finite V] in
theorem compOf_eq_of_mem {A B : Subgroup (MulAut V)} (hB : B ∈ compOf P D M A) :
    compOf P D M B = compOf P D M A := by
  have hBA : A ∈ compOf P D M B := by
    have key : ∀ {X Y : Subgroup (MulAut V)}, Relation.ReflTransGen (NCOut P D M) X Y →
        Relation.ReflTransGen (NCOut P D M) Y X := by
      intro X Y hXY
      induction hXY with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih => exact Relation.ReflTransGen.head hbc.symm ih
    exact key hB
  ext C
  constructor
  · intro hC
    exact hB.trans hC
  · intro hC
    exact hBA.trans hC

omit [Finite V] in
theorem comp_ne_comm {A B X Y : Subgroup (MulAut V)} (hA : A ∈ dOut P D M) (hB : B ∈ dOut P D M)
    (hAB : compGen P D M A ≠ compGen P D M B) (hX : X ∈ compOf P D M A)
    (hY : Y ∈ compOf P D M B) :
    X ≠ Y ∧ ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
  have hXout := compOf_subset hA hX
  have hYout := compOf_subset hB hY
  have hnot : Y ∉ compOf P D M X := by
    intro hYX
    apply hAB
    have h1 := compOf_eq_of_mem hX
    have h2 := compOf_eq_of_mem hY
    have h3 := compOf_eq_of_mem hYX
    have : compOf P D M A = compOf P D M B := by rw [← h1, ← h3, h2]
    unfold compGen
    rw [this]
  refine ⟨fun e => hnot (e ▸ mem_compOf_self), ?_⟩
  exact comm_of_not_mem_compOf hXout hYout hnot

theorem compGen_mem_lamSet {T : Subgroup (MulAut V)}
    (h : Hyp43 P D T M) (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (hA : A ∈ dOut P D M) (hqA : 3 ≤ Nat.card A) : compGen P D M A ∈ lamSet P D M := by
  obtain ⟨L, hL, hAL, hall⟩ := exists_sl_comp h hV hA hqA
  rw [compGen_eq h hA hL hAL hall]
  exact hL

theorem sl_type_of_mem_lamSet {L : Subgroup (MulAut V)} (h : Hyp41 P D)
    (hL : L ∈ lamSet P D M) :
    ∃ n : ℕ, 1 ≤ n ∧ IsSLNatSection L (commV L) (commV L ⊓ fixV L) n ∧
      commV L ⊔ fixV L = ⊤ ∧ ∀ B, B ∈ dInter D L ↔ IsSylowOf 2 B L := by
  have hL' := hL
  obtain ⟨-, ⟨n, hn1, hSL⟩, hΛ2, -⟩ := hL'
  have htop := hSL.commV_sup_fixV hn1 (h.sylowGood_of_lamSet hL)
  have hinv : ∀ x ∈ L, ∀ p ∈ commV L, x p ∈ commV L := by
    intro x hx p hp
    have h1 : (commV L).map x.toMonoidHom = commV L := by
      rw [← B19.commV_map_conj]
      congr 1
      exact conjSub_self_of_mem hx
    have : x p ∈ (commV L).map x.toMonoidHom := ⟨p, hp, rfl⟩
    rwa [h1] at this
  exact ⟨n, hn1, hSL.of_sup_eq_top hinv htop, htop, hΛ2⟩

end Generators
section Main

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))} {M : Subgroup (MulAut V)}

theorem four_eighteen_struct {T : Subgroup (MulAut V)} (h : Hyp43 P D T M)
    (hcen : ∀ A ∈ dOut P D M, ∀ x ∈ compGen P D M A,
      (∀ y ∈ compGen P D M A, y * x = x * y) → x = 1) :
    D = dCore P D M ∪ ⋃ A ∈ dOut P D M, dInter D (compGen P D M A) ∧
    (⨆ A ∈ D, A : Subgroup (MulAut V)) =
      (⨆ C ∈ dCore P D M, C) ⊔ ⨆ A ∈ dOut P D M, compGen P D M A ∧
    (∀ A ∈ dOut P D M, ∀ B ∈ dOut P D M, compGen P D M A ≠ compGen P D M B →
      ∀ x ∈ compGen P D M A, ∀ y ∈ compGen P D M B, x * y = y * x) ∧
    (∀ A ∈ dOut P D M, ∀ C ∈ dCore P D M, ∀ x ∈ compGen P D M A, ∀ y ∈ C, x * y = y * x) ∧
    (∀ A ∈ dOut P D M, Disjoint (compGen P D M A) ((⨆ C ∈ dCore P D M, C) ⊔
      ⨆ B ∈ {B | B ∈ dOut P D M ∧ compGen P D M B ≠ compGen P D M A}, compGen P D M B)) ∧
    (∀ A ∈ dOut P D M, ∀ B ∈ dOut P D M, compGen P D M A ≠ compGen P D M B →
      commV (compGen P D M A) ≤ fixV (compGen P D M B)) ∧
    (∀ A ∈ dOut P D M, ∀ C ∈ dCore P D M, commV (compGen P D M A) ≤ fixV C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    ext B
    constructor
    · intro hB
      by_cases hc : B ∈ dCore P D M
      · exact Or.inl hc
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨B, ⟨hB, hc⟩, hB, le_compGen⟩)
    · rintro (hc | hmem)
      · exact hc.1
      · obtain ⟨A, -, hB⟩ := Set.mem_iUnion₂.1 hmem
        exact hB.1
  ·
    refine le_antisymm (iSup₂_le fun B hB => ?_) (sup_le (iSup₂_le fun C hC => ?_)
      (iSup₂_le fun A hA => ?_))
    · by_cases hc : B ∈ dCore P D M
      · exact le_sup_of_le_left
          (le_iSup₂_of_le (f := fun (X : Subgroup (MulAut V)) (_ : X ∈ dCore P D M) => X) B hc
            le_rfl)
      · exact le_sup_of_le_right
          (le_trans (le_compGen (P := P) (D := D) (M := M) (A := B))
            (le_iSup₂_of_le (f := fun (X : Subgroup (MulAut V)) (_ : X ∈ dOut P D M) =>
              compGen P D M X) B ⟨hB, hc⟩ le_rfl))
    · exact le_iSup₂_of_le (f := fun (X : Subgroup (MulAut V)) (_ : X ∈ D) => X) C hC.1 le_rfl
    · unfold compGen
      exact iSup₂_le fun B hB =>
        le_iSup₂_of_le (f := fun (X : Subgroup (MulAut V)) (_ : X ∈ D) => X) B
          (compOf_subset hA hB).1 le_rfl
  ·
    intro A hA B hB hAB
    exact comm_of_iSup_comm (S := compOf P D M A) (S' := compOf P D M B)
      (fun X hX Y hY => (comp_ne_comm hA hB hAB hX hY).2)
  ·
    intro A hA C hC x hx y hy
    have : compGen P D M A ≤ Subgroup.centralizer ({y} : Set (MulAut V)) := by
      unfold compGen
      refine iSup₂_le fun X hX x hx => ?_
      exact Subgroup.mem_centralizer_singleton_iff.2
        (h.toHyp41.comm_of_mem_dCore hC (compOf_subset hA hX) y hy x hx).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (this hx)
  ·
    intro A hA
    rw [Subgroup.disjoint_def]
    intro x hx hx'
    have hcen' : (⨆ C ∈ dCore P D M, C) ⊔
        (⨆ B ∈ {B | B ∈ dOut P D M ∧ compGen P D M B ≠ compGen P D M A}, compGen P D M B) ≤
        Subgroup.centralizer (compGen P D M A : Set (MulAut V)) := by
      refine sup_le (iSup₂_le fun C hC c hc => ?_) (iSup₂_le fun B hB b hb => ?_)
      · refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
        exact comm_of_iSup_comm (S := compOf P D M A) (S' := {C})
          (fun X hX Y hY x hx y hy => by
            rw [Set.mem_singleton_iff] at hY
            subst hY
            exact (h.toHyp41.comm_of_mem_dCore hC (compOf_subset hA hX) y hy x hx).symm)
          e he c (by simpa using (le_iSup₂_of_le (f := fun (X : Subgroup (MulAut V))
            (_ : X ∈ ({C} : Set (Subgroup (MulAut V)))) => X) C rfl le_rfl) hc)
      · refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
        exact comm_of_iSup_comm (S := compOf P D M A) (S' := compOf P D M B)
          (fun X hX Y hY => (comp_ne_comm hA hB.1 (Ne.symm hB.2) hX hY).2) e he b hb
    exact hcen A hA x hx fun y hy => Subgroup.mem_centralizer_iff.1 (hcen' hx') y hy
  ·
    intro A hA B hB hAB
    exact commV_iSup_le_fixV (S := compOf P D M A) (S' := compOf P D M B)
      fun X hX Y hY => by
        have hXY := comp_ne_comm hA hB hAB hX hY
        have hX' := (compOf_subset hA hX).1
        have hY' := (compOf_subset hB hY).1
        have hq6 := (four_six h.toHyp41 hX' hY' hXY.1 hXY.2).2
        exact (B19.commV_mono le_sup_left).trans (hq6.trans (fixV_anti le_sup_right))
  · intro A hA C hC
    have := commV_iSup_le_fixV (S := compOf P D M A) (S' := ({C} : Set (Subgroup (MulAut V))))
      fun X hX Y hY => by
        rw [Set.mem_singleton_iff] at hY
        subst hY
        have hXo := compOf_subset hA hX
        have hne : X ≠ Y := fun e => hXo.2 (e ▸ hC)
        have hcomm := fun x hx y hy => (h.toHyp41.comm_of_mem_dCore hC hXo y hy x hx).symm
        have hq6 := (four_six h.toHyp41 hXo.1 hC.1 hne hcomm).2
        exact (B19.commV_mono le_sup_left).trans (hq6.trans (fixV_anti le_sup_right))
    unfold compGen
    simpa using this

end Main

end CFSG.CGT.PushingUpLit.BHS

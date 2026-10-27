module

public import CFSG.CGT.PushingUpLit.BHS.FourThreeD
public import CFSG.CGT.PushingUpLit.BHS.FourThreeA
public import CFSG.CGT.PushingUpLit.BHS.FourThreeC
public import CFSG.CGT.PushingUpLit.BHS.FourTwo

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def redSet (D : Set (Subgroup (MulAut V))) (N : Subgroup (MulAut V))
    (U : Set (Subgroup (MulAut V))) : Set (Subgroup (MulAut V)) :=
  {X | X ∈ D ∧ X ≤ N ∧ X ∉ U}

namespace Hyp42

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)}
  {U : Set (Subgroup (MulAut V))}

omit [Finite V] in
theorem redSet_conj (h : Hyp42 P D T M) {g : MulAut V} (hg : g ∈ setNormalizer P U)
    {X : Subgroup (MulAut V)} (hX : X ∈ redSet D (setNormalizer P U) U) :
    conjSub g X ∈ redSet D (setNormalizer P U) U := by
  refine ⟨h.conj_mem X hX.1 g hg.1, ?_, fun hU => hX.2.2 ?_⟩
  · have := conjSub_mono g hX.2.1
    rwa [conjSub_self_of_mem hg] at this
  · exact (hg.2 X).2 hU

theorem comm_of_mem_redSet (h : Hyp42 P D T M) (hU : U ⊆ dInter D T) {C X : Subgroup (MulAut V)}
    (hC : C ∈ U) (hX : X ∈ redSet D (setNormalizer P U) U) :
    ∀ c ∈ C, ∀ x ∈ X, c * x = x * c := by
  rcases h.toHyp41.four_eight_conj (hU hC).1 hX.1 with hc | ⟨g, hg, hXg⟩
  · exact hc
  · exfalso
    have hgN : g ∈ setNormalizer P U :=
      (sup_le (h.le_setNormalizer hU (hU hC)) hX.2.1) hg
    exact hX.2.2 (hXg ▸ (hgN.2 C).1 hC)

end Hyp42

theorem four_eleven {P : Subgroup (MulAut V)}
    {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)} (h : Hyp42 P D T M)
    (hV : ∀ v : V, v ^ 2 = 1) {U : Set (Subgroup (MulAut V))} (hU : U ⊆ dInter D T)
    (hN : ¬ setNormalizer P U ≤ M)
    (hmax : ∀ S : Set (Subgroup (MulAut V)), S ⊆ dInter D T → U ⊆ S →
      ¬ setNormalizer P S ≤ M → S = U) :
    (∃ B ∈ D, B ≤ setNormalizer P U ∧ ¬ B ≤ M) ∧
    (∃ A ∈ D, A ≤ M ∧ A ≤ setNormalizer P U ∧ A ∉ U) ∧
    ∀ A ∈ D, A ≤ M → A ≤ setNormalizer P U → A ∉ U → ∀ B ∈ D, B ≤ setNormalizer P U →
      ¬ B ≤ M → A ⊔ B ∈ lamSet P D M ∧ A ⊔ B ≤ setNormalizer P U := by
  set N : Subgroup (MulAut V) := setNormalizer P U with hNdef
  have hNP : N ≤ P := fun g hg => hg.1
  have hAN : ∀ A ∈ dInter D T, A ≤ N := fun A hA => h.le_setNormalizer hU hA
  have hUM : ∀ A ∈ U, A ≤ M := fun A hA => (hU hA).2.trans h.le_M
  have hAN' := hAN
  have hi := h.exists_mem_dInter_not_le hU hN
  refine ⟨hi, ?_, ?_⟩
  ·
    by_contra hno
    push Not at hno
    have hEq : U = dInter D T := Set.Subset.antisymm hU fun A hA =>
      hno A hA.1 (hA.2.trans h.le_M) (hAN A hA)
    exact hN (by rw [hNdef, hEq]; exact h.normSet_le)
  · intro A hA hAM hAN hAU B hB hBN hBM
    obtain ⟨B₀, hB₀D, hB₀N, hB₀M⟩ := hi
    set D₁ : Set (Subgroup (MulAut V)) := redSet D N U with hD₁
    set P₁ : Subgroup (MulAut V) := ⨆ X ∈ D₁, X with hP₁
    have hD₁le : ∀ X ∈ D₁, X ≤ P₁ := fun X hX =>
      le_iSup₂_of_le (f := fun (Y : Subgroup (MulAut V)) (_ : Y ∈ D₁) => Y) X hX le_rfl
    have hP₁N : P₁ ≤ N := iSup₂_le fun X hX => hX.2.1
    have hnorm : ∀ X ∈ D₁, ∀ g ∈ N, conjSub g X ∈ D₁ := fun X hX g hg => h.redSet_conj hg hX
    have hD₁sub : D₁ ⊆ dInter D N := fun X hX => ⟨hX.1, hX.2.1⟩
    obtain ⟨T₀, hdT₀, hH⟩ := four_nine h hNP (fun A' hA' => ⟨hA'.1, hAN' A' hA'⟩)
      (fun hsub => hB₀M (hsub ⟨hB₀D, hB₀N⟩).2)
    have hB₀D₁ : B₀ ∈ D₁ := ⟨hB₀D, hB₀N, fun hu => hB₀M (hUM B₀ hu)⟩
    have hcore : ¬ D₁ ⊆ dCore N (dInter D N) (M ⊓ N) := fun hsub => by
      have := (hsub hB₀D₁).2 1 N.one_mem
      rw [conjSub_one] at this
      exact hB₀M (this.trans inf_le_left)
    have hH₁ := hH.restrict_normalSet hD₁sub hnorm hcore
    have hMeq : (M ⊓ N) ⊓ P₁ = M ⊓ P₁ := by rw [inf_assoc, inf_eq_right.2 hP₁N]
    rw [hMeq] at hH₁
    set T₁ : Subgroup (MulAut V) := P₁ ⊓ T₀ with hT₁
    set M₁ : Subgroup (MulAut V) := M ⊓ P₁ with hM₁
    have hdT₁ : ∀ X ∈ dInter D₁ T₁, X ∈ dInter D T ∧ X ∉ U := fun X hX =>
      ⟨by rw [← hdT₀]; exact ⟨hX.1.1, hX.2.trans inf_le_right⟩, hX.1.2.2⟩
    have huniq : ∀ X ∈ D₁, X ≤ M₁ → ∀ g ∈ P₁, X ≤ conjSub g M₁ → conjSub g M₁ = M₁ := by
      intro X hX hXM g hg hXg
      have hT₁M : IsSylowOf 2 T₁ M₁ := isSylowOf_of_le_of_le hH₁.syl hH₁.le_M hH₁.M_le
      obtain ⟨k, hkM, hk⟩ := Glauberman.exists_conj_le_of_isSylowOf hT₁M
        (isPGroup_of_isElemAbelian2 (hH₁.elemAb X hX)) hXM
      have hkP₁ : k ∈ P₁ := hH₁.M_le hkM
      have hX'D₁ : conjSub k X ∈ D₁ := hnorm X hX k (hP₁N hkP₁)
      have hX'T₁ : conjSub k X ≤ T₁ := hk
      obtain ⟨hX'T, hX'U⟩ := hdT₁ _ ⟨hX'D₁, hX'T₁⟩
      have hlm : setNormalizer P₁ {conjSub k X} ≤ M₁ := by
        intro n hn
        have hnN : n ∈ N := hP₁N hn.1
        have hfix : conjSub n (conjSub k X) = conjSub k X := (hn.2 _).1 rfl
        have hSsub : U ∪ {conjSub k X} ⊆ dInter D T :=
          Set.union_subset hU (Set.singleton_subset_iff.2 hX'T)
        have hnS : n ∈ setNormalizer P (U ∪ {conjSub k X}) := by
          refine ⟨hNP hnN, fun B' => ⟨fun hB' => ?_, fun hB' => ?_⟩⟩
          · rcases hB' with hB'U | hB'X
            · exact Or.inl ((hnN.2 B').1 hB'U)
            · right
              rw [Set.mem_singleton_iff] at hB'X ⊢
              rw [hB'X]
              exact hfix
          · rcases hB' with hB'U | hB'X
            · exact Or.inl ((hnN.2 B').2 hB'U)
            · right
              rw [Set.mem_singleton_iff] at hB'X ⊢
              have h1 : conjSub n⁻¹ (conjSub k X) = conjSub k X := by
                have := congrArg (conjSub n⁻¹) hfix
                rw [FourTwoTools.conjSub_inv_conjSub] at this
                exact this.symm
              calc B' = conjSub n⁻¹ (conjSub n B') := (FourTwoTools.conjSub_inv_conjSub n B').symm
                _ = conjSub n⁻¹ (conjSub k X) := by rw [hB'X]
                _ = conjSub k X := h1
        have hSM : setNormalizer P (U ∪ {conjSub k X}) ≤ M := by
          by_contra hnot
          have heq := hmax (U ∪ {conjSub k X}) hSsub Set.subset_union_left hnot
          refine hX'U ?_
          rw [← heq]
          exact Or.inr rfl
        exact ⟨hSM hnS, hn.1⟩
      have hg' : k * g ∈ P₁ := P₁.mul_mem hkP₁ hg
      have hX'g : ∀ A' ∈ ({conjSub k X} : Set (Subgroup (MulAut V))),
          A' ≤ conjSub (k * g) M₁ := by
        intro A' hA'
        rw [Set.mem_singleton_iff] at hA'
        rw [hA', conjSub_mul]
        exact conjSub_mono k hXg
      have hres := hH₁.conjSub_eq_of_le_conjSub
        (U := {conjSub k X}) (Set.singleton_subset_iff.2 ⟨hX'D₁, hX'T₁⟩) hlm hg' hX'g
      rw [conjSub_mul] at hres
      have h2 := congrArg (conjSub k⁻¹) hres
      rw [FourTwoTools.conjSub_inv_conjSub, conjSub_self_of_mem (M₁.inv_mem hkM)] at h2
      exact h2
    have hLM : LocMax P₁ D₁ M₁ :=
      { hyp := hH₁.toHyp41
        M_le := inf_le_right
        uniq := huniq
        self := fun g hg hgM => hH₁.mem_of_conjSub_eq hg hgM
        cen := fun R hR hR2 => hH₁.cenIn_le_of_le_M le_rfl hR hR2 }
    have hA₁ : A ∈ D₁ := ⟨hA, hAN, hAU⟩
    have hB₁ : B ∈ D₁ := ⟨hB, hBN, fun hu => hBM (hUM B hu)⟩
    have hA₁M : A ≤ M₁ := le_inf hAM (hD₁le A hA₁)
    have hB₁M : ¬ B ≤ M₁ := fun hle => hBM (hle.trans inf_le_left)
    have hΛ := hLM.sup_mem_lamSet hV hA₁ hA₁M hB₁ hB₁M
    refine ⟨?_, sup_le hAN hBN⟩
    obtain ⟨hLP₁, ⟨n, hn1, hSL⟩, hΛ2, hΛ3⟩ := hΛ
    have hLP : A ⊔ B ≤ P := (hLP₁.trans hP₁N).trans hNP
    have hΛ2' : ∀ X : Subgroup (MulAut V), X ∈ dInter D (A ⊔ B) ↔ IsSylowOf 2 X (A ⊔ B) := by
      intro X
      constructor
      · rintro ⟨hXD, hXL⟩
        have hXD₁ : X ∈ D₁ := by
          refine ⟨hXD, hXL.trans (hLP₁.trans hP₁N), fun hXU => ?_⟩
          have hP₁c : P₁ ≤ Subgroup.centralizer (X : Set (MulAut V)) :=
            iSup₂_le fun Y hY y hy => by
              rw [Subgroup.mem_centralizer_iff]
              intro z hz
              exact h.comm_of_mem_redSet hU hXU hY z hz y hy
          refine (h.ne_bot X hXD (eq_bot_iff.2 fun x hx => ?_)).elim
          have := hSL.center_eq_bot hn1 (hXL hx) fun y hy =>
            (Subgroup.mem_centralizer_iff.1 (hP₁c (hLP₁ hy)) x hx).symm
          rw [this]
          exact (Subgroup.mem_bot).2 rfl
        exact (hΛ2 X).1 ⟨hXD₁, hXL⟩
      · intro hXs
        exact ⟨((hΛ2 X).2 hXs).1.1, hXs.1⟩
    have hD₁L : ∀ X ∈ dInter D (A ⊔ B), X ∈ dInter D₁ (A ⊔ B) := fun X hX =>
      (hΛ2 X).2 ((hΛ2' X).1 hX)
    have hms : ∀ X Y : Subgroup (MulAut V), Y ≤ P₁ → mSet P M X = mSet P M Y →
        mSet P₁ M₁ X ⊆ mSet P₁ M₁ Y := by
      rintro X Y hY heq Z ⟨⟨g, hg, hZ⟩, hXZ⟩
      have hgP : g ∈ P := hNP (hP₁N hg)
      have hZg : Z ≤ conjSub g M := hZ ▸ conjSub_mono g inf_le_left
      have hmem : conjSub g M ∈ mSet P M X := ⟨⟨g, hgP, rfl⟩, hXZ.trans hZg⟩
      rw [heq] at hmem
      have hYZ : Y ≤ Z := by
        rw [hZ, hM₁, conjSub_inf, conjSub_self_of_mem hg]
        exact le_inf hmem.2 hY
      exact ⟨⟨g, hg, hZ⟩, hYZ⟩
    refine ⟨hLP, ⟨n, hn1, hSL⟩, hΛ2', fun X hX Y hY hXY heq => hΛ3 X (hD₁L X hX) Y (hD₁L Y hY)
      hXY (Set.Subset.antisymm (hms X Y (hY.2.trans hLP₁) heq)
        (hms Y X (hX.2.trans hLP₁) heq.symm))⟩

end CFSG.CGT.PushingUpLit.BHS

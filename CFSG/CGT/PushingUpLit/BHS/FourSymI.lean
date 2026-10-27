module

public import CFSG.CGT.PushingUpLit.BHS.FourSymH

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits
  CFSG.Quasithin.G6

variable {V : Type} [CommGroup V] [Finite V]

section Comp

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))} {M A : Subgroup (MulAut V)}

theorem compOf_card (h : Hyp41 P D) {n : ℕ} (hA2 : Nat.card A = n) :
    ∀ B ∈ compOf P D M A, Nat.card B = n := by
  intro B hB
  induction hB with
  | refl => exact hA2
  | tail _ hbc ih =>
    rcases h.four_eight_conj hbc.1.1 hbc.2.1.1 with hcomm | ⟨g, -, hg⟩
    · exfalso
      obtain ⟨a, ha, b, hb, hne⟩ := hbc.2.2
      exact hne (hcomm a ha b hb)
    · rw [hg]
      exact (card_conjSub _ _).trans ih

omit [Finite V] in
theorem connD_compOf : ConnD (compOf P D M A) := by
  have hlift : ∀ X, Relation.ReflTransGen (NCOut P D M) A X →
      Relation.ReflTransGen (fun U W => U ∈ compOf P D M A ∧ W ∈ compOf P D M A ∧ NonComm U W)
        A X := by
    intro X hX
    induction hX with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
      exact ih.tail ⟨hab, hab.tail hbc, hbc.2.2⟩
  have hsymm : ∀ X Y, Relation.ReflTransGen
      (fun U W => U ∈ compOf P D M A ∧ W ∈ compOf P D M A ∧ NonComm U W) X Y →
      Relation.ReflTransGen
        (fun U W => U ∈ compOf P D M A ∧ W ∈ compOf P D M A ∧ NonComm U W) Y X := by
    intro X Y hXY
    induction hXY with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, hbc.2.2.symm'⟩ ih
  intro X hX Y hY
  exact (hsymm _ _ (hlift X hX)).trans (hlift Y hY)

omit [Finite V] in
theorem dOut_conj (h : Hyp41 P D) {X : Subgroup (MulAut V)} (hX : X ∈ dOut P D M) {g : MulAut V}
    (hg : g ∈ P) : conjSub g X ∈ dOut P D M := by
  refine ⟨h.conj_mem X hX.1 g hg, fun hcore => hX.2 ?_⟩
  have := h.conjSub_mem_dCore hcore (P.inv_mem hg)
  rwa [FourTwoTools.conjSub_inv_conjSub] at this

theorem compOf_comm_of_not_mem (h : Hyp41 P D) (hA : A ∈ dOut P D M) {X : Subgroup (MulAut V)}
    (hX : X ∈ D) (hXc : X ∉ compOf P D M A) :
    ∀ x ∈ X, ∀ e ∈ compGen P D M A, x * e = e * x := by
  intro x hx e he
  have hmem : ∀ Y ∈ compOf P D M A, ∀ y ∈ Y, ∀ x ∈ X, x * y = y * x := by
    intro Y hY y hy x hx
    by_cases hXout : X ∈ dOut P D M
    · have hYout := compOf_subset hA hY
      have hnot : X ∉ compOf P D M Y := by
        rw [compOf_eq_of_mem hY]
        exact hXc
      exact (comm_of_not_mem_compOf hYout hXout hnot y hy x hx).symm
    · have hXcore : X ∈ dCore P D M := by
        by_contra hnc
        exact hXout ⟨hX, hnc⟩
      exact h.comm_of_mem_dCore hXcore (compOf_subset hA hY) x hx y hy
  have key := comm_of_iSup_comm (S := ({X} : Set (Subgroup (MulAut V))))
    (S' := compOf P D M A) (fun X' hX' Y hY x' hx' y' hy' => by
      rw [Set.mem_singleton_iff] at hX'
      subst hX'
      exact hmem Y hY y' hy' x' hx')
  exact key x (le_iSup₂_of_le (f := fun (Z : Subgroup (MulAut V))
    (_ : Z ∈ ({X} : Set (Subgroup (MulAut V)))) => Z) X rfl le_rfl hx) e he

theorem compOf_normalizes (h : Hyp41 P D) (hV : ∀ v : V, v ^ 2 = 1) (hA : A ∈ dOut P D M)
    (hA2 : Nat.card A = 2) : compGen P D M A ≤ setNormalizer P (compOf P D M A) := by
  have hgen : ∀ X ∈ compOf P D M A, ∀ g ∈ X, ∀ A' ∈ compOf P D M A,
      conjSub g A' ∈ compOf P D M A := by
    intro X hX g hg A' hA'
    by_cases hcom : ∀ x ∈ A', g * x = x * g
    · rw [FourOneTools.conjSub_eq_of_comm hcom]
      exact hA'
    · push Not at hcom
      obtain ⟨x, hx, hne⟩ := hcom
      have hg1 : g ≠ 1 := fun e => hne (by rw [e]; simp)
      have hXout := compOf_subset hA hX
      have hA'out := compOf_subset hA hA'
      have hnc : NonComm A' X := ⟨x, hx, g, hg, fun e => hne e.symm⟩
      have hnc2 := h.noncomm_conj hV hA'out.1 hXout.1 (compOf_card h hA2 A' hA')
        (compOf_card h hA2 X hX) hnc hg hg1
      exact hA'.tail ⟨hA'out, dOut_conj h hA'out (h.le X hXout.1 hg), hnc2⟩
  refine iSup₂_le fun X hX g hg => ⟨h.le X (compOf_subset hA hX).1 hg, fun A' => ⟨?_, ?_⟩⟩
  · exact hgen X hX g hg A'
  · intro hc
    have := hgen X hX g⁻¹ (X.inv_mem hg) _ hc
    rwa [FourTwoTools.conjSub_inv_conjSub] at this

theorem hyp43_compOf {T : Subgroup (MulAut V)} (h : Hyp43 P D T M) (hV : ∀ v : V, v ^ 2 = 1)
    (hP : P = ⨆ X ∈ D, X) (hA : A ∈ dOut P D M) (hA2 : Nat.card A = 2) :
    ∃ T' : Subgroup (MulAut V),
      Hyp43 (compGen P D M A) (compOf P D M A) T' (M ⊓ compGen P D M A) := by
  set D' := compOf P D M A with hD'
  set E := compGen P D M A with hE
  have hD'D : D' ⊆ D := fun X hX => (compOf_subset hA hX).1
  have hleE : ∀ X ∈ D', X ≤ E := fun X hX =>
    le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V)) (_ : B ∈ D') => B) X hX le_rfl
  have hEP : E ≤ P := iSup₂_le fun X hX => h.le X (hD'D hX)
  have hcomm : ∀ X ∈ D, X ∉ D' → ∀ x ∈ X, ∀ e ∈ E, x * e = e * x := fun X hX hXc =>
    compOf_comm_of_not_mem h.toHyp41 hA hX hXc
  have hNE : E ≤ setNormalizer P D' := compOf_normalizes h.toHyp41 hV hA hA2
  have hnormD' : ∀ g ∈ E, ∀ X ∈ D', conjSub g X ∈ D' := fun g hg X hX => ((hNE hg).2 X).1 hX
  set Dt : Set (Subgroup (MulAut V)) := {X | ∃ g ∈ P, ∃ Y ∈ D', X = conjSub g Y} with hDt
  have hDtD : Dt ⊆ D := by
    rintro _ ⟨g, hg, Y, hY, rfl⟩
    exact h.conj_mem Y (hD'D hY) g hg
  have hDtnorm : ∀ X ∈ Dt, ∀ g ∈ P, conjSub g X ∈ Dt := by
    rintro _ ⟨g, hg, Y, hY, rfl⟩ g' hg'
    exact ⟨g' * g, P.mul_mem hg' hg, Y, hY, by rw [conjSub_mul]⟩
  have hD'Dt : D' ⊆ Dt := fun X hX => ⟨1, P.one_mem, X, hX, (conjSub_one X).symm⟩
  have hDtcore : ¬ Dt ⊆ dCore P D M := fun hsub => hA.2 (hsub (hD'Dt mem_compOf_self))
  obtain ⟨T₀, hH42⟩ := four_ten h.toHyp42 hDtD hDtnorm hDtcore
  set P₀ := ⨆ X ∈ Dt, X with hP₀
  have hEP₀ : E ≤ P₀ := iSup₂_le fun X hX =>
    le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V)) (_ : B ∈ Dt) => B) X (hD'Dt hX) le_rfl
  have hDtle : ∀ X ∈ Dt, X ≤ P₀ := fun X hX =>
    le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V)) (_ : B ∈ Dt) => B) X hX le_rfl
  have hP₀norm : P₀ ≤ Subgroup.normalizer (E : Set (MulAut V)) := by
    refine iSup₂_le fun X hX => ?_
    by_cases hXD' : X ∈ D'
    · exact (hleE X hXD').trans (Subgroup.le_normalizer)
    · refine le_trans (fun x hx => ?_) (Subgroup.centralizer_le_normalizer (E : Set (MulAut V)))
      exact Subgroup.mem_centralizer_iff.2 fun e he => (hcomm X (hDtD hX) hXD' x hx e he).symm
  have hSyl : IsSylowOf 2 (E ⊓ T₀) E :=
    FourTwoTools.isSylowOf_inf_of_le_normalizer hH42.syl hEP₀ hP₀norm
  have hexE : ∀ g ∈ P, ∀ X : Subgroup (MulAut V), X ≤ E → ∃ e ∈ E, conjSub g X = conjSub e X := by
    let S : Subgroup (MulAut V) :=
      { carrier := {g | ∀ X : Subgroup (MulAut V), X ≤ E → ∃ e ∈ E, conjSub g X = conjSub e X}
        one_mem' := fun X _ => ⟨1, E.one_mem, rfl⟩
        mul_mem' := by
          rintro g₁ g₂ h₁ h₂ X hX
          obtain ⟨e₂, he₂, h2⟩ := h₂ X hX
          have hX' : conjSub e₂ X ≤ E := (conjSub_mono e₂ hX).trans (conjSub_self_of_mem he₂).le
          obtain ⟨e₁, he₁, h1⟩ := h₁ _ hX'
          refine ⟨e₁ * e₂, E.mul_mem he₁ he₂, ?_⟩
          rw [conjSub_mul, h2, h1, conjSub_mul]
        inv_mem' := by
          rintro g hg X hX
          obtain ⟨e₀, he₀, hE₀⟩ := hg E le_rfl
          have hgE : conjSub g E = E := by rw [hE₀]; exact conjSub_self_of_mem he₀
          have hginvE : conjSub g⁻¹ E = E := by
            conv_lhs => rw [← hgE]
            exact FourTwoTools.conjSub_inv_conjSub g E
          have hY : conjSub g⁻¹ X ≤ E := (conjSub_mono g⁻¹ hX).trans hginvE.le
          obtain ⟨e, he, h1⟩ := hg _ hY
          rw [FourTwoTools.conjSub_conjSub_inv] at h1
          refine ⟨e⁻¹, E.inv_mem he, ?_⟩
          calc conjSub g⁻¹ X = conjSub e⁻¹ (conjSub e (conjSub g⁻¹ X)) :=
                (FourTwoTools.conjSub_inv_conjSub e _).symm
            _ = conjSub e⁻¹ X := by rw [← h1] }
    have hPS : P ≤ S := by
      rw [hP]
      refine iSup₂_le fun X hX g hg Y hY => ?_
      by_cases hXD' : X ∈ D'
      · exact ⟨g, hleE X hXD' hg, rfl⟩
      · refine ⟨1, E.one_mem, ?_⟩
        rw [conjSub_one]
        exact FourOneTools.conjSub_eq_of_comm fun y hy =>
          (hcomm X hX hXD' g hg y (hY hy))
    exact fun g hg => hPS hg
  refine ⟨E ⊓ T₀, ⟨⟨h.toHyp41.restrict hD'D hleE fun X hX g hg => hnormD' g hg X hX, hSyl, ?_,
    inf_le_right, ?_, ?_, ?_⟩, ?_⟩⟩
  · exact le_inf (inf_le_right.trans (hH42.le_M.trans inf_le_left)) inf_le_left
  ·
    intro heq
    have hAc : A ∈ dCore E D' (M ⊓ E) := heq ▸ (mem_compOf_self : A ∈ D')
    apply hA.2
    refine ⟨hA.1, fun g hg => ?_⟩
    obtain ⟨e, he, h1⟩ := hexE g⁻¹ (P.inv_mem hg) A (hleE A mem_compOf_self)
    have h2 : conjSub e A ≤ M := by
      have := conjSub_mono e (hAc.2 e⁻¹ (E.inv_mem he))
      rw [FourTwoTools.conjSub_conjSub_inv] at this
      exact this.trans inf_le_left
    have h3 : conjSub g⁻¹ A ≤ M := h1 ▸ h2
    have h4 := conjSub_mono g h3
    rwa [FourTwoTools.conjSub_conjSub_inv] at h4
  ·
    intro n hn
    have key : ∀ m ∈ setNormalizer E (dInter D' (E ⊓ T₀)), ∀ A', A' ∈ dInter Dt T₀ →
        conjSub m A' ∈ dInter Dt T₀ := by
      intro m hm A' hA'
      by_cases hA'D' : A' ∈ D'
      · have hAT' : A' ∈ dInter D' (E ⊓ T₀) := ⟨hA'D', le_inf (hleE A' hA'D') hA'.2⟩
        have h1 := (hm.2 A').1 hAT'
        exact ⟨hD'Dt h1.1, h1.2.trans inf_le_right⟩
      · have hc := hcomm A' (hDtD hA'.1) hA'D'
        have e : conjSub m A' = A' :=
          FourOneTools.conjSub_eq_of_comm fun x hx => (hc x hx m hm.1).symm
        rw [e]
        exact hA'
    have hnP₀ : n ∈ setNormalizer P₀ (dInter Dt T₀) := by
      refine ⟨hEP₀ hn.1, fun A' => ⟨key n hn A', fun hA' => ?_⟩⟩
      have := key n⁻¹ ((setNormalizer E (dInter D' (E ⊓ T₀))).inv_mem hn) _ hA'
      rwa [FourTwoTools.conjSub_inv_conjSub] at this
    exact ⟨(hH42.normSet_le hnP₀).1, hn.1⟩
  ·
    intro n hn
    have hnP₀ : n ∈ cenIn P₀ (fixV T₀) :=
      ⟨hEP₀ hn.1, fun u hu => hn.2 u (fixV_anti inf_le_right hu)⟩
    exact ⟨(hH42.cen_le hnP₀).1, hn.1⟩
  · exact fun X hX Z hZ hZE => h.max X (hD'D hX) Z hZ (hZE.trans hEP)

end Comp

section Final

variable {D : Set (Subgroup (MulAut V))} {E : Subgroup (MulAut V)} {m : ℕ}

omit [Finite V] in
theorem SymCore.eq_one_of_central (d : SymCore D E m) {x : MulAut V} (hx : x ∈ E)
    (hc : ∀ y ∈ E, y * x = x * y) : x = 1 := by
  have h1 : d.θ ⟨x, hx⟩ = 1 := by
    refine perm_eq_one_of_central d.three_le fun τ => ?_
    obtain ⟨y, rfl⟩ := d.θ.surjective τ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc y y.2)
  have h2 : (⟨x, hx⟩ : ↥E) = 1 := d.θ.injective (h1.trans (map_one d.θ).symm)
  exact congrArg Subtype.val h2

theorem bhsSymType : ∀ (V : Type) [CommGroup V] [Finite V]
    (P : Subgroup (MulAut V)) (D : Set (Subgroup (MulAut V))) (T M : Subgroup (MulAut V)),
    Hyp43 P D T M → (∀ v : V, v ^ 2 = 1) → P = ⨆ A ∈ D, A →
    ∀ A ∈ dOut P D M, Nat.card A = 2 → SymType M D (compGen P D M A) := by
  intro V _ _ P D T M h hV hP A hA hA2
  obtain ⟨T', hh⟩ := hyp43_compOf h hV hP hA hA2
  obtain ⟨m, ⟨d⟩⟩ := symMain hV _ (compGen P D M A) (compOf P D M A) T' (M ⊓ compGen P D M A)
    le_rfl hh rfl (compOf_card h.toHyp41 hA2) connD_compOf
  have hinE : ∀ B ∈ dInter D (compGen P D M A), B ∈ compOf P D M A := by
    intro B hB
    by_contra hBc
    have hcom := compOf_comm_of_not_mem h.toHyp41 hA hB.1 hBc
    apply h.ne_bot B hB.1
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    exact d.toSymCore.eq_one_of_central (hB.2 hb) fun y hy => (hcom b hb y hy).symm
  refine ⟨m, d.θ, d.β, d.odd, d.three_le, d.inv, d.surj, d.ker, d.equiv, d.top, ?_, ?_⟩
  · intro B hB
    exact d.trans B ⟨hinE B hB, hB.2⟩
  · obtain ⟨i₀, hi₀⟩ := d.pt
    refine ⟨i₀, fun x => ?_⟩
    rw [← hi₀ x]
    exact ⟨fun hM => ⟨hM, x.2⟩, fun hME => hME.1⟩

theorem bhsSymCase : BHSSymCase := by
  intro V _ _ P D T M h hV hP A hA hA2
  exact Or.inr (bhsSymType V P D T M h hV hP A hA hA2)

theorem four_eighteen_all {P : Subgroup (MulAut V)}
    {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)} (h : Hyp43 P D T M)
    (hV : ∀ v : V, v ^ 2 = 1) (hP : P = ⨆ A ∈ D, A) :
    (∀ A ∈ dOut P D M, SLType D (compGen P D M A) ∨ SymType M D (compGen P D M A)) ∧
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
    (∀ A ∈ dOut P D M, ∀ C ∈ dCore P D M, commV (compGen P D M A) ≤ fixV C) :=
  four_eighteen bhsSymCase h hV hP

end Final

end CFSG.CGT.PushingUpLit.BHS

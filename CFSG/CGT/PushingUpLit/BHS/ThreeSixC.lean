module

public import CFSG.CGT.PushingUpLit.BHS.ThreeSixB
public import CFSG.CGT.PushingUpLit.BHS.LLemma
public import CFSG.CGT.PushingUpLit.BHS.ThreeFive
public import CFSG.CGT.PushingUpLit.BHS.ThreeSixA

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

section Main

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem isPGroup_of_isElemAbelian2 {A : Subgroup (MulAut V)} (h : IsElemAbelian2 A) :
    IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using h.2 (x : MulAut V) x.2)⟩

omit [Finite V] in
theorem isElemAbelian2_sup {A B : Subgroup (MulAut V)} (hA : IsElemAbelian2 A)
    (hB : IsElemAbelian2 B) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian2 (A ⊔ B) := by
  have hc : ∀ X ∈ ({A, B} : Set (Subgroup (MulAut V))), ∀ Y ∈ ({A, B} : Set (Subgroup (MulAut V))),
      ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
    intro X hX Y hY x hx y hy
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact hA.1 x hx y hy
    · exact hcomm x hx y hy
    · exact (hcomm y hy x hx).symm
    · exact hB.1 x hx y hy
  have h1 := FourOneTools.comm_of_mem_sSup hc
  have h2 := FourOneTools.sq_eq_one_of_mem_sSup h1 (by
    rintro X (rfl | rfl) x hx
    · exact hA.2 x hx
    · exact hB.2 x hx)
  rw [sSup_pair] at h1 h2
  exact ⟨h1, h2⟩

theorem three_six_of_le {P T M A : Subgroup (MulAut V)}
    (hV : ∀ v : V, v ^ 2 = 1) (hmin : MinPar P T M) (hO2 : pCoreOf 2 P = ⊥)
    (hcen : cenIn P (fixV T) ≤ M) (hA : IsAOff P A) (hAT : A ≤ T) :
    ∃ L₀ : Subgroup (MulAut V), A ≤ L₀ ∧ L₀ ≤ P ∧ ∃ n : ℕ, 1 ≤ n ∧ Nat.card A = 2 ^ n ∧
      IsQuadratic A ∧ Nat.card V = wt A ∧ fixV A = commV A ⊔ fixV L₀ ∧
      (∀ a ∈ A, a ≠ 1 → fixV (Subgroup.zpowers a) = fixV A) ∧
      IsSLNatSection L₀ ⊤ (fixV L₀) n := by
  classical
  have hA2 : IsPGroup 2 A := hmin.syl.2.1.to_le hAT
  have hAne : A ≠ ⊥ := hA.2.1.2.1
  have hel : IsElemAbelian2 A := hA.2.1.2.2.1
  have hcard : Nat.card V ≤ wt A := hA.2.1.card_le_wt
  have hlt : ∀ B : Subgroup (MulAut V), B ≤ A → B ≠ ⊥ → B ≠ A → wt B < wt A :=
    fun B hBA hB0 hBne => hA.wt_lt_of_lt hBA hB0 hBne
  have hAX : ¬ A ≤ pCoreOf 2 P := by
    rw [hO2]
    exact fun h => hAne (le_bot_iff.1 h)
  obtain ⟨L, -, hLP, hAL, ⟨M₀, hM₀L, hAM₀, hM₀max, -, hgen⟩, hLM⟩ :=
    l_lemma ⟨hmin.syl, hmin.not_normal, M, hmin.le_M, hmin.lt_P, hmin.max⟩
      ⟨hmin.le_M, hmin.lt_P, hmin.max⟩ hA2 hAT hAX
  obtain ⟨x₀, ⟨hx₀L, hx₀M⟩, hx₀min⟩ :
      ∃ x₀ ∈ {x : MulAut V | x ∈ L ∧ x ∉ M₀}, ∀ x ∈ {x : MulAut V | x ∈ L ∧ x ∉ M₀},
        Nat.card ↥(A ⊔ conjSub x₀ A) ≤ Nat.card ↥(A ⊔ conjSub x A) := by
    refine Set.exists_min_image _ (fun x => Nat.card ↥(A ⊔ conjSub x A)) (Set.toFinite _) ?_
    obtain ⟨x, hxL, hxM⟩ := IsConcreteLE.exists_of_lt hM₀L
    exact ⟨x, hxL, hxM⟩
  set L₀ : Subgroup (MulAut V) := A ⊔ conjSub x₀ A with hL₀
  have hAL₀ : A ≤ L₀ := le_sup_left
  have hL₀L : L₀ ≤ L := by
    refine sup_le hAL ?_
    have := conjSub_mono x₀ hAL
    rwa [conjSub_self_of_mem hx₀L] at this
  have hLeq : L = L₀ ⊔ pCoreOf 2 L := hgen x₀ hx₀L hx₀M
  have hy : ∃ y ∈ L₀, y ∉ M₀ := by
    by_contra hno
    push Not at hno
    refine hM₀L.not_ge ?_
    rw [hLeq]
    exact sup_le hno (le_sup_right.trans hAM₀)
  have hgenx : ∀ x ∈ L₀, x ∉ M₀ → A ⊔ conjSub x A = L₀ := by
    intro x hxL₀ hxM
    refine Subgroup.eq_of_le_of_card_ge (sup_le hAL₀ ?_) ?_
    · exact (conjSub_mono x hAL₀).trans (conjSub_self_of_mem hxL₀).le
    · exact hx₀min x ⟨hL₀L hxL₀, hxM⟩
  obtain ⟨T₀, hT₀, hAT₀⟩ := Glauberman.exists_isSylowOf_ge hA2 hAL₀
  have hminL₀ : MinPar L₀ T₀ (L₀ ⊓ M₀) :=
    minPar_of_lemma hM₀L hAM₀ hM₀max hL₀L hLeq hT₀ hAT₀ hy hgenx
  have hnt : ∃ g ∈ L₀, ∃ z ∈ fixV T₀, g z ≠ z :=
    exists_not_centralizes hmin.syl hcen hLP hLeq hL₀L hT₀ hLM
  obtain ⟨n, hn1, hAn, hVc, hfix, hzp, hSL⟩ := three_five hV hminL₀ hAT₀ hel hcard hlt hnt
    (fun x hx hxM => hgenx x hx fun h => hxM ⟨hx, h⟩)
  exact ⟨L₀, hAL₀, hL₀L.trans hLP, n, hn1, hAn, isQuadratic_of_weights hV hel hAne hcard hlt,
    hVc, hfix, hzp, hSL⟩

end Main

section Numeric

variable {V : Type} [CommGroup V] [Finite V]

structure OffNumeric (A : Subgroup (MulAut V)) : Prop where
  quad : IsQuadratic A
  card : Nat.card V = wt A
  fixV_eq : ∀ a ∈ A, a ≠ 1 → fixV (Subgroup.zpowers a) = fixV A

omit [Finite V] in
theorem OffNumeric.conj {A : Subgroup (MulAut V)} (h : OffNumeric A) (g : MulAut V) :
    OffNumeric (conjSub g A) where
  quad := isQuadratic_map_conj h.quad g
  card := by rw [wt_conjSub]; exact h.card
  fixV_eq := by
    rintro _ ⟨a, ha, rfl⟩ ha1
    have ha1' : a ≠ 1 := fun h' => ha1 (by simp [h'])
    show fixV (Subgroup.zpowers ((MulAut.conj g).toMonoidHom a)) = fixV (conjSub g A)
    rw [← MonoidHom.map_zpowers, Glauberman.fixV_map_conj, h.fixV_eq a ha ha1', conjSub,
      Glauberman.fixV_map_conj]

theorem OffNumeric.of_le {P T M A : Subgroup (MulAut V)}
    (hV : ∀ v : V, v ^ 2 = 1) (hmin : MinPar P T M) (hO2 : pCoreOf 2 P = ⊥)
    (hcen : cenIn P (fixV T) ≤ M) (hA : IsAOff P A) (hAT : A ≤ T) : OffNumeric A := by
  obtain ⟨L₀, -, -, n, -, -, hq, hc, -, hz, -⟩ := three_six_of_le hV hmin hO2 hcen hA hAT
  exact ⟨hq, hc, hz⟩

theorem three_six_numeric {P T M A : Subgroup (MulAut V)}
    (hV : ∀ v : V, v ^ 2 = 1) (hmin : MinPar P T M) (hO2 : pCoreOf 2 P = ⊥)
    (hcen : cenIn P (fixV T) ≤ M) (hA : IsAOff P A) : OffNumeric A := by
  obtain ⟨k, hkP, hk⟩ := Glauberman.exists_conj_le_of_isSylowOf hmin.syl
    (isPGroup_of_isElemAbelian2 hA.2.1.2.2.1) hA.1
  have hA' : IsAOff P (conjSub k A) := hA.conj hkP
  have h1 : OffNumeric (conjSub k A) := OffNumeric.of_le hV hmin hO2 hcen hA' hk
  have h2 := h1.conj k⁻¹
  rwa [FourTwoTools.conjSub_inv_conjSub] at h2

omit [Finite V] in
theorem card_le_index_mul_index_mul_card (U W : Subgroup V) :
    Nat.card V ≤ U.index * W.index * Nat.card ↥(U ⊓ W) := by
  have h1 := Subgroup.card_mul_index (U ⊓ W)
  have h2 : (U ⊓ W).index ≤ U.index * W.index := Subgroup.index_inf_le
  calc Nat.card V = Nat.card ↥(U ⊓ W) * (U ⊓ W).index := h1.symm
    _ ≤ Nat.card ↥(U ⊓ W) * (U.index * W.index) := Nat.mul_le_mul_left _ h2
    _ = U.index * W.index * Nat.card ↥(U ⊓ W) := by ring

theorem index_fixV_eq {A : Subgroup (MulAut V)} (h : Nat.card V = wt A) :
    (fixV A).index = Nat.card A := by
  have h1 := Subgroup.card_mul_index (fixV A)
  have hpos : 0 < Nat.card (fixV A) := Nat.card_pos
  unfold wt at h
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h1, h]
  ring

theorem three_six_commuting {P T M A B : Subgroup (MulAut V)}
    (hV : ∀ v : V, v ^ 2 = 1) (hmin : MinPar P T M) (hO2 : pCoreOf 2 P = ⊥)
    (hcen : cenIn P (fixV T) ≤ M) (hA : IsAOff P A) (hB : IsAOff P B) (hAB : B ≠ A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card V = Nat.card A * Nat.card B * Nat.card (fixV (A ⊔ B)) := by
  have nA := three_six_numeric hV hmin hO2 hcen hA
  have nB := three_six_numeric hV hmin hO2 hcen hB
  have hS : IsElemAbelian2 (A ⊔ B) :=
    isElemAbelian2_sup hA.2.1.2.2.1 hB.2.1.2.2.1 hcomm
  have hSP : A ⊔ B ≤ P := sup_le hA.1 hB.1
  have hwtA : wt (A ⊔ B) ≤ wt A := hA.wt_le hSP hS
  have hwtB : wt (A ⊔ B) ≤ wt B := hB.wt_le hSP hS
  have hfix : fixV (A ⊔ B) = fixV A ⊓ fixV B := fixV_sup A B
  by_cases hinf : ∃ x ∈ A ⊓ B, x ≠ 1
  · exfalso
    obtain ⟨x, hx, hx1⟩ := hinf
    have hAB' : fixV A = fixV B := by
      rw [← nA.fixV_eq x hx.1 hx1, nB.fixV_eq x hx.2 hx1]
    have hfixS : fixV (A ⊔ B) = fixV A := by rw [hfix, ← hAB', inf_idem]
    have hle : Nat.card ↥(A ⊔ B) ≤ Nat.card A := by
      have : Nat.card ↥(A ⊔ B) * Nat.card (fixV A) ≤ Nat.card A * Nat.card (fixV A) := by
        have := hwtA
        unfold wt at this
        rwa [hfixS] at this
      exact Nat.le_of_mul_le_mul_right this Nat.card_pos
    have hBA : A ⊔ B = A := (Subgroup.eq_of_le_of_card_ge le_sup_left hle).symm
    have hle' : Nat.card ↥(A ⊔ B) ≤ Nat.card B := by
      have : Nat.card ↥(A ⊔ B) * Nat.card (fixV B) ≤ Nat.card B * Nat.card (fixV B) := by
        have := hwtB
        unfold wt at this
        rwa [hfixS, hAB'] at this
      exact Nat.le_of_mul_le_mul_right this Nat.card_pos
    have hAB2 : A ⊔ B = B := (Subgroup.eq_of_le_of_card_ge le_sup_right hle').symm
    exact hAB (hAB2.symm.trans hBA)
  · push Not at hinf
    have hbot : A ⊓ B = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact (Subgroup.mem_bot).2 (hinf x hx)
    have hcardS : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
      have := card_sup_mul_card_inf' (X := A) (Y := B) hcomm
      rwa [hbot, Subgroup.card_bot, mul_one] at this
    apply le_antisymm
    · have h1 := card_le_index_mul_index_mul_card (fixV A) (fixV B)
      rw [index_fixV_eq nA.card, index_fixV_eq nB.card, ← hfix] at h1
      calc Nat.card V ≤ Nat.card A * Nat.card B * Nat.card ↥(fixV (A ⊔ B)) := h1
        _ = _ := rfl
    · have := hwtA
      unfold wt at this
      rw [hcardS] at this
      rw [nA.card]
      unfold wt
      exact this

end Numeric

end CFSG.CGT.PushingUpLit.BHS

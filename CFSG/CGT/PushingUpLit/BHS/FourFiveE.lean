module

public import CFSG.CGT.PushingUpLit.BHS.FourFiveD

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

variable {V : Type} [CommGroup V] [Finite V]

theorem Hyp41.eq_of_le {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))} (h : Hyp41 P D)
    {X A : Subgroup (MulAut V)} (hX : X ∈ D) (hA : A ∈ D) (hXA : X ≤ A) : X = A := by
  rcases h.eq_or_inf_eq_bot hX hA with h1 | h1
  · exact h1
  · rw [inf_eq_left.2 hXA] at h1
    exact absurd h1 (h.ne_bot X hX)

omit [Finite V] in
theorem mSet_conjSub_self {P M A : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ P) :
    mSet P (conjSub g M) A = mSet P M A := by
  ext Y
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hle⟩
    exact ⟨⟨p * g, P.mul_mem hp hg, (conjSub_mul p g M).symm⟩, hle⟩
  · rintro ⟨⟨q, hq, rfl⟩, hle⟩
    refine ⟨⟨q * g⁻¹, P.mul_mem hq (P.inv_mem hg), ?_⟩, hle⟩
    rw [conjSub_mul, FourTwoTools.conjSub_inv_conjSub]

omit [Finite V] in
theorem lamSet_conjSub_self {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}
    {M : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ P) :
    lamSet P D (conjSub g M) = lamSet P D M := by
  ext L
  unfold lamSet
  simp only [Set.mem_ofPred_eq, mSet_conjSub_self hg]

theorem four_sixteen {P : Subgroup (MulAut V)}
    {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)} (h : Hyp43 P D T M)
    (hV : ∀ v : V, v ^ 2 = 1) {A B : Subgroup (MulAut V)} (hA : A ∈ D) (hB : B ∈ D)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAc : A ∉ dCore P D M) :
    ∀ X ∈ D, X ≤ A ⊔ B → X = A ∨ X = B := by
  intro X hX hXAB
  by_cases hBA : B = A
  · subst hBA
    left
    rw [sup_idem] at hXAB
    exact h.toHyp41.eq_of_le hX hB hXAB
  obtain ⟨g, hg, L, hL, hAL, hAg, hLg⟩ := four_twelve h.toHyp42 hV hA hAc
  have hL' := hL
  obtain ⟨-, ⟨n, hn1, hSL⟩, -, -⟩ := hL'
  have hA2 : IsPGroup 2 A := isPGroup_of_isElemAbelian2 (h.elemAb A hA)
  obtain ⟨T', hAT', hT'⟩ := h.toHyp42.exists_conj hg hA2 hAg
  have h' : Hyp43 P D T' (conjSub g M) := { toHyp42 := hT', max := h.max }
  set N : Subgroup (MulAut V) := Subgroup.centralizer (A : Set (MulAut V)) ⊓ P with hN
  have hNP : N ≤ P := inf_le_right
  have hAB : IsElemAbelian2 (A ⊔ B) :=
    isElemAbelian2_sup (h.elemAb A hA) (h.elemAb B hB) hcomm
  have hABP : A ⊔ B ≤ P := sup_le (h.le A hA) (h.le B hB)
  have hABN : A ⊔ B ≤ N := fun x hx =>
    ⟨Subgroup.mem_centralizer_iff.2 fun a ha => hAB.1 a (Subgroup.mem_sup_left ha) x hx, hABP hx⟩
  set E₂ : Subgroup (MulAut V) := ⨆ Y ∈ dInter D T', Y with hE₂
  have hE₂2 := four_seven h'.toHyp41 h'.syl
  have hE₂T : ∀ Y ∈ dInter D T', Y ≤ E₂ := fun Y hY =>
    le_iSup₂_of_le (f := fun (Z : Subgroup (MulAut V)) (_ : Z ∈ dInter D T') => Z) Y hY le_rfl
  have hAE₂ : A ≤ E₂ := hE₂T A ⟨hA, hAT'⟩
  have hE₂N : E₂ ≤ N := fun x hx =>
    ⟨Subgroup.mem_centralizer_iff.2 fun a ha => hE₂2.1.1 a (hAE₂ ha) x hx,
      (iSup₂_le fun Y hY => h.le Y hY.1 : E₂ ≤ P) hx⟩
  obtain ⟨S₁, hS₁, hE₂S₁⟩ :=
    Glauberman.exists_isSylowOf_ge (isPGroup_of_isElemAbelian2 hE₂2.1) hE₂N
  obtain ⟨k, hkN, hk⟩ := Glauberman.exists_conj_le_of_isSylowOf hS₁
    (isPGroup_of_isElemAbelian2 hAB) hABN
  have hkP : k ∈ P := hkN.2
  have hkc : k ∈ Subgroup.centralizer (A : Set (MulAut V)) := hkN.1
  have hkc' : k⁻¹ ∈ Subgroup.centralizer (A : Set (MulAut V)) :=
    (Subgroup.centralizer (A : Set (MulAut V))).inv_mem hkc
  have hkA : conjSub k A = A :=
    conjSub_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer (A : Set (MulAut V)) hkc)
  have hkA' : conjSub k⁻¹ A = A :=
    conjSub_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer (A : Set (MulAut V)) hkc')
  have hsupk : conjSub k (A ⊔ B) = A ⊔ conjSub k B := by
    rw [conjSub_sup, hkA]
  have hd : dInter D S₁ = dInter D T' :=
    h'.toHyp42.dInter_eq_of_le (hS₁.1.trans hNP) hS₁.2.1 fun Y hY => (hE₂T Y hY).trans hE₂S₁
  have hk' : conjSub k (A ⊔ B) ≤ S₁ := hk
  have hB'T : conjSub k B ∈ dInter D T' := by
    have : conjSub k B ∈ dInter D S₁ :=
      ⟨h.conj_mem B hB k hkP, (conjSub_mono k le_sup_right).trans hk'⟩
    rwa [hd] at this
  have hX'T : conjSub k X ∈ dInter D T' := by
    have : conjSub k X ∈ dInter D S₁ :=
      ⟨h.conj_mem X hX k hkP, (conjSub_mono k hXAB).trans hk'⟩
    rwa [hd] at this
  by_cases hXA : conjSub k X = A
  · left
    rw [← FourTwoTools.conjSub_inv_conjSub k X, hXA, hkA']
  · right
    have hBA' : conjSub k B ≠ A := fun e => hBA (by
      rw [← FourTwoTools.conjSub_inv_conjSub k B, e, hkA'])
    have hL'' : L ∈ lamSet P D (conjSub g M) := by
      rw [lamSet_conjSub_self hg]
      exact hL
    have hc1 := four_fifteen h' hV ⟨hA, hAT'⟩ hB'T (Ne.symm hBA') hL'' hAL hLg
    have hc2 := four_fifteen h' hV ⟨hA, hAT'⟩ hX'T (Ne.symm hXA) hL'' hAL hLg
    have hcommA : ∀ a ∈ A, ∀ b' ∈ conjSub k B, a * b' = b' * a := by
      rintro a ha _ ⟨b, hb, rfl⟩
      have h1 : k⁻¹ * a * k ∈ A := by
        have : conjSub k⁻¹ A = A := hkA'
        rw [← this]
        exact ⟨a, ha, rfl⟩
      have h2 := hcomm _ h1 b hb
      show a * (k * b * k⁻¹) = k * b * k⁻¹ * a
      calc a * (k * b * k⁻¹) = k * ((k⁻¹ * a * k) * b) * k⁻¹ := by group
        _ = k * (b * (k⁻¹ * a * k)) * k⁻¹ := by rw [h2]
        _ = k * b * k⁻¹ * a := by group
    have hXle : conjSub k X ≤ conjSub k B := by
      intro x hx
      have hx' : x ∈ A ⊔ conjSub k B := hsupk ▸ conjSub_mono k hXAB hx
      obtain ⟨a, ha, b', hb', rfl⟩ := exists_mul_of_mem_sup' hcommA hx'
      have hac : ∀ l ∈ L, l * a = a * l := by
        intro l hl
        have e1 := hc2 l hl (a * b') hx
        have e2 := hc1 l hl b' hb'
        calc l * a = l * (a * b') * b'⁻¹ := by group
          _ = (a * b') * l * b'⁻¹ := by rw [e1]
          _ = a * (b' * l) * b'⁻¹ := by group
          _ = a * (l * b') * b'⁻¹ := by rw [e2]
          _ = a * l := by group
      have ha1 : a = 1 := hSL.center_eq_bot hn1 (hAL ha) hac
      rw [ha1, one_mul]
      exact hb'
    have hXB : conjSub k X = conjSub k B :=
      h.toHyp41.eq_of_le (h.conj_mem X hX k hkP) (h.conj_mem B hB k hkP) hXle
    exact FourTwoTools.conjSub_injective k hXB

end CFSG.CGT.PushingUpLit.BHS

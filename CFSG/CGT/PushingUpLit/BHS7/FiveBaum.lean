module

public import CFSG.CGT.PushingUpLit.BHS7.FiveGeneric
public import CFSG.CGT.PushingUpLit.BHS7.FiveFamily

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS5

variable {V : Type} [CommGroup V] [Finite V] {P T M : Subgroup (MulAut V)}
  {ℰ : Set (Subgroup (MulAut V))}

omit [Finite V] in
theorem exists_not_le_centSub {𝒜 : Set (Subgroup (MulAut V))} {X : Subgroup (MulAut V)}
    (hXdef : X = ⨆ A ∈ 𝒜, A) {W : Subgroup V} (h : ¬ W ≤ fixV X) :
    ∃ A ∈ 𝒜, ¬ A ≤ centSub W := by
  by_contra hcon
  push Not at hcon
  apply h
  intro w hw
  rw [mem_fixV]
  intro x hx
  refine fix_of_le_iSup (S := 𝒜) (fun A hA => ?_) (hXdef ▸ hx)
  rw [mem_fixV]
  intro a ha
  exact hcon A hA ha w hw

theorem comp_fix_baum (hV : ∀ v : V, v ^ 2 = 1) (hF : FiveFive P T M ℰ)
    {𝒜 : Set (Subgroup (MulAut V))} {X : Subgroup (MulAut V)} (hXdef : X = ⨆ A ∈ 𝒜, A)
    (hoff : ∀ A ∈ 𝒜, IsOff A) (hX2 : IsPGroup 2 ↥X) (hXle : X ≤ genD P) (hXne : X ≠ ⊥)
    (hXT : ∀ t ∈ T, conjSub t X = X) {E : Subgroup (MulAut V)} (hE : E ∈ ℰ) :
    (∃ w ∈ commV E, w ∉ fixV E ∧ w ∈ fixV X) ∧
    ∀ Q : Subgroup (MulAut V), IsPGroup 2 ↥Q → Q ≤ P → X ≤ Q → fixV X ≤ fixV Q →
      Q ≤ Subgroup.normalizer (E : Set (MulAut V)) ∧
        autSub Q (commV E) ≤ autSub X (commV E) := by
  have hXN : X ≤ Subgroup.normalizer (E : Set (MulAut V)) := fun x hx =>
    mem_normalizer_of_le_iSup hF hE (by rw [hF.iSup_eq]; exact hXle hx)
  have hne : ∃ A ∈ 𝒜, ¬ A ≤ centSub (commV E) :=
    exists_not_le_centSub hXdef (not_commV_le_fixV hF hXle hXne hXT hE)
  have hXst : X ≤ stabSub (commV E) := hXN.trans (normalizer_commV_le_stabSub E)
  have hXA : ∀ A ∈ 𝒜, A ≤ X := fun A hA => hXdef ▸ le_iSup₂ (f := fun A (_ : A ∈ 𝒜) => A) A hA
  have key : (∃ w ∈ commV E, w ∉ fixV E ∧ w ∈ fixV X) ∧
      ∀ Q : Subgroup (MulAut V), IsPGroup 2 ↥Q →
        Q ≤ Subgroup.normalizer (E : Set (MulAut V)) → X ≤ Q → fixV X ≤ fixV Q →
          autSub Q (commV E) ≤ autSub X (commV E) := by
    rcases hF.type E hE with hSL | hSym
    · obtain ⟨k, hk, hnat, -, -⟩ := hSL
      obtain ⟨hfixE, hbaum, -⟩ := sl_fix_baum hk hnat hXdef hoff hX2 hXN hne
      exact ⟨hfixE, fun Q hQ2 hQN hXQ hfix => hbaum Q hQ2 hQN hXQ hfix⟩
    · obtain ⟨m, θ, β, hm, h3, hinv, hsurj, hker, hequiv, htop, -, -⟩ := hSym
      let D : SymDat E m := ⟨θ, β, hm, h3, hinv, hsurj, hker, hequiv, htop⟩
      refine ⟨sym_fix hV D hX2 hXN, fun Q hQ2 hQN hXQ hfix => ?_⟩
      by_cases h5 : 5 ≤ m
      · exact alt_baum hV h5 D hXdef hoff hX2 hXN hne Q hQ2 hQN hfix
      · have hm3 : m = 3 := by
          obtain ⟨c, hc⟩ := hm
          omega
        subst hm3
        refine three_baum hV D hX2 hQ2 hXQ hXst ?_
        obtain ⟨A, hA, hAc⟩ := hne
        exact fun h => hAc ((hXA A hA).trans h)
  refine ⟨key.1, fun Q hQ2 hQP hXQ hfix => ?_⟩
  obtain ⟨w, hwW, hwE, hwX⟩ := key.1
  have hQN : Q ≤ Subgroup.normalizer (E : Set (MulAut V)) := fun t ht =>
    mem_normalizer_of_fix hF hE (hQP ht) hwW hwE ((mem_fixV.mp (hfix hwX)) t ht)
  exact ⟨hQN, key.2 Q hQ2 hQN hXQ hfix⟩

theorem baum_le_genD (hV : ∀ v : V, v ^ 2 = 1) (hF : FiveFive P T M ℰ)
    {𝒜 : Set (Subgroup (MulAut V))} {X : Subgroup (MulAut V)} (hXdef : X = ⨆ A ∈ 𝒜, A)
    (hoff : ∀ A ∈ 𝒜, IsOff A) (hX2 : IsPGroup 2 ↥X) (hXle : X ≤ genD P) (hXne : X ≠ ⊥)
    (hXT : ∀ t ∈ T, conjSub t X = X) {Q : Subgroup (MulAut V)} (hQ2 : IsPGroup 2 ↥Q)
    (hQP : Q ≤ P) (hXQ : X ≤ Q) (hfix : fixV X ≤ fixV Q) : Q ≤ genD P := by
  intro t ht
  refine mem_genD_of_restr hF (fun v hv => ?_) fun E hE => ?_
  · exact (mem_fixV.mp (hfix (CFSG.Quasithin.fixV_anti hXle hv))) t ht
  · obtain ⟨-, hQ⟩ := comp_fix_baum hV hF hXdef hoff hX2 hXle hXne hXT hE
    obtain ⟨hQN, hres⟩ := hQ Q hQ2 hQP hXQ hfix
    have htst : t ∈ stabSub (commV E) := (normalizer_commV_le_stabSub E) (hQN ht)
    have hmem : resHom (commV E) ⟨t, htst⟩ ∈ autSub Q (commV E) :=
      mem_autSub.mpr ⟨⟨t, htst⟩, ht, rfl⟩
    obtain ⟨x, hxX, hx⟩ := mem_autSub.mp (hres hmem)
    have hxg : (x : MulAut V) ∈ ⨆ E' ∈ ℰ, E' := by
      rw [hF.iSup_eq]
      exact hXle hxX
    obtain ⟨e, he, hxe⟩ := exists_comp_restr hF hE hxg
    refine ⟨e, he, fun w hw => ?_⟩
    have h1 := congrArg (fun φ : MulAut ↥(commV E) => ((φ ⟨w, hw⟩ : ↥(commV E)) : V)) hx
    simp only [resHom_apply] at h1
    rw [← h1]
    exact hxe w hw

end CFSG.CGT.PushingUpLit.BHS7

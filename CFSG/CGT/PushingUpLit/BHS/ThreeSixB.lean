module

public import CFSG.CGT.PushingUpLit.BHS.FourTwoA
public import CFSG.CGT.PushingUpLit.BHS.HomTransfer
public import CFSG.CGT.PushingUpLit.BHS.LLemmaBasic

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

section LZero

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem minPar_of_lemma {L M₀ A L₀ T₀ : Subgroup Γ} (hM₀L : M₀ < L)
    (hAM₀ : A ⊔ pCoreOf 2 L ≤ M₀)
    (hmax : ∀ Z : Subgroup Γ, Z < L → A ⊔ pCoreOf 2 L ≤ Z → Z ≤ M₀) (hL₀L : L₀ ≤ L)
    (hL : L = L₀ ⊔ pCoreOf 2 L) (hT₀ : IsSylowOf 2 T₀ L₀) (hAT₀ : A ≤ T₀)
    (hy : ∃ y ∈ L₀, y ∉ M₀) (hgen : ∀ x ∈ L₀, x ∉ M₀ → A ⊔ conjSub x A = L₀) :
    MinPar L₀ T₀ (L₀ ⊓ M₀) := by
  set R := pCoreOf 2 L with hR
  have hRL : R ≤ L := pCoreOf_le 2 L
  have hRn : L ≤ Subgroup.normalizer (R : Set Γ) := le_normalizer_pCoreOf 2 L
  have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 L
  have hRM₀ : R ≤ M₀ := le_sup_right.trans hAM₀
  have hL₀n : L₀ ≤ Subgroup.normalizer (R : Set Γ) := hL₀L.trans hRn
  have hL2 : ¬ IsPGroup 2 L := fun h2 => by
    have : L ≤ R := le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer h2
    exact hM₀L.not_ge (this.trans hRM₀)
  have hsyl : ∀ S : Subgroup Γ, IsSylowOf 2 S L → A ⊔ R ≤ S → S ≤ M₀ := by
    intro S hS hAR
    refine hmax S (lt_of_le_of_ne hS.1 fun e => hL2 ?_) hAR
    rw [← e]
    exact hS.2.1
  have hT₀M₀ : T₀ ≤ M₀ := by
    have hU : IsPGroup 2 (T₀ ⊔ R : Subgroup Γ) :=
      IsPGroup.to_sup_of_normal_right' hT₀.2.1 hR2 (hT₀.1.trans hL₀n)
    obtain ⟨S, hS, hUS⟩ := Glauberman.exists_isSylowOf_ge hU (sup_le (hT₀.1.trans hL₀L) hRL)
    exact (le_sup_left.trans hUS).trans (hsyl S hS (sup_le_sup_right hAT₀ R |>.trans hUS))
  have hRT₀ : R ⊓ L₀ ≤ T₀ := by
    refine Nine.le_of_isSylowOf_of_normal hT₀ (hR2.to_le inf_le_left) inf_le_right ?_
    intro x hx
    apply mem_normalizer_of_conjSub_eq
    rw [conjSub_inf, conjSub_eq_of_mem_normalizer (hL₀n hx), conjSub_self_of_mem hx]
  have hDed : ∀ X : Subgroup Γ, T₀ ≤ X → X ≤ L₀ → X ⊔ R = L → X = L₀ := by
    intro X hTX hXL hXR
    refine le_antisymm hXL fun y hy' => ?_
    have hyL : y ∈ X ⊔ R := hXR ▸ hL₀L hy'
    obtain ⟨x, hx, r, hr, rfl⟩ := (mem_sup_iff_of_le_normalizer (hXL.trans hL₀n)).1 hyL
    have hrL₀ : r ∈ L₀ := by
      have := L₀.mul_mem (L₀.inv_mem (hXL hx)) hy'
      simpa using this
    exact X.mul_mem hx (hTX (hRT₀ ⟨hr, hrL₀⟩))
  obtain ⟨y, hyL₀, hyM₀⟩ := hy
  refine
  { syl := hT₀
    not_normal := ?_
    le_M := le_inf hT₀.1 hT₀M₀
    lt_P := lt_of_le_of_ne inf_le_left fun e => hyM₀ (by
      have : y ∈ L₀ ⊓ M₀ := by rw [e]; exact hyL₀
      exact this.2)
    max := ?_ }
  · intro hn
    have h1 : conjSub y T₀ = T₀ := conjSub_eq_of_mem_normalizer (hn hyL₀)
    have h2 : L₀ ≤ T₀ := by
      rw [← hgen y hyL₀ hyM₀]
      refine sup_le hAT₀ ?_
      have := conjSub_mono y hAT₀
      rwa [h1] at this
    have hL₀2 : IsPGroup 2 L₀ := hT₀.2.1.to_le h2
    apply hL2
    rw [hL]
    exact IsPGroup.to_sup_of_normal_right' hL₀2 hR2 hL₀n
  · intro X hTX hXL
    have hXL' : X ≤ L₀ := hXL.le
    have hlt : X ⊔ R < L := by
      refine lt_of_le_of_ne (sup_le (hXL'.trans hL₀L) hRL) fun e => hXL.ne ?_
      exact hDed X hTX hXL' e
    have h1 := hmax _ hlt (sup_le_sup_right (hAT₀.trans hTX) R)
    exact le_inf hXL' (le_sup_left.trans h1)

end LZero

section Nontriv

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_not_centralizes {P T M L L₀ T₀ : Subgroup (MulAut V)} (hT : IsSylowOf 2 T P)
    (hcen : cenIn P (fixV T) ≤ M) (hLP : L ≤ P) (hL : L = L₀ ⊔ pCoreOf 2 L) (hL₀L : L₀ ≤ L)
    (hT₀ : IsSylowOf 2 T₀ L₀) (hLM : ∀ g ∈ P, ¬ L ≤ conjSub g M) :
    ∃ g ∈ L₀, ∃ z ∈ fixV T₀, g z ≠ z := by
  by_contra hno
  push Not at hno
  have hRn : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set (MulAut V)) := le_normalizer_pCoreOf 2 L
  have hR2 : IsPGroup 2 (pCoreOf 2 L) := pCoreOf_isPGroup 2 L
  have hU : IsPGroup 2 (T₀ ⊔ pCoreOf 2 L : Subgroup (MulAut V)) :=
    IsPGroup.to_sup_of_normal_right' hT₀.2.1 hR2 (hT₀.1.trans (hL₀L.trans hRn))
  obtain ⟨h, hhP, hUh⟩ := FourTwoTools.exists_conjSub_ge hT hU
    (sup_le (hT₀.1.trans (hL₀L.trans hLP)) ((pCoreOf_le 2 L).trans hLP))
  refine absurd ?_ (hLM h hhP)
  intro x hx
  have hx' := hx
  rw [hL] at hx'
  obtain ⟨k, hk, r, hr, rfl⟩ := (mem_sup_iff_of_le_normalizer (hL₀L.trans hRn)).1 hx'
  rw [mem_conjSub_iff]
  refine hcen ⟨?_, fun z hz => ?_⟩
  · exact P.mul_mem (P.mul_mem (P.inv_mem hhP) (hLP hx)) hhP
  · have hmem : h z ∈ fixV (conjSub h T) := by
      rw [conjSub, Glauberman.fixV_map_conj]
      exact ⟨z, hz, rfl⟩
    have h1 : h z ∈ fixV T₀ := fixV_anti (le_sup_left.trans hUh) hmem
    have h2 : h z ∈ fixV (pCoreOf 2 L) := fixV_anti (le_sup_right.trans hUh) hmem
    have h3 : r (h z) = h z := mem_fixV.1 h2 r hr
    have h4 : k (h z) = h z := hno k hk _ h1
    simp only [MulAut.mul_apply, h3, h4]
    exact h.symm_apply_apply z

end Nontriv

end CFSG.CGT.PushingUpLit.BHS

module

public import CFSG.LocalAnalysis.ABGTheoremB.V5Signalizer
public import CFSG.LocalAnalysis.ABGTheoremB.V5ZJ

public section

namespace CFSG.ABGTheoremB.V56

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

private def ConjNCW (σ : Setting G) (W A B : Subgroup G) : Prop :=
  ∃ c ∈ σ.C ⊓ Subgroup.normalizer (W : Set G), A.map (MulAut.conj c).toMonoidHom = B

omit [Finite G] in
private theorem ConjNCW.refl (σ : Setting G) (W A : Subgroup G) : ConjNCW σ W A A :=
  ⟨1, one_mem _, map_conj_one A⟩

omit [Finite G] in
private theorem ConjNCW.trans {σ : Setting G} {W A B E : Subgroup G} (h₁ : ConjNCW σ W A B)
    (h₂ : ConjNCW σ W B E) : ConjNCW σ W A E := by
  obtain ⟨c₁, hc₁, rfl⟩ := h₁
  obtain ⟨c₂, hc₂, rfl⟩ := h₂
  exact ⟨c₂ * c₁, mul_mem hc₂ hc₁, map_conj_mul A c₂ c₁⟩

section Intersection

variable {σ : Setting G} {J W P : Subgroup G}

theorem inf_sup_eq_pCoreIn (hσ : σ.IsValid) (hJ : σ.IsV21Layer J) (h45 : σ.LemmaV45 J)
    (hV31 : LemmaV31 σ J) (hV33 : LemmaV33 σ J) (hW : W ∈ σ.familyW J)
    (hP : IsSylowOf σ.p P σ.C) {U₁ U₂ : Subgroup G} (hU₁ : U₁ ∈ signalizersPerm ⊤ σ.D W σ.p)
    (hPU₁ : P ≤ U₁) (hPU₂ : P ≤ U₂) :
    U₁ ⊓ (U₂ ⊔ W) = pCoreIn σ.p ((U₁ ⊔ W) ⊓ (U₂ ⊔ W)) ⊔ P := by
  have hp := hσ.p_prime
  have hWp : ¬ σ.p ∣ Nat.card W := hV31.coprime W hW
  set Y₁ := U₁ ⊔ W
  set Y₂ := U₂ ⊔ W
  set Y := Y₁ ⊓ Y₂
  set A₁ := pCoreIn σ.p Y₁
  set B := pCoreIn σ.p Y
  have hU₁p : IsPGroup σ.p U₁ := hU₁.1.2.1
  have hPY₁ : P ≤ Y₁ := hPU₁.trans le_sup_left
  have hPY₂ : P ≤ Y₂ := hPU₂.trans le_sup_left
  have hPY : P ≤ Y := le_inf hPY₁ hPY₂
  have hWY₂ : W ≤ Y₂ := le_sup_right
  have hPA₁ : P ≤ Subgroup.normalizer (A₁ : Set G) := hPY₁.trans (le_normalizer_pCoreIn σ.p Y₁)
  have hPB : P ≤ Subgroup.normalizer (B : Set G) := hPY.trans (le_normalizer_pCoreIn σ.p Y)
  have hMp : IsPGroup σ.p (B ⊔ P : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_pCoreIn σ.p Y) hP.isPGroup hPB
  have hle : U₁ ⊓ Y₂ ≤ B ⊔ P := by
    have hU₁eq := lemmaV51 hσ hJ h45 hV31 hV33 hW hP hU₁ hPU₁
    intro x hx
    obtain ⟨hxU₁, hxY₂⟩ := Subgroup.mem_inf.mp hx
    have hx' : x ∈ ((A₁ ⊔ P : Subgroup G) : Set G) := by
      rw [← hU₁eq]
      exact hxU₁
    rw [Subgroup.coe_mul_of_right_le_normalizer_left A₁ P hPA₁] at hx'
    obtain ⟨a, ha, y, hy, rfl⟩ := hx'
    have haY₂ : a ∈ Y₂ := by
      have := Y₂.mul_mem hxY₂ (Y₂.inv_mem (hPY₂ hy))
      simpa using this
    have hA₁Y₂ : A₁ ⊓ Y₂ ≤ B := by
      refine le_pCoreIn (inf_le_inf_right Y₂ (pCoreIn_le σ.p Y₁)) ?_
        (isPGroup_pCoreIn σ.p Y₁).to_inf_left
      exact (le_inf (inf_le_left.trans (le_normalizer_pCoreIn σ.p Y₁))
        (inf_le_right.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    exact Subgroup.mul_mem_sup (hA₁Y₂ ⟨ha, haY₂⟩) hy
  have hU₁Y₂p : IsPGroup σ.p (U₁ ⊓ Y₂ : Subgroup G) := hU₁p.to_inf_left
  have hperm : ((U₁ ⊓ Y₂ : Subgroup G) : Set G) * W = W * ((U₁ ⊓ Y₂ : Subgroup G) : Set G) :=
    permutable_inf_of_le hWY₂ hU₁.2
  have hYle : Y ≤ (U₁ ⊓ Y₂) ⊔ W := by
    intro y hy
    have hy' : y ∈ ((U₁ : Set G) * W) ∩ Y₂ := by
      refine ⟨?_, hy.2⟩
      rw [← coe_sup_of_permutable hU₁.2]
      exact hy.1
    rw [mul_inter_of_le hWY₂] at hy'
    obtain ⟨a, ha, w, hw, rfl⟩ := hy'
    exact Subgroup.mul_mem_sup ha hw
  have hMY : B ⊔ P ≤ Y := sup_le (pCoreIn_le σ.p Y) hPY
  have hdvd : Nat.card (B ⊔ P : Subgroup G) ∣ Nat.card (U₁ ⊓ Y₂ : Subgroup G) :=
    card_dvd_of_le_sup_pPrime hp hU₁Y₂p hWp hperm hMp (hMY.trans hYle)
  exact Subgroup.eq_of_le_of_card_ge hle (Nat.le_of_dvd Nat.card_pos hdvd)

theorem inf_eq_pCoreIn (hσ : σ.IsValid) (hJ : σ.IsV21Layer J) (h45 : σ.LemmaV45 J)
    (hV31 : LemmaV31 σ J) (hV33 : LemmaV33 σ J) (hW : W ∈ σ.familyW J)
    (hP : IsSylowOf σ.p P σ.C) {U₁ U₂ : Subgroup G} (hU₁ : U₁ ∈ signalizersPerm ⊤ σ.D W σ.p)
    (hU₂ : U₂ ∈ signalizersPerm ⊤ σ.D W σ.p) (hPU₁ : P ≤ U₁) (hPU₂ : P ≤ U₂) :
    U₁ ⊓ U₂ = pCoreIn σ.p ((U₁ ⊔ W) ⊓ (U₂ ⊔ W)) ⊔ P := by
  have h₁ := inf_sup_eq_pCoreIn hσ hJ h45 hV31 hV33 hW hP hU₁ hPU₁ hPU₂
  have h₂ := inf_sup_eq_pCoreIn hσ hJ h45 hV31 hV33 hW hP hU₂ hPU₂ hPU₁
  rw [inf_comm (U₂ ⊔ W)] at h₂
  apply le_antisymm
  · rw [← h₁]
    exact inf_le_inf_left U₁ le_sup_left
  · refine le_inf ?_ ?_
    · rw [← h₁]
      exact inf_le_left
    · rw [← h₂]
      exact inf_le_left

theorem inf_mem_signalizersPerm (hσ : σ.IsValid) (hJ : σ.IsV21Layer J) (h45 : σ.LemmaV45 J)
    (hV31 : LemmaV31 σ J) (hV33 : LemmaV33 σ J) (hW : W ∈ σ.familyW J)
    (hP : IsSylowOf σ.p P σ.C) {U₁ U₂ : Subgroup G} (hU₁ : U₁ ∈ signalizersPerm ⊤ σ.D W σ.p)
    (hU₂ : U₂ ∈ signalizersPerm ⊤ σ.D W σ.p) (hPU₁ : P ≤ U₁) (hPU₂ : P ≤ U₂) :
    U₁ ⊓ U₂ ∈ signalizersPerm ⊤ σ.D W σ.p := by
  have hp := hσ.p_prime
  have hp2 := hσ.p_ne_two
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  have hUp : IsPGroup σ.p (U₁ ⊓ U₂ : Subgroup G) := hU₁.1.2.1.to_inf_left
  refine ⟨⟨le_top, hUp, ?_, inf_eq_bot_of_isPGroup_of_two hp hp2 hUp hD2⟩, ?_⟩
  · exact (le_inf hU₁.1.2.2.1 hU₂.1.2.2.1).trans Subgroup.inf_normalizer_le_normalizer_inf
  · rw [inf_eq_pCoreIn hσ hJ h45 hV31 hV33 hW hP hU₁ hU₂ hPU₁ hPU₂, sup_comm]
    set Y := (U₁ ⊔ W) ⊓ (U₂ ⊔ W)
    have hPY : P ≤ Y := le_inf (hPU₁.trans le_sup_left) (hPU₂.trans le_sup_left)
    have hWY : W ≤ Y := le_inf le_sup_right le_sup_right
    exact permutable_sup_of_le_normalizer (hPY.trans (le_normalizer_pCoreIn σ.p Y))
      (hWY.trans (le_normalizer_pCoreIn σ.p Y)) (hV33.permutable W hW P hP)

end Intersection

theorem propV52 {σ : Setting G} (hσ : σ.IsValid) {J : Subgroup G} (hJ : σ.IsV21Layer J)
    (h41 : σ.PropV41 J) (h45 : σ.LemmaV45 J) (hV31 : LemmaV31 σ J) (hV33 : LemmaV33 σ J) :
    σ.HypIV7 σ.p → ∀ W ∈ σ.familyW J, ∀ P : Subgroup G, IsSylowOf σ.p P σ.C →
      σ.D ≤ Subgroup.normalizer (P : Set G) → ∀ V ∈ signalizersPerm ⊤ σ.D W σ.p, P ≤ V →
      pPrimeCoreIn σ.p (V ⊔ W) = ⊥ →
      ∀ U₁ ∈ maximals (signalizersPerm ⊤ σ.D W σ.p), ∀ U₂ ∈ maximals (signalizersPerm ⊤ σ.D W σ.p),
        V ≤ U₁ → V ≤ U₂ → ∃ c ∈ σ.C ⊓ Subgroup.normalizer (W : Set G),
          U₁.map (MulAut.conj c).toMonoidHom = U₂ := by
  intro hHyp W hW P hP hDP V hV hPV hVcore
  have hp := hσ.p_prime
  have hp2 := hσ.p_ne_two
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  have hWp : ¬ σ.p ∣ Nat.card W := hV31.coprime W hW
  have hWodd : Odd (Nat.card W) := odd_card_of_mem_familyW hσ hJ hW
  have hPne : P ≠ ⊥ :=
    ne_bot_of_isSylowOf hp hP (hHyp.dvd_CL.trans (Subgroup.card_dvd_of_le inf_le_left))
  set 𝓜 := signalizersPerm ⊤ σ.D W σ.p with h𝓜
  set 𝓐 : Set (Subgroup G) := {U | U ∈ maximals 𝓜 ∧ V ≤ U} with h𝓐
  suffices key : ∀ U₁ ∈ 𝓐, ∀ U₂ ∈ 𝓐, ConjNCW σ W U₁ U₂ by
    intro U₁ hU₁ U₂ hU₂ hVU₁ hVU₂
    exact key U₁ ⟨hU₁, hVU₁⟩ U₂ ⟨hU₂, hVU₂⟩
  by_contra hcon
  simp only [not_forall] at hcon
  obtain ⟨U₁, hU₁A, U₂, hU₂A, hbad⟩ := hcon
  set Bad : Set (Subgroup G × Subgroup G) := {x | x.1 ∈ 𝓐 ∧ x.2 ∈ 𝓐 ∧ ¬ ConjNCW σ W x.1 x.2}
  obtain ⟨⟨U₁, U₂⟩, ⟨hU₁A, hU₂A, hbad⟩, hmax⟩ :=
    Set.exists_max_image Bad (fun x => Nat.card (x.1 ⊓ x.2 : Subgroup G)) (Set.toFinite _)
      ⟨(U₁, U₂), hU₁A, hU₂A, hbad⟩
  simp only at hU₁A hU₂A hbad hmax
  have hgood : ∀ A ∈ 𝓐, ∀ B ∈ 𝓐,
      Nat.card (U₁ ⊓ U₂ : Subgroup G) < Nat.card (A ⊓ B : Subgroup G) → ConjNCW σ W A B := by
    intro A hA B hB hlt
    by_contra hAB
    exact absurd (hmax (A, B) ⟨hA, hB, hAB⟩) (not_le.mpr hlt)
  obtain ⟨hU₁max, hVU₁⟩ := hU₁A
  obtain ⟨hU₂max, hVU₂⟩ := hU₂A
  have hU₁sig := hU₁max.1
  have hU₂sig := hU₂max.1
  have hPU₁ : P ≤ U₁ := hPV.trans hVU₁
  have hPU₂ : P ≤ U₂ := hPV.trans hVU₂
  set U := U₁ ⊓ U₂ with hUdef
  have hne : U₁ ≠ U₂ := by
    rintro rfl
    exact hbad (ConjNCW.refl σ W U₁)
  have hlt₁ : U < U₁ := by
    refine lt_of_le_of_ne inf_le_left fun h => hne ?_
    have h12 : U₁ ≤ U₂ := by
      rw [← h]
      exact inf_le_right
    exact (hU₁max.2 U₂ hU₂sig h12).symm
  have hlt₂ : U < U₂ := by
    refine lt_of_le_of_ne inf_le_right fun h => hne ?_
    have h21 : U₂ ≤ U₁ := by
      rw [← h]
      exact inf_le_left
    exact hU₂max.2 U₁ hU₁sig h21
  have hUsig : U ∈ 𝓜 := inf_mem_signalizersPerm hσ hJ h45 hV31 hV33 hW hP hU₁sig hU₂sig hPU₁ hPU₂
  have hPU : P ≤ U := le_inf hPU₁ hPU₂
  have hVU : V ≤ U := le_inf hVU₁ hVU₂
  have hUp : IsPGroup σ.p U := hUsig.1.2.1
  have hUcore : pPrimeCoreIn σ.p (U ⊔ W) = ⊥ :=
    pPrimeCoreIn_sup_eq_bot_of_le hp hUp hWp hUsig.2 hVU hVcore
  set H := Subgroup.normalizer (CFSG.thompsonCenter U : Set G) with hH
  have hUWH : U ⊔ W ≤ H := le_normalizer_thompsonCenter_of_odd hp hp2 hUp hWp hWodd hUsig.2 hUcore
  have hWH : W ≤ H := le_sup_right.trans hUWH
  have hUH : U ≤ H := le_sup_left.trans hUWH
  have hNUH : Subgroup.normalizer (U : Set G) ≤ H := normalizer_le_normalizer_thompsonCenter_self U
  have hDH : σ.D ≤ H := hUsig.1.2.2.1.trans hNUH
  have hPH : P ≤ H := hPU.trans hUH
  have hUne : U ≠ ⊥ := fun h => hPne (le_bot_iff.mp (h ▸ hPU))
  have hOH : oddCoreIn H ≠ ⊥ :=
    oddCoreIn_ne_bot_of_isPLocal hp hp2 (isPLocal_normalizer_thompsonCenter hp hUp hUne)
  have hsigH : ∀ X ∈ 𝓜, X ⊓ H ∈ signalizersPerm H σ.D W σ.p := by
    intro X hX
    refine ⟨⟨inf_le_right, hX.1.2.1.to_inf_left, ?_, ?_⟩, permutable_inf_of_le hWH hX.2⟩
    · exact (le_inf hX.1.2.2.1 (hDH.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    · exact inf_eq_bot_of_isPGroup_of_two hp hp2 hX.1.2.1.to_inf_left hD2
  have hUsigH : U ∈ signalizersPerm H σ.D W σ.p := by
    have h := hsigH U hUsig
    rwa [inf_eq_left.mpr hUH] at h
  have hltH : ∀ X ∈ 𝓜, U < X → U < X ⊓ H := fun X hX hUX =>
    (lt_inf_normalizer_of_lt hp hX.1.2.1 hUX).trans_le (inf_le_inf_left X hNUH)
  have hV41 := h41 H hDH hOH P hP hDP hPH W hW hWH
  obtain ⟨P₁, hP₁, hle₁, hP₁max, -⟩ := (hV41 (U₁ ⊓ H) (hsigH U₁ hU₁sig) (le_inf hPU₁ hPH)).1
  obtain ⟨P₂, hP₂, hle₂, hP₂max, -⟩ := (hV41 (U₂ ⊓ H) (hsigH U₂ hU₂sig) (le_inf hPU₂ hPH)).1
  have hUP₁ : U ≤ P₁ := (le_inf inf_le_left hUH).trans hle₁
  have hUP₂ : U ≤ P₂ := (le_inf inf_le_right hUH).trans hle₂
  obtain ⟨b, hb, hbP⟩ := (hV41 U hUsigH hPU).2 P₁ hP₁ P₂ hP₂ hP₁max hP₂max hUP₁ hUP₂
  have hbC : b ∈ σ.C ⊓ Subgroup.normalizer (W : Set G) := hb.1
  have hbD : b ∈ Subgroup.centralizer (σ.D : Set G) := hb.2
  have hbW : b ∈ Subgroup.normalizer (W : Set G) := hb.1.2
  have hto𝓜 : ∀ X ∈ signalizersPerm H σ.D W σ.p, X ∈ 𝓜 := fun X hX =>
    ⟨⟨le_top, hX.1.2.1, hX.1.2.2.1, hX.1.2.2.2⟩, hX.2⟩
  obtain ⟨Q₁, hQ₁, hPQ₁⟩ := exists_mem_maximals_ge (hto𝓜 P₁ hP₁)
  obtain ⟨Q₂, hQ₂, hPQ₂⟩ := exists_mem_maximals_ge (hto𝓜 P₂ hP₂)
  set Q₁' := Q₁.map (MulAut.conj b).toMonoidHom with hQ₁'
  have hQ₁'max : Q₁' ∈ maximals 𝓜 := map_conj_mem_maximals hbD hbW hQ₁
  have hP₂Q₁' : P₂ ≤ Q₁' := by
    rw [← hbP]
    exact (map_conj_le_map_conj_iff b).mpr hPQ₁
  have hVP₂ : V ≤ P₂ := hVU.trans hUP₂
  have hQ₁A : Q₁ ∈ 𝓐 := ⟨hQ₁, hVU.trans (hUP₁.trans hPQ₁)⟩
  have hQ₂A : Q₂ ∈ 𝓐 := ⟨hQ₂, hVP₂.trans hPQ₂⟩
  have hQ₁'A : Q₁' ∈ 𝓐 := ⟨hQ₁'max, hVP₂.trans hP₂Q₁'⟩
  have hcard : ∀ X ∈ 𝓜, U < X → ∀ A B : Subgroup G, X ⊓ H ≤ A ⊓ B →
      Nat.card U < Nat.card (A ⊓ B : Subgroup G) := fun X hX hUX A B hle =>
    (Subgroup.card_lt_of_lt (hltH X hX hUX)).trans_le (Subgroup.card_le_of_le hle)
  have r₁ : ConjNCW σ W U₁ Q₁ := hgood U₁ ⟨hU₁max, hVU₁⟩ Q₁ hQ₁A
    (hcard U₁ hU₁sig hlt₁ U₁ Q₁ (le_inf inf_le_left (hle₁.trans hPQ₁)))
  have r₂ : ConjNCW σ W Q₁ Q₁' := ⟨b, hbC, rfl⟩
  have r₃ : ConjNCW σ W Q₁' Q₂ := hgood Q₁' hQ₁'A Q₂ hQ₂A
    (hcard U₂ hU₂sig hlt₂ Q₁' Q₂ (le_inf (hle₂.trans hP₂Q₁') (hle₂.trans hPQ₂)))
  have r₄ : ConjNCW σ W Q₂ U₂ := hgood Q₂ hQ₂A U₂ ⟨hU₂max, hVU₂⟩
    (hcard U₂ hU₂sig hlt₂ Q₂ U₂ (le_inf (hle₂.trans hPQ₂) inf_le_left))
  exact hbad (((r₁.trans r₂).trans r₃).trans r₄)

end CFSG.ABGTheoremB.V56

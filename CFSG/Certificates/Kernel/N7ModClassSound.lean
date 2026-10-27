module

public import Certificates.Data.Kernel.N7ModClass
public import CFSG.Certificates.Kernel.N6ModClassSound

public section

namespace CFSG.KernelN7

open CFSG.CGT.T75JM CFSG.CGT.T75M23 CFSG.KernelN6

namespace InvPair7

variable {P Pi : Cols} (h : InvPair P Pi)
include h

theorem relC7_cj {X Y : Cols} (hX : Small X) (hY : Small Y) (hr : RelC7 X Y) :
    RelC7 (cjC P Pi X) (cjC P Pi Y) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
  have cc : ∀ {A B : Cols}, Small A → Small B →
      compC (cjC P Pi A) (cjC P Pi B) = cjC P Pi (compC A B) := fun _ hB => h.cj_comp hB
  have cp : ∀ {A : Cols}, Small A → ∀ n, powC (cjC P Pi A) n = cjC P Pi (powC A n) :=
    fun hA n => h.cj_pow hA n
  have sc : ∀ {A B : Cols}, Small A → Small B → Small (compC A B) := fun hA _ => small_compC hA _
  have sp : ∀ {A : Cols}, Small A → ∀ n, Small (powC A n) := fun hA n => small_powC hA n
  have sY4 := sp hY 4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cc hX hX, h1, h.cj_id]
  · intro he
    apply h2
    rw [← h.uncj hX, he, compC_idC, h.right]
  · rw [cp hY, h3, h.cj_id]
  · rw [cp hY 4, cc hX sY4, cc hY (sc hX sY4), cc hX (sc hY (sc hX sY4)),
      cp (sc hX (sc hY (sc hX sY4))), h4, h.cj_id]
  · rw [cp hY 4, cc sY4 hX, cp (sc sY4 hX), h5, h.cj_id]
  · have sA := sc hX hY
    have sB := sc sY4 sA
    have sC := sc hX sB
    have sD := sc hY sC
    rw [cp hY 4, cc hX hY, cc sY4 sA, cc hX sB, cc hY sC, cp sD, cc hX sY4,
      cc hY (sc hX sY4), cc (sp sD 2) (sc hY (sc hX sY4)), cc hX (sc (sp sD 2) (sc hY (sc hX sY4))),
      cc hY (sc hX (sc (sp sD 2) (sc hY (sc hX sY4)))),
      cc hX (sc hY (sc hX (sc (sp sD 2) (sc hY (sc hX sY4))))), h6, h.cj_id]

theorem equivC7_of_cj {X Y : Cols} (hX : Small X) (hY : Small Y)
    (he : EquivC7 (cjC P Pi X) (cjC P Pi Y)) : EquivC7 X Y := by
  obtain ⟨Q, Qi, hQ, hQi, h1, h2, h3, h4⟩ := he
  have sQ : Small Q := hQ
  have sQi : Small Qi := hQi
  have back : ∀ {A : Cols}, Small A → compC A P = compC P (cjC P Pi A) := fun {A} hA => by
    unfold cjC
    rw [← compC_assoc, ← compC_assoc, h.right, idC_compC hA]
  refine ⟨compC P Q, compC Qi Pi, small_compC h.sP Q, small_compC sQi Pi, ?_, ?_, ?_, ?_⟩
  · rw [compC_assoc, ← compC_assoc Pi, h.left, idC_compC sQ, h1]
  · rw [compC_assoc, ← compC_assoc Q, h2, idC_compC h.sPi, h.right]
  · rw [← compC_assoc, back hX, compC_assoc, h3, compC_assoc]
  · rw [← compC_assoc, back hY, compC_assoc, h4, compC_assoc]

end InvPair7

theorem relCB7_iff {X Y : Cols} : relCB7 X Y = true ↔ RelC7 X Y := by
  simp only [relCB7, RelC7, Bool.and_eq_true, Bool.not_eq_true', eqC_iff, Bool.eq_false_iff,
    ne_eq]
  tauto

theorem equivData7_of_equivB7 {X Y Q Qi : Cols} (h : equivB7 X Y Q Qi = true) :
    EquivData7 X Y Q Qi := by
  simp only [equivB7, Bool.and_eq_true, eqC_iff] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨small_of_smallB h1, small_of_smallB h2, h3, h4, h5, h6⟩

theorem conj_rep7 {L : List ℕ} (hL : invAll7 L = true) {X : Cols} (hX : Small X)
    (h1 : compC X X = idC) (h2 : X ≠ idC) :
    ∃ P Pi r, InvPair P Pi ∧ cjC P Pi X = repC7 r := by
  unfold invAll7 at hL
  rw [Bool.and_eq_true, List.all_eq_true] at hL
  have hm := packC_lt hX
  have hp : isInvB (packC X) = true := by
    unfold isInvB
    rw [unpackC_packC hX, Bool.and_eq_true, eqC_iff, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
      eqC_iff]
    exact ⟨h1, h2⟩
  obtain ⟨e, he, hem⟩ := mem_of_filter hL.1 hm hp
  have hok := hL.2 e he
  simp only [invRecOK7, Bool.and_eq_true, eqC_iff] at hok
  rw [hem, unpackC_packC hX] at hok
  exact ⟨_, _, _, ⟨small_unpackC _, small_unpackC _, hok.1.1, hok.1.2⟩, hok.2⟩

theorem rel_rep7 {L₀ : List ℕ} (h0 : relAll7 0 L₀ = true) (h1 : relAll7 1 [] = true) (r : ℕ)
    {Y : Cols} (hY : Small Y) (hr : RelC7 (repC7 r) Y) :
    EquivC7 (repC7 r) Y ∨ EquivC7 (repC7 r) (evalC (repC7 r) Y twistWord7) := by
  have key : ∀ {r' : ℕ} {L : List ℕ}, relAll7 r' L = true → RelC7 (repC7 r') Y →
      ∃ e ∈ L, e % 65536 = packC Y ∧ relRecOK7 e = true := by
    intro r' L h hrel
    unfold relAll7 at h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    have hp : relB7 r' (packC Y) = true := by
      unfold relB7
      rw [unpackC_packC hY]
      exact relCB7_iff.2 hrel
    obtain ⟨e, he, hem⟩ := mem_of_filter h.1 (packC_lt hY) hp
    exact ⟨e, he, hem, h.2 e he⟩
  by_cases hr0 : r = 0
  · subst hr0
    obtain ⟨e, -, hem, hok⟩ := key h0 hr
    unfold relRecOK7 at hok
    rw [hem, unpackC_packC hY] at hok
    have hok := equivData7_of_equivB7 hok
    have hrep : repC7 0 = modelX7 := rfl
    rw [hrep]
    split at hok
    · exact Or.inl ⟨_, _, hok⟩
    · exact Or.inr ⟨_, _, hok⟩
  · have hrep : repC7 r = repC7 1 := by simp [repC7, hr0]
    rw [hrep] at hr
    obtain ⟨e, he, -, -⟩ := key h1 hr
    simp at he

theorem modClass7_of_checks {L L₀ : List ℕ} (hA : invAll7 L = true) (h0 : relAll7 0 L₀ = true)
    (h1 : relAll7 1 [] = true) : ModClass7 := by
  intro X Y hX hY hrel
  obtain ⟨P, Pi, r, hP, hc⟩ := conj_rep7 hA hX hrel.1 hrel.2.1
  have hrel' := InvPair7.relC7_cj hP hX hY hrel
  rw [hc] at hrel'
  have sY' : Small (cjC P Pi Y) := small_compC (small_compC hP.sPi Y) P
  rcases rel_rep7 h0 h1 r sY' hrel' with he | he
  · left
    rw [← hc] at he
    exact InvPair7.equivC7_of_cj hP hX hY he
  · right
    rw [← hc, hP.cj_evalC hX hY] at he
    exact InvPair7.equivC7_of_cj hP hX (small_evalC hX hY _) he

end CFSG.KernelN7

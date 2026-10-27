module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2SlpCheck
public import CFSG.Sporadic.Co2Schreier.Tuples
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Certificates.Native CFSG.Sporadic.Co2Schreier
  CFSG.Monster.B.Mathieu

theorem slpGo_eq : ∀ (ds : List (List ℤ)) (A Ainv : Array (Array ℕ)), Ainv = rawInvs 2300 A →
    slpGo A Ainv ds = extendArrs A ds
  | [], A, Ainv, _ => rfl
  | w :: ds, A, Ainv, h => by
    subst h
    rw [slpGo, extendArrs_cons]
    refine slpGo_eq ds _ _ ?_
    rw [rawInvs, rawInvs, Array.map_push]

theorem slpFinal_eq (B : Array (Array ℕ)) (ds : List (List ℤ)) :
    slpFinal B ds = extendArrs B ds :=
  slpGo_eq ds B _ rfl

theorem slp_repTuple {B : Array (Array ℕ)} {gs : List (Equiv.Perm (Fin 2300))} {ds : List (List ℤ)}
    (hB : RepTuple 2300 B gs) (hds : extWordsOK B.size ds = true)
    (hinv : allInv (slpFinal B ds) = true) :
    RepTuple 2300 (slpFinal B ds) (extendTuple gs ds) := by
  rw [slpFinal_eq] at hinv ⊢
  refine RepTuple.extend hB ?_ hinv
  rwa [← hB.1]

theorem slp_length {B : Array (Array ℕ)} {gs : List (Equiv.Perm (Fin 2300))} {ds : List (List ℤ)}
    (hB : RepTuple 2300 B gs) : (extendTuple gs ds).length = (slpFinal B ds).size := by
  rw [slpFinal_eq, extendArrs_size, extendTuple_length, ← hB.1]

theorem slpOK_sound {B : Array (Array ℕ)} {gs : List (Equiv.Perm (Fin 2300))} {ds : List (List ℤ)}
    {eqs nes : List (List ℤ × List ℤ)} (hB : RepTuple 2300 B gs)
    (h : slpOK B ds eqs nes = true) :
    (∀ e ∈ eqs, wordValue (extendTuple gs ds) e.1 = wordValue (extendTuple gs ds) e.2) ∧
      (∀ e ∈ nes, wordValue (extendTuple gs ds) e.1 ≠ wordValue (extendTuple gs ds) e.2) := by
  simp only [slpOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hds, ⟨hinv, heqs⟩, hnes⟩ := h
  have hA := slp_repTuple hB hds hinv
  have hlen := slp_length (ds := ds) hB
  have hrw : ∀ w : List ℤ, lettersOK (slpFinal B ds).size w = true →
      Rep 2300 (wordA 2300 (slpFinal B ds) (rawInvs 2300 (slpFinal B ds)) w)
        (wordValue (extendTuple gs ds) w) := fun w hw =>
    hA.word hinv (hlen ▸ hw)
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨⟨hl1, hl2⟩, hq⟩ := heqs e he
    exact (eqA_iff (hrw _ hl1) (hrw _ hl2)).1 hq
  · obtain ⟨⟨hl1, hl2⟩, hq⟩ := hnes e he
    intro heq
    have := (eqA_iff (hrw _ hl1) (hrw _ hl2)).2 heq
    rw [this] at hq
    exact absurd hq (by simp)

theorem slpTargets_sound {B : Array (Array ℕ)} {gs : List (Equiv.Perm (Fin 2300))}
    {ds : List (List ℤ)} {tg : List (List ℤ × Array ℕ)} (hB : RepTuple 2300 B gs)
    (h : slpTargets B ds tg = true) :
    ∀ e ∈ tg, ∀ g, Rep 2300 e.2 g → wordValue (extendTuple gs ds) e.1 = g := by
  simp only [slpTargets, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hds, hinv, htg⟩ := h
  have hA := slp_repTuple hB hds hinv
  have hlen := slp_length (ds := ds) hB
  intro e he g hg
  obtain ⟨hl, hq⟩ := htg e he
  have hr := hA.word hinv (hlen ▸ hl)
  exact (eqA_iff hr hg).1 hq

theorem RepTuple_select {A : Array (Array ℕ)} {gs : List (Equiv.Perm (Fin 2300))}
    (hA : RepTuple 2300 A gs) {idx : List ℕ} (hidx : ∀ i ∈ idx, 1 ≤ i ∧ i ≤ gs.length) :
    RepTuple 2300 (selArr A idx) (idx.map fun i => gs.getD (i - 1) 1) := by
  refine ⟨by simp [selArr], fun h hh => ?_⟩
  have hh' : h < idx.length := by simpa using hh
  have e1 : (selArr A idx)[h]! = A[idx[h] - 1]! := by
    rw [getElem!_pos _ h (by simpa [selArr] using hh')]
    simp [selArr]
  have e2 : (idx.map fun i => gs.getD (i - 1) 1).getD h 1 = gs.getD (idx[h] - 1) 1 := by
    rw [List.getD_eq_getElem _ _ (by simpa using hh')]
    simp
  rw [e1, e2]
  have hi := hidx _ (List.getElem_mem hh')
  exact hA.2 _ (by omega)

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2

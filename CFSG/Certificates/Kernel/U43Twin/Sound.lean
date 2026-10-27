module

public import Certificates.Data.Kernel.U43Twin.Defs
public import CFSG.Certificates.Kernel.U43Pk.Sound
import CFSG.Certificates.Kernel.PackSetSound
import CFSG.Certificates.Kernel.SporSch.LyLoop

public section

namespace CFSG.KS.U43Twin

open CFSG.KD.U43Pk CFSG.KD.U43Twin CFSG.KS.U43Pk CFSG.KC.Enum CFSG.KS.ArrBfsSim
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check

theorem cjK_dec {G H P : ℕ} (hG : Dig G) (hH : Dig H) (hP : Dig P) :
    normalize (mulRaw (mulRaw (dec G) (dec P)) (dec H)) = dec (cjK G H P) := by
  rw [mulRaw_dec hG hP, act_dec (mulK_dig hG hP) hH]
  simp only [cjK, actK, CFSG.KC.Pack.strictN_eq]

theorem ptAK_spec {n N : ℕ} {A : ℕ → ℕ → ℕ} {R : ℕ} {T : ℕ → ℕ} {E : ℕ → ℕ → ℕ}
    {PA LA SO SOI : ℕ → ℕ} {i : ℕ} (h : ptAK n N A R T E PA LA SO SOI i = true) :
    validK (T i) = true ∧ CFSG.KS.SporSch.LyM.sortB T SO SOI N i = true ∧
      (∀ k < n, E i k < N ∧ A k (T i) = T (E i k) ∧
        (E i k = 0 ∨ posK n PA LA (E i k) ≤ n * i + k)) ∧
      (i = 0 → T 0 = R ∧ PA 0 = 0 ∧ LA 0 = 0) ∧
      (i ≠ 0 → PA i < i ∧ LA i < n ∧ E (PA i) (LA i) = i ∧
        (i + 1 ≠ N → posK n PA LA i < posK n PA LA (i + 1))) := by
  unfold ptAK at h
  rw [CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h⟩ := bAnd_spec h
  obtain ⟨h2, h⟩ := bAnd_spec h
  obtain ⟨h3, h4⟩ := bAnd_spec h
  refine ⟨h1, h2, fun k hk => ?_, fun hi => ?_, fun hi => ?_⟩
  · have e := CFSG.KC.Pack.allBlk_spec h3 k hk
    rw [Nat.add_eq, Nat.zero_add, CFSG.KC.Pack.strictB_eq] at e
    obtain ⟨e1, e⟩ := bAnd_spec e
    obtain ⟨e2, e3⟩ := bAnd_spec e
    refine ⟨Eq.mp Nat.blt_eq e1, Nat.eq_of_beq_eq_true e2, ?_⟩
    rw [bIf_eq] at e3
    by_cases h0 : E i k = 0
    · exact Or.inl h0
    · have hb : Nat.beq (E i k) 0 = false :=
        Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
      rw [hb] at e3
      simp only [Bool.false_eq_true, ↓reduceIte] at e3
      exact Or.inr (Nat.le_of_ble_eq_true e3)
  · subst hi
    rw [bIf_eq] at h4
    simp only [Nat.beq_refl, ↓reduceIte] at h4
    obtain ⟨e1, e⟩ := bAnd_spec h4
    obtain ⟨e2, e3⟩ := bAnd_spec e
    exact ⟨Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2, Nat.eq_of_beq_eq_true e3⟩
  · have hb : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
    rw [bIf_eq, hb] at h4
    simp only [Bool.false_eq_true, ↓reduceIte] at h4
    obtain ⟨e1, e⟩ := bAnd_spec h4
    obtain ⟨e2, e⟩ := bAnd_spec e
    obtain ⟨e3, e4⟩ := bAnd_spec e
    refine ⟨Eq.mp Nat.blt_eq e1, Eq.mp Nat.blt_eq e2, Nat.eq_of_beq_eq_true e3, fun hi' => ?_⟩
    rw [bIf_eq] at e4
    have hb' : Nat.beq (Nat.succ i) N = false :=
      Bool.eq_false_iff.2 fun h => hi' (Nat.eq_of_beq_eq_true h)
    rw [hb'] at e4
    simp only [Bool.false_eq_true, ↓reduceIte] at e4
    exact Eq.mp Nat.blt_eq e4

theorem tablesA_of {n N : ℕ} {act : ℕ → Array ℕ → Array ℕ} {A : ℕ → ℕ → ℕ} {R : ℕ}
    {T : ℕ → ℕ} {E : ℕ → ℕ → ℕ} {PA LA SO SOI : ℕ → ℕ} (hN : 2 ≤ N)
    (hA : ∀ k < n, ∀ P, rawValidK P = true → act k (dec P) = dec (A k P))
    (hpt : ∀ i < N, ptAK n N A R T E PA LA SO SOI i = true) :
    Tables n N act keyOf (fun i => dec (T i)) E PA LA ∧
      (∀ i < N, valid (dec (T i)) = true) ∧ T 0 = R := by
  have hs : ∀ i < N, CFSG.KS.SporSch.LyM.sortB T SO SOI N i = true := fun i hi =>
    (ptAK_spec (hpt i hi)).2.1
  have hinj := CFSG.KS.SporSch.LyLoop.sortB_inj hs
  have hv : ∀ i < N, validK (T i) = true := fun i hi => (ptAK_spec (hpt i hi)).1
  have hr : ∀ i < N, rawValidK (T i) = true := fun i hi => (validK_spec (hv i hi)).1
  refine ⟨⟨hN, fun i hi k hk => ?_, fun a ha b hb e => ?_, ?_, ?_, fun j hj1 hjN => ?_,
    fun j hj1 hjN => ?_, fun i hi k hk => ?_⟩, fun i hi => valid_dec (hv i hi), ?_⟩
  · obtain ⟨e1, e2, -⟩ := (ptAK_spec (hpt i hi)).2.2.1 k hk
    refine ⟨e1, ?_⟩
    rw [hA k hk _ (hr i hi), e2]
  · exact hinj a ha b hb (keyOf_dec_inj (hr a ha) (hr b hb) e)
  · exact ((ptAK_spec (hpt 0 (by omega))).2.2.2.1 rfl).2.1
  · exact ((ptAK_spec (hpt 0 (by omega))).2.2.2.1 rfl).2.2
  · obtain ⟨h1, h2, h3, -⟩ := (ptAK_spec (hpt j hjN)).2.2.2.2 (by omega)
    exact ⟨h1, h2, h3⟩
  · obtain ⟨-, -, -, h4⟩ := (ptAK_spec (hpt j (by omega))).2.2.2.2 (by omega)
    exact h4 (by omega)
  · exact ((ptAK_spec (hpt i hi)).2.2.1 k hk).2.2
  · exact ((ptAK_spec (hpt 0 (by omega))).2.2.2.1 rfl).1

end CFSG.KS.U43Twin

end

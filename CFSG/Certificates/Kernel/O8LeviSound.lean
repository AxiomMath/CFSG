module

public import Certificates.Data.Kernel.O8.Levi
public import CFSG.Certificates.Kernel.O8SoundDefs
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.O8WordProved
import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage1

@[expose] def leviCheckG (n : ℕ) (G P : ℕ → Array ℕ) (ws : List ℕ) (L : Array ℕ) : Bool :=
  let k := ws.foldr (fun s acc => compA n (P s) acc) (idA n)
  wordRowsG G ws == L && eqA n (compA n (compA n k k) (compA n k k)) (idA n)

namespace LeviPf

open CFSG.KC.Enum CFSG.KS CFSG.KC.O8.OrthPf CFSG.KC.O8.WordPf

@[expose] def AgL (n w : ℕ) (t : Array ℕ) (P : ℕ) : Prop :=
  ∀ x < n, t[x]! = pg w (mask w) P x

theorem fget_pg (X i w : ℕ) : fget X i w = pg w (mask w) X i := by
  have e : Nat.mul i w = Nat.mul w i := Nat.mul_comm i w
  change Nat.land (Nat.shiftRight X (Nat.mul i w)) (maskN w) =
    Nat.land (Nat.shiftRight X (Nat.mul w i)) (mask w)
  rw [e]
  rfl

theorem maskN_mask (w : ℕ) : maskN w = mask w := rfl

theorem agL_compA {n w : ℕ} {t u : Array ℕ} {P Q : ℕ} (hn : n < 2 ^ 32) (ht : AgL n w t P)
    (hu : AgL n w u Q) (hQ : ∀ x < n, pg w (mask w) Q x < n) :
    AgL n w (compA n t u) (pcomp n w (mask w) P Q) := fun x hx => by
  rw [CFSG.Monster.B.Co2.compA_get hx, hu x hx, ht _ (hQ x hx), PF.pg_pcomp hn hx]

theorem lt_pcomp {n w : ℕ} {P Q : ℕ} (hn : n < 2 ^ 32) (hP : ∀ x < n, pg w (mask w) P x < n)
    (hQ : ∀ x < n, pg w (mask w) Q x < n) :
    ∀ x < n, pg w (mask w) (pcomp n w (mask w) P Q) x < n := fun x hx => by
  rw [PF.pg_pcomp hn hx]
  exact hP _ (hQ x hx)

theorem agL_of_toList {n w : ℕ} {t : Array ℕ} {P : ℕ}
    (h : t.toList = (List.range n).map fun i => fget P i w) : AgL n w t P := fun x hx => by
  have hsz : t.size = n := by
    have := congrArg List.length h
    simpa using this
  have h1 : t.toList[x]? = some (fget P x w) := by
    rw [h]
    simp [hx]
  rw [getElem!_pos t x (by omega), ← fget_pg]
  rw [Array.getElem?_toList, Array.getElem?_eq_getElem (by omega)] at h1
  exact Option.some.inj h1

theorem fold_agL {n w m PP : ℕ} {P : ℕ → Array ℕ} (hn : n < 16777216) (hw : n + 1 < 2 ^ w)
    (hP : ∀ s < m, AgL n w (P s) (permAt n w PP s))
    (hPlt : ∀ s < m, ∀ x < n, pg w (mask w) (permAt n w PP s) x < n) :
    ∀ ws : List ℕ, (∀ s ∈ ws, s < m) →
      AgL n w (ws.foldr (fun s acc => compA n (P s) acc) (idA n)) (wordPermK n w PP ws) ∧
        ∀ x < n, pg w (mask w) (wordPermK n w PP ws) x < n
  | [], _ => by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [List.foldr_nil, CFSG.Monster.B.Co2.idA_get hx]
      exact (PF.pg_pidn hn hw hx).symm
    · change pg w (mask w) (pidn n w) x < n
      rw [PF.pg_pidn hn hw hx]
      exact hx
  | s :: ws, h' => by
    obtain ⟨ih1, ih2⟩ := fold_agL hn hw hP hPlt ws (fun t ht => h' t (by simp [ht]))
    have hs := h' s (by simp)
    have hn32 : n < 2 ^ 32 := by omega
    change AgL n w (compA n (P s) (ws.foldr (fun s acc => compA n (P s) acc) (idA n)))
        (pcomp n w (maskN w) (permAt n w PP s) (wordPermK n w PP ws)) ∧
      ∀ x < n, pg w (mask w) (pcomp n w (maskN w) (permAt n w PP s) (wordPermK n w PP ws)) x < n
    rw [maskN_mask]
    exact ⟨agL_compA hn32 (hP s hs) ih1 ih2, lt_pcomp hn32 (hPlt s hs) ih2⟩

end LeviPf

open CFSG.KC.Enum CFSG.KS CFSG.KC.O8.OrthPf CFSG.KC.O8.WordPf CFSG.KC.O8.LeviPf in
theorem levi_sound {n w m GP PP L : Nat} {G P : ℕ → Array ℕ} {ws : List ℕ} {Lr : Array ℕ}
    (hn : n < 16777216) (hw : n + 1 < 2 ^ w)
    (hG : ∀ s < 6, G s = decR (mat GP s))
    (hP : ∀ s < m, (P s).toList = (List.range n).map fun i => fget (permAt n w PP s) i w)
    (hm : m ≤ 6) (hl : ∀ s ∈ ws, s < m) (hL : Lr = decR L) (h : leviOK n w GP PP ws L = true) :
    leviCheckG n G P ws Lr = true := by
  unfold leviOK at h
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hl6 : ∀ s ∈ ws, s < 6 := fun s hs => Nat.lt_of_lt_of_le (hl s hs) hm
  have hrows : wordRowsG G ws = Lr := by
    rw [← wordRowsK_eq hG ws hl6, Nat.eq_of_beq_eq_true h1, hL]
  rw [allN_eq, List.all_eq_true] at h2
  have hPlt : ∀ s < m, ∀ x < n, pg w (mask w) (permAt n w PP s) x < n := fun s hs x hx => by
    have := h2 s (List.mem_range.2 (Nat.lt_of_lt_of_le hs hm))
    rw [allN_eq, List.all_eq_true] at this
    have h5 := this x (List.mem_range.2 hx)
    rw [Nat.blt_eq] at h5
    exact h5
  have hn32 : n < 2 ^ 32 := by omega
  obtain ⟨hk, hklt⟩ := fold_agL hn hw (fun s hs => agL_of_toList (hP s hs)) hPlt ws hl
  have hk2 := agL_compA hn32 hk hk hklt
  have hk2lt := lt_pcomp hn32 hklt hklt
  have hk4 := agL_compA hn32 hk2 hk2 hk2lt
  rw [strictN_eq] at h3
  beta_reduce at h3
  rw [strictN_eq] at h3
  beta_reduce at h3
  rw [nIf_eq, maskN_mask] at h3
  have h4 : pcomp n w (mask w) (pcomp n w (mask w) (wordPermK n w PP ws) (wordPermK n w PP ws))
      (pcomp n w (mask w) (wordPermK n w PP ws) (wordPermK n w PP ws)) = pidn n w := by
    by_contra hne
    rw [if_neg (fun h' => hne (Nat.eq_of_beq_eq_true h'))] at h3
    exact absurd h3 (by decide)
  simp only [leviCheckG]
  rw [hrows, beq_self_eq_true, Bool.true_and, eqA, CFSG.Monster.B.Co2.allLt_iff]
  intro x hx
  rw [hk4 x hx, h4, PF.pg_pidn hn hw hx, CFSG.Monster.B.Co2.idA_get hx, beq_self_eq_true]

end CFSG.KC.O8

end

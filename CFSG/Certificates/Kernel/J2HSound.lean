module

public import Certificates.Data.Kernel.J2H
public import CFSG.Certificates.Kernel.J2CoverSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.PK.Basic
public import CFSG.Certificates.Kernel.LocalQTCovTPrim
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutModel

public section

namespace CFSG.KC.J2H

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.J2Cover CFSG.Certificates
open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover

variable {n : ℕ}

@[expose] def sgnProd (gs : ℕ → Equiv.Perm (Fin n)) (wd : List ℤ) : Equiv.Perm (Fin n) :=
  (wd.map fun l => if 0 < l then gs (l.toNat - 1) else (gs ((-l).toNat - 1))⁻¹).prod

@[simp] theorem sgnProd_nil (gs : ℕ → Equiv.Perm (Fin n)) : sgnProd gs [] = 1 := rfl

theorem sgnProd_cons (gs : ℕ → Equiv.Perm (Fin n)) (l : ℤ) (wd : List ℤ) :
    sgnProd gs (l :: wd) =
      (if 0 < l then gs (l.toNat - 1) else (gs ((-l).toNat - 1))⁻¹) * sgnProd gs wd := by
  simp [sgnProd]

theorem sgnProd_append (gs : ℕ → Equiv.Perm (Fin n)) (a b : List ℤ) :
    sgnProd gs (a ++ b) = sgnProd gs a * sgnProd gs b := by
  simp [sgnProd]

theorem lettersOK_cons {j : ℕ} {l : ℤ} {wd : List ℤ} (h : lettersOK j (l :: wd) = true) :
    (l ≠ 0 ∧ l.natAbs ≤ j) ∧ lettersOK j wd = true := by
  simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  exact ⟨h.1, by simpa [lettersOK, List.all_eq_true] using h.2⟩

theorem rep_wordA_sgn {S Sinv : Array (Array ℕ)} {gs : ℕ → Equiv.Perm (Fin n)} {j : ℕ}
    (hS : ∀ h < j, Rep n S[h]! (gs h)) (hSi : ∀ h < j, Rep n Sinv[h]! (gs h)⁻¹) :
    ∀ wd : List ℤ, lettersOK j wd = true → Rep n (wordA n S Sinv wd) (sgnProd gs wd)
  | [], _ => by simpa [wordA] using (rep_idA (n := n))
  | l :: wd, h => by
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := lettersOK_cons h
    rw [wordA, sgnProd_cons]
    refine rep_compA ?_ (rep_wordA_sgn hS hSi wd hw)
    unfold letterA
    by_cases hpos : 0 < l
    · rw [if_pos hpos, if_pos hpos]
      exact hS _ (by omega)
    · rw [if_neg hpos, if_neg hpos]
      exact hSi _ (by omega)

theorem sgnProd_mem {H : Subgroup (Equiv.Perm (Fin n))} {gs : ℕ → Equiv.Perm (Fin n)} {m : ℕ}
    (hg : ∀ i < m, gs i ∈ H) : ∀ wd : List ℤ, lettersOK m wd = true → sgnProd gs wd ∈ H
  | [], _ => H.one_mem
  | l :: wd, h => by
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := lettersOK_cons h
    rw [sgnProd_cons]
    refine H.mul_mem ?_ (sgnProd_mem hg wd hw)
    split
    · exact hg _ (by omega)
    · exact H.inv_mem (hg _ (by omega))

theorem rep_of_binds {w : ℕ} {PS PSI : ℕ → ℕ} {kS nb BP : ℕ} {S : Array (Array ℕ)}
    {base : Array ℕ} (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true) {j : ℕ}
    (hj : j < kS) :
    Rep n S[j]! (permOfArr n S[j]!) ∧ Rep n (rawInvs n S)[j]! (permOfArr n S[j]!)⁻¹ := by
  have hS : S[j]! = unpack n w (PS j) := hb.2.2.2.2.1 j hj
  have hsz : j < S.size := by rw [hb.2.2.2.1]; exact hj
  obtain ⟨h1, h2⟩ := invEqK_sound (CFSG.KS.PK.allN_iff.1 hp j hj)
  rw [getElem!_rawInvs hsz, hS, h1]
  exact rep_permOfArr h2

theorem word_rep {w : ℕ} {PS PSI : ℕ → ℕ} {kS nb BP : ℕ} {S : Array (Array ℕ)}
    {base : Array ℕ} (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    {wd : List ℤ} {r : ℕ} (h : wordEqK n w (mask w) (pidn n w) PS PSI kS wd r = true) :
    Rep n (unpack n w r) (sgnProd (fun h => permOfArr n S[h]!) wd) := by
  obtain ⟨he, hl⟩ := wordEqK_sound ⟨hb.2.2.2.1, hb.2.2.2.2.1⟩ hp h
  rw [← he]
  exact rep_wordA_sgn (fun h hh => (rep_of_binds hb hp hh).1)
    (fun h hh => (rep_of_binds hb hp hh).2) wd hl

theorem rep_pidn : Rep 315 (unpack 315 9 (pidn 315 9)) 1 := by
  rw [CFSG.KC.LQT.Cov.T.unpack_pidn (by norm_num) (by norm_num)]
  exact rep_idA

theorem card_comm_eq {S : Array (Array ℕ)} {k : ℕ} {hk : k ≤ S.size} {base : List (Fin 315)}
    {hbn : base.Nodup} {W : Array (List ℤ)} {kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}
    (hb : Binds 315 9 PS kS nb BP S (base.map Fin.val).toArray)
    (hp : allN kS (fun j => permOK 315 9 (mask 9) (315 * 9) (PS j) (PSI j)) = true)
    (hl : LevelsOK 315 9 PS PSI LR TR TRI kS nb BP)
    (hc : rawChainOK 315 (S.extract 0 k) S (base.map Fin.val).toArray W 4 = true)
    {m : ℕ} {G : ℕ → ℕ} {g : ℕ → Equiv.Perm (Fin 315)}
    (hG : ∀ j < m, canonK 315 9 (mask 9) (315 * 9) (G j) = true ∧
      Rep 315 (unpack 315 9 (G j)) (g j)) :
    Nat.card {x : (RawSchreierDatum.ofArrays 315 (by norm_num) S k hk base hbn W).originalSubgroup //
        ∀ j < m, (x : Equiv.Perm (Fin 315)) * g j = g j * x} =
      prodCnt 315 9 nb LR TR (commAllK m G) := by
  set Q := RawSchreierDatum.ofArrays 315 (by norm_num) S k hk base hbn W
  have hQ : ValidSchreier Q := ofArrays_valid (by norm_num) hc
  let fT : Table → Bool := fun T => allN m (fun j => commT 315 T (arrTable 315 (unpack 315 9 (G j))))
  have hf : ∀ X, canonK 315 9 (mask 9) (315 * 9) X = true →
      fT (arrTable 315 (unpack 315 9 X)) = commAllK m G X := by
    intro X hX
    rw [Bool.eq_iff_iff, CFSG.KS.PK.allN_iff, commAllK, CFSG.KS.PK.allN_iff]
    refine forall_congr' fun j => imp_congr_right fun hj => ?_
    rw [commT_unpack hX (hG j hj).1]
  have h1 := countProducts_sound hb hp hl hf
  rw [← ofArrays_levelTables (hn := by norm_num) (hk := hk) (hb := hbn) hc] at h1
  have hfP : ∀ T x, CFSG.Sporadic.Th.Rep 315 T x →
      (fT T = true ↔ ∀ j < m, x * g j = g j * x) := by
    intro T x hT
    rw [CFSG.KS.PK.allN_iff]
    refine forall_congr' fun j => imp_congr_right fun hj => ?_
    exact commT_iff hT (rep_arrTable (by norm_num) (hG j hj).2)
  have h2 := countProducts_spec (P := fun x : Equiv.Perm (Fin 315) => ∀ j < m, x * g j = g j * x)
    hfP (forall₂_levelTables (by norm_num) Q) (CFSG.Sporadic.Th.Rep.idT (by norm_num))
  simp only [one_mul, List.map_id'] at h2
  rw [← h1, h2]
  exact card_subtype_eq_countP Q.originalSubgroup (enumeration Q) (enumeration_nodup Q hQ)
    (mem_enumeration_iff Q hQ) (fun x : Equiv.Perm (Fin 315) => ∀ j < m, x * g j = g j * x)

end CFSG.KC.J2H

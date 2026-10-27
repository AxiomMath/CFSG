module

public import CFSG.Certificates.Kernel.OrbRow.WordRep
public import CFSG.Certificates.Kernel.BfsPinKeyYSound

public section

namespace CFSG.KC.OrbRow

open CFSG.KC.Enum CFSG.KC.PGrp CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin

variable {n w : ℕ}

theorem posWord_rec_canon {G : ℕ → ℕ} :
    ∀ (wd : List ℕ), (∀ l ∈ wd, canonK n w (mask w) (n * w) (G l) = true) → ∀ (acc : ℕ),
      canonK n w (mask w) (n * w) acc = true →
      canonK n w (mask w) (n * w) (List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
        (fun l _ ih acc => strictN (pcomp n w (mask w) acc (G l)) ih) wd acc) = true
  | [], _, _, h => h
  | l :: wd, hG, acc, h => by
    change canonK n w (mask w) (n * w) (strictN (pcomp n w (mask w) acc (G l)) _) = true
    rw [strictN_apply]
    exact posWord_rec_canon wd (fun l' hl' => hG l' (List.mem_cons_of_mem _ hl')) _
      (canonK_pcomp h (hG l List.mem_cons_self))

theorem posWordK_canon (hsz : szOK n w = true) {G : ℕ → ℕ} {wd : List ℕ}
    (hG : ∀ l ∈ wd, canonK n w (mask w) (n * w) (G l) = true) :
    canonK n w (mask w) (n * w) (posWordK n w G wd) = true :=
  posWord_rec_canon wd hG _ (PP.id hsz).1

theorem posWordK_chunks {m : ℕ} (hsz : szOK n w = true) {F : ℕ → ℕ}
    (hF : ∀ l < m, CFSG.KC.Misc.ArrEnum.permB n w (F l) = true) {W : List (List ℕ)}
    (hW : ∀ c ∈ W, ∀ l ∈ c, l < m) (ik : List ℕ) :
    posWordK n w (fun j => posWordK n w F (W.getD j [])) ik =
      posWordK n w F ((ik.map fun j => W.getD j []).flatten) := by
  obtain ⟨hn, hw⟩ := szOK_facts' hsz
  have hex : ∀ l, ∃ g : Equiv.Perm (Fin n), l < m → Orb.PRep n w (F l) g := by
    intro l
    by_cases hl : l < m
    · exact ⟨_, fun _ => Orb.prep_of_rep
        (CFSG.Monster.B.Co2.rep_permOfArr (Orb.isInvA_unpack (hF l hl))).1⟩
    · exact ⟨1, fun h => absurd h hl⟩
  choose σ hσ using hex
  have hc : ∀ l < m, canonK n w (mask w) (n * w) (F l) = true := fun l hl =>
    (CFSG.KC.Misc.ArrEnum.pp_of_permB hsz (hF l hl)).1
  have hget : ∀ j, ∀ l ∈ W.getD j [], l < m := by
    intro j l hl
    by_cases hj : j < W.length
    · rw [List.getD_eq_getElem _ _ hj] at hl
      exact hW _ (List.getElem_mem hj) l hl
    · rw [List.getD_eq_default _ _ (by omega)] at hl
      exact absurd hl List.not_mem_nil
  have hflat : ∀ l ∈ (ik.map fun j => W.getD j []).flatten, l < m := by
    intro l hl
    obtain ⟨c, hc', hl⟩ := List.mem_flatten.1 hl
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc'
    exact hget j l hl
  have e : ((ik.map fun j => W.getD j []).flatten.map σ).prod =
      (ik.map fun j => ((W.getD j []).map σ).prod).prod := by
    rw [List.map_flatten, List.prod_flatten, List.map_map, List.map_map]
    rfl
  refine canon_eq_of_prep (g := ((ik.map fun j => W.getD j []).flatten.map σ).prod)
    (posWordK_canon hsz fun j _ => posWordK_canon hsz fun l hl => hc l (hget j l hl))
    (posWordK_canon hsz fun l hl => hc l (hflat l hl)) ?_
    (posWordK_rep hn hw fun l hl => hσ l (hflat l hl))
  rw [e]
  exact posWordK_rep hn hw fun j _ => posWordK_rep hn hw fun l hl => hσ l (hget j l hl)

end CFSG.KC.OrbRow

end

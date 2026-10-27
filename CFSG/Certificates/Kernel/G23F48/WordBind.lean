module

public import Certificates.Data.Kernel.G23F48.Words
public import CFSG.Milestones.ASVolI.F48.Rest.Perm
public import CFSG.Certificates.Kernel.Enum.ZCSound
public import CFSG.Certificates.Kernel.Misc.ArrBind

public section

namespace CFSG.KC.G23F48

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.Misc.ArrEnum
open CFSG.ONSchreier.Native (pinvCand)

theorem evA_size {n k : ℕ} (L Li : Array (Array ℕ)) (word : List (Fin k × Bool)) :
    (burnsideF48t_evA n L Li word).size = n := by
  cases word with
  | nil => simp [burnsideF48t_evA, CFSG.ONSchreier.Native.pid]
  | cons l word => simp [burnsideF48t_evA, CFSG.ONSchreier.Native.pcomp]

theorem prep_evP {n w k : ℕ} {LP LPI : ℕ → ℕ} {σ : Fin k → Equiv.Perm (Fin n)}
    (hn : n < 16777216) (hw : n + 1 < 2 ^ w)
    (hσ : ∀ i : Fin k, PRep n w (LP i) (σ i) ∧ PRep n w (LPI i) (σ i)⁻¹) :
    ∀ word : List (Fin k × Bool), PRep n w (evP n w LP LPI word) (burnsideF48s_ev σ word)
  | [] => prep_pidn hn hw
  | ⟨i, false⟩ :: word => by
    rw [burnsideF48s_ev_cons]
    exact prep_pcomp (by omega) (hσ i).2 (prep_evP hn hw hσ word)
  | ⟨i, true⟩ :: word => by
    rw [burnsideF48s_ev_cons]
    exact prep_pcomp (by omega) (hσ i).1 (prep_evP hn hw hσ word)

theorem evA_eq_unpack {n w k : ℕ} {L : Array (Array ℕ)} {LP LPI : ℕ → ℕ}
    (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (hk : k ≤ L.size)
    (hb : ∀ i < k, arrBind L[i]! n w (LP i) = true)
    (hp : ∀ i < k, permOK n w (mask w) (n * w) (LP i) (LPI i) = true)
    (word : List (Fin k × Bool)) :
    burnsideF48t_evA n L (L.map (pinvCand n)) word = unpack n w (evP n w LP LPI word) := by
  have hg : ∀ i : Fin k, ∃ g : Equiv.Perm (Fin n), PRep n w (LP i) g ∧ PRep n w (LPI i) g⁻¹ :=
    fun i => CFSG.KC.EnumSound.permOK_perm (hp i i.2)
  choose σ hσ using hg
  have hL : ∀ i : Fin k, CFSG.ONSchreier.PRep n L[(i : ℕ)]! (σ i) := fun i x => by
    rw [arrBind_sound (hb i i.2), unpack_get x.2]
    exact (hσ i).1 x
  have hrec : burnsideF48t_RecL n L (L.map (pinvCand n)) σ := fun i => by
    refine ⟨hL i, ?_⟩
    have e : (L.map (pinvCand n))[(i : ℕ)]! = pinvCand n L[(i : ℕ)]! := by
      rw [getElem!_pos _ _ (by simp only [Array.size_map]; omega), getElem!_pos L _ (by omega),
        Array.getElem_map]
    rw [e]
    exact (CFSG.KS.BfsPar.prep_pinvCand (hL i)).1
  have hA := burnsideF48t_prep_evA hrec word
  have hP := prep_evP hn hw hσ word
  apply Array.ext
  · rw [evA_size]
    simp [unpack]
  · intro i h1 h2
    have hi : i < n := by rwa [evA_size] at h1
    rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2, hA ⟨i, hi⟩, unpack_get hi]
    exact (hP ⟨i, hi⟩).symm

end CFSG.KC.G23F48

end

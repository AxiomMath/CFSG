module

public import Certificates.Data.Kernel.Fi23Q.SubChain
public import CFSG.Certificates.Kernel.Fi23Q.ChainSound

public section

namespace CFSG.KS.Fi23Q

open CFSG.KC.Enum CFSG.KC.Fi23Q

variable {G : Type*} [Group G]

theorem fixG_iff {img : ℕ → ℕ → ℕ} {p : ℕ} {R : List (ℕ × List ℕ)} :
    fixG img p R = true ↔ ∀ m ∈ R, ∀ v ∈ m.2, img v p = p := by
  induction R with
  | nil => simp [fixG]
  | cons m t ih =>
    change (Bool.rec (motive := fun _ => Bool) false (fixG img p t)
      (allL m.2 fun v => Nat.beq (img v p) p)) = true ↔ _
    rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, ih, allL_iff]
    simp [Nat.beq_eq]

theorem chainG_of {img : ℕ → ℕ → ℕ} {ok : ℕ → Bool} {act : G → ℕ → ℕ} {E : ℕ → G}
    (hW : ∀ v, ok v = true → ∀ x < 31671, img v x = act (E v) x) :
    ∀ Ls : List (ℕ × List ℕ), chainG img ok Ls = true →
      ChainP act (Ls.map fun l => (l.1, l.2.map E)) ∧ ∀ l ∈ Ls, ∀ v ∈ l.2, ok v = true
  | [], _ => ⟨trivial, fun _ h => absurd h List.not_mem_nil⟩
  | l :: R, h => by
    change (Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false (chainG img ok R) (fixG img l.1 R))
          (nodupN (l.2.map fun v => img v l.1)))
        (allL l.2 ok))
      (Nat.blt l.1 31671)) = true at h
    simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨hp, hv, hd, hf, hR⟩ := h
    rw [Nat.blt_eq] at hp
    rw [allL_iff] at hv
    rw [nodupN_iff] at hd
    rw [fixG_iff] at hf
    obtain ⟨ihC, ihV⟩ := chainG_of hW R hR
    have hmap : (l.2.map fun v => img v l.1) = (l.2.map E).map fun y => act y l.1 := by
      rw [List.map_map]
      exact List.map_congr_left fun v hv' => hW v (hv v hv') l.1 hp
    refine ⟨⟨by rw [← hmap]; exact hd, ?_, ihC⟩, ?_⟩
    · intro m hm y hy
      obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hm
      obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hy
      rw [← hW v (ihV m' hm' v hv') l.1 hp]
      exact hf m' hm' v hv'
    · intro l' hl' v hv'
      rcases List.mem_cons.1 hl' with rfl | hl'
      · exact hv v hv'
      · exact ihV l' hl' v hv'

end CFSG.KS.Fi23Q

end

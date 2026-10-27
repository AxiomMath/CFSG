module

public import Certificates.Data.Kernel.L34DWord
public import CFSG.Certificates.Kernel.L34TwoSigKSound
import CFSG.Certificates.Kernel.L34KSnd.Tab

public section

namespace CFSG.KC.L34Two

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34KSnd
open CFSG.KC.L34Scan CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem dwordK_mem {m : Nat} {A : Nat → Nat} {H : Subgroup (Equiv.Perm (Fin 42))} (hm : 0 < m)
    (hA : ∀ j < m, canonK 42 6 (mask 6) (42 * 6) (A j) = true ∧
      ∃ a ∈ H, TabRep (unpack 42 6 (A j)) a) :
    ∀ f wd, canonK 42 6 (mask 6) (42 * 6) (dwordK 42 6 A m f wd) = true ∧
      ∃ v ∈ H, TabRep (unpack 42 6 (dwordK 42 6 A m f wd)) v
  | 0, _ => ⟨canon_pidn hsz42, 1, H.one_mem, by
      change TabRep (unpack 42 6 (pidn 42 6)) 1
      rw [← idTab_unpack' hsz42]
      exact TabRep.idTab⟩
  | f + 1, wd => by
    have e : dwordK 42 6 A m (f + 1) wd = strictN (Nat.land wd 15) fun d =>
        nIf(Nat.beq d 0, pidn 42 6,
          pcomp 42 6 (mask 6) (A (Nat.mod (Nat.sub d 1) m))
            (dwordK 42 6 A m f (Nat.shiftRight wd 4))) := rfl
    rw [e, strictN_eq]
    cases Nat.beq (Nat.land wd 15) 0
    · obtain ⟨ca, a, ha, har⟩ := hA _ (Nat.mod_lt _ hm)
      obtain ⟨cw, v, hv, hvr⟩ := dwordK_mem hm hA f (Nat.shiftRight wd 4)
      refine ⟨canonK_pcomp ca cw, a * v, H.mul_mem ha hv, ?_⟩
      have hr := har.comp hvr
      rw [comp_unpack' ca cw] at hr
      exact hr
    · exact ⟨canon_pidn hsz42, 1, H.one_mem, by
        change TabRep (unpack 42 6 (pidn 42 6)) 1
        rw [← idTab_unpack' hsz42]
        exact TabRep.idTab⟩

theorem mem_of_dwordK {m f wd G : Nat} {A : Nat → Nat} {H : Subgroup (Equiv.Perm (Fin 42))}
    {g : Equiv.Perm (Fin 42)} (hm : 0 < m)
    (hA : ∀ j < m, canonK 42 6 (mask 6) (42 * 6) (A j) = true ∧
      ∃ a ∈ H, TabRep (unpack 42 6 (A j)) a)
    (hg : TabRep (unpack 42 6 G) g) (h : Nat.beq (dwordK 42 6 A m f wd) G = true) : g ∈ H := by
  obtain ⟨-, v, hv, hvr⟩ := dwordK_mem hm hA f wd
  rw [Nat.eq_of_beq_eq_true h] at hvr
  rwa [hg.perm_eq hvr]

end CFSG.KC.L34Two

end

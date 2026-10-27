module

public import Certificates.Data.Kernel.M24G.FuseInv
public import Certificates.Data.CFSGNative.AS91.M24Fuse
public import CFSG.Certificates.Kernel.M24G.KzeroSound
import CFSG.Certificates.Kernel.M24G.IdxSound

public section

namespace CFSG.KC.M24G

open CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

theorem fuseInv_mem {L : List Nat} {pos : KTree (Nat × Nat)} (hp : posOK (fun c => c) L pos = true)
    {k : Nat} (h : ∃ i, findK k pos = some i) : k ∈ L := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨hl, e⟩ := (findK_eq_some _ hp k i).1 hi
  have e' : L[i] = k := e
  rw [← e']
  exact List.getElem_mem hl

theorem fuseInvLoop_of {S LA LB : List (Array Nat)} {aL bL : List Nat}
    {pA pB : KTree (Nat × Nat)} (hV : ∀ t ∈ S, DuadV t)
    (hpA : posOK (fun c => c) aL pA = true) (hpB : posOK (fun c => c) bL pB = true)
    (hA : ∀ {t : Array Nat}, DuadV t → (t ∈ LA ↔ Native.kzeroKey t ∈ aL))
    (hB : ∀ {t : Array Nat}, DuadV t → (t ∈ LB ↔ Native.kzeroKey t ∈ bL))
    (h : fuseInvF S pA pB = true) : Native.fuseInvLoop S.toArray LA LB = true := by
  unfold Native.fuseInvLoop
  unfold fuseInvF at h
  rw [List.toList_toArray]
  rw [List.all_eq_true] at h ⊢
  intro t ht
  have hv := hV t ht
  have hid : DuadV Native.kzeroId := duadV_of _ (by decide)
  have h1 := h t ht
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Option.isSome_iff_exists] at h1
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.contains_iff_mem]
  rcases h1 with ((h1 | h1) | h1) | h1
  · refine Or.inl (Or.inl (Or.inl fun e => h1 ?_))
    rw [← kzeroMul_eq, e]
  · exact Or.inl (Or.inl (Or.inr (kzeroKeyF_inj hv hid h1)))
  · refine Or.inl (Or.inr ((hA hv).2 ?_))
    rw [kzeroKey_eq]
    exact fuseInv_mem hpA h1
  · refine Or.inr ((hB hv).2 ?_)
    rw [kzeroKey_eq]
    exact fuseInv_mem hpB h1

end CFSG.KC.M24G

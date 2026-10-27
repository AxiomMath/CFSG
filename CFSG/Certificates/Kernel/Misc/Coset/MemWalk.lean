module

public import CFSG.Certificates.Kernel.Misc.Coset.MemSound
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.Sporadic.Recognition.CoverTransferWords

public section

namespace CFSG.KC.MiscCoset

open CFSG.CosetTable CFSG.Certificates CFSG.Sporadic.Recognition.CoverTransfer

variable {m : ℕ}

theorem mk_eq_one_of_renumber (ws : List (List (Fin m × Bool))) {S : List (Fin m)}
    {w : List (Fin m × Bool)} {u : List (Fin S.length × Bool)} (hren : renumber S w = some u)
    (h1 : PresentedGroup.mk {r | r ∈ (restrictWords S ws).map FreeGroup.mk} (FreeGroup.mk u) = 1) :
    PresentedGroup.mk {r | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk w) = 1 := by
  have hf : FreeGroup.lift (fun i => (PresentedGroup.of i : PG m ws)) =
      PresentedGroup.mk {r | r ∈ ws.map FreeGroup.mk} :=
    FreeGroup.ext_hom _ _ fun i => by rw [FreeGroup.lift_apply_of]; rfl
  have hg : ∀ v ∈ ws, FreeGroup.lift (fun i => (PresentedGroup.of i : PG m ws))
      (FreeGroup.mk v) = 1 := by
    intro v hv
    rw [hf]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem hv)
  have hrel := lift_restrictWords ws S _ hg
  have hψ : (PresentedGroup.toGroup hrel).comp (PresentedGroup.mk _) =
      FreeGroup.lift fun j => (PresentedGroup.of (S.get j) : PG m ws) :=
    FreeGroup.ext_hom _ _ fun j => by
      rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
      exact PresentedGroup.toGroup.of hrel
  have e := DFunLike.congr_fun hψ (FreeGroup.mk u)
  rw [MonoidHom.comp_apply, h1, map_one, lift_mk_map, map_renumber S w u hren, hf] at e
  exact e.symm

theorem mk_eq_one_of_walk (ws : List (List (Fin m × Bool))) {S : List (Fin m)}
    (hm : S.length < 128) {rels : List (List (ℕ × Bool))}
    (hrels : (restrictWords S ws).map encW = rels)
    {inv L eps nLab nT N RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S' : ℕ → ℕ} {amap : ℕ}
    {words : List (List (ℕ × Bool))} {walk cov : List ℕ}
    (h : KB.tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S' amap rels words walk cov =
      true) (htop : KB.topOk amap S.length = true) (hwords : words = [])
    (w : List (Fin m × Bool)) (hs : (renumber S w).isSome = true) {cs refs : List ℕ}
    (hc : (encW ((renumber S w).get hs)).map Mem.codeN = cs) (hw : Mem.memOK F nF cs refs = true) :
    PresentedGroup.mk {r | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk w) = 1 := by
  refine mk_eq_one_of_renumber ws (Option.some_get hs).symm ?_
  have hmem := Mem.memOK_sound (pgGen (restrictWords S ws)) (sword_rels _ hrels) h hm htop
    (u := encW ((renumber S w).get hs)) (by
      intro l hl
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hl
      exact x.1.isLt) (by rw [hc]; exact hw)
  rw [sword_pgGen, hwords, KB.wordSub_nil, Subgroup.mem_bot] at hmem
  exact hmem

end CFSG.KC.MiscCoset

end

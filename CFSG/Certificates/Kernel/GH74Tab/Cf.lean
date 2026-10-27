module

public import Certificates.Data.Kernel.GH74Tab.Cf

public section

namespace CFSG.KC.GH74Tab

open Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

variable {n : ℕ} [NeZero n]

theorem mem_permsOfList_finRange {m : ℕ} (σ : Perm (Fin m)) : σ ∈ permsOfList (List.finRange m) :=
  mem_permsOfList_of_mem fun x _ => List.mem_finRange x

theorem mem_cfF (g : Amb n) :
    g ∈ cfF n ↔ g * vStdE1 n = vStdE1 n * g ∧ g.2 * x4 = x4 * g.2 ∧ sign g.1 = sign g.2 := by
  obtain ⟨σ, d⟩ := g
  simp only [cfF, cfSig, cfD, List.mem_flatMap, List.mem_filter, List.mem_map, decide_eq_true_eq,
    Prod.ext_iff, Prod.fst_mul, Prod.snd_mul]
  constructor
  · rintro ⟨τ, ⟨-, hτ⟩, e, ⟨⟨-, he⟩, hs⟩, rfl, rfl⟩
    exact ⟨⟨hτ, he⟩, he, hs⟩
  · rintro ⟨⟨hσ, -⟩, hd, hs⟩
    exact ⟨σ, ⟨mem_permsOfList_finRange σ, hσ⟩, d, ⟨⟨mem_permsOfList_finRange d, hd⟩, hs⟩, rfl, rfl⟩

theorem nodup_cfF : (cfF n).Nodup := by
  have hp : ∀ m : ℕ, (permsOfList (List.finRange m)).Nodup := fun m =>
    nodup_permsOfList (List.nodup_finRange m)
  refine List.nodup_flatMap.2 ⟨fun σ _ => ((hp 4).filter _).filter _ |>.map ?_, ?_⟩
  · intro d e h
    exact (Prod.ext_iff.1 h).2
  · refine List.Pairwise.imp_of_mem ?_ ((hp n).filter _)
    intro σ τ _ _ hne
    simp only [Function.onFun, List.disjoint_left, List.mem_map]
    rintro g ⟨d, -, rfl⟩ ⟨e, -, he⟩
    exact hne (Prod.ext_iff.1 he).1.symm

theorem cfSetE1_eq : cfSetE1 n = (cfF n).toFinset := by
  ext g
  simp only [cfSetE1, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset, mem_cfF]

theorem card_cfSetE1 : (cfSetE1 n).card = (cfF n).length := by
  rw [cfSetE1_eq, List.toFinset_card_of_nodup nodup_cfF]

theorem cfCoverE1_eq (T : Tab n) : T.cfCoverE1 = cfCovF T (repListE1 n) := by
  unfold Tab.cfCoverE1 cfCovF cfKs
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, mem_cfListE1, mem_cfF]

end CFSG.KC.GH74Tab

end

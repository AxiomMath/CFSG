module

public import CFSG.CGT.PushingUpLit.SYMB.SevenFamily

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement Pointwise

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ} {n : ℕ}
  {φ : ↥G →* Equiv.Perm (Fin n)} {ψ : ↥V →* ↥(G6.coreMod n)} {T' : Set (Equiv.Perm (Fin n))}

theorem blocks_comm_pCore_le (S : SymSetting G T V n φ ψ T') {𝓕 : Set (Subgroup Γ)}
    (hblk : ∀ F ∈ 𝓕, IsBTBlock G T F ∧ ¬ F ≤ cStarIn G T) :
    ⁅(sSup 𝓕 : Subgroup Γ), pCoreOf 2 G⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  exact comm_mem_of_forall_gen S.data.normal (fun F hF => (hblk F hF).1.le)
    (fun F hF f hf q hq => sym_block_comm_pCore_le S (hblk F hF).1 (hblk F hF).2 f hf q hq)

theorem symJoin_of_blocks (S : SymSetting G T V n φ ψ T') {𝓕 : Set (Subgroup Γ)}
    (hblk : ∀ F ∈ 𝓕, IsBTBlock G T F ∧ ¬ F ≤ cStarIn G T)
    (hcov : ∀ (t : Equiv.Perm (Fin n)) (x c : Fin n), SymTriple T' t x c →
      ∃ F ∈ 𝓕, cyc x (t x) c ∈ imgG G φ F) (hne : 𝓕.Nonempty) :
    SymJoin G T V φ ψ (sSup 𝓕) := by
  classical
  have hres : oResidualTwo ↥(sSup 𝓕) = ⊤ :=
    oResidualTwo_sSup_eq_top fun F hF => (hblk F hF).1.residual
  have hle : sSup 𝓕 ≤ G := sSup_le fun F hF => (hblk F hF).1.le
  have hAE : alternatingGroup (Fin n) ≤ imgG G φ (sSup 𝓕) := by
    refine alternatingGroup_le_of_cyc_mem _ S.swaps S.comm S.nonempty
      (exists_fixed_of_swaps S.odd S.swaps S.comm) ?_
    intro t ht x hx c hcf
    obtain ⟨F, hF, hcyc⟩ := hcov t x c (⟨ht, hx, hcf⟩ : SymTriple T' t x c)
    exact imgG_mono G φ (le_sSup hF) hcyc
  refine ⟨hle, hres, commutator_sSup_eq fun F hF => (hblk F hF).1.commutator, ?_,
    sym_nonCentral_of_alt S hAE, ?_⟩
  · refine le_antisymm ?_ hAE
    intro σ hσ
    obtain ⟨e, he, heE, rfl⟩ := mem_imgG.1 hσ
    exact map_mem_alternating_of_oResidualTwo hres hle heE
  · obtain ⟨F, hF⟩ := hne
    obtain ⟨k, hk, hψ⟩ := sym_block_ker_psi S (hblk F hF).1 (hblk F hF).2
    exact ⟨k, ⟨le_sSup hF hk.1, hk.2⟩, hψ⟩

end CFSG.CGT.PushingUpLit.SYMB

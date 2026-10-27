module

public import CFSG.CGT.PushingUpLit.SYMB.SevenPairs
public import CFSG.CGT.PushingUpLit.SYMB.KernelTwo
public import CFSG.CGT.PushingUpLit.SYMB.JoinBlock
public import CFSG.CGT.PushingUpLit.SYMB.BlockFacts
public import CFSG.CGT.PushingUpLit.SYMB.BlockOmega
public import CFSG.CGT.PushingUpLit.SYMB.Final
public import CFSG.CGT.PushingUpLit.SYMB.SymMaxSwap

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement Pointwise

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}

@[expose] def altBlocks {n : ℕ} (G T : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n)) :
    Set (Subgroup Γ) :=
  {F | IsBTBlock G T F ∧ ¬ F ≤ cStarIn G T ∧
    ∃ Ω : Finset (Fin n), 5 ≤ Ω.card ∧ imgG G φ F = altOn Ω}

section Cover

variable {m : ℕ} {φ : ↥G →* Equiv.Perm (Fin (2 * m + 1))}
  {ψ : ↥V →* ↥(G6.coreMod (2 * m + 1))} {T' : Set (Equiv.Perm (Fin (2 * m + 1)))}

theorem exists_altBlock_cyc (S : SymSetting G T V (2 * m + 1) φ ψ T') (hm : 3 ≤ m)
    (hih : IHFor G) {t : Equiv.Perm (Fin (2 * m + 1))} {x c : Fin (2 * m + 1)}
    (h : SymTriple T' t x c) : ∃ F ∈ altBlocks G T φ, cyc x (t x) c ∈ imgG G φ F := by
  classical
  obtain ⟨t₂, ht₂, hne⟩ : ∃ t₂ ∈ T', t₂ ≠ t := by
    have hcard : T'.ncard = m := symSetting_ncard (by omega) S
    have h1 : 1 < T'.ncard := by omega
    obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff (Set.toFinite T')).1 h1
    by_cases hat : a = t
    · exact ⟨b, hb, fun hbt => hab (hat.trans hbt.symm)⟩
    · exact ⟨a, ha, hat⟩
  have hcard5 : (Ωs t t₂ c).card = 5 :=
    card_Ωs S.swaps S.comm h.mem ht₂ (Ne.symm hne) h.fixed
  have hxs : x ∈ t.support := Equiv.Perm.mem_support.2 h.moves
  have hxΩ : x ∈ Ωs t t₂ c := by simp [Ωs, hxs]
  have htxΩ : t x ∈ Ωs t t₂ c := by
    have : t x ∈ t.support := Equiv.Perm.apply_mem_support.2 hxs
    simp [Ωs, this]
  have hcΩ : c ∈ Ωs t t₂ c := by simp [Ωs]
  obtain ⟨F, hF, hFn, hFΩ⟩ := exists_block_altOn S hih (by omega) (by omega)
    (stab_Ωs S.swaps S.comm h.mem ht₂ h.fixed) h.mem h.moves h.fixed hxΩ htxΩ hcΩ
  refine ⟨F, ⟨hF, hFn, Ωs t t₂ c, by omega, hFΩ⟩, ?_⟩
  have hxc : x ≠ c := fun h' => h.moves (h' ▸ h.fixed t h.mem)
  have htc : t x ≠ c := fun h' => by
    have hxc' : x = c := t.injective (h'.trans (h.fixed t h.mem).symm)
    exact h.moves (h'.trans hxc'.symm)
  rw [hFΩ]
  exact cyc_mem_altOn hxΩ htxΩ hcΩ h.moves.symm hxc htc

theorem alt_le_img_altBlocks (S : SymSetting G T V (2 * m + 1) φ ψ T') (hm : 3 ≤ m)
    (hih : IHFor G) :
    alternatingGroup (Fin (2 * m + 1)) ≤ imgG G φ (sSup (altBlocks G T φ)) := by
  refine alternatingGroup_le_of_cyc_mem _ S.swaps S.comm S.nonempty
    (exists_fixed_of_swaps S.odd S.swaps S.comm) ?_
  intro t ht x hx c hcf
  obtain ⟨F, hF, hcyc⟩ := exists_altBlock_cyc S hm hih (⟨ht, hx, hcf⟩ : SymTriple T' t x c)
  exact imgG_mono G φ (le_sSup hF) hcyc

theorem altBlocks_nonempty (S : SymSetting G T V (2 * m + 1) φ ψ T') (hm : 3 ≤ m)
    (hih : IHFor G) : (altBlocks G T φ).Nonempty := by
  obtain ⟨t, ht⟩ := S.nonempty
  obtain ⟨c, hc⟩ := exists_fixed_of_swaps S.odd S.swaps S.comm
  obtain ⟨a, a', haa, hta⟩ := S.swaps t ht
  have hmov : t a ≠ a := by
    rw [hta, Equiv.swap_apply_left]
    exact haa.symm
  obtain ⟨F, hF, -⟩ := exists_altBlock_cyc S hm hih (⟨ht, hmov, hc⟩ : SymTriple T' t a c)
  exact ⟨F, hF⟩

end Cover

variable {n : ℕ} {φ : ↥G →* Equiv.Perm (Fin n)} {ψ : ↥V →* ↥(G6.coreMod n)}
  {T' : Set (Equiv.Perm (Fin n))}

omit [Finite Γ] in
theorem sym_nonCentral_of_alt (S : SymSetting G T V n φ ψ T') {E : Subgroup Γ}
    (hAE : alternatingGroup (Fin n) ≤ imgG G φ E) : ⁅E, omegaOneCenterOf T⁆ ≠ ⊥ := by
  intro hbot
  have hEC : E ≤ Subgroup.centralizer (omegaOneCenterOf T : Set Γ) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
  have hBC : baum T ≤ Subgroup.centralizer (omegaOneCenterOf T : Set Γ) :=
    (inf_le_left : baum T ≤ T).trans (SymCover.le_centralizer_omegaOneCenterOf T)
  have hCC : G ⊓ Subgroup.centralizer (V : Set Γ) ≤
      Subgroup.centralizer (omegaOneCenterOf T : Set Γ) :=
    inf_le_right.trans (Subgroup.centralizer_le S.vT)
  apply S.ne
  refine le_antisymm (cStarIn_le G T) fun g hg => ?_
  exact centralizer_le_cStarIn G T ⟨hg, sup_le (sup_le hBC hEC) hCC (sym_le_sup_of_alt S hAE hg)⟩

omit [Finite Γ] in
theorem sym_mem_kerG (S : SymSetting G T V n φ ψ T') {g : Γ} (hg : g ∈ G)
    (hc : g ∈ Subgroup.centralizer (V : Set Γ)) : g ∈ kerG G φ := by
  refine mem_kerG.2 ⟨hg, ?_⟩
  have h : (⟨g, hg⟩ : ↥G) ∈ φ.ker := by
    rw [S.data.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨hg, hc⟩
  exact h

theorem altBlocks_comm_pCore_le (S : SymSetting G T V n φ ψ T') :
    ⁅(sSup (altBlocks G T φ) : Subgroup Γ), pCoreOf 2 G⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  exact comm_mem_of_forall_gen S.data.normal (fun F hF => hF.1.le)
    (fun F hF f hf q hq => sym_block_comm_pCore_le S hF.1 hF.2.1 f hf q hq)

section Join

variable {m : ℕ} {φ : ↥G →* Equiv.Perm (Fin (2 * m + 1))}
  {ψ : ↥V →* ↥(G6.coreMod (2 * m + 1))} {T' : Set (Equiv.Perm (Fin (2 * m + 1)))}

theorem symJoin_altBlocks (S : SymSetting G T V (2 * m + 1) φ ψ T') (hm : 3 ≤ m)
    (hih : IHFor G) : SymJoin G T V φ ψ (sSup (altBlocks G T φ)) := by
  classical
  have hres : oResidualTwo ↥(sSup (altBlocks G T φ)) = ⊤ :=
    oResidualTwo_sSup_eq_top fun F hF => hF.1.residual
  have hle : sSup (altBlocks G T φ) ≤ G := sSup_le fun F hF => hF.1.le
  have hAE := alt_le_img_altBlocks S hm hih
  refine ⟨hle, hres, commutator_sSup_eq fun F hF => hF.1.commutator, ?_,
    sym_nonCentral_of_alt S hAE, ?_⟩
  · refine le_antisymm ?_ hAE
    intro σ hσ
    obtain ⟨e, he, heE, rfl⟩ := mem_imgG.1 hσ
    exact map_mem_alternating_of_oResidualTwo hres hle heE
  · obtain ⟨F, hF⟩ := altBlocks_nonempty S hm hih
    obtain ⟨k, hk, hψ⟩ := sym_block_ker_psi S hF.1 hF.2.1
    exact ⟨k, ⟨le_sSup hF hk.1, hk.2⟩, hψ⟩

end Join

end CFSG.CGT.PushingUpLit.SYMB

module

public import CFSG.CGT.PushingUpLit.BHS6.SymOffender
public import CFSG.CGT.PushingUpLit.SYMB.CaseOne
public import CFSG.CGT.PushingUpLit.SYMB.Final

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}

theorem exists_symSetting {m : ℕ} (hm : 2 ≤ m) (hchar : CharTwo G) (hsylow : IsSylowOf 2 T G)
    (hne : cStarIn G T ≠ G) (hVn : G ≤ Subgroup.normalizer (V : Set Γ))
    (hVT : omegaOneCenterOf T ≤ V) (hVQ : V ≤ omegaOneCenterOf (pCoreOf 2 G))
    (hnat : IsNatSym G V (2 * m + 1)) :
    ∃ (φ : ↥G →* Equiv.Perm (Fin (2 * m + 1))) (ψ : ↥V →* ↥(G6.coreMod (2 * m + 1)))
      (T' : Set (Equiv.Perm (Fin (2 * m + 1)))), SymSetting G T V (2 * m + 1) φ ψ T' := by
  have hT : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hsylow
  have hT0 : T ≠ ⊥ := by
    rintro rfl
    apply hne
    refine le_antisymm (cStarIn_le G ⊥) fun g hg => ?_
    have hΩ : omegaOneCenterOf (⊥ : Subgroup Γ) = ⊥ := by
      refine le_bot_iff.mp ((Subgroup.closure_le _).mpr fun x hx => ?_)
      exact hx.1.1
    refine centralizer_le_cStarIn G ⊥ ⟨hg, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    have h1 : h = 1 := Subgroup.mem_bot.mp (hΩ ▸ hh)
    simp [h1]
  have hC : G ⊓ Subgroup.centralizer (V : Set Γ) ≤ cStarIn G T :=
    (inf_le_inf_left G (Subgroup.centralizer_le fun x hx => hVT hx)).trans
      (centralizer_le_cStarIn G T)
  have hOT : pCoreOf 2 G ≤ T := hT.pCoreOf_le
  have hVQ' : V ≤ pCoreOf 2 G := hVQ.trans (C1GN.omegaOneCenterOf_le_self _)
  have hVT' : V ≤ T := hVQ'.trans hOT
  have hVe : IsElemAbelian 2 V := isElemAbelian_of_le' hVQ (isElemAbelian_omegaOneCenterOf' _)
  have hbaum : ¬ baum T ≤ Subgroup.centralizer (V : Set Γ) :=
    baum_not_le_centralizer hT hT0 hVn hC hne
  have hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ) :=
    thompsonJ_not_le_centralizer hVT' hVe hbaum
  obtain ⟨φ, ψ, hφs, hφk, hψs, hψk, hψe, T', hne', hs, hc, hbm⟩ :=
    sym_swap_data hm hT hVn hVQ hJ hnat
  exact ⟨φ, ψ, T', ⟨⟨hVn, hVe, hφs, hφk, hψs, hψk, hψe⟩, ⟨m, rfl⟩, hchar, hT, hne, hVQ, hVT,
    hne', hs, hc, hbm⟩⟩

@[expose] def SymCaseTwoAt (P : ℕ → Prop) : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (G T V : Subgroup Γ) (m : ℕ), P m →
    ∀ (φ : ↥G →* Equiv.Perm (Fin (2 * m + 1))) (ψ : ↥V →* ↥(G6.coreMod (2 * m + 1)))
      (T' : Set (Equiv.Perm (Fin (2 * m + 1)))),
      SymSetting G T V (2 * m + 1) φ ψ T' → IHFor G → (∀ L ∈ lSet G T, imgG G φ L ≠ ⊤) →
        ∃ F : Subgroup Γ, IsBTBlock G T F ∧
          imgG G φ F = alternatingGroup (Fin (2 * m + 1))

@[expose] def SymCaseTwo : Prop := SymCaseTwoAt fun m => 2 ≤ m

theorem symCaseTwo_of_five_seven (h5 : SymCaseTwoAt fun m => m = 2)
    (h7 : SymCaseTwoAt fun m => 3 ≤ m) : SymCaseTwo := by
  intro Γ _ _ G T V m hm φ ψ T' S hih hno
  rcases Nat.lt_or_ge m 3 with h | h
  · exact h5 Γ G T V m (by omega) φ ψ T' S hih hno
  · exact h7 Γ G T V m h φ ψ T' S hih hno

theorem threeEightSymmIH_of_caseTwo (h : SymCaseTwo) : ThreeEightSymmIH := by
  intro Γ _ _ G T V m hm hchar hsylow hne hVn hVT hVQ hnat hih
  obtain ⟨φ, ψ, T', S⟩ := exists_symSetting hm hchar hsylow hne hVn hVT hVQ hnat
  have h4 : 4 ≤ 2 * m + 1 := by omega
  by_cases hcase : ∃ L ∈ lSet G T, imgG G φ L = ⊤
  · obtain ⟨L, hL, hLtop⟩ := hcase
    obtain ⟨F, hF, hFn, -, hFφ⟩ := exists_block_alt_of_imgG_eq_top hm S hih hL hLtop
    exact ⟨F, hF, sym_conclusion_of_block S h4 hF hFn hFφ⟩
  · push Not at hcase
    obtain ⟨F, hF, hFφ⟩ := h Γ G T V m hm φ ψ T' S hih hcase
    have hFn : ¬ F ≤ cStarIn G T := fun hFC => sym_not_alt_le_imgG S hFC hFφ.ge
    exact ⟨F, hF, sym_conclusion_of_block S h4 hF hFn hFφ⟩

end CFSG.CGT.PushingUpLit.SYMB

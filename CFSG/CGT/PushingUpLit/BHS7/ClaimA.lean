module

public import CFSG.CGT.PushingUpLit.BHS7.SevenThree
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem isSubnormal_of_le_of_le_normalizer {M L : Subgroup Γ} (hML : M ≤ L)
    (hN : L ≤ Subgroup.normalizer (M : Set Γ)) : IsSubnormal M L :=
  CFSG.Quasithin.A3.subnormal_of_normal hML
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hML).mpr hN)

theorem isSubnormal_of_mem_concl {L S : Subgroup Γ} {𝒢 : Set (Subgroup Γ)}
    (hbl : ∀ E ∈ 𝒢, IsBTBlock L S E) (hinv : ∀ E ∈ 𝒢, ∀ g ∈ L, A1b.conjSub g E ∈ 𝒢)
    (hcomm : ∀ E ∈ 𝒢, ∀ E' ∈ 𝒢, E ≠ E' → ∀ x ∈ E, ∀ y ∈ E', x * y = y * x)
    {E : Subgroup Γ} (hE : E ∈ 𝒢) : IsSubnormal E L := by
  set M : Subgroup Γ := ⨆ E' ∈ 𝒢, E' with hM
  have hEM : E ≤ M := le_iSup₂_of_le (f := fun (E' : Subgroup Γ) (_ : E' ∈ 𝒢) => E') E hE le_rfl
  have hML : M ≤ L := iSup₂_le fun E' hE' => (hbl E' hE').le
  have hMn : M ≤ Subgroup.normalizer (E : Set Γ) := by
    refine iSup₂_le fun E' hE' => ?_
    by_cases hEE : E' = E
    · subst hEE
      exact Subgroup.le_normalizer
    · have : E' ≤ Subgroup.centralizer (E : Set Γ) := fun x hx =>
        Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm E' hE' E hE hEE x hx y hy).symm
      exact this.trans (Subgroup.centralizer_le_normalizer _)
  have hkey : ∀ g ∈ L, A1b.conjSub g M ≤ M := by
    intro g hg
    rw [hM, conjSub_iSup]
    refine iSup_le fun E' => ?_
    rw [conjSub_iSup]
    refine iSup_le fun hE' => ?_
    exact le_iSup₂_of_le (f := fun (E'' : Subgroup Γ) (_ : E'' ∈ 𝒢) => E'') (A1b.conjSub g E')
      (hinv E' hE' g hg) le_rfl
  have hLn : L ≤ Subgroup.normalizer (M : Set Γ) := fun g hg =>
    mem_normalizer_of_conjSub_le (hkey g hg) (hkey g⁻¹ (L.inv_mem hg))
  exact CFSG.Quasithin.A3.subnormal_trans (isSubnormal_of_le_of_le_normalizer hEM hMn)
    (isSubnormal_of_le_of_le_normalizer hML hLn)

theorem exists_subnormal_block_ge {L S F : Subgroup Γ} (h : LocalCStarConcl L S)
    (hF : IsBTBlock L S F) (hFC : ¬ F ≤ cStarIn L S) :
    ∃ E : Subgroup Γ, IsBTBlock L S E ∧ F ≤ E ∧ IsSubnormal E L := by
  obtain ⟨𝒢, hbl, hinv, hcomm, -, hd, -, -⟩ := h
  obtain ⟨E, hE, hFE⟩ := hd F hF hFC
  exact ⟨E, hbl E hE, hFE, isSubnormal_of_mem_concl hbl hinv hcomm hE⟩

variable [Finite Γ]

theorem isBTBlock_of_super {G L S T E : Subgroup Γ} (hT : IsSylowTwoOf T G)
    (hE : IsBTBlock G T E) (hLG : L ≤ G) (hEL : E ≤ L) (hS : IsSylowTwoOf S L)
    (hBS : baum T ≤ S) (hn : ¬ E ≤ cStarIn G T) : IsBTBlock L S E := by
  have hb : baum S = baum T := baum_eq_of_isPGroup_of_baum_le hT hS.2.1 (hS.1.trans hLG) hBS
  have hb0 : baum T ≠ ⊥ := by
    intro h0
    apply hn
    rw [cStarIn_eq_of_baum_eq_bot h0]
    exact hE.le
  exact
    { le := hEL
      residual := hE.residual
      commutator := by rw [hb]; exact hE.commutator
      perfect := hE.perfect
      elemAbelian := hE.elemAbelian
      nonCentral := by
        intro h0
        apply hn
        have h1 : E ≤ L ⊓ Subgroup.centralizer (omegaOneCenterOf S : Set Γ) := by
          refine le_inf hEL fun e he => ?_
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          have h2 : ⁅e, z⁆ ∈ (⁅E, omegaOneCenterOf S⁆ : Subgroup Γ) :=
            Subgroup.commutator_mem_commutator he hz
          rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
          exact h2.symm
        exact h1.trans ((centralizer_le_cStarIn L S).trans (two_three_d hT hb0 hLG hS hBS))
      type := hE.type }

theorem claim_A {G T : Subgroup Γ} (h : MinCex G T) {E : Subgroup Γ} (hE : E ∈ bStarT G T)
    {L : Subgroup Γ} (hLG : L < G) (hBL : baum T ≤ L) (hEL : E ≤ L) : IsSubnormal E L := by
  have hT : IsSylowTwoOf T G := h.sylow
  have hEb : IsBTBlock G T E := hE.1.2
  have hEn : ¬ E ≤ cStarIn G T := hE.2
  have hLC : ¬ L ≤ cStarIn G T := fun hl => hEn (hEL.trans hl)
  have hb0 : baum T ≠ ⊥ := fun h0 => h.ne (cStarIn_eq_of_baum_eq_bot h0)
  obtain ⟨S, hS, hBS⟩ := B6.exists_isSylowTwoOf_ge (hT.2.1.to_le inf_le_left) hBL
  obtain ⟨-, -, hconcl⟩ := seven_three h hT ⟨hLG, hBL, hLC⟩ hS
  have hEL' : IsBTBlock L S E := isBTBlock_of_super hT hEb hLG.le hEL hS hBS hEn
  have hn' : ¬ E ≤ cStarIn L S := fun hc => hEn (hc.trans (two_three_d hT hb0 hLG.le hS hBS))
  obtain ⟨E', hE'b, hEE', hsub⟩ := exists_subnormal_block_ge hconcl hEL' hn'
  have hSX : baum S = baum T := baum_eq_of_isPGroup_of_baum_le hT hS.2.1 (hS.1.trans hLG.le) hBS
  have hE'G : IsBTBlock G T E' :=
    isBTBlock_of_sub hE'b hLG.le hSX (fun hc => hEn (hEE'.trans hc))
  have heq : E' = E := hE.1.1.2 E' (mem_btBlocksG_of_isBTBlock hE'G) hEE'
  rwa [heq] at hsub

end CFSG.CGT.PushingUpLit.BHS7

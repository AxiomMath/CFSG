module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapChainModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.SymplecticPilot (nsTorusSp complSp)
open CFSG.LieType.Ree (ReeTag)

theorem eq_of_card_three_of_card_six {M : Type*} [Group M] {J A B : Subgroup M}
    (hJ : Nat.card J = 6) (hAJ : A ≤ J) (hBJ : B ≤ J) (hA : Nat.card A = 3)
    (hB : Nat.card B = 3) : A = B := by
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [hJ]; norm_num)
  set A' := A.subgroupOf J with hA'
  set B' := B.subgroupOf J with hB'
  have hcA : Nat.card A' = 3 := by
    rw [hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAJ).toEquiv, hA]
  have hcB : Nat.card B' = 3 := by
    rw [hB', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBJ).toEquiv, hB]
  have hidx : A'.index = 2 := by
    have h := Subgroup.card_mul_index A'
    rw [hcA, hJ] at h
    omega
  have : A'.Normal := Subgroup.normal_of_index_eq_two hidx
  have hle : B' ≤ A' := by
    by_contra hBA
    have hdisj : B' ⊓ A' = ⊥ := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hdvd : Nat.card (B' ⊓ A' : Subgroup J) ∣ 3 := hcB ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        apply hBA
        have heq : B' ⊓ A' = B' := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hcB])
        rw [← heq]
        exact inf_le_right
    have h1 := card_map_mk'_of_inf_eq_bot A' hdisj
    have h2 : Nat.card (B'.map (QuotientGroup.mk' A')) ∣ Nat.card (J ⧸ A') :=
      Subgroup.card_subgroup_dvd_card _
    rw [h1, hcB, ← Subgroup.index_eq_card, hidx] at h2
    omega
  have heq : B' = A' := Subgroup.eq_of_le_of_card_ge hle (by rw [hcA, hcB])
  have := congrArg (fun H : Subgroup J => H.map J.subtype) heq
  simp only [hA', hB', Subgroup.subgroupOf_map_subtype, inf_of_le_left hAJ,
    inf_of_le_left hBJ] at this
  exact this.symm

section RootSL2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_SL2_of_card_two (hK : Nat.card K = 2) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 6 := by
  classical
  have := Fintype.ofFinite K
  have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [Matrix.card_SL_field, Fin.prod_univ_two, hq]
  norm_num

theorem card_rootSL2 (hK : Nat.card K = 2) {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    Nat.card (rootSL2 K γ) = 6 := by
  obtain ⟨-, -, ⟨e, -⟩, -⟩ := CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps .F4 K hγ
  have hle : rootSubgroup .F4 K γ ⊔ rootSubgroup .F4 K (-γ) ≤ adjointGroup .F4 K :=
    sup_le (rootSubgroup_le_adjointGroup γ) (rootSubgroup_le_adjointGroup (-γ))
  rw [rootSL2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    ← Nat.card_congr e.toEquiv]
  exact card_SL2_of_card_two hK

theorem eq_of_le_rootSL2 (hK : Nat.card K = 2) {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    {A B : Subgroup (adjointGroup .F4 K)} (hA : A ≤ rootSL2 K γ) (hB : B ≤ rootSL2 K γ)
    (hA3 : Nat.card A = 3) (hB3 : Nat.card B = 3) : A = B :=
  eq_of_card_three_of_card_six (card_rootSL2 hK hγ) hA hB hA3 hB3

theorem map_graphAutF4_rootSL2 [CharP K ReeTag.F4.prime] {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : IsRoot .F4 γ) :
    (rootSL2 K γ).map (graphAutF4 K).toMonoidHom = rootSL2 K (psiF4 γ) := by
  rw [rootSL2_eq_sup hγ, Subgroup.map_sup, map_graphAutF4_rootGroup hγ,
    map_graphAutF4_rootGroup (IsRoot.neg hγ), psiF4_neg hγ, rootSL2_eq_sup (isRoot_psiF4 hγ)]

theorem zThreeSL_eq_sl2Upper_mul_sl2Lower :
    (SymplecticPilot.zThreeSL : Matrix.SpecialLinearGroup (Fin 2) K) =
      CFSG.LieType.Steinberg.sl2Upper 1 * CFSG.LieType.Steinberg.sl2Lower 1 := by
  refine Subtype.ext ?_
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hneg : (-1 : K) = 1 := CharTwo.neg_eq 1
  rw [Matrix.SpecialLinearGroup.coe_mul]
  change SymplecticPilot.zThreeMat = !![(1 : K), 1; 0, 1] * !![(1 : K), 0; 1, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SymplecticPilot.zThreeMat, Matrix.mul_apply, Fin.sum_univ_two, h2, hneg]

theorem stdX_le_rootSL2 : stdX K ≤ rootSL2 K root0122 := by
  have hv : CFSG.Timmesfeld.LieEmbed.c3ToF4 ![2, 2, 1] = root0122 := by decide
  have hv' : CFSG.Timmesfeld.LieEmbed.c3ToF4 (-![2, 2, 1]) = -root0122 := by
    rw [map_neg, hv]
  have hu : CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock K 3 0
      (CFSG.LieType.Steinberg.sl2Upper 1) = Sp.x 3 K ![2, 2, 1] 1 := by
    rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock_sl2Upper]
    exact (Sp.x_eq (by decide) 1).symm
  have hl : CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock K 3 0
      (CFSG.LieType.Steinberg.sl2Lower 1) = Sp.x 3 K (-![2, 2, 1]) 1 := by
    rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock_sl2Lower]
    exact (Sp.x_eq (by decide) 1).symm
  rw [stdX, Subgroup.map_le_iff_le_comap, SymplecticPilot.nsTorusSp, zpowers_le, mem_comap,
    SymplecticPilot.nsElt, zThreeSL_eq_sl2Upper_mul_sl2Lower, map_mul, hu, hl, map_mul,
    c3LeviHom_x, c3LeviHom_x, hv, hv', rootSL2_eq_sup isRoot_root0122]
  exact mul_mem (mem_sup_left (Adjoint.xPar_mem isRoot_root0122 1))
    (mem_sup_right (Adjoint.xPar_mem (IsRoot.neg isRoot_root0122) 1))

theorem card_stdX : Nat.card (stdX K) = 3 := by
  rw [stdX, Subgroup.card_map_of_injective c3LeviHom_injective, SymplecticPilot.card_nsTorusSp]

theorem stdB_eq_B2Levi : stdB K = B2Levi K := by
  have key : ∀ (f g : Fin 2 → Fin 3) (hf : Function.Injective f) (hg : Function.Injective g),
      f = g → (CFSG.ClassicalInvolution.Models.SymplecticPairs.spEmbed (K := K) f hf).range =
        (CFSG.ClassicalInvolution.Models.SymplecticPairs.spEmbed (K := K) g hg).range := by
    intro f g hf hg h
    subst h
    rfl
  rw [stdB, SymplecticPilot.complSp_eq_range_spEmbed, key _ _ _ (Fin.succ_injective 2)
    Fin.succAbove_zero, ← range_b2LeviHom, b2LeviHom, MonoidHom.range_comp]

end RootSL2

section Words

@[expose] def wordAct : List ℕ → (Fin (Tag.rank .F4) → ℤ) → (Fin (Tag.rank .F4) → ℤ)
  | [], v => v
  | i :: ω, v => wordAct ω (reflect .F4 (Tag.F4.idx i) v)

@[expose] noncomputable def wordW : List ℕ → WeylGroup .F4
  | [] => 1
  | i :: ω => wordW ω * simple .F4 (Tag.F4.idx i)

theorem wordW_smul_eq_wordAct (ω : List ℕ) (v : Fin (Tag.rank .F4) → ℤ) :
    wordW ω • v = wordAct ω v := by
  induction ω generalizing v with
  | nil => rw [wordW, one_smul, wordAct]
  | cons i ω ih => rw [wordW, mul_smul, simple_smul, ih, wordAct]

theorem wordAct_neg (ω : List ℕ) (v : Fin (Tag.rank .F4) → ℤ) :
    wordAct ω (-v) = -wordAct ω v := by
  rw [← wordW_smul_eq_wordAct, smul_neg, wordW_smul_eq_wordAct]

end Words

section WeylMaps

variable (K : Type) [Field K]

@[expose] noncomputable def wRep (ω : List ℕ) : adjointGroup .F4 K :=
  weylRepC K (wordW ω)

variable {K}

theorem map_wRep_rootSL2 (ω : List ℕ) {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    (rootSL2 K γ).map (MulAut.conj (wRep K ω)).toMonoidHom = rootSL2 K (wordAct ω γ) := by
  rw [wRep, map_conj_weylRepC_rootSL2 _ hγ, wordW_smul_eq_wordAct]

theorem map_wRep_rootGroup (ω : List ℕ) {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    ((Adjoint.f4Datum K).rootGroup γ).map (MulAut.conj (wRep K ω)).toMonoidHom =
      (Adjoint.f4Datum K).rootGroup (wordAct ω γ) := by
  rw [wRep, map_conj_weylRepC_rootGroup _ hγ, wordW_smul_eq_wordAct]

theorem rootGroup_le_B2Levi {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ b2LeviRoots) :
    (Adjoint.f4Datum K).rootGroup γ ≤ B2Levi K := by
  rw [B2Levi_eq_iSup_rootGroup]
  exact le_iSup₂_of_le (f := fun δ (_ : δ ∈ b2LeviRoots) => (Adjoint.f4Datum K).rootGroup δ) γ hγ
    le_rfl

theorem rootSL2_le_B2Levi {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ b2LeviRoots)
    (hγ' : -γ ∈ b2LeviRoots) : rootSL2 K γ ≤ B2Levi K := by
  rw [rootSL2_eq_sup (mem_b2LeviRoots.1 hγ).1]
  exact sup_le (rootGroup_le_B2Levi hγ) (rootGroup_le_B2Levi hγ')

theorem rootGroups_le_map_wRep_B2Levi (ω : List ℕ) {α β : Fin (Tag.rank .F4) → ℤ}
    (hβ : β ∈ b2LeviRoots) (hβ' : -β ∈ b2LeviRoots) (hαβ : wordAct ω β = α) :
    (Adjoint.f4Datum K).rootGroup α ⊔ (Adjoint.f4Datum K).rootGroup (-α) ≤
      (B2Levi K).map (MulAut.conj (wRep K ω)).toMonoidHom := by
  have hr : IsRoot .F4 β := (mem_b2LeviRoots.1 hβ).1
  have hr' : IsRoot .F4 (-β) := (mem_b2LeviRoots.1 hβ').1
  have e1 : (Adjoint.f4Datum K).rootGroup α =
      ((Adjoint.f4Datum K).rootGroup β).map (MulAut.conj (wRep K ω)).toMonoidHom := by
    rw [map_wRep_rootGroup ω hr, hαβ]
  have e2 : (Adjoint.f4Datum K).rootGroup (-α) =
      ((Adjoint.f4Datum K).rootGroup (-β)).map (MulAut.conj (wRep K ω)).toMonoidHom := by
    rw [map_wRep_rootGroup ω hr', wordAct_neg, hαβ]
  rw [e1, e2, ← Subgroup.map_sup]
  exact Subgroup.map_mono (sup_le (rootGroup_le_B2Levi hβ) (rootGroup_le_B2Levi hβ'))

end WeylMaps

end CFSG.SeitzReduction.F4Pilot

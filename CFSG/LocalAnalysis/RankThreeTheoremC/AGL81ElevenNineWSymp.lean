module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWAbstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveSymp
public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.SpTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.SymplecticTwo
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveTower

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher (flagStabilizer)
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
open CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus (IsWBlock IsSpTwoLeviProduct)
open scoped commutatorElement

section SpTwo

theorem mem_of_odd_orderOf_of_index_two {G : Type*} [Group G] {H : Subgroup G} (h : H.index = 2)
    {x : G} (hx : Odd (orderOf x)) : x ∈ H := by
  obtain ⟨c, hc⟩ := hx
  have hx1 : x = (x ^ 2) ^ (c + 1) := by
    rw [← pow_mul, show 2 * (c + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [hx1]
  exact Subgroup.pow_mem _ (Subgroup.sq_mem_of_index_two h x) _

variable {k : ℕ} {X : Fin k → Type} [∀ i, Group (X i)] [∀ i, Finite (X i)]

theorem mem_spTwoProduct_of_odd {x : ∀ i, X i} (hx : Odd (orderOf x)) :
    x ∈ ParabCensus.spTwoProduct (X := X) := by
  classical
  rw [ParabCensus.spTwoProduct, Subgroup.mem_pi]
  intro i _
  have hxi : Odd (orderOf (x i)) := hx.of_dvd_nat (orderOf_map_dvd (Pi.evalMonoidHom X i) x)
  by_cases h6 : Nonempty (X i ≃* Equiv.Perm (Fin 6))
  · rw [ParabCensus.spTwoLev_eq_map_alt h6]
    refine ⟨Classical.choice h6 (x i),
      mem_of_odd_orderOf_of_index_two alternatingGroup.index_eq_two ?_, ?_⟩
    · rw [MulEquiv.orderOf_eq]
      exact hxi
    · simp
  · rw [ParabCensus.spTwoLev_eq_top h6]
    exact Subgroup.mem_top _

variable {R : Type} [Group R] [Finite R]

theorem mem_wSup_of_odd_of_spTwo (h : IsSpTwoLeviProduct R) {x : R ⧸ CFSG.pCore 2 R}
    (hx : Odd (orderOf x)) : x ∈ wSup (R ⧸ CFSG.pCore 2 R) := by
  obtain ⟨k, X, hgrp, hfin, ⟨e⟩, hX⟩ := h
  letI := hgrp
  letI := hfin
  have h1 : e x ∈ wSup (∀ i, X i) := ParabCensus.spTwoProduct_le_wSup hX
    (mem_spTwoProduct_of_odd (by rw [MulEquiv.orderOf_eq]; exact hx))
  rw [← map_wSup_eq e] at h1
  obtain ⟨y, hy, hyx⟩ := h1
  rwa [e.injective hyx] at hy

theorem leviInnAtPW_of_spTwo {p : ℕ} [OddPrime p] {Y : Type} [Group Y] [Finite Y]
    {P : Subgroup Y} (h : IsSpTwoLeviProduct ↥P) : LeviInnAtPW p P := by
  intro l hl k hcomm
  set l' : ↥P := ⟨l, hl⟩
  have hc : QuotientGroup.mk' (CFSG.pCore 2 ↥P) l' ^ (p ^ k) ∈
      Subgroup.centralizer (wSup (↥P ⧸ CFSG.pCore 2 ↥P) : Set (↥P ⧸ CFSG.pCore 2 ↥P)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥P) w
    have hw' : (w' : Y) ∈ wPre P := ⟨w', hw, rfl⟩
    have h1 := commutatorElement_eq_one_iff_mul_comm.1 (hcomm _ hw')
    rw [← map_pow, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using h1.symm)
  rw [ParabCensus.IsSpTwoLeviProduct.centralizer_wSup_eq_bot h, Subgroup.mem_bot] at hc
  have hodd : Odd (orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥P) l')) :=
    (OddPrime.odd_pow p k).of_dvd_nat (orderOf_dvd_of_pow_eq_one hc)
  have hW : QuotientGroup.mk' (CFSG.pCore 2 ↥P) l'⁻¹ ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P) := by
    rw [map_inv]
    exact inv_mem (mem_wSup_of_odd_of_spTwo h hodd)
  refine ⟨l⁻¹, ⟨l'⁻¹, hW, rfl⟩, fun w _ => ?_⟩
  rw [mul_inv_cancel, commutatorElement_one_left]
  exact Subgroup.one_mem _

end SpTwo

section Big

variable {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {I : Set ℕ}

theorem commutator_statedSp_eq_top_big (hK4 : 4 ≤ Nat.card K) (m : ℕ) :
    commutator (StatedSp m K) = ⊤ := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · haveI : Subsingleton (StatedSp m K) := by rw [hm]; infer_instance
    refine eq_top_iff.mpr fun x _ => ?_
    rw [Subsingleton.elim x 1]
    exact one_mem _
  · exact (spFlag_isQuasisimple_Sp (K := K) hm (Or.inl hK4)).1

theorem quasisimple_oddCenter_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : CFSG.Open.IsQuasisimple X ∧ Odd (Nat.card (Subgroup.center X))) :
    CFSG.Open.IsQuasisimple X' ∧ Odd (Nat.card (Subgroup.center X')) :=
  ⟨CFSG.Open.IsQuasisimple.of_mulEquiv e.symm h.1,
    Nat.card_congr (Subgroup.centerCongr e).toEquiv ▸ h.2⟩

theorem spFlagLeviBlock_cases_big (hK4 : 4 ≤ Nat.card K) (hI' : ∀ i ∈ I, i ≤ r) (t : ℕ)
    (j : Fin (r + 1)) :
    spFlagLeviBlock (K := K) hI' t j = ⊥ ∨
      (CFSG.Open.IsQuasisimple ↥(spFlagLeviBlock (K := K) hI' t j) ∧
        Odd (Nat.card (Subgroup.center ↥(spFlagLeviBlock (K := K) hI' t j)))) := by
  classical
  by_cases hj0 : (j : ℕ) = 0
  · have h0 : spFlagLeviBlock hI' t j =
        (commutator (StatedSp (r - t) K)).map (spFlagResEmb (r := r) (K := K) t) :=
      spFlagLeviBlock_of_eq_zero hI' hj0
    rcases Nat.eq_zero_or_pos (r - t) with hm | hm
    · left
      rw [h0]
      refine Subgroup.eq_bot_of_card_eq _ ?_
      have hcomm : commutator (StatedSp (r - t) K) = ⊥ := by
        rw [hm]
        refine le_bot_iff.mp fun x _ => Subgroup.mem_bot.mpr (Subsingleton.elim x 1)
      rw [Nat.card_congr (MulEquiv.subgroupCongr h0).symm.toEquiv,
        Nat.card_congr (spFlagLeviBlockZeroEquiv (K := K) hI' t hj0).toEquiv,
        hcomm, Subgroup.card_bot]
    · right
      rw [h0]
      have hcenter_bot : Subgroup.center (StatedSp (r - t) K) = ⊥ := by
        rw [CFSG.LieType.Universal.Symplectic.center_eq,
          CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
      have hW : CFSG.Open.IsQuasisimple (StatedSp (r - t) K) ∧
          Odd (Nat.card (Subgroup.center (StatedSp (r - t) K))) := by
        refine ⟨spFlag_isQuasisimple_Sp hm (Or.inl hK4), ?_⟩
        rw [hcenter_bot, Subgroup.card_bot]
        exact odd_one
      have eW : StatedSp (r - t) K ≃*
          ↥((commutator (StatedSp (r - t) K)).map (spFlagResEmb (r := r) (K := K) t)) :=
        ((Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr
            (commutator_statedSp_eq_top_big hK4 (r - t))).symm).trans
          ((spFlagLeviBlockZeroEquiv (K := K) hI' t hj0).symm.trans
            (MulEquiv.subgroupCongr h0)))
      exact quasisimple_oddCenter_of_mulEquiv eW hW
  · by_cases hj : (j : ℕ) ∈ I
    · rw [spFlagLeviBlock_of_mem hI' hj0 hj]
      rcases ParabCensus.range_toGL_cases (K := K) (m := (j : ℕ) - spFlagPrev I j) with
        hbot | ⟨hK2, -, -⟩ | hq
      · left
        rw [MonoidHom.range_comp, hbot, Subgroup.map_bot]
      · exact absurd hK4 (by omega)
      · right
        rw [MonoidHom.range_comp]
        exact quasisimple_oddCenter_of_mulEquiv
          (Subgroup.equivMapOfInjective _ _ (spFlagCutEmb_injective _ _ _)) hq
    · rw [spFlagLeviBlock_of_not_mem hI' hj0 hj]
      exact Or.inl rfl

theorem odd_relIndex_spFlagLeviHom_big (hK4 : 4 ≤ Nat.card K) (hI' : ∀ i ∈ I, i ≤ r) {t : ℕ}
    (htI : t ∈ I) (hle : Subgroup.pi Set.univ (spFlagLeviBlock (K := K) hI' t) ≤
      (spFlagLeviHom hI' htI).range) :
    Odd ((Subgroup.pi Set.univ (spFlagLeviBlock (K := K) hI' t)).relIndex
      (spFlagLeviHom hI' htI).range) := by
  classical
  have hpiT : (spFlagLeviHom (K := K) hI' htI).range ≤
      Subgroup.pi Set.univ (ParabCensus.spFlagLeviTopBlocks hI' t) := by
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_pi]
    intro j _
    rw [spFlagLeviHom, MonoidHom.pi_apply]
    by_cases hj0 : (j : ℕ) = 0
    · rw [ParabCensus.spFlagLeviTopBlocks_zero hI' t hj0,
        spFlagLeviCoord_of_eq_zero hI' htI hj0, MonoidHom.comp_apply]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    · by_cases hj : (j : ℕ) ∈ I
      · rw [ParabCensus.spFlagLeviTopBlocks_mem hI' t hj0 hj,
          spFlagLeviCoord_of_mem hI' htI hj0 hj, MonoidHom.comp_apply]
        exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
      · rw [ParabCensus.spFlagLeviTopBlocks_not_mem hI' t hj0 hj,
          spFlagLeviCoord_of_not_mem hI' htI hj0 hj]
        exact one_mem _
  have hodd : ¬ 2 ∣
      (Subgroup.pi Set.univ (spFlagLeviBlock (K := K) hI' t)).relIndex
        (spFlagLeviHom hI' htI).range := by
    refine ParabCensus.not_two_dvd_relIndex_pi (T := ParabCensus.spFlagLeviTopBlocks hI' t) ?_
      hle hpiT ?_
    · intro j
      by_cases hj0 : (j : ℕ) = 0
      · rw [spFlagLeviBlock_of_eq_zero hI' hj0, ParabCensus.spFlagLeviTopBlocks_zero hI' t hj0]
        exact Subgroup.map_le_range _ _
      · by_cases hj : (j : ℕ) ∈ I
        · rw [spFlagLeviBlock_of_mem hI' hj0 hj, ParabCensus.spFlagLeviTopBlocks_mem hI' t hj0 hj,
            MonoidHom.range_comp]
          exact Subgroup.map_le_range _ _
        · rw [spFlagLeviBlock_of_not_mem hI' hj0 hj,
            ParabCensus.spFlagLeviTopBlocks_not_mem hI' t hj0 hj]
    · intro j
      by_cases hj0 : (j : ℕ) = 0
      · rw [spFlagLeviBlock_of_eq_zero hI' hj0, ParabCensus.spFlagLeviTopBlocks_zero hI' t hj0]
        have hEq : (commutator (StatedSp (r - t) K)).map (spFlagResEmb (r := r) (K := K) t) =
            (spFlagResEmb (r := r) (K := K) t).range := by
          rw [commutator_statedSp_eq_top_big hK4, Subgroup.map_top]
        rw [hEq, Subgroup.relIndex_self]
        norm_num
      · by_cases hj : (j : ℕ) ∈ I
        · rw [spFlagLeviBlock_of_mem hI' hj0 hj, ParabCensus.spFlagLeviTopBlocks_mem hI' t hj0 hj,
            MonoidHom.range_comp,
            ← Subgroup.map_top (spFlagCutEmb (spFlagPrev I j) j (hI' j hj)),
            Subgroup.relIndex_map_map_of_injective _ _ (spFlagCutEmb_injective _ _ _),
            Subgroup.relIndex_top_right]
          exact ParabCensus.not_two_dvd_index_range_toGL _
        · rw [spFlagLeviBlock_of_not_mem hI' hj0 hj,
            ParabCensus.spFlagLeviTopBlocks_not_mem hI' t hj0 hj, Subgroup.relIndex_self]
          norm_num
  exact Nat.not_even_iff_odd.mp fun he => hodd (even_iff_two_dvd.mp he)

end Big

theorem leviInnOnPW_symp (p : ℕ) [OddPrime p]
    (hGA : GriessAllModelsStatement) : LeviInnOnPW p (IsLieOf IdxB) := by
  intro Y _ _ L P hCP hB hLn _ _ hrk
  haveI := hLn
  rcases ParabCensus.isLieOf_idxB_cases hB with h2 | hbig
  · exact leviInnAtPW_of_spTwo
      (ParabCensus.isSpTwoLeviProduct_idxBTwo (oddCenterRest_of_griess hGA) hCP h2)
  obtain ⟨r, K, _, _, _, -, hK4, ⟨φ⟩⟩ := ParabCensus.exists_mulEquiv_statedSp_of_idxBBig
    (oddCenterRest_of_griess hGA) hCP.comp hCP.odd hbig
  obtain ⟨ρ, I, t, hI, htI, hmax, hρ⟩ := exists_flagStabilizer_of_compParab hCP φ
  have hI' : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  have hker : ρ.toMonoidHom.ker ≤ Subgroup.center (StatedSp r K) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 ρ.injective]
    exact bot_le
  have hρo : Odd (Nat.card ρ.toMonoidHom.ker) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 ρ.injective, Subgroup.card_bot]
    exact odd_one
  have hle := pi_le_range_spFlagLeviHom (K := K) hI' htI hmax
  have hcases := spFlagLeviBlock_cases_big (K := K) hK4 hI' t
  exact leviInnAtW_of_levi_dataP (OddPrime.ne_two p) (K := StatedSp r K)
    (G := fun _ : Fin (r + 1) => StatedSp r K) hCP.parab.1 hCP.odd ρ.toMonoidHom ρ.surjective
    hker hρo (flagStabilizer r K I) hρ.symm (spFlagLeviBlock hI' t)
    (fun j => (spFlagLeviCoord hI' htI j).range) (spFlagLeviHom hI' htI)
    (isPGroup_ker_spFlagLeviHom hI' htI fun i hi => (hI i hi).1)
    hle (commutator_range_spFlagLeviHom_le hI' htI) (odd_relIndex_spFlagLeviHom_big hK4 hI' htI hle)
    (fun j => (hcases j).imp_right fun h => (Or.inl h : IsWBlock _)) (fun x j => ⟨x, rfl⟩)
    (fun j hj => blockOK_spFlagLeviBlockP p hI' htI j ((hcases j).resolve_left hj).1)
    (fun j E _ _ _ x hρx _ => Subtype.ext (ρ.injective (hρx.trans (map_one ρ.toMonoidHom).symm)))
    (fun j hq x _ hβx => by
      rcases hcases j with hb | hb
      · rw [hb, Subgroup.map_bot, Subgroup.mem_bot] at hβx
        exact hβx
      · exact absurd hb.1 hq)
    hrk

theorem fieldIndexOnPW_symp (p : ℕ) [OddPrime p]
    (hGA : GriessAllModelsStatement) : FieldIndexOnPW p (IsLieOf IdxB) :=
  fieldIndexOnPW_of_outPNice (fun _ _ _ _ _ _ hC _ => outPNiceP_of_idxB p hC)
    (leviInnOnPW_symp p hGA)

end CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW

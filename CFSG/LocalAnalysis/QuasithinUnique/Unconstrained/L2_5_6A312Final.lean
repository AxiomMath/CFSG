module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Small
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Rank2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312L2p
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Unc25G2.A312Sub

namespace Unc25G2.A312Sub

section Final

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_modO2Image {X L : Subgroup G} (hLX : IsComponentIn L X) :
    CFSG.IsQuasisimple ↥(modO2Image X L) := by
  have hLc : L ∈ cComp X := mem_cComp_of_isComponentIn hLX
  have hLq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hLX
  obtain ⟨ψ, hψs, hψk⟩ := exists_modO2_surjection hLc
  have hker : ψ.ker ≤ Subgroup.center ↥L := by
    rw [hψk]
    exact pCore_two_le_center_of_quasisimple hLq
  have hnorm : ψ.ker.Normal := inferInstance
  have h := (CFSG.LocalAnalysis.ComponentInitial.quasisimple_central_quotient hLq hker).1
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs) h

theorem modO2Image_equiv_of_simple {X L : Subgroup G} (hLX : IsComponentIn L X)
    (hs : IsSimpleGroup ↥L) : Nonempty (↥L ≃* ↥(modO2Image X L)) := by
  have hLc : L ∈ cComp X := mem_cComp_of_isComponentIn hLX
  have hLq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hLX
  obtain ⟨e⟩ := modO2_mulEquiv hLc
  have hpc : CFSG.pCore 2 ↥L = ⊥ :=
    pCore_eq_bot_of_simple (not_isPGroup_two_of_quasisimple hLq)
  exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hpc.symm)).trans e⟩

theorem final_small
    {K L : Subgroup G} (hKL : K ≤ L) (hKl : IsListed25 K)
    (hKnb : ¬ fusionIsBenderGroup ↥K) {N : ℕ} (hN : N = 360 ∨ N = 5616 ∨ N = 7920)
    (hL : Nat.card ↥L = N)
    (hM11 : N = 7920 → Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) :
    K = L ∨ (Nonempty (↥K ≃* alternatingGroup (Fin 6)) ∧
      Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) := by
  have hdvd : Nat.card ↥K ∣ N := hL ▸ Subgroup.card_dvd_of_le hKL
  rcases K_small hKl hKnb hN hdvd with h | ⟨h7920, hA6⟩
  · left
    exact Subgroup.eq_of_le_of_card_ge hKL (by rw [h, hL])
  · right
    exact ⟨hA6, hM11 h7920⟩

theorem fusionIsBenderGroup_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : fusionIsBenderGroup X) : fusionIsBenderGroup Y := by
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ | ⟨a, ha, ⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.symm.trans e'⟩⟩)

end Final

end Unc25G2.A312Sub

theorem a312Sublist :
    A312Sublist := by
  intro G _ _ T M hs X S K L hX hS hKc hKs hKo hKL hLX hKl hKnb hLl
  have hKq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn hKc
  have hLq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hLX
  have hLc : L ∈ cComp X := mem_cComp_of_isComponentIn hLX
  have hLbq : CFSG.IsQuasisimple ↥(modO2Image X L) := isQuasisimple_modO2Image hLX
  have key : ∀ {P : Subgroup ↥(modO2Image X L) → Prop}, Over ↥(modO2Image X L) P →
      (∀ B : Subgroup ↥(modO2Image X L), P B → ∀ ψ : ↥K →* ↥B, Function.Surjective ψ →
        IsPGroup 2 ψ.ker → False) → K = L := by
    intro P hover hP
    rcases sub_of_over hS hKc hKL hLX hover with h | ⟨hPB, ψ, hψs, hψk⟩
    · exact h
    · exact (hP _ hPB ψ hψs hψk).elim
  have key0 : Over ↥(modO2Image X L) (fun _ => False) → K = L :=
    fun h => key h (fun B hB => hB.elim)
  have keyQ1 : Over ↥(modO2Image X L) Q1 → K = L := fun h =>
    key h (fun B hB ψ hψs hψk => (K_side hKq hKl hKnb ψ hψs hψk).1 hB)
  have keyQ2 : Over ↥(modO2Image X L) Q2 → K = L := fun h =>
    key h (fun B hB ψ hψs hψk => (K_side hKq hKl hKnb ψ hψs hψk).2.1 hB)
  rcases hLl with hB | hR | ⟨h33 | ⟨⟨e⟩⟩⟩ | ⟨p, hpf, hp7, hp⟩
  ·
    left
    have hs' : IsSimpleGroup ↥L := RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
    obtain ⟨e⟩ := modO2Image_equiv_of_simple hLX hs'
    exact key0 (over_bender hLbq (fusionIsBenderGroup_of_mulEquiv e hB))
  · rcases hR with ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨⟨e⟩⟩ | h
    ·
      left
      have hs' : IsSimpleGroup ↥L := isSimpleGroup_of_stated (t := .PSL) h
      obtain ⟨e⟩ := modO2Image_equiv_of_simple hLX hs'
      exact keyQ1 (over_l3even _ n hLbq hn (IsPSL.of_mulEquiv e h))
    ·
      left
      have hs' : IsSimpleGroup ↥L := isSimpleGroup_of_stated (t := .PSp) h
      obtain ⟨e⟩ := modO2Image_equiv_of_simple hLX hs'
      exact keyQ1 (over_sp4 _ n hLbq hn (IsPSp4.of_mulEquiv e h))
    ·
      have hL : Nat.card ↥L = 360 := (Nat.card_congr e.toEquiv).trans card_alt_six_loc
      exact final_small hKL hKl hKnb (N := 360) (Or.inl rfl) hL (fun h => by omega)
    ·
      left
      obtain ⟨e⟩ := modO2_mulEquiv hLc
      exact keyQ1 (over_l3even _ 2 hLbq (by norm_num) (IsPSL.of_mulEquiv e h))
  ·
    have hL := card_psl_three_three h33
    exact final_small hKL hKl hKnb (N := 5616) (Or.inr (Or.inl rfl)) hL (fun h => by omega)
  ·
    have hL : Nat.card ↥L = 7920 := (Nat.card_congr e.toEquiv).trans
      CFSG.Semidihedral.GL2Recognition.card_nativeM11
    exact final_small hKL hKl hKnb (N := 7920) (Or.inr (Or.inr rfl)) hL (fun _ => ⟨e⟩)
  ·
    left
    have hs' : IsSimpleGroup ↥L := isSimpleGroup_of_stated (t := .PSL) hp
    obtain ⟨e⟩ := modO2Image_equiv_of_simple hLX hs'
    exact keyQ2 (over_l2p _ p hpf.1 (by omega) (IsPSL.of_mulEquiv e hp))

end CFSG.QuasithinUnique

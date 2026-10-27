module

public import CFSG.LocalAnalysis.GLTheoremA.Lemma48
public import CFSG.LocalAnalysis.GLTheoremA.Lemma45

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

private theorem glaPPrimeCoreOf_eq_self_of_not_dvd {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (hH : ¬ p ∣ Nat.card H) : GLAPPrimeCoreOf p H = H := by
  refine le_antisymm (Subgroup.map_subtype_le _) ?_
  have hcop : Nat.Coprime p (Nat.card (⊤ : Subgroup ↥H)) := by
    rw [Subgroup.card_top]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hH
  have htop : (⊤ : Subgroup ↥H) ≤ GLAPPrimeCore p ↥H := le_sSup ⟨inferInstance, hcop⟩
  intro h hh
  exact Subgroup.mem_map.2 ⟨⟨h, hh⟩, htop (Subgroup.mem_top _), rfl⟩

theorem le_glaPPrimeCoreOf_of_commutator_le {p : ℕ} (hp : p.Prime) {C N : Subgroup G}
    (𝓛 : Set (Subgroup G)) (h𝓛 : ∀ L ∈ 𝓛, GLAPComponent p C L) (hN : ¬ p ∣ Nat.card N)
    (hNK : N ≤ sSup 𝓛 ⊔ GLAPPrimeCoreOf p C)
    (hc : (⁅N, sSup 𝓛⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p C) : N ≤ GLAPPrimeCoreOf p C := by
  have hKE : sSup 𝓛 ≤ GLAPLayer p C := sSup_le_sSup (fun L hL => h𝓛 L hL)
  have hEC : GLAPLayer p C ≤ C := sSup_le fun L (hL : GLAPComponent p C L) => hL.1
  have hKC : sSup 𝓛 ≤ C := hKE.trans hEC
  have hOC : GLAPPrimeCoreOf p C ≤ C := Subgroup.map_subtype_le _
  have hCN : C ≤ Subgroup.normalizer (GLAPPrimeCoreOf p C : Set G) :=
    le_normalizer_glaPPrimeCoreOf p C
  have hNsup : N ≤ N ⊔ GLAPPrimeCoreOf p C := le_sup_left
  have hOsup : GLAPPrimeCoreOf p C ≤ N ⊔ GLAPPrimeCoreOf p C := le_sup_right
  have hNO : N ≤ Subgroup.normalizer (GLAPPrimeCoreOf p C : Set G) :=
    hNK.trans ((sup_le hKC hOC).trans hCN)
  have hNOp : ¬ p ∣ Nat.card (N ⊔ GLAPPrimeCoreOf p C : Subgroup G) := by
    have h := not_dvd_card_sup_of_le_normalizer hp hNO (not_dvd_card_glaPPrimeCoreOf hp C) hN
    rwa [sup_comm] at h
  have hKN : sSup 𝓛 ⊔ GLAPPrimeCoreOf p C ≤
      Subgroup.normalizer ((N ⊔ GLAPPrimeCoreOf p C : Subgroup G) : Set G) := by
    refine sup_le (fun k hk => ?_) ?_
    · have key : N ⊔ GLAPPrimeCoreOf p C ≤ GLBConj k (N ⊔ GLAPPrimeCoreOf p C) := by
        refine sup_le (fun n hn => mem_gLBConj.2 ?_) (fun o ho => mem_gLBConj.2 ?_)
        · have hcm : n * k * n⁻¹ * k⁻¹ ∈ GLAPPrimeCoreOf p C :=
            hc (Subgroup.commutator_mem_commutator hn hk)
          have hid : k * n * k⁻¹ = (n * k * n⁻¹ * k⁻¹)⁻¹ * n := by group
          rw [hid]
          exact mul_mem (hOsup ((GLAPPrimeCoreOf p C).inv_mem hcm)) (hNsup hn)
        · have hko : k * o * k⁻¹ ∈ GLAPPrimeCoreOf p C :=
            (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p C (hKC hk)) o).1 ho
          exact hOsup hko
      exact CFSG.LocalAnalysis.GLTheoremA.mem_normalizer_of_conj_mem
        (fun y hy => mem_gLBConj.1 (key hy))
    · exact hOsup.trans Subgroup.le_normalizer
  have hE : ∀ L ∈ 𝓛, GLAPLayer p C ≤ Subgroup.normalizer (L : Set G) := by
    intro L hL
    refine sSup_le fun L' hL' => ?_
    by_cases hLL : L' = L
    · subst hLL
      exact Subgroup.le_normalizer
    · intro g hg
      exact CFSG.HardMathSupport.Solomon.LocalBalance.mem_normalizer_of_ne hp (h𝓛 L hL)
        (hL' : GLAPComponent p C L') (fun h => hLL h.symm) hg
  have hEK : GLAPLayer p C ≤ Subgroup.normalizer ((sSup 𝓛 : Subgroup G) : Set G) :=
    fun e he => CFSG.LocalAnalysis.GLTheoremA.mem_normalizer_sSup (fun L hL => hE L hL he)
  have hEO : GLAPLayer p C ≤ Subgroup.normalizer (GLAPPrimeCoreOf p C : Set G) := hEC.trans hCN
  have hEKO : GLAPLayer p C ⊔ GLAPPrimeCoreOf p C ≤
      Subgroup.normalizer ((sSup 𝓛 ⊔ GLAPPrimeCoreOf p C : Subgroup G) : Set G) := by
    refine sup_le (fun e he => ?_) ?_
    · exact CFSG.LocalAnalysis.GLTheoremA.mem_normalizer_sup (hEK he) (hEO he)
    · exact (le_sup_right : GLAPPrimeCoreOf p C ≤ sSup 𝓛 ⊔ GLAPPrimeCoreOf p C).trans
        Subgroup.le_normalizer
  have hCEO : C ≤
      Subgroup.normalizer ((GLAPLayer p C ⊔ GLAPPrimeCoreOf p C : Subgroup G) : Set G) :=
    fun g hg => CFSG.LocalAnalysis.GLTheoremA.mem_normalizer_sup
      (CFSG.LocalAnalysis.GLTheoremA.mem_normalizer_glaPLayer (p := p) (Subgroup.le_normalizer hg))
      (hCN hg)
  have hle1 : N ⊔ GLAPPrimeCoreOf p C ≤ sSup 𝓛 ⊔ GLAPPrimeCoreOf p C :=
    sup_le hNK le_sup_right
  have hle2 : sSup 𝓛 ⊔ GLAPPrimeCoreOf p C ≤ GLAPLayer p C ⊔ GLAPPrimeCoreOf p C :=
    sup_le (hKE.trans le_sup_left) le_sup_right
  have hle3 : GLAPLayer p C ⊔ GLAPPrimeCoreOf p C ≤ C := sup_le hEC hOC
  have hsn : CFSG.Open.IsSubnormal (N ⊔ GLAPPrimeCoreOf p C) C :=
    CFSG.Open.IsSubnormal.step hle1 ((Subgroup.normal_subgroupOf_iff_le_normalizer hle1).2 hKN)
      (CFSG.Open.IsSubnormal.step hle2
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hle2).2 hEKO)
        (CFSG.Open.IsSubnormal.step hle3
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hle3).2 hCEO)
          (CFSG.Open.IsSubnormal.refl C)))
  have hfix := glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsn
  rw [inf_eq_right.2 hOsup, glaPPrimeCoreOf_eq_self_of_not_dvd hp hNOp] at hfix
  exact hNsup.trans hfix.symm.le

end CFSG.LocalAnalysis.GLTheoremA

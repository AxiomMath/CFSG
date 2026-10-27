module

public import CFSG.Open.GLADefs
public import CFSG.LocalAnalysis.GL83PartI.Goldschmidt_2_5
public import CFSG.LocalAnalysis.GL83PartI.GL1_4_2
import CFSG.LocalAnalysis.GLTheoremB.BaseCase
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Components

public section

universe u

namespace GL83.Goldschmidt

section Cores

variable {G : Type u} [Group G]

theorem le_piCoreOf_of_normal [Finite G] {σ : Set Nat.Primes} {N A : Subgroup G} (hNA : N ≤ A)
    (hn : A ≤ Subgroup.normalizer (N : Set G)) (hπ : CFSG.IsPiSubgroup σ N) :
    N ≤ piCoreOf σ A := by
  have hnorm : (N.subgroupOf A).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).2 hn
  have hπ' : CFSG.IsPiSubgroup σ (N.subgroupOf A) := fun r hr =>
    hπ r (hr.trans (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNA).toEquiv).dvd)
  have hle := CFSG.LocalCores.le_piCore_of_normal hnorm hπ'
  have := Subgroup.map_mono (f := A.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hNA] at this

theorem normalizer_le_normalizer_piCoreOf (σ : Set Nat.Primes) (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (piCoreOf σ S : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  have h := map_piCoreOf σ (MulAut.conj g : G →* G) (MulAut.conj g).injective S
  rw [h, hg]

theorem piCoreOf_inf_le_piCoreOf [Finite G] {σ : Set Nat.Primes} {A B : Subgroup G}
    (hBA : B ≤ A) : piCoreOf σ A ⊓ B ≤ piCoreOf σ B := by
  refine le_piCoreOf_of_normal inf_le_right (fun b hb => ?_)
    ((isPiSubgroup_piCoreOf σ A).of_le inf_le_left)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.1 (le_normalizer_piCoreOf σ A (hBA hb)) x
  have h2 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hb) x
  exact and_congr h1 h2

theorem piCoreOf_le_piCoreOf_of_le_normalizer [Finite G] {σ : Set Nat.Primes} {S H : Subgroup G}
    (hSH : S ≤ H) (hHS : H ≤ Subgroup.normalizer (S : Set G)) : piCoreOf σ S ≤ piCoreOf σ H :=
  le_piCoreOf_of_normal ((piCoreOf_le σ S).trans hSH)
    (hHS.trans (normalizer_le_normalizer_piCoreOf σ S)) (isPiSubgroup_piCoreOf σ S)

end Cores

end GL83.Goldschmidt

namespace GL83

open CFSG.Open GL83.Goldschmidt CFSG.SignalizerFunctorTheorem.McBride
  CFSG.SignalizerFunctorTheorem.McBride.Nonsolv CFSG.LocalAnalysis.GLTheoremB

variable {G : Type u} [Group G] [Finite G]

theorem pCoreOf_le_sol (q : ℕ) [Fact q.Prime] (B : Subgroup G) : pCoreOf q B ≤ sol B := by
  unfold CFSG.Open.pCoreOf sol
  refine Subgroup.map_mono ?_
  have := CFSG.pCore_isNilpotent (p := q) (G := ↥B)
  exact CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical CFSG.pCore_normal inferInstance

theorem pCoreOf_inf_le_pCoreOf (q : ℕ) [Fact q.Prime] {A B : Subgroup G} (hBA : B ≤ A) :
    pCoreOf q A ⊓ B ≤ pCoreOf q B := by
  rw [pCoreOf_eq_piCoreOf, pCoreOf_eq_piCoreOf]
  exact piCoreOf_inf_le_piCoreOf hBA

theorem pCoreOf_le_pCoreOf_of_le_normalizer (q : ℕ) [Fact q.Prime] {S H : Subgroup G}
    (hSH : S ≤ H) (hHS : H ≤ Subgroup.normalizer (S : Set G)) : pCoreOf q S ≤ pCoreOf q H := by
  rw [pCoreOf_eq_piCoreOf, pCoreOf_eq_piCoreOf]
  exact piCoreOf_le_piCoreOf_of_le_normalizer hSH hHS

theorem I_19_1_6_of_cyclic {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {H E : Subgroup G}
    (hEH : E ≤ H) (hE : IsElemAbelian p E) (hE2 : p ^ 2 ≤ Nat.card E)
    (hcyc : ∀ J ∈ lcalOf (↥(GLAPPrimeCoreOf p H) ⧸ CFSG.solvableRadical ↥(GLAPPrimeCoreOf p H)),
      ∀ P : Subgroup (MulAut ↥J), IsPGroup p P → IsCyclic P) :
    (⨅ (e : G) (_ : e ∈ E), ⨅ (_ : e ≠ 1),
        pCoreOf q (H ⊓ Subgroup.centralizer ({e} : Set G))) ⊓ GLAPPrimeCoreOf p H ≤
      pCoreOf q H := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  set K := GLAPPrimeCoreOf p H with hK
  have hKH : K ≤ H := Subgroup.map_subtype_le _
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_glaPPrimeCoreOf p H
  have hEK : E ≤ Subgroup.normalizer (K : Set G) := hEH.trans hHK
  have hpK : ¬ p ∣ Nat.card K := not_dvd_card_glaPPrimeCoreOf hp H
  have h1 := GL1_4_2 hp hEK hE hE2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpK) hcyc
  set S := sol K with hS
  have hSK : S ≤ K := sol_le K
  have hHS : H ≤ Subgroup.normalizer (S : Set G) := hHK.trans (SolQuot.normalizer_le_nrm_sol K)
  have hES : E ≤ Subgroup.normalizer (S : Set G) := hEH.trans hHS
  have hSp : ¬ p ∣ Nat.card S := fun h => hpK (h.trans (Subgroup.card_dvd_of_le hSK))
  have h2 := Goldschmidt_2_5_pCore hq hp (isSolvable_sol K) hES hE hE2 hSp
  rintro w ⟨hwI, hwK⟩
  have hwe : ∀ e ∈ E, e ≠ 1 →
      w ∈ pCoreOf q (H ⊓ Subgroup.centralizer ({e} : Set G)) := fun e he he1 =>
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hwI e) he) he1
  have hwC : ∀ e ∈ E, e ≠ 1 → w ∈ Subgroup.centralizer ({e} : Set G) := fun e he he1 =>
    (Subgroup.map_subtype_le _ (hwe e he he1)).2
  have hwS : w ∈ S := by
    refine h1 (Subgroup.mem_iInf.2 fun e => Subgroup.mem_iInf.2 fun he =>
      Subgroup.mem_iInf.2 fun he1 => ?_)
    have hle : K ⊓ Subgroup.centralizer ({e} : Set G) ≤ H ⊓ Subgroup.centralizer ({e} : Set G) :=
      inf_le_inf_right _ hKH
    exact pCoreOf_le_sol q _ (pCoreOf_inf_le_pCoreOf q hle ⟨hwe e he he1, hwK, hwC e he he1⟩)
  have hw3 : w ∈ pCoreOf q S := by
    refine h2 (Subgroup.mem_iInf.2 fun e => Subgroup.mem_iInf.2 fun he =>
      Subgroup.mem_iInf.2 fun he1 => ?_)
    have hle : S ⊓ Subgroup.centralizer ({e} : Set G) ≤ H ⊓ Subgroup.centralizer ({e} : Set G) :=
      inf_le_inf_right _ (hSK.trans hKH)
    exact pCoreOf_inf_le_pCoreOf q hle ⟨hwe e he he1, hwS, hwC e he he1⟩
  exact pCoreOf_le_pCoreOf_of_le_normalizer q (hSK.trans hKH) hHS hw3

end GL83

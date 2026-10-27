module

public import CFSG.LargeExtraspecial.S63BBasic
public import CFSG.LieType.Chevalley.GraphTwistedOuterTwoPart

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Timmesfeld CFSG.ComponentClassification

namespace S63

@[expose] def D42CentInput : Prop :=
  ∀ (Y : Type) [Group Y], Blueprint.LieModel Y .trialityD4 0 2 1 →
    ∀ (s : Y), orderOf s = 2 → ∀ N : Subgroup Y, N ≤ centralizer ({s} : Set Y) →
      (∀ c ∈ centralizer ({s} : Set Y), ∀ n ∈ N, c * n * c⁻¹ ∈ N) → IsPGroup 2 N → s ∈ N →
        (∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n = 1 ∨ n = s) → 2 ^ 5 ≤ Nat.card N →
          N ≤ zpowers s ⊔ ⁅N, centralizer ({s} : Set Y)⁆ ∧ centralizer (N : Set Y) ≤ N

theorem odd_card_outer_of_trialityD4 {Y : Type} [Group Y] [Finite Y]
    (h : Blueprint.LieModel Y .trialityD4 0 2 1) :
    Odd (Nat.card (OuterAutomorphisms.Outer Y)) := by
  have hY : Blueprint.ChevalleyExceptionalModel Y .trialityD4 2 1 := by
    rcases h with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have h2 := (LieType.Chevalley.graph_twisted_exceptional_model_outer_two_part_bound Y
    .trialityD4 2 1 3 hY (Or.inr ⟨rfl, rfl⟩)).2.1 rfl
  have h1 : ordProj[2] 1 = 1 := by simp
  rw [h1] at h2
  have hne : Nat.card (OuterAutomorphisms.Outer Y) ≠ 0 := Nat.card_pos.ne'
  have hcop := Nat.coprime_ordCompl Nat.prime_two hne
  rw [h2, Nat.div_one] at hcop
  exact Nat.coprime_two_left.mp hcop

namespace SmithConf

variable {X : Type} [Group X] [Finite X] {ζ : X} {F : Subgroup X}
variable (hC : SmithConf ζ F) (hs : IsSimpleGroup (UZ ζ))
include hC hs

theorem le_normalClosure_of_le_sup (hFeq : Finn ζ F = F)
    (hNle : (iota (F := F) hs).range ≤ zpowers (piU ζ (zetaU ζ)) ⊔
      ⁅(iota (F := F) hs).range, centralizer ({piU ζ (zetaU ζ)} : Set (UZ ζ))⁆) :
    F ≤ normalClosure ({ζ} : Set X) := by
  have hζF : ζ ∈ Finn ζ F := hC.zeta_mem_Finn
  have hιζ : iota (F := F) hs ⟨ζ, hζF⟩ = piU ζ (zetaU ζ) :=
    iota_of_mem_U hs ⟨ζ, hζF⟩ (zetaU ζ).2
  set H : Subgroup X := normalClosure ({ζ} : Set X) ⊓ Finn ζ F with hH
  have hle : zpowers (piU ζ (zetaU ζ)) ⊔
      ⁅(iota (F := F) hs).range, centralizer ({piU ζ (zetaU ζ)} : Set (UZ ζ))⁆ ≤
      (H.subgroupOf (Finn ζ F)).map (iota (F := F) hs) := by
    refine sup_le ?_ ?_
    · rw [zpowers_le]
      exact ⟨⟨ζ, hζF⟩, mem_subgroupOf.mpr ⟨(zetaU ζ).2, hζF⟩, hιζ⟩
    · rw [commutator_le]
      rintro _ ⟨f, rfl⟩ c hc
      obtain ⟨u, rfl, hu⟩ := hC.exists_lift_of_comm hs (mem_centralizer_singleton_iff.mp hc)
      have hgU : (f : X) * u * (f : X)⁻¹ * (u : X)⁻¹ ∈ normalClosure ({ζ} : Set X) :=
        mul_mem (normalClosure_normal.conj_mem _ u.2 _) (inv_mem u.2)
      have hgF : (f : X) * u * (f : X)⁻¹ * (u : X)⁻¹ ∈ Finn ζ F := by
        have h1 := hC.conj_mem_Finn u.2 hu (inv_mem f.2)
        rw [show (f : X) * u * (f : X)⁻¹ * (u : X)⁻¹ = f * ((u : X) * (f : X)⁻¹ * (u : X)⁻¹) by
          group]
        exact mul_mem f.2 h1
      refine ⟨⟨_, hgF⟩, mem_subgroupOf.mpr ⟨hgU, hgF⟩, ?_⟩
      rw [iota_of_mem_U hs ⟨_, hgF⟩ hgU, commutatorElement_def, iota_conj hs f u]
      rw [show (⟨(f : X) * u * (f : X)⁻¹ * (u : X)⁻¹, hgU⟩ : ↥(normalClosure ({ζ} : Set X))) =
          ⟨(f : X) * u * (f : X)⁻¹, normalClosure_normal.conj_mem _ u.2 _⟩ * u⁻¹ from rfl,
        map_mul, map_inv]
  intro f hf
  have hf' : f ∈ Finn ζ F := by rw [hFeq]; exact hf
  obtain ⟨g, hg, hgf⟩ := hle (hNle ⟨⟨f, hf'⟩, rfl⟩)
  replace hg := mem_subgroupOf.mp hg
  have := hC.iota_injective hs hgf
  rw [← show ((g : ↥(Finn ζ F)) : X) = f from congrArg Subtype.val this]
  exact hg.1

omit [Finite X] in
theorem false_of_centralizer_le (hFU : F ≤ normalClosure ({ζ} : Set X))
    (hCN : centralizer ((iota (F := F) hs).range : Set (UZ ζ)) ≤ (iota (F := F) hs).range)
    (hZ : center ↥(normalClosure ({ζ} : Set X)) = ⊥) : False := by
  have hπinj : Function.Injective (piU ζ) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  obtain ⟨τ, hτc, hτne⟩ := hC.nonIsolated
  obtain ⟨f, hf, hfc⟩ := exists_mem_mul_centralizer (hC.hyp.conj_mem_E τ hτc.2 hτc.1)
  have hτU := mem_normalClosure_of_isConj hτc.2
  have hcU : f⁻¹ * τ ∈ normalClosure ({ζ} : Set X) := mul_mem (inv_mem (hFU hf)) hτU
  have hπc : piU ζ ⟨f⁻¹ * τ, hcU⟩ ∈
      centralizer ((iota (F := F) hs).range : Set (UZ ζ)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    rw [iota_of_mem_U hs g (hFU (Finn_le ζ F g.2)), ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp hfc g (Finn_le ζ F g.2))
  obtain ⟨g, hg⟩ := hCN hπc
  rw [iota_of_mem_U hs g (hFU (Finn_le ζ F g.2))] at hg
  have hcg : f⁻¹ * τ = g := congrArg Subtype.val (hπinj hg).symm
  have hτF : τ ∈ F := by
    rw [show τ = f * (f⁻¹ * τ) by group, hcg]
    exact mul_mem hf (Finn_le ζ F g.2)
  exact hτne (hC.hyp.conj_mem_F τ hτF hτc.2)

end SmithConf

end S63

end CFSG.LargeExtraspecial

module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4F
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SympL4Surv

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage12
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

theorem odd_of_mod_eight {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq8 : p ^ f % 8 ≠ 1) :
    Odd f := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  by_contra hnot
  obtain ⟨m, rfl⟩ := Nat.not_odd_iff_even.mp hnot
  have hsq : p ^ (m + m) = (p ^ m) ^ 2 := by ring
  rw [hsq] at hq8
  have hm : p ^ m % 2 = 1 := by
    rw [Nat.pow_mod, hpodd]
    simp
  have h8 : ∀ a : ℕ, a % 2 = 1 → a ^ 2 % 8 = 1 := by
    intro a ha
    have := Nat.mod_lt a (by norm_num : 8 > 0)
    interval_cases h : a % 8 <;> simp [Nat.pow_mod, h] <;> omega
  exact hq8 (h8 _ hm)

variable {F : Type} [Field F] [Finite F]

theorem not_admAut_of_sl3 {k : Kind} {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (hodd : Odd (Nat.card F)) (h3 : 3 ≤ Nat.card F) {u : MulAut (projectiveSL 4 F)}
    (ρ : SpecialLinearGroup (Fin 3) F →* projectiveSL 4 F) (hρ : Function.Injective ρ)
    (hfix : ∀ g, u (ρ g) = ρ g) : ¬ AdmAut k u := by
  intro hadm
  let ψ : SpecialLinearGroup (Fin 3) F →* ↥(fixSub u) := ρ.codRestrict _ hfix
  have hψ : Function.Injective ψ := fun a b h => hρ (congrArg Subtype.val h)
  have hs := isSimpleGroup_projectiveSL3 F
  have hperf := isPerfect_projectiveSL3 F
  have : Nontrivial (projectiveSL 3 F) := IsSimpleGroup.toNontrivial
  exact not_kindFactorAll hp2 (involved_qdSL_projectiveSL3 (p := p))
    (not_card_dvd_factorial_projectiveSL3 hodd h3)
    (hadm _ (Group.IsPerfect.not_isSolvable _) ⟨ψ.range,
      (proj 3 F).comp (MonoidHom.ofInjective hψ).symm.toMonoidHom,
      (QuotientGroup.mk'_surjective _).comp (MonoidHom.ofInjective hψ).symm.surjective⟩)

theorem not_admAut_symp {k : Kind} (hk : IsClassicalKind k) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f) (h2 : (2 : F) ≠ 0)
    (A : GL (Fin 4) F) (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = -A) :
    ¬ AdmAut k (conjAut 4 F A * dualAut 4 F) := by
  intro hadm
  obtain ⟨ϖ, hfix, hker⟩ := exists_sp4_hom_of_alt_L4 h2 A hA
  obtain ⟨hsimple, hns, hbad⟩ := BS4.psp4_bad hk hp hp2 hf hcard
  let ψ : ↥(StatedSp 2 F) →* ↥(fixSub (conjAut 4 F A * dualAut 4 F)) := ϖ.codRestrict _ hfix
  have hle : ψ.ker ≤ ((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F)).comap
      (MonoidHom.id (StatedSp 2 F)) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hker x (congrArg Subtype.val (MonoidHom.mem_ker.mp hx)))
  let c : ↥ψ.range →* StatedProj (StatedSp 2 F) :=
    (QuotientGroup.map ψ.ker _ (MonoidHom.id (StatedSp 2 F)) hle).comp
      (QuotientGroup.quotientKerEquivRange ψ).symm.toMonoidHom
  have hc : Function.Surjective c :=
    (QuotientGroup.map_surjective_of_surjective ψ.ker
      ((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F)) (MonoidHom.id (StatedSp 2 F))
      (fun t => QuotientGroup.mk_surjective t) hle).comp
      (QuotientGroup.quotientKerEquivRange ψ).symm.surjective
  exact hbad (hadm _ hns ⟨ψ.range, c, hc⟩)

theorem surv4Orth_of_admAut {k : Kind} (hk : IsClassicalKind k) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq8 : p ^ f % 8 ≠ 1) (hcard : Nat.card F = p ^ f)
    {u : MulAut (projectiveSL 4 F)} (hu2 : u * u = 1) (hadm : AdmAut k u) : Surv4Orth u := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hK2 : ringChar F ≠ 2 := by rwa [ringChar.eq F p]
  have hFodd : Odd (Nat.card F) := by
    rw [hcard, Nat.odd_iff]
    exact Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)
  have h3 : 3 ≤ Nat.card F := by
    rw [hcard]
    have h2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    have := Nat.odd_iff.mp hFodd
    omega
  rcases linear4_involution_cases hp hf hcard (odd_of_mod_eight hp hp2 hq8) hK2 u
      (by rw [sq]; exact hu2) with ⟨ρ, hρ, hfix⟩ | hS
  · exact absurd hadm (not_admAut_of_sl3 hp2 hFodd h3 ρ hρ hfix)
  · rcases hS with h | h | ⟨A, hα, hA | hA⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨A, hα, hA⟩)
    · rw [hα] at hadm
      exact absurd hadm (not_admAut_symp hk hp hp2 hf hcard (Ring.two_ne_zero hK2) A hA)

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

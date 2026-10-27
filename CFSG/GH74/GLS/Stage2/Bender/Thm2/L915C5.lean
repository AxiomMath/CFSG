module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915C4
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Case
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915C3

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement Pointwise

@[expose] def Prop9_5Tail : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∀ (J : Subgroup G) (n : ℕ), IsQuasisimple ↥J → z ∈ J →
      (∀ c ∈ J, (∀ g ∈ J, c * g = g * c) → c * c = 1 → c = 1) → 1 ≤ n →
      LieModel (↥J ⧸ center ↥J) .PSL 3 p n → Op p M ≤ J → IsElementaryAbelian p ↥(Op p M) →
      Nat.card ↥(Op p M) = p ^ (2 * n) → Op p M ⊓ Cen z = ⊥ →
      (∀ x ∈ Op p M, x ≠ 1 → ∀ y ∈ Op p M, y ≠ 1 → ∃ c ∈ J ⊓ Cen z, c * x * c⁻¹ = y) →
      M ≤ normalizer (J : Set G)

namespace L915

section Final

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
  {N A B : Subgroup G}

theorem caseC_false_of_tail (hNo : NoL3Overgroup) (hTail : Prop9_5Tail) (hC : Ctx9 G z k S M p)
    (h : Hyp95 z M p N A B) (hO2 : Op 2 N = ⊥) (hnot : Fs N ≠ Op p N)
    (hAE : ¬ A ≤ centralizer (Em N : Set G))
    (hcC : C43c (zSec z N (z_mem_N h) (pCore p ↥N)) p (xBar p N (A1 z M N p))) : False := by
  have hp := hC.prime
  have hzN : z ∈ N := z_mem_N h
  have hA₀ : Op p M ⊓ N ⊓ Cen z = ⊥ := a0_eq_bot k1_statement hNo hC h hO2 hAE hcC
  obtain ⟨J, n, hn, hJ, hJn, hOJ, hJK, hzJ, hA₁J, hLie, hAJ, hel, hcard⟩ := exists_caseC_J hC h hAE hcC
  have hO2' : pCore 2 ↥N = ⊥ := by
    have := hO2
    rw [Op_eq_map, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype] at this
    exact le_bot_iff.mp this
  have htrans := A1_transitive hC h hO2 hA₀ hJ hOJ hJK hzJ hcC
  have hPA : Op p M = A1 z M N p :=
    P_eq_A1 hC h hA₀ (fun x hx hx1 y hy hy1 => by
      obtain ⟨j, -, hjz, hjxy⟩ := htrans x hx hx1 y hy hy1
      exact ⟨j, hjz, hjxy⟩)
  have hA₁N : A1 z M N p ≤ N := (A1_le hC hzN).trans inf_le_right
  set JG : Subgroup G := J.map N.subtype with hJG
  have hJGq : IsQuasisimple ↥JG :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (J.equivMapOfInjective N.subtype N.subtype_injective)
      hJ.1
  have hzJG : z ∈ JG := ⟨⟨z, hzN⟩, hzJ, rfl⟩
  have hnoc : ∀ c ∈ JG, (∀ g ∈ JG, c * g = g * c) → c * c = 1 → c = 1 := noc_of_component hJ hO2'
  have hLieG : LieModel (↥JG ⧸ center ↥JG) .PSL 3 p n := by
    refine Odd87.Transport.lieModel_of_mulEquiv ?_ hLie
    exact QuotientGroup.congr (center ↥J) (center ↥JG)
      (J.equivMapOfInjective N.subtype N.subtype_injective) (Subgroup.map_center_eq _)
  have hPJ : Op p M ≤ JG := by
    rw [hPA]
    intro a ha
    exact ⟨⟨a, hA₁N ha⟩, hA₁J (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  have hinj := mk_injOn_A1 hC hA₀ hOJ hzJ
  set Xb := xBar p N (A1 z M N p) with hXb
  let φ : ↥(A1 z M N p) →* ↥Xb :=
    ((QuotientGroup.mk' (pCore p ↥N)).comp (Subgroup.inclusion hA₁N)).codRestrict Xb
      (fun a => ⟨⟨a, hA₁N a.2⟩, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩)
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : QuotientGroup.mk' (pCore p ↥N) ⟨a, hA₁N a.2⟩ =
        QuotientGroup.mk' (pCore p ↥N) ⟨b, hA₁N b.2⟩ := congrArg Subtype.val hab
    have := hinj _ (Subgroup.mem_subgroupOf.mpr a.2) _ (Subgroup.mem_subgroupOf.mpr b.2) h1
    exact Subtype.ext (congrArg (fun x : ↥N => (x : G)) this)
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, a', ha', rfl⟩
    exact ⟨⟨a', Subgroup.mem_subgroupOf.mp ha'⟩, rfl⟩
  have hel' : CFSG.IsElementaryAbelian p ↥(A1 z M N p) :=
    isElementaryAbelian_of_injective' φ hφinj hel
  have hcard' : Nat.card ↥(A1 z M N p) = p ^ (2 * n) := by
    rw [Nat.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)]
    exact hcard
  have hPcz : Op p M ⊓ Cen z = ⊥ := by
    rw [hPA]
    refine eq_bot_iff.mpr fun x hx => ?_
    have h1 : x ∈ Op p M ⊓ N ⊓ Cen z := ⟨A1_le hC hzN hx.1, hx.2⟩
    rw [hA₀, Subgroup.mem_bot] at h1
    exact h1
  have htransG : ∀ x ∈ Op p M, x ≠ 1 → ∀ y ∈ Op p M, y ≠ 1 → ∃ c ∈ JG ⊓ Cen z, c * x * c⁻¹ = y := by
    rw [hPA]
    intro x hx hx1 y hy hy1
    obtain ⟨j, hjJ, hjz, hjxy⟩ := htrans x hx hx1 y hy hy1
    exact ⟨(j : G), ⟨⟨j, hjJ, rfl⟩, hjz⟩, hjxy⟩
  have hel'' : IsElementaryAbelian p ↥(Op p M) := by
    rw [hPA]
    exact hel'
  have hcard'' : Nat.card ↥(Op p M) = p ^ (2 * n) := by
    rw [hPA]
    exact hcard'
  have hMJ : M ≤ normalizer (JG : Set G) :=
    hTail G z k S M p hC JG n hJGq hzJG hnoc hn hLieG hPJ hel'' hcard'' hPcz htransG
  have hJGN : JG ≤ N := Subgroup.map_subtype_le _
  have hNJ : N ≤ normalizer (JG : Set G) := by
    have key : ∀ m ∈ N, ∀ g ∈ JG, m * g * m⁻¹ ∈ JG := by
      rintro m hm _ ⟨g, hg, rfl⟩
      refine ⟨⟨m, hm⟩ * g * ⟨m, hm⟩⁻¹, ?_, rfl⟩
      exact (mem_normalizer_iff.mp (hJn ⟨m, hm⟩) g).mp hg
    intro m hm
    rw [mem_normalizer_iff]
    intro g
    exact ⟨key m hm g, fun hg => by simpa [mul_assoc] using key m⁻¹ (N.inv_mem hm) _ hg⟩
  have hJGne : JG ≠ ⊥ := by
    intro hb
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hJGq
    exact (Subgroup.nontrivial_iff_ne_bot JG).mp hnt hb
  have hNJeq : normalizer (JG : Set G) = N := normalizer_eq_of_normalized9 hC h.coatom hJGne hJGN hNJ
  have hMN : M ≤ N := hNJeq ▸ hMJ
  have hMeq : M = N := by
    by_contra hne
    exact h.coatom.1 (hC.coatom.2 N (lt_of_le_of_ne hMN hne))
  apply hnot
  rw [← hMeq]
  exact hC.fstar

end Final

end L915

theorem prop9_5caseC_of_tail (hNo : NoL3Overgroup) (hTail : Prop9_5Tail) : Prop9_5CaseC := by
  intro G _ _ z k S M p hC N A B h hO2 hnot hAE hcC
  exact L915.caseC_false_of_tail hNo hTail hC h hO2 hnot hAE hcC

theorem prop9_5core_of_43E_tail (h43E : Prop4_3E) (hNo : NoL3Overgroup) (hTail : Prop9_5Tail) :
    Prop9_5Core :=
  prop9_5core_of_43E h43E ig_5_12_thm (prop9_5caseC_of_tail hNo hTail)

theorem lemma9_15_of_43E (h43E : Prop4_3E) (hNo : NoL3Overgroup) (hTail : Prop9_5Tail)
    (h911 : Prop9_11Core) : Lemma9_15 :=
  lemma9_15_of_cores (prop9_5core_of_43E_tail h43E hNo hTail) h911

end CFSG.GH74.GLS.Stage2.Bender.Thm2

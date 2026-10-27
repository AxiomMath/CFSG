module

public import CFSG.ClassicalInvolution.Q3.Q3T6BDiagSub
public import CFSG.ClassicalInvolution.Q3.Q3T6BLAut
public import CFSG.ClassicalInvolution.Asc77.AscFusionR11
public import CFSG.ClassicalInvolution.Asc77.AscL62Lem33
public import CFSG.ClassicalInvolution.Asc77.AscSixZW
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.AschTight.C195Wreath
public import CFSG.ClassicalInvolution.AschTight.Thm6Tight
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.Q3.Q3T6BOddFix
public import CFSG.ClassicalInvolution.Q3.Q3T6BOuter
public import CFSG.ClassicalInvolution.Q3.Q3T6BSym
public import CFSG.ClassicalInvolution.Q3.Q3T6BTrivEx
public import CFSG.ClassicalInvolution.Q3.Q3TNZ
public import CFSG.ClassicalInvolution.Uniform.U4Class
public import CFSG.ClassicalInvolution.Uniform.U4Resid
public import CFSG.ClassicalInvolution.Uniform.UBranchProof
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.Goldschmidt.StatementsX
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Outer
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Walter.J1
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
public import Certificates.Certificate110
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4
open scoped commutatorElement MatrixGroups

variable {F : Type} [Group F] [Finite F]

theorem isPGroup_two_zpowers_of_pow_two_pow {g : F} {k : ℕ} (h : g ^ 2 ^ k = 1) :
    IsPGroup 2 (Subgroup.zpowers g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_card, Nat.card_zpowers]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
  exact ⟨j, hj⟩

theorem twinProd_le_centralizer {K J : Subgroup F} {t : F} (hJ : Mem3 J t)
    (htK : ∀ k ∈ K, k * t = t * k) : twinProd K J ≤ Subgroup.centralizer ({t} : Set F) :=
  iSup₂_le fun _ hL => (mem3_of_mem_twinClass hJ htK hL).le_centralizer

section Core

variable {X Y : Subgroup F} {x y : F}

theorem diag_pow_of_mem (hs : Swap X x y) (hex : ExAt x) {q : F} (hq : q ∈ X) (n : ℕ) :
    diag y (q ^ n) = diag y q ^ n := by
  have := map_pow (diagHom X y (hs.comm_twin hex)) (⟨q, hq⟩ : ↥X) n
  simpa [diagHom] using this

theorem diag_dichotomy (hs : Swap X x y) (hxex : ExAt x) (hyex : ExAt y) (hY : Mem3 Y y)
    (hxY : x ∈ Subgroup.normalizer (Y : Set F)) (hnt : ¬ ∀ j ∈ Y, ⁅x, j⁆ ∈ oddCoreOf Y) :
    (∀ q ∈ X, diag y q ∈ Subgroup.normalizer (Y : Set F) ∧
        ∀ k ∈ Y, ⁅diag y q, k⁆ ∈ oddCoreOf Y) ∨
      (∀ q ∈ X, q * q = x → diag y q ∈ twinProd (diagGroupOf hs hxex) Y) := by
  classical
  set Δ : Subgroup F := diagGroupOf hs hxex with hΔ
  have hc := hs.comm_twin hxex
  have hx2 : x * x = 1 := hs.member.mul_self
  have hOY : oddCoreOf Y = ⊥ := Mem3.oddCoreOf_eq_bot hY hyex
  have hnt' : ∃ j ∈ Y, x * j ≠ j * x := by
    by_contra hcon
    push Not at hcon
    apply hnt
    intro j hj
    rw [hOY, Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcon j hj)
  have htK : ∀ k ∈ Δ, k * y = y * k := fun k hk => diagGroupOf_comm_y hs hxex hk
  have hzK : ∀ k ∈ Δ, k * x = x * k := fun k hk => diagGroupOf_comm_x hs hxex hk
  set A : Subgroup F := twinProd Δ Y ⊓ Subgroup.centralizer ({x} : Set F) with hA
  have hA2 : IsPGroup 2 A := isPGroup_twinProd_centralizer hY htK hyex hx2 hxY hzK hnt'
  have hKA : Δ ≤ Subgroup.normalizer (A : Set F) := le_normalizer_twinProd_inf_centralizer hzK
  have hΔC : Δ ≤ Subgroup.centralizer ({x} : Set F) ⊓ Subgroup.centralizer ({y} : Set F) :=
    fun k hk => ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hzK k hk),
      Subgroup.mem_centralizer_singleton_iff.mpr (htK k hk)⟩
  have hAC : A ≤ Subgroup.centralizer ({x} : Set F) ⊓ Subgroup.centralizer ({y} : Set F) :=
    fun a ha => ⟨ha.2, twinProd_le_centralizer hY htK ha.1⟩
  have hsubH : IsSubnormal Δ
      (Subgroup.centralizer ({x} : Set F) ⊓ Subgroup.centralizer ({y} : Set F)) :=
    isSubnormal_diagGroupOf hs hxex
  have hsub : IsSubnormal Δ (Δ ⊔ A) :=
    isSubnormal_of_le_of_le hsubH (sup_le hΔC hAC) le_sup_left
  have hM : ∀ m ∈ Δ ⊔ A, ∃ k ∈ Δ, ∃ a ∈ A, m = k * a := by
    intro m hm
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Δ A hKA] at hm
    obtain ⟨k, hk, a, ha, hka⟩ := hm
    exact ⟨k, hk, a, ha, hka.symm⟩
  have hAN : A ≤ Subgroup.normalizer (Δ : Set F) :=
    subnormal_odd_normalizer (diagGroupOf_le_closure_odd hs hxex) hA2 hsub le_sup_right hM
  by_cases hex4 : ∃ q ∈ X, q * q = x ∧ diag y q ∈ A
  ·
    right
    obtain ⟨q₀, hq₀X, hq₀2, hq₀A⟩ := hex4
    intro q hqX hq2
    obtain ⟨a, haX, hacon⟩ := Mem3.exists_conj_in_member hs.member hq₀X hqX hq₀2 hq2
    have hd : diag y q = diag y a * diag y q₀ * (diag y a)⁻¹ := by
      rw [← hacon]
      exact diag_conj_of_mem hs hxex haX hq₀X
    have hmem : diag y q ∈ A := by
      rw [hd]
      exact (Subgroup.mem_normalizer_iff.mp (hKA (diag_mem_diagGroupOf hs hxex haX)) _).mp hq₀A
    exact hmem.1
  ·
    left
    push Not at hex4
    have hcomm : ∀ g ∈ Δ, Odd (orderOf g) → ∀ a ∈ twinProd Δ Y ⊓ Subgroup.centralizer ({x} : Set F),
        g * a = a * g := by
      intro g hg hgodd a ha
      obtain ⟨c, hcdef⟩ : ∃ c : F, c = g * a * g⁻¹ * a⁻¹ := ⟨_, rfl⟩
      have hcΔ : c ∈ Δ := by
        have h1 : a * g⁻¹ * a⁻¹ ∈ Δ :=
          (Subgroup.mem_normalizer_iff.mp (hAN ha) g⁻¹).mp (Δ.inv_mem hg)
        have : c = g * (a * g⁻¹ * a⁻¹) := by rw [hcdef]; group
        rw [this]
        exact Δ.mul_mem hg h1
      have hcA : c ∈ A := by
        have h1 : g * a * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hKA hg) a).mp ha
        rw [hcdef]
        exact A.mul_mem h1 (A.inv_mem ha)
      obtain ⟨q', hq'X, hq'⟩ := (mem_diagGroupOf_iff hs hxex).mp hcΔ
      have hc2 : IsPGroup 2 (Subgroup.zpowers c) := hA2.to_le (Subgroup.zpowers_le.mpr hcA)
      obtain ⟨m, hm⟩ := hc2.exists_card_eq
      rw [Nat.card_zpowers] at hm
      have hcm : c ^ 2 ^ m = 1 := by rw [← hm]; exact pow_orderOf_eq_one c
      have hq'm : diag y (q' ^ 2 ^ m) = 1 := by
        rw [diag_pow_of_mem hs hxex hq'X, ← hq']
        exact hcm
      have hq'2 : IsPGroup 2 (Subgroup.zpowers q') := by
        refine isPGroup_two_zpowers_of_pow_two_pow (k := m + 1) ?_
        rcases diag_eq_one hs hxex (X.pow_mem hq'X _) hq'm with h1 | h1
        · rw [pow_succ, pow_mul, h1, one_pow]
        · rw [pow_succ, pow_mul, h1, pow_two, hx2]
      have hq'4 : q' ^ 4 = 1 := hs.member.pow_four_of_isPGroup hq'X hq'2
      have hsq : q' * q' = 1 ∨ q' * q' = x := by
        have h1 : (q' * q') * (q' * q') = 1 := by
          rw [← hq'4, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
        exact hs.member.isUniqueInvolution.unique (q' * q') (X.mul_mem hq'X hq'X) h1
      have hc1 : c = 1 := by
        rcases hsq with h1 | h1
        · have hd1 : diag y q' = 1 := by
            rcases hs.member.isUniqueInvolution.unique q' hq'X h1 with h2 | h2
            · rw [h2]
              simp [diag]
            · rw [h2]
              unfold diag
              have : y * x * y⁻¹ = x := by rw [hs.comm]; group
              rw [this, hx2]
          rw [hq', hd1]
        · exact absurd (hq' ▸ hcA) (hex4 q' hq'X h1)
      have key : g * a * g⁻¹ = a := by
        have : g * a * g⁻¹ * a⁻¹ = 1 := by rw [← hcdef]; exact hc1
        exact mul_inv_eq_one.mp this
      calc g * a = (g * a * g⁻¹) * g := by group
        _ = a * g := by rw [key]
    have hNY : ∀ g ∈ Δ, Odd (orderOf g) → g ∈ Subgroup.normalizer (Y : Set F) := fun g hg hgodd =>
      odd_mem_normalizer_of_centralizes hY hyex hx2 hxY hnt htK hzK hcomm hg hgodd
    have hΔNY : Δ ≤ Subgroup.normalizer (Y : Set F) :=
      (diagGroupOf_le_closure_odd hs hxex).trans
        ((Subgroup.closure_le _).mpr fun g hg => hNY g hg.1 hg.2)
    obtain ⟨ρ, hρ⟩ := exists_action hY
    have hρx : ρ ⟨x, hxY⟩ ≠ 1 := fun h1 => hnt ((hρ ⟨x, hxY⟩).mp h1)
    have hS : ∀ g ∈ diagOddSet X y,
        ∃ hg : g ∈ Subgroup.normalizer (Y : Set F), ρ ⟨g, hg⟩ = 1 := by
      rintro g ⟨s, hsX, p, k, hp, hp2, hsp, rfl⟩
      have hgN : diag y s ∈ Subgroup.normalizer (Y : Set F) :=
        hΔNY (diag_mem_diagGroupOf hs hxex hsX)
      obtain ⟨hgx, -⟩ := diag_comm_both hs hxex hsX
      exact ⟨hgN, act_trivial_of_odd ρ hxY hx2 hρx hgN hgx (odd_orderOf_diag hc hsX hp hp2 hsp)⟩
    intro q hqX
    have hmem : diag y q ∈ Subgroup.closure (diagOddSet X y) :=
      diag_mem_closure_odd hs hxex hqX
    obtain ⟨hdN, hd1⟩ := closure_act_trivial ρ hS _ hmem
    exact ⟨hdN, (hρ ⟨_, hdN⟩).mp hd1⟩

end Core

end CFSG.ClassicalInvolution.Q3.Q3T6B

module

public import CFSG.LocalAnalysis.EvenBN.U5.LinLayer
public import CFSG.LocalAnalysis.SeitzReduction.PerfectCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup
import CFSG.Holt.General.Simple
import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofNineC
import CFSG.LocalAnalysis.EvenBN.U5.LinOrders
import CFSG.LocalAnalysis.EvenBN.Common.TwoElementary
import CFSG.Goldschmidt.Steps.LemmaXCore
import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductPerfect

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups commutatorElement

namespace LinCase

section GenericT1

theorem card_range_dvd_of_ker_le {X Q Q₁ : Type*} [Group X] [Finite X] [Group Q] [Group Q₁]
    (θ : X →* Q) (ν : X →* Q₁) (h : θ.ker ≤ ν.ker) :
    Nat.card ν.range ∣ Nat.card θ.range := by
  have h1 := Subgroup.card_ker_mul_card_range θ
  have h2 := Subgroup.card_ker_mul_card_range ν
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le h
  have hpos : 0 < Nat.card θ.ker := Nat.card_pos
  refine ⟨c, ?_⟩
  have : Nat.card θ.ker * Nat.card θ.range = Nat.card θ.ker * (Nat.card ν.range * c) := by
    rw [h1, ← h2, hc]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem odd_normal_eq_bot_of_simple {Q : Type*} [Group Q] [Finite Q] {P N : Subgroup Q}
    (hP : IsSimpleGroup P) (hnab : ∃ x y : P, x * y ≠ y * x) (hNP : N ≤ P)
    (hN : ∀ π ∈ P, ∀ n ∈ N, π * n * π⁻¹ ∈ N) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have hnorm : (N.subgroupOf P).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hN (g : Q) g.2 n hn
  haveI := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf P) with h0 | h1
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hNP hx⟩ : P) ∈ N.subgroupOf P := hx
    rw [h0, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  · exfalso
    have hNP' : N = P := by
      apply le_antisymm hNP
      intro x hx
      have : (⟨x, hx⟩ : P) ∈ N.subgroupOf P := by rw [h1]; exact Subgroup.mem_top _
      exact this
    subst hNP'
    have hev := CFSG.Holt.General.even_card_of_isSimpleGroup hnab
    exact (Nat.not_even_iff_odd.2 hodd) hev

theorem odd_normal_eq_bot_of_prod {Q : Type*} [Group Q] [Finite Q] {D₁ D₂ D N : Subgroup Q}
    (h1 : IsSimpleGroup D₁) (h2 : IsSimpleGroup D₂) (hn1 : ∃ x y : D₁, x * y ≠ y * x)
    (hn2 : ∃ x y : D₂, x * y ≠ y * x) (hD : D₁ ⊔ D₂ = D) (hc : ⁅D₁, D₂⁆ = ⊥)
    (hCD : centralizer (D : Set Q) = ⊥) (hND : N ≤ D) (hN : ∀ x ∈ D, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  rcases sec39c_normal_in_prod h1 h2 hD hc hCD hND hN with h0 | hle | hle
  · exact h0
  · exfalso
    have hev := CFSG.Holt.General.even_card_of_isSimpleGroup hn1
    have hdvd : Nat.card D₁ ∣ Nat.card N := Subgroup.card_dvd_of_le hle
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 ((even_iff_two_dvd.1 hev).trans hdvd))
  · exfalso
    have hev := CFSG.Holt.General.even_card_of_isSimpleGroup hn2
    have hdvd : Nat.card D₂ ∣ Nat.card N := Subgroup.card_dvd_of_le hle
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 ((even_iff_two_dvd.1 hev).trans hdvd))

end GenericT1

end LinCase

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

section Layer

variable (hl : d.LinCtx)
include hl

theorem lin_centralizer_layer :
    centralizer ((CFSG.layer (d.s38dH ⧸ d.s38dO) : Subgroup (d.s38dH ⧸ d.s38dO)) :
      Set (d.s38dH ⧸ d.s38dO)) = ⊥ := by
  obtain ⟨hout, -⟩ := hl.hyp.sec3_3_two hl.gms
  obtain ⟨⟨-, -, -, hnc, hcent, -, -⟩, -⟩ := hout
  rw [← hnc]
  exact hcent

theorem lin_outer_layer_solvable :
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      ↥(CFSG.layer (d.s38dH ⧸ d.s38dO))) := by
  have hf : 1 ≤ f := by have := hl.hyp.two_le; omega
  obtain ⟨K', _, _, _, -, ⟨e⟩⟩ :=
    exists_mulEquiv_projectiveSL_three_sq hf (lin_layer_facts hl).2.1
  exact CFSG.SeitzReduction.LinearPilot.isSolvable_outer_of_mulEquiv (by norm_num) e

theorem lin_perfect_le_layer {P : Subgroup (d.s38dH ⧸ d.s38dO)} (hP : ⁅P, P⁆ = P) :
    P ≤ CFSG.layer (d.s38dH ⧸ d.s38dO) := by
  haveI : (CFSG.layer (d.s38dH ⧸ d.s38dO)).Characteristic :=
    CFSG.LocalCores.layer_characteristic
  refine CFSG.SeitzReduction.perfect_le_of_isSolvable_outer (lin_outer_layer_solvable hl) le_top
    Subgroup.le_normalizer_of_normal ?_ hP le_top
  rw [inf_top_eq, lin_centralizer_layer hl]
  infer_instance

theorem lin_X_le_M₂ {X : Subgroup G} (hXH : X ≤ d.s38dH) (hX : ⁅X, X⁆ = X) : X ≤ d.M₂ := by
  have hM' : (d.M₂.subgroupOf d.s38dH).map d.s38dθ = CFSG.layer (d.s38dH ⧸ d.s38dO) :=
    (lin_layer_facts hl).2.2
  set X' : Subgroup ↥d.s38dH := X.subgroupOf d.s38dH with hX'
  have hX'p : ⁅X', X'⁆ = X' := s38d_perfect_subgroupOf hXH hX
  have hXθp : ⁅X'.map d.s38dθ, X'.map d.s38dθ⁆ = X'.map d.s38dθ := by
    rw [← Subgroup.map_commutator, hX'p]
  have hle : X'.map d.s38dθ ≤ CFSG.layer (d.s38dH ⧸ d.s38dO) := lin_perfect_le_layer hl hXθp
  have hMC : ∀ m ∈ X', ∃ n ∈ d.M₂.subgroupOf d.s38dH, n⁻¹ * m ∈ d.s38dO := by
    intro m hm
    have h1 : d.s38dθ m ∈ (d.M₂.subgroupOf d.s38dH).map d.s38dθ := by
      rw [hM']; exact hle ⟨m, hm, rfl⟩
    obtain ⟨n, hn, hnm⟩ := h1
    refine ⟨n, hn, ?_⟩
    have : d.s38dθ (n⁻¹ * m) = 1 := by rw [map_mul, map_inv, hnm, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 this
  haveI := s38d_M₂_normal d
  haveI : Group.IsSolvable d.s38dO :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (GMSK.odd_card_standardComponentOddCore _)
  have hres : X' ≤ d.M₂.subgroupOf d.s38dH :=
    CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProduct.perfect_le_of_forall_inv_mul_mem
      Subgroup.le_normalizer_of_normal hX'p Subgroup.le_normalizer_of_normal hMC
  intro x hx
  exact hres (show (⟨x, hXH hx⟩ : d.s38dH) ∈ X' from hx)

theorem lin_M₂_le_X
    (hO : ∀ o : ↥d.s38dH, o ∈ d.s38dO → ∀ n ∈ d.N₂, (o : G) * n = n * (o : G))
    {X : Subgroup G} (hXH : X ≤ d.s38dH) (hX : ⁅X, X⁆ = X)
    (hθ : (X.subgroupOf d.s38dH).map d.s38dθ = CFSG.layer (d.s38dH ⧸ d.s38dO)) : d.M₂ ≤ X := by
  have hM' : (d.M₂.subgroupOf d.s38dH).map d.s38dθ = CFSG.layer (d.s38dH ⧸ d.s38dO) :=
    (lin_layer_facts hl).2.2
  have hXM : X ≤ d.M₂ := lin_X_le_M₂ hl hXH hX
  set X' : Subgroup ↥d.s38dH := X.subgroupOf d.s38dH with hX'
  set M' : Subgroup ↥d.s38dH := d.M₂.subgroupOf d.s38dH with hM'def
  have hX'M' : X' ≤ M' := fun x hx => hXM hx
  have hN'perf : ⁅d.N₂.subgroupOf d.s38dH, d.N₂.subgroupOf d.s38dH⁆ = d.N₂.subgroupOf d.s38dH :=
    s38d_perfect_subgroupOf d.N₂_le_centralizer_I₂ (s38d_N₂_perfect hl.hyp)
  have hCent : ∀ m ∈ M', ∀ o ∈ d.s38dO, o * m = m * o := by
    haveI : (centralizer (d.s38dO : Set ↥d.s38dH)).Normal := Subgroup.normal_centralizer
    have hN' : (d.N₂.subgroupOf d.s38dH : Set ↥d.s38dH) ⊆
        (centralizer (d.s38dO : Set ↥d.s38dH) : Set ↥d.s38dH) := by
      intro n hn
      rw [SetLike.mem_coe, mem_centralizer_iff]
      intro o ho
      exact Subtype.ext (hO o ho n hn)
    have hM'C : M' ≤ centralizer (d.s38dO : Set ↥d.s38dH) := by
      rw [hM'def, s38d_M₂_subgroupOf]
      exact normalClosure_le_normal hN'
    intro m hm o ho
    exact mem_centralizer_iff.1 (hM'C hm) o ho
  have hM'perf : ⁅M', M'⁆ = M' := by
    rw [hM'def, s38d_M₂_subgroupOf]
    exact s38d_normalClosure_perfect hN'perf
  have hMC : ∀ m ∈ M', ∃ x ∈ X', x⁻¹ * m ∈ d.s38dO := by
    intro m hm
    have h1 : d.s38dθ m ∈ X'.map d.s38dθ := by
      rw [hθ, ← hM']; exact ⟨m, hm, rfl⟩
    obtain ⟨x, hx, hxm⟩ := h1
    refine ⟨x, hx, ?_⟩
    have : d.s38dθ (x⁻¹ * m) = 1 := by rw [map_mul, map_inv, hxm, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 this
  have hMX : M' ≤ X' := by
    rw [← hM'perf, commutator_le]
    intro a ha b hb
    obtain ⟨x₁, hx₁, hw₁⟩ := hMC a ha
    obtain ⟨x₂, hx₂, hw₂⟩ := hMC b hb
    have ha' : a = x₁ * (x₁⁻¹ * a) := by group
    have hb' : b = x₂ * (x₂⁻¹ * b) := by group
    have hw₁M : x₁⁻¹ * a ∈ M' := mul_mem (inv_mem (hX'M' hx₁)) ha
    have hw₂M : x₂⁻¹ * b ∈ M' := mul_mem (inv_mem (hX'M' hx₂)) hb
    have h12 : (x₁⁻¹ * a) * x₂ = x₂ * (x₁⁻¹ * a) := hCent x₂ (hX'M' hx₂) _ hw₁
    have h21 : (x₂⁻¹ * b) * x₁ = x₁ * (x₂⁻¹ * b) := hCent x₁ (hX'M' hx₁) _ hw₂
    have hww : (x₁⁻¹ * a) * (x₂⁻¹ * b) = (x₂⁻¹ * b) * (x₁⁻¹ * a) := hCent _ hw₂M _ hw₁
    rw [ha', hb', s38d_commutator_mul_central h12 h21 hww]
    exact s38d_commutator_le_self X' (commutator_mem_commutator hx₁ hx₂)
  intro x hx
  exact hMX (show (⟨x, s38d_M₂_le_H d hx⟩ : ↥d.s38dH) ∈ M' from hx)

theorem lin_theta_X_eq (hi : d.Sec38Input) (ho : d.Sec38Outcome)
    (hO : ∀ o : ↥d.s38dH, o ∈ d.s38dO → ∀ n ∈ d.N₂, (o : G) * n = n * (o : G))
    {X : Subgroup G} (hXH : X ≤ d.s38dH) (hXL : X ≤ d.L₂) (hX : ⁅X, X⁆ = X) (hN₂X : d.N₂ ≤ X)
    (hEX : d.E ⊔ X = d.L₂) :
    (X.subgroupOf d.s38dH).map d.s38dθ = CFSG.layer (d.s38dH ⧸ d.s38dO) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf2 : 2 ≤ f := hl.hyp.two_le
  have hΛ := lin_layer_facts hl
  have hXN : X ≤ normalizer (d.E : Set G) := hXL.trans d.L₂_le_normalizer_E
  set θX : ↥X →* d.s38dH ⧸ d.s38dO := d.s38dθ.comp (Subgroup.inclusion hXH) with hθX
  set νX : ↥X →* Bar d.E ⧸ OE d :=
    (QuotientGroup.mk' (OE d)).comp ((proj d.E).comp (Subgroup.inclusion hXN)) with hνX
  have hθrange : θX.range = (X.subgroupOf d.s38dH).map d.s38dθ := by
    ext y
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨⟨x, hXH hx⟩, hx, rfl⟩
    · rintro ⟨⟨x, hxH⟩, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hX'p : ⁅X.subgroupOf d.s38dH, X.subgroupOf d.s38dH⁆ = X.subgroupOf d.s38dH :=
    s38d_perfect_subgroupOf hXH hX
  have hθle : θX.range ≤ CFSG.layer (d.s38dH ⧸ d.s38dO) := by
    rw [hθrange]
    exact lin_perfect_le_layer hl (by rw [← Subgroup.map_commutator, hX'p])
  suffices hmain : θX.range = CFSG.layer (d.s38dH ⧸ d.s38dO) by rw [← hθrange]; exact hmain
  obtain ⟨ht, hout⟩ := ho
  obtain ⟨⟨-, -, hJle, hnc, hcent, halt, -⟩, hsimple⟩ := hout
  set J : Subgroup (Bar d.E ⧸ OE d) := (bar d.E d.N₂).map (QuotientGroup.mk' (OE d)) with hJ
  have hlayX : CFSG.layer (Bar d.E ⧸ OE d) ≤ νX.range := by
    rw [← hnc]
    refine (s38d_normalClosure_le d).trans ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨x₀, rfl⟩ := proj_surjective z
    have hl₂ : (x₀ : G) ∈ d.L₂ := (mem_bar_iff d.E_le_L₂ x₀).1 hz
    rw [← hEX] at hl₂
    obtain ⟨e, he, x, hx, hex⟩ := Common.exists_mul_of_le_normalizer hXN (x₀ : G) hl₂
    refine ⟨⟨x, hx⟩, ?_⟩
    have hproj : proj d.E ⟨x, hXN hx⟩ = proj d.E x₀ := by
      rw [proj_eq_proj_iff]
      show x⁻¹ * (x₀ : G) ∈ d.E
      rw [hex]
      have h1 := (mem_normalizer_iff.1 (inv_mem (hXN hx)) e).1 he
      have e1 : x⁻¹ * (e * x) = x⁻¹ * e * x⁻¹⁻¹ := by group
      rw [e1]
      exact h1
    exact congrArg (QuotientGroup.mk' (OE d)) hproj
  have hkerodd : Odd (Nat.card θX.ker) := by
    have hO' : Odd (Nat.card d.s38dO) := GMSK.odd_card_standardComponentOddCore _
    let ψ : θX.ker →* d.s38dO :=
      { toFun := fun m => ⟨⟨(m.1 : G), hXH m.1.2⟩, (QuotientGroup.eq_one_iff _).1 m.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hinj : Function.Injective ψ := by
      intro a b hab
      have h2 : ((a.1 : ↥X) : G) = ((b.1 : ↥X) : G) :=
        congrArg (fun z : d.s38dO => (((z : d.s38dH)) : G)) hab
      exact Subtype.ext (Subtype.ext h2)
    exact Odd.of_dvd_nat hO' (Subgroup.card_dvd_of_injective ψ hinj)
  set N : Subgroup (Bar d.E ⧸ OE d) := θX.ker.map νX with hN
  have hNodd : Odd (Nat.card N) := Odd.of_dvd_nat hkerodd (Subgroup.card_map_dvd θX.ker νX)
  have hNnorm : ∀ π ∈ νX.range, ∀ n ∈ N, π * n * π⁻¹ ∈ N := by
    rintro _ ⟨x₀, rfl⟩ _ ⟨k, hk, rfl⟩
    refine ⟨x₀ * k * x₀⁻¹, ?_, by simp⟩
    exact (MonoidHom.normal_ker θX).conj_mem k hk x₀
  have hlayN : ∀ π ∈ CFSG.layer (Bar d.E ⧸ OE d), ∀ n ∈ N, π * n * π⁻¹ ∈ N :=
    fun π hπ n hn => hNnorm π (hlayX hπ) n hn
  haveI hlaynormal : (CFSG.layer (Bar d.E ⧸ OE d)).Normal :=
    haveI : (CFSG.layer (Bar d.E ⧸ OE d)).Characteristic := CFSG.LocalCores.layer_characteristic
    inferInstance
  have hcentlay : centralizer ((CFSG.layer (Bar d.E ⧸ OE d) : Subgroup (Bar d.E ⧸ OE d)) :
      Set (Bar d.E ⧸ OE d)) = ⊥ := by rw [← hnc]; exact hcent
  have hbot : N ⊓ CFSG.layer (Bar d.E ⧸ OE d) = ⊥ := by
    have hNP : N ⊓ CFSG.layer (Bar d.E ⧸ OE d) ≤ CFSG.layer (Bar d.E ⧸ OE d) := inf_le_right
    have hnorm : ∀ π ∈ CFSG.layer (Bar d.E ⧸ OE d), ∀ n ∈ N ⊓ CFSG.layer (Bar d.E ⧸ OE d),
        π * n * π⁻¹ ∈ N ⊓ CFSG.layer (Bar d.E ⧸ OE d) := fun π hπ n hn =>
      Subgroup.mem_inf.2 ⟨hlayN π hπ n (Subgroup.mem_inf.1 hn).1,
        mul_mem (mul_mem hπ (Subgroup.mem_inf.1 hn).2) (inv_mem hπ)⟩
    have hoddN' : Odd (Nat.card (N ⊓ CFSG.layer (Bar d.E ⧸ OE d) : Subgroup _)) :=
      Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le inf_le_left)
    rcases halt.or with hA | hB
    · obtain ⟨hs, hnab, -, -⟩ := hA
      rw [hnc] at hs hnab
      exact LinCase.odd_normal_eq_bot_of_simple hs hnab hNP hnorm hoddN'
    · obtain ⟨D₁, D₂, -, -, -, hs1, hn1, hs2, hn2, hsup, -, hcomm, -, -, -, -, -⟩ := hB
      exact LinCase.odd_normal_eq_bot_of_prod hs1 hs2 hn1 hn2 (hsup.trans hnc) hcomm hcentlay hNP
        hnorm hoddN'
  have hNbot : N = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    have hcent' : n ∈ centralizer ((CFSG.layer (Bar d.E ⧸ OE d) : Subgroup (Bar d.E ⧸ OE d)) :
        Set (Bar d.E ⧸ OE d)) := by
      rw [mem_centralizer_iff]
      intro π hπ
      have h1 : π * n * π⁻¹ * n⁻¹ ∈ N ⊓ CFSG.layer (Bar d.E ⧸ OE d) := by
        refine Subgroup.mem_inf.2 ⟨mul_mem (hlayN π hπ n hn) (inv_mem hn), ?_⟩
        have h2 : n * π⁻¹ * n⁻¹ ∈ CFSG.layer (Bar d.E ⧸ OE d) :=
          hlaynormal.conj_mem π⁻¹ (inv_mem hπ) n
        have e : π * n * π⁻¹ * n⁻¹ = π * (n * π⁻¹ * n⁻¹) := by group
        rw [e]
        exact mul_mem hπ h2
      rw [hbot, Subgroup.mem_bot] at h1
      calc π * n = (π * n * π⁻¹ * n⁻¹) * (n * π) := by group
        _ = n * π := by rw [h1, one_mul]
    rw [hcentlay] at hcent'
    exact hcent'
  have hkerle : θX.ker ≤ νX.ker := by
    intro k hk
    have : νX k ∈ N := ⟨k, hk, rfl⟩
    rw [hNbot, Subgroup.mem_bot] at this
    exact this
  have hdvd1 : Nat.card (CFSG.layer (Bar d.E ⧸ OE d)) ∣ Nat.card θX.range :=
    (Subgroup.card_dvd_of_le hlayX).trans (LinCase.card_range_dvd_of_ker_le θX νX hkerle)
  have hdvd2 : Nat.card θX.range ∣ Nat.card (CFSG.layer (d.s38dH ⧸ d.s38dO)) :=
    Subgroup.card_dvd_of_le hθle
  rcases halt.or with hA | hB
  ·
    have hsimp : IsSimpleGroup ↥(CFSG.layer (Bar d.E ⧸ OE d)) := by
      obtain ⟨hs, -, -, -⟩ := hA
      rwa [hnc] at hs
    have hLie : LieModel ↥(CFSG.layer (Bar d.E ⧸ OE d)) .PSL 3 2 (2 * f) := (hsimple hsimp).1
    have e1 := LinCase.card_lieModel_PSL3 hLie
    have e2 := LinCase.card_lieModel_PSL3 hΛ.2.1
    have hpos : 0 < Nat.gcd 3 (2 ^ (2 * f) - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hcard : Nat.card (CFSG.layer (Bar d.E ⧸ OE d)) =
        Nat.card (CFSG.layer (d.s38dH ⧸ d.s38dO)) :=
      Nat.eq_of_mul_eq_mul_right hpos (e1.trans e2.symm)
    apply Subgroup.eq_of_le_of_card_ge hθle
    rw [← hcard]
    exact Nat.le_of_dvd Nat.card_pos hdvd1
  ·
    exfalso
    obtain ⟨D₁, D₂, -, -, -, hs1, hn1, hs2, hn2, hsup, -, hcomm, -, -, ψ, -, -⟩ := hB
    have hJcard2 : Nat.card ↥(normalClosure (J : Set (Bar d.E ⧸ OE d))) =
        Nat.card ↥J * Nat.card ↥J := by
      rw [Nat.card_congr ψ.toEquiv, Nat.card_prod]
    have hZ : ∀ z : J, (∀ y : J, z * y = y * z) → z = 1 := by
      intro z hz
      set d₀ : ↥(normalClosure (J : Set (Bar d.E ⧸ OE d))) := ψ.symm (z, 1) with hd₀
      have h1 : ψ d₀ = (z, 1) := ψ.apply_symm_apply _
      have hd₀c : ∀ e : ↥(normalClosure (J : Set (Bar d.E ⧸ OE d))), d₀ * e = e * d₀ := by
        intro e
        apply ψ.injective
        obtain ⟨a, b, hab⟩ : ∃ a b : J, ψ e = (a, b) := ⟨_, _, rfl⟩
        rw [map_mul, map_mul, h1, hab, Prod.mk_mul_mk, Prod.mk_mul_mk, hz a, one_mul, mul_one]
      have hd₀cent : (d₀ : Bar d.E ⧸ OE d) ∈ centralizer ((normalClosure (J : Set (Bar d.E ⧸ OE d)) :
          Subgroup (Bar d.E ⧸ OE d)) : Set (Bar d.E ⧸ OE d)) := by
        rw [mem_centralizer_iff]
        intro e he
        exact congrArg Subtype.val (hd₀c ⟨e, he⟩).symm
      rw [hcent, Subgroup.mem_bot] at hd₀cent
      have hd₀1 : d₀ = 1 := Subtype.ext hd₀cent
      have h2 : ψ d₀ = (1, 1) := by rw [hd₀1, map_one]; rfl
      exact (Prod.mk.inj (h1.symm.trans h2)).1
    obtain ⟨e⟩ := s38d_quot_equiv_image (QuotientGroup.mk' (OE d)) (by
        rw [QuotientGroup.ker_mk']; exact GMSK.odd_card_standardComponentOddCore _)
      hi.quasisimple (by
        intro hodd
        exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2
          (CFSG.Goldschmidt.LemmaX.two_dvd_card_of_isQuasisimple hi.quasisimple)))
      hZ
    have hJcard : Nat.card ↥J = Nat.card (↥(bar d.E d.N₂) ⧸ center ↥(bar d.E d.N₂)) :=
      (Nat.card_congr e.toEquiv).symm
    have hU := LinCase.card_lieModel_PSU3 (by omega) hi.model
    have hL := LinCase.card_lieModel_PSL3 hΛ.2.1
    refine LinCase.not_card_sq_dvd hf2 hU hL ?_
    have h3 : Nat.card (CFSG.layer (Bar d.E ⧸ OE d)) =
        Nat.card (↥(bar d.E d.N₂) ⧸ center ↥(bar d.E d.N₂)) ^ 2 := by
      rw [← hnc, hJcard2, hJcard]; ring
    rw [← h3]
    exact hdvd1.trans hdvd2

theorem lin_L₂_eq (hi : d.Sec38Input) (ho : d.Sec38Outcome) (hodd : d.Sec38Odd) :
    d.L₂ = d.E ⊔ d.M₂ := by
  have hI : ∀ x ∈ d.L₂, ∀ i ∈ d.I₂, x⁻¹ * (i * x * i⁻¹) ∈ d.E := fun x hx i hi => by
    have h1 := hodd.comm_le (commutator_mem_commutator (inv_mem hx) hi)
    have e : x⁻¹ * (i * x * i⁻¹) = ⁅x⁻¹, i⁆ := by rw [commutatorElement_def]; group
    rw [e]
    exact h1
  have hO : ∀ o : ↥d.s38dH, o ∈ d.s38dO → ∀ n ∈ d.N₂, (o : G) * n = n * (o : G) :=
    fun o ho n hn => by
      have h1 : (o : G) ∈ d.s38dO.map d.s38dH.subtype := ⟨o, ho, rfl⟩
      exact (mem_centralizer_iff.1 (hodd.oddCore_le h1) n hn).symm
  obtain ⟨X, hXYL, hN₂X, hXp, hEX⟩ := s38d_exists_X hl.gms hl.hyp hI
  have hXH : X ≤ d.s38dH := hXYL.trans inf_le_right
  have hXL : X ≤ d.L₂ := hXYL.trans inf_le_left
  have hθ := lin_theta_X_eq hl hi ho hO hXH hXL hXp hN₂X hEX
  have hMX := lin_M₂_le_X hl hO hXH hXp hθ
  have hXM := lin_X_le_M₂ hl hXH hXp
  apply le_antisymm
  · rw [← hEX]
    exact sup_le_sup_left hXM _
  · exact sup_le d.E_le_L₂ (hMX.trans hXL)

theorem lin_sec38_layer (hi : d.Sec38Input) (ho : d.Sec38Outcome) (hodd : d.Sec38Odd) :
    d.Sec38Layer :=
  ⟨lin_L₂_eq hl hi ho hodd, s38d_V_le hl.gms hl.hyp, s38d_odd ho⟩

end Layer

end Data

end CFSG.LocalAnalysis.EvenBN.U5

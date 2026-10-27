module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Lemma36Init
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.TopStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.ModelCert

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction

structure TopData (G : Type) [Group G] [Finite G] (n : ℕ) (U T : ℕ → Subgroup G) (s : ℕ → G)
    (u x : G) : Prop where
  chain : InCGb G n U T s
  maximal : ∀ m U' T' s', InCGb G m U' T' s' → U' 0 = U 0 → m ≤ n
  base : cqOrd (U 0) = 60
  two_le : 2 ≤ n
  out : Out G (U (n - 1)) u
  xmem : x ∈ U (n - 1)
  xinv : orderOf x = 2
  x240 : Nat.card ↥(U (n - 1) ⊓ centralizer ({x} : Set G)) = 240
  jstar : U (n - 2) = jOf (U (n - 1)) x
  cent : U (n - 1) ⊓ centralizer (jOf (U (n - 1)) x : Set G) = zpowers x
  facts : PropA.Facts (U (n - 1)) u x
  rbc : RbcFacts (U (n - 1)) u x

section Conj

variable {G : Type} [Group G]

theorem conj_conj_eq_self_of_sq_commute {s y : G} (h : s * s * y = y * (s * s)) :
    s * (s * y * s⁻¹) * s⁻¹ = y := by
  calc s * (s * y * s⁻¹) * s⁻¹ = (s * s * y) * (s⁻¹ * s⁻¹) := by group
    _ = (y * (s * s)) * (s⁻¹ * s⁻¹) := by rw [h]
    _ = y := by group

end Conj

section Jstar


variable {G : Type} [Group G] [Finite G] {n : ℕ} {U T : ℕ → Subgroup G} {s : ℕ → G} {u : G}

theorem exists_jstar (hC : InCG G n U T s) (hn : 2 ≤ n) (hOu : Out G (U (n - 1)) u) :
    ∃ x ∈ U (n - 1), orderOf x = 2 ∧ Nat.card ↥(U (n - 1) ⊓ centralizer ({x} : Set G)) = 240 ∧
      U (n - 2) = jOf (U (n - 1)) x ∧
      U (n - 1) ⊓ centralizer (jOf (U (n - 1)) x : Set G) = zpowers x ∧
      PropA.Facts (U (n - 1)) u x ∧ RbcFacts (U (n - 1)) u x := by
  have hi1 : 1 ≤ n - 1 := by omega
  have hin : n - 1 ≤ n := by omega
  have hcomp := hC.links.comp (n - 1) hin
  have helem := hC.links.elem (n - 1) hi1 hin
  have hne : U (n - 1 - 1) ≠ U (n - 1) := fun h => by
    have := hC.inj (n - 1 - 1) (by omega) (n - 1) (by omega) h
    omega
  have hinv : U (n - 1) = (U (n - 1)).map (MulAut.conj (s (n - 1))).toMonoidHom := by
    rcases hC.links.link (n - 1) hi1 hin with ⟨hneq, -⟩ | h
    · exfalso
      have hcomp2 := isCompIn_map_conj_of_mem_normalizer hcomp.2
        (mem_normalizer_centralizer_of_mem_normalizer helem.2.1)
      have hcomm := hcomp.2.commute_of_ne hcomp2 hneq
      refine hC.top.1 (s (n - 1)) (Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun a ha => ?_)
      exact mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm
    · exact h
  have hsN : s (n - 1) ∈ normalizer ((U (n - 1) : Subgroup G) : Set G) :=
    Solomon78.mem_normalizer_iff_map_conj_eq.2 hinv.symm
  obtain ⟨c, hcC, hact⟩ := hOu.exists_mem_centralizer_act_eq hsN
  have hsq : ∀ y ∈ U (n - 1), s (n - 1) * s (n - 1) * y = y * (s (n - 1) * s (n - 1)) :=
    fun y hy => by
      simpa [pow_two] using mem_centralizer_iff.1 (hcomp.2.1 hy) (s (n - 1) ^ 2) helem.2.2.1
  have hc2 : c ^ 2 ∈ zpowers u := by
    have hcX : c ^ 2 ∈ centralizer ((U (n - 1) : Subgroup G) : Set G) := by
      refine mem_centralizer_iff.2 fun y hy => ?_
      have hsy : s (n - 1) * y * (s (n - 1))⁻¹ ∈ U (n - 1) :=
        (Subgroup.mem_normalizer_iff.1 hsN y).1 hy
      have h1 : c * (c * y * c⁻¹) * c⁻¹ = y := by
        calc c * (c * y * c⁻¹) * c⁻¹ = c * (s (n - 1) * y * (s (n - 1))⁻¹) * c⁻¹ := by
              rw [← hact y hy]
          _ = s (n - 1) * (s (n - 1) * y * (s (n - 1))⁻¹) * (s (n - 1))⁻¹ := (hact _ hsy).symm
          _ = y := conj_conj_eq_self_of_sq_commute (hsq y hy)
      have h2 : c * c * y = y * (c * c) := by
        calc c * c * y = (c * (c * y * c⁻¹) * c⁻¹) * (c * c) := by group
          _ = y * (c * c) := by rw [h1]
      rw [pow_two]
      exact h2.symm
    have hS : ∀ S : Sylow 2 (centralizer ((U (n - 1) : Subgroup G) : Set G)), Nat.card S = 2 :=
      hOu.std.card_sylow_eq_two_m12 hOu.m12
    have hcap := hOu.std.centralizer_inf_centralizer_eq_zpowers hS hOu.mem hOu.inv
    rw [← hcap]
    exact Subgroup.mem_inf.2 ⟨hcX, pow_mem hcC 2⟩
  have hc_not : c ∉ zpowers u := by
    intro hcu
    have hcX : c ∈ centralizer ((U (n - 1) : Subgroup G) : Set G) :=
      (Subgroup.zpowers_le.2 hOu.mem) hcu
    refine TLinks.not_le_centralizer_of_inv hC.links hi1 hin hinv hne fun y hy => ?_
    have h0 : y * c = c * y := mem_centralizer_iff.1 hcX y hy
    have h1 : s (n - 1) * y * (s (n - 1))⁻¹ = y := by
      rw [hact y hy, ← h0, mul_inv_cancel_right]
    rw [mem_centralizer_singleton_iff]
    calc y * s (n - 1) = (s (n - 1) * y * (s (n - 1))⁻¹) * s (n - 1) := by rw [h1]
      _ = s (n - 1) * y := by group
  have hQle : U (n - 1 - 1) ≤ U (n - 1) := hC.links.le_of_inv hi1 hin hinv
  have hQs : U (n - 1 - 1) ≤ centralizer ({s (n - 1)} : Set G) := by
    intro q hq
    have h1 := helem.2.2.2.1 hq
    rw [Step.centralizer_sup_zpowers] at h1
    exact h1.2
  have hQc : U (n - 1 - 1) ≤ U (n - 1) ⊓ centralizer ({c} : Set G) := by
    intro q hq
    refine ⟨hQle hq, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : s (n - 1) * q * (s (n - 1))⁻¹ = q := by
      rw [← mem_centralizer_singleton_iff.1 (hQs hq), mul_inv_cancel_right]
    have h2 := hact q (hQle hq)
    rw [h1] at h2
    calc q * c = (c * q * c⁻¹) * c := by rw [← h2]
      _ = c * q := by group
  have hQq := helem.2.2.2.isQuasisimple
  have hQperf : ⁅U (n - 1 - 1), U (n - 1 - 1)⁆ = U (n - 1 - 1) :=
    Subgroup.isPerfect_iff.1 hQq.1
  have hQbot : U (n - 1 - 1) ≠ ⊥ := by
    intro h
    rw [h] at hQq
    obtain ⟨-, -, a, b, hab⟩ := hQq
    exact hab (Subsingleton.elim _ _)
  obtain ⟨x₀, hx₀X, hx₀2, hx₀240⟩ := exists_twoA hOu.m12
  obtain ⟨-, hR₀⟩ :=
    rbcFacts_of_outer hOu.std hOu.m12 hOu.mem hOu.inv hOu.outer hx₀X hx₀2 hx₀240
  rcases hR₀.perfect_cent c hcC hc2 hc_not _ hQc hQperf with hbot | ⟨x, hxX, hx2, hx240, hQx, hcent⟩
  · exact absurd hbot hQbot
  · obtain ⟨hF, hR⟩ :=
      rbcFacts_of_outer hOu.std hOu.m12 hOu.mem hOu.inv hOu.outer hxX hx2 hx240
    refine ⟨x, hxX, hx2, hx240, ?_, hcent, hF, hR⟩
    rw [show n - 2 = n - 1 - 1 by omega]
    exact hQx

end Jstar

section Top


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

theorem exists_topData (hY : SolomonK.Yoshida74Co3K)
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hMcard : Nat.card CFSG.Open.MonsterY443Derived = CFSG.Open.monsterOrder)
    (htop : TopIsM12 G) (hO : Out G L t) :
    ∃ (n : ℕ) (U T : ℕ → Subgroup G) (s : ℕ → G) (u x : G), TopData G n U T s u x := by
  obtain ⟨x₀, hx₀L, hx₀2, hx₀240⟩ := exists_twoA hO.m12
  obtain ⟨hF₀, -⟩ := rbcFacts_of_outer hO.std hO.m12 hO.mem hO.inv hO.outer hx₀L hx₀2 hx₀240
  have hx₀t : x₀ ∈ centralizer ({t} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hO.mem x₀ hx₀L)
  have hC₀ := inCGb_initial hO hx₀L hx₀2 hx₀240 hF₀
  obtain ⟨n, U, T, s, hC, h0, hmax⟩ := exists_inCGb_maximal (K := jOf L x₀)
    ⟨2, _, _, _, hC₀, seq3_zero _ _ _⟩
  have hn2 : 2 ≤ n := hmax 2 _ _ _ hC₀ (seq3_zero _ _ _)
  have hstd : StdHyp G (U (n - 1)) := InCG.stdHyp_top hMcard (citPart2_of_cit hCIT) hO hC.1
  have hM12 : IsSporadic (U (n - 1)) .M12 := htop _ hstd hC.notF3Five_top
  obtain ⟨u, hOu⟩ := outer_at_top hY hO hstd hM12
  obtain ⟨x, hxX, hx2, hx240, hjstar, hcent, hF, hR⟩ := exists_jstar hC.1 hn2 hOu
  refine ⟨n, U, T, s, u, x, ⟨hC, fun m U' T' s' h h' => hmax m U' T' s' h (h'.trans h0), ?_, hn2,
    hOu, hxX, hx2, hx240, hjstar, hcent, hF, hR⟩⟩
  rw [h0]
  exact cqOrd_jOf hF₀ hx₀t hx₀2

end Top

end CFSG.EvenSporadicStandard.M12Std.Rbc

module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriFacts
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonE6Facts
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3Core
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompInn
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonE6Rank5
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA.CanonInn CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.StandardType (GGTorusLift)

theorem card_center_dvd_of_map_centerQuot {Γ : Type} [Group Γ] [Finite Γ] {L K : Subgroup Γ}
    (hKL : K ≤ L) (hK : CFSG.Open.IsQuasisimple ↥K) :
    Nat.card ↥(Subgroup.center ↥((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))) ∣
      Nat.card ↥(Subgroup.center ↥K) := by
  let π := QuotientGroup.mk' (Subgroup.center ↥L)
  let K' := K.subgroupOf L
  let J := K'.map π
  let f : ↥K' →* ↥J := (π.comp K'.subtype).codRestrict J fun x =>
    Subgroup.mem_map_of_mem π x.2
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    simpa [f] using hxy
  have hker : f.ker ≤ Subgroup.center ↥K' := by
    intro x hx
    have hx1 : π x = 1 := by
      have := congrArg Subtype.val hx
      simpa [f] using this
    have hxZ : (x : ↥L) ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff _).1 hx1
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have h := Subgroup.mem_center_iff.1 hxZ (y : ↥L)
    simpa using h
  haveI : Group.IsPerfect ↥K := ⟨hK.1⟩
  have hperf' : Group.IsPerfect ↥K' :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKL).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKL).symm.surjective
  have hcomap := CFSG.LocalCores.comap_center_eq_of_perfect hperf' f hf hker
  have hmap : (Subgroup.center ↥K').map f = Subgroup.center ↥J := by
    rw [← hcomap, Subgroup.map_comap_eq_self_of_surjective hf]
  have hdvd : Nat.card ↥(Subgroup.center ↥J) ∣ Nat.card ↥(Subgroup.center ↥K') := by
    calc Nat.card ↥(Subgroup.center ↥J)
        = Nat.card ↥((Subgroup.center ↥K').map f) := by rw [hmap]
      _ ∣ Nat.card ↥(Subgroup.center ↥K') := Subgroup.card_map_dvd _ f
  have hcard : Nat.card ↥(Subgroup.center ↥K') = Nat.card ↥(Subgroup.center ↥K) :=
    Nat.card_congr (Subgroup.centerCongr (Subgroup.subgroupOfEquivOfLe hKL)).toEquiv
  rwa [hcard] at hdvd

theorem exists_u3CoreHyp_of_u3Setup (hF : SubcompField) {Γ : Type} [Group Γ] [Finite Γ]
    {L K B : Subgroup Γ} {y : Γ} {n : ℕ} (hset : U3Setup Γ L K B y n) :
    ∃ (labL : GLALabel) (hyN : y ∈ Subgroup.normalizer (L : Set Γ)),
      GLASplit 3 labL ∧ B ≤ Subgroup.normalizer (L : Set Γ) ∧
      (∀ b ∈ B, MarkedInnDiag L b labL) ∧
      U3CoreHyp (↥L ⧸ Subgroup.center ↥L) labL (centerQuotAut ↥L (conjAut L y hyN)) n
        ((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) := by
  obtain ⟨hodd, hn3, hsplit, hB, hyB, hyL, -, -, hKcomp, hKlab, -, -, hR⟩ := hset
  obtain ⟨labL, -, hsplit3, hBNL, hM⟩ := split_label hsplit
  have hyN : y ∈ Subgroup.normalizer (L : Set Γ) := hBNL hyB
  have hy3 : y ^ 3 = 1 := hB.2 y hyB
  have hMy : MarkedInnDiag L y labL := hM y hyB
  let S := ↥L ⧸ Subgroup.center ↥L
  let β : MulAut S := centerQuotAut ↥L (conjAut L y hyN)
  let J : Subgroup S := (K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))
  have hqsL := isQuasisimple_of_marking hMy
  have hβne : β ≠ 1 :=
    CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.centerQuotAut_conjAut_ne_one hyN hyL hqsL.1
  have hdvd : labL.n ∣ n :=
    hF Γ L K y labL ⟨.twA, 2, n⟩ 3 Nat.prime_three (by norm_num) hy3 hyN hyL hMy hKcomp hKlab
      (by simp)
  have hKl : HasLabel ↥K (· = ⟨.twA, 2, n⟩) :=
    (labelOf_iff_hasLabel K ⟨.twA, 2, n⟩).1 hKlab
  obtain ⟨hcen, hinn, hpow, hJcomp, hJlab⟩ := marked_bridge hyN hy3 hMy hKcomp hKl
  have hrank : ∀ r : ℕ, GGTorusLift 3 r S → r ≤ 3 := by
    intro r hr
    obtain ⟨E, U, hEL, hUL, hU, hU2, hEU, hE, hEcard, hEC⟩ :=
      exists_of_ggTorusLift hqsL.1 (MulEquiv.refl S) hr
    have hle : Nat.card E ≤ 3 ^ 3 * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set Γ)) :=
      hR E U hEL hUL hU hU2 hEU hE
    rw [hEcard, hEC, Subgroup.card_bot, mul_one] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hle
  refine ⟨labL, hyN, hsplit3, hBNL, hM, ?_⟩
  exact ⟨hcen, hinn, hsplit3, hpow, hβne, hodd, hn3, hdvd, hJcomp, hJlab, hrank⟩

theorem u3SubcompL_of_core (hF : SubcompField) (hC : U3CoreS) : U3SubcompL := by
  intro Γ _ _ L K B y n hset
  have hKcomp : IsComponentOf K (L ⊓ Subgroup.centralizer ({y} : Set Γ)) := hset.2.2.2.2.2.2.2.2.1
  obtain ⟨labL, hyN, hsplit3, hBNL, hM, hcore⟩ := exists_u3CoreHyp_of_u3Setup hF hset
  let S := ↥L ⧸ Subgroup.center ↥L
  let β : MulAut S := centerQuotAut ↥L (conjAut L y hyN)
  let J : Subgroup S := (K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))
  have hcore' : U3CoreHyp S labL β n J := hcore
  have h3J : 3 ∣ Nat.card ↥(Subgroup.center ↥J) := hC S labL β n J trivial hcore'
  have hKL : K ≤ L := hKcomp.1.trans inf_le_left
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have hdvdZ : Nat.card ↥(Subgroup.center ↥J) ∣ Nat.card ↥(Subgroup.center ↥K) :=
    card_center_dvd_of_map_centerQuot hKL hKq
  exact h3J.trans hdvdZ

end CFSG.LocalAnalysis.GLTheoremA.CanonU3

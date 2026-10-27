module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123NoS5
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EFrame
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123aX
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123aV
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123aComp
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec123_noS5_of (hp : Asc82Pre11) (h121 : Asc82Lemma121) (h63 : Asc82Lemma63)
    (hH : ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
        Asc82Hyp62 G) (h65 : Asc82Lemma65) : Sec123NoS5 := by
  intro G _ _ t L S z K1 K2 E X hctx hX hAlt hne
  obtain ⟨e⟩ := hne
  have hS : Sec3SettingLB G t L := hctx.toSec10Z.toSec10Setting.toSec3SettingLB
  have hf : Sec12Frame t L S := sec12Frame_of hp hctx.toSec10Ctx hctx.alt1
  obtain ⟨hV8, V1, V2, hsup, hinf, hnat⟩ := hAlt
  rcases hnat with ⟨⟨e'⟩, -, -⟩ | ⟨-, hV1, hV2⟩
  ·
    have h1 : Nat.card X = Nat.card (alternatingGroup (Fin 5)) := Nat.card_congr e'.toEquiv
    have h2 : Nat.card X = Nat.card (Equiv.Perm (Fin 5)) := Nat.card_congr e.toEquiv
    have h3 := two_mul_nat_card_alternatingGroup (α := Fin 5)
    have h4 : 0 < Nat.card X := Nat.card_pos
    omega
  have hXY : X ≤ (secM t S L ⊓ L) ⊔ S := le_sup_left.trans hX.sup.le
  obtain ⟨s0, φ₁, φ₂, a₁, b₁, a₂, b₂, -, hs0ord, hs0t, hs0N, hs0L, hφ₁, hφ₂, ha₁, ha₂, hact₁,
    hact₂⟩ := sec123_s0 hf hctx.sylow hXY e hV1 hV2
  obtain ⟨hpsp, -, -, -, -, hsyl⟩ := hp.basic G t L S z hctx.toSec10Z
  obtain ⟨b, hbB, hcomm, hJ, hJ29⟩ := hp.facts.outerI4m G L hpsp (S ⊓ L) hsyl s0 hs0N hs0ord hs0L
  have hbB' : b ∈ secB S L := hbB
  have hBL : secB S L ≤ L := hf.bdata.1
  obtain ⟨φB, hφB, -, -⟩ := sec123_B_data hf.bdata
  have hs02 : s0 * s0 = 1 := by
    have h := pow_orderOf_eq_one s0
    rw [hs0ord, sq] at h
    exact h
  have hbb : b * b = 1 := hφB.mul_self_eq_one hbB'
  have hss : (s0 * b) * (s0 * b) = 1 := by
    calc s0 * b * (s0 * b) = s0 * (b * s0) * b := by group
      _ = s0 * (s0 * b) * b := by rw [← hcomm]
      _ = (s0 * s0) * (b * b) := by group
      _ = 1 := by rw [hs02, hbb, mul_one]
  have hs1 : s0 * b ≠ 1 := by
    intro h
    apply hs0L
    rw [eq_inv_of_mul_eq_one_left h]
    exact Subgroup.mem_sup_left (Subgroup.inv_mem _ (hBL hbB'))
  have hsord : orderOf (s0 * b) = 2 := orderOf_eq_prime (by rw [sq]; exact hss) hs1
  have hts : t * (s0 * b) = (s0 * b) * t := by
    have h1 : t * s0 = s0 * t := Subgroup.mem_centralizer_iff.mp hs0t t (Set.mem_singleton t)
    have h2 : b * t = t * b := Subgroup.mem_centralizer_iff.mp hf.htC b (hBL hbB')
    calc t * (s0 * b) = (t * s0) * b := by group
      _ = (s0 * t) * b := by rw [h1]
      _ = s0 * (t * b) := by group
      _ = s0 * (b * t) := by rw [h2]
      _ = (s0 * b) * t := by group
  obtain ⟨I, hIC, hIF, hIN⟩ :=
    sec123_comp hp.s3.l36 h63 (hH G t L hS) hS hsord hts hJ hJ29
  obtain ⟨-, -, -, -, -, -, ⟨-, hBV, -⟩⟩ := h121 G t L S z K1 K2 E hctx
  have hVel : CFSG.Open.IsElemAbelian 2 (secV t S L E) := hV8.1
  have hV1V : V1 ≤ secV t S L E := le_sup_left.trans hsup.le
  have hV2V : V2 ≤ secV t S L E := le_sup_right.trans hsup.le
  have hcard : Nat.card ↥((V1 ⊓ centralizer ({s0} : Set G)) ⊔ (V2 ⊓ centralizer ({s0} : Set G))) =
      64 :=
    sec123_card_D hφ₁ hφ₂ ha₁ ha₂ hact₁ hact₂
      (fun x hx y hy => hVel.comm (hV1V hx) (hV2V hy)) hinf
  set D : Subgroup G := (V1 ⊓ centralizer ({s0} : Set G)) ⊔ (V2 ⊓ centralizer ({s0} : Set G))
    with hD
  have hDV : D ≤ secV t S L E :=
    sup_le (inf_le_left.trans hV1V) (inf_le_left.trans hV2V)
  have hDcent : D ≤ centralizer ({s0} : Set G) := sup_le inf_le_right inf_le_right
  have hDel : CFSG.Open.IsElemAbelian 2 D := CFSG.Open.IsElemAbelian.mono hVel hDV
  have hDs : ∀ d ∈ D, d * (s0 * b) = (s0 * b) * d := by
    intro d hd
    have h1 : s0 * d = d * s0 :=
      Subgroup.mem_centralizer_iff.mp (hDcent hd) s0 (Set.mem_singleton s0)
    have h2 : d * b = b * d := hVel.comm (hDV hd) (hBV hbB')
    calc d * (s0 * b) = (d * s0) * b := by group
      _ = (s0 * d) * b := by rw [h1]
      _ = s0 * (d * b) := by group
      _ = s0 * (b * d) := by rw [h2]
      _ = (s0 * b) * d := by group
  have hsD : s0 * b ∉ D := by
    intro hmem
    have hsV : s0 * b ∈ secV t S L E := hDV hmem
    have hs0V : s0 ∈ secV t S L E := by
      have := (secV t S L E).mul_mem hsV ((secV t S L E).inv_mem (hBV hbB'))
      simpa using this
    obtain ⟨x, hx, hne⟩ := sec123_not_central hφ₁ ha₁ hact₁
    apply hne
    have hc : s0 * x = x * s0 := hVel.comm hs0V (hV1V hx)
    calc s0 * x * s0⁻¹ = x * s0 * s0⁻¹ := by rw [hc]
      _ = x := by group
  have hcard6 : Nat.card D = 2 ^ 6 := hcard.trans (by norm_num)
  obtain ⟨hE7el, hE7card⟩ := sec123_E7 hDel hcard6 hss hDs hsD
  have hE7le : D ⊔ zpowers (s0 * b) ≤ normalizer (I : Set G) := by
    refine le_trans ?_ hIN
    refine sup_le (fun d hd => ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact (hDs d hd).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
  have h7 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 2) hE7le hE7el hE7card
  have h6 := h65 G t L hS (hH G t L hS) I hIC hIF
  omega

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.ClassicalInvolution.AschTight.S1911C8b
public import CFSG.ClassicalInvolution.AschTight.Hall196Basic

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable (p f : ℕ) [Fact p.Prime]

theorem c19_8_of : C19_8Tmp p f := by
  intro G _ _ _ K z S W L t V hd
  dsimp only
  have hd0 := hd.toSec19Data
  have htb := hd.tight.toTightBranch
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hcomm := comm_of_mem hd0
  have hWL : W ≤ Subgroup.normalizer (L : Set G) :=
    (le_centralizer_of_mem hd0 (mem_W hd)).trans
      (centralizer_le_normalizer_member htb hd.memL hd.invL)
  set A : Subgroup G := (S : Subgroup G) ⊓ Subgroup.centralizer
    ((((S : Subgroup G) ⊓ K ⊔ Subgroup.zpowers t) : Subgroup G) : Set G) with hA
  set Z : Subgroup G := W ⊓ Subgroup.centralizer
    (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) with hZ
  have hZA : Z ≤ A := by
    rintro w ⟨hwW, hwC⟩
    refine ⟨hd.hWS hwW, mem_centralizer_sup_of hwC ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute t w from hcomm t (mem_W hd) w hwW) k).eq
  have hdisj : centralizerModOdd A L ⊓ Z = ⊥ := by
    obtain ⟨RL, hRL, hWRL, -, -⟩ := exists_sylow_member hd
    rw [eq_bot_iff, ← inf_centralizer_inf_eq_bot hd hRL]
    rintro x ⟨hxc, hxZ⟩
    refine ⟨hxZ, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
    obtain ⟨-, -, -, hc⟩ := hxc
    have h1 : ⁅x, r⁆ ∈ oddCoreOf L := hc r (hRL.1 hr)
    have h2 : ⁅x, r⁆ ∈ RL := by
      rw [commutatorElement_def]
      have h3 : x * r * x⁻¹ ∈ RL := by
        have := conj_mem_conjSub (n := x) hr
        rwa [hWRL x hxZ.1] at this
      exact RL.mul_mem h3 (RL.inv_mem hr)
    have h4 : ⁅x, r⁆ = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard L) h1
      (hRL.2.1.to_le (Subgroup.zpowers_le.mpr h2))
    rw [commutatorElement_def] at h4
    calc r * x = (x * r * x⁻¹ * r⁻¹)⁻¹ * (x * r) := by group
      _ = x * r := by rw [h4, inv_one, one_mul]
  refine ⟨le_antisymm ?_ (sup_le (fun x hx => hx.1) hZA), disjoint_iff.mpr hdisj, ?_⟩
  · intro a ha
    obtain ⟨RL, hRL, w, hw, hc⟩ := exists_mul_eq_of_mem_A hd ha.1
      (mem_centralizer_inf_of_mem_A ha.2) (mem_centralizer_t_of_mem_A ha.2)
    have hwA := hZA hw
    have hcS : a * w⁻¹ ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem ha.1
      ((S : Subgroup G).inv_mem (hd.hWS hw.1))
    have hcL : a * w⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mul_mem _ (centralizer_le_normalizer_member htb hd.memL hd.invL
        (mem_centralizer_t_of_mem_A ha.2)) (Subgroup.inv_mem _ (hWL hw.1))
    have hcmem : a * w⁻¹ ∈ centralizerModOdd A L := by
      refine ⟨A.mul_mem ha (A.inv_mem hwA), hcL,
        mem_normalizer_oddCoreOf_of_mem_normalizer hcL, fun l hl => ?_⟩
      refine AscL62.centSylow hd.tight.branch.odd hd.tight.branch.five hΩ (K := L) (R := RL)
        (V := Subgroup.zpowers (a * w⁻¹)) hd.memL hRL
        ((S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hcS))) ?_ ?_ l hl (a * w⁻¹)
        (Subgroup.mem_zpowers _)
      · intro y hy
        exact mem_normalizer_iff_conjSub_eq.mp ((Subgroup.zpowers_le.mpr hcL) hy)
      · intro r hr v hv
        exact Subgroup.mem_centralizer_iff.mp ((Subgroup.zpowers_le.mpr hc) hv) r hr
    have e : a = (a * w⁻¹) * w := by group
    rw [e]
    exact Subgroup.mul_mem_sup hcmem hw
  · intro c hc w hw
    have hcC := mem_centralizer_inf_of_mem_A hc.1.2
    have hcW := mem_normalizer_W_of_mem_A hd hc.1.1 hcC (mem_centralizer_t_of_mem_A hc.1.2)
    have h1 : c * w * c⁻¹ * w⁻¹ ∈ Z := by
      refine ⟨W.mul_mem ((Subgroup.mem_normalizer_iff.mp hcW w).mp hw.1) (W.inv_mem hw.1), ?_⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hcC hw.2)
        (Subgroup.inv_mem _ hcC)) (Subgroup.inv_mem _ hw.2)
    have h2 : c * w * c⁻¹ * w⁻¹ ∈ centralizerModOdd A L := by
      have hwc : w * c⁻¹ * w⁻¹ ∈ centralizerModOdd A L := by
        rw [← Hall196.conjSub_centralizerModOdd (hWL hw.1) (conjSub_eq_self_of_mem (hZA hw))]
        exact conj_mem_conjSub (Subgroup.inv_mem _ hc)
      have e : c * w * c⁻¹ * w⁻¹ = c * (w * c⁻¹ * w⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hc hwc
    have h3 : c * w * c⁻¹ * w⁻¹ ∈ centralizerModOdd A L ⊓ Z := ⟨h2, h1⟩
    rw [hdisj, Subgroup.mem_bot] at h3
    calc c * w = c * w * c⁻¹ * w⁻¹ * (w * c) := by group
      _ = w * c := by rw [h3, one_mul]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

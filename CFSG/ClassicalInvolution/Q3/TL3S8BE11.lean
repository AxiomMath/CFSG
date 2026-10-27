module

public import CFSG.ClassicalInvolution.Q3.TL3S8BC8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section E11

variable {G : Type} [Group G] [Finite G]

abbrev TightBPrimeBot (K : Subgroup G) (S : Sylow 2 G) (W L : Subgroup G) : Prop :=
  (S : Subgroup G) ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
      Subgroup.centralizer (W : Set G) ⊓ centralizerModOdd ⊤ L = ⊥

variable {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace TightSylowDataT

variable (hd : TightSylowDataT K z S W L t V)
include hd

theorem mem_centralizerModOdd_of_mem_centralizer {c : G} (hcS : c ∈ (S : Subgroup G))
    (hcL : c ∈ Subgroup.normalizer (L : Set G)) {RL : Subgroup G} (hRL : IsSylow2In RL L)
    (hc : c ∈ Subgroup.centralizer (RL : Set G)) : c ∈ centralizerModOdd ⊤ L := by
  refine ⟨Subgroup.mem_top c, hcL, mem_normalizer_oddCoreOf_of_mem_normalizer hcL,
    fun l hl => ?_⟩
  exact Sec6Gen.centSylow hd.tight.hypGen hd.memL hRL
    (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hcS))
    (fun y hy => mem_normalizer_iff_conjSub_eq.mp ((Subgroup.zpowers_le.mpr hcL) hy))
    (fun r hr v hv => Subgroup.mem_centralizer_iff.mp ((Subgroup.zpowers_le.mpr hc) hv) r hr)
    l hl c (Subgroup.mem_zpowers c)

theorem mem_W_of_c19_11b (hB : TightBPrimeBot K S W L) {a : G} (haS : a ∈ (S : Subgroup G))
    (haC : a ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G))
    (haW : a ∈ Subgroup.centralizer (W : Set G)) : a ∈ W := by
  have hd0 := hd.toTightSylowData
  have hcomm := hd0.comm_of_mem
  have hat : a ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp haW t hd.mem_W).symm
  obtain ⟨RL, hRL, w, hw, hc⟩ := hd.exists_mul_eq_of_mem_A haS haC hat
  have hWL : W ≤ Subgroup.normalizer (L : Set G) :=
    (hd0.le_centralizer_of_mem hd.mem_W).trans
      (hd.tight.centralizer_le_normalizer_member hd.memL hd.invL)
  have hcS : a * w⁻¹ ∈ (S : Subgroup G) :=
    (S : Subgroup G).mul_mem haS ((S : Subgroup G).inv_mem (hd.hWS hw.1))
  have hcL : a * w⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (hd.tight.centralizer_le_normalizer_member hd.memL hd.invL hat)
      (Subgroup.inv_mem _ (hWL hw.1))
  have hwW : w ∈ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcomm x hx w hw.1
  have hmem : a * w⁻¹ ∈ (S : Subgroup G) ⊓
      Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
      Subgroup.centralizer (W : Set G) ⊓ centralizerModOdd ⊤ L :=
    ⟨⟨⟨hcS, Subgroup.mul_mem _ haC (Subgroup.inv_mem _ hw.2)⟩,
      Subgroup.mul_mem _ haW (Subgroup.inv_mem _ hwW)⟩,
      hd.mem_centralizerModOdd_of_mem_centralizer hcS hcL hRL hc⟩
  rw [hB, Subgroup.mem_bot] at hmem
  have e : a = w := by
    calc a = a * w⁻¹ * w := by group
      _ = w := by rw [hmem, one_mul]
  rw [e]
  exact hw.1

theorem exists_mul_mem_centralizer_of_comm {s : G} (hsS : s ∈ (S : Subgroup G))
    (hsU : ∀ u ∈ K ⊓ W, s * u = u * s) :
    ∃ c ∈ V, s * c⁻¹ ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  have hd0 := hd.toTightSylowData
  have hcomm := hd0.comm_of_mem
  have hUR : K ⊓ W ≤ (S : Subgroup G) ⊓ K := fun x hx => ⟨hd.hWS hx.2, hx.1⟩
  have hcard := hd0.card_inf_eq
  obtain ⟨b, hbR, hbU⟩ := S1911.exists_mem_not_mem hcard
  have hdef := S1911.inv_mul_conj_mem hUR hcard hbR (hd0.le_normalizer_inf hsS) hsU
  have hVR : V ≤ Subgroup.normalizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    fun v hv => hd0.le_normalizer_inf (hd.hWS (hd.leW hv))
  have hdisj : V ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hd.inf_sec19Y_eq_bot]
    rintro x ⟨hxV, hxC⟩
    have hx : x ∈ W ⊓ sec19Y K z := by
      rw [hd0.inf_sec19Y_eq]
      exact ⟨hd.leW hxV, hxC⟩
    exact ⟨hxV, hx.2⟩
  obtain ⟨c, hcV, hc⟩ := S1911.exists_defect_eq hUR hcard (C := V) hVR
    (fun c hc u hu => hcomm c (hd.leW hc) u hu.2) hdisj hd.card_inf_eq_card.le hbR hbU hdef
  exact ⟨c, hcV, S1911.mem_centralizer_of_defect_eq hUR hcard hbR hbU (hVR hcV) hsU
    (fun u hu => hcomm c (hd.leW hcV) u hu.2) hc.symm⟩

theorem inf_centralizer_W_eq (hB : TightBPrimeBot K S W L) :
    (S : Subgroup G) ⊓ Subgroup.centralizer (W : Set G) = W := by
  have hcomm := hd.comm_of_mem
  apply le_antisymm
  · rintro s ⟨hsS, hsW⟩
    obtain ⟨c, hcV, hc⟩ := hd.exists_mul_mem_centralizer_of_comm hsS
      (fun u hu => (Subgroup.mem_centralizer_iff.mp hsW u hu.2).symm)
    have hcW : c⁻¹ ∈ Subgroup.centralizer (W : Set G) :=
      Subgroup.inv_mem _ (Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx c (hd.leW hcV))
    have h := hd.mem_W_of_c19_11b hB ((S : Subgroup G).mul_mem hsS
      ((S : Subgroup G).inv_mem (hd.hWS (hd.leW hcV)))) hc (Subgroup.mul_mem _ hsW hcW)
    have e : s = s * c⁻¹ * c := by group
    rw [e]
    exact W.mul_mem h (hd.leW hcV)
  · exact le_inf hd.hWS fun w hw => Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx w hw

theorem comm_V_of_comm_U {a : G} (haS : a ∈ (S : Subgroup G))
    (hat : a ∈ Subgroup.centralizer ({t} : Set G)) (haU : ∀ u ∈ K ⊓ W, a * u = u * a) :
    ∀ v ∈ V, a * v = v * a := by
  obtain ⟨RL, hRL, haRL, hWRL, hVRL, hcardRL⟩ := hd.exists_sylow_member_of_mem_A haS hat
  obtain ⟨b, hbR, hbV⟩ := S1911.exists_mem_not_mem hcardRL
  have hcomm := hd.comm_of_mem
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    hcomm x (hd.leW hx) y (hd.leW hy)
  intro v hv
  obtain ⟨u, hu, hdef⟩ := S1911.exists_defect_eq hVRL hcardRL (C := K ⊓ W)
    (fun x hx => mem_normalizer_iff_conjSub_eq.mpr (hWRL x hx.2))
    (fun x hx y hy => hcomm x hx.2 y (hd.leW hy)) (hd.inf_inf_centralizer_eq_bot hRL)
    hd.card_inf_eq_card.ge hbR hbV hv
  have h := S1911.conj_eq_of_defect hVRL hcardRL hVc hbR hbV
    (mem_normalizer_iff_conjSub_eq.mpr haRL) (hd.mem_normalizer_V_of_mem_A haS hat) hv
    (fun x hx => hcomm u hu.2 x (hd.leW hx)) hdef (haU u hu)
  calc a * v = a * v * a⁻¹ * a := by group
    _ = v * a := by rw [h]

theorem mem_W_of_comm_U (hB : TightBPrimeBot K S W L) {a : G} (haS : a ∈ (S : Subgroup G))
    (hat : a ∈ Subgroup.centralizer ({t} : Set G)) (haU : ∀ u ∈ K ⊓ W, a * u = u * a) :
    a ∈ W := by
  have haV := hd.comm_V_of_comm_U haS hat haU
  have haW : a ∈ Subgroup.centralizer (W : Set G) := by
    have h := S1911.mem_centralizer_sup_of (H₁ := K ⊓ W) (H₂ := V)
      (Subgroup.mem_centralizer_iff.mpr fun u hu => (haU u hu).symm)
      (Subgroup.mem_centralizer_iff.mpr fun v hv => (haV v hv).symm)
    rwa [← hd.sup_eq_inf_sup] at h
  exact (hd.inf_centralizer_W_eq hB).le ⟨haS, haW⟩

end TightSylowDataT


end E11

end CFSG.ClassicalInvolution.Q3

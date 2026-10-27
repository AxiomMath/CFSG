module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets4
public import CFSG.ClassicalInvolution.AschTight.Sec19DataT
public import CFSG.ClassicalInvolution.AschTight.S1911C8b

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem mem_centralizerModOdd_of_mem_centralizer (hd : Sec19DataT p f K z S W L t V) {c : G}
    (hcS : c ∈ (S : Subgroup G)) (hcL : c ∈ Subgroup.normalizer (L : Set G)) {RL : Subgroup G}
    (hRL : IsSylow2In RL L) (hc : c ∈ Subgroup.centralizer (RL : Set G)) :
    c ∈ centralizerModOdd ⊤ L := by
  refine ⟨Subgroup.mem_top c, hcL, mem_normalizer_oddCoreOf_of_mem_normalizer hcL,
    fun l hl => ?_⟩
  exact AscL62.centSylow hd.tight.branch.odd hd.tight.branch.five (hypOmegaMod_of_tightD hd.tight)
    (K := L) (R := RL) (V := Subgroup.zpowers c) hd.memL hRL
    (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hcS))
    (fun y hy => mem_normalizer_iff_conjSub_eq.mp ((Subgroup.zpowers_le.mpr hcL) hy))
    (fun r hr v hv => Subgroup.mem_centralizer_iff.mp ((Subgroup.zpowers_le.mpr hc) hv) r hr)
    l hl c (Subgroup.mem_zpowers c)

theorem mem_W_of_c19_11b (h11b : C19_11bTmp p f) (hd : Sec19DataT p f K z S W L t V) {a : G}
    (haS : a ∈ (S : Subgroup G))
    (haC : a ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G))
    (haW : a ∈ Subgroup.centralizer (W : Set G)) : a ∈ W := by
  have hd0 := hd.toSec19Data
  have hcomm := comm_of_mem hd0
  have hat : a ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp haW t (mem_W hd)).symm
  obtain ⟨RL, hRL, w, hw, hc⟩ := exists_mul_eq_of_mem_A hd haS haC hat
  have hWL : W ≤ Subgroup.normalizer (L : Set G) :=
    (le_centralizer_of_mem hd0 (mem_W hd)).trans
      (centralizer_le_normalizer_member hd.tight.toTightBranch hd.memL hd.invL)
  have hcS : a * w⁻¹ ∈ (S : Subgroup G) :=
    (S : Subgroup G).mul_mem haS ((S : Subgroup G).inv_mem (hd.hWS hw.1))
  have hcL : a * w⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (centralizer_le_normalizer_member hd.tight.toTightBranch hd.memL hd.invL
      hat) (Subgroup.inv_mem _ (hWL hw.1))
  have hwW : w ∈ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcomm x hx w hw.1
  have hmem : a * w⁻¹ ∈ (S : Subgroup G) ⊓
      Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
      Subgroup.centralizer (W : Set G) ⊓ centralizerModOdd ⊤ L :=
    ⟨⟨⟨hcS, Subgroup.mul_mem _ haC (Subgroup.inv_mem _ hw.2)⟩,
      Subgroup.mul_mem _ haW (Subgroup.inv_mem _ hwW)⟩,
      mem_centralizerModOdd_of_mem_centralizer hd hcS hcL hRL hc⟩
  rw [h11b G K z S W L t V hd, Subgroup.mem_bot] at hmem
  have e : a = w := by
    calc a = a * w⁻¹ * w := by group
      _ = w := by rw [hmem, one_mul]
  rw [e]
  exact hw.1

omit [IsSimpleGroup G] in
theorem inf_le_sec19X (hd : Sec19Data p f K z S W) : (S : Subgroup G) ⊓ K ≤ sec19X K z :=
  le_iSup₂ (f := fun (B : Subgroup G) (_ : (B ∈ USet (CoreAssembly.conjClass K) ∨
    B ∈ RSet (CoreAssembly.conjClass K)) ∧ B ≤ Subgroup.centralizer ({z} : Set G)) => B) _
    ⟨Or.inr (inf_mem_rSet hd), inf_le_left.trans hd.hSz⟩

omit [IsSimpleGroup G] in
theorem mem_centralizer_of_mem_centralizerModOdd {H : Subgroup G} {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha : a ∈ centralizerModOdd ⊤ H) {x : G}
    (hxS : x ∈ (S : Subgroup G)) (hxH : x ∈ H) : x * a = a * x := by
  obtain ⟨-, -, -, hc⟩ := ha
  have h1 : ⁅a, x⁆ = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard H) (hc x hxH)
    (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (by
      rw [commutatorElement_def]
      exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem haS hxS)
        ((S : Subgroup G).inv_mem haS)) ((S : Subgroup G).inv_mem hxS))))
  rw [commutatorElement_def] at h1
  calc x * a = (a * x * a⁻¹ * x⁻¹)⁻¹ * (a * x) := by group
    _ = a * x := by rw [h1, inv_one, one_mul]

theorem inf_centralizerModOdd_le_of_c19_11b (h11b : C19_11bTmp p f)
    (hd : Sec19DataT p f K z S W L t V) :
    (S : Subgroup G) ⊓ centralizerModOdd ⊤ (sec19X K z) ≤ W := by
  have hd0 := hd.toSec19Data
  rintro a ⟨haS, ha⟩
  refine mem_W_of_c19_11b h11b hd haS ?_ ?_
  · rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact mem_centralizer_of_mem_centralizerModOdd haS ha hr.1 (inf_le_sec19X hd0 hr)
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact mem_centralizer_of_mem_centralizerModOdd haS ha (hd.hWS hw) (le_sec19X hd0 hw)

theorem inf_sec19Y_inf_le_of_c19_11b (h11b : C19_11bTmp p f)
    (hd : Sec19DataT p f K z S W L t V) :
    (S : Subgroup G) ⊓ sec19Y K z ⊓ Subgroup.centralizer (W : Set G) ≤ W := by
  rintro a ⟨⟨haS, haY⟩, haW⟩
  exact mem_W_of_c19_11b h11b hd haS
    (mem_centralizer_of_mem_inf_sec19Y hd.toSec19Data haS haY) haW

variable (p f) in
theorem c19_11_of (h11b : C19_11bTmp p f) : C19_11Tmp p f := by
  intro G _ _ _ K z S W hd
  obtain ⟨L, t, V, hdT⟩ := exists_sec19DataT hd
  exact inf_centralizerModOdd_le_of_c19_11b h11b hdT

variable (p f) in
theorem c19_11a_of (h11b : C19_11bTmp p f) : C19_11aTmp p f := by
  intro G _ _ _ K z S W hd
  obtain ⟨L, t, V, hdT⟩ := exists_sec19DataT hd
  exact inf_sec19Y_inf_le_of_c19_11b h11b hdT

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

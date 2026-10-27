module

public import CFSG.ClassicalInvolution.AschTight.S1911C8a
public import CFSG.ClassicalInvolution.AschTight.S1911Quat2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

omit [Finite G] [IsSimpleGroup G] in
theorem mem_centralizer_sup_of {H₁ H₂ : Subgroup G} {x : G}
    (h₁ : x ∈ Subgroup.centralizer (H₁ : Set G)) (h₂ : x ∈ Subgroup.centralizer (H₂ : Set G)) :
    x ∈ Subgroup.centralizer ((H₁ ⊔ H₂ : Subgroup G) : Set G) := by
  have hle : H₁ ⊔ H₂ ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp h₁ y hy
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp h₂ y hy
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

variable {a : G}

theorem comm_V_of_mem_A (hd : Sec19DataT p f K z S W L t V) (haS : a ∈ (S : Subgroup G))
    (haC : a ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G))
    (hat : a ∈ Subgroup.centralizer ({t} : Set G)) : ∀ v ∈ V, a * v = v * a := by
  obtain ⟨RL, hRL, haRL, hWRL, hVRL, hcardRL⟩ := exists_sylow_member_of_mem_A hd haS hat
  obtain ⟨b, hbR, hbV⟩ := exists_mem_not_mem hcardRL
  have hcomm := comm_of_mem hd.toSec19Data
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    hcomm x (hd.leW hx) y (hd.leW hy)
  intro v hv
  obtain ⟨u, hu, hdef⟩ := exists_defect_eq hVRL hcardRL (C := K ⊓ W)
    (fun x hx => mem_normalizer_iff_conjSub_eq.mpr (hWRL x hx.2))
    (fun x hx y hy => hcomm x hx.2 y (hd.leW hy)) (inf_inf_centralizer_eq_bot hd hRL)
    (card_inf_eq_card hd).ge hbR hbV hv
  have hau : a * u = u * a :=
    (Subgroup.mem_centralizer_iff.mp haC u ⟨hd.hWS hu.2, hu.1⟩).symm
  have h := conj_eq_of_defect hVRL hcardRL hVc hbR hbV (mem_normalizer_iff_conjSub_eq.mpr haRL)
    (mem_normalizer_V_of_mem_A hd haS hat) hv (fun x hx => hcomm u hu.2 x (hd.leW hx)) hdef hau
  calc a * v = a * v * a⁻¹ * a := by group
    _ = v * a := by rw [h]

theorem exists_mul_eq_of_mem_A (hd : Sec19DataT p f K z S W L t V) (haS : a ∈ (S : Subgroup G))
    (haC : a ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G))
    (hat : a ∈ Subgroup.centralizer ({t} : Set G)) :
    ∃ RL : Subgroup G, IsSylow2In RL L ∧ ∃ w ∈ W ⊓ Subgroup.centralizer
      (((S : Subgroup G) ⊓ K : Subgroup G) : Set G),
        a * w⁻¹ ∈ Subgroup.centralizer (RL : Set G) := by
  obtain ⟨RL, hRL, haRL, hWRL, hVRL, hcardRL⟩ := exists_sylow_member_of_mem_A hd haS hat
  obtain ⟨b, hbR, hbV⟩ := exists_mem_not_mem hcardRL
  have hcomm := comm_of_mem hd.toSec19Data
  have haV := comm_V_of_mem_A hd haS haC hat
  have haN : a ∈ Subgroup.normalizer (RL : Set G) := mem_normalizer_iff_conjSub_eq.mpr haRL
  have hda : b⁻¹ * (a * b * a⁻¹) ∈ V := inv_mul_conj_mem hVRL hcardRL hbR haN haV
  have hcardZ : Nat.card V ≤ Nat.card ↥(W ⊓ Subgroup.centralizer
      (((S : Subgroup G) ⊓ K : Subgroup G) : Set G)) := by
    rw [← inf_sec19Y_eq hd.toSec19Data, card_inf_sec19Y hd]
  obtain ⟨w, hw, hwdef⟩ := exists_defect_eq hVRL hcardRL
    (C := W ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G))
    (fun x hx => mem_normalizer_iff_conjSub_eq.mpr (hWRL x hx.1))
    (fun x hx y hy => hcomm x hx.1 y (hd.leW hy)) (inf_centralizer_inf_eq_bot hd hRL)
    hcardZ hbR hbV hda
  refine ⟨RL, hRL, w, hw, ?_⟩
  exact mem_centralizer_of_defect_eq hVRL hcardRL hbR hbV
    (mem_normalizer_iff_conjSub_eq.mpr (hWRL w hw.1)) haV
    (fun x hx => hcomm w hw.1 x (hd.leW hx)) hwdef.symm

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

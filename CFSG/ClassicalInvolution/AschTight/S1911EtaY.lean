module

public import CFSG.ClassicalInvolution.AschTight.S1911Eta3
public import CFSG.ClassicalInvolution.AschTight.E2StarTargets

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

omit [IsSimpleGroup G] in
theorem le_sec19X (hd : Sec19Data p f K z S W) : W ≤ sec19X K z := by
  obtain ⟨η, S', hη, -, hWη, hηS⟩ := exists_eta hd
  rw [hWη]
  refine iSup₂_le fun A hA => ?_
  exact le_iSup₂ (f := fun (B : Subgroup G) (_ : (B ∈ USet (CoreAssembly.conjClass K) ∨
    B ∈ RSet (CoreAssembly.conjClass K)) ∧ B ≤ Subgroup.centralizer ({z} : Set G)) => B) A
    ⟨Or.inl (hη.1 hA).1, (hηS A hA).trans hd.hSz⟩

omit [IsSimpleGroup G] in
theorem mem_centralizer_of_mem_inf_sec19Y (hd : Sec19Data p f K z S W) {x : G}
    (hxS : x ∈ (S : Subgroup G)) (hxY : x ∈ sec19Y K z) :
    x ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  obtain ⟨-, -, -, hc⟩ := hxY
  have h1 : ⁅x, r⁆ ∈ oddCoreOf K := hc r hr.2
  have h2 : ⁅x, r⁆ ∈ (S : Subgroup G) ⊓ K := by
    rw [commutatorElement_def]
    have h3 : x * r * x⁻¹ ∈ (S : Subgroup G) ⊓ K :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_inf hd hxS) r).mp hr
    exact Subgroup.mul_mem _ h3 (Subgroup.inv_mem _ hr)
  have h4 : ⁅x, r⁆ = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h1
    ((S.isPGroup'.to_le inf_le_left).to_le (Subgroup.zpowers_le.mpr h2))
  rw [commutatorElement_def] at h4
  calc r * x = (x * r * x⁻¹ * r⁻¹)⁻¹ * (x * r) := by group
    _ = x * r := by rw [h4, inv_one, one_mul]

theorem inf_sec19Y_eq (hd : Sec19Data p f K z S W) :
    W ⊓ sec19Y K z = W ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  apply le_antisymm
  · exact fun x hx => ⟨hx.1, mem_centralizer_of_mem_inf_sec19Y hd (hd.hWS hx.1) hx.2⟩
  · rintro x ⟨hxW, hxC⟩
    refine ⟨hxW, le_sec19X hd hxW, mem_normalizer_of_mem_W hd hxW,
      mem_normalizer_oddCoreOf_of_mem_normalizer (mem_normalizer_of_mem_W hd hxW), ?_⟩
    intro l hl
    have hΩ := hypOmegaMod_of_tightD hd.tight
    refine AscL62.centSylow hd.tight.branch.odd hd.tight.branch.five hΩ (K := K)
      (R := (S : Subgroup G) ⊓ K) (V := Subgroup.zpowers x) (CoreAssembly.mem_conjClass_self K)
      (isSylow2In_inf hd) ((S.isPGroup'.to_le hd.hWS).to_le (Subgroup.zpowers_le.mpr hxW)) ?_ ?_
      l hl x (Subgroup.mem_zpowers x)
    · intro y hy
      exact mem_normalizer_iff_conjSub_eq.mp
        ((Subgroup.zpowers_le.mpr (mem_normalizer_of_mem_W hd hxW)) hy)
    · intro r hr v hv
      have hvC : v ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
        (Subgroup.zpowers_le.mpr hxC) hv
      exact Subgroup.mem_centralizer_iff.mp hvC r hr

theorem inf_sec19Y_eq_bot (hd : Sec19DataT p f K z S W L t V) : V ⊓ sec19Y K z = ⊥ := by
  have hd0 := hd.toSec19Data
  have hΩ := hypOmegaMod_of_tightD hd.tight
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hxC : x ∈ W ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
    rw [← inf_sec19Y_eq hd0]
    exact ⟨hd.leW hx.1, hx.2⟩
  have h2 : 2 ≤ Nat.card (Subgroup.zpowers x) := by
    rw [Nat.card_zpowers]
    have h0 : orderOf x ≠ 0 := (isOfFinOrder_of_finite x).orderOf_pos.ne'
    have h1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
    omega
  have htx : t ∈ Subgroup.zpowers x :=
    mem_of_le_member hd.invL ((Subgroup.zpowers_le.mpr hx.1).trans (le_member hd))
      ((hΩ.isPGroup_of_mem_USet hd.tight.branch.odd hd.memV).to_le
        (Subgroup.zpowers_le.mpr hx.1)) h2
  exact not_mem_centralizer_inf hd0 hd.memL (member_ne hd) hd.invL
    ((Subgroup.zpowers_le.mpr hxC.2) htx)

theorem inf_inf_sec19Y_eq_bot (hd : Sec19DataT p f K z S W L t V) :
    V ⊓ (W ⊓ sec19Y K z) = ⊥ := by
  rw [eq_bot_iff, ← inf_sec19Y_eq_bot hd]
  intro x hx
  exact ⟨hx.1, hx.2.2⟩

theorem card_sup_inf_sec19Y (hd : Sec19DataT p f K z S W L t V) :
    Nat.card ↥(V ⊔ (W ⊓ sec19Y K z)) = Nat.card V * Nat.card ↥(W ⊓ sec19Y K z) :=
  card_sup_of_comm (fun a ha b hb => comm_of_mem hd.toSec19Data a (hd.leW ha) b hb.1)
    (inf_inf_sec19Y_eq_bot hd)

theorem sup_inf_sec19Y_eq (hd : Sec19DataT p f K z S W L t V) :
    W = V ⊔ (W ⊓ sec19Y K z) := by
  have hd0 := hd.toSec19Data
  have hcomm := comm_of_mem hd0
  have hUR : K ⊓ W ≤ (S : Subgroup G) ⊓ K := fun x hx => ⟨hd.hWS hx.2, hx.1⟩
  have hle := card_le_card_inf_centralizer_mul hUR (card_inf_eq hd0) (W := W)
    (fun w hw => le_normalizer_inf hd0 (hd.hWS hw)) (fun w hw u hu => hcomm w hw u hu.2)
  rw [← inf_sec19Y_eq hd0, card_inf_eq_card hd] at hle
  have hsub : V ⊔ (W ⊓ sec19Y K z) ≤ W := sup_le hd.leW inf_le_left
  refine (Subgroup.eq_of_le_of_card_ge hsub ?_).symm
  rw [card_sup_inf_sec19Y hd, mul_comm]
  exact hle

theorem card_inf_sec19Y (hd : Sec19DataT p f K z S W L t V) :
    Nat.card ↥(W ⊓ sec19Y K z) = Nat.card V := by
  have h1 := card_eq_mul hd
  rw [card_inf_eq_card hd] at h1
  have h2 : Nat.card W = Nat.card V * Nat.card ↥(W ⊓ sec19Y K z) := by
    conv_lhs => rw [sup_inf_sec19Y_eq hd]
    exact card_sup_inf_sec19Y hd
  have hV : 0 < Nat.card V := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hV (h2.symm.trans h1)

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

module

public import CFSG.ClassicalInvolution.AschTight.S1911C7c
public import CFSG.ClassicalInvolution.AschTight.Hall196Idx2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem le_inf_sup (hd : Sec19DataT p f K z S W L t V) : W ≤ (S : Subgroup G) ⊓ K ⊔ V := by
  conv_lhs => rw [sup_eq_inf_sup hd]
  exact sup_le (fun x hx => Subgroup.mem_sup_left ⟨hd.hWS hx.2, hx.1⟩) le_sup_right

theorem card_inf_sup (hd : Sec19DataT p f K z S W L t V) :
    Nat.card ↥((S : Subgroup G) ⊓ K ⊔ V) = 2 * Nat.card W := by
  have hd0 := hd.toSec19Data
  have h := Hall196.card_sup_mul_card_inf' (A := (S : Subgroup G) ⊓ K) (C := V)
    (fun v hv => le_normalizer_inf hd0 (hd.hWS (hd.leW hv)))
  have hbot : (S : Subgroup G) ⊓ K ⊓ V = ⊥ := by
    rw [eq_bot_iff, ← inf_member_eq_bot hd]
    exact fun x hx => ⟨hx.2, hx.1.2⟩
  rw [hbot, Subgroup.card_bot, mul_one, card_inf_eq hd0] at h
  rw [h, card_eq_mul hd]
  ring

theorem conj_eq_mul_of_mem_inf_sup (hd : Sec19DataT p f K z S W L t V) {x : G}
    (hx : x ∈ (S : Subgroup G) ⊓ K ⊔ V) (hxW : x ∉ W) : x * t * x⁻¹ = t * z := by
  have hcomm := comm_of_mem hd.toSec19Data
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  obtain ⟨r, hr, hrt⟩ := exists_conj_eq_mul hd
  have hrW : r ∉ W := by
    intro hrW
    have h1 : r * t * r⁻¹ = t := by rw [hcomm r hrW t (mem_W hd)]; group
    rw [h1] at hrt
    exact hI.ne_one (mul_eq_left.mp hrt.symm)
  have hw : r⁻¹ * x ∈ W := inv_mul_mem_of_not_mem_of_card_two_mul (le_inf_sup hd)
    (card_inf_sup hd) (Subgroup.mem_sup_left hr) hx hrW hxW
  have hwt : r⁻¹ * x * t = t * (r⁻¹ * x) := hcomm _ hw t (mem_W hd)
  calc x * t * x⁻¹ = r * (r⁻¹ * x * t) * (r⁻¹ * x)⁻¹ * r⁻¹ := by group
    _ = r * (t * (r⁻¹ * x)) * (r⁻¹ * x)⁻¹ * r⁻¹ := by rw [hwt]
    _ = r * t * r⁻¹ := by group
    _ = t * z := hrt

theorem ne_of_mem_inf_sup (hd : Sec19DataT p f K z S W L t V) {x : G}
    (hx : x ∈ (S : Subgroup G) ⊓ K ⊔ V) (hxW : x ∉ W) {w : G} (hxw : x * w = w * x)
    (hw : w = t ∨ w = t * z) : False := by
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hxt := conj_eq_mul_of_mem_inf_sup hd hx hxW
  have hxS : x ∈ (S : Subgroup G) :=
    (sup_le inf_le_left (hd.leW.trans hd.hWS) : (S : Subgroup G) ⊓ K ⊔ V ≤ S) hx
  have hxz : x * z * x⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz hxS)]
    group
  have hxw' : x * w * x⁻¹ = w := by rw [hxw]; group
  rcases hw with rfl | rfl
  · rw [hxt] at hxw'
    exact hI.ne_one (mul_eq_left.mp hxw')
  · have e : x * (t * z) * x⁻¹ = t := by
      calc x * (t * z) * x⁻¹ = (x * t * x⁻¹) * (x * z * x⁻¹) := by group
        _ = t * (z * z) := by rw [hxt, hxz, mul_assoc]
        _ = t := by rw [hI.sq, mul_one]
    rw [e] at hxw'
    exact hI.ne_one (mul_eq_left.mp hxw'.symm)

theorem card_le_four_of_le_inf_sup (hd : Sec19DataT p f K z S W L t V) {E : Subgroup G}
    (hEP : E ≤ (S : Subgroup G) ⊓ K ⊔ V) (hE : IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  classical
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hE.2 x hx
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEW : ∀ x ∈ E, x ∈ W → x = 1 ∨ x = z ∨ x = t ∨ x = t * z := by
    intro x hx hxW
    by_cases h1 : x = 1
    · exact Or.inl h1
    · exact Or.inr (invol_mem_W hd hxW (hE2 x hx) h1)
  have hfin : ∀ F : Finset G, (E : Set G) ⊆ ↑F → F.card ≤ 4 → Nat.card E ≤ 4 := by
    intro F hF hF4
    calc Nat.card E = (E : Set G).ncard := (Nat.card_coe_set_eq _).symm
      _ ≤ (F : Set G).ncard := Set.ncard_le_ncard hF (Finset.finite_toSet F)
      _ = F.card := Set.ncard_coe_finset F
      _ ≤ 4 := hF4
  by_cases hle : E ≤ W
  · refine hfin {1, z, t, t * z} (fun x hx => ?_) Finset.card_le_four
    rcases hEW x hx (hle hx) with h | h | h | h <;> simp [h]
  · obtain ⟨x, hxE, hxW⟩ := Set.not_subset.mp hle
    have hxP := hEP hxE
    have hsmall : ∀ w ∈ E, w ∈ W → w = 1 ∨ w = z := by
      intro w hwE hwW
      rcases hEW w hwE hwW with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (ne_of_mem_inf_sup hd hxP hxW (hEc x hxE w hwE) (Or.inl h)).elim
      · exact (ne_of_mem_inf_sup hd hxP hxW (hEc x hxE w hwE) (Or.inr h)).elim
    refine hfin {1, z, x, x * z} (fun y hy => ?_) Finset.card_le_four
    by_cases hyW : y ∈ W
    · rcases hsmall y hy hyW with h | h <;> simp [h]
    · have hw : x⁻¹ * y ∈ W := inv_mul_mem_of_not_mem_of_card_two_mul (le_inf_sup hd)
        (card_inf_sup hd) hxP (hEP hy) hxW hyW
      have hwE : x⁻¹ * y ∈ E := E.mul_mem (E.inv_mem hxE) hy
      have e : y = x * (x⁻¹ * y) := by group
      rcases hsmall _ hwE hw with h | h
      · rw [h, mul_one] at e
        simp [e]
      · rw [h] at e
        simp [e]

theorem sec19X_eq_of_case2 (hd : Sec19DataT p f K z S W L t V)
    (h1 : W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W) :
    (K ⊔ oddCoreOf (sec19X K z)) ⊔ V = sec19X K z :=
  sup_oddCore_sup_eq hd (Hall196.relIndex_sup_sec19Y_of_sec19DataT hd).2.2 h1

theorem isSL2Three_sec19X_of_case2 (hd : Sec19DataT p f K z S W L t V)
    (h1 : W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W) :
    IsSL2Three (sec19X K z) (K ⊔ oddCoreOf (sec19X K z)) (p ^ f) :=
  isSL2Three_sec19X hd (Hall196.relIndex_sup_sec19Y_of_sec19DataT hd).2.2 h1

omit [IsSimpleGroup G] in
theorem le_normalizer_inf_sec19X (hd : Sec19DataT p f K z S W L t V) :
    (S : Subgroup G) ≤ Subgroup.normalizer (((S : Subgroup G) ⊓ sec19X K z : Subgroup G) :
      Set G) := by
  intro s hs
  have hX := Hall196.centralizer_le_normalizer_sec19X K z (hd.hSz hs)
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  rw [conjSub, Subgroup.map_inf_eq _ _ _ (MulAut.conj s).injective]
  change conjSub s (S : Subgroup G) ⊓ conjSub s (sec19X K z) = _
  rw [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hs),
    conjSub_eq_of_mem_normalizer hX]

theorem inf_sec19X_eq_of_case2 (hd : Sec19DataT p f K z S W L t V)
    (h1 : W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W) :
    (S : Subgroup G) ⊓ sec19X K z = (S : Subgroup G) ⊓ K ⊔ V :=
  inf_sec19X_eq hd (sec19X_eq_of_case2 hd h1)

theorem isWreathed_inf_sec19X_of_case2 (hd : Sec19DataT p f K z S W L t V)
    (h1 : W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W) :
    IsWreathed ((S : Subgroup G) ⊓ sec19X K z) := by
  rw [inf_sec19X_eq_of_case2 hd h1]
  exact Hall196.isWreathed_inf_sup hd

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

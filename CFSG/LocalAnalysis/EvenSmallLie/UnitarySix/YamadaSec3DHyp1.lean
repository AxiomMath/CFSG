module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DTools

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open scoped commutatorElement

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46} {t : G}

theorem toG_ch_le {c c' : ChainData} (h : ∀ w ∈ c.gens, w ∈ c'.gens) :
    toG e c.grp ≤ toG e c'.grp :=
  toG_mono (grp_le_of_subset h)

theorem gw_mem_ch {c : ChainData} {w : List ℕ} (hw : ∀ k ∈ w, k < 18 ∧ [k] ∈ c.gens) :
    gw e w ∈ toG e c.grp :=
  (gw_mem_toG fun k hk => (hw k hk).1).2 (wP_mem_of_letters w fun k hk => (hw k hk).2)

theorem gw_eq_xId {a b : List ℕ} (h : (a, b) ∈ xIds) (ha : ∀ k ∈ a, k < 18)
    (hb : ∀ k ∈ b, k < 18) : gw e a = gw e b :=
  gw_eq_gw ha hb (xId_of_mem h)

theorem card_toG_ch {c : ChainData} (hc : c.GensOK) : Nat.card (toG e c.grp) = Nat.card c.grp :=
  card_toG (grp_le_T46 hc)

theorem gw_mem_centralizer_toG {c : ChainData} {w : List ℕ} (hw : ∀ k ∈ w, k < 18)
    (h : wP w ∈ centralizer (c.grp : Set (Equiv.Perm (Fin 693)))) :
    gw e w ∈ centralizer (toG e c.grp : Set G) := by
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨k, hk, rfl⟩ := mem_toG.1 hy
  rw [gw_eq w hw, ← map_mul, ← map_mul]
  exact congrArg (iotaG e) (Subtype.ext (mem_centralizer_iff.1 h k hk))

theorem gw_mem_normalizer_toG {c : ChainData} (hc : c.GensOK) {w : List ℕ} (hw : ∀ k ∈ w, k < 18)
    (h : wP w ∈ normalizer (c.grp : Set (Equiv.Perm (Fin 693)))) :
    gw e w ∈ normalizer (toG e c.grp : Set G) := by
  have h1 : gw e w ∈ toG e (normalizer (c.grp : Set (Equiv.Perm (Fin 693))) ⊓ T46) :=
    (gw_mem_toG hw).2 ⟨h, wP_mem_T46 w hw⟩
  rw [← normalizer_toG (grp_le_T46 hc)] at h1
  exact h1.1

theorem iotaG_comm (a b : T46) : ⁅iotaG e a, iotaG e b⁆ = iotaG e ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]

theorem iotaG_comm_mem {H : Subgroup (Equiv.Perm (Fin 693))} {a b : T46}
    (h : ⁅(a : Equiv.Perm (Fin 693)), (b : Equiv.Perm (Fin 693))⁆ ∈ H) :
    ⁅iotaG e a, iotaG e b⁆ ∈ toG e H := by
  rw [iotaG_comm]
  exact iotaG_mem_toG.2 (by simpa [commutatorElement_def] using h)

theorem grp_sq_of_comm {c : ChainData} (hc : c.GensOK)
    (hcomm : c.grp ≤ centralizer (c.grp : Set (Equiv.Perm (Fin 693))))
    (hgen : ∀ w ∈ c.gens, w.length = 1) : ∀ x ∈ c.grp, x * x = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨k, rfl⟩ := List.length_eq_one_iff.1 (hgen w hw)
    rw [wP_single]
    exact gP_mul_self (by simpa using hc _ hw)
  | one => rw [one_mul]
  | mul x y hx hy ihx ihy =>
    have hxy : x * y = y * x := mem_centralizer_iff.1 (hcomm hy) x hx
    calc x * y * (x * y) = x * x * (y * y) := by
          rw [mul_assoc, ← mul_assoc y x y, ← hxy, mul_assoc, mul_assoc]
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x _ ihx => rw [← mul_inv_rev, ihx, inv_one]

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3

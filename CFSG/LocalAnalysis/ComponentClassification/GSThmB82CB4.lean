module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4h
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82L2

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer Seven
open scoped commutatorElement

namespace Eight2

variable {X : Type} [Group X] [Finite X]

theorem a_mem_commutator {h : Hyp52 X} {y : X} (hyP : y ∈ h.P) (h61 : h.Lemma61Shape y) :
    h.a ∈ ⁅h.S, h.S⁆ := by
  have hyS : y ∈ h.S := (mem_inf.mp hyP).1
  rcases h61 with h1 | ⟨b, -, hbx, -, hbB, -⟩
  · have ha : h.a ∈ ⁅h.B, zpowers y⁆ := h1 ▸ mem_zpowers _
    exact commutator_mono (h.B_le.trans inf_le_left) (zpowers_le.mpr hyS) ha
  · have hbS : b ∈ h.S := h.B_le_S (mem_inf.mp hbB).1
    have hxS : h.x⁻¹ ∈ h.S := inv_mem h.x_mem
    have h1 : ⁅h.x⁻¹, b⁆ = h.a := by
      rw [commutatorElement_def, inv_inv, hbx]
      group
    rw [← h1]
    exact commutator_mem_commutator hxS hbS

omit [Finite X] in
theorem commutator_le_self' (D : Subgroup X) : ⁅D, D⁆ ≤ D :=
  commutator_le.mpr fun _ h₁ _ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

omit [Finite X] in
theorem conj_mem_commutator_self {D : Subgroup X} {s w : X} (hs : s ∈ D) (hw : w ∈ ⁅D, D⁆) :
    s * w * s⁻¹ ∈ ⁅D, D⁆ := by
  have hD : D.map (MulAut.conj s).toMonoidHom = D := by
    ext v
    constructor
    · rintro ⟨v', hv', rfl⟩
      exact mul_mem (mul_mem hs hv') (inv_mem hs)
    · intro hv
      refine ⟨s⁻¹ * v * s, mul_mem (mul_mem (inv_mem hs) hv) hs, ?_⟩
      change s * (s⁻¹ * v * s) * s⁻¹ = v
      group
  have h1 : ⁅D, D⁆.map (MulAut.conj s).toMonoidHom = ⁅D, D⁆ := by
    rw [map_commutator, hD]
  rw [← h1]
  exact ⟨w, hw, rfl⟩

variable {h : Hyp52 X}

theorem z_mem_commutator (Z : ZData h) (hD8 : 8 ≤ Nat.card h.D) : Z.z ∈ ⁅h.S, h.S⁆ := by
  have hD2 : IsPGroup 2 h.D := h.isPGroup_S.to_le h.D_le_S
  have hne : ⁅h.D, h.D⁆ ≠ ⊥ := by
    intro hbot
    have hcomm : ∀ v ∈ h.D, ∀ d ∈ h.D, v * d = d * v := by
      intro v hv d hd
      have h1 : ⁅v, d⁆ ∈ ⁅h.D, h.D⁆ := commutator_mem_commutator hv hd
      rw [hbot, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hle : h.D ≤ zpowers Z.z := by
      intro v hv
      rcases Z.hZDz v hv (hcomm v hv) with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
    have h2 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_two_of Z.hzz Z.hz1] at h2
    omega
  obtain ⟨w, hw, hw1, hwZ⟩ := exists_mem_center_of_normal hD2 (commutator_le_self' _)
    (fun s hs v hv => conj_mem_commutator_self hs hv) hne
  have hwD : w ∈ h.D := commutator_le_self' _ hw
  rcases Z.hZDz w hwD (fun d hd => (hwZ d hd).symm) with h1 | h1
  · exact absurd h1 hw1
  · rw [← h1]
    exact commutator_mono h.D_le_S h.D_le_S hw

theorem rhoE_mem_commutator {w : X} (hw : w ∈ ⁅h.S, h.S⁆) :
    rhoE h.J w ∈ commutator (MulAut (Jbar h)) := by
  have hSN : h.S ≤ normalizer (h.J : Set X) := h.S_le_normalizer
  have h1 : ⁅h.S, h.S⁆ ≤ ⁅normalizer (h.J : Set X), normalizer (h.J : Set X)⁆ :=
    commutator_mono hSN hSN
  have h2 : ⁅normalizer (h.J : Set X), normalizer (h.J : Set X)⁆ =
      (commutator ↥(normalizer (h.J : Set X))).map (normalizer (h.J : Set X)).subtype := by
    rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  obtain ⟨w', hw', rfl⟩ := (h2 ▸ h1 hw : w ∈ _)
  show rhoE h.J (w' : X) ∈ _
  rw [rhoE_of_mem w'.2]
  have h3 : (commutator ↥(normalizer (h.J : Set X))).map (Eight.oddBarAction h.J) ≤
      commutator (MulAut (Jbar h)) := by
    rw [commutator_def, commutator_def, map_commutator]
    exact commutator_mono le_top le_top
  exact h3 ⟨w', hw', rfl⟩

theorem comm_center_cases (hComm : CF82L2Comm) (Z : ZData h)
    (hC : h.P ⊓ centralizer (h.S : Set X) = zpowers h.a) {w : X} (hw : w ∈ ⁅h.S, h.S⁆)
    (hwZ : ∀ t ∈ h.S, t * w = w * t) :
    w = 1 ∨ w = h.a ∨ w = Z.z ∨ w = h.a * Z.z := by
  have hwS : w ∈ h.S := commutator_le_self' _ hw
  have hSN : h.S ≤ normalizer (h.J : Set X) := h.S_le_normalizer
  obtain ⟨T₀, hT₀⟩ := Z.sylow
  obtain ⟨p, f, hp, hp2, hf, hJL⟩ := Z.lie
  have hT8 : 8 ≤ Nat.card T₀ := by
    have := Z.h8
    rwa [← hT₀] at this
  have hwc : rhoE h.J w ∈ centralizer (innOf (T₀ : Subgroup (Jbar h)) : Set (MulAut (Jbar h))) := by
    rw [hT₀, ← rhoImg_eq_innOf h.D_le_J, mem_centralizer_iff]
    rintro _ ⟨⟨d, hdN⟩, hd, rfl⟩
    rw [← rhoE_of_mem hdN, ← rhoE_mul hdN (hSN hwS), ← rhoE_mul (hSN hwS) hdN,
      hwZ d (h.D_le_S (mem_subgroupOf.mp hd))]
  obtain ⟨t, htT, htC, hσ⟩ := hComm _ p f hp hp2 hf hJL T₀ hT8 _ (rhoE_mem_commutator hw) hwc
  rw [hT₀] at htT htC
  have hPZ : ∀ v ∈ h.P, (∀ t ∈ h.S, t * v = v * t) → v = 1 ∨ v = h.a := by
    intro v hvP hvZ
    have hv : v ∈ h.P ⊓ centralizer (h.S : Set X) :=
      mem_inf.mpr ⟨hvP, mem_centralizer_iff.mpr hvZ⟩
    rw [hC] at hv
    exact eq_one_or_of_mem_zpowers h.orderOf_a hv
  have hzS : Z.z ∈ h.S := h.D_le_S Z.hzD
  rcases Z.hZD t htT htC with h1 | h1 <;> rw [← hσ] at h1
  · have hwP : w ∈ h.P := mem_inf.mpr ⟨hwS, (rhoE_eq_one_iff (hSN hwS)).mp h1⟩
    rcases hPZ w hwP hwZ with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
  · have hz' : Z.z⁻¹ = Z.z := inv_eq_of_mul_eq_one_right Z.hzz
    have hwz : w * Z.z ∈ h.P := by
      refine mem_inf.mpr ⟨mul_mem hwS hzS, (rhoE_eq_one_iff (mul_mem (hSN hwS) (hSN hzS))).mp ?_⟩
      rw [rhoE_mul (hSN hwS) (hSN hzS), h1, ← rhoE_mul (hSN hzS) (hSN hzS), Z.hzz, rhoE_one]
    have hwzZ : ∀ t ∈ h.S, t * (w * Z.z) = w * Z.z * t := fun t ht => by
      rw [← mul_assoc, hwZ t ht, mul_assoc, Z.hzS t ht, mul_assoc]
    rcases hPZ _ hwz hwzZ with h2 | h2
    · right; right; left
      calc w = w * Z.z * Z.z := by rw [mul_assoc, Z.hzz, mul_one]
        _ = Z.z := by rw [h2, one_mul]
    · right; right; right
      calc w = w * Z.z * Z.z := by rw [mul_assoc, Z.hzz, mul_one]
        _ = h.a * Z.z := by rw [h2]

end Eight2

end CFSG.ComponentClassification.GSThmB

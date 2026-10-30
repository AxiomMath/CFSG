module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Prod
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

private lemma isElemAbelian_of_le {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E)
    {H : Subgroup G} (hH : H ≤ E) : CFSG.Open.IsElemAbelian 2 H := by
  refine ⟨?_, ?_⟩
  · rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    simpa using isMulCommutative_iff.mp hE.1 ⟨a, hH a.2⟩ ⟨b, hH b.2⟩
  · intro x hx
    exact hE.2 x (hH hx)

private lemma inf_zpowers_eq_bot_of_notMem {W : Subgroup G} {v : G} (hv2 : v ^ 2 = 1)
    (hvW : v ∉ W) : W ⊓ Subgroup.zpowers v = ⊥ := by
  have hv1 : v ≠ 1 := fun h => hvW (h ▸ W.one_mem)
  have hvorder : orderOf v = 2 := orderOf_eq_prime hv2 hv1
  rw [Subgroup.eq_bot_iff_card]
  have hdvd : Nat.card ↥(W ⊓ Subgroup.zpowers v) ∣ 2 := by
    have h := Subgroup.card_dvd_of_le (H := W ⊓ Subgroup.zpowers v)
      (K := Subgroup.zpowers v) inf_le_right
    rwa [Nat.card_zpowers, hvorder] at h
  have hne : Nat.card ↥(W ⊓ Subgroup.zpowers v) ≠ 2 := by
    intro h2
    have heq : W ⊓ Subgroup.zpowers v = Subgroup.zpowers v := by
      refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
      rw [h2, Nat.card_zpowers, hvorder]
    have : v ∈ W ⊓ Subgroup.zpowers v := by
      rw [heq]; exact Subgroup.mem_zpowers v
    exact hvW this.1
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact h1
  · exact absurd h2 hne

private lemma mem_sup_zpowers_iff {H : Subgroup G} {v z : G}
    (hcomm : ∀ h ∈ H, v * h = h * v) (hv2 : v ^ 2 = 1) :
    z ∈ H ⊔ Subgroup.zpowers v ↔ z ∈ H ∨ ∃ h ∈ H, z = h * v := by
  have hv1 : v * v = 1 := by simpa [pow_two] using hv2
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv1
  constructor
  · intro hz
    let S : Subgroup G :=
      { carrier := {y | y ∈ H ∨ ∃ h ∈ H, y = h * v}
        one_mem' := Or.inl H.one_mem
        mul_mem' := by
          rintro a b (ha | ⟨ha, haH, rfl⟩) (hb | ⟨hb, hbH, rfl⟩)
          · exact Or.inl (H.mul_mem ha hb)
          · exact Or.inr ⟨a * hb, H.mul_mem ha hbH, by rw [mul_assoc]⟩
          · exact Or.inr ⟨ha * b, H.mul_mem haH hb,
              by rw [mul_assoc, hcomm b hb, ← mul_assoc]⟩
          · exact Or.inl (by
              have e : (ha * v) * (hb * v) = ha * hb := by
                calc (ha * v) * (hb * v) = ha * (v * (hb * v)) := mul_assoc ha v (hb * v)
                  _ = ha * ((v * hb) * v) := by rw [mul_assoc v hb v]
                  _ = ha * ((hb * v) * v) := by rw [hcomm hb hbH]
                  _ = ha * (hb * (v * v)) := by rw [mul_assoc hb v v]
                  _ = ha * (hb * 1) := by rw [hv1]
                  _ = ha * hb := by rw [mul_one]
              rw [e]; exact H.mul_mem haH hbH)
        inv_mem' := by
          rintro a (ha | ⟨ha, haH, rfl⟩)
          · exact Or.inl (H.inv_mem ha)
          · refine Or.inr ⟨ha⁻¹, H.inv_mem haH, ?_⟩
            rw [mul_inv_rev, hvinv, hcomm ha⁻¹ (H.inv_mem haH)] }
    have hHS : H ≤ S := fun a ha => Or.inl ha
    have hvS : v ∈ S := Or.inr ⟨1, H.one_mem, by rw [one_mul]⟩
    have hzS : z ∈ S := (sup_le hHS (Subgroup.zpowers_le.mpr hvS)) hz
    exact hzS
  · rintro (hz | ⟨h, hh, rfl⟩)
    · exact Subgroup.mem_sup_left hz
    · exact (H ⊔ Subgroup.zpowers v).mul_mem (Subgroup.mem_sup_left hh)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))

private lemma sec8t84_sup_zpowers_card {Q : Subgroup G} (hQ : CFSG.Open.IsElemAbelian 2 Q)
    {W : Subgroup G} (hWQ : W ≤ Q) (hWcard : Nat.card W = 8)
    {v : G} (hvQ : v ∈ Q) (hv2 : v ^ 2 = 1) (hvW : v ∉ W) :
    Nat.card ↥(W ⊔ Subgroup.zpowers v) = 16 ∧
      CFSG.Open.IsElemAbelian 2 (W ⊔ Subgroup.zpowers v) ∧
      v ∈ W ⊔ Subgroup.zpowers v ∧ W ≤ W ⊔ Subgroup.zpowers v := by
  have hzvQ : Subgroup.zpowers v ≤ Q := Subgroup.zpowers_le.mpr hvQ
  have hcomm : ∀ a ∈ W, ∀ b ∈ Subgroup.zpowers v, a * b = b * a := by
    intro a ha b hb
    have h := isMulCommutative_iff.mp hQ.1 ⟨a, hWQ ha⟩ ⟨b, hzvQ hb⟩
    simpa using h
  have hinf : W ⊓ Subgroup.zpowers v = ⊥ := inf_zpowers_eq_bot_of_notMem hv2 hvW
  have hcard : Nat.card ↥(W ⊔ Subgroup.zpowers v) = 16 := by
    rw [sec124_card_sup hcomm hinf, hWcard]
    have hv1 : v ≠ 1 := fun h => hvW (h ▸ W.one_mem)
    have hvorder : orderOf v = 2 := orderOf_eq_prime hv2 hv1
    have : Nat.card ↥(Subgroup.zpowers v) = 2 := by rw [Nat.card_zpowers, hvorder]
    rw [this]
  exact ⟨hcard, isElemAbelian_of_le hQ (sup_le hWQ hzvQ),
    Subgroup.mem_sup_right (Subgroup.mem_zpowers v), le_sup_left⟩

theorem sec8t84_no_e32 {G : Type} [Group G] [Finite G] {P B1 B2 : Subgroup G}
    (hP : ∀ B : Subgroup G, B ≤ P → CFSG.Open.IsElemAbelian 2 B → Nat.card B = 16 →
      B = B1 ∨ B = B2)
    {Q : Subgroup G} (hQP : Q ≤ P) (hQ : CFSG.Open.IsElemAbelian 2 Q) : Nat.card Q ≤ 16 := by
  by_contra hle
  rw [not_le] at hle
  have hP2 : IsPGroup 2 Q := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hQ.2 (g : G) g.2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
  have hk5 : 5 ≤ k := by
    have h4 : 4 < k := by
      have hpow : 2 ^ 4 < 2 ^ k := by
        rw [← hk]; norm_num; exact hle
      exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hpow
    omega
  have hcardQ32 : 2 ^ 5 ≤ Nat.card Q := by
    rw [hk]; exact Nat.pow_le_pow_right (by norm_num) hk5
  obtain ⟨H', hH'le, hH'card⟩ :=
    Sylow.exists_subgroup_le_card_pow_prime_of_le_card (G := Q) (H := ⊤) (n := 5)
      Nat.prime_two hP2 (by simpa [Subgroup.card_top] using hcardQ32)
  let Q' : Subgroup G := H'.map Q.subtype
  have hQ'card : Nat.card Q' = 32 := by
    dsimp only [Q']
    rw [Subgroup.card_map_of_injective Q.subtype_injective, hH'card]
    norm_num
  have hQ'leQ : Q' ≤ Q := Subgroup.map_subtype_le H'
  have hcardH'8 : 2 ^ 3 ≤ Nat.card H' := by rw [hH'card]; norm_num
  obtain ⟨H'', hH''le, hH''card⟩ :=
    Sylow.exists_subgroup_le_card_pow_prime_of_le_card (G := Q) (H := H') (n := 3)
      Nat.prime_two hP2 hcardH'8
  let W : Subgroup G := H''.map Q.subtype
  have hWcard : Nat.card W = 8 := by
    dsimp only [W]
    rw [Subgroup.card_map_of_injective Q.subtype_injective, hH''card]
    norm_num
  have hWleQ' : W ≤ Q' := Subgroup.map_mono hH''le
  have hWQ : W ≤ Q := hWleQ'.trans hQ'leQ
  have hWneQ' : W ≠ Q' := by
    intro h
    have : Nat.card W = Nat.card Q' := by rw [h]
    rw [hWcard, hQ'card] at this
    norm_num at this
  obtain ⟨x, hxQ', hxW⟩ : ∃ x, x ∈ Q' ∧ x ∉ W := by
    by_contra h
    push Not at h
    exact hWneQ' (le_antisymm hWleQ' (fun y hy => h y hy))
  have hxQ : x ∈ Q := hQ'leQ hxQ'
  have hx2 : x ^ 2 = 1 := hQ.2 x hxQ
  obtain ⟨hcardA1, heA1, hxA1, hWA1⟩ :=
    sec8t84_sup_zpowers_card hQ hWQ hWcard hxQ hx2 hxW
  let A1 : Subgroup G := W ⊔ Subgroup.zpowers x
  have hA1leQ' : A1 ≤ Q' := sup_le hWleQ' (Subgroup.zpowers_le.mpr hxQ')
  have hA1leQ : A1 ≤ Q := hA1leQ'.trans hQ'leQ
  have hA1leP : A1 ≤ P := hA1leQ.trans hQP
  have hA1neQ' : A1 ≠ Q' := by
    intro h
    have : Nat.card A1 = Nat.card Q' := by rw [h]
    rw [hcardA1, hQ'card] at this
    norm_num at this
  obtain ⟨y, hyQ', hyA1⟩ : ∃ y, y ∈ Q' ∧ y ∉ A1 := by
    by_contra h
    push Not at h
    exact hA1neQ' (le_antisymm hA1leQ' (fun y hy => h y hy))
  have hyQ : y ∈ Q := hQ'leQ hyQ'
  have hy2 : y ^ 2 = 1 := hQ.2 y hyQ
  have hyW : y ∉ W := fun h => hyA1 (hWA1 h)
  obtain ⟨hcardA2, heA2, hyA2, _⟩ :=
    sec8t84_sup_zpowers_card hQ hWQ hWcard hyQ hy2 hyW
  let A2 : Subgroup G := W ⊔ Subgroup.zpowers y
  have hA2leQ' : A2 ≤ Q' := sup_le hWleQ' (Subgroup.zpowers_le.mpr hyQ')
  have hA2leQ : A2 ≤ Q := hA2leQ'.trans hQ'leQ
  have hA2leP : A2 ≤ P := hA2leQ.trans hQP
  have hxyQ' : x * y ∈ Q' := Q'.mul_mem hxQ' hyQ'
  have hxyQ : x * y ∈ Q := hQ'leQ hxyQ'
  have hxy2 : (x * y) ^ 2 = 1 := hQ.2 (x * y) hxyQ
  have hxyW : x * y ∉ W := by
    intro h
    have hxyA1 : x * y ∈ A1 := hWA1 h
    have : y ∈ A1 := by
      have h1 : x⁻¹ * (x * y) = y := by group
      rw [← h1]
      exact A1.mul_mem (A1.inv_mem hxA1) hxyA1
    exact hyA1 this
  obtain ⟨hcardA3, heA3, hxyA3, _⟩ :=
    sec8t84_sup_zpowers_card hQ hWQ hWcard hxyQ hxy2 hxyW
  let A3 : Subgroup G := W ⊔ Subgroup.zpowers (x * y)
  have hA3leQ' : A3 ≤ Q' := sup_le hWleQ' (Subgroup.zpowers_le.mpr hxyQ')
  have hA3leQ : A3 ≤ Q := hA3leQ'.trans hQ'leQ
  have hA3leP : A3 ≤ P := hA3leQ.trans hQP
  have hcomm_y : ∀ w ∈ W, y * w = w * y := by
    intro w hw
    have h := isMulCommutative_iff.mp hQ.1 ⟨y, hyQ⟩ ⟨w, hWQ hw⟩
    simpa using h
  have hcomm_xy : ∀ w ∈ W, (x * y) * w = w * (x * y) := by
    intro w hw
    have h := isMulCommutative_iff.mp hQ.1 ⟨x * y, hxyQ⟩ ⟨w, hWQ hw⟩
    simpa using h
  have h12 : A1 ≠ A2 := by
    intro h
    have hxA2 : x ∈ A2 := h ▸ hxA1
    change x ∈ W ⊔ Subgroup.zpowers y at hxA2
    rw [mem_sup_zpowers_iff hcomm_y hy2] at hxA2
    rcases hxA2 with hxW' | ⟨w, hw, hxw⟩
    · exact hxW hxW'
    · have : y ∈ A1 := by
        have hwy : w * y ∈ A1 := hxw ▸ hxA1
        have h1 : w⁻¹ * (w * y) = y := by group
        rw [← h1]
        exact A1.mul_mem (A1.inv_mem (hWA1 hw)) hwy
      exact hyA1 this
  have h13 : A1 ≠ A3 := by
    intro h
    have hxA3 : x ∈ A3 := h ▸ hxA1
    change x ∈ W ⊔ Subgroup.zpowers (x * y) at hxA3
    rw [mem_sup_zpowers_iff hcomm_xy hxy2] at hxA3
    rcases hxA3 with hxW' | ⟨w, hw, hxw⟩
    · exact hxW hxW'
    · have : y ∈ A1 := by
        have hw2 : w * w = 1 := by
          have h := hQ.2 w (hWQ hw); simpa [pow_two] using h
        have hwx : w * x = x * y := by
          nth_rewrite 1 [hxw]
          rw [← mul_assoc, hw2, one_mul]
        have h1 : x⁻¹ * (w * x) = y := by
          rw [hwx, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [← h1]
        exact A1.mul_mem (A1.inv_mem hxA1) (A1.mul_mem (hWA1 hw) hxA1)
      exact hyA1 this
  have h23 : A2 ≠ A3 := by
    intro h
    have hyA3 : y ∈ A3 := h ▸ hyA2
    change y ∈ W ⊔ Subgroup.zpowers (x * y) at hyA3
    rw [mem_sup_zpowers_iff hcomm_xy hxy2] at hyA3
    rcases hyA3 with hyW' | ⟨w, hw, hyw⟩
    · exact hyW hyW'
    · have hxW' : x ∈ W := by
        have h1 : w⁻¹ * y = x * y := by
          nth_rewrite 1 [hyw]
          rw [← mul_assoc, inv_mul_cancel, one_mul]
        have : x = w⁻¹ := (mul_right_cancel h1).symm
        rw [this]; exact W.inv_mem hw
      exact hxW hxW'
  have hb1 : A1 = B1 ∨ A1 = B2 := hP A1 hA1leP heA1 hcardA1
  have hb2 : A2 = B1 ∨ A2 = B2 := hP A2 hA2leP heA2 hcardA2
  have hb3 : A3 = B1 ∨ A3 = B2 := hP A3 hA3leP heA3 hcardA3
  rcases hb1 with h1 | h1 <;> rcases hb2 with h2 | h2 <;> rcases hb3 with h3 | h3
  · exact h12 (h1.trans h2.symm)
  · exact h12 (h1.trans h2.symm)
  · exact h13 (h1.trans h3.symm)
  · exact h23 (h2.trans h3.symm)
  · exact h23 (h2.trans h3.symm)
  · exact h13 (h1.trans h3.symm)
  · exact h12 (h1.trans h2.symm)
  · exact h12 (h1.trans h2.symm)

end CFSG.OddStandard.SmallF3.Omega

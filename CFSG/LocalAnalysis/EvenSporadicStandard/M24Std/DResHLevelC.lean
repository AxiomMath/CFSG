module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResHLevelCA

public section

namespace CFSG.EvenSporadicStandard.M24Std.DResH

open Subgroup CFSG.EvenSporadicStandard.M24Std.DRes Fixed

open LevelC Heisenberg

set_option linter.unusedVariables false in
theorem levelC
    {V : Type*} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v * v = 1) (hV : Nat.card V = 2 ^ 12)
    {Y : Type} [Group Y] (ρ : Y →* MulAut V)
    {S1 S2 Z1 Z2 : Subgroup Y} {π1 : S1 →* alternatingGroup (Fin 6)}
    {π2 : S2 →* alternatingGroup (Fin 6)}
    (q1 : QuasiData S1 Z1 π1) (q2 : QuasiData S2 Z2 π2)
    (hcomm : ∀ a ∈ S1, ∀ b ∈ S2, a * b = b * a)
    (t : Y) (ht : t * t = 1) (hts : ∀ a ∈ S1, t * a * t⁻¹ ∈ S2)
    (hts' : ∀ a ∈ S2, t * a * t⁻¹ ∈ S1)
    (z1 : Y) (hz1 : z1 ∈ Z1) (hz1ne : z1 ≠ 1) (hz2 : t * z1 * t⁻¹ ∈ Z2)
    (hfpf : ∀ v : V, ρ (z1 * (t * z1 * t⁻¹)) v = v → v = 1)
    (c d : Y) (hc : c ∈ S2) (hd : d ∈ S2) (hc3 : c * c * c = 1) (hd3 : d * d * d = 1)
    (hcd : c * d * c⁻¹ * d⁻¹ = t * z1 * t⁻¹) :
    ∃ D1 D2 : Subgroup V, Nat.card D1 = 2 ^ 6 ∧ Nat.card D2 = 2 ^ 6 ∧ D1 ⊓ D2 = ⊥ ∧
      D1 ⊔ D2 = ⊤ ∧
      (∀ s ∈ S2, ∀ v ∈ D1, ρ s v = v) ∧ (∀ s ∈ S1, ∀ v ∈ D2, ρ s v = v) ∧
      (∀ v : V, (∀ s ∈ S2, ρ s v = v) → v ∈ D1) ∧
      (∀ v : V, (∀ s ∈ S1, ρ s v = v) → v ∈ D2) ∧
      (∀ v ∈ D1, ∃ w ∈ D1, ρ z1 w * w⁻¹ = v) ∧
      (∀ v ∈ D2, ∃ w ∈ D2, ρ (t * z1 * t⁻¹) w * w⁻¹ = v) ∧
      (∀ v ∈ D1, ρ t v ∈ D2) ∧ (∀ v ∈ D2, ρ t v ∈ D1) ∧ S1 ⊓ S2 = ⊥ := by
  obtain ⟨z2, hz2def⟩ : ∃ z2 : Y, z2 = t * z1 * t⁻¹ := ⟨_, rfl⟩
  rw [← hz2def] at hz2 hfpf hcd ⊢
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hz1S : z1 ∈ S1 := q1.Z_le hz1
  have hz2S : z2 ∈ S2 := q2.Z_le hz2
  have hz13 : z1 * z1 * z1 = 1 := cube_eq_one_of_card_three q1.card_Z hz1
  have hz23 : z2 * z2 * z2 = 1 := cube_eq_one_of_card_three q2.card_Z hz2
  have hz2ne : z2 ≠ 1 := by
    intro h
    apply hz1ne
    have h1 : t * z1 * t⁻¹ = 1 := hz2def ▸ h
    calc z1 = t⁻¹ * (t * z1 * t⁻¹) * t := by group
      _ = 1 := by rw [h1]; group
  have hz1c : ∀ g ∈ S1, g * z1 = z1 * g := fun g hg => q1.central g hg z1 hz1
  have hz1c' : ∀ g ∈ S2, g * z1 = z1 * g := fun g hg => (hcomm z1 hz1S g hg).symm
  have hz2c : ∀ g ∈ S2, g * z2 = z2 * g := fun g hg => q2.central g hg z2 hz2
  have hz2c' : ∀ g ∈ S1, g * z2 = z2 * g := fun g hg => hcomm g hg z2 hz2S
  have hz12 : z1 * z2 = z2 * z1 := hcomm z1 hz1S z2 hz2S
  have hω13 : ρ z1 * ρ z1 * ρ z1 = 1 := by rw [← map_mul, ← map_mul, hz13, map_one]
  have hω23 : ρ z2 * ρ z2 * ρ z2 = 1 := by rw [← map_mul, ← map_mul, hz23, map_one]
  have hω12 : ρ z1 * ρ z2 = ρ z2 * ρ z1 := by rw [← map_mul, ← map_mul, hz12]
  have hfpf' : ∀ v : V, (ρ z1 * ρ z2) v = v → v = 1 := fun v hv =>
    hfpf v (by rw [map_mul]; exact hv)
  have hnotinv : ρ z1 * ρ z2 ≠ 1 := by
    intro h
    have hall : ∀ v : V, v = 1 := fun v => hfpf' v (by rw [h]; rfl)
    have h1 : Nat.card V = 1 := Nat.card_eq_one_iff_unique.2
      ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
    rw [hV] at h1
    norm_num at h1
  have hne : ρ z1 ≠ ρ z2 := by
    intro heq
    have ha : t * c * t⁻¹ ∈ S1 := hts' c hc
    have hb : t * d * t⁻¹ ∈ S1 := hts' d hd
    have hab : (t * c * t⁻¹) * (t * d * t⁻¹) * (t * c * t⁻¹)⁻¹ * (t * d * t⁻¹)⁻¹ = z1 := by
      calc (t * c * t⁻¹) * (t * d * t⁻¹) * (t * c * t⁻¹)⁻¹ * (t * d * t⁻¹)⁻¹
          = t * (c * d * c⁻¹ * d⁻¹) * t⁻¹ := by group
        _ = t * (t * z1 * t⁻¹) * t⁻¹ := by rw [hcd, hz2def]
        _ = (t * t) * z1 * (t⁻¹ * t⁻¹) := by group
        _ = z1 := by rw [ht, ← mul_inv_rev, ht]; group
    have hab' : (t * c * t⁻¹) * (t * d * t⁻¹) = z1 * (t * d * t⁻¹) * (t * c * t⁻¹) := by
      calc (t * c * t⁻¹) * (t * d * t⁻¹)
          = ((t * c * t⁻¹) * (t * d * t⁻¹) * (t * c * t⁻¹)⁻¹ * (t * d * t⁻¹)⁻¹) *
            (t * d * t⁻¹) * (t * c * t⁻¹) := by group
        _ = z1 * (t * d * t⁻¹) * (t * c * t⁻¹) := by rw [hab]
    have hb3 : (t * d * t⁻¹) * (t * d * t⁻¹) * (t * d * t⁻¹) = 1 := by
      calc _ = t * (d * d * d) * t⁻¹ := by group
        _ = 1 := by rw [hd3]; group
    have hcd' : c * d = z2 * d * c := by
      calc c * d = (c * d * c⁻¹ * d⁻¹) * d * c := by group
        _ = z2 * d * c := by rw [hcd]
    refine false_of_two_heisenberg hV2 hV (ρ z1) (ρ (t * c * t⁻¹)) (ρ (t * d * t⁻¹)) (ρ c) (ρ d)
      hω13 (fun v hv => hfpf' v ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (Or.inl ?_)
    · show ρ z1 (ρ z2 v) = v
      rw [← heq, hv, hv]
    · rw [← map_mul, ← map_mul, hb3, map_one]
    · rw [← map_mul, ← map_mul, hd3, map_one]
    · rw [← map_mul, ← map_mul, hz1c _ ha]
    · rw [← map_mul, ← map_mul, hz1c _ hb]
    · rw [← map_mul, ← map_mul, hz1c' _ hc]
    · rw [← map_mul, ← map_mul, hz1c' _ hd]
    · rw [← map_mul, ← map_mul, hcomm _ hb _ hc]
    · rw [← map_mul, ← map_mul, hcomm _ hb _ hd]
    · rw [← map_mul, ← map_mul, ← map_mul, hab']
    · calc ρ c * ρ d = ρ (c * d) := (map_mul ρ c d).symm
        _ = ρ (z2 * d * c) := by rw [hcd']
        _ = ρ z2 * ρ d * ρ c := by rw [map_mul, map_mul]
        _ = ρ z1 * ρ d * ρ c := by rw [← heq]
  obtain ⟨D2, hD2⟩ : ∃ D : Subgroup V, D = fixedSubgroupAut (ρ z1) := ⟨_, rfl⟩
  obtain ⟨D1, hD1⟩ : ∃ D : Subgroup V, D = fixedSubgroupAut (ρ z2) := ⟨_, rfl⟩
  have memD2 : ∀ v : V, v ∈ D2 ↔ ρ z1 v = v := fun v => by
    rw [hD2]; exact mem_fixedSubgroupAut
  have memD1 : ∀ v : V, v ∈ D1 ↔ ρ z2 v = v := fun v => by
    rw [hD1]; exact mem_fixedSubgroupAut
  have inv : ∀ (z : Y) (D : Subgroup V), D = fixedSubgroupAut (ρ z) → ∀ s : Y, s * z = z * s →
      ∀ v ∈ D, ρ s v ∈ D := by
    intro z D hD s hs v hv
    subst hD
    refine fixedSubgroupAut_invariant ?_ v hv
    rw [← map_mul, ← map_mul, hs]
  have inv2S1 : ∀ s ∈ S1, ∀ v ∈ D2, ρ s v ∈ D2 := fun s hs => inv z1 D2 hD2 s (hz1c s hs)
  have inv2S2 : ∀ s ∈ S2, ∀ v ∈ D2, ρ s v ∈ D2 := fun s hs => inv z1 D2 hD2 s (hz1c' s hs)
  have inv1S1 : ∀ s ∈ S1, ∀ v ∈ D1, ρ s v ∈ D1 := fun s hs => inv z2 D1 hD1 s (hz2c' s hs)
  have inv1S2 : ∀ s ∈ S2, ∀ v ∈ D1, ρ s v ∈ D1 := fun s hs => inv z2 D1 hD1 s (hz2c s hs)
  have hβω : ρ z1 * (ρ z1 * ρ z2) = (ρ z1 * ρ z2) * ρ z1 := by
    calc ρ z1 * (ρ z1 * ρ z2) = ρ z1 * (ρ z2 * ρ z1) := by rw [hω12]
      _ = (ρ z1 * ρ z2) * ρ z1 := by group
  have hω3 : (ρ z1 * ρ z2) * (ρ z1 * ρ z2) * (ρ z1 * ρ z2) = 1 := by
    rw [mul_cube_of_comm hω12, hω13, hω23, mul_one]
  have hcard := card_decomp_omega hV2 (ρ z1 * ρ z2) (ρ z1) hω3 hfpf' hω13 hβω ⊤
    (fun _ _ => mem_top _) (fun _ _ => mem_top _)
  simp only [top_inf_eq, Subgroup.card_top, hV] at hcard
  have hx2 : ρ z1 * ρ z2 * (ρ z1 * ρ z2) * ρ z1 = ρ z2 * ρ z2 := by
    have hc : Commute (ρ z2) (ρ z1) := hω12.symm
    have hc' : (ρ z2 * ρ z2) * ρ z1 = ρ z1 * (ρ z2 * ρ z2) := (hc.mul_left hc).eq
    calc ρ z1 * ρ z2 * (ρ z1 * ρ z2) * ρ z1
        = ρ z1 * ρ z1 * (ρ z2 * ρ z2) * ρ z1 := by rw [hc.mul_mul_mul_comm]
      _ = ρ z1 * ρ z1 * ((ρ z2 * ρ z2) * ρ z1) := by rw [mul_assoc]
      _ = ρ z1 * ρ z1 * (ρ z1 * (ρ z2 * ρ z2)) := by rw [hc']
      _ = (ρ z1 * ρ z1 * ρ z1) * (ρ z2 * ρ z2) := by group
      _ = ρ z2 * ρ z2 := by rw [hω13, one_mul]
  rw [hx2, fixedSubgroupAut_mul_self _ hω23, ← hD1, ← hD2] at hcard
  have h12 : ρ z2 * ρ t = ρ t * ρ z1 := by
    rw [← map_mul, ← map_mul]
    congr 1
    calc z2 * t = t * z1 * t⁻¹ * t := by rw [hz2def]
      _ = t * z1 := by group
  have h21 : ρ z1 * ρ t = ρ t * ρ z2 := by
    rw [← map_mul, ← map_mul]
    congr 1
    calc z1 * t = z1 * t⁻¹ := by rw [htinv]
      _ = (t * t) * z1 * t⁻¹ := by rw [ht, one_mul]
      _ = t * (t * z1 * t⁻¹) := by group
      _ = t * z2 := by rw [hz2def]
  have hle12 : Nat.card D2 ≤ Nat.card D1 := by
    have := card_le_of_apply (⊤ : Subgroup V) (ρ t) (ρ z1) (ρ z2) (fun _ _ => mem_top _) h12
    simpa only [top_inf_eq, ← hD1, ← hD2] using this
  have hle21 : Nat.card D1 ≤ Nat.card D2 := by
    have := card_le_of_apply (⊤ : Subgroup V) (ρ t) (ρ z2) (ρ z1) (fun _ _ => mem_top _) h21
    simpa only [top_inf_eq, ← hD1, ← hD2] using this
  have hAB : Nat.card D2 = Nat.card D1 := le_antisymm hle12 hle21
  have hA1 : Nat.card D2 ≠ 1 := by
    intro h
    have hB1 : Nat.card D1 = 1 := by rw [← hAB, h]
    rw [h, hB1, one_mul, mul_one] at hcard
    have hM : fixedSubgroupAut (ρ z1 * ρ z2 * ρ z1) = ⊤ :=
      (Subgroup.card_eq_iff_eq_top _).1 (by rw [← hcard, hV])
    have hall : ∀ v : V, (ρ z1 * ρ z2 * ρ z1) v = v := fun v => by
      have : v ∈ fixedSubgroupAut (ρ z1 * ρ z2 * ρ z1) := by rw [hM]; trivial
      exact mem_fixedSubgroupAut.1 this
    have h1 : ρ z1 * ρ z2 * ρ z1 = 1 := MulEquiv.ext hall
    apply hne
    calc ρ z1 = ρ z1 * (ρ z1 * ρ z2 * ρ z1) := by rw [h1, mul_one]
      _ = ρ z1 * ρ z1 * (ρ z2 * ρ z1) := by group
      _ = ρ z1 * ρ z1 * (ρ z1 * ρ z2) := by rw [hω12]
      _ = (ρ z1 * ρ z1 * ρ z1) * ρ z2 := by group
      _ = ρ z2 := by rw [hω13, one_mul]
  have hD2ne : D2 ≠ ⊥ := fun h => hA1 (by rw [h]; exact Subgroup.card_bot)
  have hD1ne : D1 ≠ ⊥ := fun h => hA1 (by rw [hAB, h]; exact Subgroup.card_bot)
  obtain ⟨hf2, hbd2⟩ := faithful_of_fpf hV2 hV ρ q2 inv2S2 hD2ne hz2 fun v hv hzv => hfpf' v (by
    show ρ z1 (ρ z2 v) = v
    rw [hzv, (memD2 v).1 hv])
  obtain ⟨hf1, hbd1⟩ := faithful_of_fpf hV2 hV ρ q1 inv1S1 hD1ne hz1 fun v hv hzv => hfpf' v (by
    show ρ z1 (ρ z2 v) = v
    rw [(memD1 v).1 hv, hzv])
  rw [← hAB] at hcard
  have hMpos : 0 < Nat.card (fixedSubgroupAut (ρ z1 * ρ z2 * ρ z1)) := Nat.card_pos
  have hA64' : 64 ≤ Nat.card D2 := by simpa using hbd2
  have hAA : 64 * 64 ≤ Nat.card D2 * Nat.card D2 := Nat.mul_le_mul hA64' hA64'
  have hcard' : Nat.card (fixedSubgroupAut (ρ z1 * ρ z2 * ρ z1)) * (Nat.card D2 * Nat.card D2) =
      4096 := by
    have : (2 : ℕ) ^ 12 = 4096 := by norm_num
    rw [this] at hcard
    rw [hcard]
    ring
  have hMc : Nat.card (fixedSubgroupAut (ρ z1 * ρ z2 * ρ z1)) = 1 := by
    by_contra h
    have h2 : 2 ≤ Nat.card (fixedSubgroupAut (ρ z1 * ρ z2 * ρ z1)) := by omega
    have := Nat.mul_le_mul h2 hAA
    omega
  have hD2c : Nat.card D2 = 2 ^ 6 := by
    rw [hMc, one_mul] at hcard'
    have : Nat.card D2 * Nat.card D2 = 64 * 64 := by omega
    have := Nat.mul_self_inj.1 this
    omega
  have hD1c : Nat.card D1 = 2 ^ 6 := by rw [← hAB, hD2c]
  have hinf : D1 ⊓ D2 = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [mem_bot]
    exact hfpf' v (by
      show ρ z1 (ρ z2 v) = v
      rw [(memD1 v).1 (mem_inf.1 hv).1, (memD2 v).1 (mem_inf.1 hv).2])
  have hsup : D1 ⊔ D2 = ⊤ :=
    (Subgroup.isComplement'_of_card_mul_and_disjoint (by rw [hD1c, hD2c, hV]; norm_num)
      (disjoint_iff.2 hinf)).sup_eq_top
  have htriv2 : ∀ s ∈ S1, ∀ v ∈ D2, ρ s v = v :=
    trivial_of_faithful hV2 ρ q1 q2 hcomm hD2c inv2S1 inv2S2 hf2
  have htriv1 : ∀ s ∈ S2, ∀ v ∈ D1, ρ s v = v :=
    trivial_of_faithful hV2 ρ q2 q1 (fun a ha b hb => (hcomm b hb a ha).symm) hD1c inv1S2 inv1S1
      hf1
  have hsurj1 := exists_comm_eq (ρ z1) (ρ z2) hω12 (fun v h1 h2 => hfpf' v (by
    show ρ z1 (ρ z2 v) = v
    rw [h2, h1])) hD1
  have hsurj2 := exists_comm_eq (ρ z2) (ρ z1) hω12.symm (fun v h1 h2 => hfpf' v (by
    show ρ z1 (ρ z2 v) = v
    rw [h1, h2])) hD2
  have hS12 : S1 ⊓ S2 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    obtain ⟨hxS1, hxS2⟩ := mem_inf.1 hx
    have hxZ1 : x ∈ Z1 := mem_of_central q1 hxS1 fun g hg => (hcomm g hg x hxS2).symm
    have hxZ2 : x ∈ Z2 := mem_of_central q2 hxS2 fun g hg => hcomm x hxS1 g hg
    by_contra hx1
    have h1 := eq_one_or_eq_or_eq_inv_of_card_three q1.card_Z hxZ1 hx1 hz1
    have h2 := eq_one_or_eq_or_eq_inv_of_card_three q2.card_Z hxZ2 hx1 hz2
    have hprod : ∀ a b : Y, a = x → b = x⁻¹ → ρ z1 * ρ z2 = 1 → False := fun _ _ _ _ h => hnotinv h
    rcases h1 with h1 | h1 | h1
    · exact hz1ne h1
    · rcases h2 with h2 | h2 | h2
      · exact hz2ne h2
      · exact hne (by rw [h1, h2])
      · exact hnotinv (by rw [← map_mul, h1, h2, mul_inv_cancel, map_one])
    · rcases h2 with h2 | h2 | h2
      · exact hz2ne h2
      · exact hnotinv (by rw [← map_mul, h1, h2, inv_mul_cancel, map_one])
      · exact hne (by rw [h1, h2])
  refine ⟨D1, D2, hD1c, hD2c, hinf, hsup, htriv1, htriv2, ?_, ?_, hsurj1, ?_, ?_, ?_, hS12⟩
  · intro v hv
    exact (memD1 v).2 (hv z2 hz2S)
  · intro v hv
    exact (memD2 v).2 (hv z1 hz1S)
  · intro v hv
    exact hsurj2 v hv
  · intro v hv
    rw [memD2]
    have := congrArg (fun f : MulAut V => f v) h21
    simp only [MulAut.mul_apply] at this
    rw [this, (memD1 v).1 hv]
  · intro v hv
    rw [memD1]
    have := congrArg (fun f : MulAut V => f v) h12
    simp only [MulAut.mul_apply] at this
    rw [this, (memD2 v).1 hv]


end CFSG.EvenSporadicStandard.M24Std.DResH

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem sec9c_fixed_eq_one {B : Subgroup G} {T : Set G} (hB : IsElemAb2 B 4)
    (hirr : ∀ B' : Subgroup G, B' ≤ B → (∀ x ∈ T, ∀ c ∈ B', x * c * x⁻¹ ∈ B') →
      B' = ⊥ ∨ B' = B)
    {b : G} (hb : b ∈ B) (hfix : ∀ x ∈ T, x * b * x⁻¹ = b) : b = 1 := by
  have hle : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.mpr hb
  have hinv : ∀ x ∈ T, ∀ c ∈ Subgroup.zpowers b, x * c * x⁻¹ ∈ Subgroup.zpowers b := by
    intro x hx c hc
    rw [Subgroup.mem_zpowers_iff] at hc ⊢
    obtain ⟨k, rfl⟩ := hc
    exact ⟨k, by rw [← conj_zpow, hfix x hx]⟩
  rcases hirr (Subgroup.zpowers b) hle hinv with h | h
  · exact Subgroup.zpowers_eq_bot.mp h
  · exfalso
    have hcard : Nat.card (Subgroup.zpowers b) = 16 := by
      rw [h, hB.2]; norm_num
    rw [Nat.card_zpowers] at hcard
    have hdvd : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one (hB.1.2 b hb)
    have hle2 : orderOf b ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega

private lemma sec9c_sixteen_dvd_of_range {B : Subgroup G} {V : Subgroup (↥B × ↥B)}
    (hB16 : Nat.card B = 16) (π : ↥V →* ↥B) (h : (π.range).map B.subtype = B) :
    16 ∣ Nat.card V := by
  have htop : π.range = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype]
    exact h
  have hsurj : Function.Surjective π := fun y =>
    MonoidHom.mem_range.mp (by rw [htop]; exact Subgroup.mem_top y)
  have hdvd : Nat.card ↥B ∣ Nat.card ↥V := Subgroup.card_dvd_of_surjective hsurj
  rwa [hB16] at hdvd

private lemma sec9c_fst_range_inv {B : Subgroup G} {T : Set G} (V : Subgroup (↥B × ↥B))
    (hinv : ∀ x ∈ T, ∀ w ∈ V, ∃ w' ∈ V,
      ((w'.1 : ↥B) : G) = x * ((w.1 : ↥B) : G) * x⁻¹ ∧
        ((w'.2 : ↥B) : G) = x * ((w.2 : ↥B) : G) * x⁻¹) :
    ∀ x ∈ T, ∀ c ∈ (((MonoidHom.fst ↥B ↥B).comp V.subtype).range).map B.subtype,
      x * c * x⁻¹ ∈ (((MonoidHom.fst ↥B ↥B).comp V.subtype).range).map B.subtype := by
  intro x hx c hc
  rw [Subgroup.mem_map] at hc ⊢
  obtain ⟨z, hz, hzc⟩ := hc
  rw [MonoidHom.mem_range] at hz
  obtain ⟨w, hw⟩ := hz
  obtain ⟨w', hw'V, hw'1, _⟩ := hinv x hx (w : ↥B × ↥B) w.2
  refine ⟨w'.1, MonoidHom.mem_range.mpr ⟨⟨w', hw'V⟩, rfl⟩, ?_⟩
  rw [← hzc]
  have hz' : z = (w : ↥B × ↥B).1 := hw.symm
  rw [hz']
  exact hw'1

private lemma sec9c_snd_range_inv {B : Subgroup G} {T : Set G} (V : Subgroup (↥B × ↥B))
    (hinv : ∀ x ∈ T, ∀ w ∈ V, ∃ w' ∈ V,
      ((w'.1 : ↥B) : G) = x * ((w.1 : ↥B) : G) * x⁻¹ ∧
        ((w'.2 : ↥B) : G) = x * ((w.2 : ↥B) : G) * x⁻¹) :
    ∀ x ∈ T, ∀ c ∈ (((MonoidHom.snd ↥B ↥B).comp V.subtype).range).map B.subtype,
      x * c * x⁻¹ ∈ (((MonoidHom.snd ↥B ↥B).comp V.subtype).range).map B.subtype := by
  intro x hx c hc
  rw [Subgroup.mem_map] at hc ⊢
  obtain ⟨z, hz, hzc⟩ := hc
  rw [MonoidHom.mem_range] at hz
  obtain ⟨w, hw⟩ := hz
  obtain ⟨w', hw'V, _, hw'2⟩ := hinv x hx (w : ↥B × ↥B) w.2
  refine ⟨w'.2, MonoidHom.mem_range.mpr ⟨⟨w', hw'V⟩, rfl⟩, ?_⟩
  rw [← hzc]
  have hz' : z = (w : ↥B × ↥B).2 := hw.symm
  rw [hz']
  exact hw'2

theorem sec9c_card_dvd {B : Subgroup G} {T : Set G} (hB : IsElemAb2 B 4)
    (hirr : ∀ B' : Subgroup G, B' ≤ B → (∀ x ∈ T, ∀ c ∈ B', x * c * x⁻¹ ∈ B') →
      B' = ⊥ ∨ B' = B)
    (V : Subgroup (↥B × ↥B)) (hV : V ≠ ⊥)
    (hinv : ∀ x ∈ T, ∀ w ∈ V, ∃ w' ∈ V,
      ((w'.1 : ↥B) : G) = x * ((w.1 : ↥B) : G) * x⁻¹ ∧
        ((w'.2 : ↥B) : G) = x * ((w.2 : ↥B) : G) * x⁻¹) :
    16 ∣ Nat.card V := by
  have hB16 : Nat.card B = 16 := by rw [hB.2]; norm_num
  have hRfle : (((MonoidHom.fst ↥B ↥B).comp V.subtype).range).map B.subtype ≤ B :=
    Subgroup.map_subtype_le _
  rcases hirr _ hRfle (sec9c_fst_range_inv V hinv) with hf | hf
  ·
    have hfr : ((MonoidHom.fst ↥B ↥B).comp V.subtype).range = ⊥ := by
      apply Subgroup.map_injective B.subtype_injective
      rw [hf, Subgroup.map_bot]
    have hf_one : ∀ w : ↥V, (w : ↥B × ↥B).1 = 1 := by
      intro w
      have hmem : ((MonoidHom.fst ↥B ↥B).comp V.subtype) w ∈
          (((MonoidHom.fst ↥B ↥B).comp V.subtype).range) :=
        MonoidHom.mem_range.mpr ⟨w, rfl⟩
      rw [hfr, Subgroup.mem_bot] at hmem
      simpa using hmem
    obtain ⟨w₀, hw₀V, hw₀ne⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hV)
    rw [Subgroup.mem_bot] at hw₀ne
    have hw₀2 : (w₀ : ↥B × ↥B).2 ≠ 1 := by
      intro h2
      exact hw₀ne (Prod.ext (by simpa using hf_one ⟨w₀, hw₀V⟩) h2)
    have hR2ne : (((MonoidHom.snd ↥B ↥B).comp V.subtype).range).map B.subtype ≠ ⊥ := by
      intro hbot
      have hmem : ((w₀ : ↥B × ↥B).2 : G) ∈
          (((MonoidHom.snd ↥B ↥B).comp V.subtype).range).map B.subtype := by
        rw [Subgroup.mem_map]
        exact ⟨w₀.2, MonoidHom.mem_range.mpr ⟨⟨w₀, hw₀V⟩, rfl⟩, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hw₀2 (Subtype.ext hmem)
    have hR2le : (((MonoidHom.snd ↥B ↥B).comp V.subtype).range).map B.subtype ≤ B :=
      Subgroup.map_subtype_le _
    rcases hirr _ hR2le (sec9c_snd_range_inv V hinv) with h2 | h2
    · exact absurd h2 hR2ne
    · exact sec9c_sixteen_dvd_of_range hB16 _ h2
  · exact sec9c_sixteen_dvd_of_range hB16 _ hf

theorem sec9c_B_le_K {B M K : Subgroup G} {T : Set G} (hB : IsElemAb2 B 4) (hBM : B ≤ M)
    (hTB : ∀ x ∈ T, x ∈ normalizer (B : Set G)) (hTK : ∀ x ∈ T, x ∈ K)
    (hMK : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hirr : ∀ B' : Subgroup G, B' ≤ B → (∀ x ∈ T, ∀ c ∈ B', x * c * x⁻¹ ∈ B') →
      B' = ⊥ ∨ B' = B) : B ≤ K := by
  have hxB : ∀ x ∈ T, ∀ h : G, h ∈ B ↔ x * h * x⁻¹ ∈ B :=
    fun x hx => Subgroup.mem_normalizer_iff.mp (hTB x hx)
  have hinv : ∀ x ∈ T, ∀ c ∈ B ⊓ K, x * c * x⁻¹ ∈ B ⊓ K := by
    intro x hx c hc
    obtain ⟨hcB, hcK⟩ := hc
    exact ⟨(hxB x hx c).mp hcB,
      K.mul_mem (K.mul_mem (hTK x hx) hcK) (K.inv_mem (hTK x hx))⟩
  rcases hirr (B ⊓ K) inf_le_left hinv with h | h
  · have hfix : ∀ b ∈ B, ∀ x ∈ T, x * b * x⁻¹ = b := by
      intro b hb x hx
      have hcB : b * (x * b⁻¹ * x⁻¹) ∈ B :=
        B.mul_mem hb ((hxB x hx b⁻¹).mp (B.inv_mem hb))
      have hcK : b * (x * b⁻¹ * x⁻¹) ∈ K := by
        have hbx : b * x * b⁻¹ ∈ K := hMK b (hBM hb) x (hTK x hx)
        have heq : b * (x * b⁻¹ * x⁻¹) = (b * x * b⁻¹) * x⁻¹ := by group
        rw [heq]
        exact K.mul_mem hbx (K.inv_mem (hTK x hx))
      have hc : b * (x * b⁻¹ * x⁻¹) = 1 := by
        have hmem : b * (x * b⁻¹ * x⁻¹) ∈ B ⊓ K := ⟨hcB, hcK⟩
        rw [h, Subgroup.mem_bot] at hmem
        exact hmem
      have h1 : x * b⁻¹ * x⁻¹ = b⁻¹ := by
        have hcong := congrArg (fun t => b⁻¹ * t) hc
        simpa [mul_assoc] using hcong
      calc x * b * x⁻¹ = (x * b⁻¹ * x⁻¹)⁻¹ := by group
        _ = (b⁻¹)⁻¹ := by rw [h1]
        _ = b := inv_inv b
    have hBbot : B = ⊥ :=
      le_bot_iff.mp fun b hb => sec9c_fixed_eq_one hB hirr hb (hfix b hb)
    have h16 : Nat.card B = 16 := by rw [hB.2]; norm_num
    rw [hBbot, Subgroup.card_bot] at h16
    omega
  · rw [← h]
    exact inf_le_right

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.MFusionBasic

public section

namespace CFSG.EvenSporadicStandard.J4Std.MFusion

open Subgroup CFSG.EvenSporadicStandard.J4Std

variable {G : Type} [Group G]

theorem mem_conjSub_inv_iff {g x : G} {A : Subgroup G} : x ∈ conjSub g⁻¹ A ↔ g * x * g⁻¹ ∈ A := by
  rw [mem_conjSub_iff, inv_inv]

theorem conj_injective (g : G) {x x' : G} (h : g * x * g⁻¹ = g * x' * g⁻¹) : x = x' :=
  mul_left_cancel (mul_right_cancel h)

section Adjoin

variable {B : Subgroup G} {t : G} {ht : t * t = 1} {hn : ∀ b ∈ B, t * b * t⁻¹ ∈ B}

theorem adjoinInv_sq (hsq : ∀ b ∈ B, b * b = 1) (htc : ∀ b ∈ B, b * t = t * b) :
    ∀ a ∈ adjoinInv B t ht hn, a * a = 1 := by
  intro a ha
  rcases mem_adjoinInv_iff.1 ha with ha | ⟨b, hb, rfl⟩
  · exact hsq a ha
  · calc t * b * (t * b) = t * (b * t) * b := by group
      _ = t * (t * b) * b := by rw [htc b hb]
      _ = (t * t) * (b * b) := by group
      _ = 1 := by rw [ht, hsq b hb, one_mul]

theorem adjoinInv_comm (hcomm : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (htc : ∀ b ∈ B, b * t = t * b) :
    ∀ a ∈ adjoinInv B t ht hn, ∀ a' ∈ adjoinInv B t ht hn, a * a' = a' * a := by
  intro a ha a' ha'
  rcases mem_adjoinInv_iff.1 ha with ha | ⟨b, hb, rfl⟩ <;>
    rcases mem_adjoinInv_iff.1 ha' with ha' | ⟨b', hb', rfl⟩
  · exact hcomm a ha a' ha'
  · calc a * (t * b') = (a * t) * b' := by group
      _ = (t * a) * b' := by rw [htc a ha]
      _ = t * (a * b') := by group
      _ = t * (b' * a) := by rw [hcomm a ha b' hb']
      _ = t * b' * a := by group
  · calc t * b * a' = t * (b * a') := by group
      _ = t * (a' * b) := by rw [hcomm b hb a' ha']
      _ = (t * a') * b := by group
      _ = (a' * t) * b := by rw [htc a' ha']
      _ = a' * (t * b) := by group
  · have e1 : t * b * (t * b') = b * b' := by
      calc t * b * (t * b') = t * (b * t) * b' := by group
        _ = t * (t * b) * b' := by rw [htc b hb]
        _ = (t * t) * (b * b') := by group
        _ = b * b' := by rw [ht, one_mul]
    have e2 : t * b' * (t * b) = b' * b := by
      calc t * b' * (t * b) = t * (b' * t) * b := by group
        _ = t * (t * b') * b := by rw [htc b' hb']
        _ = (t * t) * (b' * b) := by group
        _ = b' * b := by rw [ht, one_mul]
    rw [e1, e2, hcomm b hb b' hb']

theorem adjoinInv_cent (htc : ∀ b ∈ B, b * t = t * b) :
    ∀ a ∈ adjoinInv B t ht hn, a * t = t * a := by
  intro a ha
  rcases mem_adjoinInv_iff.1 ha with ha | ⟨b, hb, rfl⟩
  · exact htc a ha
  · calc t * b * t = t * (b * t) := by group
      _ = t * (t * b) := by rw [htc b hb]

end Adjoin

section Rank

variable {L U T0 : Subgroup G} {z : G} {Y : Subgroup G}

theorem exists_conj_V (hR : RankData L U z) {g : G} (A : Subgroup G)
    (hzA : g * z * g⁻¹ ∈ A) (hsq : ∀ a ∈ A, a * a = 1)
    (hcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hcent : ∀ a ∈ A, a * (g * z * g⁻¹) = (g * z * g⁻¹) * a) (hcard : 2 ^ 12 ≤ Nat.card A) :
    Nat.card A = 2 ^ 12 ∧ ∃ l ∈ L, A = conjSub (g * l) (Vsub U z) := by
  have hmemB : ∀ b ∈ conjSub g⁻¹ A, g * b * g⁻¹ ∈ A := fun b hb => mem_conjSub_inv_iff.1 hb
  have hB1 : ∀ b ∈ conjSub g⁻¹ A, b * b = 1 := by
    intro b hb
    have h := hsq _ (hmemB b hb)
    apply conj_injective g
    calc g * (b * b) * g⁻¹ = (g * b * g⁻¹) * (g * b * g⁻¹) := by group
      _ = 1 := h
      _ = g * 1 * g⁻¹ := by group
  have hBc : ∀ b ∈ conjSub g⁻¹ A, b * z = z * b := by
    intro b hb
    have h := hcent _ (hmemB b hb)
    apply conj_injective g
    calc g * (b * z) * g⁻¹ = (g * b * g⁻¹) * (g * z * g⁻¹) := by group
      _ = (g * z * g⁻¹) * (g * b * g⁻¹) := h
      _ = g * (z * b) * g⁻¹ := by group
  have hBcomm : ∀ b ∈ conjSub g⁻¹ A, ∀ b' ∈ conjSub g⁻¹ A, b * b' = b' * b := by
    intro b hb b' hb'
    have h := hcomm _ (hmemB b hb) _ (hmemB b' hb')
    apply conj_injective g
    calc g * (b * b') * g⁻¹ = (g * b * g⁻¹) * (g * b' * g⁻¹) := by group
      _ = (g * b' * g⁻¹) * (g * b * g⁻¹) := h
      _ = g * (b' * b) * g⁻¹ := by group
  have hcardB : Nat.card (conjSub g⁻¹ A) = Nat.card A := card_conjSub _ _
  have hcard' : Nat.card A = 2 ^ 12 :=
    le_antisymm (hcardB ▸ hR.rank_cent _ hBc hB1 hBcomm) hcard
  obtain ⟨l, hl, hBl⟩ := hR.conj_E12 (conjSub g⁻¹ A) (mem_conjSub_inv_iff.2 hzA) hBc hB1 hBcomm
    (hcardB.trans hcard')
  refine ⟨hcard', l, hl, ?_⟩
  ext x
  have h1 : x ∈ A ↔ g⁻¹ * x * g ∈ conjSub g⁻¹ A := by
    rw [mem_conjSub_inv_iff, show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
  rw [h1, hBl, mem_conjSub_iff, mem_conjSub_iff,
    show (g * l)⁻¹ * x * (g * l) = l⁻¹ * (g⁻¹ * x * g) * l by group]

theorem exists_conj_cenIn [Finite G] (hS : Setting L z) (hD : LocalData L U T0)
    (htrans : ∀ u ∈ U, ∃ n ∈ Nsub U z, n * z * n⁻¹ = z * u) (hR : RankData L U z)
    (hW : WeakData U z Y) {y : G} (hyM : y ∈ normalizer (Y : Set G)) {g : G}
    (hg : g * z * g⁻¹ = y) :
    ∃ g' : G, (∀ u ∈ U, g' * u * g'⁻¹ ∈ cenIn Y y) ∧ Nat.card (cenIn Y y) = 2 ^ 11 := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  have hy2 : y * y = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hS.z_mul_self]; group
  have hyY : y ∉ Y := fun h => hW.noconj_Y g y h hg
  have hyn : ∀ a ∈ Y, y * a * y⁻¹ ∈ Y := fun a ha => (mem_normalizer_iff.1 hyM a).1 ha
  have hle := card_le_sq_cenIn (hy := hyn) (hc := hW.Y_comm) hW.Y_sq hy2
  rw [hW.card_Y] at hle
  have hC11 : 2 ^ 11 ≤ Nat.card (cenIn Y y) := by
    have h22 : (2 : ℕ) ^ 22 = (2 ^ 11) ^ 2 := by norm_num
    rw [h22] at hle
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 hle
  have hCsq : ∀ b ∈ cenIn Y y, b * b = 1 := fun b hb => hW.Y_sq b (cenIn_le_left hb)
  have hCcomm : ∀ b ∈ cenIn Y y, ∀ b' ∈ cenIn Y y, b * b' = b' * b := fun b hb b' hb' =>
    hW.Y_comm b (cenIn_le_left hb) b' (cenIn_le_left hb')
  have hCy : ∀ b ∈ cenIn Y y, b * y = y * b := fun b hb => (mem_cenIn.1 hb).2
  have hnC : ∀ b ∈ cenIn Y y, y * b * y⁻¹ ∈ cenIn Y y := fun b hb => by
    have : y * b * y⁻¹ = b := by
      calc y * b * y⁻¹ = b * y * y⁻¹ := by rw [hCy b hb]
        _ = b := by group
    rw [this]
    exact hb
  have hyC : y ∉ cenIn Y y := fun h => hyY (cenIn_le_left h)
  have hAsq := adjoinInv_sq (ht := hy2) (hn := hnC) hCsq hCy
  have hAcomm := adjoinInv_comm (ht := hy2) (hn := hnC) hCcomm hCy
  have hAy := adjoinInv_cent (ht := hy2) (hn := hnC) hCy
  have hyA : y ∈ adjoinInv (cenIn Y y) y hy2 hnC := by
    have := mul_mem_adjoinInv (B := cenIn Y y) (t := y) (ht := hy2) (hn := hnC) (one_mem _)
    rwa [mul_one] at this
  have hcardA : Nat.card (adjoinInv (cenIn Y y) y hy2 hnC) = 2 * Nat.card (cenIn Y y) :=
    card_adjoinInv hyC
  obtain ⟨hcA, l, hl, hAeq⟩ := exists_conj_V (U := U) hR (adjoinInv (cenIn Y y) y hy2 hnC)
    (g := g) (by rw [hg]; exact hyA) hAsq hAcomm (by rw [hg]; exact hAy) (by omega)
  have hC' : Nat.card (cenIn Y y) = 2 ^ 11 := by omega
  refine ⟨g * l, ?_, hC'⟩
  have hCle : cenIn Y y ≤ conjSub (g * l) U := by
    intro c hc
    have hcA : c ∈ adjoinInv (cenIn Y y) y hy2 hnC := le_adjoinInv hc
    rw [hAeq, mem_conjSub_iff] at hcA
    obtain ⟨u, hu, hcu⟩ := (mem_Vsub_iff hS hUL).1 hcA
    rcases hcu with hcu | hcu
    · exact mem_conjSub_iff.2 (by rw [hcu]; exact hu)
    · exfalso
      obtain ⟨n, hn, hnz⟩ := htrans u hu
      apply hW.noconj_Y (g * l * n) c (cenIn_le_left hc)
      calc (g * l * n) * z * (g * l * n)⁻¹ = (g * l) * (n * z * n⁻¹) * (g * l)⁻¹ := by group
        _ = (g * l) * (z * u) * (g * l)⁻¹ := by rw [hnz]
        _ = c := by rw [← hcu]; group
  have hcard_conj : Nat.card (conjSub (g * l) U) = Nat.card (cenIn Y y) := by
    rw [card_conjSub, hD.card_U, hC']
  have hCeq : cenIn Y y = conjSub (g * l) U := eq_of_le_of_card_ge hCle hcard_conj.le
  intro u hu
  rw [hCeq]
  exact conj_mem_conjSub hu

end Rank

end CFSG.EvenSporadicStandard.J4Std.MFusion

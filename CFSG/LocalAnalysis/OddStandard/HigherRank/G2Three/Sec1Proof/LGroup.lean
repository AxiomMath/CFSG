module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.LGroupA

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Open Subgroup
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem normIn_eq_of_index_le_two {L E : Subgroup Γ} {z : Γ} (hzE : z ∈ E) (hz2 : orderOf z = 2)
    (hcard : Nat.card (normIn L E) < 3 * Nat.card (normIn (centEl L z) E))
    (hfix : ∀ e ∈ E, e ∉ zpowers z → ∃ m ∈ normIn (centEl L z) E, m * e ≠ e * m) :
    normIn L E = normIn (centEl L z) E := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hzsq : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz2] at h
    simpa [pow_two] using h
  have hMle : normIn (centEl L z) E ≤ normIn L E := by
    rw [normIn, normIn]
    exact inf_le_inf_right (normalizer (E : Set Γ)) (show centEl L z ≤ L from inf_le_left)
  have hidxeq : (normIn (centEl L z) E).relIndex (normIn L E) *
      Nat.card (normIn (centEl L z) E) = Nat.card (normIn L E) := by
    have h := Subgroup.relIndex_mul_card (H := normIn (centEl L z) E) (K := normIn L E)
    rwa [inf_eq_left.mpr hMle] at h
  have hMpos : 0 < Nat.card (normIn (centEl L z) E) := Nat.card_pos
  have hidxlt : (normIn (centEl L z) E).relIndex (normIn L E) < 3 := by
    have h : (normIn (centEl L z) E).relIndex (normIn L E) *
        Nat.card (normIn (centEl L z) E) < 3 * Nat.card (normIn (centEl L z) E) := by
      rw [hidxeq]; exact hcard
    exact (Nat.mul_lt_mul_right hMpos).mp h
  have hidxle : (normIn (centEl L z) E).relIndex (normIn L E) ≤ 2 := by omega
  have hsubidx : ((normIn (centEl L z) E).subgroupOf (normIn L E)).index ≤ 2 := hidxle
  have hidxpos : ((normIn (centEl L z) E).subgroupOf (normIn L E)).index ≠ 0 := by
    intro h0
    have h := Subgroup.card_mul_index (H := (normIn (centEl L z) E).subgroupOf (normIn L E))
    rw [h0, mul_zero] at h
    exact Nat.card_pos.ne' h.symm
  have hnorm : ((normIn (centEl L z) E).subgroupOf (normIn L E)).Normal := by
    rcases (show ((normIn (centEl L z) E).subgroupOf (normIn L E)).index = 1 ∨
        ((normIn (centEl L z) E).subgroupOf (normIn L E)).index = 2 from by omega) with h1 | h2
    · exact Subgroup.normal_of_index_eq_one h1
    · exact Subgroup.normal_of_index_eq_two h2
  apply le_antisymm _ hMle
  intro n hn
  have hnL : n ∈ L := hn.1
  have hnN : n ∈ normalizer (E : Set Γ) := hn.2
  have hwE : n * z * n⁻¹ ∈ E := (Subgroup.mem_set_normalizer_iff.mp hnN z).mp hzE
  have hwzp : n * z * n⁻¹ ∈ zpowers z := by
    by_contra hw
    obtain ⟨m, hmM, hmne⟩ := hfix (n * z * n⁻¹) hwE hw
    have hnm : n⁻¹ * m * n ∈ normIn (centEl L z) E := by
      have hconj := hnorm.conj_mem (⟨m, hMle hmM⟩ : ↥(normIn L E)) (by
        rw [Subgroup.mem_subgroupOf]; exact hmM) (⟨n, hn⟩ : ↥(normIn L E))⁻¹
      rw [Subgroup.mem_subgroupOf] at hconj
      simpa using hconj
    have hnmcent : (n⁻¹ * m * n) * z = z * (n⁻¹ * m * n) := by
      have hmem : n⁻¹ * m * n ∈ centEl L z := (Subgroup.mem_inf.mp hnm).1
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hmem).2
    exact hmne (by
      calc m * (n * z * n⁻¹) = n * ((n⁻¹ * m * n) * z) * n⁻¹ := by group
        _ = n * (z * (n⁻¹ * m * n)) * n⁻¹ := by rw [hnmcent]
        _ = (n * z * n⁻¹) * m := by group)
  have hw : n * z * n⁻¹ = z := by
    rcases zpowers_eq_one_or_self hz1 hzsq hwzp with h1 | h1
    · exfalso
      have hz1' : z = 1 := by
        calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
          _ = 1 := by rw [h1]; group
      exact hz1 hz1'
    · exact h1
  refine ⟨⟨hnL, ?_⟩, hnN⟩
  show n ∈ Subgroup.centralizer ({z} : Set Γ)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc n * z = (n * z * n⁻¹) * n := by group
    _ = z * n := by rw [hw]

theorem fact19_of_witness {L S E F Y₁ Y₂ Y₃ : Subgroup Γ} (hS : IsSylowIn 2 L S)
    (h6 : ∀ Y ∈ maxElemAbelian S, ∃ s ∈ S,
      ∃ Y₀ ∈ ({E, F, Y₁, Y₂, Y₃} : Set (Subgroup Γ)), Y = conjSub s Y₀)
    (h1 : ∃ l ∈ L, Y₁ = conjSub l E ∨ Y₁ = conjSub l F)
    (h2 : ∃ l ∈ L, Y₂ = conjSub l E ∨ Y₂ = conjSub l F)
    (h3 : ∃ l ∈ L, Y₃ = conjSub l E ∨ Y₃ = conjSub l F) :
    ∀ Y ∈ maxElemAbelian L, ∃ l ∈ L, Y = conjSub l E ∨ Y = conjSub l F := by
  intro Y hY
  obtain ⟨g, hgL, hgS⟩ := exists_conj_mem_maxElemAbelian_of_sylow hS hY
  obtain ⟨s, hsS, Y₀, hY₀, hEq⟩ := h6 (conjSub g Y) hgS
  have hYL : Y = conjSub (g⁻¹ * s) Y₀ := by
    calc Y = conjSub g⁻¹ (conjSub g Y) := (conjSub_inv_conjSub g Y).symm
      _ = conjSub g⁻¹ (conjSub s Y₀) := by rw [hEq]
      _ = conjSub (g⁻¹ * s) Y₀ := by rw [conjSub_mul]
  have hgsL : g⁻¹ * s ∈ L := L.mul_mem (L.inv_mem hgL) (hS.1 hsS)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY₀
  rcases hY₀ with rfl | rfl | rfl | rfl | rfl
  · exact ⟨g⁻¹ * s, hgsL, Or.inl hYL⟩
  · exact ⟨g⁻¹ * s, hgsL, Or.inr hYL⟩
  · obtain ⟨l, hlL, hl | hl⟩ := h1
    · refine ⟨(g⁻¹ * s) * l, L.mul_mem hgsL hlL, ?_⟩
      rw [hYL, hl, conjSub_mul]
      exact Or.inl rfl
    · refine ⟨(g⁻¹ * s) * l, L.mul_mem hgsL hlL, ?_⟩
      rw [hYL, hl, conjSub_mul]
      exact Or.inr rfl
  · obtain ⟨l, hlL, hl | hl⟩ := h2
    · refine ⟨(g⁻¹ * s) * l, L.mul_mem hgsL hlL, ?_⟩
      rw [hYL, hl, conjSub_mul]
      exact Or.inl rfl
    · refine ⟨(g⁻¹ * s) * l, L.mul_mem hgsL hlL, ?_⟩
      rw [hYL, hl, conjSub_mul]
      exact Or.inr rfl
  · obtain ⟨l, hlL, hl | hl⟩ := h3
    · refine ⟨(g⁻¹ * s) * l, L.mul_mem hgsL hlL, ?_⟩
      rw [hYL, hl, conjSub_mul]
      exact Or.inl rfl
    · refine ⟨(g⁻¹ * s) * l, L.mul_mem hgsL hlL, ?_⟩
      rw [hYL, hl, conjSub_mul]
      exact Or.inr rfl

theorem fact110_two_of_centIn {L F : Subgroup Γ} {σ : Γ} (hL : L.Normal) (hσ : σ * σ = 1)
    (hcentF : centIn L F = F) (hσF : ∀ f ∈ F, σ * f = f * σ) :
    σ ∈ normalizer (F : Set Γ) ∧ ∀ g ∈ normIn L F, ⁅σ, g⁆ ∈ F := by
  have hσinv : σ⁻¹ = σ := by
    calc σ⁻¹ = σ⁻¹ * 1 := by rw [mul_one]
      _ = σ⁻¹ * (σ * σ) := by rw [hσ]
      _ = σ := by group
  constructor
  · apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    exact fun f hf => (hσF f hf).symm
  · intro g hg
    obtain ⟨hgL, hgN⟩ := hg
    have hmemL : ⁅σ, g⁆ ∈ L := by
      rw [commutatorElement_def]
      exact L.mul_mem (hL.conj_mem g hgL σ) (L.inv_mem hgL)
    have hmemC : ⁅σ, g⁆ ∈ Subgroup.centralizer (F : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      rw [commutatorElement_def]
      have hgif : g⁻¹ * f * g ∈ F := by
        simpa using (Subgroup.mem_set_normalizer_iff.mp (inv_mem hgN) f).mp hf
      have hσf : σ * f = f * σ := hσF f hf
      have hσf' : σ * (g⁻¹ * f * g) = (g⁻¹ * f * g) * σ := hσF (g⁻¹ * f * g) hgif
      have hσf'inv : σ⁻¹ * (g⁻¹ * f * g) = (g⁻¹ * f * g) * σ⁻¹ := by
        rw [hσinv]; exact hσf'
      calc f * (σ * g * σ⁻¹ * g⁻¹)
          = f * σ * g * σ⁻¹ * g⁻¹ := by group
        _ = σ * f * g * σ⁻¹ * g⁻¹ := by rw [← hσf]
        _ = σ * g * (g⁻¹ * f * g) * σ⁻¹ * g⁻¹ := by group
        _ = σ * g * ((g⁻¹ * f * g) * σ⁻¹) * g⁻¹ := by group
        _ = σ * g * (σ⁻¹ * (g⁻¹ * f * g)) * g⁻¹ := by rw [← hσf'inv]
        _ = (σ * g * σ⁻¹ * g⁻¹) * f := by group
    have hcent : ⁅σ, g⁆ ∈ centIn L F := ⟨hmemL, hmemC⟩
    rwa [hcentF] at hcent

theorem isSylowIn_two_of_card {C F : Subgroup Γ} (hFC : F ≤ C) (hC : Nat.card C = 1512)
    (hF : Nat.card F = 8) : IsSylowIn 2 C F := by
  refine ⟨hFC, IsPGroup.of_card (n := 3) ?_, ?_⟩
  · rw [hF]; norm_num
  · have hrel : F.relIndex C * Nat.card (F ⊓ C : Subgroup Γ) = Nat.card C :=
      Subgroup.relIndex_mul_card (H := F) (K := C)
    rw [inf_eq_left.mpr hFC, hC, hF] at hrel
    have : F.relIndex C = 189 := by omega
    rw [this]; norm_num

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

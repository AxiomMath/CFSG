module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalCore
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.Quasithin

variable {p : ℕ} {P Y : Type} [Group P] [Group Y]

theorem centerOf_map {ι : P →* Y} (hι : Function.Injective ι) (T : Subgroup P) :
    centerOf (T.map ι) = (centerOf T).map ι := by
  ext y
  constructor
  · rintro ⟨hy, hyc⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨x, ⟨hx, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hyc (ι t) ⟨t, ht, rfl⟩
    exact hι (by rw [map_mul, map_mul]; exact this)
  · rintro ⟨x, ⟨hx, hxc⟩, rfl⟩
    refine ⟨Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hxc t ht]

theorem normalizer_map_inf_range {ι : P →* Y} (hι : Function.Injective ι) (U : Subgroup P) :
    Subgroup.normalizer ((U.map ι : Subgroup Y) : Set Y) ⊓ ι.range =
      (Subgroup.normalizer (U : Set P)).map ι := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨hy, x, rfl⟩
    have h1 : (Subgroup.normalizer ((U.map ι : Subgroup Y) : Set Y)).comap ι =
        Subgroup.normalizer (((U.map ι).comap ι : Subgroup P) : Set P) :=
      Subgroup.comap_normalizer_eq_of_le_range (Subgroup.map_le_range ι U)
    rw [Subgroup.comap_map_eq_self_of_injective hι] at h1
    exact Subgroup.mem_map.mpr ⟨x, h1 ▸ (hy : x ∈ (Subgroup.normalizer
      ((U.map ι : Subgroup Y) : Set Y)).comap ι), rfl⟩
  · refine le_inf (Subgroup.le_normalizer_map ι) (Subgroup.map_le_range ι _)

theorem mem_normalizer_map_iff {ι : P →* Y} (hι : Function.Injective ι) (H : Subgroup P) (x : P) :
    ι x ∈ Subgroup.normalizer ((H.map ι : Subgroup Y) : Set Y) ↔
      x ∈ Subgroup.normalizer (H : Set P) := by
  have h1 : (Subgroup.normalizer ((H.map ι : Subgroup Y) : Set Y)).comap ι =
      Subgroup.normalizer (((H.map ι).comap ι : Subgroup P) : Set P) :=
    Subgroup.comap_normalizer_eq_of_le_range (Subgroup.map_le_range ι H)
  rw [Subgroup.comap_map_eq_self_of_injective hι] at h1
  exact SetLike.ext_iff.mp h1 x

namespace SiegelRadicalData

theorem map [Fact p.Prime] {T U : Subgroup P} (h : SiegelRadicalData p ⊤ T U) (ι : P →* Y)
    (hι : Function.Injective ι) : SiegelRadicalData p ι.range (T.map ι) (U.map ι) where
  T_le := Subgroup.map_le_range ι T
  U_le := Subgroup.map_mono h.U_le
  elem := h.elem.map ι
  card_U := (Subgroup.card_map_of_injective hι).trans h.card_U
  card_T := (Subgroup.card_map_of_injective hι).trans h.card_T
  card_center := by
    rw [centerOf_map hι, Subgroup.card_map_of_injective hι, h.card_center]
  unique := by
    intro B hBT hB hBc
    have hBr : B ≤ ι.range := hBT.trans (Subgroup.map_le_range ι T)
    have hB' : B.comap ι ≤ T := by
      intro x hx
      obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.mp (hBT hx)
      exact hι hte ▸ ht
    have hcard : Nat.card (B.comap ι) = p ^ 3 := by
      rw [← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq_self hBr, hBc]
    have := h.unique _ hB' (hB.comap hι) hcard
    rw [← Subgroup.map_comap_eq_self hBr, this]
  coatom := by
    intro M hM hMK
    have hN : Subgroup.normalizer (U : Set P) ≤ M.comap ι := by
      intro x hx
      have hx1 : ι x ∈ (Subgroup.normalizer (U : Set P)).map ι := ⟨x, hx, rfl⟩
      rw [← normalizer_map_inf_range hι] at hx1
      exact hM hx1
    have hcoat := h.coatom (M.comap ι) (by simpa using hN) le_top
    rcases hcoat with h1 | h1
    · left
      rw [normalizer_map_inf_range hι, ← Subgroup.map_comap_eq_self hMK, h1, inf_top_eq]
    · right
      refine le_antisymm hMK fun y hy => ?_
      obtain ⟨x, rfl⟩ := hy
      have : x ∈ M.comap ι := h1 ▸ Subgroup.mem_top x
      exact this

end SiegelRadicalData

structure SiegelModuleData (K U : Subgroup Y) : Prop where
  irred : ∀ W : Subgroup Y, W ≤ U → Subgroup.normalizer (U : Set Y) ⊓ K ≤
    Subgroup.normalizer (W : Set Y) → W = ⊥ ∨ W = U
  centralizer_le : Subgroup.centralizer (U : Set Y) ≤ U

namespace SiegelModuleData

theorem of_model {U : Subgroup P} (ι : P →* Y) (hι : Function.Injective ι)
    [ι.range.Normal] (hC : Subgroup.centralizer (ι.range : Set Y) = ⊥)
    (hirr : ∀ W : Subgroup P, W ≤ U → Subgroup.normalizer (U : Set P) ≤
      Subgroup.normalizer (W : Set P) → W = ⊥ ∨ W = U)
    (haut : ∀ α : MulAut P, (∀ u ∈ U, α u = u) → ∃ k ∈ U, α = MulAut.conj k) :
    SiegelModuleData ι.range (U.map ι) where
  irred := by
    intro W hWU hN
    have hWr : W ≤ ι.range := hWU.trans (Subgroup.map_le_range ι U)
    have hW' : W.comap ι ≤ U := by
      intro x hx
      obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.mp (hWU hx)
      exact hι hte ▸ ht
    have hN' : Subgroup.normalizer (U : Set P) ≤ Subgroup.normalizer ((W.comap ι : Subgroup P) :
        Set P) := by
      intro x hx
      have hx1 : ι x ∈ (Subgroup.normalizer (U : Set P)).map ι := ⟨x, hx, rfl⟩
      rw [← normalizer_map_inf_range hι] at hx1
      have h2 := hN hx1
      rw [Subgroup.mem_normalizer_iff] at h2 ⊢
      intro z
      have := h2 (ι z)
      simp only [Subgroup.mem_comap, map_mul, map_inv]
      exact this
    rcases hirr _ hW' hN' with h1 | h1
    · left
      rw [← Subgroup.map_comap_eq_self hWr, h1, Subgroup.map_bot]
    · right
      rw [← Subgroup.map_comap_eq_self hWr, h1]
  centralizer_le := by
    intro y hy
    have hy' := Subgroup.mem_centralizer_iff.mp hy
    let e : P ≃* ι.range := MonoidHom.ofInjective hι
    let α : MulAut P := e.trans ((MulAut.conjNormal y).trans e.symm)
    have hα : ∀ x : P, ι (α x) = y * ι x * y⁻¹ := by
      intro x
      have h1 : (e (α x) : Y) = ι (α x) := rfl
      have h2 : e (α x) = MulAut.conjNormal y (e x) := by
        simp [α]
      rw [← h1, h2]
      simp [MulAut.conjNormal_apply, e, MonoidHom.ofInjective_apply]
    have hαU : ∀ u ∈ U, α u = u := by
      intro u hu
      apply hι
      rw [hα, ← hy' (ι u) ⟨u, hu, rfl⟩, mul_inv_cancel_right]
    obtain ⟨k, hk, hαk⟩ := haut α hαU
    have hz : (ι k)⁻¹ * y ∈ Subgroup.centralizer (ι.range : Set Y) := by
      refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro _ ⟨x, rfl⟩
      have h1 := hα x
      rw [hαk, MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
      calc ι x * ((ι k)⁻¹ * y) = (ι k)⁻¹ * (ι k * ι x * (ι k)⁻¹) * y := by group
        _ = (ι k)⁻¹ * (y * ι x * y⁻¹) * y := by rw [h1]
        _ = (ι k)⁻¹ * y * ι x := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hz
    exact Subgroup.mem_map.mpr ⟨k, hk, hz⟩

end SiegelModuleData

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

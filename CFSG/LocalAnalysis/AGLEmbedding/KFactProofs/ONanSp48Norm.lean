module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Swap
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48SL28

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped MatrixGroups

theorem sl28_center_trivial {x : Sl28} (hx : ∀ l : Sl28, x * l = l * x) : x = 1 := by
  have hn : (Subgroup.center Sl28).Normal := inferInstance
  rcases sl28_isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Sl28) with h | h
  · have : x ∈ Subgroup.center Sl28 := Subgroup.mem_center_iff.2 fun l => (hx l).symm
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  · exfalso
    obtain ⟨a, b, hab⟩ := sl28_nonabelian
    apply hab
    have : a ∈ Subgroup.center Sl28 := by rw [h]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 this b).symm

theorem sl28_exists_noncomm {x : Sl28} (hx : x ≠ 1) : ∃ l : Sl28, x * l * x⁻¹ * l⁻¹ ≠ 1 := by
  by_contra h
  push Not at h
  exact hx (sl28_center_trivial fun l => by
    have := h l
    calc x * l = (x * l * x⁻¹ * l⁻¹) * l * x := by group
      _ = l * x := by rw [this]; group)

theorem comm_blk (u v x y : Sl28) :
    (blk0 u * blk1 v) * (blk0 x * blk1 y) * (blk0 u * blk1 v)⁻¹ * (blk0 x * blk1 y)⁻¹ =
      blk0 (u * x * u⁻¹ * x⁻¹) * blk1 (v * y * v⁻¹ * y⁻¹) := by
  rw [conj_blk, blk_inv, blk_mul]

theorem blk0_mem_wrp_top (l : Sl28) : blk0 l ∈ wrp (⊤ : Subgroup Sl28) :=
  ⟨l, Subgroup.mem_top _, 1, Subgroup.mem_top _, Or.inl (by simp)⟩

theorem blk1_mem_wrp_top (l : Sl28) : blk1 l ∈ wrp (⊤ : Subgroup Sl28) :=
  ⟨1, Subgroup.mem_top _, l, Subgroup.mem_top _, Or.inl (by simp)⟩

theorem swp_mem_wrp_top : swp ∈ wrp (⊤ : Subgroup Sl28) := swp_mem_wrp _

section Top

variable {W : Subgroup Sp8} (hn : ∀ h ∈ wrp (⊤ : Subgroup Sl28), ∀ w ∈ W, h * w * h⁻¹ ∈ W)
include hn

theorem blk0_all_of_block {u v : Sl28} (hu : u ≠ 1) (hw : blk0 u * blk1 v ∈ W) :
    ∀ l : Sl28, blk0 l ∈ W := by
  obtain ⟨l, hl⟩ := sl28_exists_noncomm hu
  have hc : blk0 (u * l * u⁻¹ * l⁻¹) ∈ W := by
    have h1 := hn (blk0 l) (blk0_mem_wrp_top l) _ (W.inv_mem hw)
    have h2 := W.mul_mem hw h1
    have h3 : (blk0 u * blk1 v) * (blk0 l * (blk0 u * blk1 v)⁻¹ * (blk0 l)⁻¹) =
        blk0 (u * l * u⁻¹ * l⁻¹) := by
      have := comm_blk u v l 1
      simp only [map_one, mul_one, mul_inv_cancel, inv_one] at this
      rw [← this]
      group
    rwa [h3] at h2
  have hne : u * l * u⁻¹ * l⁻¹ ≠ 1 := hl
  have hnorm : (W.comap blk0).Normal :=
    ⟨fun v hv l => by
      show blk0 (l * v * l⁻¹) ∈ W
      rw [map_mul, map_mul, map_inv]
      exact hn (blk0 l) (blk0_mem_wrp_top l) _ hv⟩
  rcases sl28_isSimpleGroup.eq_bot_or_eq_top_of_normal (W.comap blk0) with h | h
  · exfalso
    have : (u * l * u⁻¹ * l⁻¹) ∈ W.comap blk0 := hc
    rw [h] at this
    exact hne (Subgroup.mem_bot.1 this)
  · intro l'
    have : l' ∈ W.comap blk0 := by rw [h]; exact Subgroup.mem_top l'
    exact this

theorem blk1_all_of_block {u v : Sl28} (hv : v ≠ 1) (hw : blk0 u * blk1 v ∈ W) :
    ∀ l : Sl28, blk1 l ∈ W := by
  obtain ⟨l, hl⟩ := sl28_exists_noncomm hv
  have hc : blk1 (v * l * v⁻¹ * l⁻¹) ∈ W := by
    have h1 := hn (blk1 l) (blk1_mem_wrp_top l) _ (W.inv_mem hw)
    have h2 := W.mul_mem hw h1
    have h3 : (blk0 u * blk1 v) * (blk1 l * (blk0 u * blk1 v)⁻¹ * (blk1 l)⁻¹) =
        blk1 (v * l * v⁻¹ * l⁻¹) := by
      have := comm_blk u v 1 l
      simp only [map_one, mul_one, one_mul, mul_inv_cancel, inv_one] at this
      rw [← this]
      group
    rwa [h3] at h2
  have hne : v * l * v⁻¹ * l⁻¹ ≠ 1 := hl
  have hnorm : (W.comap blk1).Normal :=
    ⟨fun v hv l => by
      show blk1 (l * v * l⁻¹) ∈ W
      rw [map_mul, map_mul, map_inv]
      exact hn (blk1 l) (blk1_mem_wrp_top l) _ hv⟩
  rcases sl28_isSimpleGroup.eq_bot_or_eq_top_of_normal (W.comap blk1) with h | h
  · exfalso
    have : (v * l * v⁻¹ * l⁻¹) ∈ W.comap blk1 := hc
    rw [h] at this
    exact hne (Subgroup.mem_bot.1 this)
  · intro l'
    have : l' ∈ W.comap blk1 := by rw [h]; exact Subgroup.mem_top l'
    exact this

theorem blk1_of_blk0 (h0 : ∀ l : Sl28, blk0 l ∈ W) (l : Sl28) : blk1 l ∈ W := by
  have := hn swp swp_mem_wrp_top _ (h0 l)
  rwa [swp_conj_blk0] at this

theorem blk0_of_blk1 (h1 : ∀ l : Sl28, blk1 l ∈ W) (l : Sl28) : blk0 l ∈ W := by
  have := hn swp swp_mem_wrp_top _ (h1 l)
  rwa [swp_conj_blk1] at this

theorem blocks_of_block {u v : Sl28} (huv : ¬ (u = 1 ∧ v = 1)) (hw : blk0 u * blk1 v ∈ W) :
    (∀ l : Sl28, blk0 l ∈ W) ∧ (∀ l : Sl28, blk1 l ∈ W) := by
  by_cases hu : u = 1
  · have hv : v ≠ 1 := fun hv => huv ⟨hu, hv⟩
    have h1 := blk1_all_of_block hn hv hw
    exact ⟨blk0_of_blk1 hn h1, h1⟩
  · have h0 := blk0_all_of_block hn hu hw
    exact ⟨h0, blk1_of_blk0 hn h0⟩

end Top

theorem normal_wrp_top {W : Subgroup Sp8} (hle : W ≤ wrp (⊤ : Subgroup Sl28))
    (hn : ∀ h ∈ wrp (⊤ : Subgroup Sl28), ∀ w ∈ W, h * w * h⁻¹ ∈ W) (hW : W ≠ ⊥) :
    (∀ l : Sl28, blk0 l ∈ W) ∧ (∀ l : Sl28, blk1 l ∈ W) := by
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hW
  obtain ⟨x, -, y, -, hw | hw⟩ := hle w.2
  · refine blocks_of_block hn (u := x) (v := y) (fun ⟨hx, hy⟩ => hw1 ?_) (hw ▸ w.2)
    apply Subtype.ext
    rw [hw, hx, hy]
    simp
  ·
    have hwW' : (w : Sp8) ∈ W := w.2
    have hl : slZ ≠ 1 := slZ_ne_one
    have h1 := hn (blk0 slZ) (blk0_mem_wrp_top slZ) _ (W.inv_mem hwW')
    have h2 := W.mul_mem hwW' h1
    have h3 : (w : Sp8) * (blk0 slZ * (w : Sp8)⁻¹ * (blk0 slZ)⁻¹) =
        blk0 (slZ⁻¹) * blk1 (y * slZ * y⁻¹) := by
      rw [hw]
      have hs : swp * blk0 slZ * swp⁻¹ = blk1 slZ := swp_conj_blk0 slZ
      have hcb : (blk0 x * blk1 y) * blk1 slZ * (blk0 x * blk1 y)⁻¹ = blk1 (y * slZ * y⁻¹) := by
        have := conj_blk x y 1 slZ
        simpa using this
      calc blk0 x * blk1 y * swp * (blk0 slZ * (blk0 x * blk1 y * swp)⁻¹ * (blk0 slZ)⁻¹) =
            (blk0 x * blk1 y) * (swp * blk0 slZ * swp⁻¹) * (blk0 x * blk1 y)⁻¹ *
              (blk0 slZ)⁻¹ := by group
        _ = (blk0 x * blk1 y) * blk1 slZ * (blk0 x * blk1 y)⁻¹ * (blk0 slZ)⁻¹ := by rw [hs]
        _ = blk1 (y * slZ * y⁻¹) * (blk0 slZ)⁻¹ := by rw [hcb]
        _ = blk0 (slZ⁻¹) * blk1 (y * slZ * y⁻¹) := by
          rw [← map_inv, (blk_commute _ _).eq]
    rw [h3] at h2
    exact blocks_of_block hn (u := slZ⁻¹) (v := y * slZ * y⁻¹)
      (fun ⟨h, _⟩ => hl (inv_eq_one.1 h)) h2

theorem spE_le_of_blocks {W : Subgroup Sp8} (h0 : blk0 slZ ∈ W) (h1 : blk1 slZ ∈ W) :
    spE ≤ W := by
  intro g hg
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_spE_iff g).1 hg
  have hx' : blk0 x ∈ W := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [map_zpow]
    exact W.zpow_mem h0 n
  have hy' : blk1 y ∈ W := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [map_zpow]
    exact W.zpow_mem h1 n
  exact W.mul_mem hx' hy'

theorem spT0_le_wrp : spT0 ≤ wrp slD := wrp_eq_normalizer ▸ Subgroup.le_normalizer

theorem wrp_normalizes_spT0 {n : Sp8} (hn : n ∈ wrp slD) {t : Sp8} (ht : t ∈ spT0) :
    n * t * n⁻¹ ∈ spT0 :=
  (Subgroup.mem_normalizer_iff.1 (wrp_eq_normalizer ▸ hn : n ∈ Subgroup.normalizer
    (spT0 : Set Sp8)) t).1 ht

theorem normal_wrp_slD {W : Subgroup Sp8} (hle : W ≤ wrp slD)
    (hn : ∀ h ∈ wrp slD, ∀ w ∈ W, h * w * h⁻¹ ∈ W) (hW : W ≠ ⊥) :
    blk0 slZ ∈ W ∧ blk1 slZ ∈ W := by
  have hT : ∃ t ∈ W, t ∈ spT0 ∧ t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hW
    have hwN : (w : Sp8) ∈ wrp slD := hle w.2
    have hcomm : ∀ z ∈ spE, (w : Sp8) * z = z * w := by
      intro z hz
      have hzT : z ∈ spT0 := spE_le_spT0 hz
      have h1 : z * (w : Sp8)⁻¹ * z⁻¹ ∈ W := hn z (spT0_le_wrp hzT) _ (W.inv_mem w.2)
      have h2 : (w : Sp8) * (z * (w : Sp8)⁻¹ * z⁻¹) ∈ W := W.mul_mem w.2 h1
      have h3 : (w : Sp8) * (z * (w : Sp8)⁻¹ * z⁻¹) ∈ spT0 := by
        have : (w : Sp8) * (z * (w : Sp8)⁻¹ * z⁻¹) = ((w : Sp8) * z * (w : Sp8)⁻¹) * z⁻¹ := by
          group
        rw [this]
        exact spT0.mul_mem (wrp_normalizes_spT0 hwN hzT) (spT0.inv_mem hzT)
      have h4 := hcon _ h2 h3
      calc (w : Sp8) * z = ((w : Sp8) * (z * (w : Sp8)⁻¹ * z⁻¹)) * z * w := by group
        _ = z * w := by rw [h4]; group
    have hwT : (w : Sp8) ∈ spT0 := centralizer_spE_le hcomm
    exact hw1 (Subtype.ext (hcon _ w.2 hwT))
  obtain ⟨t, htW, htT, ht1⟩ := hT
  obtain ⟨e, heW, heT, he3, he1⟩ : ∃ e ∈ W, e ∈ spT0 ∧ e ^ 3 = 1 ∧ e ≠ 1 := by
    by_cases h3 : t ^ 3 = 1
    · exact ⟨t, htW, htT, h3, ht1⟩
    · refine ⟨t ^ 3, W.pow_mem htW 3, spT0.pow_mem htT 3, ?_, h3⟩
      rw [← pow_mul]
      exact exp_spT0 t htT
  have hswp : swp ∈ wrp slD := swp_mem_wrp slD
  have hboth : blk0 slZ ∈ W → blk1 slZ ∈ W := fun h => by
    have := hn swp hswp _ h
    rwa [swp_conj_blk0] at this
  rcases spE_cases heT he3 he1 with ⟨n, hnN, rfl⟩ | ⟨n, hnN, rfl⟩
  · have h1 : spZ1 ∈ W := by
      have := hn n⁻¹ (Subgroup.inv_mem _ hnN) _ heW
      have e : n⁻¹ * (n * spZ1 * n⁻¹) * n⁻¹⁻¹ = spZ1 := by group
      rwa [e] at this
    exact ⟨h1, hboth h1⟩
  · have h1 : spZ12 ∈ W := by
      have := hn n⁻¹ (Subgroup.inv_mem _ hnN) _ heW
      have e : n⁻¹ * (n * spZ12 * n⁻¹) * n⁻¹⁻¹ = spZ12 := by group
      rwa [e] at this
    have hw0 : blk0 slW ∈ wrp slD := ⟨slW, slW_mem_slD, 1, slD.one_mem, Or.inl (by simp)⟩
    have h2 := hn _ hw0 _ h1
    have h3 : blk0 slW * spZ12 * (blk0 slW)⁻¹ = blk0 slZ⁻¹ * blk1 slZ := by
      have := conj_blk slW 1 slZ slZ
      simp only [map_one, mul_one, one_mul, inv_one] at this
      rw [slW_conj_z] at this
      rw [spZ12]
      exact this
    rw [h3] at h2
    have hd : blk1 (slZ * slZ) ∈ W := by
      have := W.mul_mem h1 h2
      have e : spZ12 * (blk0 slZ⁻¹ * blk1 slZ) = blk1 (slZ * slZ) := by
        rw [spZ12, blk_mul]
        simp
      rwa [e] at this
    have h4 : blk1 slZ ∈ W := by
      have := W.mul_mem hd hd
      have e : blk1 (slZ * slZ) * blk1 (slZ * slZ) = blk1 slZ := by
        rw [← map_mul]
        congr 1
        have hz3 : slZ * (slZ * slZ) = 1 := by
          have := slZ_pow3
          rwa [pow_three] at this
        calc slZ * slZ * (slZ * slZ) = (slZ * (slZ * slZ)) * slZ := by simp only [mul_assoc]
          _ = slZ := by rw [hz3, one_mul]
      rwa [e] at this
    have h5 : blk0 slZ ∈ W := by
      have := W.mul_mem h1 (W.inv_mem h4)
      have e : spZ12 * (blk1 slZ)⁻¹ = blk0 slZ := by
        rw [spZ12]; group
      rwa [e] at this
    exact ⟨h5, h4⟩

theorem normal_dichotomy_sp8 (θ : Sp8 ≃* Sp8) (hθT : ∀ x, x ∈ spT0 ↔ θ x ∈ spT0)
    {H : Subgroup Sp8}
    (hH : H = wrp slD ∨ H = wrp (⊤ : Subgroup Sl28) ∨
      H = (wrp (⊤ : Subgroup Sl28)).map θ.toMonoidHom)
    {W : Subgroup Sp8} (hle : W ≤ H) (hn : ∀ h ∈ H, ∀ w ∈ W, h * w * h⁻¹ ∈ W) :
    W = ⊥ ∨ spE ≤ W := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  rcases hH with rfl | rfl | rfl
  · obtain ⟨h0, h1⟩ := normal_wrp_slD hle hn hW
    exact spE_le_of_blocks h0 h1
  · obtain ⟨h0, h1⟩ := normal_wrp_top hle hn hW
    exact spE_le_of_blocks (h0 slZ) (h1 slZ)
  · set W' := W.comap θ.toMonoidHom with hW'def
    have hle' : W' ≤ wrp (⊤ : Subgroup Sl28) := by
      intro w hw
      obtain ⟨m, hm, hmw⟩ := hle hw
      have : m = w := θ.injective hmw
      rwa [← this]
    have hn' : ∀ h ∈ wrp (⊤ : Subgroup Sl28), ∀ w ∈ W', h * w * h⁻¹ ∈ W' := by
      intro h hh w hw
      show θ (h * w * h⁻¹) ∈ W
      rw [map_mul, map_mul, map_inv]
      exact hn (θ h) ⟨h, hh, rfl⟩ _ hw
    have hW'ne : W' ≠ ⊥ := by
      intro h
      apply hW
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨m, -, hmw⟩ := hle hw
      have hm : m ∈ W' := by
        show θ m ∈ W
        have : θ m = w := hmw
        rw [this]
        exact hw
      rw [h, Subgroup.mem_bot] at hm
      rw [← hmw, hm, map_one]
      exact Subgroup.one_mem _
    obtain ⟨h0, h1⟩ := normal_wrp_top hle' hn' hW'ne
    have hE : spE ≤ W' := spE_le_of_blocks (h0 slZ) (h1 slZ)
    intro z hz
    have hz' : θ.symm z ∈ spE := by
      rw [mem_spE_iff_cube] at hz ⊢
      refine ⟨?_, ?_⟩
      · rw [hθT, MulEquiv.apply_symm_apply]
        exact hz.1
      · rw [← map_pow, hz.2, map_one]
    have := hE hz'
    show z ∈ W
    have h6 : θ (θ.symm z) ∈ W := this
    rwa [MulEquiv.apply_symm_apply] at h6

end CFSG.AGLEmbedding.KFactProofs.Sp48

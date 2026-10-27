module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Norm

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped MatrixGroups

theorem sl28_commutator_top : (⁅(⊤ : Subgroup Sl28), ⊤⁆ : Subgroup Sl28) = ⊤ := by
  have h : commutator Sl28 = ⊤ := by
    rcases sl28_isSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Sl28) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := sl28_nonabelian
      have hcomm : IsMulCommutative Sl28 := (commutator_eq_bot_iff Sl28).1 h
      exact hab (hcomm.is_comm.comm a b)
    · exact h
  rwa [commutator_def] at h

theorem blk0_range_perfect :
    ⁅MonoidHom.range blk0, MonoidHom.range blk0⁆ = MonoidHom.range blk0 := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, sl28_commutator_top]

theorem blk1_range_perfect :
    ⁅MonoidHom.range blk1, MonoidHom.range blk1⁆ = MonoidHom.range blk1 := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, sl28_commutator_top]

theorem mem_blkRange_iff (g : Sp8) :
    g ∈ MonoidHom.range blkHom ↔ ∃ x y : Sl28, g = blk0 x * blk1 y :=
  ⟨fun ⟨⟨x, y⟩, h⟩ => ⟨x, y, h.symm⟩, fun ⟨x, y, h⟩ => ⟨(x, y), h.symm⟩⟩

theorem blk0_mem_blkRange (x : Sl28) : blk0 x ∈ MonoidHom.range blkHom :=
  (mem_blkRange_iff _).2 ⟨x, 1, by simp⟩

theorem blk1_mem_blkRange (y : Sl28) : blk1 y ∈ MonoidHom.range blkHom :=
  (mem_blkRange_iff _).2 ⟨1, y, by simp⟩

theorem spT0_le_blkRange : spT0 ≤ MonoidHom.range blkHom := fun g hg => by
  obtain ⟨x, -, y, -, rfl⟩ := (mem_spT0_iff g).1 hg
  exact (mem_blkRange_iff _).2 ⟨x, y, rfl⟩

theorem blkRange_le_wrp : MonoidHom.range blkHom ≤ wrp (⊤ : Subgroup Sl28) := fun g hg => by
  obtain ⟨x, y, rfl⟩ := (mem_blkRange_iff g).1 hg
  exact blk_mem_wrp (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem wrp_top_normalizes_blkRange {m : Sp8} (hm : m ∈ wrp (⊤ : Subgroup Sl28)) {v : Sp8}
    (hv : v ∈ MonoidHom.range blkHom) : m * v * m⁻¹ ∈ MonoidHom.range blkHom := by
  obtain ⟨x, y, rfl⟩ := (mem_blkRange_iff v).1 hv
  obtain ⟨a, -, b, -, rfl | rfl⟩ := hm
  · rw [conj_blk]
    exact (mem_blkRange_iff _).2 ⟨_, _, rfl⟩
  · have : blk0 a * blk1 b * swp * (blk0 x * blk1 y) * (blk0 a * blk1 b * swp)⁻¹ =
        (blk0 a * blk1 b) * (swp * (blk0 x * blk1 y) * swp⁻¹) * (blk0 a * blk1 b)⁻¹ := by
      group
    rw [this, conj_swp_blk, conj_blk]
    exact (mem_blkRange_iff _).2 ⟨_, _, rfl⟩

theorem map_blkRange_eq {ω : Sp8 ≃* Sp8}
    (h : (wrp (⊤ : Subgroup Sl28)).map ω.toMonoidHom = wrp (⊤ : Subgroup Sl28)) :
    (MonoidHom.range blkHom).map ω.toMonoidHom = MonoidHom.range blkHom := by
  have hle : (MonoidHom.range blkHom).map ω.toMonoidHom ≤ wrp (⊤ : Subgroup Sl28) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← h]
    exact ⟨v, blkRange_le_wrp hv, rfl⟩
  have hnorm : ∀ m ∈ wrp (⊤ : Subgroup Sl28), ∀ w ∈ (MonoidHom.range blkHom).map ω.toMonoidHom,
      m * w * m⁻¹ ∈ (MonoidHom.range blkHom).map ω.toMonoidHom := by
    rintro m hm _ ⟨v, hv, rfl⟩
    have hm' : m ∈ (wrp (⊤ : Subgroup Sl28)).map ω.toMonoidHom := by rw [h]; exact hm
    obtain ⟨m', hm', rfl⟩ := hm'
    exact ⟨m' * v * m'⁻¹, wrp_top_normalizes_blkRange hm' hv, by simp [map_mul, map_inv]⟩
  have hne : (MonoidHom.range blkHom).map ω.toMonoidHom ≠ ⊥ := by
    intro hbot
    have h1 : ω (blk0 slZ) ∈ (MonoidHom.range blkHom).map ω.toMonoidHom :=
      ⟨_, blk0_mem_blkRange slZ, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have := ω.injective (h1.trans (map_one ω).symm)
    exact spZ1_ne_one this
  obtain ⟨h0, h1⟩ := normal_wrp_top hle hnorm hne
  have hge : MonoidHom.range blkHom ≤ (MonoidHom.range blkHom).map ω.toMonoidHom := by
    intro g hg
    obtain ⟨x, y, rfl⟩ := (mem_blkRange_iff g).1 hg
    exact Subgroup.mul_mem _ (h0 x) (h1 y)
  exact (Subgroup.eq_of_le_of_card_ge hge
    (by rw [Subgroup.card_map_of_injective ω.injective])).symm

theorem blkRange_normalizes_blk0 {v b : Sp8} (hv : v ∈ MonoidHom.range blkHom)
    (hb : b ∈ MonoidHom.range blk0) : v * b * v⁻¹ ∈ MonoidHom.range blk0 := by
  obtain ⟨x, y, rfl⟩ := (mem_blkRange_iff v).1 hv
  obtain ⟨u, rfl⟩ := hb
  have := conj_blk x y u 1
  simp only [map_one, mul_one, mul_inv_cancel] at this
  rw [this]
  exact ⟨x * u * x⁻¹, rfl⟩

theorem blkRange_normalizes_blk1 {v b : Sp8} (hv : v ∈ MonoidHom.range blkHom)
    (hb : b ∈ MonoidHom.range blk1) : v * b * v⁻¹ ∈ MonoidHom.range blk1 := by
  obtain ⟨x, y, rfl⟩ := (mem_blkRange_iff v).1 hv
  obtain ⟨u, rfl⟩ := hb
  have := conj_blk x y 1 u
  simp only [map_one, one_mul, mul_one, mul_inv_cancel] at this
  rw [this]
  exact ⟨y * u * y⁻¹, rfl⟩

theorem map_blk0_range_eq {ω : Sp8 ≃* Sp8}
    (hV : (MonoidHom.range blkHom).map ω.toMonoidHom = MonoidHom.range blkHom)
    (hz : ω (blk0 slZ) = blk0 slZ) :
    (MonoidHom.range blk0).map ω.toMonoidHom = MonoidHom.range blk0 := by
  have hn : ∀ l : Sl28, ∀ w ∈ (MonoidHom.range blk0).map ω.toMonoidHom,
      blk0 l * w * (blk0 l)⁻¹ ∈ (MonoidHom.range blk0).map ω.toMonoidHom := by
    rintro l _ ⟨b, hb, rfl⟩
    have h1 : blk0 l ∈ (MonoidHom.range blkHom).map ω.toMonoidHom := by
      rw [hV]
      exact blk0_mem_blkRange l
    obtain ⟨v, hv, hvl⟩ := h1
    exact ⟨v * b * v⁻¹, blkRange_normalizes_blk0 hv hb, by
      have : ω v = blk0 l := hvl
      simp [map_mul, map_inv, this]⟩
  have hzW : blk0 slZ ∈ (MonoidHom.range blk0).map ω.toMonoidHom := ⟨blk0 slZ, ⟨slZ, rfl⟩, hz⟩
  have hnorm : (((MonoidHom.range blk0).map ω.toMonoidHom).comap blk0).Normal :=
    ⟨fun v hv l => by
      show blk0 (l * v * l⁻¹) ∈ (MonoidHom.range blk0).map ω.toMonoidHom
      rw [map_mul, map_mul, map_inv]
      exact hn l _ hv⟩
  rcases sl28_isSimpleGroup.eq_bot_or_eq_top_of_normal
    (((MonoidHom.range blk0).map ω.toMonoidHom).comap blk0) with h | h
  · exfalso
    have : slZ ∈ ((MonoidHom.range blk0).map ω.toMonoidHom).comap blk0 := hzW
    rw [h, Subgroup.mem_bot] at this
    exact slZ_ne_one this
  · have hge : MonoidHom.range blk0 ≤ (MonoidHom.range blk0).map ω.toMonoidHom := by
      rintro _ ⟨l, rfl⟩
      have : l ∈ ((MonoidHom.range blk0).map ω.toMonoidHom).comap blk0 := by
        rw [h]
        exact Subgroup.mem_top l
      exact this
    exact (Subgroup.eq_of_le_of_card_ge hge
      (by rw [Subgroup.card_map_of_injective ω.injective])).symm

theorem map_blk1_range_eq {ω : Sp8 ≃* Sp8}
    (hV : (MonoidHom.range blkHom).map ω.toMonoidHom = MonoidHom.range blkHom)
    (hz : ω (blk1 slZ) = blk1 slZ) :
    (MonoidHom.range blk1).map ω.toMonoidHom = MonoidHom.range blk1 := by
  have hn : ∀ l : Sl28, ∀ w ∈ (MonoidHom.range blk1).map ω.toMonoidHom,
      blk1 l * w * (blk1 l)⁻¹ ∈ (MonoidHom.range blk1).map ω.toMonoidHom := by
    rintro l _ ⟨b, hb, rfl⟩
    have h1 : blk1 l ∈ (MonoidHom.range blkHom).map ω.toMonoidHom := by
      rw [hV]
      exact blk1_mem_blkRange l
    obtain ⟨v, hv, hvl⟩ := h1
    exact ⟨v * b * v⁻¹, blkRange_normalizes_blk1 hv hb, by
      have : ω v = blk1 l := hvl
      simp [map_mul, map_inv, this]⟩
  have hzW : blk1 slZ ∈ (MonoidHom.range blk1).map ω.toMonoidHom := ⟨blk1 slZ, ⟨slZ, rfl⟩, hz⟩
  have hnorm : (((MonoidHom.range blk1).map ω.toMonoidHom).comap blk1).Normal :=
    ⟨fun v hv l => by
      show blk1 (l * v * l⁻¹) ∈ (MonoidHom.range blk1).map ω.toMonoidHom
      rw [map_mul, map_mul, map_inv]
      exact hn l _ hv⟩
  rcases sl28_isSimpleGroup.eq_bot_or_eq_top_of_normal
    (((MonoidHom.range blk1).map ω.toMonoidHom).comap blk1) with h | h
  · exfalso
    have : slZ ∈ ((MonoidHom.range blk1).map ω.toMonoidHom).comap blk1 := hzW
    rw [h, Subgroup.mem_bot] at this
    exact slZ_ne_one this
  · have hge : MonoidHom.range blk1 ≤ (MonoidHom.range blk1).map ω.toMonoidHom := by
      rintro _ ⟨l, rfl⟩
      have : l ∈ ((MonoidHom.range blk1).map ω.toMonoidHom).comap blk1 := by
        rw [h]
        exact Subgroup.mem_top l
      exact this
    exact (Subgroup.eq_of_le_of_card_ge hge
      (by rw [Subgroup.card_map_of_injective ω.injective])).symm

theorem blkRange_center {v : Sp8} (hv : v ∈ MonoidHom.range blkHom)
    (hc : ∀ w ∈ MonoidHom.range blkHom, v * w = w * v) : v = 1 := by
  obtain ⟨x, y, rfl⟩ := (mem_blkRange_iff v).1 hv
  have hx : x = 1 := by
    refine sl28_center_trivial fun l => ?_
    have h := hc (blk0 l) (blk0_mem_blkRange l)
    have h1 : blk0 x * blk1 y * blk0 l = blk0 (x * l) * blk1 y := by
      have := blk_mul x y l 1
      simpa using this
    have h2 : blk0 l * (blk0 x * blk1 y) = blk0 (l * x) * blk1 y := by
      have := blk_mul l 1 x y
      simpa using this
    rw [h1, h2] at h
    exact (blk_inj h).1
  have hy : y = 1 := by
    refine sl28_center_trivial fun l => ?_
    have h := hc (blk1 l) (blk1_mem_blkRange l)
    have h1 : blk0 x * blk1 y * blk1 l = blk0 x * blk1 (y * l) := by
      have := blk_mul x y 1 l
      simpa using this
    have h2 : blk1 l * (blk0 x * blk1 y) = blk0 x * blk1 (l * y) := by
      have := blk_mul 1 l x y
      simpa using this
    rw [h1, h2] at h
    exact (blk_inj h).2
  rw [hx, hy]
  simp

end CFSG.AGLEmbedding.KFactProofs.Sp48

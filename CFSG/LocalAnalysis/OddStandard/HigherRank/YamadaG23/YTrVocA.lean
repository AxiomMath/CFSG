module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] {f : Γ₁ →* Γ₂}

theorem conjClass_map (T : Subgroup Γ₁) (y : Γ₁) :
    conjClass (T.map f) (f y) = f '' conjClass T y := by
  ext w
  constructor
  · rintro ⟨t', ht', rfl⟩
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp ht'
    exact ⟨t * y * t⁻¹, ⟨t, ht, rfl⟩, by simp [map_mul]⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hv
    exact ⟨f t, Subgroup.mem_map_of_mem f ht, by simp [map_mul]⟩

theorem invols_map (hf : Function.Injective f) (T : Subgroup Γ₁) :
    invols (T.map f) = f '' invols T := by
  ext y
  constructor
  · rintro ⟨hy, horder⟩
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨t, ⟨ht, by rwa [orderOf_injective f hf t] at horder⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨htT, horder⟩ := ht
    exact ⟨Subgroup.mem_map_of_mem f htT, by rw [orderOf_injective f hf t, horder]⟩

theorem cen_map (hf : Function.Injective f) (T : Subgroup Γ₁) :
    cen (T.map f) = (cen T).map f := by
  ext y
  constructor
  · intro hy
    simp only [cen, Subgroup.mem_inf] at hy
    obtain ⟨hyT, hyC⟩ := hy
    obtain ⟨x, hxT, rfl⟩ := Subgroup.mem_map.mp hyT
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    simp only [cen, Subgroup.mem_inf]
    refine ⟨hxT, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    apply hf
    rw [map_mul, map_mul]
    exact hyC (f t) (Subgroup.mem_map_of_mem f ht)
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    simp only [cen, Subgroup.mem_inf] at hx
    obtain ⟨hxT, hxC⟩ := hx
    simp only [cen, Subgroup.mem_inf]
    refine ⟨Subgroup.mem_map_of_mem f hxT, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hh
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hxC t ht]

theorem centEl_map (hf : Function.Injective f) (V : Subgroup Γ₁) (y : Γ₁) :
    centEl (V.map f) (f y) = (centEl V y).map f := by
  ext z
  constructor
  · intro hz
    simp only [centEl, Subgroup.mem_inf] at hz
    obtain ⟨hzV, hzC⟩ := hz
    obtain ⟨x, hxV, rfl⟩ := Subgroup.mem_map.mp hzV
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    simp only [centEl, Subgroup.mem_inf]
    refine ⟨hxV, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hzC ⊢
    apply hf
    rw [map_mul, map_mul]
    exact hzC
  · intro hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    simp only [centEl, Subgroup.mem_inf] at hx
    obtain ⟨hxV, hxC⟩ := hx
    simp only [centEl, Subgroup.mem_inf]
    refine ⟨Subgroup.mem_map_of_mem f hxV, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxC ⊢
    rw [← map_mul, ← map_mul, hxC]

theorem conjSub_map (c : Γ₁) (Y : Subgroup Γ₁) :
    conjSub (f c) (Y.map f) = (conjSub c Y).map f := by
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    refine ⟨c * y' * c⁻¹, ⟨y', hy', rfl⟩, ?_⟩
    simp [map_mul]
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hz
    exact ⟨f y', Subgroup.mem_map_of_mem f hy', by simp [map_mul]⟩

private theorem exists_eq_map_of_le_aux (hf : Function.Injective f) {V : Subgroup Γ₁}
    {N : Subgroup Γ₂} (h : N ≤ V.map f) : ∃ N₁ : Subgroup Γ₁, N₁ ≤ V ∧ N₁.map f = N := by
  refine ⟨N.comap f, ?_, ?_⟩
  · intro x hx
    obtain ⟨v, hv, hveq⟩ := Subgroup.mem_map.mp (h hx)
    rwa [hf hveq] at hv
  · exact Subgroup.map_comap_eq_self (h.trans (Subgroup.map_le_range f V))

theorem isMaximalIn_map (hf : Function.Injective f) (V M : Subgroup Γ₁) :
    IsMaximalIn (V.map f) (M.map f) ↔ IsMaximalIn V M := by
  unfold IsMaximalIn
  constructor
  · rintro ⟨hlt, hmax⟩
    refine ⟨(Subgroup.map_lt_map_iff_of_injective hf).mp hlt, fun N hMN hNV => ?_⟩
    exact Subgroup.map_injective hf
      (hmax (N.map f) ((Subgroup.map_lt_map_iff_of_injective hf).mpr hMN)
        (Subgroup.map_mono hNV))
  · rintro ⟨hlt, hmax⟩
    refine ⟨(Subgroup.map_lt_map_iff_of_injective hf).mpr hlt, fun N hMN hNV => ?_⟩
    obtain ⟨N₁, hN₁V, rfl⟩ := exists_eq_map_of_le_aux hf hNV
    rw [hmax N₁ ((Subgroup.map_lt_map_iff_of_injective hf).mp hMN) hN₁V]

theorem exists_eq_map_of_le (hf : Function.Injective f) {V : Subgroup Γ₁} {N : Subgroup Γ₂}
    (h : N ≤ V.map f) : ∃ N₁ : Subgroup Γ₁, N₁ ≤ V ∧ N₁.map f = N :=
  exists_eq_map_of_le_aux hf h

end CFSG.OddStandard.HigherRank.YamadaG23

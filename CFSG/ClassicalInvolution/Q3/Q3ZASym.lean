module

public import CFSG.ClassicalInvolution.Q3.Q3ZARel

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZA

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.ClassicalInvolution.Q3.Q3Z
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups commutatorElement
open Matrix

theorem mem_planeGroup_lb (k : Fin 2) (x : SL(2, F3)) :
    longBlock F3 2 k x ∈ planeGroup (stdPlane F3 2 k) := by
  rw [planeGroup_stdPlane]
  exact ⟨x, rfl⟩

namespace SymTri

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} (T : SymTri G Ω)

@[expose] noncomputable def sw : G := T.Θ₀₁ swapElt

theorem sw_mul_self : T.sw * T.sw = 1 := by
  rw [sw, ← map_mul, swapElt_mul_self, map_one]

theorem sw_inv : T.sw⁻¹ = T.sw := inv_eq_of_mul_eq_one_right T.sw_mul_self

theorem sw_mem_range : T.sw ∈ T.Θ₀₁.range := ⟨swapElt, rfl⟩

@[expose] noncomputable def Θ₁₂ : StatedSp 2 F3 →* G :=
  (MulAut.conj T.sw).toMonoidHom.comp T.Θ₀₂

theorem Θ₁₂_apply (x : StatedSp 2 F3) : T.Θ₁₂ x = T.sw * T.Θ₀₂ x * T.sw⁻¹ := rfl

theorem inj₁₂ : Function.Injective T.Θ₁₂ := (MulAut.conj T.sw).injective.comp T.inj₀₂

theorem conj_Θ₁₂ (x : StatedSp 2 F3) : T.sw * T.Θ₁₂ x * T.sw⁻¹ = T.Θ₀₂ x := by
  rw [Θ₁₂_apply]
  calc T.sw * (T.sw * T.Θ₀₂ x * T.sw⁻¹) * T.sw⁻¹
      = (T.sw * T.sw) * T.Θ₀₂ x * (T.sw * T.sw)⁻¹ := by group
    _ = T.Θ₀₂ x := by rw [T.sw_mul_self]; group

theorem sw_conj (x : StatedSp 2 F3) :
    T.sw * T.Θ₀₁ x * T.sw⁻¹ = T.Θ₀₁ (swapElt * x * swapElt⁻¹) := by
  simp only [sw, map_mul, map_inv]

theorem sw_conj_lb0 (x : SL(2, F3)) :
    T.sw * T.Θ₀₁ (longBlock F3 2 0 x) * T.sw⁻¹ = T.Θ₀₁ (longBlock F3 2 1 x) := by
  rw [sw_conj, mul_inv_eq_iff_eq_mul.2 (swap_mul_lb x)]

theorem sw_conj_rU (u : F3) : T.sw * rU T.Θ₀₁ u * T.sw⁻¹ = rL T.Θ₀₁ u := by
  show T.sw * T.Θ₀₁ (sb (usl u)) * T.sw⁻¹ = T.Θ₀₁ (sb (lsl u))
  rw [sw_conj, mul_inv_eq_iff_eq_mul.2 (swap_mul_sbU u)]

theorem sw_conj_rL (u : F3) : T.sw * rL T.Θ₀₁ u * T.sw⁻¹ = rU T.Θ₀₁ u := by
  show T.sw * T.Θ₀₁ (sb (lsl u)) * T.sw⁻¹ = T.Θ₀₁ (sb (usl u))
  rw [sw_conj, mul_inv_eq_iff_eq_mul.2 (swap_mul_sbL u)]

theorem Θ₀₁_lb0_mem (x : SL(2, F3)) : T.Θ₀₁ (longBlock F3 2 0 x) ∈ T.K₀ := by
  rw [← T.blk₀₁₀]
  exact ⟨_, mem_planeGroup_lb 0 x, rfl⟩

theorem Θ₀₁_lb1_mem (x : SL(2, F3)) : T.Θ₀₁ (longBlock F3 2 1 x) ∈ T.K₁ := by
  rw [← T.blk₀₁₁]
  exact ⟨_, mem_planeGroup_lb 1 x, rfl⟩

theorem Θ₀₂_lb1_mem (x : SL(2, F3)) : T.Θ₀₂ (longBlock F3 2 1 x) ∈ T.K₂ := by
  rw [← T.blk₀₂₁]
  exact ⟨_, mem_planeGroup_lb 1 x, rfl⟩

theorem Θ₁₂_lb0 (x : SL(2, F3)) : T.Θ₁₂ (longBlock F3 2 0 x) = T.Θ₀₁ (longBlock F3 2 1 x) := by
  rw [Θ₁₂_apply, T.matched x, sw_conj_lb0]

theorem Θ₁₂_lb1 (x : SL(2, F3)) : T.Θ₁₂ (longBlock F3 2 1 x) = T.Θ₀₂ (longBlock F3 2 1 x) := by
  rw [Θ₁₂_apply, T.comm₀₁ T.sw T.sw_mem_range _ (T.Θ₀₂_lb1_mem x), mul_assoc, mul_inv_cancel,
    mul_one]

theorem map_Θ₁₂_planeGroup0 : (planeGroup (stdPlane F3 2 0)).map T.Θ₁₂ = T.K₁ := by
  rw [← T.blk₀₁₁, planeGroup_stdPlane, planeGroup_stdPlane]
  show (longBlock F3 2 0).range.map T.Θ₁₂ = (longBlock F3 2 1).range.map T.Θ₀₁
  rw [MonoidHom.map_range, MonoidHom.map_range]
  congr 1
  exact MonoidHom.ext T.Θ₁₂_lb0

theorem map_Θ₁₂_planeGroup1 : (planeGroup (stdPlane F3 2 1)).map T.Θ₁₂ = T.K₂ := by
  rw [← T.blk₀₂₁, planeGroup_stdPlane]
  show (longBlock F3 2 1).range.map T.Θ₁₂ = (longBlock F3 2 1).range.map T.Θ₀₂
  rw [MonoidHom.map_range, MonoidHom.map_range]
  congr 1
  exact MonoidHom.ext T.Θ₁₂_lb1

theorem comm₁₂ : ∀ a ∈ T.Θ₁₂.range, ∀ b ∈ T.K₀, a * b = b * a := by
  rintro _ ⟨x, rfl⟩ b hb
  have hb' : T.sw * b * T.sw⁻¹ ∈ T.K₁ := by
    rw [← T.blk₀₁₀] at hb
    obtain ⟨y, hy, rfl⟩ := hb
    rw [planeGroup_stdPlane] at hy
    obtain ⟨c, rfl⟩ := hy
    rw [T.sw_conj_lb0]
    exact T.Θ₀₁_lb1_mem c
  have hc := T.comm₀₂ (T.Θ₀₂ x) ⟨x, rfl⟩ _ hb'
  apply (MulAut.conj T.sw).injective
  simp only [map_mul, MulAut.conj_apply]
  rw [T.conj_Θ₁₂]
  exact hc

@[expose] noncomputable def toFrame : C3Frame G Ω where
  K₀ := T.K₀
  K₁ := T.K₁
  K₂ := T.K₂
  Θ₀₁ := T.Θ₀₁
  Θ₁₂ := T.Θ₁₂
  inj₀₁ := T.inj₀₁
  inj₁₂ := T.inj₁₂
  hK₂ := T.mem₂
  blk₀₁₀ := T.blk₀₁₀
  blk₀₁₁ := T.blk₀₁₁
  blk₁₂₀ := T.map_Θ₁₂_planeGroup0
  blk₁₂₁ := T.map_Θ₁₂_planeGroup1
  comm₀₁ := T.comm₀₁
  comm₁₂ := T.comm₁₂

theorem layerTriple : LayerTriple Ω T.Θ₀₁ T.Θ₁₂ T.Θ₀₂ where
  injA := T.inj₀₁
  injB := T.inj₁₂
  injX := T.inj₀₂
  members := ⟨T.K₀, T.K₁, T.K₂, T.mem₀, T.mem₁, T.mem₂, T.blk₀₁₀, T.blk₀₁₁, T.map_Θ₁₂_planeGroup0,
    T.map_Θ₁₂_planeGroup1, T.blk₀₂₀, T.blk₀₂₁, T.comm₀₁, T.comm₁₂, T.comm₀₂⟩
  hub x := (T.Θ₁₂_lb0 x).symm
  end_p x := T.matched x
  end_r x := (T.Θ₁₂_lb1 x).symm

theorem swapCtx {X' : StatedSp 2 F3 →* G} {e : F3} (he : e * e = 1)
    (hU : ∀ u, X' (sb (usl u)) = T.Θ₀₂ (sb (usl (e * u))))
    (hL : ∀ u, X' (sb (lsl u)) = T.Θ₀₂ (sb (lsl (e * u)))) :
    SwapCtx T.Θ₀₁ T.Θ₁₂ X' T.sw e where
  e_sq := he
  aU := T.sw_conj_rU
  aL := T.sw_conj_rL
  cU u := by
    show T.sw * X' (sb (usl u)) * T.sw⁻¹ = T.Θ₁₂ (sb (usl (e * u)))
    rw [hU, Θ₁₂_apply]
  bU u := by
    show T.sw * T.Θ₁₂ (sb (usl u)) * T.sw⁻¹ = X' (sb (usl (e * u)))
    rw [T.conj_Θ₁₂, hU, ← mul_assoc, he, one_mul]
  cL u := by
    show T.sw * X' (sb (lsl u)) * T.sw⁻¹ = T.Θ₁₂ (sb (lsl (e * u)))
    rw [hL, Θ₁₂_apply]
  bL u := by
    show T.sw * T.Θ₁₂ (sb (lsl u)) * T.sw⁻¹ = X' (sb (lsl (e * u)))
    rw [T.conj_Θ₁₂, hL, ← mul_assoc, he, one_mul]

theorem heisCtx_of_heisAt {X' : StatedSp 2 F3 →* G} (hX : ∀ r, ∃ r', X' r = T.Θ₀₂ r')
    (h : HeisAt T.Θ₀₁ T.Θ₁₂ X') : ∃ φ : Heis →* G, HeisCtx T.Θ₀₁ T.Θ₁₂ X' φ := by
  obtain ⟨φ, -, h0, h1, h2, h3, hact⟩ := h
  refine ⟨φ, ⟨h0, h1, h2, h3, hact, (T.Θ₁₂_lb0 _).symm, fun r => ?_⟩⟩
  obtain ⟨r', hr'⟩ := hX r
  rw [hr']
  exact T.comm₀₂ _ ⟨r', rfl⟩ _ (T.Θ₀₁_lb1_mem _)

theorem steinbergFamily_of_heisAt {X' : StatedSp 2 F3 →* G} {e : F3} (he : e * e = 1)
    (hU : ∀ u, X' (sb (usl u)) = T.Θ₀₂ (sb (usl (e * u))))
    (hL : ∀ u, X' (sb (lsl u)) = T.Θ₀₂ (sb (lsl (e * u))))
    (hX : ∀ r, ∃ r', X' r = T.Θ₀₂ r') (h : HeisAt T.Θ₀₁ T.Θ₁₂ X') :
    SteinbergFamily (rU T.Θ₀₁) (rU T.Θ₁₂) (rU X') (rL T.Θ₀₁) (rL T.Θ₁₂) (rL X') := by
  obtain ⟨φ, H⟩ := T.heisCtx_of_heisAt hX h
  exact H.steinbergFamily (T.swapCtx he hU hL)

end SymTri

section Nodes

variable {G : Type} [Group G]

theorem closure_root_ranges (θ : StatedSp 2 F3 →* G) :
    Subgroup.closure (Set.range (rU θ) ∪ Set.range (rL θ)) = (sb.range).map θ := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · exact ⟨_, ⟨usl u, rfl⟩, rfl⟩
    · exact ⟨_, ⟨lsl u, rfl⟩, rfl⟩
  · rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have hle : Subgroup.closure (Set.range (CFSG.LieType.Steinberg.sl2Upper : F3 → SL(2, F3)) ∪
        Set.range (CFSG.LieType.Steinberg.sl2Lower : F3 → SL(2, F3))) ≤
        (Subgroup.closure (Set.range (rU θ) ∪ Set.range (rL θ))).comap (θ.comp sb) := by
      rw [Subgroup.closure_le]
      rintro _ (⟨u, rfl⟩ | ⟨u, rfl⟩)
      · exact Subgroup.subset_closure (Or.inl ⟨u, rfl⟩)
      · exact Subgroup.subset_closure (Or.inr ⟨u, rfl⟩)
    exact hle (CFSG.LieType.Steinberg.Sp.mem_closure_sl2 g)

theorem closure_root_ranges_mem_shortNodes (θ : StatedSp 2 F3 →* G) :
    Subgroup.closure (Set.range (rU θ) ∪ Set.range (rL θ)) ∈ shortNodes θ := by
  rw [closure_root_ranges]
  exact ⟨_, shortBlock_range_mem_adaptedShort, rfl⟩

theorem exists_rU_ne_one {θ : StatedSp 2 F3 →* G} (hθ : Function.Injective θ) :
    ∃ s, rU θ s ≠ 1 := by
  refine ⟨1, fun h => ?_⟩
  have h' : θ (sb (usl 1)) = θ 1 := h.trans (map_one θ).symm
  have h1 : sb (usl 1) = 1 := hθ h'
  have h2 : usl 1 = 1 :=
    (shortBlock_injective (zero_ne_one : (0 : Fin 2) ≠ 1)) (h1.trans (map_one sb).symm)
  have h3 := congrArg (fun m : SL(2, F3) => (m : Matrix (Fin 2) (Fin 2) F3) 0 1) h2
  simp [usl] at h3

end Nodes

namespace SymTri

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} (T : SymTri G Ω)

theorem steinbergA2_of_heisAt
    (h : HeisAt T.Θ₀₁ T.Θ₁₂ T.Θ₀₂ ∨ HeisAt T.Θ₀₁ T.Θ₁₂ (T.Θ₀₂.comp iotaHom)) :
    SteinbergA2 T.toFrame := by
  have key : ∃ X' : StatedSp 2 F3 →* G, SteinbergFamily (rU T.Θ₀₁) (rU T.Θ₁₂) (rU X')
      (rL T.Θ₀₁) (rL T.Θ₁₂) (rL X') := by
    rcases h with h | h
    · exact ⟨T.Θ₀₂, T.steinbergFamily_of_heisAt (e := 1) (by simp) (fun u => by simp)
        (fun u => by simp) (fun r => ⟨r, rfl⟩) h⟩
    · exact ⟨T.Θ₀₂.comp iotaHom, T.steinbergFamily_of_heisAt (e := -1) (by simp)
        (fun u => by simp [iota_sb_usl]) (fun u => by simp [iota_sb_lsl])
        (fun r => ⟨iotaHom r, rfl⟩) h⟩
  obtain ⟨X', hF⟩ := key
  exact ⟨rU T.Θ₀₁, rU T.Θ₁₂, rU X', rL T.Θ₀₁, rL T.Θ₁₂, rL X', hF,
    exists_rU_ne_one T.inj₀₁, closure_root_ranges_mem_shortNodes _,
    closure_root_ranges_mem_shortNodes _⟩

end SymTri

end CFSG.ClassicalInvolution.Q3.Q3ZA

module

public import CFSG.LieType.SpecialLinear.EndNode.Parabolic
public import CFSG.Quasithin.Background.SmithParabolic

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis CFSG.LieType.RootSystem CFSG.LieType.Universal.SpecialLinear

noncomputable section

variable (m : ℕ) (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

@[expose] def firstRowFix {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SLm2 m F) V) : Submodule k V :=
  fixSub ρ (firstRowRadical m F)

@[expose] def lastColFix {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SLm2 m F) V) : Submodule k V :=
  fixSub ρ (lastColRadical m F)

omit [Finite F] in
theorem firstRowFix_stable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SLm2 m F) V) :
    ∀ m' ∈ (embedSucc m F).range, ∀ w ∈ firstRowFix m F ρ, ρ m' w ∈ firstRowFix m F ρ := by
  rintro m' ⟨a, rfl⟩ w hw
  rw [firstRowFix, mem_fixSub] at hw ⊢
  intro s hs
  have hnorm : (embedSucc m F a)⁻¹ * s * embedSucc m F a ∈ firstRowRadical m F := by
    have h := embedSucc_conj_mem_firstRow m F a⁻¹ hs
    simpa [map_inv] using h
  calc ρ s (ρ (embedSucc m F a) w)
        = ρ (s * embedSucc m F a) w := by rw [map_mul, Module.End.mul_apply]
    _ = ρ ((embedSucc m F a) * ((embedSucc m F a)⁻¹ * s * embedSucc m F a)) w := by
          group
    _ = ρ (embedSucc m F a) (ρ ((embedSucc m F a)⁻¹ * s * embedSucc m F a) w) := by
          rw [map_mul, Module.End.mul_apply]
    _ = ρ (embedSucc m F a) w := by rw [hw _ hnorm]

omit [Finite F] in
theorem firstRowFix_stable_embedSucc {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SLm2 m F) V) :
    ∀ g : SLm1 m F, ∀ w ∈ firstRowFix m F ρ,
      ρ (embedSucc m F g) w ∈ firstRowFix m F ρ := by
  intro g w hw
  exact firstRowFix_stable m F ρ (embedSucc m F g) ⟨g, rfl⟩ w hw

omit [Finite F] in
theorem lastColFix_stable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SLm2 m F) V) :
    ∀ m' ∈ (embedCastSucc m F).range, ∀ w ∈ lastColFix m F ρ, ρ m' w ∈ lastColFix m F ρ := by
  rintro m' ⟨a, rfl⟩ w hw
  rw [lastColFix, mem_fixSub] at hw ⊢
  intro s hs
  have hnorm : (embedCastSucc m F a)⁻¹ * s * embedCastSucc m F a ∈ lastColRadical m F := by
    have h := embedCastSucc_conj_mem_lastCol m F a⁻¹ hs
    simpa [map_inv] using h
  calc ρ s (ρ (embedCastSucc m F a) w)
        = ρ (s * embedCastSucc m F a) w := by rw [map_mul, Module.End.mul_apply]
    _ = ρ ((embedCastSucc m F a) *
          ((embedCastSucc m F a)⁻¹ * s * embedCastSucc m F a)) w := by
          group
    _ = ρ (embedCastSucc m F a)
          (ρ ((embedCastSucc m F a)⁻¹ * s * embedCastSucc m F a) w) := by
          rw [map_mul, Module.End.mul_apply]
    _ = ρ (embedCastSucc m F a) w := by rw [hw _ hnorm]

omit [Finite F] in
theorem lastColFix_stable_embedCastSucc {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (SLm2 m F) V) :
    ∀ g : SLm1 m F, ∀ w ∈ lastColFix m F ρ,
      ρ (embedCastSucc m F g) w ∈ lastColFix m F ρ := by
  intro g w hw
  exact lastColFix_stable m F ρ (embedCastSucc m F g) ⟨g, rfl⟩ w hw

@[expose] noncomputable def firstNodeRestrict {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k (SLm2 m F) V) :
    Representation k (SLm1 m F) (firstRowFix m F ρ) :=
  restrictRep (ρ.comp (embedSucc m F)) (firstRowFix m F ρ)
    (firstRowFix_stable_embedSucc m F ρ)

@[expose] noncomputable def lastNodeRestrict {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k (SLm2 m F) V) :
    Representation k (SLm1 m F) (lastColFix m F ρ) :=
  restrictRep (ρ.comp (embedCastSucc m F)) (lastColFix m F ρ)
    (lastColFix_stable_embedCastSucc m F ρ)

private instance finite_coxeterGroup_A (n : ℕ) :
    Finite (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_A n)).Group :=
  CFSG.LieType.RootSystem.finite_group (isFiniteType_A n)

theorem firstNodeRestrict_isSimple {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [CharP k p] {ρ : Representation k (SLm2 m F) V} (hρ : IsSimpleRep ρ)
    (hsplit : SplitOver k (curtisDatum (m+1) F p).H)
    {y : V} (hyW : y ∈ firstRowFix m F ρ) (hy0 : y ≠ 0) :
    IsSimpleRep (firstNodeRestrict m F ρ) := by
  have hne : firstRowFix m F ρ ≠ ⊥ := by
    intro hbot
    have hy : y ∈ (⊥ : Submodule k V) := by rw [← hbot]; exact hyW
    exact hy0 (by simpa using hy)
  refine ⟨Submodule.nontrivial_iff_ne_bot.mpr hne, ?_⟩
  intro X hX
  let Y : Submodule k V := X.map (firstRowFix m F ρ).subtype
  have hY : Y ≤ fixSub ρ (firstRowRadical m F) := by
    intro v hv
    obtain ⟨x, _, rfl⟩ := Submodule.mem_map.mp hv
    exact x.2
  have hYP : ∀ m' ∈ (embedSucc m F).range, ∀ v ∈ Y, ρ m' v ∈ Y := by
    intro m' hm' v hv
    obtain ⟨a, rfl⟩ := hm'
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
    exact Submodule.mem_map.mpr ⟨_, hX a x hx, rfl⟩
  have hsmith := (curtisDatum (m+1) F p).eq_bot_or_fixSub_le
    (hsplit := hsplit) (ρ := ρ) hρ
    (N := firstRowRadical m F) (N' := firstColRadical m F)
    (P := (embedSucc m F).range)
    (embedSucc_range_normalizes_firstRow m F)
    (embedSucc_range_normalizes_firstCol m F)
    (firstColRadical_le_L m F p)
    (curtisDatum_U_le_firstRow_sup m F p)
    (curtisDatum_L_le_firstCol_sup m F p) hY hYP
  rcases hsmith with hbot | htop
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hxv : (x : V) ∈ Y := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hbot] at hxv
    exact Subtype.ext (by simpa using hxv)
  · right
    rw [Submodule.eq_top_iff']
    intro w
    have hwY : (w : V) ∈ Y := htop w.2
    obtain ⟨x, hx, hxw⟩ := Submodule.mem_map.mp hwY
    exact (Subtype.ext hxw) ▸ hx

theorem lastNodeRestrict_isSimple {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [CharP k p] {ρ : Representation k (SLm2 m F) V} (hρ : IsSimpleRep ρ)
    (hsplit : SplitOver k (curtisDatum (m+1) F p).H)
    {y : V} (hyW : y ∈ lastColFix m F ρ) (hy0 : y ≠ 0) :
    IsSimpleRep (lastNodeRestrict m F ρ) := by
  have hne : lastColFix m F ρ ≠ ⊥ := by
    intro hbot
    have hy : y ∈ (⊥ : Submodule k V) := by rw [← hbot]; exact hyW
    exact hy0 (by simpa using hy)
  refine ⟨Submodule.nontrivial_iff_ne_bot.mpr hne, ?_⟩
  intro X hX
  let Y : Submodule k V := X.map (lastColFix m F ρ).subtype
  have hY : Y ≤ fixSub ρ (lastColRadical m F) := by
    intro v hv
    obtain ⟨x, _, rfl⟩ := Submodule.mem_map.mp hv
    exact x.2
  have hYP : ∀ m' ∈ (embedCastSucc m F).range, ∀ v ∈ Y, ρ m' v ∈ Y := by
    intro m' hm' v hv
    obtain ⟨a, rfl⟩ := hm'
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
    exact Submodule.mem_map.mpr ⟨_, hX a x hx, rfl⟩
  have hsmith := (curtisDatum (m+1) F p).eq_bot_or_fixSub_le
    (hsplit := hsplit) (ρ := ρ) hρ
    (N := lastColRadical m F) (N' := lastRowRadical m F)
    (P := (embedCastSucc m F).range)
    (embedCastSucc_range_normalizes_lastCol m F)
    (embedCastSucc_range_normalizes_lastRow m F)
    (lastRowRadical_le_L m F p)
    (curtisDatum_U_le_lastCol_sup m F p)
    (curtisDatum_L_le_lastRow_sup m F p) hY hYP
  rcases hsmith with hbot | htop
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hxv : (x : V) ∈ Y := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hbot] at hxv
    exact Subtype.ext (by simpa using hxv)
  · right
    rw [Submodule.eq_top_iff']
    intro w
    have hwY : (w : V) ∈ Y := htop w.2
    obtain ⟨x, hx, hxw⟩ := Submodule.mem_map.mp hwY
    exact (Subtype.ext hxw) ▸ hx

end

end CFSG.LieType.SpecialLinear

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8FrameDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame

variable {G H : Type*} [Group G] [Group H]

private theorem setEq_map {ν : G → ℕ} {ν' : H → ℕ} {s : ℕ} {J : Subgroup G} (θ : G →* H)
    (hν : ∀ x, ν' (θ x) = ν x) :
    {y : H | y ∈ J.map θ ∧ ν' y = s} = θ '' {x : G | x ∈ J ∧ ν x = s} := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, by rwa [hν] at hy⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hxs⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rwa [hν]⟩

theorem FrameProps.map {ν : G → ℕ} {ν' : H → ℕ} {s : ℕ} {R J : Subgroup G}
    (h : FrameProps ν s R J) (θ : G →* H) (hθ : Function.Injective θ)
    (hν : ∀ x, ν' (θ x) = ν x) : FrameProps ν' s (R.map θ) (J.map θ) where
  one_ne := by rw [← map_one θ, hν]; exact h.one_ne
  ncard_eq := by
    rw [setEq_map θ hν, Set.ncard_image_of_injective _ hθ]
    exact h.ncard_eq
  le_closure := by
    rw [setEq_map θ hν, ← MonoidHom.map_closure]
    exact Subgroup.map_mono h.le_closure
  sep := by
    rintro _ ⟨x, hxJ, rfl⟩ hx1 hνx
    obtain ⟨m, hm, hd⟩ := h.sep x hxJ (fun h' => hx1 (by rw [h', map_one])) (by rwa [hν] at hνx)
    refine ⟨fun k => θ (m k), fun k => ⟨⟨m k, (hm k).1, rfl⟩, ?_⟩, fun k l hkl => ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨m k * j * (m k)⁻¹, (Subgroup.mem_normalizer_iff.1 (hm k).2 j).1 hj, by simp⟩
      · rintro ⟨j, hj, hjy⟩
        refine ⟨(m k)⁻¹ * j * m k, (Subgroup.mem_normalizer_iff''.1 (hm k).2 j).1 hj, ?_⟩
        rw [map_mul, map_mul, map_inv, hjy]
        group
    · refine ⟨fun h' => (hd k l hkl).1 (hθ ?_), fun h' => (hd k l hkl).2 (hθ ?_)⟩ <;>
        simpa using h'
  simple := by
    rintro _ ⟨x, hxJ, rfl⟩ hνx
    obtain ⟨W, hW, hWs, ⟨a, b, hab⟩, hW3⟩ := h.simple x hxJ (by rwa [hν] at hνx)
    refine ⟨W.map θ, le_inf (Subgroup.map_mono (hW.trans inf_le_left)) ?_,
      (W.equivMapOfInjective θ hθ).isSimpleGroup_congr.1 hWs,
      ⟨W.equivMapOfInjective θ hθ a, W.equivMapOfInjective θ hθ b, fun h' => hab ?_⟩, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      rw [← map_mul, ← map_mul]
      exact congrArg θ (Subgroup.mem_centralizer_iff.1 (hW hw).2 x rfl)
    · exact (W.equivMapOfInjective θ hθ).injective (by rw [map_mul, map_mul]; exact h')
    · rwa [Subgroup.card_map_of_injective hθ]

theorem FrameProps.subgroupOf {ν : G → ℕ} {s : ℕ} {R J : Subgroup G} (h : FrameProps ν s R J)
    (hJR : J ≤ R) : FrameProps (fun x : R => ν x) s ⊤ (J.subgroupOf R) where
  one_ne := h.one_ne
  ncard_eq := by
    have : {x : R | x ∈ J.subgroupOf R ∧ ν x = s} = Subtype.val ⁻¹' {x : G | x ∈ J ∧ ν x = s} :=
      rfl
    rw [this, Set.ncard_preimage_of_injective_subset_range Subtype.val_injective]
    · exact h.ncard_eq
    · rintro x ⟨hx, -⟩
      exact ⟨⟨x, hJR hx⟩, rfl⟩
  le_closure := by
    intro y hy
    have h1 : (y : G) ∈ Subgroup.closure {x : G | x ∈ J ∧ ν x = s} := h.le_closure hy
    have h2 : R.subtype '' {x : R | x ∈ J.subgroupOf R ∧ ν x = s} =
        {x : G | x ∈ J ∧ ν x = s} := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · rintro ⟨hx, hxs⟩
        exact ⟨⟨x, hJR hx⟩, ⟨hx, hxs⟩, rfl⟩
    rw [← h2, ← MonoidHom.map_closure] at h1
    obtain ⟨z, hz, hzy⟩ := h1
    have : z = y := Subtype.ext hzy
    rwa [this] at hz
  sep := by
    intro x hx hx1 hνx
    obtain ⟨m, hm, hd⟩ := h.sep x hx (fun h' => hx1 (Subtype.ext h')) hνx
    refine ⟨fun k => ⟨m k, (hm k).1⟩, fun k => ⟨Subgroup.mem_top _, ?_⟩, fun k l hkl => ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      exact Subgroup.mem_normalizer_iff.1 (hm k).2 (y : G)
    · refine ⟨fun h' => (hd k l hkl).1 (congrArg Subtype.val h'),
        fun h' => (hd k l hkl).2 (congrArg Subtype.val h')⟩
  simple := by
    intro x hx hνx
    obtain ⟨W, hW, hWs, ⟨a, b, hab⟩, hW3⟩ := h.simple x hx hνx
    have hWR : W ≤ R := hW.trans inf_le_left
    refine ⟨W.subgroupOf R, le_inf le_top ?_,
      (Subgroup.subgroupOfEquivOfLe hWR).isSimpleGroup_congr.2 hWs,
      ⟨(Subgroup.subgroupOfEquivOfLe hWR).symm a, (Subgroup.subgroupOfEquivOfLe hWR).symm b,
        fun h' => hab ?_⟩, ?_⟩
    · intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hW hw).2 (x : G) rfl)
    · exact (Subgroup.subgroupOfEquivOfLe hWR).symm.injective (by rw [map_mul, map_mul]; exact h')
    · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWR).toEquiv]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame

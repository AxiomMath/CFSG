module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ModelTwoAF

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
open CFSG.RankThreeCoreUniqueness.Helpers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fixes_pred_blocks_of_normal_isPGroup_W
    {W : Subgroup (Perm (ι × Bool))} (hWF : W ≤ blockFix ι)
    (hWfl : ∀ i : ι, ∃ w ∈ W, w (i, false) = (i, true))
    [DecidablePred fun i : ι => blockTransp i ∈ W]
    (hcardC : Fintype.card {i // ¬ blockTransp i ∈ W} ≠ 2 ∧
      Fintype.card {i // ¬ blockTransp i ∈ W} ≠ 4)
    {N Q : Subgroup (Perm (ι × Bool))}
    (hNW : N ≤ Subgroup.normalizer (W : Set (Perm (ι × Bool))))
    (hNlift : ∀ π : Perm ι, (∀ i, blockTransp i ∈ W ↔ blockTransp (π i) ∈ W) →
      prodCongrLeft (fun _ : Bool => π) ∈ N)
    (hQN : Q ≤ N) (hQ : IsPGroup 2 Q) (hQn : ∀ x ∈ N, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) :
    ∀ q ∈ Q, ∀ (i : ι) (b : Bool), ¬ blockTransp i ∈ W → ((q : Perm (ι × Bool)) (i, b)).1 = i := by
  have hstab : ∀ g ∈ N, g ∈ blockStab ι := fun g hg =>
    blockStab_of_mem_normalizer hWF hWfl (hNW hg)
  set Q' : Subgroup (Perm ι) := (Q.subgroupOf (blockStab ι)).map blockMapHom with hQ'
  have hQ'p : IsPGroup 2 Q' :=
    (hQ.comap_of_injective _ (blockStab ι).subtype_injective).map blockMapHom
  have hQ's : Q' ≤ predStab (fun i : ι => blockTransp i ∈ W) := by
    rintro _ ⟨⟨q, hqs⟩, hq, rfl⟩ i
    exact tt_mem_iff_of_mem_normalizer (hNW (hQN (Subgroup.mem_subgroupOf.1 hq))) hqs i
  have hQ'n : ∀ σ ∈ predStab (fun i : ι => blockTransp i ∈ W), ∀ π ∈ Q', σ * π * σ⁻¹ ∈ Q' := by
    rintro σ hσ _ ⟨⟨q, hqs⟩, hq, rfl⟩
    have hqQ : q ∈ Q := Subgroup.mem_subgroupOf.1 hq
    have hx : prodCongrLeft (fun _ : Bool => σ) ∈ N := hNlift σ hσ
    have hxs := hstab _ hx
    have hbx : blockMapHom (⟨prodCongrLeft (fun _ : Bool => σ), hxs⟩ : ↥(blockStab ι)) = σ := by
      ext a
      have := blockMapHom_apply (⟨prodCongrLeft (fun _ : Bool => σ), hxs⟩ : ↥(blockStab ι)) (a, false)
      exact this.trans rfl
    have hxqN : prodCongrLeft (fun _ : Bool => σ) * q * (prodCongrLeft (fun _ : Bool => σ))⁻¹ ∈ Q :=
      hQn _ hx q hqQ
    refine ⟨⟨_, (blockStab ι).mul_mem ((blockStab ι).mul_mem hxs hqs) ((blockStab ι).inv_mem hxs)⟩,
      Subgroup.mem_subgroupOf.2 hxqN, ?_⟩
    have : (⟨prodCongrLeft (fun _ : Bool => σ) * q * (prodCongrLeft (fun _ : Bool => σ))⁻¹,
        (blockStab ι).mul_mem ((blockStab ι).mul_mem hxs hqs) ((blockStab ι).inv_mem hxs)⟩ :
        ↥(blockStab ι)) = ⟨_, hxs⟩ * ⟨q, hqs⟩ * ⟨_, hxs⟩⁻¹ := Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hbx]
  have hQ's' : Q' ≤ predStab (fun i : ι => ¬ blockTransp i ∈ W) := by
    rw [predStab_not (fun i : ι => blockTransp i ∈ W)]; exact hQ's
  have hQ'n' : ∀ σ ∈ predStab (fun i : ι => ¬ blockTransp i ∈ W), ∀ π ∈ Q', σ * π * σ⁻¹ ∈ Q' := by
    rw [predStab_not (fun i : ι => blockTransp i ∈ W)]; exact hQ'n
  have h2 := eq_one_of_normal_isPGroup_pred (fun i : ι => ¬ blockTransp i ∈ W) hcardC hQ'p hQ's' hQ'n'
  intro q hq i b hi
  have hqs : q ∈ blockStab ι := hstab q (hQN hq)
  have hmem : blockMapHom (⟨q, hqs⟩ : ↥(blockStab ι)) ∈ Q' :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hq)
  have := h2 _ hmem i hi
  rw [← blockMapHom_apply (⟨q, hqs⟩ : ↥(blockStab ι)) (i, b)] at *
  exact this

variable {G : Type} [Group G] [Finite G] {S M : Subgroup G}

theorem theta_S_fixes_true_blocks (hA : Asc81bHyp M S) (_hι : 5 ≤ Fintype.card ι)
    (θ : ↥M →* Perm (ι × Bool))
    (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ S)
    (hAlt : ∀ x ∈ alternatingGroup (ι × Bool), ∃ m : ↥M, θ m = x)
    (T : Finset ι)
    (hW : (((thompsonJ S).subgroupOf M).map θ : Subgroup (Perm (ι × Bool))) =
      ((fsign T).ker).map (blockPermHom ι))
    (hT1 : T.card ≠ 1) (hT2 : T.card ≠ 2) (hT4 : T.card ≠ 4)
    (s : ↥M) (hs : (s : G) ∈ S) (i : ι) (hi : i ∈ T) (b : Bool) :
    (θ s (i, b)).1 = i := by
  classical
  set W : Subgroup (Perm (ι × Bool)) := ((thompsonJ S).subgroupOf M).map θ with hWdef
  have hWF : W ≤ blockFix ι := by
    rw [hW]; rintro _ ⟨g, -, rfl⟩; exact blockPermHom_mem g
  have hWfl := exists_flip_of_AT T hT1
  rw [← hW] at hWfl
  have hts : ∀ i, blockTransp i ∈ W ↔ i ∉ T := fun i => by
    rw [hW]; exact mem_blockPermHom_map_ker_iff T i
  have hcardC : Fintype.card {i // ¬ blockTransp i ∈ W} = T.card := by
    rw [Fintype.card_subtype]
    congr 1
    ext i
    simp [hts i]
  set Ss : Subgroup (Perm (ι × Bool)) := (S.subgroupOf M).map θ with hSs
  have hSp : IsPGroup 2 (S.subgroupOf M) :=
    hA.twoRadical.isPGroup.comap_of_injective M.subtype M.subtype_injective
  have hSsp : IsPGroup 2 Ss := hSp.map θ
  set N : Subgroup (Perm (ι × Bool)) :=
    θ.range ⊓ Subgroup.normalizer (W : Set (Perm (ι × Bool))) with hN
  have hQN : Ss ≤ N := by
    rintro _ ⟨s', hs', rfl⟩
    exact ⟨⟨s', rfl⟩, theta_mem_normalizer_W θ s'
      (Subgroup.le_normalizer (Subgroup.mem_subgroupOf.1 hs'))⟩
  have hNlift : ∀ π : Perm ι, (∀ i, blockTransp i ∈ W ↔ blockTransp (π i) ∈ W) →
      prodCongrLeft (fun _ : Bool => π) ∈ N := by
    intro π hπ
    have hπT : ∀ i, i ∈ T ↔ π i ∈ T := fun i => by
      have := hπ i
      rw [hts, hts] at this
      exact not_iff_not.1 this
    have hsign : sign (prodCongrLeft fun _ : Bool => π) = 1 := by
      rw [sign_prodCongrLeft, Fintype.prod_bool]
      exact Int.units_mul_self _
    refine ⟨?_, ?_⟩
    · obtain ⟨m, hm⟩ := hAlt _ (mem_alternatingGroup.2 hsign)
      exact ⟨m, hm⟩
    · exact liftBlocks_mem_normalizer T W hW π hπT
  have hQn : ∀ x ∈ N, ∀ q ∈ Ss, x * q * x⁻¹ ∈ Ss := by
    rintro x ⟨⟨m, rfl⟩, hxN⟩ q ⟨s', hs', rfl⟩
    have hmN : (m : G) ∈ Subgroup.normalizer (S : Set G) :=
      mem_normalizer_of_theta_normalizes hA le_rfl hA.twoRadical.1 θ hker m hxN
    have hsS : (s' : G) ∈ S := Subgroup.mem_subgroupOf.1 hs'
    have h1 : (m : G) * (s' : G) * (m : G)⁻¹ ∈ S := ((Subgroup.mem_normalizer_iff.1 hmN) _).1 hsS
    exact ⟨m * s' * m⁻¹, Subgroup.mem_subgroupOf.2 (by simpa using h1), by simp⟩
  exact fixes_pred_blocks_of_normal_isPGroup_W hWF hWfl (by rw [hcardC]; exact ⟨hT2, hT4⟩)
    (N := N) (Q := Ss) inf_le_right hNlift hQN hSsp hQn (θ s) ⟨s, Subgroup.mem_subgroupOf.2 hs, rfl⟩
    i b (by rw [hts]; simpa using hi)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

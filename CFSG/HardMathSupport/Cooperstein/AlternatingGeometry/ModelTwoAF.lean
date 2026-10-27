module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.CgsNormalizer
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.AFChar
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BlockFixOfNormalW

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
open CFSG.RankThreeCoreUniqueness.Helpers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem blockPermHom_tI (i : ι) : blockPermHom ι (tI i) = blockTransp i := by
  refine Equiv.ext fun ⟨k, b⟩ => ?_
  by_cases hk : k = i
  · subst hk
    cases b
    · show (k, tI k k false) = swap (k, false) (k, true) (k, false)
      rw [swap_apply_left, tI_apply, if_pos rfl]
      simp [bsw]
    · show (k, tI k k true) = swap (k, false) (k, true) (k, true)
      rw [swap_apply_right, tI_apply, if_pos rfl]
      simp [bsw]
  · show (k, tI i k b) = swap (i, false) (i, true) (k, b)
    rw [swap_apply_of_ne_of_ne (by simp [hk]) (by simp [hk]), tI_apply, if_neg hk]
    rfl

variable {G : Type} [Group G] [Finite G] {S M : Subgroup G}

theorem theta_mem_normalizer_W {Ω : Type*} (θ : ↥M →* Perm Ω) (m : ↥M)
    (hm : (m : G) ∈ Subgroup.normalizer (S : Set G)) :
    θ m ∈ Subgroup.normalizer
      ((((thompsonJ S).subgroupOf M).map θ : Subgroup (Perm Ω)) : Set (Perm Ω)) := by
  have hJ : (m : G) ∈ Subgroup.normalizer (thompsonJ S : Set G) :=
    normalizer_le_normalizer_thompsonJ S hm
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨m * j * m⁻¹, Subgroup.mem_subgroupOf.2 ?_, by simp⟩
    exact ((Subgroup.mem_normalizer_iff.1 hJ) (j : G)).1 (Subgroup.mem_subgroupOf.1 hj)
  · rintro ⟨j, hj, hjw⟩
    refine ⟨m⁻¹ * j * m, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · have := ((Subgroup.mem_normalizer_iff.1 hJ) (((m⁻¹ * j * m : ↥M)) : G)).2
      have h2 : (m : G) * ((m⁻¹ * j * m : ↥M) : G) * (m : G)⁻¹ = (j : G) := by
        simp [mul_assoc]
      exact this (by rw [h2]; exact Subgroup.mem_subgroupOf.1 hj)
    · have : θ (m⁻¹ * j * m) = (θ m)⁻¹ * θ j * θ m := by simp [map_mul, map_inv]
      rw [this, hjw]; group

theorem mem_of_theta_mem_blockFix_gen (hA : Asc81bHyp M S) (θ : ↥M →* Perm (ι × Bool))
    (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ S)
    (hbs : ∀ m : ↥M, (m : G) ∈ Subgroup.normalizer (S : Set G) → θ m ∈ blockStab ι)
    (hWJ : ∀ σ ∈ blockFix ι, σ ∈ Subgroup.normalizer
      ((((thompsonJ S).subgroupOf M).map θ : Subgroup (Perm (ι × Bool))) : Set (Perm (ι × Bool))))
    (m : ↥M) (hm : θ m ∈ blockFix ι) : (m : G) ∈ S := by
  classical
  set Y : Subgroup G := ((blockFix ι).comap θ).map M.subtype with hY
  have hYM : Y ≤ M := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hYN : Y ≤ Subgroup.normalizer (S : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_normalizer_of_theta_normalizes hA le_rfl hA.twoRadical.1 θ hker y (hWJ _ hy)
  have hYH : Y ≤ M ⊓ Subgroup.normalizer (S : Set G) := le_inf hYM hYN
  have hYn : (Y.subgroupOf (M ⊓ Subgroup.normalizer (S : Set G))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨z, hz, hzn⟩ := Subgroup.mem_subgroupOf.1 hn
    have hgM : (g : G) ∈ M := g.2.1
    have hθg : θ ⟨g, hgM⟩ ∈ blockStab ι := hbs ⟨g, hgM⟩ g.2.2
    have hθz : θ z ∈ blockFix ι := hz
    have hzeq : z = ⟨(n : G), n.2.1⟩ := Subtype.ext hzn
    refine Subgroup.mem_subgroupOf.2 ⟨⟨g, hgM⟩ * z * ⟨g, hgM⟩⁻¹, ?_, ?_⟩
    · show θ (⟨g, hgM⟩ * z * ⟨g, hgM⟩⁻¹) ∈ blockFix ι
      rw [map_mul, map_mul, map_inv]
      exact conj_mem_blockFix hθg hθz
    · rw [hzeq]; rfl
  have hYp : IsPGroup 2 Y := by
    rintro ⟨y, z, hz, rfl⟩
    have hθz : θ z ∈ blockFix ι := hz
    have h2 : θ (z * z) = 1 := by rw [map_mul]; exact blockFix_sq hθz
    obtain ⟨k, hk⟩ := hA.twoRadical.isPGroup ⟨(z * z : ↥M), hker _ h2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : (((z : G) * (z : G)) ^ 2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    show (z : G) ^ 2 ^ (k + 1) = 1
    rw [pow_succ, mul_comm, pow_mul, pow_two]
    exact hk'
  have hle : Y ≤ pCoreOf 2 (M ⊓ Subgroup.normalizer (S : Set G)) :=
    normal_pGroup_le_pCoreOf 2 Y _ hYH hYn hYp
  have hS : pCoreOf 2 (M ⊓ Subgroup.normalizer (S : Set G)) = S := hA.twoRadical.2.2.symm
  rw [hS] at hle
  exact hle ⟨m, hm, rfl⟩

theorem mem_blockPermHom_map_ker_iff (T : Finset ι) (i : ι) :
    blockTransp i ∈ ((fsign T).ker).map (blockPermHom ι) ↔ i ∉ T := by
  rw [← blockPermHom_tI, Subgroup.mem_map_iff_mem blockPermHom_injective, MonoidHom.mem_ker,
    fsign_tI]
  by_cases h : i ∈ T
  · simp [h]
  · simp [h]

theorem exists_flip_of_AT (T : Finset ι) (hT1 : T.card ≠ 1) (i : ι) :
    ∃ w ∈ ((fsign T).ker).map (blockPermHom ι), w (i, false) = (i, true) := by
  by_cases hi : i ∈ T
  · obtain ⟨j, hjT, hji⟩ : ∃ j ∈ T, j ≠ i := by
      have hpos : 1 < T.card := by
        have : 0 < T.card := Finset.card_pos.2 ⟨i, hi⟩
        omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hpos
      by_cases hai : a = i
      · exact ⟨b, hb, fun h => hab (hai.trans h.symm)⟩
      · exact ⟨a, ha, hai⟩
    refine ⟨blockPermHom ι (tI i * tI j), ⟨tI i * tI j, ?_, rfl⟩, ?_⟩
    · exact MonoidHom.mem_ker.2 (by
        rw [map_mul, fsign_tI, fsign_tI, if_pos hi, if_pos hjT]; decide)
    · simp [blockPermHom, blockPerm_apply, Pi.mul_apply, tI_apply, Ne.symm hji, bsw]
  · exact ⟨blockTransp i, (mem_blockPermHom_map_ker_iff T i).2 hi, swap_apply_left _ _⟩

theorem theta_S_iff_mem_blockFix_AF (hA : Asc81bHyp M S) (hι : 5 ≤ Fintype.card ι)
    (θ : ↥M →* Perm (ι × Bool))
    (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ S)
    (hAlt : ∀ x ∈ alternatingGroup (ι × Bool), ∃ m : ↥M, θ m = x)
    (T : Finset ι)
    (hW : (((thompsonJ S).subgroupOf M).map θ : Subgroup (Perm (ι × Bool))) =
      ((fsign T).ker).map (blockPermHom ι))
    (hT1 : T.card ≠ 1) (hT2 : T.card ≠ 2) (hT4 : T.card ≠ 4)
    (hTc2 : Tᶜ.card ≠ 2) (hTc4 : Tᶜ.card ≠ 4) (x : Perm (ι × Bool)) :
    (∃ s : ↥M, (s : G) ∈ S ∧ θ s = x) ↔ x ∈ blockFix ι ∧ x ∈ θ.range := by
  classical
  set W : Subgroup (Perm (ι × Bool)) := ((thompsonJ S).subgroupOf M).map θ with hWdef
  have hWF : W ≤ blockFix ι := by
    rw [hW]; rintro _ ⟨g, -, rfl⟩; exact blockPermHom_mem g
  have hWfl := exists_flip_of_AT T hT1
  rw [← hW] at hWfl
  have hts : ∀ i, blockTransp i ∈ W ↔ i ∉ T := fun i => by
    rw [hW]; exact mem_blockPermHom_map_ker_iff T i
  have hbs : ∀ m : ↥M, (m : G) ∈ Subgroup.normalizer (S : Set G) → θ m ∈ blockStab ι :=
    fun m hm => blockStab_of_mem_normalizer hWF hWfl (theta_mem_normalizer_W θ m hm)
  have hWJ : ∀ σ ∈ blockFix ι, σ ∈ Subgroup.normalizer (W : Set (Perm (ι × Bool))) := by
    intro σ hσ
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hconj : ∀ y ∈ blockFix ι, σ * y * σ⁻¹ = y := fun y hy => by
      have := blockFix_mul_comm hσ hy
      rw [this]; group
    constructor
    · intro hmem; rw [hconj h (hWF hmem)]; exact hmem
    · intro hmem
      have hF : σ * h * σ⁻¹ ∈ blockFix ι := hWF hmem
      have hhF : h ∈ blockFix ι := by
        have := conj_mem_blockFix ((blockStab ι).inv_mem (blockFix_le_blockStab hσ)) hF
        simpa [mul_assoc] using this
      rw [hconj h hhF] at hmem; exact hmem
  have hcardT : Fintype.card {i // blockTransp i ∈ W} = Tᶜ.card := by
    rw [Fintype.card_subtype]
    congr 1
    ext i
    simp [hts i]
  have hcardC : Fintype.card {i // ¬ blockTransp i ∈ W} = T.card := by
    rw [Fintype.card_subtype]
    congr 1
    ext i
    simp [hts i]
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨?_, ⟨s, rfl⟩⟩
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
    have hle : Ss ≤ blockFix ι :=
      le_blockFix_of_normal_isPGroup_W hWF hWfl
        (by rw [hcardT]; exact ⟨hTc2, hTc4⟩) (by rw [hcardC]; exact ⟨hT2, hT4⟩)
        (N := N) (Q := Ss) inf_le_right hNlift hQN hSsp hQn
    exact hle ⟨s, Subgroup.mem_subgroupOf.2 hs, rfl⟩
  · rintro ⟨hx, m, rfl⟩
    exact ⟨m, mem_of_theta_mem_blockFix_gen hA θ hker hbs hWJ m hx, rfl⟩

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

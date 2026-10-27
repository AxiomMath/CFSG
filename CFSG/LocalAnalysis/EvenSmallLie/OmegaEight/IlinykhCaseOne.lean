module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.IlinykhFrame
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.IlinykhGL
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.EvenSmallLie.OmegaEight

open Finset

@[expose] def evenSub : AddSubgroup FrameVec where
  carrier := {v | ∑ i, v i = 0}
  add_mem' {v w} hv hw := by
    change ∑ i, (v i + w i) = 0
    rw [sum_add_distrib]
    change ∑ i, v i = 0 at hv
    change ∑ i, w i = 0 at hw
    rw [hv, hw, add_zero]
  zero_mem' := by
    change ∑ _i : Fin 8, (0 : ZMod 2) = 0
    rw [sum_const_zero]
  neg_mem' {v} hv := by
    change ∑ i, -v i = 0
    change ∑ i, v i = 0 at hv
    rw [sum_neg_distrib, hv, neg_zero]

theorem mem_evenSub {v : FrameVec} : v ∈ evenSub ↔ ∑ i, v i = 0 := Iff.rfl

@[expose] def evenZ : evenSub := ⟨frameZ, by rw [mem_evenSub]; decide⟩

theorem permVec_mem_evenSub (σ : Equiv.Perm (Fin 8)) {v : FrameVec} (hv : v ∈ evenSub) :
    permVec σ v ∈ evenSub := by
  rw [mem_evenSub] at hv ⊢
  rw [← hv]
  exact Equiv.sum_comp σ.symm v

@[expose] def evenSubEquiv : evenSub ≃+ (Fin 7 → ZMod 2) where
  toFun v i := (v : FrameVec) (Fin.castSucc i)
  invFun w := ⟨Fin.snoc (α := fun _ => ZMod 2) w (∑ i, w i), by
    rw [mem_evenSub, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    exact CharTwo.add_self_eq_zero _⟩
  left_inv v := by
    apply Subtype.ext
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]
      have h := v.2
      rw [mem_evenSub, Fin.sum_univ_castSucc] at h
      exact (eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq _)
    · simp only [Fin.snoc_castSucc]
  right_inv w := by
    funext i
    simp only [Fin.snoc_castSucc]
  map_add' v w := rfl

theorem card_addPerms_evenSub :
    Nat.card (addPerms evenSub) = 2 ^ 21 * 3 ^ 4 * 5 * 7 ^ 2 * 31 * 127 := by
  rw [card_addPerms_congr evenSubEquiv, card_addPerms_pi, card_GL_seven_two]

@[expose] def frameSupp (v : FrameVec) : Finset (Fin 8) := univ.filter fun i => v i ≠ 0

@[expose] def frameWt (v : FrameVec) : ℕ := (frameSupp v).card

theorem blockVec_frameSupp (v : FrameVec) : blockVec (frameSupp v) = v := by
  funext i
  simp only [blockVec, frameSupp, mem_filter, mem_univ, true_and]
  generalize v i = a
  revert a
  decide

theorem permVec_blockVec (σ : Equiv.Perm (Fin 8)) (s : Finset (Fin 8)) :
    permVec σ (blockVec s) = blockVec (s.image σ) := by
  funext i
  simp only [permVec, blockVec, mem_image]
  congr 1
  apply propext
  constructor
  · intro h
    exact ⟨σ.symm i, h, σ.apply_symm_apply i⟩
  · rintro ⟨a, ha, rfl⟩
    rwa [σ.symm_apply_apply]

theorem frameWt_frameDecode : ∀ n < 256, frameWt (frameDecode n) = framePop n := by
  decide +kernel

theorem frameWt_eq (v : FrameVec) : frameWt v = framePop (frameEncode v) := by
  rw [← frameWt_frameDecode _ (frameEncode_lt v), frameDecode_frameEncode]

theorem evenSub_iff_frameDecode : ∀ n < 256, (∑ i, frameDecode n i = 0 ↔ framePop n % 2 = 0) := by
  decide +kernel

theorem mem_evenSub_iff_frameWt (v : FrameVec) : v ∈ evenSub ↔ frameWt v % 2 = 0 := by
  rw [frameWt_eq, mem_evenSub, ← evenSub_iff_frameDecode _ (frameEncode_lt v),
    frameDecode_frameEncode]

theorem exists_alternating_permVec_eq {u v : FrameVec} (h : frameWt u = frameWt v) :
    ∃ σ ∈ alternatingGroup (Fin 8), permVec σ u = v := by
  have htr := Set.powersetCard.isPretransitive_alternatingGroup (α := Fin 8)
    (n := frameWt u) (by simp)
  obtain ⟨g, hg⟩ := htr.exists_smul_eq (⟨frameSupp u, rfl⟩ : Set.powersetCard (Fin 8) _)
    ⟨frameSupp v, h.symm⟩
  have hg' := congrArg (fun s : Set.powersetCard (Fin 8) (frameWt u) => (s : Finset (Fin 8))) hg
  refine ⟨g, g.2, ?_⟩
  have hg'' : (frameSupp u).image (g : Equiv.Perm (Fin 8)) = frameSupp v := hg'
  rw [← blockVec_frameSupp u, permVec_blockVec, hg'', blockVec_frameSupp]

theorem eq_of_permVec_evenSub {σ τ : Equiv.Perm (Fin 8)}
    (h : ∀ v ∈ evenSub, permVec σ v = permVec τ v) : σ = τ := by
  have h1 : ∀ v ∈ evenSub, permVec (τ⁻¹ * σ) v = v := fun v hv => by
    rw [permVec_mul, h v hv, permVec_inv_permVec]
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, (τ⁻¹ * σ) i ≠ i := by
    by_contra! hall
    exact hne (inv_mul_eq_one.mp (Equiv.ext hall)).symm
  set π := τ⁻¹ * σ
  obtain ⟨j, hji, hjπ⟩ : ∃ j, j ≠ i ∧ j ≠ π i := by
    by_contra! hall
    have hcard : (univ : Finset (Fin 8)) ⊆ {i, π i} := fun j _ => by
      by_cases hj : j = i
      · simp [hj]
      · simp [hall j hj]
    have := card_le_card hcard
    rw [card_univ, Fintype.card_fin] at this
    exact absurd (this.trans card_le_two) (by decide)
  have hv : frameE i + frameE j ∈ evenSub := by
    rw [mem_evenSub]
    simp only [Pi.add_apply, sum_add_distrib, frameE, sum_ite_eq', mem_univ, ite_true]
    decide
  have h2 := congrFun (h1 _ hv) (π i)
  rw [permVec_add, permVec_frameE, permVec_frameE] at h2
  simp only [Pi.add_apply, frameE, ite_true, hi, hjπ.symm, ite_false,
    π.injective.ne hji.symm] at h2
  exact absurd h2 (by decide)

theorem frameWt_frameZ : frameWt frameZ = 8 := by
  rw [frameWt_eq, frameEncode_frameZ]
  decide

theorem frameWt_eq_zero_iff (v : FrameVec) : frameWt v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h' : frameSupp v = ∅ := card_eq_zero.mp h
    rw [← blockVec_frameSupp v, h']
    funext i
    simp [blockVec]
  · rintro rfl
    simp [frameWt, frameSupp]

theorem frameWt_le (v : FrameVec) : frameWt v ≤ 8 := by
  have := card_le_univ (frameSupp v)
  rwa [Fintype.card_fin] at this

theorem frameWt_eq_eight_iff (v : FrameVec) : frameWt v = 8 ↔ v = frameZ := by
  have key : ∀ m < 256, framePop m = 8 ↔ m = 255 := by decide +kernel
  rw [frameWt_eq, key _ (frameEncode_lt v), ← frameEncode_frameZ]
  exact frameEncode_injective.eq_iff

theorem prime_127 : Nat.Prime 127 := by norm_num

theorem dvd_20160_mod_127 : ∀ d, d ∣ 20160 → d % 127 = 1 → d = 1 := by
  have key : ∀ d ∈ Nat.divisors 20160, d % 127 = 1 → d = 1 := by decide +kernel
  intro d hd hmod
  exact key d (Nat.mem_divisors.mpr ⟨hd, by decide⟩) hmod

set_option maxRecDepth 100000 in
theorem even_orbit_sizes : ∀ K ∈ ({2, 4, 6} : Finset ℕ).powerset, K = ∅ ∨ K = {2, 4, 6} ∨
    ¬ ((range 256).filter fun n => framePop n = 8 ∨ framePop n ∈ K).card ∣
      2 ^ 21 * 3 ^ 4 * 5 * 7 ^ 2 * 31 * 127 := by
  decide +kernel

theorem even_orbit_full :
    ((range 256).filter fun n => framePop n = 8 ∨ framePop n ∈ ({2, 4, 6} : Finset ℕ)).card =
      127 := by
  decide +kernel

@[expose] def evenPerm (σ : Equiv.Perm (Fin 8)) : Equiv.Perm evenSub where
  toFun v := ⟨permVec σ v, permVec_mem_evenSub σ v.2⟩
  invFun v := ⟨permVec σ⁻¹ v, permVec_mem_evenSub σ⁻¹ v.2⟩
  left_inv v := Subtype.ext (permVec_inv_permVec σ v)
  right_inv v := Subtype.ext (permVec_permVec_inv σ v)

theorem card_alternatingGroup_fin_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 8)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 8), Fintype.card_fin] at h
  have : Nat.factorial 8 = 40320 := by decide
  omega

theorem normalizer_fixes_evenZ_of_alternating {N : Type*} [Group N] [MulAction N evenSub]
    (hadd : ∀ (n : N) (x y : evenSub), n • (x + y) = n • x + n • y)
    (hup : ∀ n : N, n • evenZ = evenZ → ∃ σ ∈ alternatingGroup (Fin 8),
      ∀ v : evenSub, ((n • v : evenSub) : FrameVec) = permVec σ v)
    (hlow : ∀ σ ∈ alternatingGroup (Fin 8), ∃ n : N,
      ∀ v : evenSub, ((n • v : evenSub) : FrameVec) = permVec σ v) :
    ∀ n : N, n • evenZ = evenZ := by
  classical
  by_contra! hmove
  obtain ⟨n₀, hn₀⟩ := hmove
  set Y : Finset FrameVec := univ.filter fun v => ∃ n : N, ((n • evenZ : evenSub) : FrameVec) = v
  have hYz : frameZ ∈ Y := by simp [Y]; exact ⟨1, by rw [one_smul]; rfl⟩
  have hY0 : ∀ v ∈ Y, v ≠ 0 := by
    intro v hv h0
    simp only [Y, mem_filter, mem_univ, true_and] at hv
    obtain ⟨n, hn⟩ := hv
    have h : n • evenZ = 0 := Subtype.ext (by rw [hn, h0]; rfl)
    have h' := congrArg (n⁻¹ • ·) h
    simp only [inv_smul_smul, smul_zero_of_hadd hadd] at h'
    exact frameZ_ne_zero (congrArg Subtype.val h')
  have hYeven : ∀ v ∈ Y, v ∈ evenSub := by
    intro v hv
    simp only [Y, mem_filter, mem_univ, true_and] at hv
    obtain ⟨n, rfl⟩ := hv
    exact (n • evenZ).2
  have hYperm : ∀ σ ∈ alternatingGroup (Fin 8), ∀ v ∈ Y, permVec σ v ∈ Y := by
    intro σ hσ v hv
    simp only [Y, mem_filter, mem_univ, true_and] at hv ⊢
    obtain ⟨n, rfl⟩ := hv
    obtain ⟨m, hm⟩ := hlow σ hσ
    exact ⟨m * n, by rw [mul_smul, hm]⟩
  have hYwt : ∀ u ∈ Y, ∀ w, frameWt w = frameWt u → w ∈ Y := by
    intro u hu w hw
    obtain ⟨σ, hσ, hσu⟩ := exists_alternating_permVec_eq hw.symm
    rw [← hσu]
    exact hYperm σ hσ u hu
  set K : Finset ℕ := ({2, 4, 6} : Finset ℕ).filter fun k => ∃ u ∈ Y, frameWt u = k
  have hYK : Y = univ.filter fun v => frameWt v = 8 ∨ frameWt v ∈ K := by
    ext v
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hv
      have hev := (mem_evenSub_iff_frameWt v).mp (hYeven v hv)
      have hne : frameWt v ≠ 0 := fun h0 => hY0 v hv ((frameWt_eq_zero_iff v).mp h0)
      have hle := frameWt_le v
      by_cases h8 : frameWt v = 8
      · exact Or.inl h8
      · right
        simp only [K, mem_filter, mem_insert, mem_singleton]
        refine ⟨by omega, v, hv, rfl⟩
    · rintro (h8 | hK)
      · exact hYwt _ hYz v (h8.trans frameWt_frameZ.symm)
      · simp only [K, mem_filter] at hK
        obtain ⟨-, u, hu, huk⟩ := hK
        exact hYwt u hu v (huk ▸ rfl)
  have hYcard : Y.card = ((range 256).filter fun n => framePop n = 8 ∨ framePop n ∈ K).card := by
    rw [hYK, card_filter_frameVec]
    refine congrArg card (filter_congr fun n hn => ?_)
    rw [frameWt_eq, frameEncode_frameDecode n (mem_range.mp hn)]
  have horbcard : Nat.card (MulAction.orbit N evenZ) = Y.card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨(x.1 : FrameVec), ?_⟩) ⟨?_, ?_⟩)
    · obtain ⟨_, n, rfl⟩ := x
      simp only [Y, mem_filter, mem_univ, true_and]
      exact ⟨n, rfl⟩
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext h)
    · rintro ⟨v, hv⟩
      simp only [Y, mem_filter, mem_univ, true_and] at hv
      obtain ⟨n, rfl⟩ := hv
      exact ⟨⟨n • evenZ, n, rfl⟩, rfl⟩
  have hdvd : Y.card ∣ 2 ^ 21 * 3 ^ 4 * 5 * 7 ^ 2 * 31 * 127 := by
    rw [← horbcard, ← card_addPerms_evenSub]
    exact card_orbit_dvd_card_addPerms hadd evenZ
  have hKsub : K ∈ ({2, 4, 6} : Finset ℕ).powerset := mem_powerset.mpr (filter_subset _ _)
  rcases even_orbit_sizes K hKsub with hK | hK | hK
  ·
    apply hn₀
    have hmem : ((n₀ • evenZ : evenSub) : FrameVec) ∈ Y := by
      simp only [Y, mem_filter, mem_univ, true_and]
      exact ⟨n₀, rfl⟩
    rw [hYK, hK] at hmem
    simp only [mem_filter, mem_univ, true_and, notMem_empty, or_false] at hmem
    exact Subtype.ext ((frameWt_eq_eight_iff _).mp hmem)
  ·
    rw [hK] at hYcard
    rw [even_orbit_full] at hYcard
    set φ := MulAction.toPermHom N evenSub
    set Γ := φ.range
    have horb : MulAction.orbit N evenZ = MulAction.orbit Γ evenZ := by
      ext x
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨⟨φ n, n, rfl⟩, rfl⟩
      · rintro ⟨⟨_, n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
    have hΩ : Nat.card (MulAction.orbit Γ evenZ) = 127 := by
      rw [← horb, horbcard, hYcard]
    have hall : ∀ v : evenSub, v ≠ 0 → v ∈ MulAction.orbit Γ evenZ := by
      intro v hv
      rw [← horb]
      have hvY : (v : FrameVec) ∈ Y := by
        rw [hYK, hK]
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
        have hev := (mem_evenSub_iff_frameWt v).mp v.2
        have hne : frameWt v ≠ 0 := fun h0 =>
          hv (Subtype.ext ((frameWt_eq_zero_iff (v : FrameVec)).mp h0))
        have hle := frameWt_le (v : FrameVec)
        omega
      simp only [Y, mem_filter, mem_univ, true_and] at hvY
      obtain ⟨n, hn⟩ := hvY
      exact ⟨n, Subtype.ext hn⟩
    have hfaith : ∀ k : Γ, (∀ x : MulAction.orbit Γ evenZ, k • x = x) → k = 1 := by
      rintro ⟨_, n, rfl⟩ hk
      apply Subtype.ext
      apply Equiv.ext
      intro v
      by_cases hv : v = 0
      · rw [hv]
        exact smul_zero_of_hadd hadd n
      · have h := hk ⟨v, hall v hv⟩
        exact congrArg Subtype.val h
    have htrans : ∀ x y : MulAction.orbit Γ evenZ, ∃ k : Γ, k • x = y :=
      fun x y => MulAction.exists_smul_eq Γ x y
    set ω : MulAction.orbit Γ evenZ := ⟨evenZ, MulAction.mem_orbit_self evenZ⟩
    have hstab : Nat.card (MulAction.stabilizer Γ ω) = 20160 := by
      rw [← card_alternatingGroup_fin_eight]
      symm
      have hmemΓ : ∀ σ ∈ alternatingGroup (Fin 8), evenPerm σ ∈ Γ := by
        intro σ hσ
        obtain ⟨n, hn⟩ := hlow σ hσ
        exact ⟨n, Equiv.ext fun v => Subtype.ext (hn v)⟩
      refine Nat.card_eq_of_bijective
        (fun σ => ⟨⟨evenPerm σ, hmemΓ σ σ.2⟩, Subtype.ext (Subtype.ext (permVec_frameZ σ))⟩)
        ⟨?_, ?_⟩
      · intro σ τ h
        have h' : evenPerm σ = evenPerm τ := congrArg (fun x => x.1.1) h
        apply Subtype.ext
        apply eq_of_permVec_evenSub
        intro v hv
        exact congrArg (fun π : Equiv.Perm evenSub => ((π ⟨v, hv⟩ : evenSub) : FrameVec)) h'
      · rintro ⟨⟨_, n, rfl⟩, hn⟩
        have hnz : n • evenZ = evenZ := congrArg Subtype.val hn
        obtain ⟨σ, hσ, hσn⟩ := hup n hnz
        refine ⟨⟨σ, hσ⟩, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        exact Equiv.ext fun v => Subtype.ext (hσn v).symm
    have hlt := card_stabilizer_lt_of_prime_degree hfaith htrans prime_127 hΩ ω
      (by rw [hstab]; omega) (by rw [hstab]; exact dvd_20160_mod_127)
    rw [hstab] at hlt
    omega
  · exact hK (hYcard ▸ hdvd)

@[expose] def evenRealized (N : Type*) [Group N] [MulAction N evenSub] :
    Subgroup (Equiv.Perm (Fin 8)) where
  carrier := {σ | ∃ n : N, ∀ v : evenSub, ((n • v : evenSub) : FrameVec) = permVec σ v}
  mul_mem' := by
    rintro σ τ ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n * m, fun v => ?_⟩
    rw [mul_smul, hn, hm, permVec_mul]
  one_mem' := ⟨1, fun v => by rw [one_smul, permVec_one]⟩
  inv_mem' := by
    rintro σ ⟨n, hn⟩
    refine ⟨n⁻¹, fun v => ?_⟩
    set w : evenSub := ⟨permVec σ⁻¹ v, permVec_mem_evenSub σ⁻¹ v.2⟩
    have h : n • w = v := Subtype.ext (by rw [hn, permVec_permVec_inv])
    calc ((n⁻¹ • v : evenSub) : FrameVec) = ((n⁻¹ • n • w : evenSub) : FrameVec) := by rw [h]
      _ = permVec σ⁻¹ v := by rw [inv_smul_smul]

theorem frameClass_of_even : ∀ n < 256, framePop n % 2 = 0 →
    frameClass n = 0 ∨ frameClass n = 2 ∨ frameClass n = 4 ∨ frameClass n = 5 ∨
      frameClass n = 7 ∨ frameClass n = 9 := by
  decide +kernel

theorem frameClass_two : ∀ n < 256, frameClass n = 2 →
    ∃ i j : Fin 8, i ≠ j ∧ frameDecode n = frameE i + frameE j := by
  decide +kernel

theorem frameClass_seven : ∀ n < 256, frameClass n = 7 →
    ∃ i j : Fin 8, i ≠ j ∧ frameDecode n = frameZ + frameE i + frameE j := by
  decide +kernel

theorem card_frameClass_five_nine :
    ((range 256).filter fun n => frameClass n = 5 ∨ frameClass n = 9).card = 57 := by
  decide +kernel

theorem normalizer_fixes_evenZ_of_frame {N : Type*} [Group N] [MulAction N evenSub]
    (hadd : ∀ (n : N) (x y : evenSub), n • (x + y) = n • x + n • y)
    (hgen : ∀ σ ∈ frameGens, ∃ n : N,
      ∀ v : evenSub, ((n • v : evenSub) : FrameVec) = permVec σ v)
    (htwo : ∀ (n : N) (i j : Fin 8), i ≠ j →
      ((n • evenZ : evenSub) : FrameVec) ≠ frameE i + frameE j)
    (hsix : ∀ (n : N) (i j : Fin 8), i ≠ j →
      ((n • evenZ : evenSub) : FrameVec) ≠ frameZ + frameE i + frameE j)
    (hplane : ∀ n : N, ∀ B ∈ frameBlocks, ((n • evenZ : evenSub) : FrameVec) ≠ blockVec B) :
    ∀ n : N, n • evenZ = evenZ := by
  classical
  by_contra! hmove
  obtain ⟨n₀, hn₀⟩ := hmove
  set Y : Set FrameVec := {v | ∃ n : N, ((n • evenZ : evenSub) : FrameVec) = v}
  have hYcl : ∀ σ ∈ Subgroup.closure frameGens, ∀ v ∈ Y, permVec σ v ∈ Y := by
    intro σ hσ v hv
    obtain ⟨m, hm⟩ := ((Subgroup.closure_le (evenRealized N)).2 hgen) hσ
    obtain ⟨n, rfl⟩ := hv
    exact ⟨m * n, by rw [mul_smul, hm]⟩
  have hcls : ∀ v ∈ Y, frameCls v = 5 ∨ frameCls v = 9 := by
    rintro _ ⟨n, rfl⟩
    set v := ((n • evenZ : evenSub) : FrameVec)
    have hlt := frameEncode_lt v
    have hev : framePop (frameEncode v) % 2 = 0 := by
      rw [← frameWt_eq, ← mem_evenSub_iff_frameWt]
      exact (n • evenZ).2
    have h0 : frameCls v ≠ 0 := by
      rw [ne_eq, frameCls_eq_zero_iff]
      intro h
      have h' := congrArg (n⁻¹ • ·) (Subtype.ext h : n • evenZ = 0)
      simp only [inv_smul_smul, smul_zero_of_hadd hadd] at h'
      exact frameZ_ne_zero (congrArg Subtype.val h')
    have h2 : frameCls v ≠ 2 := fun h => by
      obtain ⟨i, j, hij, hv⟩ := frameClass_two _ hlt h
      rw [frameDecode_frameEncode] at hv
      exact htwo n i j hij hv
    have h7 : frameCls v ≠ 7 := fun h => by
      obtain ⟨i, j, hij, hv⟩ := frameClass_seven _ hlt h
      rw [frameDecode_frameEncode] at hv
      exact hsix n i j hij hv
    have h4 : frameCls v ≠ 4 := fun h => by
      obtain ⟨B, hB, hv⟩ := (frameCls_eq_four_iff v).mp h
      exact hplane n B hB hv
    rcases frameClass_of_even _ hlt hev with h | h | h | h | h | h
    · exact absurd h h0
    · exact absurd h h2
    · exact absurd h h4
    · exact Or.inl h
    · exact absurd h h7
    · exact Or.inr h
  have hu : ((n₀ • evenZ : evenSub) : FrameVec) ∈ Y := ⟨n₀, rfl⟩
  have hu5 : frameCls ((n₀ • evenZ : evenSub) : FrameVec) = 5 := by
    rcases hcls _ hu with h | h
    · exact h
    · exact absurd (Subtype.ext ((frameCls_eq_nine_iff _).mp h)) hn₀
  have hYeq : ∀ v, v ∈ Y ↔ frameCls v = 5 ∨ frameCls v = 9 := by
    intro v
    refine ⟨hcls v, ?_⟩
    rintro (h | h)
    · exact mem_of_frameCls_eq hYcl (hu5.trans h.symm) (by rw [hu5]; decide)
        (by rw [hu5]; decide) (by rw [hu5]; decide) hu
    · rw [(frameCls_eq_nine_iff v).mp h]
      exact ⟨1, by rw [one_smul]; rfl⟩
  have hcard : Nat.card (MulAction.orbit N evenZ) = 57 := by
    rw [← card_frameClass_five_nine]
    have h1 : ((range 256).filter fun n => frameClass n = 5 ∨ frameClass n = 9).card =
        (univ.filter fun v : FrameVec => frameCls v = 5 ∨ frameCls v = 9).card := by
      rw [card_filter_frameVec]
      refine congrArg card (filter_congr fun n hn => ?_)
      rw [frameCls_frameDecode (mem_range.mp hn)]
    rw [h1, ← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨(x.1 : FrameVec), ?_⟩) ⟨?_, ?_⟩)
    · obtain ⟨_, n, rfl⟩ := x
      simp only [mem_filter, mem_univ, true_and]
      exact (hYeq _).mp ⟨n, rfl⟩
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext h)
    · rintro ⟨v, hv⟩
      simp only [mem_filter, mem_univ, true_and] at hv
      obtain ⟨n, rfl⟩ := (hYeq v).mpr hv
      exact ⟨⟨n • evenZ, n, rfl⟩, rfl⟩
  have hdvd := card_orbit_dvd_card_addPerms hadd evenZ
  rw [hcard, card_addPerms_evenSub] at hdvd
  exact absurd hdvd (by decide)

end CFSG.EvenSmallLie.OmegaEight

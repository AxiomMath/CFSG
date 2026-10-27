module

public import CFSG.HardMathSupport.Solomon.Coordinator.LBID4RankLast
public import CFSG.HardMathSupport.Solomon.Coordinator.LBID4RankCW

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LBID4

open QuadraticMap Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section Nonsplit

variable [FiniteDimensional K V] (h3 : (3 : K) ≠ 0) (F0 F1 F2 : EFrame Q) (h01 : F0.Perp F1)
  (h02 : F0.Perp F2) (h12 : F1.Perp F2)

include h3 h01 h02 h12 in
theorem exists_frame_last_nonsplit [Finite K] (hB : (polarBilin Q).Nondegenerate)
    (hdim : finrank K V = 8) {W : Submodule K V} (hW : ∀ w ∈ W, Q w = 0) (hWdim : finrank K W = 4)
    (hω : ∀ y : K, y ^ 2 + y + 1 ≠ 0) (hR : NDeg Q (lastPlane F0 F1 F2))
    (hM'dim : finrank K ↥(F0.orthSub ⊓ F1.orthSub) = 4)
    (hRdim : finrank K ↥(lastPlane F0 F1 F2) = 2) :
    ∃ F : EFrame Q, F.b ∈ lastPlane F0 F1 F2 ∧ F.b' ∈ lastPlane F0 F1 F2 := by
  classical
  obtain ⟨t, ht0, htQ⟩ := exists_isotropic_three Q ![F0.b, F0.b', F1.b]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at htQ
  set a0 := t 0
  set a1 := t 1
  set a2 := t 2
  have hu_eq : a0 • F0.b + a1 • F0.b' + a2 • F1.b =
      (a0 • F0.b + a1 • F0.b') + (a2 • F1.b + (0 : K) • F1.b') := by
    rw [zero_smul, add_zero]
  rw [hu_eq, EFrame.q_two h01] at htQ
  have hN : F0.c * (a0 ^ 2 - a0 * a1 + a1 ^ 2) + F1.c * a2 ^ 2 = 0 := by
    linear_combination htQ
  have ha2 : a2 ≠ 0 := by
    intro h
    rw [h] at hN
    have h0 : a0 ^ 2 - a0 * a1 + a1 ^ 2 = 0 := by
      have : F0.c * (a0 ^ 2 - a0 * a1 + a1 ^ 2) = 0 := by linear_combination hN
      exact (mul_eq_zero.mp this).resolve_left F0.c_ne
    obtain ⟨h0', h1'⟩ := EFrame.eq_zero_of_norm_eq_zero hω h0
    apply ht0
    funext i
    fin_cases i
    · exact h0'
    · exact h1'
    · exact h
  set u := (a0 • F0.b + a1 • F0.b') + (a2 • F1.b + (0 : K) • F1.b')
  set u' := ((-a1) • F0.b + (a0 - a1) • F0.b') + ((-a2) • F1.b + (-a2) • F1.b')
  have hQu : Q u = 0 := by rw [EFrame.q_two h01]; linear_combination hN
  have hQu' : Q u' = 0 := by rw [EFrame.q_two h01]; linear_combination hN
  have huu' : polar Q u u' = 0 := by rw [EFrame.polar_two h01]; linear_combination -hN
  have huu : polar Q u u = 0 := by rw [polar_self_eq, hQu, mul_zero]
  have hu'u' : polar Q u' u' = 0 := by rw [polar_self_eq, hQu', mul_zero]
  let v : Fin 2 → V := ![u, u']
  set U := Submodule.span K (Set.range v)
  have hU : ∀ x ∈ U, Q x = 0 := by
    refine q_eq_zero_of_mem_span ?_ ?_
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hQu
      · exact hQu'
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      fin_cases i <;> fin_cases j
      · exact huu
      · exact huu'
      · rw [polar_comm]; exact huu'
      · exact hu'u'
  have hpb1 : ∀ α β γ δ : K, polar Q ((α • F0.b + β • F0.b') + (γ • F1.b + δ • F1.b')) F1.b =
      F1.c * (2 * γ - δ) := by
    intro α β γ δ
    rw [polar_add_left, F0.polar_comb_of_orth h01.1, F1.polar_comb_b, zero_add]
  have hpb1' : ∀ α β γ δ : K, polar Q ((α • F0.b + β • F0.b') + (γ • F1.b + δ • F1.b')) F1.b' =
      F1.c * (2 * δ - γ) := by
    intro α β γ δ
    rw [polar_add_left, F0.polar_comb_of_orth h01.2, F1.polar_comb_b', zero_add]
  have hli : LinearIndependent K v := by
    rw [LinearIndependent.pair_iff]
    intro x y hxy
    have e1 := congrArg (pol Q F1.b) hxy
    have e2 := congrArg (pol Q F1.b') hxy
    simp only [map_add, map_smul, pol_apply, map_zero, smul_eq_mul] at e1 e2
    rw [hpb1, hpb1] at e1
    rw [hpb1', hpb1'] at e2
    have hc := mul_ne_zero F1.c_ne ha2
    have hx : F1.c * a2 * (3 * x) = 0 := by linear_combination e1 - e2
    have hx' : x = 0 := by
      rcases mul_eq_zero.mp hx with h | h
      · exact absurd h hc
      · exact (mul_eq_zero.mp h).resolve_left h3
    refine ⟨hx', ?_⟩
    rw [hx'] at e2
    have : F1.c * a2 * y = 0 := by linear_combination -e2
    exact (mul_eq_zero.mp this).resolve_left hc
  have hUdim : finrank K U = 2 := by
    rw [finrank_span_eq_card hli]
    rfl
  have hfix2 : ∀ α β γ δ : K, F0.proj ((α • F0.b + β • F0.b') + (γ • F1.b + δ • F1.b')) +
      F1.proj ((α • F0.b + β • F0.b') + (γ • F1.b + δ • F1.b')) =
        (α • F0.b + β • F0.b') + (γ • F1.b + δ • F1.b') := by
    intro α β γ δ
    rw [map_add F0.proj (α • F0.b + β • F0.b') (γ • F1.b + δ • F1.b'),
      map_add F1.proj (α • F0.b + β • F0.b') (γ • F1.b + δ • F1.b'), F0.proj_comb_self h3,
      EFrame.proj_comb_of_perp h01, EFrame.proj_comb_of_perp h01.symm, F1.proj_comb_self h3]
    abel
  have hfix : ∀ x ∈ U, F0.proj x + F1.proj x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      fin_cases i
      · exact hfix2 _ _ _ _
      · exact hfix2 _ _ _ _
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add, map_add,
        show F0.proj a + F0.proj b + (F1.proj a + F1.proj b) =
          (F0.proj a + F1.proj a) + (F0.proj b + F1.proj b) by abel, ha, hb]
    | smul c a _ ha => rw [map_smul, map_smul, ← smul_add, ha]
  set M' := F0.orthSub ⊓ F1.orthSub
  have hM' : ∀ m, m ∈ M' ↔ F0.Orth m ∧ F1.Orth m := fun m => by
    simp only [M', Submodule.mem_inf, EFrame.mem_orthSub]
  have hUM' : U ⊓ M' = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hxU, hxM⟩
    obtain ⟨ho0, ho1⟩ := (hM' x).mp hxM
    rw [← hfix x hxU, F0.proj_of_orth ho0, F1.proj_of_orth ho1, add_zero]
  have hM'orth : M' ≤ orth Q U := by
    intro m hm
    obtain ⟨ho0, ho1⟩ := (hM' m).mp hm
    have hker : U ≤ LinearMap.ker (pol Q m) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, pol_apply]
      fin_cases i <;>
        simp only [v, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        rw [polar_add_left, F0.polar_comb_of_orth ho0, F1.polar_comb_of_orth ho1, add_zero]
    rw [mem_orth]
    intro n hn
    have := hker hn
    rwa [LinearMap.mem_ker, pol_apply] at this
  have hsup : U ⊔ M' = orth Q U := by
    apply Submodule.eq_of_le_of_finrank_eq (sup_le (le_orth_of_singular hU) hM'orth)
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U M'
    rw [hUM', finrank_bot, add_zero, hUdim, hM'dim] at h1
    rw [finrank_orth hB, hdim, hUdim, h1]
  have hA : finrank K ↥(W ⊓ orth Q U) + 2 = finrank K ↥(W ⊓ U) + 4 := by
    have := finrank_inf_orth_add (U := U) hB hW (by rw [hWdim, hdim])
    rw [hUdim, hWdim] at this
    exact this
  set N := W ⊓ orth Q U
  let π : V →ₗ[K] V := LinearMap.id - F0.proj - F1.proj
  have hπ : ∀ w ∈ N, ∃ u0 ∈ U, π w ∈ M' ∧ π w = w - u0 := by
    intro w hw
    have hwU : w ∈ U ⊔ M' := by rw [hsup]; exact hw.2
    obtain ⟨u0, hu0, m, hm, rfl⟩ := Submodule.mem_sup.mp hwU
    obtain ⟨ho0, ho1⟩ := (hM' m).mp hm
    have hπm : π (u0 + m) = m := by
      simp only [π, LinearMap.sub_apply, LinearMap.id_apply, map_add,
        F0.proj_of_orth ho0, F1.proj_of_orth ho1]
      rw [sub_zero, sub_zero, sub_sub, hfix u0 hu0, sub_self, zero_add]
    refine ⟨u0, hu0, ?_, ?_⟩
    · rw [hπm]; exact hm
    · rw [hπm]; abel
  set S := N.map π
  have hSM' : S ≤ M' := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨u0, -, h, -⟩ := hπ w hw
    exact h
  have hSQ : ∀ y ∈ S, Q y = 0 := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨u0, hu0, -, h⟩ := hπ w hw
    have hwu0 : polar Q w u0 = 0 := by
      rw [polar_comm]
      exact mem_orth.mp hw.2 u0 hu0
    rw [h, q_sub, hW w hw.1, hU u0 hu0, hwu0]
    ring
  have hker : N ⊓ LinearMap.ker π ≤ W ⊓ U := by
    rintro w ⟨hwN, hwk⟩
    obtain ⟨u0, hu0, -, h⟩ := hπ w hwN
    have hwk' : π w = 0 := hwk
    rw [hwk', eq_comm, sub_eq_zero] at h
    exact ⟨hwN.1, h ▸ hu0⟩
  have hS2 : 2 ≤ finrank K S := by
    have h1 : finrank K S + finrank K ↥(N ⊓ LinearMap.ker π) = finrank K N :=
      finrank_map_add_finrank_inf_ker π N
    have h2 := Submodule.finrank_mono hker
    omega
  let ρ : V →ₗ[K] V := LinearMap.id - F2.proj
  have hρR : ∀ y ∈ M', ρ y ∈ lastPlane F0 F1 F2 := by
    intro y hy
    obtain ⟨ho0, ho1⟩ := (hM' y).mp hy
    rw [mem_lastPlane]
    exact ⟨ho0.sub (F0.orth_proj_of_perp h02 y), ho1.sub (F1.orth_proj_of_perp h12 y),
      F2.orth_sub_proj h3 y⟩
  have hSρ : S ⊓ LinearMap.ker ρ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro y ⟨hyS, hyk⟩
    have hy : y = F2.proj y := by
      have : y - F2.proj y = 0 := hyk
      exact sub_eq_zero.mp this
    have hQy := hSQ y hyS
    rw [hy, EFrame.proj_apply, EFrame.q_comb] at hQy
    obtain ⟨hs, ht⟩ := EFrame.eq_zero_of_norm_eq_zero hω
      ((mul_eq_zero.mp hQy).resolve_left F2.c_ne)
    rw [hy, EFrame.proj_apply, hs, ht, zero_smul, zero_smul, add_zero]
  have hSρdim := finrank_map_add_finrank_inf_ker ρ S
  rw [hSρ, finrank_bot, add_zero] at hSρdim
  have hSρR : S.map ρ ≤ lastPlane F0 F1 F2 := by
    rintro _ ⟨y, hy, rfl⟩
    exact hρR y (hSM' hy)
  have hSdim : finrank K S = 2 := by
    have := Submodule.finrank_mono hSρR
    omega
  have hSρeq : S.map ρ = lastPlane F0 F1 F2 :=
    Submodule.eq_of_le_of_finrank_eq hSρR (by rw [hSρdim, hSdim, hRdim])
  have hpolS : ∀ y ∈ S, ∀ y' ∈ S, polar Q y y' = 0 := fun y hy y' hy' =>
    polar_eq_zero_of_singular' hSQ hy hy'
  have hSR : ∀ y ∈ S, y ∈ lastPlane F0 F1 F2 → y = 0 := by
    intro y hyS hyR
    refine hR y hyR fun r' hr' => ?_
    rw [← hSρeq] at hr'
    obtain ⟨y', hy', rfl⟩ := hr'
    have ho2 : F2.Orth y := ((mem_lastPlane F0 F1 F2).mp hyR).2.2
    have hp : polar Q y (F2.proj y') = 0 := by
      rw [polar_comm, EFrame.proj_apply]
      exact F2.polar_comb_of_orth ho2 _ _
    simp only [ρ, LinearMap.sub_apply, LinearMap.id_apply]
    rw [polar_sub_right, hpolS y hyS y' hy', hp, sub_zero]
  have hSproj : S ⊓ LinearMap.ker F2.proj = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro y ⟨hyS, hyk⟩
    have hyk' : F2.proj y = 0 := hyk
    have ho2 := F2.orth_of_proj_eq_zero h3 hyk'
    obtain ⟨ho0, ho1⟩ := (hM' y).mp (hSM' hyS)
    exact hSR y hyS ((mem_lastPlane F0 F1 F2).mpr ⟨ho0, ho1, ho2⟩)
  have hSpdim := finrank_map_add_finrank_inf_ker F2.proj S
  rw [hSproj, finrank_bot, add_zero] at hSpdim
  have hSpP : S.map F2.proj ≤ F2.plane := by
    rintro _ ⟨y, -, rfl⟩
    exact F2.proj_mem_plane y
  have hSpeq : S.map F2.proj = F2.plane :=
    Submodule.eq_of_le_of_finrank_eq hSpP (by rw [hSpdim, hSdim, F2.finrank_plane h3])
  obtain ⟨y1, hy1S, hy1⟩ : F2.b ∈ S.map F2.proj := by rw [hSpeq]; exact F2.b_mem_plane
  obtain ⟨y2, hy2S, hy2⟩ : F2.b' ∈ S.map F2.proj := by rw [hSpeq]; exact F2.b'_mem_plane
  have hr1R : y1 - F2.b ∈ lastPlane F0 F1 F2 := by
    have := hρR y1 (hSM' hy1S)
    simpa [ρ, hy1] using this
  have hr2R : y2 - F2.b' ∈ lastPlane F0 F1 F2 := by
    have := hρR y2 (hSM' hy2S)
    simpa [ρ, hy2] using this
  have ho1 : F2.Orth (y1 - F2.b) := ((mem_lastPlane F0 F1 F2).mp hr1R).2.2
  have ho2 : F2.Orth (y2 - F2.b') := ((mem_lastPlane F0 F1 F2).mp hr2R).2.2
  have hQy1 := hSQ y1 hy1S
  have hQy2 := hSQ y2 hy2S
  have hpy := hpolS y1 hy1S y2 hy2S
  have ey1 : y1 = F2.b + (y1 - F2.b) := by abel
  have ey2 : y2 = F2.b' + (y2 - F2.b') := by abel
  rw [ey1, q_add, F2.q_b, polar_comm, ho1.1] at hQy1
  rw [ey2, q_add, F2.q_b', polar_comm, ho2.2] at hQy2
  rw [ey1, ey2, polar_add_left, polar_add_right, polar_add_right, F2.polar_bb',
    polar_comm _ F2.b (y2 - F2.b'), ho2.1] at hpy
  refine ⟨⟨y1 - F2.b, y2 - F2.b', -F2.c, neg_ne_zero.mpr F2.c_ne, ?_, ?_, ?_⟩, hr1R, hr2R⟩
  · linear_combination hQy1
  · linear_combination hQy2
  · have h4 : polar Q (y1 - F2.b) F2.b' = 0 := ho1.2
    rw [h4] at hpy
    linear_combination hpy

end Nonsplit

theorem exists_frame_last [Finite K] [FiniteDimensional K V] (h3 : (3 : K) ≠ 0)
    (hB : (polarBilin Q).Nondegenerate) (hdim : finrank K V = 8) {W : Submodule K V}
    (hW : ∀ w ∈ W, Q w = 0) (hWdim : finrank K W = 4) (F0 F1 F2 : EFrame Q) (h01 : F0.Perp F1)
    (h02 : F0.Perp F2) (h12 : F1.Perp F2) (hR : NDeg Q (lastPlane F0 F1 F2))
    (hM'dim : finrank K ↥(F0.orthSub ⊓ F1.orthSub) = 4)
    (hRdim : finrank K ↥(lastPlane F0 F1 F2) = 2) :
    ∃ F : EFrame Q, F.b ∈ lastPlane F0 F1 F2 ∧ F.b' ∈ lastPlane F0 F1 F2 := by
  by_cases hω : ∃ ω : K, ω ^ 2 + ω + 1 = 0
  · exact exists_frame_last_split h3 F0 F1 F2 h01 h02 h12 hB hdim hW hWdim hω hR
  · push Not at hω
    exact exists_frame_last_nonsplit h3 F0 F1 F2 h01 h02 h12 hB hdim hW hWdim hω hR hM'dim hRdim

end CFSG.HardMathSupport.Solomon.Coordinator.LBID4

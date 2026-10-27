module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222OrthPair
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222SpBC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofTypeAC

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open scoped Matrix

section Linear

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {Q : QuadraticForm K (ι → K)}

omit [DecidableEq ι] in
theorem exists_polar_perp_not_mem_span {m : ℕ} (hm : m + m < Fintype.card ι) (g : Fin m → ι → K) :
    ∃ a, (∀ i, Q.polarBilin a (g i) = 0) ∧ a ∉ Submodule.span K (Set.range g) := by
  by_contra! h
  set f : (ι → K) →ₗ[K] (Fin m → K) := LinearMap.pi fun i => Q.polarBilin.flip (g i) with hf
  have hle : LinearMap.ker f ≤ Submodule.span K (Set.range g) := fun a ha => h a fun i => by
    have h1 := congrFun (LinearMap.mem_ker.mp ha) i
    simpa [hf] using h1
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : finrank K (LinearMap.range f) ≤ m := by
    simpa using Submodule.finrank_le (LinearMap.range f)
  have h3 := Submodule.finrank_mono hle
  have h4 := finrank_range_le_card (R := K) g
  rw [Fintype.card_fin] at h4
  change finrank K (Submodule.span K (Set.range g)) ≤ m at h4
  rw [Module.finrank_fintype_fun_eq_card] at h1
  omega

omit [DecidableEq ι] in
theorem exists_good_vectors_typeBC {N : Matrix ι ι K}
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v)) {z y₀ : ι → K}
    (hy₀ : N *ᵥ y₀ = z) (hz0 : z ≠ 0) (hrk : 3 ≤ N.rank) :
    ∃ x y : ι → K, Q.polarBilin x z = 0 ∧ Q.polarBilin y z = 0 ∧ (∀ c : K, N *ᵥ x ≠ c • z) ∧
      (∀ c : K, N *ᵥ y ≠ c • z) ∧ ∀ c : K, N *ᵥ y ≠ c • (N *ᵥ x) := by
  have hperp : ∀ h, h ∈ LinearMap.range N.mulVecLin →
      Q.polarBilin h y₀ = 0 → ∃ x, N *ᵥ x = h ∧ Q.polarBilin x z = 0 :=
    fun h ⟨x, hx⟩ hhy => ⟨x, hx, by rw [← hy₀, ← hadj]; rw [← hx] at hhy; exact hhy⟩
  obtain ⟨hx', hxr, hxy₀, hxT⟩ := exists_mem_range_perp_not_mem (Q := Q) N y₀
    (T := K ∙ z) (by rw [finrank_span_singleton hz0]; omega)
  obtain ⟨x, hx, hxz⟩ := hperp hx' hxr hxy₀
  have hxg : ∀ c : K, N *ᵥ x ≠ c • z := fun c h =>
    hxT (Submodule.mem_span_singleton.mpr ⟨c, by rw [← hx, h]⟩)
  have hNx0 : N *ᵥ x ≠ 0 := fun h => hxg 0 (by rw [h, zero_smul])
  obtain ⟨hy', hyr, hyy₀, hyT⟩ := exists_mem_range_perp_not_mem (Q := Q) N y₀
    (T := K ∙ (N *ᵥ x)) (by rw [finrank_span_singleton hNx0]; omega)
  obtain ⟨y₁, hy₁, hy₁z⟩ := hperp hy' hyr hyy₀
  have hy₁x : ∀ c : K, N *ᵥ y₁ ≠ c • (N *ᵥ x) := fun c h =>
    hyT (Submodule.mem_span_singleton.mpr ⟨c, by rw [← hy₁, h]⟩)
  refine ⟨x, ?_⟩
  by_cases hg : ∀ c : K, N *ᵥ y₁ ≠ c • z
  · exact ⟨y₁, hxz, hy₁z, hxg, hg, hy₁x⟩
  push Not at hg
  obtain ⟨μ, hμ⟩ := hg
  refine ⟨y₁ + x, hxz, by rw [map_add, LinearMap.add_apply, hy₁z, hxz, add_zero], hxg,
    fun c h => hxg (c - μ) ?_, fun c h => hy₁x (c - 1) ?_⟩
  · rw [mulVec_add, hμ] at h
    rw [sub_smul, ← h]
    abel
  · rw [mulVec_add] at h
    rw [sub_smul, one_smul, ← h]
    abel

variable [CharP K 2]

theorem commutant_typeBC_of_good [Finite K] (hQ : Q.polarBilin.Nondegenerate)
    (hK : 3 ≤ Nat.card K) {N : Matrix ι ι K} (hN : N * N = 0)
    (hadj : ∀ u v, Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v)) {z : ι → K}
    (hz : ∀ v, Q.polarBilin v z ^ 2 = Q.polarBilin v (N *ᵥ v)) (hz0 : z ≠ 0) {x y : ι → K}
    (hxz : Q.polarBilin x z = 0) (hyz : Q.polarBilin y z = 0) (hxg : ∀ c : K, N *ᵥ x ≠ c • z)
    (hyg : ∀ c : K, N *ᵥ y ≠ c • z) (hyx : ∀ c : K, N *ᵥ y ≠ c • (N *ᵥ x)) {X : GL ι K}
    (hXB : ∀ v w, Q.polarBilin ((X : Matrix ι ι K) *ᵥ v) ((X : Matrix ι ι K) *ᵥ w) =
      Q.polarBilin v w)
    (hXN : (X : Matrix ι ι K) * N = N * X)
    (hgood : ∀ w, Q.polarBilin w z = 0 → (∀ c : K, N *ᵥ w ≠ c • z) →
      (X : Matrix ι ι K) * cTwoX Q (N *ᵥ w) w = cTwoX Q (N *ᵥ w) w * X) :
    ∃ s t : K, (X : Matrix ι ι K) = 1 + s • N + t • polMat Q z z := by
  obtain ⟨t₂, ht₂0, ht₂1⟩ := exists_ne_zero_ne_one_of_three_le_card hK
  have hmem : ∀ w, Q.polarBilin w z = 0 → (∀ c : K, N *ᵥ w ≠ c • z) →
      ∃ c : K, ((X : Matrix ι ι K) - 1) *ᵥ w = c • (N *ᵥ w) := fun w hwz hwg =>
    exists_sub_one_mulVec_of_commute hQ hN hXB hXN (fun h => hwg 0 (by rw [h, zero_smul]))
      (hgood w hwz hwg)
  set L := (X : Matrix ι ι K) - 1 with hL
  have hlin : ∀ a b : ι → K, ∀ t : K, L *ᵥ (a + t • b) = L *ᵥ a + t • (L *ᵥ b) := fun a b t => by
    rw [mulVec_add, mulVec_smul]
  obtain ⟨s, hs⟩ := hmem x hxz hxg
  have hshift : ∀ w v, Q.polarBilin w z = 0 → (∀ c : K, N *ᵥ w ≠ c • z) →
      Q.polarBilin v z = 0 → (∀ c : K, N *ᵥ v ≠ c • z) →
      (∀ a b : K, a • (N *ᵥ w) + b • (N *ᵥ v) = 0 → a = 0 ∧ b = 0) →
      L *ᵥ v = s • (N *ᵥ v) → L *ᵥ w = s • (N *ᵥ w) := by
    intro w v hwz hwg hvz hvg hind hv
    obtain ⟨cw, hcw⟩ := hmem w hwz hwg
    have hgoodt : ∃ t : K, t ≠ 0 ∧ ∀ c : K, N *ᵥ (w + t • v) ≠ c • z := by
      by_contra! h
      obtain ⟨μ₁, hμ₁⟩ := h 1 one_ne_zero
      obtain ⟨μ₂, hμ₂⟩ := h t₂ ht₂0
      apply hvg ((1 - t₂)⁻¹ * (μ₁ - μ₂))
      have h3 : (1 - t₂) • (N *ᵥ v) = (μ₁ - μ₂) • z := by
        rw [mulVec_add, mulVec_smul, one_smul] at hμ₁
        rw [mulVec_add, mulVec_smul] at hμ₂
        rw [sub_smul, sub_smul, ← hμ₁, ← hμ₂, one_smul]
        abel
      have h4 : (1 - t₂) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht₂1)
      rw [mul_smul, ← h3, smul_smul, inv_mul_cancel₀ h4, one_smul]
    obtain ⟨t, ht0, htg⟩ := hgoodt
    obtain ⟨c, hc⟩ := hmem (w + t • v) (by
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hwz, hvz, smul_zero,
        add_zero]) htg
    rw [hlin, hcw, hv, mulVec_add, mulVec_smul] at hc
    have h1 : (c - cw) • (N *ᵥ w) + (t * (c - s)) • (N *ᵥ v) = 0 := by
      linear_combination (norm := module) -hc
    obtain ⟨h2, h3⟩ := hind _ _ h1
    have h4 : c = s := sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left ht0)
    rw [hcw, ← sub_eq_zero.mp h2, h4]
  have hNx0 : N *ᵥ x ≠ 0 := fun h => hxg 0 (by rw [h, zero_smul])
  have hindyx : ∀ a b : K, a • (N *ᵥ y) + b • (N *ᵥ x) = 0 → a = 0 ∧ b = 0 := fun a b h => by
    by_cases ha : a = 0
    · rw [ha, zero_smul, zero_add] at h
      exact ⟨ha, (smul_eq_zero.mp h).resolve_right hNx0⟩
    · exfalso
      apply hyx (-(a⁻¹ * b))
      have h1 : a⁻¹ • (a • (N *ᵥ y) + b • (N *ᵥ x)) = 0 := by rw [h, smul_zero]
      rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ha, one_smul] at h1
      rw [neg_smul, eq_neg_iff_add_eq_zero]
      exact h1
  have hys : L *ᵥ y = s • (N *ᵥ y) := hshift y x hyz hyg hxz hxg hindyx hs
  have hA : ∀ w, Q.polarBilin w z = 0 → (∀ c : K, N *ᵥ w ≠ c • z) → L *ᵥ w = s • (N *ᵥ w) := by
    intro w hwz hwg
    have hw0 : N *ᵥ w ≠ 0 := fun h => hwg 0 (by rw [h, zero_smul])
    by_cases hdep : ∃ l : K, N *ᵥ w = l • (N *ᵥ x)
    · obtain ⟨l, hl⟩ := hdep
      have hl0 : l ≠ 0 := fun h => hw0 (by rw [hl, h, zero_smul])
      refine hshift w y hwz hwg hyz hyg (fun a b h => ?_) hys
      rw [hl, smul_smul] at h
      obtain ⟨h1, h2⟩ := hindyx b (a * l) (by rw [add_comm]; exact h)
      exact ⟨(mul_eq_zero.mp h2).resolve_right hl0, h1⟩
    · push Not at hdep
      refine hshift w x hwz hwg hxz hxg (fun a b h => ?_) hs
      by_cases ha : a = 0
      · rw [ha, zero_smul, zero_add] at h
        exact ⟨ha, (smul_eq_zero.mp h).resolve_right hNx0⟩
      · exfalso
        apply hdep (-(a⁻¹ * b))
        have h1 : a⁻¹ • (a • (N *ᵥ w) + b • (N *ᵥ x)) = 0 := by rw [h, smul_zero]
        rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ha, one_smul] at h1
        rw [neg_smul, eq_neg_iff_add_eq_zero]
        exact h1
  have hB' : ∀ w, Q.polarBilin w z = 0 → L *ᵥ w = s • (N *ᵥ w) := by
    intro w hwz
    by_cases hwg : ∀ c : K, N *ᵥ w ≠ c • z
    · exact hA w hwz hwg
    push Not at hwg
    obtain ⟨μ, hμ⟩ := hwg
    have h1 := hA (w + x) (by
      rw [map_add, LinearMap.add_apply, hwz, hxz, add_zero]) fun c h => hxg (c - μ) (by
        rw [mulVec_add, hμ] at h
        rw [sub_smul, ← h]
        abel)
    rw [mulVec_add, mulVec_add, hs, smul_add] at h1
    exact add_right_cancel h1
  refine eq_of_fix_of_mem hQ hN hadj hz hz0 hXB hXN (fun k hk => ?_) fun w hwz => ⟨s, hB' w hwz⟩
  have hkz : Q.polarBilin k z = 0 := by
    have h1 := hz k
    rwa [hk, map_zero, pow_eq_zero_iff two_ne_zero] at h1
  have h1 := hB' k hkz
  rwa [hk, smul_zero, hL, sub_mulVec, one_mulVec, sub_eq_zero] at h1

theorem mulVec_eq_zero_of_rank_two (hQ : Q.polarBilin.Nondegenerate) {N : Matrix ι ι K}
    (hN : N * N = 0) (hiso : ∀ v, Q (v + N *ᵥ v) = Q v) (hrk : N.rank = 2) {z : ι → K}
    (hz : ∀ v, Q.polarBilin v z ^ 2 = Q (N *ᵥ v)) (hz0 : z ≠ 0) (hQz : Q z = 0) {x₁ : ι → K}
    (hx₁ : Q.polarBilin x₁ z = 1) {v : ι → K} (hvz : Q.polarBilin v z = 0)
    (hvy : Q.polarBilin v (N *ᵥ x₁) = 0) : N *ᵥ v = 0 := by
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hadj := polar_mulVec_adj Q hN hiso
  obtain ⟨y₀, hy₀⟩ := exists_mulVec_eq_of_sqrt_vector hQ hN hiso hz
  have hy₀z : Q.polarBilin y₀ z = 0 := by
    have h1 := hz y₀
    rwa [hy₀, hQz, pow_eq_zero_iff two_ne_zero] at h1
  obtain ⟨y₁, hy₁⟩ : ∃ y₁, y₁ = N *ᵥ x₁ := ⟨_, rfl⟩
  rw [← hy₁] at hvy
  have hy₁y₀ : Q.polarBilin y₁ y₀ = 1 := by rw [hy₁, hadj, hy₀, hx₁]
  have hli : LinearIndependent K ![z, y₁] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have hb : b = 0 := by
      have e1 := congrArg (fun v => Q.polarBilin v y₀) hab
      simpa [hBs z y₀, hy₀z, hy₁y₀] using e1
    rw [hb, zero_smul, add_zero] at hab
    exact ⟨(smul_eq_zero.mp hab).resolve_right hz0, hb⟩
  have hrange : Submodule.span K (Set.range ![z, y₁]) = LinearMap.range N.mulVecLin := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro i
      fin_cases i
      · exact ⟨y₀, hy₀⟩
      · exact ⟨x₁, hy₁.symm⟩
    · rw [finrank_span_eq_card hli, Fintype.card_fin]
      exact hrk.symm
  refine hQ.1 _ fun u => ?_
  have hu : N *ᵥ u ∈ Submodule.span K (Set.range ![z, y₁]) := by
    rw [hrange]
    exact ⟨u, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
  rw [hadj, ← hc, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul, hvz, hvy, smul_zero,
    add_zero]

theorem commutant_c2_of_fix [Finite K] (hQ : Q.polarBilin.Nondegenerate)
    (hι : 8 ≤ Fintype.card ι) {N : Matrix ι ι K} (hN : N * N = 0)
    (hiso : ∀ v, Q (v + N *ᵥ v) = Q v) (hrk : N.rank = 2) {z : ι → K}
    (hz : ∀ v, Q.polarBilin v z ^ 2 = Q (N *ᵥ v)) (hz0 : z ≠ 0) (hQz : Q z = 0) {X : GL ι K}
    (hXQ : ∀ v, Q ((X : Matrix ι ι K) *ᵥ v) = Q v) (hXN : (X : Matrix ι ι K) * N = N * X)
    {c₀ : K} (hF : ∀ w, Q w = c₀ → Q.polarBilin w z = 0 →
      (X : Matrix ι ι K) * cTwoX Q (N *ᵥ w) w = cTwoX Q (N *ᵥ w) w * X)
    (hsing : ∀ k, N *ᵥ k = 0 → Q k = 0 → (X : Matrix ι ι K) *ᵥ k = k) :
    ∃ s t : K, (X : Matrix ι ι K) = 1 + s • N + t • polMat Q z z := by
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hadj := polar_mulVec_adj Q hN hiso
  have hzB : ∀ v, Q.polarBilin v z ^ 2 = Q.polarBilin v (N *ᵥ v) := fun v => by
    rw [polar_self_mulVec Q hiso]
    exact hz v
  have hNN : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  have hXB := polarBilin_mulVec_of_isometry Q hXQ
  set sq := (frobeniusEquiv K 2).symm with hsqdef
  have hsq : ∀ c : K, sq c * sq c = c := fun c => by
    have h := frobenius_apply_frobeniusEquiv_symm K 2 c
    rwa [frobenius_def, pow_two] at h
  obtain ⟨y₀, hy₀⟩ := exists_mulVec_eq_of_sqrt_vector hQ hN hiso hz
  have hy₀z : Q.polarBilin y₀ z = 0 := by
    have h1 := hz y₀
    rwa [hy₀, hQz, pow_eq_zero_iff two_ne_zero] at h1
  obtain ⟨x₁, hx₁⟩ := exists_polarBilin_eq_one hQ hz0
  obtain ⟨y₁, hy₁⟩ : ∃ y₁, y₁ = N *ᵥ x₁ := ⟨_, rfl⟩
  have hQy₁ : Q y₁ = 1 := by rw [hy₁, ← hz, hx₁, one_pow]
  have hy₁y₀ : Q.polarBilin y₁ y₀ = 1 := by rw [hy₁, hadj, hy₀, hx₁]
  have hNy₁ : N *ᵥ y₁ = 0 := by rw [hy₁]; exact hNN x₁
  have hkz : ∀ k, N *ᵥ k = 0 → Q.polarBilin k z = 0 := fun k hk => by
    have h1 := hz k
    rwa [hk, QuadraticMap.map_zero, pow_eq_zero_iff two_ne_zero] at h1
  have hky : ∀ k, N *ᵥ k = 0 → Q.polarBilin k y₁ = 0 := fun k hk => by
    rw [hy₁, ← hadj, hk, map_zero, LinearMap.zero_apply]
  have hker : ∀ v, Q.polarBilin v z = 0 → Q.polarBilin v y₁ = 0 → N *ᵥ v = 0 :=
    fun v hvz hvy => mulVec_eq_zero_of_rank_two hQ hN hiso hrk hz hz0 hQz hx₁ hvz (hy₁ ▸ hvy)
  have hli : LinearIndependent K ![z, y₁] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have hb : b = 0 := by
      have e1 := congrArg (fun v => Q.polarBilin v y₀) hab
      simpa [hBs z y₀, hy₀z, hy₁y₀] using e1
    rw [hb, zero_smul, add_zero] at hab
    exact ⟨(smul_eq_zero.mp hab).resolve_right hz0, hb⟩
  have hNw : ∀ w, Q.polarBilin w z = 0 → N *ᵥ w = Q.polarBilin w y₁ • z := fun w hwz => by
    have h1 := hker (w - Q.polarBilin w y₁ • y₀) (by
      rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hwz, hy₀z, smul_zero,
        sub_zero]) (by
      rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hBs y₀ y₁, hy₁y₀,
        smul_eq_mul, mul_one, sub_self])
    rw [mulVec_sub, mulVec_smul, hy₀, sub_eq_zero] at h1
    exact h1
  have hkv : ∀ v, N *ᵥ v = 0 → Q (v + sq (Q v) • y₁) = 0 ∧ N *ᵥ (v + sq (Q v) • y₁) = 0 := by
    intro v hv
    refine ⟨?_, by rw [mulVec_add, mulVec_smul, hv, hNy₁, smul_zero, add_zero]⟩
    rw [quad_add, QuadraticMap.map_smul, hQy₁, map_smul, hky v hv, smul_zero, add_zero,
      smul_eq_mul, mul_one, hsq, CharTwo.add_self_eq_zero]
  have h4b' : ∀ v, N *ᵥ v = 0 →
      (X : Matrix ι ι K) *ᵥ (v + sq (Q v) • y₁) = v + sq (Q v) • y₁ := fun v hv =>
    hsing _ (hkv v hv).2 (hkv v hv).1
  obtain ⟨a, ha, han⟩ := exists_polar_perp_not_mem_span (Q := Q) (m := 2) (by omega) ![z, y₁]
  have haz : Q.polarBilin a z = 0 := ha 0
  have hay : Q.polarBilin a y₁ = 0 := ha 1
  obtain ⟨b', hb'⟩ := exists_polar_dual Q hQ ![a, z, y₁]
    (linearIndependent_finCons.mpr ⟨hli, han⟩)
  have hab : Q.polarBilin a (b' 0) = 1 := by simpa using hb' 0 0
  have hbz : Q.polarBilin (b' 0) z = 0 := by rw [hBs]; simpa using hb' 1 0
  have hby : Q.polarBilin (b' 0) y₁ = 0 := by rw [hBs]; simpa using hb' 2 0
  have hNa : N *ᵥ a = 0 := hker a haz hay
  have hNb : N *ᵥ b' 0 = 0 := hker _ hbz hby
  have hNab : N *ᵥ (a + b' 0) = 0 := by rw [mulVec_add, hNa, hNb, add_zero]
  have hsqab : sq (Q (a + b' 0)) = sq (Q a) + sq (Q (b' 0)) + 1 := by
    rw [quad_add, hab, map_add, map_add, map_one]
  have hy₁eq : y₁ = (a + b' 0 + sq (Q (a + b' 0)) • y₁) - (a + sq (Q a) • y₁) -
      (b' 0 + sq (Q (b' 0)) • y₁) := by
    rw [hsqab]
    module
  have hXy₁ : (X : Matrix ι ι K) *ᵥ y₁ = y₁ := by
    calc (X : Matrix ι ι K) *ᵥ y₁ = (X : Matrix ι ι K) *ᵥ ((a + b' 0 + sq (Q (a + b' 0)) • y₁) -
          (a + sq (Q a) • y₁) - (b' 0 + sq (Q (b' 0)) • y₁)) := by rw [← hy₁eq]
      _ = y₁ := by rw [mulVec_sub, mulVec_sub, h4b' _ hNab, h4b' a hNa, h4b' _ hNb, ← hy₁eq]
  have hfix : ∀ k, N *ᵥ k = 0 → (X : Matrix ι ι K) *ᵥ k = k := fun k hk => by
    have h1 := h4b' k hk
    rw [mulVec_add, mulVec_smul, hXy₁] at h1
    exact add_right_cancel h1
  have hmem : ∀ w, Q.polarBilin w z = 0 →
      ∃ c : K, ((X : Matrix ι ι K) - 1) *ᵥ w = c • (N *ᵥ w) := by
    intro w hwz
    by_cases hw : N *ᵥ w = 0
    · exact ⟨0, by rw [hw, smul_zero, sub_mulVec, one_mulVec, hfix w hw, sub_self]⟩
    have hwy : Q.polarBilin w y₁ ≠ 0 := fun h => hw (by rw [hNw w hwz, h, zero_smul])
    obtain ⟨k₀, hk₀, hQk₀, hwk₀⟩ : ∃ k₀, N *ᵥ k₀ = 0 ∧ Q k₀ = 0 ∧ Q.polarBilin w k₀ ≠ 0 := by
      by_contra! h
      apply hwy
      have e := congrArg (Q.polarBilin w) hy₁eq
      rw [map_sub, map_sub, h _ (hkv _ hNab).2 (hkv _ hNab).1, h _ (hkv _ hNa).2 (hkv _ hNa).1,
        h _ (hkv _ hNb).2 (hkv _ hNb).1, sub_zero, sub_zero] at e
      exact e
    set t := (c₀ + Q w) / Q.polarBilin w k₀ with ht
    have hQw' : Q (w + t • k₀) = c₀ := by
      rw [quad_add, QuadraticMap.map_smul, hQk₀, smul_zero, add_zero, map_smul, smul_eq_mul, ht,
        div_mul_cancel₀ _ hwk₀]
      linear_combination Q w * CharTwo.two_eq_zero (R := K)
    have hw'z : Q.polarBilin (w + t • k₀) z = 0 := by
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hwz, hkz k₀ hk₀,
        smul_zero, add_zero]
    have hNw' : N *ᵥ (w + t • k₀) = N *ᵥ w := by
      rw [mulVec_add, mulVec_smul, hk₀, smul_zero, add_zero]
    obtain ⟨c, hc⟩ := exists_sub_one_mulVec_of_commute hQ hN hXB hXN (by rw [hNw']; exact hw)
      (hF _ hQw' hw'z)
    have hk₀' : ((X : Matrix ι ι K) - 1) *ᵥ k₀ = 0 := by
      rw [sub_mulVec, one_mulVec, hfix k₀ hk₀, sub_self]
    refine ⟨c, ?_⟩
    rw [hNw', mulVec_add, mulVec_smul, hk₀', smul_zero, add_zero] at hc
    exact hc
  exact eq_of_fix_of_mem hQ hN hadj hzB hz0 hXB hXN hfix hmem

theorem commutant_c2_orth [Finite K] (hQ : Q.polarBilin.Nondegenerate)
    (hι : 8 ≤ Fintype.card ι) {N : Matrix ι ι K} (hN : N * N = 0)
    (hiso : ∀ v, Q (v + N *ᵥ v) = Q v) (hrk : N.rank = 2) {z : ι → K}
    (hz : ∀ v, Q.polarBilin v z ^ 2 = Q (N *ᵥ v)) (hz0 : z ≠ 0) (hQz : Q z = 0) {X : GL ι K}
    (hXQ : ∀ v, Q ((X : Matrix ι ι K) *ᵥ v) = Q v) (hXN : (X : Matrix ι ι K) * N = N * X)
    (hF : ∀ w, Q w = 0 → Q.polarBilin w z = 0 →
      (X : Matrix ι ι K) * cTwoX Q (N *ᵥ w) w = cTwoX Q (N *ᵥ w) w * X)
    (hR : ∀ a b, N *ᵥ a = 0 → N *ᵥ b = 0 → Q a = 0 → Q b = 0 → Q.polarBilin a b = 0 →
      (X : Matrix ι ι K) * cTwoX Q a b = cTwoX Q a b * X) :
    ∃ s t : K, (X : Matrix ι ι K) = 1 + s • N + t • polMat Q z z := by
  refine commutant_c2_of_fix hQ hι hN hiso hrk hz hz0 hQz hXQ hXN hF fun k hk hQk => ?_
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hadj := polar_mulVec_adj Q hN hiso
  have hzB : ∀ v, Q.polarBilin v z ^ 2 = Q.polarBilin v (N *ᵥ v) := fun v => by
    rw [polar_self_mulVec Q hiso]
    exact hz v
  have hNN : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  have hXB := polarBilin_mulVec_of_isometry Q hXQ
  have hNz : N *ᵥ z = 0 := mulVec_sqrt_vector_of_adj hQ hN hadj hzB
  have hXz : (X : Matrix ι ι K) *ᵥ z = z := mulVec_sqrt_vector_of_commute_adj hQ hzB hXB hXN
  set sq := (frobeniusEquiv K 2).symm with hsqdef
  have hsq : ∀ c : K, sq c * sq c = c := fun c => by
    have h := frobenius_apply_frobeniusEquiv_symm K 2 c
    rwa [frobenius_def, pow_two] at h
  obtain ⟨x₁, hx₁⟩ := exists_polarBilin_eq_one hQ hz0
  obtain ⟨y₁, hy₁⟩ : ∃ y₁, y₁ = N *ᵥ x₁ := ⟨_, rfl⟩
  have hQy₁ : Q y₁ = 1 := by rw [hy₁, ← hz, hx₁, one_pow]
  have hNy₁ : N *ᵥ y₁ = 0 := by rw [hy₁]; exact hNN x₁
  have hkz : ∀ k, N *ᵥ k = 0 → Q.polarBilin k z = 0 := fun k hk => by
    have h1 := hz k
    rwa [hk, QuadraticMap.map_zero, pow_eq_zero_iff two_ne_zero] at h1
  have hky : ∀ k, N *ᵥ k = 0 → Q.polarBilin k y₁ = 0 := fun k hk => by
    rw [hy₁, ← hadj, hk, map_zero, LinearMap.zero_apply]
  have hker : ∀ v, Q.polarBilin v z = 0 → Q.polarBilin v y₁ = 0 → N *ᵥ v = 0 :=
    fun v hvz hvy => mulVec_eq_zero_of_rank_two hQ hN hiso hrk hz hz0 hQz hx₁ hvz (hy₁ ▸ hvy)
  have hXz0 : ∀ c, cTwoX Q z c = 0 → c = Q.polarBilin x₁ c • z := fun c hc => by
    have h1 := congrArg (· *ᵥ x₁) hc
    simp only [cTwoX_mulVec, hx₁, one_smul, zero_mulVec] at h1
    linear_combination (norm := module) h1 -
      CharTwo.two_eq_zero (R := K) • (Q.polarBilin x₁ c • z)
  have hconj : ∀ a b, N *ᵥ a = 0 → N *ᵥ b = 0 → Q a = 0 → Q b = 0 → Q.polarBilin a b = 0 →
      cTwoX Q ((X : Matrix ι ι K) *ᵥ a) ((X : Matrix ι ι K) *ᵥ b) = cTwoX Q a b := by
    intro a b ha hb hQa hQb hab
    rw [← conj_cTwoX_of_polar hXB, hR a b ha hb hQa hQb hab, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  have h4a : ∀ k, N *ᵥ k = 0 → Q k = 0 → ∃ φ : K, (X : Matrix ι ι K) *ᵥ k = k + φ • z := by
    intro k hk hQk
    have h1 := hconj z k hNz hk hQz hQk (by rw [hBs]; exact hkz k hk)
    rw [hXz] at h1
    have h2 : cTwoX Q z ((X : Matrix ι ι K) *ᵥ k - k) = 0 := by
      rw [sub_eq_add_neg, ← neg_one_smul K k, cTwoX_add_smul_right, h1, neg_one_smul,
        add_neg_cancel]
    exact ⟨_, by rw [← hXz0 _ h2, add_sub_cancel]⟩
  obtain ⟨a, ha, han⟩ := exists_polar_perp_not_mem_span (Q := Q) (m := 3) (by omega)
    ![z, y₁, k]
  have haz : Q.polarBilin a z = 0 := ha 0
  have hay : Q.polarBilin a y₁ = 0 := ha 1
  have hak : Q.polarBilin a k = 0 := ha 2
  have hNa : N *ᵥ a = 0 := hker a haz hay
  obtain ⟨k', hk'⟩ : ∃ k', k' = a + sq (Q a) • y₁ := ⟨_, rfl⟩
  have hQk' : Q k' = 0 := by
    rw [hk', quad_add, QuadraticMap.map_smul, hQy₁, map_smul, hay, smul_zero, add_zero,
      smul_eq_mul, mul_one, hsq, CharTwo.add_self_eq_zero]
  have hNk' : N *ᵥ k' = 0 := by rw [hk', mulVec_add, mulVec_smul, hNa, hNy₁, smul_zero, add_zero]
  have hkk' : Q.polarBilin k k' = 0 := by
    rw [hk', map_add, map_smul, smul_eq_mul, hBs k a, hak, hky k hk, mul_zero, add_zero]
  obtain ⟨φ, hφ⟩ := h4a k hk hQk
  obtain ⟨φ', hφ'⟩ := h4a k' hNk' hQk'
  have h1 := hconj k k' hk hNk' hQk hQk' hkk'
  rw [hφ, hφ'] at h1
  have h2 := congrArg (· *ᵥ x₁) h1
  simp only [cTwoX_mulVec, map_add, map_smul, smul_eq_mul, hx₁, mul_one] at h2
  by_cases hφ0 : φ = 0
  · rw [hφ, hφ0, zero_smul, add_zero]
  exfalso
  apply han
  have h3 : φ • a = (-(Q.polarBilin x₁ k * φ' + Q.polarBilin x₁ k' * φ)) • z +
      (-(φ * sq (Q a))) • y₁ + (-φ') • k := by
    linear_combination (norm := module) h2 - φ • hk' -
      CharTwo.two_eq_zero (R := K) • ((φ * φ') • z)
  rw [← Submodule.smul_mem_iff _ hφ0, h3]
  exact add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))

end Linear

section Groups

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [Finite K] [CharP K 2]

theorem noPairOrbit_typeC_orth (Q : QuadraticForm K (ι → K)) (q : (ι → K) → K) (hq : ⇑Q = q)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hK : 3 ≤ Nat.card K) (hι : 8 ≤ Fintype.card ι)
    {e : rankTwoQuot A ≃* StatedProj (StatedOmega q)} (hZ : Odd (Nat.card (center ↥A))) {p : G}
    (hp2 : orderOf p = 2) {M : GL ι K} (hpM : Represents e p M) (hM2 : orderOf M = 2)
    (hnz : ∃ v, Q (((M : Matrix ι ι K) - 1) *ᵥ v) ≠ 0) : NoPairOrbit A p := by
  subst hq
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hp2' : p ^ 2 = 1 := by rw [← hp2]; exact pow_orderOf_eq_one p
  have hM2' : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
  have hMQ := statedOmega_isometry hpM.2.1
  have hN : ((M : Matrix ι ι K) - 1) * ((M : Matrix ι ι K) - 1) = 0 := sub_one_mul_self hM2'
  have hev := even_commRank_of_mem_statedOmega Q hQ hpM.2.1
  have hiso : ∀ v, Q (v + ((M : Matrix ι ι K) - 1) *ᵥ v) = Q v := fun v => by
    rw [sub_mulVec, one_mulVec, add_sub_cancel]
    exact hMQ v
  obtain ⟨z, hz⟩ := exists_sqrt_vector Q hQ hN hiso
  have hQz : Q z = 0 := quad_eq_zero_of_sqrt_vector hQ hMQ hN hev hz
  obtain ⟨N, hNdef⟩ : ∃ N, N = (M : Matrix ι ι K) - 1 := ⟨_, rfl⟩
  rw [← hNdef] at hN hiso hz hnz
  have hMN : (M : Matrix ι ι K) = 1 + N := by rw [hNdef, add_sub_cancel]
  have hadj := polar_mulVec_adj Q hN hiso
  have hzB : ∀ v, Q.polarBilin v z ^ 2 = Q.polarBilin v (N *ᵥ v) := fun v => by
    rw [polar_self_mulVec Q hiso]
    exact hz v
  have hNN : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  have hNz : N *ᵥ z = 0 := mulVec_sqrt_vector_of_adj hQ hN hadj hzB
  have hz0 : z ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := hnz
    exact hv (by rw [← hz v, map_zero, zero_pow two_ne_zero])
  have hcomm : ∀ X : GL ι K, X * M = M * X → (X : Matrix ι ι K) * N = N * X := fun X hXM => by
    have h1 := congrArg (fun Y : GL ι K => (Y : Matrix ι ι K)) hXM
    simp only [Units.val_mul] at h1
    rw [hNdef, Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.mul_one, Matrix.one_mul]
  have hPz : ∀ X : GL ι K, (∀ v, Q ((X : Matrix ι ι K) *ᵥ v) = Q v) → X * M = M * X →
      (X : Matrix ι ι K) * polMat Q z z = polMat Q z z * X := fun X hXQ hXM => by
    have hXB := polarBilin_mulVec_of_isometry Q hXQ
    have hXz := mulVec_sqrt_vector_of_commute_adj hQ hzB hXB (hcomm X hXM)
    have h1 := conj_polMat_self_of_polar hXB z
    rw [hXz] at h1
    calc (X : Matrix ι ι K) * polMat Q z z =
        X * polMat Q z z * ((X⁻¹ : GL ι K) : Matrix ι ι K) * X := by
          rw [Matrix.mul_assoc _ (((X⁻¹ : GL ι K) : Matrix ι ι K)), Units.inv_mul, Matrix.mul_one]
      _ = polMat Q z z * X := by rw [h1]
  obtain ⟨μ, hμ0, hμ1⟩ := exists_ne_zero_ne_one_of_three_le_card hK
  intro u hu hu2 horb
  obtain ⟨U, hU⟩ := exists_represents e (mem_inf.mp hu).1
  have hUM : U * M = M * U := Units.ext (by
    rw [Units.val_mul, Units.val_mul]
    exact hU.mul_comm_of_commute hpM hM2' (mem_centralizer_singleton_iff.mp (mem_inf.mp hu).2))
  have hUQ := statedOmega_isometry hU.2.1
  have hUB := polarBilin_mulVec_of_isometry Q hUQ
  have hroot : ∀ a b : ι → K, Q a = 0 → Q b = 0 → Q.polarBilin a b = 0 →
      cTwoX Q a b * N = N * cTwoX Q a b →
      (U : Matrix ι ι K) * cTwoX Q a b = cTwoX Q a b * U := fun a b ha hb hab hEN =>
    commute_of_pairOrbit_orth hQ hT hZ hμ0 hμ1 hp2' hpM horb hU (cTwoX_mul_self hab)
      (by rw [hMN, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hEN])
      (fun t v => cTwoX_isometry ha hb hab t v) (even_rank_cTwoX hQ a b)
  have hF : ∀ w, Q w = 0 → Q.polarBilin w z = 0 →
      (U : Matrix ι ι K) * cTwoX Q (N *ᵥ w) w = cTwoX Q (N *ᵥ w) w * U := fun w hw hwz =>
    hroot _ _ (by rw [← hz, hwz, zero_pow two_ne_zero]) hw
      (by rw [hBs, ← hzB, hwz, zero_pow two_ne_zero]) (cTwoX_commute_typeA hN hadj w)
  have hR : ∀ a b, N *ᵥ a = 0 → N *ᵥ b = 0 → Q a = 0 → Q b = 0 → Q.polarBilin a b = 0 →
      (U : Matrix ι ι K) * cTwoX Q a b = cTwoX Q a b * U := fun a b ha hb hQa hQb hab =>
    hroot a b hQa hQb hab (by
      refine Matrix.ext_iff_mulVec.mpr fun v => ?_
      simp only [← mulVec_mulVec, cTwoX_mulVec, mulVec_add, mulVec_smul, ha, hb, hadj, map_zero,
        zero_smul, smul_zero, add_zero])
  have hrk : N.rank = 2 ∨ 3 ≤ N.rank := by
    have hev' : Even N.rank := by rw [hNdef]; exact hev
    have hr0 : N.rank ≠ 0 := fun h => by
      obtain ⟨v, hv⟩ := hnz
      have h1 : N *ᵥ v ∈ LinearMap.range N.mulVecLin := ⟨v, rfl⟩
      rw [Submodule.finrank_eq_zero.mp h] at h1
      rw [(Submodule.mem_bot K).mp h1, QuadraticMap.map_zero] at hv
      exact hv rfl
    obtain ⟨r, hr⟩ := hev'
    omega
  obtain ⟨s, t, hst⟩ : ∃ s t : K, (U : Matrix ι ι K) = 1 + s • N + t • polMat Q z z := by
    rcases hrk with hrk | hrk
    · exact commutant_c2_orth hQ hι hN hiso hrk hz hz0 hQz hUQ (hcomm U hUM) hF hR
    obtain ⟨y₀, hy₀⟩ := exists_mulVec_eq_of_sqrt_vector hQ hN hiso hz
    obtain ⟨x, y, hxz, hyz, hxg, hyg, hyx⟩ := exists_good_vectors_typeBC hadj hy₀ hz0 hrk
    refine commutant_typeBC_of_good hQ hK hN hadj hzB hz0 hxz hyz hxg hyg hyx hUB (hcomm U hUM)
      fun w hwz hwg => ?_
    have hli : LinearIndependent K ![N *ᵥ w, z] := by
      rw [LinearIndependent.pair_iff]
      intro a b hab
      by_cases ha : a = 0
      · rw [ha, zero_smul, zero_add] at hab
        exact ⟨ha, (smul_eq_zero.mp hab).resolve_right hz0⟩
      · exfalso
        apply hwg (-(a⁻¹ * b))
        have h1 : a⁻¹ • (a • (N *ᵥ w) + b • z) = 0 := by rw [hab, smul_zero]
        rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ha, one_smul] at h1
        rw [neg_smul, eq_neg_iff_add_eq_zero]
        exact h1
    obtain ⟨x', hx'⟩ := exists_polar_dual Q hQ ![N *ᵥ w, z] hli
    have hwx : Q.polarBilin w (N *ᵥ x' 0) = 1 := by rw [← hadj]; simpa using hx' 0 0
    have hxz' : Q.polarBilin (x' 0) z = 0 := by rw [hBs]; simpa using hx' 1 0
    have hQNx : Q (N *ᵥ x' 0) = 0 := by rw [← hz, hxz', zero_pow two_ne_zero]
    have hNw' : N *ᵥ (w + Q w • (N *ᵥ x' 0)) = N *ᵥ w := by
      rw [mulVec_add, mulVec_smul, hNN, smul_zero, add_zero]
    have h1 := hF (w + Q w • (N *ᵥ x' 0)) (by
        rw [quad_add, QuadraticMap.map_smul, hQNx, map_smul, smul_eq_mul, smul_eq_mul, hwx,
          mul_zero, add_zero, mul_one, CharTwo.add_self_eq_zero]) (by
        rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hwz, hadj, hNz, map_zero,
          smul_zero, add_zero])
    rw [hNw', cTwoX_add_smul_right, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, hR _ _ (hNN w) (hNN _) (by rw [← hz, hwz, zero_pow two_ne_zero]) hQNx
        (by rw [hadj, hNN, map_zero])] at h1
    exact add_right_cancel h1
  refine central_of_commute_all hZ hpM hM2' hu2 hU fun X hX hXM => Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hst, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, hcomm X hXM, hPz X (statedOmega_isometry hX) hXM]

end Groups

section Families

theorem pairOrbitFree_orthPlus : PairOrbitFree .orthPlus := by
  intro G _ _ A D hD _ hZ hq p ℓ hp
  cases D with
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨hp2, M, hpM, hM2, -⟩ := hp
    have hK3 : 3 ≤ Nat.card K := by
      have h4 : 4 ≤ 2 ^ m := hq
      rw [hK]
      omega
    by_cases h0 : ∀ v, quadPlus n K (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ v) = 0
    · exact noPairOrbit_typeA_orth (quadPlus n K) (StatedQuadPlus n K) (coe_quadPlus n K)
        (nondegenerate_polarBilin_quadPlus n K) (exists_totallySingular_quadPlus (by omega) K) hK3
        hZ hp2 hpM hM2 h0
    · push Not at h0
      exact noPairOrbit_typeC_orth (quadPlus n K) (StatedQuadPlus n K) (coe_quadPlus n K)
        (nondegenerate_polarBilin_quadPlus n K) (exists_totallySingular_quadPlus (by omega) K) hK3
        (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) hZ hp2 hpM hM2 h0
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

theorem pairOrbitFree_orthMinus : PairOrbitFree .orthMinus := by
  intro G _ _ A D hD _ hZ hq p ℓ hp
  cases D with
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    obtain ⟨hp2, M, hpM, hM2, -⟩ := hp
    have hK3 : 3 ≤ Nat.card K := by
      have h4 : 4 ≤ 2 ^ m := hq
      rw [hK]
      omega
    by_cases h0 : ∀ v, quadMinus n K b c
        (((M : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) -
          1) *ᵥ v) = 0
    · exact noPairOrbit_typeA_orth (quadMinus n K b c) (StatedQuadMinus n K b c)
        (coe_quadMinus n K b c) (nondegenerate_polarBilin_quadMinus_of_finite n K hbc)
        (exists_totallySingular_quadMinus hn K b c) hK3 hZ hp2 hpM hM2 h0
    · push Not at h0
      exact noPairOrbit_typeC_orth (quadMinus n K b c) (StatedQuadMinus n K b c)
        (coe_quadMinus n K b c) (nondegenerate_polarBilin_quadMinus_of_finite n K hbc)
        (exists_totallySingular_quadMinus hn K b c) hK3
        (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) hZ hp2 hpM hM2 h0
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD

end Families

end CFSG.ComponentClassification.RankTwoClassical

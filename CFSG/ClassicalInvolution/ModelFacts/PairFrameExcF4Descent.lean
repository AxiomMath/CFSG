module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Stab
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLang
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLeviToral
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolution

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def JF4 : Set (Fin (Tag.rank .F4)) := {j | j.val ≠ 0}

theorem iform_thetaF4_single_of_mem {j : Fin (Tag.rank .F4)} (hj : j ∈ JF4) :
    iform thetaF4 (Pi.single j 1) = 0 := by
  rw [iform_thetaF4_single]
  have : j.val ≠ 0 := hj
  simp [this]

theorem mem_parabolicRoots_F4 {σ : Fin (Tag.rank .F4) → ℤ} (hσ : IsRoot .F4 σ)
    (h : iform thetaF4 σ = 0) : σ ∈ parabolicRoots .F4 JF4 := by
  refine ⟨hσ, fun i hi => ?_⟩
  have h0 := (iform_thetaF4_eq_zero_iff σ (mem_rootFinset.2 hσ)).1 h
  have hi0 : i = ⟨0, by decide⟩ := by
    apply Fin.ext
    have : ¬ i.val ≠ 0 := hi
    simpa using this
  rw [hi0]
  exact h0

section Descent

variable {k : Type} [Field k]

theorem iform_eq_zero_of_rootChar_pairDiagF4_eq_one {δ : Fin (Tag.rank .F4) → ℤ}
    (hδ : IsRoot .F4 δ) (hl : iform δ δ = 4) {c : kˣ}
    (hc : ∀ j : ℕ, 1 ≤ j → j ≤ 8 → c ^ j ≠ 1) {σ : Fin (Tag.rank .F4) → ℤ} (hσ : IsRoot .F4 σ)
    (h : rootChar (pairDiagF4 δ c) σ = 1) :
    iform thetaF4 σ = 0 ∧ (-1 : kˣ) ^ (iform δ σ / 2) = 1 := by
  rw [rootChar_pairDiagF4 hδ hl] at h
  have b := abs_iform_thetaF4_le σ (mem_rootFinset.2 hσ)
  rw [abs_le] at b
  obtain ⟨m, hm⟩ := even_iform_of_long_F4 isRoot_thetaF4 iform_thetaF4_self σ
  have hpow : ∀ n : ℤ, (c ^ n) ^ 2 = c ^ (2 * n) := fun n => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
    norm_cast
  have h2 : ((-1 : kˣ) ^ (iform δ σ / 2) * c ^ (iform thetaF4 σ / 2)) ^ 2 = 1 := by rw [h]; simp
  rw [mul_pow, neg_one_zpow_sq, one_mul, hpow] at h2
  have hy : iform thetaF4 σ = 0 := by
    have := eq_zero_of_zpow_eq_one hc (m := 2 * (iform thetaF4 σ / 2)) (N := 8) (by
      rw [abs_le]; omega) h2
    omega
  refine ⟨hy, ?_⟩
  rw [hy] at h
  simpa using h

theorem rootDiagUnit_corootDiagF4_comm_levi (c : kˣ) {g : ModGL .F4 k}
    (hg : g ∈ parabolicLevi .F4 k JF4) :
    rootDiagUnit .F4 (corootDiagF4 thetaF4 c) * g =
      g * rootDiagUnit .F4 (corootDiagF4 thetaF4 c) := by
  have hle : parabolicLevi .F4 k JF4 ≤
      Subgroup.centralizer {rootDiagUnit .F4 (corootDiagF4 thetaF4 c)} := by
    obtain ⟨hx, hy, -⟩ := root_diagonal_conjugation .F4 k (corootDiagF4 thetaF4 c)
    refine sup_le (fun t ht => ?_) ((Subgroup.closure_le _).2 ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (rootDiagUnit_mul_comm_of_mem_torusGroup _ ht).symm
    · rintro _ ⟨j, hj, c', rfl | rfl⟩
      · have h1 : corootDiagF4 thetaF4 c j = 1 := by
          simp [corootDiagF4, iform_thetaF4_single_of_mem hj]
        have h2 := hx j c'
        rw [h1, Units.val_one, one_mul] at h2
        exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h2).symm
      · have h1 : corootDiagF4 thetaF4 c j = 1 := by
          simp [corootDiagF4, iform_thetaF4_single_of_mem hj]
        have h2 := hy j c'
        rw [h1, inv_one, Units.val_one, one_mul] at h2
        exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h2).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm

theorem exists_levi_fixed_conj_F4 (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) {δ : Fin (Tag.rank .F4) → ℤ} (hδ : IsRoot .F4 δ)
    (hl : iform δ δ = 4) (hδθ : iform thetaF4 δ = 0) {y v : ModGL .F4 k}
    (hv : v ∈ parabolicLevi .F4 k JF4) (hFy : entrywiseFrobGL .F4 k p e y = y)
    (hvy : v * y * v⁻¹ = rootDiagUnit .F4 (corootDiagF4 δ (-1))) :
    ∃ h ∈ parabolicLevi .F4 k JF4, entrywiseFrobGL .F4 k p e h = h ∧
      h * y * h⁻¹ = rootDiagUnit .F4 (corootDiagF4 δ (-1)) := by
  classical
  have hchar : ringChar k ≠ 2 := by rw [ringChar.eq k p]; exact hp2
  have hk2 : (-1 : kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hchar (by simpa using congrArg Units.val h)
  obtain ⟨c, hc⟩ := exists_unit_pow_ne_one (k := k) 8
  set a' := pairDiagF4 δ c with ha'
  set d := rootDiagUnit .F4 (corootDiagF4 δ (-1 : kˣ)) with hd
  set db := rootDiagUnit .F4 (corootDiagF4 thetaF4 c) with hdb
  have hsign : ∀ i, corootDiagF4 δ (-1 : kˣ) i = (1 : kˣ) ∨ corootDiagF4 δ (-1 : kˣ) i = -1 :=
    fun i => by
      rcases Int.even_or_odd (iform δ (Pi.single i 1) / 2) with h | h
      · left; exact h.neg_one_zpow
      · right; exact h.neg_one_zpow
  have hFd : entrywiseFrobGL .F4 k p e d = d := entrywiseFrobGL_rootDiagUnit_of_sign p e hsign
  have hker : ∀ σ ∈ kernelRoots (rootCharHom a'), IsRoot .F4 σ ∧ iform thetaF4 σ = 0 ∧
      rootChar (corootDiagF4 δ (-1 : kˣ)) σ = 1 := by
    intro σ hσ
    obtain ⟨hσr, hσ1⟩ := hσ
    obtain ⟨h1, h2⟩ := iform_eq_zero_of_rootChar_pairDiagF4_eq_one hδ hl hc hσr hσ1
    exact ⟨hσr, h1, by rw [rootChar_corootDiagF4 hδ hl]; exact h2⟩
  set M := torusGroup .F4 k ⊔ rootSpan .F4 k (kernelRoots (rootCharHom a')) with hM
  have hMd : ∀ m ∈ M, m * d * m⁻¹ = d := by
    have hle : M ≤ Subgroup.centralizer {d} := by
      refine sup_le (fun t ht => ?_) ?_
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (rootDiagUnit_mul_comm_of_mem_torusGroup _ ht).symm
      · exact rootSpan_le_centralizer (corootDiagF4 δ (-1 : kˣ))
          (fun σ hσ => ⟨(hker σ hσ).1, (hker σ hσ).2.2⟩)
    intro m hm
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle hm)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hMJ : M ≤ parabolicLevi .F4 k JF4 := by
    refine sup_le (torusGroup_le_parabolicLevi JF4) ?_
    refine iSup₂_le fun σ hσ => rootSubgroup_le_parabolicLevi' ?_
    exact mem_parabolicRoots_F4 (hker σ hσ).1 (hker σ hσ).2.1
  have hlang : ∀ u ∈ M, ∃ m ∈ M, u = m⁻¹ * entrywiseFrobGL .F4 k p e m :=
    fun u hu => exists_eq_inv_mul_frob_torus_sup_rootSpan p he (rootCharHom a') hu
  have hFvJ : entrywiseFrobGL .F4 k p e v ∈ parabolicLevi .F4 k JF4 :=
    baseChangeGL_mem_parabolicLevi (iterateFrobenius k p e) hv
  have hu : entrywiseFrobGL .F4 k p e v * v⁻¹ ∈ M := by
    set u := entrywiseFrobGL .F4 k p e v * v⁻¹ with hudef
    have huJ : u ∈ parabolicLevi .F4 k JF4 := mul_mem hFvJ (inv_mem hv)
    have hF : entrywiseFrobGL .F4 k p e v * y * (entrywiseFrobGL .F4 k p e v)⁻¹ = d := by
      have := congrArg (entrywiseFrobGL .F4 k p e) hvy
      rw [map_mul, map_mul, map_inv, hFy, hFd] at this
      exact this
    have hud : d * u = u * d := by
      have hy' : v⁻¹ * d * v = y := by rw [← hvy]; group
      have h1 : u * d * u⁻¹ = d := by
        calc u * d * u⁻¹ = entrywiseFrobGL .F4 k p e v * (v⁻¹ * d * v) *
              (entrywiseFrobGL .F4 k p e v)⁻¹ := by rw [hudef]; group
          _ = d := by rw [hy', hF]
      calc d * u = (u * d * u⁻¹) * u := by rw [h1]
        _ = u * d := by group
    have hub : db * u = u * db := rootDiagUnit_corootDiagF4_comm_levi c huJ
    have hmem : u ∈ toralCentralizer .F4 k a' := by
      rw [mem_toralCentralizer]
      refine ⟨parabolicSubgroup_le_adjointGroup _ _ _
        (parabolicLevi_le_parabolicSubgroup JF4 huJ), ?_⟩
      have hmul : rootDiagUnit .F4 a' = d * db := rootDiagUnit_mul _ _
      rw [mul_inv_eq_iff_eq_mul, hmul]
      calc d * db * u = d * (db * u) := by group
        _ = d * (u * db) := by rw [hub]
        _ = (d * u) * db := by group
        _ = (u * d) * db := by rw [hud]
        _ = u * (d * db) := by group
    exact toralCentralizer_le_toralRootGroup a'
      (fun w hw => rootCharStabilizer_pairDiagF4_le hk2 hδ hl hδθ hc hw) hmem
  obtain ⟨m, hm, hFix, hconj⟩ := exists_fixed_conj (entrywiseFrobGL .F4 k p e) hvy hMd hlang hu
  exact ⟨m * v, mul_mem (hMJ hm) hv, hFix, hconj⟩

end Descent

end CFSG.ClassicalInvolution.ModelFacts.Levi

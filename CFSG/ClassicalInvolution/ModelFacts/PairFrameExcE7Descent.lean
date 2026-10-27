module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Stab
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLang
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLeviToral
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolution

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def JE7 : Set (Fin (Tag.rank .E7)) := {j | j.val ≠ 0}

theorem iform_thetaE7_single_of_mem {j : Fin (Tag.rank .E7)} (hj : j ∈ JE7) :
    iform thetaE7 (Pi.single j 1) = 0 := by
  rw [iform_thetaE7_single]
  have : j.val ≠ 0 := hj
  simp [this]

theorem mem_parabolicRoots_E7 {σ : Fin (Tag.rank .E7) → ℤ} (hσ : IsRoot .E7 σ)
    (h : iform thetaE7 σ = 0) : σ ∈ parabolicRoots .E7 JE7 := by
  refine ⟨hσ, fun i hi => ?_⟩
  have h0 := (iform_thetaE7_eq_zero_iff σ (mem_rootFinset.2 hσ)).1 h
  have hi0 : i = ⟨0, by decide⟩ := by
    apply Fin.ext
    have : ¬ i.val ≠ 0 := hi
    simpa using this
  rw [hi0]
  exact h0

section Descent

variable {k : Type} [Field k]

theorem iform_eq_zero_of_rootChar_pairDiagE7_eq_one {δ : Fin (Tag.rank .E7) → ℤ} {c : kˣ}
    (hc : ∀ j : ℕ, 1 ≤ j → j ≤ 8 → c ^ j ≠ 1) {σ : Fin (Tag.rank .E7) → ℤ} (hσ : IsRoot .E7 σ)
    (h : rootChar (pairDiagE7 δ c) σ = 1) : iform thetaE7 σ = 0 ∧ (-1 : kˣ) ^ iform δ σ = 1 := by
  rw [rootChar_pairDiagE7] at h
  have b := abs_iform_thetaE7_le σ (mem_rootFinset.2 hσ)
  rw [abs_le] at b
  have hpow : ∀ n : ℤ, (c ^ n) ^ 2 = c ^ (2 * n) := fun n => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
    norm_cast
  have h2 : ((-1 : kˣ) ^ iform δ σ * c ^ iform thetaE7 σ) ^ 2 = 1 := by rw [h]; simp
  rw [mul_pow, neg_one_zpow_sq, one_mul, hpow] at h2
  have hy : iform thetaE7 σ = 0 := by
    have := eq_zero_of_zpow_eq_one hc (m := 2 * iform thetaE7 σ) (N := 8) (by
      rw [abs_le]; omega) h2
    omega
  refine ⟨hy, ?_⟩
  rw [hy, zpow_zero, mul_one] at h
  exact h

theorem rootDiagUnit_thetaDiag_comm_levi_E7 (c : kˣ) {g : ModGL .E7 k}
    (hg : g ∈ parabolicLevi .E7 k JE7) :
    rootDiagUnit .E7 (thetaDiag thetaE7 c) * g = g * rootDiagUnit .E7 (thetaDiag thetaE7 c) := by
  have hle : parabolicLevi .E7 k JE7 ≤
      Subgroup.centralizer {rootDiagUnit .E7 (thetaDiag thetaE7 c)} := by
    obtain ⟨hx, hy, -⟩ := root_diagonal_conjugation .E7 k (thetaDiag thetaE7 c)
    refine sup_le (fun t ht => ?_) ((Subgroup.closure_le _).2 ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (rootDiagUnit_mul_comm_of_mem_torusGroup _ ht).symm
    · rintro _ ⟨j, hj, c', rfl | rfl⟩
      · have h1 : thetaDiag thetaE7 c j = 1 := by
          simp [thetaDiag, iform_thetaE7_single_of_mem hj]
        have h2 := hx j c'
        rw [h1, Units.val_one, one_mul] at h2
        exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h2).symm
      · have h1 : thetaDiag thetaE7 c j = 1 := by
          simp [thetaDiag, iform_thetaE7_single_of_mem hj]
        have h2 := hy j c'
        rw [h1, inv_one, Units.val_one, one_mul] at h2
        exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h2).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm

theorem exists_levi_fixed_conj_E7 (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsRoot .E7 δ)
    (hδθ : iform thetaE7 δ = 0) {y v : ModGL .E7 k} (hv : v ∈ parabolicLevi .E7 k JE7)
    (hFy : entrywiseFrobGL .E7 k p e y = y)
    (hvy : v * y * v⁻¹ = rootDiagUnit .E7 (thetaDiag δ (-1))) :
    ∃ h ∈ parabolicLevi .E7 k JE7, entrywiseFrobGL .E7 k p e h = h ∧
      h * y * h⁻¹ = rootDiagUnit .E7 (thetaDiag δ (-1)) := by
  classical
  have hchar : ringChar k ≠ 2 := by rw [ringChar.eq k p]; exact hp2
  have hk2 : (-1 : kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hchar (by simpa using congrArg Units.val h)
  obtain ⟨c, hc⟩ := exists_unit_pow_ne_one (k := k) 8
  set a' := pairDiagE7 δ c with ha'
  set d := rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)) with hd
  set db := rootDiagUnit .E7 (thetaDiag thetaE7 c) with hdb
  have hsign : ∀ i, thetaDiag δ (-1 : kˣ) i = (1 : kˣ) ∨ thetaDiag δ (-1 : kˣ) i = -1 :=
    fun i => by
      rcases Int.even_or_odd (iform δ (Pi.single i 1)) with h | h
      · left; exact h.neg_one_zpow
      · right; exact h.neg_one_zpow
  have hFd : entrywiseFrobGL .E7 k p e d = d := entrywiseFrobGL_rootDiagUnit_of_sign p e hsign
  have hker : ∀ σ ∈ kernelRoots (rootCharHom a'), IsRoot .E7 σ ∧ iform thetaE7 σ = 0 ∧
      rootChar (thetaDiag δ (-1 : kˣ)) σ = 1 := by
    intro σ hσ
    obtain ⟨hσr, hσ1⟩ := hσ
    obtain ⟨h1, h2⟩ := iform_eq_zero_of_rootChar_pairDiagE7_eq_one hc hσr hσ1
    exact ⟨hσr, h1, by rw [rootChar_thetaDiag]; exact h2⟩
  set M := torusGroup .E7 k ⊔ rootSpan .E7 k (kernelRoots (rootCharHom a')) with hM
  have hMd : ∀ m ∈ M, m * d * m⁻¹ = d := by
    have hle : M ≤ Subgroup.centralizer {d} := by
      refine sup_le (fun t ht => ?_) ?_
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (rootDiagUnit_mul_comm_of_mem_torusGroup _ ht).symm
      · exact rootSpan_le_centralizer (thetaDiag δ (-1 : kˣ))
          (fun σ hσ => ⟨(hker σ hσ).1, (hker σ hσ).2.2⟩)
    intro m hm
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle hm)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hMJ : M ≤ parabolicLevi .E7 k JE7 := by
    refine sup_le (torusGroup_le_parabolicLevi JE7) ?_
    refine iSup₂_le fun σ hσ => rootSubgroup_le_parabolicLevi' ?_
    exact mem_parabolicRoots_E7 (hker σ hσ).1 (hker σ hσ).2.1
  have hlang : ∀ u ∈ M, ∃ m ∈ M, u = m⁻¹ * entrywiseFrobGL .E7 k p e m :=
    fun u hu => exists_eq_inv_mul_frob_torus_sup_rootSpan p he (rootCharHom a') hu
  have hFvJ : entrywiseFrobGL .E7 k p e v ∈ parabolicLevi .E7 k JE7 :=
    baseChangeGL_mem_parabolicLevi (iterateFrobenius k p e) hv
  have hu : entrywiseFrobGL .E7 k p e v * v⁻¹ ∈ M := by
    set u := entrywiseFrobGL .E7 k p e v * v⁻¹ with hudef
    have huJ : u ∈ parabolicLevi .E7 k JE7 := mul_mem hFvJ (inv_mem hv)
    have hF : entrywiseFrobGL .E7 k p e v * y * (entrywiseFrobGL .E7 k p e v)⁻¹ = d := by
      have := congrArg (entrywiseFrobGL .E7 k p e) hvy
      rw [map_mul, map_mul, map_inv, hFy, hFd] at this
      exact this
    have hud : d * u = u * d := by
      have hy' : v⁻¹ * d * v = y := by rw [← hvy]; group
      have h1 : u * d * u⁻¹ = d := by
        calc u * d * u⁻¹ = entrywiseFrobGL .E7 k p e v * (v⁻¹ * d * v) *
              (entrywiseFrobGL .E7 k p e v)⁻¹ := by rw [hudef]; group
          _ = d := by rw [hy', hF]
      calc d * u = (u * d * u⁻¹) * u := by rw [h1]
        _ = u * d := by group
    have hub : db * u = u * db := rootDiagUnit_thetaDiag_comm_levi_E7 c huJ
    have hmem : u ∈ toralCentralizer .E7 k a' := by
      rw [mem_toralCentralizer]
      refine ⟨parabolicSubgroup_le_adjointGroup _ _ _
        (parabolicLevi_le_parabolicSubgroup JE7 huJ), ?_⟩
      have hmul : rootDiagUnit .E7 a' = d * db := rootDiagUnit_mul _ _
      rw [mul_inv_eq_iff_eq_mul, hmul]
      calc d * db * u = d * (db * u) := by group
        _ = d * (u * db) := by rw [hub]
        _ = (d * u) * db := by group
        _ = (u * d) * db := by rw [hud]
        _ = u * (d * db) := by group
    exact toralCentralizer_le_toralRootGroup a'
      (fun w hw => rootCharStabilizer_pairDiagE7_le hk2 hδ hδθ hc hw) hmem
  obtain ⟨m, hm, hFix, hconj⟩ := exists_fixed_conj (entrywiseFrobGL .E7 k p e) hvy hMd hlang hu
  exact ⟨m * v, mul_mem (hMJ hm) hv, hFix, hconj⟩

end Descent

end CFSG.ClassicalInvolution.ModelFacts.Levi

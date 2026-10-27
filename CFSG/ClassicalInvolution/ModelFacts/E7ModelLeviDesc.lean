module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelLeviStab
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLang
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLeviToral
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolution

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem RootSpace CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.ClassicalInvolution.ModelFacts.Levi

variable {k : Type} [Field k]

theorem rootDiagUnit_thetaDiag_comm_levi_G {J : Set (Fin (Tag.rank .E7))}
    {l : Fin (Tag.rank .E7) → ℤ} (hlJ : ∀ j ∈ J, iform l (Pi.single j 1) = 0) (c : kˣ)
    {g : ModGL .E7 k} (hg : g ∈ parabolicLevi .E7 k J) :
    rootDiagUnit .E7 (thetaDiag l c) * g = g * rootDiagUnit .E7 (thetaDiag l c) := by
  have hle : parabolicLevi .E7 k J ≤
      Subgroup.centralizer {rootDiagUnit .E7 (thetaDiag l c)} := by
    obtain ⟨hx, hy, -⟩ := root_diagonal_conjugation .E7 k (thetaDiag l c)
    refine sup_le (fun t ht => ?_) ((Subgroup.closure_le _).2 ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (rootDiagUnit_mul_comm_of_mem_torusGroup _ ht).symm
    · rintro _ ⟨j, hj, c', rfl | rfl⟩
      · have h1 : thetaDiag l c j = 1 := by
          simp [thetaDiag, hlJ j hj]
        have h2 := hx j c'
        rw [h1, Units.val_one, one_mul] at h2
        exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h2).symm
      · have h1 : thetaDiag l c j = 1 := by
          simp [thetaDiag, hlJ j hj]
        have h2 := hy j c'
        rw [h1, inv_one, Units.val_one, one_mul] at h2
        exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h2).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm


section Descent

theorem exists_levi_fixed_conj_G (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) {J : Set (Fin (Tag.rank .E7))}
    {l : Fin (Tag.rank .E7) → ℤ} {B : ℕ} (hlJ : ∀ j ∈ J, iform l (Pi.single j 1) = 0)
    (hB : ∀ σ ∈ rootFinset .E7, |iform l σ| ≤ B)
    (hker : ∀ σ ∈ rootFinset .E7, iform l σ = 0 → σ ∈ parabolicRoots .E7 J)
    {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsRoot .E7 δ) {y v : ModGL .E7 k}
    (hv : v ∈ parabolicLevi .E7 k J) (hFy : entrywiseFrobGL .E7 k p e y = y)
    (hvy : v * y * v⁻¹ = rootDiagUnit .E7 (thetaDiag δ (-1))) :
    ∃ h ∈ parabolicLevi .E7 k J, entrywiseFrobGL .E7 k p e h = h ∧
      h * y * h⁻¹ = rootDiagUnit .E7 (thetaDiag δ (-1)) := by
  classical
  have hchar : ringChar k ≠ 2 := by rw [ringChar.eq k p]; exact hp2
  have hk2 : (-1 : kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hchar (by simpa using congrArg Units.val h)
  obtain ⟨c, hc⟩ := exists_unit_pow_ne_one (k := k) (4 * B)
  set a' := pairDiagG δ l c with ha'
  set d := rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)) with hd
  set db := rootDiagUnit .E7 (thetaDiag l c) with hdb
  have hsign : ∀ i, thetaDiag δ (-1 : kˣ) i = (1 : kˣ) ∨ thetaDiag δ (-1 : kˣ) i = -1 :=
    fun i => by
      rcases Int.even_or_odd (iform δ (Pi.single i 1)) with h | h
      · left; exact h.neg_one_zpow
      · right; exact h.neg_one_zpow
  have hFd : entrywiseFrobGL .E7 k p e d = d := entrywiseFrobGL_rootDiagUnit_of_sign p e hsign
  have hker' : ∀ σ ∈ kernelRoots (rootCharHom a'), IsRoot .E7 σ ∧ iform l σ = 0 ∧
      rootChar (thetaDiag δ (-1 : kˣ)) σ = 1 := by
    intro σ hσ
    obtain ⟨hσr, hσ1⟩ := hσ
    obtain ⟨h1, h2⟩ := iform_eq_zero_of_rootChar_pairDiagG_eq_one hB hc hσr hσ1
    exact ⟨hσr, h1, by rw [rootChar_thetaDiag]; exact h2⟩
  set M := torusGroup .E7 k ⊔ rootSpan .E7 k (kernelRoots (rootCharHom a')) with hM
  have hMd : ∀ m ∈ M, m * d * m⁻¹ = d := by
    have hle : M ≤ Subgroup.centralizer {d} := by
      refine sup_le (fun t ht => ?_) ?_
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (rootDiagUnit_mul_comm_of_mem_torusGroup _ ht).symm
      · exact rootSpan_le_centralizer (thetaDiag δ (-1 : kˣ))
          (fun σ hσ => ⟨(hker' σ hσ).1, (hker' σ hσ).2.2⟩)
    intro m hm
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle hm)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hMJ : M ≤ parabolicLevi .E7 k J := by
    refine sup_le (torusGroup_le_parabolicLevi J) ?_
    refine iSup₂_le fun σ hσ => rootSubgroup_le_parabolicLevi' ?_
    exact hker σ (mem_rootFinset.2 (hker' σ hσ).1) (hker' σ hσ).2.1
  have hlang : ∀ u ∈ M, ∃ m ∈ M, u = m⁻¹ * entrywiseFrobGL .E7 k p e m :=
    fun u hu => exists_eq_inv_mul_frob_torus_sup_rootSpan p he (rootCharHom a') hu
  have hFvJ : entrywiseFrobGL .E7 k p e v ∈ parabolicLevi .E7 k J :=
    baseChangeGL_mem_parabolicLevi (iterateFrobenius k p e) hv
  have hu : entrywiseFrobGL .E7 k p e v * v⁻¹ ∈ M := by
    set u := entrywiseFrobGL .E7 k p e v * v⁻¹ with hudef
    have huJ : u ∈ parabolicLevi .E7 k J := mul_mem hFvJ (inv_mem hv)
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
    have hub : db * u = u * db := rootDiagUnit_thetaDiag_comm_levi_G hlJ c huJ
    have hmem : u ∈ toralCentralizer .E7 k a' := by
      rw [mem_toralCentralizer]
      refine ⟨parabolicSubgroup_le_adjointGroup _ _ _
        (parabolicLevi_le_parabolicSubgroup J huJ), ?_⟩
      have hmul : rootDiagUnit .E7 a' = d * db := rootDiagUnit_mul _ _
      rw [mul_inv_eq_iff_eq_mul, hmul]
      calc d * db * u = d * (db * u) := by group
        _ = d * (u * db) := by rw [hub]
        _ = (d * u) * db := by group
        _ = (u * d) * db := by rw [hud]
        _ = u * (d * db) := by group
    exact toralCentralizer_le_toralRootGroup a'
      (fun w hw => rootCharStabilizer_pairDiagG_le hk2 hB hδ hc hw) hmem
  obtain ⟨m, hm, hFix, hconj⟩ := exists_fixed_conj (entrywiseFrobGL .E7 k p e) hvy hMd hlang hu
  exact ⟨m * v, mul_mem (hMJ hm) hv, hFix, hconj⟩


theorem mem_levi_of_commute_signdiag [Infinite k] (hk : (-1 : kˣ) ≠ 1)
    {J J' : Set (Fin (Tag.rank .E7))} {l : Fin (Tag.rank .E7) → ℤ} {B : ℕ}
    (hlJ : ∀ j ∈ J, iform l (Pi.single j 1) = 0) (hB : ∀ σ ∈ rootFinset .E7, |iform l σ| ≤ B)
    {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsRoot .E7 δ)
    (hker : ∀ σ ∈ rootFinset .E7, iform l σ = 0 → Even (iform δ σ) →
      σ ∈ parabolicRoots .E7 J')
    {y : ModGL .E7 k} (hyG : y ∈ adjointGroup .E7 k) (hyJ : y ∈ parabolicLevi .E7 k J)
    (hyd : y * rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)) =
      rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)) * y) :
    y ∈ parabolicLevi .E7 k J' := by
  obtain ⟨c, hc⟩ := exists_unit_pow_ne_one (k := k) (4 * B)
  have hmem : y ∈ toralCentralizer .E7 k (pairDiagG δ l c) := by
    rw [mem_toralCentralizer]
    refine ⟨hyG, ?_⟩
    have hmul : rootDiagUnit .E7 (pairDiagG δ l c) =
        rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)) * rootDiagUnit .E7 (thetaDiag l c) :=
      rootDiagUnit_mul _ _
    have hub : rootDiagUnit .E7 (thetaDiag l c) * y = y * rootDiagUnit .E7 (thetaDiag l c) :=
      rootDiagUnit_thetaDiag_comm_levi_G hlJ c hyJ
    rw [mul_inv_eq_iff_eq_mul, hmul]
    calc rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)) * rootDiagUnit .E7 (thetaDiag l c) * y =
        rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)) * (rootDiagUnit .E7 (thetaDiag l c) * y) := by
          group
      _ = rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)) * (y * rootDiagUnit .E7 (thetaDiag l c)) := by
          rw [hub]
      _ = (rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)) * y) * rootDiagUnit .E7 (thetaDiag l c) := by
          group
      _ = (y * rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ))) * rootDiagUnit .E7 (thetaDiag l c) := by
          rw [hyd]
      _ = y * (rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)) * rootDiagUnit .E7 (thetaDiag l c)) := by
          group
  have hM := toralCentralizer_le_toralRootGroup (pairDiagG δ l c)
    (fun w hw => rootCharStabilizer_pairDiagG_le hk hB hδ hc hw) hmem
  refine (sup_le (torusGroup_le_parabolicLevi J') (iSup₂_le fun σ hσ =>
    rootSubgroup_le_parabolicLevi' ?_)) hM
  obtain ⟨hσr, hσ1⟩ := hσ
  obtain ⟨h1, h2⟩ := iform_eq_zero_of_rootChar_pairDiagG_eq_one hB hc hσr hσ1
  have h3 : Even (iform δ σ) := by
    by_contra hodd
    rw [Int.not_even_iff_odd] at hodd
    rw [hodd.neg_one_zpow] at h2
    exact hk h2
  exact hker σ (mem_rootFinset.2 hσr) h1 h3

end Descent

end CFSG.ClassicalInvolution.ModelFacts.E7Model

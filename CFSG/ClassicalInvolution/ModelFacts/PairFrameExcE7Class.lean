module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Levi
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Class

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Sign

@[expose] def e7SignChar (δ : Fin (Tag.rank .E7) → ℤ) :
    Multiplicative (Fin (Tag.rank .E7) → ℤ) →* ℤˣ where
  toFun v := (-1 : ℤˣ) ^ iform δ (Multiplicative.toAdd v)
  map_one' := by
    have : iform δ (0 : Fin (Tag.rank .E7) → ℤ) = 0 := by simp [iform]
    simp [this]
  map_mul' u v := by
    rw [toAdd_mul, iform_add_right, zpow_add]

theorem signCharTuple_e7SignChar {k : Type} [Field k] (δ : Fin (Tag.rank .E7) → ℤ) :
    signCharTuple (k := k) (e7SignChar δ) = thetaDiag δ (-1 : kˣ) := by
  funext i
  have h : intUnitsMap k (-1 : ℤˣ) = -1 := Units.ext (by simp [intUnitsMap])
  simp only [signCharTuple, e7SignChar, thetaDiag, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
    map_zpow, h]

theorem thetaDiag_neg_E7 {k : Type} [Field k] (δ : Fin (Tag.rank .E7) → ℤ) :
    thetaDiag (-δ) (-1 : kˣ) = thetaDiag δ (-1 : kˣ) := by
  funext i
  have h1 : iform (-δ) (Pi.single i 1) = -iform δ (Pi.single i 1) := by
    rw [show (-δ : Fin (Tag.rank .E7) → ℤ) = (-1 : ℤ) • δ by simp, iform_smul_left]
    ring
  simp only [thetaDiag, h1]
  rcases Int.even_or_odd (iform δ (Pi.single i 1)) with he | ho
  · rw [he.neg_one_zpow, (he.neg).neg_one_zpow]
  · rw [ho.neg_one_zpow, (ho.neg).neg_one_zpow]

end Sign

section Class

variable {k : Type} [Field k] [IsAlgClosed k]

theorem exists_root_of_conj_thetaDiag_E7 (hk : ringChar k ≠ 2) {a : Fin (Tag.rank .E7) → kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) {g : ModGL .E7 k} (hg : g ∈ adjointGroup .E7 k)
    (hga : g * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ)) * g⁻¹ = rootDiagUnit .E7 a) :
    ∃ δ, IsRoot .E7 δ ∧ a = thetaDiag δ (-1 : kˣ) := by
  have ha' := eq_signCharTuple_of_sign hk ha
  rw [← signCharTuple_e7SignChar thetaE7 (k := k)] at hga
  rw [ha'] at hga
  obtain ⟨t, ht⟩ := (exists_conj_rootDiagUnit_signCharTuple_iff hk (e7SignChar thetaE7)
    (maskChar (signTupleBits a))).1 ⟨g, hg, hga⟩
  refine ⟨t • thetaE7, IsRoot.smul isRoot_thetaE7 t, ?_⟩
  rw [ha']
  funext i
  rw [← signCharTuple_e7SignChar (t • thetaE7) (k := k)]
  simp only [signCharTuple]
  congr 1
  rw [ht (Pi.single i 1)]
  simp only [e7SignChar, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  have := iform_smul_smul t thetaE7 (t⁻¹ • (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ))
  rw [smul_inv_smul] at this
  rw [this]

end Class

section Glue

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem exists_levi_fixed_conj_or_eq_thetaDiag_E7
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) (hp2 : p ≠ 2) {e : ℕ}
    (he : 1 ≤ e) {y g : ModGL .E7 k} (hy : y ∈ parabolicLevi .E7 k JE7) (hy2 : y ^ 2 = 1)
    (hFy : entrywiseFrobGL .E7 k p e y = y) (hg : g ∈ adjointGroup .E7 k)
    (hgy : g * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ)) * g⁻¹ = y)
    (hyU : y * rootSL2 .E7 k thetaE7 (uSL 1) = rootSL2 .E7 k thetaE7 (uSL 1) * y) :
    y = rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ)) ∨
      ∃ δ, IsRoot .E7 δ ∧ iform thetaE7 δ = 0 ∧ ∃ h ∈ parabolicLevi .E7 k JE7,
        entrywiseFrobGL .E7 k p e h = h ∧
          h * y * h⁻¹ = rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)) := by
  have hk : ringChar k ≠ 2 := by rw [ringChar.eq k p]; exact hp2
  obtain ⟨v, hv, a, ha, hva⟩ := exists_levi_conj_eq_rootDiagUnit hp2 k halg hy hy2
  have hvg : v * g ∈ adjointGroup .E7 k :=
    mul_mem (parabolicSubgroup_le_adjointGroup _ _ _ (parabolicLevi_le_parabolicSubgroup JE7 hv)) hg
  obtain ⟨δ, hδ, rfl⟩ := exists_root_of_conj_thetaDiag_E7 hk ha hvg
    (by rw [← hva, ← hgy]; group)
  obtain ⟨l, hu, -⟩ := exists_levi_conj_rootSL2_thetaE7 hv
  have hinj : Function.Injective (rootSL2 .E7 k thetaE7) :=
    ((exceptional_Lang_root_rank_one_data .E7 k thetaE7).2.2.2.2.2.2.2.1 hk).1
  have hχ : rootChar (thetaDiag δ (-1 : kˣ)) thetaE7 = 1 := by
    have h1 : rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)) *
          rootSL2 .E7 k thetaE7 (uSL ((l : k) * 1)) =
        rootSL2 .E7 k thetaE7 (uSL ((l : k) * 1)) * rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)) := by
      rw [← hu 1, ← hva]
      calc v * y * v⁻¹ * (v * rootSL2 .E7 k thetaE7 (uSL 1) * v⁻¹) =
          v * (y * rootSL2 .E7 k thetaE7 (uSL 1)) * v⁻¹ := by group
        _ = v * (rootSL2 .E7 k thetaE7 (uSL 1) * y) * v⁻¹ := by rw [hyU]
        _ = _ := by group
    have h2 := (rootDiagUnit_conj_rootSL2 (thetaDiag δ (-1 : kˣ)) isRoot_thetaE7
      ((l : k) * 1)).1
    rw [mul_inv_eq_iff_eq_mul.2 h1] at h2
    have h3 := uSL_injective_of_field (hinj h2)
    have hl : (l : k) * 1 ≠ 0 := by simp
    have h4 : ((rootChar (thetaDiag δ (-1 : kˣ)) thetaE7 : kˣ) : k) = 1 := by
      have := mul_right_cancel₀ hl (h3.symm.trans (one_mul _).symm)
      exact this
    exact Units.ext h4
  have hev : Even (iform thetaE7 δ) := by
    rw [iform_comm]
    refine even_of_neg_one_zpow_eq_one hk ?_
    rw [← rootChar_thetaDiag]
    exact hχ
  rcases eq_or_iform_eq_zero_of_even_E7 hδ hev with rfl | rfl | h0
  ·
    left
    have hc := rootDiagUnit_thetaDiag_comm_levi_E7 (-1 : kˣ) hv
    calc y = v⁻¹ * (v * y * v⁻¹) * v := by group
      _ = v⁻¹ * (rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ)) * v) := by rw [hva]; group
      _ = v⁻¹ * (v * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ))) := by rw [hc]
      _ = _ := by group
  · left
    have hc := rootDiagUnit_thetaDiag_comm_levi_E7 (-1 : kˣ) hv
    rw [thetaDiag_neg_E7] at hva
    calc y = v⁻¹ * (v * y * v⁻¹) * v := by group
      _ = v⁻¹ * (rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ)) * v) := by rw [hva]; group
      _ = v⁻¹ * (v * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ))) := by rw [hc]
      _ = _ := by group
  · right
    exact ⟨δ, hδ, h0, exists_levi_fixed_conj_E7 p hp2 he hδ h0 hv hFy hva⟩

end Glue

end CFSG.ClassicalInvolution.ModelFacts.Levi

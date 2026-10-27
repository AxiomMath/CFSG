module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Levi
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Class

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Sign

@[expose] def f4SignChar (δ : Fin (Tag.rank .F4) → ℤ) (hev : ∀ v, Even (iform δ v)) :
    Multiplicative (Fin (Tag.rank .F4) → ℤ) →* ℤˣ where
  toFun v := (-1 : ℤˣ) ^ (iform δ (Multiplicative.toAdd v) / 2)
  map_one' := by
    have : iform δ (0 : Fin (Tag.rank .F4) → ℤ) = 0 := by simp [iform]
    simp [this]
  map_mul' u v := by
    rw [toAdd_mul, iform_add_right, ← zpow_add]
    congr 1
    obtain ⟨a, ha⟩ := hev (Multiplicative.toAdd u)
    obtain ⟨b, hb⟩ := hev (Multiplicative.toAdd v)
    omega

theorem signCharTuple_f4SignChar {k : Type} [Field k] (δ : Fin (Tag.rank .F4) → ℤ)
    (hev : ∀ v, Even (iform δ v)) :
    signCharTuple (k := k) (f4SignChar δ hev) = corootDiagF4 δ (-1 : kˣ) := by
  funext i
  have h : intUnitsMap k (-1 : ℤˣ) = -1 := Units.ext (by simp [intUnitsMap])
  simp only [signCharTuple, f4SignChar, corootDiagF4, MonoidHom.coe_mk, OneHom.coe_mk,
    toAdd_ofAdd, map_zpow, h]

theorem corootDiagF4_neg {k : Type} [Field k] (δ : Fin (Tag.rank .F4) → ℤ)
    (hev : ∀ v, Even (iform δ v)) :
    corootDiagF4 (-δ) (-1 : kˣ) = corootDiagF4 δ (-1 : kˣ) := by
  funext i
  have h1 : iform (-δ) (Pi.single i 1) = -iform δ (Pi.single i 1) := by
    rw [show (-δ : Fin (Tag.rank .F4) → ℤ) = (-1 : ℤ) • δ by simp, iform_smul_left]
    ring
  obtain ⟨a, ha⟩ := hev (Pi.single i 1)
  simp only [corootDiagF4, h1]
  have h2 : -iform δ (Pi.single i 1) / 2 = -(iform δ (Pi.single i 1) / 2) := by omega
  rw [h2]
  rcases Int.even_or_odd (iform δ (Pi.single i 1) / 2) with he | ho
  · rw [he.neg_one_zpow, (he.neg).neg_one_zpow]
  · rw [ho.neg_one_zpow, (ho.neg).neg_one_zpow]

end Sign

section Class

variable {k : Type} [Field k] [IsAlgClosed k]

theorem exists_root_of_conj_corootDiagF4 (hk : ringChar k ≠ 2) {a : Fin (Tag.rank .F4) → kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) {g : ModGL .F4 k} (hg : g ∈ adjointGroup .F4 k)
    (hga : g * rootDiagUnit .F4 (corootDiagF4 thetaF4 (-1 : kˣ)) * g⁻¹ = rootDiagUnit .F4 a) :
    ∃ δ, IsRoot .F4 δ ∧ iform δ δ = 4 ∧ a = corootDiagF4 δ (-1 : kˣ) := by
  have hevθ := even_iform_of_long_F4 isRoot_thetaF4 iform_thetaF4_self
  have ha' := eq_signCharTuple_of_sign hk ha
  rw [← signCharTuple_f4SignChar thetaF4 hevθ (k := k)] at hga
  rw [ha'] at hga
  obtain ⟨t, ht⟩ := (exists_conj_rootDiagUnit_signCharTuple_iff hk (f4SignChar thetaF4 hevθ)
    (maskChar (signTupleBits a))).1 ⟨g, hg, hga⟩
  have hδroot : IsRoot .F4 (t • thetaF4) := IsRoot.smul isRoot_thetaF4 t
  have hδl : iform (t • thetaF4) (t • thetaF4) = 4 := by
    rw [iform_smul_smul, iform_thetaF4_self]
  refine ⟨t • thetaF4, hδroot, hδl, ?_⟩
  rw [ha']
  funext i
  rw [← signCharTuple_f4SignChar (t • thetaF4) (even_iform_of_long_F4 hδroot hδl) (k := k)]
  simp only [signCharTuple]
  congr 1
  rw [ht (Pi.single i 1)]
  simp only [f4SignChar, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  have := iform_smul_smul t thetaF4 (t⁻¹ • (Pi.single i 1 : Fin (Tag.rank .F4) → ℤ))
  rw [smul_inv_smul] at this
  rw [this]

end Class

section Glue

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem exists_levi_fixed_conj_or_eq_corootDiagF4
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) (hp2 : p ≠ 2) {e : ℕ}
    (he : 1 ≤ e) {y g : ModGL .F4 k} (hy : y ∈ parabolicLevi .F4 k JF4) (hy2 : y ^ 2 = 1)
    (hFy : entrywiseFrobGL .F4 k p e y = y) (hg : g ∈ adjointGroup .F4 k)
    (hgy : g * rootDiagUnit .F4 (corootDiagF4 thetaF4 (-1 : kˣ)) * g⁻¹ = y)
    (hyU : y * rootSL2 .F4 k thetaF4 (uSL 1) = rootSL2 .F4 k thetaF4 (uSL 1) * y) :
    y = rootDiagUnit .F4 (corootDiagF4 thetaF4 (-1 : kˣ)) ∨
      ∃ δ, IsRoot .F4 δ ∧ iform δ δ = 4 ∧ iform thetaF4 δ = 0 ∧
        ∃ h ∈ parabolicLevi .F4 k JF4, entrywiseFrobGL .F4 k p e h = h ∧
          h * y * h⁻¹ = rootDiagUnit .F4 (corootDiagF4 δ (-1 : kˣ)) := by
  have hk : ringChar k ≠ 2 := by rw [ringChar.eq k p]; exact hp2
  obtain ⟨v, hv, a, ha, hva⟩ := exists_levi_conj_eq_rootDiagUnit hp2 k halg hy hy2
  have hvg : v * g ∈ adjointGroup .F4 k :=
    mul_mem (parabolicSubgroup_le_adjointGroup _ _ _ (parabolicLevi_le_parabolicSubgroup JF4 hv)) hg
  obtain ⟨δ, hδ, hδl, rfl⟩ := exists_root_of_conj_corootDiagF4 hk ha hvg
    (by rw [← hva, ← hgy]; group)
  have hδev := even_iform_of_long_F4 hδ hδl
  obtain ⟨l, hu, -⟩ := exists_levi_conj_rootSL2_thetaF4 hv
  have hinj : Function.Injective (rootSL2 .F4 k thetaF4) :=
    ((exceptional_Lang_root_rank_one_data .F4 k thetaF4).2.2.2.2.2.2.2.1 hk).1
  have hχ : rootChar (corootDiagF4 δ (-1 : kˣ)) thetaF4 = 1 := by
    have h1 : rootDiagUnit .F4 (corootDiagF4 δ (-1 : kˣ)) *
          rootSL2 .F4 k thetaF4 (uSL ((l : k) * 1)) =
        rootSL2 .F4 k thetaF4 (uSL ((l : k) * 1)) *
          rootDiagUnit .F4 (corootDiagF4 δ (-1 : kˣ)) := by
      rw [← hu 1, ← hva]
      calc v * y * v⁻¹ * (v * rootSL2 .F4 k thetaF4 (uSL 1) * v⁻¹) =
          v * (y * rootSL2 .F4 k thetaF4 (uSL 1)) * v⁻¹ := by group
        _ = v * (rootSL2 .F4 k thetaF4 (uSL 1) * y) * v⁻¹ := by rw [hyU]
        _ = _ := by group
    have h2 := (rootDiagUnit_conj_rootSL2 (corootDiagF4 δ (-1 : kˣ)) isRoot_thetaF4
      ((l : k) * 1)).1
    rw [mul_inv_eq_iff_eq_mul.2 h1] at h2
    have h3 := uSL_injective_of_field (hinj h2)
    have hl : (l : k) * 1 ≠ 0 := by simp
    have h4 : ((rootChar (corootDiagF4 δ (-1 : kˣ)) thetaF4 : kˣ) : k) = 1 := by
      have := mul_right_cancel₀ hl (h3.symm.trans (one_mul _).symm)
      exact this
    exact Units.ext h4
  have hev : Even (iform thetaF4 δ / 2) := by
    rw [iform_comm]
    refine even_of_neg_one_zpow_eq_one hk ?_
    rw [← rootChar_corootDiagF4 hδ hδl]
    exact hχ
  rcases eq_or_iform_eq_zero_of_even_F4 hδ hev with rfl | rfl | h0
  ·
    left
    have hc := rootDiagUnit_corootDiagF4_comm_levi (-1 : kˣ) hv
    calc y = v⁻¹ * (v * y * v⁻¹) * v := by group
      _ = v⁻¹ * (rootDiagUnit .F4 (corootDiagF4 thetaF4 (-1 : kˣ)) * v) := by rw [hva]; group
      _ = v⁻¹ * (v * rootDiagUnit .F4 (corootDiagF4 thetaF4 (-1 : kˣ))) := by rw [hc]
      _ = _ := by group
  · left
    have hc := rootDiagUnit_corootDiagF4_comm_levi (-1 : kˣ) hv
    rw [corootDiagF4_neg thetaF4 (even_iform_of_long_F4 isRoot_thetaF4 iform_thetaF4_self)] at hva
    calc y = v⁻¹ * (v * y * v⁻¹) * v := by group
      _ = v⁻¹ * (rootDiagUnit .F4 (corootDiagF4 thetaF4 (-1 : kˣ)) * v) := by rw [hva]; group
      _ = v⁻¹ * (v * rootDiagUnit .F4 (corootDiagF4 thetaF4 (-1 : kˣ))) := by rw [hc]
      _ = _ := by group
  · right
    exact ⟨δ, hδ, hδl, h0, exists_levi_fixed_conj_F4 p hp2 he hδ hδl h0 hv hFy hva⟩

end Glue

end CFSG.ClassicalInvolution.ModelFacts.Levi

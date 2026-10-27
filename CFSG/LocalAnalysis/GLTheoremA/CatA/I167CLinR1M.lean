module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CLinR1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open Matrix

private noncomputable def i167CLin_r_one_aux1 (K : Type) [Field K] {d : ℕ} :
    GL (Fin d) K ≃* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  (Matrix.GeneralLinearGroup.toLin (n := Fin d) (R := K)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin d → K))

private lemma i167CLin_r_one_aux2 {K : Type} [Field K] {d : ℕ}
    (A : GL (Fin d) K) (v : Fin d → K) :
    (i167CLin_r_one_aux1 K A) v = (A : Matrix (Fin d) (Fin d) K) *ᵥ v := by
  simp [i167CLin_r_one_aux1, Matrix.mulVecLin_apply]

private lemma i167CLin_r_one_aux3 {K : Type} [Field K] {d : ℕ} (g : GL (Fin d) K) :
    (i167CLin_r_one_aux1 K g : (Fin d → K) →ₗ[K] (Fin d → K))
        = Matrix.toLin' (g : Matrix (Fin d) (Fin d) K) ∧
      LinearMap.ker ((i167CLin_r_one_aux1 K g : (Fin d → K) →ₗ[K] (Fin d → K)) - 1)
        = LinearMap.ker (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1)) := by
  have hψg : (i167CLin_r_one_aux1 K g : (Fin d → K) →ₗ[K] (Fin d → K))
      = Matrix.toLin' (g : Matrix (Fin d) (Fin d) K) := by
    refine LinearMap.ext fun v => ?_
    simpa [Matrix.toLin'_apply] using i167CLin_r_one_aux2 g v
  refine ⟨hψg, ?_⟩
  have hsub : Matrix.toLin' (g : Matrix (Fin d) (Fin d) K) - 1
      = Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1) := by
    rw [map_sub, Matrix.toLin'_one]
    congr 1
  rw [hψg, hsub]

private lemma i167CLin_r_one_aux4 {K : Type} [Field K] {d : ℕ}
    {Ã : Subgroup (GL (Fin d) K)} (hÃ : IsElemAbelian 3 Ã) :
    IsElemAbelian 3 (Ã.map (i167CLin_r_one_aux1 K).toMonoidHom) := by
  haveI : IsMulCommutative Ã := hÃ.1
  constructor
  · rw [isMulCommutative_iff]
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hcomm : (a : GL (Fin d) K) * ↑b = ↑b * ↑a := by
      simpa using congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Ã) ⟨b, hb⟩)
    rw [← map_mul, ← map_mul, hcomm]
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    simpa using congrArg (i167CLin_r_one_aux1 K) (hÃ.2 a ha)

private lemma i167CLin_r_one_aux5 {K : Type} [Field K] {d : ℕ}
    {Ã : Subgroup (GL (Fin d) K)}
    (hmax : ∀ s : GL (Fin d) K, s ^ 3 = 1 → (∀ a ∈ Ã, a * s = s * a) → s ∈ Ã) :
    ∀ s : (Fin d → K) ≃ₗ[K] (Fin d → K), s ^ 3 = 1 →
      (∀ a ∈ Ã.map (i167CLin_r_one_aux1 K).toMonoidHom, a * s = s * a) →
      s ∈ Ã.map (i167CLin_r_one_aux1 K).toMonoidHom := by
  intro s hs3 hcomm
  have hs3' : ((i167CLin_r_one_aux1 K).symm s) ^ 3 = 1 := by
    apply (i167CLin_r_one_aux1 K).injective
    simpa using hs3
  have hcomm' : ∀ a ∈ Ã,
      a * (i167CLin_r_one_aux1 K).symm s = (i167CLin_r_one_aux1 K).symm s * a := by
    intro a ha
    apply (i167CLin_r_one_aux1 K).injective
    have h := hcomm (i167CLin_r_one_aux1 K a) (Subgroup.mem_map_of_mem _ ha)
    simpa using h
  rw [show s = i167CLin_r_one_aux1 K ((i167CLin_r_one_aux1 K).symm s) from
    ((i167CLin_r_one_aux1 K).apply_symm_apply s).symm]
  exact Subgroup.mem_map_of_mem _ (hmax _ hs3' hcomm')

private lemma i167CLin_r_one_aux6 {K : Type} [Field K] {d : ℕ}
    {Ã : Subgroup (GL (Fin d) K)} {g : GL (Fin d) K}
    (hCA : ∀ a ∈ Ã, (∀ v ∈ LinearMap.ker (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1)),
      (a : Matrix (Fin d) (Fin d) K) *ᵥ v = v) → a ∈ Subgroup.zpowers g) :
    ∀ a ∈ Ã.map (i167CLin_r_one_aux1 K).toMonoidHom,
      (∀ v, i167CLin_r_one_aux1 K g v = v → a v = v) →
      a ∈ Subgroup.zpowers (i167CLin_r_one_aux1 K g) := by
  intro a ha hfix
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  have hker := (i167CLin_r_one_aux3 g).2
  have hfix' : ∀ v ∈ LinearMap.ker (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1)),
      (a' : Matrix (Fin d) (Fin d) K) *ᵥ v = v := by
    intro v hv
    have hmem : v ∈ LinearMap.ker
        ((i167CLin_r_one_aux1 K g : (Fin d → K) →ₗ[K] (Fin d → K)) - 1) := by
      rw [hker]; exact hv
    have hvfix : i167CLin_r_one_aux1 K g v = v := by
      have h0 : ((i167CLin_r_one_aux1 K g : (Fin d → K) →ₗ[K] (Fin d → K)) - 1) v = 0 := hmem
      simpa [LinearMap.sub_apply, sub_eq_zero] using h0
    have hvfix' := hfix v hvfix
    simpa [i167CLin_r_one_aux2] using hvfix'
  have ha'z : a' ∈ Subgroup.zpowers g := hCA a' ha' hfix'
  have hmap : i167CLin_r_one_aux1 K a' ∈ (Subgroup.zpowers g).map (i167CLin_r_one_aux1 K).toMonoidHom :=
    Subgroup.mem_map_of_mem _ ha'z
  rwa [MonoidHom.map_zpowers] at hmap

theorem i167CLin_r_one {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {d : ℕ}
    (Ã : Subgroup (GL (Fin d) K)) (hÃ : IsElemAbelian 3 Ã)
    (hmax : ∀ s : GL (Fin d) K, s ^ 3 = 1 → (∀ a ∈ Ã, a * s = s * a) → s ∈ Ã) {g : GL (Fin d) K}
    (hgÃ : g ∈ Ã) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    (hCA : ∀ a ∈ Ã, (∀ v ∈ LinearMap.ker (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1)),
      (a : Matrix (Fin d) (Fin d) K) *ᵥ v = v) → a ∈ Subgroup.zpowers g) :
    d = Module.finrank K (LinearMap.ker (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1))) + 2 := by
  let H : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)) := Ã.map (i167CLin_r_one_aux1 K).toMonoidHom
  have hH : IsElemAbelian 3 H := i167CLin_r_one_aux4 hÃ
  have hmaxH := i167CLin_r_one_aux5 hmax
  have hCAH := i167CLin_r_one_aux6 hCA
  have hmem : i167CLin_r_one_aux1 K g ∈ H := Subgroup.mem_map_of_mem _ hgÃ
  have hpow : (i167CLin_r_one_aux1 K g) ^ 3 = 1 := by
    simpa using congrArg (i167CLin_r_one_aux1 K) hg3
  have hne : i167CLin_r_one_aux1 K g ≠ 1 :=
    fun h => hg1 ((i167CLin_r_one_aux1 K).injective (by simpa using h))
  have key := i167CLin_r_one_module hK H hH hmaxH hmem hpow hne hCAH
  rw [Module.finrank_fin_fun, (i167CLin_r_one_aux3 g).2] at key
  exact key

end CFSG.LocalAnalysis.GLTheoremA.I167

end

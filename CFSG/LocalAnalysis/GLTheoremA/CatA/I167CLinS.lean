module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CDefs

import CFSG.Open.StatedZModTwo
import CFSG.RankThree.PartTwo.Sec21.HeringFFLOut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4 Matrix

theorem i167CLin_gl_iso {S : Type} [Group S] {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {d : ℕ}
    (e : S ≃* LargeEvenProj (StatedSL d K)) :
    ∃ φ : GL (Fin d) K ≃* S, ∀ x : GL (Fin d) K, ∃ hx : x ∈ StatedSL d K,
      e (φ x) = LargeEvenProjMk (StatedSL d K) ⟨x, hx⟩ := by
  have hSL : StatedSL d K = ⊤ := statedSL_eq_top_of_card_two hK d
  have hSc : StatedScalars (Fin d) K = ⊥ := statedScalars_eq_bot_of_card_two hK (Fin d)
  have hx0 : ∀ x : GL (Fin d) K, x ∈ StatedSL d K := fun x => by rw [hSL]; trivial
  have hker : (LargeEvenProjMk (StatedSL d K)).ker = ⊥ := by
    rw [show LargeEvenProjMk (StatedSL d K) =
        QuotientGroup.mk' ((StatedScalars (Fin d) K).subgroupOf (StatedSL d K)) from rfl,
      QuotientGroup.ker_mk', hSc, Subgroup.bot_subgroupOf]
  have hπinj : Function.Injective (LargeEvenProjMk (StatedSL d K)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have hπsurj : Function.Surjective (LargeEvenProjMk (StatedSL d K)) :=
    QuotientGroup.mk'_surjective _
  let f : GL (Fin d) K →* LargeEvenProj (StatedSL d K) :=
    MonoidHom.mk' (fun x => LargeEvenProjMk (StatedSL d K) ⟨x, hx0 x⟩)
      (fun x y => map_mul (LargeEvenProjMk (StatedSL d K)) ⟨x, hx0 x⟩ ⟨y, hx0 y⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact congrArg (fun z : ↥(StatedSL d K) => (z : GL (Fin d) K)) (hπinj hxy)
    · intro y
      obtain ⟨h, hh⟩ := hπsurj y
      exact ⟨h, by rw [← hh]; rfl⟩
  refine ⟨(MulEquiv.ofBijective f hf).trans e.symm, fun x => ⟨hx0 x, ?_⟩⟩
  show e (e.symm (f x)) = LargeEvenProjMk (StatedSL d K) ⟨x, hx0 x⟩
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem i167CLin_bb_inner {S : Type} [Group S] {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {d : ℕ}
    (hd : 3 ≤ d) (e : S ≃* LargeEvenProj (StatedSL d K)) {β : MulAut S} {m : ℕ} (hm : Odd m) (hβ : β ^ m = 1) :
    ∃ s : S, β = MulAut.conj s := by
  let ε : S ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL d K :=
    e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj d K).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL d K))
  have hpow : (MulAut.congr ε β) ^ m = 1 := by
    rw [← map_pow, hβ, map_one]
  obtain ⟨y, hy⟩ :=
    CFSG.RankThree.PartTwo.Sec21.Hering214.inner_of_pow_odd_eq_one (K := K) hK hd hm hpow
  exact ⟨ε.symm y, (MulAut.congr ε).injective (by
    rw [hy, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj,
      MulEquiv.apply_symm_apply])⟩

private lemma i167CLin_tilde_basic_aux1 {S : Type} [Group S] (hcen : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  rw [MonoidHom.mem_ker] at hz
  rw [← hcen, Subgroup.mem_center_iff]
  intro g
  have h := congrArg (fun φ : MulAut S => φ g) hz
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc g * z = z * g * z⁻¹ * z := by rw [h]
    _ = z * g := by group

private lemma i167CLin_tilde_basic_aux2 {S : Type} [Group S]
    {α : MulAut S} {K : Type} [Field K] [Finite K] {d : ℕ}
    (e : S ≃* LargeEvenProj (StatedSL d K)) (φ : GL (Fin d) K ≃* S)
    (hφ : ∀ x : GL (Fin d) K, ∃ hx : x ∈ StatedSL d K, e (φ x) = LargeEvenProjMk (StatedSL d K) ⟨x, hx⟩)
    (g : GL (Fin d) K)
    (hgr : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = g * (h : GL (Fin d) K) * g⁻¹ →
      MulAut.congr e α (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h') :
    α = MulAut.conj (φ g) := by
  obtain ⟨hg, hφg⟩ := hφ g
  ext s
  obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective
    (N := (LargeEvenScalars (Fin d) K).subgroupOf (StatedSL d K)) (e s)
  have hmem : (g * (h : GL (Fin d) K) * g⁻¹) ∈ StatedSL d K :=
    mul_mem (mul_mem hg h.2) (inv_mem hg)
  have hgr' := hgr h ⟨g * (h : GL (Fin d) K) * g⁻¹, hmem⟩ rfl
  have he1 : e (α s) =
      LargeEvenProjMk (StatedSL d K) ⟨g * (h : GL (Fin d) K) * g⁻¹, hmem⟩ := by
    rw [← hgr', hh]
    simp [MulAut.congr]
  have he2 : e ((φ g) * s * (φ g)⁻¹) =
      LargeEvenProjMk (StatedSL d K) ⟨g * (h : GL (Fin d) K) * g⁻¹, hmem⟩ := by
    calc e ((φ g) * s * (φ g)⁻¹)
        = e (φ g) * e s * (e (φ g))⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = LargeEvenProjMk (StatedSL d K) ⟨g, hg⟩ * LargeEvenProjMk (StatedSL d K) h *
            (LargeEvenProjMk (StatedSL d K) ⟨g, hg⟩)⁻¹ := by rw [hφg, hh]
      _ = LargeEvenProjMk (StatedSL d K) (⟨g, hg⟩ * h * ⟨g, hg⟩⁻¹) := by
            rw [← map_inv, ← map_mul, ← map_mul]
      _ = LargeEvenProjMk (StatedSL d K) ⟨g * (h : GL (Fin d) K) * g⁻¹, hmem⟩ := by
            rw [show (⟨g, hg⟩ * h * ⟨g, hg⟩⁻¹ : ↥(StatedSL d K)) =
              ⟨g * (h : GL (Fin d) K) * g⁻¹, hmem⟩ from Subtype.ext rfl]
  have hαs : α s = (φ g) * s * (φ g)⁻¹ := e.injective (he1.trans he2.symm)
  simpa [MulAut.conj_apply] using hαs

theorem i167CLin_tilde_basic {S : Type} [Group S] (hcen : Subgroup.center S = ⊥) {Bb : Subgroup (MulAut S)}
    {α : MulAut S} (hBb : IsElemAbelian 3 Bb) (hαB : α ∈ Bb) {K : Type} [Field K] [Finite K] {d : ℕ}
    (e : S ≃* LargeEvenProj (StatedSL d K)) (φ : GL (Fin d) K ≃* S)
    (hφ : ∀ x : GL (Fin d) K, ∃ hx : x ∈ StatedSL d K, e (φ x) = LargeEvenProjMk (StatedSL d K) ⟨x, hx⟩)
    (g : GL (Fin d) K)
    (hgr : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = g * (h : GL (Fin d) K) * g⁻¹ →
      MulAut.congr e α (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h')
    (Ã : Subgroup (GL (Fin d) K)) (hÃ : ∀ x, x ∈ Ã ↔ (MulAut.conj (φ x) : MulAut S) ∈ Bb) :
    IsElemAbelian 3 Ã ∧ g ∈ Ã ∧ α = MulAut.conj (φ g) := by
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := i167CLin_tilde_basic_aux1 hcen
  have hα : α = MulAut.conj (φ g) := i167CLin_tilde_basic_aux2 e φ hφ g hgr
  have hinjψ : Function.Injective
      (fun x : GL (Fin d) K => (MulAut.conj (φ x) : MulAut S)) := hinj.comp φ.injective
  have hinjψ' : Function.Injective
      ((MulAut.conj : S →* MulAut S).comp (φ.toMonoidHom.comp Ã.subtype)) :=
    hinj.comp (φ.injective.comp Subtype.coe_injective)
  refine ⟨?_, ?_, hα⟩
  · unfold IsElemAbelian
    refine ⟨?_, ?_⟩
    · haveI : IsMulCommutative Bb := hBb.1
      rw [isMulCommutative_iff]
      intro a b
      apply hinjψ'
      simp only [MonoidHom.comp_apply, map_mul]
      have hcomm' := IsMulCommutative.is_comm.comm (⟨MulAut.conj (φ a), (hÃ a).1 a.2⟩ : Bb)
        (⟨MulAut.conj (φ b), (hÃ b).1 b.2⟩ : Bb)
      simpa using congrArg Subtype.val hcomm'
    · intro x hx
      have hψx : MulAut.conj (φ x) ∈ Bb := (hÃ x).1 hx
      have h3 := hBb.2 (MulAut.conj (φ x)) hψx
      apply hinjψ
      calc MulAut.conj (φ (x ^ 3)) = (MulAut.conj (φ x)) ^ 3 := by rw [map_pow, map_pow]
        _ = 1 := h3
        _ = MulAut.conj (φ 1) := by simp
  · rw [hÃ, ← hα]
    exact hαB

theorem i167CLin_tilde_max {S : Type} [Group S] {Bb : Subgroup (MulAut S)} (hSc : ScpS 3 S Bb)
    (hBin : ∀ β ∈ Bb, ∃ s : S, β = MulAut.conj s) {K : Type} [Field K] [Finite K] {d : ℕ}
    (φ : GL (Fin d) K ≃* S) (Ã : Subgroup (GL (Fin d) K))
    (hÃ : ∀ x, x ∈ Ã ↔ (MulAut.conj (φ x) : MulAut S) ∈ Bb) :
    ∀ s : GL (Fin d) K, s ^ 3 = 1 → (∀ a ∈ Ã, a * s = s * a) → s ∈ Ã := by
  intro s hs3 hcomm
  set σ : S := φ s with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow, hs3, map_one]
  have hcent : ∀ β ∈ Bb, β σ = σ := by
    intro β hβ
    obtain ⟨σ', hσ'⟩ := hBin β hβ
    have hxÃ : φ.symm σ' ∈ Ã := by
      rw [hÃ]
      simpa [hσ'] using hβ
    have hx := hcomm (φ.symm σ') hxÃ
    have hσ'σ : σ' * σ = σ * σ' := by
      have h := congrArg φ hx
      simp only [map_mul, MulEquiv.apply_symm_apply] at h
      simpa [hσ] using h
    calc β σ = (MulAut.conj σ') σ := by rw [hσ']
      _ = σ' * σ * σ'⁻¹ := rfl
      _ = σ * σ' * σ'⁻¹ := by rw [hσ'σ]
      _ = σ := by group
  have hconj : MulAut.conj σ ∈ Bb := hSc σ hcent hσ3
  rw [hÃ]
  simpa [hσ] using hconj

private theorem i167CLin_tilde_centJ_aux1 {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2) :
    (2 : K) = 0 := by
  letI := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime hcard
  exact_mod_cast CharP.cast_eq_zero K 2

private theorem i167CLin_tilde_centJ_aux2 {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (A G : V →ₗ[K] V) (h2 : (2 : K) = 0) (hG : G ^ 3 = 1) (hAG : A * G = G * A) :
    G * (1 + G + G ^ 2) = (1 + G + G ^ 2) ∧
      (1 + G + G ^ 2) + (G - 1) * G = 1 ∧ A * (G - 1) = (G - 1) * A := by
  have h2E : (2 : Module.End K V) = 0 := by
    have := map_ofNat (algebraMap K (Module.End K V)) 2
    rw [h2, map_zero] at this
    exact this.symm
  have hP2 : G ^ 2 + G ^ 2 = 0 := by
    calc G ^ 2 + G ^ 2 = (2 : Module.End K V) * G ^ 2 := by noncomm_ring
      _ = 0 := by rw [h2E, zero_mul]
  refine ⟨?_, ?_, ?_⟩
  · calc G * (1 + G + G ^ 2) = G + G ^ 2 + G ^ 3 := by noncomm_ring
      _ = 1 + G + G ^ 2 := by rw [hG]; abel
  · calc (1 + G + G ^ 2) + (G - 1) * G = 1 + (G ^ 2 + G ^ 2) := by noncomm_ring
      _ = 1 := by rw [hP2, add_zero]
  · calc A * (G - 1) = A * G - A := by noncomm_ring
      _ = G * A - A := by rw [hAG]
      _ = (G - 1) * A := by noncomm_ring

private theorem i167CLin_tilde_centJ_aux3 {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (A M G : V →ₗ[K] V) (h2 : (2 : K) = 0) (hG : G ^ 3 = 1)
    (hAG : A * G = G * A) (hMG : M * G = G * M)
    (hA : ∀ v, G v = v → A v = v) (hM : ∀ v, M (G v - v) = G v - v) :
    A * M = M * A := by
  obtain ⟨hPmul, hPQG, hAQ⟩ := i167CLin_tilde_centJ_aux2 A G h2 hG hAG
  set P : V →ₗ[K] V := 1 + G + G ^ 2 with hP
  set Q : V →ₗ[K] V := G - 1 with hQ
  have hPmul' : G * P = P := by rw [hP]; exact hPmul
  have hPQG' : P + Q * G = 1 := by rw [hP, hQ]; exact hPQG
  have hAQ' : A * Q = Q * A := by rw [hQ]; exact hAQ
  apply LinearMap.ext; intro v
  change A (M v) = M (A v)
  have hv : P v + Q (G v) = v := by
    have := congrArg (fun f : V →ₗ[K] V => f v) hPQG'
    simpa [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply] using this
  have hPv : G (P v) = P v := by
    have := congrArg (fun f : V →ₗ[K] V => f v) hPmul'
    simpa [Module.End.mul_apply] using this
  have hMU : M (Q (G v)) = Q (G v) := by
    have h := hM (G v)
    simpa [hQ, LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply] using h
  have hMP : G (M (P v)) = M (P v) := by
    have h := congrArg (fun f : V →ₗ[K] V => f (P v)) hMG
    simp only [Module.End.mul_apply] at h
    rw [hPv] at h
    exact h.symm
  have hAx : M (A (Q (G v))) = A (Q (G v)) := by
    have h := congrArg (fun f : V →ₗ[K] V => f (G v)) hAQ'
    have hQv : A (Q (G v)) = G (A (G v)) - A (G v) := by
      simpa [hQ, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] using h
    rw [hQv]; exact hM (A (G v))
  have hMv : M v = M (P v) + Q (G v) := by
    have h := congrArg M hv.symm
    rw [map_add, hMU] at h
    exact h
  have hAv : A v = P v + A (Q (G v)) := by
    have h := congrArg A hv.symm
    rw [map_add, hA (P v) hPv] at h
    exact h
  rw [hMv, hAv]
  simp only [map_add, hA (M (P v)) hMP, hAx]

private theorem i167CLin_tilde_centJ_aux4 {K : Type} [Field K] {d : ℕ} {g a m : GL (Fin d) K}
    (h2 : (2 : K) = 0) (hg3 : g ^ 3 = 1) (hag : a * g = g * a) (hmg : m * g = g * m)
    (haW : ∀ v : Fin d → K, Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1) v = 0 →
      (a : Matrix (Fin d) (Fin d) K) *ᵥ v = v)
    (hmU : ∀ v : Fin d → K,
      v ∈ LinearMap.range (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1)) →
      (m : Matrix (Fin d) (Fin d) K) *ᵥ v = v) :
    (a : Matrix (Fin d) (Fin d) K) * (m : Matrix (Fin d) (Fin d) K) =
      (m : Matrix (Fin d) (Fin d) K) * (a : Matrix (Fin d) (Fin d) K) := by
  let G : (Fin d → K) →ₗ[K] (Fin d → K) := Matrix.toLinAlgEquiv' (g : Matrix (Fin d) (Fin d) K)
  let A : (Fin d → K) →ₗ[K] (Fin d → K) := Matrix.toLinAlgEquiv' (a : Matrix (Fin d) (Fin d) K)
  let M : (Fin d → K) →ₗ[K] (Fin d → K) := Matrix.toLinAlgEquiv' (m : Matrix (Fin d) (Fin d) K)
  have hsub : Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1) = G - 1 := by
    change Matrix.toLinAlgEquiv' ((g : Matrix (Fin d) (Fin d) K) - 1) =
      Matrix.toLinAlgEquiv' (g : Matrix (Fin d) (Fin d) K) - 1
    rw [map_sub, map_one]
  have hG3 : G ^ 3 = 1 := by
    have hg3' : (g : Matrix (Fin d) (Fin d) K) ^ 3 = 1 := by
      have := congrArg (fun u : GL (Fin d) K => (u : Matrix (Fin d) (Fin d) K)) hg3
      simpa using this
    change Matrix.toLinAlgEquiv' (g : Matrix (Fin d) (Fin d) K) ^ 3 = 1
    rw [← map_pow, hg3', map_one]
  have hAG : A * G = G * A := by
    have hm : (a : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) =
        (g : Matrix (Fin d) (Fin d) K) * (a : Matrix (Fin d) (Fin d) K) := by
      have := congrArg (fun u : GL (Fin d) K => (u : Matrix (Fin d) (Fin d) K)) hag
      simpa using this
    simpa [A, G, map_mul] using congrArg (fun N : Matrix (Fin d) (Fin d) K =>
      Matrix.toLinAlgEquiv' N) hm
  have hMG : M * G = G * M := by
    have hm : (m : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) =
        (g : Matrix (Fin d) (Fin d) K) * (m : Matrix (Fin d) (Fin d) K) := by
      have := congrArg (fun u : GL (Fin d) K => (u : Matrix (Fin d) (Fin d) K)) hmg
      simpa using this
    simpa [M, G, map_mul] using congrArg (fun N : Matrix (Fin d) (Fin d) K =>
      Matrix.toLinAlgEquiv' N) hm
  have hA : ∀ v, G v = v → A v = v := by
    intro v hv
    have hvker : v ∈ LinearMap.ker (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1)) := by
      rw [LinearMap.mem_ker, hsub, LinearMap.sub_apply, Module.End.one_apply, hv, sub_self]
    simpa [A] using haW v hvker
  have hM : ∀ v, M (G v - v) = G v - v := by
    intro v
    have hmem : G v - v ∈ LinearMap.range (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1)) := by
      refine ⟨v, ?_⟩
      rw [hsub, LinearMap.sub_apply, Module.End.one_apply]
    simpa [M] using hmU (G v - v) hmem
  have hcomm := i167CLin_tilde_centJ_aux3 A M G h2 hG3 hAG hMG hA hM
  have := congrArg (fun f : (Fin d → K) →ₗ[K] (Fin d → K) => LinearMap.toMatrixAlgEquiv' f) hcomm
  simpa [A, M] using this

private theorem i167CLin_tilde_centJ_aux5 {S : Type} [Group S] (hcen : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  intro x y hxy
  have h : ∀ z : S, x * z * x⁻¹ = y * z * y⁻¹ := by
    intro z
    have := congrArg (fun f : MulAut S => f z) hxy
    simpa using this
  have hcent : y⁻¹ * x ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz := congrArg (fun w => y⁻¹ * w) (h z)
    have hz' : y⁻¹ * x * z * x⁻¹ = z * y⁻¹ := by simpa [mul_assoc] using hz
    calc z * (y⁻¹ * x) = z * y⁻¹ * x := by simp [mul_assoc]
      _ = (y⁻¹ * x * z * x⁻¹) * x := by rw [← hz']
      _ = y⁻¹ * x * z := by simp [mul_assoc]
  have h1 : y⁻¹ * x = 1 := by
    have := hcent
    rwa [hcen, Subgroup.mem_bot] at this
  have : x = y := by
    have := congrArg (fun w => y * w) h1
    simpa [mul_assoc] using this
  exact this

private theorem i167CLin_tilde_centJ_aux6 {S : Type} [Group S] {K : Type} [Field K] {d : ℕ}
    (e : S ≃* LargeEvenProj (StatedSL d K)) (φ : GL (Fin d) K ≃* S)
    (hφ : ∀ x : GL (Fin d) K, ∃ hx : x ∈ StatedSL d K, e (φ x) = LargeEvenProjMk (StatedSL d K) ⟨x, hx⟩)
    (g a : GL (Fin d) K) (h2 : (2 : K) = 0) (hg3 : g ^ 3 = 1) (hag : a * g = g * a)
    (haW : ∀ v : Fin d → K, Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1) v = 0 →
      (a : Matrix (Fin d) (Fin d) K) *ᵥ v = v)
    (M : Subgroup (GL (Fin d) K)) (hMle : M ≤ Subgroup.centralizer ({g} : Set (GL (Fin d) K)))
    (hMtriv : ∀ m ∈ M, ∀ v ∈ LinearMap.range (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1)),
      (m : Matrix (Fin d) (Fin d) K) *ᵥ v = v)
    (J : Subgroup S)
    (hJM : ∀ x ∈ J, ∃ m ∈ M, ∃ hm : m ∈ StatedSL d K, e x = LargeEvenProjMk (StatedSL d K) ⟨m, hm⟩) :
    ∀ j ∈ J, MulAut.conj (φ a) j = j := by
  intro j hj
  obtain ⟨m, hm, hmS, hmj⟩ := hJM j hj
  have hmg : m * g = g * m := Subgroup.mem_centralizer_singleton_iff.mp (hMle hm)
  have hcomm := i167CLin_tilde_centJ_aux4 h2 hg3 hag hmg haW (fun v hv => hMtriv m hm v hv)
  have hcommGL : a * m = m * a := Units.ext (by simpa using hcomm)
  obtain ⟨haS, hφa⟩ := hφ a
  have hsub : (⟨a, haS⟩ * ⟨m, hmS⟩ * ⟨a, haS⟩⁻¹ : ↥(StatedSL d K)) = ⟨m, hmS⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcommGL, mul_assoc, mul_inv_cancel, mul_one]
  have heq : e (φ a * j * (φ a)⁻¹) = e j := by
    calc e (φ a * j * (φ a)⁻¹)
        = e (φ a) * e j * (e (φ a))⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = LargeEvenProjMk (StatedSL d K) ⟨a, haS⟩ * e j *
            (LargeEvenProjMk (StatedSL d K) ⟨a, haS⟩)⁻¹ := by rw [hφa]
      _ = LargeEvenProjMk (StatedSL d K) ⟨a, haS⟩ *
            LargeEvenProjMk (StatedSL d K) ⟨m, hmS⟩ *
            (LargeEvenProjMk (StatedSL d K) ⟨a, haS⟩)⁻¹ := by rw [hmj]
      _ = LargeEvenProjMk (StatedSL d K) (⟨a, haS⟩ * ⟨m, hmS⟩ * ⟨a, haS⟩⁻¹) := by
            rw [map_mul, map_mul, map_inv]
      _ = LargeEvenProjMk (StatedSL d K) ⟨m, hmS⟩ := by rw [hsub]
      _ = e j := hmj.symm
  rw [MulAut.conj_apply]
  exact e.injective heq

private theorem i167CLin_tilde_centJ_aux7 {S : Type} [Group S] (hcen : Subgroup.center S = ⊥)
    {K : Type} [Field K] {d : ℕ} (φ : GL (Fin d) K ≃* S) (g a : GL (Fin d) K)
    (h : MulAut.conj (φ a) ∈ Subgroup.zpowers (MulAut.conj (φ g))) :
    a ∈ Subgroup.zpowers g := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have hconj : MulAut.conj ((φ g) ^ k) = MulAut.conj (φ a) := by rw [map_zpow]; exact hk
  have hxy : (φ g) ^ k = φ a := i167CLin_tilde_centJ_aux5 hcen hconj
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, φ.injective (by rw [map_zpow]; exact hxy)⟩

theorem i167CLin_tilde_centJ {S : Type} [Group S] (hcen : Subgroup.center S = ⊥) {Bb : Subgroup (MulAut S)}
    {α : MulAut S} {J : Subgroup S} (hCJ : CentJ Bb α J) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {d : ℕ} (e : S ≃* LargeEvenProj (StatedSL d K)) (φ : GL (Fin d) K ≃* S)
    (hφ : ∀ x : GL (Fin d) K, ∃ hx : x ∈ StatedSL d K, e (φ x) = LargeEvenProjMk (StatedSL d K) ⟨x, hx⟩)
    (g : GL (Fin d) K) (hg3 : g ^ 3 = 1) (hαg : α = MulAut.conj (φ g))
    (Ã : Subgroup (GL (Fin d) K)) (hÃ : ∀ x, x ∈ Ã ↔ (MulAut.conj (φ x) : MulAut S) ∈ Bb)
    (hAab : IsElemAbelian 3 Ã) (hgÃ : g ∈ Ã) (M : Subgroup (GL (Fin d) K))
    (hMle : M ≤ Subgroup.centralizer ({g} : Set (GL (Fin d) K)))
    (hMtriv : ∀ m ∈ M, ∀ v ∈ LinearMap.range (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1)),
      (m : Matrix (Fin d) (Fin d) K) *ᵥ v = v)
    (hJM : ∀ x ∈ J, ∃ m ∈ M, ∃ hm : m ∈ StatedSL d K, e x = LargeEvenProjMk (StatedSL d K) ⟨m, hm⟩) :
    ∀ a ∈ Ã, (∀ v ∈ LinearMap.ker (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1)),
      (a : Matrix (Fin d) (Fin d) K) *ᵥ v = v) → a ∈ Subgroup.zpowers g := by
  intro a ha hker
  have h2 : (2 : K) = 0 := i167CLin_tilde_centJ_aux1 hK
  have haW : ∀ v : Fin d → K, Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1) v = 0 →
      (a : Matrix (Fin d) (Fin d) K) *ᵥ v = v :=
    fun v hv => hker v (LinearMap.mem_ker.mpr hv)
  have hag : a * g = g * a := by
    have hsub : (⟨a, ha⟩ : ↥Ã) * ⟨g, hgÃ⟩ = ⟨g, hgÃ⟩ * ⟨a, ha⟩ := hAab.1.is_comm.comm _ _
    have := congrArg (fun u : ↥Ã => (u : GL (Fin d) K)) hsub
    simpa using this
  have hcentral : ∀ j ∈ J, MulAut.conj (φ a) j = j :=
    i167CLin_tilde_centJ_aux6 e φ hφ g a h2 hg3 hag haW M hMle hMtriv J hJM
  have hmem : MulAut.conj (φ a) ∈ Subgroup.zpowers (MulAut.conj (φ g)) := by
    have hbase := hCJ (MulAut.conj (φ a)) ((hÃ a).mp ha) hcentral
    simpa [hαg] using hbase
  exact i167CLin_tilde_centJ_aux7 hcen φ g a hmem

theorem i167CLin_scp_matrix {S : Type} [Group S] (hcen : Subgroup.center S = ⊥) {Bb : Subgroup (MulAut S)}
    {α : MulAut S} {J : Subgroup S} (hBb : IsElemAbelian 3 Bb) (hαB : α ∈ Bb) (hSc : ScpS 3 S Bb)
    (hCJ : CentJ Bb α J) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {d : ℕ} (hd : 3 ≤ d)
    (e : S ≃* LargeEvenProj (StatedSL d K)) (g : GL (Fin d) K) (hg3 : g ^ 3 = 1)
    (hgr : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = g * (h : GL (Fin d) K) * g⁻¹ →
      MulAut.congr e α (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h')
    (M : Subgroup (GL (Fin d) K)) (hMle : M ≤ Subgroup.centralizer ({g} : Set (GL (Fin d) K)))
    (hMtriv : ∀ m ∈ M, ∀ v ∈ LinearMap.range (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1)),
      (m : Matrix (Fin d) (Fin d) K) *ᵥ v = v)
    (hJM : ∀ x ∈ J, ∃ m ∈ M, ∃ hm : m ∈ StatedSL d K, e x = LargeEvenProjMk (StatedSL d K) ⟨m, hm⟩) :
    ∃ Ã : Subgroup (GL (Fin d) K), IsElemAbelian 3 Ã ∧ g ∈ Ã ∧
      (∀ s : GL (Fin d) K, s ^ 3 = 1 → (∀ a ∈ Ã, a * s = s * a) → s ∈ Ã) ∧
      (∀ a ∈ Ã, (∀ v ∈ LinearMap.ker (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1)),
        (a : Matrix (Fin d) (Fin d) K) *ᵥ v = v) → a ∈ Subgroup.zpowers g) := by
  obtain ⟨φ, hφ⟩ := i167CLin_gl_iso hK e
  have hBin : ∀ β ∈ Bb, ∃ s : S, β = MulAut.conj s := fun β hβ =>
    i167CLin_bb_inner hK hd e (m := 3) (by decide) (hBb.2 β hβ)
  let Ã : Subgroup (GL (Fin d) K) := Bb.comap ((MulAut.conj : S →* MulAut S).comp φ.toMonoidHom)
  have hÃ : ∀ x, x ∈ Ã ↔ (MulAut.conj (φ x) : MulAut S) ∈ Bb := fun x => Iff.rfl
  obtain ⟨hab, hgÃ, hαg⟩ := i167CLin_tilde_basic hcen hBb hαB e φ hφ g hgr Ã hÃ
  exact ⟨Ã, hab, hgÃ, i167CLin_tilde_max hSc hBin φ Ã hÃ,
    i167CLin_tilde_centJ hcen hCJ hK e φ hφ g hg3 hαg Ã hÃ hab hgÃ M hMle hMtriv hJM⟩

end CFSG.LocalAnalysis.GLTheoremA.I167

end

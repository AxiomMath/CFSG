module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ6

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

section NormAll

variable {τ : Tag} {K : Type} [Field K] {J : Set (Fin τ.rank)}

@[expose] def NormAll (J : Set (Fin τ.rank)) (g : ModGL τ K) : Prop :=
  ∀ d : ℤ, g ∈ Subgroup.normalizer (degSeries τ K J d : Set (ModGL τ K))

theorem NormAll.one : NormAll (K := K) J 1 := fun d => Subgroup.one_mem _

theorem NormAll.mul {g g' : ModGL τ K} (hg : NormAll J g) (hg' : NormAll J g') :
    NormAll J (g * g') := fun d => Subgroup.mul_mem _ (hg d) (hg' d)

theorem NormAll.inv {g : ModGL τ K} (hg : NormAll J g) : NormAll J g⁻¹ :=
  fun d => Subgroup.inv_mem _ (hg d)

theorem NormAll.of_parabolic {g : ModGL τ K} (hg : g ∈ parabolicSubgroup τ K J) : NormAll J g :=
  fun d => parabolicSubgroup_le_normalizer_degSeries d hg

theorem NormAll.of_rootDiagUnit (a : Fin τ.rank → Kˣ) : NormAll (K := K) J (rootDiagUnit τ a) :=
  fun d => rootDiagUnit_mem_normalizer_degSeries a d

theorem NormAll.of_posUnipotent {g : ModGL τ K} (hg : g ∈ posUnipotent τ K) : NormAll J g :=
  fun d => posUnipotent_le_normalizer_degSeries d hg

theorem NormAll.of_radical {g : ModGL τ K} (hg : g ∈ parabolicRadical τ K J) : NormAll J g :=
  NormAll.of_posUnipotent (parabolicRadical_le_posUnipotent J hg)

theorem NormAll.conj_mem {g : ModGL τ K} (hg : NormAll J g) {d : ℤ} {x : ModGL τ K}
    (hx : x ∈ degSeries τ K J d) : g * x * g⁻¹ ∈ degSeries τ K J d :=
  (Subgroup.mem_normalizer_iff.1 (hg d) x).1 hx

end NormAll

section Lconj

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 3] {J : Set (Fin τ.rank)}

@[expose] def lconj {g : ModGL τ K} (hg : NormAll J g) {d : ℤ} (hd : 1 ≤ d) :
    Lyr (isLayer_degSeries (K := K) (J := J) hd) →ₗ[ZMod 3]
      Lyr (isLayer_degSeries (K := K) (J := J) hd) :=
  Lyr.mapL _ (MulAut.conj g).toMonoidHom (fun _ hx => hg.conj_mem hx)
    (fun _ hx => hg.conj_mem hx)

theorem lconj_mk {g : ModGL τ K} (hg : NormAll J g) {d : ℤ} (hd : 1 ≤ d)
    (x : degSeries τ K J d) :
    lconj hg hd (Lyr.mk _ x) = Lyr.mk _ ⟨g * x.1 * g⁻¹, hg.conj_mem x.2⟩ := rfl

theorem lconj_mul {g g' : ModGL τ K} (hg : NormAll J g) (hg' : NormAll J g') {d : ℤ} (hd : 1 ≤ d)
    (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) :
    lconj (hg.mul hg') hd z = lconj hg hd (lconj hg' hd z) := by
  obtain ⟨x, rfl⟩ := Lyr.mk_surjective _ z
  rw [lconj_mk, lconj_mk, lconj_mk]
  congr 1

theorem lconj_one {d : ℤ} (hd : 1 ≤ d) (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) :
    lconj (NormAll.one (K := K) (J := J)) hd z = z := by
  obtain ⟨x, rfl⟩ := Lyr.mk_surjective _ z
  rw [lconj_mk]
  congr 1

theorem lconj_congr {g g' : ModGL τ K} (hg : NormAll J g) (hg' : NormAll J g') (h : g = g')
    {d : ℤ} (hd : 1 ≤ d) (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) :
    lconj hg hd z = lconj hg' hd z := by
  subst h; rfl

theorem lconj_inv_lconj {g : ModGL τ K} (hg : NormAll J g) {d : ℤ} (hd : 1 ≤ d)
    (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) :
    lconj hg.inv hd (lconj hg hd z) = z := by
  rw [← lconj_mul, lconj_congr (hg.inv.mul hg) NormAll.one (inv_mul_cancel g), lconj_one]

theorem lconj_lconj_inv {g : ModGL τ K} (hg : NormAll J g) {d : ℤ} (hd : 1 ≤ d)
    (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) :
    lconj hg hd (lconj hg.inv hd z) = z := by
  rw [← lconj_mul, lconj_congr (hg.mul hg.inv) NormAll.one (mul_inv_cancel g), lconj_one]

theorem lconj_radical {q : ModGL τ K} (hq : q ∈ parabolicRadical τ K J) {d : ℤ} (hd : 1 ≤ d)
    (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) :
    lconj (NormAll.of_radical hq) hd z = z := by
  obtain ⟨x, rfl⟩ := Lyr.mk_surjective _ z
  rw [lconj_mk]
  have h1 : q * x.1⁻¹ * q⁻¹ * x.1 ∈ degSeries τ K J (d + 1) := by
    have h2 := commutator_degSeries_le (K := K) (J := J) (le_refl 1) hd
      (Subgroup.commutator_mem_commutator (degSeries_one (τ := τ) (K := K) (J := J) ▸ hq)
        (Subgroup.inv_mem _ x.2))
    have e : (1 : ℤ) + d = d + 1 := by ring
    rw [e] at h2
    simpa [commutatorElement_def] using h2
  rw [Lyr.mk_eq_mk]
  simpa [mul_assoc] using h1

end Lconj

section Anticomm

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 3] {J : Set (Fin τ.rank)}

theorem lconj_zeta_odd {d : ℤ} (hd : 1 ≤ d) (hodd : Odd d)
    (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) :
    lconj (NormAll.of_rootDiagUnit (K := K) (J := J) (zetaDiag J)) hd z = -z :=
  conjL_zeta_odd hd hodd z

theorem lconj_anticomm_odd {Γ y q : ModGL τ K} (hΓ : NormAll J Γ) (hy : NormAll J y)
    (hq : q ∈ parabolicRadical τ K J)
    (h : y * Γ * y⁻¹ = q * (rootDiagUnit τ (zetaDiag (K := K) J) * Γ)) {d : ℤ} (hd : 1 ≤ d)
    (hodd : Odd d) (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) :
    lconj hy hd (lconj hΓ hd z) = -lconj hΓ hd (lconj hy hd z) := by
  have hζ : NormAll J (rootDiagUnit τ (zetaDiag (K := K) J)) := NormAll.of_rootDiagUnit _
  have hq' : NormAll J q := NormAll.of_radical hq
  have e : y * Γ = (q * (rootDiagUnit τ (zetaDiag (K := K) J) * Γ)) * y := by
    calc y * Γ = (y * Γ * y⁻¹) * y := by group
      _ = _ := by rw [h]
  calc lconj hy hd (lconj hΓ hd z) = lconj (hy.mul hΓ) hd z := (lconj_mul hy hΓ hd z).symm
    _ = lconj ((hq'.mul (hζ.mul hΓ)).mul hy) hd z :=
      lconj_congr (hy.mul hΓ) ((hq'.mul (hζ.mul hΓ)).mul hy) e hd z
    _ = lconj (hq'.mul (hζ.mul hΓ)) hd (lconj hy hd z) := lconj_mul (hq'.mul (hζ.mul hΓ)) hy hd z
    _ = lconj hq' hd (lconj (hζ.mul hΓ) hd (lconj hy hd z)) := lconj_mul hq' (hζ.mul hΓ) hd _
    _ = lconj (hζ.mul hΓ) hd (lconj hy hd z) := lconj_radical hq hd _
    _ = lconj hζ hd (lconj hΓ hd (lconj hy hd z)) := lconj_mul hζ hΓ hd _
    _ = -lconj hΓ hd (lconj hy hd z) := lconj_zeta_odd hd hodd _

@[expose] def lmap (φ : ModGL τ K →* ModGL τ K)
    (hφ : ∀ d : ℤ, ∀ x ∈ degSeries τ K J d, φ x ∈ degSeries τ K J d) {d : ℤ} (hd : 1 ≤ d) :
    Lyr (isLayer_degSeries (K := K) (J := J) hd) →ₗ[ZMod 3]
      Lyr (isLayer_degSeries (K := K) (J := J) hd) :=
  Lyr.mapL _ φ (hφ d) (hφ (d + 1))

theorem lmap_mk (φ : ModGL τ K →* ModGL τ K)
    (hφ : ∀ d : ℤ, ∀ x ∈ degSeries τ K J d, φ x ∈ degSeries τ K J d) {d : ℤ} (hd : 1 ≤ d)
    (x : degSeries τ K J d) :
    lmap φ hφ hd (Lyr.mk _ x) = Lyr.mk _ ⟨φ x.1, hφ d x.1 x.2⟩ := rfl

theorem lmap_lconj {φ : ModGL τ K →* ModGL τ K}
    (hφ : ∀ d : ℤ, ∀ x ∈ degSeries τ K J d, φ x ∈ degSeries τ K J d)
    {Γ₁ Γ₂ : ModGL τ K} (hΓ₁ : NormAll J Γ₁) (hΓ₂ : NormAll J Γ₂) {d : ℤ} (hd : 1 ≤ d)
    (h : ∀ x ∈ degSeries τ K J d, φ (Γ₁ * x * Γ₁⁻¹) = Γ₂ * φ x * Γ₂⁻¹)
    (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) :
    lmap φ hφ hd (lconj hΓ₁ hd z) = lconj hΓ₂ hd (lmap φ hφ hd z) := by
  obtain ⟨x, rfl⟩ := Lyr.mk_surjective _ z
  rw [lconj_mk, lmap_mk, lmap_mk, lconj_mk]
  congr 1
  exact Subtype.ext (h x.1 x.2)

theorem lmap_cube {φ : ModGL τ K →* ModGL τ K}
    (hφ : ∀ d : ℤ, ∀ x ∈ degSeries τ K J d, φ x ∈ degSeries τ K J d) {d : ℤ} (hd : 1 ≤ d)
    (h3 : ∀ x ∈ degSeries τ K J d, φ (φ (φ x)) = x)
    (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) :
    lmap φ hφ hd (lmap φ hφ hd (lmap φ hφ hd z)) = z := by
  obtain ⟨x, rfl⟩ := Lyr.mk_surjective _ z
  rw [lmap_mk, lmap_mk, lmap_mk]
  congr 1
  exact Subtype.ext (h3 x.1 x.2)

@[expose] def lmapEquiv {φ : ModGL τ K →* ModGL τ K}
    (hφ : ∀ d : ℤ, ∀ x ∈ degSeries τ K J d, φ x ∈ degSeries τ K J d) {d : ℤ} (hd : 1 ≤ d)
    (h3 : ∀ x ∈ degSeries τ K J d, φ (φ (φ x)) = x) :
    Lyr (isLayer_degSeries (K := K) (J := J) hd) ≃ₗ[ZMod 3]
      Lyr (isLayer_degSeries (K := K) (J := J) hd) :=
  LinearEquiv.ofLinear (lmap φ hφ hd) ((lmap φ hφ hd).comp (lmap φ hφ hd))
    (LinearMap.ext fun z => lmap_cube hφ hd h3 z)
    (LinearMap.ext fun z => lmap_cube hφ hd h3 z)

end Anticomm

section Count

variable {L : Type*} [AddCommGroup L] [Module (ZMod 3) L] [Finite L]

theorem card_fixSp_eq_of_conj (t t' : L →ₗ[ZMod 3] L) (B : L ≃ₗ[ZMod 3] L)
    (h : ∀ x, B (t x) = t' (B x)) : Nat.card (fixSp t') = Nat.card (fixSp t) := by
  refine Nat.card_congr (Equiv.symm ?_)
  refine Equiv.ofBijective (fun x : fixSp t => (⟨B x.1, ?_⟩ : fixSp t')) ⟨?_, ?_⟩
  · rw [mem_fixSp, ← h, mem_fixSp.1 x.2]
  · intro x y hxy
    exact Subtype.ext (B.injective (congrArg Subtype.val hxy))
  · rintro ⟨y, hy⟩
    refine ⟨⟨B.symm y, ?_⟩, Subtype.ext (by simp)⟩
    rw [mem_fixSp]
    apply B.injective
    rw [h, LinearEquiv.apply_symm_apply, mem_fixSp.1 hy]

theorem card_inf_klein_le_of_conj (t₁ t₂ : L →ₗ[ZMod 3] L) (h₁ : ∀ x, t₁ (t₁ x) = x)
    (h₂ : ∀ x, t₂ (t₂ x) = x) (hc : ∀ x, t₁ (t₂ x) = t₂ (t₁ x)) (B : L ≃ₗ[ZMod 3] L)
    (hB₁ : ∀ x, B (t₁ x) = t₂ (B x)) (hB₂ : ∀ x, B (t₂ x) = t₁ (t₂ (B x)))
    (c₁ : Nat.card (fixSp t₁) ^ 2 ≤ Nat.card L) :
    Nat.card (fixSp t₁ ⊓ fixSp t₂ : Submodule (ZMod 3) L) ^ 4 ≤ Nat.card L := by
  have e2 := card_fixSp_eq_of_conj t₁ t₂ B hB₁
  have e3 := card_fixSp_eq_of_conj t₂ (t₁ * t₂) B hB₂
  refine card_fix_klein_le t₁ t₂ h₁ h₂ hc c₁ ?_ ?_
  · rw [e2]; exact c₁
  · rw [e3, e2]; exact c₁

end Count

end CFSG.LocalAnalysis.GLTheoremA

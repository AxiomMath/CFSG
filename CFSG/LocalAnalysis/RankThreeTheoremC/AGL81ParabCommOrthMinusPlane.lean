module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusComm

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

open Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.AGLEmbedding.LeviBlock
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

section Plane

theorem eq_zero_of_isOmegaTwisted_one {e : K}
    (h : IsOmegaTwisted b c (1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) e) : e = 0 := by
  unfold IsOmegaTwisted at h
  have h1 := LinearMap.congr_fun h (Pi.single 0 1)
  have h2 := congrFun h1 0
  simp only [LinearEquiv.coe_one, Module.End.one_eq_id, LinearMap.id_comp, Module.End.mul_apply,
    LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Pi.single_eq_same, mul_one, LinearMap.id_apply] at h2
  simpa using h2

theorem isOmegaTwisted_pow {ψ : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)} {e : K}
    (hψ : IsOmegaTwisted b c ψ e) (n : ℕ) : IsOmegaTwisted b c (ψ ^ n) ((n : K) * e) := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul]
    exact (omegaRotations b c).one_mem
  | succ n ih =>
    have := IsOmegaTwisted.mul ih hψ
    rw [← pow_succ] at this
    rw [Nat.cast_succ, add_mul, one_mul]
    exact this

theorem plane_isOmegaTwisted_zero (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {N : ℕ} (hN : Odd N)
    (g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) (μ : K)
    (hμ : ∀ a, minusTailForm K b c (g a) = μ * minusTailForm K b c a) {s : K}
    (hs : ∀ a, (g ^ N) a = s • a) : IsOmegaTwisted b c g 0 := by
  have hani := anisotropic_minusTailForm hirr
  have hb := minusPlane_b_ne_zero hirr
  obtain ⟨e₀, he₀⟩ : ∃ a : Fin 2 → K, a ≠ 0 := ⟨Pi.single 0 1, fun h => by simpa using congrFun h 0⟩
  have hqe₀ : minusTailForm K b c e₀ ≠ 0 := fun h => he₀ (hani _ h)
  have hμ0 : μ ≠ 0 := by
    intro h0
    have h1 := hμ e₀
    rw [h0, zero_mul] at h1
    have h2 : g e₀ = 0 := hani _ h1
    exact he₀ (g.injective (by rw [h2, map_zero]))
  obtain ⟨ν, hν⟩ := isSquare_of_charTwo' μ
  have hν0 : ν ≠ 0 := by
    rintro rfl
    exact hμ0 (by rw [hν, mul_zero])
  let ψ : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) :=
    { toFun := fun a => ν⁻¹ • g a
      map_add' := fun a a' => by rw [map_add, smul_add]
      map_smul' := fun a x => by
        rw [map_smul, smul_comm]
        rfl
      invFun := fun a => g.symm (ν • a)
      left_inv := fun a => by
        simp only [smul_smul, mul_inv_cancel₀ hν0, one_smul, LinearEquiv.symm_apply_apply]
      right_inv := fun a => by
        simp only [map_smul, LinearEquiv.apply_symm_apply, smul_smul, inv_mul_cancel₀ hν0,
          one_smul] }
  have hψ : ∀ a, ψ a = ν⁻¹ • g a := fun a => rfl
  have hψO : ψ ∈ TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K b c) := by
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun a => ?_
    rw [hψ, QuadraticMap.map_smul, smul_eq_mul, hμ, hν]
    field_simp
  obtain ⟨l, -, hl⟩ := isOmegaTwisted_of_mem_orthogonalGroup hb hψO
  have hpowψ : ∀ (n : ℕ) (a : Fin 2 → K), (ψ ^ n) a = ν⁻¹ ^ n • (g ^ n) a := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [pow_succ ψ n, LinearEquiv.mul_apply, hψ, map_smul, ih, pow_succ g n,
        LinearEquiv.mul_apply, smul_smul, pow_succ' ν⁻¹ n]
  have hscal : ψ ^ N ∈ scalars K (Fin 2 → K) :=
    mem_scalars.2 ⟨ν⁻¹ ^ N * s, fun a => by rw [hpowψ, hs, smul_smul]⟩
  have hone : ψ ^ N = 1 :=
    scalar_eq_one_of_isometry (pow_mem hψO N) hscal hqe₀
  have hl0 : l = 0 := by
    have h1 := isOmegaTwisted_pow hl N
    rw [hone] at h1
    have h2 := eq_zero_of_isOmegaTwisted_one h1
    rw [CharTwo.natCast_eq_ite, if_neg (Nat.not_even_iff_odd.2 hN), one_mul] at h2
    exact h2
  rw [hl0] at hl
  have hgψ : (g : Module.End K (Fin 2 → K)) = ν • (ψ : Module.End K (Fin 2 → K)) := by
    refine LinearMap.ext fun a => ?_
    show g a = ν • ψ a
    rw [hψ, smul_smul, mul_inv_cancel₀ hν0, one_smul]
  unfold IsOmegaTwisted at hl ⊢
  rw [hgψ, smul_mul_assoc, hl, mul_smul_comm]

end Plane

section PlaneBlock

variable {r : ℕ} {t : ℕ} (ht : t ≤ r)

local notation "𝕍" => (Fin r ⊕ Fin r → K) × (Fin 2 → K)

@[expose] def G0 : Subgroup (𝕍 ≃ₗ[K] 𝕍) where
  carrier := {g | (∀ v : 𝕍, g v ∈ tailFlag K (Fin 2 → K) r t ↔ v ∈ tailFlag K (Fin 2 → K) r t) ∧
    ∀ v : 𝕍, IsResPerp ht (g v) ↔ IsResPerp ht v}
  mul_mem' := fun {g g'} hg hg' =>
    ⟨fun v => (hg.1 _).trans (hg'.1 v), fun v => (hg.2 _).trans (hg'.2 v)⟩
  one_mem' := ⟨fun v => Iff.rfl, fun v => Iff.rfl⟩
  inv_mem' := fun {g} hg => by
    have e : ∀ v : 𝕍, g (g⁻¹ v) = v := fun v => by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    refine ⟨fun v => ?_, fun v => ?_⟩
    · have := hg.1 (g⁻¹ v)
      rw [e] at this
      exact this.symm
    · have := hg.2 (g⁻¹ v)
      rw [e] at this
      exact this.symm

theorem mem_G0 {g : 𝕍 ≃ₗ[K] 𝕍} :
    g ∈ G0 (K := K) (r := r) ht ↔ (∀ v : 𝕍, g v ∈ tailFlag K (Fin 2 → K) r t ↔
      v ∈ tailFlag K (Fin 2 → K) r t) ∧ ∀ v : 𝕍, IsResPerp ht (g v) ↔ IsResPerp ht v := Iff.rfl

@[expose] def pmL (g : 𝕍 ≃ₗ[K] 𝕍) : (Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
  (LinearMap.snd K (Fin r ⊕ Fin r → K) (Fin 2 → K)) ∘ₗ ((g : 𝕍 →ₗ[K] 𝕍) ∘ₗ
    (LinearMap.inr K (Fin r ⊕ Fin r → K) (Fin 2 → K)))

theorem pmL_apply (g : 𝕍 ≃ₗ[K] 𝕍) (a : Fin 2 → K) :
    pmL g a = (g ((0 : Fin r ⊕ Fin r → K), a)).2 := rfl

variable (hm0 : r - t = 0)
include hm0

theorem fst_mem_tailFlag_of_isResPerp {v : 𝕍} (hv : IsResPerp ht v) :
    ((v.1, 0) : 𝕍) ∈ tailFlag K (Fin 2 → K) r t := by
  rw [mem_tailFlag_iff]
  refine ⟨mem_flag.2 ⟨fun j => ?_, fun j hj => ?_⟩, rfl⟩
  · obtain ⟨y, rfl⟩ := (splitIdx ht).surjective j
    rcases y with i | k
    · exact hv i
    · exact absurd k.isLt (by omega)
  · exact absurd j.isLt (by omega)

theorem pmL_mul {g g' : 𝕍 ≃ₗ[K] 𝕍} (hg : g ∈ G0 (K := K) (r := r) ht)
    (hg' : g' ∈ G0 (K := K) (r := r) ht) (a : Fin 2 → K) :
    pmL (g * g') a = pmL g (pmL g' a) := by
  rw [pmL_apply, pmL_apply, pmL_apply, LinearEquiv.mul_apply]
  have hperp : IsResPerp ht (g' ((0 : Fin r ⊕ Fin r → K), a)) :=
    (hg'.2 _).2 (fun i => by simp)
  have hF := fst_mem_tailFlag_of_isResPerp ht hm0 hperp
  have hdec : g' ((0 : Fin r ⊕ Fin r → K), a) =
      ((g' ((0 : Fin r ⊕ Fin r → K), a)).1, 0) + (0, (g' ((0 : Fin r ⊕ Fin r → K), a)).2) := by
    ext <;> simp
  have h1 : (g ((g' ((0 : Fin r ⊕ Fin r → K), a)).1, 0)) ∈ tailFlag K (Fin 2 → K) r t :=
    (hg.1 _).2 hF
  have h2 := (mem_tailFlag_iff.1 h1).2
  conv_lhs => rw [hdec, map_add]
  rw [Prod.snd_add, h2, zero_add]

end PlaneBlock

section PlaneHom

variable {r : ℕ} {t : ℕ} (ht : t ≤ r) (hm0 : r - t = 0)

local notation "𝕍" => (Fin r ⊕ Fin r → K) × (Fin 2 → K)

@[expose] noncomputable def pmEquiv (g : ↥(G0 (K := K) (r := r) ht)) :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) :=
  LinearEquiv.ofLinear (pmL (g : 𝕍 ≃ₗ[K] 𝕍)) (pmL ((g⁻¹ : ↥(G0 (K := K) (r := r) ht)) : 𝕍 ≃ₗ[K] 𝕍))
    (LinearMap.ext fun a => by
      rw [LinearMap.comp_apply, ← pmL_mul ht hm0 g.2 (g⁻¹).2 a]
      have : ((g : 𝕍 ≃ₗ[K] 𝕍) * ((g⁻¹ : ↥(G0 (K := K) (r := r) ht)) : 𝕍 ≃ₗ[K] 𝕍)) = 1 :=
        by rw [← Subgroup.coe_mul, mul_inv_cancel]; rfl
      rw [this]
      rfl)
    (LinearMap.ext fun a => by
      rw [LinearMap.comp_apply, ← pmL_mul ht hm0 (g⁻¹).2 g.2 a]
      have : (((g⁻¹ : ↥(G0 (K := K) (r := r) ht)) : 𝕍 ≃ₗ[K] 𝕍) * (g : 𝕍 ≃ₗ[K] 𝕍)) = 1 :=
        by rw [← Subgroup.coe_mul, inv_mul_cancel]; rfl
      rw [this]
      rfl)

theorem pmEquiv_apply (g : ↥(G0 (K := K) (r := r) ht)) (a : Fin 2 → K) :
    pmEquiv ht hm0 g a = pmL (g : 𝕍 ≃ₗ[K] 𝕍) a := rfl

@[expose] noncomputable def pmHom : ↥(G0 (K := K) (r := r) ht) →* ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :=
  MonoidHom.mk' (pmEquiv ht hm0) fun g g' => LinearEquiv.ext fun a => by
    rw [pmEquiv_apply, LinearEquiv.mul_apply, pmEquiv_apply, pmEquiv_apply]
    exact pmL_mul ht hm0 g.2 g'.2 a

theorem quadTail_eq_of_fst_mem {b c : K} {v : 𝕍}
    (hF : ((v.1, 0) : 𝕍) ∈ tailFlag K (Fin 2 → K) r t) :
    quadTail r (minusTailForm K b c) v = minusTailForm K b c v.2 := by
  have hdec : v = ((v.1, 0) : 𝕍) + ((0 : Fin r ⊕ Fin r → K), v.2) := by
    ext <;> simp
  conv_lhs => rw [hdec]
  rw [QuadraticMap.map_add (quadTail r (minusTailForm K b c)),
    quadTail_eq_zero_of_mem_tailFlag hF, quadTail_tail, polar_quadTail]
  simp

include hm0 in
theorem commutator_sub_mem_of_plane {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g₁ g₂ : 𝕍 ≃ₗ[K] 𝕍} (hg₁ : g₁ ∈ G0 (K := K) (r := r) ht)
    (hg₂ : g₂ ∈ G0 (K := K) (r := r) ht) {μ₁ μ₂ : K}
    (hq₁ : ∀ v, quadTail r (minusTailForm K b c) (g₁ v) = μ₁ * quadTail r (minusTailForm K b c) v)
    (hq₂ : ∀ v, quadTail r (minusTailForm K b c) (g₂ v) = μ₂ * quadTail r (minusTailForm K b c) v)
    {N₁ N₂ : ℕ} (hN₁ : Odd N₁) (hN₂ : Odd N₂) {a₁ a₂ : K}
    (hs₁ : ∀ v, (g₁ ^ N₁) v = a₁ • v) (hs₂ : ∀ v, (g₂ ^ N₂) v = a₂ • v) (v : 𝕍)
    (hv : IsResPerp ht v) :
    (⁅g₁, g₂⁆ : 𝕍 ≃ₗ[K] 𝕍) v - v ∈ tailFlag K (Fin 2 → K) r t := by
  have key : ∀ (g : 𝕍 ≃ₗ[K] 𝕍) (hg : g ∈ G0 (K := K) (r := r) ht) (μ : K)
      (hq : ∀ v, quadTail r (minusTailForm K b c) (g v) = μ * quadTail r (minusTailForm K b c) v)
      (N : ℕ) (hN : Odd N) (a : K) (hs : ∀ v, (g ^ N) v = a • v),
      IsOmegaTwisted b c (pmHom ht hm0 ⟨g, hg⟩) 0 := by
    intro g hg μ hq N hN a hs
    refine plane_isOmegaTwisted_zero hirr hN (pmHom ht hm0 ⟨g, hg⟩) μ (fun a' => ?_) (s := a)
      (fun a' => ?_)
    · have h1 := hq ((0 : Fin r ⊕ Fin r → K), a')
      have hperp : IsResPerp ht (g ((0 : Fin r ⊕ Fin r → K), a')) :=
        (hg.2 _).2 (fun i => by simp)
      rw [quadTail_eq_of_fst_mem (fst_mem_tailFlag_of_isResPerp ht hm0 hperp), quadTail_tail] at h1
      exact h1
    · rw [← map_pow]
      show pmL (g ^ N) a' = a • a'
      rw [pmL_apply, hs]
      simp
  have p₁ := key g₁ hg₁ μ₁ hq₁ N₁ hN₁ a₁ hs₁
  have p₂ := key g₂ hg₂ μ₂ hq₂ N₂ hN₂ a₂ hs₂
  have hcomm := commute_of_isOmegaTwisted_zero p₁ p₂
  set h : 𝕍 ≃ₗ[K] 𝕍 := ⁅g₁, g₂⁆ with hh
  have hG : h ∈ G0 (K := K) (r := r) ht := by
    rw [hh, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)) (inv_mem hg₂)
  have hone : pmHom ht hm0 (⁅(⟨g₁, hg₁⟩ : ↥(G0 (K := K) (r := r) ht)), ⟨g₂, hg₂⟩⁆) = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 hcomm
  have hpm : ∀ a, (h ((0 : Fin r ⊕ Fin r → K), a)).2 = a := fun a => by
    have := LinearEquiv.congr_fun hone a
    exact this
  have hF0 := fst_mem_tailFlag_of_isResPerp ht hm0 hv
  have h1 : h ((v.1, 0) : 𝕍) - ((v.1, 0) : 𝕍) ∈ tailFlag K (Fin 2 → K) r t :=
    Submodule.sub_mem _ ((hG.1 _).2 hF0) hF0
  have hp : IsResPerp ht (h ((0 : Fin r ⊕ Fin r → K), v.2)) :=
    (hG.2 _).2 (fun i => by simp)
  have hF1 := fst_mem_tailFlag_of_isResPerp ht hm0 hp
  have h3 : h ((0 : Fin r ⊕ Fin r → K), v.2) - ((0 : Fin r ⊕ Fin r → K), v.2) =
      ((h ((0 : Fin r ⊕ Fin r → K), v.2)).1, 0) := by
    ext
    · simp
    · simp [hpm]
  have hdec : v = ((v.1, 0) : 𝕍) + ((0 : Fin r ⊕ Fin r → K), v.2) := by
    ext <;> simp
  have h4 : h v - v = (h ((v.1, 0) : 𝕍) - ((v.1, 0) : 𝕍)) +
      (h ((0 : Fin r ⊕ Fin r → K), v.2) - ((0 : Fin r ⊕ Fin r → K), v.2)) := by
    conv_lhs => rw [hdec, map_add]
    abel
  rw [h4, h3]
  exact Submodule.add_mem _ h1 hF1

end PlaneHom

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

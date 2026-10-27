module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParAbs2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParLift
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParSurvCheck

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Matrix Subgroup

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def maskList (mask : ℕ) : List ℕ := (List.range 4).filter fun m => mask.testBit m

theorem toMat_zero8' : toMat 8 8 zero8 = 0 := by
  ext r c
  rw [toMat_apply, zero8, Matrix.zero_apply]
  revert r c; decide

theorem toMat_id8' : toMat 8 8 id8 = 1 := by
  ext r c
  rw [toMat_apply, id8, one_apply]
  revert r c; decide

theorem toMat_eProdBits (mask : ℕ) :
    toMat 8 8 (eProdBits mask) = ((maskList mask).map fun m => toMat 8 8 (eBits m)).prod := by
  have key : ∀ (l : List ℕ) (acc : Array ℕ), toMat 8 8 (l.foldl (fun acc m =>
      if mask.testBit m then bmul 8 8 acc (eBits m) else acc) acc) =
      toMat 8 8 acc * ((l.filter fun m => mask.testBit m).map fun m => toMat 8 8 (eBits m)).prod := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons m l ih =>
      intro acc
      by_cases hm : mask.testBit m
      · simp only [List.foldl_cons, hm, ↓reduceIte]
        rw [ih, toMat_bmul, List.filter_cons_of_pos (by simpa using hm), List.map_cons,
          List.prod_cons, mul_assoc]
      · simp only [List.foldl_cons, hm, Bool.false_eq_true, ↓reduceIte]
        rw [ih, List.filter_cons_of_neg (by simpa using hm)]
  rw [eProdBits, key, toMat_id8', one_mul, maskList]

section SU

theorem one_add_embedM_sq (ψ : Mat8) : (1 + embedM ψ) * (1 + embedM ψ) = 1 := by
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, embedM_mul_embedM, add_zero, add_assoc,
    mat8_add_self16, add_zero]

noncomputable def eProdSU (mask : ℕ) : SU42b := ((maskList mask).map eSU).prod

theorem eProdSU_mem_E16 (mask : ℕ) : eProdSU mask ∈ E16 := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hg
  have hm4 : m < 4 := List.mem_range.mp (List.mem_filter.mp hm).1
  exact Subgroup.subset_closure ⟨⟨m, hm4⟩, rfl⟩

theorem coe_eProdSU (mask : ℕ) :
    ((eProdSU mask : GL (Fin 8) (ZMod 2)) : Mat8) = toMat 8 8 (eProdBits mask) := by
  rw [toMat_eProdBits, eProdSU]
  have hl : ∀ m ∈ maskList mask, m < 4 := fun m hm =>
    List.mem_range.mp (List.mem_filter.mp hm).1
  generalize maskList mask = l at hl ⊢
  induction l with
  | nil => simp
  | cons m l ih =>
    rw [List.map_cons, List.prod_cons, Subgroup.coe_mul, Units.val_mul,
      ih fun m' h => hl m' (by simp [h]), coe_eSU m (hl m (by simp)), List.map_cons, List.prod_cons]

noncomputable def wordSU (w : List (Fin 3)) : SU42b := ⟨wordGL w, wordGL_mem w⟩

theorem coe_wordSU (w : List (Fin 3)) :
    ((wordSU w : GL (Fin 8) (ZMod 2)) : Mat8) = toMat 8 8 (wordBits w) := coe_wordGL w

theorem coe_genSU' (s : Fin 3) :
    ((genSU s : GL (Fin 8) (ZMod 2)) : Mat8) = toMat 8 8 (genBits s) := by
  rw [genSU, coe_genGL]; rfl

theorem genSU_zero_mul_self : genSU 0 * genSU 0 = 1 :=
  Subtype.ext (Units.ext genMat_zero_mul_self)

theorem SU42b_ext {g h : SU42b}
    (hgh : ((g : GL (Fin 8) (ZMod 2)) : Mat8) = ((h : GL (Fin 8) (ZMod 2)) : Mat8)) : g = h :=
  Subtype.ext (Units.ext hgh)

theorem c2_spec :
    toMat 8 8 (genBits 0) * toMat 8 8 (wordBits c2W0) =
        toMat 8 8 (wordBits c2W0) * toMat 8 8 (eProdBits 4) ∧
      toMat 8 8 (genBits 1) * toMat 8 8 (wordBits c2W1) =
        toMat 8 8 (eProdBits 8) * toMat 8 8 (genBits 0) * toMat 8 8 (eProdBits 11) *
          toMat 8 8 (genBits 0) * toMat 8 8 (wordBits c2W1) * toMat 8 8 (eProdBits 5) := by
  have h := cCheck_eq_true
  simp only [cCheck, c2Check, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨-, h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← toMat_bmul, ← toMat_bmul, h1]
  · simp only [← toMat_bmul]
    rw [h2]

theorem SU42b_eq_top_of_normal (N : Subgroup SU42b) [N.Normal]
    (hE : E16 ≤ N) : N = ⊤ := by
  have hx : genSU 0 * wordSU c2W0 = wordSU c2W0 * eProdSU 4 := by
    apply SU42b_ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_genSU', coe_wordSU, coe_eProdSU]
    exact c2_spec.1
  have hy : genSU 1 * wordSU c2W1 =
      eProdSU 8 * genSU 0 * eProdSU 11 * genSU 0 * wordSU c2W1 * eProdSU 5 := by
    apply SU42b_ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_genSU', coe_wordSU, coe_eProdSU]
    exact c2_spec.2
  have hconj : ∀ g : SU42b, ∀ mask : ℕ, g * eProdSU mask * g⁻¹ ∈ N := fun g mask =>
    ‹N.Normal›.conj_mem _ (hE (eProdSU_mem_E16 mask)) g
  have h0 : genSU 0 ∈ N := by
    have : genSU 0 = wordSU c2W0 * eProdSU 4 * (wordSU c2W0)⁻¹ := by
      rw [← hx]; group
    rw [this]; exact hconj _ _
  have h1 : genSU 1 ∈ N := by
    have hxx : (genSU 0)⁻¹ = genSU 0 := inv_eq_of_mul_eq_one_right genSU_zero_mul_self
    have : genSU 1 = eProdSU 8 * (genSU 0 * eProdSU 11 * (genSU 0)⁻¹) *
        (wordSU c2W1 * eProdSU 5 * (wordSU c2W1)⁻¹) := by
      rw [hxx]
      calc genSU 1 = genSU 1 * wordSU c2W1 * (wordSU c2W1)⁻¹ := by group
        _ = _ := by rw [hy]; group
    rw [this]
    exact N.mul_mem (N.mul_mem (hE (eProdSU_mem_E16 8)) (hconj _ _)) (hconj _ _)
  rw [eq_top_iff, SU42b_eq_closure, Subgroup.closure_le]
  rintro g (rfl | rfl)
  exacts [h0, h1]

theorem toMat_basisBits (z : ℕ) (c : Fin 8) : toMat 8 8 (basisBits z c) = candBlock z c := by
  simp only [basisBits, candBlock]
  split_ifs <;> rfl

theorem c1W_bound {z : ℕ} (hz : z < 4) {i : ℕ} (hi : i < 8) : ∀ p ∈ c1W z i, p.1 < 2 ∧ p.2 < 8 := by
  interval_cases z <;> interval_cases i <;> decide

theorem c1_spec {z : ℕ} (hz : z < 4) (c : Fin 8) :
    candBlock z c = ((c1W z c).map fun p => n0M p.1 * toMat 8 8 (basisBits z p.2) * n1M p.1 +
      toMat 8 8 (basisBits z p.2)).sum := by
  have h := cCheck_eq_true
  simp only [cCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have h1 := h.1 z hz c c.isLt
  rw [← toMat_basisBits, h1]
  generalize c1W z c = l
  have key : ∀ acc : Array ℕ, toMat 8 8 (l.foldl (fun acc p => bxor 8 acc (bxor 8 (bmul 8 8
      (bmul 8 8 (n0Bits p.1) (basisBits z p.2)) (n1Bits p.1)) (basisBits z p.2))) acc) =
      toMat 8 8 acc + (l.map fun p => n0M p.1 * toMat 8 8 (basisBits z p.2) * n1M p.1 +
        toMat 8 8 (basisBits z p.2)).sum := by
    induction l with
    | nil => intro acc; simp
    | cons p l ih =>
      intro acc
      rw [List.foldl_cons, ih, toMat_bxor, toMat_bxor, toMat_bmul, toMat_bmul, List.map_cons,
        List.sum_cons, add_assoc]
      rfl
  rw [key, toMat_zero8', zero_add]

end SU

section Main

structure R3Hyp (π : Γ →* (W →ₗ[ZMod 2] W)) (K : Subgroup Γ) (θ : K ≃* SU42b)
    (τW : W →ₗ[ZMod 2] W) (ι : (Fin 8 → ZMod 2) →ₗ[ZMod 2] W) (D : Subgroup Γ)
    (B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) (τ : Γ →* Γ) : Prop where
  inj : Function.Injective ι
  fix : ∀ u, τW (ι u) = ι u
  range : ∀ u, ∃ x, τW x + x = ι u
  card : Nat.card W = 2 ^ 16
  comm : ∀ k : K, ∀ x, τW (π k x) = π k (τW x)
  ι_eq : ∀ k : K, ∀ u, π k (ι u) = ι (((θ k : GL (Fin 8) (ZMod 2)) : Mat8) *ᵥ u)
  D_card : Nat.card D ≤ 2 ^ 8
  E_le : ∀ m < 4, ((θ.symm (eSU m) : K) : Γ) ∈ D
  ν_norm : ∀ j < 2, ∀ d ∈ D,
    ((θ.symm (nuSU j) : K) : Γ) * d * ((θ.symm (nuSU j) : K) : Γ)⁻¹ ∈ D
  W0 : ∀ d ∈ D, ∀ x, (∀ m < 4, π ((θ.symm (eSU m) : K) : Γ) x = x) → π d x = x
  W1 : ∀ d ∈ D, ∀ x, ∀ m < 4, π ((θ.symm (eSU m) : K) : Γ) (π d x + x) = π d x + x
  τfix : ∀ d ∈ D, τW ∘ₗ π d ∘ₗ τW = π d → ∃ g ∈ E16, π d = π ((θ.symm g : K) : Γ)
  τsurj : ∀ m < 4, ∃ d ∈ D, π d ∘ₗ τW ∘ₗ π d ∘ₗ τW = π ((θ.symm (eSU m) : K) : Γ)
  B0 : B ≠ 0
  Balt : ∀ x, B x x = 0
  BK : ∀ k : K, ∀ x y, B (π k x) (π k y) = B x y
  BD : ∀ d ∈ D, ∀ x y, B (π d x) (π d y) = B x y
  gen : K ⊔ D = ⊤
  ττ : ∀ g, τ (τ g) = g
  πτ : ∀ g, π (τ g) = τW ∘ₗ π g ∘ₗ τW
  τK : ∀ k ∈ K, τ k = k
  τD : ∀ d ∈ D, τ d ∈ D
  Dinj : ∀ d ∈ D, π d = 1 → d = 1
  Kr : ∀ g, π g = 1 → τ g = g → g = 1

variable {π : Γ →* (W →ₗ[ZMod 2] W)} {K : Subgroup Γ} {θ : K ≃* SU42b} {τW : W →ₗ[ZMod 2] W}
  {ι : (Fin 8 → ZMod 2) →ₗ[ZMod 2] W} {D : Subgroup Γ} {B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2}
  {τ : Γ →* Γ}

theorem R3Hyp.exists_coords [Finite Γ] [Finite W] (h : R3Hyp π K θ τW ι D B τ) :
    ∃ (e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)) (z : ℕ), z < 4 ∧ matOf e τW = tM16 ∧
      (∀ k : K, matOf e (π k) = rhoM ((θ k : GL (Fin 8) (ZMod 2)) : Mat8)) ∧
      (∀ d ∈ D, ∃ ψ ∈ psiZ z, matOf e (π d) = 1 + embedM ψ) ∧
      ∀ ψ ∈ psiZ z, ∃ d ∈ D, matOf e (π d) = 1 + embedM ψ := by
  obtain ⟨e, hτ, hK⟩ := exists_good_coords π K θ τW ι h.inj h.fix h.range h.card h.comm h.ι_eq
  obtain ⟨z, hz, h1, h2⟩ := r3_blocks π K θ τW e hτ hK D h.D_card h.E_le h.ν_norm h.W0 h.W1
    h.τfix h.τsurj B h.B0 h.Balt h.BK h.BD
  exact ⟨e, z, hz, hτ, hK, h1, h2⟩

variable {e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)}

theorem τW_comp_τW (he : matOf e τW = tM16) : τW ∘ₗ τW = LinearMap.id := by
  apply matOf_injective e
  rw [matOf_comp, he, tM16_mul_tM16, matOf_id]

variable (h : R3Hyp π K θ τW ι D B τ)
include h

theorem R3Hyp.τ_mem_ker (he : matOf e τW = tM16) {g : Γ} (hg : g ∈ π.ker) : τ g ∈ π.ker := by
  rw [MonoidHom.mem_ker] at hg ⊢
  rw [h.πτ, hg, Module.End.one_eq_id, LinearMap.id_comp, τW_comp_τW he]

theorem R3Hyp.τ_ker_inv [Finite Γ] (he : matOf e τW = tM16) : ∀ g ∈ π.ker, τ g = g⁻¹ :=
  inv_of_fixedPoints τ h.ττ (fun _ hg => h.τ_mem_ker he hg) (fun g hg hτ => h.Kr g hg hτ)

theorem R3Hyp.odd_card_ker [Finite Γ] (he : matOf e τW = tM16) : Odd (Nat.card π.ker) :=
  odd_card_of_fixedPoints τ h.ττ (fun _ hg => h.τ_mem_ker he hg) (fun g hg hτ => h.Kr g hg hτ)

theorem R3Hyp.matOf_mul (g g' : Γ) : matOf e (π (g * g')) = matOf e (π g) * matOf e (π g') := by
  rw [map_mul, YamadaPar.matOf_mul]

theorem R3Hyp.eq_of_matOf {d d' : Γ} (hd : d ∈ D) (hd' : d' ∈ D)
    (hdd : matOf e (π d) = matOf e (π d')) : d = d' := by
  have hmem : d⁻¹ * d' ∈ D := D.mul_mem (D.inv_mem hd) hd'
  have h1 : π (d⁻¹ * d') = 1 := by
    apply matOf_injective e
    have h2 : matOf e (π d⁻¹) * matOf e (π d) = 1 := by
      rw [← R3Hyp.matOf_mul h, inv_mul_cancel, map_one, matOf_one]
    rw [R3Hyp.matOf_mul h, matOf_one, ← hdd, h2]
  have h3 := h.Dinj _ hmem h1
  calc d = d * (d⁻¹ * d') := by rw [h3, mul_one]
    _ = d' := by group

theorem R3Hyp.D_mul_self {z : ℕ} (hDe : ∀ d ∈ D, ∃ ψ ∈ psiZ z, matOf e (π d) = 1 + embedM ψ)
    {d : Γ} (hd : d ∈ D) : d * d = 1 := by
  obtain ⟨ψ, -, hψ⟩ := hDe d hd
  have h1 : π (d * d) = 1 := by
    apply matOf_injective e
    rw [R3Hyp.matOf_mul h, hψ, one_add_embedM_sq, matOf_one]
  exact h.Dinj _ (D.mul_mem hd hd) h1

theorem R3Hyp.eSU_mem_centralizer [Finite Γ] (he : matOf e τW = tM16) {z : ℕ}
    (hDe : ∀ d ∈ D, ∃ ψ ∈ psiZ z, matOf e (π d) = 1 + embedM ψ) {m : ℕ} (hm : m < 4) :
    ((θ.symm (eSU m) : K) : Γ) ∈ centralizer (π.ker : Set Γ) := by
  obtain ⟨d, hd, hdm⟩ := h.τsurj m hm
  have hτd := h.τD d hd
  have hx : ((θ.symm (eSU m) : K) : Γ) = d⁻¹ * τ d := by
    have hinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right (h.D_mul_self hDe hd)
    rw [hinv]
    refine (h.eq_of_matOf (e := e) (D.mul_mem hd hτd) (h.E_le m hm) ?_).symm
    rw [map_mul, h.πτ, ← hdm]
    rfl
  rw [hx, mem_centralizer_iff]
  intro n hn
  exact (commute_inv_mul_of_inv τ (h.τ_ker_inv he) d hn).symm

theorem R3Hyp.K_le_centralizer [Finite Γ]
    (he : matOf e τW = tM16) {z : ℕ}
    (hDe : ∀ d ∈ D, ∃ ψ ∈ psiZ z, matOf e (π d) = 1 + embedM ψ) :
    K ≤ centralizer (π.ker : Set Γ) := by
  set N : Subgroup SU42b := ((centralizer (π.ker : Set Γ)).subgroupOf K).map θ.toMonoidHom
  have hN : N.Normal := (Subgroup.normal_subgroupOf).map _ θ.surjective
  have hE : E16 ≤ N := by
    rw [E16, Subgroup.closure_le]
    rintro _ ⟨m, rfl⟩
    exact ⟨θ.symm (eSU m), Subgroup.mem_subgroupOf.mpr (h.eSU_mem_centralizer he hDe m.isLt),
      by simp⟩
  have htop := SU42b_eq_top_of_normal N hE
  intro k hk
  have hmem : θ ⟨k, hk⟩ ∈ N := htop ▸ Subgroup.mem_top _
  obtain ⟨k', hk', hkk'⟩ := hmem
  have : k' = ⟨k, hk⟩ := θ.injective hkk'
  subst this
  exact Subgroup.mem_subgroupOf.mp hk'

theorem R3Hyp.D_le_centralizer [Finite Γ]
    (he : matOf e τW = tM16) {z : ℕ} (hz : z < 4)
    (hK : ∀ k : K, matOf e (π k) = rhoM ((θ k : GL (Fin 8) (ZMod 2)) : Mat8))
    (hDe : ∀ d ∈ D, ∃ ψ ∈ psiZ z, matOf e (π d) = 1 + embedM ψ)
    (hDe' : ∀ ψ ∈ psiZ z, ∃ d ∈ D, matOf e (π d) = 1 + embedM ψ) :
    D ≤ centralizer (π.ker : Set Γ) := by
  have hKc := h.K_le_centralizer he hDe
  set C := centralizer (π.ker : Set Γ) with hC
  have hCn : C.Normal := Subgroup.normal_centralizer
  set P : Mat8 → Prop := fun ψ => ∃ d ∈ D, d ∈ C ∧ matOf e (π d) = 1 + embedM ψ with hP
  have hP0 : P 0 := ⟨1, D.one_mem, C.one_mem, by rw [map_one, matOf_one, embedM_zero, add_zero]⟩
  have hPadd : ∀ x y, P x → P y → P (x + y) := by
    rintro x y ⟨d, hd, hdC, hdx⟩ ⟨d', hd', hd'C, hd'y⟩
    refine ⟨d * d', D.mul_mem hd hd', C.mul_mem hdC hd'C, ?_⟩
    rw [R3Hyp.matOf_mul h, hdx, hd'y, one_add_embedM_mul]
  have hPsum : ∀ l : List Mat8, (∀ x ∈ l, P x) → P l.sum := by
    intro l hl
    induction l with
    | nil => exact hP0
    | cons x l ih =>
      rw [List.sum_cons]
      exact hPadd _ _ (hl x (by simp)) (ih fun y hy => hl y (by simp [hy]))
  have hcomm : ∀ j < 2, ∀ ψ ∈ psiZ z, P (n0M j * ψ * n1M j + ψ) := by
    intro j hj ψ hψ
    obtain ⟨d, hd, hdψ⟩ := hDe' ψ hψ
    set ν := ((θ.symm (nuSU j) : K) : Γ)
    have hνK : ν ∈ K := (θ.symm (nuSU j)).2
    have hdd : d⁻¹ = d := inv_eq_of_mul_eq_one_right (h.D_mul_self hDe hd)
    refine ⟨ν * d * ν⁻¹ * d⁻¹, D.mul_mem (h.ν_norm j hj d hd) (D.inv_mem hd), ?_, ?_⟩
    · have h1 : d * ν⁻¹ * d⁻¹ ∈ C := hCn.conj_mem _ (C.inv_mem (hKc hνK)) d
      have h2 : ν * d * ν⁻¹ * d⁻¹ = ν * (d * ν⁻¹ * d⁻¹) := by group
      rw [h2]
      exact C.mul_mem (hKc hνK) h1
    · have hν : matOf e (π ν) = rhoM (toMat 8 8 (nuBits j)) := by
        rw [hK, MulEquiv.apply_symm_apply, coe_nuSU j hj]
      have hνi : matOf e (π ν⁻¹) = rhoM (toMat 8 8 (nuInvBits j)) := by
        rw [show ν⁻¹ = ((θ.symm (nuSU j)⁻¹ : K) : Γ) by simp [ν], hK, MulEquiv.apply_symm_apply,
          coe_nuSU_inv j hj]
      have hconj : rhoM (toMat 8 8 (nuBits j)) * (1 + embedM ψ) * rhoM (toMat 8 8 (nuInvBits j)) =
          1 + embedM (n0M j * ψ * n1M j) := by
        rw [mul_add, mul_one, add_mul, ← rhoM_mul, (wordCheck_spec.2 j hj).2.2, rhoM_one,
          rhoM_nu_embedM j hj]
      rw [R3Hyp.matOf_mul h, R3Hyp.matOf_mul h, R3Hyp.matOf_mul h, hν, hνi, hdd, hdψ, hconj,
        one_add_embedM_mul]
  have hbasis : ∀ c : Fin 8, P (candBlock z c) := by
    intro c
    rw [c1_spec hz c]
    refine hPsum _ fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have hb := c1W_bound hz c.isLt p hp
    have hmem : toMat 8 8 (basisBits z p.2) ∈ psiZ z := by
      rw [show p.2 = ((⟨p.2, hb.2⟩ : Fin 8) : ℕ) from rfl, toMat_basisBits]
      exact Submodule.subset_span ⟨_, rfl⟩
    exact hcomm p.1 hb.1 _ hmem
  have hspan : ∀ ψ ∈ psiZ z, P ψ := by
    intro ψ hψ
    refine Submodule.span_induction (p := fun ψ _ => P ψ) ?_ hP0 (fun x y _ _ => hPadd x y) ?_ hψ
    · rintro _ ⟨c, rfl⟩; exact hbasis c
    · intro a x _ hx
      rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) a with rfl | rfl
      · rw [zero_smul]; exact hP0
      · rw [one_smul]; exact hx
  intro d hd
  obtain ⟨ψ, hψ, hdψ⟩ := hDe d hd
  obtain ⟨d', hd', hd'C, hd'ψ⟩ := hspan ψ hψ
  rwa [h.eq_of_matOf hd hd' (hdψ.trans hd'ψ.symm)]

theorem R3Hyp.ker_le_center [Finite Γ]
    (he : matOf e τW = tM16) {z : ℕ} (hz : z < 4)
    (hK : ∀ k : K, matOf e (π k) = rhoM ((θ k : GL (Fin 8) (ZMod 2)) : Mat8))
    (hDe : ∀ d ∈ D, ∃ ψ ∈ psiZ z, matOf e (π d) = 1 + embedM ψ)
    (hDe' : ∀ ψ ∈ psiZ z, ∃ d ∈ D, matOf e (π d) = 1 + embedM ψ) :
    π.ker ≤ center Γ := by
  have hle : (⊤ : Subgroup Γ) ≤ centralizer (π.ker : Set Γ) := by
    rw [← h.gen]
    exact sup_le (h.K_le_centralizer he hDe) (h.D_le_centralizer he hz hK hDe hDe')
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro g
  exact (mem_centralizer_iff.mp (hle (Subgroup.mem_top g)) n hn).symm

end Main

end CFSG.EvenSmallLie.UnitarySix.YamadaPar

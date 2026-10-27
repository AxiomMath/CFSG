module

public import CFSG.RankThree.PartOne.SRC.RankOneSL2
public import CFSG.LinearAlgebra.UnitaryInvolutionIndex.Eigen
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic

public section

open scoped MatrixGroups

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG.SL2MinimalFaithful CFSG.RankThree.PartOne.SRC

theorem le_finrank_of_twisted_additive_family
    {F L V : Type*} [Field F] [Field L] [IsAlgClosed L] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    (f : F → Module.End L V) (hmul : ∀ s t, f (s + t) = f s * f t) (hone : f 0 = 1)
    (hss : ∀ t, (f t).IsSemisimple)
    (h : Module.End L V) (hinj : Function.Injective h) (c : F) (hc : c ≠ 0)
    (hh : ∀ t, f t * h = h * f (c * t))
    {m : ℕ} (hcm : ∀ k, 0 < k → k < m → c ^ k ≠ 1)
    (hnt : ∃ t, f t ≠ 1) : m ≤ Module.finrank L V := by
  classical
  have hcomm : ∀ s t, Commute (f s) (f t) := fun s t => by
    show f s * f t = f t * f s
    rw [← hmul, ← hmul, add_comm]
  let W : (F → L) → Submodule L V := fun χ => ⨅ t, (f t).maxGenEigenspace (χ t)
  have hW : ∀ χ v, v ∈ W χ ↔ ∀ t, f t v = χ t • v := by
    intro χ v
    simp only [W, Submodule.mem_iInf]
    refine forall_congr' fun t => ?_
    rw [(hss t).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace, Module.End.mem_eigenspace_iff]
  have hmaps : ∀ i j φ, Set.MapsTo (f i) ((f j).maxGenEigenspace φ) ((f j).maxGenEigenspace φ) :=
    fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
  have hind : iSupIndep W :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f hmaps
  have htop : ⨆ χ, W χ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
      (fun i j _ => hcomm i j) (fun z => Module.End.iSup_maxGenEigenspace_eq_top (f z))
  let _ : Fintype {χ // W χ ≠ ⊥} := hind.fintypeNeBotOfFiniteDimensional
  have hcard : Fintype.card {χ // W χ ≠ ⊥} ≤ Module.finrank L V :=
    hind.subtype_ne_bot_le_finrank
  have hχmul : ∀ χ, W χ ≠ ⊥ → ∀ s t, χ (s + t) = χ s * χ t := by
    intro χ hχ s t
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hχ
    have h1 := (hW χ v).mp hv
    have h2 : χ (s + t) • v = (χ s * χ t) • v := by
      rw [← h1 (s + t), hmul, Module.End.mul_apply, h1 t, map_smul, h1 s, smul_smul, mul_comm]
    exact smul_left_injective L hv0 h2
  have hχzero : ∀ χ, W χ ≠ ⊥ → χ 0 = 1 := by
    intro χ hχ
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hχ
    have h1 := (hW χ v).mp hv 0
    rw [hone, Module.End.one_apply] at h1
    have h2 : (1 : L) • v = χ 0 • v := by rw [one_smul]; exact h1
    exact (smul_left_injective L hv0 h2).symm
  have hχne : ∀ χ, W χ ≠ ⊥ → ∀ t, χ t ≠ 0 := by
    intro χ hχ t h0
    have := hχmul χ hχ t (-t)
    rw [add_neg_cancel, hχzero χ hχ, h0, zero_mul] at this
    exact one_ne_zero this
  obtain ⟨χ₀, hχ₀, t₀, ht₀⟩ : ∃ χ₀, W χ₀ ≠ ⊥ ∧ ∃ t₀, χ₀ t₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t, ht⟩ := hnt
    apply ht
    have hle : ⨆ χ, W χ ≤ LinearMap.eqLocus (f t) 1 := by
      refine iSup_le fun χ v hv => ?_
      rw [LinearMap.mem_eqLocus]
      by_cases hχ : W χ = ⊥
      · rw [hχ, Submodule.mem_bot] at hv
        subst hv
        simp
      · rw [(hW χ v).mp hv t, hcon χ hχ t, one_smul]
        rfl
    rw [htop] at hle
    exact LinearMap.eqLocus_eq_top.mp (top_le_iff.mp hle)
  have hpow : ∀ (k : ℕ) (t : F), f t * h ^ k = h ^ k * f (c ^ k * t) := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      have e : c * (c ^ k * t) = c ^ (k + 1) * t := by ring
      calc f t * h ^ (k + 1) = (f t * h ^ k) * h := by rw [pow_succ, mul_assoc]
        _ = h ^ k * (f (c ^ k * t) * h) := by rw [ih, mul_assoc]
        _ = h ^ k * (h * f (c * (c ^ k * t))) := by rw [hh]
        _ = h ^ (k + 1) * f (c ^ (k + 1) * t) := by rw [e, ← mul_assoc, ← pow_succ]
  have hmove : ∀ (k : ℕ) (v : V), v ∈ W χ₀ → (h ^ k) v ∈ W (fun t => χ₀ (c ^ k * t)) := by
    intro k v hv
    rw [hW]
    intro t
    have h1 := congrArg (fun T : Module.End L V => T v) (hpow k t)
    simp only [Module.End.mul_apply] at h1
    rw [h1, (hW χ₀ v).mp hv (c ^ k * t), map_smul]
  have hinjk : ∀ k : ℕ, Function.Injective (h ^ k) := by
    intro k
    rw [Module.End.coe_pow]
    exact hinj.iterate k
  have hne : ∀ k : ℕ, W (fun t => χ₀ (c ^ k * t)) ≠ ⊥ := by
    intro k
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hχ₀
    refine (Submodule.ne_bot_iff _).mpr ⟨(h ^ k) v, hmove k v hv, ?_⟩
    intro h0
    apply hv0
    exact hinjk k (by rw [h0, map_zero])
  have hdist : ∀ k k' : ℕ, k < k' → k' < m →
      (fun t => χ₀ (c ^ k * t)) ≠ (fun t => χ₀ (c ^ k' * t)) := by
    intro k k' hkk hk'm heq
    have hb : c ^ (k' - k) ≠ 1 := hcm (k' - k) (by omega) (by omega)
    have hu : ∀ u, χ₀ (c ^ (k' - k) * u) = χ₀ u := by
      intro u
      have hck : c ^ k ≠ 0 := pow_ne_zero _ hc
      have h1 := congrFun heq ((c ^ k)⁻¹ * u)
      have e1 : c ^ k * ((c ^ k)⁻¹ * u) = u := by field_simp
      have e2 : c ^ k' * ((c ^ k)⁻¹ * u) = c ^ (k' - k) * u := by
        have : c ^ k' = c ^ (k' - k) * c ^ k := by rw [← pow_add]; congr 1; omega
        rw [this]; field_simp
      rw [e1, e2] at h1
      exact h1.symm
    apply ht₀
    have hb1 : c ^ (k' - k) - 1 ≠ 0 := sub_ne_zero.mpr hb
    have hall : ∀ x, χ₀ x = 1 := by
      intro x
      have e : c ^ (k' - k) * ((c ^ (k' - k) - 1)⁻¹ * x) =
          (c ^ (k' - k) - 1)⁻¹ * x + x := by
        field_simp
        ring
      have h1 := hu ((c ^ (k' - k) - 1)⁻¹ * x)
      rw [e, hχmul χ₀ hχ₀] at h1
      exact mul_left_cancel₀ (hχne χ₀ hχ₀ _) (h1.trans (mul_one _).symm)
    exact hall t₀
  have hinjι : Function.Injective (fun k : Fin m =>
      (⟨fun t => χ₀ (c ^ (k : ℕ) * t), hne k⟩ : {χ // W χ ≠ ⊥})) := by
    intro k k' hkk
    by_contra hne'
    have hne'' : (k : ℕ) ≠ k' := fun h => hne' (Fin.ext h)
    have heq : (fun t => χ₀ (c ^ (k : ℕ) * t)) = (fun t => χ₀ (c ^ (k' : ℕ) * t)) :=
      congrArg Subtype.val hkk
    rcases lt_or_gt_of_ne hne'' with hlt | hgt
    · exact hdist k k' hlt k'.2 heq
    · exact hdist k' k hgt k.2 heq.symm
  calc m = Fintype.card (Fin m) := (Fintype.card_fin m).symm
    _ ≤ Fintype.card {χ // W χ ≠ ⊥} := Fintype.card_le_of_injective _ hinjι
    _ ≤ Module.finrank L V := hcard

theorem exists_endomorphism_embedding_algebraicClosure {k V₀ : Type*} [Field k] [AddCommGroup V₀]
    [Module k V₀] [Module.Finite k V₀] :
    ∃ Φ : Module.End k V₀ →+*
        Module.End (AlgebraicClosure k) (Fin (Module.finrank k V₀) → AlgebraicClosure k),
      Function.Injective Φ := by
  let b := Module.finBasis k V₀
  let Φ : Module.End k V₀ →+*
      Module.End (AlgebraicClosure k) (Fin (Module.finrank k V₀) → AlgebraicClosure k) :=
    (Matrix.toLinAlgEquiv' (R := AlgebraicClosure k)
        (n := Fin (Module.finrank k V₀))).toAlgHom.toRingHom.comp
      ((algebraMap k (AlgebraicClosure k)).mapMatrix.comp
        (LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom)
  refine ⟨Φ, ?_⟩
  intro x y hxy
  have h1 := Matrix.toLinAlgEquiv'.injective hxy
  have h2 := Matrix.map_injective (algebraMap k (AlgebraicClosure k)).injective h1
  exact (LinearMap.toMatrixAlgEquiv b).injective h2

theorem sl2_unipotent_pow_nsmul {F : Type*} [Field F] (t : F) (n : ℕ) :
    (unipotent t) ^ n = unipotent (n • t) := by
  induction n with
  | zero => simp [unipotent_zero]
  | succ n ih => rw [pow_succ, ih, ← unipotent_add, succ_nsmul]

theorem sl2_faithful_finrank {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hpF : ringChar F ≠ p) {V₀ : Type*} [AddCommGroup V₀] [Module (ZMod p) V₀]
    [Module.Finite (ZMod p) V₀] (ρ : SL(2, F) →* Module.End (ZMod p) V₀)
    (hρ : Function.Injective ρ) :
    (Nat.card F - 1) / 2 ≤ Module.finrank (ZMod p) V₀ := by
  classical
  obtain ⟨Φ, hΦ⟩ := exists_endomorphism_embedding_algebraicClosure (k := ZMod p) (V₀ := V₀)
  let R : SL(2, F) →* Module.End (AlgebraicClosure (ZMod p))
      (Fin (Module.finrank (ZMod p) V₀) → AlgebraicClosure (ZMod p)) := Φ.toMonoidHom.comp ρ
  have hR : Function.Injective R := hΦ.comp hρ
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf ζ = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_units]
  have hrprime : (ringChar F).Prime := CharP.prime_ringChar F
  have hrL : ((ringChar F : ℕ) : AlgebraicClosure (ZMod p)) ≠ 0 := by
    intro h0
    have h1 : p ∣ ringChar F := (CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod p)) p _).mp h0
    exact hpF ((Nat.prime_dvd_prime_iff_eq Fact.out hrprime).mp h1).symm
  have hrF : ((ringChar F : ℕ) : F) = 0 := ringChar.Nat.cast_ringChar
  have hmul : ∀ s t, R (unipotent (s + t)) = R (unipotent s) * R (unipotent t) := by
    intro s t
    rw [unipotent_add, map_mul]
  have hone : R (unipotent (0 : F)) = 1 := by rw [unipotent_zero, map_one]
  have hss : ∀ t : F, (R (unipotent t)).IsSemisimple := by
    intro t
    refine CFSG.UnitaryInvolutionIndex.isSemisimple_of_pow_eq_one hrL ?_
    rw [← map_pow, sl2_unipotent_pow_nsmul, nsmul_eq_mul, hrF, zero_mul, unipotent_zero, map_one]
  have hinj : Function.Injective (R (torus ζ)⁻¹) := by
    intro x y hxy
    have h1 : R (torus ζ) * R (torus ζ)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have := congrArg (R (torus ζ)) hxy
    simpa [← Module.End.mul_apply, h1] using this
  have hc : (ζ : F) ^ 2 ≠ 0 := pow_ne_zero 2 ζ.ne_zero
  have hh : ∀ t : F, R (unipotent t) * R (torus ζ)⁻¹ =
      R (torus ζ)⁻¹ * R (unipotent ((ζ : F) ^ 2 * t)) := by
    intro t
    rw [← map_mul, ← map_mul]
    congr 1
    have h1 := torus_mul_unipotent ζ t
    calc unipotent t * (torus ζ)⁻¹ = (torus ζ)⁻¹ * (torus ζ * unipotent t) * (torus ζ)⁻¹ := by group
      _ = (torus ζ)⁻¹ * (unipotent ((ζ : F) ^ 2 * t) * torus ζ) * (torus ζ)⁻¹ := by rw [h1]
      _ = (torus ζ)⁻¹ * unipotent ((ζ : F) ^ 2 * t) := by group
  have hcm : ∀ k : ℕ, 0 < k → k < (Nat.card F - 1) / 2 → ((ζ : F) ^ 2) ^ k ≠ 1 := by
    intro k hk0 hkm hk1
    have h1 : ζ ^ (2 * k) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, pow_mul]
      simpa using hk1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at h2
    have h3 := Nat.le_of_dvd (by omega) h2
    omega
  have hnt : ∃ t : F, R (unipotent t) ≠ 1 := by
    refine ⟨1, fun h1 => ?_⟩
    have h2 : unipotent (1 : F) = 1 := hR (by rw [h1, map_one])
    have h3 : unipotent (1 : F) = unipotent 0 := by rw [h2, unipotent_zero]
    exact one_ne_zero (unipotent_injective h3)
  have key := le_finrank_of_twisted_additive_family (F := F) (L := AlgebraicClosure (ZMod p))
    (V := Fin (Module.finrank (ZMod p) V₀) → AlgebraicClosure (ZMod p))
    (fun t => R (unipotent t)) hmul hone hss (R (torus ζ)⁻¹) hinj ((ζ : F) ^ 2) hc hh
    (m := (Nat.card F - 1) / 2) hcm hnt
  rwa [Module.finrank_fin_fun] at key

theorem sl2_faithful_weights_of_module {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hpF : ringChar F ≠ p) {W : Type} [CommGroup W] [Finite W] [hmod : Module (ZMod p) (Additive W)]
    {d : ℕ} (hd : Nat.card W = p ^ d) (ρ : SL(2, F) →* MulAut W) (hρ : Function.Injective ρ) :
    (Nat.card F - 1) / 2 ≤ d := by
  have : Module.Finite (ZMod p) (Additive W) := Module.Finite.of_finite
  let lin : MulAut W → Module.End (ZMod p) (Additive W) := fun σ =>
    AddMonoidHom.toZModLinearMap p
      { toFun := fun x => Additive.ofMul (σ (Additive.toMul x))
        map_zero' := by simp
        map_add' := fun x y => by simp }
  have hlin : ∀ (σ : MulAut W) (x : Additive W),
      Additive.toMul ((lin σ) x) = σ (Additive.toMul x) := fun σ x => rfl
  let ψ : MulAut W →* Module.End (ZMod p) (Additive W) :=
    { toFun := lin
      map_one' := LinearMap.ext fun x => by apply Additive.toMul.injective; rw [hlin]; rfl
      map_mul' := fun σ τ => LinearMap.ext fun x => by
        apply Additive.toMul.injective
        rw [Module.End.mul_apply, hlin, hlin, hlin]
        rfl }
  have hψ : Function.Injective ψ := by
    intro σ τ h
    ext x
    exact congrArg Additive.toMul (LinearMap.congr_fun h (Additive.ofMul x))
  have h1 := sl2_faithful_finrank hpF (ψ.comp ρ) (hψ.comp hρ)
  have h2 : Module.finrank (ZMod p) (Additive W) = d := by
    have := FiniteField.pow_finrank_eq_natCard p (Additive W)
    have h3 : Nat.card (Additive W) = p ^ d := hd
    rw [h3] at this
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le this
  rwa [h2] at h1

theorem sl2_faithful_weights {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) {p : ℕ}
    [Fact p.Prime] (hpF : ringChar F ≠ p) {W : Type} [CommGroup W] [Finite W]
    (hexp : ∀ w : W, w ^ p = 1) {d : ℕ} (hd : Nat.card W = p ^ d) (ρ : SL(2, F) →* MulAut W)
    (hρ : Function.Injective ρ) : (Nat.card F - 1) / 2 ≤ d := by
  have _ := hodd
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hexpA : ∀ x : Additive W, p • x = 0 := by
    intro x
    rw [← ofMul_toMul x, ← ofMul_pow, hexp, ofMul_one]
  exact sl2_faithful_weights_of_module (W := W) (hmod := AddCommGroup.zmodModule hexpA) hpF hd ρ hρ

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

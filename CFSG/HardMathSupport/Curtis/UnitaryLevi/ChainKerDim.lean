module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.DualPieceScalar
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.FixedSpaceDim
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.SemilinearPm
public import Mathlib.Tactic.Basify

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module

variable {K : Type*} [Field K] {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def sclGL (a : Kˣ) (e : LinearMap.GeneralLinearGroup K V) :
    LinearMap.GeneralLinearGroup K V :=
  Units.map (algebraMap K (Module.End K V)).toMonoidHom a * e

theorem coe_sclGL (a : Kˣ) (e : LinearMap.GeneralLinearGroup K V) :
    ((sclGL a e : LinearMap.GeneralLinearGroup K V) : Module.End K V) =
      (a : K) • (e : Module.End K V) := by
  simp [sclGL, Algebra.smul_def]

theorem sclGL_pow_three {a : Kˣ} (ha : a ^ 3 = 1) {e : LinearMap.GeneralLinearGroup K V}
    (he : e ^ 3 = 1) : sclGL a e ^ 3 = 1 := by
  have hc : Commute (Units.map (algebraMap K (Module.End K V)).toMonoidHom a) e :=
    Units.ext (Algebra.commutes (a : K) (e : Module.End K V))
  rw [sclGL, hc.mul_pow, ← map_pow, ha, he, map_one, mul_one]

theorem quotAct_eq_smul {F F' : Submodule K V} {x E : Module.End K V} (a : K) (hx : x = a • E)
    (hF : ∀ v ∈ F, x v ∈ F) (hF' : ∀ v ∈ F', x v ∈ F') (hFe : ∀ v ∈ F, E v ∈ F)
    (hFe' : ∀ v ∈ F', E v ∈ F') : quotAct x hF hF' = a • quotAct E hFe hFe' := by
  subst hx
  refine LinearMap.ext fun q => ?_
  induction q using Submodule.Quotient.induction_on with
  | H u =>
    rw [quotAct_mk]
    show _ = a • quotAct E hFe hFe' (Submodule.Quotient.mk u)
    rw [quotAct_mk, ← Submodule.Quotient.mk_smul]
    rfl

theorem finrank_ker_quotAct_congr {F₁ F₁' F₂ F₂' : Submodule K V} (h : F₁ = F₂) (h' : F₁' = F₂')
    (g : Module.End K V) (hF₁ : ∀ v ∈ F₁, g v ∈ F₁) (hF₁' : ∀ v ∈ F₁', g v ∈ F₁')
    (hF₂ : ∀ v ∈ F₂, g v ∈ F₂) (hF₂' : ∀ v ∈ F₂', g v ∈ F₂') :
    finrank K (LinearMap.ker (quotAct g hF₁ hF₁' - 1)) =
      finrank K (LinearMap.ker (quotAct g hF₂ hF₂' - 1)) := by
  subst h h'
  rfl

theorem ker_inv_smul_sub_one {M : Type*} [AddCommGroup M] [Module K M] (A : Module.End K M)
    (lam : Kˣ) :
    LinearMap.ker (((lam⁻¹ : Kˣ) : K) • A - 1) = LinearMap.ker (A - (lam : K) • 1) := by
  have : ((lam⁻¹ : Kˣ) : K) • A - 1 = ((lam⁻¹ : Kˣ) : K) • (A - (lam : K) • 1) := by
    rw [smul_sub, smul_smul, Units.inv_mul, one_smul]
  rw [this, LinearMap.ker_smul _ _ (Units.ne_zero _)]

open scoped Classical in
theorem finrank_ker_quotEnd_of_scalar [FiniteDimensional K V] {x : LinearMap.GeneralLinearGroup K V}
    {F F' : Submodule K V} (hFF' : F ≤ F') (hx : x ∈ stabPair F F') (c : K)
    (hc : ∀ v ∈ F', (x : Module.End K V) v - c • v ∈ F) :
    finrank K (LinearMap.ker (quotEnd F F' ⟨x, hx⟩ - 1)) =
      if c = 1 then finrank K F' - finrank K F else 0 :=
  finrank_ker_quotAct_sub_one_of_scalar hFF' hx.1 hx.2.1 c hc


theorem chainFil_monotone_of_lt {B : V →ₛₗ[σ] V →ₗ[K] K} {s : ℕ} (hs : 1 ≤ s)
    {W : ℕ → Submodule K V} (hmono : ∀ j, j < s → W j ≤ W (j + 1))
    (hiso : W s ≤ (W s).orthogonalBilin B) : Monotone (chainFil B s W) := by
  refine monotone_nat_of_le_succ fun i => ?_
  by_cases h0 : i = 0
  · subst h0
    rw [chainFil_zero]
    exact bot_le
  by_cases h1 : i < s
  · rw [chainFil_of_le (by omega) (by omega), chainFil_of_le (by omega) (by omega)]
    exact hmono i h1
  by_cases h2 : i = s
  · subst h2
    rw [chainFil_of_le (by omega) le_rfl, chainFil_of_dual (by omega) (by omega)]
    have : 2 * i + 1 - (i + 1) = i := by omega
    rw [this]
    exact hiso
  by_cases h3 : i < 2 * s
  · rw [chainFil_of_dual (by omega) (by omega), chainFil_of_dual (by omega) (by omega)]
    have e1 : 2 * s + 1 - (i + 1) = 2 * s - i := by omega
    have e2 : 2 * s + 1 - i = (2 * s - i) + 1 := by omega
    rw [e1, e2]
    intro v hv
    rw [Submodule.mem_orthogonalBilin] at hv ⊢
    exact fun w hw => hv w (hmono _ (by omega) hw)
  · rw [chainFil_of_gt (by omega : 2 * s < i + 1)]
    exact le_top


theorem sum_range_two_mul_succ (f : ℕ → ℕ) (s : ℕ) :
    ∑ i ∈ Finset.range (2 * s + 1), f i =
      ∑ i ∈ Finset.range s, f i + f s + ∑ j ∈ Finset.range s, f (s + 1 + (s - 1 - j)) := by
  have h2 : ∑ j ∈ Finset.range s, f (s + 1 + (s - 1 - j)) = ∑ j ∈ Finset.range s, f (s + 1 + j) :=
    Finset.sum_range_reflect (fun k => f (s + 1 + k)) s
  have h3 : ∑ k ∈ Finset.range s, f (s + (k + 1)) = ∑ k ∈ Finset.range s, f (s + 1 + k) :=
    Finset.sum_congr rfl fun k _ => by rw [show s + (k + 1) = s + 1 + k by ring]
  rw [h2, show 2 * s + 1 = s + (s + 1) by ring, Finset.sum_range_add, Finset.sum_range_succ', h3]
  simp only [add_zero]
  ring

theorem inv_mul_eq_one_iff (lam : Kˣ) (y : K) : ((lam⁻¹ : Kˣ) : K) * y = 1 ↔ y = lam := by
  rw [Units.val_inv_eq_inv_val, inv_mul_eq_one₀ (Units.ne_zero lam)]
  exact eq_comm

theorem mono_of_lt_chain {s : ℕ} {W : ℕ → Submodule K V}
    (hlt : ∀ j, 1 ≤ j → j ≤ s → W (j - 1) < W j) : ∀ j, j < s → W j ≤ W (j + 1) := fun j hj => by
  simpa using (hlt (j + 1) (by omega) (by omega)).le

section Main

variable [CharP K 2] [FiniteDimensional K V] {B : V →ₛₗ[σ] V →ₗ[K] K} {s : ℕ}
  {W : ℕ → Submodule K V} {U : Subgroup (LinearMap.GeneralLinearGroup K V)}

open scoped Classical in
theorem finrank_ker_chain_eq_range (hσ : Function.Surjective σ) (hB : B.SeparatingLeft)
    (hs : 1 ≤ s) (hW0 : W 0 = ⊥) (hmono : ∀ j, j < s → W j ≤ W (j + 1))
    (hiso : W s ≤ (W s).orthogonalBilin B) (h : ChainStabData B s W U) (hK : Nat.card K = 4)
    {e : LinearMap.GeneralLinearGroup K V} (he : e ∈ U) (he3 : e ^ 3 = 1) (c : ℕ → K)
    (hc : ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j, (e : Module.End K V) v - c j • v ∈ W (j - 1))
    (lam : Kˣ) :
    finrank K (LinearMap.ker ((e : Module.End K V) - (lam : K) • 1)) =
      ∑ i ∈ Finset.range s, finrank K (PieceQ (W i) (W (i + 1))) *
          ((if c (i + 1) = (lam : K) then 1 else 0) +
            (if (σ (c (i + 1)))⁻¹ = (lam : K) then 1 else 0)) +
        finrank K (LinearMap.ker (((perpGL B (W s) ⟨e, h.mem_isoStab hs he⟩ :
          LinearMap.GeneralLinearGroup K (perpQuot B (W s))) :
            Module.End K (perpQuot B (W s))) - (lam : K) • 1)) := by
  set x := sclGL lam⁻¹ e with hxdef
  have hxc : ((x : LinearMap.GeneralLinearGroup K V) : Module.End K V) =
      ((lam⁻¹ : Kˣ) : K) • (e : Module.End K V) := coe_sclGL _ _
  have hxapp : ∀ v, ((x : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
      ((lam⁻¹ : Kˣ) : K) • (e : Module.End K V) v := fun v => by rw [hxc]; rfl
  have hx3 : x ^ 3 = 1 := sclGL_pow_three (units_pow_three_eq_one_of_card_four hK lam⁻¹) he3
  have hker : LinearMap.ker ((e : Module.End K V) - (lam : K) • 1) =
      LinearMap.ker (((x : LinearMap.GeneralLinearGroup K V) : Module.End K V) - 1) := by
    rw [hxc, ker_inv_smul_sub_one]
  have hFstab : ∀ i, ∀ v ∈ chainFil B s W i,
      ((x : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈ chainFil B s W i := by
    intro i v hv
    rw [hxapp]
    exact Submodule.smul_mem _ _ (chainFil_stable hW0 he3 (h.iso e he) (h.stab e he) i v hv)
  have hmonoF := chainFil_monotone_of_lt hs hmono hiso
  let P : ℕ → ℕ := fun i => finrank K (LinearMap.ker (quotEnd (chainFil B s W i)
    (chainFil B s W (i + 1)) ⟨x, mem_stabPair_of_pow_three hx3 (hFstab i) (hFstab (i + 1))⟩ - 1))
  have key : finrank K (LinearMap.ker (((x : LinearMap.GeneralLinearGroup K V) :
      Module.End K V) - 1)) = ∑ i ∈ Finset.range (2 * s + 1), P i :=
    finrank_ker_eq_sum_pieces' (N := 2 * s + 1) x hx3 (chainFil B s W) (chainFil_zero B s W)
      hmonoF (chainFil_of_gt (by omega)) hFstab
  have hscal : ∀ i < s, ∀ hm : x ∈ stabPair (chainFil B s W i) (chainFil B s W (i + 1)),
      finrank K (LinearMap.ker (quotEnd (chainFil B s W i) (chainFil B s W (i + 1)) ⟨x, hm⟩ - 1)) =
        finrank K (PieceQ (W i) (W (i + 1))) * (if c (i + 1) = (lam : K) then 1 else 0) := by
    intro i hi hm
    have hFF : chainFil B s W i ≤ chainFil B s W (i + 1) := hmonoF (Nat.le_succ i)
    have hc' : ∀ v ∈ chainFil B s W (i + 1),
        ((x : LinearMap.GeneralLinearGroup K V) : Module.End K V) v -
          (((lam⁻¹ : Kˣ) : K) * c (i + 1)) • v ∈ chainFil B s W i := by
      intro v hv
      rw [chainFil_eq_of_le hW0 (by omega : i + 1 ≤ s)] at hv
      rw [chainFil_eq_of_le hW0 (by omega : i ≤ s)]
      have h1 := hc (i + 1) (by omega) (by omega) v hv
      simp only [Nat.add_sub_cancel] at h1
      have h2 := (W i).smul_mem ((lam⁻¹ : Kˣ) : K) h1
      convert h2 using 1
      rw [hxapp, smul_sub, smul_smul]
    rw [finrank_ker_quotEnd_of_scalar hFF hm _ hc',
      chainFil_eq_of_le hW0 (by omega : i + 1 ≤ s), chainFil_eq_of_le hW0 (by omega : i ≤ s)]
    have hp := finrank_pieceQ_add (hmono i hi)
    by_cases hcl : c (i + 1) = (lam : K)
    · have a1 := (inv_mul_eq_one_iff lam _).2 hcl
      simp only [a1, ite_true]
      simp only [hcl, ite_true, mul_one]
      omega
    · have a1 := (inv_mul_eq_one_iff lam _).not.2 hcl
      simp only [a1, ite_false]
      simp only [hcl, ite_false, mul_zero]
  have hdual : ∀ j < s, ∀ hm : x ∈ stabPair (chainFil B s W (s + 1 + (s - 1 - j)))
      (chainFil B s W (s + 1 + (s - 1 - j) + 1)),
      finrank K (LinearMap.ker (quotEnd (chainFil B s W (s + 1 + (s - 1 - j)))
        (chainFil B s W (s + 1 + (s - 1 - j) + 1)) ⟨x, hm⟩ - 1)) =
        finrank K (PieceQ (W j) (W (j + 1))) *
          (if (σ (c (j + 1)))⁻¹ = (lam : K) then 1 else 0) := by
    intro j hj hm
    have e1 : chainFil B s W (s + 1 + (s - 1 - j)) = (W (j + 1)).orthogonalBilin B := by
      have := chainFil_eq_dual hW0 (B := B) (s := s) (a := j + 1) (by omega)
      rwa [show 2 * s + 1 - (j + 1) = s + 1 + (s - 1 - j) by omega] at this
    have e2 : chainFil B s W (s + 1 + (s - 1 - j) + 1) = (W j).orthogonalBilin B := by
      have := chainFil_eq_dual hW0 (B := B) (s := s) (a := j) (by omega)
      rwa [show 2 * s + 1 - j = s + 1 + (s - 1 - j) + 1 by omega] at this
    have hFF := hmonoF (Nat.le_succ (s + 1 + (s - 1 - j)))
    have hinv : ∀ v ∈ W (j + 1),
        ((e⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈ W (j + 1) :=
      h.stab e⁻¹ (U.inv_mem he) (j + 1) (by omega) (by omega)
    have hcj : ∀ v ∈ W (j + 1), (e : Module.End K V) v - c (j + 1) • v ∈ W j := by
      intro v hv
      simpa using hc (j + 1) (by omega) (by omega) v hv
    have hc' : ∀ v ∈ chainFil B s W (s + 1 + (s - 1 - j) + 1),
        ((x : LinearMap.GeneralLinearGroup K V) : Module.End K V) v -
          (((lam⁻¹ : Kˣ) : K) * (σ (c (j + 1)))⁻¹) • v ∈
            chainFil B s W (s + 1 + (s - 1 - j)) := by
      intro v hv
      rw [e2] at hv
      rw [e1]
      have h1 := dual_piece_scalar e (h.iso e he) hinv (c (j + 1)) hcj v hv
      have h2 := Submodule.smul_mem _ ((lam⁻¹ : Kˣ) : K) h1
      convert h2 using 1
      rw [hxapp, smul_sub, smul_smul]
    rw [finrank_ker_quotEnd_of_scalar hFF hm _ hc', e1, e2,
      finrank_orthogonalBilin_eq hσ hB, finrank_orthogonalBilin_eq hσ hB]
    have hp := finrank_pieceQ_add (hmono j hj)
    have h3 := Submodule.finrank_le (W (j + 1))
    by_cases hcl : (σ (c (j + 1)))⁻¹ = (lam : K)
    · have a1 := (inv_mul_eq_one_iff lam _).2 hcl
      simp only [a1, ite_true]
      simp only [hcl, ite_true, mul_one]
      omega
    · have a1 := (inv_mul_eq_one_iff lam _).not.2 hcl
      simp only [a1, ite_false]
      simp only [hcl, ite_false, mul_zero]
  have htail : ∀ hm : x ∈ stabPair (chainFil B s W s) (chainFil B s W (s + 1)),
      finrank K (LinearMap.ker (quotEnd (chainFil B s W s) (chainFil B s W (s + 1))
        ⟨x, hm⟩ - 1)) =
        finrank K (LinearMap.ker (((perpGL B (W s) ⟨e, h.mem_isoStab hs he⟩ :
          LinearMap.GeneralLinearGroup K (perpQuot B (W s))) :
            Module.End K (perpQuot B (W s))) - (lam : K) • 1)) := by
    intro hm
    have e1 : chainFil B s W s = W s := chainFil_of_le hs le_rfl
    have e2 : chainFil B s W (s + 1) = (W s).orthogonalBilin B := by
      have := chainFil_eq_dual hW0 (B := B) (s := s) (a := s) le_rfl
      rwa [show 2 * s + 1 - s = s + 1 by omega] at this
    have hWe : ∀ v ∈ W s, (e : Module.End K V) v ∈ W s := h.stab e he s hs le_rfl
    have hWe' : ∀ v ∈ (W s).orthogonalBilin B, (e : Module.End K V) v ∈ (W s).orthogonalBilin B :=
      fun v hv => apply_mem_orthogonalBilin (h.mem_isoStab hs he) hv
    show finrank K (LinearMap.ker (quotAct ((x : LinearMap.GeneralLinearGroup K V) :
      Module.End K V) hm.1 hm.2.1 - 1)) = _
    refine (finrank_ker_quotAct_congr e1 e2 _ hm.1 hm.2.1
      (fun v hv => by rw [hxapp]; exact Submodule.smul_mem _ _ (hWe v hv))
      (fun v hv => by rw [hxapp]; exact Submodule.smul_mem _ _ (hWe' v hv))).trans ?_
    rw [quotAct_eq_smul ((lam⁻¹ : Kˣ) : K) hxc _ _ hWe hWe', ker_inv_smul_sub_one]
    rfl
  rw [hker, key, sum_range_two_mul_succ]
  have hA : ∑ i ∈ Finset.range s, P i = ∑ i ∈ Finset.range s,
      finrank K (PieceQ (W i) (W (i + 1))) * (if c (i + 1) = (lam : K) then 1 else 0) :=
    Finset.sum_congr rfl fun i hi => hscal i (Finset.mem_range.1 hi) _
  have hD : ∑ j ∈ Finset.range s, P (s + 1 + (s - 1 - j)) = ∑ j ∈ Finset.range s,
      finrank K (PieceQ (W j) (W (j + 1))) *
        (if (σ (c (j + 1)))⁻¹ = (lam : K) then 1 else 0) :=
    Finset.sum_congr rfl fun j hj => hdual j (Finset.mem_range.1 hj) _
  have hT : P s = finrank K (LinearMap.ker (((perpGL B (W s) ⟨e, h.mem_isoStab hs he⟩ :
      LinearMap.GeneralLinearGroup K (perpQuot B (W s))) :
        Module.End K (perpQuot B (W s))) - (lam : K) • 1)) := htail _
  rw [hA, hD, hT]
  simp only [mul_add, Finset.sum_add_distrib]
  ring


open scoped Classical in
theorem finrank_ker_chain_eq (hσ : Function.Surjective σ) (hB : B.SeparatingLeft)
    (hs : 1 ≤ s) (hW0 : W 0 = ⊥) (hmono : ∀ j, j < s → W j ≤ W (j + 1))
    (hiso : W s ≤ (W s).orthogonalBilin B) (h : ChainStabData B s W U) (hK : Nat.card K = 4)
    {e : LinearMap.GeneralLinearGroup K V} (he : e ∈ U) (he3 : e ^ 3 = 1) (c : ℕ → K)
    (hc : ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j, (e : Module.End K V) v - c j • v ∈ W (j - 1))
    (lam : Kˣ) :
    finrank K (LinearMap.ker ((e : Module.End K V) - (lam : K) • 1)) =
      ∑ j ∈ Finset.Icc 1 s, finrank K (PieceQ (W (j - 1)) (W j)) *
          ((if c j = (lam : K) then 1 else 0) + (if (σ (c j))⁻¹ = (lam : K) then 1 else 0)) +
        finrank K (LinearMap.ker (((perpGL B (W s) ⟨e, h.mem_isoStab hs he⟩ :
          LinearMap.GeneralLinearGroup K (perpQuot B (W s))) :
            Module.End K (perpQuot B (W s))) - (lam : K) • 1)) := by
  rw [finrank_ker_chain_eq_range hσ hB hs hW0 hmono hiso h hK he he3 c hc lam]
  congr 1
  rw [Finset.range_eq_Ico]
  have := Finset.sum_Ico_add' (fun j => finrank K (PieceQ (W (j - 1)) (W j)) *
    ((if c j = (lam : K) then 1 else 0) + (if (σ (c j))⁻¹ = (lam : K) then 1 else 0))) 0 s 1
  have h' : Finset.Ico (0 + 1) (s + 1) = Finset.Icc 1 s := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [h'] at this
  rw [← this]
  rfl

open scoped Classical in
theorem finrank_ker_chain_eq_scalOf (hσ : Function.Surjective σ) (hB : B.SeparatingLeft)
    (hs : 1 ≤ s) (hW0 : W 0 = ⊥) (hmono : ∀ j, j < s → W j ≤ W (j + 1))
    (hiso : W s ≤ (W s).orthogonalBilin B) (h : ChainStabData B s W U) (hK : Nat.card K = 4)
    (u : U) (hu3 : (u : LinearMap.GeneralLinearGroup K V) ^ 3 = 1) (lam : Kˣ) :
    finrank K (LinearMap.ker (((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) -
        (lam : K) • 1)) =
      ∑ i : Fin s, finrank K (PieceQ (W i) (W (i + 1))) *
          ((if h.scalOf u i = (lam : K) then 1 else 0) +
            (if (σ (h.scalOf u i))⁻¹ = (lam : K) then 1 else 0)) +
        finrank K (LinearMap.ker (((perpGL B (W s) ⟨u, h.mem_isoStab hs u.2⟩ :
          LinearMap.GeneralLinearGroup K (perpQuot B (W s))) :
            Module.End K (perpQuot B (W s))) - (lam : K) • 1)) := by
  let c : ℕ → K := fun j => if hj : 1 ≤ j ∧ j ≤ s then h.scalOf u ⟨j - 1, by omega⟩ else 0
  have hc : ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j,
      ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) v - c j • v ∈ W (j - 1) := by
    intro j hj1 hjs v hv
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have := h.scalOf_spec u ⟨i, by omega⟩ v hv
    simpa [c, show 1 ≤ i + 1 ∧ i + 1 ≤ s from ⟨by omega, by omega⟩] using this
  have := finrank_ker_chain_eq_range hσ hB hs hW0 hmono hiso h hK u.2 hu3 c hc lam
  rw [this]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun i => finrank K (PieceQ (W i) (W (i + 1))) *
    ((if c (i + 1) = (lam : K) then 1 else 0) + (if (σ (c (i + 1)))⁻¹ = (lam : K) then 1 else 0)))
    s]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hci : c (i.1 + 1) = h.scalOf u i := by
    simp [c, show 1 ≤ i.1 + 1 ∧ i.1 + 1 ≤ s from ⟨by omega, by omega⟩]
  rw [hci]

omit [CharP K 2] in
open scoped Classical in
theorem finrank_ker_scalar_sub {M : Type*} [AddCommGroup M] [Module K M] (hM : finrank K M = 1)
    (A : Module.End K M) (ν lam : K) (hA : A = ν • LinearMap.id) :
    finrank K (LinearMap.ker (A - lam • 1)) = if ν = lam then 1 else 0 := by
  classical
  have h1 : A - lam • 1 = (ν - lam) • (1 : Module.End K M) := by
    rw [hA, sub_smul]; rfl
  rw [h1]
  by_cases hν : ν = lam
  · subst hν
    rw [sub_self, zero_smul, LinearMap.ker_zero, finrank_top, hM]
    simp
  · simp only [hν, ite_false]
    rw [LinearMap.ker_smul _ _ (sub_ne_zero.2 hν)]
    have : LinearMap.ker (1 : Module.End K M) = ⊥ := LinearMap.ker_id
    rw [this, finrank_bot]


omit [CharP K 2] [FiniteDimensional K V] in
theorem exists_units_scalar_of_finrank_one {M : Type*} [AddCommGroup M] [Module K M]
    (hM : finrank K M = 1) (A : LinearMap.GeneralLinearGroup K M) :
    ∃ ν : Kˣ, ∀ m, (A : Module.End K M) m = (ν : K) • m := by
  obtain ⟨ν, hν, -⟩ := (A : Module.End K M).existsUnique_eq_smul_id_of_finrank_eq_one hM
  have hν0 : ν ≠ 0 := by
    rintro rfl
    have : Module.Finite K M := Module.finite_of_finrank_pos (by omega : 0 < finrank K M)
    obtain ⟨m, hm⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (by omega : 0 < finrank K M)
    apply hm
    have h1 := coe_apply_inv_apply A m
    rw [hν] at h1
    simpa using h1.symm
  exact ⟨Units.mk0 ν hν0, fun m => by rw [hν]; rfl⟩

open scoped Classical in
theorem finrank_ker_chain_eq_of_finrank_one (hσ : Function.Surjective σ) (hB : B.SeparatingLeft)
    (hs : 1 ≤ s) (hW0 : W 0 = ⊥) (hmono : ∀ j, j < s → W j ≤ W (j + 1))
    (hiso : W s ≤ (W s).orthogonalBilin B) (h : ChainStabData B s W U) (hK : Nat.card K = 4)
    {e : LinearMap.GeneralLinearGroup K V} (he : e ∈ U) (he3 : e ^ 3 = 1) (c : ℕ → K)
    (hc : ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j, (e : Module.End K V) v - c j • v ∈ W (j - 1))
    (hM : finrank K (perpQuot B (W s)) = 1) (lam : Kˣ) :
    ∃ ν : Kˣ, (∀ m, ((perpGL B (W s) ⟨e, h.mem_isoStab hs he⟩ :
        LinearMap.GeneralLinearGroup K (perpQuot B (W s))) :
          Module.End K (perpQuot B (W s))) m = (ν : K) • m) ∧
      finrank K (LinearMap.ker ((e : Module.End K V) - (lam : K) • 1)) =
        ∑ j ∈ Finset.Icc 1 s, finrank K (PieceQ (W (j - 1)) (W j)) *
            ((if c j = (lam : K) then 1 else 0) +
              (if (σ (c j))⁻¹ = (lam : K) then 1 else 0)) +
          (if (ν : K) = (lam : K) then 1 else 0) := by
  obtain ⟨ν, hν⟩ := exists_units_scalar_of_finrank_one hM (perpGL B (W s) ⟨e, h.mem_isoStab hs he⟩)
  refine ⟨ν, hν, ?_⟩
  rw [finrank_ker_chain_eq hσ hB hs hW0 hmono hiso h hK he he3 c hc lam,
    finrank_ker_scalar_sub hM _ (ν : K) (lam : K) (LinearMap.ext fun m => by simpa using hν m)]

open scoped Classical in
theorem finrank_ker_chain_eq_scalOf_of_finrank_one (hσ : Function.Surjective σ)
    (hB : B.SeparatingLeft) (hs : 1 ≤ s) (hW0 : W 0 = ⊥) (hmono : ∀ j, j < s → W j ≤ W (j + 1))
    (hiso : W s ≤ (W s).orthogonalBilin B) (h : ChainStabData B s W U) (hK : Nat.card K = 4)
    (u : U) (hu3 : (u : LinearMap.GeneralLinearGroup K V) ^ 3 = 1)
    (hM : finrank K (perpQuot B (W s)) = 1) (lam : Kˣ) :
    ∃ ν : Kˣ, (∀ m, ((perpGL B (W s) ⟨u, h.mem_isoStab hs u.2⟩ :
        LinearMap.GeneralLinearGroup K (perpQuot B (W s))) :
          Module.End K (perpQuot B (W s))) m = (ν : K) • m) ∧
      finrank K (LinearMap.ker (((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) -
          (lam : K) • 1)) =
        ∑ i : Fin s, finrank K (PieceQ (W i) (W (i + 1))) *
            ((if h.scalOf u i = (lam : K) then 1 else 0) +
              (if (σ (h.scalOf u i))⁻¹ = (lam : K) then 1 else 0)) +
          (if (ν : K) = (lam : K) then 1 else 0) := by
  obtain ⟨ν, hν⟩ := exists_units_scalar_of_finrank_one hM (perpGL B (W s) ⟨u, h.mem_isoStab hs u.2⟩)
  refine ⟨ν, hν, ?_⟩
  rw [finrank_ker_chain_eq_scalOf hσ hB hs hW0 hmono hiso h hK u hu3 lam,
    finrank_ker_scalar_sub hM _ (ν : K) (lam : K) (LinearMap.ext fun m => by simpa using hν m)]

end Main

end CFSG.HardMathSupport.Curtis.UnitaryLevi

module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOneAut
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSchreier

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open Submodule
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K]

omit [Field K] in
theorem perm_inv_apply_of_fix {α : Type} {ψ : Equiv.Perm α} {x : α} (hψ : ψ x = x) :
    ψ⁻¹ x = x := by
  rw [Equiv.Perm.inv_eq_iff_eq, hψ]

section Conj

variable (h : UnitaryFieldData p f K) {ψ : Equiv.Perm (hypIsotropicLines h 1 1)}

theorem conj_mem_rkOneG (hψ : ψ ∈ lineNormalizer h 1 1)
    {x : Equiv.Perm (hypIsotropicLines h 1 1)} (hx : x ∈ rkOneG h) : ψ * x * ψ⁻¹ ∈ rkOneG h :=
  (Subgroup.mem_normalizer_iff.mp hψ x).mp hx

theorem conj_mem_rkOneGInf (hψ : ψ ∈ lineNormalizer h 1 1) (hψi : ψ (infL h) = infL h)
    {x : Equiv.Perm (hypIsotropicLines h 1 1)} (hx : x ∈ rkOneGInf h) :
    ψ * x * ψ⁻¹ ∈ rkOneGInf h := by
  obtain ⟨hxG, hxi⟩ := (mem_rkOneGInf h).mp hx
  refine (mem_rkOneGInf h).mpr ⟨conj_mem_rkOneG h hψ hxG, ?_⟩
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_inv_apply_of_fix hψi, hxi, hψi]

theorem conj_mem_rkOneGZero (hψ : ψ ∈ lineNormalizer h 1 1) (hψ0 : ψ (zeroL h) = zeroL h)
    {x : Equiv.Perm (hypIsotropicLines h 1 1)} (hx : x ∈ rkOneGZero h) :
    ψ * x * ψ⁻¹ ∈ rkOneGZero h := by
  obtain ⟨hxG, hx0⟩ := (mem_rkOneGZero h).mp hx
  refine (mem_rkOneGZero h).mpr ⟨conj_mem_rkOneG h hψ hxG, ?_⟩
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_inv_apply_of_fix hψ0, hx0, hψ0]

theorem conj_mem_rkOneT (hψ : ψ ∈ lineNormalizer h 1 1) (hψi : ψ (infL h) = infL h)
    (hψ0 : ψ (zeroL h) = zeroL h) {x : Equiv.Perm (hypIsotropicLines h 1 1)}
    (hx : x ∈ rkOneT h) : ψ * x * ψ⁻¹ ∈ rkOneT h := by
  rw [← rkOneGInf_inf_rkOneGZero h] at hx ⊢
  exact ⟨conj_mem_rkOneGInf h hψ hψi hx.1, conj_mem_rkOneGZero h hψ hψ0 hx.2⟩

theorem conj_mem_rkOneUStar (hψ : ψ ∈ lineNormalizer h 1 1) (hψi : ψ (infL h) = infL h)
    {u : Equiv.Perm (hypIsotropicLines h 1 1)} (hu : u ∈ rkOneUStar h) :
    ψ * u * ψ⁻¹ ∈ rkOneUStar h := by
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup (Equiv.Perm (hypIsotropicLines h 1 1)),
      Q = (rkOneUStar h).map (MulAut.conj ψ).toMonoidHom := ⟨_, rfl⟩
  have hQmem : ∀ v ∈ rkOneUStar h, ψ * v * ψ⁻¹ ∈ Q := fun v hv => by
    rw [hQ]
    exact ⟨v, hv, MulAut.conj_apply ψ v⟩
  have hle : Q ≤ rkOneGInf h := by
    rw [hQ]
    rintro _ ⟨v, hv, rfl⟩
    exact conj_mem_rkOneGInf h hψ hψi (rkOneUStar_le_rkOneGInf h hv)
  have hcardQ : Nat.card Q = (p ^ f) ^ 3 := by
    rw [hQ, Subgroup.card_map_of_injective (MulAut.conj ψ).injective]
    exact card_rkOneUStar h
  have hcard : Nat.card (Q.subgroupOf (rkOneGInf h)) = p ^ (3 * f) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcardQ, ← pow_mul, mul_comm]
  obtain ⟨P, hP⟩ := (IsPGroup.of_card hcard).exists_le_sylow
  have hmem : (⟨ψ * u * ψ⁻¹, hle (hQmem u hu)⟩ : rkOneGInf h) ∈ Q.subgroupOf (rkOneGInf h) :=
    Subgroup.mem_subgroupOf.mpr (hQmem u hu)
  have h1 : (⟨ψ * u * ψ⁻¹, hle (hQmem u hu)⟩ : rkOneGInf h) ∈
      (rkOneUStar h).subgroupOf (rkOneGInf h) := (rkOneUStar_eq_sylow h P) ▸ hP hmem
  exact Subgroup.mem_subgroupOf.mp h1

@[expose] noncomputable def conjUStar (hψ : ψ ∈ lineNormalizer h 1 1)
    (hψi : ψ (infL h) = infL h) : MulAut (rkOneUStar h) where
  toFun u := ⟨ψ * u * ψ⁻¹, conj_mem_rkOneUStar h hψ hψi u.2⟩
  invFun u := ⟨ψ⁻¹ * u * ψ⁻¹⁻¹,
    conj_mem_rkOneUStar h (inv_mem hψ) (perm_inv_apply_of_fix hψi) u.2⟩
  left_inv u := Subtype.ext (by
    change ψ⁻¹ * (ψ * (u : Equiv.Perm (hypIsotropicLines h 1 1)) * ψ⁻¹) * ψ⁻¹⁻¹ = u
    group)
  right_inv u := Subtype.ext (by
    change ψ * (ψ⁻¹ * (u : Equiv.Perm (hypIsotropicLines h 1 1)) * ψ⁻¹⁻¹) * ψ⁻¹ = u
    group)
  map_mul' u v := Subtype.ext (by
    change ψ * ((u : Equiv.Perm (hypIsotropicLines h 1 1)) * v) * ψ⁻¹ =
      ψ * u * ψ⁻¹ * (ψ * v * ψ⁻¹)
    group)

theorem coe_conjUStar (hψ : ψ ∈ lineNormalizer h 1 1) (hψi : ψ (infL h) = infL h)
    (u : rkOneUStar h) :
    ((conjUStar h hψ hψi u : rkOneUStar h) : Equiv.Perm (hypIsotropicLines h 1 1)) =
      ψ * u * ψ⁻¹ :=
  rfl

theorem coe_conjUStar_inv (hψ : ψ ∈ lineNormalizer h 1 1) (hψi : ψ (infL h) = infL h)
    (u : rkOneUStar h) :
    (((conjUStar h hψ hψi)⁻¹ u : rkOneUStar h) : Equiv.Perm (hypIsotropicLines h 1 1)) =
      ψ⁻¹ * u * ψ := by
  change ψ⁻¹ * (u : Equiv.Perm (hypIsotropicLines h 1 1)) * ψ⁻¹⁻¹ = _
  rw [inv_inv]

theorem conjUStar_inv_eq (hψ : ψ ∈ lineNormalizer h 1 1) (hψi : ψ (infL h) = infL h) :
    conjUStar h (inv_mem hψ) (perm_inv_apply_of_fix hψi) = (conjUStar h hψ hψi)⁻¹ :=
  MulEquiv.ext fun _ => rfl

theorem rkOneTauFun_uS (c : K) {a b : K} (hab : h.norm a + h.trace b = 0) :
    rkOneTauFun h c (uS h a b hab) = uS h (c * a) (h.norm c * b) (tau_param h c hab) :=
  uS_ext h (by rw [uA_rkOneTauFun, uA_uS, uA_uS]) (by rw [uB_rkOneTauFun, uB_uS, uB_uS])

omit [Field K] in
theorem conj_conj_eq {G : Type} [Group G] {ψ t t' x : G} (ht : t' = ψ * t * ψ⁻¹) :
    t' * x * t'⁻¹ = ψ * (t * (ψ⁻¹ * x * ψ) * t⁻¹) * ψ⁻¹ := by
  subst ht
  group

omit [Field K] in
theorem conj_inv_conj_eq {G : Type} [Group G] {θ θ' y z : G} (he : θ' = θ⁻¹)
    (hz : z = θ * y * θ⁻¹) : θ' * z * θ'⁻¹ = y := by
  subst he hz
  group

theorem coe_uS {a b : K} (hab : h.norm a + h.trace b = 0) :
    ((uS h a b hab : rkOneUStar h) : Equiv.Perm (hypIsotropicLines h 1 1)) = rkOneU h a b hab :=
  rfl

theorem coe_rkOneTau_chi (s : Kˣ) (x : rkOneUStar h) :
    ((rkOneTau h (rkOneChi h s) x : rkOneUStar h) : Equiv.Perm (hypIsotropicLines h 1 1)) =
      rkOneTElt h s * x * (rkOneTElt h s)⁻¹ := by
  have hx : ∃ (a b : K) (hab : h.norm a + h.trace b = 0), x = uS h a b hab :=
    ⟨uA h x, uB h x, uAB_param h x, eq_uS h x⟩
  obtain ⟨a, b, hab, rfl⟩ := hx
  have e1 : rkOneTau h (rkOneChi h s) (uS h a b hab) =
      uS h ((rkOneChi h s : K) * a) (h.norm (rkOneChi h s : K) * b) (rkOneChi_param h s hab) :=
    rkOneTauFun_uS h _ hab
  simp only [e1, coe_uS]
  exact (rkOneTElt_conj_chi h s hab).symm

theorem conjUStar_tau_mem (hψ : ψ ∈ lineNormalizer h 1 1) (hψi : ψ (infL h) = infL h)
    (hψ0 : ψ (zeroL h) = zeroL h) {m : Kˣ} (hm : m ∈ rkOneM h) :
    conjUStar h hψ hψi * rkOneTau h m * (conjUStar h hψ hψi)⁻¹ ∈
      (rkOneM h).map (rkOneTau h) := by
  obtain ⟨s, rfl⟩ := hm
  have h1 : ψ * rkOneTElt h s * ψ⁻¹ ∈ rkOneT h :=
    conj_mem_rkOneT h hψ hψi hψ0 ((mem_rkOneT h).mpr ⟨s, rfl⟩)
  have h2 : ∃ s' : Kˣ, rkOneTElt h s' = ψ * rkOneTElt h s * ψ⁻¹ := (mem_rkOneT h).mp h1
  obtain ⟨s', hs'⟩ := h2
  refine ⟨rkOneChi h s', ⟨s', rfl⟩, MulEquiv.ext fun x => Subtype.ext ?_⟩
  have e2 : (((conjUStar h hψ hψi * rkOneTau h (rkOneChi h s) * (conjUStar h hψ hψi)⁻¹) x :
      rkOneUStar h) : Equiv.Perm (hypIsotropicLines h 1 1)) =
      ψ * (rkOneTElt h s * (ψ⁻¹ * x * ψ) * (rkOneTElt h s)⁻¹) * ψ⁻¹ := by
    simp only [MulAut.mul_apply, coe_conjUStar, coe_rkOneTau_chi, coe_conjUStar_inv]
  exact (coe_rkOneTau_chi h s' x).trans ((conj_conj_eq hs').trans e2.symm)

theorem conjUStar_mem_normalizer (hψ : ψ ∈ lineNormalizer h 1 1)
    (hψi : ψ (infL h) = infL h) (hψ0 : ψ (zeroL h) = zeroL h) :
    conjUStar h hψ hψi ∈ Subgroup.normalizer (((rkOneM h).map (rkOneTau h) :
      Subgroup (MulAut (rkOneUStar h))) : Set (MulAut (rkOneUStar h))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact conjUStar_tau_mem h hψ hψi hψ0 hm
  · rintro ⟨m, hm, hmy⟩
    have h1 := conjUStar_tau_mem h (inv_mem hψ) (perm_inv_apply_of_fix hψi)
      (perm_inv_apply_of_fix hψ0) hm
    exact conj_inv_conj_eq (conjUStar_inv_eq h hψ hψi) hmy ▸ h1

end Conj

section Semilinear

variable (h : UnitaryFieldData p f K)

theorem norm_ne_zero_of_ne_zero {c : K} (hc : c ≠ 0) : h.norm c ≠ 0 :=
  mul_ne_zero hc ((map_ne_zero h.bar).mpr hc)

theorem diagonal_rkVec_mul (x y w x' y' w' : K) :
    diagonal (rkVec x y w) * diagonal (rkVec x' y' w') =
      diagonal (rkVec (x * x') (y * y') (w * w')) := by
  rw [diagonal_mul_diagonal]
  congr 1
  funext v
  rcases v with i | i | i <;> rfl

theorem diagonal_rkVec_one : diagonal (rkVec (1 : K) 1 1) = 1 := by
  rw [← diagonal_one]
  congr 1
  funext v
  rcases v with i | i | i <;> rfl

theorem diagonal_rkVec_mulVec (x y w x' y' w' : K) :
    diagonal (rkVec x y w) *ᵥ rkVec x' y' w' = rkVec (x * x') (y * y') (w * w') := by
  funext v
  rw [mulVec_diagonal]
  rcases v with i | i | i <;> rfl

@[expose] noncomputable def rkOneSMat (c : Kˣ) : GL (HypIndex 1 1) K where
  val := diagonal (rkVec (h.norm c) c 1)
  inv := diagonal (rkVec (h.norm c)⁻¹ (c : K)⁻¹ 1)
  val_inv := by
    rw [diagonal_rkVec_mul, mul_inv_cancel₀ (norm_ne_zero_of_ne_zero h c.ne_zero),
      mul_inv_cancel₀ c.ne_zero, mul_one, diagonal_rkVec_one]
  inv_val := by
    rw [diagonal_rkVec_mul, inv_mul_cancel₀ (norm_ne_zero_of_ne_zero h c.ne_zero),
      inv_mul_cancel₀ c.ne_zero, mul_one, diagonal_rkVec_one]

theorem rkOneSMat_similitude (c : Kˣ) :
    (((rkOneSMat h c : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map
      h.bar)ᵀ * hypGram 1 1 K * (rkOneSMat h c : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
        h.norm c • hypGram 1 1 K := by
  change ((diagonal (rkVec (h.norm c) c 1)).map h.bar)ᵀ * hypGram 1 1 K *
    diagonal (rkVec (h.norm c) c 1) = _
  ext x y
  rw [mul_diagonal, diagonal_map (map_zero h.bar), diagonal_transpose, diagonal_mul,
    Matrix.smul_apply, hypGram_apply]
  split_ifs with hxy
  · rw [hxy, mul_one, smul_eq_mul, mul_one]
    rcases x with i | i | i <;> obtain rfl := Fin.fin_one_eq_zero i
    · rw [hypPartner_inl, rkVec_inl, rkVec_inr_inr, mul_one]
      exact h.mem_fixedField.mp (h.norm_mem_fixedField c)
    · rw [hypPartner_inr_inl, rkVec_inr_inl, UnitaryFieldData.norm, mul_comm]
    · rw [hypPartner_inr_inr, rkVec_inr_inr, rkVec_inl, map_one, one_mul]
  · rw [mul_zero, zero_mul, smul_zero]

@[expose] noncomputable def rkOneSElt (c : Kˣ) (σ : K ≃+* K) : semilinearSimilitudes h 1 1 :=
  ⟨⟨rkOneSMat h c, σ⟩, mem_semilinearSimilitudes.mpr ⟨h.norm c,
    norm_ne_zero_of_ne_zero h c.ne_zero, h.mem_fixedField.mp (h.norm_mem_fixedField c),
    rkOneSMat_similitude h c⟩⟩

theorem rkOneSElt_left (c : Kˣ) (σ : K ≃+* K) :
    ((rkOneSElt h c σ : semilinearSimilitudes h 1 1) : SemiGL (HypIndex 1 1) K).left =
      rkOneSMat h c :=
  rfl

theorem rkOneSElt_right (c : Kˣ) (σ : K ≃+* K) :
    ((rkOneSElt h c σ : semilinearSimilitudes h 1 1) : SemiGL (HypIndex 1 1) K).right = σ :=
  rfl

theorem coe_rkOneSMat (c : Kˣ) :
    ((rkOneSMat h c : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      diagonal (rkVec (h.norm c) c 1) :=
  rfl

theorem coord_rkVec (σ : K ≃+* K) (x y w : K) :
    (fun a => σ (rkVec x y w a)) = rkVec (σ x) (σ y) (σ w) := by
  funext v
  rcases v with i | i | i <;> rfl

theorem rkOneSElt_span (c : Kˣ) (σ : K ≃+* K) {L : hypIsotropicLines h 1 1} {x y w : K}
    (hL : (L : Submodule K (HypIndex 1 1 → K)) = K ∙ rkVec x y w) :
    ((semilinearPointAction h 1 1 (rkOneSElt h c σ) L : hypIsotropicLines h 1 1) :
      Submodule K (HypIndex 1 1 → K)) = K ∙ rkVec (h.norm c * σ x) (c * σ y) (σ w) := by
  rw [semilinearPointAction_apply, rkOneSElt_left, rkOneSElt_right, hL, coordImage_span_singleton,
    coord_rkVec]
  refine (gl_smul_span (rkOneSMat h c) _).trans ?_
  rw [coe_rkOneSMat, diagonal_rkVec_mulVec, one_mul]

theorem rkOneSElt_infL (c : Kˣ) (σ : K ≃+* K) :
    semilinearPointAction h 1 1 (rkOneSElt h c σ) (infL h) = infL h := by
  apply Subtype.ext
  rw [rkOneSElt_span h c σ (coe_infL h), coe_infL, map_one, map_zero, mul_one, mul_zero,
    show rkVec (h.norm (c : K)) 0 0 = h.norm (c : K) • rkVec 1 0 0 by
      rw [rkVec_smul, mul_one, mul_zero],
    span_singleton_smul_eq (IsUnit.mk0 _ (norm_ne_zero_of_ne_zero h c.ne_zero))]

theorem rkOneSElt_rkPtL (c : Kˣ) (σ : K ≃+* K) {a b : K} (hab : h.norm a + h.trace b = 0) :
    semilinearPointAction h 1 1 (rkOneSElt h c σ) (rkPtL h hab) =
      rkPtL h (sigma_param h c σ hab) := by
  apply Subtype.ext
  rw [rkOneSElt_span h c σ (coe_rkPtL h hab), coe_rkPtL, map_one]

end Semilinear

theorem mem_semilinearPointGroup_of_fix (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    {ψ : Equiv.Perm (hypIsotropicLines h 1 1)} (hψ : ψ ∈ lineNormalizer h 1 1)
    (hψi : ψ (infL h) = infL h) (hψ0 : ψ (zeroL h) = zeroL h) :
    ψ ∈ semilinearPointGroup h 1 1 := by
  obtain ⟨c, σ, hcσ⟩ := unitary_rank_one_root_torus_automorphisms h hq (conjUStar h hψ hψi)
    (conjUStar_mem_normalizer h hψ hψi hψ0)
  refine ⟨rkOneSElt h c σ, Equiv.ext fun L => ?_⟩
  by_cases hL : L = infL h
  · rw [hL, hψi, rkOneSElt_infL]
  · obtain ⟨a, b, hab, rfl⟩ := exists_rkPtL_eq L hL
    have h1 := congrArg (fun x : rkOneUStar h =>
      (x : Equiv.Perm (hypIsotropicLines h 1 1)) (zeroL h)) (hcσ a b hab)
    change (ψ * rkOneU h a b hab * ψ⁻¹) (zeroL h) =
      rkOneU h _ _ (sigma_param h c σ hab) (zeroL h) at h1
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_inv_apply_of_fix hψ0, rkOneU_zeroL,
      rkOneU_zeroL] at h1
    rw [rkOneSElt_rkPtL, h1]

theorem unitary_rank_one_permutation_normalizer (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) :
    lineNormalizer h 1 1 = semilinearPointGroup h 1 1 ∧
    derivedSeries (lineNormalizer h 1 1 ⧸
      (hypProjLineAction h 1 1).range.subgroupOf (lineNormalizer h 1 1)) 2 = ⊥ := by
  have hEq : lineNormalizer h 1 1 = semilinearPointGroup h 1 1 := by
    refine le_antisymm (fun φ hφ => ?_) semilinearPointGroup_le_normalizer
    have hne : φ (infL h) ≠ φ (zeroL h) := fun he => zeroL_ne_infL (φ.injective he).symm
    obtain ⟨g, hg, hg1, hg2⟩ := rkOneG_two_transitive h _ _ _ _ hne zeroL_ne_infL.symm
    have hgN : g ∈ lineNormalizer h 1 1 := Subgroup.le_normalizer hg
    have hψE := mem_semilinearPointGroup_of_fix h hq (mul_mem hgN hφ)
      (by rw [Equiv.Perm.mul_apply, hg1]) (by rw [Equiv.Perm.mul_apply, hg2])
    have hgE : g ∈ semilinearPointGroup h 1 1 := hypProjLineAction_range_le hg
    have he : φ = g⁻¹ * (g * φ) := by rw [inv_mul_cancel_left]
    rw [he]
    exact mul_mem (inv_mem hgE) hψE
  exact ⟨hEq, derivedSeries_two_eq_bot_of_eq_semilinearPointGroup h hEq⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

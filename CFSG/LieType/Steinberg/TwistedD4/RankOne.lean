module

public import CFSG.LieType.Steinberg.TwistedD4.Local
public import CFSG.LieType.Steinberg.TwistedE6.RankOne
public import CFSG.LieType.Chevalley.TwistPerfect

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedD4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits

variable {K : Type} [Field K]

local notation "𝕏" => rootGroup (rootOperatorFamily d4) K

local notation "𝕩" => xPar (rootOperatorFamily d4)

local notation "𝕃" => CurtisTits.rankOne (rootGroup (rootOperatorFamily d4) K)

section Restrict

variable {a k : Fin d4.rank} (hk : d4.cartan a k = -1)

local notation "ℛ" => rankOneRels (K := K) (rootOperatorFamily d4) a

include hk in
theorem restrictHom_upper
    (c : K) (h : 𝕩 (Pi.single a 1) c ∈ 𝕃 a) :
    restrictHom (rootOperatorFamily d4) hk ⟨_, h⟩ = sl2Upper c := by
  rw [← restrictHom_x (rootOperatorFamily d4) hk c]
  congr 1
  exact Subtype.ext (xPar_simple a c)

include hk in
theorem restrictHom_lower
    (c : K) (h : 𝕩 (-Pi.single a 1) c ∈ 𝕃 a) :
    restrictHom (rootOperatorFamily d4) hk ⟨_, h⟩ = sl2Lower c := by
  rw [← restrictHom_y (rootOperatorFamily d4) hk c]
  congr 1
  exact Subtype.ext (xPar_neg_simple a c)

theorem restrictHom_w
    {t : K} (ht : t ≠ 0) :
    ((restrictHom (rootOperatorFamily d4) hk ((ℛ).w t) : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = !![0, t; -t⁻¹, 0] := by
  rw [RankOneRels.w_def, map_mul, map_mul, restrictHom_x, restrictHom_y]
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower]
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ ht, inv_mul_cancel₀ ht]

theorem restrictHom_h
    {t : K} (ht : t ≠ 0) :
    ((restrictHom (rootOperatorFamily d4) hk ((ℛ).h t) : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = !![t, 0; 0, t⁻¹] := by
  rw [RankOneRels.h_def, map_mul, map_inv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, restrictHom_w hk ht, restrictHom_w hk one_ne_zero]
  ext p q
  fin_cases p <;> fin_cases q <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]

theorem restrictHom_torusElement
    (t : Kˣ) (h : torusElement d4 K a t ∈ 𝕃 a) :
    ((restrictHom (rootOperatorFamily d4) hk ⟨_, h⟩ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = !![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)] := by
  have e : (⟨_, h⟩ : 𝕃 a) = (ℛ).h t := Subtype.ext (by
    rw [rankOneRels_h (rootOperatorFamily d4) a t.ne_zero, Units.mk0_val])
  rw [e, restrictHom_h hk t.ne_zero, Units.val_inv_eq_inv_val]

theorem restrictHom_weylElement
    (h : Chevalley.weylElement d4 K a ∈ 𝕃 a) :
    ((restrictHom (rootOperatorFamily d4) hk ⟨_, h⟩ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := by
  have e : (⟨_, h⟩ : 𝕃 a) = (ℛ).w 1 := Subtype.ext (rankOneRels_w_one _ a).symm
  rw [e, restrictHom_w hk one_ne_zero, inv_one]

include hk in
theorem eq_zero_of_conj_xPar
    {c s : K}
    (h : 𝕩 (Pi.single a 1) c * 𝕩 (-Pi.single a 1) 1 * (𝕩 (Pi.single a 1) c)⁻¹ =
      𝕩 (-Pi.single a 1) s) : c = 0 := by
  have hx : ∀ d : K, 𝕩 (Pi.single a 1) d ∈ 𝕃 a := fun d =>
    Subgroup.mem_sup_left (xPar_mem (isRoot_single d4 a) d)
  have hy : ∀ d : K, 𝕩 (-Pi.single a 1) d ∈ 𝕃 a := fun d =>
    Subgroup.mem_sup_right (xPar_mem (isRoot_neg_single d4 a) d)
  have e : (⟨_, hx c⟩ : 𝕃 a) * ⟨_, hy 1⟩ * (⟨_, hx c⟩ : 𝕃 a)⁻¹ = ⟨_, hy s⟩ := Subtype.ext h
  have e' := congrArg (restrictHom (rootOperatorFamily d4) hk) e
  rw [map_mul, map_mul, map_inv, restrictHom_upper hk, restrictHom_lower hk,
    restrictHom_lower hk] at e'
  have h00 := congrArg (fun s : Matrix.SpecialLinearGroup (Fin 2) K =>
    (s : Matrix (Fin 2) (Fin 2) K) 0 0) e'
  simpa [Matrix.SpecialLinearGroup.coe_inv, coe_sl2Upper, coe_sl2Lower, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.adjugate_fin_two] using h00

end Restrict

section Long

variable (σ : K →+* K)

theorem cartan_two_zero : d4.cartan (nd 2) (nd 0) = -1 := by decide

theorem proj_single_two : proj (Pi.single (nd 2) 1) = Pi.single (ng 0) 1 := by
  rw [proj_apply, orbitSum_single]
  rfl

theorem proj_neg_single_two : proj (-Pi.single (nd 2) 1) = -Pi.single (ng 0) 1 := by
  rw [proj_apply, orbitSum_neg_single]
  rfl

theorem rho_single_two : rho (Pi.single (nd 2) 1) = Pi.single (nd 2) 1 := by
  rw [rho_single, rhoPerm_two]

theorem rho_neg_single_two :
    rho (-Pi.single (nd 2) 1) = -Pi.single (nd 2) 1 := by
  rw [rho_neg_single, rhoPerm_two]

theorem twistedRootSubgroupD4_long_le :
    twistedRootSubgroupD4 σ (Pi.single (ng 0) 1) ≤ 𝕏 (Pi.single (nd 2) 1) ∧
      twistedRootSubgroupD4 σ (-Pi.single (ng 0) 1) ≤ 𝕏 (-Pi.single (nd 2) 1) := by
  constructor
  · have h := twistedRootSubgroupD4_le σ (isRoot_single d4 (nd 2)) proj_single_two
    simp only [rho_single_two, sup_idem] at h
    exact h
  · have h := twistedRootSubgroupD4_le σ (isRoot_neg_single d4 (nd 2)) proj_neg_single_two
    simp only [rho_neg_single_two, sup_idem] at h
    exact h

theorem val_mem_rankOne_two
    {g : twistedGroup σ}
    (hg : g ∈ rankOne (twistedRootGroup σ) (ng 0)) : (g : adjointGroup d4 K) ∈ 𝕃 (nd 2) := by
  have hle : rankOne (twistedRootGroup σ) (ng 0) ≤ (𝕃 (nd 2)).comap (twistedGroup σ).subtype :=
    sup_le (fun x hx => Subgroup.mem_sup_left ((twistedRootSubgroupD4_long_le σ).1 hx))
      (fun x hx => Subgroup.mem_sup_right ((twistedRootSubgroupD4_long_le σ).2 hx))
  exact hle hg

local notation "R₂" => restrictHom (K := K) (rootOperatorFamily d4) cartan_two_zero

variable {σ} (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem restrictHom_mem_slFixed
    {g : twistedGroup σ}
    (hg : g ∈ rankOne (twistedRootGroup σ) (ng 0)) :
    R₂ ⟨_, val_mem_rankOne_two σ hg⟩ ∈ TwistedE6.slFixed K σ := by
  set Q : Subgroup (adjointGroup d4 K) :=
    ((TwistedE6.slFixed K σ).comap R₂).map (𝕃 (nd 2)).subtype with hQ
  have hX : ∀ {s : ℤ} (hs : s = 1 ∨ s = -1),
      twistedRootSubgroupD4 σ (s • Pi.single (ng 0) 1) ≤ Q := by
    intro s hs x hx
    have hr : IsRoot d4 (s • Pi.single (nd 2) 1) := isRoot_smul_single hs (nd 2)
    have hp : proj (s • Pi.single (nd 2) 1) = s • Pi.single (ng 0) 1 := by
      rw [proj_smul_single hs]
      rfl
    have hfix : rho (s • Pi.single (nd 2) 1) = s • Pi.single (nd 2) 1 := by
      rw [rho_smul_single, rhoPerm_two]
    obtain ⟨c, hc, rfl⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ hr hp hfix x).1 hx
    refine ⟨⟨_, xPar_single_mem_rankOne' (nd 2) hs c⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, TwistedE6.mem_slFixed]
    rcases hs with rfl | rfl
    · have e : (⟨_, xPar_single_mem_rankOne' (nd 2) (Or.inl rfl) c⟩ : 𝕃 (nd 2)) =
          ⟨𝕩 (Pi.single (nd 2) 1) c, xPar_single_mem_rankOne (F := rootOperatorFamily d4) _ c⟩ :=
        Subtype.ext (by simp only [one_smul])
      rw [e, restrictHom_upper cartan_two_zero, coe_sl2Upper]
      intro p q
      fin_cases p <;> fin_cases q <;> simp [hc]
    · have e : (⟨_, xPar_single_mem_rankOne' (nd 2) (Or.inr rfl) c⟩ : 𝕃 (nd 2)) =
          ⟨𝕩 (-Pi.single (nd 2) 1) c,
            xPar_neg_single_mem_rankOne (F := rootOperatorFamily d4) _ c⟩ :=
        Subtype.ext (by simp only [neg_one_smul])
      rw [e, restrictHom_lower cartan_two_zero, coe_sl2Lower]
      intro p q
      fin_cases p <;> fin_cases q <;> simp [hc]
  have hle : rankOne (twistedRootGroup σ) (ng 0) ≤ Q.comap (twistedGroup σ).subtype := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · have h := hX (s := 1) (Or.inl rfl)
      rw [one_smul] at h
      exact h hx
    · have h := hX (s := -1) (Or.inr rfl)
      rw [neg_one_smul] at h
      exact h hx
  obtain ⟨y, hy, hyg⟩ := hle hg
  have e : y = ⟨_, val_mem_rankOne_two σ hg⟩ := Subtype.ext hyg
  rw [← e]
  exact hy

omit hσ in
theorem eq_of_restrictHom_eq
    {x y : adjointGroup d4 K} (hx : x ∈ 𝕃 (nd 2)) (hy : y ∈ 𝕃 (nd 2))
    (h : ((R₂ ⟨x, hx⟩ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((R₂ ⟨y, hy⟩ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) :
    x = y :=
  congrArg Subtype.val (restrictHom_injective (rootOperatorFamily d4) cartan_two_zero
    (Subtype.ext h))

omit hσ in
theorem restrictHom_mul_val
    {x y : adjointGroup d4 K} (hx : x ∈ 𝕃 (nd 2)) (hy : y ∈ 𝕃 (nd 2)) :
    R₂ ⟨x * y, mul_mem hx hy⟩ = R₂ ⟨x, hx⟩ * R₂ ⟨y, hy⟩ := by
  rw [← map_mul]
  rfl

omit hσ in
theorem xPar_single_two_mem
    (c : K) : 𝕩 (Pi.single (nd 2) 1) c ∈ 𝕃 (nd 2) :=
  Subgroup.mem_sup_left (xPar_mem (isRoot_single d4 _) c)

theorem xPar_single_two_mem_twisted
    {c : K} (hc : σ c = c) :
    𝕩 (Pi.single (nd 2) 1) c ∈ twistedRootSubgroupD4 σ (Pi.single (ng 0) 1) :=
  proj_single_two ▸ xPar_mem_of_fixed hσ (isRoot_single d4 _) rho_single_two hc

theorem xPar_neg_single_two_mem_twisted
    {c : K} (hc : σ c = c) :
    𝕩 (-Pi.single (nd 2) 1) c ∈ twistedRootSubgroupD4 σ (-Pi.single (ng 0) 1) :=
  proj_neg_single_two ▸ xPar_mem_of_fixed hσ (isRoot_neg_single d4 _) rho_neg_single_two hc

theorem exists_xLong
    {c : K} (hc : σ c = c) :
    ∃ u ∈ twistedRootGroup σ (Pi.single (ng 0) 1),
      (u : adjointGroup d4 K) = 𝕩 (Pi.single (nd 2) 1) c :=
  ⟨⟨_, twistedRootSubgroupD4_le_twistedGroup σ (isRoot_single _ _)
    (xPar_single_two_mem_twisted hσ hc)⟩, xPar_single_two_mem_twisted hσ hc, rfl⟩

omit hσ in
theorem exists_hLongElt
    {t : Kˣ} (ht : σ t = t) :
    ∃ h ∈ hHat σ (ng 0), (h : adjointGroup d4 K) = torusElement d4 K (nd 2) t := by
  have htf : t ∈ fixedUnits σ := (mem_fixedUnits σ).2 ht
  obtain ⟨g, -, hg⟩ := exists_hLong (σ := σ) ⟨t, htf⟩
  refine ⟨g, ?_, hg⟩
  rw [hHat, Subgroup.mem_subgroupOf, hg]
  exact ⟨⟨t, htf⟩, rfl⟩

theorem bruhat_long
    {g : twistedGroup σ} (hg : g ∈ rankOne (twistedRootGroup σ) (ng 0)) :
    (∃ h ∈ hHat σ (ng 0), ∃ u ∈ twistedRootGroup σ (Pi.single (ng 0) 1), g = h * u) ∨
      ∃ u ∈ twistedRootGroup σ (Pi.single (ng 0) 1), ∃ h ∈ hHat σ (ng 0),
        ∃ v ∈ twistedRootGroup σ (Pi.single (ng 0) 1), g = u * nHat σ (ng 0) * h * v := by
  have hg2 := val_mem_rankOne_two σ hg
  set M := R₂ ⟨_, hg2⟩ with hM
  have hfix := (TwistedE6.mem_slFixed σ).1 (restrictHom_mem_slFixed hσ hg)
  rw [← hM] at hfix
  have hh2 : ∀ t : Kˣ, torusElement d4 K (nd 2) t ∈ 𝕃 (nd 2) := torusElement_mem_rankOne (nd 2)
  have hn2 : Chevalley.weylElement d4 K (nd 2) ∈ 𝕃 (nd 2) := weylElement_mem_rankOne' (nd 2)
  by_cases h0 : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · left
    have hdet := M.det_coe
    rw [Matrix.det_fin_two, h0, mul_zero, sub_zero] at hdet
    have h00 : (M : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    obtain ⟨h, hh, hhv⟩ := exists_hLongElt (σ := σ) (t := Units.mk0 _ h00)
      (by rw [Units.val_mk0]; exact hfix 0 0)
    obtain ⟨u, hu, huv⟩ := exists_xLong hσ (c := (M : Matrix (Fin 2) (Fin 2) K) 0 1 /
      (M : Matrix (Fin 2) (Fin 2) K) 0 0) (by rw [map_div₀, hfix, hfix])
    refine ⟨h, hh, u, hu, Subtype.ext ?_⟩
    rw [Subgroup.coe_mul, hhv, huv]
    refine eq_of_restrictHom_eq hg2 (mul_mem (hh2 _) (xPar_single_two_mem _)) ?_
    rw [← hM, restrictHom_mul_val (hh2 _) (xPar_single_two_mem _),
      Matrix.SpecialLinearGroup.coe_mul, restrictHom_torusElement cartan_two_zero,
      restrictHom_upper cartan_two_zero, coe_sl2Upper]
    exact TwistedE6.sl_eq_of_lower_eq_zero' M h0 h00
  · right
    have hγ : -(M : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := neg_ne_zero.2 h0
    obtain ⟨u, hu, huv⟩ := exists_xLong hσ (c := (M : Matrix (Fin 2) (Fin 2) K) 0 0 /
      (M : Matrix (Fin 2) (Fin 2) K) 1 0) (by rw [map_div₀, hfix, hfix])
    obtain ⟨h, hh, hhv⟩ := exists_hLongElt (σ := σ) (t := Units.mk0 _ hγ)
      (by rw [Units.val_mk0, map_neg, hfix])
    obtain ⟨v, hv, hvv⟩ := exists_xLong hσ (c := (M : Matrix (Fin 2) (Fin 2) K) 1 1 /
      (M : Matrix (Fin 2) (Fin 2) K) 1 0) (by rw [map_div₀, hfix, hfix])
    refine ⟨u, hu, h, hh, v, hv, Subtype.ext ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, huv, hhv, hvv, nHat_val,
      nHatE_zero]
    refine eq_of_restrictHom_eq hg2 (mul_mem (mul_mem (mul_mem (xPar_single_two_mem _) hn2)
      (hh2 _)) (xPar_single_two_mem _)) ?_
    rw [← hM, restrictHom_mul_val (mul_mem (mul_mem (xPar_single_two_mem _) hn2) (hh2 _))
      (xPar_single_two_mem _), restrictHom_mul_val (mul_mem (xPar_single_two_mem _) hn2) (hh2 _),
      restrictHom_mul_val (xPar_single_two_mem _) hn2, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      restrictHom_torusElement cartan_two_zero, restrictHom_upper cartan_two_zero,
      restrictHom_upper cartan_two_zero, restrictHom_weylElement cartan_two_zero, coe_sl2Upper,
      coe_sl2Upper]
    exact TwistedE6.sl_eq_of_lower_ne_zero' M h0

theorem eq_one_of_mem_normalizer_long
    {u : twistedGroup σ}
    (hu : u ∈ twistedRootGroup σ (Pi.single (ng 0) 1))
    (hn : u ∈ Subgroup.normalizer
      (twistedRootGroup σ (-Pi.single (ng 0) 1) : Set (twistedGroup σ))) : u = 1 := by
  have hfix : rho (Pi.single (nd 2) 1) = Pi.single (nd 2) 1 := rho_single_two
  have hfix' : rho (-Pi.single (nd 2) 1) = -Pi.single (nd 2) 1 := rho_neg_single_two
  obtain ⟨c, -, huc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_single d4 _)
    proj_single_two hfix u).1 hu
  have hy := xPar_neg_single_two_mem_twisted hσ (c := 1) (map_one σ)
  set y : twistedGroup σ := ⟨_, twistedRootSubgroupD4_le_twistedGroup σ
    (isRoot_neg_single _ _) hy⟩
  have hmem := (hn y).1 hy
  obtain ⟨s, -, hs⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_neg_single d4 _)
    proj_neg_single_two hfix' _).1 hmem
  have h' : 𝕩 (Pi.single (nd 2) 1) c * 𝕩 (-Pi.single (nd 2) 1) 1 *
      (𝕩 (Pi.single (nd 2) 1) c)⁻¹ = 𝕩 (-Pi.single (nd 2) 1) s := by
    rw [← huc]
    exact hs
  have hc0 := eq_zero_of_conj_xPar cartan_two_zero h'
  refine Subtype.ext ?_
  rw [huc, hc0, xPar_zero]
  rfl

end Long

section LongSL

variable (σ : K →+* K)

local notation "R₂" => restrictHom (K := K) (rootOperatorFamily d4) cartan_two_zero

abbrev fixedField : Subfield K := RingHom.eqLocusField σ (RingHom.id K)

@[expose] def slLongE
    : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ) →* adjointGroup d4 K :=
  (𝕃 (nd 2)).subtype.comp
    ((restrictEquiv (rootOperatorFamily d4) cartan_two_zero).symm.toMonoidHom.comp
      (Matrix.SpecialLinearGroup.map (fixedField σ).subtype))

theorem slLongE_upper
    (c : fixedField σ) :
    slLongE σ (sl2Upper c) = 𝕩 (Pi.single (nd 2) 1) (c : K) := by
  have e : Matrix.SpecialLinearGroup.map (fixedField σ).subtype (sl2Upper c) = sl2Upper (c : K) :=
    Subtype.ext (by
      ext p q
      fin_cases p <;> fin_cases q <;> simp [coe_sl2Upper])
  simp only [slLongE, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e,
    restrictEquiv_symm_upper, Subgroup.coe_subtype, rankOneRels_x]
  exact (xPar_simple _ _).symm

theorem slLongE_lower
    (c : fixedField σ) :
    slLongE σ (sl2Lower c) = 𝕩 (-Pi.single (nd 2) 1) (c : K) := by
  have e : Matrix.SpecialLinearGroup.map (fixedField σ).subtype (sl2Lower c) = sl2Lower (c : K) :=
    Subtype.ext (by
      ext p q
      fin_cases p <;> fin_cases q <;> simp [coe_sl2Lower])
  simp only [slLongE, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e,
    restrictEquiv_symm_lower, Subgroup.coe_subtype, rankOneRels_y]
  exact (xPar_neg_simple _ _).symm

variable {σ} (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem slLongE_mem
    (s : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)) :
    slLongE σ s ∈ twistedGroup σ := by
  obtain ⟨e, a, b, c, rfl⟩ := sl2_eq_prod s
  have hx : ∀ d : fixedField σ, slLongE σ (sl2Upper d) ∈ twistedGroup σ := fun d => by
    rw [slLongE_upper]
    exact twistedRootSubgroupD4_le_twistedGroup σ (isRoot_single _ _)
      (xPar_single_two_mem_twisted hσ d.2)
  have hy : ∀ d : fixedField σ, slLongE σ (sl2Lower d) ∈ twistedGroup σ := fun d => by
    rw [slLongE_lower]
    exact twistedRootSubgroupD4_le_twistedGroup σ (isRoot_neg_single _ _)
      (xPar_neg_single_two_mem_twisted hσ d.2)
  simp only [map_mul]
  exact mul_mem (mul_mem (mul_mem (hy e) (hx a)) (hy b)) (hx c)

variable (σ) in
@[expose] def slLong
    : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ) →* twistedGroup σ :=
  (slLongE σ).codRestrict _ (slLongE_mem hσ)

theorem slLong_val
    (s : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)) :
    (slLong σ hσ s : adjointGroup d4 K) = slLongE σ s := rfl

theorem slLong_injective
    : Function.Injective (slLong σ hσ) := by
  intro s s' h
  have h' : (slLong σ hσ s : adjointGroup d4 K) = slLong σ hσ s' := congrArg Subtype.val h
  simp only [slLong_val, slLongE, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Subgroup.coe_subtype] at h'
  have h'' := (restrictEquiv (rootOperatorFamily d4) cartan_two_zero).symm.injective
    (Subtype.ext h')
  refine Subtype.ext ?_
  ext p q
  have := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K =>
    (M : Matrix (Fin 2) (Fin 2) K) p q) h''
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at this
  exact this

end LongSL

section Short

variable (σ : K →+* K)

theorem cartan_zero_two : d4.cartan (nd 0) (nd 2) = -1 := by decide

theorem xOuter_eq
    (s : ℤ) (c d e : K) :
    xOuter s c d e = 𝕩 (s • Pi.single (nd 0) 1) c * 𝕩 (rho (s • Pi.single (nd 0) 1)) d *
      𝕩 (rho (rho (s • Pi.single (nd 0) 1))) e := by
  rw [rho_smul_single, rho_smul_single, rhoPerm_zero, rhoPerm_one]
  rfl

theorem xOuter_inj
    {s : ℤ} (hs : s = 1 ∨ s = -1) {c d e c' d' e' : K}
    (h : xOuter s c d e = xOuter s c' d' e') : c = c' ∧ d = d' ∧ e = e' := by
  rw [xOuter_eq, xOuter_eq] at h
  exact xPar_rho_mul_inj (isRoot_smul_single hs _) (rho_smul_single_ne hs (by decide)) h

theorem xOuter_mem_unip
    {s : ℤ} (hs : s = 1 ∨ s = -1) (c d e : K) :
    xOuter s c d e ∈ unip (K := K) (s • htHom) := by
  have h : ∀ a : Fin d4.rank, 𝕏 (s • Pi.single a 1) ≤ unip (K := K) (s • htHom) := fun a =>
    rootGroup_le_unip _ (by
      rw [AddMonoidHom.smul_apply, htHom_apply, smul_eq_mul, ht]
      rcases hs with rfl | rfl <;> simp [Finset.sum_pi_single'])
  exact mul_mem (mul_mem (h _ (xPar_mem (isRoot_smul_single hs _) c))
    (h _ (xPar_mem (isRoot_smul_single hs _) d))) (h _ (xPar_mem (isRoot_smul_single hs _) e))

theorem hShortHom_mem_diag
    (t : Kˣ) : hShortHom σ t ∈ diag K := by
  rw [hShortHom_apply]
  exact mul_mem (mul_mem (torus_le_diag _ ⟨_, rfl⟩) (torus_le_diag _ ⟨_, rfl⟩))
    (torus_le_diag _ ⟨_, rfl⟩)

theorem eq_one_of_hShortHom_eq_one
    {t : Kˣ} (h : hShortHom σ t = 1) : t = 1 := by
  have hconj : ∀ l : Fin d4.rank, ((t ^ d4.cartan (nd 0) l : Kˣ) : K) *
      ((((Units.map σ.toMonoidHom t) ^ d4.cartan (nd 1) l : Kˣ) : K) *
        (((Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t)) ^ d4.cartan (nd 3) l :
          Kˣ) : K)) = 1 := by
    intro l
    have e := torus3_conj_xElement (nd 0) (nd 1) (nd 3) l t (Units.map σ.toMonoidHom t)
      (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t)) (1 : K)
    rw [← hShortHom_apply, h, one_mul, inv_one, mul_one] at e
    have := xElement_injective l e
    simpa using this.symm
  have hu : ∀ u : Kˣ, ((Units.map σ.toMonoidHom u : Kˣ) : K) = σ u := fun _ => rfl
  have h0 := hconj (nd 0)
  have h2 := hconj (nd 2)
  simp only [hu, show d4.cartan (nd 0) (nd 0) = 2 by decide,
    show d4.cartan (nd 1) (nd 0) = 0 by decide, show d4.cartan (nd 3) (nd 0) = 0 by decide,
    show d4.cartan (nd 0) (nd 2) = -1 by decide, show d4.cartan (nd 1) (nd 2) = -1 by decide,
    show d4.cartan (nd 3) (nd 2) = -1 by decide, zpow_neg, zpow_ofNat, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val, Units.val_one, pow_zero, pow_one, mul_one] at h0 h2
  have ht : ((t : K)) ^ 2 = 1 := h0
  refine Units.ext ?_
  rcases sq_eq_one_iff.1 ht with h1 | h1
  · exact h1
  · rw [Units.val_one]
    rw [h1, map_neg, map_one, map_neg, map_one] at h2
    have : (-1 : K) = 1 := by
      have e : (-1 : K)⁻¹ * ((-1 : K)⁻¹ * (-1 : K)⁻¹) = -1 := by rw [inv_neg, inv_one]; ring
      rw [← e]
      exact h2
    rw [h1, this]

theorem phiShort_single
    (c : K) :
    phiShort σ ⟨𝕩 (Pi.single (nd 0) 1) c,
      xPar_single_mem_rankOne (F := rootOperatorFamily d4) _ c⟩ =
      xOuter 1 c (σ c) (σ (σ c)) := by
  have e : (⟨𝕩 (Pi.single (nd 0) 1) c, xPar_single_mem_rankOne (F := rootOperatorFamily d4) _ c⟩ :
      𝕃 (nd 0)) = ⟨_, xPar_single_mem_rankOne' (nd 0) (Or.inl rfl) c⟩ :=
    Subtype.ext (by simp only [one_smul])
  rw [e, phiShort_xPar σ (Or.inl rfl)]

theorem phiShort_neg_single
    (c : K) :
    phiShort σ ⟨𝕩 (-Pi.single (nd 0) 1) c,
      xPar_neg_single_mem_rankOne (F := rootOperatorFamily d4) _ c⟩ =
      xOuter (-1) c (σ c) (σ (σ c)) := by
  have e : (⟨𝕩 (-Pi.single (nd 0) 1) c,
      xPar_neg_single_mem_rankOne (F := rootOperatorFamily d4) _ c⟩ : 𝕃 (nd 0)) =
      ⟨_, xPar_single_mem_rankOne' (nd 0) (Or.inr rfl) c⟩ :=
    Subtype.ext (by simp only [neg_one_smul])
  rw [e, phiShort_xPar σ (Or.inr rfl)]

theorem phiShort_injective
    : Function.Injective (phiShort σ) := by
  refine (injective_iff_map_eq_one _).2 fun y hy => ?_
  have hpos : ∀ a : Fin d4.rank, 0 < ((1 : ℤ) • htHom) (Pi.single a 1 : Fin d4.rank → ℤ) :=
    fun a => by simp [htHom_apply, ht, Finset.sum_pi_single']
  rcases rankOne_bruhat (rootOperatorFamily d4) (nd 0) y.2 with ⟨h, hh, u, hu, he⟩ |
    ⟨u, hu, h, hh, v, hv, he⟩
  · obtain ⟨t, rfl⟩ := hh
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (isRoot_single d4 _) u).1 hu
    have hy' : y = ⟨torusElement d4 K (nd 0) t, torusElement_mem_rankOne _ t⟩ *
        ⟨_, xPar_single_mem_rankOne (F := rootOperatorFamily d4) _ c⟩ := Subtype.ext he
    rw [hy', map_mul, phiShort_torusElement, phiShort_single] at hy
    have hmem : hShortHom σ t ∈ diag K ⊓ unip (K := K) ((1 : ℤ) • htHom) := by
      refine Subgroup.mem_inf.2 ⟨hShortHom_mem_diag σ t, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hy]
      exact Subgroup.inv_mem _ (xOuter_mem_unip (Or.inl rfl) _ _ _)
    rw [diag_inf_unip, Subgroup.mem_bot] at hmem
    have ht1 := eq_one_of_hShortHom_eq_one σ hmem
    rw [hmem, one_mul] at hy
    have h0 : (1 : adjointGroup d4 K) = xOuter 1 0 (σ 0) (σ (σ 0)) := by
      simp [xOuter, xPar_zero]
    have hc : c = 0 := (xOuter_inj (Or.inl rfl) (hy.trans h0)).1
    rw [hy']
    apply Subtype.ext
    simp only [ht1, hc, Subgroup.coe_mul, xPar_zero, mul_one, OneMemClass.coe_one]
    exact torusElement_one_eq _
  · exfalso
    obtain ⟨a, rfl⟩ := (mem_rootGroup_iff (isRoot_single d4 _) u).1 hu
    obtain ⟨t, rfl⟩ := hh
    obtain ⟨b, rfl⟩ := (mem_rootGroup_iff (isRoot_single d4 _) v).1 hv
    have hy' : y = ⟨_, xPar_single_mem_rankOne (F := rootOperatorFamily d4) _ a⟩ *
        ⟨_, weylElement_mem_rankOne' (nd 0)⟩ * ⟨_, torusElement_mem_rankOne (nd 0) t⟩ *
          ⟨_, xPar_single_mem_rankOne (F := rootOperatorFamily d4) _ b⟩ := Subtype.ext he
    rw [hy', map_mul, map_mul, map_mul, phiShort_single, phiShort_weylElement,
      phiShort_torusElement, phiShort_single] at hy
    set U := xOuter 1 a (σ a) (σ (σ a))
    set V := xOuter 1 b (σ b) (σ (σ b))
    have hn : nHatE K (ng 1) = U⁻¹ * (hShortHom σ t * V)⁻¹ := by
      calc nHatE K (ng 1) = U⁻¹ * (U * nHatE K (ng 1) * hShortHom σ t * V) *
            (hShortHom σ t * V)⁻¹ := by group
        _ = U⁻¹ * (hShortHom σ t * V)⁻¹ := by rw [hy, mul_one]
    have hU : U ∈ tri (K := K) ((1 : ℤ) • htHom) :=
      unip_le_tri _ (xOuter_mem_unip (Or.inl rfl) _ _ _)
    have hV : V ∈ tri (K := K) ((1 : ℤ) • htHom) :=
      unip_le_tri _ (xOuter_mem_unip (Or.inl rfl) _ _ _)
    have hH : hShortHom σ t ∈ tri (K := K) ((1 : ℤ) • htHom) :=
      diag_le_tri _ (hShortHom_mem_diag σ t)
    have htri : nHatE K (ng 1) ∈ tri (K := K) ((1 : ℤ) • htHom) := by
      rw [hn]
      exact mul_mem (inv_mem hU) (inv_mem (mul_mem hH hV))
    have hx : 𝕩 (Pi.single (nd 0) 1) (1 : K) ∈ tri (K := K) ((1 : ℤ) • htHom) :=
      unip_le_tri _ (rootGroup_le_unip _ (hpos _) (xPar_mem (isRoot_single d4 _) 1))
    have hconj := mul_mem (mul_mem htri hx) (inv_mem htri)
    have c1 : Commute (𝕩 (Pi.single (nd 0) 1) (1 : K)) (Chevalley.weylElement d4 K (nd 1)) :=
      commute_rankOne_outer (a := nd 0) (b := nd 1) (by decide) (by decide) (by decide)
        (xPar_single_mem_rankOne (F := rootOperatorFamily d4) _ 1) (weylElement_mem_rankOne' (nd 1))
    have c3 : Commute (𝕩 (Pi.single (nd 0) 1) (1 : K)) (Chevalley.weylElement d4 K (nd 3)) :=
      commute_rankOne_outer (a := nd 0) (b := nd 3) (by decide) (by decide) (by decide)
        (xPar_single_mem_rankOne (F := rootOperatorFamily d4) _ 1) (weylElement_mem_rankOne' (nd 3))
    have e : nHatE K (ng 1) * 𝕩 (Pi.single (nd 0) 1) (1 : K) * (nHatE K (ng 1))⁻¹ =
        Chevalley.weylElement d4 K (nd 0) * 𝕩 (Pi.single (nd 0) 1) (1 : K) *
          (Chevalley.weylElement d4 K (nd 0))⁻¹ := by
      rw [nHatE_one]
      calc Chevalley.weylElement d4 K (nd 0) * Chevalley.weylElement d4 K (nd 1) *
            Chevalley.weylElement d4 K (nd 3) * 𝕩 (Pi.single (nd 0) 1) 1 *
            (Chevalley.weylElement d4 K (nd 0) * Chevalley.weylElement d4 K (nd 1) *
              Chevalley.weylElement d4 K (nd 3))⁻¹ =
          Chevalley.weylElement d4 K (nd 0) * (Chevalley.weylElement d4 K (nd 1) *
            (Chevalley.weylElement d4 K (nd 3) * 𝕩 (Pi.single (nd 0) 1) 1 *
              (Chevalley.weylElement d4 K (nd 3))⁻¹) * (Chevalley.weylElement d4 K (nd 1))⁻¹) *
            (Chevalley.weylElement d4 K (nd 0))⁻¹ := by group
        _ = _ := by rw [← c3.eq, mul_inv_cancel_right, ← c1.eq, mul_inv_cancel_right]
    rw [e] at hconj
    have hneg : Chevalley.weylElement d4 K (nd 0) * 𝕩 (Pi.single (nd 0) 1) (1 : K) *
        (Chevalley.weylElement d4 K (nd 0))⁻¹ ∈ unip (K := K) (-((1 : ℤ) • htHom)) := by
      have h1 := weylElement_conj_mem (F := rootOperatorFamily d4) (nd 0) (isRoot_single d4 _)
        (xPar_mem (F := rootOperatorFamily d4) (isRoot_single d4 (nd 0)) (1 : K))
      rw [show reflect d4 (nd 0) (Pi.single (nd 0) 1) = -Pi.single (nd 0) 1 by decide] at h1
      exact rootGroup_le_unip _ (by simp [htHom_apply, ht, Finset.sum_pi_single']) h1
    have h1 := Subgroup.mem_inf.2 ⟨hconj, hneg⟩
    rw [tri_inf_unip_neg, Subgroup.mem_bot, conj_eq_one_iff] at h1
    exact one_ne_zero (xPar_injective (isRoot_single d4 (nd 0)) (h1.trans (xPar_zero _).symm))

theorem proj_single_zero : proj (Pi.single (nd 0) 1) = Pi.single (ng 1) 1 := by
  rw [proj_apply, orbitSum_single]
  rfl

theorem proj_neg_single_zero : proj (-Pi.single (nd 0) 1) = -Pi.single (ng 1) 1 := by
  rw [proj_apply, orbitSum_neg_single]
  rfl

theorem rho_single_zero_ne : rho (Pi.single (nd 0) 1) ≠ Pi.single (nd 0) 1 := by
  have := rho_smul_single_ne (s := 1) (Or.inl rfl) (i := nd 0) (by decide)
  rwa [one_smul] at this

theorem rho_neg_single_zero_ne : rho (-Pi.single (nd 0) 1) ≠ -Pi.single (nd 0) 1 := by
  have := rho_smul_single_ne (s := -1) (Or.inr rfl) (i := nd 0) (by decide)
  rwa [neg_one_smul] at this

theorem xOrbit_single
    (c : K) : xOrbit σ (Pi.single (nd 0) 1) c = xOuter 1 c (σ c) (σ (σ c)) := by
  have := xOrbit_smul_single σ (s := 1) (Or.inl rfl) c
  rwa [one_smul] at this

theorem xOrbit_neg_single
    (c : K) :
    xOrbit σ (-Pi.single (nd 0) 1) c = xOuter (-1) c (σ c) (σ (σ c)) := by
  have := xOrbit_smul_single σ (s := -1) (Or.inr rfl) c
  rwa [neg_one_smul] at this

variable {σ} (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem rankOne_short_le_range :
    rankOne (twistedRootGroup σ) (ng 1) ≤ (phiShortTw σ hσ).range := by
  refine sup_le (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨c, hc⟩ := (mem_twistedRootSubgroupD4_iff_of_orbit hσ (isRoot_single d4 (nd 0))
      proj_single_zero rho_single_zero_ne x).1 hx
    refine ⟨⟨_, xPar_single_mem_rankOne (F := rootOperatorFamily d4) _ c⟩, Subtype.ext ?_⟩
    rw [phiShortTw_val, phiShort_single, hc, xOrbit_single]
  · obtain ⟨c, hc⟩ := (mem_twistedRootSubgroupD4_iff_of_orbit hσ (isRoot_neg_single d4 (nd 0))
      proj_neg_single_zero rho_neg_single_zero_ne x).1 hx
    refine ⟨⟨_, xPar_neg_single_mem_rankOne (F := rootOperatorFamily d4) _ c⟩, Subtype.ext ?_⟩
    rw [phiShortTw_val, phiShort_neg_single, hc, xOrbit_neg_single]

theorem bruhat_short
    {g : twistedGroup σ} (hg : g ∈ rankOne (twistedRootGroup σ) (ng 1)) :
    (∃ h ∈ hHat σ (ng 1), ∃ u ∈ twistedRootGroup σ (Pi.single (ng 1) 1), g = h * u) ∨
      ∃ u ∈ twistedRootGroup σ (Pi.single (ng 1) 1), ∃ h ∈ hHat σ (ng 1),
        ∃ v ∈ twistedRootGroup σ (Pi.single (ng 1) 1), g = u * nHat σ (ng 1) * h * v := by
  obtain ⟨y, rfl⟩ := rankOne_short_le_range hσ hg
  have hU : ∀ c : K, phiShortTw σ hσ ⟨_, xPar_single_mem_rankOne (F := rootOperatorFamily d4) _ c⟩ ∈
      twistedRootGroup σ (Pi.single (ng 1) 1) := fun c => by
    rw [mem_twistedRootGroup, phiShortTw_val, phiShort_single]
    have := xOuter_mem σ (s := 1) (Or.inl rfl) (hσ c)
    rwa [one_smul] at this
  have hT : ∀ t : Kˣ, phiShortTw σ hσ ⟨_, torusElement_mem_rankOne (nd 0) t⟩ ∈ hHat σ (ng 1) :=
    fun t => by
      rw [hHat, Subgroup.mem_subgroupOf, phiShortTw_val, phiShort_torusElement]
      exact ⟨t, rfl⟩
  have hN : phiShortTw σ hσ ⟨_, weylElement_mem_rankOne' (nd 0)⟩ = nHat σ (ng 1) :=
    Subtype.ext (by rw [phiShortTw_val, phiShort_weylElement]; rfl)
  rcases rankOne_bruhat (rootOperatorFamily d4) (nd 0) y.2 with ⟨h, hh, u, hu, he⟩ |
    ⟨u, hu, h, hh, v, hv, he⟩
  · left
    obtain ⟨t, rfl⟩ := hh
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (isRoot_single d4 _) u).1 hu
    have hy' : y = ⟨torusElement d4 K (nd 0) t, torusElement_mem_rankOne _ t⟩ *
        ⟨_, xPar_single_mem_rankOne (F := rootOperatorFamily d4) _ c⟩ := Subtype.ext he
    exact ⟨_, hT t, _, hU c, by rw [hy', map_mul]⟩
  · right
    obtain ⟨a, rfl⟩ := (mem_rootGroup_iff (isRoot_single d4 _) u).1 hu
    obtain ⟨t, rfl⟩ := hh
    obtain ⟨b, rfl⟩ := (mem_rootGroup_iff (isRoot_single d4 _) v).1 hv
    have hy' : y = ⟨_, xPar_single_mem_rankOne (F := rootOperatorFamily d4) _ a⟩ *
        ⟨_, weylElement_mem_rankOne' (nd 0)⟩ * ⟨_, torusElement_mem_rankOne (nd 0) t⟩ *
          ⟨_, xPar_single_mem_rankOne (F := rootOperatorFamily d4) _ b⟩ := Subtype.ext he
    exact ⟨_, hU a, _, hT t, _, hU b, by rw [hy', map_mul, map_mul, map_mul, hN]⟩

theorem eq_one_of_mem_normalizer_short
    {u : twistedGroup σ}
    (hu : u ∈ twistedRootGroup σ (Pi.single (ng 1) 1))
    (hn : u ∈ Subgroup.normalizer
      (twistedRootGroup σ (-Pi.single (ng 1) 1) : Set (twistedGroup σ))) : u = 1 := by
  obtain ⟨c, hc⟩ := (mem_twistedRootSubgroupD4_iff_of_orbit hσ (isRoot_single d4 (nd 0))
    proj_single_zero rho_single_zero_ne u).1 hu
  rw [xOrbit_single, ← phiShort_single] at hc
  set A : 𝕃 (nd 0) := ⟨_, xPar_single_mem_rankOne (F := rootOperatorFamily d4) (nd 0) c⟩
  set B : 𝕃 (nd 0) := ⟨_, xPar_neg_single_mem_rankOne (F := rootOperatorFamily d4) (nd 0) 1⟩
  have hB : phiShortTw σ hσ B ∈ twistedRootGroup σ (-Pi.single (ng 1) 1) := by
    rw [mem_twistedRootGroup, phiShortTw_val, phiShort_neg_single]
    have := xOuter_mem σ (s := -1) (Or.inr rfl) (hσ 1)
    rwa [neg_one_smul] at this
  have hmem := (hn _).1 hB
  obtain ⟨s, hs⟩ := (mem_twistedRootSubgroupD4_iff_of_orbit hσ (isRoot_neg_single d4 (nd 0))
    proj_neg_single_zero rho_neg_single_zero_ne _).1 hmem
  rw [xOrbit_neg_single, ← phiShort_neg_single] at hs
  have hu' : u = phiShortTw σ hσ A := Subtype.ext hc
  have key : phiShort σ (A * B * A⁻¹) =
      phiShort σ ⟨_, xPar_neg_single_mem_rankOne (F := rootOperatorFamily d4) (nd 0) s⟩ := by
    rw [← hs, hu', map_mul, map_mul, map_inv]
    rfl
  have e := congrArg Subtype.val (phiShort_injective σ key)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e
  have hc0 := eq_zero_of_conj_xPar cartan_zero_two e
  rw [hu']
  apply Subtype.ext
  rw [phiShortTw_val]
  change phiShort σ ⟨_, _⟩ = 1
  rw [phiShort_single, hc0]
  simp [xOuter, xPar_zero]

variable (σ) in
@[expose] def slShort
    : Matrix.SpecialLinearGroup (Fin 2) K →* twistedGroup σ :=
  (phiShortTw σ hσ).comp
    (restrictEquiv (rootOperatorFamily d4) cartan_zero_two).symm.toMonoidHom

theorem slShort_injective
    : Function.Injective (slShort σ hσ) := fun _ _ h =>
  (restrictEquiv (rootOperatorFamily d4) cartan_zero_two).symm.injective
    (phiShort_injective σ (congrArg Subtype.val h))

theorem slShort_upper
    (c : K) :
    (slShort σ hσ (sl2Upper c) : adjointGroup d4 K) = xOuter 1 c (σ c) (σ (σ c)) := by
  simp only [slShort, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, restrictEquiv_symm_upper,
    phiShortTw_val]
  rw [← phiShort_single]
  congr 1
  exact Subtype.ext ((rankOneRels_x _ _ c).trans (xPar_simple _ c).symm)

theorem slShort_lower
    (c : K) :
    (slShort σ hσ (sl2Lower c) : adjointGroup d4 K) = xOuter (-1) c (σ c) (σ (σ c)) := by
  simp only [slShort, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, restrictEquiv_symm_lower,
    phiShortTw_val]
  rw [← phiShort_neg_single]
  congr 1
  exact Subtype.ext ((rankOneRels_y _ _ c).trans (xPar_neg_simple _ c).symm)

end Short

end CFSG.LieType.Steinberg.TwistedD4

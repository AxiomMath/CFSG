module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open Subgroup
open scoped Matrix

variable {p : ℕ} [Fact p.Prime]

theorem monoidHom_eq_one_of_finrank_eq_one {F : Type} [Field F] [CharP F p]
    {T : Type} [AddCommGroup T] [Module F T] (hT : Module.finrank F T = 1)
    {G : Type} [Group G] [Finite G] (hG : oPPrimeHull p (⊤ : Subgroup G) = ⊤)
    (ρ : G →* (Module.End F T)ˣ) : ρ = 1 := by
  haveI : Nontrivial T := Module.nontrivial_of_finrank_pos (by rw [hT]; norm_num)
  rw [← MonoidHom.ker_eq_top_iff, eq_top_iff, ← hG]
  refine (Subgroup.closure_le (ρ.ker)).mpr ?_
  rintro x ⟨-, k, hk⟩
  have h1 : orderOf (ρ x) ∣ p ^ k := by
    rw [← hk]
    exact orderOf_map_dvd ρ x
  have hpow : (ρ x : Module.End F T) ^ (p ^ k) = 1 := by
    rw [← Units.val_pow_eq_pow_val, (orderOf_dvd_iff_pow_eq_one).mp h1, Units.val_one]
  obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hT (ρ x)
  obtain ⟨d, hd, huniq⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hT (1 : Module.End F T)
  have hd1 : d = 1 := (huniq 1 (by simp [Module.End.one_eq_id])).symm
  have hcd : c ^ (p ^ k) = d := by
    refine huniq (c ^ (p ^ k)) ?_
    rw [← hpow, hc]
    have halg : (c • (1 : Module.End F T)) ^ (p ^ k) =
        (c ^ (p ^ k)) • (1 : Module.End F T) := by
      calc (c • (1 : Module.End F T)) ^ (p ^ k)
          = (algebraMap F (Module.End F T) c) ^ (p ^ k) := by
              rw [Algebra.algebraMap_eq_smul_one]
        _ = algebraMap F (Module.End F T) (c ^ (p ^ k)) :=
              (map_pow (algebraMap F (Module.End F T)) c (p ^ k)).symm
        _ = (c ^ (p ^ k)) • (1 : Module.End F T) := Algebra.algebraMap_eq_smul_one ..
    rwa [Module.End.one_eq_id] at halg
  have hc1 : c = 1 := by
    have hz : (c - 1) ^ (p ^ k) = 0 := by
      rw [sub_pow_char_pow, hcd, hd1, one_pow, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)
  apply Units.ext
  rw [Units.val_one, hc, ← Module.End.one_eq_id, ← Algebra.algebraMap_eq_smul_one, hc1,
    map_one]

theorem sLTwoOrTrivial_of_finrank_eq_two_field {F : Type} [Field F] [Finite F]
    (hD : ∀ H : Subgroup (GL (Fin 2) F), oPPrimeHull p H = H →
      IsSLType 2 F (↥H ⧸ CFSG.pCore p ↥H) ∨ Nat.card (↥H ⧸ CFSG.pCore p ↥H) = 1)
    {U : Type} [AddCommGroup U] [Module F U] [Module.Finite F U]
    (hU : Module.finrank F U = 2) {H : Subgroup (Module.End F U)ˣ}
    (hH : oPPrimeHull p H = H) :
    IsSLType 2 F (↥H ⧸ CFSG.pCore p ↥H) ∨ Nat.card (↥H ⧸ CFSG.pCore p ↥H) = 1 := by
  classical
  let b : Module.Basis (Fin 2) F U := Module.finBasisOfFinrankEq F U hU
  let e : (Module.End F U)ˣ ≃* GL (Fin 2) F := (Matrix.GeneralLinearGroup.toLin' b).symm
  have hH' : oPPrimeHull p (H.map e.toMonoidHom) = H.map e.toMonoidHom := by
    rw [← map_oPPrimeHull, hH]
  obtain ⟨E⟩ := nonempty_quot_pCore_map_of_injective (p := p) e.toMonoidHom e.injective H
  rcases hD (H.map e.toMonoidHom) hH' with h | h
  · obtain ⟨ψ⟩ := h
    exact Or.inl ⟨E.trans ψ⟩
  · exact Or.inr (by rw [Nat.card_congr E.toEquiv]; exact h)

theorem sLTwoOrTrivial_of_finrank_eq_two (hD : SLTwoOrTrivialAt p)
    {U : Type} [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (hU : Module.finrank (ZMod p) U = 2) {H : Subgroup (Module.End (ZMod p) U)ˣ}
    (hH : oPPrimeHull p H = H) :
    IsSLType 2 (ZMod p) (↥H ⧸ CFSG.pCore p ↥H) ∨ Nat.card (↥H ⧸ CFSG.pCore p ↥H) = 1 :=
  sLTwoOrTrivial_of_finrank_eq_two_field (F := ZMod p) hD hU hH

section DegreeThree

variable {F : Type} [Field F] [CharP F p] [Finite F]

private noncomputable def actEnd (H : Subgroup (GL (Fin 3) F)) :
    ↥H →* (Module.End F (Fin 3 → F))ˣ :=
  (Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := F)).toMonoidHom.comp H.subtype

private theorem actEnd_apply (H : Subgroup (GL (Fin 3) F)) (g : ↥H) (v : Fin 3 → F) :
    (actEnd H g : Module.End F (Fin 3 → F)) v =
      (H.subtype g : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by
  simpa [actEnd, Matrix.mulVecLin_apply] using
    Matrix.GeneralLinearGroup.toLin_apply (H.subtype g) v

private noncomputable def actWEnd (H : Subgroup (GL (Fin 3) F))
    {W : Submodule F (Fin 3 → F)}
    (hW : ∀ g : ↥H, ∀ x ∈ W, (H.subtype g : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ W) (g : ↥H) :
    Module.End F ↥W :=
  (actEnd H g : Module.End F (Fin 3 → F)).restrict
    (fun x hx => by rw [actEnd_apply]; exact hW g x hx)

private theorem actWEnd_mul (H : Subgroup (GL (Fin 3) F))
    {W : Submodule F (Fin 3 → F)}
    (hW : ∀ g : ↥H, ∀ x ∈ W, (H.subtype g : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ W) (g h : ↥H) :
    actWEnd H hW (g * h) = actWEnd H hW g * actWEnd H hW h := by
  ext x
  simp only [actWEnd, LinearMap.coe_restrict_apply, Module.End.mul_apply, map_mul,
    Units.val_mul]

private theorem actWEnd_one (H : Subgroup (GL (Fin 3) F))
    {W : Submodule F (Fin 3 → F)}
    (hW : ∀ g : ↥H, ∀ x ∈ W, (H.subtype g : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ W) :
    actWEnd H hW 1 = 1 := by
  ext x
  simp [actWEnd]

private noncomputable def actWHom (H : Subgroup (GL (Fin 3) F))
    {W : Submodule F (Fin 3 → F)}
    (hW : ∀ g : ↥H, ∀ x ∈ W, (H.subtype g : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ W) :
    ↥H →* Module.End F ↥W :=
  { toFun := actWEnd H hW
    map_one' := actWEnd_one H hW
    map_mul' := actWEnd_mul H hW }

private noncomputable def actW (H : Subgroup (GL (Fin 3) F))
    {W : Submodule F (Fin 3 → F)}
    (hW : ∀ g : ↥H, ∀ x ∈ W, (H.subtype g : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ W) :
    ↥H →* (Module.End F ↥W)ˣ :=
  (actWHom H hW).toHomUnits

private theorem coe_actW (H : Subgroup (GL (Fin 3) F))
    {W : Submodule F (Fin 3 → F)}
    (hW : ∀ g : ↥H, ∀ x ∈ W, (H.subtype g : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ W) (g : ↥H) :
    ((actW H hW g : (Module.End F ↥W)ˣ) : Module.End F ↥W) = actWEnd H hW g :=
  MonoidHom.coe_toHomUnits _ g

private noncomputable def actW'End (H : Subgroup (GL (Fin 3) F))
    {W W' : Submodule F (Fin 3 → F)} (hcompl : IsCompl W W') (g : ↥H) :
    Module.End F ↥W' :=
  ((W'.projection W hcompl.symm).comp
    (Matrix.toLin' (H.subtype g : Matrix (Fin 3) (Fin 3) F))).restrict
    (fun x _ => by
      have hx : (W'.projection W hcompl.symm)
          ((Matrix.toLin' (H.subtype g : Matrix (Fin 3) (Fin 3) F)) x) ∈
          (W'.projection W hcompl.symm).range :=
        LinearMap.mem_range.mpr
          ⟨(Matrix.toLin' (H.subtype g : Matrix (Fin 3) (Fin 3) F)) x, rfl⟩
      rwa [Submodule.range_projection (hpq := hcompl.symm)] at hx)

private theorem projection_idem {W W' : Submodule F (Fin 3 → F)} (hcompl : IsCompl W W')
    (x : Fin 3 → F) :
    (W'.projection W hcompl.symm) ((W'.projection W hcompl.symm) x) =
      (W'.projection W hcompl.symm) x := by
  have hx : (W'.projection W hcompl.symm) x ∈ W' := by
    have h : (W'.projection W hcompl.symm) x ∈ (W'.projection W hcompl.symm).range :=
      LinearMap.mem_range.mpr ⟨x, rfl⟩
    rwa [Submodule.range_projection (hpq := hcompl.symm)] at h
  exact Submodule.projection_apply_left (hpq := hcompl.symm) ⟨_, hx⟩

private theorem sub_projection_mem {W W' : Submodule F (Fin 3 → F)} (hcompl : IsCompl W W')
    (x : Fin 3 → F) : x - (W'.projection W hcompl.symm) x ∈ W := by
  have hk : x - (W'.projection W hcompl.symm) x ∈ (W'.projection W hcompl.symm).ker :=
    LinearMap.mem_ker.mpr (by rw [map_sub, projection_idem hcompl, sub_self])
  rwa [Submodule.ker_projection (hpq := hcompl.symm)] at hk

private theorem actW'End_mul (H : Subgroup (GL (Fin 3) F))
    {W W' : Submodule F (Fin 3 → F)} (hcompl : IsCompl W W')
    (hW : ∀ g : ↥H, ∀ x ∈ W, (H.subtype g : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ W)
    (g h : ↥H) : actW'End H hcompl (g * h) = actW'End H hcompl g * actW'End H hcompl h := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  simp only [actW'End, LinearMap.coe_restrict_apply, Module.End.mul_apply, LinearMap.comp_apply,
    map_mul, Units.val_mul]
  rw [Matrix.toLin'_mul, LinearMap.comp_apply]
  have hzero : (W'.projection W hcompl.symm)
      ((actEnd H g : Module.End F (Fin 3 → F))
        ((actEnd H h : Module.End F (Fin 3 → F)) w -
          (W'.projection W hcompl.symm)
            ((actEnd H h : Module.End F (Fin 3 → F)) w))) = 0 := by
    have hmem : (actEnd H h : Module.End F (Fin 3 → F)) w -
        (W'.projection W hcompl.symm)
          ((actEnd H h : Module.End F (Fin 3 → F)) w) ∈ W :=
      sub_projection_mem hcompl _
    have hker : (actEnd H g : Module.End F (Fin 3 → F))
        ((actEnd H h : Module.End F (Fin 3 → F)) w -
          (W'.projection W hcompl.symm)
            ((actEnd H h : Module.End F (Fin 3 → F)) w)) ∈
        (W'.projection W hcompl.symm).ker := by
      rw [actEnd_apply]
      exact (Submodule.ker_projection (hpq := hcompl.symm)).symm ▸ hW g _ hmem
    exact LinearMap.mem_ker.mp hker
  have h0 : (W'.projection W hcompl.symm)
        ((actEnd H g : Module.End F (Fin 3 → F))
          ((actEnd H h : Module.End F (Fin 3 → F)) w)) -
      (W'.projection W hcompl.symm)
        ((actEnd H g : Module.End F (Fin 3 → F))
          ((W'.projection W hcompl.symm)
            ((actEnd H h : Module.End F (Fin 3 → F)) w))) = 0 := by
    rw [← map_sub, ← map_sub]
    exact hzero
  exact sub_eq_zero.mp h0

private theorem actW'End_one (H : Subgroup (GL (Fin 3) F))
    {W W' : Submodule F (Fin 3 → F)} (hcompl : IsCompl W W') :
    actW'End H hcompl 1 = 1 := by
  ext w
  simpa [actW'End] using congrFun (Submodule.projection_apply_left (hpq := hcompl.symm) w)

private noncomputable def actW'Hom (H : Subgroup (GL (Fin 3) F))
    {W W' : Submodule F (Fin 3 → F)} (hcompl : IsCompl W W')
    (hW : ∀ g : ↥H, ∀ x ∈ W, (H.subtype g : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ W) :
    ↥H →* Module.End F ↥W' :=
  { toFun := actW'End H hcompl
    map_one' := actW'End_one H hcompl
    map_mul' := actW'End_mul H hcompl hW }

private noncomputable def actW' (H : Subgroup (GL (Fin 3) F))
    {W W' : Submodule F (Fin 3 → F)} (hcompl : IsCompl W W')
    (hW : ∀ g : ↥H, ∀ x ∈ W, (H.subtype g : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ W) :
    ↥H →* (Module.End F ↥W')ˣ :=
  (actW'Hom H hcompl hW).toHomUnits

private theorem coe_actW' (H : Subgroup (GL (Fin 3) F))
    {W W' : Submodule F (Fin 3 → F)} (hcompl : IsCompl W W')
    (hW : ∀ g : ↥H, ∀ x ∈ W, (H.subtype g : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ W) (g : ↥H) :
    ((actW' H hcompl hW g : (Module.End F ↥W')ˣ) : Module.End F ↥W') =
    actW'End H hcompl g :=
  MonoidHom.coe_toHomUnits _ g

private theorem actEnd_sub_one_sq (H : Subgroup (GL (Fin 3) F))
    {W W' : Submodule F (Fin 3 → F)} (hcompl : IsCompl W W')
    (hW : ∀ g : ↥H, ∀ x ∈ W, (H.subtype g : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ W)
    (g : ↥H) (hWg : actWEnd H hW g = 1) (hW'g : actW'End H hcompl g = 1) :
    ((actEnd H g : Module.End F (Fin 3 → F)) - 1) ^ 2 = 0 := by
  set n : Module.End F (Fin 3 → F) := (actEnd H g : Module.End F (Fin 3 → F)) - 1 with hn
  have hkill : ∀ x ∈ W, n x = 0 := by
    intro x hx
    have h1 : actWEnd H hW g ⟨x, hx⟩ = ⟨x, hx⟩ := by
      rw [hWg, Module.End.one_apply]
    have h2 : (actEnd H g : Module.End F (Fin 3 → F)) x = x := by
      have h := congrArg Subtype.val h1
      simpa [actWEnd, LinearMap.coe_restrict_apply] using h
    rw [hn, LinearMap.sub_apply, h2, Module.End.one_apply, sub_self]
  have hinto : ∀ v : Fin 3 → F, n v ∈ W := by
    intro v
    have hv : v ∈ W ⊔ W' := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, hkill x hx, zero_add]
    have h1 : actW'End H hcompl g ⟨y, hy⟩ = ⟨y, hy⟩ := by
      rw [hW'g]; rfl
    have h2 : (W'.projection W hcompl.symm)
        ((actEnd H g : Module.End F (Fin 3 → F)) y) = y := by
      have h := congrArg Subtype.val h1
      simpa [actW'End, actEnd_apply, LinearMap.coe_restrict_apply, LinearMap.comp_apply] using h
    have hker : (actEnd H g : Module.End F (Fin 3 → F)) y - y ∈
        (W'.projection W hcompl.symm).ker := by
      rw [LinearMap.mem_ker, map_sub, h2,
        Submodule.projection_apply_left (hpq := hcompl.symm) ⟨y, hy⟩, sub_self]
    rw [hn, LinearMap.sub_apply, Module.End.one_apply]
    rwa [Submodule.ker_projection (hpq := hcompl.symm)] at hker
  rw [pow_two]
  apply LinearMap.ext
  intro v
  rw [Module.End.mul_apply, hkill (n v) (hinto v), LinearMap.zero_apply]

private theorem pow_eq_one_of_sq_eq_zero {n : Module.End F (Fin 3 → F)} (hn : n * n = 0) :
    (1 + n) ^ p = 1 := by
  have hstep : ∀ k : ℕ, (1 + n) ^ k = 1 + k • n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, add_mul, mul_add, mul_one, one_mul, smul_mul_assoc, mul_add, mul_one,
        hn, add_zero, add_assoc, add_comm n (k • n), ← succ_nsmul]
  rw [hstep p]
  have hp0 : p • n = 0 := by
    rw [← Nat.cast_smul_eq_nsmul F p n, CharP.cast_eq_zero F p, zero_smul]
  rw [hp0, add_zero]

private theorem isPGroup_ker_prod (H : Subgroup (GL (Fin 3) F))
    {W W' : Submodule F (Fin 3 → F)} (hcompl : IsCompl W W')
    (hW : ∀ g : ↥H, ∀ x ∈ W, (H.subtype g : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ W) :
    IsPGroup p ((actW H hW).prod (actW' H hcompl hW)).ker := by
  rw [IsPGroup.iff_orderOf]
  intro g
  have hg : ((actW H hW).prod (actW' H hcompl hW)) (g : ↥H) = 1 := MonoidHom.mem_ker.mp g.2
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hg
  have h1' : actW H hW (g : ↥H) = 1 := h1
  have h2' : actW' H hcompl hW (g : ↥H) = 1 := h2
  have hWg : actWEnd H hW (g : ↥H) = 1 := by
    rw [← coe_actW H hW, h1', Units.val_one]
  have hW'g : actW'End H hcompl (g : ↥H) = 1 := by
    rw [← coe_actW' H hcompl hW, h2', Units.val_one]
  have hnn : ((actEnd H (g : ↥H) : Module.End F (Fin 3 → F)) - 1) *
      ((actEnd H (g : ↥H) : Module.End F (Fin 3 → F)) - 1) = 0 := by
    rw [← pow_two]
    exact actEnd_sub_one_sq H hcompl hW (g : ↥H) hWg hW'g
  have hpow : (g : ↥H) ^ p = 1 := by
    have hinj : Function.Injective (actEnd H) :=
      (Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := F)).injective.comp H.subtype_injective
    apply hinj
    show actEnd H ((g : ↥H) ^ p) = actEnd H 1
    rw [map_pow, map_one]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have h1 : (actEnd H (g : ↥H) : Module.End F (Fin 3 → F)) =
        1 + ((actEnd H (g : ↥H) : Module.End F (Fin 3 → F)) - 1) := by abel
    rw [h1]
    exact pow_eq_one_of_sq_eq_zero hnn
  have hdvd : orderOf (g : ↥H) ∣ p := orderOf_dvd_of_pow_eq_one hpow
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h | h
  · exact ⟨0, by rw [← Subgroup.orderOf_coe g, h, pow_zero]⟩
  · exact ⟨1, by rw [← Subgroup.orderOf_coe g, h, pow_one]⟩

private theorem to_quotient_pCore (hD : ∀ H : Subgroup (GL (Fin 2) F), oPPrimeHull p H = H →
      IsSLType 2 F (↥H ⧸ CFSG.pCore p ↥H) ∨ Nat.card (↥H ⧸ CFSG.pCore p ↥H) = 1)
    {U : Type} [AddCommGroup U] [Module F U] [Module.Finite F U]
    (hU : Module.finrank F U = 2) {G : Type} [Group G] [Finite G]
    (hG : oPPrimeHull p (⊤ : Subgroup G) = ⊤)
    (ρ : G →* (Module.End F U)ˣ) (hker : IsPGroup p ρ.ker) :
    IsSLType 2 F (G ⧸ CFSG.pCore p G) ∨ Nat.card (G ⧸ CFSG.pCore p G) = 1 := by
  have hrange : oPPrimeHull p ρ.range = ρ.range := by
    rw [MonoidHom.range_eq_map, oPPrimeHull_map_eq ρ hG]
  have key := sLTwoOrTrivial_of_finrank_eq_two_field (F := F) hD hU (H := ρ.range) hrange
  obtain ⟨E⟩ := nonempty_quot_pCore_mulEquiv_of_surjective (p := p) ρ.rangeRestrict
    ρ.rangeRestrict_surjective (by rwa [MonoidHom.ker_rangeRestrict])
  rcases key with h | h
  · obtain ⟨ψ⟩ := h
    exact Or.inl ⟨E.trans ψ⟩
  · exact Or.inr (by rw [Nat.card_congr E.toEquiv]; exact h)

theorem sl2_or_trivial_of_not_irreducible_field
    (hD : ∀ H : Subgroup (GL (Fin 2) F), oPPrimeHull p H = H →
      IsSLType 2 F (↥H ⧸ CFSG.pCore p ↥H) ∨ Nat.card (↥H ⧸ CFSG.pCore p ↥H) = 1)
    {H : Subgroup (GL (Fin 3) F)} (hH : oPPrimeHull p H = H)
    (hred : ¬ CFSG.RepresentationTheory.IsIrreducibleMatrixRep H.subtype) :
    IsSLType 2 F (↥H ⧸ CFSG.pCore p ↥H) ∨ Nat.card (↥H ⧸ CFSG.pCore p ↥H) = 1 := by
  classical
  rw [CFSG.RepresentationTheory.IsIrreducibleMatrixRep] at hred
  push Not at hred
  obtain ⟨W, hW, hWne, hWlt⟩ := hred
  obtain ⟨W', hcompl⟩ := Submodule.exists_isCompl W
  have hV : Module.finrank F (Fin 3 → F) = 3 := Module.finrank_fin_fun F
  have hsum : Module.finrank F W + Module.finrank F W' = 3 := by
    have h := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hV] at h
    omega
  have hWpos : 0 < Module.finrank F W := by
    rw [Module.finrank_pos_iff_of_free]
    exact Submodule.nontrivial_iff_ne_bot.mpr hWne
  have hW'pos : 0 < Module.finrank F W' := by
    rw [Module.finrank_pos_iff_of_free, Submodule.nontrivial_iff_ne_bot]
    intro hbot
    apply hWlt
    have h := hcompl.sup_eq_top
    rwa [hbot, sup_bot_eq] at h
  have hker := isPGroup_ker_prod H hcompl hW
  rcases lt_or_ge (Module.finrank F W) 2 with hlt | hge
  · have hW1 : Module.finrank F W = 1 := by omega
    have hW'2 : Module.finrank F W' = 2 := by omega
    have honeW : actW H hW = 1 :=
      monoidHom_eq_one_of_finrank_eq_one hW1 (oPPrimeHull_top_of_eq hH) (actW H hW)
    have hkerW' : IsPGroup p (actW' H hcompl hW).ker := by
      have hEq : ((actW H hW).prod (actW' H hcompl hW)).ker = (actW' H hcompl hW).ker := by
        rw [MonoidHom.ker_prod, honeW, MonoidHom.ker_one, top_inf_eq]
      rwa [hEq] at hker
    exact to_quotient_pCore (F := F) hD hW'2 (oPPrimeHull_top_of_eq hH) (actW' H hcompl hW) hkerW'
  · have hW2 : Module.finrank F W = 2 := by omega
    have hW'1 : Module.finrank F W' = 1 := by omega
    have honeW' : actW' H hcompl hW = 1 :=
      monoidHom_eq_one_of_finrank_eq_one hW'1 (oPPrimeHull_top_of_eq hH) (actW' H hcompl hW)
    have hkerW : IsPGroup p (actW H hW).ker := by
      have hEq : ((actW H hW).prod (actW' H hcompl hW)).ker = (actW H hW).ker := by
        rw [MonoidHom.ker_prod, honeW', MonoidHom.ker_one, inf_top_eq]
      rwa [hEq] at hker
    exact to_quotient_pCore (F := F) hD hW2 (oPPrimeHull_top_of_eq hH) (actW H hW) hkerW

end DegreeThree

theorem sl2_or_trivial_of_not_irreducible (hD : SLTwoOrTrivialAt p)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hH : oPPrimeHull p H = H)
    (hred : ¬ CFSG.RepresentationTheory.IsIrreducibleMatrixRep H.subtype) :
    IsSLType 2 (ZMod p) (↥H ⧸ CFSG.pCore p ↥H) ∨
      Nat.card (↥H ⧸ CFSG.pCore p ↥H) = 1 :=
  sl2_or_trivial_of_not_irreducible_field (F := ZMod p) hD hH hred

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

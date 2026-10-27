module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootAdj
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs
public import CFSG.LieType.Chevalley.E6PinnedAdjoint
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootStd

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot

open Psi

variable {K : Type} [Field K]

theorem Psi.list_prod_weylElt_rootVec_sgn
    (ω : List (Fin TwistTag.E6.tag.rank)) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧
      (((ω.map fun i => weylElt TwistTag.E6.tag K i 1).prod : ModGL TwistTag.E6.tag K) :
          Module.End K (RootModule TwistTag.E6.tag K)) (rootVec TwistTag.E6.tag K β) =
        ε • rootVec TwistTag.E6.tag K ((coxeterSystem TwistTag.E6.tag).wordProd ω • β) := by
  induction ω with
  | nil => exact ⟨1, Or.inl rfl, by simp⟩
  | cons i ω ih =>
    obtain ⟨ε, hε, h⟩ := ih
    have hr : IsRoot TwistTag.E6.tag ((coxeterSystem TwistTag.E6.tag).wordProd ω • β) :=
      IsRoot.smul hβ _
    refine ⟨ε * (-1) ^ stringDown TwistTag.E6.tag i
      ((coxeterSystem TwistTag.E6.tag).wordProd ω • β), ?_, ?_⟩
    · rcases hε with rfl | rfl <;> rcases neg_one_pow_eq_or K
        (stringDown TwistTag.E6.tag i ((coxeterSystem TwistTag.E6.tag).wordProd ω • β)) with
        h' | h' <;> rw [h'] <;> simp
    · have e : (coxeterSystem TwistTag.E6.tag).wordProd (i :: ω) • β =
          reflect TwistTag.E6.tag i ((coxeterSystem TwistTag.E6.tag).wordProd ω • β) := by
        rw [CoxeterSystem.wordProd_cons, mul_smul]
        exact simple_smul i _
      rw [e, List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, h, map_smul,
        E6PinnedAdjoint.weylElt_one_rootVec i hr, smul_smul]

theorem Psi.canonicalRep_rootVec_sgn
    (w : WeylGroup TwistTag.E6.tag) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧
      (canonicalRep (coxeterSystem TwistTag.E6.tag) K w :
          Module.End K (RootModule TwistTag.E6.tag K)) (rootVec TwistTag.E6.tag K β) =
        ε • rootVec TwistTag.E6.tag K (w • β) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem TwistTag.E6.tag).exists_isReduced w
  rw [canonicalRep_wordProd hω]
  exact list_prod_weylElt_rootVec_sgn ω hβ

@[expose] def Psi.Hc (K : Type) [Field K] : Submodule K (RootModule TwistTag.E6.tag K) :=
  Finsupp.supported K K (Set.range (Sum.inl : Fin TwistTag.E6.tag.rank → Label TwistTag.E6.tag))

theorem Psi.hVec_mem_Hc (l : Fin TwistTag.E6.tag.rank) : hVec TwistTag.E6.tag K l ∈ Hc K :=
  Finsupp.single_mem_supported K _ ⟨l, rfl⟩

theorem Psi.apply_inr_of_mem_Hc {x : RootModule TwistTag.E6.tag K} (hx : x ∈ Hc K)
    (ν : Fin TwistTag.E6.tag.rank → ℤ) (hν : IsRoot TwistTag.E6.tag ν) :
    x (Sum.inr ⟨ν, hν⟩) = 0 :=
  (Finsupp.mem_supported' K x).1 hx _ (by simp)

theorem Psi.mem_span_Hc {x : RootModule TwistTag.E6.tag K} (hx : x ∈ Hc K) :
    x ∈ Submodule.span K ((fun b => (Finsupp.single b (1 : K) : RootModule TwistTag.E6.tag K)) ''
      Set.range (Sum.inl : Fin TwistTag.E6.tag.rank → Label TwistTag.E6.tag)) := by
  rwa [← Finsupp.supported_eq_span_single]

theorem Psi.weylElt_Hc
    (j : Fin TwistTag.E6.tag.rank) (t : Kˣ) {x : RootModule TwistTag.E6.tag K} (hx : x ∈ Hc K) :
    (weylElt TwistTag.E6.tag K j t : Module.End K (RootModule TwistTag.E6.tag K)) x ∈ Hc K := by
  refine Submodule.span_induction
    (p := fun x _ => (weylElt TwistTag.E6.tag K j t : Module.End K (RootModule TwistTag.E6.tag K))
      x ∈ Hc K) ?_ ?_ ?_ ?_ (mem_span_Hc hx)
  · rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
    have : (weylElt TwistTag.E6.tag K j t : Module.End K (RootModule TwistTag.E6.tag K))
        (Finsupp.single (Sum.inl l) 1) = hVec TwistTag.E6.tag K l -
          (((TwistTag.E6.tag.cartan l j).natAbs : ℕ) : K) • hVec TwistTag.E6.tag K j :=
      weylElt_hVec j l t
    rw [this]
    exact sub_mem (hVec_mem_Hc l) (Submodule.smul_mem _ _ (hVec_mem_Hc j))
  · simp
  · intro x y _ _ hx hy
    rw [map_add]
    exact add_mem hx hy
  · intro a x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

theorem Psi.torusElt_Hc
    (j : Fin TwistTag.E6.tag.rank) (t : Kˣ) {x : RootModule TwistTag.E6.tag K} (hx : x ∈ Hc K) :
    (torusElt TwistTag.E6.tag K j t : Module.End K (RootModule TwistTag.E6.tag K)) x ∈ Hc K := by
  refine Submodule.span_induction
    (p := fun x _ => (torusElt TwistTag.E6.tag K j t : Module.End K (RootModule TwistTag.E6.tag K))
      x ∈ Hc K) ?_ ?_ ?_ ?_ (mem_span_Hc hx)
  · rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
    have : (torusElt TwistTag.E6.tag K j t : Module.End K (RootModule TwistTag.E6.tag K))
        (Finsupp.single (Sum.inl l) 1) = hVec TwistTag.E6.tag K l := torusElt_hVec j l t
    rw [this]
    exact hVec_mem_Hc l
  · simp
  · intro x y _ _ hx hy
    rw [map_add]
    exact add_mem hx hy
  · intro a x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

@[expose] def Psi.StabH (K : Type) [Field K] : Subgroup (ModGL TwistTag.E6.tag K) where
  carrier := {g | (∀ x ∈ Hc K, (g : Module.End K (RootModule TwistTag.E6.tag K)) x ∈ Hc K) ∧
    ∀ x ∈ Hc K, ((g⁻¹ : ModGL TwistTag.E6.tag K) :
      Module.End K (RootModule TwistTag.E6.tag K)) x ∈ Hc K}
  mul_mem' {a b} ha hb := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [Units.val_mul, Module.End.mul_apply]
      exact ha.1 _ (hb.1 x hx)
    · rw [mul_inv_rev, Units.val_mul, Module.End.mul_apply]
      exact hb.2 _ (ha.2 x hx)
  one_mem' := ⟨fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩
  inv_mem' {a} ha := ⟨ha.2, fun x hx => by rw [inv_inv]; exact ha.1 x hx⟩

theorem Psi.canonicalRep_mem_StabH
    (w : WeylGroup TwistTag.E6.tag) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) K w ∈ StabH K := by
  refine (Subgroup.closure_le (StabH K)).2 ?_ (canonicalRep_mem_closure _ K w)
  rintro _ ⟨i, rfl⟩
  exact ⟨fun x hx => weylElt_Hc i 1 hx, fun x hx => by
    rw [weylElt_inv]
    exact weylElt_Hc i (-1) hx⟩

theorem Psi.w0_apply_one_aux : ∀ ν ∈ rootFinset TwistTag.E6.tag,
    (w0word.foldr (fun a w => (TwistTag.E6.orbitWord a).foldr (reflect TwistTag.E6.tag) w) ν)
        (e6Idx 1) = ∑ j, TwistTag.E6.tag.cartan (e6Idx 1) j * ν j := by
  decide +kernel

theorem Psi.wordProd_smul_aux (ω : List (Fin TwistTag.E6.tag.rank))
    (v : Fin TwistTag.E6.tag.rank → ℤ) :
    (coxeterSystem TwistTag.E6.tag).wordProd ω • v = ω.foldr (reflect TwistTag.E6.tag) v := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul]
    rfl

theorem Psi.prod_orbitReflection_smul' (l : List (Fin TwistTag.E6.foldedTag.rank))
    (v : Fin TwistTag.E6.tag.rank → ℤ) :
    (l.map TwistTag.E6.orbitReflection).prod • v =
      l.foldr (fun a w => (TwistTag.E6.orbitWord a).foldr (reflect TwistTag.E6.tag) w) v := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih, List.foldr_cons]
    exact wordProd_smul_aux (TwistTag.E6.orbitWord a) _

theorem Psi.w0_smul_apply_one {ν : Fin TwistTag.E6.tag.rank → ℤ}
    (hν : IsRoot TwistTag.E6.tag ν) :
    (w0 • ν) (e6Idx 1) = ∑ j, TwistTag.E6.tag.cartan (e6Idx 1) j * ν j := by
  rw [w0, prod_orbitReflection_smul']
  exact w0_apply_one_aux ν (mem_rootFinset.2 hν)

theorem Psi.orbit_card_a2 : (TwistTag.E6.orbit a2).card = 1 := by decide +kernel

theorem Psi.orbitMin_a2' : TwistTag.E6.orbitMin a2 = e6Idx 1 := by decide +kernel

section Torus

variable (σ : K ≃+* K)

theorem Psi.coe_orbitX_a2 (c : orbitField TwistTag.E6 K σ.toRingHom a2) :
    ((orbitX TwistTag.E6 K σ.toRingHom a2 c : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) = xUnit TwistTag.E6.tag K (e6Idx 1) (c : K) := by
  rw [coe_orbitX, orbit_card_a2, orbitMin_a2']
  simp [List.range_succ]

theorem Psi.coe_orbitY_a2 (c : orbitField TwistTag.E6 K σ.toRingHom a2) :
    ((orbitY TwistTag.E6 K σ.toRingHom a2 c : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) = yUnit TwistTag.E6.tag K (e6Idx 1) (c : K) := by
  rw [coe_orbitY, orbit_card_a2, orbitMin_a2']
  simp [List.range_succ]

@[expose] def Psi.unitOfField (u : (orbitField TwistTag.E6 K σ.toRingHom a2)ˣ) : Kˣ :=
  Units.map (Subfield.subtype (orbitField TwistTag.E6 K σ.toRingHom a2)).toMonoidHom u

theorem Psi.coe_unitOfField (u : (orbitField TwistTag.E6 K σ.toRingHom a2)ˣ) :
    ((unitOfField σ u : Kˣ) : K) = ((u : orbitField TwistTag.E6 K σ.toRingHom a2) : K) := rfl

theorem Psi.coe_orbitN_a2 (u : (orbitField TwistTag.E6 K σ.toRingHom a2)ˣ) :
    ((orbitN TwistTag.E6 K σ.toRingHom a2 u : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) = weylElt TwistTag.E6.tag K (e6Idx 1) (unitOfField σ u) := by
  rw [orbitN, Subgroup.coe_mul, Subgroup.coe_mul, coe_orbitX_a2, coe_orbitY_a2,
    CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul]
  congr 3

theorem Psi.coe_orbitH_a2 (u : (orbitField TwistTag.E6 K σ.toRingHom a2)ˣ) :
    ((orbitH TwistTag.E6 K σ.toRingHom a2 u : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) = torusElt TwistTag.E6.tag K (e6Idx 1) (unitOfField σ u) := by
  have h1 : unitOfField σ (1 : (orbitField TwistTag.E6 K σ.toRingHom a2)ˣ) = 1 :=
    map_one (Units.map (Subfield.subtype (orbitField TwistTag.E6 K σ.toRingHom a2)).toMonoidHom)
  rw [orbitH, Subgroup.coe_mul, Subgroup.coe_inv, coe_orbitN_a2, coe_orbitN_a2, h1, weylElt_inv]
  rfl

end Torus

theorem Psi.units_inv_apply_of_apply_eq_unit {M : Type*} [AddCommGroup M] [Module K M]
    (g : (Module.End K M)ˣ) {x y : M} (a : Kˣ)
    (h : (g : Module.End K M) x = (a : K) • y) :
    ((g⁻¹ : (Module.End K M)ˣ) : Module.End K M) y = ((a⁻¹ : Kˣ) : K) • x := by
  have h1 := congrArg (fun z => ((g⁻¹ : (Module.End K M)ˣ) : Module.End K M) z) h
  simp only [map_smul] at h1
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply] at h1
  rw [h1, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

section Conj


theorem Psi.conj_torus_rootVec (t : Kˣ) {μ : Fin TwistTag.E6.tag.rank → ℤ}
    (hμ : IsRoot TwistTag.E6.tag μ) :
    ((n0 * torusElt TwistTag.E6.tag K (e6Idx 1) t * n0⁻¹ : ModGL TwistTag.E6.tag K) :
        Module.End K (RootModule TwistTag.E6.tag K)) (rootVec TwistTag.E6.tag K μ) =
      ((t ^ μ (e6Idx 1) : Kˣ) : K) • rootVec TwistTag.E6.tag K μ := by
  have hν : IsRoot TwistTag.E6.tag (w0⁻¹ • μ) := IsRoot.smul hμ w0⁻¹
  have hwν : w0 • (w0⁻¹ • μ) = μ := smul_inv_smul w0 μ
  obtain ⟨ε, hε, h1⟩ := canonicalRep_rootVec_sgn (K := K) w0 hν
  rw [hwν] at h1
  have h1' : (n0 (K := K) : Module.End K (RootModule TwistTag.E6.tag K))
      (rootVec TwistTag.E6.tag K (w0⁻¹ • μ)) = ε • rootVec TwistTag.E6.tag K μ := h1
  have h2 := E6PinnedAdjoint.units_inv_apply_of_apply_eq (n0 (K := K)) ε hε h1'
  have hm : ∑ j, TwistTag.E6.tag.cartan (e6Idx 1) j * (w0⁻¹ • μ) j = μ (e6Idx 1) := by
    rw [← w0_smul_apply_one hν, hwν]
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, h2]
  simp only [map_smul]
  rw [torusElt_rootVec _ _ hν, hm]
  simp only [map_smul, h1', smul_smul]
  congr 1
  rcases hε with rfl | rfl <;> ring

theorem Psi.conj_torus_Hc (t : Kˣ) (l : Fin TwistTag.E6.tag.rank) :
    ((n0 * torusElt TwistTag.E6.tag K (e6Idx 1) t * n0⁻¹ : ModGL TwistTag.E6.tag K) :
        Module.End K (RootModule TwistTag.E6.tag K)) (hVec TwistTag.E6.tag K l) ∈ Hc K := by
  have hn : n0 (K := K) ∈ StabH K := canonicalRep_mem_StabH w0
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
  exact hn.1 _ (torusElt_Hc _ t (hn.2 _ (hVec_mem_Hc l)))

theorem Psi.piD_torus (t : Kˣ) (y : RootModule TwistTag.E6.tag K) :
    piD K (((n0 * torusElt TwistTag.E6.tag K (e6Idx 1) t * n0⁻¹ : ModGL TwistTag.E6.tag K) :
        Module.End K (RootModule TwistTag.E6.tag K)) y) = ((t⁻¹ : Kˣ) : K) • piD K y := by
  have key : (piD K).comp ((n0 * torusElt TwistTag.E6.tag K (e6Idx 1) t * n0⁻¹ :
      ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) =
      (((t⁻¹ : Kˣ) : K) • (LinearMap.id : Rv K →ₗ[K] Rv K)).comp (piD K) := by
    refine Finsupp.basisSingleOne.ext fun b => ?_
    rcases b with l | ⟨μ, hμ⟩
    · show piD K (((n0 * torusElt TwistTag.E6.tag K (e6Idx 1) t * n0⁻¹ : ModGL TwistTag.E6.tag K) :
        Module.End K (RootModule TwistTag.E6.tag K)) (hVec TwistTag.E6.tag K l)) =
        (((t⁻¹ : Kˣ) : K) • (LinearMap.id : Rv K →ₗ[K] Rv K)) (piD K (hVec TwistTag.E6.tag K l))
      rw [piD_hVec, map_zero]
      exact piD_eq_zero_of_apply_eq_zero fun γ =>
        apply_inr_of_mem_Hc (conj_torus_Hc t l) _ (isRoot_sub_highest γ)
    · have hb : (Finsupp.single (Sum.inr ⟨μ, hμ⟩) 1 : RootModule TwistTag.E6.tag K) =
          rootVec TwistTag.E6.tag K μ := (rootVec_eq_single_of_isRoot hμ).symm
      show piD K (((n0 * torusElt TwistTag.E6.tag K (e6Idx 1) t * n0⁻¹ : ModGL TwistTag.E6.tag K) :
        Module.End K (RootModule TwistTag.E6.tag K)) (Finsupp.single (Sum.inr ⟨μ, hμ⟩) 1)) =
        (((t⁻¹ : Kˣ) : K) • (LinearMap.id : Rv K →ₗ[K] Rv K))
          (piD K (Finsupp.single (Sum.inr ⟨μ, hμ⟩) 1))
      rw [hb, conj_torus_rootVec t hμ, map_smul]
      ext γ
      simp only [Pi.smul_apply, piD_rootVec, smul_eq_mul, LinearMap.smul_apply, LinearMap.id_apply]
      by_cases h : μ = γ.1 - e6HighestRoot
      · rw [if_pos h, h, sub_highest_apply_one γ, zpow_neg_one]
      · rw [if_neg h]
        simp
  exact LinearMap.congr_fun key y

theorem Psi.torus_v0 (t : Kˣ) :
    ((n0 * torusElt TwistTag.E6.tag K (e6Idx 1) t * n0⁻¹ : ModGL TwistTag.E6.tag K) :
        Module.End K (RootModule TwistTag.E6.tag K)) (v0 K) =
      ((t ^ (-2 : ℤ) : Kˣ) : K) • v0 K := by
  have := conj_torus_rootVec (K := K) t isRoot_neg_highest
  simp only [Pi.neg_apply, e6HighestRoot_idx_one] at this
  exact this

theorem psi_conj_torus (σ : K ≃+* K) (u : (orbitField TwistTag.E6 K σ.toRingHom a2)ˣ)
    (z : ModGL TwistTag.E6.tag K) :
    psi K ((n0 (K := K) * ((orbitH TwistTag.E6 K σ.toRingHom a2 u :
          adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) * (n0 (K := K))⁻¹) * z *
        (n0 (K := K) * ((orbitH TwistTag.E6 K σ.toRingHom a2 u :
          adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) * (n0 (K := K))⁻¹)⁻¹) =
      ((u : orbitField TwistTag.E6 K σ.toRingHom a2) : K) • psi K z := by
  rw [coe_orbitH_a2]
  set t := unitOfField σ u with ht
  have h0 := units_inv_apply_of_apply_eq_unit (n0 * torusElt TwistTag.E6.tag K (e6Idx 1) t * n0⁻¹)
    (t ^ (-2 : ℤ)) (torus_v0 (K := K) t)
  have := psi_conj (n0 * torusElt TwistTag.E6.tag K (e6Idx 1) t * n0⁻¹) z
    (((t ^ (-2 : ℤ))⁻¹ : Kˣ) : K) (((t⁻¹ : Kˣ) : K) • (LinearMap.id : Rv K →ₗ[K] Rv K)) h0
    (fun y => by rw [piD_torus]; rfl)
  have e1 : (((t ^ (-2 : ℤ))⁻¹ : Kˣ) : K) = (t : K) ^ 2 := by
    rw [zpow_neg, inv_inv]
    simp
  rw [e1] at this
  rw [this]
  ext γ
  simp only [Pi.smul_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
    Units.val_inv_eq_inv_val]
  have htne : (t : K) ≠ 0 := t.ne_zero
  rw [← coe_unitOfField σ u]
  field_simp
  exact mul_comm _ _

end Conj

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

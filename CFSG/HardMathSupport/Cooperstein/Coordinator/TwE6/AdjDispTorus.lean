module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.Interfaces

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule

@[expose] def twN1 : Fin TwistTag.E6.foldedTag.rank := ⟨1, by decide⟩

theorem orbit_card_twN0 : (TwistTag.E6.orbit twN0).card = 2 := by decide

theorem orbit_card_twN1 : (TwistTag.E6.orbit twN1).card = 2 := by decide

theorem rank_E6_eq : Tag.E6.rank = 6 := by decide

@[expose] def e6node (i : ℕ) (h : i < 6) : Fin Tag.E6.rank := ⟨i, lt_of_lt_of_eq h rank_E6_eq.symm⟩

@[expose] def e6n0 : Fin Tag.E6.rank := e6node 0 (by norm_num)
@[expose] def e6n2 : Fin Tag.E6.rank := e6node 2 (by norm_num)
@[expose] def e6n4 : Fin Tag.E6.rank := e6node 4 (by norm_num)
@[expose] def e6n5 : Fin Tag.E6.rank := e6node 5 (by norm_num)
@[expose] def e6n1 : Fin Tag.E6.rank := e6node 1 (by norm_num)
@[expose] def e6n3 : Fin Tag.E6.rank := e6node 3 (by norm_num)

theorem e6n_val : e6n0.val = 0 ∧ e6n1.val = 1 ∧ e6n2.val = 2 ∧ e6n3.val = 3 ∧ e6n4.val = 4 ∧
    e6n5.val = 5 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem e6c_vals :
    CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6c e6n0 = 1 ∧
    CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6c e6n2 = 2 ∧
    CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6c e6n4 = 1 ∧
    CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6c e6n5 = 2 ∧
    CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6c e6n1 = 0 ∧
    CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6c e6n3 = 0 := by decide

theorem perm_orbitMin_00 : (TwistTag.E6.perm ^ 0) (TwistTag.E6.orbitMin twN0) =
    e6n0 :=
  Fin.ext (by show ((TwistTag.E6.perm ^ 0) (TwistTag.E6.orbitMin twN0)).val = 0; decide)

theorem perm_orbitMin_01 : (TwistTag.E6.perm ^ 1) (TwistTag.E6.orbitMin twN0) =
    e6n5 :=
  Fin.ext (by show ((TwistTag.E6.perm ^ 1) (TwistTag.E6.orbitMin twN0)).val = 5; decide)

theorem perm_orbitMin_10 : (TwistTag.E6.perm ^ 0) (TwistTag.E6.orbitMin twN1) =
    e6n2 :=
  Fin.ext (by show ((TwistTag.E6.perm ^ 0) (TwistTag.E6.orbitMin twN1)).val = 2; decide)

theorem perm_orbitMin_11 : (TwistTag.E6.perm ^ 1) (TwistTag.E6.orbitMin twN1) =
    e6n4 :=
  Fin.ext (by show ((TwistTag.E6.perm ^ 1) (TwistTag.E6.orbitMin twN1)).val = 4; decide)

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

section Mult

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

include hf hK hσ in
theorem chi_mul_cover {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V} {y : V}
    {χ : ↥(TwistedE6.fixedGroup K σ) → k} {J : Finset (Fin TwistTag.E6.foldedTag.rank)}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    {h h' : ↥(TwistedE6.fixedGroup K σ)}
    (hh : h ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ))
    (hh' : h' ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ)) :
    χ (h * h') = χ h * χ h' := by
  have hmul : h * h' ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ) :=
    mul_mem hh hh'
  have h1 := ht.2.2.1 _ hmul
  have h2 : ρ (h * h') y = (χ h * χ h') • y := by
    rw [map_mul, Module.End.mul_apply, ht.2.2.1 _ hh', map_smul, ht.2.2.1 _ hh, smul_smul, mul_comm]
  exact smul_left_injective k ht.2.1 (h1.symm.trans h2)

include hf hK hσ in
theorem chi_one_cover {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V} {y : V}
    {χ : ↥(TwistedE6.fixedGroup K σ) → k} {J : Finset (Fin TwistTag.E6.foldedTag.rank)}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J) : χ 1 = 1 := by
  apply smul_left_injective k ht.2.1
  show χ 1 • y = (1 : k) • y
  rw [← ht.2.2.1 1 (one_mem _), map_one, Module.End.one_apply, one_smul]

include hf hK hσ in
theorem chi_list_prod_cover {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V} {y : V}
    {χ : ↥(TwistedE6.fixedGroup K σ) → k} {J : Finset (Fin TwistTag.E6.foldedTag.rank)}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    (l : List ↥(TwistedE6.fixedGroup K σ))
    (hl : ∀ x ∈ l, x ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ)) :
    χ l.prod = (l.map χ).prod := by
  induction l with
  | nil => simpa using chi_one_cover hf hK σ hσ ht
  | cons x l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons,
      chi_mul_cover hf hK σ hσ ht (hl x List.mem_cons_self)
        (Subgroup.list_prod_mem _ fun y hy => hl y (List.mem_cons_of_mem _ hy)),
      ih fun y hy => hl y (List.mem_cons_of_mem _ hy)]

end Mult

include hf hK hσ in
theorem exists_hatH_prod {h : ↥(TwistedE6.fixedGroup K σ)}
    (hh : h ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ)) :
    ∃ s : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ a)ˣ,
      ∃ z ∈ (coverHom hf hK σ hσ).ker,
        h = ((List.finRange TwistTag.E6.foldedTag.rank).map fun a =>
          hatH hf hK σ hσ a (s a)).prod * z := by
  have hg : ((coverHom hf hK σ hσ h : ↥(graphFixedRootGroup TwistTag.E6 K σ)) : ModGL TwistTag.E6.tag K)
      ∈ graphFixedRootTorus TwistTag.E6 K σ := hh
  rw [CFSG.Timmesfeld.ExceptionalOrders.graphFixedRootTorus_eq_compatTorus
    (surjective_of_finite σ)] at hg
  obtain ⟨c, hc, hcg⟩ := (CFSG.Timmesfeld.ExceptionalOrders.mem_compatTorus σ).1 hg
  obtain ⟨s, rfl⟩ := exists_compatDiag_eq (σ := σ) hc
  refine ⟨s, ((List.finRange TwistTag.E6.foldedTag.rank).map fun a =>
    hatH hf hK σ hσ a (s a)).prod⁻¹ * h, ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_list_prod, List.map_map]
  have e1 : (((List.finRange TwistTag.E6.foldedTag.rank).map
      ((coverHom hf hK σ hσ) ∘ fun a => hatH hf hK σ hσ a (s a))).prod :
        ↥(graphFixedRootGroup TwistTag.E6 K σ)) = coverHom hf hK σ hσ h := by
    apply Subtype.ext
    rw [Subgroup.val_list_prod, List.map_map]
    have := list_prod_orbitH (K := K) (σ := σ) (t := TwistTag.E6) s
    rw [← hcg, coe_torusCoordHom, List.ofFn_eq_map, ← this]
    refine congrArg List.prod (List.map_congr_left fun a _ => ?_)
    show ((coverHom hf hK σ hσ (hatH hf hK σ hσ a (s a)) : ↥(graphFixedRootGroup TwistTag.E6 K σ)) :
      ModGL TwistTag.E6.tag K) = _
    rw [coverHom_hatH]
    rfl
  rw [e1, inv_mul_cancel]

include hK hσ in
@[expose] def mkOrbitUnit (a : Fin TwistTag.E6.foldedTag.rank)
    (ha : (TwistTag.E6.orbit a).card = 2) (w : Kˣ) : (orbitField TwistTag.E6 K σ a)ˣ :=
  have hmem : ∀ c : K, c ∈ orbitField TwistTag.E6 K σ a := fun c => by
    rw [mem_orbitField, ha, pow_two]
    exact sigma_sigma_eq hK σ hσ c
  ⟨⟨(w : K), hmem _⟩, ⟨((w⁻¹ : Kˣ) : K), hmem _⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩

include hf hK hσ in
theorem ker_eq_hatH {z : ↥(TwistedE6.fixedGroup K σ)} (hz : z ∈ (coverHom hf hK σ hσ).ker) :
    ∃ w : Kˣ, z = hatH hf hK σ hσ twN0 (mkOrbitUnit hK σ hσ twN0 orbit_card_twN0 w) *
      hatH hf hK σ hσ twN1 (mkOrbitUnit hK σ hσ twN1 orbit_card_twN1 (w ^ 2)) := by
  rw [ker_coverHom hf hK σ hσ] at hz
  obtain ⟨v, hv⟩ := CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.centerHom_surjective
    (θ := σ) (q := 2 ^ f) hK hσ ⟨z, hz⟩
  have hz' : (z : ↥(e6Data_valid.minGroup K)) =
      CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus e6Data_valid K
        (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.tvec (v : Kˣ) CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6c) := by
    have := congrArg (fun x : ↥(Subgroup.center ↥(TwistedE6.fixedGroup K σ)) =>
      ((x : ↥(TwistedE6.fixedGroup K σ)) : ↥(e6Data_valid.minGroup K))) hv
    exact this.symm
  obtain ⟨h3, hθ⟩ := (CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.mem_rootsOfUnity_gcd_iff hσ).1
    v.2
  refine ⟨(v : Kˣ), Subtype.ext ?_⟩
  rw [hz']
  show _ = minOrbitHom σ twN0 (HSL _) * minOrbitHom σ twN1 (HSL _)
  rw [minOrbitHom_HSL, minOrbitHom_HSL, orbit_card_twN0, orbit_card_twN1]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.singleton_append,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hinv : ((v : Kˣ))⁻¹ = (v : Kˣ) ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact h3
  have hs2 : Units.map σ.toMonoidHom ((v : Kˣ) ^ 2) = (v : Kˣ) := by
    rw [map_pow]
    have : Units.map σ.toMonoidHom (v : Kˣ) = (v : Kˣ) ^ 2 := hθ.trans hinv
    rw [this, ← pow_mul]
    have h4 : (v : Kˣ) ^ 4 = (v : Kˣ) := by
      rw [show 4 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
    exact h4
  have u00 : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (ha : (TwistTag.E6.orbit a).card = 2) (w : Kˣ),
      Units.map ((σ ^ 0).comp (orbitField TwistTag.E6 K σ a).subtype).toMonoidHom
        (mkOrbitUnit hK σ hσ a ha w) = w := fun a ha w => Units.ext (by simp [mkOrbitUnit])
  have u01 : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (ha : (TwistTag.E6.orbit a).card = 2) (w : Kˣ),
      Units.map ((σ ^ 1).comp (orbitField TwistTag.E6 K σ a).subtype).toMonoidHom
        (mkOrbitUnit hK σ hσ a ha w) = Units.map σ.toMonoidHom w :=
    fun a ha w => Units.ext (by simp [mkOrbitUnit])
  rw [perm_orbitMin_00, perm_orbitMin_01, perm_orbitMin_10, perm_orbitMin_11, u00, u01, u00, u01]
  have hsv : Units.map σ.toMonoidHom (v : Kˣ) = (v : Kˣ) ^ 2 := hθ.trans hinv
  rw [hsv]
  simp only [hinv, hs2]
  have ht : CFSG.LieType.Steinberg.CentralExt.AdjointClosed.tvec (v : Kˣ)
      CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6c =
      Pi.mulSingle e6n0 (v : Kˣ) * Pi.mulSingle e6n5 ((v : Kˣ) ^ 2) *
        Pi.mulSingle e6n2 ((v : Kˣ) ^ 2) *
        Pi.mulSingle e6n4 (v : Kˣ) := by
    funext k
    obtain ⟨kv, hk⟩ := k
    have hk6 : kv < 6 := by rwa [rank_E6_eq] at hk
    obtain ⟨c0, c2, c4, c5, c1, c3⟩ := e6c_vals
    obtain ⟨v0, v1, v2, v3, v4, v5⟩ := e6n_val
    interval_cases kv
    · have : (⟨0, hk⟩ : Fin Tag.E6.rank) = e6n0 := rfl
      rw [this]
      simp [CFSG.LieType.Steinberg.CentralExt.AdjointClosed.tvec, c0, Pi.mulSingle_apply,
        Fin.ext_iff, v0, v2, v4, v5]
    · have : (⟨1, hk⟩ : Fin Tag.E6.rank) = e6n1 := rfl
      rw [this]
      simp [CFSG.LieType.Steinberg.CentralExt.AdjointClosed.tvec, c1, Pi.mulSingle_apply,
        Fin.ext_iff, v1, v0, v2, v4, v5]
    · have : (⟨2, hk⟩ : Fin Tag.E6.rank) = e6n2 := rfl
      rw [this]
      simp [CFSG.LieType.Steinberg.CentralExt.AdjointClosed.tvec, c2, Pi.mulSingle_apply,
        Fin.ext_iff, v2, v0, v4, v5]
    · have : (⟨3, hk⟩ : Fin Tag.E6.rank) = e6n3 := rfl
      rw [this]
      simp [CFSG.LieType.Steinberg.CentralExt.AdjointClosed.tvec, c3, Pi.mulSingle_apply,
        Fin.ext_iff, v3, v0, v2, v4, v5]
    · have : (⟨4, hk⟩ : Fin Tag.E6.rank) = e6n4 := rfl
      rw [this]
      simp [CFSG.LieType.Steinberg.CentralExt.AdjointClosed.tvec, c4, Pi.mulSingle_apply,
        Fin.ext_iff, v4, v0, v2, v5]
    · have : (⟨5, hk⟩ : Fin Tag.E6.rank) = e6n5 := rfl
      rw [this]
      simp [CFSG.LieType.Steinberg.CentralExt.AdjointClosed.tvec, c5, Pi.mulSingle_apply,
        Fin.ext_iff, v5, v0, v2, v4]
  rw [ht, map_mul, map_mul, map_mul, CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus_mulSingle,
    CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus_mulSingle,
    CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus_mulSingle,
    CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus_mulSingle]
  simp only [mul_assoc]

include hf hK hσ in
theorem hatH_mem_H (a : Fin TwistTag.E6.foldedTag.rank) (u : (orbitField TwistTag.E6 K σ a)ˣ) :
    hatH hf hK σ hσ a u ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ) :=
  (twistedE6CoverRankOne hf hK σ hσ).hh_mem a u

include hf hK hσ in
theorem chi_ker_eq_one {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V} {y : V}
    {χ : ↥(TwistedE6.fixedGroup K σ) → k} {J : Finset (Fin TwistTag.E6.foldedTag.rank)}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J) (h0 : twN0 ∈ J) (h1 : twN1 ∈ J)
    {z : ↥(TwistedE6.fixedGroup K σ)} (hz : z ∈ (coverHom hf hK σ hσ).ker) : χ z = 1 := by
  obtain ⟨w, rfl⟩ := ker_eq_hatH hf hK σ hσ hz
  rw [chi_mul_cover hf hK σ hσ ht (hatH_mem_H hf hK σ hσ _ _) (hatH_mem_H hf hK σ hσ _ _)]
  have e0 : ∀ u, χ (hatH hf hK σ hσ twN0 u) = 1 := ((ht.2.2.2 twN0).1 h0).1
  have e1 : ∀ u, χ (hatH hf hK σ hσ twN1 u) = 1 := ((ht.2.2.2 twN1).1 h1).1
  rw [e0, e1, mul_one]

include hf hK hσ in
theorem chi_eq_on_Hcover {k V W : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] {ρ₁ : Representation k ↥(TwistedE6.fixedGroup K σ) V}
    {ρ₂ : Representation k ↥(TwistedE6.fixedGroup K σ) W} {y₁ : V} {y₂ : W}
    {χ₁ χ₂ : ↥(TwistedE6.fixedGroup K σ) → k} {J₁ J₂ : Finset (Fin TwistTag.E6.foldedTag.rank)}
    (ht₁ : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ₁ y₁ χ₁ J₁)
    (ht₂ : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ₂ y₂ χ₂ J₂)
    (h0₁ : twN0 ∈ J₁) (h1₁ : twN1 ∈ J₁) (h0₂ : twN0 ∈ J₂) (h1₂ : twN1 ∈ J₂)
    (hd : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (u : (orbitField TwistTag.E6 K σ a)ˣ),
      χ₁ (hatH hf hK σ hσ a u) = χ₂ (hatH hf hK σ hσ a u)) :
    ∀ h ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ), χ₁ h = χ₂ h := by
  intro h hh
  obtain ⟨s, z, hz, rfl⟩ := exists_hatH_prod hf hK σ hσ hh
  have hP : ∀ x ∈ (List.finRange TwistTag.E6.foldedTag.rank).map
      (fun a => hatH hf hK σ hσ a (s a)), x ∈ (twistedE6Datum hf hK σ hσ).H.comap
        (coverHom hf hK σ hσ) := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact hatH_mem_H hf hK σ hσ a (s a)
  have hPm := Subgroup.list_prod_mem _ hP
  have hzm : z ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ) := by
    show coverHom hf hK σ hσ z ∈ (twistedE6Datum hf hK σ hσ).H
    have h1 : coverHom hf hK σ hσ z = (1 : ↥(graphFixedRootGroup TwistTag.E6 K σ)) := hz
    rw [h1]
    exact Subgroup.one_mem _
  rw [chi_mul_cover hf hK σ hσ ht₁ hPm hzm, chi_mul_cover hf hK σ hσ ht₂ hPm hzm,
    chi_list_prod_cover hf hK σ hσ ht₁ _ hP, chi_list_prod_cover hf hK σ hσ ht₂ _ hP,
    chi_ker_eq_one hf hK σ hσ ht₁ h0₁ h1₁ hz, chi_ker_eq_one hf hK σ hσ ht₂ h0₂ h1₂ hz]
  simp only [List.map_map, mul_one]
  refine congrArg List.prod (List.map_congr_left fun a _ => ?_)
  exact hd a (s a)

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

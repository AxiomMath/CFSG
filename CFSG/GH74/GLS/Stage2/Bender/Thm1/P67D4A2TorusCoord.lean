module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Torus

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Compat

variable {K : Type} [Field K] {σ : K ≃+* K}

@[expose] def a2tcVec (x₀ x₁ x₂ x₃ : Kˣ) : Fin d4.rank → Kˣ := ![x₀, x₁, x₂, x₃]

@[expose] def a2tcCompat (σ : K ≃+* K) : Subgroup (Fin d4.rank → Kˣ) where
  carrier := {c | c (nd 1) = Units.map σ.toRingHom.toMonoidHom (c (nd 0)) ∧
    c (nd 3) = Units.map σ.toRingHom.toMonoidHom (c (nd 1)) ∧
    Units.map σ.toRingHom.toMonoidHom (c (nd 3)) = c (nd 0) ∧
    Units.map σ.toRingHom.toMonoidHom (c (nd 2)) = c (nd 2)}
  mul_mem' {a b} ha hb := by
    obtain ⟨a1, a2, a3, a4⟩ := ha
    obtain ⟨b1, b2, b3, b4⟩ := hb
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Pi.mul_apply, Pi.mul_apply, a1, b1, map_mul]
    · rw [Pi.mul_apply, Pi.mul_apply, a2, b2, map_mul]
    · rw [Pi.mul_apply, Pi.mul_apply, map_mul, a3, b3]
    · rw [Pi.mul_apply, map_mul, a4, b4]
  one_mem' := ⟨by simp, by simp, by simp, by simp⟩
  inv_mem' {a} ha := by
    obtain ⟨a1, a2, a3, a4⟩ := ha
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Pi.inv_apply, Pi.inv_apply, a1, map_inv]
    · rw [Pi.inv_apply, Pi.inv_apply, a2, map_inv]
    · rw [Pi.inv_apply, Pi.inv_apply, map_inv, a3]
    · rw [Pi.inv_apply, map_inv, a4]

theorem a2tc_long_mem {t : Kˣ} (ht : Units.map σ.toRingHom.toMonoidHom t = t) :
    a2tcVec t⁻¹ t⁻¹ (t ^ 2) t⁻¹ ∈ a2tcCompat σ := by
  have hinv : Units.map σ.toRingHom.toMonoidHom t⁻¹ = t⁻¹ := by rw [map_inv, ht]
  have hsq : Units.map σ.toRingHom.toMonoidHom (t ^ 2) = t ^ 2 := by rw [map_pow, ht]
  exact ⟨hinv.symm, hinv.symm, hinv, hsq⟩

theorem a2tc_short_mem (hσ3 : ∀ c, σ (σ (σ c)) = c) (t : Kˣ) :
    a2tcVec (t ^ 2) ((Units.map σ.toRingHom.toMonoidHom t) ^ 2)
      (t * Units.map σ.toRingHom.toMonoidHom t *
        Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom t))⁻¹
      ((Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom t)) ^ 2) ∈
        a2tcCompat σ := by
  have h3 : Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom
      (Units.map σ.toRingHom.toMonoidHom t)) = t := Units.ext (hσ3 t)
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (Units.map σ.toRingHom.toMonoidHom t) ^ 2 = Units.map σ.toRingHom.toMonoidHom (t ^ 2)
    rw [map_pow]
  · show (Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom t)) ^ 2 =
      Units.map σ.toRingHom.toMonoidHom ((Units.map σ.toRingHom.toMonoidHom t) ^ 2)
    rw [map_pow]
  · show Units.map σ.toRingHom.toMonoidHom
      ((Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom t)) ^ 2) = t ^ 2
    rw [map_pow, h3]
  · show Units.map σ.toRingHom.toMonoidHom (t * Units.map σ.toRingHom.toMonoidHom t *
        Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom t))⁻¹ =
      (t * Units.map σ.toRingHom.toMonoidHom t *
        Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom t))⁻¹
    rw [map_inv, map_mul, map_mul, h3]
    congr 1
    ac_rfl

end Compat

theorem a2tc_cartan_zero :
    d4.cartan (nd 0) (nd 0) = 2 ∧ d4.cartan (nd 0) (nd 1) = 0 ∧ d4.cartan (nd 0) (nd 2) = -1 ∧
      d4.cartan (nd 0) (nd 3) = 0 := by
  decide

theorem a2tc_cartan_one :
    d4.cartan (nd 1) (nd 0) = 0 ∧ d4.cartan (nd 1) (nd 1) = 2 ∧ d4.cartan (nd 1) (nd 2) = -1 ∧
      d4.cartan (nd 1) (nd 3) = 0 := by
  decide

theorem a2tc_cartan_three :
    d4.cartan (nd 3) (nd 0) = 0 ∧ d4.cartan (nd 3) (nd 1) = 0 ∧ d4.cartan (nd 3) (nd 2) = -1 ∧
      d4.cartan (nd 3) (nd 3) = 2 := by
  decide

section Vec

variable
  {K : Type} [Field K]

theorem a2tc_torusElt_two (t : Kˣ) :
    torusElt d4 K (nd 2) t = rootDiagUnit d4 (a2tcVec t⁻¹ t⁻¹ (t ^ 2) t⁻¹) := by
  rw [torusElt_eq_rootDiagUnit]
  congr 1
  funext j
  obtain ⟨c0, c1, c2, c3⟩ := a2tor_cartan_two
  fin_cases j
  · exact (congrArg (t ^ ·) c0).trans (zpow_neg_one t)
  · exact (congrArg (t ^ ·) c1).trans (zpow_neg_one t)
  · exact (congrArg (t ^ ·) c2).trans (zpow_ofNat t 2)
  · exact (congrArg (t ^ ·) c3).trans (zpow_neg_one t)

theorem a2tc_torusElt_short (u v w : Kˣ) :
    torusElt d4 K (nd 0) u * torusElt d4 K (nd 1) v * torusElt d4 K (nd 3) w =
      rootDiagUnit d4 (a2tcVec (u ^ 2) (v ^ 2) (u * v * w)⁻¹ (w ^ 2)) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
    ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  funext j
  obtain ⟨a0, a1, a2, a3⟩ := a2tc_cartan_zero
  obtain ⟨b0, b1, b2, b3⟩ := a2tc_cartan_one
  obtain ⟨c0, c1, c2, c3⟩ := a2tc_cartan_three
  fin_cases j
  · show u ^ d4.cartan (nd 0) (nd 0) * v ^ d4.cartan (nd 1) (nd 0) * w ^ d4.cartan (nd 3) (nd 0) =
      u ^ 2
    rw [a0, b0, c0]
    simp
  · show u ^ d4.cartan (nd 0) (nd 1) * v ^ d4.cartan (nd 1) (nd 1) * w ^ d4.cartan (nd 3) (nd 1) =
      v ^ 2
    rw [a1, b1, c1]
    simp
  · show u ^ d4.cartan (nd 0) (nd 2) * v ^ d4.cartan (nd 1) (nd 2) * w ^ d4.cartan (nd 3) (nd 2) =
      (u * v * w)⁻¹
    rw [a2, b2, c2, zpow_neg_one, zpow_neg_one, zpow_neg_one, mul_inv, mul_inv]
  · show u ^ d4.cartan (nd 0) (nd 3) * v ^ d4.cartan (nd 1) (nd 3) * w ^ d4.cartan (nd 3) (nd 3) =
      w ^ 2
    rw [a3, b3, c3]
    simp

end Vec

section Coord

variable
  {K : Type} [Field K] {σ : K ≃+* K}

theorem a2tc_iSup_le (hσ3 : ∀ c, σ (σ (σ c)) = c) :
    (⨆ i, hHatE σ.toRingHom i : Subgroup (adjointGroup d4 K)) ≤
      ((a2tcCompat σ).map (rootDiagUnitHom d4 K)).comap (adjointGroup d4 K).subtype := by
  refine iSup_le fun i => ?_
  match i with
  | ⟨0, _⟩ =>
    intro g hg
    obtain ⟨t, ht, rfl⟩ := a2tor_exists_of_mem_hHatE_zero hg
    exact ⟨_, a2tc_long_mem (t := t) (Units.ext ht), (a2tc_torusElt_two t).symm⟩
  | ⟨1, _⟩ =>
    intro g hg
    obtain ⟨t, rfl⟩ := a2tor_exists_of_mem_hHatE_one hg
    have e : ((hShortHom σ.toRingHom t : adjointGroup d4 K) : ModGL d4 K) =
        rootDiagUnit d4 (a2tcVec (t ^ 2) ((Units.map σ.toRingHom.toMonoidHom t) ^ 2)
          (t * Units.map σ.toRingHom.toMonoidHom t *
            Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom t))⁻¹
          ((Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom t)) ^ 2)) := by
      rw [hShortHom_apply]
      simp only [Subgroup.coe_mul, a2tor_coe_torusElement]
      exact a2tc_torusElt_short _ _ _
    exact ⟨_, a2tc_short_mem hσ3 t, e.symm⟩

theorem a2tc_coord (hσ3 : ∀ c, σ (σ (σ c)) = c) {g : adjointGroup d4 K}
    (hg : g ∈ ⨆ i, hHatE σ.toRingHom i) :
    ∃ c ∈ a2tcCompat σ, (g : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag c := by
  obtain ⟨c, hc, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (a2tc_iSup_le hσ3 hg))
  exact ⟨c, hc, e.symm⟩

end Coord

section Main

variable
  {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem A2Core.a2_torus_coord (h : A2Core σ d q) {g : adjointGroup d4 K}
    (hg : g ∈ ⨆ i, hHatE σ.toRingHom i) :
    ∃ c : Fin d4.rank → Kˣ, (g : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag c ∧
      c (nd 1) = Units.map σ.toRingHom.toMonoidHom (c (nd 0)) ∧
      c (nd 3) = Units.map σ.toRingHom.toMonoidHom (c (nd 1)) ∧
      Units.map σ.toRingHom.toMonoidHom (c (nd 3)) = c (nd 0) ∧
      Units.map σ.toRingHom.toMonoidHom (c (nd 2)) = c (nd 2) := by
  obtain ⟨c, hc, e⟩ := a2tc_coord
    (fun x => sigma_three_of_card (σ := σ.toRingHom) h.card h.frob x) hg
  exact ⟨c, e, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩

theorem A2Core.a2_torus_mem (h : A2Core σ d q) {a b : Kˣ}
    (ha : Units.map σ.toRingHom.toMonoidHom a = a) (hb : Units.map σ.toRingHom.toMonoidHom b = b) :
    ∃ g ∈ ⨆ i, hHatE σ.toRingHom i,
      (g : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![a, a, b, a] := by
  have _ := h
  have hu : Units.map σ.toRingHom.toMonoidHom (a ^ 2 * b) = a ^ 2 * b := by
    rw [map_mul, map_pow, ha, hb]
  have hτ : Units.map σ.toRingHom.toMonoidHom (a ^ 3 * b ^ 2) = a ^ 3 * b ^ 2 := by
    rw [map_mul, map_pow, map_pow, ha, hb]
  refine ⟨hShortHom σ.toRingHom (a ^ 2 * b) * torusElement d4 K (nd 2) (a ^ 3 * b ^ 2),
    Subgroup.mul_mem _ (le_iSup (hHatE σ.toRingHom) (ng 1) (a2tor_mem_hHatE_one _))
      (le_iSup (hHatE σ.toRingHom) (ng 0) (a2tor_mem_hHatE_zero (congrArg Units.val hτ))), ?_⟩
  rw [Subgroup.coe_mul, hShortHom_apply]
  simp only [Subgroup.coe_mul, a2tor_coe_torusElement]
  rw [hu, hu, a2tc_torusElt_short, a2tc_torusElt_two, ← rootDiagUnit_mul]
  change rootDiagUnit d4 _ = rootDiagUnit d4 (a2tcVec a a b a)
  congr 1
  funext j
  have ha0 := a.ne_zero
  have hb0 := b.ne_zero
  fin_cases j
  · show (a ^ 2 * b) ^ 2 * (a ^ 3 * b ^ 2)⁻¹ = a
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
  · show (a ^ 2 * b) ^ 2 * (a ^ 3 * b ^ 2)⁻¹ = a
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
  · show ((a ^ 2 * b) * (a ^ 2 * b) * (a ^ 2 * b))⁻¹ * (a ^ 3 * b ^ 2) ^ 2 = b
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
  · show (a ^ 2 * b) ^ 2 * (a ^ 3 * b ^ 2)⁻¹ = a
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp

end Main

section FixedUnits

variable {K : Type} [Field K]

theorem a2tc_card_fixedUnits {σ' : K →+* K} {q : ℕ} (hF : Nat.card (fixedField σ') = q) :
    Nat.card (fixedUnits σ') = q - 1 := by
  have key : Nat.card (fixedField σ')ˣ = Nat.card (fixedUnits σ') := by
    refine Nat.card_eq_of_bijective
      (fun u => (⟨Units.map (fixedField σ').subtype.toMonoidHom u, Units.ext u.1.2⟩ :
        fixedUnits σ')) ⟨?_, ?_⟩
    · intro u v huv
      exact Units.ext (Subtype.ext (congrArg (fun w : fixedUnits σ' => ((w : Kˣ) : K)) huv))
    · rintro ⟨v, hv⟩
      have hv' : σ' (v : K) = v := congrArg Units.val hv
      exact ⟨Units.mk0 ⟨(v : K), hv'⟩ (fun h => v.ne_zero (congrArg Subtype.val h)),
        Subtype.ext (Units.ext rfl)⟩
  rw [← key, Nat.card_units, hF]

end FixedUnits

section Card

variable
  {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem A2Core.a2_torus_card (h : A2Core σ d q) :
    Nat.card {t : (⨆ i, hHatE σ.toRingHom i : Subgroup (adjointGroup d4 K)) //
      a2Conj σ d ((t : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
        ((t : adjointGroup d4 K) : ModGL TwistTag.D4.tag K)} = (q - 1) ^ 2 := by
  classical
  have hmem : ∀ p : fixedUnits σ.toRingHom × fixedUnits σ.toRingHom,
      ∃ g ∈ ⨆ i, hHatE σ.toRingHom i,
        (g : ModGL d4 K) = rootDiagUnit d4 (a2tcVec p.1 p.1 p.2 p.1) :=
    fun p => a2_torus_mem h p.1.2 p.2.2
  choose g hg hgc using hmem
  have hfix : ∀ p, a2Conj σ d (g p : ModGL d4 K) = (g p : ModGL d4 K) := by
    intro p
    rw [hgc, a2tor_conj_rootDiagUnit]
    congr 1
    funext i
    fin_cases i
    · exact p.1.2
    · exact p.1.2
    · exact p.2.2
    · exact p.1.2
  let Ψ : fixedUnits σ.toRingHom × fixedUnits σ.toRingHom →
      {t : (⨆ i, hHatE σ.toRingHom i : Subgroup (adjointGroup d4 K)) //
        a2Conj σ d ((t : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
          ((t : adjointGroup d4 K) : ModGL TwistTag.D4.tag K)} :=
    fun p => ⟨⟨g p, hg p⟩, hfix p⟩
  have hbij : Function.Bijective Ψ := by
    refine ⟨?_, ?_⟩
    · intro p p' hpp'
      have e : (rootDiagUnit d4 (a2tcVec (p.1 : Kˣ) p.1 p.2 p.1) : ModGL d4 K) =
          rootDiagUnit d4 (a2tcVec (p'.1 : Kˣ) p'.1 p'.2 p'.1) := by
        rw [← hgc p, ← hgc p']
        exact congrArg (fun s => (((s.1 : ↥(⨆ i, hHatE σ.toRingHom i)) : adjointGroup d4 K) :
          ModGL d4 K)) hpp'
      have e' := rootDiagUnit_injective e
      have e0 := congrFun e' (nd 0)
      have e2 := congrFun e' (nd 2)
      exact Prod.ext (Subtype.ext e0) (Subtype.ext e2)
    · rintro ⟨⟨t, ht⟩, hfixt⟩
      have hfixt' : a2Conj σ d (t : ModGL d4 K) = (t : ModGL d4 K) := hfixt
      obtain ⟨c, hc, c1, c3, c3', c2⟩ := a2_torus_coord h ht
      rw [hc, a2tor_conj_rootDiagUnit] at hfixt'
      have hfc := congrFun (rootDiagUnit_injective hfixt')
      have f0 : Units.map σ.toRingHom.toMonoidHom (c (nd 0)) = c (nd 0) := hfc (nd 0)
      have f2 : Units.map σ.toRingHom.toMonoidHom (c (nd 2)) = c (nd 2) := hfc (nd 2)
      have e1 : c (nd 1) = c (nd 0) := c1.trans f0
      have e3 : c (nd 3) = c (nd 0) := by rw [c3, e1, f0]
      have hcv : a2tcVec (c (nd 0)) (c (nd 0)) (c (nd 2)) (c (nd 0)) = c := by
        funext i
        fin_cases i
        · rfl
        · exact e1.symm
        · rfl
        · exact e3.symm
      refine ⟨(⟨c (nd 0), f0⟩, ⟨c (nd 2), f2⟩), ?_⟩
      refine Subtype.ext (Subtype.ext (Subtype.ext ?_))
      change ((g (⟨c (nd 0), f0⟩, ⟨c (nd 2), f2⟩) : adjointGroup d4 K) : ModGL d4 K) =
        (t : ModGL d4 K)
      rw [hgc, hc]
      exact congrArg (rootDiagUnit d4) hcv
  rw [← Nat.card_eq_of_bijective Ψ hbij, Nat.card_prod, a2tc_card_fixedUnits
    (CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom h.two_le h.card
      (fun c => h.frob c)), sq]

end Card

end CFSG.GH74.GLS.Stage2.Bender.Thm1

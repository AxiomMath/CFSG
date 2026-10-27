module

public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.GF2Type.Smith1980Orth.W4SigmaGL
public import CFSG.LargeExtraspecial.S4CETool

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4C1

open Module QuadraticMap

namespace Par

section Hom

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {Γ : Type*} [Group Γ]

abbrev perp (Q : QuadraticForm (ZMod 2) V) (D : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  LinearMap.BilinForm.orthogonal Q.polarBilin D

theorem mem_perp {D : Submodule (ZMod 2) V} {v : V} :
    v ∈ perp Q D ↔ ∀ d ∈ D, polar Q d v = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  simp only [LinearMap.BilinForm.isOrtho_def, polarBilin_apply_apply]

variable (ρ : Γ →* (V ≃ₗ[ZMod 2] V)) {D : Submodule (ZMod 2) V}

theorem apply_inv_apply' (g : Γ) (d : V) : ρ g (ρ g⁻¹ d) = d := by
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem inv_apply_apply' (g : Γ) (d : V) : ρ g⁻¹ (ρ g d) = d := by
  rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

variable (hO : ∀ g, ρ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
  (hD : ∀ g, ∀ d ∈ D, ρ g d ∈ D)

include hD in
theorem map_D (g : Γ) : D.map (ρ g : V →ₗ[ZMod 2] V) = D := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨d, hd, rfl⟩
    exact hD g d hd
  · intro d hd
    exact ⟨ρ g⁻¹ d, hD g⁻¹ d hd, apply_inv_apply' ρ g d⟩

include hO hD in
theorem apply_mem_perp (g : Γ) {e : V} (he : e ∈ perp Q D) : ρ g e ∈ perp Q D := by
  rw [mem_perp] at he ⊢
  intro d hd
  have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hO g) (ρ g⁻¹ d) e
  rw [apply_inv_apply'] at h1
  rw [h1]
  exact he _ (hD g⁻¹ d hd)

include hO hD in
theorem map_E (g : Γ) : (perp Q D).map (ρ g : V →ₗ[ZMod 2] V) = perp Q D := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨e, he, rfl⟩
    exact apply_mem_perp ρ hO hD g he
  · intro e he
    exact ⟨ρ g⁻¹ e, apply_mem_perp ρ hO hD g⁻¹ he, apply_inv_apply' ρ g e⟩

@[expose] noncomputable def resD : Γ →* (D ≃ₗ[ZMod 2] D) :=
  MonoidHom.mk' (fun g => (ρ g).ofSubmodules D D (map_D ρ hD g)) fun g h => by
    ext d
    simp only [LinearEquiv.ofSubmodules_apply, LinearEquiv.mul_apply, map_mul]

theorem resD_apply (g : Γ) (d : D) : ((resD ρ hD g d : D) : V) = ρ g d := rfl

abbrev subE (Q : QuadraticForm (ZMod 2) V) (D : Submodule (ZMod 2) V) :
    Submodule (ZMod 2) (perp Q D) :=
  D.comap (perp Q D).subtype

abbrev QW (Q : QuadraticForm (ZMod 2) V) (D : Submodule (ZMod 2) V) : Type :=
  (perp Q D) ⧸ subE Q D

include hO hD in
theorem map_subE (g : Γ) :
    (subE Q D).map (((ρ g).ofSubmodules (perp Q D) (perp Q D) (map_E ρ hO hD g) :
      perp Q D ≃ₗ[ZMod 2] perp Q D) : perp Q D →ₗ[ZMod 2] perp Q D) = subE Q D := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨e, he, rfl⟩
    exact hD g e he
  · intro e he
    refine ⟨⟨ρ g⁻¹ e, apply_mem_perp ρ hO hD g⁻¹ e.2⟩, hD g⁻¹ e he, ?_⟩
    exact Subtype.ext (apply_inv_apply' ρ g e)

@[expose] noncomputable def resW : Γ →* (QW Q D ≃ₗ[ZMod 2] QW Q D) :=
  MonoidHom.mk' (fun g => Submodule.Quotient.equiv (subE Q D) (subE Q D)
      ((ρ g).ofSubmodules (perp Q D) (perp Q D) (map_E ρ hO hD g)) (map_subE ρ hO hD g))
    fun g h => by
      ext w
      obtain ⟨e, rfl⟩ := Submodule.Quotient.mk_surjective _ w
      simp only [LinearEquiv.mul_apply, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
        LinearEquiv.coe_coe, map_mul, LinearEquiv.ofSubmodules_apply]
      rfl

theorem resW_mk (g : Γ) (e : perp Q D) :
    resW ρ hO hD g (Submodule.Quotient.mk e) =
      Submodule.Quotient.mk ⟨ρ g e, apply_mem_perp ρ hO hD g e.2⟩ := rfl

theorem resD_eq_one_iff (g : Γ) : resD ρ hD g = 1 ↔ ∀ d ∈ D, ρ g d = d := by
  rw [LinearEquiv.ext_iff]
  constructor
  · intro h d hd
    have := h ⟨d, hd⟩
    exact congrArg Subtype.val this
  · intro h d
    exact Subtype.ext (h d d.2)

theorem resW_eq_one_iff (g : Γ) : resW ρ hO hD g = 1 ↔ ∀ e ∈ perp Q D, ρ g e - e ∈ D := by
  rw [LinearEquiv.ext_iff]
  constructor
  · intro h e he
    have := h (Submodule.Quotient.mk ⟨e, he⟩)
    rw [resW_mk, LinearEquiv.coe_one, id_eq, Submodule.Quotient.eq] at this
    exact this
  · intro h w
    obtain ⟨e, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [resW_mk, LinearEquiv.coe_one, id_eq, Submodule.Quotient.eq]
    exact h e e.2

theorem add_self_zmod2 (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

include hO in
theorem pow_four_eq_one {g : Γ} (h1 : ∀ d ∈ D, ρ g d = d)
    (h2 : ∀ e ∈ perp Q D, ρ g e - e ∈ D) : ρ (g * g * g * g) = 1 := by
  have ha : ∀ v, ρ g v - v ∈ perp Q D := by
    intro v
    rw [mem_perp]
    intro d hd
    have h3 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hO g) d v
    rw [h1 d hd] at h3
    rw [polar_sub_right, h3, sub_self]
  ext v
  simp only [map_mul, LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq]
  set a := ρ g v - v with ha_def
  set b := ρ g a - a with hb_def
  have hb : b ∈ D := h2 a (ha v)
  have hgb : ρ g b = b := h1 b hb
  have hv : ρ g v = v + a := by rw [ha_def]; abel
  have hga : ρ g a = a + b := by rw [hb_def]; abel
  have hbb : b + b = 0 := add_self_zmod2 b
  have haa : a + a = 0 := add_self_zmod2 a
  have h2v : ρ g (ρ g v) = v + b := by
    rw [hv, map_add, hga, hv]
    calc v + a + (a + b) = v + (a + a) + b := by abel
      _ = v + b := by rw [haa, add_zero]
  have h2b : ρ g (ρ g b) = b := by rw [hgb, hgb]
  have h4 : ρ g (ρ g (ρ g (ρ g v))) = ρ g (ρ g (v + b)) := by rw [h2v]
  rw [h4, map_add, map_add, h2v, h2b]
  calc v + b + b = v + (b + b) := by abel
    _ = v := by rw [hbb, add_zero]

end Hom

section Quad

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {D : Submodule (ZMod 2) V}

theorem le_perp (hDs : ∀ d ∈ D, Q d = 0) : D ≤ perp Q D := by
  intro d hd
  rw [mem_perp]
  intro d' hd'
  have h1 := hDs (d' + d) (D.add_mem hd' hd)
  simp only [polar, h1, hDs d hd, hDs d' hd', sub_zero]

theorem subE_le_radical (hDs : ∀ d ∈ D, Q d = 0) :
    subE Q D ≤ (Q.comp (perp Q D).subtype).radical := by
  intro x hx
  have hxD : (x : V) ∈ D := hx
  refine ⟨?_, ?_⟩
  · exact hDs x hxD
  · refine LinearMap.ext fun y => ?_
    simp only [polarBilin_apply_apply, LinearMap.zero_apply]
    have h2 := (mem_perp.mp y.2) x hxD
    simpa [polar, QuadraticMap.comp_apply, map_add] using h2

@[expose] noncomputable def Qbar (hDs : ∀ d ∈ D, Q d = 0) : QuadraticForm (ZMod 2) (QW Q D) :=
  (Q.comp (perp Q D).subtype).lift (subE Q D) (subE_le_radical hDs)

theorem Qbar_mk (hDs : ∀ d ∈ D, Q d = 0) (e : perp Q D) :
    Qbar hDs (Submodule.Quotient.mk e) = Q e :=
  rfl

theorem polar_Qbar_mk (hDs : ∀ d ∈ D, Q d = 0) (e u : perp Q D) :
    polar (Qbar hDs) (Submodule.Quotient.mk e) (Submodule.Quotient.mk u) = polar Q e u := by
  rw [polar, ← Submodule.Quotient.mk_add, Qbar_mk, Qbar_mk, Qbar_mk]
  rfl

theorem Qbar_nondegenerate (hQ : Q.polarBilin.Nondegenerate) (hDs : ∀ d ∈ D, Q d = 0) :
    (Qbar hDs).polarBilin.Nondegenerate := by
  rw [(QuadraticMap.isSymm_polarBilin (Qbar hDs)).isRefl.nondegenerate_iff_separatingLeft]
  intro w hw
  obtain ⟨e, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have h1 : ∀ u : perp Q D, polar Q e u = 0 := by
    intro u
    have := hw (Submodule.Quotient.mk u)
    rwa [polarBilin_apply_apply, polar_Qbar_mk] at this
  have h2 : (e : V) ∈ perp Q (perp Q D) := by
    rw [mem_perp]
    intro u hu
    rw [polar_comm]
    exact h1 ⟨u, hu⟩
  have h3 : perp Q (perp Q D) = D :=
    LinearMap.BilinForm.orthogonal_orthogonal hQ (QuadraticMap.isSymm_polarBilin Q).isRefl D
  rw [h3] at h2
  rw [Submodule.Quotient.mk_eq_zero]
  exact h2

theorem finrank_QW (hQ : Q.polarBilin.Nondegenerate) (hDs : ∀ d ∈ D, Q d = 0) :
    finrank (ZMod 2) (QW Q D) + 2 * finrank (ZMod 2) D = finrank (ZMod 2) V := by
  have h1 : finrank (ZMod 2) (QW Q D) + finrank (ZMod 2) (subE Q D) =
      finrank (ZMod 2) (perp Q D) := Submodule.finrank_quotient_add_finrank (subE Q D)
  have h2 : finrank (ZMod 2) (perp Q D) = finrank (ZMod 2) V - finrank (ZMod 2) D :=
    LinearMap.BilinForm.finrank_orthogonal hQ D
  have h3 : finrank (ZMod 2) (subE Q D) = finrank (ZMod 2) D :=
    (Submodule.comapSubtypeEquivOfLe (le_perp hDs)).finrank_eq
  have h4 : finrank (ZMod 2) D ≤ finrank (ZMod 2) (perp Q D) := Submodule.finrank_mono (le_perp hDs)
  omega

variable {Γ : Type*} [Group Γ] (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
  (hO : ∀ g, ρ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hD : ∀ g, ∀ d ∈ D, ρ g d ∈ D)

theorem resW_mem_orthogonalGroup (hDs : ∀ d ∈ D, Q d = 0) (g : Γ) :
    resW ρ hO hD g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qbar hDs) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro w
  obtain ⟨e, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [resW_mk, Qbar_mk, Qbar_mk]
  exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hO g) e

end Quad

section Card

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {D : Submodule (ZMod 2) V} {Γ : Type*} [Group Γ] [Finite Γ]
  (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
  (hO : ∀ g, ρ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hD : ∀ g, ∀ d ∈ D, ρ g d ∈ D)

include hO hD in
theorem card_dvd_two_pow_mul (hρ : Function.Injective ρ) (hDs : ∀ d ∈ D, Q d = 0) {x : V}
    (hx : x ∈ D) (hxfix : ∀ g, ρ g x = x) :
    ∃ j : ℕ, Nat.card Γ ∣ 2 ^ j *
      (Nat.card (MulAction.stabilizer (D ≃ₗ[ZMod 2] D) (⟨x, hx⟩ : D)) *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Qbar hDs))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K₁ : Subgroup Γ := (resD ρ hD).ker with hK₁
  set φ₂ : K₁ →* (QW Q D ≃ₗ[ZMod 2] QW Q D) := (resW ρ hO hD).comp K₁.subtype with hφ₂
  set K₂ : Subgroup K₁ := φ₂.ker with hK₂
  have hK₂p : IsPGroup 2 K₂ := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro k
    refine ⟨2, ?_⟩
    have hk1 : resD ρ hD (k : K₁) = 1 := k.1.2
    have hk2 : resW ρ hO hD ((k : K₁) : Γ) = 1 := k.2
    have h4 := pow_four_eq_one ρ hO ((resD_eq_one_iff ρ hD _).mp hk1)
      ((resW_eq_one_iff ρ hO hD _).mp hk2)
    have h5 : ((k : K₁) : Γ) * (k : K₁) * (k : K₁) * (k : K₁) = 1 := hρ (by rw [h4, map_one])
    apply Subtype.ext
    apply Subtype.ext
    simpa [pow_succ, mul_assoc, mul_assoc] using h5
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card.mp hK₂p)
  have c1 := Subgroup.card_ker_mul_card_range (resD ρ hD)
  have c2 := Subgroup.card_ker_mul_card_range φ₂
  have hr1 : Nat.card (resD ρ hD).range ∣ Nat.card (MulAction.stabilizer (D ≃ₗ[ZMod 2] D)
      (⟨x, hx⟩ : D)) := by
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨g, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    exact Subtype.ext (hxfix g)
  have hr2 : Nat.card φ₂.range ∣
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Qbar hDs)) := by
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨k, rfl⟩
    exact resW_mem_orthogonalGroup ρ hO hD hDs _
  refine ⟨j, ?_⟩
  have hK1card : Nat.card K₁ = 2 ^ j * Nat.card φ₂.range := by
    rw [← c2]
    exact by rw [hj]
  rw [← c1, hK1card]
  calc 2 ^ j * Nat.card φ₂.range * Nat.card (resD ρ hD).range
      ∣ 2 ^ j * (Nat.card (MulAction.stabilizer (D ≃ₗ[ZMod 2] D) (⟨x, hx⟩ : D)) *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Qbar hDs))) := by
        rw [mul_assoc]
        refine mul_dvd_mul_left _ ?_
        rw [mul_comm]
        exact mul_dvd_mul hr1 hr2

end Card

section LinGroup

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]

theorem card_stabilizer_mul {k : ℕ} (hk : finrank (ZMod 2) U = k) {x : U} (hx : x ≠ 0) :
    Nat.card (MulAction.stabilizer (U ≃ₗ[ZMod 2] U) x) * (2 ^ k - 1) =
      ∏ i : Fin k, (2 ^ k - 2 ^ (i : ℕ)) := by
  haveI : Finite U := Module.finite_of_finite (ZMod 2)
  have horb : (MulAction.orbit (U ≃ₗ[ZMod 2] U) x) = ({0} : Set U)ᶜ := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩ h0
      apply hx
      have : g x = 0 := h0
      exact g.injective (by rw [this, map_zero])
    · intro hy
      obtain ⟨g, hg⟩ := CFSG.LargeExtraspecial.S4.exists_linearEquiv_apply_eq_of_ne (F := ZMod 2)
        hx hy
      exact ⟨g, hg⟩
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (U ≃ₗ[ZMod 2] U) x)
  have hU : Nat.card U = 2 ^ k := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hk]
  rw [MulAction.index_stabilizer, horb,
    CFSG.GF2Type.Smith1980Orth.W4Sigma.card_linearEquiv_eq_prod hk, Set.ncard_compl,
    Set.ncard_singleton, hU] at h1
  exact h1

theorem card_stabilizer_two (hk : finrank (ZMod 2) U = 2) {x : U} (hx : x ≠ 0) :
    Nat.card (MulAction.stabilizer (U ≃ₗ[ZMod 2] U) x) = 2 := by
  have h := card_stabilizer_mul hk hx
  have e : ∏ i : Fin 2, (2 ^ 2 - 2 ^ (i : ℕ)) = 6 := by decide
  have e2 : (2 ^ 2 - 1 : ℕ) = 3 := by norm_num
  rw [e, e2] at h
  omega

theorem card_stabilizer_three (hk : finrank (ZMod 2) U = 3) {x : U} (hx : x ≠ 0) :
    Nat.card (MulAction.stabilizer (U ≃ₗ[ZMod 2] U) x) = 24 := by
  have h := card_stabilizer_mul hk hx
  have e : ∏ i : Fin 3, (2 ^ 3 - 2 ^ (i : ℕ)) = 168 := by decide
  have e2 : (2 ^ 3 - 1 : ℕ) = 7 := by norm_num
  rw [e, e2] at h
  omega

theorem card_stabilizer_four (hk : finrank (ZMod 2) U = 4) {x : U} (hx : x ≠ 0) :
    Nat.card (MulAction.stabilizer (U ≃ₗ[ZMod 2] U) x) = 1344 := by
  have h := card_stabilizer_mul hk hx
  have e : ∏ i : Fin 4, (2 ^ 4 - 2 ^ (i : ℕ)) = 20160 := by decide
  have e2 : (2 ^ 4 - 1 : ℕ) = 15 := by norm_num
  rw [e, e2] at h
  omega

end LinGroup

section Bounds

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {D : Submodule (ZMod 2) V}

theorem card_orth_dvd (hDs : ∀ d ∈ D, Q d = 0) {n : ℕ} (hW : finrank (ZMod 2) (QW Q D) = n) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Qbar hDs)) ∣
      ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  rw [← CFSG.GF2Type.Smith1980Orth.W4Sigma.card_linearEquiv_eq_prod hW]
  exact Subgroup.card_subgroup_dvd_card _

theorem card_orth_four (hQ : Q.polarBilin.Nondegenerate) (hDs : ∀ d ∈ D, Q d = 0)
    (hW : finrank (ZMod 2) (QW Q D) = 4) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Qbar hDs)) = 72 ∨
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Qbar hDs)) = 120 := by
  have hnd := Qbar_nondegenerate hQ hDs
  have hdim : finrank (ZMod 2) (QW Q D) = 2 * (1 + 1) := by rw [hW]
  by_cases hp : CFSG.GroupTheory.WeirSylow.IsPlusType (Qbar hDs)
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hnd hdim
      (ε := 1) (Or.inl ⟨rfl, hp⟩)
    left
    simp only [Nat.card_zmod, Nat.cast_ofNat, Finset.Icc_self, Finset.prod_singleton] at h
    have h' : ((Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Qbar hDs)) : ℕ) : ℤ) = 72 := by
      rw [h]
      norm_num
    exact_mod_cast h'
  · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hnd hdim
      (ε := -1) (Or.inr ⟨rfl, hp⟩)
    right
    simp only [Nat.card_zmod, Nat.cast_ofNat, Finset.Icc_self, Finset.prod_singleton] at h
    have h' : ((Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Qbar hDs)) : ℕ) : ℤ) = 120 := by
      rw [h]
      norm_num
    exact_mod_cast h'

theorem finrank_QW_eq (hQ : Q.polarBilin.Nondegenerate) (hDs : ∀ d ∈ D, Q d = 0) {n k m : ℕ}
    (hV : finrank (ZMod 2) V = n) (hk : finrank (ZMod 2) D = k) (hnk : n = 2 * k + m) :
    finrank (ZMod 2) (QW Q D) = m := by
  have := finrank_QW hQ hDs
  omega

end Bounds

theorem card_le_of_dvd {n j m N : ℕ} (hm : Odd m) (hmN : m ≤ N) (h1 : n ∣ 2 ^ j * m)
    (h2 : ¬ 2 ^ 10 ∣ n) : n ≤ 2 ^ 9 * N := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at h1
    exact (mul_ne_zero (pow_ne_zero _ two_ne_zero) hm.pos.ne') h1
  obtain ⟨a, c, hc, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hcm : c ∣ m := by
    have h3 : c ∣ 2 ^ j * m := (Dvd.intro_left _ rfl).trans h1
    exact (Nat.Coprime.pow_right j hc.coprime_two_right).dvd_of_dvd_mul_left h3
  have ha : a ≤ 9 := by
    by_contra h
    exact h2 (Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) c)
  calc 2 ^ a * c ≤ 2 ^ 9 * c := Nat.mul_le_mul_right c (Nat.pow_le_pow_right (by norm_num) ha)
    _ ≤ 2 ^ 9 * N := Nat.mul_le_mul_left _ ((Nat.le_of_dvd hm.pos hcm).trans hmN)

section Final

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {D : Submodule (ZMod 2) V} {Γ : Type*} [Group Γ] [Finite Γ]
  (ρ : Γ →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ)
  (hO : ∀ g, ρ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hD : ∀ g, ∀ d ∈ D, ρ g d ∈ D)
  (hQ : Q.polarBilin.Nondegenerate) (hDs : ∀ d ∈ D, Q d = 0) (hV : finrank (ZMod 2) V = 8)
  {x : V} (hx : x ∈ D) (hx0 : x ≠ 0) (hxfix : ∀ g, ρ g x = x)

include hρ hO hD hQ hDs hV hx hx0 hxfix in
theorem odd_bound_two (hk : finrank (ZMod 2) D = 2) :
    ∃ j m : ℕ, Odd m ∧ m ≤ 15 ∧ Nat.card Γ ∣ 2 ^ j * m := by
  obtain ⟨j, hj⟩ := card_dvd_two_pow_mul ρ hO hD hρ hDs hx hxfix
  have hx' : (⟨x, hx⟩ : D) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  rw [card_stabilizer_two hk hx'] at hj
  have hW : finrank (ZMod 2) (QW Q D) = 4 := finrank_QW_eq hQ hDs hV hk (by omega)
  rcases card_orth_four hQ hDs hW with h | h
  · rw [h] at hj
    refine ⟨j + 4, 9, by decide, by norm_num, ?_⟩
    have e : 2 ^ j * (2 * 72) = 2 ^ (j + 4) * 9 := by ring
    rwa [e] at hj
  · rw [h] at hj
    refine ⟨j + 4, 15, by decide, le_rfl, ?_⟩
    have e : 2 ^ j * (2 * 120) = 2 ^ (j + 4) * 15 := by ring
    rwa [e] at hj

include hρ hO hD hQ hDs hV hx hx0 hxfix in
theorem odd_bound_three (hk : finrank (ZMod 2) D = 3) :
    ∃ j m : ℕ, Odd m ∧ m ≤ 9 ∧ Nat.card Γ ∣ 2 ^ j * m := by
  obtain ⟨j, hj⟩ := card_dvd_two_pow_mul ρ hO hD hρ hDs hx hxfix
  have hx' : (⟨x, hx⟩ : D) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  rw [card_stabilizer_three hk hx'] at hj
  have hW : finrank (ZMod 2) (QW Q D) = 2 := finrank_QW_eq hQ hDs hV hk (by omega)
  have h6 : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Qbar hDs)) ∣ 6 := by
    have := card_orth_dvd hDs hW
    have e : ∏ i : Fin 2, (2 ^ 2 - 2 ^ (i : ℕ)) = 6 := by decide
    rwa [e] at this
  refine ⟨j + 4, 9, by decide, le_rfl, ?_⟩
  have h7 := hj.trans (mul_dvd_mul_left _ (mul_dvd_mul_left _ h6))
  have e : 2 ^ j * (24 * 6) = 2 ^ (j + 4) * 9 := by ring
  rwa [e] at h7

include hρ hO hD hQ hDs hV hx hx0 hxfix in
theorem odd_bound_four (hk : finrank (ZMod 2) D = 4) :
    ∃ j m : ℕ, Odd m ∧ m ≤ 21 ∧ Nat.card Γ ∣ 2 ^ j * m := by
  obtain ⟨j, hj⟩ := card_dvd_two_pow_mul ρ hO hD hρ hDs hx hxfix
  have hx' : (⟨x, hx⟩ : D) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  rw [card_stabilizer_four hk hx'] at hj
  have hW : finrank (ZMod 2) (QW Q D) = 0 := finrank_QW_eq hQ hDs hV hk (by omega)
  have h1 : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Qbar hDs)) ∣ 1 := by
    have := card_orth_dvd hDs hW
    simpa using this
  refine ⟨j + 6, 21, by decide, le_rfl, ?_⟩
  have h7 := hj.trans (mul_dvd_mul_left _ (mul_dvd_mul_left _ h1))
  have e : 2 ^ j * (1344 * 1) = 2 ^ (j + 6) * 21 := by ring
  rwa [e] at h7

end Final

section Kernel

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {D : Submodule (ZMod 2) V} {Γ : Type*} [Group Γ]
  (ρ : Γ →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ)
  (hO : ∀ g, ρ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hD : ∀ g, ∀ d ∈ D, ρ g d ∈ D)

include hO in
theorem sub_mem_perp_of_resD (g : Γ) (hg : resD ρ hD g = 1) (v : V) : ρ g v - v ∈ perp Q D := by
  rw [mem_perp]
  intro d hd
  have h1 := (resD_eq_one_iff ρ hD g).mp hg d hd
  have h3 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hO g) d v
  rw [h1] at h3
  rw [polar_sub_right, h3, sub_self]

include hρ hO in
theorem ker_resD_comm (hDeq : perp Q D = D) {g h : Γ} (hg : resD ρ hD g = 1)
    (hh : resD ρ hD h = 1) : g * h = h * g := by
  apply hρ
  ext v
  simp only [map_mul, LinearEquiv.mul_apply]
  have ha : ρ g v - v ∈ D := hDeq ▸ sub_mem_perp_of_resD ρ hO hD g hg v
  have hb : ρ h v - v ∈ D := hDeq ▸ sub_mem_perp_of_resD ρ hO hD h hh v
  have e1 : ρ g (ρ h v) = ρ g v + (ρ h v - v) := by
    have h5 := (resD_eq_one_iff ρ hD g).mp hg _ hb
    calc ρ g (ρ h v) = ρ g (v + (ρ h v - v)) := by rw [add_sub_cancel]
      _ = ρ g v + ρ g (ρ h v - v) := map_add _ _ _
      _ = ρ g v + (ρ h v - v) := by rw [h5]
  have e2 : ρ h (ρ g v) = ρ h v + (ρ g v - v) := by
    have h5 := (resD_eq_one_iff ρ hD h).mp hh _ ha
    calc ρ h (ρ g v) = ρ h (v + (ρ g v - v)) := by rw [add_sub_cancel]
      _ = ρ h v + ρ h (ρ g v - v) := map_add _ _ _
      _ = ρ h v + (ρ g v - v) := by rw [h5]
  rw [e1, e2]
  abel

include hρ hO in
theorem ker_resD_sq (hDeq : perp Q D = D) {g : Γ} (hg : resD ρ hD g = 1) : g * g = 1 := by
  apply hρ
  ext v
  simp only [map_mul, LinearEquiv.mul_apply, map_one, LinearEquiv.coe_one, id_eq]
  have ha : ρ g v - v ∈ D := hDeq ▸ sub_mem_perp_of_resD ρ hO hD g hg v
  have h5 := (resD_eq_one_iff ρ hD g).mp hg _ ha
  have e1 : ρ g (ρ g v) = ρ g v + (ρ g v - v) := by
    calc ρ g (ρ g v) = ρ g (v + (ρ g v - v)) := by rw [add_sub_cancel]
      _ = ρ g v + ρ g (ρ g v - v) := map_add _ _ _
      _ = ρ g v + (ρ g v - v) := by rw [h5]
  rw [e1]
  have h6 := add_self_zmod2 (ρ g v - v)
  calc ρ g v + (ρ g v - v) = v + ((ρ g v - v) + (ρ g v - v)) := by abel
    _ = v := by rw [h6, add_zero]

end Kernel

section Index

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {D : Submodule (ZMod 2) V} {Γ : Type*} [Group Γ] [Finite Γ]
  (ρ : Γ →* (V ≃ₗ[ZMod 2] V)) (hD : ∀ g, ∀ d ∈ D, ρ g d ∈ D)

include hD in
theorem card_le_ker_mul_four {x : V} (hx : x ∈ D) (hx0 : x ≠ 0) (hxfix : ∀ g, ρ g x = x)
    (hk : finrank (ZMod 2) D = 4) : Nat.card Γ ≤ Nat.card (resD ρ hD).ker * 1344 := by
  have c1 := Subgroup.card_ker_mul_card_range (resD ρ hD)
  have hx' : (⟨x, hx⟩ : D) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have hr1 : Nat.card (resD ρ hD).range ∣ Nat.card (MulAction.stabilizer (D ≃ₗ[ZMod 2] D)
      (⟨x, hx⟩ : D)) := by
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨g, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    exact Subtype.ext (hxfix g)
  rw [card_stabilizer_four hk hx'] at hr1
  have h2 := Nat.le_of_dvd (by norm_num) hr1
  rw [← c1]
  exact Nat.mul_le_mul_left _ h2

end Index

end Par

end CFSG.GF2Type.Smith1979.W4C1

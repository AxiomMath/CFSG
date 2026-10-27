module

public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.NormalFormAux
public import CFSG.HardMathSupport.Foote.ModuleExclusions.FieldCube.Generation
public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.Defs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner (monomGL)

variable {F : Type} [Field F]

noncomputable abbrev Dω (ω : Fˣ) : GL (Fin 3) F :=
  CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.diagGL F 1 ω (ω ^ 2)

noncomputable abbrev fS (σ : F ≃+* F) : MulAut (projectiveSL 3 F) := fieldAut 3 F σ

noncomputable abbrev cD (ω : Fˣ) : MulAut (projectiveSL 3 F) := conjAut 3 F (Dω ω)

noncomputable abbrev cX (lam : Fˣ) : MulAut (projectiveSL 3 F) := conjAut 3 F (monomGL F lam)

theorem heisCube_eq (σ : F ≃+* F) (lam ω : Fˣ) :
    heisCube σ lam ω =
      Subgroup.zpowers (fS σ) ⊔ (Subgroup.zpowers (cD ω) ⊔ Subgroup.zpowers (cX lam)) := rfl

theorem map_Dω {σ : F ≃+* F} {ω : Fˣ} (hω : σ (ω : F) = ω) :
    Matrix.GeneralLinearGroup.map σ.toRingHom (Dω ω) = Dω ω := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Dω, CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.diagGL, hω]

theorem map_monomGL {σ : F ≃+* F} {lam : Fˣ} (hl : σ (lam : F) = lam) :
    Matrix.GeneralLinearGroup.map σ.toRingHom (monomGL F lam) = monomGL F lam := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [monomGL, hl]

theorem commute_fS_cD {σ : F ≃+* F} {ω : Fˣ} (hω : σ (ω : F) = ω) :
    Commute (fS σ) (cD ω) := by
  change fieldAut 3 F σ * conjAut 3 F (Dω ω) = conjAut 3 F (Dω ω) * fieldAut 3 F σ
  rw [CFSG.HardMathSupport.Foote.ModuleExclusions.fieldAut_mul_conjAut, map_Dω hω]

theorem commute_fS_cX {σ : F ≃+* F} {lam : Fˣ} (hl : σ (lam : F) = lam) :
    Commute (fS σ) (cX lam) := by
  change fieldAut 3 F σ * conjAut 3 F (monomGL F lam) = conjAut 3 F (monomGL F lam) *
    fieldAut 3 F σ
  rw [CFSG.HardMathSupport.Foote.ModuleExclusions.fieldAut_mul_conjAut, map_monomGL hl]

theorem monomGL_mul_Dω {ω : Fˣ} (hω3 : ω ^ 3 = 1) (lam : Fˣ) :
    monomGL F lam * Dω ω =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (ω ^ 2) * (Dω ω * monomGL F lam) := by
  have h3 : (ω : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have h4 : (ω : F) ^ 4 = ω := by rw [pow_succ, h3, one_mul]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Dω, CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.diagGL, monomGL,
      Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal_pow] <;>
    ring_nf <;> simp [h3, h4]

theorem commute_cD_cX {ω : Fˣ} (hω3 : ω ^ 3 = 1) (lam : Fˣ) :
    Commute (cD ω) (cX lam) := by
  change conjAut 3 F (Dω ω) * conjAut 3 F (monomGL F lam) =
    conjAut 3 F (monomGL F lam) * conjAut 3 F (Dω ω)
  have h : conjAut 3 F (monomGL F lam * Dω ω) = conjAut 3 F (Dω ω * monomGL F lam) := by
    rw [monomGL_mul_Dω hω3, map_mul, conjAut_scalar, one_mul]
  rw [← map_mul, ← map_mul, h]

theorem fS_pow_three {σ : F ≃+* F} (hσ : σ ^ 3 = 1) : fS σ ^ 3 = 1 := by
  change fieldAut 3 F σ ^ 3 = 1
  rw [← map_pow, hσ, map_one]

theorem Dω_pow_three {ω : Fˣ} (hω3 : ω ^ 3 = 1) : Dω ω ^ 3 = 1 := by
  have h3 : (ω : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have h6 : (ω : F) ^ 6 = 1 := by rw [show 6 = 3 * 2 by rfl, pow_mul, h3, one_pow]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Dω, CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.diagGL,
      Matrix.diagonal_pow, Matrix.one_apply, ← pow_mul, h3, h6]

theorem cD_pow_three {ω : Fˣ} (hω3 : ω ^ 3 = 1) : cD (F := F) ω ^ 3 = 1 := by
  change conjAut 3 F (Dω ω) ^ 3 = 1
  rw [← map_pow, Dω_pow_three hω3, map_one]

theorem monomGL_pow_three (lam : Fˣ) :
    monomGL F lam ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) lam := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [monomGL, Matrix.GeneralLinearGroup.scalar, pow_succ, Matrix.mul_apply,
      Fin.sum_univ_three]

theorem cX_pow_three (lam : Fˣ) : cX (F := F) lam ^ 3 = 1 := by
  change conjAut 3 F (monomGL F lam) ^ 3 = 1
  rw [← map_pow, monomGL_pow_three, conjAut_scalar]

section Elements

variable {σ : F ≃+* F} {lam ω : Fˣ}

theorem le_centralizer_fS (hl : σ (lam : F) = lam) (hω : σ (ω : F) = ω) :
    Subgroup.zpowers (cD ω) ⊔ Subgroup.zpowers (cX lam) ≤
      Subgroup.centralizer ({fS σ} : Set (MulAut (projectiveSL 3 F))) := by
  refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_fS_cD hω).eq.symm
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_fS_cX hl).eq.symm

theorem mem_zpowers_cX_iff {c : MulAut (projectiveSL 3 F)} (hc : c ∈ Subgroup.zpowers (cX lam)) :
    ∃ k : ℕ, c = cX lam ^ k := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  have h3 : cX (F := F) lam ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat]; exact cX_pow_three lam
  refine ⟨(n % 3).toNat, ?_⟩
  rw [zpow_eq_zpow_emod n h3, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg n (by norm_num))]

theorem exists_of_mem_heisCube (hσ : σ ^ 3 = 1) (hω3 : ω ^ 3 = 1) (hl : σ (lam : F) = lam)
    (hω : σ (ω : F) = ω) {b : MulAut (projectiveSL 3 F)} (hb : b ∈ heisCube σ lam ω) :
    ∃ i j k : ℕ, b = fS σ ^ i * cD ω ^ j * cX lam ^ k := by
  rw [heisCube_eq] at hb
  have hA : ∀ a ∈ Subgroup.zpowers (cD ω) ⊔ Subgroup.zpowers (cX lam), Commute a (fS σ) :=
    fun a ha => Subgroup.mem_centralizer_singleton_iff.1 (le_centralizer_fS hl hω ha)
  obtain ⟨i, a, ha, rfl⟩ := exists_pow_mul_of_mem_sup (fS_pow_three hσ) hA b hb
  have hB : ∀ c ∈ Subgroup.zpowers (cX lam), Commute c (cD ω) := by
    intro c hc
    obtain ⟨k, rfl⟩ := mem_zpowers_cX_iff hc
    exact ((commute_cD_cX hω3 lam).pow_right k).symm
  obtain ⟨j, c, hc, rfl⟩ := exists_pow_mul_of_mem_sup (cD_pow_three hω3) hB a ha
  obtain ⟨k, rfl⟩ := mem_zpowers_cX_iff hc
  exact ⟨i, j, k, by rw [mul_assoc]⟩

end Elements

section Orbits

variable {σ : F ≃+* F} {lam ω : Fˣ}

theorem pow_smul_eq_self {G α : Type*} [Group G] [MulAction G α] {g : G} {x : α}
    (h : g • x = x) (n : ℕ) : g ^ n • x = x := by
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ n ih => rw [pow_succ, mul_smul, h, ih]

theorem ncard_orbit_le_three {G α : Type*} [Group G] [MulAction G α] (B : Subgroup G) (x : α)
    (c : G) (hc : c ^ 3 = 1) (h : ∀ b ∈ B, ∃ m : ℕ, b • x = c ^ m • x) :
    (MulAction.orbit B x).ncard ≤ 3 := by
  classical
  have hsub : MulAction.orbit B x ⊆ (fun k : Fin 3 => c ^ (k : ℕ) • x) '' Set.univ := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨m, hm⟩ := h b b.2
    refine ⟨⟨m % 3, Nat.mod_lt _ (by norm_num)⟩, Set.mem_univ _, ?_⟩
    have : c ^ (m % 3) = c ^ m := by
      conv_rhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hc, one_pow, one_mul]
    simp only [this]
    exact hm.symm
  refine (Set.ncard_le_ncard hsub (Set.Finite.image _ (Set.toFinite _))).trans ?_
  exact (Set.ncard_image_le (Set.toFinite _)).trans (by simp)

theorem fS_ne_one (hσ : orderOf σ = 3) : fS σ ≠ 1 := by
  intro h
  have hσ1 : σ ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hσ; norm_num at hσ
  obtain ⟨c, hc⟩ : ∃ c : F, σ c ≠ c := by
    by_contra hall
    push_neg at hall
    exact hσ1 (RingEquiv.ext hall)
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have := congrArg (fun φ : MulAut (projectiveSL 3 F) =>
    φ (CFSG.HardMathSupport.Foote.ModuleExclusions.tbar h01 c)) h
  simp only [MulAut.one_apply] at this
  change fieldAut 3 F σ (CFSG.HardMathSupport.Foote.ModuleExclusions.tbar h01 c) = _ at this
  rw [CFSG.HardMathSupport.Foote.ModuleExclusions.fieldAut_tbar] at this
  exact hc (CFSG.HardMathSupport.Foote.ModuleExclusions.tbar_injective h01 this)

variable [Finite F]

theorem card_heisCube (hσ : orderOf σ = 3) (hω3 : ω ^ 3 = 1) (hl : σ (lam : F) = lam)
    (hω : σ (ω : F) = ω) : ∃ s : ℕ, 1 ≤ s ∧ Nat.card (heisCube σ lam ω) = 3 ^ s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ3 : σ ^ 3 = 1 := hσ ▸ pow_orderOf_eq_one σ
  have : Finite (MulAut (projectiveSL 3 F)) := MulEquiv.finite_left
  have hp : IsPGroup 3 (heisCube σ lam ω) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨i, j, k, hg⟩ := exists_of_mem_heisCube hσ3 hω3 hl hω g.2
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, hg, Subgroup.coe_one]
    have h1 : Commute (fS σ ^ i) (cD ω ^ j) := ((commute_fS_cD hω).pow_left i).pow_right j
    have h2 : Commute (fS σ ^ i * cD ω ^ j) (cX lam ^ k) :=
      (((commute_fS_cX hl).pow_left i).pow_right k).mul_left
        (((commute_cD_cX hω3 lam).pow_left j).pow_right k)
    rw [h2.mul_pow, h1.mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j,
      mul_comm k, pow_mul, pow_mul, pow_mul, fS_pow_three hσ3, cD_pow_three hω3, cX_pow_three,
      one_pow, one_pow, one_pow, mul_one, mul_one]
  obtain ⟨s, hs⟩ := hp.exists_card_eq
  refine ⟨s, ?_, hs⟩
  rcases Nat.eq_zero_or_pos s with h0 | h0
  · exfalso
    rw [h0, pow_zero] at hs
    have hmem : fS σ ∈ heisCube σ lam ω :=
      (le_sup_left : Subgroup.zpowers (fS σ) ≤ _) (Subgroup.mem_zpowers _)
    have hsub := (Subgroup.card_eq_one).1 hs
    have : fS σ ∈ (⊥ : Subgroup (MulAut (projectiveSL 3 F))) := hsub ▸ hmem
    exact fS_ne_one hσ ((Subgroup.mem_bot).1 this)
  · exact h0

end Orbits

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis

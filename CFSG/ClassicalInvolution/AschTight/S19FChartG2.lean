module

public import CFSG.ClassicalInvolution.AschTight.S19FSL2
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2TorusGen
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2NC

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Generic Matrix
open scoped MatrixGroups

section Stable

variable {F : Type} [Field F] [Finite F] {r : ℕ} (hF : Nat.card F = r ^ 2) {δ : F ≃+* F}
  (hδ : ∀ c, δ c = c ^ r)

include hF hδ

theorem exists_fixed_quaternion_of_stable (hodd : Odd (Nat.card F)) {C : Type} [Group C]
    (β : MulAut C) (hβ2 : ∀ x, β (β x) = x) (Φ : SL2 F →* C) (hΦ : Function.Injective Φ)
    (hβΦ : ∀ A, β (Φ A) = Φ (SpecialLinearGroup.map δ.toRingHom A))
    (hlin : ∀ c : C, c * Φ (-1) = Φ (-1) * c → LinAct Φ c) (g : C)
    (hβR : (conjSub g Φ.range).map β.toMonoidHom = conjSub g Φ.range) :
    ∃ P : Subgroup C, IsPGroup 2 P ∧ P ≤ conjSub g Φ.range ∧ (∀ x ∈ P, β x = x) ∧
      ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
  have hrange : Φ.range.map β.toMonoidHom = Φ.range := by
    ext x
    constructor
    · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
      exact ⟨_, (hβΦ A).symm⟩
    · rintro ⟨A, rfl⟩
      refine ⟨Φ (SpecialLinearGroup.map δ.symm.toRingHom A), ⟨_, rfl⟩, ?_⟩
      change β (Φ _) = Φ A
      rw [hβΦ]
      congr 1
      apply Subtype.ext
      ext i j
      simp
  have h1 : (conjSub g Φ.range).map β.toMonoidHom = conjSub (β g) Φ.range := by
    have e : β.toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (β g)).toMonoidHom.comp β.toMonoidHom := by
      ext x
      simp [MulAut.conj_apply]
    rw [conjSub, Subgroup.map_map, e, ← Subgroup.map_map, hrange]
    rfl
  rw [h1] at hβR
  have hc : conjSub (g⁻¹ * β g) Φ.range = Φ.range := by
    rw [conjSub_mul, hβR, conjSub_inv_conjSub]
  have hcz := (isUniqueInvolution_range_sl2 hodd hΦ).conj_eq hc
  have hcomm : (g⁻¹ * β g) * Φ (-1) = Φ (-1) * (g⁻¹ * β g) := by
    calc (g⁻¹ * β g) * Φ (-1) = (g⁻¹ * β g) * Φ (-1) * (g⁻¹ * β g)⁻¹ * (g⁻¹ * β g) := by group
      _ = Φ (-1) * (g⁻¹ * β g) := by rw [hcz]
  exact exists_fixed_quaternion_of_chart hF hδ hodd β hβ2 Φ hΦ hβΦ g (hlin _ hcomm)

end Stable

section Chart

theorem units_map_entrywiseHom_invol {τ : Tag} {K : Type} [Field K] {σ : K →+* K}
    (hσ : σ.comp σ = RingHom.id K) (g : ModGL τ K) :
    Units.map (entrywiseHom σ) (Units.map (entrywiseHom σ) g) = g := by
  ext1
  simp only [Units.coe_map]
  exact (entrywise_entrywise σ σ _).trans (by rw [hσ, entrywise_id])


@[expose] noncomputable def g2Chart (K : Type) [Field K] (i : Fin Tag.G2.rank) :
    SL2 K →* ↥(adjointGroup .G2 K) :=
  (simpleRootSL2 .G2 K i).codRestrict (adjointGroup .G2 K) (simpleRootSL2_mem_adjointGroup i)

variable {K : Type} [Field K]

theorem coe_g2Chart (i : Fin Tag.G2.rank) (A : SL2 K) :
    ((g2Chart K i A : adjointGroup .G2 K) : ModGL .G2 K) = simpleRootSL2 .G2 K i A :=
  rfl

theorem g2Chart_injective (hK : ringChar K ≠ 2) (i : Fin Tag.G2.rank) :
    Function.Injective (g2Chart K i) := fun _ _ h =>
  simpleRootSL2_injective hK i (congrArg Subtype.val h)

theorem rankOne_g2_eq_range (i : Fin Tag.G2.rank) :
    CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Steinberg.Adjoint.g2Datum K).rootGroup i =
      (g2Chart K i).range := by
  open CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.Steinberg.Adjoint in
  obtain ⟨φ, -, hup, hlow⟩ := Adjoint.g2_exists_sl2_hom (K := K) i
  have hφ : φ = g2Chart K i := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K)) ?_
    rintro M (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · refine Subtype.ext ?_
      change ((φ (CFSG.LieType.Steinberg.sl2Upper c) : adjointGroup .G2 K) : ModGL .G2 K) =
        simpleRootSL2 .G2 K i (uSL c)
      rw [hup, RootOperatorFamily.coe_eltElement,
        RootOperatorFamily.eltUnit_simple, simpleRootSL2_uSL]
    · refine Subtype.ext ?_
      change ((φ (CFSG.LieType.Steinberg.sl2Lower c) : adjointGroup .G2 K) : ModGL .G2 K) =
        simpleRootSL2 .G2 K i (vSL c)
      rw [hlow, RootOperatorFamily.coe_eltElement,
        RootOperatorFamily.eltUnit_neg_simple, simpleRootSL2_vSL]
  have hup' : ∀ c, φ (CFSG.LieType.Steinberg.sl2Upper c) =
      Adjoint.xPar (rootOperatorFamily .G2) (Pi.single i 1) c := fun c => by
    rw [hup, Adjoint.xPar_simple]
  have hlow' : ∀ c, φ (CFSG.LieType.Steinberg.sl2Lower c) =
      Adjoint.xPar (rootOperatorFamily .G2) (-Pi.single i 1) c := fun c => by
    rw [hlow, Adjoint.xPar_neg_simple]
  have hle : rankOne (Adjoint.rootGroup (rootOperatorFamily .G2) K) i ≤ φ.range := by
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨c, rfl⟩ :=
        Adjoint.exists_of_mem_rootGroup_simple (rootOperatorFamily .G2) hg
      exact ⟨_, hup c⟩
    · intro g hg
      obtain ⟨c, rfl⟩ :=
        Adjoint.exists_of_mem_rootGroup_neg_simple (rootOperatorFamily .G2) hg
      exact ⟨_, hlow c⟩
  rw [← hφ]
  exact ModelFacts.rankOne_eq_range_of_sl2 (D := Adjoint.g2Datum K) (i := i) φ
    (fun c => by rw [hup']; exact Adjoint.xPar_mem (isRoot_single .G2 i) c)
    (fun c => by rw [hlow']; exact Adjoint.xPar_mem (isRoot_neg_single .G2 i) c) hle

theorem simpleRootSL2_entrywise (σ : K →+* K) (i : Fin Tag.G2.rank) (A : SL2 K) :
    Units.map (entrywiseHom σ) (simpleRootSL2 .G2 K i A) =
      simpleRootSL2 .G2 K i (SpecialLinearGroup.map σ A) := by
  have hu : ∀ c, SpecialLinearGroup.map σ (uSL c) = uSL (σ c) := fun c => Subtype.ext (by
    rw [SpecialLinearGroup.map_apply_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uSL])
  have hv : ∀ c, SpecialLinearGroup.map σ (vSL c) = vSL (σ c) := fun c => Subtype.ext (by
    rw [SpecialLinearGroup.map_apply_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vSL])
  have h : (Units.map (entrywiseHom σ)).comp (simpleRootSL2 .G2 K i) =
      (simpleRootSL2 .G2 K i).comp (SpecialLinearGroup.map σ) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K)) ?_
    rintro M (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change Units.map (entrywiseHom σ) (simpleRootSL2 .G2 K i (uSL c)) =
        simpleRootSL2 .G2 K i (SpecialLinearGroup.map σ (uSL c))
      rw [simpleRootSL2_uSL, units_map_entrywiseHom_xUnit, hu, simpleRootSL2_uSL]
    · change Units.map (entrywiseHom σ) (simpleRootSL2 .G2 K i (vSL c)) =
        simpleRootSL2 .G2 K i (SpecialLinearGroup.map σ (vSL c))
      rw [simpleRootSL2_vSL, units_map_entrywiseHom_yUnit, hv, simpleRootSL2_vSL]
  exact DFunLike.congr_fun h A

theorem linAct_g2Chart [Finite K] (hK : Odd (Nat.card K)) (i : Fin Tag.G2.rank)
    {c : adjointGroup .G2 K} (hc : c * g2Chart K i (-1) = g2Chart K i (-1) * c) :
    LinAct (g2Chart K i) c := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd hK
  have hneg1 : (-1 : Kˣ) ≠ 1 := fun h => h2 (by
    have h' := congrArg Units.val h
    rw [Units.val_neg, Units.val_one] at h'
    linear_combination -h')
  set a : Fin Tag.G2.rank → Kˣ := fun j => if j = i then 1 else -1 with ha_def
  have ha : ∀ j, a j = 1 ∨ a j = -1 := fun j => by
    by_cases h : j = i
    · exact Or.inl (by simp [a, h])
    · exact Or.inr (by simp [a, h])
  have hne : a ≠ 1 := by
    intro h
    obtain ⟨j, hj⟩ : ∃ j : Fin Tag.G2.rank, j ≠ i := by
      fin_cases i
      exacts [⟨⟨1, by decide⟩, by decide⟩, ⟨⟨0, by decide⟩, by decide⟩]
    have := congrFun h j
    simp only [a, hj, ite_false, Pi.one_apply] at this
    exact hneg1 this
  have hγ : (Pi.single i 1 : Fin Tag.G2.rank → ℤ) ∈ rootCharKernel a :=
    ⟨isRoot_single _ i, by rw [rootChar_single_g2]; simp [a]⟩
  have hw : (1 : WeylGroup Tag.G2) • (Pi.single i 1 : Fin Tag.G2.rank → ℤ) = Pi.single i 1 :=
    one_smul _ _
  have hle := toralCentralizer_le_linActSubgroup hK ha hne hγ hw
  have hneg := rootChart_neg_one hK ha hne hγ hw
  rw [rootChart_one] at hle hneg
  have hmem : (c : ModGL .G2 K) ∈ toralCentralizer Tag.G2 K a := by
    rw [mem_toralCentralizer]
    refine ⟨c.2, ?_⟩
    have h := congrArg Subtype.val hc
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_g2Chart, hneg] at h
    rw [← h]
    group
  obtain ⟨D, hD⟩ := hle hmem
  refine ⟨D, fun A => Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_g2Chart, coe_g2Chart]
  exact hD A

theorem exists_eq_conjSub_g2Chart {R : Subgroup ↥(adjointGroup .G2 K)}
    (hR : R ∈ fundamentalSubgroups .G2 (CFSG.LieType.Steinberg.Adjoint.g2Datum K)) :
    ∃ (i : Fin Tag.G2.rank) (g : adjointGroup .G2 K), R = conjSub g (g2Chart K i).range := by
  open CFSG.LieType.Steinberg.Adjoint in
  obtain ⟨g, γ, hγ, rfl⟩ := hR
  have hct := g2_isCTGroupDatum K
  have hroot : IsRoot .G2 γ := by
    have h : γ ∈ (g2Datum K).roots := by
      rcases hγ with h | ⟨-, h⟩ | ⟨h', -⟩
      · exact h.1
      · exact h
      · exact absurd h' (by decide)
    exact mem_adjDatum_roots.mp h
  obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 hroot
  obtain ⟨h, hh⟩ := ModelFacts.exists_map_conj_rankOne hct w
  have hb : (Pi.single j 1 : Fin (Tag.rank .G2) → ℤ) ∈ (g2Datum K).roots :=
    mem_adjDatum_roots.mpr (isRoot_single .G2 j)
  have h2 : (g2Datum K).rootGroup (w • Pi.single j 1) ⊔
      (g2Datum K).rootGroup (-(w • Pi.single j 1)) =
      (CFSG.LieType.CurtisTits.rankOne (g2Datum K).rootGroup j).map
        (MulAut.conj h).toMonoidHom := (hh _ hb).symm
  refine ⟨j, g * h, ?_⟩
  subst hw
  rw [h2, conjSub_mul, rankOne_g2_eq_range]
  rfl

theorem fieldInvolution_fixes_nonabelian_g2 [Finite K] {r : ℕ} (hK : Nat.card K = r ^ 2)
    (hodd : Odd (Nat.card K)) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ r)
    (β : MulAut ↥(adjointGroup .G2 K))
    (hβ : ∀ u, (β u : ModGL .G2 K) = Units.map (entrywiseHom δ.toRingHom) (u : ModGL .G2 K))
    {R : Subgroup ↥(adjointGroup .G2 K)}
    (hR : R ∈ fundamentalSubgroups .G2 (CFSG.LieType.Steinberg.Adjoint.g2Datum K))
    (hβR : R.map β.toMonoidHom = R) :
    ∃ P : Subgroup ↥(adjointGroup .G2 K), IsPGroup 2 P ∧ P ≤ R ∧ (∀ x ∈ P, β x = x) ∧
      ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
  obtain ⟨i, g, rfl⟩ := exists_eq_conjSub_g2Chart hR
  have hK2 : ringChar K ≠ 2 := fun hc => two_ne_zero_of_odd hodd (by
    have h := ringChar.Nat.cast_ringChar (R := K)
    rw [hc] at h
    exact_mod_cast h)
  have hδδ := frob_frob hK hδ
  have hδid : δ.toRingHom.comp δ.toRingHom = RingHom.id K := RingHom.ext fun c => hδδ c
  have hβ2 : ∀ x, β (β x) = x := fun x => Subtype.ext (by
    rw [hβ, hβ, units_map_entrywiseHom_invol hδid])
  have hβΦ : ∀ A, β (g2Chart K i A) = g2Chart K i (SpecialLinearGroup.map δ.toRingHom A) :=
    fun A => Subtype.ext (by rw [hβ, coe_g2Chart, coe_g2Chart, simpleRootSL2_entrywise])
  exact exists_fixed_quaternion_of_stable hK hδ hodd β hβ2 (g2Chart K i) (g2Chart_injective hK2 i)
    hβΦ (fun c hc => linAct_g2Chart hodd i hc) g hβR

end Chart

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19F

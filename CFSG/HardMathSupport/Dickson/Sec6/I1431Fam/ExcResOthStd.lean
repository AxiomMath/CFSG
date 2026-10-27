module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOthSL2
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.NormGroup
public import CFSG.RankThree.Chevalley.SteinbergBID4TrialityConjugacy
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryBasic
public import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLang
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Open.StatedAPI CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)

open Matrix
open CFSG.ClassicalInvolution.ModelFacts.Levi (rootSL2_WSL_mem_monomialSubgroup mapsRootLines_rootSL2_WSL)

open scoped commutatorElement

set_option linter.unusedSectionVars false

section Rk1

variable {τ : Tag} {L : Type} [Field L]

theorem excOth_orth_pp {p q : Fin τ.rank} (hc : τ.cartan p q = 0) :
    (Pi.single p 1 : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (Pi.single q 1 : Fin τ.rank → ℤ))
      = 0 := by
  rw [dotProduct_mulVec_eq_iform]
  exact ssTw_iform_single_of_cartan_zero hc

theorem excOth_commute_gen (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p q : Fin τ.rank}
    (hc : τ.cartan p q = 0) (s t : L) :
    Commute (xUnit τ L p s) (xUnit τ L q t) ∧ Commute (xUnit τ L p s) (yUnit τ L q t) ∧
      Commute (yUnit τ L p s) (xUnit τ L q t) ∧ Commute (yUnit τ L p s) (yUnit τ L q t) := by
  have H := (simply_laced_orthogonal_root_commutation τ hτ).2 L
  have hp := isRoot_single τ p
  have hq := isRoot_single τ q
  have o1 := excOth_orth_pp (τ := τ) hc
  refine ⟨H _ _ hp hq o1 _ (xUnit_mem_rootSubgroup p s) _ (xUnit_mem_rootSubgroup q t),
    H _ _ hp (IsRoot.neg hq) (by rw [mulVec_neg, dotProduct_neg, o1, neg_zero]) _
      (xUnit_mem_rootSubgroup p s) _ (yUnit_mem_rootSubgroup q t),
    H _ _ (IsRoot.neg hp) hq (by rw [neg_dotProduct, o1, neg_zero]) _
      (yUnit_mem_rootSubgroup p s) _ (xUnit_mem_rootSubgroup q t),
    H _ _ (IsRoot.neg hp) (IsRoot.neg hq)
      (by rw [mulVec_neg, dotProduct_neg, neg_dotProduct, o1, neg_zero, neg_zero]) _
      (yUnit_mem_rootSubgroup p s) _ (yUnit_mem_rootSubgroup q t)⟩

theorem excOth_commute_simple (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p q : Fin τ.rank}
    (hc : τ.cartan p q = 0) (A B : SL2 L) :
    Commute (simpleRootSL2 τ L p A) (simpleRootSL2 τ L q B) := by
  have hgen := fun s t => excOth_commute_gen hτ hc (L := L) s t
  have h1 : ∀ Y, (∃ t, Y = xUnit τ L q t) ∨ (∃ t, Y = yUnit τ L q t) →
      ∀ A : SL2 L, Commute (simpleRootSL2 τ L p A) Y := by
    intro Y hY A
    have hA : A ∈ Subgroup.closure ({g : SL2 L | ∃ t : L, g = uSL t} ∪
        {g : SL2 L | ∃ t : L, g = vSL t}) := by rw [excOth_SL2_closure]; trivial
    induction hA using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with ⟨s, rfl⟩ | ⟨s, rfl⟩
      · rw [simpleRootSL2_uSL]
        rcases hY with ⟨t, rfl⟩ | ⟨t, rfl⟩
        · exact (hgen s t).1
        · exact (hgen s t).2.1
      · rw [simpleRootSL2_vSL]
        rcases hY with ⟨t, rfl⟩ | ⟨t, rfl⟩
        · exact (hgen s t).2.2.1
        · exact (hgen s t).2.2.2
    | one => rw [map_one]; exact Commute.one_left _
    | mul a b _ _ ha hb => rw [map_mul]; exact ha.mul_left hb
    | inv a _ ha => rw [map_inv]; exact ha.inv_left
  have hB : B ∈ Subgroup.closure ({g : SL2 L | ∃ t : L, g = uSL t} ∪
      {g : SL2 L | ∃ t : L, g = vSL t}) := by rw [excOth_SL2_closure]; trivial
  induction hB using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rw [simpleRootSL2_uSL]; exact h1 _ (Or.inl ⟨t, rfl⟩) A
    · rw [simpleRootSL2_vSL]; exact h1 _ (Or.inr ⟨t, rfl⟩) A
  | one => rw [map_one]; exact Commute.one_right _
  | mul a b _ _ ha hb => rw [map_mul]; exact ha.mul_right hb
  | inv a _ ha => rw [map_inv]; exact ha.inv_right

theorem excOth_conj_simple {a b : Fin τ.rank} {n : ModGL τ L}
    (hx : ∀ c, n * xUnit τ L a c * n⁻¹ = xUnit τ L b c)
    (hy : ∀ c, n * yUnit τ L a c * n⁻¹ = yUnit τ L b c) (A : SL2 L) :
    n * simpleRootSL2 τ L a A * n⁻¹ = simpleRootSL2 τ L b A := by
  have h : (MulAut.conj n).toMonoidHom.comp (simpleRootSL2 τ L a) = simpleRootSL2 τ L b := by
    apply excOth_SL2_hom_ext
    · intro t
      simp [simpleRootSL2_uSL, hx]
    · intro t
      simp [simpleRootSL2_vSL, hy]
  simpa using DFunLike.congr_fun h A

theorem excOth_entrywise_simple (σ : L →+* L) (i : Fin τ.rank) (A : SL2 L) :
    Units.map (entrywiseHom σ) (simpleRootSL2 τ L i A) =
      simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map σ A) := by
  rw [← rootSL2_single_apply, ← rootSL2_single_apply]
  exact entrywise_rootSL2_of_field σ _ A

theorem excOth_simple_injective (i : Fin τ.rank) : Function.Injective (simpleRootSL2 τ L i) := by
  intro A B h
  rw [← rootSL2_single_apply, ← rootSL2_single_apply] at h
  exact rootSL2_injective_of_field _ h

theorem excOth_simple_mem_sub {J : Set (Fin τ.rank)} {i : Fin τ.rank} (hi : i ∈ J) (A : SL2 L) :
    simpleRootSL2 τ L i A ∈ subsystemGroup τ L J := by
  have hA : A ∈ Subgroup.closure ({g : SL2 L | ∃ t : L, g = uSL t} ∪
      {g : SL2 L | ∃ t : L, g = vSL t}) := by rw [excOth_SL2_closure]; trivial
  induction hA using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rw [simpleRootSL2_uSL]; exact xUnit_mem_subsystemGroup hi t
    · rw [simpleRootSL2_vSL]; exact yUnit_mem_subsystemGroup hi t
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

section Std

variable [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem excOth_frob_sq (f : ℕ) (x : frobeniusFixedField L ℓ (2 * f)) :
    iterateFrobenius L ℓ f (iterateFrobenius L ℓ f (x : L)) = x := by
  have h := mem_frobeniusFixedField.1 x.2
  simp only [iterateFrobenius_def]
  rw [← pow_mul, ← pow_add, ← two_mul]
  exact h

theorem excOth_not_commute_xy (d : Fin τ.rank) :
    ¬ Commute (xUnit τ L d 1) (yUnit τ L d 1) := by
  intro h
  rw [← simpleRootSL2_uSL, ← simpleRootSL2_vSL] at h
  have h1 : uSL (1 : L) * vSL 1 = vSL 1 * uSL 1 := by
    apply excOth_simple_injective d
    rw [map_mul, map_mul]
    exact h.eq
  have h2 := congrArg (fun M : SL2 L => (M : Matrix (Fin 2) (Fin 2) L) 0 0) h1
  simp [coe_uSL, coe_vSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two] at h2

theorem excOth_noL2_std_swap (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hf : 1 ≤ f)
    {J : Set (Fin τ.rank)} {a b d : Fin τ.rank} (ha : a ∈ J) (hb : b ∈ J) (hd : d ∈ J)
    (hcab : τ.cartan a b = 0) (hcad : τ.cartan a d = 0) (hcbd : τ.cartan b d = 0)
    {n₁ : ModGL τ L}
    (hxa : ∀ c, n₁ * xUnit τ L a c * n₁⁻¹ = xUnit τ L b c)
    (hya : ∀ c, n₁ * yUnit τ L a c * n₁⁻¹ = yUnit τ L b c)
    (hxb : ∀ c, n₁ * xUnit τ L b c * n₁⁻¹ = xUnit τ L a c)
    (hyb : ∀ c, n₁ * yUnit τ L b c * n₁⁻¹ = yUnit τ L a c)
    (hxd : ∀ c, n₁ * xUnit τ L d c * n₁⁻¹ = xUnit τ L d c)
    (hyd : ∀ c, n₁ * yUnit τ L d c * n₁⁻¹ = yUnit τ L d c) :
    ExcOthNoL2 (subsystemGroup τ L J ⊓
      twistedFixedPoints n₁ (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  classical
  intro F _
  refine ⟨fun φ => ?_⟩
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFr
  set P : Subgroup (ModGL τ L) := subsystemGroup τ L J ⊓
      twistedFixedPoints n₁ (Units.map (entrywiseHom Fr)) with hP
  let K : Subfield L := frobeniusFixedField L ℓ (2 * f)
  have hK2 : ∀ x : K, Fr (Fr (x : L)) = x := excOth_frob_sq f
  let ρa : SL2 K →* ModGL τ L :=
    (simpleRootSL2 τ L a).comp (Matrix.SpecialLinearGroup.map K.subtype)
  let ρb : SL2 K →* ModGL τ L :=
    (simpleRootSL2 τ L b).comp ((Matrix.SpecialLinearGroup.map Fr).comp
      (Matrix.SpecialLinearGroup.map K.subtype))
  have hcomm : ∀ A B, Commute (ρa A) (ρb B) := fun A B => excOth_commute_simple hτ hcab _ _
  let ρ : SL2 K →* ModGL τ L :=
    (MonoidHom.noncommCoprod ρa ρb hcomm).comp (MonoidHom.prod (MonoidHom.id _) (MonoidHom.id _))
  have hρ : ∀ A, ρ A = ρa A * ρb A := fun A => by simp [ρ]
  have hsq : ∀ A : SL2 K, Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr
      (Matrix.SpecialLinearGroup.map K.subtype A)) = Matrix.SpecialLinearGroup.map K.subtype A := by
    intro A
    ext i j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact hK2 (A i j)
  have hfix : ∀ A, n₁ * Units.map (entrywiseHom Fr) (ρ A) * n₁⁻¹ = ρ A := by
    intro A
    have e1 : ρa A = simpleRootSL2 τ L a (Matrix.SpecialLinearGroup.map K.subtype A) := rfl
    have e2 : ρb A = simpleRootSL2 τ L b (Matrix.SpecialLinearGroup.map Fr
      (Matrix.SpecialLinearGroup.map K.subtype A)) := rfl
    have e : ∀ X Y : ModGL τ L, n₁ * (X * Y) * n₁⁻¹ = (n₁ * X * n₁⁻¹) * (n₁ * Y * n₁⁻¹) :=
      fun X Y => by group
    rw [hρ, map_mul, e1, e2, excOth_entrywise_simple, excOth_entrywise_simple, hsq, e,
      excOth_conj_simple hxa hya, excOth_conj_simple hxb hyb]
    exact (excOth_commute_simple hτ hcab _ _).symm.eq
  have hρP : ∀ A, ρ A ∈ P := fun A => by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [hρ]
      exact mul_mem (excOth_simple_mem_sub ha _) (excOth_simple_mem_sub hb _)
    · rw [mem_twistedFixedPoints]
      exact hfix A
  have hcP : xUnit τ L d 1 ∈ P := by
    refine Subgroup.mem_inf.2 ⟨xUnit_mem_subsystemGroup hd 1, ?_⟩
    rw [mem_twistedFixedPoints, entrywise_xUnit, one_pow]
    exact hxd 1
  have hc'P : yUnit τ L d 1 ∈ P := by
    refine Subgroup.mem_inf.2 ⟨yUnit_mem_subsystemGroup hd 1, ?_⟩
    rw [mem_twistedFixedPoints, entrywise_yUnit, one_pow]
    exact hyd 1
  have hcen : (⟨xUnit τ L d 1, hcP⟩ : ↥P) ∉ Subgroup.center ↥P := by
    intro hz
    have := Subgroup.mem_center_iff.1 hz ⟨yUnit τ L d 1, hc'P⟩
    exact excOth_not_commute_xy d (congrArg Subtype.val this).symm
  have hcρ : ∀ A : SL2 K, Commute (ρ A) (xUnit τ L d 1) := by
    intro A
    rw [hρ, ← simpleRootSL2_uSL]
    exact (excOth_commute_simple hτ hcad _ _).mul_left (excOth_commute_simple hτ hcbd _ _)
  have hker : ∀ B : SL2 K, ρ B = 1 → (B : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    intro B hB
    rw [hρ] at hB
    have hX : ρa B = (ρb B)⁻¹ := eq_inv_of_mul_eq_one_left hB
    have hc1 : Commute (ρa B) (simpleRootSL2 τ L a (uSL 1)) := by
      rw [hX]
      exact ((excOth_commute_simple hτ hcab _ _).symm).inv_left
    have h1 : Matrix.SpecialLinearGroup.map K.subtype B * uSL 1 =
        uSL 1 * Matrix.SpecialLinearGroup.map K.subtype B := by
      apply excOth_simple_injective a
      rw [map_mul, map_mul]
      exact hc1.eq
    have h2 := congrArg (fun M : SL2 L => (M : Matrix (Fin 2) (Fin 2) L) 0 0) h1
    simp [coe_uSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h2
    exact Subtype.ext (by simpa using h2)
  have hK3 : 3 ≤ Nat.card K := by
    have h3 : Nat.card K = ℓ ^ (2 * f) := card_frobeniusFixedField (by omega)
    rw [h3]
    have hℓ := (Fact.out : ℓ.Prime).two_le
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ 2
      _ ≤ ℓ ^ (2 * f) := Nat.pow_le_pow_right (by omega) (by omega)
  refine excOth_sl2_heis φ (ρ.codRestrict P hρP) hK3 (fun B hB => hker B ?_) hcen
    (fun s => ?_) (fun t => ?_)
  · exact congrArg Subtype.val hB
  · exact Subtype.ext (hcρ _)
  · exact Subtype.ext (hcρ _)

end Std

section Star

theorem excOth_iform_single (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (p q : Fin τ.rank) :
    iform (Pi.single p 1 : Fin τ.rank → ℤ) (Pi.single q 1) = τ.cartan p q := by
  have hs : τ.symmetrizer p p = 1 := by
    rcases hτ with rfl | rfl | rfl | rfl <;> simp [Tag.symmetrizer]
  rw [iform_single_left, hs, one_mul]
  rw [Finset.sum_eq_single q (fun l _ hl => by rw [Pi.single_eq_of_ne hl, mul_zero])
    (fun h => absurd (Finset.mem_univ q) h), Pi.single_eq_same, mul_one]

theorem excOth_iform_self (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) : iform α α = 2 := by
  rw [← dotProduct_mulVec_eq_iform]
  exact rootForm_self hτ hα

theorem excOth_not_isRoot_add_sub (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ) (h0 : iform β γ = 0) :
    ¬IsRoot τ (β + γ) ∧ ¬IsRoot τ (β - γ) := by
  have h0' : iform γ β = 0 := by rw [iform_comm]; exact h0
  have hβ2 := excOth_iform_self hτ hβ
  have hγ2 := excOth_iform_self hτ hγ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have e := excOth_iform_self hτ h
    rw [iform_add_left, iform_add_right, iform_add_right, hβ2, hγ2, h0, h0'] at e
    omega
  · have e := excOth_iform_self hτ h
    rw [sub_eq_add_neg, iform_add_left, iform_add_right, iform_add_right, iform_neg_right,
      iform_neg_left, iform_neg_left, iform_neg_right, hβ2, hγ2, h0, h0'] at e
    omega

end Star


section Triple

@[expose] def excOth_mulHom {G H : Type*} [Group G] [Group H] (f g : G →* H)
    (h : ∀ x y, Commute (f x) (g y)) : G →* H :=
  (MonoidHom.noncommCoprod f g h).comp (MonoidHom.prod (MonoidHom.id G) (MonoidHom.id G))

theorem excOth_mulHom_apply {G H : Type*} [Group G] [Group H] (f g : G →* H)
    (h : ∀ x y, Commute (f x) (g y)) (x : G) : excOth_mulHom f g h x = f x * g x := rfl

theorem excOth_reflect (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (v : Fin τ.rank → ℤ) : rootReflection β • v = v - iform β v • β := by
  rw [rootReflection_smul hβ]
  have h2 := corootPair_mul hβ v
  rw [excOth_iform_self hτ hβ] at h2
  have : corootPair β v = iform β v := by linarith
  rw [this]

@[expose] noncomputable def excOthW (τ : Tag) (a b c m : Fin τ.rank) : WeylGroup τ :=
  rootReflection (Pi.single m 1 : Fin τ.rank → ℤ) * rootReflection (Pi.single a 1) *
    rootReflection (Pi.single b 1) * rootReflection (Pi.single c 1)

theorem excOthW_smul (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {a b c m : Fin τ.rank}
    (hab : τ.cartan a b = 0) (hac : τ.cartan a c = 0) (hbc : τ.cartan b c = 0)
    (ham : τ.cartan a m = -1) (hbm : τ.cartan b m = -1) (hcm : τ.cartan c m = -1) :
    excOthW τ a b c m • (Pi.single m 1 : Fin τ.rank → ℤ) =
      (Pi.single a 1 : Fin τ.rank → ℤ) + Pi.single b 1 + Pi.single c 1 +
        (Pi.single m 1 + Pi.single m 1) := by
  have hs := fun p q => excOth_iform_single (τ := τ) hτ p q
  have hsym : ∀ p q : Fin τ.rank, iform (Pi.single p 1 : Fin τ.rank → ℤ) (Pi.single q 1) =
      iform (Pi.single q 1) (Pi.single p 1) := fun p q => iform_comm _ _
  have c_ma : iform (Pi.single m 1 : Fin τ.rank → ℤ) (Pi.single a 1) = -1 := by
    rw [hsym, hs, ham]
  have c_mb : iform (Pi.single m 1 : Fin τ.rank → ℤ) (Pi.single b 1) = -1 := by
    rw [hsym, hs, hbm]
  have c_mc : iform (Pi.single m 1 : Fin τ.rank → ℤ) (Pi.single c 1) = -1 := by
    rw [hsym, hs, hcm]
  have c_cm : iform (Pi.single c 1 : Fin τ.rank → ℤ) (Pi.single m 1) = -1 := by rw [hs, hcm]
  have c_bm : iform (Pi.single b 1 : Fin τ.rank → ℤ) (Pi.single m 1) = -1 := by rw [hs, hbm]
  have c_am : iform (Pi.single a 1 : Fin τ.rank → ℤ) (Pi.single m 1) = -1 := by rw [hs, ham]
  have c_bc : iform (Pi.single b 1 : Fin τ.rank → ℤ) (Pi.single c 1) = 0 := by rw [hs, hbc]
  have c_ac : iform (Pi.single a 1 : Fin τ.rank → ℤ) (Pi.single c 1) = 0 := by rw [hs, hac]
  have c_ab : iform (Pi.single a 1 : Fin τ.rank → ℤ) (Pi.single b 1) = 0 := by rw [hs, hab]
  have c_mm : iform (Pi.single m 1 : Fin τ.rank → ℤ) (Pi.single m 1) = 2 :=
    excOth_iform_self hτ (isRoot_single τ m)
  have e1 : rootReflection (Pi.single c 1 : Fin τ.rank → ℤ) • (Pi.single m 1 : Fin τ.rank → ℤ) =
      Pi.single m 1 + Pi.single c 1 := by
    rw [excOth_reflect hτ (isRoot_single τ c), c_cm]
    simp
  have e2 : rootReflection (Pi.single b 1 : Fin τ.rank → ℤ) •
      ((Pi.single m 1 : Fin τ.rank → ℤ) + Pi.single c 1) =
        Pi.single m 1 + Pi.single c 1 + Pi.single b 1 := by
    rw [excOth_reflect hτ (isRoot_single τ b), iform_add_right, c_bm, c_bc]
    simp
  have e3 : rootReflection (Pi.single a 1 : Fin τ.rank → ℤ) •
      ((Pi.single m 1 : Fin τ.rank → ℤ) + Pi.single c 1 + Pi.single b 1) =
        Pi.single m 1 + Pi.single c 1 + Pi.single b 1 + Pi.single a 1 := by
    rw [excOth_reflect hτ (isRoot_single τ a), iform_add_right, iform_add_right, c_am, c_ac,
      c_ab]
    simp
  have e4 : rootReflection (Pi.single m 1 : Fin τ.rank → ℤ) •
      ((Pi.single m 1 : Fin τ.rank → ℤ) + Pi.single c 1 + Pi.single b 1 + Pi.single a 1) =
        (Pi.single a 1 : Fin τ.rank → ℤ) + Pi.single b 1 + Pi.single c 1 +
          (Pi.single m 1 + Pi.single m 1) := by
    rw [excOth_reflect hτ (isRoot_single τ m), iform_add_right, iform_add_right, iform_add_right,
      c_mm, c_mc, c_mb, c_ma]
    have h : (2 + -1 + -1 + -1 : ℤ) = -1 := by norm_num
    rw [h, neg_smul, one_smul, sub_neg_eq_add]
    abel
  unfold excOthW
  simp only [mul_smul]
  rw [e1, e2, e3, e4]

end Triple

section TripleStd

theorem excOth_map_WSL (σ : L →+* L) :
    Matrix.SpecialLinearGroup.map σ (WSL : SL2 L) = WSL := by
  apply Subtype.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> simp [WSL]

theorem excOth_theta_orth (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {a b c m : Fin τ.rank}
    (hab : τ.cartan a b = 0) (hac : τ.cartan a c = 0) (hbc : τ.cartan b c = 0)
    (ham : τ.cartan a m = -1) (hbm : τ.cartan b m = -1) (hcm : τ.cartan c m = -1) :
    iform (excOthW τ a b c m • (Pi.single m 1 : Fin τ.rank → ℤ)) (Pi.single a 1) = 0 ∧
    iform (excOthW τ a b c m • (Pi.single m 1 : Fin τ.rank → ℤ)) (Pi.single b 1) = 0 ∧
    iform (excOthW τ a b c m • (Pi.single m 1 : Fin τ.rank → ℤ)) (Pi.single c 1) = 0 := by
  have hs := fun p q => excOth_iform_single (τ := τ) hτ p q
  have haa := excOth_iform_self hτ (isRoot_single τ a)
  have hbb := excOth_iform_self hτ (isRoot_single τ b)
  have hcc := excOth_iform_self hτ (isRoot_single τ c)
  have hab' : iform (Pi.single a 1 : Fin τ.rank → ℤ) (Pi.single b 1) = 0 := by rw [hs, hab]
  have hac' : iform (Pi.single a 1 : Fin τ.rank → ℤ) (Pi.single c 1) = 0 := by rw [hs, hac]
  have hbc' : iform (Pi.single b 1 : Fin τ.rank → ℤ) (Pi.single c 1) = 0 := by rw [hs, hbc]
  have ham' : iform (Pi.single a 1 : Fin τ.rank → ℤ) (Pi.single m 1) = -1 := by rw [hs, ham]
  have hbm' : iform (Pi.single b 1 : Fin τ.rank → ℤ) (Pi.single m 1) = -1 := by rw [hs, hbm]
  have hcm' : iform (Pi.single c 1 : Fin τ.rank → ℤ) (Pi.single m 1) = -1 := by rw [hs, hcm]
  have hba : iform (Pi.single b 1 : Fin τ.rank → ℤ) (Pi.single a 1) = 0 := by
    rw [iform_comm]; exact hab'
  have hca : iform (Pi.single c 1 : Fin τ.rank → ℤ) (Pi.single a 1) = 0 := by
    rw [iform_comm]; exact hac'
  have hcb : iform (Pi.single c 1 : Fin τ.rank → ℤ) (Pi.single b 1) = 0 := by
    rw [iform_comm]; exact hbc'
  have hma : iform (Pi.single m 1 : Fin τ.rank → ℤ) (Pi.single a 1) = -1 := by
    rw [iform_comm]; exact ham'
  have hmb : iform (Pi.single m 1 : Fin τ.rank → ℤ) (Pi.single b 1) = -1 := by
    rw [iform_comm]; exact hbm'
  have hmc : iform (Pi.single m 1 : Fin τ.rank → ℤ) (Pi.single c 1) = -1 := by
    rw [iform_comm]; exact hcm'
  rw [excOthW_smul hτ hab hac hbc ham hbm hcm]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [iform_add_left] <;> linarith

theorem excOth_commute_rootSL2_single (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) {j : Fin τ.rank}
    (h0 : iform θ (Pi.single j 1 : Fin τ.rank → ℤ) = 0) (A B : SL2 L) :
    Commute (rootSL2 τ L θ A) (simpleRootSL2 τ L j B) := by
  rw [← rootSL2_single_apply]
  obtain ⟨hp, hm⟩ := excOth_not_isRoot_add_sub hτ hθ (isRoot_single τ j) h0
  exact rootSL2_commute_of_orth hθ (isRoot_single τ j) h0 hp hm A B

variable [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem excOth_frob_cube (f : ℕ) (x : frobeniusFixedField L ℓ (3 * f)) :
    iterateFrobenius L ℓ f (iterateFrobenius L ℓ f (iterateFrobenius L ℓ f (x : L))) = x := by
  have h := mem_frobeniusFixedField.1 x.2
  simp only [iterateFrobenius_def]
  rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, show f + (f + f) = 3 * f by ring]
  exact h

end TripleStd

section TripleMain

variable [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem excOth_noL2_std_triple (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hf : 1 ≤ f)
    {J : Set (Fin τ.rank)} {a b c m : Fin τ.rank} (ha : a ∈ J) (hb : b ∈ J) (hc : c ∈ J)
    (hm : m ∈ J) (hcab : τ.cartan a b = 0) (hcac : τ.cartan a c = 0) (hcbc : τ.cartan b c = 0)
    (hcam : τ.cartan a m = -1) (hcbm : τ.cartan b m = -1) (hccm : τ.cartan c m = -1)
    {n₁ : ModGL τ L}
    (hxa : ∀ t, n₁ * xUnit τ L a t * n₁⁻¹ = xUnit τ L b t)
    (hya : ∀ t, n₁ * yUnit τ L a t * n₁⁻¹ = yUnit τ L b t)
    (hxb : ∀ t, n₁ * xUnit τ L b t * n₁⁻¹ = xUnit τ L c t)
    (hyb : ∀ t, n₁ * yUnit τ L b t * n₁⁻¹ = yUnit τ L c t)
    (hxc : ∀ t, n₁ * xUnit τ L c t * n₁⁻¹ = xUnit τ L a t)
    (hyc : ∀ t, n₁ * yUnit τ L c t * n₁⁻¹ = yUnit τ L a t)
    (hxm : ∀ t, n₁ * xUnit τ L m t * n₁⁻¹ = xUnit τ L m t)
    (hym : ∀ t, n₁ * yUnit τ L m t * n₁⁻¹ = yUnit τ L m t) :
    ExcOthNoL2 (subsystemGroup τ L J ⊓
      twistedFixedPoints n₁ (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  classical
  intro F _
  refine ⟨fun φ => ?_⟩
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFr
  set P : Subgroup (ModGL τ L) := subsystemGroup τ L J ⊓
      twistedFixedPoints n₁ (Units.map (entrywiseHom Fr)) with hP
  let K : Subfield L := frobeniusFixedField L ℓ (3 * f)
  have hK3 : ∀ x : K, Fr (Fr (Fr (x : L))) = x := excOth_frob_cube f
  let ρa : SL2 K →* ModGL τ L :=
    (simpleRootSL2 τ L a).comp (Matrix.SpecialLinearGroup.map K.subtype)
  let ρb : SL2 K →* ModGL τ L :=
    (simpleRootSL2 τ L b).comp ((Matrix.SpecialLinearGroup.map Fr).comp
      (Matrix.SpecialLinearGroup.map K.subtype))
  let ρc : SL2 K →* ModGL τ L :=
    (simpleRootSL2 τ L c).comp ((Matrix.SpecialLinearGroup.map Fr).comp
      ((Matrix.SpecialLinearGroup.map Fr).comp (Matrix.SpecialLinearGroup.map K.subtype)))
  have hab : ∀ A B, Commute (ρa A) (ρb B) := fun A B => excOth_commute_simple hτ hcab _ _
  have hac : ∀ A B, Commute (ρa A) (ρc B) := fun A B => excOth_commute_simple hτ hcac _ _
  have hbc : ∀ A B, Commute (ρb A) (ρc B) := fun A B => excOth_commute_simple hτ hcbc _ _
  let ρab : SL2 K →* ModGL τ L := excOth_mulHom ρa ρb hab
  have habc : ∀ A B, Commute (ρab A) (ρc B) := fun A B => by
    rw [excOth_mulHom_apply]
    exact (hac A B).mul_left (hbc A B)
  let ρ : SL2 K →* ModGL τ L := excOth_mulHom ρab ρc habc
  have hρ : ∀ A, ρ A = ρa A * ρb A * ρc A := fun A => rfl
  have hcube : ∀ A : SL2 K, Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr
      (Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map K.subtype A))) =
        Matrix.SpecialLinearGroup.map K.subtype A := by
    intro A
    ext i j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact hK3 (A i j)
  have hrot : ∀ (X Y Z : ModGL τ L), Commute X Y → Commute X Z → Y * Z * X = X * Y * Z := by
    intro X Y Z h1 h2
    exact ((h1.mul_right h2).eq).symm.trans (mul_assoc X Y Z).symm
  have hfix : ∀ A, n₁ * Units.map (entrywiseHom Fr) (ρ A) * n₁⁻¹ = ρ A := by
    intro A
    have e1 : ρa A = simpleRootSL2 τ L a (Matrix.SpecialLinearGroup.map K.subtype A) := rfl
    have e2 : ρb A = simpleRootSL2 τ L b (Matrix.SpecialLinearGroup.map Fr
      (Matrix.SpecialLinearGroup.map K.subtype A)) := rfl
    have e3 : ρc A = simpleRootSL2 τ L c (Matrix.SpecialLinearGroup.map Fr
      (Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map K.subtype A))) := rfl
    have e : ∀ X Y Z : ModGL τ L, n₁ * (X * Y * Z) * n₁⁻¹ =
        (n₁ * X * n₁⁻¹) * (n₁ * Y * n₁⁻¹) * (n₁ * Z * n₁⁻¹) := fun X Y Z => by group
    rw [hρ, map_mul, map_mul, e1, e2, e3, excOth_entrywise_simple, excOth_entrywise_simple,
      excOth_entrywise_simple, hcube, e, excOth_conj_simple hxa hya, excOth_conj_simple hxb hyb,
      excOth_conj_simple hxc hyc]
    exact hrot _ _ _ (excOth_commute_simple hτ hcab _ _) (excOth_commute_simple hτ hcac _ _)
  have hρP : ∀ A, ρ A ∈ P := fun A => by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [hρ]
      exact mul_mem (mul_mem (excOth_simple_mem_sub ha _) (excOth_simple_mem_sub hb _))
        (excOth_simple_mem_sub hc _)
    · rw [mem_twistedFixedPoints]
      exact hfix A
  set nW : ModGL τ L := rootSL2 τ L (Pi.single m 1) WSL * rootSL2 τ L (Pi.single a 1) WSL *
    rootSL2 τ L (Pi.single b 1) WSL * rootSL2 τ L (Pi.single c 1) WSL with hnW
  have hnW' : nW = simpleRootSL2 τ L m WSL * simpleRootSL2 τ L a WSL *
      simpleRootSL2 τ L b WSL * simpleRootSL2 τ L c WSL := by
    simp only [hnW, rootSL2_single_apply]
  have hnWmono : nW ∈ monomialSubgroup τ L :=
    mul_mem (mul_mem (mul_mem (rootSL2_WSL_mem_monomialSubgroup (isRoot_single τ m))
      (rootSL2_WSL_mem_monomialSubgroup (isRoot_single τ a)))
      (rootSL2_WSL_mem_monomialSubgroup (isRoot_single τ b)))
      (rootSL2_WSL_mem_monomialSubgroup (isRoot_single τ c))
  have hnWmaps : MapsRootLines nW (excOthW τ a b c m) :=
    (((mapsRootLines_rootSL2_WSL (isRoot_single τ m)).mul
      (mapsRootLines_rootSL2_WSL (isRoot_single τ a))).mul
      (mapsRootLines_rootSL2_WSL (isRoot_single τ b))).mul
      (mapsRootLines_rootSL2_WSL (isRoot_single τ c))
  obtain ⟨s, hs⟩ := exists_conj_rootSL2_eq hnWmono hnWmaps (isRoot_single τ m)
    (rfl : excOthW τ a b c m • (Pi.single m 1 : Fin τ.rank → ℤ) = _)
  have hθroot : IsRoot τ (excOthW τ a b c m • (Pi.single m 1 : Fin τ.rank → ℤ)) :=
    IsRoot.smul (isRoot_single τ m) _
  obtain ⟨ho_a, ho_b, ho_c⟩ := excOth_theta_orth hτ hcab hcac hcbc hcam hcbm hccm
  have hnWsub : nW ∈ subsystemGroup τ L J := by
    rw [hnW']
    exact mul_mem (mul_mem (mul_mem (excOth_simple_mem_sub hm _) (excOth_simple_mem_sub ha _))
      (excOth_simple_mem_sub hb _)) (excOth_simple_mem_sub hc _)
  have hFrnW : Units.map (entrywiseHom Fr) nW = nW := by
    rw [hnW']
    simp only [map_mul, excOth_entrywise_simple, excOth_map_WSL]
  have hn₁nW : n₁ * nW * n₁⁻¹ = nW := by
    have e : ∀ X Y Z U : ModGL τ L, n₁ * (X * Y * Z * U) * n₁⁻¹ =
        (n₁ * X * n₁⁻¹) * (n₁ * Y * n₁⁻¹) * (n₁ * Z * n₁⁻¹) * (n₁ * U * n₁⁻¹) :=
      fun X Y Z U => by group
    have key := hrot _ _ _ (excOth_commute_simple hτ hcab (WSL : SL2 L) (WSL : SL2 L))
      (excOth_commute_simple hτ hcac (WSL : SL2 L) (WSL : SL2 L))
    rw [hnW', e, excOth_conj_simple hxm hym, excOth_conj_simple hxa hya,
      excOth_conj_simple hxb hyb, excOth_conj_simple hxc hyc]
    calc _ = simpleRootSL2 τ L m WSL * (simpleRootSL2 τ L b WSL * simpleRootSL2 τ L c WSL *
          simpleRootSL2 τ L a WSL) := by group
      _ = _ := by rw [key]; group
  set c₀ : ModGL τ L := nW * xUnit τ L m 1 * nW⁻¹ with hc₀
  set c₁ : ModGL τ L := nW * yUnit τ L m 1 * nW⁻¹ with hc₁
  have hc₀eq : c₀ = rootSL2 τ L (excOthW τ a b c m • (Pi.single m 1 : Fin τ.rank → ℤ))
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s) (uSL 1)) := by
    rw [hc₀, ← simpleRootSL2_uSL, ← rootSL2_single_apply]
    exact hs _
  have hcρ : ∀ (M : SL2 L) (A : SL2 K), Commute (ρ A)
      (rootSL2 τ L (excOthW τ a b c m • (Pi.single m 1 : Fin τ.rank → ℤ)) M) := by
    intro M A
    rw [hρ]
    exact (((excOth_commute_rootSL2_single hτ hθroot ho_a M _).symm.mul_left
      (excOth_commute_rootSL2_single hτ hθroot ho_b M _).symm).mul_left
      (excOth_commute_rootSL2_single hτ hθroot ho_c M _).symm)
  have hcρ₀ : ∀ A : SL2 K, Commute (ρ A) c₀ := fun A => by
    rw [hc₀eq]
    exact hcρ _ A
  have hcP₀ : c₀ ∈ P := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact mul_mem (mul_mem hnWsub (xUnit_mem_subsystemGroup hm 1)) (inv_mem hnWsub)
    · rw [mem_twistedFixedPoints, hc₀, map_mul, map_mul, map_inv, hFrnW, entrywise_xUnit,
        one_pow]
      have : n₁ * (nW * xUnit τ L m 1 * nW⁻¹) * n₁⁻¹ =
          (n₁ * nW * n₁⁻¹) * (n₁ * xUnit τ L m 1 * n₁⁻¹) * (n₁ * nW * n₁⁻¹)⁻¹ := by group
      rw [this, hn₁nW, hxm]
  have hcP₁ : c₁ ∈ P := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact mul_mem (mul_mem hnWsub (yUnit_mem_subsystemGroup hm 1)) (inv_mem hnWsub)
    · rw [mem_twistedFixedPoints, hc₁, map_mul, map_mul, map_inv, hFrnW, entrywise_yUnit,
        one_pow]
      have : n₁ * (nW * yUnit τ L m 1 * nW⁻¹) * n₁⁻¹ =
          (n₁ * nW * n₁⁻¹) * (n₁ * yUnit τ L m 1 * n₁⁻¹) * (n₁ * nW * n₁⁻¹)⁻¹ := by group
      rw [this, hn₁nW, hym]
  have hcen : (⟨c₀, hcP₀⟩ : ↥P) ∉ Subgroup.center ↥P := by
    intro hz
    have h2 : c₁ * c₀ = c₀ * c₁ :=
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨c₁, hcP₁⟩)
    apply excOth_not_commute_xy (τ := τ) (L := L) m
    have hx : nW⁻¹ * c₀ * nW = xUnit τ L m 1 := by rw [hc₀]; group
    have hy : nW⁻¹ * c₁ * nW = yUnit τ L m 1 := by rw [hc₁]; group
    have h3 : yUnit τ L m 1 * xUnit τ L m 1 = xUnit τ L m 1 * yUnit τ L m 1 := by
      calc yUnit τ L m 1 * xUnit τ L m 1 = (nW⁻¹ * c₁ * nW) * (nW⁻¹ * c₀ * nW) := by
            rw [hx, hy]
        _ = nW⁻¹ * (c₁ * c₀) * nW := by group
        _ = nW⁻¹ * (c₀ * c₁) * nW := by rw [h2]
        _ = (nW⁻¹ * c₀ * nW) * (nW⁻¹ * c₁ * nW) := by group
        _ = xUnit τ L m 1 * yUnit τ L m 1 := by rw [hx, hy]
    exact h3.symm
  have hker : ∀ B : SL2 K, ρ B = 1 → (B : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    intro B hB
    rw [hρ] at hB
    have hX : ρa B = (ρb B * ρc B)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← mul_assoc]
      exact hB
    have hc1 : Commute (ρa B) (simpleRootSL2 τ L a (uSL 1)) := by
      rw [hX]
      exact ((excOth_commute_simple hτ hcab _ _).symm.mul_left
        (excOth_commute_simple hτ hcac _ _).symm).inv_left
    have h1 : Matrix.SpecialLinearGroup.map K.subtype B * uSL 1 =
        uSL 1 * Matrix.SpecialLinearGroup.map K.subtype B := by
      apply excOth_simple_injective a
      rw [map_mul, map_mul]
      exact hc1.eq
    have h2 := congrArg (fun M : SL2 L => (M : Matrix (Fin 2) (Fin 2) L) 0 0) h1
    simp [coe_uSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h2
    exact Subtype.ext (by simpa using h2)
  have hK3' : 3 ≤ Nat.card K := by
    have h3 : Nat.card K = ℓ ^ (3 * f) := card_frobeniusFixedField (by omega)
    rw [h3]
    have hℓ := (Fact.out : ℓ.Prime).two_le
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ 2
      _ ≤ ℓ ^ (3 * f) := Nat.pow_le_pow_right (by omega) (by omega)
  refine excOth_sl2_heis φ (ρ.codRestrict P hρP) hK3' (fun B hB => hker B ?_) hcen
    (fun s' => ?_) (fun t => ?_)
  · exact congrArg Subtype.val hB
  · exact Subtype.ext (hcρ₀ _)
  · exact Subtype.ext (hcρ₀ _)

end TripleMain

end Rk1

end CFSG.HardMathSupport.Dickson.Sec6.I1431

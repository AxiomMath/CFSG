module

public import CFSG.Quasithin.Background.HStandard
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankFix
import TauCeti.RepresentationTheory.Unipotent.PowerOrder

public section

namespace CFSG.ClassicalGroups.Unitary

open CFSG.Quasithin CFSG.Quasithin.H
open scoped Matrix

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

@[expose] noncomputable def linAutOf (a : MulAut (StdMod (Fin 4) K))
    (ha : IsSemilinear a (RingEquiv.refl K)) : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) where
  toFun := toAddMap a
  invFun := toAddMap a⁻¹
  map_add' := toAddMap_add a
  map_smul' c v := by simpa using ha c v
  left_inv v := toAddMap_apply_inv a v
  right_inv v := toAddMap_inv_apply a v

@[expose] noncomputable def linHomOf (A : Subgroup (MulAut (StdMod (Fin 4) K)))
    (hlin : ∀ a ∈ A, IsSemilinear a (RingEquiv.refl K)) :
    A →* ((Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) where
  toFun a := linAutOf (a : MulAut (StdMod (Fin 4) K)) (hlin a a.2)
  map_one' := by ext v; rfl
  map_mul' a b := by ext v; simp [linAutOf, toAddMap_mul]

@[expose] noncomputable def smallOrbitRep (A : Subgroup (MulAut (StdMod (Fin 4) K)))
    (hlin : ∀ a ∈ A, IsSemilinear a (RingEquiv.refl K)) :
    Representation K A (Fin 4 → K) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (linHomOf A hlin)

theorem smallOrbitRep_apply (A : Subgroup (MulAut (StdMod (Fin 4) K)))
    (hlin : ∀ a ∈ A, IsSemilinear a (RingEquiv.refl K)) (a : A) (v : Fin 4 → K) :
    smallOrbitRep A hlin a v = toAddMap (a : MulAut (StdMod (Fin 4) K)) v := rfl

theorem isPGroup_two_of_elemAbelian2 {A : Subgroup (MulAut (StdMod (Fin 4) K))}
    (hA : IsElemAbelian2 A) : IsPGroup 2 A := by
  rw [isPGroup_iff_exists_pow_pow_eq_one]
  refine ⟨1, fun a => ?_⟩
  apply Subtype.ext
  simpa using hA.2 (a : MulAut (StdMod (Fin 4) K)) a.2

theorem mem_fixV_ofAdd_iff (A : Subgroup (MulAut (StdMod (Fin 4) K)))
    (v : Fin 4 → K) :
    Multiplicative.ofAdd v ∈ fixV A ↔ ∀ a ∈ A, toAddMap a v = v := by
  rw [mem_fixV]
  constructor
  · intro h a ha
    have := h a ha
    simpa [toAddMap] using congrArg Multiplicative.toAdd this
  · intro h a ha
    simpa [toAddMap] using congrArg Multiplicative.ofAdd (h a ha)

@[expose] noncomputable def hermReflForm (hσ : IsUnitaryInvolution σ) :
    CFSG.LieType.BorelTits.ReflForm K (Fin 4 → K) where
  σ := σ
  β := herm σ
  add_left := herm_add_left σ
  smul_left := fun c u v => herm_smul_left σ c u v
  add_right := herm_add_right σ
  smul_right := fun c u v => herm_smul_right σ c u v
  refl := fun u v h => by rw [herm_conj σ hσ.invol, h, map_zero]
  nondeg := fun u h => eq_zero_of_herm σ h

@[expose] noncomputable def smallOrbitTrace (σ : K ≃+* K) : K →+ K :=
  AddMonoidHom.id K + σ.toAddMonoidHom

@[expose] noncomputable def fixedFieldAdd (σ : K ≃+* K) : AddSubgroup K where
  carrier := {c | σ c = c}
  zero_mem' := map_zero σ
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, ha, hb]
  neg_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_neg, ha]

theorem smallOrbitTrace_apply (σ : K ≃+* K) (x : K) : smallOrbitTrace σ x = x + σ x := rfl

theorem map_smallOrbitTrace_fixed (hσ : IsUnitaryInvolution σ) (x : K) :
    σ (smallOrbitTrace σ x) = smallOrbitTrace σ x := by
  rw [smallOrbitTrace_apply, map_add, hσ.invol, add_comm]

theorem natCard_fixedFieldAdd (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) = 0)
    {m : ℕ} (hK : Nat.card K = (2 ^ m) ^ 2) :
    Nat.card (fixedFieldAdd σ) = 2 ^ m := by
  have hFix := CFSG.LocalAnalysis.RankThreeUC.card_fixedField_mul_self hσ h2
  have hpow : Nat.card (fixedFieldAdd σ) ^ 2 = (2 ^ m) ^ 2 := by
    rw [pow_two, pow_two]
    calc Nat.card (fixedFieldAdd σ) * Nat.card (fixedFieldAdd σ)
        = Nat.card {c : K // σ c = c} * Nat.card {c : K // σ c = c} := rfl
      _ = Nat.card K := hFix
      _ = 2 ^ m * 2 ^ m := by rw [hK, pow_two]
  exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) hpow

theorem smallOrbit_card_le_three_mul {m : ℕ} (hK : Nat.card K = (2 ^ m) ^ 2) :
    Nat.card K ≤ 2 ^ (3 * m) := by
  have hmono : (2 : ℕ) ^ (2 * m) ≤ 2 ^ (3 * m) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  calc Nat.card K = (2 ^ m) ^ 2 := hK
    _ = 2 ^ (2 * m) := by
      rw [pow_two, ← pow_add]
      congr 1
      omega
    _ ≤ 2 ^ (3 * m) := hmono

section Main

variable {A : Subgroup (MulAut (StdMod (Fin 4) K))}

private theorem exists_small_orbit_aux [CharP K 2]
    (hσ : IsUnitaryInvolution σ) {m : ℕ} (hK : Nat.card K = (2 ^ m) ^ 2)
    (hA : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    (hlin : ∀ a ∈ A, IsSemilinear a (RingEquiv.refl K))
    (hiso : ∀ a ∈ A, ∀ x y, herm σ (toAddMap a x) (toAddMap a y) = herm σ x y) :
    ∃ w ∉ fixV A, ∃ U : Subgroup (StdMod (Fin 4) K),
      Nat.card U ≤ 2 ^ (3 * m) ∧ ∀ a ∈ A, a w * w⁻¹ ∈ U := by
  classical
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  let hf := hermReflForm (σ := σ) hσ
  let ρ := smallOrbitRep A hlin
  let D : Submodule K (Fin 4 → K) := ρ.invariants
  let Dperp : Submodule K (Fin 4 → K) := hf.perp D
  let Tfix : Submodule K (Fin 4 → K) := D ⊓ Dperp
  have hmemD : ∀ v : Fin 4 → K, v ∈ D ↔ ∀ a ∈ A, toAddMap a v = v := by
    intro v
    rw [show D = ρ.invariants from rfl, Representation.mem_invariants]
    constructor
    · intro h a ha
      have := h ⟨a, ha⟩
      simpa [ρ, smallOrbitRep_apply] using this
    · intro h a
      simpa [ρ, smallOrbitRep_apply] using h (a : MulAut (StdMod (Fin 4) K)) a.2
  have hDperp_inv : ∀ a ∈ A, ∀ v ∈ Dperp, toAddMap a v ∈ Dperp := by
    intro a ha v hv
    rw [show Dperp = hf.perp D from rfl, hf.mem_perp] at hv ⊢
    intro d hd
    have hd' : toAddMap a⁻¹ d = d := (hmemD d).mp hd a⁻¹ (inv_mem ha)
    have h1 : toAddMap a (toAddMap a⁻¹ d) = d := by
      rw [← toAddMap_mul, mul_inv_cancel, toAddMap_one]
    calc herm σ d (toAddMap a v)
        = herm σ (toAddMap a (toAddMap a⁻¹ d)) (toAddMap a v) := by rw [h1]
      _ = herm σ (toAddMap a⁻¹ d) v := hiso a ha _ _
      _ = herm σ d v := by rw [hd']
      _ = 0 := hv d hd
  have hDneTop : D ≠ ⊤ := by
    intro htop
    apply hA1
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    apply toAddMap_injective
    intro v
    rw [toAddMap_one]
    exact (hmemD v).mp (by rw [htop]; exact Submodule.mem_top) a ha
  have hDperp_ne : Dperp ≠ ⊥ := by
    intro hbot
    apply hDneTop
    calc D = hf.perp (hf.perp D) := (hf.perp_perp D).symm
      _ = hf.perp Dperp := rfl
      _ = hf.perp ⊥ := by rw [hbot]
      _ = ⊤ := hf.perp_bot
  have hDperp_comap : ∀ a : A, Dperp ≤ Submodule.comap (ρ a) Dperp := by
    intro a v hv
    exact hDperp_inv (a : MulAut (StdMod (Fin 4) K)) a.2 v hv
  let ρD : Representation K A Dperp := ρ.subrepresentation Dperp hDperp_comap
  have hT_ne : Tfix ≠ ⊥ := by
    have hnt : Nontrivial Dperp := Submodule.nontrivial_iff_ne_bot.mpr hDperp_ne
    obtain ⟨v, hv0, hvfix⟩ :=
      @Representation.exists_common_fixed_vector_of_isPGroup K A Dperp _ _ _ _
        2 (expChar_prime (R := K) 2) (inferInstance) hnt
        (isPGroup_two_of_elemAbelian2 hA) ρD
    have hvD : (v : Fin 4 → K) ∈ D := by
      rw [hmemD]
      intro a ha
      have h := hvfix ⟨a, ha⟩
      have := congrArg Subtype.val h
      simpa [ρD, ρ, smallOrbitRep_apply, Representation.subrepresentation_apply] using this
    intro hbot
    have hvT : (v : Fin 4 → K) ∈ Tfix := by
      change (v : Fin 4 → K) ∈ D ⊓ Dperp
      exact Submodule.mem_inf.mpr ⟨hvD, v.2⟩
    rw [hbot] at hvT
    have hvzero : (v : Fin 4 → K) = 0 := by simpa using hvT
    exact hv0 (Subtype.ext hvzero)
  have hT_le_D : Tfix ≤ D := fun _ hx => hx.1
  have hT_le_Dperp : Tfix ≤ Dperp := fun _ hx => hx.2
  have hT_iso : ∀ x ∈ Tfix, ∀ y ∈ Tfix, herm σ x y = 0 := by
    intro x hx y hy
    exact (hf.mem_perp.mp hy.2) x hx.1
  have htle : Module.finrank K Tfix ≤ 2 := by
    have hle : Tfix ≤ hf.perp Tfix := by
      intro x hx
      rw [hf.mem_perp]
      intro y hy
      change herm σ y x = 0
      rw [herm_conj σ hσ.invol x y, hT_iso x hx y hy, map_zero]
    have h1 := hf.finrank_perp Tfix
    have h2' := Submodule.finrank_mono hle
    rw [Module.finrank_fin_fun] at h1
    omega
  have htpos : 0 < Module.finrank K Tfix := by
    have hne : Module.finrank K Tfix ≠ 0 := by
      intro h0
      apply hT_ne
      rw [← Submodule.finrank_eq_zero]
      exact h0
    omega
  have hdispDperp : ∀ a ∈ A, ∀ v : Fin 4 → K, toAddMap a v - v ∈ Dperp := by
    intro a ha v
    rw [show Dperp = hf.perp D from rfl, hf.mem_perp]
    intro d hd
    have hd' : toAddMap a d = d := (hmemD d).mp hd a ha
    have hdinv : toAddMap a⁻¹ d = d := (hmemD d).mp hd a⁻¹ (inv_mem ha)
    calc herm σ d (toAddMap a v - v)
        = herm σ d (toAddMap a v) - herm σ d v := by rw [herm_sub_right]
      _ = herm σ (toAddMap a (toAddMap a⁻¹ d)) (toAddMap a v) - herm σ d v := by
            rw [← toAddMap_mul, mul_inv_cancel, toAddMap_one]
      _ = herm σ (toAddMap a⁻¹ d) v - herm σ d v := by rw [hiso a ha]
      _ = herm σ d v - herm σ d v := by rw [hdinv]
      _ = 0 := sub_self _
  have ht12 : Module.finrank K Tfix = 1 ∨ Module.finrank K Tfix = 2 := by omega
  rcases ht12 with ht | ht
  ·
    let U : Subgroup (StdMod (Fin 4) K) := AddSubgroup.toSubgroup Tfix.toAddSubgroup
    have hcardU : Nat.card U ≤ 2 ^ (3 * m) := by
      have hcardT : Nat.card Tfix = Nat.card K ^ Module.finrank K Tfix :=
        Module.natCard_eq_pow_finrank
      calc Nat.card U = Nat.card Tfix := rfl
        _ = Nat.card K ^ 1 := by rw [hcardT, ht]
        _ = Nat.card K := pow_one _
        _ ≤ 2 ^ (3 * m) := smallOrbit_card_le_three_mul hK
    by_cases hDperp_eq : Dperp = Tfix
    · obtain ⟨v, hvD⟩ : ∃ v : Fin 4 → K, v ∉ D := by
        by_contra h
        have h' : ∀ v, v ∈ D := by
          intro v
          by_contra hv
          exact h ⟨v, hv⟩
        exact hDneTop (le_antisymm (fun _ _ => Submodule.mem_top) (fun v _ => h' v))
      refine ⟨Multiplicative.ofAdd v, ?_, U, hcardU, ?_⟩
      · rw [mem_fixV_ofAdd_iff]
        intro h
        exact hvD ((hmemD v).mpr h)
      · intro a ha
        have hmemT : toAddMap a v - v ∈ Tfix := by
          rw [← hDperp_eq]
          exact hdispDperp a ha v
        have hmul : a (Multiplicative.ofAdd v) * (Multiplicative.ofAdd v)⁻¹ =
            Multiplicative.ofAdd (toAddMap a v - v) := by
          simp [toAddMap, sub_eq_add_neg]
        rw [hmul]
        rw [show U = AddSubgroup.toSubgroup Tfix.toAddSubgroup from rfl,
          Multiplicative.mem_toSubgroup]
        simpa using hmemT
    · let Tsub : Submodule K Dperp := Tfix.comap Dperp.subtype
      have hmemTsub : ∀ x : Dperp, x ∈ Tsub ↔ (x : Fin 4 → K) ∈ Tfix := by
        intro x
        rfl
      have hTsub_ne_top : Tsub ≠ ⊤ := by
        intro htop
        apply hDperp_eq
        apply le_antisymm _ hT_le_Dperp
        intro x hx
        have hx' : (⟨x, hx⟩ : Dperp) ∈ Tsub := by
          rw [htop]
          exact Submodule.mem_top
        exact (hmemTsub ⟨x, hx⟩).mp hx'
      have hTsub_comap : ∀ a : A, Tsub ≤ Submodule.comap (ρD a) Tsub := by
        intro a x hx
        have hxT : (x : Fin 4 → K) ∈ Tfix := (hmemTsub x).mp hx
        have hfix : toAddMap (a : MulAut (StdMod (Fin 4) K)) (x : Fin 4 → K) =
            (x : Fin 4 → K) := (hmemD _).mp hxT.1 _ a.2
        change (ρD a) x ∈ Tsub
        rw [hmemTsub]
        have hcoe : ((ρD a) x : Fin 4 → K) =
            toAddMap (a : MulAut (StdMod (Fin 4) K)) (x : Fin 4 → K) := by
          simp [ρD, ρ, smallOrbitRep_apply, Representation.subrepresentation_apply]
        rw [hcoe, hfix]
        exact hxT
      let ρQ : Representation K A (Dperp ⧸ Tsub) := ρD.quotient Tsub hTsub_comap
      have hntQ : Nontrivial (Dperp ⧸ Tsub) :=
        Submodule.Quotient.nontrivial_iff.mpr hTsub_ne_top
      obtain ⟨q, hq0, hqfix⟩ :=
        @Representation.exists_common_fixed_vector_of_isPGroup K A (Dperp ⧸ Tsub) _ _ _ _
          2 (expChar_prime (R := K) 2) (inferInstance) hntQ
          (isPGroup_two_of_elemAbelian2 hA) ρQ
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective Tsub q
      have hxT : (x : Fin 4 → K) ∉ Tfix := by
        intro hx
        apply hq0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact (hmemTsub x).mpr hx
      have hxfix : ∀ a : A, toAddMap (a : MulAut (StdMod (Fin 4) K)) (x : Fin 4 → K) -
          (x : Fin 4 → K) ∈ Tfix := by
        intro a
        have h := hqfix a
        simp only [ρQ, Representation.quotient_apply, Submodule.mapQ_apply] at h
        have hsub : (ρD a) x - x ∈ Tsub := (Submodule.Quotient.eq Tsub).mp h
        have hcoe : (((ρD a) x - x : Dperp) : Fin 4 → K) =
            toAddMap (a : MulAut (StdMod (Fin 4) K)) (x : Fin 4 → K) - (x : Fin 4 → K) := by
          simp [ρD, ρ, smallOrbitRep_apply, Representation.subrepresentation_apply]
        rw [← hcoe]
        exact (hmemTsub _).mp hsub
      refine ⟨Multiplicative.ofAdd (x : Fin 4 → K), ?_, U, hcardU, ?_⟩
      · rw [mem_fixV_ofAdd_iff]
        intro h
        apply hxT
        exact Submodule.mem_inf.mpr ⟨(hmemD (x : Fin 4 → K)).mpr h, x.2⟩
      · intro a ha
        have hmemT : toAddMap (a : MulAut (StdMod (Fin 4) K)) (x : Fin 4 → K) -
            (x : Fin 4 → K) ∈ Tfix := hxfix ⟨a, ha⟩
        have hmul : a (Multiplicative.ofAdd (x : Fin 4 → K)) *
            (Multiplicative.ofAdd (x : Fin 4 → K))⁻¹ =
            Multiplicative.ofAdd (toAddMap (a : MulAut (StdMod (Fin 4) K)) (x : Fin 4 → K) -
              (x : Fin 4 → K)) := by
          simp [toAddMap, sub_eq_add_neg]
        rw [hmul]
        rw [show U = AddSubgroup.toSubgroup Tfix.toAddSubgroup from rfl,
          Multiplicative.mem_toSubgroup]
        simpa using hmemT
  ·
    have hT_max : hf.perp Tfix = Tfix := by
      have hle : Tfix ≤ hf.perp Tfix := by
        intro x hx
        rw [hf.mem_perp]
        intro y hy
        change herm σ y x = 0
        rw [herm_conj σ hσ.invol x y, hT_iso x hx y hy, map_zero]
      have h1 := hf.finrank_perp Tfix
      have h2' := Submodule.finrank_mono hle
      rw [Module.finrank_fin_fun] at h1
      have hdim : Module.finrank K (hf.perp Tfix) = 2 := by omega
      exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [ht, hdim])).symm
    have hD_eq_T : D = Tfix := by
      apply le_antisymm
      · calc D = hf.perp (hf.perp D) := (hf.perp_perp D).symm
          _ = hf.perp Dperp := rfl
          _ ≤ hf.perp Tfix := hf.perp_antitone hT_le_Dperp
          _ = Tfix := hT_max
      · exact hT_le_D
    have hDperp_eq_T : Dperp = Tfix := by
      apply le_antisymm
      · calc Dperp = hf.perp D := rfl
          _ ≤ hf.perp Tfix := hf.perp_antitone hT_le_D
          _ = Tfix := hT_max
      · exact hT_le_Dperp
    have hDneTop2 : D ≠ ⊤ := by
      intro htop
      have h4 : Module.finrank K D = 4 := by
        rw [htop, finrank_top, Module.finrank_fin_fun]
      rw [hD_eq_T, ht] at h4
      omega
    obtain ⟨v, hvD⟩ : ∃ v : Fin 4 → K, v ∉ D := by
      by_contra h
      have h' : ∀ v, v ∈ D := by
        intro v
        by_contra hv
        exact h ⟨v, hv⟩
      exact hDneTop2 (le_antisymm (fun _ _ => Submodule.mem_top) (fun v _ => h' v))
    have hvDperp : v ∉ Dperp := by
      intro h
      have hT : v ∈ Tfix := by
        rw [← hDperp_eq_T]
        exact h
      rw [← hD_eq_T] at hT
      exact hvD hT
    have hsurj_h : Function.Surjective (fun t : Tfix => herm σ v (t : Fin 4 → K)) := by
      obtain ⟨d, hdD, hdv⟩ : ∃ d ∈ D, herm σ d v ≠ 0 := by
        by_contra h
        apply hvDperp
        rw [show Dperp = hf.perp D from rfl, hf.mem_perp]
        intro d hd
        by_contra hd0
        exact h ⟨d, hd, hd0⟩
      have hdT : d ∈ Tfix := by
        rw [← hD_eq_T]
        exact hdD
      have hvd : herm σ v d ≠ 0 := by
        intro hzero
        apply hdv
        rw [herm_conj σ hσ.invol, hzero, map_zero]
      intro c
      refine ⟨(c * (herm σ v d)⁻¹) • (⟨d, hdT⟩ : Tfix), ?_⟩
      change herm σ v ((c * (herm σ v d)⁻¹) • d) = c
      rw [herm_smul_right]
      field_simp
    let φ : Tfix →+ K :=
      { toFun := fun t => smallOrbitTrace σ (herm σ v (t : Fin 4 → K))
        map_zero' := by simp [smallOrbitTrace]
        map_add' := fun t t' => by simp [smallOrbitTrace, herm_add_right, map_add] }
    let Ffix := fixedFieldAdd σ
    let φ' : Tfix →+ Ffix :=
      { toFun := fun t => ⟨φ t, by
          change σ (smallOrbitTrace σ (herm σ v (t : Fin 4 → K))) =
            smallOrbitTrace σ (herm σ v (t : Fin 4 → K))
          exact map_smallOrbitTrace_fixed hσ _⟩
        map_zero' := by apply Subtype.ext; simp [φ, smallOrbitTrace]
        map_add' := fun t t' => by
          apply Subtype.ext
          simp [φ, smallOrbitTrace, herm_add_right, map_add] }
    have hsurjφ : Function.Surjective φ' := by
      intro a
      have ha : σ (a : K) = (a : K) := a.2
      obtain ⟨c, hc⟩ := hσ.trace_surj (a : K) ha
      obtain ⟨t, ht⟩ := hsurj_h c
      refine ⟨t, ?_⟩
      apply Subtype.ext
      change herm σ v (t : Fin 4 → K) + σ (herm σ v (t : Fin 4 → K)) = (a : K)
      have ht' : herm σ v (t : Fin 4 → K) = c := ht
      rw [ht']
      exact hc
    have hcardT : Nat.card Tfix = 2 ^ (4 * m) := by
      have hTcard := Module.natCard_eq_pow_finrank (K := K) (V := Tfix)
      calc Nat.card Tfix = Nat.card K ^ Module.finrank K Tfix := hTcard
        _ = Nat.card K ^ 2 := by rw [ht]
        _ = ((2 ^ m) ^ 2) ^ 2 := by rw [hK]
        _ = 2 ^ (4 * m) := by
          have h1 : (2 ^ m) ^ 2 = 2 ^ (2 * m) := by
            rw [pow_two, ← pow_add]
            congr 1
            omega
          rw [h1, pow_two, ← pow_add]
          congr 1
          omega
    have hFcard : Nat.card Ffix = 2 ^ m := natCard_fixedFieldAdd hσ h2 hK
    have hkerT := AddSubgroup.card_ker_mul_card_of_surjective (f := φ') hsurjφ
    have hkereq : Nat.card φ'.ker = 2 ^ (3 * m) := by
      have h := hkerT
      rw [hFcard, hcardT] at h
      have hpos : 0 < 2 ^ m := pow_pos (by norm_num : (0 : ℕ) < 2) m
      refine Nat.eq_of_mul_eq_mul_right hpos ?_
      calc Nat.card φ'.ker * 2 ^ m = 2 ^ (4 * m) := h
        _ = 2 ^ (3 * m) * 2 ^ m := by
          rw [← pow_add]
          congr 1
          omega
    let Uadd : AddSubgroup (Fin 4 → K) := φ'.ker.map Tfix.subtype.toAddMonoidHom
    let U : Subgroup (StdMod (Fin 4) K) := AddSubgroup.toSubgroup Uadd
    have hcardU : Nat.card U ≤ 2 ^ (3 * m) := by
      have hmap : Nat.card Uadd = Nat.card φ'.ker :=
        AddSubgroup.card_map_of_injective (f := Tfix.subtype.toAddMonoidHom)
          (fun x y h => Subtype.ext h)
      calc Nat.card U = Nat.card Uadd := rfl
        _ = Nat.card φ'.ker := hmap
        _ = 2 ^ (3 * m) := hkereq
        _ ≤ 2 ^ (3 * m) := le_rfl
    refine ⟨Multiplicative.ofAdd v, ?_, U, hcardU, ?_⟩
    · rw [mem_fixV_ofAdd_iff]
      intro h
      exact hvD ((hmemD v).mpr h)
    · intro a ha
      have hdisp : toAddMap a v - v ∈ Tfix := by
        rw [← hDperp_eq_T]
        exact hdispDperp a ha v
      have htrace : φ ⟨toAddMap a v - v, hdisp⟩ = 0 := by
        change smallOrbitTrace σ (herm σ v (toAddMap a v - v)) = 0
        have hav : toAddMap a v = v + (toAddMap a v - v) := by abel
        have hvv : herm σ (v + (toAddMap a v - v)) (v + (toAddMap a v - v)) =
            herm σ v v := by
          rw [← hav]
          exact hiso a ha v v
        have hexp : herm σ v v + herm σ v (toAddMap a v - v) +
            herm σ (toAddMap a v - v) v + herm σ (toAddMap a v - v) (toAddMap a v - v) =
            herm σ v v := by
          have h := hvv
          simp only [herm_add_left, herm_add_right] at h
          simpa only [add_assoc, add_left_comm, add_comm] using h
        have hzero0 : herm σ v (toAddMap a v - v) +
            herm σ (toAddMap a v - v) v +
            herm σ (toAddMap a v - v) (toAddMap a v - v) = 0 := by
          have h := hexp
          simp only [add_assoc, add_left_comm, add_comm] at h ⊢
          exact add_left_cancel (by simpa only [add_zero] using h)
        have htt : herm σ (toAddMap a v - v) (toAddMap a v - v) = 0 :=
          hT_iso _ hdisp _ hdisp
        have htv : herm σ (toAddMap a v - v) v = σ (herm σ v (toAddMap a v - v)) :=
          herm_conj σ hσ.invol v _
        rw [htv, htt, add_zero] at hzero0
        simpa [smallOrbitTrace_apply] using hzero0
      have hmemker : toAddMap a v - v ∈ Uadd := by
        have hmem : (⟨toAddMap a v - v, hdisp⟩ : Tfix) ∈ φ'.ker := by
          rw [AddMonoidHom.mem_ker]
          apply Subtype.ext
          exact htrace
        exact AddSubgroup.mem_map.mpr ⟨_, hmem, rfl⟩
      have hmul : a (Multiplicative.ofAdd v) * (Multiplicative.ofAdd v)⁻¹ =
          Multiplicative.ofAdd (toAddMap a v - v) := by
        simp [toAddMap, sub_eq_add_neg]
      rw [hmul]
      rw [show U = AddSubgroup.toSubgroup Uadd from rfl, Multiplicative.mem_toSubgroup]
      simpa using hmemker

end Main

theorem exists_small_orbit_unitary (hσ : IsUnitaryInvolution σ) {m : ℕ}
    (hK : Nat.card K = (2 ^ m) ^ 2)
    {A : Subgroup (MulAut (StdMod (Fin 4) K))} (hA : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    (hlin : ∀ a ∈ A, IsSemilinear a (RingEquiv.refl K))
    (hiso : ∀ a ∈ A, ∀ x y, herm σ (toAddMap a x) (toAddMap a y) = herm σ x y) :
    ∃ w ∉ fixV A, ∃ U : Subgroup (StdMod (Fin 4) K),
      Nat.card U ≤ 2 ^ (3 * m) ∧ ∀ a ∈ A, a w * w⁻¹ ∈ U := by
  have hchar : CharP K 2 := by
    have hFintype : Fintype K := Fintype.ofFinite K
    exact @charP_of_card_eq_prime_pow K _ _ hFintype 2 (2 * m) (inferInstance) (by
      rw [← Nat.card_eq_fintype_card, hK, pow_two, ← pow_add]
      congr 1
      omega)
  exact @exists_small_orbit_aux K _ _ σ A hchar hσ m hK hA hA1 hlin hiso

end CFSG.ClassicalGroups.Unitary

end

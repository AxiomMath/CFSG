module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6Rigidity
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEInnerRoots
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4Inner

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem exists_eq_mul_conj_inv_of_fixedPointFree {G : Type*} [Group G] {A : Subgroup G}
    [Finite A] {h : G} (hA : ∀ v ∈ A, h * v * h⁻¹ ∈ A)
    (hfree : ∀ v ∈ A, h * v * h⁻¹ = v → v = 1) {a : G} (ha : a ∈ A) :
    ∃ v ∈ A, a = h * v * h⁻¹ * v⁻¹ := by
  let f : A → A := fun v => ⟨h * v * h⁻¹ * (v : G)⁻¹, mul_mem (hA v v.2) (inv_mem v.2)⟩
  have hinj : Function.Injective f := by
    intro v w hvw
    have e := congrArg Subtype.val hvw
    simp only [f] at e
    have hfix : h * ((w : G)⁻¹ * v) * h⁻¹ = (w : G)⁻¹ * v := by
      calc h * ((w : G)⁻¹ * v) * h⁻¹ = (h * (w : G) * h⁻¹)⁻¹ * (h * v * h⁻¹) := by group
        _ = (w : G)⁻¹ * v := by
          rw [show h * (v : G) * h⁻¹ = h * w * h⁻¹ * (w : G)⁻¹ * v by
            rw [← e]; group]
          group
    have h1 := hfree _ (mul_mem (inv_mem w.2) v.2) hfix
    exact Subtype.ext (inv_mul_eq_one.1 h1).symm
  obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨a, ha⟩
  exact ⟨v, v.2, (congrArg Subtype.val hv).symm⟩

variable {K : Type} [Field K]

theorem mem_rootSpan_of_rootDiagUnit_conj_eq
    {τ : Tag} {S : Set (Fin τ.rank → ℤ)} (hS : ∀ β ∈ S, IsRoot τ β ∧ 0 < height β)
    (hSc : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S)
    {B : Set (Fin τ.rank → Kˣ)} {v : ModGL τ K} (hv : v ∈ rootSpan τ K S)
    (hfix : ∀ b ∈ B, rootDiagUnit τ b * v * (rootDiagUnit τ b)⁻¹ = v) :
    v ∈ rootSpan τ K {β | β ∈ S ∧ ∀ b ∈ B, rootChar b β = 1} := by
  obtain ⟨m, γ, hγ⟩ := ((finite_setOf_isRoot τ).subset fun β hβ => (hS β hβ).1).fin_embedding
  have hγS : ∀ i, γ i ∈ S := fun i => hγ ▸ Set.mem_range_self i
  have hγpos : ∀ i, IsRoot τ (γ i) ∧ 0 < height (γ i) := fun i => hS _ (hγS i)
  obtain ⟨c, -, rfl⟩ := (bijOn_prod_pinnedX K hS hSc γ γ.injective hγ).surjOn hv
  have hinj := (positive_root_product_injectivity τ K γ γ.injective hγpos).2
  have hc : ∀ i, c i ≠ 0 → ∀ b ∈ B, rootChar b (γ i) = 1 := by
    intro i hi b hb
    have h1 := hfix b hb
    rw [rootDiagUnit_conj_list_prod b γ (fun i => (hγpos i).1) c] at h1
    have h2 := congrFun (hinj h1) i
    have h3 : ((rootChar b (γ i) : K) - 1) * c i = 0 := by
      beta_reduce at h2
      linear_combination h2
    exact Units.ext (by
      rw [Units.val_one]
      exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hi))
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  by_cases hi : c i = 0
  · simp only [hi, pinnedX_zero]
    exact one_mem _
  · exact Subgroup.mem_iSup_of_mem (γ i) (Subgroup.mem_iSup_of_mem ⟨hγS i, hc i hi⟩
      (mem_rootSubgroup.2 ⟨c i, rfl⟩))

theorem odd_orderOf_rootDiagUnit_of_odd
    [Finite K] {τ : Tag} (hK : Odd (Nat.card Kˣ)) (b : Fin τ.rank → Kˣ) :
    Odd (orderOf (rootDiagUnit τ b)) := by
  have hodd : Odd (Nat.card (Fin τ.rank → Kˣ)) := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin τ.rank), Fintype.card_fin]
    exact hK.pow
  exact hodd.of_dvd_nat ((orderOf_map_dvd (rootDiagUnitHom τ K) b).trans (orderOf_dvd_natCard b))

theorem twistHom_pinnedX_eq_of_charTwo
    {t : TwistTag}
    (h2 : (2 : K) = 0) (σ : K →+* K) {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α) (c : K) :
    twistHom t K σ (pinnedX t.tag K α c) = pinnedX t.tag K (permLattice t.perm α) (σ c) := by
  obtain ⟨ε, hε, h⟩ := diagramMap_conj_pinnedX (K := K) t hα
  have hσ : Units.map (entrywiseHom σ) (pinnedX t.tag K α c) = pinnedX t.tag K α (σ c) :=
    Units.ext (entrywise_pinnedX σ α c)
  rw [twistHom_apply, hσ, h, eq_one_of_mul_self_eq_one_of_two_eq_zero h2 hε, one_mul]

@[expose] def twistedE6TorusTuple (σ : K →+* K) (i : Fin TwistTag.E6.tag.rank) (u : Kˣ) :
    Fin TwistTag.E6.tag.rank → Kˣ :=
  fun j => u ^ TwistTag.E6.tag.cartan i j *
    Units.map σ.toMonoidHom u ^ TwistTag.E6.tag.cartan (TwistTag.E6.perm i) j

theorem rootChar_twistedE6TorusTuple (σ : K →+* K) (i : Fin TwistTag.E6.tag.rank) (u : Kˣ)
    (γ : Fin TwistTag.E6.tag.rank → ℤ) :
    rootChar (twistedE6TorusTuple σ i u) γ = u ^ coPair TwistTag.E6.tag i γ *
      Units.map σ.toMonoidHom u ^ coPair TwistTag.E6.tag (TwistTag.E6.perm i) γ := by
  simp only [rootChar, twistedE6TorusTuple, mul_zpow, Finset.prod_mul_distrib, coPair,
    ← zpow_mul]
  rw [prod_zpow_eq_zpow_sum, prod_zpow_eq_zpow_sum]

theorem rootDiagUnit_twistedE6TorusTuple
    (σ : K →+* K) (i : Fin TwistTag.E6.tag.rank)
    (u : Kˣ) :
    rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σ i u) =
      torusElt TwistTag.E6.tag K i u *
        torusElt TwistTag.E6.tag K (TwistTag.E6.perm i) (Units.map σ.toMonoidHom u) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  rfl


@[expose] def twistedE6RootCheck : Bool :=
  (List.range Tag.E6.rootCertificate.roots.length).all fun k =>
    ((List.finRange 6).all fun j =>
      decide (|coPair Tag.E6 j (Tag.E6.rootCertificate.root k)| ≤ 2)) &&
    (decide (height (Tag.E6.rootCertificate.root k) ≤ 0) ||
      (List.ofFn (Tag.E6.rootCertificate.root k) == List.ofFn (highRoot Tag.E6)) ||
      (([0, 2, 3] : List (Fin 6)).any fun i =>
        (decide (coPair Tag.E6 i (Tag.E6.rootCertificate.root k) ≠ 0) ||
          decide (coPair Tag.E6 (TwistTag.E6.perm i) (Tag.E6.rootCertificate.root k) ≠ 0)) &&
        (decide (coPair Tag.E6 i (permLattice TwistTag.E6.perm
            (Tag.E6.rootCertificate.root k)) ≠ 0) ||
          decide (coPair Tag.E6 (TwistTag.E6.perm i) (permLattice TwistTag.E6.perm
            (Tag.E6.rootCertificate.root k)) ≠ 0))))

theorem twistedE6RootCheck_eq_true : twistedE6RootCheck = true := by decide +kernel

theorem e6HighestRoot_eq_highRoot : e6HighestRoot = highRoot Tag.E6 := rfl

theorem abs_coPair_le_two_E6 {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (j : Fin TwistTag.E6.tag.rank) :
    |coPair TwistTag.E6.tag j γ| ≤ 2 := by
  have h := twistedE6RootCheck_eq_true
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq Tag.E6.rootCertificate_check hγ
  simp only [twistedE6RootCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    List.mem_finRange, decide_eq_true_eq, true_implies] at h
  exact (h k hk).1 j

theorem exists_twistedE6TorusIndex
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) (hpos : 0 < height γ)
    (hne : γ ≠ e6HighestRoot) :
    ∃ i ∈ ([⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩] : List (Fin TwistTag.E6.tag.rank)),
      (coPair TwistTag.E6.tag i γ ≠ 0 ∨ coPair TwistTag.E6.tag (TwistTag.E6.perm i) γ ≠ 0) ∧
      (coPair TwistTag.E6.tag i (permLattice TwistTag.E6.perm γ) ≠ 0 ∨
        coPair TwistTag.E6.tag (TwistTag.E6.perm i) (permLattice TwistTag.E6.perm γ) ≠ 0) := by
  have h := twistedE6RootCheck_eq_true
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq Tag.E6.rootCertificate_check hγ
  simp only [twistedE6RootCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  rcases (h k hk).2 with (h1 | h2) | ⟨i, hi, hγi⟩
  · exact absurd h1 (not_le.2 hpos)
  · exact absurd ((RootCertificate.eq_of_ofFn_beq h2).trans e6HighestRoot_eq_highRoot.symm) hne
  · exact ⟨i, hi, hγi⟩

theorem coPair_e6HighestRoot {j : Fin TwistTag.E6.tag.rank} (hj : j ≠ ⟨1, by decide⟩) :
    coPair TwistTag.E6.tag j e6HighestRoot = 0 := by
  revert j
  decide

theorem zpow_mul_pow_zpow_ne_one {q : ℕ} (hq : 4 ≤ q) {ζ : Kˣ} (hζ : orderOf ζ = q ^ 2 - 1)
    {m m' : ℤ} (hm : |m| ≤ 2) (hm' : |m'| ≤ 2) (hne : m ≠ 0 ∨ m' ≠ 0) :
    ζ ^ m * (ζ ^ q) ^ m' ≠ 1 := by
  rw [← zpow_natCast, ← zpow_mul, ← zpow_add]
  intro h
  have hd := orderOf_dvd_iff_zpow_eq_one.2 h
  rw [hζ] at hd
  have hq2 : ((q ^ 2 - 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - 1 := by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    push_cast [this]
    ring
  rw [hq2] at hd
  have hq' : (4 : ℤ) ≤ q := by exact_mod_cast hq
  rw [abs_le] at hm hm'
  have habs : |m + (q : ℤ) * m'| < (q : ℤ) ^ 2 - 1 := by
    rw [abs_lt]
    constructor <;> nlinarith
  have h0 := Int.eq_zero_of_abs_lt_dvd hd habs
  rcases hne with hne | hne
  · by_cases hm0 : m' = 0
    · rw [hm0, mul_zero, add_zero] at h0
      exact hne h0
    · have : (q : ℤ) ≤ |(q : ℤ) * m'| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ q)]
        exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hm0)
      have h1 : (q : ℤ) * m' = -m := by linarith
      rw [h1, abs_neg] at this
      have := abs_le.2 hm
      linarith
  · have : (q : ℤ) ≤ |(q : ℤ) * m'| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ q)]
      exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hne)
    have h1 : (q : ℤ) * m' = -m := by linarith
    rw [h1, abs_neg] at this
    have := abs_le.2 hm
    linarith


theorem coe_orbitH_of_card_two (σ : K →+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (ha : (TwistTag.E6.orbit a).card = 2) (u : (orbitField TwistTag.E6 K σ a)ˣ) :
    (orbitH TwistTag.E6 K σ a u : ModGL TwistTag.E6.tag K) =
      torusElt TwistTag.E6.tag K (TwistTag.E6.orbitMin a)
          (Units.map (orbitField TwistTag.E6 K σ a).subtype.toMonoidHom u) *
        torusElt TwistTag.E6.tag K (TwistTag.E6.perm (TwistTag.E6.orbitMin a))
          (Units.map (σ.comp (orbitField TwistTag.E6 K σ a).subtype).toMonoidHom u) := by
  rw [coe_orbitH, ha, show List.range 2 = [0, 1] from rfl]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero,
    pow_one, Equiv.Perm.one_apply, RingHom.one_def, RingHom.id_comp]

theorem coe_orbitH_of_card_one (σ : K →+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (ha : (TwistTag.E6.orbit a).card = 1) (u : (orbitField TwistTag.E6 K σ a)ˣ) :
    (orbitH TwistTag.E6 K σ a u : ModGL TwistTag.E6.tag K) =
      torusElt TwistTag.E6.tag K (TwistTag.E6.orbitMin a)
          (Units.map (orbitField TwistTag.E6 K σ a).subtype.toMonoidHom u) := by
  rw [coe_orbitH, ha, show List.range 1 = [0] from rfl]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero,
    Equiv.Perm.one_apply, RingHom.one_def, RingHom.id_comp]

theorem rootDiagUnit_twistedE6TorusTuple_mem (σ : K ≃+* K) (hσ : σ ^ TwistTag.E6.order = 1)
    {i : Fin TwistTag.E6.tag.rank} (hi : i = ⟨0, by decide⟩ ∨ i = ⟨2, by decide⟩ ∨
      i = ⟨3, by decide⟩) (u : Kˣ) :
    rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σ.toRingHom i u) ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
  have hσσ : ∀ x : K, σ (σ x) = x := fun x => by
    have h := congrArg (fun f : K ≃+* K => f x) hσ
    simpa [TwistTag.order, pow_two] using h
  rw [rootDiagUnit_twistedE6TorusTuple]
  have hcard2 : ∀ a : Fin TwistTag.E6.foldedTag.rank, (TwistTag.E6.orbit a).card = 2 →
      ∀ x : K, x ∈ orbitField TwistTag.E6 K σ.toRingHom a := fun a ha x => by
    rw [mem_orbitField, ha, pow_two]
    exact hσσ x
  rcases hi with rfl | rfl | rfl
  ·
    have hfull := hcard2 ⟨0, by decide⟩ (by decide)
    have hu0 : (⟨(u : K), hfull _⟩ : orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩) ≠ 0 :=
      fun h => u.ne_zero (congrArg Subtype.val h)
    have hm := orbitH_mem_graphFixedRootGroup TwistTag.E6 σ.toRingHom ⟨0, by decide⟩
      (Units.mk0 _ hu0)
    rw [coe_orbitH_of_card_two σ.toRingHom ⟨0, by decide⟩ (by decide),
      show TwistTag.E6.orbitMin ⟨0, by decide⟩ = ⟨0, by decide⟩ by decide] at hm
    convert hm using 3 <;> exact Units.ext rfl
  ·
    have hfull := hcard2 ⟨1, by decide⟩ (by decide)
    have hu0 : (⟨(u : K), hfull _⟩ : orbitField TwistTag.E6 K σ.toRingHom ⟨1, by decide⟩) ≠ 0 :=
      fun h => u.ne_zero (congrArg Subtype.val h)
    have hm := orbitH_mem_graphFixedRootGroup TwistTag.E6 σ.toRingHom ⟨1, by decide⟩
      (Units.mk0 _ hu0)
    rw [coe_orbitH_of_card_two σ.toRingHom ⟨1, by decide⟩ (by decide),
      show TwistTag.E6.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ by decide] at hm
    convert hm using 3 <;> exact Units.ext rfl
  ·
    have hmem : (u : K) * σ u ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨2, by decide⟩ := by
      rw [mem_orbitField, show (TwistTag.E6.orbit ⟨2, by decide⟩).card = 1 by decide, pow_one]
      change σ ((u : K) * σ u) = (u : K) * σ u
      rw [map_mul, hσσ, mul_comm]
    have hu0 : (⟨(u : K) * σ u, hmem⟩ :
        orbitField TwistTag.E6 K σ.toRingHom ⟨2, by decide⟩) ≠ 0 := fun h =>
      mul_ne_zero u.ne_zero ((map_ne_zero σ).2 u.ne_zero) (congrArg Subtype.val h)
    have hm := orbitH_mem_graphFixedRootGroup TwistTag.E6 σ.toRingHom ⟨2, by decide⟩
      (Units.mk0 _ hu0)
    rw [coe_orbitH_of_card_one σ.toRingHom ⟨2, by decide⟩ (by decide),
      show TwistTag.E6.orbitMin ⟨2, by decide⟩ = ⟨3, by decide⟩ by decide] at hm
    have e : torusElt TwistTag.E6.tag K ⟨3, by decide⟩ u *
        torusElt TwistTag.E6.tag K (TwistTag.E6.perm ⟨3, by decide⟩)
          (Units.map σ.toRingHom.toMonoidHom u) =
        torusElt TwistTag.E6.tag K ⟨3, by decide⟩ (u * Units.map σ.toRingHom.toMonoidHom u) := by
      rw [show TwistTag.E6.perm ⟨3, by decide⟩ = ⟨3, by decide⟩ by decide,
        torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
        ← rootDiagUnit_mul]
      congr 1
      funext j
      rw [Pi.mul_apply, mul_zpow]
    rw [e]
    convert hm using 2
    exact Units.ext rfl

theorem exists_twistedE6Torus {f : ℕ} (hf : 2 ≤ f) [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (hpos : 0 < height γ) (hne : γ ≠ e6HighestRoot) :
    ∃ b : Fin TwistTag.E6.tag.rank → Kˣ,
      rootDiagUnit TwistTag.E6.tag b ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom ∧
      rootChar b e6HighestRoot = 1 ∧ rootChar b γ ≠ 1 ∧
      rootChar b (permLattice TwistTag.E6.perm γ) ≠ 1 := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units, hK] at hζ
  have hq : 4 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  have hσζ : Units.map σ.toRingHom.toMonoidHom ζ = ζ ^ (2 ^ f) := Units.ext (by
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    exact hσ ζ)
  obtain ⟨i, hi, hγi, hργi⟩ := exists_twistedE6TorusIndex hγ hpos hne
  have hi' : i = ⟨0, by decide⟩ ∨ i = ⟨2, by decide⟩ ∨ i = ⟨3, by decide⟩ := by
    simpa using hi
  have hργ : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm γ) :=
    hγ.permLattice TwistTag.E6.cartan_perm
  refine ⟨twistedE6TorusTuple σ.toRingHom i ζ, rootDiagUnit_twistedE6TorusTuple_mem σ
    (twistedE6_sigma_pow_order hK hσ) hi' ζ, ?_, ?_, ?_⟩
  · have h1 : i ≠ ⟨1, by decide⟩ := by rcases hi' with rfl | rfl | rfl <;> decide
    have h2 : TwistTag.E6.perm i ≠ ⟨1, by decide⟩ := by
      rcases hi' with rfl | rfl | rfl <;> decide
    rw [rootChar_twistedE6TorusTuple, coPair_e6HighestRoot h1, coPair_e6HighestRoot h2,
      zpow_zero, zpow_zero, mul_one]
  · rw [rootChar_twistedE6TorusTuple, hσζ]
    exact zpow_mul_pow_zpow_ne_one hq hζ (abs_coPair_le_two_E6 hγ _)
      (abs_coPair_le_two_E6 hγ _) hγi
  · rw [rootChar_twistedE6TorusTuple, hσζ]
    exact zpow_mul_pow_zpow_ne_one hq hζ (abs_coPair_le_two_E6 hργ _)
      (abs_coPair_le_two_E6 hργ _) hργi

end CFSG.SeitzReduction

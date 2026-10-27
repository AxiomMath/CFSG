module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6YWeyl
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6X

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint

local instance twistedE6PilotHR6YMainNeZero : NeZero Tag.E6.rank := ⟨by decide⟩

section Defs

variable {K : Type} [Field K]

@[expose] noncomputable def shortRootTorus {k : Type} [Field k] (ι : k →+* K) :
    Subgroup (ModGL TwistTag.E6.tag K) :=
  w1Torus ι

theorem mem_shortRootTorus {k : Type} [Field k] {ι : k →+* K} {g : ModGL TwistTag.E6.tag K} :
    g ∈ shortRootTorus ι ↔ ∃ l : kˣ, rootDiagUnit Tag.E6
      (d4CentralDiag (Units.map ι.toMonoidHom l) (Units.map ι.toMonoidHom l)) = g :=
  Iff.rfl

@[expose] noncomputable def w1Complement (σ : K →+* K) : Subgroup (ModGL TwistTag.E6.tag K) :=
  d4CentralTorus K ⊓ graphFixedRootGroup TwistTag.E6 K σ

theorem w1Complement_le_C0 (σ : K →+* K) :
    w1Complement σ ≤ graphFixedRootGroup TwistTag.E6 K σ :=
  inf_le_right

end Defs


section W1

variable {K : Type} [Field K]

@[expose] def shortVT : Fin TwistTag.E6.tag.rank → ℤ := (![2, 2, 3, 4, 3, 2] : Fin 6 → ℤ)

theorem shortV_cartan_check : permLattice TwistTag.E6.perm shortVT = shortVT ∧
    ∀ l : Fin Tag.E6.rank, ∑ j, shortV j * Tag.E6.cartan j l = centralExp 1 1 l := by
  decide

theorem frameTorusElt_shortV_eq (a : Kˣ) :
    frameTorusElt Tag.E6 K shortV a = rootDiagUnit Tag.E6 (d4CentralDiag a a) := by
  have hs : ∀ i : Fin Tag.E6.rank, Tag.E6.symmetrizer i i = 1 := by decide
  rw [frameTorusElt]
  simp only [hs, one_mul]
  rw [list_prod_torusElt_eq_rootDiagUnit, cartanChar_zpow',
    show d4CentralDiag a a = d4CentralDiag (a ^ (1 : ℤ)) (a ^ (1 : ℤ)) by rw [zpow_one],
    d4CentralDiag_zpow]
  congr 1
  funext l
  rw [shortV_cartan_check.2 l]

theorem shortRootTorus_le_C0 {k : Type} [Field k] {ι : k →+* K} {σ : K →+* K}
    (hσι : ∀ c, σ (ι c) = ι c) :
    shortRootTorus ι ≤ graphFixedRootGroup TwistTag.E6 K σ := by
  rintro _ ⟨l, rfl⟩
  change rootDiagUnit Tag.E6 (d4CentralDiag (Units.map ι.toMonoidHom l)
    (Units.map ι.toMonoidHom l)) ∈ graphFixedRootGroup TwistTag.E6 K σ
  rw [← frameTorusElt_shortV_eq]
  exact frameTorusElt_mem_graphFixedRootGroup σ (γ := shortVT) shortV_cartan_check.1
    (Units.ext (hσι _))

end W1

section Main

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem pow_card_units_eq_one_of_mem_d4CentralTorus [Finite K] {z : ModGL Tag.E6 K}
    (hz : z ∈ d4CentralTorus K) : z ^ Nat.card Kˣ = 1 := by
  obtain ⟨μ, ν, rfl⟩ := mem_d4CentralTorus.1 hz
  have h1 : (μ, ν) ^ Nat.card Kˣ = 1 := Prod.ext (by simp [pow_card_eq_one'])
    (by simp [pow_card_eq_one'])
  change (rootDiagUnitHom Tag.E6 K (d4CentralHom K (μ, ν))) ^ Nat.card Kˣ = 1
  rw [← map_pow, ← map_pow, h1, map_one, map_one]

theorem twistHom_eq_and_eq_of_mul {t : TwistTag} {σ : K →+* K} {A B : Subgroup (ModGL t.tag K)}
    (hAB : A ⊓ B = ⊥) {z l g : ModGL t.tag K} (hz : z ∈ A) (hl : l ∈ B)
    (hFz : twistHom t K σ z ∈ A) (hFl : twistHom t K σ l ∈ B) (hg : g = z * l)
    (hFg : twistHom t K σ g = g) : twistHom t K σ z = z ∧ twistHom t K σ l = l := by
  have h2 : twistHom t K σ z * twistHom t K σ l = z * l := by rw [← map_mul, ← hg, hFg, hg]
  have h1 : (twistHom t K σ z)⁻¹ * z = twistHom t K σ l * l⁻¹ := by
    calc (twistHom t K σ z)⁻¹ * z = (twistHom t K σ z)⁻¹ * (z * l) * l⁻¹ := by group
      _ = (twistHom t K σ z)⁻¹ * (twistHom t K σ z * twistHom t K σ l) * l⁻¹ := by rw [h2]
      _ = twistHom t K σ l * l⁻¹ := by group
  have hA : (twistHom t K σ z)⁻¹ * z ∈ A := mul_mem (inv_mem hFz) hz
  have hB : (twistHom t K σ z)⁻¹ * z ∈ B := by
    rw [h1]
    exact mul_mem hFl (inv_mem hl)
  have h0 : (twistHom t K σ z)⁻¹ * z = 1 := by
    have := mem_inf.2 ⟨hA, hB⟩
    rwa [hAB, mem_bot] at this
  rw [h0] at h1
  exact ⟨inv_mul_eq_one.1 h0, mul_inv_eq_one.1 h1.symm⟩

theorem centralizer_w1Torus_inf_eq (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    centralizer (shortRootTorus (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) ⊓
          graphFixedRootGroup TwistTag.E6 K σ =
        w1Complement σ ⊔ omegaMinusLevi σ ∧
      w1Complement σ ≤ centralizer (omegaMinusLevi σ : Set (ModGL TwistTag.E6.tag K)) ∧
      Disjoint (w1Complement σ) (omegaMinusLevi σ) ∧
      ¬ 2 ∣ Nat.card (w1Complement σ) ∧
      shortRootTorus (algebraMap k K) ≤ w1Complement σ := by
  have hf : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite K := finite_of_card hK
  have : CharP K 2 := charP_two_of_card hf hK
  have hK2 : (2 : K) = 0 := E6GraphLevi.two_eq_zero_of_card_sq hf hK
  have hσι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c :=
    E6GraphLevi.fixed_algebraMap (sigma_eq_pow_card hk hσ)
  have : IsSimpleGroup (subsystemGroup Tag.E6 K setD) := isSimpleGroup_d4Levi (K := K)
  have : Group.IsPerfect (subsystemGroup Tag.E6 K setD) := isPerfect_d4Levi (K := K)
  have hZD : d4CentralTorus K ⊓ subsystemGroup Tag.E6 K setD = ⊥ := d4CentralTorus_inf_d4Levi
  have hZc : d4CentralTorus K ≤
      centralizer (subsystemGroup Tag.E6 K setD : Set (ModGL Tag.E6 K)) :=
    d4CentralTorus_le_centralizer
  have hZcomm : ∀ z ∈ d4CentralTorus K, ∀ z' ∈ d4CentralTorus K, z * z' = z' * z := by
    intro z hz z' hz'
    obtain ⟨μ, ν, rfl⟩ := mem_d4CentralTorus.1 hz
    obtain ⟨μ', ν', rfl⟩ := mem_d4CentralTorus.1 hz'
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have hL : omegaMinusLevi σ =
      subsystemGroup TwistTag.E6.tag K setD ⊓ twistedFixedGroup TwistTag.E6 K σ :=
    omegaMinusLevi_eq_of_card hf hK hσ
  have hLD : omegaMinusLevi σ ≤ subsystemGroup Tag.E6 K setD := inf_le_left
  have hLC : omegaMinusLevi σ ≤ graphFixedRootGroup TwistTag.E6 K σ :=
    omegaMinusLevi_le_graphFixedRootGroup σ
  have hYc : w1Complement σ ≤ centralizer (omegaMinusLevi σ : Set (ModGL TwistTag.E6.tag K)) :=
    fun z hz => mem_centralizer_iff.2 fun l hl => mem_centralizer_iff.1 (hZc hz.1) l (hLD hl)
  have hdisj : Disjoint (w1Complement σ) (omegaMinusLevi σ) := by
    rw [disjoint_iff, eq_bot_iff]
    intro z hz
    exact (eq_bot_iff.1 hZD) (mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hz).1).1, hLD (mem_inf.1 hz).2⟩)
  have hodd : ¬ 2 ∣ Nat.card (w1Complement σ) := by
    intro h2
    have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hpow : (y : ModGL TwistTag.E6.tag K) ^ Nat.card Kˣ = 1 :=
      pow_card_units_eq_one_of_mem_d4CentralTorus (mem_inf.1 y.2).1
    have hdvd : orderOf y ∣ Nat.card Kˣ := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hpow
    rw [hy, Nat.card_units, hK] at hdvd
    have h2f : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    have h1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega
  have hW1C : shortRootTorus (algebraMap k K) ≤ graphFixedRootGroup TwistTag.E6 K σ :=
    shortRootTorus_le_C0 hσι
  have hW1Z : shortRootTorus (algebraMap k K) ≤ d4CentralTorus K :=
    w1Torus_le_d4CentralTorus _
  have hmain : ∀ g : ModGL Tag.E6 K,
      g ∈ (graphFixedRootGroup TwistTag.E6 K σ : Subgroup (ModGL Tag.E6 K)) →
      (∀ d : ModGL Tag.E6 K, d ∈ shortRootTorus (algebraMap k K) → d * g = g * d) →
      g ∈ (w1Complement σ ⊔ omegaMinusLevi σ : Subgroup (ModGL Tag.E6 K)) := by
    intro g hgC hgc
    have hq : 4 ≤ Nat.card k := by
      rw [hk]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    obtain ⟨c, hc⟩ := F4Pilot.exists_three_le_orderOf hq
    have hμ : 3 ≤ orderOf (Units.map (algebraMap k K).toMonoidHom c) := by
      rw [orderOf_injective _ (Units.map_injective (algebraMap k K).injective) c]
      exact hc
    have hdW : rootDiagUnit Tag.E6 (d4CentralDiag (Units.map (algebraMap k K).toMonoidHom c)
        (Units.map (algebraMap k K).toMonoidHom c)) ∈ shortRootTorus (algebraMap k K) :=
      ⟨c, rfl⟩
    have hgA : g ∈ adjointGroup Tag.E6 K := (graphFixedRootGroup_le _ _ _ hgC).1
    have hgF : twistHom TwistTag.E6 K σ g = g :=
      ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ hgC)).2
    have hgT : g ∈ toralCentralizer .E6 K (d4CentralDiag (Units.map (algebraMap k K).toMonoidHom c)
        (Units.map (algebraMap k K).toMonoidHom c)) := by
      refine mem_toralCentralizer.2 ⟨hgA, ?_⟩
      rw [hgc _ hdW, mul_inv_cancel_right]
    have hgM := mem_toralRootGroup_of_twistHom_eq hf2 hK hσ hμ hgT hgF
    have hMle : toralRootGroup .E6 K (d4CentralDiag (Units.map (algebraMap k K).toMonoidHom c)
        (Units.map (algebraMap k K).toMonoidHom c)) ≤
          d4CentralTorus K ⊔ subsystemGroup Tag.E6 K setD := by
      refine sup_le (torusGroup_le_d4CentralTorus_sup (E6GraphLevi.exists_sq_eq_of_two hK2)) ?_
      rw [rootCharKernel_w1Diag hμ]
      exact (subsystemGroup_eq_rootSpan (τ := Tag.E6) (K := K) setD).symm.le.trans le_sup_right
    obtain ⟨⟨z, l⟩, ⟨hz, hl, hzl⟩, -⟩ := E6GraphLevi.existsUnique_mul_of_commute hZD
      (fun z hz l hl => (mem_centralizer_iff.1 (hZc hz) l hl).symm) g (hMle hgM)
    dsimp only at hz hl hzl
    have hfix := twistHom_eq_and_eq_of_mul (t := TwistTag.E6) (σ := σ) hZD hz hl
      (twistHom_mem_d4CentralTorus σ hz) (d4F_mem_d4Levi σ hl) hzl hgF
    have hlL : l ∈ omegaMinusLevi σ := by
      rw [hL]
      exact ⟨hl, (mem_twistedFixedGroup_iff_twistHom _ _ _).2
        ⟨d4Levi_le_adjointGroup hl, hfix.2⟩⟩
    have hzY : z ∈ w1Complement σ := by
      have e : z = g * l⁻¹ := by rw [hzl, mul_inv_cancel_right]
      have hzC : z ∈ graphFixedRootGroup TwistTag.E6 K σ := by
        rw [e]
        exact Subgroup.mul_mem _ hgC (Subgroup.inv_mem _ (hLC hlL))
      exact Subgroup.mem_inf.2 ⟨hz, hzC⟩
    rw [hzl]
    exact mul_mem_sup hzY hlL
  refine ⟨le_antisymm (fun g hg => hmain g (mem_inf.1 hg).2
    fun d hd => mem_centralizer_iff.1 (mem_inf.1 hg).1 d hd) ?_, hYc, hdisj, hodd,
    le_inf hW1Z hW1C⟩
  · refine sup_le (le_inf (fun z hz => mem_centralizer_iff.2 fun d hd =>
      hZcomm d (hW1Z hd) z (mem_inf.1 hz).1) inf_le_right)
      (le_inf (fun l hl => mem_centralizer_iff.2 fun d hd =>
        (mem_centralizer_iff.1 (hZc (hW1Z hd)) l (hLD hl)).symm) hLC)

end Main

section RootTorus

variable {K : Type} [Field K]

@[expose] def shortRootU : Fin Tag.E6.rank → ℤ := (![1, 1, 1, 2, 2, 1] : Fin 6 → ℤ)

@[expose] def shortRootU' : Fin Tag.E6.rank → ℤ := (![1, 1, 2, 2, 1, 1] : Fin 6 → ℤ)

theorem shortRootU_eq : (shortRootU : Fin TwistTag.E6.tag.rank → ℤ) = twistedE6ClassRootU := rfl

theorem shortRootU'_eq : (shortRootU' : Fin TwistTag.E6.tag.rank → ℤ) = twistedE6ClassRootU' :=
  rfl

theorem shortRoots_check :
    shortRootU ∈ rootFinset .E6 ∧ shortRootU' ∈ rootFinset .E6 ∧
      iform shortRootU shortRootU = 2 ∧ iform shortRootU' shortRootU' = 2 ∧
      shortRootU + shortRootU' = shortV := by
  decide +kernel

theorem rootTorusSL2_mul_rootTorusSL2_eq [CharP K 2] (c : Kˣ) :
    rootTorusSL2 Tag.E6 K shortRootU c * rootTorusSL2 Tag.E6 K shortRootU' c =
      rootDiagUnit Tag.E6 (d4CentralDiag c c) := by
  obtain ⟨hU, hU', n1, n2, hsum⟩ := shortRoots_check
  replace hU := mem_rootFinset.1 hU
  replace hU' := mem_rootFinset.1 hU'
  obtain ⟨-, -, -, -, -, -, hvU, -⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps Tag.E6 K hU
  obtain ⟨-, -, -, -, -, -, hvU', -⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps Tag.E6 K hU'
  obtain ⟨hhU, hrU⟩ := hvU c
  obtain ⟨hhU', hrU'⟩ := hvU' c
  refine Units.ext (rootModule_end_ext (fun j => ?_) fun δ hδ => ?_)
  · simp only [Units.val_mul, Module.End.mul_apply]
    rw [hhU', hhU]
    exact (rootDiag_hVec _ j).symm
  · simp only [Units.val_mul, Module.End.mul_apply]
    rw [hrU' δ hδ, map_smul, hrU δ hδ, smul_smul]
    change _ = rootDiag (d4CentralDiag c c) (rootVec Tag.E6 K δ)
    rw [rootDiag_rootVec _ hδ, rootChar_d4CentralDiag]
    congr 1
    have h1 : 2 * iform shortRootU δ / iform shortRootU shortRootU = iform shortRootU δ := by
      rw [n1]; omega
    have h2 : 2 * iform shortRootU' δ / iform shortRootU' shortRootU' = iform shortRootU' δ := by
      rw [n2]; omega
    have h3 : iform shortRootU δ + iform shortRootU' δ = δ 0 + δ 5 := by
      rw [← iform_add_left, hsum]
      exact shortV_check.1 δ (mem_rootFinset.2 hδ)
    rw [h1, h2, ← Units.val_mul, ← zpow_add, ← zpow_add, add_comm, h3]

end RootTorus

section Complement

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem centralizer_omegaMinusLevi_inf_eq (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    centralizer (omegaMinusLevi σ : Set (ModGL TwistTag.E6.tag K)) ⊓
        (centralizer (shortRootTorus (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) ⊓
          graphFixedRootGroup TwistTag.E6 K σ) = w1Complement σ := by
  have hf : 1 ≤ f := by omega
  obtain ⟨hC, hYc, hdisj, -, -⟩ := centralizer_w1Torus_inf_eq hf2 hk hK hσ
  rw [hC]
  refine le_antisymm (fun g hg => ?_) (le_inf hYc le_sup_left)
  obtain ⟨hgc, hgYL⟩ := mem_inf.1 hg
  obtain ⟨⟨y, l⟩, ⟨hy, hl, rfl⟩, -⟩ := E6GraphLevi.existsUnique_mul_of_commute
    (disjoint_iff.1 hdisj) (fun y hy l hl => (mem_centralizer_iff.1 (hYc hy) l hl).symm) g hgYL
  dsimp only at hy hl ⊢
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  have hσσ : ∀ c, σE (σE c) = c := apply_apply_eq hK hσ
  obtain ⟨ω, hω⟩ := exists_apply_ne hf hK hσ
  have : IsSimpleGroup (omegaMinusLevi σE.toRingHom) := isSimpleGroup_omegaMinusLevi hf hK hσ
  have : Group.IsPerfect (omegaMinusLevi σE.toRingHom) := by
    have hP : Group.IsPerfect ↥(subsystemGroup TwistTag.E6.tag K setD ⊓
        twistedFixedGroup TwistTag.E6 K (σE : K →+* K)) := isPerfect_d4Fixed hσσ (ω := ω) hω
    exact Group.IsPerfect.ofSurjective (f := (MulEquiv.subgroupCongr
      (omegaMinusLevi_eq hσσ (ω := ω) hω).symm).toMonoidHom) (MulEquiv.surjective _)
  have hlc : (⟨l, hl⟩ : omegaMinusLevi σE.toRingHom) ∈ center (omegaMinusLevi σE.toRingHom) := by
    rw [mem_center_iff]
    intro m
    refine Subtype.ext ?_
    have h1 := mem_centralizer_iff.1 hgc m m.2
    have h2 := mem_centralizer_iff.1 (hYc hy) m m.2
    change (m : ModGL TwistTag.E6.tag K) * l = l * m
    have e : y * ((m : ModGL TwistTag.E6.tag K) * l) = y * (l * m) := by
      calc y * ((m : ModGL TwistTag.E6.tag K) * l) = (y * m) * l := by group
        _ = (m * y) * l := by rw [h2]
        _ = m * (y * l) := by group
        _ = (y * l) * m := h1
        _ = y * (l * m) := by group
    exact mul_left_cancel e
  rw [center_eq_bot_of_isSimpleGroup_of_isPerfect, mem_bot] at hlc
  have hl1 : l = 1 := congrArg Subtype.val hlc
  rw [hl1, mul_one]
  exact hy

theorem centralizer_shortTorus_inf_eq (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ Y₁ : Subgroup (ModGL TwistTag.E6.tag K),
      centralizer (shortRootTorus (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) ⊓
          graphFixedRootGroup TwistTag.E6 K σ = Y₁ ⊔ omegaMinusLevi σ ∧
        Y₁ ≤ centralizer (omegaMinusLevi σ : Set (ModGL TwistTag.E6.tag K)) ∧
        Disjoint Y₁ (omegaMinusLevi σ) ∧ ¬ 2 ∣ Nat.card Y₁ ∧
        Y₁ ≤ graphFixedRootGroup TwistTag.E6 K σ := by
  obtain ⟨hC, hYc, hdisj, hodd, -⟩ := centralizer_w1Torus_inf_eq hf2 hk hK hσ
  exact ⟨w1Complement σ, hC, hYc, hdisj, hodd, w1Complement_le_C0 σ⟩

end Complement

end CFSG.SeitzReduction.TwistedE6Pilot

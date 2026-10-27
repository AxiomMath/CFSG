module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesNatural
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups

section Numerics

theorem n_le_card_mul {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {J : Finset ℕ} (hJn : ∀ i ∈ J, i < n)
    (hJ : J.Nonempty) (hshift : J.image (fun i => (i + d) % n) = J) : n ≤ J.card * d := by
  obtain ⟨i₀, hi₀⟩ := hJ
  have : NeZero n := ⟨hn.ne'⟩
  let f : ℕ → ℕ := fun k => (i₀ + k * d) % n
  have hfJ : ∀ k, f k ∈ J := by
    intro k
    induction k with
    | zero => simp [f, Nat.mod_eq_of_lt (hJn i₀ hi₀), hi₀]
    | succ k ih =>
      have : f (k + 1) = (f k + d) % n := by
        simp only [f]
        rw [Nat.mod_add_mod]
        congr 1; ring
      rw [this]
      have hmem : (f k + d) % n ∈ J.image (fun i => (i + d) % n) :=
        Finset.mem_image_of_mem _ ih
      rwa [hshift] at hmem
  have hord : addOrderOf (d : ZMod n) = n / Nat.gcd n d := ZMod.addOrderOf_coe d hn.ne'
  have hinj : Set.InjOn f (Set.Iio (n / Nat.gcd n d)) := by
    intro k hk k' hk' h
    have h1 : ((i₀ + k * d : ℕ) : ZMod n) = ((i₀ + k' * d : ℕ) : ZMod n) := by
      have := congrArg (fun x : ℕ => (x : ZMod n)) h
      simpa [f, ZMod.natCast_mod] using this
    have h2 : k • (d : ZMod n) = k' • (d : ZMod n) := by
      have : (i₀ : ZMod n) + k • (d : ZMod n) = (i₀ : ZMod n) + k' • (d : ZMod n) := by
        simpa [nsmul_eq_mul] using h1
      exact add_left_cancel this
    exact nsmul_injOn_Iio_addOrderOf (by rw [hord]; exact hk) (by rw [hord]; exact hk') h2
  have hcard : n / Nat.gcd n d ≤ J.card := by
    have := Finset.card_le_card_of_injOn (s := Finset.range (n / Nat.gcd n d)) (t := J) f
      (fun k _ => hfJ k) (by
        intro k hk k' hk' h
        exact hinj (by simpa using hk) (by simpa using hk') h)
    simpa using this
  have hgd : Nat.gcd n d ≤ d := Nat.le_of_dvd hd (Nat.gcd_dvd_right n d)
  calc n = (n / Nat.gcd n d) * Nat.gcd n d := (Nat.div_mul_cancel (Nat.gcd_dvd_left n d)).symm
    _ ≤ J.card * d := Nat.mul_le_mul hcard hgd

theorem le_two_of_two_pow_pred_le {r : ℕ} (hr : 1 ≤ r) (h : 2 ^ (r - 1) ≤ r) : r ≤ 2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hs : 2 ≤ s := by omega
  simp only [Nat.add_sub_cancel] at h
  have key : ∀ s : ℕ, 2 ≤ s → s + 1 < 2 ^ s := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => norm_num
    | succ s hs ih => rw [pow_succ]; omega
  have := key s hs
  omega

end Numerics

section RootGroup

open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem eq_conj_rootGroup (A : Subgroup SL(2, F)) (hA : ∀ a ∈ A, a * a = 1)
    (hcard : Nat.card A = Nat.card F) :
    ∃ x : SL(2, F), ∀ g, g ∈ A ↔ x⁻¹ * g * x ∈ (upperUnipotent (F := F)).range := by
  obtain ⟨x, hx⟩ := exists_conj_le_rootGroup A hA
  refine ⟨x, fun g => ⟨fun hg => hx g hg, fun hg => ?_⟩⟩
  let f : A → (upperUnipotent (F := F)).range := fun a => ⟨x⁻¹ * a * x, hx a a.2⟩
  have hinj : Function.Injective f := by
    intro a a' h
    have := congrArg Subtype.val h
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have hcardU : Nat.card (upperUnipotent (F := F)).range ≤ Nat.card A := by
    rw [upperUnipotent_card, hcard]
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le hcardU
  obtain ⟨a, ha⟩ := hbij.2 ⟨x⁻¹ * g * x, hg⟩
  have h1 : x⁻¹ * (a : SL(2, F)) * x = x⁻¹ * g * x := congrArg Subtype.val ha
  have h2 : (a : SL(2, F)) = g := by simpa using h1
  rw [← h2]
  exact a.2

end RootGroup

section RootLine

open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

variable {F : Type*} [Field F]

theorem smul_eq_mulVec' (g : SL(2, F)) (v : Fin 2 → F) :
    g • v = (g : Matrix (Fin 2) (Fin 2) F).mulVec v := rfl

theorem coe_uElt (t : F) : ((uElt t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := rfl

theorem uElt_smul_single (t : F) : uElt t • (Pi.single 0 1 : Fin 2 → F) = Pi.single 0 1 := by
  rw [smul_eq_mulVec', coe_uElt]
  ext i
  fin_cases i <;> simp

theorem mem_rootGroup_iff (g : SL(2, F)) :
    g ∈ (upperUnipotent (F := F)).range ↔ ∃ t : F, g = uElt t := by
  rw [← sl2_fixes_first_iff]
  constructor
  · intro hh
    change Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) F) (Pi.single 0 1) = Pi.single 0 1 at hh
    rw [Matrix.mulVec_single_one] at hh
    have h00 : g 0 0 = 1 := by simpa using congrFun hh 0
    have h10 : g 1 0 = 0 := by simpa using congrFun hh 1
    have h11 : g 1 1 = 1 := by
      have hd := g.2
      simpa only [Matrix.det_fin_two, h00, h10, one_mul, mul_zero, sub_zero] using hd
    refine ⟨g 0 1, ?_⟩
    ext i j
    change g i j = (!![1, g 0 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]
  · rintro ⟨t, rfl⟩
    exact uElt_smul_single t

theorem uElt_smul_sub (t : F) (y : Fin 2 → F) :
    (uElt t) • y - y = (t * y 1) • (Pi.single 0 1 : Fin 2 → F) := by
  rw [smul_eq_mulVec', coe_uElt]
  ext i
  fin_cases i
  · simp [dotProduct, Fin.sum_univ_two]
  · simp [dotProduct, Fin.sum_univ_two]

theorem uElt_smul_eq_iff (t : F) (y : Fin 2 → F) :
    (uElt t) • y = y ↔ t * y 1 = 0 := by
  rw [← sub_eq_zero, uElt_smul_sub]
  constructor
  · intro h
    have := congrFun h 0
    simpa using this
  · intro h
    rw [h]; simp

@[expose] def rootLine (x : SL(2, F)) : Submodule F (Fin 2 → F) :=
  Submodule.span F {x • (Pi.single 0 1 : Fin 2 → F)}

theorem smul_single_ne_zero (x : SL(2, F)) : x • (Pi.single 0 1 : Fin 2 → F) ≠ 0 := by
  intro h
  have h1 : (Pi.single 0 1 : Fin 2 → F) = 0 := by
    have := congrArg (fun v => x⁻¹ • v) h
    simp at this
  have := congrFun h1 0
  simp at this

theorem finrank_rootLine (x : SL(2, F)) : Module.finrank F (rootLine x) = 1 :=
  finrank_span_singleton (smul_single_ne_zero x)

theorem smul_single_mem_rootLine (x : SL(2, F)) : x • (Pi.single 0 1 : Fin 2 → F) ∈ rootLine x :=
  Submodule.mem_span_singleton_self _

theorem conj_mem_range_iff (x g : SL(2, F)) :
    x⁻¹ * g * x ∈ (upperUnipotent (F := F)).range ↔
      g • (x • (Pi.single 0 1 : Fin 2 → F)) = x • (Pi.single 0 1 : Fin 2 → F) := by
  rw [← sl2_fixes_first_iff, mul_smul, mul_smul, inv_smul_eq_iff]

theorem fixed_of_conj_mem (x g : SL(2, F)) (h : x⁻¹ * g * x ∈ (upperUnipotent (F := F)).range)
    (v : Fin 2 → F) (hv : v ∈ rootLine x) : g • v = v := by
  have h1 := (conj_mem_range_iff x g).mp h
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [smul_eq_mulVec', Matrix.mulVec_smul, ← smul_eq_mulVec', h1]

theorem sub_mem_rootLine_of_conj (x g : SL(2, F))
    (h : x⁻¹ * g * x ∈ (upperUnipotent (F := F)).range) (v : Fin 2 → F) :
    g • v - v ∈ rootLine x := by
  obtain ⟨t, ht⟩ := (mem_rootGroup_iff _).mp h
  have hg : g = x * uElt t * x⁻¹ := by
    rw [← ht]; group
  have h2 : g • v - v = x • (uElt t • (x⁻¹ • v) - x⁻¹ • v) := by
    conv_lhs => rw [hg, mul_smul, mul_smul]
    rw [smul_eq_mulVec' x (uElt t • (x⁻¹ • v) - x⁻¹ • v), Matrix.mulVec_sub,
      ← smul_eq_mulVec', ← smul_eq_mulVec', smul_inv_smul]
  rw [h2, uElt_smul_sub, smul_eq_mulVec', Matrix.mulVec_smul, ← smul_eq_mulVec']
  exact Submodule.smul_mem _ _ (smul_single_mem_rootLine x)

theorem mem_rootLine_of_fixed (x : SL(2, F)) (v : Fin 2 → F)
    (hfix : ∀ g : SL(2, F), x⁻¹ * g * x ∈ (upperUnipotent (F := F)).range → g • v = v) :
    v ∈ rootLine x := by
  have h1 : x⁻¹ * (x * uElt 1 * x⁻¹) * x ∈ (upperUnipotent (F := F)).range :=
    (mem_rootGroup_iff _).mpr ⟨1, by group⟩
  have h2 := hfix _ h1
  have h3 : uElt (1 : F) • (x⁻¹ • v) = x⁻¹ • v := by
    rw [mul_smul, mul_smul] at h2
    have := congrArg (fun w => x⁻¹ • w) h2
    simpa [inv_smul_smul] using this
  have h4 : (x⁻¹ • v) 1 = 0 := by
    have := (uElt_smul_eq_iff (1 : F) (x⁻¹ • v)).mp h3
    simpa using this
  have h5 : x⁻¹ • v = ((x⁻¹ • v) 0) • (Pi.single 0 1 : Fin 2 → F) := by
    ext i
    fin_cases i
    · simp
    · simpa using h4
  have h6 : v = ((x⁻¹ • v) 0) • (x • (Pi.single 0 1 : Fin 2 → F)) := by
    obtain ⟨y, hy⟩ : ∃ y, y = x⁻¹ • v := ⟨_, rfl⟩
    rw [← hy] at h5 ⊢
    calc v = x • y := by rw [hy, smul_inv_smul]
      _ = x • (y 0 • (Pi.single 0 1 : Fin 2 → F)) := by rw [← h5]
      _ = y 0 • (x • (Pi.single 0 1 : Fin 2 → F)) := by
        rw [smul_eq_mulVec', Matrix.mulVec_smul, ← smul_eq_mulVec']
  rw [h6]
  exact Submodule.smul_mem _ _ (smul_single_mem_rootLine x)

theorem conj_mem_range_iff_fixes_line (x g : SL(2, F)) :
    x⁻¹ * g * x ∈ (upperUnipotent (F := F)).range ↔
      ((∀ v ∈ rootLine x, g • v = v) ∧ ∀ v, g • v - v ∈ rootLine x) := by
  constructor
  · intro h
    exact ⟨fixed_of_conj_mem x g h, sub_mem_rootLine_of_conj x g h⟩
  · rintro ⟨h1, -⟩
    exact (conj_mem_range_iff x g).mpr (h1 _ (smul_single_mem_rootLine x))

end RootLine

section Fixed

variable {k : Type*} [Field k] {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module k W]

theorem rep_mul_apply (ρ : Representation k G W) (g h : G) (w : W) :
    ρ (g * h) w = ρ g (ρ h w) := by
  rw [map_mul, Module.End.mul_apply]

theorem rep_one_apply (ρ : Representation k G W) (w : W) : ρ 1 w = w := by
  rw [map_one, Module.End.one_apply]

theorem natCard_fixed_conj (ρ : Representation k G W) (A U : Subgroup G) (x : G)
    (h : ∀ g, g ∈ A ↔ x⁻¹ * g * x ∈ U) :
    Nat.card {w : W // ∀ a ∈ A, ρ a w = w} = Nat.card {w : W // ∀ u ∈ U, ρ u w = w} := by
  refine Nat.card_congr
    { toFun := fun w => ⟨ρ x⁻¹ w.1, fun u hu => ?_⟩
      invFun := fun w => ⟨ρ x w.1, fun a ha => ?_⟩
      left_inv := fun w => ?_
      right_inv := fun w => ?_ }
  · have hg : x * u * x⁻¹ ∈ A := (h _).mpr (by simpa [mul_assoc] using hu)
    have h1 := w.2 _ hg
    have h3 : ρ x⁻¹ (ρ (x * u * x⁻¹) w.1) = ρ x⁻¹ w.1 := by rw [h1]
    rw [← rep_mul_apply, show x⁻¹ * (x * u * x⁻¹) = u * x⁻¹ by group, rep_mul_apply] at h3
    exact h3
  · have hu : x⁻¹ * a * x ∈ U := (h a).mp ha
    have h1 := w.2 _ hu
    have h3 : ρ x (ρ (x⁻¹ * a * x) w.1) = ρ x w.1 := by rw [h1]
    rw [← rep_mul_apply, show x * (x⁻¹ * a * x) = a * x by group, rep_mul_apply] at h3
    exact h3
  · apply Subtype.ext
    show ρ x (ρ x⁻¹ w.1) = w.1
    rw [← rep_mul_apply, mul_inv_cancel, rep_one_apply]
  · apply Subtype.ext
    show ρ x⁻¹ (ρ x w.1) = w.1
    rw [← rep_mul_apply, inv_mul_cancel, rep_one_apply]

end Fixed

section RootFixed

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible]

omit [CharP F 2] in
theorem natCard_fixW_rootGroup {n : ℕ} (hF : Fintype.card F = 2 ^ n) {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type*} [Field E] [Finite E] [CharP E 2]
    (ιF : F →+* E) (ιD : EndRing ρ →+* E) (J : Finset ℕ) (hJn : ∀ i ∈ J, i < n)
    (Φ : (letI := ιF.toAlgebra; (matRepE b ιD).Equiv (frobTensor F E J))) :
    Nat.card {w : W // ∀ t : F, ρ (uElt t) w = w} = Nat.card (EndRing ρ) := by
  classical
  let _ := ιF.toAlgebra
  have hD : Finite (EndRing ρ) := finite_endRing ρ
  have h1 := natCard_fixW_pow ρ b (fun t : F => uElt t) ιF ιD J Φ
  have hker : Nat.card {y : (J → Fin 2) → E // ∀ t : F, frobTensor F E J (uElt t) y = y} =
      Nat.card E := by
    have h2 : {y : (J → Fin 2) → E // ∀ t : F, frobTensor F E J (uElt t) y = y} ≃
        ↥(⨅ t : F, LinearMap.ker (tensorRep F E (fun i : J => (i : ℕ)) (uElt t) - 1)) :=
      Equiv.subtypeEquivRight (fun y => by
        simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          Module.End.one_apply, sub_eq_zero]
        rfl)
    rw [Nat.card_congr h2, Module.natCard_eq_pow_finrank (K := E),
      finrank_fixed_rootGroup hF (fun i : J => (i : ℕ)) Subtype.val_injective
        (fun i => hJn i i.2), pow_one]
  have ht : 0 < (letI := ιD.toAlgebra; Module.finrank (EndRing ρ) E) := by
    let _ := ιD.toAlgebra
    have : Module.Finite (EndRing ρ) E := Module.Finite.of_finite
    exact Module.finrank_pos
  rw [hker, natCard_E_eq ιD] at h1
  exact Nat.pow_left_injective ht.ne' h1

end RootFixed

section Main

open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

set_option synthInstance.maxHeartbeats 400000 in
theorem internal_offender_aux {n : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1)
    (A : Subgroup SL(2, F)) (hA1 : A ≠ ⊥) (hA2 : ∀ a ∈ A, a * a = 1)
    (hoff : Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, ρ a w = w}) :
    Nat.card A = 2 ^ n ∧ Nat.card (EndRing ρ) = 2 ^ n ∧
      ∃ φ : W ≃+ (Fin 2 → F),
        ∀ g w, φ (ρ g w) = (g : Matrix (Fin 2) (Fin 2) F).mulVec (φ w) := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ := binary_SL2_irreducible_Frobenius_descent hn hF ρ hnt
  have hfinD : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  let b := Module.finBasis (EndRing ρ) W
  obtain ⟨E, hEF, hEfin, hEchar, ιF, ιD, J, hJne, hJn, ⟨Φ⟩, hshift, hdim⟩ := hdesc b
  obtain ⟨r, hr⟩ : ∃ r, J.card = r := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := hr ▸ Finset.card_pos.mpr hJne
  obtain ⟨⟨a, haA⟩, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
  have ha1 : a ≠ 1 := fun h => ha (Subtype.ext h)
  have hfixa : Nat.card {w : W // ρ a w = w} = 2 ^ (d * 2 ^ (r - 1)) := by
    have h1 := natCard_fixW_involution ρ b ιF ιD J hJne Φ a ha1 (hA2 a haA)
    rw [hDcard, ← pow_mul, hr] at h1
    exact h1
  have hW : Nat.card W = 2 ^ (d * 2 ^ r) := by
    have h1 := natCard_eq_pow_finrank (ρ := ρ)
    rw [hDcard, hdim, ← pow_mul, hr] at h1
    exact h1
  have hAle : Nat.card A ≤ 2 ^ n := by
    have := card_le_of_involutions A hA2
    rwa [Nat.card_eq_fintype_card (α := F), hF] at this
  have hCle : Nat.card {w : W // ∀ a ∈ A, ρ a w = w} ≤ Nat.card {w : W // ρ a w = w} :=
    Nat.card_le_card_of_injective (fun w => ⟨w.1, w.2 a haA⟩) (by
      intro x y h
      apply Subtype.ext
      have := congrArg Subtype.val h
      simpa using this)
  have h2r : 2 ^ r = 2 * 2 ^ (r - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hdn : d * 2 ^ (r - 1) ≤ n := by
    have h1 : 2 ^ (d * 2 ^ r) ≤ 2 ^ (n + d * 2 ^ (r - 1)) := by
      calc 2 ^ (d * 2 ^ r) = Nat.card W := hW.symm
        _ ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, ρ a w = w} := hoff
        _ ≤ 2 ^ n * 2 ^ (d * 2 ^ (r - 1)) := Nat.mul_le_mul hAle (hCle.trans hfixa.le)
        _ = 2 ^ (n + d * 2 ^ (r - 1)) := (pow_add _ _ _).symm
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    have h3 : d * 2 ^ r = 2 * (d * 2 ^ (r - 1)) := by rw [h2r]; ring
    omega
  have hnr : n ≤ r * d := hr ▸ n_le_card_mul (by omega) (by omega) hJn hJne hshift
  have hr2 : r ≤ 2 := by
    have h1 : d * 2 ^ (r - 1) ≤ d * r := by
      calc d * 2 ^ (r - 1) ≤ n := hdn
        _ ≤ r * d := hnr
        _ = d * r := Nat.mul_comm _ _
    exact le_two_of_two_pow_pred_le hr1 (Nat.le_of_mul_le_mul_left h1 (by omega))
  have hneq : n = d * 2 ^ (r - 1) := by
    rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
    · simp only [Nat.sub_self, pow_zero, mul_one]; omega
    · simp only [Nat.add_one_sub_one, pow_one]; omega
  have hAge : 2 ^ (d * 2 ^ (r - 1)) ≤ Nat.card A := by
    have h1 : 2 ^ (d * 2 ^ (r - 1)) * 2 ^ (d * 2 ^ (r - 1)) ≤
        Nat.card A * 2 ^ (d * 2 ^ (r - 1)) := by
      calc 2 ^ (d * 2 ^ (r - 1)) * 2 ^ (d * 2 ^ (r - 1)) = 2 ^ (d * 2 ^ r) := by
            rw [← pow_add, h2r]; congr 1; ring
        _ = Nat.card W := hW.symm
        _ ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, ρ a w = w} := hoff
        _ ≤ Nat.card A * 2 ^ (d * 2 ^ (r - 1)) :=
            Nat.mul_le_mul_left _ (hCle.trans hfixa.le)
    exact Nat.le_of_mul_le_mul_right h1 (by positivity)
  have hAeq : Nat.card A = 2 ^ n := le_antisymm hAle (hneq ▸ hAge)
  refine ⟨hAeq, ?_⟩
  rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
  ·
    have hdn1 : d = n := by simpa using hneq.symm
    subst hdn1
    have hdim2 : Module.finrank (EndRing ρ) W = 2 := by rw [hdim, hr]; rfl
    exact ⟨hDcard, exists_natural_iso hn hF ρ hnt hDcard hdim2⟩
  ·
    exfalso
    have hcard : Nat.card A = Nat.card F := by
      rw [hAeq, Nat.card_eq_fintype_card, hF]
    obtain ⟨x, hx⟩ := eq_conj_rootGroup A hA2 hcard
    have hCA : Nat.card {w : W // ∀ a ∈ A, ρ a w = w} = Nat.card (EndRing ρ) := by
      rw [natCard_fixed_conj ρ A _ x hx, ← natCard_fixW_rootGroup ρ hF b ιF ιD J hJn Φ]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
      constructor
      · intro h t
        exact h _ ((mem_rootGroup_iff _).mpr ⟨t, rfl⟩)
      · intro h u hu
        obtain ⟨t, rfl⟩ := (mem_rootGroup_iff _).mp hu
        exact h t
    have h1 : 2 ^ (d * 2 ^ 2) ≤ 2 ^ n * 2 ^ d := by
      calc 2 ^ (d * 2 ^ 2) = Nat.card W := hW.symm
        _ ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, ρ a w = w} := hoff
        _ = 2 ^ n * 2 ^ d := by rw [hAeq, hCA, hDcard]
    rw [← pow_add] at h1
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    simp only [Nat.add_one_sub_one, pow_one] at hneq
    have h3 : d * 2 ^ 2 = 4 * d := by ring
    omega

end Main

section Final

open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

theorem charP_two_of_card_eq {n : ℕ} {F : Type*} [Field F] [Fintype F]
    (hF : Fintype.card F = 2 ^ n) : CharP F 2 := by
  obtain ⟨k, hp, hk⟩ := FiniteField.card F (ringChar F)
  have hdvd : ringChar F ∣ 2 ^ n := by
    rw [← hF, hk]
    exact dvd_pow_self _ k.ne_zero
  have h2 : ringChar F = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
  exact h2 ▸ ringChar.charP F

theorem factorization_card_sl2 {n : ℕ} (hn : 1 ≤ n) {F : Type*} [Field F] [Fintype F]
    (hF : Fintype.card F = 2 ^ n) : (Nat.card SL(2, F)).factorization 2 = n := by
  have h1 := CFSG.GorensteinWalter.sl2_card_formula F
  rw [Nat.card_eq_fintype_card (α := F), hF] at h1
  rw [h1]
  have hodd : ¬ 2 ∣ ((2 ^ n) ^ 2 - 1) := by
    have h2 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    have h3 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega
  have hne : (2 ^ n) ^ 2 - 1 ≠ 0 := fun h => hodd (by rw [h]; exact dvd_zero 2)
  rw [Nat.factorization_mul (by positivity) hne, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hodd]
  simp

set_option synthInstance.maxHeartbeats 400000 in
theorem binary_SL2_internal_offender_natural_module {n : ℕ} (hn : 1 ≤ n) {F : Type*} [Field F]
    [Fintype F] (hF : Fintype.card F = 2 ^ n) {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (ρ : Representation (ZMod 2) SL(2, F) W) (hirr : ρ.IsIrreducible)
    (hnt : ∃ g, ρ g ≠ 1) (A : Subgroup SL(2, F)) [CFSG.IsElementaryAbelian 2 A] (hA1 : A ≠ ⊥)
    (hoff : Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, ρ a w = w}) :
    ∃ φ : W ≃+ (Fin 2 → F),
      (∀ g w, φ (ρ g w) = (g : Matrix (Fin 2) (Fin 2) F).mulVec (φ w)) ∧
      Module.finrank (ZMod 2) W = 2 * n ∧ Function.Injective ρ ∧
      Nat.card {ψ : Module.End (ZMod 2) W // ∀ g v, ψ (ρ g v) = ρ g (ψ v)} = 2 ^ n ∧
      ∃ ℓ : Submodule F (Fin 2 → F), Module.finrank F ℓ = 1 ∧
        (∀ g : SL(2, F), g ∈ A ↔ ((∀ v ∈ ℓ, (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v) ∧
          ∀ v, (g : Matrix (Fin 2) (Fin 2) F).mulVec v - v ∈ ℓ)) ∧
        (∀ w, (∀ a ∈ A, ρ a w = w) ↔ φ w ∈ ℓ) ∧
        Nat.card A = 2 ^ n ∧ (∃ P : Sylow 2 SL(2, F), (P : Subgroup SL(2, F)) = A) ∧
        Nat.card A * Nat.card {w : W // ∀ a ∈ A, ρ a w = w} = Nat.card W := by
  classical
  have : CharP F 2 := charP_two_of_card_eq hF
  have : Fact ρ.IsIrreducible := ⟨hirr⟩
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by
    rw [← pow_two]; exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  obtain ⟨hAeq, hD, φ, hφ⟩ := internal_offender_aux hn hF ρ hnt A hA1 hA2 hoff
  have hcard : Nat.card A = Nat.card F := by
    rw [hAeq, Nat.card_eq_fintype_card (α := F), hF]
  obtain ⟨x, hx⟩ := eq_conj_rootGroup A hA2 hcard
  have hline : ∀ g : SL(2, F), g ∈ A ↔
      ((∀ v ∈ rootLine x, (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v) ∧
        ∀ v, (g : Matrix (Fin 2) (Fin 2) F).mulVec v - v ∈ rootLine x) := fun g =>
    (hx g).trans (conj_mem_range_iff_fixes_line x g)
  have hfix : ∀ w, (∀ a ∈ A, ρ a w = w) ↔ φ w ∈ rootLine x := by
    intro w
    constructor
    · intro h
      refine mem_rootLine_of_fixed x (φ w) (fun g hg => ?_)
      have h1 := h g ((hx g).mpr hg)
      have h2 := hφ g w
      rw [h1] at h2
      exact h2.symm
    · intro h a ha
      have h1 : a • φ w = φ w := fixed_of_conj_mem x a ((hx a).mp ha) _ h
      apply φ.injective
      rw [hφ]
      exact h1
  have hcardW : Nat.card W = 2 ^ (2 * n) := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := F), hF,
      Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, ← pow_mul, mul_comm]
  have hCW : Nat.card {w : W // ∀ a ∈ A, ρ a w = w} = 2 ^ n := by
    have h1 : {w : W // ∀ a ∈ A, ρ a w = w} ≃ ↥(rootLine x) :=
      Equiv.subtypeEquiv φ.toEquiv hfix
    rw [Nat.card_congr h1, Module.natCard_eq_pow_finrank (K := F), finrank_rootLine,
      pow_one, Nat.card_eq_fintype_card, hF]
  refine ⟨φ, hφ, ?_, ?_, ?_, rootLine x, finrank_rootLine x, hline, hfix, hAeq, ?_, ?_⟩
  ·
    have h1 : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
      have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
      rwa [Nat.card_zmod] at this
    rw [hcardW] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  ·
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : ∀ v : Fin 2 → F, (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v := by
      intro v
      obtain ⟨w, rfl⟩ := φ.surjective v
      rw [← hφ, hg]
      rfl
    apply Subtype.ext
    ext i j
    have := congrFun (h1 (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at this
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this
  ·
    rw [← natCard_endRing (ρ := ρ), hD]
  ·
    refine ⟨Sylow.ofCard A ?_, rfl⟩
    rw [hAeq, factorization_card_sl2 hn hF]
  ·
    rw [hAeq, hCW, hcardW, ← pow_add, two_mul]

end Final

end CFSG.QuasithinUnique.Setup.SL2Modules

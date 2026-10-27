module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoShadow
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

section Groups

variable {G : Type*} [Group G]

private theorem twE6CI_pow_mod {x : G} (hx : x ^ 3 = 1) (m : ℕ) : x ^ m = x ^ (m % 3) := by
  conv_lhs => rw [← Nat.mod_add_div m 3, pow_add, pow_mul, hx, one_pow, mul_one]

private theorem twE6CI_mul_pows {a b : G} (hab : Commute a b) (i j k l : ℕ) :
    a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ (i + k) * b ^ (j + l) := by
  have e : b ^ j * a ^ k = a ^ k * b ^ j := ((hab.pow_pow k j).eq).symm
  calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by
        simp only [mul_assoc]
    _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [e]
    _ = a ^ (i + k) * b ^ (j + l) := by simp only [pow_add, mul_assoc]

theorem exists_pow_mul_pow_of_mem_closure_pair_of_pow_three {a b : G} (hab : Commute a b)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) {z : G} (hz : z ∈ Subgroup.closure {a, b}) :
    ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ z = a ^ i * b ^ j := by
  have key : ∃ i j : ℕ, z = a ^ i * b ^ j := by
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨1, 0, by rw [pow_one, pow_zero, mul_one]⟩
      · exact ⟨0, 1, by rw [pow_one, pow_zero, one_mul]⟩
    | one => exact ⟨0, 0, by rw [pow_zero, pow_zero, mul_one]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, j, rfl⟩ := hx
      obtain ⟨k, l, rfl⟩ := hy
      exact ⟨i + k, j + l, twE6CI_mul_pows hab i j k l⟩
    | inv x _ hx =>
      obtain ⟨i, j, rfl⟩ := hx
      refine ⟨2 * i, 2 * j, inv_eq_of_mul_eq_one_right ?_⟩
      rw [twE6CI_mul_pows hab, show i + 2 * i = 3 * i by ring, show j + 2 * j = 3 * j by ring,
        pow_mul, pow_mul, ha, hb, one_pow, one_pow, mul_one]
  obtain ⟨i, j, rfl⟩ := key
  exact ⟨i % 3, j % 3, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
    by rw [← twE6CI_pow_mod ha, ← twE6CI_pow_mod hb]⟩

theorem card_le_nine_of_forall_eq_pow_mul_pow {H : Subgroup G} {a b : G}
    (h : ∀ z ∈ H, ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ z = a ^ i * b ^ j) : Nat.card H ≤ 9 := by
  classical
  set F : Finset G := ((Finset.range 3) ×ˢ (Finset.range 3)).image fun p => a ^ p.1 * b ^ p.2
    with hF
  have hsub : (H : Set G) ⊆ (F : Set G) := by
    intro z hz
    obtain ⟨i, j, hi, hj, rfl⟩ := h z hz
    rw [hF, Finset.coe_image]
    exact ⟨(i, j), by simp [hi, hj], rfl⟩
  have hF9 : F.card ≤ 9 := by
    refine (Finset.card_image_le).trans ?_
    rw [Finset.card_product, Finset.card_range]
  calc Nat.card H = Nat.card (H : Set G) := rfl
    _ ≤ Nat.card (F : Set G) := Nat.card_mono F.finite_toSet hsub
    _ = F.card := Nat.card_eq_finsetCard F
    _ ≤ 9 := hF9

private theorem twE6CI_dvd_27 {n : ℕ} (h : n ∣ 3 ^ 3) : n = 1 ∨ n = 3 ∨ n = 9 ∨ n = 27 := by
  obtain ⟨m, hm, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h
  interval_cases m <;> simp

private theorem twE6CI_card_lt {E H₁ H₂ : Subgroup G} [Finite E] (h₂ : H₂ ≤ E) (h : H₁ ≤ H₂)
    (hne : H₁ ≠ H₂) : Nat.card H₁ < Nat.card H₂ := by
  haveI : Finite H₂ := Finite.of_injective _ (Subgroup.inclusion_injective h₂)
  exact lt_of_le_of_ne (Subgroup.card_le_of_le h) fun he =>
    hne (Subgroup.eq_of_le_of_card_ge h he.ge)

private theorem twE6CI_nine_le_card_pair {E : Subgroup G} (hc : Nat.card E = 3 ^ 3) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) (ha1 : a ≠ 1) (hba : b ∉ Subgroup.closure {a}) :
    9 ≤ Nat.card (Subgroup.closure {a, b}) := by
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have h1 : Subgroup.closure {a} ≤ E := (Subgroup.closure_le E).2 (Set.singleton_subset_iff.2 ha)
  have h2 : Subgroup.closure {a, b} ≤ E :=
    (Subgroup.closure_le E).2 (Set.insert_subset_iff.2 ⟨ha, Set.singleton_subset_iff.2 hb⟩)
  have l12 : Subgroup.closure {a} ≤ Subgroup.closure {a, b} :=
    Subgroup.closure_mono (Set.singleton_subset_iff.2 (Set.mem_insert a _))
  have n12 : Subgroup.closure {a} ≠ Subgroup.closure {a, b} := fun h =>
    hba (h ▸ Subgroup.subset_closure (Set.mem_insert_of_mem a (Set.mem_singleton b)))
  have c1 : Nat.card (Subgroup.closure {a}) ≠ 1 := fun h =>
    ha1 (by
      have hmem : a ∈ Subgroup.closure ({a} : Set G) := Subgroup.subset_closure rfl
      rw [Subgroup.card_eq_one.1 h] at hmem
      exact hmem)
  have d1 := twE6CI_dvd_27 (hc ▸ Subgroup.card_dvd_of_le h1)
  have d2 := twE6CI_dvd_27 (hc ▸ Subgroup.card_dvd_of_le h2)
  have lt12 := twE6CI_card_lt h2 l12 n12
  omega

theorem closure_three_eq_of_card_eq {E : Subgroup G} (hc : Nat.card E = 3 ^ 3) {a b c : G}
    (ha : a ∈ E) (hb : b ∈ E) (hcE : c ∈ E) (ha1 : a ≠ 1) (hba : b ∉ Subgroup.closure {a})
    (hcab : c ∉ Subgroup.closure {a, b}) : Subgroup.closure {a, b, c} = E := by
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have h3 : Subgroup.closure {a, b, c} ≤ E :=
    (Subgroup.closure_le E).2 (Set.insert_subset_iff.2 ⟨ha,
      Set.insert_subset_iff.2 ⟨hb, Set.singleton_subset_iff.2 hcE⟩⟩)
  have l23 : Subgroup.closure {a, b} ≤ Subgroup.closure {a, b, c} :=
    Subgroup.closure_mono (Set.insert_subset_insert
      (Set.singleton_subset_iff.2 (Set.mem_insert b _)))
  have n23 : Subgroup.closure {a, b} ≠ Subgroup.closure {a, b, c} := fun h =>
    hcab (h ▸ Subgroup.subset_closure
      (Set.mem_insert_of_mem a (Set.mem_insert_of_mem b (Set.mem_singleton c))))
  have c2 := twE6CI_nine_le_card_pair hc ha hb ha1 hba
  have d3 := twE6CI_dvd_27 (hc ▸ Subgroup.card_dvd_of_le h3)
  have lt23 := twE6CI_card_lt h3 l23 n23
  have h27 : Nat.card (Subgroup.closure {a, b, c}) = 3 ^ 3 := by omega
  exact Subgroup.eq_of_le_of_card_ge h3 (by rw [h27, hc])

theorem card_closure_pair_of_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 3) {a b : G} (ha : a ∈ E) (hb : b ∈ E) (ha1 : a ≠ 1)
    (hba : b ∉ Subgroup.closure {a}) : Nat.card (Subgroup.closure {a, b}) = 3 ^ 2 := by
  have hab : Commute a b := congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have le := card_le_nine_of_forall_eq_pow_mul_pow (H := Subgroup.closure {a, b}) fun z hz =>
    exists_pow_mul_pow_of_mem_closure_pair_of_pow_three hab (hE.2 a ha) (hE.2 b hb) hz
  have ge := twE6CI_nine_le_card_pair hc ha hb ha1 hba
  rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
  omega

end Groups

section Diagonal


theorem rootDiagUnit_apply_rootVec_eq_self_iff {τ : Tag} {L : Type} [Field L]
    (a : Fin τ.rank → Lˣ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ((rootDiagUnit τ a : ModGL τ L) : Module.End L (RootModule τ L)) (rootVec τ L γ) =
        rootVec τ L γ ↔ rootChar a γ = 1 := by
  change rootDiag a (rootVec τ L γ) = rootVec τ L γ ↔ _
  rw [rootDiag_rootVec a hγ]
  constructor
  · intro h
    rw [CFSG.LieType.Chevalley.rootVec_eq_single hγ] at h
    have h' := congrArg (fun m : RootModule τ L => m (Sum.inr ⟨γ, hγ⟩)) h
    simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h'
    exact Units.ext h'
  · intro h
    rw [h, Units.val_one, one_smul]

private theorem twE6CI_rootDiagUnit_pow {τ : Tag} {L : Type} [Field L] (a : Fin τ.rank → Lˣ)
    (n : ℕ) : rootDiagUnit τ a ^ n = rootDiagUnit τ (a ^ n) := by
  induction n with
  | zero => exact Units.ext (by rw [pow_zero, pow_zero]; exact rootDiag_one.symm)
  | succ n ih =>
    refine Units.ext ?_
    rw [pow_succ, ih, Units.val_mul]
    change rootDiag (a ^ n) * rootDiag a = rootDiag (a ^ (n + 1))
    rw [rootDiag_mul_rootDiag, pow_succ]

private theorem twE6CI_rootChar_pow {τ : Tag} {L : Type} [Field L] (a : Fin τ.rank → Lˣ)
    (n : ℕ) (γ : Fin τ.rank → ℤ) : rootChar (a ^ n) γ = rootChar a γ ^ n := by
  simp only [rootChar, Pi.pow_apply, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem rootChar_pow_three_of_rootDiagUnit {τ : Tag} {L : Type} [Field L]
    {a : Fin τ.rank → Lˣ} (h : rootDiagUnit τ a ^ 3 = 1) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : rootChar a γ ^ 3 = 1 := by
  rw [← twE6CI_rootChar_pow, ← rootDiagUnit_apply_rootVec_eq_self_iff _ hγ,
    ← twE6CI_rootDiagUnit_pow, h, Units.val_one, Module.End.one_apply]

end Diagonal

section Frame

variable
  {K : Type} [Field K] {σ : K ≃+* K} {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}

theorem eq_one_of_twE6Frame_eq_one {x : twistedE6RootGroup K σ}
    (h : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
      g0 = 1) : x = 1 := by
  have h' : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (1 : ModGL TwistTag.E6.tag K) := by
    rw [map_one]
    calc baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) =
        g0 * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x : ModGL TwistTag.E6.tag K) * g0) * g0⁻¹ := by group
      _ = 1 := by rw [h, mul_one, mul_inv_cancel]
  exact Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) h')

theorem rootChar_smul_eq_of_twE6Frame_commute {x y : twistedE6RootGroup K σ} (hxy : x * y = y * x)
    {b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ}
    (hx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
      g0 = rootDiagUnit TwistTag.E6.tag b)
    {t : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht : t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K)) {u : WeylGroup TwistTag.E6.tag}
    (hy : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
      g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)
    (μ : Fin TwistTag.E6.tag.rank → ℤ) : rootChar b (u • μ) = rootChar b μ := by
  obtain ⟨b₀, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u with hn
  have hc := twE6Frame_mul g0 x y
  rw [hxy, twE6Frame_mul g0 y x, hx, hy] at hc
  have hdd : rootDiagUnit TwistTag.E6.tag b * rootDiagUnit TwistTag.E6.tag b₀ =
      rootDiagUnit TwistTag.E6.tag b₀ * rootDiagUnit TwistTag.E6.tag b :=
    Units.ext (by
      change rootDiag b * rootDiag b₀ = rootDiag b₀ * rootDiag b
      rw [rootDiag_mul_rootDiag, rootDiag_mul_rootDiag, mul_comm])
  have h1 : rootDiagUnit TwistTag.E6.tag b₀ * (n * rootDiagUnit TwistTag.E6.tag b) =
      rootDiagUnit TwistTag.E6.tag b₀ * (rootDiagUnit TwistTag.E6.tag b * n) := by
    rw [← mul_assoc, hc, ← mul_assoc, hdd, mul_assoc]
  have hdn : rootDiagUnit TwistTag.E6.tag b = n * rootDiagUnit TwistTag.E6.tag b * n⁻¹ := by
    rw [mul_left_cancel h1, mul_inv_cancel_right]
  exact (rootDiagUnit_eq_conj_canonicalRep_iff b b u).1 hdn μ

theorem twE6FixDim_inv_eq (s : twistedE6RootGroup K σ) :
    twE6FixDim K σ s⁻¹ = twE6FixDim K σ s := by
  unfold twE6FixDim
  have e : LinearMap.ker ((((s⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) :
      Module.End K (RootModule TwistTag.E6.tag K)) - 1) =
      LinearMap.ker (((s : ModGL TwistTag.E6.tag K) :
        Module.End K (RootModule TwistTag.E6.tag K)) - 1) := by
    ext m
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
      Subgroup.coe_inv]
    constructor
    · intro h
      have h' := units_inv_apply_eq_self (A := ((s : ModGL TwistTag.E6.tag K))⁻¹) h
      rwa [inv_inv] at h'
    · exact units_inv_apply_eq_self
  rw [e]

theorem twE6All24PlaneIn_of_closure_pair {E₀ : Subgroup (twistedE6RootGroup K σ)}
    (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3) {a y : twistedE6RootGroup K σ}
    (ha : a ∈ E₀) (hy : y ∈ E₀) (ha1 : a ≠ 1) (hya : y ∉ Subgroup.closure {a})
    (ha24 : twE6FixDim K σ a = 24) (hay : ∀ i : ℕ, twE6FixDim K σ (a ^ i * y) = 24) :
    TwE6All24PlaneIn K σ E₀ := by
  have hab : Commute a y := congrArg Subtype.val (hE₀.1.is_comm.comm ⟨a, ha⟩ ⟨y, hy⟩)
  have ha3 := hE₀.2 a ha
  have hy3 := hE₀.2 y hy
  refine ⟨Subgroup.closure {a, y},
    (Subgroup.closure_le E₀).2 (Set.insert_subset_iff.2 ⟨ha, Set.singleton_subset_iff.2 hy⟩),
    card_closure_pair_of_isElemAbelian hE₀ hc ha hy ha1 hya, fun s hs hs1 => ?_⟩
  obtain ⟨i, j, hi, hj, rfl⟩ := exists_pow_mul_pow_of_mem_closure_pair_of_pow_three hab ha3 hy3 hs
  interval_cases j
  · interval_cases i
    · exact absurd (by rw [pow_zero, pow_zero, mul_one]) hs1
    · rw [pow_one, pow_zero, mul_one]
      exact ha24
    · have e : a ^ 2 * y ^ 0 = a⁻¹ := by
        rw [pow_zero, mul_one]
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← pow_succ]
        exact ha3
      rw [e, twE6FixDim_inv_eq, ha24]
  · rw [pow_one]
    exact hay i
  · have e : a ^ i * y ^ 2 = (a ^ (2 * i) * y)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      have h := twE6CI_mul_pows hab i 2 (2 * i) 1
      rw [pow_one] at h
      rw [h, show i + 2 * i = 3 * i by ring, pow_mul, ha3, one_pow, one_mul]
      exact hy3
    rw [e, twE6FixDim_inv_eq]
    exact hay (2 * i)

end Frame

section FrameParts

variable
  {K : Type} [Field K] {σ : K ≃+* K} {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}

theorem exists_twE6Frame_eq_of_mem_closure {S : Subgroup (WeylGroup TwistTag.E6.tag)}
    {X : Set (twistedE6RootGroup K σ)}
    (hX : ∀ y ∈ X, ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K), ∃ w ∈ S,
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
        g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
    {y : twistedE6RootGroup K σ} (hy : y ∈ Subgroup.closure X) :
    ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K), ∃ w ∈ S,
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
        g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w := by
  induction hy using Subgroup.closure_induction with
  | mem y hy => exact hX y hy
  | one => exact ⟨1, one_mem _, 1, one_mem _, by rw [twE6Frame_one, canonicalRep_one, mul_one]⟩
  | mul y z _ _ hy hz =>
    obtain ⟨t, ht, w, hw, e⟩ := hy
    obtain ⟨t', ht', w', hw', e'⟩ := hz
    obtain ⟨s, hs, e''⟩ := exists_twE6Frame_mul_eq ht ht' e e'
    exact ⟨s, hs, w * w', mul_mem hw hw', e''⟩
  | inv y _ hy =>
    obtain ⟨t, ht, w, hw, e⟩ := hy
    obtain ⟨s, hs, e'⟩ := exists_twE6Frame_inv_eq ht e
    exact ⟨s, hs, w⁻¹, inv_mem hw, e'⟩

theorem mem_of_twE6Frame_eq_of_mem_closure {S : Subgroup (WeylGroup TwistTag.E6.tag)}
    {X : Set (twistedE6RootGroup K σ)}
    (hX : ∀ y ∈ X, ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K), ∃ w ∈ S,
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
        g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
    {y : twistedE6RootGroup K σ} (hy : y ∈ Subgroup.closure X)
    {t : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht : t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K)) {u : WeylGroup TwistTag.E6.tag}
    (hyu : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
        g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u) :
    u ∈ S := by
  obtain ⟨s, hs, w, hw, e⟩ := exists_twE6Frame_eq_of_mem_closure hX hy
  rw [eq_of_torus_mul_canonicalRep_eq ht hs (hyu.symm.trans e)]
  exact hw

end FrameParts

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end

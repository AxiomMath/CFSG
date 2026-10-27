module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralBlocks
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly
public import CFSG.HardMathSupport.Timmesfeld.Torality.SylowNormalizer
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyOrder
public import CFSG.HardMathSupport.Timmesfeld.Torality.DescentCongruence

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley IntermediateField

variable {τ : Tag}

theorem isAlgebraic_zmod_algebraicClosure_of_finite (K : Type) [Field K] [Finite K] (ℓ : ℕ)
    [Fact ℓ.Prime] [CharP (AlgebraicClosure K) ℓ] :
    letI := ZMod.algebra (AlgebraicClosure K) ℓ
    Algebra.IsAlgebraic (ZMod ℓ) (AlgebraicClosure K) := by
  let _ : Algebra (ZMod ℓ) (AlgebraicClosure K) := ZMod.algebra (AlgebraicClosure K) ℓ
  refine ⟨fun y => ?_⟩
  have hint : IsIntegral K y := Algebra.IsIntegral.isIntegral y
  have := IntermediateField.adjoin.finiteDimensional hint
  have : Finite K⟮y⟯ := Module.finite_of_finite K
  let : Fintype K⟮y⟯ := Fintype.ofFinite _
  have hpow : y ^ Fintype.card K⟮y⟯ = y :=
    congrArg Subtype.val (FiniteField.pow_card (⟨y, IntermediateField.mem_adjoin_simple_self K y⟩ :
      K⟮y⟯))
  refine ⟨Polynomial.X ^ Fintype.card K⟮y⟯ - Polynomial.X,
    FiniteField.X_pow_card_sub_X_ne_zero (ZMod ℓ) Fintype.one_lt_card, ?_⟩
  rw [map_sub, map_pow, Polynomial.aeval_X, hpow, sub_self]

section Descent


theorem exists_descent_subgroup {L : Type} [Field L] [IsAlgClosed L] {ℓ r : ℕ} [Fact ℓ.Prime]
    [Fact r.Prime] (hℓr : ℓ ≠ r) [CharP L ℓ]
    (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    {B : Subgroup (ModGL τ L)} (hB : B ≤ adjointGroup τ L) (hBfin : (B : Set (ModGL τ L)).Finite)
    (E₀ : Finset L) {M : ℕ} (hM : 1 ≤ M) :
    ∃ K₁ : Subfield L, Finite K₁ ∧ (E₀ : Set L) ⊆ K₁ ∧ Nat.card K₁ ≡ 1 [MOD r ^ M] ∧
      ∀ x ∈ B, ∃ y ∈ adjointGroup τ K₁, baseChangeGL K₁.subtype y = x := by
  classical
  let F : ModGL τ L → Finset L := fun x =>
    if hx : x ∈ adjointGroup τ L then (exists_finset_descent hx).choose else ∅
  have hF : ∀ x ∈ B, ∀ K₁ : Subfield L, (F x : Set L) ⊆ K₁ →
      ∃ y ∈ adjointGroup τ K₁, baseChangeGL K₁.subtype y = x := by
    intro x hx K₁ hK₁
    have hxC := hB hx
    have := (exists_finset_descent hxC).choose_spec K₁
    simp only [F, hxC, ↓reduceDIte] at hK₁
    exact this hK₁
  set E : Finset L := E₀ ∪ hBfin.toFinset.biUnion F with hE
  obtain ⟨K₁, hK₁fin, hEK, hK₁q⟩ := exists_finite_subfield_congruence_prime hℓr E
    (fun z _ => halg.isAlgebraic z) hM
  refine ⟨K₁, hK₁fin, fun z hz => hEK (Finset.mem_coe.2 (Finset.mem_union_left _ hz)), hK₁q,
    fun x hx => hF x hx K₁ fun z hz => hEK (Finset.mem_coe.2 (Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨x, hBfin.mem_toFinset.2 hx, hz⟩)))⟩

theorem comap_le_adjointGroup {K₁ L : Type} [Field K₁] [Field L] (ι : K₁ →+* L)
    {B : Subgroup (ModGL τ L)} (hdesc : ∀ x ∈ B, ∃ y ∈ adjointGroup τ K₁, baseChangeGL ι y = x) :
    B.comap (baseChangeGL ι) ≤ adjointGroup τ K₁ := by
  intro y hy
  obtain ⟨y', hy', e⟩ := hdesc _ hy
  rw [← baseChangeGL_injective ι e]
  exact hy'

theorem isPGroup_comap {K₁ L : Type} [Field K₁] [Field L] (ι : K₁ →+* L) {p : ℕ}
    {B : Subgroup (ModGL τ L)} (hexp : ∀ x ∈ B, x ^ p = 1) :
    IsPGroup p (B.comap (baseChangeGL ι)) := by
  rintro ⟨y, hy⟩
  refine ⟨1, Subtype.ext ?_⟩
  apply baseChangeGL_injective ι
  rw [pow_one]
  simpa using hexp _ hy

theorem not_dvd_of_modEq_pow {p q M : ℕ} (hp : p.Prime) (hM : 1 ≤ M) (hq : q ≡ 1 [MOD p ^ M]) :
    ¬ p ∣ q := by
  intro h
  have h1 : q % p = 1 % p := Nat.ModEq.of_dvd (dvd_pow_self p (by omega)) hq
  rw [Nat.mod_eq_zero_of_dvd h, Nat.mod_eq_of_lt hp.one_lt] at h1
  exact zero_ne_one h1

end Descent

section


theorem exists_conj_le_monomial_bar {L : Type} [Field L] [IsAlgClosed L] {ℓ p : ℕ}
    [Fact ℓ.Prime] [hp : Fact p.Prime] (hℓ : ℓ ≠ p) [CharP L ℓ]
    (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    {B : Subgroup (ModGL τ L)} (hB : B ≤ adjointGroup τ L) (hBfin : (B : Set (ModGL τ L)).Finite)
    (hexp : ∀ x ∈ B, x ^ p = 1) :
    ∃ c ∈ adjointGroup τ L, ∀ x ∈ B, c * x * c⁻¹ ∈ monomialSubgroup τ L := by
  set M := (Nat.card (WeylGroup τ)).factorization p + 1 with hM
  have hWM : ¬ p ^ M ∣ Nat.card (WeylGroup τ) :=
    Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' hp.out
  obtain ⟨K₁, hK₁, -, hq, hdesc⟩ := exists_descent_subgroup hℓ halg hB hBfin ∅ (by omega : 1 ≤ M)
  have hqp : ¬ p ∣ Nat.card K₁ := not_dvd_of_modEq_pow hp.out (by omega) hq
  obtain ⟨u, hu, hun⟩ := exists_conj_le_monomial_of_isPGroup τ K₁ hqp hq hWM
    (comap_le_adjointGroup K₁.subtype hdesc) (isPGroup_comap K₁.subtype hexp)
  refine ⟨baseChangeGL K₁.subtype u,
    CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup K₁.subtype hu, fun x hx => ?_⟩
  obtain ⟨y, -, rfl⟩ := hdesc x hx
  have h := baseChangeGL_mem_monomialSubgroup K₁.subtype (hun y (by
    change baseChangeGL K₁.subtype y ∈ B
    exact hx))
  rwa [map_mul, map_mul, map_inv] at h

theorem exists_conj_le_monomial_centralizer_bar {L : Type} [Field L] [IsAlgClosed L] {ℓ p : ℕ}
    [Fact ℓ.Prime] [hp : Fact p.Prime] (hℓ : ℓ ≠ p) [CharP L ℓ]
    (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L) (a : Fin τ.rank → Lˣ)
    {B : Subgroup (ModGL τ L)} (hB : B ≤ adjointGroup τ L) (hBfin : (B : Set (ModGL τ L)).Finite)
    (hBa : ∀ x ∈ B, rootDiagUnit τ a * x = x * rootDiagUnit τ a) (hexp : ∀ x ∈ B, x ^ p = 1) :
    ∃ z ∈ adjointGroup τ L, rootDiagUnit τ a * z = z * rootDiagUnit τ a ∧
      ∀ x ∈ B, z * x * z⁻¹ ∈ monomialSubgroup τ L := by
  classical
  set M := (Nat.card (WeylGroup τ)).factorization p + 1 with hM
  have hWM : ¬ p ^ M ∣ Nat.card (WeylGroup τ) :=
    Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' hp.out
  set E₀ : Finset L := Finset.univ.image (fun i => (a i : L)) ∪
    Finset.univ.image (fun i => ((a i)⁻¹ : Lˣ) : Fin τ.rank → L) with hE₀
  obtain ⟨K₁, hK₁, hE₀K, hq, hdesc⟩ := exists_descent_subgroup hℓ halg hB hBfin E₀
    (by omega : 1 ≤ M)
  have hq3 : ¬ p ∣ Nat.card K₁ := not_dvd_of_modEq_pow hp.out (by omega) hq
  set ι := K₁.subtype with hι
  have ha1 : ∀ i, (a i : L) ∈ K₁ := fun i =>
    hE₀K (Finset.mem_coe.2 (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
  have ha2 : ∀ i, (((a i)⁻¹ : Lˣ) : L) ∈ K₁ := fun i =>
    hE₀K (Finset.mem_coe.2 (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun i => ((a i)⁻¹ : Lˣ) : Fin τ.rank → L) (Finset.mem_univ i))))
  let a' : Fin τ.rank → K₁ˣ := fun i =>
    ⟨⟨a i, ha1 i⟩, ⟨((a i)⁻¹ : Lˣ), ha2 i⟩, Subtype.ext (Units.mul_inv (a i)),
      Subtype.ext (Units.inv_mul (a i))⟩
  have ha' : (fun i => Units.map ι.toMonoidHom (a' i)) = a := by
    funext i
    exact Units.ext rfl
  have hda : baseChangeGL ι (rootDiagUnit τ a') = rootDiagUnit τ a := by
    rw [baseChangeGL_rootDiagUnit, ha']
  set B' := B.comap (baseChangeGL ι) with hB'
  have hB'C : B' ≤ familyCentralizer τ K₁ (fun _ : Unit => a') := by
    intro y hy
    refine mem_familyCentralizer.2 ⟨comap_le_adjointGroup ι hdesc hy, fun _ => ?_⟩
    apply baseChangeGL_injective ι
    have h := hBa _ hy
    rw [map_mul, map_mul, map_inv, hda, h, mul_inv_cancel_right]
  obtain ⟨u, hu, hun⟩ := exists_conj_le_monomial_of_isPGroup_family (fun _ : Unit => a') hq3 hq
    hWM hB'C (isPGroup_comap ι hexp)
  obtain ⟨huC, hud⟩ := mem_familyCentralizer.1 hu
  refine ⟨baseChangeGL ι u, CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι huC, ?_,
    fun x hx => ?_⟩
  · have h := congrArg (baseChangeGL ι) (hud ())
    rw [map_mul, map_mul, map_inv, hda] at h
    calc rootDiagUnit τ a * baseChangeGL ι u =
          (rootDiagUnit τ a * baseChangeGL ι u * (rootDiagUnit τ a)⁻¹) * rootDiagUnit τ a := by
          group
      _ = baseChangeGL ι u * rootDiagUnit τ a := by rw [h]
  · obtain ⟨y, -, rfl⟩ := hdesc x hx
    have h := baseChangeGL_mem_monomialSubgroup ι (Subgroup.mem_inf.1 (hun y (by
      change baseChangeGL ι y ∈ B
      exact hx))).2
    rwa [map_mul, map_mul, map_inv] at h

variable (τ) in
@[expose] def MonomialToralAt (p : ℕ) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L], ringChar L ≠ p →
    ∀ (M : Type) [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (n : ModGL τ L)
      (hn : n ∈ monomialSubgroup τ L), weylQuotientHom τ L ⟨n, hn⟩ ∈ kernelWeylGroup χ →
      weylQuotientHom τ L ⟨n, hn⟩ ^ p = 1 →
      ∃ g ∈ rootSpan τ L (kernelRoots χ), g * n * g⁻¹ ∈ torusGroup τ L

theorem monomialToralAt_three_of_block (hblk : A2BlockToral τ) : MonomialToralAt τ 3 :=
  fun _ _ _ hL _ _ _ _ hn hw h3 => exists_conj_mem_torusGroup_of_kernelWeylGroup hblk hL hn hw h3

theorem mem_kernelWeylGroup_one (w : WeylGroup τ) :
    w ∈ kernelWeylGroup (1 : Multiplicative (Fin τ.rank → ℤ) →* Unit) := by
  have hle : Subgroup.closure (Set.range (simple τ)) ≤
      kernelWeylGroup (1 : Multiplicative (Fin τ.rank → ℤ) →* Unit) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨1, i, ⟨isRoot_single τ i, rfl⟩, by group⟩
  rw [(coxeterSystem τ).subgroup_closure_range_simple] at hle
  exact hle (Subgroup.mem_top w)

theorem weylQuotientHom_torus_mul {L : Type} [Field L] {k : ModGL τ L}
    (hk : k ∈ torusGroup τ L) (w : WeylGroup τ)
    (hn : k * canonicalRep (coxeterSystem τ) L w ∈ monomialSubgroup τ L) :
    weylQuotientHom τ L ⟨_, hn⟩ = w :=
  weylQuotientHom_eq (by
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w))

theorem weylQuotientHom_pow_eq_one {L : Type} [Field L] {n : ModGL τ L}
    (hn : n ∈ monomialSubgroup τ L) {p : ℕ} (hp : n ^ p = 1) :
    weylQuotientHom τ L ⟨n, hn⟩ ^ p = 1 := by
  have e : (⟨n, hn⟩ : monomialSubgroup τ L) ^ p = 1 := Subtype.ext (by simpa using hp)
  rw [← map_pow, e, map_one]

theorem exists_conj_mem_torusGroup_of_mem_monomial {p : ℕ} (hmon : MonomialToralAt τ p)
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ p) {n : ModGL τ L}
    (hn : n ∈ monomialSubgroup τ L) (hp : n ^ p = 1) :
    ∃ g ∈ adjointGroup τ L, g * n * g⁻¹ ∈ torusGroup τ L := by
  obtain ⟨g, hg, hgn⟩ := hmon L hL Unit 1 n hn
    (mem_kernelWeylGroup_one (weylQuotientHom τ L ⟨n, hn⟩)) (weylQuotientHom_pow_eq_one hn hp)
  exact ⟨g, rootSpan_le_adjointGroup L _ hg, hgn⟩

theorem exists_conj_mem_torusGroup_of_mem_monomial_centralizer {p : ℕ}
    (hmon : MonomialToralAt τ p) {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ p)
    {a : Fin τ.rank → Lˣ} (hstab : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a)
    {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    (hna : rootDiagUnit τ a * n = n * rootDiagUnit τ a) (hp : n ^ p = 1) :
    ∃ g ∈ adjointGroup τ L, rootDiagUnit τ a * g = g * rootDiagUnit τ a ∧
      g * n * g⁻¹ ∈ torusGroup τ L := by
  obtain ⟨w, k, hk, e⟩ := monomialSubgroup_le_torusWeylCosets hn
  subst e
  have hπ : weylQuotientHom τ L ⟨_, hn⟩ = w := weylQuotientHom_torus_mul hk w hn
  have hw : w ∈ rootCharStabilizer a := by
    rw [← conj_canonicalRep_eq_iff]
    have hdk : rootDiagUnit τ a * k = k * rootDiagUnit τ a :=
      rootDiagUnit_mul_comm_of_mem_torusGroup a hk
    have h1 : rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w =
        canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ a := by
      have e1 : rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w =
          k⁻¹ * (rootDiagUnit τ a * (k * canonicalRep (coxeterSystem τ) L w)) := by
        rw [← mul_assoc (rootDiagUnit τ a) k, hdk]
        group
      rw [e1, hna]
      group
    rw [h1, mul_inv_cancel_right]
  have hwS : weylQuotientHom τ L ⟨_, hn⟩ ∈ kernelWeylGroup (rootCharHom3 a) := by
    rw [hπ]
    exact hstab hw
  obtain ⟨g, hg, hgn⟩ := hmon L hL Lˣ (rootCharHom3 a) _ hn hwS (weylQuotientHom_pow_eq_one hn hp)
  have hgc : g ∈ Subgroup.centralizer {rootDiagUnit τ a} :=
    rootSpan_le_centralizer a (fun _ h => h) hg
  refine ⟨g, rootSpan_le_adjointGroup L _ hg, ?_, hgn⟩
  exact (Subgroup.mem_centralizer_singleton_iff.1 hgc).symm

theorem conj_pow_eq_one' {G : Type*} [Group G] (c : G) {x : G} {p : ℕ} (hx : x ^ p = 1) :
    (c * x * c⁻¹) ^ p = 1 := by
  rw [conj_pow, hx, mul_one, mul_inv_cancel]

theorem rootDiagUnit_pow' {L : Type} [Field L] (a : Fin τ.rank → Lˣ) (p : ℕ) :
    rootDiagUnit τ (a ^ p) = rootDiagUnit τ a ^ p := by
  induction p with
  | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
  | succ k ih => rw [pow_succ, pow_succ, rootDiagUnit_mul, ih]

theorem exists_conj_le_torusGroup_of_plane {p : ℕ} [hp : Fact p.Prime]
    (hmon : MonomialToralAt τ p) {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ℓ ≠ p) [CharP L ℓ] (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    (hstab : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) →
      rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a)
    {A : Subgroup (ModGL τ L)} (hA : A ≤ adjointGroup τ L) (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hexp : ∀ x ∈ A, x ^ p = 1) (hcard : Nat.card A = p ^ 2) :
    ∃ C ∈ adjointGroup τ L, ∀ x ∈ A, C * x * C⁻¹ ∈ torusGroup τ L := by
  classical
  have hp1 := hp.out.one_lt
  have hLp : ringChar L ≠ p := by rw [ringChar.eq L ℓ]; exact hℓ
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hAfin : (A : Set (ModGL τ L)).Finite := Set.toFinite _
  obtain ⟨x₀, hx₀A, hx₀1⟩ : ∃ x ∈ A, x ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 h
    rw [hbot, Subgroup.card_bot] at hcard
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp1
    omega
  obtain ⟨c₁, hc₁, hc₁N⟩ := exists_conj_le_monomial_bar hℓ halg hA hAfin hexp
  obtain ⟨g, hg, hgn⟩ := exists_conj_mem_torusGroup_of_mem_monomial hmon hLp (hc₁N x₀ hx₀A)
    (conj_pow_eq_one' c₁ (hexp x₀ hx₀A))
  set c := g * c₁ with hcdef
  have hcC : c ∈ adjointGroup τ L := mul_mem hg hc₁
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgn
  have hda : c * x₀ * c⁻¹ = rootDiagUnit τ a := by
    rw [← ha, hcdef]
    group
  have hap : ∀ i, a i ^ p = 1 := by
    have h : rootDiagUnit τ (a ^ p) = rootDiagUnit τ 1 := by
      rw [rootDiagUnit_pow', rootDiagUnit_one, ← hda, conj_pow_eq_one' c (hexp x₀ hx₀A)]
    intro i
    have := congrFun (rootDiagUnit_injective h) i
    simpa using this
  set A' := A.map (MulAut.conj c).toMonoidHom with hA'
  have hA'mem : ∀ x ∈ A, c * x * c⁻¹ ∈ A' := fun x hx => ⟨x, hx, rfl⟩
  have hA'C : A' ≤ adjointGroup τ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hcC (hA hx)) (inv_mem hcC)
  have hA'fin : (A' : Set (ModGL τ L)).Finite := Set.Finite.image _ hAfin
  have hA'a : ∀ y ∈ A', rootDiagUnit τ a * y = y * rootDiagUnit τ a := by
    rintro _ ⟨x, hx, rfl⟩
    change rootDiagUnit τ a * (c * x * c⁻¹) = c * x * c⁻¹ * rootDiagUnit τ a
    rw [← hda]
    calc c * x₀ * c⁻¹ * (c * x * c⁻¹) = c * (x₀ * x) * c⁻¹ := by group
      _ = c * (x * x₀) * c⁻¹ := by rw [hcomm x₀ hx₀A x hx]
      _ = c * x * c⁻¹ * (c * x₀ * c⁻¹) := by group
  have hA'exp : ∀ y ∈ A', y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_pow_eq_one' c (hexp x hx)
  obtain ⟨z, hz, hzd, hzN⟩ := exists_conj_le_monomial_centralizer_bar hℓ halg a hA'C hA'fin hA'a
    hA'exp
  have hx₀ord : orderOf x₀ = p := orderOf_eq_prime (hexp x₀ hx₀A) hx₀1
  obtain ⟨y₀, hy₀A, hy₀⟩ : ∃ y ∈ A, y ∉ Subgroup.zpowers x₀ := by
    by_contra h
    push Not at h
    have heq : A = Subgroup.zpowers x₀ :=
      le_antisymm (fun y hy => h y hy) ((Subgroup.zpowers_le).2 hx₀A)
    rw [heq, Nat.card_zpowers, hx₀ord] at hcard
    have : p < p ^ 2 := by nlinarith
    omega
  set n' := z * (c * y₀ * c⁻¹) * z⁻¹ with hn'
  have hn'N : n' ∈ monomialSubgroup τ L := hzN _ (hA'mem y₀ hy₀A)
  have hn'a : rootDiagUnit τ a * n' = n' * rootDiagUnit τ a := by
    have h1 := hA'a _ (hA'mem y₀ hy₀A)
    have hzd' : rootDiagUnit τ a * z⁻¹ = z⁻¹ * rootDiagUnit τ a := by
      calc rootDiagUnit τ a * z⁻¹ = z⁻¹ * (z * rootDiagUnit τ a) * z⁻¹ := by group
        _ = z⁻¹ * (rootDiagUnit τ a * z) * z⁻¹ := by rw [hzd]
        _ = z⁻¹ * rootDiagUnit τ a := by group
    calc rootDiagUnit τ a * n' = (rootDiagUnit τ a * z) * (c * y₀ * c⁻¹) * z⁻¹ := by
          rw [hn']; group
      _ = z * (rootDiagUnit τ a * (c * y₀ * c⁻¹)) * z⁻¹ := by rw [hzd]; group
      _ = z * (c * y₀ * c⁻¹) * (rootDiagUnit τ a * z⁻¹) := by rw [h1]; group
      _ = n' * rootDiagUnit τ a := by rw [hzd', hn']; group
  have hn'p : n' ^ p = 1 := conj_pow_eq_one' z (hA'exp _ (hA'mem y₀ hy₀A))
  obtain ⟨g', hg', hg'd, hg'n⟩ := exists_conj_mem_torusGroup_of_mem_monomial_centralizer hmon
    hLp (hstab a hap) hn'N hn'a hn'p
  set C := g' * z * c with hCdef
  have hCC : C ∈ adjointGroup τ L := mul_mem (mul_mem hg' hz) hcC
  refine ⟨C, hCC, ?_⟩
  set S := A ⊓ (torusGroup τ L).comap (MulAut.conj C).toMonoidHom with hS
  have hx₀S : x₀ ∈ S := by
    refine ⟨hx₀A, ?_⟩
    change C * x₀ * C⁻¹ ∈ torusGroup τ L
    have e : C * x₀ * C⁻¹ = g' * (z * rootDiagUnit τ a * z⁻¹) * g'⁻¹ := by
      rw [← hda, hCdef]
      group
    have hzd'' : z * rootDiagUnit τ a * z⁻¹ = rootDiagUnit τ a := by
      rw [← hzd, mul_inv_cancel_right]
    have hg'd' : g' * rootDiagUnit τ a * g'⁻¹ = rootDiagUnit τ a := by
      rw [← hg'd, mul_inv_cancel_right]
    rw [e, hzd'', hg'd']
    exact ha ▸ hgn
  have hy₀S : y₀ ∈ S := by
    refine ⟨hy₀A, ?_⟩
    change C * y₀ * C⁻¹ ∈ torusGroup τ L
    have e : C * y₀ * C⁻¹ = g' * n' * g'⁻¹ := by
      rw [hCdef, hn']
      group
    rw [e]
    exact hg'n
  have hle : Subgroup.zpowers x₀ ≤ S := (Subgroup.zpowers_le).2 hx₀S
  have hlt : Subgroup.zpowers x₀ < S := lt_of_le_of_ne hle fun h => hy₀ (h ▸ hy₀S)
  have : Finite S := Finite.of_injective (Subgroup.inclusion (inf_le_left : S ≤ A))
    (Subgroup.inclusion_injective _)
  have h1 := Subgroup.card_lt_of_lt hlt
  rw [Nat.card_zpowers, hx₀ord] at h1
  have h2 : Nat.card S ∣ Nat.card A := Subgroup.card_dvd_of_le inf_le_left
  rw [hcard] at h2
  have h3 : Nat.card S = p ^ 2 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp.out).1 h2
    interval_cases k
    · rw [hk', pow_zero] at h1
      omega
    · rw [hk', pow_one] at h1
      omega
    · exact hk'
  have hSA : S = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hcard])
  intro x hx
  rw [← hSA] at hx
  exact hx.2

theorem planesToralBar_of_monomialToral {p : ℕ} (hp : p.Prime) (hmon : MonomialToralAt τ p)
    (hstab : ∀ (L : Type) [Field L] (a : Fin τ.rank → Lˣ), (∀ i, a i ^ p = 1) →
      rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a) :
    PlanesToralBar τ p := by
  intro K _ _ hpK A hA hcomm hexp hcard
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ℓ, hℓK⟩ := CharP.exists K
  have hℓp : ℓ.Prime := CharP.char_is_prime K ℓ
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have hℓ : ℓ ≠ p := by
    rintro rfl
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K ℓ
    apply hpK
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self ℓ n.ne_zero
  obtain ⟨C, hC, hCA⟩ := exists_conj_le_torusGroup_of_plane hmon hℓ
    (isAlgebraic_zmod_algebraicClosure_of_finite K ℓ) (hstab (AlgebraicClosure K)) hA hcomm
    hexp hcard
  refine ⟨C⁻¹, inv_mem hC, fun x hx => ?_⟩
  rw [inv_inv]
  exact hCA x hx

theorem planesToralBar_three_of_block (hblk : A2BlockToral τ)
    (hstab : ∀ (L : Type) [Field L] (a : Fin τ.rank → Lˣ), (∀ i, a i ^ 3 = 1) →
      rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a) :
    PlanesToralBar τ 3 :=
  planesToralBar_of_monomialToral Nat.prime_three (monomialToralAt_three_of_block hblk) hstab

end

end CFSG.HardMathSupport.Timmesfeld.CrossChar

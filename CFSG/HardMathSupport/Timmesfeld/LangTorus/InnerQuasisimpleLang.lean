module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleRankOne
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleCycle
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningSemilinear
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLang
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLangFrobenius
public import CFSG.Quasithin.Background.SmithCurtisChevAmb

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE
open scoped commutatorElement

set_option linter.unusedSectionVars false


section Distinct

variable {τ : Tag} {L : Type} [Field L]

theorem pinnedX_eq_of_pos_neg {α α' : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hpos : 0 < height α)
    (hα' : IsRoot τ α') (hneg : height α' < 0) {c c' : L}
    (h : pinnedX τ L α c = pinnedX τ L α' c') : c = 0 := by
  have h1 : pinnedX τ L α c ∈ borelGroup τ L :=
    Subgroup.mem_sup_right (rootSpan_le_posUnipotent (S := {α}) (fun γ hγ => by
      rw [Set.mem_singleton_iff] at hγ; subst hγ; exact ⟨hα, hpos⟩)
      (pinnedX_mem_rootSpan (Set.mem_singleton α) c))
  have h2 : pinnedX τ L α c ∈ negUnipotent τ L :=
    h ▸ rootSpan_le_negUnipotent (S := {α'}) (fun γ hγ => by
      rw [Set.mem_singleton_iff] at hγ; subst hγ; exact ⟨hα', hneg⟩)
      (pinnedX_mem_rootSpan (Set.mem_singleton α') c')
  obtain ⟨w₁, hw₁, -⟩ := weyl_longest_element τ
  have h3 : pinnedX τ L α c ∈ borelGroup τ L ⊓ negUnipotent τ L := Subgroup.mem_inf.2 ⟨h1, h2⟩
  rw [(opposite_Borel_intersection τ L w₁ hw₁).2.2.2, Subgroup.mem_bot, ← pinnedX_zero τ L α] at h3
  exact pinnedX_injective τ L α h3

theorem eq_of_pinnedX_eq_pos {α α' : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α)
    (hα' : IsRoot τ α' ∧ 0 < height α') {c c' : L}
    (h : pinnedX τ L α c = pinnedX τ L α' c') (hc : c ≠ 0) : α = α' := by
  by_contra hne
  let β : Fin 2 → Fin τ.rank → ℤ := ![α, α']
  have hβinj : Function.Injective β := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [β]
  have hpos : ∀ i, IsRoot τ (β i) ∧ 0 < height (β i) := by
    intro i
    fin_cases i <;> simp [β, hα, hα']
  have key := (positive_root_product_injectivity τ L β hβinj hpos).2
  have e1 : (List.ofFn fun i => pinnedX τ L (β i) (![c, -c'] i)).prod = 1 := by
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    simp only [β, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
    rw [h, ← pinnedX_add]
    simp [pinnedX_zero]
  have e2 : (List.ofFn fun i => pinnedX τ L (β i) ((0 : Fin 2 → L) i)).prod = 1 := by
    simp [pinnedX_zero]
  have := congrFun (key (e1.trans e2.symm)) 0
  exact hc (by simpa using this)

theorem eq_of_pinnedX_one_mem_rootSubgroup {α α' : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hα' : IsRoot τ α') (h : pinnedX τ L α 1 ∈ rootSubgroup τ L α') : α = α' := by
  obtain ⟨c', hc'⟩ := mem_rootSubgroup.1 h
  rcases IsRoot.height_pos_or_neg hα with hp | hn <;> rcases IsRoot.height_pos_or_neg hα' with hp' | hn'
  · exact eq_of_pinnedX_eq_pos ⟨hα, hp⟩ ⟨hα', hp'⟩ hc'.symm one_ne_zero
  · exact absurd (pinnedX_eq_of_pos_neg hα hp hα' hn' hc'.symm) one_ne_zero
  · have h0 := pinnedX_eq_of_pos_neg hα' hp' hα hn hc'
    rw [h0, pinnedX_zero] at hc'
    exact absurd (pinnedX_injective τ L α (hc'.symm.trans (pinnedX_zero τ L α).symm)) one_ne_zero
  ·
    obtain ⟨w₀, -, -, hw₀, hw₀sq, -⟩ := weyl_longest_element τ
    have hflip : ∀ γ, IsRoot τ γ → height γ < 0 → IsRoot τ (w₀ • γ) ∧ 0 < height (w₀ • γ) := by
      intro γ hγ hneg
      have hmem : γ ∈ (fun α => w₀ • α) '' {α | IsRoot τ α ∧ 0 < height α} := by
        rw [hw₀]; exact ⟨hγ, hneg⟩
      obtain ⟨β, ⟨hβr, hβp⟩, rfl⟩ := hmem
      have : w₀ • w₀ • β = β := by rw [← mul_smul, ← sq, hw₀sq, one_smul]
      rw [this]
      exact ⟨hβr, hβp⟩
    obtain ⟨ε₁, hε₁, h₁⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w₀ hα
    obtain ⟨ε₂, hε₂, h₂⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w₀ hα'
    have e : canonicalRep (coxeterSystem τ) L w₀ * pinnedX τ L α' c' *
        (canonicalRep (coxeterSystem τ) L w₀)⁻¹ =
        canonicalRep (coxeterSystem τ) L w₀ * pinnedX τ L α 1 *
        (canonicalRep (coxeterSystem τ) L w₀)⁻¹ := by rw [hc']
    rw [h₂, h₁] at e
    have hε₁0 : ε₁ ≠ 0 := fun h0 => by simp [h0] at hε₁
    have := eq_of_pinnedX_eq_pos (hflip α hα hn) (hflip α' hα' hn') e.symm (by simpa using hε₁0)
    exact (MulAction.injective w₀) this

end Distinct


section Step

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem LangSetup.q_pos : 0 < S.D.q := S.hqpow.1.pos

theorem FrobRootMap.step_pinnedX {D : LangDatum τ L}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρmap : FrobRootMap D ρ) (hq : 0 < D.q)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ μ : L, μ ≠ 0 ∧ ∀ c : L,
      D.step (pinnedX τ L γ c) = pinnedX τ L (ρ γ) (μ * c ^ D.q) := by
  obtain ⟨ρ₀, hroot₀, -, -, hstep⟩ := exists_step_pinnedX D
  obtain ⟨μ, hμ0, hμ⟩ := hstep γ hγ
  refine ⟨μ, hμ0, fun c => ?_⟩
  have hρ : ρ₀ γ = ρ γ := by
    have hmap := hρmap.map_rootSubgroup γ hγ
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (μ⁻¹) hq
    have h1 : D.step (pinnedX τ L γ x) ∈ (rootSubgroup τ L γ).map D.step :=
      Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ⟨x, rfl⟩)
    rw [hmap, hμ x, hx, mul_inv_cancel₀ hμ0] at h1
    exact eq_of_pinnedX_one_mem_rootSubgroup ((hroot₀ γ).2 hγ) ((hρmap.isRoot_iff γ).2 hγ) h1
  rw [hμ c, hρ]


theorem step_pinnedX {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ μ : L, μ ≠ 0 ∧ ∀ c : L,
      S.D.step (pinnedX τ L γ c) = pinnedX τ L (S.ρ γ) (μ * c ^ S.D.q) :=
  S.frob.step_pinnedX S.q_pos hγ

theorem LangSetup.iterate_isRoot (n : ℕ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    IsRoot τ ((S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ) := by
  induction n with
  | zero => exact hγ
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (S.frob.isRoot_iff _).2 ih

theorem iter_step_pinnedX (n : ℕ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ μ : L, μ ≠ 0 ∧ ∀ c : L,
      (S.D.step)^[n] (pinnedX τ L γ c) =
        pinnedX τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ) (μ * c ^ (S.D.q ^ n)) := by
  induction n with
  | zero => exact ⟨1, one_ne_zero, fun c => by simp⟩
  | succ n ih =>
    obtain ⟨μ, hμ0, hμ⟩ := ih
    obtain ⟨μ', hμ'0, hμ'⟩ := step_pinnedX S (S.iterate_isRoot n hγ)
    refine ⟨μ' * μ ^ S.D.q, mul_ne_zero hμ'0 (pow_ne_zero _ hμ0), fun c => ?_⟩
    rw [Function.iterate_succ_apply', hμ, hμ', Function.iterate_succ_apply']
    congr 1
    rw [mul_pow, ← pow_mul, pow_succ]
    ring

theorem rho_iterate_neg (n : ℕ) (γ : Fin τ.rank → ℤ) :
    (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]

end Step


section Twist

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem iterHom_eq_iterate {G : Type*} [Group G] (Φ : G →* G) (n : ℕ) (x : G) :
    iterHom Φ n x = Φ^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterHom_succ, ih, Function.iterate_succ_apply']

theorem exists_char_pow : ∃ r e : ℕ, r.Prime ∧ CharP L r ∧ 0 < e ∧ S.D.q = r ^ e := by
  obtain ⟨r, e, hr, he, hre⟩ := (isPrimePow_nat_iff _).1 S.hqpow.1
  have hr0 : ((r : ℕ) : L) = 0 := by
    have h := S.hqpow.2
    rw [← hre, Nat.cast_pow] at h
    exact (pow_eq_zero_iff (by omega)).1 h
  have : CharP L r := (CharP.charP_iff_prime_eq_zero hr).2 hr0
  exact ⟨r, e, hr, this, he, hre.symm⟩

theorem exists_ringEquiv_frob (r n : ℕ) [Fact r.Prime] [CharP L r] :
    ∃ σ : L ≃+* L, σ.toRingHom = iterateFrobenius L r n := by
  have hbij : Function.Bijective (iterateFrobenius L r n) := by
    refine ⟨(iterateFrobenius L r n).injective, fun c => ?_⟩
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (pow_pos (Fact.out : r.Prime).pos n)
    exact ⟨z, by rw [iterateFrobenius_def, hz]⟩
  exact ⟨RingEquiv.ofBijective (iterateFrobenius L r n) hbij, rfl⟩

theorem exists_step_frobTwist {r e : ℕ} [Fact r.Prime] [CharP L r] (he : S.D.q = r ^ e) :
    ∃ Q : ModGL τ L, entrywiseFrobGL τ L r e Q = Q ∧
      Q ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) ∧
      ∀ g, S.D.step g = frobTwistGL τ L r e Q g := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hFrE : Fr = iterateFrobenius L r e :=
    RingHom.ext fun c => by rw [hFr, iterateFrobenius_def, he]
  have hPfix : entrywiseFrobGL τ L r e P = P ∧
      P ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) := by
    rcases hP with rfl | ⟨t, h, rfl⟩
    · exact ⟨map_one _, one_mem _⟩
    · subst h
      exact ⟨units_map_entrywiseHom_diagramMap (iterateFrobenius L r e), diagramMap_mem_normalizer t⟩
  have hnfix : entrywiseFrobGL τ L r e S.D.n = S.D.n := by
    rw [hn]
    exact frobenius_canonicalRep (iterateFrobenius L r e) w
  refine ⟨S.D.n * P, by rw [map_mul, hPfix.1, hnfix], mul_mem ?_ hPfix.2, fun g => ?_⟩
  · rw [hn]
    exact canonicalRep_mem_normalizer w
  · rw [frobTwistGL_apply]
    show S.D.n * S.D.Φ g * S.D.n⁻¹ = _
    rw [hΦ g, hFrE]
    change S.D.n * (P * entrywiseFrobGL τ L r e g * P⁻¹) * S.D.n⁻¹ = _
    group

end Twist


section Untwist

theorem map_rootSpan_le_of_forall {τ : Tag} {L : Type} [Field L] {φ : ModGL τ L →* ModGL τ L}
    {S T : Set (Fin τ.rank → ℤ)}
    (h : ∀ γ ∈ S, ∀ c : L, φ (pinnedX τ L γ c) ∈ rootSpan τ L T) :
    (rootSpan τ L S).map φ ≤ rootSpan τ L T := by
  simp only [rootSpan, Subgroup.map_iSup]
  refine iSup₂_le fun γ hγ => ?_
  rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
  exact h γ hγ c

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem outer_rho_mem_kernelRoots {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ kernelRoots (rootCharHom a)) :
    S.ρ γ ∈ kernelRoots (rootCharHom a) := by
  rw [kernelRoots_rootCharHom] at hγ ⊢
  refine ⟨(S.frob.isRoot_iff γ).2 hγ.1, ?_⟩
  rw [S.frob.rootChar_eq a hT γ hγ.1, hγ.2, one_pow]

theorem outer_iterate_mem_kernelRoots {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (n : ℕ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ kernelRoots (rootCharHom a)) :
    (S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ ∈ kernelRoots (rootCharHom a) := by
  induction n with
  | zero => exact hγ
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact outer_rho_mem_kernelRoots S hT ih

theorem LangSetup.rho_mem_kernelRoots {a : Fin τ.rank → Lˣ} (hE : rootDiagUnit τ a ∈ S.E)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ kernelRoots (rootCharHom a)) :
    S.ρ γ ∈ kernelRoots (rootCharHom a) :=
  outer_rho_mem_kernelRoots S (S.E_le hE).1 hγ

theorem LangSetup.iterate_mem_kernelRoots {a : Fin τ.rank → Lˣ} (hE : rootDiagUnit τ a ∈ S.E)
    (n : ℕ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ kernelRoots (rootCharHom a)) :
    (S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ ∈ kernelRoots (rootCharHom a) :=
  outer_iterate_mem_kernelRoots S (S.E_le hE).1 n hγ

theorem exists_lang_torus_sup_kernelRoots {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {s : ℕ} (hs : 0 < s)
    (hker : ∀ γ ∈ kernelRoots χ, (S.ρ : (Fin τ.rank → ℤ) → _)^[s] γ ∈ kernelRoots χ)
    {y : ModGL τ L} (hy : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ)) :
    ∃ z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ), iterHom S.D.step s z = z * y := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨Q, hQfix, hQnorm, hstep⟩ := exists_step_frobTwist S hq
  have hstepeq : S.D.step = frobTwistGL τ L r e Q := MonoidHom.ext hstep
  set φ : ModGL τ L →* ModGL τ L := iterHom S.D.step s with hφdef
  have hφeq : ∀ g, φ g = Q ^ s * entrywiseFrobGL τ L r (e * s) g * (Q ^ s)⁻¹ := by
    intro g
    rw [hφdef, iterHom_eq_iterate, hstepeq, frobTwistGL_iterate r e hQfix s g]
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hfrobσ : ∀ g, entrywiseFrobGL τ L r (e * s) g = frobGL σ g := by
    intro g
    change Units.map (entrywiseHom (iterateFrobenius L r (e * s))) g =
      Units.map (entrywiseHom σ.toRingHom) g
    rw [hσ]
  have hφσ : ∀ g, φ g = Q ^ s * frobGL σ g * (Q ^ s)⁻¹ := fun g => by rw [hφeq, hfrobσ]
  set Z : Subgroup (ModGL τ L) := torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ) with hZ
  have hZconn :=
    CFSG.ClassicalInvolution.ModelFacts.Levi.isConnectedAlgebraicSubgroup_torus_sup_rootSpan
      (k := L) (τ := τ) χ
  have hQs : Q ^ s ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) := pow_mem hQnorm s
  have hφT : ∀ t ∈ torusGroup τ L, φ t ∈ torusGroup τ L := by
    intro t ht
    rw [hφσ]
    exact (Subgroup.mem_normalizer_iff.1 hQs _).1 (frobGL_mem_torusGroup σ ht)
  have hφR : ∀ g ∈ rootSpan τ L (kernelRoots χ), φ g ∈ rootSpan τ L (kernelRoots χ) := by
    have hmap : (rootSpan τ L (kernelRoots χ)).map φ ≤ rootSpan τ L (kernelRoots χ) := by
      refine map_rootSpan_le_of_forall fun γ hγ c => ?_
      obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s hγ.1
      rw [hφdef, iterHom_eq_iterate, hμ]
      exact pinnedX_mem_rootSpan (hker γ hγ) _
    exact fun g hg => hmap ⟨g, hg, rfl⟩
  have hφZ : ∀ g ∈ Z, frobTwistGL τ L r (e * s) (Q ^ s) g ∈ Z := by
    intro g hg
    have : frobTwistGL τ L r (e * s) (Q ^ s) g = φ g := by
      rw [frobTwistGL_apply, hφeq]
    rw [this]
    have hmap : Z.map φ ≤ Z := by
      rw [hZ, Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨t, ht, rfl⟩
        exact hφT t ht
      · rintro _ ⟨t, ht, rfl⟩
        exact hφR t ht
    exact hmap ⟨g, hg, rfl⟩
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction r hZconn (e := e * s)
    (Nat.mul_pos he hs) (Q ^ s) hφZ
  obtain ⟨z, hzZ, hz⟩ := hlang y hy
  refine ⟨z, hzZ, ?_⟩
  have h1 : frobTwistGL τ L r (e * s) (Q ^ s) z = φ z := by rw [frobTwistGL_apply, hφeq]
  rw [← h1]
  calc frobTwistGL τ L r (e * s) (Q ^ s) z =
      z * (z⁻¹ * frobTwistGL τ L r (e * s) (Q ^ s) z) := by group
    _ = z * y := by rw [hz]

theorem mem_componentRootSpan_iff_conj_of_mem {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {z : ModGL τ L}
    (hz : z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ)) (j : KernelComponent χ)
    (g : ModGL τ L) :
    g ∈ rootSpan τ L (componentRoots χ j) ↔ z * g * z⁻¹ ∈ rootSpan τ L (componentRoots χ j) := by
  obtain ⟨-, -, -, hSi, -⟩ := root_character_kernel_orthogonal_central_product τ L χ
  have hT : torusGroup τ L ≤ Subgroup.normalizer
      (rootSpan τ L (componentRoots χ j) : Set (ModGL τ L)) :=
    CFSG.Quasithin.SmithCurtis.Chev.torusGroup_le_normalizer_rootSpan _
      fun _ hα => isRoot_of_mem_componentRoots hα
  have hR : rootSpan τ L (kernelRoots χ) ≤ Subgroup.normalizer
      (rootSpan τ L (componentRoots χ j) : Set (ModGL τ L)) := by
    intro x hx
    obtain ⟨hSR, hSRn⟩ := hSi j
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have := hSRn.conj_mem ⟨g, hSR hg⟩ (Subgroup.mem_subgroupOf.2 hg) ⟨x, hx⟩
      exact Subgroup.mem_subgroupOf.1 this
    · intro hg
      have hx' : x⁻¹ ∈ rootSpan τ L (kernelRoots χ) := inv_mem hx
      have hSR' : x * g * x⁻¹ ∈ rootSpan τ L (kernelRoots χ) := hSR hg
      have := hSRn.conj_mem ⟨x * g * x⁻¹, hSR'⟩ (Subgroup.mem_subgroupOf.2 hg) ⟨x⁻¹, hx'⟩
      have h2 := Subgroup.mem_subgroupOf.1 this
      have h3 : g ∈ componentRootSpan L χ j := by simpa [mul_assoc] using h2
      exact h3
  exact Subgroup.mem_normalizer_iff.1 ((sup_le hT hR : _ ≤ _) hz) g

theorem outer_exists_lang {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) {s : ℕ}
    (hs : 0 < s) {y : ModGL τ L}
    (hy : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a))) :
    ∃ z : ModGL τ L, iterHom S.D.step s z = z * y ∧
      ∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
        g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
          z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j) := by
  obtain ⟨z, hzZ, hz⟩ := exists_lang_torus_sup_kernelRoots S hs
    (fun γ hγ => outer_iterate_mem_kernelRoots S hT s hγ) hy
  exact ⟨z, hz, mem_componentRootSpan_iff_conj_of_mem hzZ⟩

theorem exists_untwistT {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ} (hs : 0 < s)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s])) :
    ∃ (σ : L ≃+* L) (z : ModGL τ L), (∀ c, σ c = c ^ (S.D.q ^ s)) ∧
      (∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
        g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
          z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j)) ∧
      ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
        iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hσc : ∀ c, σ c = c ^ (S.D.q ^ s) := by
    intro c
    have h1 : σ c = iterateFrobenius L r (e * s) c := by
      rw [← hσ]
      rfl
    rw [h1, iterateFrobenius_def, hq, ← pow_mul]
  obtain ⟨w, hw, hwγ⟩ := hinner
  have hφpin : ∀ γ ∈ componentRoots (rootCharHom a) i, ∃ m : L, m ≠ 0 ∧
      ∀ c : L, iterHom S.D.step s (pinnedX τ L γ c) = pinnedX τ L (w • γ) (m * σ c) := by
    intro γ hγ
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s (isRoot_of_mem_componentRoots hγ)
    exact ⟨μ, hμ0, fun c => by rw [iterHom_eq_iterate, hμ, hwγ γ hγ, hσc]⟩
  obtain ⟨y₁, hy₁, hpin⟩ := exists_pin i σ (iterHom S.D.step s) hw hφpin
  obtain ⟨z, hφz, hnorm⟩ :=
    outer_exists_lang S hT hs ((sup_le_sup_left (rootSpan_mono fun γ hγ => hγ.1) _) hy₁)
  refine ⟨σ, z, hσc, hnorm, fun g hg => ?_⟩
  rw [map_mul, map_mul, map_inv, hφz]
  calc z * y₁ * iterHom S.D.step s g * (z * y₁)⁻¹ =
      z * (y₁ * iterHom S.D.step s g * y₁⁻¹) * z⁻¹ := by group
    _ = z * frobGL σ g * z⁻¹ := by rw [hpin g hg]

theorem exists_untwist {a : Fin τ.rank → Lˣ} (hE : rootDiagUnit τ a ∈ S.E)
    (i : KernelComponent (rootCharHom a)) {s : ℕ} (hs : 0 < s)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s])) :
    ∃ (σ : L ≃+* L) (z : ModGL τ L), (∀ c, σ c = c ^ (S.D.q ^ s)) ∧
      (∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
        g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
          z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j)) ∧
      ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
        iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ :=
  exists_untwistT S (S.E_le hE).1 i hs hinner

end Untwist

end CFSG.HardMathSupport.Timmesfeld.LangTorus

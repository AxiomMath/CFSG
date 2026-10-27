module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationTorusModels
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTransport

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits

section Fact

variable {K : Type*} [Group K] {k : Type*} [Field k]

@[expose] def ShortRootModelFact (D : UniversalRootDatum K) (x : (Fin D.rank → ℤ) → k → K) : Prop :=
  ∀ b : Fin D.rank → kˣ, (∀ i, b i = 1 ∨ b i = -1) →
    ∃ δ : K ≃* K,
      (∀ i c, δ (x (Pi.single i 1) c) = x (Pi.single i 1) ((b i : k) * c)) ∧
      (∀ i c, δ (x (-Pi.single i 1) c) = x (-Pi.single i 1) (((b i)⁻¹ : kˣ) * c)) ∧
      ∀ i, b i = 1 → ∃ Q₀ : Subgroup K,
        rankOne D.rootGroup i ≤ Q₀ ∧ IsComponentOf Q₀ (fixedGroup δ)

@[expose] def ToralShortRootFact (D : UniversalRootDatum K) (x : (Fin D.rank → ℤ) → k → K)
    (𝒯 : Set K) : Prop :=
  ∀ t ∈ 𝒯, (∀ i, ∃ b : kˣ, ActsDiagonallyOnSimple x (MonoidHom.id K) 1 i t b) ∧
    ∀ i (b : kˣ), ActsDiagonallyOnSimple x (MonoidHom.id K) 1 i t b → b = 1 →
      ∃ Q₀ : Subgroup K, rankOne D.rootGroup i ≤ Q₀ ∧
        IsComponentOf Q₀ (Subgroup.centralizer ({t} : Set K))

end Fact

section Transport

variable {K : Type*} [Group K] {X : Type*} [Group X] {k : Type*} [Field k]
  {D : UniversalRootDatum K} {x : (Fin D.rank → ℤ) → k → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem eq_one_or_neg_one_of_actsDiagonallyOnSimple (hX : ChevalleyExtras D k x C O) {ψ : K →* X}
    (hker : ψ.ker ≤ Subgroup.center K) (g : K) (i : Fin D.rank) {e : X} {a : kˣ}
    (he : ActsDiagonallyOnSimple x ψ g i e a) (he2 : e * e = 1) : a = 1 ∨ a = -1 :=
  eq_one_or_neg_one_of_actsByScalar (fun c d => map_conj_x_add hX ψ g (single_mem_roots D i) c d)
    (fun c h => eq_zero_of_ker_le_center_simple hX hker g i c h) he he2

theorem eq_one_of_centralizes_actsDiagonallyOnSimple (hX : ChevalleyExtras D k x C O) {ψ : K →* X}
    (hker : ψ.ker ≤ Subgroup.center K) (g : K) (i : Fin D.rank) {e : X} {a : kˣ}
    (he : ActsDiagonallyOnSimple x ψ g i e a)
    (hc : ∀ r ∈ rankOneImage D ψ g (Pi.single i 1), e * r = r * e) : a = 1 := by
  have hmem : ψ (g * x (Pi.single i 1) 1 * g⁻¹) ∈ rankOneImage D ψ g (Pi.single i 1) := by
    rw [rankOneImage_eq_pairGroup hX ψ g (single_mem_roots D i)]
    exact Subgroup.subset_closure (Or.inl ⟨1, rfl⟩)
  have h1 := hc _ hmem
  have hh : e * ψ (g * x (Pi.single i 1) 1 * g⁻¹) * e⁻¹ =
      ψ (g * x (Pi.single i 1) ((a : k) * 1) * g⁻¹) := he.1 1
  have h2 : ψ (g * x (Pi.single i 1) 1 * g⁻¹) =
      ψ (g * x (Pi.single i 1) ((a : k) * 1) * g⁻¹) := by
    rw [← hh, eq_comm, mul_inv_eq_iff_eq_mul]
    exact h1
  have h3 : ψ (g * x (Pi.single i 1) ((a : k) * 1 - 1) * g⁻¹) = 1 := by
    have h4 := map_conj_x_add hX ψ g (single_mem_roots D i) ((a : k) * 1 - 1) 1
    rw [sub_add_cancel, ← h2] at h4
    exact mul_eq_right.mp h4.symm
  have h5 := eq_zero_of_ker_le_center_simple hX hker g i _ h3
  have h6 : (a : k) = 1 := by linear_combination h5
  exact Units.ext (by rw [h6, Units.val_one])

theorem inComponentOfCentralizer_of_shortRootModelFact (hX : ChevalleyExtras D k x C O)
    (hgen : ⨆ i : Fin D.rank, rankOne D.rootGroup i = ⊤) (hfact : ShortRootModelFact D x)
    {ψ : K →* X} (hker : ψ.ker ≤ Subgroup.center K) (g : K) (e : X) (b : Fin D.rank → kˣ)
    (hb : ∀ i, ActsDiagonallyOnSimple x ψ g i e (b i)) (hb1 : ∀ i, b i = 1 ∨ b i = -1)
    {i : Fin D.rank} (hi : b i = 1) :
    InComponentOfCentralizer ψ.range (rankOneImage D ψ g (Pi.single i 1)) e := by
  obtain ⟨δ, hδx, hδy, hcomp⟩ := hfact b hb1
  have hδ := actsAs_automorphism_of_diagonal hX hgen ψ g e b hb δ hδx hδy
  obtain ⟨Q₀, hRQ, hQ⟩ := hcomp i hi
  rw [rankOneImage_eq_map ψ g (Pi.single i 1)]
  exact inComponentOfCentralizer_of_fixedGroup hker g e δ hδ hQ hRQ

theorem fixedGroup_conj_eq_centralizer (t : K) :
    fixedGroup (MulAut.conj t) = Subgroup.centralizer ({t} : Set K) := by
  ext y
  rw [mem_fixedGroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem actsDiagonallyOnSimple_of_actsAsConj (ψ : K →* X) (g : K) (e : X) {t : K}
    (hconj : ∀ y : K, e * ψ y * e⁻¹ = ψ (g * t * g⁻¹ * y * (g * t * g⁻¹)⁻¹)) {j : Fin D.rank}
    {a : kˣ} (ha : ActsDiagonallyOnSimple x (MonoidHom.id K) 1 j t a) :
    ActsDiagonallyOnSimple x ψ g j e a := by
  refine ⟨fun c => ?_, fun c => ?_⟩
  · rw [hconj]
    have h := ha.1 c
    simp only [MonoidHom.id_apply, inv_one, one_mul, mul_one] at h
    have e1 : g * t * g⁻¹ * (g * x (Pi.single j 1) c * g⁻¹) * (g * t * g⁻¹)⁻¹ =
        g * (t * x (Pi.single j 1) c * t⁻¹) * g⁻¹ := by group
    rw [e1, h]
  · rw [hconj]
    have h := ha.2 c
    simp only [MonoidHom.id_apply, inv_one, one_mul, mul_one] at h
    have e1 : g * t * g⁻¹ * (g * x (-Pi.single j 1) c * g⁻¹) * (g * t * g⁻¹)⁻¹ =
        g * (t * x (-Pi.single j 1) c * t⁻¹) * g⁻¹ := by group
    rw [e1, h]

theorem inComponentOfCentralizer_of_toralShortRootFact {𝒯 : Set K}
    (hfact : ToralShortRootFact D x 𝒯) {ψ : K →* X} (hker : ψ.ker ≤ Subgroup.center K) (g : K)
    {t : K} (ht : t ∈ 𝒯) {e : X}
    (he : ∀ y : K, e * ψ y * e⁻¹ = ψ (g * t * g⁻¹ * y * (g * t * g⁻¹)⁻¹)) {i : Fin D.rank}
    {b : kˣ} (hb : ActsDiagonallyOnSimple x (MonoidHom.id K) 1 i t b) (hb1 : b = 1) :
    InComponentOfCentralizer ψ.range (rankOneImage D ψ g (Pi.single i 1)) e := by
  obtain ⟨Q₀, hRQ, hQ⟩ := (hfact t ht).2 i b hb hb1
  have hδ : ∀ y : K, e * ψ (g * y * g⁻¹) * e⁻¹ = ψ (g * MulAut.conj t y * g⁻¹) := by
    intro y
    rw [he]
    congr 1
    simp only [MulAut.conj_apply]
    group
  rw [← fixedGroup_conj_eq_centralizer] at hQ
  rw [rankOneImage_eq_map ψ g (Pi.single i 1)]
  exact inComponentOfCentralizer_of_fixedGroup hker g e (MulAut.conj t) hδ hQ hRQ

end Transport

section Provider

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G}

theorem LayerGenerationLie.of_diagonalSimpleRoots_shortFact (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hE2 : ∀ x ∈ E, x * x = 1) {a : G} (ha : a ∈ E)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (htor : ∀ (D : LocalLieSystemAt p f Ω a) (j : Fin D.card) (F₀ : Subgroup G),
      CFSG.IsComponent (componentHom hΩ D j).range →
      IsFaithfulFourGroupAt E a (componentHom hΩ D j).range F₀ →
        ∃ (x : (Fin (compModel D j).D.rank → ℤ) → GaloisField p (D.exp j) → (compModel D j).K)
          (C : (Fin (compModel D j).D.rank → ℤ) → (Fin (compModel D j).D.rank → ℤ) →
            ℕ × ℕ → ℤ)
          (O : CommOrder (RootSystem.ofCartan (compModel D j).D.isFiniteType
            (compModel D j).D.divisible))
          (_ : ChevalleyExtras (compModel D j).D (GaloisField p (D.exp j)) x C O)
          (g : (compModel D j).K),
          (∀ e ∈ modOdd a F₀, ∀ i : Fin (compModel D j).D.rank, ∃ b : (GaloisField p (D.exp j))ˣ,
            ActsDiagonallyOnSimple x (componentHom hΩ D j) g i e b) ∧
          ShortRootModelFact (compModel D j).D x) :
    LayerGenerationLie Ω E a := by
  refine LayerGenerationLie.of_diagonalSimpleRoots_components hp2 h0 hA1 hq hΩ hIH hE2 ha hnc ?_
  intro D j F₀ hL hF
  obtain ⟨x, C, O, hX, g, hdiag, hfact⟩ := htor D j F₀ hL hF
  refine ⟨x, C, O, hX, g, hdiag, fun i _ => ?_⟩
  have hker := componentHom_ker_le_center hΩ D j
  have hF2 : ∀ y ∈ F₀, y * y = 1 := fun y hy => hE2 y (hF.1 hy)
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (comm_of_sq_eq_one hE2 ha (hF.1 hy)).symm
  have hcard : Nat.card (modOdd a F₀) = 4 := by
    rw [card_modOdd_of_exponent_two hFC hF2, hF.2.1]
  have hidx := indexTwoCentralizes_rankOneImage_simple hX hker g i
    (modOdd_sq_eq_one hE2 hF.1) fun e he => hdiag e he i
  obtain ⟨y, hy, hy1, hyc⟩ := exists_ne_one_centralizes_of_indexTwo
    (modOdd_sq_eq_one hE2 hF.1) le_rfl hcard hidx
  choose b hb using fun l => hdiag y hy l
  have hy2 : y * y = 1 := modOdd_sq_eq_one hE2 hF.1 y hy
  have hb1 : ∀ l, b l = 1 ∨ b l = -1 := fun l =>
    eq_one_or_neg_one_of_actsDiagonallyOnSimple hX hker g l (hb l) hy2
  have hhgen : ⨆ l : Fin (compModel D j).D.rank, rankOne (compModel D j).D.rootGroup l = ⊤ := by
    obtain ⟨_, _, hct, _⟩ := CFSG.ClassicalInvolution.ModelFacts.hasBruhatDatum (D.tag j)
      (D.rank j) p (D.exp j) Fact.out (D.isFundTag j) (D.admissible j)
    exact iSup_rankOne_eq_top _ hct
  exact ⟨y, hy, hy1, inComponentOfCentralizer_of_shortRootModelFact hX hhgen hfact hker g y b hb
    hb1 (eq_one_of_centralizes_actsDiagonallyOnSimple hX hker g i (hb i) hyc)⟩

theorem LayerGenerationLie.of_innerToral_shortFact (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hE2 : ∀ x ∈ E, x * x = 1) {a : G} (ha : a ∈ E)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (htor : ∀ (D : LocalLieSystemAt p f Ω a) (j : Fin D.card) (F₀ : Subgroup G),
      CFSG.IsComponent (componentHom hΩ D j).range →
      IsFaithfulFourGroupAt E a (componentHom hΩ D j).range F₀ →
        ∃ (x : (Fin (compModel D j).D.rank → ℤ) → GaloisField p (D.exp j) → (compModel D j).K)
          (C : (Fin (compModel D j).D.rank → ℤ) → (Fin (compModel D j).D.rank → ℤ) →
            ℕ × ℕ → ℤ)
          (O : CommOrder (RootSystem.ofCartan (compModel D j).D.isFiniteType
            (compModel D j).D.divisible))
          (_ : ChevalleyExtras (compModel D j).D (GaloisField p (D.exp j)) x C O)
          (g : (compModel D j).K) (𝒯 : Set (compModel D j).K),
          (∀ e ∈ modOdd a F₀, ∃ t ∈ 𝒯, ∀ y : (compModel D j).K,
            e * componentHom hΩ D j y * e⁻¹ =
              componentHom hΩ D j (g * t * g⁻¹ * y * (g * t * g⁻¹)⁻¹)) ∧
          ToralShortRootFact (compModel D j).D x 𝒯) :
    LayerGenerationLie Ω E a := by
  refine LayerGenerationLie.of_diagonalSimpleRoots_components hp2 h0 hA1 hq hΩ hIH hE2 ha hnc ?_
  intro D j F₀ hL hF
  obtain ⟨x, C, O, hX, g, 𝒯, hinner, hfact⟩ := htor D j F₀ hL hF
  have hker := componentHom_ker_le_center hΩ D j
  have hdiag : ∀ e ∈ modOdd a F₀, ∀ i : Fin (compModel D j).D.rank,
      ∃ b : (GaloisField p (D.exp j))ˣ, ActsDiagonallyOnSimple x (componentHom hΩ D j) g i e b := by
    intro e he i
    obtain ⟨t, ht, hconj⟩ := hinner e he
    obtain ⟨b, hb⟩ := (hfact t ht).1 i
    exact ⟨b, actsDiagonallyOnSimple_of_actsAsConj _ g e hconj hb⟩
  refine ⟨x, C, O, hX, g, hdiag, fun i _ => ?_⟩
  have hF2 : ∀ y ∈ F₀, y * y = 1 := fun y hy => hE2 y (hF.1 hy)
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (comm_of_sq_eq_one hE2 ha (hF.1 hy)).symm
  have hcard : Nat.card (modOdd a F₀) = 4 := by
    rw [card_modOdd_of_exponent_two hFC hF2, hF.2.1]
  have hidx := indexTwoCentralizes_rankOneImage_simple hX hker g i
    (modOdd_sq_eq_one hE2 hF.1) fun e he => hdiag e he i
  obtain ⟨y, hy, hy1, hyc⟩ := exists_ne_one_centralizes_of_indexTwo
    (modOdd_sq_eq_one hE2 hF.1) le_rfl hcard hidx
  obtain ⟨t, ht, hconj⟩ := hinner y hy
  obtain ⟨b, hb⟩ := (hfact t ht).1 i
  have hbψ : ActsDiagonallyOnSimple x (componentHom hΩ D j) g i y b :=
    actsDiagonallyOnSimple_of_actsAsConj _ g y hconj hb
  have hb1 : b = 1 := eq_one_of_centralizes_actsDiagonallyOnSimple hX hker g i hbψ hyc
  exact ⟨y, hy, hy1, inComponentOfCentralizer_of_toralShortRootFact hfact hker g ht hconj hb hb1⟩

end Provider

end CFSG.ClassicalInvolution.Balance

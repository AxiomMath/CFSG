module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortModel

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits

section Param

variable {K : Type*} [Group K] {X : Type} [Group X] {k : Type*} [Field k]

structure SimpleParam (D : UniversalRootDatum K) (k : Type*) [Field k]
    (x : (Fin D.rank → ℤ) → k → K) : Prop where
  param : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible)
    D.rootGroup x
  inj_central : ∀ {X : Type} [Group X] (ψ : K →* X), ψ.ker ≤ Subgroup.center K →
    ∀ (g : K) (i : Fin D.rank) (c : k), ψ (g * x (Pi.single i 1) c * g⁻¹) = 1 → c = 0

variable {D : UniversalRootDatum K} {x : (Fin D.rank → ℤ) → k → K}

theorem SimpleParam.of_chevalleyExtras
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hX : ChevalleyExtras D k x C O) : SimpleParam D k x :=
  ⟨hX.param, fun _ hker g i c h => eq_zero_of_ker_le_center_simple hX hker g i c h⟩

theorem SimpleParam.rankOneImage_eq_pairGroup (hP : SimpleParam D k x) (ψ : K →* X) (g : K)
    (i : Fin D.rank) :
    rankOneImage D ψ g (Pi.single i 1) =
      pairGroup (fun c => ψ (g * x (Pi.single i 1) c * g⁻¹))
        (fun c => ψ (g * x (-Pi.single i 1) c * g⁻¹)) := by
  have hγ : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := single_mem_roots D i
  have hγ' : -(Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hγ
  have h1 : (D.rootGroup (Pi.single i 1) : Set K) = Set.range (x (Pi.single i 1)) := by
    ext y
    exact (hP.param _ hγ).1 y
  have h2 : (D.rootGroup (-Pi.single i 1) : Set K) = Set.range (x (-Pi.single i 1)) := by
    ext y
    exact (hP.param _ hγ').1 y
  have h3 : D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1) =
      Subgroup.closure (Set.range (x (Pi.single i 1)) ∪ Set.range (x (-Pi.single i 1))) := by
    rw [Subgroup.closure_union, ← h1, ← h2, Subgroup.closure_eq, Subgroup.closure_eq]
  unfold rankOneImage rankOneRoot pairGroup
  rw [h3, Subgroup.map_map, MonoidHom.map_closure, Set.image_union, ← Set.range_comp,
    ← Set.range_comp]
  rfl

theorem SimpleParam.map_conj_x_add (hP : SimpleParam D k x) (ψ : K →* X) (g : K) (i : Fin D.rank)
    (c d : k) :
    ψ (g * x (Pi.single i 1) (c + d) * g⁻¹) =
      ψ (g * x (Pi.single i 1) c * g⁻¹) * ψ (g * x (Pi.single i 1) d * g⁻¹) := by
  rw [(hP.param _ (single_mem_roots D i)).2.1, ← map_mul]
  congr 1
  group

theorem SimpleParam.eq_one_or_neg_one_of_actsDiagonallyOnSimple (hP : SimpleParam D k x)
    {ψ : K →* X} (hker : ψ.ker ≤ Subgroup.center K) (g : K) (i : Fin D.rank) {e : X} {a : kˣ}
    (he : ActsDiagonallyOnSimple x ψ g i e a) (he2 : e * e = 1) : a = 1 ∨ a = -1 :=
  eq_one_or_neg_one_of_actsByScalar (fun c d => hP.map_conj_x_add ψ g i c d)
    (fun c h => hP.inj_central ψ hker g i c h) he he2

theorem SimpleParam.indexTwoCentralizes_rankOneImage_simple (hP : SimpleParam D k x)
    {ψ : K →* X} (hker : ψ.ker ≤ Subgroup.center K) (g : K) (i : Fin D.rank) {Ē : Subgroup X}
    (hĒ2 : ∀ y ∈ Ē, y * y = 1)
    (hdiag : ∀ e ∈ Ē, ∃ a : kˣ, ActsDiagonallyOnSimple x ψ g i e a) :
    IndexTwoCentralizes Ē (rankOneImage D ψ g (Pi.single i 1)) := by
  rw [hP.rankOneImage_eq_pairGroup ψ g i]
  exact indexTwoCentralizes_pairGroup_of_scalar hĒ2
    (fun c d => hP.map_conj_x_add ψ g i c d) (fun c h => hP.inj_central ψ hker g i c h) hdiag

theorem SimpleParam.eq_one_of_centralizes_actsDiagonallyOnSimple (hP : SimpleParam D k x)
    {ψ : K →* X} (hker : ψ.ker ≤ Subgroup.center K) (g : K) (i : Fin D.rank) {e : X} {a : kˣ}
    (he : ActsDiagonallyOnSimple x ψ g i e a)
    (hc : ∀ r ∈ rankOneImage D ψ g (Pi.single i 1), e * r = r * e) : a = 1 := by
  have hmem : ψ (g * x (Pi.single i 1) 1 * g⁻¹) ∈ rankOneImage D ψ g (Pi.single i 1) := by
    rw [hP.rankOneImage_eq_pairGroup ψ g i]
    exact Subgroup.subset_closure (Or.inl ⟨1, rfl⟩)
  have h1 := hc _ hmem
  have hh : e * ψ (g * x (Pi.single i 1) 1 * g⁻¹) * e⁻¹ =
      ψ (g * x (Pi.single i 1) ((a : k) * 1) * g⁻¹) := he.1 1
  have h2 : ψ (g * x (Pi.single i 1) 1 * g⁻¹) =
      ψ (g * x (Pi.single i 1) ((a : k) * 1) * g⁻¹) := by
    rw [← hh, eq_comm, mul_inv_eq_iff_eq_mul]
    exact h1
  have h3 : ψ (g * x (Pi.single i 1) ((a : k) * 1 - 1) * g⁻¹) = 1 := by
    have h4 := hP.map_conj_x_add ψ g i ((a : k) * 1 - 1) 1
    rw [sub_add_cancel, ← h2] at h4
    exact mul_eq_right.mp h4.symm
  have h5 := hP.inj_central ψ hker g i _ h3
  have h6 : (a : k) = 1 := by linear_combination h5
  exact Units.ext (by rw [h6, Units.val_one])

theorem SimpleParam.actsAs_automorphism_of_diagonal (hP : SimpleParam D k x)
    (hgen : ⨆ i : Fin D.rank, rankOne D.rootGroup i = ⊤) (ψ : K →* X) (g : K) (e : X)
    (b : Fin D.rank → kˣ) (hb : ∀ i, ActsDiagonallyOnSimple x ψ g i e (b i)) (δ : K ≃* K)
    (hδx : ∀ i c, δ (x (Pi.single i 1) c) = x (Pi.single i 1) ((b i : k) * c))
    (hδy : ∀ i c, δ (x (-Pi.single i 1) c) = x (-Pi.single i 1) (((b i)⁻¹ : kˣ) * c))
    (y : K) : e * ψ (g * y * g⁻¹) * e⁻¹ = ψ (g * δ y * g⁻¹) := by
  set Ψ : K →* X := ψ.comp (MulAut.conj g).toMonoidHom with hΨ
  have hle : (⊤ : Subgroup K) ≤ MonoidHom.eqLocus ((MulAut.conj e).toMonoidHom.comp Ψ)
      (Ψ.comp δ.toMonoidHom) := by
    rw [← hgen]
    refine iSup_le fun i => sup_le (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨c, rfl⟩ := ((hP.param _ (single_mem_roots D i)).1 z).mp hz
      show e * ψ (g * x (Pi.single i 1) c * g⁻¹) * e⁻¹ = ψ (g * δ (x (Pi.single i 1) c) * g⁻¹)
      rw [(hb i).1 c, hδx]
    · obtain ⟨c, rfl⟩ := ((hP.param _ ((RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _
        (single_mem_roots D i))).1 z).mp hz
      show e * ψ (g * x (-Pi.single i 1) c * g⁻¹) * e⁻¹ = ψ (g * δ (x (-Pi.single i 1) c) * g⁻¹)
      rw [(hb i).2 c, hδy]
  exact hle (Subgroup.mem_top y)

theorem SimpleParam.inComponentOfCentralizer_of_shortRootModelFact (hP : SimpleParam D k x)
    (hgen : ⨆ i : Fin D.rank, rankOne D.rootGroup i = ⊤) (hfact : ShortRootModelFact D x)
    {ψ : K →* X} (hker : ψ.ker ≤ Subgroup.center K) (g : K) (e : X) (b : Fin D.rank → kˣ)
    (hb : ∀ i, ActsDiagonallyOnSimple x ψ g i e (b i)) (hb1 : ∀ i, b i = 1 ∨ b i = -1)
    {i : Fin D.rank} (hi : b i = 1) :
    InComponentOfCentralizer ψ.range (rankOneImage D ψ g (Pi.single i 1)) e := by
  obtain ⟨δ, hδx, hδy, hcomp⟩ := hfact b hb1
  have hδ := hP.actsAs_automorphism_of_diagonal hgen ψ g e b hb δ hδx hδy
  obtain ⟨Q₀, hRQ, hQ⟩ := hcomp i hi
  rw [rankOneImage_eq_map ψ g (Pi.single i 1)]
  exact inComponentOfCentralizer_of_fixedGroup hker g e δ hδ hQ hRQ

end Param

section Provider

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G}

theorem LayerGenerationLie.of_simpleParam_shortFact (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hE2 : ∀ x ∈ E, x * x = 1) {a : G} (ha : a ∈ E)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (htor : ∀ (D : LocalLieSystemAt p f Ω a) (j : Fin D.card) (F₀ : Subgroup G),
      CFSG.IsComponent (componentHom hΩ D j).range →
      IsFaithfulFourGroupAt E a (componentHom hΩ D j).range F₀ →
        ∃ (x : (Fin (compModel D j).D.rank → ℤ) → GaloisField p (D.exp j) → (compModel D j).K)
          (g : (compModel D j).K),
          SimpleParam (compModel D j).D (GaloisField p (D.exp j)) x ∧
          (∀ e ∈ modOdd a F₀, ∀ i : Fin (compModel D j).D.rank, ∃ b : (GaloisField p (D.exp j))ˣ,
            ActsDiagonallyOnSimple x (componentHom hΩ D j) g i e b) ∧
          ShortRootModelFact (compModel D j).D x) :
    LayerGenerationLie Ω E a := by
  refine LayerGenerationLie.of_toralSimpleRoots_components hp2 h0 hA1 hq hΩ hIH hE2 ha hnc ?_
  intro D j F₀ hL hF
  obtain ⟨x, g, hP, hdiag, hfact⟩ := htor D j F₀ hL hF
  have hker := componentHom_ker_le_center hΩ D j
  have hF2 : ∀ y ∈ F₀, y * y = 1 := fun y hy => hE2 y (hF.1 hy)
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (comm_of_sq_eq_one hE2 ha (hF.1 hy)).symm
  have hcard : Nat.card (modOdd a F₀) = 4 := by
    rw [card_modOdd_of_exponent_two hFC hF2, hF.2.1]
  have hhgen : ⨆ l : Fin (compModel D j).D.rank, rankOne (compModel D j).D.rootGroup l = ⊤ := by
    obtain ⟨_, _, hct, _⟩ := CFSG.ClassicalInvolution.ModelFacts.hasBruhatDatum (D.tag j)
      (D.rank j) p (D.exp j) Fact.out (D.isFundTag j) (D.admissible j)
    exact iSup_rankOne_eq_top _ hct
  refine ⟨g, fun i => hP.indexTwoCentralizes_rankOneImage_simple hker g i
    (modOdd_sq_eq_one hE2 hF.1) fun e he => hdiag e he i, fun i _ => ?_⟩
  obtain ⟨y, hy, hy1, hyc⟩ := exists_ne_one_centralizes_of_indexTwo
    (modOdd_sq_eq_one hE2 hF.1) le_rfl hcard
    (hP.indexTwoCentralizes_rankOneImage_simple hker g i (modOdd_sq_eq_one hE2 hF.1)
      fun e he => hdiag e he i)
  choose b hb using fun l => hdiag y hy l
  have hy2 : y * y = 1 := modOdd_sq_eq_one hE2 hF.1 y hy
  have hb1 : ∀ l, b l = 1 ∨ b l = -1 := fun l =>
    hP.eq_one_or_neg_one_of_actsDiagonallyOnSimple hker g l (hb l) hy2
  exact ⟨y, hy, hy1, hP.inComponentOfCentralizer_of_shortRootModelFact hhgen hfact hker g y b hb
    hb1 (hP.eq_one_of_centralizes_actsDiagonallyOnSimple hker g i (hb i) hyc)⟩

end Provider

end CFSG.ClassicalInvolution.Balance

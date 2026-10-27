module

public import CFSG.LieType.Chevalley.E6GraphFullDiagonalCoset
public import CFSG.LieType.Chevalley.CLSEvenE6FieldInvolutionFourGroup
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionCentralizerRank

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley.E6SecondGraphFixed

section General

variable {G : Type*} [Group G]

theorem exists_four_le_eqLocus_of_conj {C : Type*} [Group C] {α β φ : MulAut C}
    (hφ : φ * α * φ⁻¹ = β) {A : Subgroup C}
    (hA : A ≤ β.toMonoidHom.eqLocus (MonoidHom.id C)) (hEA : CFSG.Open.IsElemAbelian 2 A)
    (hcard : Nat.card A = 4) :
    ∃ A' : Subgroup C, A' ≤ α.toMonoidHom.eqLocus (MonoidHom.id C) ∧
      CFSG.Open.IsElemAbelian 2 A' ∧ Nat.card A' = 4 := by
  refine ⟨A.map φ.symm.toMonoidHom, ?_, isElemAbelian_two_map hEA _, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    have hβa : β a = a := hA ha
    have hα : α = φ⁻¹ * β * φ := by
      rw [← hφ]
      group
    change α (φ.symm a) = φ.symm a
    rw [hα]
    change φ.symm (β (φ (φ.symm a))) = φ.symm a
    rw [MulEquiv.apply_symm_apply, hβa]
  · rw [Subgroup.card_map_of_injective φ.symm.injective, hcard]

theorem two_le_pRank_of_isSimpleGroup {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) : 2 ≤ CFSG.pRank 2 S :=
  two_le_pRank_of_isQuasisimple_of_odd_center (isQuasisimple_of_isSimpleGroup hS) (by
    rw [center_eq_bot_of_isSimpleGroup hS, Subgroup.card_bot]
    exact odd_one)

theorem exists_four_le_eqLocus_of_fixed_eq {C J : Subgroup G} (hJC : J ≤ C) [Finite J]
    [IsSimpleGroup J] (hnc : ∃ x y : J, x * y ≠ y * x) {η : MulAut C}
    (hfix : ∀ g : C, η g = g ↔ (g : G) ∈ J) :
    ∃ A : Subgroup C, A ≤ η.toMonoidHom.eqLocus (MonoidHom.id C) ∧
      CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 4 := by
  obtain ⟨A₀, hA₀, hcard₀⟩ := exists_four_group_of_two_le_pRank (two_le_pRank_of_isSimpleGroup hnc)
  let ι : J →* C := Subgroup.inclusion hJC
  have hι : Function.Injective ι := Subgroup.inclusion_injective hJC
  refine ⟨A₀.map ι, ?_, isElemAbelian_two_map hA₀ ι, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact (hfix (ι y)).2 y.2
  · rw [Subgroup.card_map_of_injective hι, hcard₀]

theorem exists_four_le_eqLocus_of_fixed_eq_centralizer {C J : Subgroup G} (hJC : J ≤ C)
    [Finite J] [IsSimpleGroup J] (hnc : ∃ x y : J, x * y ≠ y * x) {t : G} (htJ : t ∈ J)
    (ht2 : t * t = 1) {ξ : MulAut C} (hfix : ∀ g : C, ξ g = g ↔ (g : G) ∈ J ∧ t * g = g * t) :
    ∃ A : Subgroup C, A ≤ ξ.toMonoidHom.eqLocus (MonoidHom.id C) ∧
      CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 4 := by
  set t' : J := ⟨t, htJ⟩
  have ht' : t' ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact ht2)
  have hrank := involution_centralizer_contains_four_group (two_le_pRank_of_isSimpleGroup hnc) ht'
  obtain ⟨A₀, hA₀, hcard₀⟩ := exists_four_group_of_two_le_pRank hrank
  let ι : Subgroup.centralizer ({t'} : Set J) →* C :=
    (Subgroup.inclusion hJC).comp (Subgroup.centralizer ({t'} : Set J)).subtype
  have hι : Function.Injective ι :=
    (Subgroup.inclusion_injective hJC).comp Subtype.val_injective
  refine ⟨A₀.map ι, ?_, isElemAbelian_two_map hA₀ ι, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    have hy := Subgroup.mem_centralizer_singleton_iff.1 y.2
    refine (hfix (ι y)).2 ⟨(y : J).2, ?_⟩
    exact (congrArg Subtype.val hy).symm
  · rw [Subgroup.card_map_of_injective hι, hcard₀]

end General

theorem exists_ne_comm_of_mulEquiv_adjointGroup_F4
    {k : Type} [Field k] (h2 : (2 : k) = 0)
    {H : Type*} [Group H] (e : H ≃* adjointGroup Tag.F4 k) : ∃ x y : H, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have hab : ∀ a b : adjointGroup Tag.F4 k, a * b = b * a := fun a b => by
    apply e.symm.injective
    rw [map_mul, map_mul, hcon]
  have hbot : commutator (adjointGroup Tag.F4 k) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hab y x
  rw [single_edge_perfect Tag.F4 k (Or.inl rfl)] at hbot
  have hx := orderOf_xElement_F4 (k := k) h2
  have h1 : xElement (τ := Tag.F4) ⟨0, by decide⟩ (1 : k) = 1 := by
    have hmem : xElement (τ := Tag.F4) ⟨0, by decide⟩ (1 : k) ∈ (⊤ : Subgroup _) :=
      Subgroup.mem_top _
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  rw [h1, orderOf_one] at hx
  exact absurd hx (by decide)

theorem even_E6_graph_involution_fixed_four_group_ordinary
    {f : ℕ} (hf : 1 ≤ f) (k : Type)
    [Field k] (hk : Nat.card k = 2 ^ f) (α : MulAut (adjointGroup TwistTag.E6.tag k))
    (hα : E6GraphFullCoset.IsOrdinaryDiagGraph k α) (hα2 : α ^ 2 = 1) :
    ∃ A : Subgroup (adjointGroup TwistTag.E6.tag k),
      A ≤ α.toMonoidHom.eqLocus (MonoidHom.id _) ∧ CFSG.Open.IsElemAbelian 2 A ∧
        Nat.card A = 4 := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hk2 : ringChar k = 2 := ringChar_eq_two_of_card hf hk
  have h2 : (2 : k) = 0 := two_eq_zero_of_ringChar hk2
  set L := GaloisField 2 (2 * f)
  have hL : Nat.card L = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card hf hk hL
  let _ : Algebra k L := ι.toAlgebra
  let σ : L →+* L := iterateFrobenius L 2 f
  have hσ : ∀ c, σ c = c ^ 2 ^ f := fun c => iterateFrobenius_def (p := 2) f c
  obtain ⟨ht, η, hη, hclass, -⟩ := (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).1 k hk
  obtain ⟨⟨⟨η₀, hη₀, -, hJC, hfix₀, hsimple, -⟩, e, -⟩, -⟩ :=
    even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf k L hk hL σ hσ
  obtain ⟨-, -, -, -, ⟨-, -, -, ⟨htJ, hJC₁, η₁, hη₁, huniq, -, -, hfix₁, -⟩⟩, -⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup f hf k L hk hL σ hσ
  have : IsSimpleGroup ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
    (baseChangeGL (RingHom.id k))) := hsimple
  have : Finite ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
    (baseChangeGL (RingHom.id k))) := Finite.of_equiv _ e.symm.toEquiv
  have hnc := exists_ne_comm_of_mulEquiv_adjointGroup_F4 h2 e
  have hη₀η : η₀ = η := MulEquiv.ext fun g => Subtype.ext ((hη₀ g).trans (hη g).symm)
  have hη₁η : η₁ = η := (huniq η hη).symm
  subst hη₀η hη₁η
  rcases hclass α hα hα2 with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · obtain ⟨A, hA, hEA, hcard⟩ := exists_four_le_eqLocus_of_fixed_eq hJC hnc hfix₀
    exact exists_four_le_eqLocus_of_conj hφ hA hEA hcard
  · obtain ⟨A, hA, hEA, hcard⟩ := exists_four_le_eqLocus_of_fixed_eq_centralizer hJC hnc htJ
      (pinnedX_e6HighestRoot_mul_self hk2) hfix₁
    exact exists_four_le_eqLocus_of_conj hφ hA hEA hcard

theorem even_E6_graph_involution_fixed_four_group_twisted
    {f : ℕ} (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ)) (hout : ∀ c, α ≠ MulAut.conj c)
    (hα2 : α ^ 2 = 1) :
    ∃ A : Subgroup (graphFixedRootGroup TwistTag.E6 K σ),
      A ≤ α.toMonoidHom.eqLocus (MonoidHom.id _) ∧ CFSG.Open.IsElemAbelian 2 A ∧
        Nat.card A = 4 := by
  have hK2 : ringChar K = 2 :=
    ringChar_eq_two_of_card (n := 2 * f) (by omega) (by rw [hK, ← pow_mul, mul_comm])
  set k := GaloisField 2 f
  have hk : Nat.card k = 2 ^ f := GaloisField.card 2 f (by omega)
  have hk2 : ringChar k = 2 := ringChar_eq_two_of_card hf hk
  have h2 : (2 : k) = 0 := two_eq_zero_of_ringChar hk2
  obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card hf hk hK
  let _ : Algebra k K := ι.toAlgebra
  obtain ⟨ht, η, hη, -, -, hclass, -⟩ :=
    (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).2 K hK σ hσ
  obtain ⟨-, ⟨⟨η₀, hη₀, -, hJC, hfix₀, hsimple, -⟩, e, -⟩⟩ :=
    even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf k K hk hK σ hσ
  obtain ⟨-, -, -, -, -, ⟨-, -, -, ⟨htJ, hJC₁, η₁, hη₁, huniq, -, -, hfix₁, -⟩⟩⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup f hf k K hk hK σ hσ
  have : IsSimpleGroup ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
    (baseChangeGL (algebraMap k K))) := hsimple
  have : Finite ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
    (baseChangeGL (algebraMap k K))) := Finite.of_equiv _ e.symm.toEquiv
  have hnc := exists_ne_comm_of_mulEquiv_adjointGroup_F4 h2 e
  have hη₀η : η₀ = η := MulEquiv.ext fun g => Subtype.ext ((hη₀ g).trans (hη g).symm)
  have hη₁η : η₁ = η := (huniq η hη).symm
  subst hη₀η hη₁η
  rcases hclass α hα2 hout with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · obtain ⟨A, hA, hEA, hcard⟩ := exists_four_le_eqLocus_of_fixed_eq hJC hnc hfix₀
    exact exists_four_le_eqLocus_of_conj hφ hA hEA hcard
  · obtain ⟨A, hA, hEA, hcard⟩ := exists_four_le_eqLocus_of_fixed_eq_centralizer hJC hnc htJ
      (pinnedX_e6HighestRoot_mul_self hK2) hfix₁
    exact exists_four_le_eqLocus_of_conj hφ hA hEA hcard

theorem even_E6_graph_involution_fixed_four_group
    (f : ℕ) (hf : 1 ≤ f) :
    (∀ (k : Type) [Field k], Nat.card k = 2 ^ f →
      ∀ (α : MulAut (adjointGroup TwistTag.E6.tag k)) (g : ModGL TwistTag.E6.tag k)
        (a : Fin TwistTag.E6.tag.rank → kˣ), g ∈ adjointGroup TwistTag.E6.tag k →
        (∀ h : adjointGroup TwistTag.E6.tag k, (α h : ModGL TwistTag.E6.tag k) =
          g * rootDiagUnit TwistTag.E6.tag a *
            (diagramMap TwistTag.E6 k * h * (diagramMap TwistTag.E6 k)⁻¹) *
              (g * rootDiagUnit TwistTag.E6.tag a)⁻¹) →
        α ^ 2 = 1 →
        ∃ A : Subgroup (adjointGroup TwistTag.E6.tag k),
          A ≤ α.toMonoidHom.eqLocus (MonoidHom.id _) ∧ CFSG.Open.IsElemAbelian 2 A ∧
            Nat.card A = 4) ∧
    (∀ (K : Type) [Field K], Nat.card K = (2 ^ f) ^ 2 → ∀ σ : K →+* K, (∀ c, σ c = c ^ 2 ^ f) →
      ∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σ), (∀ c, α ≠ MulAut.conj c) →
        α ^ 2 = 1 →
        ∃ A : Subgroup (graphFixedRootGroup TwistTag.E6 K σ),
          A ≤ α.toMonoidHom.eqLocus (MonoidHom.id _) ∧ CFSG.Open.IsElemAbelian 2 A ∧
            Nat.card A = 4) :=
  ⟨fun k _ hk α g a hg hα hα2 =>
    even_E6_graph_involution_fixed_four_group_ordinary hf k hk α ⟨g, a, hg, hα⟩ hα2,
    fun K _ hK σ hσ α hout hα2 =>
      even_E6_graph_involution_fixed_four_group_twisted hf K hK σ hσ α hout hα2⟩

end CFSG.LieType.Chevalley

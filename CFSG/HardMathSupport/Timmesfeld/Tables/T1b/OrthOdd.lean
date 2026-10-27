module

public import CFSG.RankThree.PartOne.S11d.OutOrthogonal

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.RankThree.PartOne.OutStructure Matrix Subgroup QuadraticMap
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open scoped commutatorElement

section Generic

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem linearConjugationHom_range_eq_orthD :
    (linearConjugationHom Q).range = orthD Q := by
  ext δ
  rw [mem_orthD_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩

theorem orthD_relIndex_inner_not_dvd' [Finite K] (hQ : ∃ v, Q v ≠ 0)
    (hab : ∃ k : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ k) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived Q)).relIndex (orthD Q) := by
  have h1 : CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤
      (isometryConjugationHom Q).range := by
    rw [inner_eq_map_commutator Q]
    exact Subgroup.map_le_range _ _
  have h2 : (isometryConjugationHom Q).range ≤ (linearConjugationHom Q).range :=
    isometryConjugationHom_range_le Q
  rw [← linearConjugationHom_range_eq_orthD, ← Subgroup.relIndex_mul_relIndex _ _ _ h1 h2]
  intro hdvd
  have : Finite (Abelianization (matrixIsometries Q)) := inferInstance
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
  · have h3 := h.trans (relIndex_inner_dvd Q)
    obtain ⟨k, hk⟩ := hab
    rw [hk] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3))
  · have h3 := h.trans (relIndex_isometryRange_dvd Q hQ)
    have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = Nat.gcd (Nat.card K - 1) 2 := by
      rw [IsCyclic.index_powMonoidHom_range, Nat.card_units]
    rw [hsq] at h3
    have h4 := Nat.le_of_dvd (by norm_num) (h3.trans (Nat.gcd_dvd_right _ _))
    have := hp.two_le
    omega

theorem orthD_D2_of_bound' [Finite K] (hQ : ∃ v, Q v ≠ 0)
    (hab : ∃ k : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ k) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {δ : MulAut (matrixProjectiveDerived Q)} (hδ : δ ∈ orthD Q) {k : ℕ}
    (hk : δ ^ (p ^ k) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived Q)) :
    δ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
  set D := orthD Q with hD
  set I := CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q)
    with hI
  set x : D ⧸ I.subgroupOf D := QuotientGroup.mk (⟨δ, hδ⟩ : D) with hx
  have hxk : x ^ (p ^ k) = 1 := by
    rw [hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hk
  have hcard : Nat.card (D ⧸ I.subgroupOf D) = I.relIndex D := (Subgroup.index_eq_card _).symm
  have hdvd1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hxk
  have hdvd2 : orderOf x ∣ I.relIndex D := hcard ▸ orderOf_dvd_natCard x
  have hcop : Nat.Coprime (p ^ k) (I.relIndex D) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (orthD_relIndex_inner_not_dvd' Q hQ hab hp hp2))
  have hx1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have : x = 1 := orderOf_eq_one_iff.mp hx1
  have hmem := (QuotientGroup.eq_one_iff (⟨δ, hδ⟩ : D)).mp this
  exact Subgroup.mem_subgroupOf.mp hmem

theorem outPNice_of_image_top_odd [Finite K] (hQ : ∃ v, Q v ≠ 0)
    (hab : ∃ k : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ k) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (htop : matrixProjectiveImage Q = ⊤) :
    OutPNice p (matrixProjectiveDerived Q) := by
  obtain ⟨g₀, hg₀⟩ := exists_gen Q
  have hmem : ∀ α : MulAut (matrixProjectiveDerived Q),
      ∃ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = α := fun α =>
    (mem_matrixProjectiveImage_iff Q α).mp (htop ▸ Subgroup.mem_top α)
  exact outPNice_of_tower hp (matrixProjectiveConjugationHom Q g₀) (D := orthD Q) (E := ⊤)
    (fun δ hδ => inner_le_orthD Q hδ)
    (fun δ hδ k hk => orthD_D2_of_bound' Q hQ hab hp hp2 hδ hk)
    (fun α _ => trivial)
    (fun γ α _ => by
      obtain ⟨g, rfl⟩ := hmem γ
      obtain ⟨h, rfl⟩ := hmem α
      exact comm_mem_orthD Q g h)
    (fun α _ => by
      obtain ⟨h, rfl⟩ := hmem α
      obtain ⟨k, hk⟩ := hg₀ h
      exact ⟨k, (mem_orthD_iff Q _).mpr ⟨⟨g₀ ^ k * h, hk⟩, by rw [map_mul, map_zpow]⟩⟩)

end Generic

theorem card_abelianization_two_pow_of_bound {K : Type} [Field K] [Finite K] {ι : Type}
    [Fintype ι] [DecidableEq ι] {d ℓ : ℕ} (e : ι ≃ Fin d) (Q₀ : QuadraticForm K (ι → K))
    (hab : IsometryAbelianizationBound ℓ Q₀) :
    ∃ k : ℕ, Nat.card (Abelianization (matrixIsometries (reindexQuadraticForm e Q₀))) = 2 ^ k := by
  rw [card_abelianization_matrixIsometries_reindex]
  have hP : IsPGroup 2 (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q₀)) := fun x => by
    obtain ⟨c, hc⟩ := hab.1.exponent_dvd_p
    refine ⟨1, ?_⟩
    rw [pow_one, hc, pow_mul, Monoid.pow_exponent_eq_one, one_pow]
  exact hP.exists_card_eq


section Models

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.Automorphisms
open scoped Pointwise

theorem outPNice_POmegaOdd_all {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    {n r m : ℕ} (h : StatedClassicalModel X .POmegaOdd n r m) : OutPNice p X := by
  have h0 := h
  obtain ⟨⟨-, -, hn, hr2⟩, K, _, _, hK, ⟨e⟩⟩ := h0
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_odd h K hK e
  have hQ : ∃ v, coordinateQuadOdd n K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaOdd (.inl rfl) n r m
    h K hK (quadOdd n K) (coe_quadOdd n K) e
  have hab' := card_abelianization_two_pow_of_bound (oddIndexEquiv n) (quadOdd n K) hab
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_odd K n hn
    (by rw [hchar]; exact hr2)
  exact OutPNice.of_mulEquiv (coordinateOddWitnessEquiv K e)
    (outPNice_of_image_top_odd _ hQ hab' hp hp2 htop)

theorem outPNice_POmegaPlus_all_ge_five {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type}
    [Group X] {n r m : ℕ} (hn : 5 ≤ n) (h : StatedClassicalModel X .POmegaPlus n r m) :
    OutPNice p X := by
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hQ : ∃ v, coordinateQuadPlus n K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) n r m h K hK (quadPlus n K) (coe_quadPlus n K) e
  have hab' := card_abelianization_two_pow_of_bound (plusIndexEquiv n) (quadPlus n K) hab
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn
  exact OutPNice.of_mulEquiv (coordinatePlusWitnessEquiv K e)
    (outPNice_of_image_top_odd _ hQ hab' hp hp2 htop)

theorem outPNice_POmegaMinus_all {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    {n r m : ℕ} (h : StatedClassicalModel X .POmegaMinus n r m) : OutPNice p X := by
  have h0 := h
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
  have hn1 : 1 ≤ n := by omega
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  have hQ : ∃ v, coordinateQuadMinus n K hn1 b c v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaMinus
    (.inr (.inr rfl)) n r m h K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
  have hab' := card_abelianization_two_pow_of_bound (minusIndexEquiv n hn1) (quadMinus n K b c) hab
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn
    b c hirr
  exact OutPNice.of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e)
    (outPNice_of_image_top_odd _ hQ hab' hp hp2 htop)

end Models

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b

module

public import CFSG.ClassicalInvolution.Asc77.AscT3Basic
public import CFSG.ClassicalInvolution.Asc77.WP2Defs

public section

namespace CFSG.ClassicalInvolution.Asc77.T3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

section Defs

variable {G : Type} [Group G]

@[expose] def aSet (Ω : Set (Subgroup G)) (K : Subgroup G) : Set (Subgroup G) :=
  {J | ∃ zK zJ, AViol Ω K J zK zJ}

@[expose] def aGraphAdj (Ω : Set (Subgroup G)) (K J : Subgroup G) : Prop :=
  J ∈ Ω ∧ (J ∈ aSet Ω K ∨ K ∈ aSet Ω J ∨ (J ∈ twinSet Ω K ∧ J ≠ K))

@[expose] def aStar (Ω : Set (Subgroup G)) (K : Subgroup G) : Set (Subgroup G) :=
  {J | Relation.ReflTransGen (aGraphAdj Ω) K J}

@[expose] def vStar (Ω : Set (Subgroup G)) (K : Subgroup G) : Set (Subgroup G) :=
  {J | J ∈ Ω ∧ omegaOfSet Ω (twinSet Ω K) = omegaOfSet Ω (twinSet Ω J)}

@[expose] def DStarConnected (Ω : Set (Subgroup G)) : Prop :=
  ∀ K ∈ Ω, ∀ J ∈ Ω, J ∈ dstarComp Ω K

end Defs

variable (p f : ℕ) [Fact p.Prime]

@[expose] def Thm3CommBelow (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ Ω : Set (Subgroup G),
      HypOmegaMod p f Ω → ∀ K ∈ Ω, ¬ AEmpty Ω K →
        aStar Ω K = vStar Ω K ∧
          ∀ L ∈ Ω, L ∉ vStar Ω K → ∀ M ∈ vStar Ω K, ⁅L, M⁆ ≤ oddCoreOf L ⊓ oddCoreOf M

@[expose] def Thm3LieBelow (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ Ω : Set (Subgroup G),
      HypOmegaMod p f Ω → ∀ K ∈ Ω, ¬ AEmpty Ω K →
        SectionLieType p f Ω (omegaGen (aStar Ω K)) .G2 0

@[expose] def Thm3TypedBelow (n : ℕ) : Prop :=
  Thm3CommBelow p f n ∧ Thm3LieBelow p f n

@[expose] def Thm3ConnBelow (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ Ω : Set (Subgroup G),
      HypOmegaMod p f Ω → (∃ L ∈ Ω, ¬ AEmpty Ω L) → DStarConnected Ω

@[expose] def Thm3SectBelow (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n → ∀ Λ : Set (Subgroup Y),
      HypOmegaMod p f Λ → ¬ DStarConnected (oddQuotientFamily Λ) → ∀ L ∈ Λ, AEmpty Λ L

@[expose] def Thm3SectYBelow (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n → ∀ Λ : Set (Subgroup Y),
      HypOmegaMod p f Λ → ¬ DStarConnected Λ → ∀ L ∈ Λ, AEmpty Λ L

variable {p f}

theorem thm3CommBelow_of_typed {n : ℕ} (h : Thm3TypedBelow p f n) : Thm3CommBelow p f n := h.1

theorem thm3LieBelow_of_typed {n : ℕ} (h : Thm3TypedBelow p f n) : Thm3LieBelow p f n := h.2

section Graph

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem dstarAdj_symm {K J : Subgroup G} (hK : K ∈ Ω) (h : dstarAdj Ω K J) : dstarAdj Ω J K := by
  obtain ⟨-, h | h⟩ := h
  · exact ⟨hK, Or.inr h⟩
  · exact ⟨hK, Or.inl h⟩

theorem mem_dstarComp_symm {K J : Subgroup G} (hK : K ∈ Ω) (h : J ∈ dstarComp Ω K) :
    J ∈ Ω ∧ K ∈ dstarComp Ω J := by
  induction h with
  | refl => exact ⟨hK, Relation.ReflTransGen.refl⟩
  | tail _ hbc ih =>
    exact ⟨hbc.1, Relation.ReflTransGen.head (dstarAdj_symm ih.1 hbc) ih.2⟩

theorem dstarConnected_of_pivot {L : Subgroup G} (hL : L ∈ Ω) (h : ∀ M ∈ Ω, M ∈ dstarComp Ω L) :
    DStarConnected Ω := by
  intro K hK J hJ
  have h1 : L ∈ dstarComp Ω K := (mem_dstarComp_symm hL (h K hK)).2
  exact h1.trans (h J hJ)

variable {p f : ℕ} [Fact p.Prime]

theorem dstarAdj_of_aGraphAdj [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (h : aGraphAdj Ω K J) : dstarAdj Ω K J := by
  obtain ⟨hJ, ⟨zK, zJ, hv⟩ | ⟨zK, zJ, hv⟩ | ⟨⟨-, z, hzK, hzJ⟩, hne⟩⟩ := h
  · exact ⟨hJ, Or.inl hv.star⟩
  · exact ⟨hJ, Or.inr hv.star⟩
  · exact ⟨hJ, Or.inl (omegaNbr_subset_omegaStarNbr hp hΩ K
      (twin_mem_omegaNbr hΩ hK hJ hne hzK hzJ))⟩

theorem aStar_subset_dstarComp [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {K : Subgroup G}
    (hK : K ∈ Ω) {J : Subgroup G} (hJ : J ∈ aStar Ω K) : J ∈ Ω ∧ J ∈ dstarComp Ω K := by
  induction hJ with
  | refl => exact ⟨hK, Relation.ReflTransGen.refl⟩
  | tail _ hbc ih =>
    exact ⟨hbc.1, ih.2.tail (dstarAdj_of_aGraphAdj hp hΩ ih.1 hbc)⟩

theorem le_normalizer_of_commutator_le {M L : Subgroup G} (h : ⁅M, L⁆ ≤ L) :
    M ≤ Subgroup.normalizer (L : Set G) := by
  have key : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := by
    intro m hm l hl
    have h1 : ⁅m, l⁆ ∈ L := h (Subgroup.commutator_mem_commutator hm hl)
    have e : m * l * m⁻¹ = ⁅m, l⁆ * l := by rw [commutatorElement_def]; group
    rw [e]
    exact L.mul_mem h1 hl
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨fun hl => key m hm l hl, fun hl => ?_⟩
  have := key m⁻¹ (M.inv_mem hm) _ hl
  have e : m⁻¹ * (m * l * m⁻¹) * m⁻¹⁻¹ = l := by group
  rwa [e] at this

theorem thm3ConnBelow_of_comm {n : ℕ} (h : Thm3CommBelow p f n) : Thm3ConnBelow p f n := by
  intro hp hq G _ _ hn Ω hΩ ⟨L, hL, hnA⟩
  obtain ⟨hA, hcomm⟩ := h hp hq G hn Ω hΩ L hL hnA
  have hLv : L ∈ vStar Ω L := ⟨hL, rfl⟩
  refine dstarConnected_of_pivot hL fun M hM => ?_
  by_cases hMv : M ∈ vStar Ω L
  · rw [← hA] at hMv
    exact (aStar_subset_dstarComp hp hΩ hL hMv).2
  · have hML : M ≠ L := fun he => hMv (he ▸ hLv)
    have hc : ⁅M, L⁆ ≤ oddCoreOf M ⊓ oddCoreOf L := hcomm M hM hMv L hLv
    have hMN : M ≤ Subgroup.normalizer (L : Set G) :=
      le_normalizer_of_commutator_le (hc.trans (inf_le_right.trans (oddCoreOf_le_self L)))
    obtain ⟨R, hR, hRM, -⟩ := exists_mem_RSet_ge hM (isPGroup_two_bot' (G := G)) bot_le
    have hnb : M ∈ omegaNbr Ω L := ⟨hM, hML, R, hR, hRM.1, hRM.1.trans hMN⟩
    exact Relation.ReflTransGen.single ⟨hM, Or.inl (omegaNbr_subset_omegaStarNbr hp hΩ L hnb)⟩

theorem thm3SectYBelow_of_conn {n : ℕ} (h : Thm3ConnBelow p f n) : Thm3SectYBelow p f n := by
  intro hp hq Y _ _ hn Λ hΛ hdis L hL
  by_contra hnA
  exact hdis (h hp hq Y hn Λ hΛ ⟨L, hL, hnA⟩)

end Graph

abbrev oddQuot (Y : Type) [Group Y] : Y →* Y ⧸ classicalInvolutionOddCore Y :=
  QuotientGroup.mk' (classicalInvolutionOddCore Y)

section Quotient

variable {Y : Type} [Group Y] [Finite Y] {p f : ℕ} [Fact p.Prime] {Λ : Set (Subgroup Y)}

theorem odd_natCard_oddCore_inf (A : Subgroup Y) :
    Odd (Nat.card ↥(classicalInvolutionOddCore Y ⊓ A)) :=
  (CFSG.ComponentClassification.OddCore.odd_card Y).of_dvd_nat
    (Subgroup.card_dvd_of_le inf_le_left)

theorem quot_injOn_of_isPGroup {A : Subgroup Y} (hA : IsPGroup 2 A) :
    ∀ x ∈ A, oddQuot Y x = 1 → x = 1 := by
  intro x hx hx1
  have hxX : x ∈ classicalInvolutionOddCore Y := (QuotientGroup.eq_one_iff x).mp hx1
  exact eq_one_of_isPGroup_of_mem_odd (CFSG.ComponentClassification.OddCore.odd_card Y) hxX
    (hA.to_le (Subgroup.zpowers_le.mpr hx))

theorem natCard_map_quot_of_isPGroup {A : Subgroup Y} (hA : IsPGroup 2 A) :
    Nat.card ↥(A.map (oddQuot Y)) = Nat.card ↥A := by
  have h1 := Subgroup.relIndex_mul_card (oddQuot Y).ker A
  rw [Subgroup.relIndex_ker] at h1
  have hbot : (oddQuot Y).ker ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxk, hxA⟩
    simpa using quot_injOn_of_isPGroup hA x hxA (MonoidHom.mem_ker.mp hxk)
  rw [hbot, Subgroup.card_bot, mul_one] at h1
  exact h1

theorem natCard_isSylow2In_eq_pow {V P : Subgroup Y} (h : IsSylow2In V P) :
    Nat.card V = 2 ^ (Nat.card P).factorization 2 := by
  have e : Nat.card ↥(V.subgroupOf P) = 2 ^ (Nat.card P).factorization 2 :=
    Sylow.card_eq_multiplicity (sylowOfIsSylow2In h)
  have c : Nat.card ↥(V.subgroupOf P) = Nat.card V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.1).toEquiv
  rw [← c, e]

theorem isSylow2In_map_quot {R J : Subgroup Y} (h : IsSylow2In R J) :
    IsSylow2In (R.map (oddQuot Y))
      (J.map (oddQuot Y)) := by
  set π := oddQuot Y with hπ
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge
    (isPGroup_two_bot' (G := Y ⧸ classicalInvolutionOddCore Y))
    (bot_le : (⊥ : Subgroup (Y ⧸ classicalInvolutionOddCore Y)) ≤ J.map π)
  have hRcard : Nat.card R = 2 ^ (Nat.card J).factorization 2 := natCard_isSylow2In_eq_pow h
  have hVcard : Nat.card V = 2 ^ (Nat.card (J.map π)).factorization 2 :=
    natCard_isSylow2In_eq_pow hV
  have hJ : Nat.card (J.map π) * Nat.card ↥(π.ker ⊓ J) = Nat.card J := by
    have h1 := Subgroup.relIndex_mul_card π.ker J
    rw [Subgroup.relIndex_ker] at h1
    exact h1
  have hodd : Odd (Nat.card ↥(π.ker ⊓ J)) := by
    rw [hπ, QuotientGroup.ker_mk']
    exact odd_natCard_oddCore_inf J
  have hfac : (Nat.card J).factorization 2 = (Nat.card (J.map π)).factorization 2 := by
    have hzero : (Nat.card ↥(π.ker ⊓ J)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun h2 =>
        (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
    have hmul := Nat.factorization_mul (Nat.card_pos (α := ↥(J.map π))).ne'
      (Nat.card_pos (α := ↥(π.ker ⊓ J))).ne'
    rw [← hJ, hmul, Finsupp.add_apply, hzero, add_zero]
  have hRbar : Nat.card (R.map π) = Nat.card R := natCard_map_quot_of_isPGroup h.2.1
  exact hV.of_natCard_le (h.2.1.map π) (Subgroup.map_mono h.1)
    (by rw [hRbar, hRcard, hVcard, hfac])

omit [Finite Y] in
theorem mem_oddQuotientFamily {L : Subgroup Y} (hL : L ∈ Λ) :
    L.map (oddQuot Y) ∈ oddQuotientFamily Λ :=
  ⟨L, hL, rfl⟩

theorem mem_RSet_map_quot {R : Subgroup Y} (hR : R ∈ RSet Λ) :
    R.map (oddQuot Y) ∈ RSet (oddQuotientFamily Λ) := by
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  exact mem_RSet_of_isSylow2In (mem_oddQuotientFamily hJ) (isSylow2In_map_quot hRJ)

theorem mem_USet_map_quot {U : Subgroup Y} (hU : U ∈ USet Λ) :
    U.map (oddQuot Y) ∈ USet (oddQuotientFamily Λ) := by
  set π := oddQuot Y with hπ
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨J, -, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have hR2 : IsPGroup 2 R := hRJ.2.1
  refine ⟨R.map π, mem_RSet_map_quot hR, Subgroup.map_mono hUR, ?_, ?_⟩
  · let φ : ↥U →* ↥(U.map π) := (π.comp U.subtype).codRestrict (U.map π) fun x => ⟨x, x.2, rfl⟩
    have hφ : Function.Surjective φ := by
      rintro ⟨_, u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
    exact isCyclic_of_surjective φ hφ
  · have h1 := Subgroup.relIndex_mul_card U R
    rw [inf_eq_left.mpr hUR] at h1
    have h2 := Subgroup.relIndex_mul_card (U.map π) (R.map π)
    rw [inf_eq_left.mpr (Subgroup.map_mono hUR)] at h2
    have cU : Nat.card (U.map π) = Nat.card U := natCard_map_quot_of_isPGroup (hR2.to_le hUR)
    have cR : Nat.card (R.map π) = Nat.card R := natCard_map_quot_of_isPGroup hR2
    rw [cU, cR, ← h1] at h2
    have hU0 : 0 < Nat.card U := Nat.card_pos
    rw [Nat.eq_of_mul_eq_mul_right hU0 h2, hidx]

private theorem map_mem_normalizer' {M G' : Type*} [Group M] [Group G'] (ψ : M →* G')
    {R : Subgroup M} {x : M} (hx : x ∈ Subgroup.normalizer (R : Set M)) :
    ψ x ∈ Subgroup.normalizer ((R.map ψ : Subgroup G') : Set G') := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro h
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨x * r * x⁻¹, (hx r).mp hr, by simp⟩
  · rintro ⟨r, hr, hrh⟩
    refine ⟨x⁻¹ * r * x, ?_, ?_⟩
    · exact (hx (x⁻¹ * r * x)).mpr (by simpa [mul_assoc] using hr)
    · simp only [map_mul, map_inv]
      rw [hrh]
      group

theorem omegaStarNbr_map_quot {K J : Subgroup Y} (h : J ∈ omegaStarNbr Λ K)
    (hne : J.map (oddQuot Y) ≠
      K.map (oddQuot Y)) :
    J.map (oddQuot Y) ∈
      omegaStarNbr (oddQuotientFamily Λ) (K.map (oddQuot Y)) := by
  obtain ⟨hJ, -, U, hU, hUJ, hUN⟩ := h
  refine ⟨mem_oddQuotientFamily hJ, hne, _, mem_USet_map_quot hU, Subgroup.map_mono hUJ, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact map_mem_normalizer' _ (hUN hu)

theorem dstarAdj_map_quot {K J : Subgroup Y} (h : dstarAdj Λ K J) :
    J.map (oddQuot Y) =
      K.map (oddQuot Y) ∨
    dstarAdj (oddQuotientFamily Λ) (K.map (oddQuot Y))
      (J.map (oddQuot Y)) := by
  by_cases he : J.map (oddQuot Y) =
      K.map (oddQuot Y)
  · exact Or.inl he
  · right
    obtain ⟨hJ, h1 | h1⟩ := h
    · exact ⟨mem_oddQuotientFamily hJ, Or.inl (omegaStarNbr_map_quot h1 he)⟩
    · exact ⟨mem_oddQuotientFamily hJ, Or.inr (omegaStarNbr_map_quot h1 (Ne.symm he))⟩

theorem dstarConnected_map (h : DStarConnected Λ) : DStarConnected (oddQuotientFamily Λ) := by
  rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩
  have hpath : ∀ M, M ∈ dstarComp Λ K → M ∈ Λ ∧
      M.map (oddQuot Y) ∈
        dstarComp (oddQuotientFamily Λ) (K.map (oddQuot Y)) := by
    intro M hM
    induction hM with
    | refl => exact ⟨hK, Relation.ReflTransGen.refl⟩
    | tail _ hbc ih =>
      refine ⟨hbc.1, ?_⟩
      rcases dstarAdj_map_quot hbc with he | hadj
      · rw [he]
        exact ih.2
      · exact ih.2.tail hadj
  exact (hpath J (h K hK J hJ)).2

theorem thm3SectBelow_of_sectY {n : ℕ} (h : Thm3SectYBelow p f n) : Thm3SectBelow p f n := by
  intro hp hq Y' _ _ hn Λ' hΛ hdis L hL
  refine h hp hq Y' hn Λ' hΛ (fun hc => hdis (dstarConnected_map hc)) L hL

theorem thm3SectBelow_of_conn {n : ℕ} (h : Thm3ConnBelow p f n) : Thm3SectBelow p f n :=
  thm3SectBelow_of_sectY (thm3SectYBelow_of_conn h)

theorem thm3SectBelow_of_typed {n : ℕ} (h : Thm3TypedBelow p f n) : Thm3SectBelow p f n :=
  thm3SectBelow_of_conn (thm3ConnBelow_of_comm h.1)

end Quotient

end CFSG.ClassicalInvolution.Asc77.T3

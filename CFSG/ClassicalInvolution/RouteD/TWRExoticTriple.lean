module

public import CFSG.ClassicalInvolution.RouteD.TWRExoticIso
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Pair
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Shared
public import CFSG.ClassicalInvolution.RouteD.TypeCBlock

public section

namespace CFSG.ClassicalInvolution.RouteD.TWR

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.NonClassical CFSG.ClassicalInvolution.RouteD.Exotic
open scoped commutatorElement

variable {G : Type} [Group G]

theorem card_closure_pair_le [Finite G] {a b : G} (hab : a * b = b * a) (ha : a * a = 1)
    (hb : b * b = 1) : Nat.card (Subgroup.closure ({a, b} : Set G)) ≤ 4 := by
  classical
  have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have h2 : b * a = a * b := hab.symm
  have h3 : b * (a * b) = a := by rw [← mul_assoc, h2, mul_assoc, hb, mul_one]
  have h4 : a * b * a = b := by rw [mul_assoc, h2, ← mul_assoc, ha, one_mul]
  have h5 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have h6 : a * b * (a * b) = 1 := by rw [← mul_assoc, h4, hb]
  have hia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hiab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h6
  have hsub : (Subgroup.closure ({a, b} : Set G) : Set G) ⊆
      (({1, a, b, a * b} : Finset G) : Set G) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl <;> simp
    | one => simp
    | mul x y _ _ hx hy =>
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx hy ⊢
        rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
          simp [h1, h2, h3, h4, h5, h6, ha, hb]
    | inv x _ hx =>
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl <;> simp [hia, hib, hiab]
  calc Nat.card (Subgroup.closure ({a, b} : Set G))
      = Set.ncard (Subgroup.closure ({a, b} : Set G) : Set G) := Nat.card_coe_set_eq _
    _ ≤ Set.ncard ((({1, a, b, a * b} : Finset G)) : Set G) :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ({1, a, b, a * b} : Finset G).card := Set.ncard_coe_finset _
    _ ≤ 4 := Finset.card_le_four

theorem distinct_of_card_eq_eight [Finite G] {z : Fin 3 → G}
    (hE : CFSG.Open.IsElemAbelian 2 (Subgroup.closure (Set.range z)))
    (hcard : Nat.card (Subgroup.closure (Set.range z)) = 8) :
    z 0 ≠ z 1 ∧ z 0 ≠ z 2 ∧ z 1 ≠ z 2 := by
  have key : ∀ {i j k : Fin 3}, (∀ m, m = i ∨ m = j ∨ m = k) → z i = z j → False := by
    intro i j k hijk h
    have hmem : ∀ m, z m ∈ Subgroup.closure (Set.range z) := fun m =>
      Subgroup.subset_closure ⟨m, rfl⟩
    have hsq : ∀ m, z m * z m = 1 := fun m => by
      have := hE.2 _ (hmem m)
      simpa [pow_two] using this
    have hcomm : z i * z k = z k * z i := by
      have := hE.1.is_comm.comm (⟨z i, hmem i⟩ : ↥(Subgroup.closure (Set.range z)))
        ⟨z k, hmem k⟩
      exact congrArg Subtype.val this
    have hle : Subgroup.closure (Set.range z) ≤ Subgroup.closure ({z i, z k} : Set G) := by
      refine Subgroup.closure_mono ?_
      rintro _ ⟨m, rfl⟩
      rcases hijk m with rfl | rfl | rfl
      · simp
      · simp [← h]
      · simp
    have := (Subgroup.card_le_of_le hle).trans (card_closure_pair_le hcomm (hsq i) (hsq k))
    omega
  refine ⟨fun h => key (i := 0) (j := 1) (k := 2) (by decide) h,
    fun h => key (i := 0) (j := 2) (k := 1) (by decide) h,
    fun h => key (i := 1) (j := 2) (k := 0) (by decide) h⟩

variable {p f : ℕ} [Fact p.Prime]


@[expose] def ExoticAt (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (x : G) : Prop :=
  ∃ D : LieSystemData p f (locQuot Ω x) (locFamily Ω x), ∃ i₁ : Fin D.card,
    OneBig D i₁ ∧ D.card ≤ 3 ∧ (D.tag i₁ = .G2 ∨ D.tag i₁ = .trialityD4)

theorem exoticAt_of_localShapeT {Ω : Set (Subgroup G)} {x : G} {a : ℕ} {tY : StatedLieTag}
    {nY : ℕ} (ha : a ≤ 2) (htY : tY = .G2 ∨ tY = .trialityD4)
    (h : LocalShapeT p f a tY nY Ω x) : ExoticAt p f Ω x := by
  obtain ⟨D, hcard, i₁, ht, -, hrest⟩ := h
  refine ⟨D, i₁, ⟨?_, fun i hi => hrest i hi⟩, by omega, by rcases htY with h | h <;> simp [ht, h]⟩
  rintro ⟨h1, -⟩
  rcases htY with h | h <;> rw [h] at ht <;> rw [ht] at h1 <;> exact absurd h1 (by decide)

section Members

variable {Ω : Set (Subgroup G)} {x : G}

theorem iso_or_big [Finite G] (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)}
    {i₁ : Fin D.card} (h : OneBig D i₁) {N : Subgroup G} (hN : N ∈ centralizingMembers Ω {x}) :
    N ∈ isoMembers Ω x ∨ N ∈ compMembers Ω x D i₁ := by
  obtain ⟨i, hi⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
  by_cases hii : i = i₁
  · subst hii
    exact Or.inr ⟨hN, hi⟩
  · exact Or.inl (mem_isoMembers_of_a1 hΩ hex hP1 (h.rest i hii) ⟨hN, hi⟩)

theorem iso_of_involution [Finite G] (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    {M : Subgroup G} (hM : M ∈ centralizingMembers Ω {x}) (hx : IsClassicalMember p f M x) :
    M ∈ isoMembers Ω x :=
  ⟨hM, fun _ hN hNM =>
    (commutes_or_eq_of_involution (Gaps.fundNoncentral p) hΩ hex hP1 D hM hN hx).resolve_right hNM⟩

theorem iso_or_iso_of_commuting [Finite G] (hp2 : p ≠ 2) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {x}) (hE : ExoticAt p f Ω x)
    {N₁ N₂ : Subgroup G} (h₁ : N₁ ∈ centralizingMembers Ω {x})
    (h₂ : N₂ ∈ centralizingMembers Ω {x}) {y₁ y₂ : G} (hy₁ : IsClassicalMember p f N₁ y₁)
    (hy₂ : IsClassicalMember p f N₂ y₂) (hne : y₁ ≠ y₂) (hc : Commutes N₁ N₂) :
    N₁ ∈ isoMembers Ω x ∨ N₂ ∈ isoMembers Ω x := by
  obtain ⟨D, i₁, hone, -, htag⟩ := hE
  by_contra hno
  push Not at hno
  have b₁ : N₁ ∈ compMembers Ω x D i₁ := (iso_or_big hΩ hex hP1 hone h₁).resolve_left hno.1
  have b₂ : N₂ ∈ compMembers Ω x D i₁ := (iso_or_big hΩ hex hP1 hone h₂).resolve_left hno.2
  exact hne (G2D4.eq_involution_of_commuting_pair (G2D4.g2d4SharedInvolution p) hp2 hΩ hP1 D
    htag b₁ b₂ hy₁ hy₂ hc)

theorem not_three_iso [Finite G] (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) (hE : ExoticAt p f Ω x) {M₀ M₁ M₂ : Subgroup G}
    (h₀ : M₀ ∈ isoMembers Ω x) (h₁ : M₁ ∈ isoMembers Ω x) (h₂ : M₂ ∈ isoMembers Ω x)
    (h01 : M₀ ≠ M₁) (h02 : M₀ ≠ M₂) (h12 : M₁ ≠ M₂) : False := by
  obtain ⟨D, i₁, hone, hcard, -⟩ := hE
  have hidx : ∀ M ∈ isoMembers Ω x, ∃ i, i ≠ i₁ ∧ M ∈ compMembers Ω x D i := by
    intro M hM
    obtain ⟨i, hle⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨M, hM.1, rfl⟩)
    refine ⟨i, ?_, hM.1, hle⟩
    rintro rfl
    obtain ⟨L, hL, hLM, hnc⟩ := exists_noncommuting_of_not_a1 hΩ hex hP1 hone.big ⟨hM.1, hle⟩
    exact hnc (hM.2 L hL hLM)
  obtain ⟨c₀, hc₀, hm₀⟩ := hidx M₀ h₀
  obtain ⟨c₁, hc₁, hm₁⟩ := hidx M₁ h₁
  obtain ⟨c₂, hc₂, hm₂⟩ := hidx M₂ h₂
  have hdist : ∀ {i j : Fin D.card} {A B : Subgroup G}, i ≠ i₁ → A ∈ compMembers Ω x D i →
      B ∈ compMembers Ω x D j → A ≠ B → i ≠ j := by
    intro i j A B hi hA hB hAB hij
    subst hij
    exact hAB (eq_of_mem_compMembers_a1 hΩ hex hP1 (hone.rest i hi) hA hB)
  have d01 := hdist hc₀ hm₀ hm₁ h01
  have d02 := hdist hc₀ hm₀ hm₂ h02
  have d12 := hdist hc₁ hm₁ hm₂ h12
  have hsub : ({c₀, c₁, c₂} : Finset (Fin D.card)) ⊆ Finset.univ.erase i₁ := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rw [Finset.mem_erase]
    rcases hi with rfl | rfl | rfl
    · exact ⟨hc₀, Finset.mem_univ _⟩
    · exact ⟨hc₁, Finset.mem_univ _⟩
    · exact ⟨hc₂, Finset.mem_univ _⟩
  have h3 : ({c₀, c₁, c₂} : Finset (Fin D.card)).card = 3 :=
    Finset.card_eq_three.mpr ⟨c₀, c₁, c₂, d01, d02, d12, rfl⟩
  have := Finset.card_le_card hsub
  rw [h3, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
  omega

end Members

section Triple

variable {Ω : Set (Subgroup G)}

theorem triple_aux [Finite G] (hp2 : p ≠ 2) (hf : 0 < f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (htrans : ∀ L ∈ Ω, ∀ T ∈ Ω, ∃ g : G, T = conjSub g L)
    (hE : ∀ M ∈ Ω, ∀ x : G, IsClassicalMember p f M x →
      ExoticAt p f Ω x ∧ LocalOddCentral Ω {x})
    {K₀ K₁ K₂ : Subgroup G} {z₀ z₁ z₂ : G} (h₀ : K₀ ∈ Ω) (h₁ : K₁ ∈ Ω) (h₂ : K₂ ∈ Ω)
    (c₀ : IsClassicalMember p f K₀ z₀) (c₁ : IsClassicalMember p f K₁ z₁)
    (c₂ : IsClassicalMember p f K₂ z₂) (k₀₁ : Commutes K₀ K₁) (k₀₂ : Commutes K₀ K₂)
    (k₁₂ : Commutes K₁ K₂) (z₀₁ : z₀ ≠ z₁) (z₀₂ : z₀ ≠ z₂) (z₁₂ : z₁ ≠ z₂)
    (hiso : K₁ ∈ isoMembers Ω z₀) : False := by
  obtain ⟨hE₀, hP₀⟩ := hE K₀ h₀ z₀ c₀
  obtain ⟨hE₂, hP₂⟩ := hE K₂ h₂ z₂ c₂
  have ne : ∀ {A B : Subgroup G} {x y : G}, IsClassicalMember p f A x →
      IsClassicalMember p f B y → x ≠ y → A ≠ B := by
    intro A B x y hA hB hxy hAB
    subst hAB
    exact hxy (hB.eq_of_isCentralInvolution hp2 hf hA.isCentralInvolution)
  have m₀₀ : K₀ ∈ centralizingMembers Ω {z₀} := ⟨h₀, le_centralizer_of_isClassicalMember c₀⟩
  have m₂₀ : K₂ ∈ centralizingMembers Ω {z₀} :=
    mem_centralizingMembers_of_commutes h₂ c₀.mem (Gaps.commutes_symm k₀₂)
  have m₀₂ : K₀ ∈ centralizingMembers Ω {z₂} :=
    mem_centralizingMembers_of_commutes h₀ c₂.mem k₀₂
  have m₁₂ : K₁ ∈ centralizingMembers Ω {z₂} :=
    mem_centralizingMembers_of_commutes h₁ c₂.mem k₁₂
  have m₂₂ : K₂ ∈ centralizingMembers Ω {z₂} := ⟨h₂, le_centralizer_of_isClassicalMember c₂⟩
  have e₁₀ : centralizingMembers Ω {z₁} = centralizingMembers Ω {z₀} :=
    centralizingMembers_eq_of_twin hp2 hf hΩ c₀ c₁ (htrans K₀ h₀ K₁ h₁) hiso.1 hiso.2
  have iso₀ : K₀ ∈ isoMembers Ω z₀ := by
    obtain ⟨D, -⟩ := hE₀
    exact iso_of_involution hΩ hex hP₀ D m₀₀ c₀
  have hK₂ : K₂ ∉ isoMembers Ω z₀ := fun hK₂ =>
    not_three_iso hΩ hex hP₀ hE₀ iso₀ hiso hK₂ (ne c₀ c₁ z₀₁) (ne c₀ c₂ z₀₂) (ne c₁ c₂ z₁₂)
  have e₂₀ : centralizingMembers Ω {z₂} = centralizingMembers Ω {z₀} := by
    rcases iso_or_iso_of_commuting hp2 hΩ hex hP₂ hE₂ m₀₂ m₁₂ c₀ c₁ z₀₁ k₀₁ with h | h
    · exact (centralizingMembers_eq_of_twin hp2 hf hΩ c₂ c₀ (htrans K₂ h₂ K₀ h₀) m₀₂ h.2).symm
    · exact ((centralizingMembers_eq_of_twin hp2 hf hΩ c₂ c₁ (htrans K₂ h₂ K₁ h₁) m₁₂ h.2).symm
        ).trans e₁₀
  have iso₂ : K₂ ∈ isoMembers Ω z₂ := by
    obtain ⟨D, -⟩ := hE₂
    exact iso_of_involution hΩ hex hP₂ D m₂₂ c₂
  have heq : isoMembers Ω z₂ = isoMembers Ω z₀ := by
    unfold isoMembers
    rw [e₂₀]
  exact hK₂ (heq ▸ iso₂)

theorem not_indepTriple_of_exotic [Finite G] (hp2 : p ≠ 2) (hf : 0 < f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (htrans : ∀ L ∈ Ω, ∀ T ∈ Ω, ∃ g : G, T = conjSub g L)
    (hE : ∀ M ∈ Ω, ∀ x : G, IsClassicalMember p f M x →
      ExoticAt p f Ω x ∧ LocalOddCentral Ω {x}) : ¬ IndepTriple p f Ω := by
  rintro ⟨Kf, zf, hmem, hcomm, hE8, hcard⟩
  obtain ⟨z01, z02, z12⟩ := distinct_of_card_eq_eight hE8 hcard
  have c : ∀ i, IsClassicalMember p f (Kf i) (zf i) := fun i => (hmem i).2
  have m : ∀ i, Kf i ∈ Ω := fun i => (hmem i).1
  have k01 : Commutes (Kf 0) (Kf 1) := hcomm 0 1 (by decide)
  have k02 : Commutes (Kf 0) (Kf 2) := hcomm 0 2 (by decide)
  have k12 : Commutes (Kf 1) (Kf 2) := hcomm 1 2 (by decide)
  have m01 : Kf 1 ∈ centralizingMembers Ω {zf 0} :=
    mem_centralizingMembers_of_commutes (m 1) (c 0).mem (Gaps.commutes_symm k01)
  have m02 : Kf 2 ∈ centralizingMembers Ω {zf 0} :=
    mem_centralizingMembers_of_commutes (m 2) (c 0).mem (Gaps.commutes_symm k02)
  obtain ⟨hE₀, hP₀⟩ := hE (Kf 0) (m 0) (zf 0) (c 0)
  rcases iso_or_iso_of_commuting hp2 hΩ hex hP₀ hE₀ m01 m02 (c 1) (c 2) z12 k12 with h | h
  · exact triple_aux hp2 hf hΩ hex htrans hE (m 0) (m 1) (m 2) (c 0) (c 1) (c 2) k01 k02 k12
      z01 z02 z12 h
  · exact triple_aux hp2 hf hΩ hex htrans hE (m 0) (m 2) (m 1) (c 0) (c 2) (c 1) k02 k01
      (Gaps.commutes_symm k12) z02 z01 z12.symm h

theorem exotic_ctx [Finite G] {K : Subgroup G} {z : G} (hp2 : p ≠ 2) (hf : 0 < f)
    (hΩ : InClass p f (conjClass K)) (hz : IsClassicalMember p f K z)
    (hP1 : LocalOddCentral (conjClass K) {z}) {a : ℕ} (ha : a ≤ 2) {tY : StatedLieTag} {nY : ℕ}
    (htY : tY = .G2 ∨ tY = .trialityD4) (h : LocalShapeT p f a tY nY (conjClass K) z) :
    ∀ M ∈ conjClass K, ∀ x : G, IsClassicalMember p f M x →
      ExoticAt p f (conjClass K) x ∧ LocalOddCentral (conjClass K) {x} := by
  intro M hM x hx
  obtain ⟨g, hg⟩ := single_class K M hM
  have hzg : IsClassicalMember p f M (g * z * g⁻¹) := by
    rw [hg]
    exact hz.conj g
  have hxg : x = g * z * g⁻¹ := hzg.eq_of_isCentralInvolution hp2 hf hx.isCentralInvolution
  subst hxg
  exact ⟨exoticAt_of_localShapeT ha htY (LocalShapeT.conj hΩ.conjInvariant g h),
    localOddCentral_conj hΩ.conjInvariant g z hP1⟩

end Triple

end CFSG.ClassicalInvolution.RouteD.TWR

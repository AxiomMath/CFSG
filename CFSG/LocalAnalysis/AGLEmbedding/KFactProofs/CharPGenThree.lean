module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2314Abstract
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeCore

public section

namespace CFSG.AGLEmbedding.CharPGenThree

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.P1Lie

section Abstract

variable {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem glbCore_posUnipotent_eq_top_of_le_pRank
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    {p k : ℕ} (hp : p.Prime) (hrank : 0 < D.rank)
    (hk : ∀ i, k ≤ Open.pRank p (posUnipotentExcept D i)) :
    GLBCore p k (posUnipotent D) = ⊤ := by
  have hUk : k ≤ Open.pRank p (posUnipotent D) :=
    (hk ⟨0, hrank⟩).trans
      (CFSG.SectionRank.pRank_mono hp.one_lt (posUnipotentExcept_le_posUnipotent _))
  have hB : borel D H ≤ GLBCore p k (posUnipotent D) :=
    (borel_le_normalizer_posUnipotent hct).trans
      (CFSG.AGLEmbeddingD2.normalizer_le_glbCore p k le_rfl hUk)
  have hn : ∀ i, n i ∈ GLBCore p k (posUnipotent D) := fun i =>
    CFSG.AGLEmbeddingD2.normalizer_le_glbCore p k (posUnipotentExcept_le_posUnipotent i) (hk i)
      (Subgroup.mem_normalizer_fintype fun u hu => conj_n_mem_posUnipotentExcept hct i hu)
  rw [eq_top_iff, ← closure_borel_union_range hct]
  exact (Subgroup.closure_le _).2 (Set.union_subset hB (Set.range_subset_iff.2 hn))

theorem exists_pGroup_glbCore_of_central_cover {X : Type*} [Group X] [Finite X] {p k : ℕ}
    (hp : p.Prime)
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hrank : 0 < D.rank)
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ))
    (hcen : ∀ z ∈ Subgroup.center K, z ^ p = 1 → z = 1) (ψ : K →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center K)
    (hk : ∀ i, k ≤ Open.pRank p (posUnipotentExcept D i)) :
    ∃ P : Subgroup X, IsPGroup p P ∧ GLBCore p k P = ⊤ := by
  have hU : IsPGroup p (posUnipotent D) := isPGroup_iSup_pos hext hX
  have hinj : ∀ x ∈ posUnipotent D, ψ x = 1 → x = 1 := by
    intro x hx hx1
    obtain ⟨m, hm⟩ := hU ⟨x, hx⟩
    exact eq_one_of_mem_center_of_pow_prime_pow hcen (hker (MonoidHom.mem_ker.2 hx1))
      (congrArg Subtype.val hm)
  exact ⟨(posUnipotent D).map ψ, hU.map ψ,
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact2314.glbCore_map_eq_top_of_injOn hp ψ hψ hinj
      (glbCore_posUnipotent_eq_top_of_le_pRank hct hp hrank hk)⟩

end Abstract

section Rank

variable {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem three_le_pRank_of_pair {F : Type} [Field F] {x : (Fin D.rank → ℤ) → F → K}
    (hext : SteinbergExtras D n H) {p f : ℕ} [CharP F p] (hp : p.Prime)
    (hx : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup x)
    (hF : Nat.card F = p ^ f) (hf : 2 ≤ f) {γ₁ γ₂ : Fin D.rank → ℤ}
    (hr : ∀ γ ∈ ({γ₁, γ₂} : Finset (Fin D.rank → ℤ)), γ ∈ D.roots ∧
      (∃ j₁ j₂ : Fin D.rank, j₁ ≠ j₂ ∧ 0 < γ j₁ ∧ 0 < γ j₂) ∧ ∀ δ ∈ D.roots, γ ≠ 2 • δ)
    (h12 : γ₁ ≠ γ₂) (c12 : CommRoots D γ₁ γ₂) (i : Fin D.rank) :
    3 ≤ Open.pRank p (posUnipotentExcept D i) := by
  classical
  have key := sum_le_pRank_posUnipotentExcept hext hp (fun _ => f)
    (fun γ hγ => by
      obtain ⟨hE, hcard⟩ := isElemAbelian_card_of_isParametrization (p := p) hx hγ
      exact ⟨_, le_rfl, hE, by rw [hcard, hF]⟩)
    (i := i) ({γ₁, γ₂} : Finset (Fin D.rank → ℤ))
    (fun γ hγ => by
      obtain ⟨hγR, ⟨j₁, j₂, hj, h1, h2⟩, hnd⟩ := hr γ hγ
      exact ⟨mem_posExcept_of_two_pos hγR hj h1 h2 i, hnd⟩)
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro γ (rfl | rfl) δ (rfl | rfl) hne
      · exact absurd rfl hne
      · exact c12
      · exact c12.symm
      · exact absurd rfl hne)
  rw [Finset.sum_const, Finset.card_pair h12, smul_eq_mul] at key
  omega

theorem three_le_pRank_of_weighted_pair (hext : SteinbergExtras D n H) {p : ℕ} (hp : p.Prime)
    {γ₁ γ₂ : Fin D.rank → ℤ} (w₁ w₂ : ℕ)
    (h₁ : ∃ E ≤ D.rootGroup γ₁, IsElemAbelian p E ∧ p ^ w₁ ≤ Nat.card E)
    (h₂ : ∃ E ≤ D.rootGroup γ₂, IsElemAbelian p E ∧ p ^ w₂ ≤ Nat.card E)
    (hr : ∀ γ ∈ ({γ₁, γ₂} : Finset (Fin D.rank → ℤ)), γ ∈ D.roots ∧
      (∃ j₁ j₂ : Fin D.rank, j₁ ≠ j₂ ∧ 0 < γ j₁ ∧ 0 < γ j₂) ∧ ∀ δ ∈ D.roots, γ ≠ 2 • δ)
    (h12 : γ₁ ≠ γ₂) (c12 : CommRoots D γ₁ γ₂) (hw : 3 ≤ w₁ + w₂) (i : Fin D.rank) :
    3 ≤ Open.pRank p (posUnipotentExcept D i) := by
  classical
  have key := sum_le_pRank_posUnipotentExcept hext hp
    (fun γ => if γ = γ₁ then w₁ else if γ = γ₂ then w₂ else 0)
    (fun γ _ => by
      by_cases e1 : γ = γ₁
      · subst e1
        simpa using h₁
      · by_cases e2 : γ = γ₂
        · subst e2
          simpa [e1] using h₂
        · refine ⟨⊥, bot_le, ⟨inferInstance, fun g hg => ?_⟩, ?_⟩
          · rw [Subgroup.mem_bot] at hg
            rw [hg, one_pow]
          · simp [e1, e2])
    (i := i) ({γ₁, γ₂} : Finset (Fin D.rank → ℤ))
    (fun γ hγ => by
      obtain ⟨hγR, ⟨j₁, j₂, hj, h1, h2⟩, hnd⟩ := hr γ hγ
      exact ⟨mem_posExcept_of_two_pos hγR hj h1 h2 i, hnd⟩)
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro γ (rfl | rfl) δ (rfl | rfl) hne
      · exact absurd rfl hne
      · exact c12
      · exact c12.symm
      · exact absurd rfl hne)
  rw [Finset.sum_pair h12] at key
  simp only [↓reduceIte, if_neg h12.symm] at key
  omega

theorem three_le_pRank_of_image_triple (hext : SteinbergExtras D n H) {p : ℕ} (hp : p.Prime)
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) (hD : D.divisible = ∅)
    {ι : Type*} [DecidableEq ι] (T : (Fin D.rank → ℤ) →+ (ι → ℤ))
    (hsupp : ∀ ε ∈ D.roots, ∀ a b c : ι, a ≠ b → a ≠ c → b ≠ c →
      ¬ (T ε a ≠ 0 ∧ T ε b ≠ 0 ∧ T ε c ≠ 0))
    {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {γ₁ γ₂ γ₃ : Fin D.rank → ℤ} (h₁ : γ₁ ∈ D.roots) (h₂ : γ₂ ∈ D.roots) (h₃ : γ₃ ∈ D.roots)
    (e₁ : T γ₁ = Pi.single a 1 + Pi.single b 1) (e₂ : T γ₂ = Pi.single a 1 + Pi.single c 1)
    (e₃ : T γ₃ = Pi.single b 1 + Pi.single c 1)
    (ht₁ : 2 ≤ ht γ₁) (ht₂ : 2 ≤ ht γ₂) (ht₃ : 2 ≤ ht γ₃) (i : Fin D.rank) :
    3 ≤ Open.pRank p (posUnipotentExcept D i) := by
  have nn : ∀ (u v l : ι), 0 ≤ (Pi.single u 1 + Pi.single v 1 : ι → ℤ) l := by
    intro u v l
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> omega
  have v1 : T γ₁ a = 1 ∧ T γ₁ b = 1 ∧ T γ₁ c = 0 := by
    rw [e₁]; simp [hab, hab.symm, hac.symm, hbc.symm]
  have v2 : T γ₂ a = 1 ∧ T γ₂ b = 0 ∧ T γ₂ c = 1 := by
    rw [e₂]; simp [hab.symm, hac, hac.symm, hbc]
  have v3 : T γ₃ a = 0 ∧ T γ₃ b = 1 ∧ T γ₃ c = 1 := by
    rw [e₃]; simp [hab, hac, hbc, hbc.symm]
  have h12 : γ₁ ≠ γ₂ := fun h => by
    have := congrArg (fun v => T v b) h
    simp only [v1.2.1, v2.2.1] at this
    omega
  have h13 : γ₁ ≠ γ₃ := fun h => by
    have := congrArg (fun v => T v a) h
    simp only [v1.1, v3.1] at this
    omega
  have h23 : γ₂ ≠ γ₃ := fun h => by
    have := congrArg (fun v => T v a) h
    simp only [v2.1, v3.1] at this
    omega
  have n1 : ∀ l, 0 ≤ T γ₁ l := fun l => by rw [e₁]; exact nn a b l
  have n2 : ∀ l, 0 ≤ T γ₂ l := fun l => by rw [e₂]; exact nn a c l
  have n3 : ∀ l, 0 ≤ T γ₃ l := fun l => by rw [e₃]; exact nn b c l
  have c12 : CommRoots D γ₁ γ₂ :=
    commRoots_of_images T hD hsupp h₁ h₂ h12 n1 n2 ⟨a, by rw [v1.1]; exact one_ne_zero⟩ hab hac hbc
      fun s t hs ht => by
        simp only [v1.1, v1.2.1, v1.2.2, v2.1, v2.2.1, v2.2.2]
        refine ⟨?_, ?_, ?_⟩ <;> omega
  have c13 : CommRoots D γ₁ γ₃ :=
    commRoots_of_images T hD hsupp h₁ h₃ h13 n1 n3 ⟨a, by rw [v1.1]; exact one_ne_zero⟩ hab hac hbc
      fun s t hs ht => by
        simp only [v1.1, v1.2.1, v1.2.2, v3.1, v3.2.1, v3.2.2]
        refine ⟨?_, ?_, ?_⟩ <;> omega
  have c23 : CommRoots D γ₂ γ₃ :=
    commRoots_of_images T hD hsupp h₂ h₃ h23 n2 n3 ⟨a, by rw [v2.1]; exact one_ne_zero⟩ hab hac hbc
      fun s t hs ht => by
        simp only [v2.1, v2.2.1, v2.2.2, v3.1, v3.2.1, v3.2.2]
        refine ⟨?_, ?_, ?_⟩ <;> omega
  refine three_le_pRank_of_triple hext hp hX (fun γ hγ => ?_) h12 h13 h23 c12 c13 c23 i
  simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
  rcases hγ with rfl | rfl | rfl
  · exact posData_of_two_le_ht hD h₁ ht₁
  · exact posData_of_two_le_ht hD h₂ ht₂
  · exact posData_of_two_le_ht hD h₃ ht₃

theorem three_le_pRank_of_heights (hext : SteinbergExtras D n H) {p : ℕ} (hp : p.Prime)
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) (hD : D.divisible = ∅)
    {M k : ℤ} (hk : 2 ≤ k) (hMk : M < 2 * k) (hM : ∀ ε ∈ D.roots, ht ε ≤ M)
    (h3 : ∃ γ₁ ∈ D.roots, ∃ γ₂ ∈ D.roots, ∃ γ₃ ∈ D.roots, γ₁ ≠ γ₂ ∧ γ₁ ≠ γ₃ ∧ γ₂ ≠ γ₃ ∧
      k ≤ ht γ₁ ∧ k ≤ ht γ₂ ∧ k ≤ ht γ₃) (i : Fin D.rank) :
    3 ≤ Open.pRank p (posUnipotentExcept D i) := by
  obtain ⟨γ₁, h₁, γ₂, h₂, γ₃, h₃, h12, h13, h23, k1, k2, k3⟩ := h3
  refine three_le_pRank_of_triple hext hp hX (fun γ hγ => ?_) h12 h13 h23
    (commRoots_of_ht hD hM h₁ h₂ h12 (by omega) (by omega) (by omega))
    (commRoots_of_ht hD hM h₁ h₃ h13 (by omega) (by omega) (by omega))
    (commRoots_of_ht hD hM h₂ h₃ h23 (by omega) (by omega) (by omega)) i
  simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
  rcases hγ with rfl | rfl | rfl
  · exact posData_of_two_le_ht hD h₁ (by omega)
  · exact posData_of_two_le_ht hD h₂ (by omega)
  · exact posData_of_two_le_ht hD h₃ (by omega)

end Rank

end CFSG.AGLEmbedding.CharPGenThree

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def CharPGen3At (Fam : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, Fam d → Nonempty (K ≃* CatGroup d) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → p = d.1.characteristic → ¬ IsRankOneLieIndex d.1 →
        ∀ T : Sylow p K, GLBCore p 3 (T : Subgroup K) = ⊤

theorem charPGen3At_mono {Fam Fam' : TauCeti.ValidLieTypeIndex → Prop}
    (h : CharPGen3At Fam) (hle : ∀ d, Fam' d → Fam d) : CharPGen3At Fam' :=
  fun K _ _ hs hn d hd => h K hs hn d (hle d hd)

theorem charPGen3At_or {F₁ F₂ : TauCeti.ValidLieTypeIndex → Prop}
    (h₁ : CharPGen3At F₁) (h₂ : CharPGen3At F₂) : CharPGen3At fun d => F₁ d ∨ F₂ d :=
  fun K _ _ hs hn d hd => hd.elim (h₁ K hs hn d) (h₂ K hs hn d)

theorem charPGen3At_of_pGroup {Fam : TauCeti.ValidLieTypeIndex → Prop}
    (h : ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → ∀ d : TauCeti.ValidLieTypeIndex,
      Fam d → K ≃* CatGroup d → ∀ p : ℕ, p.Prime → p ≠ 2 → p = d.1.characteristic →
        ¬ IsRankOneLieIndex d.1 → ∃ P : Subgroup K, IsPGroup p P ∧ GLBCore p 3 P = ⊤) :
    CharPGen3At Fam := by
  intro K _ _ hs _ d hd ⟨e⟩ p hp hp2 hchar hrank T
  obtain ⟨P, hP, hcore⟩ := h K hs d hd e p hp hp2 hchar hrank
  exact CFSG.AGLEmbeddingD2.glbCore_eq_top_of_pGroup hp 3 hP hcore T

end CFSG.AGLEmbedding

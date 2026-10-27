module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbLeviSupp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLevi

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Levi

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.LieOut
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

@[expose] def unipRad (D : UniversalRootDatum K) (J : Set (Fin D.rank)) : Subgroup K :=
  ⨆ k ∈ Jᶜ, radical D k

theorem unipRad_le_posUnipotent (J : Set (Fin D.rank)) : unipRad D J ≤ posUnipotent D := by
  unfold unipRad
  exact iSup₂_le fun k _ => radical_le_posUnipotent k

private theorem radical_le_unipRad {J : Set (Fin D.rank)} {k : Fin D.rank} (hk : k ∉ J) :
    radical D k ≤ unipRad D J :=
  le_iSup₂_of_le (f := fun k (_ : k ∈ Jᶜ) => radical D k) k hk le_rfl

private theorem single_pm_facts {j : Fin D.rank} {γ : Fin D.rank → ℤ}
    (hγ : γ = Pi.single j 1 ∨ γ = -Pi.single j 1) :
    γ ∈ D.roots ∧ (∀ m, m ≠ j → γ m = 0) ∧ γ j ≠ 0 := by
  rcases hγ with rfl | rfl
  · exact ⟨(RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j,
      fun m hm => by simp [Pi.single_apply, hm], by simp⟩
  · exact ⟨(RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _
      ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j),
      fun m hm => by simp [Pi.single_apply, hm], by simp⟩

private theorem openCone_empty_nonadj {j k : Fin D.rank} (hjk : j ≠ k)
    (hjk0 : D.cartan j k = 0) (hkj0 : D.cartan k j = 0) {γ δ : Fin D.rank → ℤ}
    (hγs : ∀ m, m ≠ j → γ m = 0) (hγj : γ j ≠ 0)
    (hδs : ∀ m, m ≠ k → δ m = 0) (hδk : δ k ≠ 0) :
    ∀ ε ∈ openCone D.roots γ δ, False := by
  rintro ε ⟨hε, a, b, ha, hb, rfl⟩
  have hγk : γ k = 0 := hγs k (Ne.symm hjk)
  have hδj : δ j = 0 := hδs j hjk
  have hsupp : ∀ m ∉ ({j, k} : Set (Fin D.rank)), (a • γ + b • δ) m = 0 := by
    intro m hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hm
    simp [nsmul_eq_mul, hγs m hm.1, hδs m hm.2]
  have hJ : ∀ m ∈ ({j, k} : Set (Fin D.rank)), ∀ m' ∈ ({j, k} : Set (Fin D.rank)),
      m ≠ m' → D.cartan m m' = 0 := by
    rintro m (rfl | rfl) m' (rfl | rfl) hne
    · exact absurd rfl hne
    · exact hjk0
    · exact hkj0
    · exact absurd rfl hne
  obtain ⟨l, hl, hE⟩ := eq_of_support_of_independent hJ hε hsupp
  have hzero : ∀ m, m ≠ l → (a • γ + b • δ) m = 0 := by
    intro m hm
    rcases hE with h | h | h | h <;> rw [h] <;> simp [Pi.single_apply, hm]
  have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
  have hEj : (a • γ + b • δ) j ≠ 0 := by
    have e : (a • γ + b • δ) j = (a : ℤ) * γ j := by simp [hδj]
    rw [e]
    exact mul_ne_zero ha0 hγj
  have hEk : (a • γ + b • δ) k ≠ 0 := by
    have e : (a • γ + b • δ) k = (b : ℤ) * δ k := by simp [hγk]
    rw [e]
    exact mul_ne_zero hb0 hδk
  rcases hl with rfl | rfl
  · exact hEk (hzero _ (Ne.symm hjk))
  · exact hEj (hzero _ hjk)

private theorem comm_gens_nonadj (hext : SteinbergExtras D n H) {j k : Fin D.rank}
    (hjk : j ≠ k) (hjk0 : D.cartan j k = 0) (hkj0 : D.cartan k j = 0) {γ δ : Fin D.rank → ℤ}
    (hγ : γ = Pi.single j 1 ∨ γ = -Pi.single j 1) (hδ : δ = Pi.single k 1 ∨ δ = -Pi.single k 1)
    {x y : K} (hx : x ∈ D.rootGroup γ) (hy : y ∈ D.rootGroup δ) : x * y = y * x := by
  obtain ⟨hγr, hγs, hγj⟩ := single_pm_facts hγ
  obtain ⟨hδr, hδs, hδk⟩ := single_pm_facts hδ
  have hγk : γ k = 0 := hγs k (Ne.symm hjk)
  have hδj : δ j = 0 := hδs j hjk
  have hli : LinIndepPair γ δ := by
    intro a b hab
    have h1 := congrFun hab j
    have h2 := congrFun hab k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hδj, hγk, mul_zero,
      zero_add, add_zero] at h1 h2
    exact ⟨(mul_eq_zero.1 h1).resolve_right hγj, (mul_eq_zero.1 h2).resolve_right hδk⟩
  have hbot : (⨆ ε ∈ openCone D.roots γ δ, D.rootGroup ε) ≤ (⊥ : Subgroup K) :=
    iSup₂_le fun ε hε => (openCone_empty_nonadj hjk hjk0 hkj0 hγs hγj hδs hδk ε hε).elim
  exact commutatorElement_eq_one_iff_mul_comm.1
    (Subgroup.mem_bot.1 (hbot (hext.commutator_mem γ hγr δ hδr hli x hx y hy)))

private theorem commute_left_join {G : Type*} [Group G] {P P' : Subgroup G} {b : G}
    (h : ∀ a ∈ P, a * b = b * a) (h' : ∀ a ∈ P', a * b = b * a) :
    ∀ a ∈ P ⊔ P', a * b = b * a := by
  have hle : P ⊔ P' ≤ Subgroup.centralizer ({b} : Set G) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_iff.2 fun g hg => by
        rw [Set.mem_singleton_iff.1 hg]; exact (h a ha).symm)
      (fun a ha => Subgroup.mem_centralizer_iff.2 fun g hg => by
        rw [Set.mem_singleton_iff.1 hg]; exact (h' a ha).symm)
  exact fun a ha => (Subgroup.mem_centralizer_iff.1 (hle ha) b (Set.mem_singleton b)).symm

private theorem commute_right_join {G : Type*} [Group G] {Q Q' : Subgroup G} {a : G}
    (h : ∀ b ∈ Q, a * b = b * a) (h' : ∀ b ∈ Q', a * b = b * a) :
    ∀ b ∈ Q ⊔ Q', a * b = b * a := by
  have hle : Q ⊔ Q' ≤ Subgroup.centralizer ({a} : Set G) :=
    sup_le (fun b hb => Subgroup.mem_centralizer_iff.2 fun g hg => by
        rw [Set.mem_singleton_iff.1 hg]; exact h b hb)
      (fun b hb => Subgroup.mem_centralizer_iff.2 fun g hg => by
        rw [Set.mem_singleton_iff.1 hg]; exact h' b hb)
  exact fun b hb => Subgroup.mem_centralizer_iff.1 (hle hb) a (Set.mem_singleton a)

private theorem commute_join_join {G : Type*} [Group G] {P P' Q Q' : Subgroup G}
    (h₁ : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) (h₂ : ∀ a ∈ P', ∀ b ∈ Q, a * b = b * a)
    (h₃ : ∀ a ∈ P, ∀ b ∈ Q', a * b = b * a) (h₄ : ∀ a ∈ P', ∀ b ∈ Q', a * b = b * a) :
    ∀ a ∈ P ⊔ P', ∀ b ∈ Q ⊔ Q', a * b = b * a := by
  have hQ : ∀ b ∈ Q, ∀ a ∈ P ⊔ P', a * b = b * a := fun b hb =>
    commute_left_join (fun a ha => h₁ a ha b hb) (fun a ha => h₂ a ha b hb)
  have hQ' : ∀ b ∈ Q', ∀ a ∈ P ⊔ P', a * b = b * a := fun b hb =>
    commute_left_join (fun a ha => h₃ a ha b hb) (fun a ha => h₄ a ha b hb)
  intro a ha
  exact commute_right_join (fun b hb => hQ b hb a ha) (fun b hb => hQ' b hb a ha)

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)

include hct hext in
theorem parJ_le_normalizer_unipRad (J : Set (Fin D.rank)) :
    parJ D H J ≤ Subgroup.normalizer (unipRad D J : Set K) := by
  unfold unipRad
  exact le_normalizer_iSup fun k => le_normalizer_iSup fun hk =>
    parJ_le_normalizer_radical hct hext hk

include hct hext in
theorem unipJ_eq_sup (J : Set (Fin D.rank)) :
    unipJ D J = unipRad D J ⊔ ⨆ j ∈ J, rankOne D.rootGroup j := by
  unfold unipJ
  apply le_antisymm
  · exact sup_le (CFSG.AGLEmbeddingD2.ParabLevi.posUnipotent_le_leviRad_sup_leviM (I := J) hct)
      le_sup_right
  · exact sup_le ((unipRad_le_posUnipotent J).trans le_sup_left) le_sup_right

include hct hext in
theorem rankOne_commute {j k : Fin D.rank} (hjk : j ≠ k) (h : D.cartan j k = 0) {x y : K}
    (hx : x ∈ rankOne D.rootGroup j) (hy : y ∈ rankOne D.rootGroup k) : x * y = y * x := by
  have hkj : D.cartan k j = 0 := D.isFiniteType.apply_eq_zero_symm h
  have h₁ : ∀ a ∈ D.rootGroup (Pi.single j 1), ∀ b ∈ D.rootGroup (Pi.single k 1),
      a * b = b * a :=
    fun a ha b hb => comm_gens_nonadj hext hjk h hkj (Or.inl rfl) (Or.inl rfl) ha hb
  have h₂ : ∀ a ∈ D.rootGroup (-Pi.single j 1), ∀ b ∈ D.rootGroup (Pi.single k 1),
      a * b = b * a :=
    fun a ha b hb => comm_gens_nonadj hext hjk h hkj (Or.inr rfl) (Or.inl rfl) ha hb
  have h₃ : ∀ a ∈ D.rootGroup (Pi.single j 1), ∀ b ∈ D.rootGroup (-Pi.single k 1),
      a * b = b * a :=
    fun a ha b hb => comm_gens_nonadj hext hjk h hkj (Or.inl rfl) (Or.inr rfl) ha hb
  have h₄ : ∀ a ∈ D.rootGroup (-Pi.single j 1), ∀ b ∈ D.rootGroup (-Pi.single k 1),
      a * b = b * a :=
    fun a ha b hb => comm_gens_nonadj hext hjk h hkj (Or.inr rfl) (Or.inr rfl) ha hb
  exact commute_join_join h₁ h₂ h₃ h₄ x hx y hy

include hct hext in
theorem posUnipotentExcept_le_of_independent {J : Set (Fin D.rank)} {i : Fin D.rank} (hi : i ∈ J)
    (hJ : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → D.cartan j k = 0) :
    posUnipotentExcept D i ≤
      unipRad D J ⊔ ⨆ j ∈ J \ {i}, D.rootGroup (Pi.single j 1) := by
  unfold posUnipotentExcept
  refine iSup₂_le fun γ hγ => ?_
  by_cases h : ∃ k ∉ J, 0 < γ k
  · obtain ⟨k, hk, hγk⟩ := h
    exact le_sup_of_le_left ((rootGroup_le_radical hγ.1.1 hγk).trans (radical_le_unipRad hk))
  · push Not at h
    have hsupp : ∀ k ∉ J, γ k = 0 := fun k hk =>
      le_antisymm (h k hk) (coord_nonneg_of_ht_pos hγ.1.1 hγ.1.2 k)
    obtain ⟨j, hj, hcases⟩ := eq_of_support_of_independent hJ hγ.1.1 hsupp
    have hnn := coord_nonneg_of_ht_pos hγ.1.1 hγ.1.2 j
    rcases hcases with rfl | rfl | rfl | rfl
    · have hji : j ≠ i := by
        rintro rfl
        exact hγ.2 (Set.mem_insert _ _)
      exact le_sup_of_le_right (le_iSup₂_of_le
        (f := fun j (_ : j ∈ J \ {i}) => D.rootGroup (Pi.single j 1)) j ⟨hj, hji⟩ le_rfl)
    · simp at hnn
    · have hji : j ≠ i := by
        rintro rfl
        exact hγ.2 (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      have hαj : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
        (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j
      exact le_sup_of_le_right ((hext.two_smul_le (Pi.single j 1) hαj hγ.1.1).trans
        (le_iSup₂_of_le (f := fun j (_ : j ∈ J \ {i}) => D.rootGroup (Pi.single j 1)) j
          ⟨hj, hji⟩ le_rfl))
    · simp at hnn

end CFSG.AGLEmbeddingD2.Tits.GN516.Levi

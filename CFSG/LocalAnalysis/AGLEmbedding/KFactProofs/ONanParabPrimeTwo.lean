module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeQuot

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg
open scoped commutatorElement

section Commuting

variable {G : Type*} [Group G]

@[expose] def Commutes (A B : Subgroup G) : Prop := ∀ a ∈ A, ∀ b ∈ B, a * b = b * a

theorem Commutes.symm {A B : Subgroup G} (h : Commutes A B) : Commutes B A :=
  fun b hb a ha => (h a ha b hb).symm

theorem commutes_iff_le_centralizer {A B : Subgroup G} :
    Commutes A B ↔ A ≤ Subgroup.centralizer (B : Set G) := by
  refine ⟨fun h a ha => Subgroup.mem_centralizer_iff.2 fun b hb => (h a ha b hb).symm,
    fun h a ha b hb => ?_⟩
  exact (Subgroup.mem_centralizer_iff.1 (h ha) b hb).symm

theorem Commutes.sup_left {A A' B : Subgroup G} (h : Commutes A B) (h' : Commutes A' B) :
    Commutes (A ⊔ A') B := by
  rw [commutes_iff_le_centralizer] at *
  exact sup_le h h'

theorem Commutes.sup_right {A B B' : Subgroup G} (h : Commutes A B) (h' : Commutes A B') :
    Commutes A (B ⊔ B') :=
  (h.symm.sup_left h'.symm).symm

theorem Commutes.biSup_left {ι : Type*} {s : Finset ι} {A : ι → Subgroup G} {B : Subgroup G}
    (h : ∀ i ∈ s, Commutes (A i) B) : Commutes (⨆ i ∈ s, A i) B := by
  rw [commutes_iff_le_centralizer]
  exact iSup₂_le fun i hi => commutes_iff_le_centralizer.1 (h i hi)

theorem card_sup_dvd_mul_of_commutes [Finite G] {A B : Subgroup G} (h : Commutes A B) :
    Nat.card ↥(A ⊔ B) ∣ Nat.card A * Nat.card B := by
  refine card_sup_dvd_mul A B fun a ha => ?_
  rw [Subgroup.mem_set_normalizer_iff]
  intro g
  constructor
  · intro hg
    have : a * g * a⁻¹ = g := by rw [h a ha g hg, mul_inv_cancel_right]
    rw [this]
    exact hg
  · intro hg
    have e : g = a * g * a⁻¹ := by
      calc g = a⁻¹ * (a * g * a⁻¹) * a := by group
        _ = (a * g * a⁻¹) * a⁻¹ * a := by rw [h a⁻¹ (A.inv_mem ha) _ hg]
        _ = a * g * a⁻¹ := by group
    rw [e]
    exact hg

end Commuting

section Levi

variable {G : Type*} [Group G] [Finite G] {ι : Type*} [DecidableEq ι]

structure LeviData (L : ι → Subgroup G) (p : ℕ) (adj exc : ι → ι → Prop) : Prop where
  adj_symm : ∀ i j, adj i j → adj j i
  comm : ∀ i j, i ≠ j → ¬ adj i j → Commutes (L i) (L j)
  node : ∀ i, ⁅L i, L i⁆ = L i ∨ ¬ p ∣ Nat.card (L i)
  pair : ∀ i j, i ≠ j → adj i j → ⁅L i, L i⁆ ≠ L i → ⁅L j, L j⁆ ≠ L j →
    ⁅L i ⊔ L j, L i ⊔ L j⁆ = L i ⊔ L j ∨ exc i j
  exc_symm : ∀ i j, exc i j → exc j i
  exc_unique : ∀ i j k, exc i j → exc i k → j = k
  exc_perfect : ∀ i j, exc i j → ∃ V : Subgroup G, V ≤ L i ⊔ L j ∧ ⁅V, V⁆ = V ∧
    (p ∣ Nat.card ↥(L i ⊔ L j) → p ∣ Nat.card V)

theorem exists_perfect_dvd_of_leviData {L : ι → Subgroup G} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {adj exc : ι → ι → Prop} (hL : LeviData L p adj exc) (I : Finset ι)
    (hpI : p ∣ Nat.card ↥(⨆ i ∈ I, L i)) :
    ∃ V : Subgroup G, V ≤ ⨆ i ∈ I, L i ∧ ⁅V, V⁆ = V ∧ p ∣ Nat.card V := by
  classical
  set Λ : Subgroup G := ⨆ i ∈ I, L i with hΛ
  set Z : Subgroup G := perfectJoin Λ with hZ
  by_cases hpZ : p ∣ Nat.card Z
  · exact ⟨Z, perfectJoin_le Λ, perfectJoin_perfect Λ, hpZ⟩
  exfalso
  set Bd : Finset ι := I.filter (fun i => ¬ L i ≤ Z) with hBd
  have hLΛ : ∀ i ∈ I, L i ≤ Λ := fun i hi => le_iSup₂_of_le i hi le_rfl
  have hbad : ∀ i ∈ Bd, i ∈ I ∧ ¬ L i ≤ Z := fun i hi => Finset.mem_filter.1 hi
  have hnp : ∀ i ∈ Bd, ⁅L i, L i⁆ ≠ L i := fun i hi hperf =>
    (hbad i hi).2 (le_perfectJoin (hLΛ i (hbad i hi).1) hperf)
  have hfree : ∀ i ∈ Bd, ¬ p ∣ Nat.card (L i) := by
    intro i hi
    rcases hL.node i with h | h
    · exact absurd h (hnp i hi)
    · exact h
  have hedge : ∀ i ∈ Bd, ∀ j ∈ Bd, i ≠ j → adj i j → exc i j := by
    intro i hi j hj hij hadj
    rcases hL.pair i j hij hadj (hnp i hi) (hnp j hj) with h | h
    · exfalso
      apply (hbad i hi).2
      refine (le_sup_left : L i ≤ L i ⊔ L j).trans (le_perfectJoin ?_ h)
      exact sup_le (hLΛ i (hbad i hi).1) (hLΛ j (hbad j hj).1)
    · exact h
  have key : ∀ F : Finset ι, F ⊆ Bd → ¬ p ∣ Nat.card ↥(⨆ i ∈ F, L i) := by
    intro F
    induction F using Finset.strongInduction with
    | H F ih =>
    intro hFB
    by_cases hFe : F = ∅
    · subst hFe
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, Subgroup.card_bot]
      exact fun h => by have := Nat.le_of_dvd one_pos h; omega
    · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hFe
      by_cases hpart : ∃ j' ∈ F, j' ≠ j ∧ adj j j'
      · obtain ⟨j', hj', hjj', hadj⟩ := hpart
        have hexc : exc j j' := hedge j (hFB hj) j' (hFB hj') hjj'.symm hadj
        have hj'e : j' ∈ F.erase j := Finset.mem_erase.2 ⟨hjj', hj'⟩
        set F' : Finset ι := (F.erase j).erase j' with hF'
        have hF'sub : F' ⊆ F := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
        have hjF' : j ∉ F' := by simp [hF']
        have hF'F : F' ⊂ F := (Finset.ssubset_iff_of_subset hF'sub).2 ⟨j, hj, hjF'⟩
        have hFeq : F = insert j (insert j' F') := by
          rw [hF', Finset.insert_erase hj'e, Finset.insert_erase hj]
        have hsplit : (⨆ i ∈ F, L i) = (⨆ i ∈ F', L i) ⊔ (L j ⊔ L j') := by
          conv_lhs => rw [hFeq]
          rw [Finset.iSup_insert, Finset.iSup_insert]
          ac_rfl
        have hcommute : Commutes (⨆ i ∈ F', L i) (L j ⊔ L j') := by
          refine Commutes.biSup_left fun i hi => ?_
          have hiF : i ∈ F := hF'sub hi
          have hij : i ≠ j := fun h => hjF' (h ▸ hi)
          have hij' : i ≠ j' := fun h => by simp [hF', h] at hi
          refine Commutes.sup_right (hL.comm i j hij fun hadj' => ?_)
            (hL.comm i j' hij' fun hadj' => ?_)
          · have h1 := hedge i (hFB hiF) j (hFB hj) hij hadj'
            exact hij' (hL.exc_unique j i j' (hL.exc_symm _ _ h1) hexc)
          · have h1 := hedge i (hFB hiF) j' (hFB hj') hij' hadj'
            exact hij (hL.exc_unique j' i j (hL.exc_symm _ _ h1) (hL.exc_symm _ _ hexc))
        have hpS : ¬ p ∣ Nat.card ↥(L j ⊔ L j') := by
          intro hpS
          obtain ⟨V, hVS, hV, hpV⟩ := hL.exc_perfect j j' hexc
          have hSΛ : L j ⊔ L j' ≤ Λ := sup_le (hLΛ j (hbad j (hFB hj)).1)
            (hLΛ j' (hbad j' (hFB hj')).1)
          exact hpZ ((hpV hpS).trans (Subgroup.card_dvd_of_le (le_perfectJoin (hVS.trans hSΛ) hV)))
        rw [hsplit]
        intro hdvd
        rcases hp.dvd_mul.1 (hdvd.trans (card_sup_dvd_mul_of_commutes hcommute)) with h | h
        · exact ih F' hF'F (hF'sub.trans hFB) h
        · exact hpS h
      · push Not at hpart
        set F' : Finset ι := F.erase j with hF'
        have hF'sub : F' ⊆ F := Finset.erase_subset _ _
        have hjF' : j ∉ F' := by simp [hF']
        have hF'F : F' ⊂ F := (Finset.ssubset_iff_of_subset hF'sub).2 ⟨j, hj, hjF'⟩
        have hFeq : F = insert j F' := by rw [hF', Finset.insert_erase hj]
        have hsplit : (⨆ i ∈ F, L i) = (⨆ i ∈ F', L i) ⊔ L j := by
          conv_lhs => rw [hFeq]
          rw [Finset.iSup_insert, sup_comm]
        have hcommute : Commutes (⨆ i ∈ F', L i) (L j) := by
          refine Commutes.biSup_left fun i hi => ?_
          have hiF : i ∈ F := hF'sub hi
          have hij : i ≠ j := fun h => hjF' (h ▸ hi)
          exact hL.comm i j hij fun hadj' => hpart i hiF hij (hL.adj_symm _ _ hadj')
        rw [hsplit]
        intro hdvd
        rcases hp.dvd_mul.1 (hdvd.trans (card_sup_dvd_mul_of_commutes hcommute)) with h | h
        · exact ih F' hF'F (hF'sub.trans hFB) h
        · exact hfree j (hFB hj) h
  have hEΛ : (⨆ i ∈ Bd, L i) ≤ Λ := iSup₂_le fun i hi => hLΛ i (hbad i hi).1
  have hΛle : Λ ≤ (⨆ i ∈ Bd, L i) ⊔ Z := by
    refine iSup₂_le fun i hi => ?_
    by_cases hiZ : L i ≤ Z
    · exact hiZ.trans le_sup_right
    · exact (le_iSup₂_of_le i (Finset.mem_filter.2 ⟨hi, hiZ⟩) le_rfl :
        L i ≤ ⨆ i ∈ Bd, L i).trans le_sup_left
  have hΛeq : Λ = (⨆ i ∈ Bd, L i) ⊔ Z := le_antisymm hΛle (sup_le hEΛ (perfectJoin_le Λ))
  have hdvd := card_sup_dvd_mul (⨆ i ∈ Bd, L i) Z (hEΛ.trans (le_normalizer_perfectJoin Λ))
  rw [← hΛeq] at hdvd
  rcases hp.dvd_mul.1 (hpI.trans hdvd) with h | h
  · exact key Bd (subset_refl _) h
  · exact hpZ h

end Levi


section Product

variable {G : Type*} [Group G]

theorem card_dvd_mul_of_forall_mem_mul [Finite G] {J A B : Subgroup G} (hAJ : A ≤ J)
    (hBJ : B ≤ J) (h : ∀ x ∈ J, ∃ a ∈ A, ∃ b ∈ B, x = a * b) :
    Nat.card J ∣ Nat.card A * Nat.card B := by
  classical
  set Bj : Subgroup J := B.subgroupOf J with hBj
  set Aj : Subgroup J := A.subgroupOf J with hAj
  set x₀ : J ⧸ Bj := QuotientGroup.mk (1 : J) with hx₀
  have horb : MulAction.orbit Aj x₀ = Set.univ := by
    ext y
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    induction y using QuotientGroup.induction_on with
    | H u =>
      obtain ⟨a, ha, b, hb, hu⟩ := h u.1 u.2
      refine ⟨⟨⟨a, hAJ ha⟩, ha⟩, ?_⟩
      show (QuotientGroup.mk ((⟨a, hAJ ha⟩ : J) * 1) : J ⧸ Bj) = QuotientGroup.mk u
      rw [QuotientGroup.eq]
      show ((⟨a, hAJ ha⟩ * 1 : J)⁻¹ * u) ∈ B.subgroupOf J
      rw [Subgroup.mem_subgroupOf]
      have : ((⟨a, hAJ ha⟩ * 1 : J)⁻¹ * u : J).1 = b := by
        simp [hu]
      rw [this]
      exact hb
  have h1 : Nat.card (J ⧸ Bj) = (MulAction.stabilizer Aj x₀).index := by
    rw [MulAction.index_stabilizer, horb, Set.ncard_univ]
  have h2 : (MulAction.stabilizer Aj x₀).index ∣ Nat.card Aj := Subgroup.index_dvd_card _
  have h3 : Nat.card J = Nat.card (J ⧸ Bj) * Nat.card Bj :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Bj
  have hA : Nat.card Aj = Nat.card A := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAJ).toEquiv
  have hB : Nat.card Bj = Nat.card B := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBJ).toEquiv
  rw [h3, hB, h1]
  rw [hA] at h2
  exact mul_dvd_mul h2 dvd_rfl

end Product


section RankOne

variable {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem rankOne_le_normalizer_posUnipotentExcept
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (i : Fin D.rank) :
    rankOne D.rootGroup i ≤ Subgroup.normalizer (posUnipotentExcept D i : Set K) := by
  have hXN : D.rootGroup (Pi.single i 1) ≤ Subgroup.normalizer (posUnipotentExcept D i : Set K) :=
    rootGroup_single_le_normalizer hext i
  have hnN : n i ∈ Subgroup.normalizer (posUnipotentExcept D i : Set K) :=
    Subgroup.mem_normalizer_fintype fun u hu => conj_n_mem_posUnipotentExcept hct i hu
  refine sup_le hXN fun y hy => ?_
  have hα : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _
      ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)
  have h1 := hct.conj_mem i _ hα y hy
  have h2 : weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i)
      (-Pi.single i 1) = Pi.single i 1 := by
    rw [map_neg, weylAction_simple_single, neg_neg]
  rw [h2] at h1
  have h3 : y = (n i)⁻¹ * (n i * y * (n i)⁻¹) * n i := by group
  rw [h3]
  exact mul_mem (mul_mem (inv_mem hnN) (hXN h1)) hnN

theorem iSup_torus_le_normalizer_rankOne
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (i : Fin D.rank) :
    (⨆ k, H k) ≤ Subgroup.normalizer (rankOne D.rootGroup i : Set K) := by
  refine iSup_le fun k h hh => ?_
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hα' : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
  exact conj_mem_sup h (fun y hy => hct.H_conj_mem k _ hα h hh y hy)
    (fun y hy => hct.H_conj_mem k _ hα' h hh y hy) x hx

theorem exists_mul_rankOne_eq
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (i : Fin D.rank) {b : K} (hb : b ∈ borel D H) {l : K}
    (hl : l ∈ rankOne D.rootGroup i) :
    ∃ l' ∈ rankOne D.rootGroup i, ∃ b' ∈ borel D H, b * l = l' * b' := by
  obtain ⟨t, ht, u, hu, x, hx, rfl⟩ := exists_eq_mul_mul_of_mem_borel hct hext i hb
  have hxL : x ∈ rankOne D.rootGroup i := Subgroup.mem_sup_left hx
  set l'' : K := x * l with hl''
  have hl''L : l'' ∈ rankOne D.rootGroup i := mul_mem hxL hl
  have hu' : l''⁻¹ * u * l'' ∈ posUnipotentExcept D i := by
    have hN := rankOne_le_normalizer_posUnipotentExcept hct hext i (inv_mem hl''L)
    have := (Subgroup.mem_set_normalizer_iff.1 hN u).1 hu
    simpa using this
  have htL : t * l'' * t⁻¹ ∈ rankOne D.rootGroup i :=
    (Subgroup.mem_set_normalizer_iff.1 (iSup_torus_le_normalizer_rankOne hct i ht) l'').1 hl''L
  refine ⟨t * l'' * t⁻¹, htL, t * (l''⁻¹ * u * l''),
    mul_mem (iSup_le_borel ht) (posUnipotent_le_borel (posUnipotentExcept_le_posUnipotent i hu')),
    ?_⟩
  rw [hl'']
  group

end RankOne


section Orthogonal

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem root_apply_mul_apply_nonneg {ε : Fin D.rank → ℤ} (hε : ε ∈ D.roots) (i j : Fin D.rank) :
    0 ≤ ε i * ε j := by
  rcases (RootSystem.ofCartan D.isFiniteType D.divisible).sign ε hε with h | h
  · exact mul_nonneg (h i) (h j)
  · nlinarith [h i, h j]

theorem pair_apply_left {i j : Fin D.rank} (hij : i ≠ j) (z : ℤ × ℤ) : pair i j z i = z.1 := by
  simp [pair_apply, hij]

theorem pair_apply_right {i j : Fin D.rank} (hij : i ≠ j) (z : ℤ × ℤ) : pair i j z j = z.2 := by
  simp [pair_apply, hij.symm]

theorem pair_reflection_left_mem_roots {i j : Fin D.rank} {z : ℤ × ℤ}
    (hz : pair i j z ∈ D.roots) :
    pair i j (-z.1 - D.cartan i j * z.2, z.2) ∈ D.roots := by
  have := (RootSystem.ofCartan D.isFiniteType D.divisible).refl_mem i _ hz
  rwa [RootSystem.ofCartan_refl_apply, reflection_pair_left j (D.isFiniteType.apply_self i)]
    at this

theorem pair_reflection_right_mem_roots {i j : Fin D.rank} {z : ℤ × ℤ}
    (hz : pair i j z ∈ D.roots) :
    pair i j (z.1, -z.2 - D.cartan j i * z.1) ∈ D.roots := by
  have := (RootSystem.ofCartan D.isFiniteType D.divisible).refl_mem j _ hz
  rwa [RootSystem.ofCartan_refl_apply, reflection_pair_right i (D.isFiniteType.apply_self j)]
    at this

theorem nsmul_add_nsmul_eq_pair (i j : Fin D.rank) (σ τ : ℤ) (a b : ℕ) :
    a • (σ • (Pi.single i 1 : Fin D.rank → ℤ)) + b • (τ • (Pi.single j 1 : Fin D.rank → ℤ)) =
      pair i j ((a : ℤ) * σ, (b : ℤ) * τ) := by
  rw [pair_apply, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]

theorem linIndepPair_single {i j : Fin D.rank} (hij : i ≠ j) {σ τ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hτ : τ = 1 ∨ τ = -1) :
    LinIndepPair (σ • (Pi.single i 1 : Fin D.rank → ℤ)) (τ • (Pi.single j 1 : Fin D.rank → ℤ)) := by
  intro a b h
  have h1 := congrFun h i
  have h2 := congrFun h j
  simp [hij, hij.symm] at h1 h2
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> simp_all

theorem openCone_eq_empty_of_cartan_eq_zero {i j : Fin D.rank} (hij : i ≠ j)
    (hA : D.cartan i j = 0) {σ τ : ℤ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    openCone D.roots (σ • Pi.single i 1) (τ • Pi.single j 1) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro ε ⟨hε, a, b, ha, hb, rfl⟩
  rw [nsmul_add_nsmul_eq_pair] at hε
  have h1 := root_apply_mul_apply_nonneg hε i j
  have h2 := root_apply_mul_apply_nonneg (pair_reflection_left_mem_roots hε) i j
  rw [pair_apply_left hij, pair_apply_right hij] at h1 h2
  simp only [hA, zero_mul, sub_zero] at h2
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> nlinarith

theorem commutes_rootGroup_of_cartan_eq_zero (hext : SteinbergExtras D n H) {i j : Fin D.rank}
    (hij : i ≠ j) (hA : D.cartan i j = 0) {σ τ : ℤ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    Commutes (D.rootGroup (σ • Pi.single i 1)) (D.rootGroup (τ • Pi.single j 1)) := by
  have hroot : ∀ (k : Fin D.rank) (s : ℤ), (s = 1 ∨ s = -1) →
      s • (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots := by
    intro k s hs
    have h1 : (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots :=
      (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k
    rcases hs with rfl | rfl
    · simpa using h1
    · simpa using (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ h1
  intro x hx y hy
  have h := hext.commutator_mem _ (hroot i σ hσ) _ (hroot j τ hτ) (linIndepPair_single hij hσ hτ)
    x hx y hy
  rw [openCone_eq_empty_of_cartan_eq_zero hij hA hσ hτ] at h
  simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Subgroup.mem_bot] at h
  exact commutatorElement_eq_one_iff_mul_comm.1 h

theorem commutes_rankOne_of_cartan_eq_zero (hext : SteinbergExtras D n H) {i j : Fin D.rank}
    (hij : i ≠ j) (hA : D.cartan i j = 0) :
    Commutes (rankOne D.rootGroup i) (rankOne D.rootGroup j) := by
  have h : ∀ σ τ : ℤ, (σ = 1 ∨ σ = -1) → (τ = 1 ∨ τ = -1) →
      Commutes (D.rootGroup (σ • Pi.single i 1)) (D.rootGroup (τ • Pi.single j 1)) :=
    fun σ τ hσ hτ => commutes_rootGroup_of_cartan_eq_zero hext hij hA hσ hτ
  have h1 : ∀ σ : ℤ, (σ = 1 ∨ σ = -1) → Commutes (D.rootGroup (σ • Pi.single i 1))
      (rankOne D.rootGroup j) := fun σ hσ => by
    refine Commutes.sup_right ?_ ?_
    · simpa using h σ 1 hσ (Or.inl rfl)
    · simpa using h σ (-1) hσ (Or.inr rfl)
  refine Commutes.sup_left ?_ ?_
  · simpa using h1 1 (Or.inl rfl)
  · simpa using h1 (-1) (Or.inr rfl)

end Orthogonal

section PairPerfect

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem le_of_mem_of_card_eq_two {X N : Subgroup K} (hX : Nat.card X = 2) {y : K} (hyX : y ∈ X)
    (hy1 : y ≠ 1) (hyN : y ∈ N) : X ≤ N := by
  have : Finite X := Nat.finite_of_card_ne_zero (by omega)
  have hz : Subgroup.zpowers y ≤ X := (Subgroup.zpowers_le).2 hyX
  have hdvd : Nat.card (Subgroup.zpowers y) ∣ 2 := hX ▸ Subgroup.card_dvd_of_le hz
  have hne : Nat.card (Subgroup.zpowers y) ≠ 1 := by
    rw [Nat.card_zpowers]
    exact fun h => hy1 (orderOf_eq_one_iff.1 h)
  have h2 : Nat.card (Subgroup.zpowers y) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd h hne
    · exact h
  have : Subgroup.zpowers y = X :=
    Subgroup.eq_of_le_of_card_ge hz (by rw [h2, hX])
  rw [← this]
  exact (Subgroup.zpowers_le).2 hyN

theorem conj_mem_commutator_self {S : Subgroup K} {g : K} (hg : g ∈ S) {z : K}
    (hz : z ∈ ⁅S, S⁆) : g * z * g⁻¹ ∈ ⁅S, S⁆ := by
  have h1 : (⁅S, S⁆).map (MulAut.conj g).toMonoidHom =
      ⁅S.map (MulAut.conj g).toMonoidHom, S.map (MulAut.conj g).toMonoidHom⁆ :=
    Subgroup.map_commutator _ _ _
  have h2 : S.map (MulAut.conj g).toMonoidHom ≤ S := by
    rintro _ ⟨s, hs, rfl⟩
    exact mul_mem (mul_mem hg hs) (inv_mem hg)
  have h3 : (⁅S, S⁆).map (MulAut.conj g).toMonoidHom ≤ ⁅S, S⁆ :=
    h1 ▸ Subgroup.commutator_mono h2 h2
  exact h3 ⟨z, hz, rfl⟩

theorem weylAction_simple_pair_left (i j : Fin D.rank) (z : ℤ × ℤ) :
    weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i)
        (pair i j z) = pair i j (-z.1 - D.cartan i j * z.2, z.2) := by
  rw [weylAction_simple, reflection_pair_left j (D.isFiniteType.apply_self i)]

theorem weylAction_simple_pair_right (i j : Fin D.rank) (z : ℤ × ℤ) :
    weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j)
        (pair i j z) = pair i j (z.1, -z.2 - D.cartan j i * z.1) := by
  rw [weylAction_simple, reflection_pair_right i (D.isFiniteType.apply_self j)]

theorem single_eq_pair_left (i j : Fin D.rank) :
    (Pi.single i 1 : Fin D.rank → ℤ) = pair i j (1, 0) := by
  simp [pair_apply]

theorem single_eq_pair_right (i j : Fin D.rank) :
    (Pi.single j 1 : Fin D.rank → ℤ) = pair i j (0, 1) := by
  simp [pair_apply]

theorem openCone_pair_subset {i j : Fin D.rank} (hij : i ≠ j) (hAij : D.cartan i j = -1)
    (hAji : D.cartan j i = -1) {ε : Fin D.rank → ℤ}
    (hε : ε ∈ openCone D.roots (Pi.single i 1) (Pi.single j 1)) :
    ε = pair i j (1, 1) ∨ ε = pair i j (2, 2) := by
  obtain ⟨hεr, a, b, ha, hb, rfl⟩ := hε
  have e : a • (Pi.single i 1 : Fin D.rank → ℤ) + b • (Pi.single j 1 : Fin D.rank → ℤ) =
      pair i j ((a : ℤ), (b : ℤ)) := by
    simpa using nsmul_add_nsmul_eq_pair i j 1 1 a b
  rw [e] at hεr ⊢
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have h1 := root_apply_mul_apply_nonneg (pair_reflection_left_mem_roots hεr) i j
  have h2 := root_apply_mul_apply_nonneg (pair_reflection_right_mem_roots hεr) i j
  rw [pair_apply_left hij, pair_apply_right hij] at h1 h2
  simp only [hAij, hAji] at h1 h2
  have hba : (b : ℤ) = a := by nlinarith
  have hba' : b = a := by exact_mod_cast hba
  subst hba'
  by_cases ha3 : 3 ≤ b
  · exfalso
    have hδ : pair i j ((1 : ℤ), (1 : ℤ)) ∈ D.roots := by
      have := pair_reflection_right_mem_roots (D := D) (i := i) (j := j) (z := (1, 0))
        (by rw [← single_eq_pair_left]; exact (RootSystem.ofCartan D.isFiniteType
          D.divisible).single_mem i)
      simpa [hAji] using this
    have hnot : ¬ LinIndepPair (pair i j ((b : ℤ), (b : ℤ))) (pair i j ((1 : ℤ), (1 : ℤ))) := by
      intro h
      have := (h 1 (-(b : ℤ)) (by
        simp only [pair_apply]
        ext k
        simp [Pi.single_apply]
        ring)).1
      exact one_ne_zero this
    have hprop := (RootSystem.ofCartan D.isFiniteType D.divisible).proportional _ hεr _ hδ hnot
    rcases hprop with h | h | h | h | h | h <;>
    · have := congrFun h i
      simp [pair_apply_left hij] at this <;> omega
  · have : b = 1 ∨ b = 2 := by omega
    rcases this with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)

theorem conj_ne_one {g c : K} (hc : c ≠ 1) : g * c * g⁻¹ ≠ 1 := by
  intro h
  apply hc
  calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
    _ = 1 := by rw [h]; group

theorem pair_one_one_mem_roots {i j : Fin D.rank} (hAji : D.cartan j i = -1) :
    pair i j ((1 : ℤ), (1 : ℤ)) ∈ D.roots := by
  have := pair_reflection_right_mem_roots (D := D) (i := i) (j := j) (z := (1, 0))
    (by rw [← single_eq_pair_left]; exact (RootSystem.ofCartan D.isFiniteType
      D.divisible).single_mem i)
  simpa [hAji] using this

theorem commutator_rankOne_sup_eq
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {i j : Fin D.rank} (hij : i ≠ j) (hAij : D.cartan i j = -1)
    (hAji : D.cartan j i = -1) (hci : Nat.card (D.rootGroup (Pi.single i 1)) = 2)
    (hci' : Nat.card (D.rootGroup (-Pi.single i 1)) = 2)
    (hcj : Nat.card (D.rootGroup (Pi.single j 1)) = 2)
    (hcj' : Nat.card (D.rootGroup (-Pi.single j 1)) = 2)
    (hnc : ∃ x ∈ D.rootGroup (Pi.single i 1), ∃ y ∈ D.rootGroup (Pi.single j 1), ⁅x, y⁆ ≠ 1) :
    ⁅rankOne D.rootGroup i ⊔ rankOne D.rootGroup j,
        rankOne D.rootGroup i ⊔ rankOne D.rootGroup j⁆ =
      rankOne D.rootGroup i ⊔ rankOne D.rootGroup j := by
  set S := rankOne D.rootGroup i ⊔ rankOne D.rootGroup j with hS
  set N := ⁅S, S⁆ with hN
  refine le_antisymm (commutator_self_le S) ?_
  obtain ⟨xi, hxi, xj, hxj, hc1⟩ := hnc
  have hLiS : rankOne D.rootGroup i ≤ S := le_sup_left
  have hLjS : rankOne D.rootGroup j ≤ S := le_sup_right
  have hαi : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hαj : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j
  have hδ : pair i j ((1 : ℤ), (1 : ℤ)) ∈ D.roots := pair_one_one_mem_roots hAji
  have hxiS : xi ∈ S := hLiS (Subgroup.mem_sup_left hxi)
  have hxjS : xj ∈ S := hLjS (Subgroup.mem_sup_left hxj)
  have hniS : n i ∈ S := hLiS (hct.n_mem i)
  have hnjS : n j ∈ S := hLjS (hct.n_mem j)
  set c : K := ⁅xi, xj⁆ with hc
  have hcN : c ∈ N := Subgroup.commutator_mem_commutator hxiS hxjS
  have hcX : c ∈ D.rootGroup (pair i j ((1 : ℤ), (1 : ℤ))) := by
    have hmem := hext.commutator_mem _ hαi _ hαj (by
      simpa using linIndepPair_single (D := D) hij (Or.inl rfl) (Or.inl rfl)) xi hxi xj hxj
    refine (iSup₂_le (fun ε hε => ?_) : ⨆ ε ∈ openCone D.roots (Pi.single i 1)
      (Pi.single j 1), D.rootGroup ε ≤ D.rootGroup (pair i j ((1 : ℤ), (1 : ℤ)))) hmem
    rcases openCone_pair_subset hij hAij hAji hε with rfl | rfl
    · exact le_rfl
    · have h2 : pair i j ((2 : ℤ), (2 : ℤ)) = 2 • pair i j ((1 : ℤ), (1 : ℤ)) := by
        rw [← map_nsmul]
        rfl
      have h2r : 2 • pair i j ((1 : ℤ), (1 : ℤ)) ∈ D.roots := h2 ▸ hε.1
      rw [h2]
      exact hext.two_smul_le _ hδ h2r
  have hyj : n i * c * (n i)⁻¹ ∈ D.rootGroup (Pi.single j 1) := by
    have h := hct.conj_mem i _ hδ c hcX
    rw [weylAction_simple_pair_left] at h
    simpa [hAij, ← single_eq_pair_right] using h
  have hzi : n j * c * (n j)⁻¹ ∈ D.rootGroup (Pi.single i 1) := by
    have h := hct.conj_mem j _ hδ c hcX
    rw [weylAction_simple_pair_right] at h
    simpa [hAji, ← single_eq_pair_left] using h
  have hyjN : n i * c * (n i)⁻¹ ∈ N := conj_mem_commutator_self hniS hcN
  have hziN : n j * c * (n j)⁻¹ ∈ N := conj_mem_commutator_self hnjS hcN
  have hyj1 : n i * c * (n i)⁻¹ ≠ 1 := conj_ne_one hc1
  have hzi1 : n j * c * (n j)⁻¹ ≠ 1 := conj_ne_one hc1
  have hXj : D.rootGroup (Pi.single j 1) ≤ N := le_of_mem_of_card_eq_two hcj hyj hyj1 hyjN
  have hXi : D.rootGroup (Pi.single i 1) ≤ N := le_of_mem_of_card_eq_two hci hzi hzi1 hziN
  have hneg : ∀ (k : Fin D.rank) {y : K}, y ∈ D.rootGroup (Pi.single k 1) →
      n k * y * (n k)⁻¹ ∈ D.rootGroup (-Pi.single k 1) := by
    intro k y hy
    have h := hct.conj_mem k _ ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k) y hy
    rwa [weylAction_simple_single] at h
  have hXj' : D.rootGroup (-Pi.single j 1) ≤ N :=
    le_of_mem_of_card_eq_two hcj' (hneg j hyj) (conj_ne_one hyj1)
      (conj_mem_commutator_self hnjS (hXj hyj))
  have hXi' : D.rootGroup (-Pi.single i 1) ≤ N :=
    le_of_mem_of_card_eq_two hci' (hneg i hzi) (conj_ne_one hzi1)
      (conj_mem_commutator_self hniS (hXi hzi))
  exact sup_le (sup_le hXi hXi') (sup_le hXj hXj')

theorem card_rootGroup_of_param {k : Type*} [Field k]
    {x : (Fin D.rank → ℤ) → k → K}
    (hx : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup x)
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    Nat.card (D.rootGroup γ) = Nat.card k := by
  obtain ⟨hmem, -, hinj⟩ := hx γ hγ
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun c : k => (⟨x γ c, (hmem _).2 ⟨c, rfl⟩⟩ : D.rootGroup γ)) ⟨fun a b hab => ?_, fun g => ?_⟩)
  · exact hinj (congrArg Subtype.val hab)
  · obtain ⟨c, hc⟩ := (hmem g.1).1 g.2
    exact ⟨c, Subtype.ext hc⟩

theorem commutator_rankOne_sup_eq_of_param
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {k : Type} [Field k] {x : (Fin D.rank → ℤ) → k → K}
    (hx : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup x)
    (hk : Nat.card k = 2) {i j : Fin D.rank} (hij : i ≠ j) (hAij : D.cartan i j = -1)
    (hAji : D.cartan j i = -1)
    (hnc : ∃ a b : k, ⁅x (Pi.single i 1) a, x (Pi.single j 1) b⁆ ≠ 1) :
    ⁅rankOne D.rootGroup i ⊔ rankOne D.rootGroup j,
        rankOne D.rootGroup i ⊔ rankOne D.rootGroup j⁆ =
      rankOne D.rootGroup i ⊔ rankOne D.rootGroup j := by
  have hα : ∀ l : Fin D.rank, (Pi.single l 1 : Fin D.rank → ℤ) ∈ D.roots := fun l =>
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem l
  have hα' : ∀ l : Fin D.rank, (-Pi.single l 1 : Fin D.rank → ℤ) ∈ D.roots := fun l =>
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ (hα l)
  obtain ⟨a, b, hab⟩ := hnc
  refine commutator_rankOne_sup_eq hct hext hij hAij hAji
    ((card_rootGroup_of_param hx (hα i)).trans hk) ((card_rootGroup_of_param hx (hα' i)).trans hk)
    ((card_rootGroup_of_param hx (hα j)).trans hk) ((card_rootGroup_of_param hx (hα' j)).trans hk)
    ⟨x (Pi.single i 1) a, ((hx _ (hα i)).1 _).2 ⟨a, rfl⟩, x (Pi.single j 1) b,
      ((hx _ (hα j)).1 _).2 ⟨b, rfl⟩, hab⟩

end PairPerfect

section Assembly

variable {K Y : Type*} [Group K] [Group Y] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

structure TwoLevi (D : UniversalRootDatum K) (exc : Fin D.rank → Fin D.rank → Prop) : Prop where
  node : ∀ i, ⁅rankOne D.rootGroup i, rankOne D.rootGroup i⁆ = rankOne D.rootGroup i ∨
    ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card (rankOne D.rootGroup i)
  pair : ∀ i j, i ≠ j → D.cartan i j ≠ 0 →
    ⁅rankOne D.rootGroup i, rankOne D.rootGroup i⁆ ≠ rankOne D.rootGroup i →
    ⁅rankOne D.rootGroup j, rankOne D.rootGroup j⁆ ≠ rankOne D.rootGroup j →
    ⁅rankOne D.rootGroup i ⊔ rankOne D.rootGroup j, rankOne D.rootGroup i ⊔ rankOne D.rootGroup j⁆ =
      rankOne D.rootGroup i ⊔ rankOne D.rootGroup j ∨ exc i j
  exc_symm : ∀ i j, exc i j → exc j i
  exc_unique : ∀ i j k, exc i j → exc i k → j = k
  exc_perfect : ∀ i j, exc i j → ∃ V : Subgroup K,
    V ≤ rankOne D.rootGroup i ⊔ rankOne D.rootGroup j ∧ ⁅V, V⁆ = V ∧
      ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ Nat.card ↥(rankOne D.rootGroup i ⊔ rankOne D.rootGroup j) →
        p ∣ Nat.card V

theorem map_commutator_self_eq {A : Subgroup K} (π : K →* Y) (h : ⁅A, A⁆ = A) :
    ⁅A.map π, A.map π⁆ = A.map π := by
  rw [← Subgroup.map_commutator, h]

theorem Commutes.map {A B : Subgroup K} (π : K →* Y) (h : Commutes A B) :
    Commutes (A.map π) (B.map π) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, h a ha b hb]

theorem dvd_card_map_of_dvd_card [Finite K] (π : K →* Y) (hker : ∀ z ∈ π.ker, z ^ 3 = 1) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {V : Subgroup K} (hpV : p ∣ Nat.card V) :
    p ∣ Nat.card (V.map π) := by
  have : Fact p.Prime := ⟨hp⟩
  have h := Subgroup.card_ker_mul_card_range (π.comp V.subtype)
  have hr : (π.comp V.subtype).range = V.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hr] at h
  rw [← h] at hpV
  rcases hp.dvd_mul.1 hpV with h1 | h1
  · exfalso
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h1
    have hx' : ((x : V) : K) ∈ π.ker := MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 x.2)
    have hx3 : ((x : V) : K) ^ 3 = 1 := hker _ hx'
    have : orderOf ((x : V) : K) ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    have e : orderOf ((x : V) : K) = orderOf x := by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    rw [e, hx] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · exact h1

theorem TwoLevi.leviData [Finite K] {exc : Fin D.rank → Fin D.rank → Prop} (hL : TwoLevi D exc)
    (π : K →* Y) (hker : ∀ z ∈ π.ker, z ^ 3 = 1)
    (hsymm : ∀ i j, D.cartan i j ≠ 0 → D.cartan j i ≠ 0)
    (hcomm : ∀ i j, i ≠ j → D.cartan i j = 0 →
      Commutes (rankOne D.rootGroup i) (rankOne D.rootGroup j)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) :
    LeviData (fun i => (rankOne D.rootGroup i).map π) p (fun i j => D.cartan i j ≠ 0) exc where
  adj_symm := hsymm
  comm i j hij hadj := (hcomm i j hij (not_not.1 hadj)).map π
  node i := by
    rcases hL.node i with h | h
    · exact Or.inl (map_commutator_self_eq (A := rankOne D.rootGroup i) π h)
    · exact Or.inr fun hd => h p hp hp5
        (hd.trans (Subgroup.card_map_dvd (rankOne D.rootGroup i) π))
  pair i j hij hadj hi hj := by
    have hi' : ⁅rankOne D.rootGroup i, rankOne D.rootGroup i⁆ ≠ rankOne D.rootGroup i :=
      fun h => hi (map_commutator_self_eq (A := rankOne D.rootGroup i) π h)
    have hj' : ⁅rankOne D.rootGroup j, rankOne D.rootGroup j⁆ ≠ rankOne D.rootGroup j :=
      fun h => hj (map_commutator_self_eq (A := rankOne D.rootGroup j) π h)
    rcases hL.pair i j hij hadj hi' hj' with h | h
    · left
      rw [← Subgroup.map_sup]
      exact map_commutator_self_eq π h
    · exact Or.inr h
  exc_symm := hL.exc_symm
  exc_unique := hL.exc_unique
  exc_perfect i j h := by
    obtain ⟨V, hVS, hV, hpV⟩ := hL.exc_perfect i j h
    refine ⟨V.map π, ?_, map_commutator_self_eq π hV, fun hd => ?_⟩
    · rw [← Subgroup.map_sup]
      exact Subgroup.map_mono hVS
    · rw [← Subgroup.map_sup] at hd
      exact dvd_card_map_of_dvd_card π hker hp hp5
        (hpV p hp hp5 (hd.trans (Subgroup.card_map_dvd _ π)))

theorem iSup₂_induction {ι : Type*} {P : ι → Prop} {S : ι → Subgroup Y} {C : Y → Prop} {x : Y}
    (hx : x ∈ ⨆ i, ⨆ (_ : P i), S i) (mem : ∀ i, P i → ∀ y ∈ S i, C y) (one : C 1)
    (mul : ∀ y z, C y → C z → C (y * z)) : C x := by
  refine Subgroup.iSup_induction (C := C) _ hx (fun i y hy => ?_) one mul
  exact Subgroup.iSup_induction (C := C) _ hy (fun hPi z hz => mem i hPi z hz) one mul

section Quotient

variable {M : ℕ} {π : K →* Y}

theorem _root_.CFSG.AGLEmbedding.ParabHub.BorelQuotient.parabCore_two [Finite K] [Finite Y]
    {exc : Fin D.rank → Fin D.rank → Prop} (h : BorelQuotient D n H π M) (hM : M ∣ 3)
    (hL : TwoLevi D exc) : ParabCore Y 2 := by
  classical
  intro T J hNJ hJ p hp hp5
  refine ⟨fun hpq => ?_, fun hpJ => Or.inr ?_⟩
  · exfalso
    have : p ≤ 3 := Nat.le_of_dvd (by norm_num) (by simpa using hpq)
    omega
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : (borel D H).map π' ≤ J := by
    rw [← hNπ]
    exact hNJ
  have hBA : borel D H ≤ J.comap π' := fun b hb => hBJ ⟨b, hb, rfl⟩
  have hJeq := eq_map_borel_sup_of_le h.ct h.extras hπ' hBJ
  have hker3 : ∀ z ∈ π'.ker, z ^ 3 = 1 := fun z hz => by
    obtain ⟨k, hk⟩ := hM
    rw [hk, pow_mul, hQ.ker_pow z hz, one_pow]
  have hpB : ¬ p ∣ Nat.card ((borel D H).map π') := fun hpB => by
    have := dvd_of_dvd_card_map_borel h.ct h.extras h.pGroup π'
      (fun t ht => hQ.pow_eq_one_of_mem_iSup ht) hp (by omega) hpB
    have := Nat.le_of_dvd (by norm_num) (this.trans hM)
    omega
  set I : Finset (Fin D.rank) := Finset.univ.filter (fun i => i ∈ negIndices D (J.comap π'))
    with hI
  set Λ : Subgroup Y := ⨆ i ∈ I, (rankOne D.rootGroup i).map π' with hΛ
  have hmemI : ∀ i ∈ I, i ∈ negIndices D (J.comap π') := fun i hi => (Finset.mem_filter.1 hi).2
  have hLJ : ∀ i ∈ I, (rankOne D.rootGroup i).map π' ≤ J := fun i hi =>
    Subgroup.map_le_iff_le_comap.2 (rankOne_le_of_mem_negIndices hBA (hmemI i hi))
  have hΛJ : Λ ≤ J := iSup₂_le hLJ
  have hswap : ∀ g ∈ Λ, ∀ b ∈ (borel D H).map π', ∃ g' ∈ Λ, ∃ b' ∈ (borel D H).map π',
      b * g = g' * b' := by
    intro g hg
    refine iSup₂_induction (C := fun g => ∀ b ∈ (borel D H).map π', ∃ g' ∈ Λ,
      ∃ b' ∈ (borel D H).map π', b * g = g' * b') hg ?_ ?_ ?_
    · rintro i hi _ ⟨l, hl, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨l', hl', b', hb', e⟩ := exists_mul_rankOne_eq h.ct h.extras i hb hl
      have hLΛ : (rankOne D.rootGroup i).map π' ≤ Λ := le_iSup₂_of_le i hi le_rfl
      exact ⟨π' l', hLΛ ⟨l', hl', rfl⟩, π' b', ⟨b', hb', rfl⟩, by
        rw [← map_mul, ← map_mul, e]⟩
    · intro b hb
      exact ⟨1, one_mem _, b, hb, by rw [one_mul, mul_one]⟩
    · intro y z hy hz b hb
      obtain ⟨y', hy', b₁, hb₁, e₁⟩ := hy b hb
      obtain ⟨z', hz', b₂, hb₂, e₂⟩ := hz b₁ hb₁
      exact ⟨y' * z', mul_mem hy' hz', b₂, hb₂, by rw [← mul_assoc, e₁, mul_assoc, e₂, mul_assoc]⟩
  let T' : Subgroup Y :=
    { carrier := {x | ∃ g ∈ Λ, ∃ b ∈ (borel D H).map π', x = g * b}
      mul_mem' := by
        rintro _ _ ⟨g₁, hg₁, b₁, hb₁, rfl⟩ ⟨g₂, hg₂, b₂, hb₂, rfl⟩
        obtain ⟨g', hg', b', hb', e⟩ := hswap g₂ hg₂ b₁ hb₁
        exact ⟨g₁ * g', mul_mem hg₁ hg', b' * b₂, mul_mem hb' hb₂, by
          rw [mul_assoc, ← mul_assoc b₁, e]; group⟩
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨g, hg, b, hb, rfl⟩
        obtain ⟨g', hg', b', hb', e⟩ := hswap g⁻¹ (inv_mem hg) b⁻¹ (inv_mem hb)
        exact ⟨g', hg', b', hb', by rw [mul_inv_rev, e]⟩ }
  have hJT : J ≤ T' := by
    rw [hJeq]
    refine sup_le (fun b hb => ⟨1, one_mem _, b, hb, by rw [one_mul]⟩) ?_
    refine iSup₂_le fun i hi => ?_
    have hiI : i ∈ I := Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩
    have hLΛ : (rankOne D.rootGroup i).map π' ≤ Λ := le_iSup₂_of_le i hiI le_rfl
    exact fun x hx => ⟨x, hLΛ hx, 1, one_mem _, by rw [mul_one]⟩
  have hJdvd : Nat.card J ∣ Nat.card Λ * Nat.card ((borel D H).map π') :=
    card_dvd_mul_of_forall_mem_mul hΛJ hBJ fun x hx => hJT hx
  have hpΛ : p ∣ Nat.card Λ := by
    rcases hp.dvd_mul.1 (hpJ.trans hJdvd) with h1 | h1
    · exact h1
    · exact absurd h1 hpB
  have hsymm : ∀ i j, D.cartan i j ≠ 0 → D.cartan j i ≠ 0 := fun i j h1 h2 =>
    h1 (D.isFiniteType.apply_eq_zero_iff.2 h2)
  have hLD := hL.leviData π' hker3 hsymm
    (fun i j hij hA => commutes_rankOne_of_cartan_eq_zero h.extras hij hA) hp hp5
  obtain ⟨V, hVΛ, hV, hpV⟩ := exists_perfect_dvd_of_leviData hp hp5 hLD I hpΛ
  exact ⟨V, hVΛ.trans hΛJ, hV, hpV⟩

end Quotient

theorem TwoLevi.of_pair
    (node : ∀ i, ⁅rankOne D.rootGroup i, rankOne D.rootGroup i⁆ = rankOne D.rootGroup i ∨
      ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card (rankOne D.rootGroup i))
    (pair : ∀ i j, i ≠ j → D.cartan i j ≠ 0 →
      ⁅rankOne D.rootGroup i, rankOne D.rootGroup i⁆ ≠ rankOne D.rootGroup i →
      ⁅rankOne D.rootGroup j, rankOne D.rootGroup j⁆ ≠ rankOne D.rootGroup j →
      ⁅rankOne D.rootGroup i ⊔ rankOne D.rootGroup j,
          rankOne D.rootGroup i ⊔ rankOne D.rootGroup j⁆ =
        rankOne D.rootGroup i ⊔ rankOne D.rootGroup j) :
    TwoLevi D (fun _ _ => False) where
  node := node
  pair i j hij hA hi hj := Or.inl (pair i j hij hA hi hj)
  exc_symm _ _ h := h
  exc_unique _ _ _ h := h.elim
  exc_perfect _ _ h := h.elim

theorem not_dvd_card_rankOne_of_sl2 {i : Fin D.rank} {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) {x : (Fin D.rank → ℤ) → k → K}
    (hx : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup x)
    {ρ : Matrix.SpecialLinearGroup (Fin 2) k →* K}
    (hU : ∀ c, ρ (sl2Upper c) = x (Pi.single i 1) c)
    (hL : ∀ c, ρ (sl2Lower c) = x (-Pi.single i 1) c) :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card (rankOne D.rootGroup i) := by
  intro p hp hp5 hd
  rw [rankOne_eq_range_of_sl2 hx hU hL] at hd
  have h6 : Nat.card ρ.range ∣ 2 * 3 := (Subgroup.card_range_dvd ρ).trans (by
    rw [card_sl2, hk]
    norm_num)
  rcases (Nat.Prime.dvd_mul hp).1 (hd.trans h6) with h | h <;>
    have := Nat.le_of_dvd (by norm_num) h <;> omega

theorem TwoLevi.of_param {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2)
    {x : (Fin D.rank → ℤ) → k → K}
    (hx : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup x)
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H)
    (hsl2 : ∀ i : Fin D.rank, ∃ ρ : Matrix.SpecialLinearGroup (Fin 2) k →* K,
      (∀ c, ρ (sl2Upper c) = x (Pi.single i 1) c) ∧ ∀ c, ρ (sl2Lower c) = x (-Pi.single i 1) c)
    {exc : Fin D.rank → Fin D.rank → Prop} (hsymm : ∀ i j, exc i j → exc j i)
    (huniq : ∀ i j l, exc i j → exc i l → j = l)
    (hperf : ∀ i j, exc i j → ∃ V : Subgroup K,
      V ≤ rankOne D.rootGroup i ⊔ rankOne D.rootGroup j ∧ ⁅V, V⁆ = V ∧
        ∀ p : ℕ, p.Prime → 5 ≤ p →
          p ∣ Nat.card ↥(rankOne D.rootGroup i ⊔ rankOne D.rootGroup j) → p ∣ Nat.card V)
    (hpair : ∀ i j, i ≠ j → D.cartan i j ≠ 0 → ¬ exc i j →
      D.cartan i j = -1 ∧ D.cartan j i = -1 ∧
        ∃ a b : k, ⁅x (Pi.single i 1) a, x (Pi.single j 1) b⁆ ≠ 1) :
    TwoLevi D exc where
  node i := by
    obtain ⟨ρ, hU, hL⟩ := hsl2 i
    exact Or.inr (not_dvd_card_rankOne_of_sl2 hk hx hU hL)
  pair i j hij hA _ _ := by
    by_cases hexc : exc i j
    · exact Or.inr hexc
    · obtain ⟨h1, h2, h3⟩ := hpair i j hij hA hexc
      exact Or.inl (commutator_rankOne_sup_eq_of_param hct hext hx hk hij h1 h2 h3)
  exc_symm := hsymm
  exc_unique := huniq
  exc_perfect := hperf

end Assembly

end CFSG.AGLEmbedding.ParabPrime

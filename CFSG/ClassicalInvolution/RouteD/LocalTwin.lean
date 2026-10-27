module

public import CFSG.ClassicalInvolution.RouteD.ConsistencyA
public import CFSG.ClassicalInvolution.RouteD.GenerationA
public import CFSG.ClassicalInvolution.ModelFacts.Models

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def LocalShapeT (p f a : ℕ) [Fact p.Prime] (tY : StatedLieTag) (nY : ℕ)
    (Ω : Set (Subgroup G)) (x : G) : Prop :=
  ∃ D : LieSystemData p f (locQuot Ω x) (locFamily Ω x), D.card = a + 1 ∧
    ∃ i₁ : Fin D.card, D.tag i₁ = tY ∧ D.rank i₁ = nY ∧
      ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2

@[expose] def compFundamental {X : Type} [Group X] {Φ : Set (Subgroup X)} (D : LieSystemData p f X Φ)
    (i : Fin D.card) : Set (Subgroup X) :=
  {K | ∃ R ∈ fundamentalSubgroups (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D, K = R.map (D.hom i)}

theorem compFundamental_subset_of_A1 {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) (i : Fin D.card) (ht : D.tag i = .PSL) (hr : D.rank i = 2) :
    compFundamental D i ⊆ {(D.hom i).range} := by
  have key : ∀ (t : StatedLieTag) (n e : ℕ) (hT : t = .PSL) (hN : n = 2)
      (hadm : StatedLieAdmissible t n p e) (φ : (modelUniv t n p e Fact.out).K →* X),
      {K | ∃ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, K = R.map φ} ⊆
        {φ.range} := by
    intro t n e hT hN hadm φ
    subst hT hN
    rintro K ⟨R, hR, rfl⟩
    have : R = ⊤ := CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups_eq_top_PSL_two p e
      Fact.out hadm R hR
    rw [this, Subgroup.map_top]
    rfl
  exact key _ _ _ ht hr (D.admissible i) (D.hom i)

theorem ncard_compFundamental_le {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) (i : Fin D.card) {tY : StatedLieTag} {nY : ℕ}
    (ht : D.tag i = tY) (hr : D.rank i = nY) (hY : tY ≠ .trialityD4)
    (hfin : Finite (modelUniv tY nY p f Fact.out).K) :
    (compFundamental D i).ncard ≤
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D).ncard := by
  have he : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h; exact absurd h hY
  have key : ∀ (t : StatedLieTag) (n e : ℕ) (hT : t = tY) (hN : n = nY) (hE : e = f)
      (φ : (modelUniv t n p e Fact.out).K →* X),
      {K | ∃ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, K = R.map φ}.ncard ≤
        (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D).ncard := by
    intro t n e hT hN hE φ
    subst hT hN hE
    have himg : {K | ∃ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
        K = R.map φ} =
        (fun R : Subgroup (modelUniv t n p e Fact.out).K => R.map φ) ''
          fundamentalSubgroups t (modelUniv t n p e Fact.out).D := by
      ext K
      constructor
      · rintro ⟨R, hR, rfl⟩
        exact ⟨R, hR, rfl⟩
      · rintro ⟨R, hR, rfl⟩
        exact ⟨R, hR, rfl⟩
    rw [himg]
    exact Set.ncard_image_le (Set.toFinite _)
  exact key _ _ _ ht hr he (D.hom i)

theorem LocalShapeT.ncard_locFamily_le [Finite G] {a : ℕ} {tY : StatedLieTag} {nY : ℕ}
    {Ω : Set (Subgroup G)} {x : G} (h : LocalShapeT p f a tY nY Ω x) (hY : tY ≠ .trialityD4)
    (hfin : Finite (modelUniv tY nY p f Fact.out).K) :
    (locFamily Ω x).ncard ≤
      a + (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D).ncard := by
  obtain ⟨D, hcard, i₁, ht, hr, hrest⟩ := h
  let c : {i : Fin D.card // i ≠ i₁} → Subgroup (locQuot Ω x) := fun i => (D.hom i.1).range
  have hΦ : locFamily Ω x ⊆ compFundamental D i₁ ∪ Set.range c := by
    intro K hK
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental K hK
    by_cases hi : i = i₁
    · subst hi
      exact Or.inl ⟨R, hR, rfl⟩
    · right
      have := compFundamental_subset_of_A1 D i (hrest i hi).1 (hrest i hi).2 ⟨R, hR, rfl⟩
      exact ⟨⟨i, hi⟩, this.symm⟩
  have hcr : (Set.range c).ncard ≤ a := by
    rw [← Set.image_univ]
    calc (c '' Set.univ).ncard ≤ (Set.univ : Set {i : Fin D.card // i ≠ i₁}).ncard :=
          Set.ncard_image_le (Set.toFinite _)
      _ = Nat.card {i : Fin D.card // i ≠ i₁} := Set.ncard_univ _
      _ = a := by
          rw [Nat.card_eq_fintype_card]
          simp [Fintype.card_subtype_compl, hcard]
  calc (locFamily Ω x).ncard ≤ (compFundamental D i₁ ∪ Set.range c).ncard :=
        Set.ncard_le_ncard hΦ (Set.toFinite _)
    _ ≤ (compFundamental D i₁).ncard + (Set.range c).ncard := Set.ncard_union_le _ _
    _ ≤ _ := by
        have := ncard_compFundamental_le D i₁ ht hr hY hfin
        omega

theorem LocalShapeA.toT {m : ℕ} {Ω : Set (Subgroup G)} {x : G} (h : LocalShapeA p f m Ω x) :
    LocalShapeT p f 1 .PSL (m + 1) Ω x := by
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := h
  refine ⟨D, hcard, i₁, ht₁, hr₁, fun i hi => ?_⟩
  have h0 := i₀.isLt
  have h1 := i₁.isLt
  have h2 := i.isLt
  have h3 := Fin.val_ne_of_ne hne
  have h4 := Fin.val_ne_of_ne hi
  have : i = i₀ := Fin.ext (by omega)
  subst this
  exact ⟨ht₀, hr₀⟩

section Model

variable {t : StatedLieTag} {K : Type} [Group K]

theorem conjSub_mem_fundamentalSubgroups {D : UniversalRootDatum K} {R : Subgroup K}
    (hR : R ∈ fundamentalSubgroups t D) (g : K) : conjSub g R ∈ fundamentalSubgroups t D := by
  obtain ⟨g₀, γ, hγ, rfl⟩ := hR
  exact ⟨g * g₀, γ, hγ, by rw [conjSub_mul]⟩

theorem eq_of_map_eq_of_perfect {A B : Type} [Group A] [Group B] (φ : A →* B)
    (hker : φ.ker ≤ Subgroup.center A) {R R' : Subgroup A} (hR : R ≤ ⁅R, R⁆) (hR' : R' ≤ ⁅R', R'⁆)
    (h : R.map φ = R'.map φ) : R = R' := by
  have key : ∀ R R' : Subgroup A, R.map φ = R'.map φ → R ≤ R' ⊔ φ.ker := by
    intro R R' h a ha
    have : a ∈ (R'.map φ).comap φ := by
      rw [← h]
      exact ⟨a, ha, rfl⟩
    rwa [Subgroup.comap_map_eq] at this
  exact le_antisymm (le_of_perfect_of_le_sup_center hker hR (key R R' h))
    (le_of_perfect_of_le_sup_center hker hR' (key R' R h.symm))

theorem map_perfect {A B : Type} [Group A] [Group B] (φ : A →* B) {R : Subgroup A}
    (hR : R ≤ ⁅R, R⁆) : R.map φ ≤ ⁅R.map φ, R.map φ⁆ := by
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_mono hR

theorem not_commutes_self_of_mem {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) {L : Subgroup G} (hL : L ∈ Ω) : ¬ Commutes L L := by
  obtain ⟨z, hz⟩ := hΩ.classical L hL
  exact not_commutes_self_of_isClassicalMember hz

end Model

structure ExtModelU (t tY : StatedLieTag) (T Y : LieUniversal) (a : ℕ) where
  Rθ : Subgroup T.K
  twin : Fin (a - 1) → Subgroup T.K
  Θ : Y.K →* T.K
  Rθ_mem : Rθ ∈ fundamentalSubgroups t T.D
  twin_mem : ∀ i, twin i ∈ fundamentalSubgroups t T.D
  Θ_ker : Θ.ker ≤ Subgroup.center Y.K
  Θ_mem : ∀ R ∈ fundamentalSubgroups tY Y.D, R.map Θ ∈ fundamentalSubgroups t T.D
  Θ_comm : ∀ R ∈ fundamentalSubgroups tY Y.D, Commutes (R.map Θ) Rθ
  twin_comm : ∀ i, Commutes (twin i) Rθ
  twin_comm_Θ : ∀ i, ∀ R ∈ fundamentalSubgroups tY Y.D, Commutes (twin i) (R.map Θ)
  twin_inj : Function.Injective twin
  perf_T : ∀ R ∈ fundamentalSubgroups t T.D, R ≤ ⁅R, R⁆
  perf_Y : ∀ R ∈ fundamentalSubgroups tY Y.D, R ≤ ⁅R, R⁆

abbrev ExtModel (p f : ℕ) [Fact p.Prime] (t : StatedLieTag) (n : ℕ) (tY : StatedLieTag)
    (nY a : ℕ) : Type :=
  ExtModelU t tY (modelUniv t n p f Fact.out) (modelUniv tY nY p f Fact.out) a

theorem exists_lieSystemData_of_fundamental {t : StatedLieTag} {n : ℕ} (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p f) {Ω : Set (Subgroup G)}
    (ψ : (modelUniv t n p f Fact.out).K →* G) (hsurj : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center _)
    (hne : (fundamentalSubgroups t (modelUniv t n p f Fact.out).D).Nonempty)
    (hΩ : ∀ L : Subgroup G, L ∈ Ω ↔
      ∃ R ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D, L = R.map ψ) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = t ∧ D.rank i = n := by
  refine ⟨{
    card := 1
    tag := fun _ => t
    rank := fun _ => n
    exp := fun _ => f
    hom := fun _ => ψ
    isFundTag := fun _ => hfund
    admissible := fun _ => hadm
    exp_eq := fun _ => Or.inl rfl
    ker_le_center := fun _ => hker
    commute := fun i j h => absurd (Subsingleton.elim i j) h
    generate := ?_
    fundamental := ?_
    meets := ?_ }, rfl, 0, rfl, rfl⟩
  · rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := hsurj x
    exact Subgroup.mem_iSup_of_mem (0 : Fin 1) ⟨y, rfl⟩
  · intro L hL
    obtain ⟨R, hR, rfl⟩ := (hΩ L).mp hL
    exact ⟨0, R, hR, rfl⟩
  · intro i
    obtain ⟨R, hR⟩ := hne
    exact ⟨R, hR, (hΩ _).mpr ⟨R, hR, rfl⟩⟩

section Core

variable [Finite G]

theorem commutes_map {A B : Type} [Group A] [Group B] (φ : A →* B) {R S : Subgroup A}
    (h : Commutes R S) : Commutes (R.map φ) (S.map φ) := by
  rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
  rw [← map_mul, ← map_mul, h r hr s hs]

omit [Finite G] in
theorem mem_centralizingMembers_of_commutes {Ω : Set (Subgroup G)} {x : G} {N L : Subgroup G}
    (hL : L ∈ Ω) (hx : x ∈ N) (h : Commutes L N) : L ∈ centralizingMembers Ω {x} :=
  ⟨hL, fun _ hy => Subgroup.mem_centralizer_singleton_iff.mpr (h _ hy _ hx)⟩

theorem routeD_core {t : StatedLieTag} {n : ℕ} {tY : StatedLieTag} {nY a : ℕ} (ha : 1 ≤ a)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p f)
    (hscT : FundamentalSingleClass t (modelUniv t n p f Fact.out).D)
    (hY : tY ≠ .trialityD4) (hfinY : Finite (modelUniv tY nY p f Fact.out).K)
    (M : ExtModel p f t n tY nY a) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀)
    (hconn : DeltaConnected Ω) {z : G} (hz : IsClassicalMember p f K₀ z)
    (hshape : LocalShapeT p f a tY nY Ω z) (hP1 : LocalOddCentral Ω {z})
    (ψ : (modelUniv t n p f Fact.out).K →* G) (hker : ψ.ker ≤ Subgroup.center _)
    (hΩψ : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D, R.map ψ ∈ Ω) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = t ∧ D.rank i = n := by
  classical
  set N₀ : Subgroup G := M.Rθ.map ψ with hN₀
  have hN₀Ω : N₀ ∈ Ω := hΩψ _ M.Rθ_mem
  obtain ⟨g₀, hg₀⟩ := hsingle N₀ hN₀Ω
  have hxN : g₀ * z * g₀⁻¹ ∈ N₀ := by
    rw [hg₀]
    exact conj_mem_conjSub hz.mem
  set x : G := g₀ * z * g₀⁻¹ with hx
  have hK₀z : K₀ ∈ centralizingMembers Ω {z} := ⟨hK₀, le_centralizer_of_isClassicalMember hz⟩
  have hN₀x : N₀ ∈ centralizingMembers Ω {x} := by
    rw [hx, centralizingMembers_conj hΩ.conjInvariant g₀ z]
    exact ⟨K₀, hK₀z, hg₀.symm⟩
  set ΘΩ : Set (Subgroup G) := (fun R => (R.map M.Θ).map ψ) ''
    fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D with hΘΩ
  set TW : Set (Subgroup G) := (fun i => (M.twin i).map ψ) '' Set.univ with hTW
  set 𝓡 : Set (Subgroup G) := TW ∪ ΘΩ with h𝓡
  have hmem : ∀ S ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D,
      Commutes S M.Rθ → S.map ψ ∈ centralizingMembers Ω {x} := fun S hS hc =>
    mem_centralizingMembers_of_commutes (hΩψ S hS) hxN (commutes_map ψ hc)
  have h𝓡sub : 𝓡 ⊆ centralizingMembers Ω {x} := by
    rintro _ (⟨i, -, rfl⟩ | ⟨R, hR, rfl⟩)
    · exact hmem _ (M.twin_mem i) (M.twin_comm i)
    · exact hmem _ (M.Θ_mem R hR) (M.Θ_comm R hR)
  have hN₀R : N₀ ∉ 𝓡 := by
    have hnc := not_commutes_self_of_mem hΩ hN₀Ω
    rintro (⟨i, -, hi⟩ | ⟨R, hR, hRN⟩)
    · have hi' : (M.twin i).map ψ = N₀ := hi
      refine hnc ?_
      have := commutes_map ψ (M.twin_comm i)
      rwa [hi'] at this
    · have hRN' : (R.map M.Θ).map ψ = N₀ := hRN
      refine hnc ?_
      have := commutes_map ψ (M.Θ_comm R hR)
      rwa [hRN'] at this
  have hdisj : Disjoint TW ΘΩ := by
    rw [Set.disjoint_left]
    rintro _ ⟨i, -, rfl⟩ ⟨R, hR, hRi⟩
    have hRi' : (R.map M.Θ).map ψ = (M.twin i).map ψ := hRi
    refine not_commutes_self_of_mem hΩ (hΩψ _ (M.twin_mem i)) ?_
    have := commutes_map ψ (M.twin_comm_Θ i R hR)
    rwa [hRi'] at this
  have hTWinj : Function.Injective (fun i : Fin (a - 1) => (M.twin i).map ψ) := by
    intro i j hij
    exact M.twin_inj (eq_of_map_eq_of_perfect ψ hker (M.perf_T _ (M.twin_mem i))
      (M.perf_T _ (M.twin_mem j)) hij)
  have hΘinj : Set.InjOn (fun R => (R.map M.Θ).map ψ)
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) := by
    intro R hR R' hR' h
    have h1 : R.map M.Θ = R'.map M.Θ :=
      eq_of_map_eq_of_perfect ψ hker (map_perfect M.Θ (M.perf_Y R hR))
        (map_perfect M.Θ (M.perf_Y R' hR')) h
    exact eq_of_map_eq_of_perfect M.Θ M.Θ_ker (M.perf_Y R hR) (M.perf_Y R' hR') h1
  have hTWcard : TW.ncard = a - 1 := by
    rw [hTW, Set.ncard_image_of_injective _ hTWinj, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hΘcard : ΘΩ.ncard =
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D).ncard := by
    rw [hΘΩ, hΘinj.ncard_image]
  have h𝓡card : 𝓡.ncard = (a - 1) +
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D).ncard := by
    rw [h𝓡, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hTWcard, hΘcard]
  have hcard : (centralizingMembers Ω {x}).ncard ≤ 1 + 𝓡.ncard := by
    rw [hx, ncard_centralizingMembers_conj hΩ.conjInvariant, ncard_centralizingMembers_eq hΩ hP1,
      h𝓡card]
    have := hshape.ncard_locFamily_le hY hfinY
    omega
  have hEq : centralizingMembers Ω {x} = insert N₀ 𝓡 :=
    centralizingMembers_eq_insert hN₀x h𝓡sub hN₀R hcard
  set 𝔖 : Set (Subgroup G) := {L | ∃ R ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D,
    L = R.map ψ} with h𝔖
  have hsub : 𝔖 ⊆ Ω := by
    rintro _ ⟨R, hR, rfl⟩
    exact hΩψ R hR
  have hne : 𝔖.Nonempty := ⟨N₀, M.Rθ, M.Rθ_mem, rfl⟩
  have hcl : ∀ N ∈ 𝔖, ∀ L ∈ Ω, L ≠ N → Commutes N L → L ∈ 𝔖 := by
    rintro N ⟨R, hR, rfl⟩ L hL hLN hcomm
    obtain ⟨h, hh⟩ := hscT M.Rθ M.Rθ_mem R hR
    have hNeq : R.map ψ = conjSub (ψ h) N₀ := by
      rw [hh, hN₀, conjSub_map]
    set L' := conjSub (ψ h)⁻¹ L with hL'
    have hL'Ω : L' ∈ Ω := hΩ.conjInvariant _ L hL
    have hLL' : L = conjSub (ψ h) L' := (conjSub_conjSub_inv _ L).symm
    have hL'N : L' ≠ N₀ := fun e => hLN (by rw [hNeq, hLL', e])
    have hcomm' : Commutes N₀ L' := by
      rw [hNeq, hLL'] at hcomm
      exact (commutes_conjSub_iff _).mp hcomm
    have hL'x : L' ∈ centralizingMembers Ω {x} :=
      mem_centralizingMembers_of_commutes hL'Ω hxN hcomm'.symm
    rw [hEq] at hL'x
    rcases hL'x with h1 | h1
    · exact absurd h1 hL'N
    · obtain ⟨S, hS, hSL'⟩ : ∃ S ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D,
          L' = S.map ψ := by
        rcases h1 with ⟨i, -, hi⟩ | ⟨R', hR', hR'L'⟩
        · exact ⟨M.twin i, M.twin_mem i, hi.symm⟩
        · exact ⟨R'.map M.Θ, M.Θ_mem R' hR', hR'L'.symm⟩
      refine ⟨conjSub h S, conjSub_mem_fundamentalSubgroups hS h, ?_⟩
      rw [hLL', hSL', conjSub_map]
  have hΩsub : Ω ⊆ 𝔖 := subset_of_adj_closed hconn hsub hne hcl
  refine exists_lieSystemData_of_fundamental hfund hadm ψ ?_ hker ⟨M.Rθ, M.Rθ_mem⟩
    (fun L => ⟨fun hL => hΩsub hL, fun hL => hsub hL⟩)
  refine MonoidHom.range_eq_top.mp (eq_top_iff.mpr ?_)
  calc (⊤ : Subgroup G) = ⨆ L ∈ Ω, L := hΩ.generated.symm
    _ ≤ ψ.range := iSup₂_le fun L hL => by
      obtain ⟨R, -, rfl⟩ := hΩsub hL
      exact Subgroup.map_le_range ψ R

end Core

end CFSG.ClassicalInvolution.RouteD

module

public import CFSG.ClassicalInvolution.RouteD.GenerationA
public import CFSG.ClassicalInvolution.RouteD.ConsistencyA
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCRecognition
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCModel

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  isHyperbolicPlane_stdPlane longBlock spEmbed)
open CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

section Shape

variable {G : Type} [Group G]

@[expose] def LocalShapeC (p f m : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (x : G) : Prop :=
  ∃ D : LieSystemData p f (locQuot Ω x) (locFamily Ω x), D.card = 2 ∧
    ∃ i₀ i₁ : Fin D.card, i₀ ≠ i₁ ∧ D.tag i₀ = .PSL ∧ D.rank i₀ = 2 ∧ D.tag i₁ = .PSp ∧
      D.rank i₁ = m

end Shape

section Sets

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def planeGroupSet (F : Type) [Field F] (m : ℕ) : Set (Subgroup (StatedSp m F)) :=
  {R | ∃ P, IsHyperbolicPlane P ∧ R = planeGroup P}

@[expose] def planeSet {n : ℕ} (ψ : StatedSp n (GaloisField p f) →* G) : Set (Subgroup G) :=
  {L | ∃ P, IsHyperbolicPlane P ∧ L = (planeGroup P).map ψ}

theorem fundamentalSubgroups_psp_eq {m : ℕ} (hadm : StatedLieAdmissible .PSp m p f) :
    fundamentalSubgroups .PSp (modelUniv .PSp m p f (Fact.out : p.Prime)).D =
      planeGroupSet (GaloisField p f) m := by
  ext R
  exact Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff hadm R

theorem ncard_fundamental_le_of_psp {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) (i : Fin D.card) (ht : D.tag i = .PSp) {m : ℕ}
    (hr : D.rank i = m) :
    {K : Subgroup X | ∃ R ∈ fundamentalSubgroups (D.tag i)
        (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D, K = R.map (D.hom i)}.ncard ≤
      (planeGroupSet (GaloisField p f) m).ncard := by
  have he : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h; exact absurd h (by decide)
  have key : ∀ (t : StatedLieTag) (n e : ℕ) (hT : t = .PSp) (hN : n = m) (hE : e = f)
      (φ : (modelUniv t n p e Fact.out).K →* X),
      StatedLieAdmissible t n p e →
      {K : Subgroup X | ∃ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
        K = R.map φ}.ncard ≤ (planeGroupSet (GaloisField p f) m).ncard := by
    intro t n e hT hN hE φ hA
    have hE' : f = e := hE.symm
    subst hT hN hE'
    have himg : {K : Subgroup X | ∃ R ∈ fundamentalSubgroups .PSp
        (modelUniv .PSp n p f Fact.out).D, K = R.map φ} =
        (fun R : Subgroup (StatedSp n (GaloisField p f)) => R.map φ) ''
          (planeGroupSet (GaloisField p f) n) := by
      rw [← fundamentalSubgroups_psp_eq hA]
      ext K
      constructor
      · rintro ⟨R, hR, rfl⟩
        exact ⟨R, hR, rfl⟩
      · rintro ⟨R, hR, rfl⟩
        exact ⟨R, hR, rfl⟩
    rw [himg]
    exact Set.ncard_image_le (Set.toFinite _)
  exact key _ _ _ ht hr he (D.hom i) (D.admissible i)

theorem LocalShapeC.ncard_locFamily_le {G : Type} [Group G] [Finite G] {m : ℕ}
    {Ω : Set (Subgroup G)} {x : G} (h : LocalShapeC p f m Ω x) :
    (locFamily Ω x).ncard ≤ 1 + (planeGroupSet (GaloisField p f) m).ncard := by
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := h
  let P : Fin D.card → Set (Subgroup (locQuot Ω x)) := fun i =>
    {K | ∃ R ∈ fundamentalSubgroups (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D, K = R.map (D.hom i)}
  have hΦ : locFamily Ω x ⊆ P i₀ ∪ P i₁ := by
    intro K hK
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental K hK
    have hi := i.isLt
    have hi₀ := i₀.isLt
    have hi₁ := i₁.isLt
    have hne' : i₀.val ≠ i₁.val := fun e => hne (Fin.ext e)
    have : i = i₀ ∨ i = i₁ := by
      rcases Nat.lt_or_ge i.val 1 with h1 | h1
      · by_cases h0 : i₀.val = 0
        · left; exact Fin.ext (by omega)
        · right; exact Fin.ext (by omega)
      · by_cases h0 : i₀.val = 1
        · left; exact Fin.ext (by omega)
        · right; exact Fin.ext (by omega)
    rcases this with rfl | rfl
    · exact Or.inl ⟨R, hR, rfl⟩
    · exact Or.inr ⟨R, hR, rfl⟩
  have h0 : (P i₀).ncard ≤ 1 :=
    (ncard_fundamental_le_of_psl D i₀ ht₀ (k := 1) hr₀ (by omega)).trans
      (longRootSet_two_ncard_le (F := GaloisField p f) (by omega))
  have h1 : (P i₁).ncard ≤ (planeGroupSet (GaloisField p f) m).ncard :=
    ncard_fundamental_le_of_psp D i₁ ht₁ hr₁
  calc (locFamily Ω x).ncard ≤ (P i₀ ∪ P i₁).ncard := Set.ncard_le_ncard hΦ (Set.toFinite _)
    _ ≤ (P i₀).ncard + (P i₁).ncard := Set.ncard_union_le _ _
    _ ≤ _ := by omega

end Sets

section Embed

variable {F : Type} [Field F]

noncomputable abbrev spEmbedLast (F : Type) [Field F] (m : ℕ) :
    StatedSp m F →* StatedSp (m + 1) F :=
  spEmbed (Fin.castSucc : Fin m → Fin (m + 1)) (Fin.castSucc_injective m)

theorem last_not_mem_range (m : ℕ) :
    (Sum.inl (Fin.last m) : Fin (m + 1) ⊕ Fin (m + 1)) ∉
      Set.range (Sum.map (Fin.castSucc : Fin m → Fin (m + 1)) Fin.castSucc) := by
  rintro ⟨a, ha⟩
  rcases a with a | a
  · simp only [Sum.map_inl, Sum.inl.injEq] at ha
    exact Fin.castSucc_lt_last a |>.ne ha
  · simp at ha

theorem injective_comp_spEmbedLast {G : Type} [Group G] (m : ℕ) {ψ : StatedSp (m + 1) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (StatedSp (m + 1) F)) :
    Function.Injective (ψ.comp (spEmbedLast F m)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hcen : spEmbedLast F m x ∈ Subgroup.center (StatedSp (m + 1) F) := hker hx
  have hsupp : spEmbedLast F m x ∈
      Models.SymplecticPairs.suppGroup (Set.range (Sum.map (Fin.castSucc : Fin m → Fin (m + 1))
        Fin.castSucc)) := by
    rw [← Models.SymplecticPairs.range_spEmbed (Fin.castSucc_injective m)]
    exact ⟨x, rfl⟩
  have h1 := Models.SymplecticPairs.eq_one_of_mem_center_of_mem_suppGroup hcen hsupp
    (last_not_mem_range m)
  exact Models.SymplecticPairs.spEmbed_injective (Fin.castSucc_injective m) (by rw [h1, map_one])

theorem exists_planeGroup_map_spEmbedLast {m : ℕ} (hm : 1 ≤ m) {R : Subgroup (StatedSp m F)}
    (hR : R ∈ planeGroupSet F m) :
    ∃ P, IsHyperbolicPlane P ∧ R.map (spEmbedLast F m) = planeGroup P := by
  obtain ⟨P', hP', rfl⟩ := hR
  obtain ⟨g, hg⟩ := Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock hP'
    (⟨0, by omega⟩ : Fin m)
  have hc : (spEmbedLast F m).comp (longBlock F m ⟨0, by omega⟩) =
      longBlock F (m + 1) (Fin.castSucc ⟨0, by omega⟩) :=
    MonoidHom.ext fun A =>
      Models.SymplecticPairs.spEmbed_longBlock (Fin.castSucc_injective m) _ A
  have h1 : (longBlock F m ⟨0, by omega⟩).range.map (spEmbedLast F m) =
      (longBlock F (m + 1) (Fin.castSucc ⟨0, by omega⟩)).range := by
    rw [← MonoidHom.range_comp, hc]
  refine (Models.SymplecticPairs.exists_conj_longBlock_iff (Fin.castSucc ⟨0, by omega⟩) _).1
    ⟨spEmbedLast F m g, ?_⟩
  rw [hg, map_map_conj, h1]

theorem commute_spEmbedLast_longBlock_last (m : ℕ) (x : StatedSp m F) (A : SL(2, F)) :
    Commute (spEmbedLast F m x) (longBlock F (m + 1) (Fin.last m) A) := by
  have hx : spEmbedLast F m x ∈ Models.SymplecticPairs.suppGroup
      (Set.range (Sum.map (Fin.castSucc : Fin m → Fin (m + 1)) Fin.castSucc)) := by
    rw [← Models.SymplecticPairs.range_spEmbed (Fin.castSucc_injective m)]
    exact ⟨x, rfl⟩
  have hy : longBlock F (m + 1) (Fin.last m) A ∈ Models.SymplecticPairs.suppGroup
      (Set.range (Sum.map (Fin.castSucc : Fin m → Fin (m + 1)) Fin.castSucc))ᶜ := by
    refine Models.SymplecticPairs.suppGroup_mono ?_ (Models.SymplecticPairs.isSupp_longBlock
      (K := F) (Fin.last m) A)
    intro a ha hmem
    obtain ⟨b, rfl⟩ := hmem
    rcases Models.SymplecticPairs.mem_coords.1 ha with h | h
    · rcases b with b | b
      · simp only [Sum.map_inl, Sum.inl.injEq] at h
        exact (Fin.castSucc_lt_last b).ne h
      · simp at h
    · rcases b with b | b
      · simp at h
      · simp only [Sum.map_inr, Sum.inr.injEq] at h
        exact (Fin.castSucc_lt_last b).ne h
  exact Models.SymplecticPairs.commute_suppGroup_compl hx hy

end Embed

section D11

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem typeC_centralizingMembers [Finite G] {m : ℕ} (hm : 2 ≤ m) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember p f K z)
    (hshape : LocalShapeC p f m Ω z) (hP1 : LocalOddCentral Ω {z})
    {ψ : StatedSp (m + 1) (GaloisField p f) →* G}
    (hker : ψ.ker ≤ Subgroup.center (StatedSp (m + 1) (GaloisField p f)))
    (hΩψ : ∀ P, IsHyperbolicPlane P → (planeGroup P).map ψ ∈ Ω) {g₀ : G}
    (hg₀ : (longBlock (GaloisField p f) (m + 1) (Fin.last m)).range.map ψ = conjSub g₀ K) :
    centralizingMembers Ω {g₀ * z * g₀⁻¹} =
      insert ((longBlock (GaloisField p f) (m + 1) (Fin.last m)).range.map ψ)
        ((fun R => (R.map (spEmbedLast (GaloisField p f) m)).map ψ) ''
          planeGroupSet (GaloisField p f) m) := by
  set F := GaloisField p f with hF
  set N := (longBlock F (m + 1) (Fin.last m)).range.map ψ with hNdef
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hNm : N ∈ centralizingMembers Ω {g₀ * z * g₀⁻¹} := by
    rw [centralizingMembers_conj hΩ.conjInvariant g₀ z]
    exact ⟨K, hKz, hg₀.symm⟩
  have hxN : g₀ * z * g₀⁻¹ ∈ N := by
    rw [hg₀]
    exact conj_mem_conjSub hz.mem
  have hmemΩ : ∀ R ∈ planeGroupSet F m, (R.map (spEmbedLast F m)).map ψ ∈ Ω := by
    intro R hR
    obtain ⟨P, hP, hRP⟩ := exists_planeGroup_map_spEmbedLast (by omega) hR
    rw [hRP]
    exact hΩψ P hP
  have hcomm : ∀ R ∈ planeGroupSet F m, Commutes ((R.map (spEmbedLast F m)).map ψ) N := by
    rintro R hR _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩ _ ⟨_, ⟨A, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (commute_spEmbedLast_longBlock_last m r A).eq
  have h𝓡 : (fun R => (R.map (spEmbedLast F m)).map ψ) '' planeGroupSet F m ⊆
      centralizingMembers Ω {g₀ * z * g₀⁻¹} := by
    rintro _ ⟨R, hR, rfl⟩
    refine ⟨hmemΩ R hR, fun y hy => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm R hR y hy _ hxN
  have hNR : N ∉ (fun R => (R.map (spEmbedLast F m)).map ψ) '' planeGroupSet F m := by
    rintro ⟨R, hR, hRN⟩
    have h1 := hcomm R hR
    have hRN' : (R.map (spEmbedLast F m)).map ψ = N := hRN
    rw [hRN'] at h1
    have h2' : Commutes K K := by
      rw [hg₀] at h1
      exact (commutes_conjSub_iff g₀).mp h1
    exact not_commutes_self_of_isClassicalMember hz h2'
  have hinj : Function.Injective
      (fun R : Subgroup (StatedSp m F) => (R.map (spEmbedLast F m)).map ψ) := by
    intro R R' h
    simp only [Subgroup.map_map] at h
    exact Subgroup.map_injective (injective_comp_spEmbedLast m hker) h
  have hcard : (centralizingMembers Ω {g₀ * z * g₀⁻¹}).ncard ≤
      1 + ((fun R => (R.map (spEmbedLast F m)).map ψ) '' planeGroupSet F m).ncard := by
    rw [Set.ncard_image_of_injective _ hinj, ncard_centralizingMembers_conj hΩ.conjInvariant,
      ncard_centralizingMembers_eq hΩ hP1]
    exact hshape.ncard_locFamily_le
  exact centralizingMembers_eq_insert hNm h𝓡 hNR hcard

end D11

section Closure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem exists_planeGroup_conj {F : Type} [Field F] {n : ℕ} (hn : 1 ≤ n) {P : Submodule F _}
    (hP : IsHyperbolicPlane P) (g : StatedSp n F) :
    ∃ P', IsHyperbolicPlane P' ∧
      (planeGroup P).map (MulAut.conj g).toMonoidHom = planeGroup P' := by
  obtain ⟨g', hg'⟩ := Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock hP
    (⟨0, by omega⟩ : Fin n)
  refine (Models.SymplecticPairs.exists_conj_longBlock_iff (⟨0, by omega⟩ : Fin n) _).1
    ⟨g * g', ?_⟩
  rw [hg', Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem typeC_closure [Finite G] {m : ℕ} (hm : 2 ≤ m) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember p f K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeC p f m Ω z)
    (hP1 : LocalOddCentral Ω {z}) {ψ : StatedSp (m + 1) (GaloisField p f) →* G}
    (hker : ψ.ker ≤ Subgroup.center (StatedSp (m + 1) (GaloisField p f)))
    (hΩψ : ∀ P, IsHyperbolicPlane P → (planeGroup P).map ψ ∈ Ω) :
    ∀ N ∈ planeSet ψ, ∀ L ∈ Ω, L ≠ N → Commutes N L → L ∈ planeSet ψ := by
  rintro N ⟨P₀, hP₀, rfl⟩ L hL hLN hcomm
  set F := GaloisField p f with hF
  set N₀ := (longBlock F (m + 1) (Fin.last m)).range.map ψ with hN₀
  have hN₀Ω : N₀ ∈ Ω := by
    have := hΩψ (stdPlane F (m + 1) (Fin.last m)) (isHyperbolicPlane_stdPlane _)
    rwa [Models.SymplecticPairs.planeGroup_stdPlane] at this
  obtain ⟨g₀, hg₀⟩ := hsingle _ hN₀Ω
  obtain ⟨g₁, hg₁⟩ := Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock hP₀ (Fin.last m)
  have hNeq : (planeGroup P₀).map ψ = conjSub (ψ g₁) N₀ := by
    rw [hg₁]
    exact map_map_conj ψ g₁ _
  rw [hNeq] at hLN hcomm
  set L' := conjSub (ψ g₁)⁻¹ L with hL'
  have hL'Ω : L' ∈ Ω := hΩ.conjInvariant _ L hL
  have hLL' : L = conjSub (ψ g₁) L' := (conjSub_conjSub_inv _ L).symm
  have hL'N : L' ≠ N₀ := fun e => hLN (by rw [hLL', e])
  have hcomm' : Commutes N₀ L' := by
    rw [hLL'] at hcomm
    exact (commutes_conjSub_iff _).mp hcomm
  have hxN : g₀ * z * g₀⁻¹ ∈ N₀ := by
    rw [hg₀]
    exact conj_mem_conjSub hz.mem
  have hL'x : L' ∈ centralizingMembers Ω {g₀ * z * g₀⁻¹} :=
    ⟨hL'Ω, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm' _ hxN y hy).symm⟩
  rw [typeC_centralizingMembers hm hΩ hK hz hshape hP1 hker hΩψ hg₀] at hL'x
  rcases hL'x with h | ⟨R, hR, hRL'⟩
  · exact absurd h hL'N
  · obtain ⟨P₂, hP₂, hRP⟩ := exists_planeGroup_map_spEmbedLast (by omega) hR
    obtain ⟨P₃, hP₃, hP₃eq⟩ := exists_planeGroup_conj (n := m + 1) (by omega) hP₂ g₁
    refine ⟨P₃, hP₃, ?_⟩
    have hRL'' : (planeGroup P₂).map ψ = L' := by
      rw [← hRP]
      exact hRL'
    rw [← hP₃eq, map_map_conj, hRL'', hLL']
    rfl

end Closure

section Closing

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem exists_lieSystemData_of_planeSet (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 2 ≤ n)
    {Ω : Set (Subgroup G)} (ψ : StatedSp n (GaloisField p f) →* G)
    (hsurj : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField p f)))
    (hΩ : ∀ L : Subgroup G, L ∈ Ω ↔ L ∈ planeSet ψ) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSp ∧ D.rank i = n := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hadm : StatedLieAdmissible .PSp n p f := by
    refine ⟨Fact.out, by omega, hn, ?_⟩
    intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  refine ⟨{
    card := 1
    tag := fun _ => .PSp
    rank := fun _ => n
    exp := fun _ => f
    hom := fun _ => ψ
    isFundTag := fun _ => trivial
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
    obtain ⟨P, hP, rfl⟩ := (hΩ L).mp hL
    exact ⟨0, planeGroup P, (Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff hadm _).2
      ⟨P, hP, rfl⟩, rfl⟩
  · intro i
    exact ⟨planeGroup (stdPlane (GaloisField p f) n ⟨0, by omega⟩),
      (Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff hadm _).2
        ⟨_, isHyperbolicPlane_stdPlane _, rfl⟩,
      (hΩ _).2 ⟨_, isHyperbolicPlane_stdPlane _, rfl⟩⟩

theorem routeD_typeC_of_chain [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {m : ℕ} (hm : 2 ≤ m)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeC p f m Ω z)
    (hP1 : LocalOddCentral Ω {z}) (U : Fin (m + 1) → Subgroup G) (hUn : U (Fin.last m) ∈ Ω)
    (hcomm : ∀ i j : Fin (m + 1), i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin (m + 1), i.val + 1 = j.val → j.val + 1 < m + 1 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j))
    (hsp : ∀ i j : Fin (m + 1), i.val + 1 = m + 1 → j.val + 2 = m + 1 →
      ∃ W, Models.SymplecticPairs.SymplecticBlockStandardPair (GaloisField p f) W (U i) (U j)) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSp ∧ D.rank i = m + 1 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hadm : StatedLieAdmissible .PSp (m + 1) p f := by
    refine ⟨Fact.out, by omega, by omega, ?_⟩
    intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  obtain ⟨ψ, hker, hrange, -, -, hblk⟩ := Models.SymplecticPairs.weakCT_symplectic_subgroup hadm
    (by omega) hp2 hF (by omega) U hcomm hpair hsp
  have hlast : (longBlock (GaloisField p f) (m + 1) (Fin.last m)).range.map ψ = U (Fin.last m) := by
    rw [Models.SymplecticPairs.range_longBlock_eq_rankOne (by show ¬ m + 1 < m + 1; omega)]
    exact hblk (Fin.last m)
  have hΩψ : ∀ P, IsHyperbolicPlane P → (planeGroup P).map ψ ∈ Ω := by
    intro P hP
    obtain ⟨g, hg⟩ := Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock hP (Fin.last m)
    rw [hg, map_map_conj, hlast]
    exact hΩ.conjInvariant _ _ hUn
  have hsub : planeSet ψ ⊆ Ω := by
    rintro _ ⟨P, hP, rfl⟩
    exact hΩψ P hP
  have hne : (planeSet ψ).Nonempty :=
    ⟨_, _, isHyperbolicPlane_stdPlane (Fin.last m), rfl⟩
  have hcl := typeC_closure hm hΩ hK hz hsingle hshape hP1 hker hΩψ
  have hΩsub : Ω ⊆ planeSet ψ := subset_of_adj_closed hconn hsub hne hcl
  refine exists_lieSystemData_of_planeSet hq (by omega) ψ ?_ hker
    (fun L => ⟨fun hL => hΩsub hL, fun hL => hsub hL⟩)
  refine MonoidHom.range_eq_top.mp (eq_top_iff.mpr ?_)
  calc (⊤ : Subgroup G) = ⨆ L ∈ Ω, L := hΩ.generated.symm
    _ ≤ ψ.range := iSup₂_le fun L hL => by
      obtain ⟨P, -, rfl⟩ := hΩsub hL
      exact Subgroup.map_le_range ψ _

end Closing


end CFSG.ClassicalInvolution.RouteD

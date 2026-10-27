module

public import CFSG.ClassicalInvolution.Q3.Q3EXD4FKind
public import CFSG.ClassicalInvolution.Q3.Q3EXD4FComp
public import CFSG.ClassicalInvolution.Q3.Q3EXD4Local
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourTwins

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.RouteD.Gaps (locMk)


structure D4Ctx3 (G : Type) [Group G] [Finite G] (K : Subgroup G) (z : G) (a : ℕ) : Prop where
  setup : RouteD3Setup K z
  o3 : LocalOddThreeFree3 (conjClass3 K) z
  loc : LocalShapeC3 a (CompData.model .POmegaPlus 4) (conjClass3 K) z

section Data

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {a : ℕ}

theorem exists_D4At3 (S : D4Ctx3 G K z a) {N : Subgroup G} (hN : N ∈ conjClass3 K) :
    ∃ w : G, IsClassicalMember3 N w ∧ LocalOddCentral (conjClass3 K) {w} ∧
      LocalOddThreeFree3 (conjClass3 K) w ∧
      ∃ (ι : Type) (_ : Finite ι)
        (D : LieSystemData3 ι (locQuot (conjClass3 K) w) (locFamily (conjClass3 K) w))
        (i₁ : ι), Nat.card ι = a + 1 ∧ D.kind i₁ = CompData.model .POmegaPlus 4 ∧
          ∀ i, i ≠ i₁ → D.kind i = CompData.sl23 := by
  have hΩ := S.setup.inClass
  obtain ⟨hex, hP1⟩ := S.setup.setup
  obtain ⟨g, hg⟩ := single_class3 K N hN
  have hw : IsClassicalMember3 N (g * z * g⁻¹) := by
    rw [hg]
    exact S.setup.cls.conj g
  have hP1' : LocalOddCentral (conjClass3 K) {g * z * g⁻¹} :=
    RouteD.Gaps.localOddCentral_conj hΩ.conjInvariant g z hP1
  have hO3' : LocalOddThreeFree3 (conjClass3 K) (g * z * g⁻¹) :=
    localOddThreeFree3_conj hΩ.conjInvariant g z S.o3
  obtain ⟨ι, hι, D, hcard, i₁, hk, hrest⟩ := S.loc
  obtain ⟨D', hD'⟩ := exists_lieSystemData3_conj hΩ.conjInvariant g z D
  exact ⟨_, hw, hP1', hO3', ι, hι, D', i₁, hcard, by rw [hD']; exact hk,
    fun i hi => by rw [hD']; exact hrest i hi⟩

theorem single_class_of_mem3 {N : Subgroup G} (hN : N ∈ conjClass3 K) :
    ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g N := by
  intro L hL
  obtain ⟨g₁, hg₁⟩ := single_class3 K L hL
  obtain ⟨g, hg⟩ := single_class3 K N hN
  exact ⟨g₁ * g⁻¹, by rw [conjSub_mul, hg, conjSub_inv_conjSub, hg₁]⟩

variable {Ω : Set (Subgroup G)} {ι : Type}

theorem outerSet_eq_compMembers3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {N : Subgroup G}
    {w : G} (hw : IsClassicalMember3 N w) (hN : N ∈ Ω) (hP1 : LocalOddCentral Ω {w})
    (hO3 : LocalOddThreeFree3 Ω w) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g N)
    (D : LieSystemData3 ι (locQuot Ω w) (locFamily Ω w)) {i₁ : ι}
    (hk : D.kind i₁ = CompData.model .POmegaPlus 4)
    (hrest : ∀ i, i ≠ i₁ → D.kind i = CompData.sl23) :
    outerSet Ω N = compMembers3 Ω w D i₁ := by
  have hMFZ := RouteD.Gaps.fundNoncentral 3
  have hfund : IsFundTag (.POmegaPlus : StatedLieTag) := trivial
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hcn : cnbhd Ω N = centralizingMembers Ω {w} := by
    ext L
    constructor
    · rintro ⟨hLΩ, h⟩
      exact (mem_centralizingMembers_iff3 hMFZ hΩ hex hw hN hP1 hO3 D hLΩ).mpr h
    · intro hL
      exact ⟨hL.1, (mem_centralizingMembers_iff3 hMFZ hΩ hex hw hN hP1 hO3 D hL.1).mp hL⟩
  ext L
  constructor
  · rintro ⟨hLc, hne⟩
    have hLw : L ∈ centralizingMembers Ω {w} := hcn ▸ hLc
    obtain ⟨j, hj, -⟩ := exists_unique_comp3 hΩ hex hP1 hO3 D hLw
    by_cases hji : j = i₁
    · subst hji
      exact hj
    · exfalso
      obtain ⟨T, hTmem⟩ := exists_mem_compMembers3 (D := D) j
      have hLT : L = T := eq_of_mem_compMembers_a13 hΩ hex hP1 hO3 (hrest j hji) hj hTmem
      have hu : Universal3 Ω w L :=
        universal3_of_a1comp hΩ hex hP1 hO3 D (hrest j hji) hj
      have hcl := closedNbhd_whole3 hΩ hw hsingle hLw.1 hLw hu
      have h1 := cnbhd_eq_of_closedNbhd_eq (v := (⟨L, hLw.1⟩ : ↥Ω)) (fun _ h => h.1) hcl
      exact hne (h1.trans hcn.symm)
  · intro hL
    have hLw := hL.1
    refine ⟨hcn ▸ hLw, fun heq => ?_⟩
    exact closedNbhd_ne_of_comp3 hfund hadm (by decide) (by decide) hΩ hex hw hN hP1 hO3 D hk hL
      hLw.1 ((cnbhd_eq_iff_closedNbhd_eq (u := ⟨L, hLw.1⟩) (v := ⟨N, hN⟩)).mp heq)

end Data

section Transitive

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {a : ℕ}
  {Ω : Set (Subgroup G)} {ι : Type}

theorem exists_lift_outerGen3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {N : Subgroup G} {w : G}
    (hw : IsClassicalMember3 N w) (hN : N ∈ Ω) (hP1 : LocalOddCentral Ω {w})
    (hO3 : LocalOddThreeFree3 Ω w) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g N)
    (D : LieSystemData3 ι (locQuot Ω w) (locFamily Ω w)) {i₁ : ι}
    (hk : D.kind i₁ = CompData.model .POmegaPlus 4)
    (hrest : ∀ i, i ≠ i₁ → D.kind i = CompData.sl23) (k : (D.kind i₁).G) :
    ∃ y : ↥(locLayer Ω w), (y : G) ∈ outerGen Ω N ∧ locMk Ω w y = D.hom i₁ k := by
  have hout := outerSet_eq_compMembers3 hΩ hex hw hN hP1 hO3 hsingle D hk hrest
  have hsc := singleClass_of_kind hk (trivial : IsFundTag (.POmegaPlus : StatedLieTag))
    ⟨Nat.prime_three, le_rfl, le_rfl⟩ (by decide) (by decide)
  let S : Subgroup (D.kind i₁).G :=
    Subgroup.comap (D.hom i₁) (Subgroup.map (locMk Ω w)
      ((outerGen Ω N).subgroupOf (locLayer Ω w)))
  have hgen := top_le_iSup_fund_of_kind hk
  have hS : ∀ R ∈ (D.kind i₁).fund, R ≤ S := by
    intro R hR k hk'
    obtain ⟨N', hN'⟩ := exists_corr_right3 hΩ D hsc hR
    have hN'out : N' ∈ outerSet Ω N := by
      rw [hout]
      exact ⟨hN'.1, hN'.2.2 ▸ Subgroup.map_le_range _ _⟩
    have hmem : D.hom i₁ k ∈ locImg Ω w N' := by
      rw [hN'.2.2]
      exact ⟨k, hk', rfl⟩
    obtain ⟨y, hy, hyk⟩ := hmem
    exact ⟨y, Subgroup.mem_subgroupOf.mpr (le_outerGen hN'out (Subgroup.mem_subgroupOf.mp hy)),
      hyk⟩
  have hkS : k ∈ S := (hgen.trans (iSup₂_le hS)) trivial
  obtain ⟨y, hy, hyk⟩ := hkS
  exact ⟨y, Subgroup.mem_subgroupOf.mp hy, hyk⟩

theorem exists_conj_of_mem_outerSet3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {N : Subgroup G}
    {w : G} (hw : IsClassicalMember3 N w) (hN : N ∈ Ω) (hP1 : LocalOddCentral Ω {w})
    (hO3 : LocalOddThreeFree3 Ω w) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g N)
    (D : LieSystemData3 ι (locQuot Ω w) (locFamily Ω w)) {i₁ : ι}
    (hk : D.kind i₁ = CompData.model .POmegaPlus 4)
    (hrest : ∀ i, i ≠ i₁ → D.kind i = CompData.sl23) {E E' : Subgroup G}
    (hE : E ∈ outerSet Ω N) (hE' : E' ∈ outerSet Ω N) :
    ∃ y ∈ outerGen Ω N, conjSub y E = E' := by
  have hout := outerSet_eq_compMembers3 hΩ hex hw hN hP1 hO3 hsingle D hk hrest
  rw [hout] at hE hE'
  have hsc := singleClass_of_kind hk (trivial : IsFundTag (.POmegaPlus : StatedLieTag))
    ⟨Nat.prime_three, le_rfl, le_rfl⟩ (by decide) (by decide)
  obtain ⟨R, hR⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hE
  obtain ⟨R', hR'⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hE'
  obtain ⟨g, hg⟩ := hsc R hR.2.1 R' hR'.2.1
  obtain ⟨y, hyY, hy⟩ := exists_lift_outerGen3 hΩ hex hw hN hP1 hO3 hsingle D hk hrest g
  refine ⟨y, hyY, ?_⟩
  have hyx : (y : G) ∈ Subgroup.centralizer ({w} : Set G) :=
    centralizingLayer_le_centralizer Ω {w} y.2
  have hconj : conjSub (y : G) E ∈ centralizingMembers Ω {w} := by
    refine ⟨hΩ.conjInvariant _ E hE.1.1, fun a ha => ?_⟩
    rw [mem_conjSub_iff] at ha
    have hx' := hE.1.2 ha
    have : a = (y : G) * ((y : G)⁻¹ * a * (y : G)) * (y : G)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyx hx') ((Subgroup.inv_mem _) hyx)
  have himg : locImg Ω w (conjSub (y : G) E) = locImg Ω w E' := by
    rw [Gaps.locImg_conjSub_layer, hR.2.2, hy, hR'.2.2, hg]
    unfold conjSub
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext a
    simp
  exact locImg_injOn3 hΩ hex hP1 hO3 hconj hE'.1 himg

theorem outerSet_nonempty3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {N : Subgroup G} {w : G}
    (hw : IsClassicalMember3 N w) (hN : N ∈ Ω) (hP1 : LocalOddCentral Ω {w})
    (hO3 : LocalOddThreeFree3 Ω w) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g N)
    (D : LieSystemData3 ι (locQuot Ω w) (locFamily Ω w)) {i₁ : ι}
    (hk : D.kind i₁ = CompData.model .POmegaPlus 4)
    (hrest : ∀ i, i ≠ i₁ → D.kind i = CompData.sl23) : (outerSet Ω N).Nonempty := by
  rw [outerSet_eq_compMembers3 hΩ hex hw hN hP1 hO3 hsingle D hk hrest]
  exact exists_mem_compMembers3 (D := D) i₁

theorem outerSet_nonempty_of_shape3 (S : D4Ctx3 G K z a) {N : Subgroup G}
    (hN : N ∈ conjClass3 K) : (outerSet (conjClass3 K) N).Nonempty := by
  obtain ⟨hex, -⟩ := S.setup.setup
  obtain ⟨w, hw, hP1, hO3, ι, -, D, i₁, -, hk, hrest⟩ := exists_D4At3 S hN
  exact outerSet_nonempty3 S.setup.inClass hex hw hN hP1 hO3 (single_class_of_mem3 hN) D hk hrest

theorem exists_conj_of_shape3 (S : D4Ctx3 G K z a) {N E E' : Subgroup G}
    (hN : N ∈ conjClass3 K) (hE : E ∈ outerSet (conjClass3 K) N)
    (hE' : E' ∈ outerSet (conjClass3 K) N) :
    ∃ y ∈ outerGen (conjClass3 K) N, conjSub y E = E' := by
  obtain ⟨hex, -⟩ := S.setup.setup
  obtain ⟨w, hw, hP1, hO3, ι, -, D, i₁, -, hk, hrest⟩ := exists_D4At3 S hN
  exact exists_conj_of_mem_outerSet3 S.setup.inClass hex hw hN hP1 hO3 (single_class_of_mem3 hN)
    D hk hrest hE hE'

theorem ncard_twins_of_shape3 (S : D4Ctx3 G K z a) {N : Subgroup G} (hN : N ∈ conjClass3 K) :
    {T : Subgroup G | T ∈ conjClass3 K ∧
      cnbhd (conjClass3 K) T = cnbhd (conjClass3 K) N}.ncard = a := by
  obtain ⟨hex, -⟩ := S.setup.setup
  obtain ⟨w, hw, hP1, hO3, ι, hι, D, i₁, hcard, hk, hrest⟩ := exists_D4At3 S hN
  obtain ⟨⟨s, hs, hsm⟩, -⟩ := exists_localData3 S.setup.inClass hex hw hN hP1 hO3
    (single_class_of_mem3 hN) D hcard hk hrest
  have hset : {T : Subgroup G | T ∈ conjClass3 K ∧
      cnbhd (conjClass3 K) T = cnbhd (conjClass3 K) N} =
        Subtype.val '' (s : Set ↥(conjClass3 K)) := by
    ext T
    constructor
    · rintro ⟨hT, h⟩
      refine ⟨⟨T, hT⟩, ?_, rfl⟩
      rw [Finset.mem_coe, hsm]
      exact (cnbhd_eq_iff_closedNbhd_eq (u := ⟨T, hT⟩) (v := ⟨N, hN⟩)).mp h
    · rintro ⟨u, hu, rfl⟩
      rw [Finset.mem_coe, hsm] at hu
      exact ⟨u.2, (cnbhd_eq_iff_closedNbhd_eq (u := u) (v := ⟨N, hN⟩)).mpr hu⟩
  rw [hset, Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset, hs]

end Transitive

section Twins

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem exists_three_twins3 (S : D4Ctx3 G K z 4) {N : Subgroup G}
    (hN : N ∈ conjClass3 K) :
    ∃ T₂ T₃ T₄ : Subgroup G, T₂ ≠ T₃ ∧ T₂ ≠ T₄ ∧ T₃ ≠ T₄ ∧ T₂ ≠ N ∧ T₃ ≠ N ∧ T₄ ≠ N ∧
      ∀ T, (T ∈ conjClass3 K ∧ cnbhd (conjClass3 K) T = cnbhd (conjClass3 K) N) ↔
        (T = N ∨ T = T₂ ∨ T = T₃ ∨ T = T₄) := by
  classical
  let 𝒯 : Set (Subgroup G) :=
    {T | T ∈ conjClass3 K ∧ cnbhd (conjClass3 K) T = cnbhd (conjClass3 K) N}
  have h𝒯 : 𝒯.ncard = 4 := ncard_twins_of_shape3 S hN
  have hN𝒯 : N ∈ 𝒯 := ⟨hN, rfl⟩
  have h3 : (𝒯 \ {N}).ncard = 3 := by
    rw [Set.ncard_sdiff_singleton_of_mem hN𝒯, h𝒯]
  obtain ⟨T₂, T₃, T₄, h23, h24, h34, hset⟩ := Set.ncard_eq_three.mp h3
  have hT : ∀ T, (T = T₂ ∨ T = T₃ ∨ T = T₄) → T ∈ 𝒯 ∧ T ≠ N := by
    intro T hT
    have : T ∈ 𝒯 \ {N} := by
      rw [hset]
      rcases hT with rfl | rfl | rfl <;> simp
    exact ⟨this.1, this.2⟩
  refine ⟨T₂, T₃, T₄, h23, h24, h34, (hT T₂ (Or.inl rfl)).2, (hT T₃ (Or.inr (Or.inl rfl))).2,
    (hT T₄ (Or.inr (Or.inr rfl))).2, fun T => ⟨fun hTm => ?_, fun h => ?_⟩⟩
  · by_cases hTN : T = N
    · exact Or.inl hTN
    · have : T ∈ 𝒯 \ {N} := ⟨hTm, hTN⟩
      rw [hset] at this
      simpa using Or.inr this
  · rcases h with rfl | h
    · exact hN𝒯
    · exact (hT T h).1


theorem commutes_outer_eq_twin3 (S : D4Ctx3 G K z 4) {N M L : Subgroup G}
    (hN : N ∈ conjClass3 K) (hM : M ∈ outerSet (conjClass3 K) N)
    (hL : L ∈ outerSet (conjClass3 K) M) (hLN : Commutes L N) :
    cnbhd (conjClass3 K) L = cnbhd (conjClass3 K) N := by
  classical
  set Ω := conjClass3 K with hΩdef
  have hΩ : InClass3 Ω := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  have hMΩ : M ∈ Ω := hM.1.1
  have hLΩ : L ∈ Ω := hL.1.1
  by_cases hLeqN : L = N
  · rw [hLeqN]
  obtain ⟨T₂, T₃, T₄, h23, h24, h34, h2N, h3N, h4N, hT⟩ := exists_three_twins3 S hN
  obtain ⟨w, hw, hP1, hO3, ι, hι, D, i₁, hcard, hk, hrest⟩ := exists_D4At3 S hMΩ
  obtain ⟨-, F, fadj, hCF, -, e, he⟩ := exists_localData3 hΩ hex hw hMΩ hP1 hO3
    (single_class_of_mem3 hMΩ) D hcard hk hrest
  have hNM : N ∈ outerSet Ω M := mem_outerSet_symm hN hM
  have hTmem : ∀ T, (T = T₂ ∨ T = T₃ ∨ T = T₄) → T ∈ Ω ∧ cnbhd Ω T = cnbhd Ω N := fun T h =>
    (hT T).mpr (Or.inr h)
  have hTout : ∀ T, (T = T₂ ∨ T = T₃ ∨ T = T₄) → T ∈ outerSet Ω M := fun T h =>
    twin_mem_outerSet (hTmem T h).1 (hTmem T h).2 hM
  let v : ∀ T, T ∈ outerSet Ω M → ↥(outerNbhd (commAdj Ω) (⟨M, hMΩ⟩ : ↥Ω)) := fun T hT' =>
    ⟨⟨T, hT'.1.1⟩, (mem_outerNbhd_iff hMΩ hT'.1.1).mpr hT'⟩
  have hcomm : ∀ T T', (T = N ∨ T = T₂ ∨ T = T₃ ∨ T = T₄) → (T' = N ∨ T' = T₂ ∨ T' = T₃ ∨ T' = T₄) →
      T ≠ T' → Commutes T T' := by
    intro T T' hT1 hT2 hne
    have hT1' := (hT T).mpr hT1
    have hT2' := (hT T').mpr hT2
    have : T ∈ cnbhd Ω T' := by
      rw [hT2'.2, ← hT1'.2]
      exact self_mem_cnbhd hT1'.1
    exact this.2.resolve_left hne
  have hadjF : ∀ (a b : ↥(outerNbhd (commAdj Ω) (⟨M, hMΩ⟩ : ↥Ω))), a ≠ b →
      (Commutes a.1.1 b.1.1 ↔ fadj (e a) (e b)) := fun a b hab => he a b hab
  set vN := v N hNM with hvN
  set v₂ := v T₂ (hTout T₂ (Or.inl rfl)) with hv₂
  set v₃ := v T₃ (hTout T₃ (Or.inr (Or.inl rfl))) with hv₃
  set v₄ := v T₄ (hTout T₄ (Or.inr (Or.inr rfl))) with hv₄
  set vL := v L hL with hvL
  have hne : ∀ {a b : ↥(outerNbhd (commAdj Ω) (⟨M, hMΩ⟩ : ↥Ω))}, a.1.1 ≠ b.1.1 → a ≠ b :=
    fun h hab => h (by rw [hab])
  have hf12 : fadj (e vN) (e v₂) := (hadjF vN v₂ (hne h2N.symm)).mp
    (hcomm N T₂ (Or.inl rfl) (Or.inr (Or.inl rfl)) h2N.symm)
  have hf13 : fadj (e vN) (e v₃) := (hadjF vN v₃ (hne h3N.symm)).mp
    (hcomm N T₃ (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) h3N.symm)
  have hf14 : fadj (e vN) (e v₄) := (hadjF vN v₄ (hne h4N.symm)).mp
    (hcomm N T₄ (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl))) h4N.symm)
  have hf23 : fadj (e v₂) (e v₃) := (hadjF v₂ v₃ (hne h23)).mp
    (hcomm T₂ T₃ (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) h23)
  have he12 : e vN ≠ e v₂ := fun h => h2N.symm (congrArg (fun a => a.1.1) (e.injective h))
  have he13 : e vN ≠ e v₃ := fun h => h3N.symm (congrArg (fun a => a.1.1) (e.injective h))
  have he23 : e v₂ ≠ e v₃ := fun h => h23 (congrArg (fun a => a.1.1) (e.injective h))
  obtain ⟨F₄, hF4₁, hF4₂, hF4₃, -, -, -, hF4⟩ := hCF (e vN) (e v₂) (e v₃) he12 he13 he23 hf12 hf13
    hf23
  have hv4 : e v₄ = F₄ := by
    rcases hF4 (e v₄) hf14 with h | h | h
    · exact absurd (e.injective h) (fun h' => h24 (congrArg (fun a => a.1.1) h').symm)
    · exact absurd (e.injective h) (fun h' => h34 (congrArg (fun a => a.1.1) h').symm)
    · exact h
  have hLN' : fadj (e vN) (e vL) := (hadjF vN vL (hne (fun h => hLeqN h.symm))).mp hLN.symm
  have hLcases := hF4 (e vL) hLN'
  have hLT : L = T₂ ∨ L = T₃ ∨ L = T₄ := by
    rcases hLcases with h | h | h
    · exact Or.inl (congrArg (fun a => a.1.1) (e.injective h))
    · exact Or.inr (Or.inl (congrArg (fun a => a.1.1) (e.injective h)))
    · exact Or.inr (Or.inr (congrArg (fun a => a.1.1) (e.injective (h.trans hv4.symm))))
  exact (hTmem L hLT).2

end Twins

end CFSG.ClassicalInvolution.Q3.Q3W.EX

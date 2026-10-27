module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Orthogonal

public section

namespace CFSG.Quasithin.LieOver

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank Module
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  (statedProjectiveSubspaceStabilizer statedProjectiveFlagStabilizer)
open scoped Pointwise

abbrev lkGL (r : ℕ) (K : Type) [Field K] (A : Type) [AddCommGroup A] [Module K A] : Type :=
  ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)

noncomputable abbrev lkQ {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] (r : ℕ)
    (qA : QuadraticForm K A) : Type :=
  orthElementaryGroup (quadTail r qA) ⧸ elemScalars (quadTail r qA)

noncomputable abbrev lkPi {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] (r : ℕ)
    (qA : QuadraticForm K A) (i : Fin r) : Subgroup (lkQ r qA) :=
  stabP (quadTail r qA) (tailFlag K A r ((i : ℕ) + 1))

noncomputable abbrev lkUbar {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] (r : ℕ)
    (qA : QuadraticForm K A) : Subgroup (lkQ r qA) :=
  ((tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA))).map
    (QuotientGroup.mk' (elemScalars (quadTail r qA)))

noncomputable abbrev lkBbar {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] (r : ℕ)
    (qA : QuadraticForm K A) : Subgroup (lkQ r qA) :=
  ((tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA))).map
    (QuotientGroup.mk' (elemScalars (quadTail r qA)))

section Tail

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

abbrev lkGen (qA : QuadraticForm K A) (a₀ : A) (M : Subgroup (lkGL r K A)) :
    Subgroup (lkGL r K A) :=
  Subgroup.closure ((tailBorel r qA : Set (lkGL r K A)) ∪
    tailWeylElt r qA a₀ '' {i | tailWeylElt r qA a₀ i ∈ M})

theorem lk_peel [FiniteDimensional K A] (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
    {M : Subgroup (lkGL r K A)} (hUM : tailUnipotent r qA ≤ M) :
    ∀ (ℓ : ℕ) (n : lkGL r K A) (hn : n ∈ tailTorusWeyl r qA a₀), n ∈ M →
      weylLengthB r ((tailTorusWeylNu r qA hani ha₀ ⟨n, hn⟩ : weylGroupB r) :
        (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = ℓ → n ∈ lkGen qA a₀ M := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro n hn _ hℓ
    have h1 := eq_one_of_weylLengthB_eq_zero (tailTorusWeylNu r qA hani ha₀ ⟨n, hn⟩).2 hℓ
    have hker : (⟨n, hn⟩ : tailTorusWeyl r qA a₀) ∈ (tailTorusWeylNu r qA hani ha₀).ker :=
      MonoidHom.mem_ker.2 (Subtype.ext h1)
    rw [tailTorusWeylNu_ker hani ha₀, Subgroup.mem_subgroupOf] at hker
    exact Subgroup.subset_closure (Or.inl (tailTorus_le_tailBorel hker))
  | succ ℓ ih =>
    intro n hn hnM hℓ
    set w := ((tailTorusWeylNu r qA hani ha₀ ⟨n, hn⟩ : weylGroupB r) :
      (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) with hw
    have hwW : w ∈ weylGroupB r := (tailTorusWeylNu r qA hani ha₀ ⟨n, hn⟩).2
    have hne : w ≠ 1 := by
      rintro h1
      rw [h1, weylLengthB_one] at hℓ
      omega
    obtain ⟨i, hi⟩ := exists_simpleRootB_neg hwW hne
    have hα := simpleRootB_mem_posRootsB (r := r) i
    have hXα : tailRootGroup r qA (simpleRootB r i) ≤ M :=
      (tailRootGroup_le_tailUnipotent hα).trans hUM
    have hXβ : tailRootGroup r qA (-(w⁻¹ (simpleRootB r i))) ≤ M :=
      (tailRootGroup_le_tailUnipotent hi).trans hUM
    have hmap := map_conj_tailRootGroup hani ha₀ ⟨n, hn⟩ (posRootsB_subset_rootsB hi)
    have hww : w (w⁻¹ (simpleRootB r i)) = simpleRootB r i := by
      rw [LinearEquiv.coe_inv]
      exact LinearEquiv.apply_symm_apply _ _
    rw [← hw, map_neg, hww] at hmap
    have hXneg : tailRootGroup r qA (-simpleRootB r i) ≤ M := by
      rw [← hmap]
      rintro _ ⟨y, hy, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem hnM (hXβ hy)) (inv_mem hnM)
    have hniM : tailWeylElt r qA a₀ i ∈ M := tailWeylElt_mem_of_le a₀ i hXα hXneg
    have hniH : tailWeylElt r qA a₀ i ∈ lkGen qA a₀ M :=
      Subgroup.subset_closure (Or.inr ⟨i, hniM, rfl⟩)
    have hn' : (tailWeylElt r qA a₀ i)⁻¹ * n ∈ tailTorusWeyl r qA a₀ :=
      mul_mem (inv_mem (tailWeylElt_mem_tailTorusWeyl a₀ i)) hn
    have hν : ((tailTorusWeylNu r qA hani ha₀ ⟨_, hn'⟩ : weylGroupB r) :
        (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = simpleReflB r i * w := by
      have he : (⟨(tailWeylElt r qA a₀ i)⁻¹ * n, hn'⟩ : tailTorusWeyl r qA a₀) =
          (⟨tailWeylElt r qA a₀ i, tailWeylElt_mem_tailTorusWeyl a₀ i⟩ :
            tailTorusWeyl r qA a₀)⁻¹ * ⟨n, hn⟩ := rfl
      rw [he, map_mul, map_inv, tailTorusWeylNu_tailWeylElt hani ha₀ i, Subgroup.coe_mul,
        Subgroup.coe_inv]
      congr 1
      rw [inv_eq_iff_mul_eq_one, simpleReflB_mul_self]
    have hlen := weylLengthB_simpleReflB_mul hwW hi
    rw [← hν, hℓ, Nat.add_sub_cancel] at hlen
    have := ih _ hn' (mul_mem (inv_mem hniM) hnM) hlen
    have he : n = tailWeylElt r qA a₀ i * ((tailWeylElt r qA a₀ i)⁻¹ * n) := by group
    rw [he]
    exact mul_mem hniH this

theorem lk_le_gen [FiniteDimensional K A] (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
    {M : Subgroup (lkGL r K A)} (hMG : M ≤ orthElementaryGroup (quadTail r qA))
    (hUM : tailUnipotent r qA ≤ M) : M ≤ lkGen qA a₀ M := by
  intro g hg
  obtain ⟨b₁, h₁, n, hn, b₂, h₂, rfl⟩ :=
    (orthogonal_geometry_tail_Bruhat_coverage hani ha₀ g).1 (hMG hg)
  have h₁' : b₁ ∈ (tailUnipotent r qA : Set (lkGL r K A)) *
      (tailTorus r qA : Set (lkGL r K A)) := by
    rw [← (tailBorel_eq_mul hani).2]
    exact h₁
  have h₂' : b₂ ∈ (tailTorus r qA : Set (lkGL r K A)) *
      (tailUnipotent r qA : Set (lkGL r K A)) := by
    rw [← (tailBorel_eq_mul hani).1]
    exact h₂
  obtain ⟨u₁, hu₁, t₁, ht₁, rfl⟩ := h₁'
  obtain ⟨t₂, ht₂, u₂, hu₂, rfl⟩ := h₂'
  have hnT : t₁ * n * t₂ ∈ tailTorusWeyl r qA a₀ :=
    mul_mem (mul_mem (tailTorus_le_tailTorusWeyl a₀ ht₁) hn) (tailTorus_le_tailTorusWeyl a₀ ht₂)
  have hnM : t₁ * n * t₂ ∈ M := by
    have he : t₁ * n * t₂ = u₁⁻¹ * (u₁ * t₁ * n * (t₂ * u₂)) * u₂⁻¹ := by group
    rw [he]
    exact mul_mem (mul_mem (inv_mem (hUM hu₁)) hg) (inv_mem (hUM hu₂))
  have hkey := lk_peel hani ha₀ hUM _ (t₁ * n * t₂) hnT hnM rfl
  have he2 : u₁ * t₁ * n * (t₂ * u₂) = u₁ * (t₁ * n * t₂) * u₂ := by group
  rw [he2]
  exact mul_mem (mul_mem (Subgroup.subset_closure (Or.inl ((tailUnipotent_le_tailBorel hani) hu₁)))
    hkey) (Subgroup.subset_closure (Or.inl ((tailUnipotent_le_tailBorel hani) hu₂)))

theorem lk_weyl_lift [FiniteDimensional K A] (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
    {M : Subgroup (lkGL r K A)} (hall : ∀ i : Fin r, tailWeylElt r qA a₀ i ∈ M) :
    ∀ w ∈ weylGroupB r, ∃ z : tailTorusWeyl r qA a₀, z.1 ∈ M ∧
      ((tailTorusWeylNu r qA hani ha₀ z : weylGroupB r) :
        (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = w := by
  intro w hw
  rw [← closure_simpleReflB (r := r)] at hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨⟨tailWeylElt r qA a₀ i, tailWeylElt_mem_tailTorusWeyl a₀ i⟩, hall i,
      congrArg Subtype.val (tailTorusWeylNu_tailWeylElt hani ha₀ i)⟩
  | one => exact ⟨1, M.one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨z₁, h1, e1⟩ := hx
    obtain ⟨z₂, h2, e2⟩ := hy
    refine ⟨z₁ * z₂, M.mul_mem h1 h2, ?_⟩
    rw [map_mul, Subgroup.coe_mul, e1, e2]
  | inv x _ hx =>
    obtain ⟨z, h1, e⟩ := hx
    refine ⟨z⁻¹, M.inv_mem h1, ?_⟩
    rw [map_inv, Subgroup.coe_inv, e]

theorem lk_all_gen [FiniteDimensional K A] (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
    (hr : 2 ≤ r) {M : Subgroup (lkGL r K A)} (hUM : tailUnipotent r qA ≤ M)
    (hall : ∀ i : Fin r, tailWeylElt r qA a₀ i ∈ M) :
    orthElementaryGroup (quadTail r qA) ≤ M := by
  have hW := lk_weyl_lift hani ha₀ hall
  have hσS : simpleRootB r ⟨r - 1, by omega⟩ ∈ shortRootsB r := by
    rw [simpleRootB_of_not_lt (show ¬ (r - 1 + 1 < r) by omega)]
    exact ⟨_, Or.inl rfl⟩
  have hσSr : simpleRootB r ⟨r - 1, by omega⟩ ∈ rootsB r := Or.inl hσS
  have hσSP : simpleRootB r ⟨r - 1, by omega⟩ ∈ posRootsB r := simpleRootB_mem_posRootsB _
  have hσL : simpleRootB r ⟨0, by omega⟩ ∈ OrthogonalSplit.roots r := by
    rw [simpleRootB_eq_simpleRoot (i := ⟨0, by omega⟩) (show 0 + 1 < r by omega)]
    exact OrthogonalSplit.posRoots_subset_roots
      (OrthogonalSplit.simpleRoot_mem_posRoots hr ⟨0, by omega⟩)
  have hσLr : simpleRootB r ⟨0, by omega⟩ ∈ rootsB r := Or.inr hσL
  have hσLP : simpleRootB r ⟨0, by omega⟩ ∈ posRootsB r := simpleRootB_mem_posRootsB _
  have hroot : ∀ γ ∈ rootsB r, tailRootGroup r qA γ ≤ M := by
    intro γ hγ
    rcases hγ with hs | hl
    · obtain ⟨w, hw, hwσ⟩ := exists_weylB_apply_eq_short (r := r) hσS hs
      obtain ⟨z, hzM, hzw⟩ := hW w hw
      have hmap := map_conj_tailRootGroup hani ha₀ z hσSr
      rw [hzw, hwσ] at hmap
      rw [← hmap]
      rintro _ ⟨y, hy, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem hzM ((tailRootGroup_le_tailUnipotent hσSP).trans hUM hy))
        (inv_mem hzM)
    · obtain ⟨w, hw, hwσ⟩ := exists_weylB_apply_eq_long (r := r) hσL hl
      obtain ⟨z, hzM, hzw⟩ := hW w hw
      have hmap := map_conj_tailRootGroup hani ha₀ z hσLr
      rw [hzw, hwσ] at hmap
      rw [← hmap]
      rintro _ ⟨y, hy, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem hzM ((tailRootGroup_le_tailUnipotent hσLP).trans hUM hy))
        (inv_mem hzM)
  have hsup : tailRootSupr r qA ≤ M := by
    unfold tailRootSupr
    exact iSup₂_le fun γ hγ => hroot γ hγ
  rw [(orthogonal_geometry_tail_root_generation hani ⟨a₀, ha₀⟩).1]
  exact hsup

theorem lk_cover_G [FiniteDimensional K A] (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
    (hr : 2 ≤ r) {M : Subgroup (lkGL r K A)} (hMG : M ≤ orthElementaryGroup (quadTail r qA))
    (hUM : tailUnipotent r qA ≤ M) (hne : M ≠ orthElementaryGroup (quadTail r qA)) :
    ∃ i : Fin r, M ≤ MulAction.stabilizer (lkGL r K A) (tailFlag K A r ((i : ℕ) + 1)) := by
  by_cases hall : ∀ i : Fin r, tailWeylElt r qA a₀ i ∈ M
  · exact absurd (le_antisymm hMG (lk_all_gen hani ha₀ hr hUM hall)) hne
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    have hsub : lkGen qA a₀ M ≤
        MulAction.stabilizer (lkGL r K A) (tailFlag K A r ((i : ℕ) + 1)) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ (hb | ⟨j, hj, rfl⟩)
      · exact Submodule.mem_stabilizer_submodule_iff_map_eq.2
          ((mem_tailBorel.1 hb).2 _ (by omega) (by have := i.isLt; omega))
      · refine MulAction.mem_stabilizer_iff.2 ((tailWeylElt_smul_tailFlag hani ha₀ i j).2 ?_)
        rintro rfl
        exact hi hj
    exact ⟨i, fun g hg => hsub (lk_le_gen hani ha₀ hMG hUM hg)⟩

theorem lk_borel_le (i : Fin r) : lkBbar r qA ≤ lkPi r qA i := by
  refine Subgroup.map_mono (fun x hx => ?_)
  rw [Subgroup.mem_subgroupOf] at hx
  exact mem_stabilizer_iff_map.2 ((mem_tailBorel.1 hx).2 _ (by omega)
    (by have := i.isLt; omega))

theorem lk_ubar_le_bbar [FiniteDimensional K A] (hani : qA.Anisotropic) :
    lkUbar r qA ≤ lkBbar r qA :=
  Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.2 (tailUnipotent_le_tailBorel hani (Subgroup.mem_subgroupOf.1 hx))

theorem lk_anti [FiniteDimensional K A] (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
    {i j : Fin r} (h : lkPi r qA i ≤ lkPi r qA j) : i = j := by
  by_contra hij
  have hfix : tailWeylElt r qA a₀ j • tailFlag K A r ((i : ℕ) + 1) =
      tailFlag K A r ((i : ℕ) + 1) :=
    (tailWeylElt_smul_tailFlag hani ha₀ i j).2 (Ne.symm hij)
  have hx1 : QuotientGroup.mk' (elemScalars (quadTail r qA))
      ⟨tailWeylElt r qA a₀ j, tailWeylElt_mem a₀ j⟩ ∈ lkPi r qA i :=
    Subgroup.mem_map_of_mem _ (mem_stabilizer_iff_map.2
      (Submodule.mem_stabilizer_submodule_iff_map_eq.1 (MulAction.mem_stabilizer_iff.2 hfix)))
  have hx2 := h hx1
  have hfixj := mem_stabP_iff.1 hx2 ⟨tailWeylElt r qA a₀ j, tailWeylElt_mem a₀ j⟩ rfl
  have hsmj : tailWeylElt r qA a₀ j • tailFlag K A r ((j : ℕ) + 1) =
      tailFlag K A r ((j : ℕ) + 1) :=
    MulAction.mem_stabilizer_iff.1 (Submodule.mem_stabilizer_submodule_iff_map_eq.2 hfixj)
  exact (tailWeylElt_smul_tailFlag hani ha₀ j j).1 hsmj rfl

theorem lk_cover_Q [FiniteDimensional K A] (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
    (hr : 2 ≤ r) (A' : Subgroup (lkQ r qA)) (hU : lkUbar r qA ≤ A') (hA : A' ≠ ⊤) :
    ∃ i : Fin r, A' ≤ lkPi r qA i := by
  set X : Subgroup (orthElementaryGroup (quadTail r qA)) :=
    A'.comap (QuotientGroup.mk' (elemScalars (quadTail r qA))) with hX
  set M : Subgroup (lkGL r K A) := X.map (orthElementaryGroup (quadTail r qA)).subtype with hM
  have hMG : M ≤ orthElementaryGroup (quadTail r qA) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hUM : tailUnipotent r qA ≤ M := by
    intro u hu
    have huG : u ∈ orthElementaryGroup (quadTail r qA) := tailUnipotent_le hu
    refine ⟨⟨u, huG⟩, ?_, rfl⟩
    show QuotientGroup.mk' (elemScalars (quadTail r qA)) ⟨u, huG⟩ ∈ A'
    apply hU
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hu)
  have hMne : M ≠ orthElementaryGroup (quadTail r qA) := by
    intro hME
    apply hA
    rw [eq_top_iff]
    intro a _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    have hx : (x : lkGL r K A) ∈ M := by
      rw [hME]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := Subtype.ext hyx
    rw [hyx'] at hy
    exact hy
  obtain ⟨i, hi⟩ := lk_cover_G hani ha₀ hr hMG hUM hMne
  refine ⟨i, fun a ha => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  have hxX : x ∈ X := ha
  have hxM : (x : lkGL r K A) ∈ M := Subgroup.mem_map_of_mem _ hxX
  have hfix := Submodule.mem_stabilizer_submodule_iff_map_eq.1 (hi hxM)
  exact Subgroup.mem_map_of_mem _ (mem_stabilizer_iff_map.2 hfix)

theorem lk_coatom_Q [FiniteDimensional K A] (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
    (hr : 2 ≤ r) (i : Fin r) : IsCoatom (lkPi r qA i) := by
  unfold IsCoatom
  refine ⟨fun htop => ?_, fun X hX => ?_⟩
  · have hmem : QuotientGroup.mk' (elemScalars (quadTail r qA))
        ⟨tailWeylElt r qA a₀ i, tailWeylElt_mem a₀ i⟩ ∈ lkPi r qA i := by
      rw [htop]
      exact Subgroup.mem_top _
    have hfix := mem_stabP_iff.1 hmem ⟨tailWeylElt r qA a₀ i, tailWeylElt_mem a₀ i⟩ rfl
    have hsm : tailWeylElt r qA a₀ i • tailFlag K A r ((i : ℕ) + 1) =
        tailFlag K A r ((i : ℕ) + 1) :=
      MulAction.mem_stabilizer_iff.1 (Submodule.mem_stabilizer_submodule_iff_map_eq.2 hfix)
    exact (tailWeylElt_smul_tailFlag hani ha₀ i i).1 hsm rfl
  · by_contra hne
    have hBle : lkBbar r qA ≤ X := (lk_borel_le i).trans hX.le
    have hUle : lkUbar r qA ≤ X := (lk_ubar_le_bbar hani).trans hBle
    obtain ⟨j, hj⟩ := lk_cover_Q hani ha₀ hr X hUle hne
    have hij : lkPi r qA i ≤ lkPi r qA j := hX.le.trans hj
    have hij' : i = j := lk_anti hani ha₀ hij
    subst hij'
    exact hX.2 hj

end Tail

theorem lk_isCoatom_map {G H : Type} [Group G] [Group H] (e : G ≃* H) {X : Subgroup G} :
    IsCoatom (X.map (e : G →* H)) ↔ IsCoatom X :=
  OrderIso.isCoatom_iff e.mapSubgroup X

section Quotient

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

theorem lk_cover_sylow [FiniteDimensional K A] (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
    (hr : 2 ≤ r) [Finite (lkQ r qA)]
    (S₁ S₀ : Sylow 2 (lkQ r qA))
    (hS₁ : (S₁ : Subgroup (lkQ r qA)) = lkUbar r qA)
    (hN₁ : Subgroup.normalizer ((lkUbar r qA : Subgroup (lkQ r qA)) : Set (lkQ r qA)) =
      lkBbar r qA)
    (hS₀ : Subgroup.normalizer ((S₀ : Subgroup (lkQ r qA)) : Set (lkQ r qA)) = lkBbar r qA)
    (hcoat : ∀ M : Subgroup (lkQ r qA), IsCoatom M → lkBbar r qA ≤ M →
      ∃ j : Fin r, M = lkPi r qA j)
    (A₀ : Subgroup (lkQ r qA)) (hS : (S₀ : Subgroup (lkQ r qA)) ≤ A₀) (hA : A₀ ≠ ⊤) :
    ∃ j : Fin r, A₀ ≤ lkPi r qA j := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (lkQ r qA) S₁ S₀
  set f : lkQ r qA →* lkQ r qA := (MulAut.conj g).toMonoidHom with hf
  have hcoe : ((S₀ : Subgroup (lkQ r qA)) : Set (lkQ r qA)) =
      MulAut.conj g '' ((S₁ : Subgroup (lkQ r qA)) : Set (lkQ r qA)) := by
    rw [← hg]
    exact Sylow.coe_smul
  have hfS : (lkUbar r qA).map f = (S₀ : Subgroup (lkQ r qA)) := by
    rw [← hS₁]
    apply SetLike.ext'
    rw [Subgroup.coe_map, hcoe]
    rfl
  have hbij : Function.Bijective f := (MulAut.conj g).bijective
  have hsurj : Function.Surjective f := (MulAut.conj g).surjective
  have hBf : (lkBbar r qA).map f = lkBbar r qA := by
    have h1 := Subgroup.map_normalizer_eq_of_bijective (lkUbar r qA) hbij
    rw [hN₁, hfS, hS₀] at h1
    exact h1
  have hAcomap : lkUbar r qA ≤ A₀.comap f := by
    rw [← Subgroup.map_le_iff_le_comap, hfS]
    exact hS
  have hA₁ : A₀.comap f ≠ ⊤ := by
    intro htop
    apply hA
    rw [← Subgroup.map_comap_eq_self_of_surjective hsurj A₀, htop,
      Subgroup.map_top_of_surjective _ hsurj]
  obtain ⟨i, hi⟩ := lk_cover_Q hani ha₀ hr (A₀.comap f) hAcomap hA₁
  have hA₀le : A₀ ≤ (lkPi r qA i).map f := by
    calc A₀ = (A₀.comap f).map f := (Subgroup.map_comap_eq_self_of_surjective hsurj A₀).symm
      _ ≤ (lkPi r qA i).map f := Subgroup.map_mono hi
  have hcoatM : IsCoatom ((lkPi r qA i).map f) :=
    (lk_isCoatom_map (MulAut.conj g : lkQ r qA ≃* lkQ r qA)).2 (lk_coatom_Q hani ha₀ hr i)
  have hBM : lkBbar r qA ≤ (lkPi r qA i).map f := by
    rw [← hBf]
    exact Subgroup.map_mono (lk_borel_le i)
  obtain ⟨j, hj⟩ := hcoat _ hcoatM hBM
  exact ⟨j, hj ▸ hA₀le⟩

end Quotient

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem lk_model {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type} [AddCommGroup A]
    [Module K A] {r : ℕ} {qA : QuadraticForm K A} {Q : QuadraticForm K (ι → K)}
    {Q0 : (ι → K) → K} (ψ : (quadTail r qA).IsometryEquiv Q) (hQ : ⇑Q = Q0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {F : Fin r → Submodule K (ι → K)}
    (hF : ∀ i, F i = (tailFlag K A r ((i : ℕ) + 1)).map ψ.toLinearMap)
    (hr : 3 ≤ r) (hani : qA.Anisotropic) (hreg : (polarBilin qA).Nondegenerate)
    (hm : finrank K A = 1 ∨ finrank K A = 2) :
    (∀ i : Fin r, IsCoatom (statedProjectiveSubspaceStabilizer Q0 (F i))) ∧
    ∀ S : Sylow 2 (StatedProj (StatedOmega Q0)),
      statedProjectiveFlagStabilizer Q0 F =
          Subgroup.normalizer ((S : Subgroup (StatedProj (StatedOmega Q0))) :
            Set (StatedProj (StatedOmega Q0))) →
        ∀ X : Subgroup (StatedProj (StatedOmega Q0)),
          (S : Subgroup (StatedProj (StatedOmega Q0))) ≤ X → X ≠ ⊤ →
            ∃ i : Fin r, X ≤ statedProjectiveSubspaceStabilizer Q0 (F i) := by
  have hr2 : 2 ≤ r := by omega
  have hpos : 0 < finrank K A := by rcases hm with h | h <;> omega
  haveI : FiniteDimensional K A := Module.finite_of_finrank_pos hpos
  haveI : Nontrivial A := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨a₀, ha₀⟩ := exists_ne (0 : A)
  have hBI := borelInterface_of_tailIsometry (p := 2) ψ hQ hE hr hani hreg hm hF
  obtain ⟨-, -, -, hcl4, -⟩ := hBI
  haveI : Finite A := Module.finite_of_finite K
  haveI : Finite (lkGL r K A) := Finite.of_injective
    (fun g : lkGL r K A => (g : ((Fin r ⊕ Fin r → K) × A) → (Fin r ⊕ Fin r → K) × A))
    DFunLike.coe_injective
  haveI : Finite (orthElementaryGroup (quadTail r qA)) := inferInstance
  haveI : Finite (lkQ r qA) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  obtain ⟨S₁, hS₁⟩ :=
    (orthogonal_geometry_tail_Sylow_flag_normalizer (p := 2) hr hani hreg hm).2.2.1
  have hN₁ := (orthogonal_geometry_tail_Sylow_flag_normalizer (p := 2) hr hani hreg hm).2.2.2.1
  have hPhiPi : ∀ i : Fin r, (statedProjectiveSubspaceStabilizer Q0 (F i)).map
      (tailProjEquiv ψ hQ hE).toMonoidHom = lkPi r qA i := by
    intro i
    rw [tailProjEquiv_subspaceStabilizer ψ hQ hE, hF i, map_symm_map_isometry]
  have hPhiB : (statedProjectiveFlagStabilizer Q0 F).map (tailProjEquiv ψ hQ hE).toMonoidHom =
      lkBbar r qA := by
    have hFψ : (fun i => (F i).map ψ.symm.toLinearMap) = stdFlag K A r :=
      funext fun i => by
        rw [hF i, map_symm_map_isometry]
        try rfl
    rw [tailProjEquiv_flagStabilizer ψ hQ hE, hFψ]
    show stabFlagP r qA (stdFlag K A r) = ((tailBorel r qA).subgroupOf
      (orthElementaryGroup (quadTail r qA))).map (QuotientGroup.mk' (elemScalars (quadTail r qA)))
    rw [stabFlagP, tailBorel_subgroupOf_eq]
  have hcoat : ∀ M : Subgroup (lkQ r qA), IsCoatom M → lkBbar r qA ≤ M →
      ∃ j : Fin r, M = lkPi r qA j := by
    intro M hM hBM
    have hM' : IsCoatom (M.map (tailProjEquiv ψ hQ hE).symm.toMonoidHom) :=
      (lk_isCoatom_map (tailProjEquiv ψ hQ hE).symm).2 hM
    have hle : statedProjectiveFlagStabilizer Q0 F ≤
        M.map (tailProjEquiv ψ hQ hE).symm.toMonoidHom := by
      intro x hx
      refine ⟨(tailProjEquiv ψ hQ hE) x, hBM ?_, (tailProjEquiv ψ hQ hE).symm_apply_apply x⟩
      rw [← hPhiB]
      exact Subgroup.mem_map_of_mem _ hx
    obtain ⟨j, hj⟩ := hcl4 _ hM' hle
    refine ⟨j, ?_⟩
    have h2 : M = (statedProjectiveSubspaceStabilizer Q0 (F j)).map
        (tailProjEquiv ψ hQ hE).toMonoidHom := by
      rw [← hj, Subgroup.map_map]
      have hid : (tailProjEquiv ψ hQ hE).toMonoidHom.comp
          (tailProjEquiv ψ hQ hE).symm.toMonoidHom = MonoidHom.id _ := by
        ext x
        simp
      rw [hid, Subgroup.map_id]
    rw [h2, hPhiPi j]
  refine ⟨fun i => ?_, fun S hSN X hSX hX => ?_⟩
  · have h1 : IsCoatom ((statedProjectiveSubspaceStabilizer Q0 (F i)).map
        (tailProjEquiv ψ hQ hE).toMonoidHom) := by
      rw [hPhiPi i]
      exact lk_coatom_Q hani ha₀ hr2 i
    exact (lk_isCoatom_map (tailProjEquiv ψ hQ hE)).1 h1
  · let S₀ : Sylow 2 (lkQ r qA) :=
      S.mapSurjective (f := (tailProjEquiv ψ hQ hE).toMonoidHom)
        (tailProjEquiv ψ hQ hE).surjective
    have hS₀coe : (S₀ : Subgroup (lkQ r qA)) =
        (S : Subgroup (StatedProj (StatedOmega Q0))).map (tailProjEquiv ψ hQ hE).toMonoidHom :=
      rfl
    have hS₀N : Subgroup.normalizer ((S₀ : Subgroup (lkQ r qA)) : Set (lkQ r qA)) =
        lkBbar r qA := by
      rw [hS₀coe, ← Subgroup.map_normalizer_eq_of_bijective (S : Subgroup _)
        (f := (tailProjEquiv ψ hQ hE).toMonoidHom) (tailProjEquiv ψ hQ hE).bijective, ← hSN, hPhiB]
    have hSX' : (S₀ : Subgroup (lkQ r qA)) ≤ X.map (tailProjEquiv ψ hQ hE).toMonoidHom := by
      rw [hS₀coe]
      exact Subgroup.map_mono hSX
    have hX' : X.map (tailProjEquiv ψ hQ hE).toMonoidHom ≠ ⊤ := by
      intro h
      apply hX
      rw [eq_top_iff]
      intro x _
      have hx : (tailProjEquiv ψ hQ hE) x ∈ X.map (tailProjEquiv ψ hQ hE).toMonoidHom := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := hx
      have hyx' : y = x := (tailProjEquiv ψ hQ hE).injective hyx
      rw [hyx'] at hy
      exact hy
    obtain ⟨j, hj⟩ := lk_cover_sylow hani ha₀ hr2 S₁ S₀ hS₁ hN₁ hS₀N hcoat _ hSX' hX'
    refine ⟨j, ?_⟩
    have h3 : X.map (tailProjEquiv ψ hQ hE).toMonoidHom ≤
        (statedProjectiveSubspaceStabilizer Q0 (F j)).map (tailProjEquiv ψ hQ hE).toMonoidHom := by
      rw [hPhiPi j]
      exact hj
    exact (Subgroup.map_le_map_iff_of_injective (f := (tailProjEquiv ψ hQ hE).toMonoidHom)
      (tailProjEquiv ψ hQ hE).injective).1 h3

theorem lk_minus {n : ℕ} {b c : K} (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (∀ i : Fin (n - 1), IsCoatom (statedProjectiveSubspaceStabilizer (StatedQuadMinus n K b c)
      (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i))) ∧
    ∀ S : Sylow 2 (lfMinusModel n K b c),
      statedProjectiveFlagStabilizer (StatedQuadMinus n K b c)
          (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2)) =
        Subgroup.normalizer ((S : Subgroup (lfMinusModel n K b c)) :
          Set (lfMinusModel n K b c)) →
      ∀ X : Subgroup (lfMinusModel n K b c), (S : Subgroup (lfMinusModel n K b c)) ≤ X →
        X ≠ ⊤ → ∃ i : Fin (n - 1), X ≤ statedProjectiveSubspaceStabilizer
          (StatedQuadMinus n K b c) (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i) :=
  lk_model (minusTailIsometry n K b c) (coe_quadMinus n K b c)
    (commutator_orthogonalGroup_quadMinus hn hirr)
    (tailModelFlag_eq_map (minusTailIsometry n K b c) fun _ => rfl) (by omega)
    (anisotropic_minusTailForm hirr) (nondegenerate_minusTailForm hirr)
    (Or.inr finrank_fin_two_fun)

end Model


theorem pOmegaMinusCover_holds : POmegaMinusCover := by
  intro n K _ _ _ b c hn hirr S hS A hSA hA
  exact (lk_minus hn hirr).2 S hS A hSA hA

theorem pOmegaMinusCoatom_holds : POmegaMinusCoatom := by
  intro n K _ _ _ b c hn hirr i
  exact covBy_top_iff.2 ((lk_minus hn hirr).1 i)

end CFSG.Quasithin.LieOver

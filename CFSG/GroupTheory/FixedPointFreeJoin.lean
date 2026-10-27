module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG

open scoped commutatorElement

theorem commutator_mem_of_mem_closure {G : Type*} [Group G] {Z : Subgroup G} {k : G}
    {S : Set G} (hS : ∀ s ∈ S, s ∈ Subgroup.normalizer (Z : Set G))
    (h : ∀ s ∈ S, ⁅k, s⁆ ∈ Z) :
    ∀ x ∈ Subgroup.closure S, ⁅k, x⁆ ∈ Z := by
  let T : Subgroup G :=
    { carrier := {x : G | x ∈ Subgroup.normalizer (Z : Set G) ∧ ⁅k, x⁆ ∈ Z}
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      mul_mem' := by
        rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
        refine ⟨Subgroup.mul_mem _ hxN hyN, ?_⟩
        have hconj : x * ⁅k, y⁆ * x⁻¹ ∈ Z :=
          (Subgroup.mem_normalizer_iff.mp hxN (⁅k, y⁆)).mp hy
        have hformula : ⁅k, x * y⁆ = ⁅k, x⁆ * (x * ⁅k, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [hformula]
        exact Z.mul_mem hx hconj
      inv_mem' := by
        rintro x ⟨hxN, hx⟩
        have hxinvN : x⁻¹ ∈ Subgroup.normalizer (Z : Set G) := Subgroup.inv_mem _ hxN
        refine ⟨hxinvN, ?_⟩
        have hconj : x⁻¹ * (⁅k, x⁆)⁻¹ * x ∈ Z := by
          simpa using
            (Subgroup.mem_normalizer_iff.mp hxinvN (⁅k, x⁆)⁻¹).mp (Z.inv_mem hx)
        have hformula : ⁅k, x⁻¹⁆ = x⁻¹ * (⁅k, x⁆)⁻¹ * x := by
          simp only [commutatorElement_def]
          group
        rw [hformula]
        exact hconj }
  have hST : S ⊆ T := fun s hs => ⟨hS s hs, h s hs⟩
  exact fun x hx => ((Subgroup.closure_le T).mpr hST hx).2

private lemma le_normalizer_of_commutator_self {G : Type*} [Group G] {A V : Subgroup G}
    (hVA : V ≤ A) (h : ⁅A, A⁆ ≤ V) : A ≤ Subgroup.normalizer (V : Set G) := by
  intro a ha
  have hva : ∀ v ∈ V, ⁅a, v⁆ ∈ V := fun v hv =>
    Subgroup.commutator_le.mp h a ha v (hVA hv)
  have hva' : ∀ v ∈ V, ⁅a⁻¹, v⁆ ∈ V := fun v hv =>
    Subgroup.commutator_le.mp h a⁻¹ (A.inv_mem ha) v (hVA hv)
  have hconj_a : ∀ v ∈ V, a * v * a⁻¹ ∈ V := by
    intro v hv
    have hformula : a * v * a⁻¹ = ⁅a, v⁆ * v := by
      simp only [commutatorElement_def]
      group
    rw [hformula]
    exact V.mul_mem (hva v hv) hv
  have hconj_ainv : ∀ v ∈ V, a⁻¹ * v * a ∈ V := by
    intro v hv
    have hformula : a⁻¹ * v * a = ⁅a⁻¹, v⁆ * v := by
      simp only [commutatorElement_def]
      group
    rw [hformula]
    exact V.mul_mem (hva' v hv) hv
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    exact hconj_a v hv
  · intro hv
    have hmem : a⁻¹ * (a * v * a⁻¹) * a ∈ V := hconj_ainv (a * v * a⁻¹) hv
    have hformula : a⁻¹ * (a * v * a⁻¹) * a = v := by group
    rwa [hformula] at hmem

private def commutatorNormalizerSubgroup {G : Type*} [Group G] (B V : Subgroup G)
    (hVnorm : B ≤ Subgroup.normalizer (V : Set G)) : Subgroup G where
  carrier := {x : G | x ∈ B ∧ ∀ y ∈ B, ⁅x, y⁆ ∈ V}
  one_mem' := ⟨B.one_mem, fun y _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxB, hx⟩ ⟨hyB, hy⟩
    refine ⟨B.mul_mem hxB hyB, ?_⟩
    intro z hz
    have hconj : x * ⁅y, z⁆ * x⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hVnorm hxB) (⁅y, z⁆)).mp (hy z hz)
    have hformula : ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hformula]
    exact V.mul_mem hconj (hx z hz)
  inv_mem' := by
    rintro x ⟨hxB, hx⟩
    have hxinvN : x⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.inv_mem _ (hVnorm hxB)
    refine ⟨B.inv_mem hxB, ?_⟩
    intro z hz
    have hconj : x⁻¹ * (⁅x, z⁆)⁻¹ * x ∈ V := by
      simpa using
        (Subgroup.mem_normalizer_iff.mp hxinvN (⁅x, z⁆)⁻¹).mp (V.inv_mem (hx z hz))
    have hformula : ⁅x⁻¹, z⁆ = x⁻¹ * (⁅x, z⁆)⁻¹ * x := by
      simp only [commutatorElement_def]
      group
    rw [hformula]
    exact hconj

private lemma family_le_commutatorNormalizerSubgroup {G : Type*} [Group G] {B V : Subgroup G}
    {𝒮 : Set (Subgroup G)}
    (hBcl : B = Subgroup.closure (⋃ A : {A : Subgroup G // A ∈ 𝒮}, (A.1 : Set G)))
    (h : ∀ A ∈ 𝒮, ∀ B' ∈ 𝒮, ⁅A, B'⁆ ≤ V)
    (hVnorm : B ≤ Subgroup.normalizer (V : Set G)) :
    ∀ A : {A : Subgroup G // A ∈ 𝒮},
      A.1 ≤ commutatorNormalizerSubgroup B V hVnorm := by
  intro A a ha
  have haB : a ∈ B := by
    rw [hBcl]
    exact Subgroup.subset_closure (Set.mem_iUnion_of_mem A ha)
  refine ⟨haB, ?_⟩
  intro y hy
  rw [hBcl] at hy
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
      obtain ⟨A', hzA'⟩ := Set.mem_iUnion.mp hz
      exact Subgroup.commutator_le.mp (h A.1 A.2 A'.1 A'.2) a ha z hzA'
  | one => simp
  | mul z w hz hw ihz ihw =>
      have hzB : z ∈ B := by rw [hBcl]; exact hz
      have hconj : z * ⁅a, w⁆ * z⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hVnorm hzB) (⁅a, w⁆)).mp ihw
      have hformula : ⁅a, z * w⁆ = ⁅a, z⁆ * (z * ⁅a, w⁆ * z⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [hformula]
      exact V.mul_mem ihz hconj
  | inv z hz ih =>
      have hzB : z ∈ B := by rw [hBcl]; exact hz
      have hzN : z⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
        Subgroup.inv_mem _ (hVnorm hzB)
      have hconj : z⁻¹ * (⁅a, z⁆)⁻¹ * z ∈ V := by
        simpa using
          (Subgroup.mem_normalizer_iff.mp hzN (⁅a, z⁆)⁻¹).mp (V.inv_mem ih)
      have hformula : ⁅a, z⁻¹⁆ = z⁻¹ * (⁅a, z⁆)⁻¹ * z := by
        simp only [commutatorElement_def]
        group
      rwa [hformula]

theorem commutator_iSup_le {G : Type*} [Group G] {V : Subgroup G} {𝒮 : Set (Subgroup G)}
    (hV : ∀ A ∈ 𝒮, V ≤ A) (h : ∀ A ∈ 𝒮, ∀ B ∈ 𝒮, ⁅A, B⁆ ≤ V) :
    ⁅(⨆ A ∈ 𝒮, A), (⨆ A ∈ 𝒮, A)⁆ ≤ V := by
  let 𝒮' := {A : Subgroup G // A ∈ 𝒮}
  let B : Subgroup G := Subgroup.closure (⋃ A : 𝒮', (A.1 : Set G))
  have hB : B = ⨆ A : 𝒮', A.1 := by
    rw [show B = Subgroup.closure (⋃ A : 𝒮', (A.1 : Set G)) from rfl,
      Subgroup.iSup_eq_closure]
  have hBcl : B = Subgroup.closure (⋃ A : 𝒮', (A.1 : Set G)) := by
    rw [hB, Subgroup.iSup_eq_closure]
  have hVnorm : B ≤ Subgroup.normalizer (V : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    obtain ⟨A, hxA⟩ := Set.mem_iUnion.mp hx
    exact le_normalizer_of_commutator_self (hV A.1 A.2) (h A.1 A.2 A.1 A.2) hxA
  have hAC := family_le_commutatorNormalizerSubgroup hBcl h hVnorm
  have hBC : B ≤ commutatorNormalizerSubgroup B V hVnorm := by
    calc
      B = Subgroup.closure (⋃ A : 𝒮', (A.1 : Set G)) := hBcl
      _ ≤ commutatorNormalizerSubgroup B V hVnorm := by
        refine (Subgroup.closure_le _).mpr ?_
        intro x hx
        obtain ⟨A, hxA⟩ := Set.mem_iUnion.mp hx
        exact hAC A hxA
  have hcommB : ⁅B, B⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact (hBC hx).2 y hy
  have hcomm : ⁅(⨆ A : 𝒮', A.1), (⨆ A : 𝒮', A.1)⁆ ≤ V := by
    rwa [hB] at hcommB
  simpa only [iSup_subtype'] using hcomm

private lemma subgroupOf_map_normalizerMonoidHom {G : Type*} [Group G] {X W : Subgroup G}
    {k : G} (hkX : k ∈ Subgroup.normalizer (X : Set G))
    (hkW : k ∈ Subgroup.normalizer (W : Set G)) :
    (W.subgroupOf X).map
      ((Subgroup.normalizerMonoidHom X ⟨k, hkX⟩ : MulAut X) : X →* X) =
      W.subgroupOf X := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hkW (w : G)).mp hw
  · intro hx
    have hmemX : k⁻¹ * (x : G) * k ∈ X := by
      simpa using
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (X : Set G)).inv_mem hkX)
          (x : G)).mp x.2
    have hmemW : k⁻¹ * (x : G) * k ∈ W := by
      simpa using
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (W : Set G)).inv_mem hkW)
          (x : G)).mp hx
    refine ⟨⟨k⁻¹ * (x : G) * k, hmemX⟩, hmemW, ?_⟩
    apply Subtype.ext
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
    group

private noncomputable def conjQuotient {G : Type*} [Group G] {X W : Subgroup G}
    [hN : (W.subgroupOf X).Normal] {k : G}
    (hkX : k ∈ Subgroup.normalizer (X : Set G))
    (hkW : k ∈ Subgroup.normalizer (W : Set G)) :
    MulAut (X ⧸ W.subgroupOf X) :=
  QuotientGroup.congr (W.subgroupOf X) (W.subgroupOf X)
    (Subgroup.normalizerMonoidHom X ⟨k, hkX⟩)
    (subgroupOf_map_normalizerMonoidHom hkX hkW)

private theorem conjQuotient_mk {G : Type*} [Group G] {X W : Subgroup G}
    [hN : (W.subgroupOf X).Normal] {k : G}
    (hkX : k ∈ Subgroup.normalizer (X : Set G))
    (hkW : k ∈ Subgroup.normalizer (W : Set G)) (x : X) :
    conjQuotient hkX hkW (QuotientGroup.mk x) =
      QuotientGroup.mk (Subgroup.normalizerMonoidHom X ⟨k, hkX⟩ x) := by
  unfold conjQuotient
  exact QuotientGroup.congr_mk (W.subgroupOf X) (W.subgroupOf X)
    (Subgroup.normalizerMonoidHom X ⟨k, hkX⟩)
    (subgroupOf_map_normalizerMonoidHom hkX hkW) x

private theorem conjQuotient_mk' {G : Type*} [Group G] {X W : Subgroup G}
    [hN : (W.subgroupOf X).Normal] {k : G}
    (hkX : k ∈ Subgroup.normalizer (X : Set G))
    (hkW : k ∈ Subgroup.normalizer (W : Set G)) (x : X) :
    conjQuotient hkX hkW (QuotientGroup.mk' (W.subgroupOf X) x) =
      QuotientGroup.mk' (W.subgroupOf X) (Subgroup.normalizerMonoidHom X ⟨k, hkX⟩ x) := by
  simpa only [QuotientGroup.coe_mk'] using conjQuotient_mk hkX hkW x

private noncomputable def conjCommutator {G : Type*} [Group G] {X W : Subgroup G}
    [hN : (W.subgroupOf X).Normal] {k : G}
    (hkX : k ∈ Subgroup.normalizer (X : Set G))
    (hkW : k ∈ Subgroup.normalizer (W : Set G))
    (q : X ⧸ W.subgroupOf X) : X ⧸ W.subgroupOf X :=
  q * (conjQuotient hkX hkW q)⁻¹

private theorem conjCommutator_mk {G : Type*} [Group G] {X W : Subgroup G}
    [hN : (W.subgroupOf X).Normal] {k : G}
    (hkX : k ∈ Subgroup.normalizer (X : Set G))
    (hkW : k ∈ Subgroup.normalizer (W : Set G)) (x : X) :
    conjCommutator hkX hkW (QuotientGroup.mk x) =
      QuotientGroup.mk (x * (Subgroup.normalizerMonoidHom X ⟨k, hkX⟩ x)⁻¹) := by
  unfold conjCommutator
  rw [conjQuotient_mk]
  change QuotientGroup.mk' (W.subgroupOf X) x *
      (QuotientGroup.mk' (W.subgroupOf X)
        (Subgroup.normalizerMonoidHom X ⟨k, hkX⟩ x))⁻¹ =
    QuotientGroup.mk' (W.subgroupOf X)
      (x * (Subgroup.normalizerMonoidHom X ⟨k, hkX⟩ x)⁻¹)
  rw [← map_inv, ← map_mul]

private theorem conjCommutator_mul {G : Type*} [Group G] {X W : Subgroup G}
    [hN : (W.subgroupOf X).Normal] [IsMulCommutative (X ⧸ W.subgroupOf X)]
    {k : G} (hkX : k ∈ Subgroup.normalizer (X : Set G))
    (hkW : k ∈ Subgroup.normalizer (W : Set G))
    (q r : X ⧸ W.subgroupOf X) :
    conjCommutator hkX hkW (q * r) =
      conjCommutator hkX hkW q * conjCommutator hkX hkW r := by
  unfold conjCommutator
  rw [map_mul, mul_inv_rev]
  ac_rfl

private lemma conjCommutator_one {G : Type*} [Group G] {X W : Subgroup G}
    [hN : (W.subgroupOf X).Normal] {k : G}
    (hkX : k ∈ Subgroup.normalizer (X : Set G))
    (hkW : k ∈ Subgroup.normalizer (W : Set G)) :
    conjCommutator hkX hkW (1 : X ⧸ W.subgroupOf X) = 1 := by
  simp [conjCommutator, conjQuotient]

private lemma conjCommutator_inv {G : Type*} [Group G] {X W : Subgroup G}
    [hN : (W.subgroupOf X).Normal] [IsMulCommutative (X ⧸ W.subgroupOf X)]
    {k : G} (hkX : k ∈ Subgroup.normalizer (X : Set G))
    (hkW : k ∈ Subgroup.normalizer (W : Set G)) (q : X ⧸ W.subgroupOf X) :
    conjCommutator hkX hkW q⁻¹ = (conjCommutator hkX hkW q)⁻¹ := by
  have h1 : conjCommutator hkX hkW q * conjCommutator hkX hkW q⁻¹ = 1 := by
    rw [← conjCommutator_mul, mul_inv_cancel, conjCommutator_one]
  calc
    conjCommutator hkX hkW q⁻¹ = (conjCommutator hkX hkW q)⁻¹ *
        (conjCommutator hkX hkW q * conjCommutator hkX hkW q⁻¹) := by group
    _ = (conjCommutator hkX hkW q)⁻¹ := by rw [h1, mul_one]

private lemma conjCommutator_injective {G : Type*} [Group G] {E Z : Subgroup G}
    [hN : (Z.subgroupOf E).Normal] [IsMulCommutative (E ⧸ Z.subgroupOf E)]
    {k : G} (hkE : k ∈ Subgroup.normalizer (E : Set G))
    (hkZ : k ∈ Subgroup.normalizer (Z : Set G))
    (hfree : ∀ x ∈ E, k * x * k⁻¹ * x⁻¹ ∈ Z → x ∈ Z) :
    Function.Injective
      (conjCommutator hkE hkZ : E ⧸ Z.subgroupOf E → E ⧸ Z.subgroupOf E) := by
  intro q r hqr
  induction q using QuotientGroup.induction_on with
  | H x =>
    induction r using QuotientGroup.induction_on with
    | H y =>
      have hc_mul := conjCommutator_mul (X := E) (W := Z) hkE hkZ
      have h1 : conjCommutator (X := E) (W := Z) hkE hkZ
          ((QuotientGroup.mk x * (QuotientGroup.mk y)⁻¹ :
            E ⧸ Z.subgroupOf E)) = 1 := by
        rw [hc_mul, hqr, conjCommutator_inv]
        group
      have h2 : (QuotientGroup.mk x * (QuotientGroup.mk y)⁻¹ :
          E ⧸ Z.subgroupOf E) = QuotientGroup.mk (x * y⁻¹) := by
        change QuotientGroup.mk' _ x * (QuotientGroup.mk' _ y)⁻¹ =
          QuotientGroup.mk' _ (x * y⁻¹)
        rw [← map_inv, ← map_mul]
      rw [h2, conjCommutator_mk] at h1
      have hzZ : (x * y⁻¹ : E) ∈ Z.subgroupOf E := by
        have hmemZ : (x * y⁻¹ * (Subgroup.normalizerMonoidHom E ⟨k, hkE⟩
            (x * y⁻¹))⁻¹ : E) ∈ Z.subgroupOf E :=
          (QuotientGroup.eq_one_iff _).mp h1
        have hcommZ : k * ((x * y⁻¹ : E) : G) * k⁻¹ *
            ((x * y⁻¹ : E) : G)⁻¹ ∈ Z := by
          have hinv := Z.inv_mem hmemZ
          simpa [Subgroup.normalizerMonoidHom_apply_apply_coe, mul_assoc] using hinv
        exact hfree (x * y⁻¹) (E.mul_mem x.2 (E.inv_mem y.2)) hcommZ
      exact (QuotientGroup.eq_iff_div_mem).mpr (by simpa [div_eq_mul_inv] using hzZ)

private noncomputable def conjCommutatorHom {G : Type*} [Group G] {X W : Subgroup G}
    [hN : (W.subgroupOf X).Normal] [IsMulCommutative (X ⧸ W.subgroupOf X)]
    {k : G} (hkX : k ∈ Subgroup.normalizer (X : Set G))
    (hkW : k ∈ Subgroup.normalizer (W : Set G)) :
    X ⧸ W.subgroupOf X →* X ⧸ W.subgroupOf X where
  toFun := conjCommutator hkX hkW
  map_one' := conjCommutator_one hkX hkW
  map_mul' := conjCommutator_mul hkX hkW

private lemma mem_of_map_mem_of_injective_of_mapsTo {Q : Type*} [Group Q] [Finite Q]
    {c : Q →* Q} (hc : Function.Injective c) {P : Subgroup Q} (hP : P.map c ≤ P)
    {q : Q} (hq : c q ∈ P) : q ∈ P := by
  have hcard : Nat.card (P.map c) = Nat.card P := Subgroup.card_map_of_injective hc
  have heq : P.map c = P :=
    Subgroup.eq_of_le_of_card_ge hP (le_of_eq hcard.symm)
  rw [← heq] at hq
  obtain ⟨p, hp, hpc⟩ := Subgroup.mem_map.mp hq
  rwa [hc hpc] at hp

private lemma conjCommutator_maps_image_section {G : Type*} [Group G] {E Z V : Subgroup G}
    [hN : (Z.subgroupOf E).Normal] [IsMulCommutative (E ⧸ Z.subgroupOf E)]
    {k : G} (hkE : k ∈ Subgroup.normalizer (E : Set G))
    (hkZ : k ∈ Subgroup.normalizer (Z : Set G))
    (hkV : k ∈ Subgroup.normalizer (V : Set G)) :
    ((V.subgroupOf E).map (QuotientGroup.mk' (Z.subgroupOf E))).map
        (conjCommutatorHom hkE hkZ) ≤
      (V.subgroupOf E).map (QuotientGroup.mk' (Z.subgroupOf E)) := by
  rw [Subgroup.map_le_iff_le_comap]
  intro q hq
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hq
  change conjCommutator hkE hkZ (QuotientGroup.mk' (Z.subgroupOf E) v) ∈
    (V.subgroupOf E).map (QuotientGroup.mk' (Z.subgroupOf E))
  rw [show conjCommutator hkE hkZ (QuotientGroup.mk' (Z.subgroupOf E) v) =
      QuotientGroup.mk' (Z.subgroupOf E)
        (v * (Subgroup.normalizerMonoidHom E ⟨k, hkE⟩ v)⁻¹) by
    change conjCommutator hkE hkZ (QuotientGroup.mk v) = _
    rw [conjCommutator_mk]
    simp only [QuotientGroup.coe_mk']]
  refine Subgroup.mem_map_of_mem _ ?_
  have hkv : k * (v : G) * k⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp hkV (v : G)).mp hv
  have hmem : ((v * (Subgroup.normalizerMonoidHom E ⟨k, hkE⟩ v)⁻¹ : E) : G) ∈ V := by
    simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using
      V.mul_mem hv (V.inv_mem hkv)
  exact (Subgroup.mem_subgroupOf).mpr hmem

private lemma mem_of_mem_map_mk_of_mem {G : Type*} [Group G] {E Z V : Subgroup G}
    [hN : (Z.subgroupOf E).Normal] (hZV : Z ≤ V) {x : E}
    (hx : QuotientGroup.mk' (Z.subgroupOf E) x ∈
      (V.subgroupOf E).map (QuotientGroup.mk' (Z.subgroupOf E))) :
    (x : G) ∈ V := by
  obtain ⟨v, hv, hvx⟩ := Subgroup.mem_map.mp hx
  have hwZ : (v / x : E) ∈ Z.subgroupOf E :=
    (QuotientGroup.eq_iff_div_mem).mp hvx
  have hwV : ((v / x : E) : G) ∈ V := hZV hwZ
  have hv_eq : (v : E) = (v / x : E) * x := (div_mul_cancel v x).symm
  have hx_eq : x = (v / x : E)⁻¹ * v := by
    calc
      x = (v / x : E)⁻¹ * ((v / x : E) * x) := by group
      _ = (v / x : E)⁻¹ * v := by rw [← hv_eq]
  rw [hx_eq]
  exact V.mul_mem (V.inv_mem hwV) hv

private lemma fixedPointFree_quotient {G : Type*} [Group G] [Finite G]
    {E Z V : Subgroup G} {k : G} (hZE : Z ≤ E) (hZV : Z ≤ V)
    (hEE : ⁅E, E⁆ ≤ Z) (hkE : k ∈ Subgroup.normalizer (E : Set G))
    (hkZ : k ∈ Subgroup.normalizer (Z : Set G))
    (hkV : k ∈ Subgroup.normalizer (V : Set G))
    (hfree : ∀ x ∈ E, k * x * k⁻¹ * x⁻¹ ∈ Z → x ∈ Z) :
    ∀ x ∈ E, k * x * k⁻¹ * x⁻¹ ∈ V → x ∈ V := by
  have hEZ : E ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_of_commutator_self hZE hEE
  letI : (Z.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZE).mpr hEZ
  let Q := E ⧸ Z.subgroupOf E
  have hcommE : _root_.commutator E ≤ Z.subgroupOf E := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact hEE (Subgroup.commutator_mem_commutator x.2 y.2)
  letI : IsMulCommutative Q :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mpr hcommE
  let c : Q →* Q := conjCommutatorHom hkE hkZ
  let P : Subgroup Q := (V.subgroupOf E).map (QuotientGroup.mk' (Z.subgroupOf E))
  have hc_inj : Function.Injective c := conjCommutator_injective hkE hkZ hfree
  have hP : P.map c ≤ P := conjCommutator_maps_image_section hkE hkZ hkV
  intro x hxE hxV
  let xE : E := ⟨x, hxE⟩
  have hcxP : c (QuotientGroup.mk' (Z.subgroupOf E) xE) ∈ P := by
    change conjCommutator hkE hkZ (QuotientGroup.mk xE) ∈ P
    rw [conjCommutator_mk]
    refine Subgroup.mem_map_of_mem _ ?_
    have hmem : ((xE * (Subgroup.normalizerMonoidHom E ⟨k, hkE⟩ xE)⁻¹ : E) : G) ∈ V := by
      have hmem' : (xE : G) * (k * (xE : G) * k⁻¹)⁻¹ ∈ V := by
        have h : (xE : G) * (k * (xE : G) * k⁻¹)⁻¹ =
            (k * (xE : G) * k⁻¹ * (xE : G)⁻¹)⁻¹ := by group
        rw [h]
        exact V.inv_mem hxV
      simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using hmem'
    exact (Subgroup.mem_subgroupOf).mpr hmem
  have hxP : QuotientGroup.mk' (Z.subgroupOf E) xE ∈ P :=
    mem_of_map_mem_of_injective_of_mapsTo hc_inj hP hcxP
  exact mem_of_mem_map_mk_of_mem hZV hxP

private lemma mem_iSup_subgroupOf_of_mem_closure {G : Type*} [Group G] {B : Subgroup G}
    {𝒮 : Set (Subgroup G)} {x : B}
    (hsub : (⋃ A : {A : Subgroup G // A ∈ 𝒮}, (A.1 : Set G)) ⊆ B)
    (hx : (x : G) ∈ Subgroup.closure (⋃ A : {A : Subgroup G // A ∈ 𝒮}, (A.1 : Set G))) :
    x ∈ ⨆ A : {A : Subgroup G // A ∈ 𝒮}, A.1.subgroupOf B := by
  have hle : Subgroup.closure (⋃ A : {A : Subgroup G // A ∈ 𝒮}, (A.1 : Set G)) ≤
      (⨆ A : {A : Subgroup G // A ∈ 𝒮}, A.1.subgroupOf B).map (Subgroup.subtype B) := by
    rw [Subgroup.closure_le]
    intro y hy
    obtain ⟨A, hyA⟩ := Set.mem_iUnion.mp hy
    have hyB : y ∈ B := hsub (Set.mem_iUnion_of_mem A hyA)
    have hmemA : (⟨y, hyB⟩ : B) ∈ A.1.subgroupOf B := Subgroup.mem_subgroupOf.mpr hyA
    exact Subgroup.mem_map_of_mem (Subgroup.subtype B)
      (Subgroup.mem_iSup_of_mem
        (S := fun A : {A : Subgroup G // A ∈ 𝒮} => A.1.subgroupOf B) A hmemA)
  obtain ⟨y, hyS, hyx⟩ := Subgroup.mem_map.mp (hle hx)
  have hyx' : y = x := Subtype.ext hyx
  rwa [hyx'] at hyS

private lemma iSup_subgroupOf_eq_top {G : Type*} [Group G] {B : Subgroup G}
    {𝒮 : Set (Subgroup G)} (hB : B = ⨆ A ∈ 𝒮, A) :
    (⨆ A : {A : Subgroup G // A ∈ 𝒮}, A.1.subgroupOf B) = ⊤ := by
  let 𝒮' := {A : Subgroup G // A ∈ 𝒮}
  have hclosure : Subgroup.closure (⋃ A : 𝒮', (A.1 : Set G)) = B := by
    rw [hB, iSup_subtype', Subgroup.iSup_eq_closure]
  have hsub : (⋃ A : 𝒮', (A.1 : Set G)) ⊆ B := by
    intro x hx
    rw [← hclosure]
    exact Subgroup.subset_closure hx
  rw [eq_top_iff]
  intro x _
  have hxcl : (x : G) ∈ Subgroup.closure (⋃ A : 𝒮', (A.1 : Set G)) := by
    rw [hclosure]
    exact x.2
  exact mem_iSup_subgroupOf_of_mem_closure hsub hxcl

private lemma conjCommutator_map_section_le {G : Type*} [Group G] {B V A : Subgroup G}
    [hN : (V.subgroupOf B).Normal] [IsMulCommutative (B ⧸ V.subgroupOf B)]
    {d : G} (hdB : d ∈ Subgroup.normalizer (B : Set G))
    (hdV : d ∈ Subgroup.normalizer (V : Set G))
    (hdA : d ∈ Subgroup.normalizer (A : Set G)) :
    ((A.subgroupOf B).map (QuotientGroup.mk' (V.subgroupOf B))).map
        (conjCommutatorHom hdB hdV) ≤
      (A.subgroupOf B).map (QuotientGroup.mk' (V.subgroupOf B)) := by
  rw [Subgroup.map_le_iff_le_comap]
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hq
  change conjCommutator hdB hdV (QuotientGroup.mk a) ∈
    (A.subgroupOf B).map (QuotientGroup.mk' (V.subgroupOf B))
  rw [show conjCommutator hdB hdV (QuotientGroup.mk a) =
      QuotientGroup.mk' (V.subgroupOf B)
        (a * (Subgroup.normalizerMonoidHom B ⟨d, hdB⟩ a)⁻¹) by
    rw [conjCommutator_mk]
    simp only [QuotientGroup.coe_mk']]
  refine Subgroup.mem_map_of_mem _ ?_
  have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
  have hda : d * (a : G) * d⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp hdA (a : G)).mp haA
  have hcommA : d * (a : G) * d⁻¹ * (a : G)⁻¹ ∈ A :=
    A.mul_mem hda (A.inv_mem haA)
  have hmem : (((a * (Subgroup.normalizerMonoidHom B ⟨d, hdB⟩ a)⁻¹ : B)) : G) ∈ A := by
    have hmem' : (a : G) * (d * (a : G) * d⁻¹)⁻¹ ∈ A := by
      have h : (a : G) * (d * (a : G) * d⁻¹)⁻¹ =
          (d * (a : G) * d⁻¹ * (a : G)⁻¹)⁻¹ := by group
      rw [h]
      exact A.inv_mem hcommA
    simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using hmem'
  exact (Subgroup.mem_subgroupOf).mpr hmem

private lemma conjCommutator_injective_on_section {G : Type*} [Group G] {B V A : Subgroup G}
    [hN : (V.subgroupOf B).Normal] [IsMulCommutative (B ⧸ V.subgroupOf B)]
    {d : G} (hdB : d ∈ Subgroup.normalizer (B : Set G))
    (hdV : d ∈ Subgroup.normalizer (V : Set G))
    (hfree : ∀ x ∈ A, d * x * d⁻¹ * x⁻¹ ∈ V → x ∈ V) :
    Function.Injective
      (fun p : (A.subgroupOf B).map (QuotientGroup.mk' (V.subgroupOf B)) =>
        conjCommutator hdB hdV (p : B ⧸ V.subgroupOf B)) := by
  intro p q hpq
  obtain ⟨a, ha, hpa⟩ := Subgroup.mem_map.mp p.2
  obtain ⟨b, hb, hqb⟩ := Subgroup.mem_map.mp q.2
  have hpq' : conjCommutator hdB hdV (QuotientGroup.mk' (V.subgroupOf B) a) =
      conjCommutator hdB hdV (QuotientGroup.mk' (V.subgroupOf B) b) := by
    calc
      conjCommutator hdB hdV (QuotientGroup.mk' (V.subgroupOf B) a) =
          conjCommutator hdB hdV (↑p) := by rw [hpa]
      _ = conjCommutator hdB hdV (↑q) := hpq
      _ = conjCommutator hdB hdV (QuotientGroup.mk' (V.subgroupOf B) b) := by rw [hqb]
  have h1 : conjCommutator hdB hdV
      (QuotientGroup.mk' (V.subgroupOf B) (a * b⁻¹)) = 1 := by
    have h2 : conjCommutator hdB hdV
        (QuotientGroup.mk' (V.subgroupOf B) a *
          (QuotientGroup.mk' (V.subgroupOf B) b)⁻¹) = 1 := by
      rw [conjCommutator_mul hdB hdV, hpq', conjCommutator_inv]
      group
    rwa [show QuotientGroup.mk' (V.subgroupOf B) a *
          (QuotientGroup.mk' (V.subgroupOf B) b)⁻¹ =
        QuotientGroup.mk' (V.subgroupOf B) (a * b⁻¹) by
      rw [← map_inv, ← map_mul]] at h2
  change conjCommutator hdB hdV (QuotientGroup.mk (a * b⁻¹)) = 1 at h1
  rw [conjCommutator_mk] at h1
  have hzV : ((a * b⁻¹ : B) : G) ∈ V := by
    have hmem := (QuotientGroup.eq_one_iff _).mp h1
    have hcommV : d * ((a * b⁻¹ : B) : G) * d⁻¹ *
        ((a * b⁻¹ : B) : G)⁻¹ ∈ V := by
      have hinv := V.inv_mem hmem
      simpa [Subgroup.normalizerMonoidHom_apply_apply_coe, mul_assoc] using hinv
    exact hfree (a * b⁻¹) (A.mul_mem (Subgroup.mem_subgroupOf.mp ha)
      (A.inv_mem (Subgroup.mem_subgroupOf.mp hb))) hcommV
  apply Subtype.ext
  rw [← hpa, ← hqb]
  exact (QuotientGroup.eq_iff_div_mem).mpr
    (by simpa [div_eq_mul_inv] using (Subgroup.mem_subgroupOf.mpr hzV))

private lemma bijective_of_iSup_of_injective {Q : Type*} [Group Q] [Finite Q]
    {ι : Type*} {P : ι → Subgroup Q} (hPtop : ⨆ i, P i = ⊤)
    {c : Q →* Q} (hcP : ∀ i, (P i).map c ≤ P i)
    (hcinj : ∀ i, Function.Injective (fun p : P i => c (p : Q))) :
    Function.Bijective c := by
  have hle : ∀ i, P i ≤ c.range := by
    intro i q hq
    let f : P i → P i := fun p => ⟨c p, hcP i (Subgroup.mem_map_of_mem c p.2)⟩
    have hf : Function.Injective f := by
      intro p q hpq
      exact hcinj i (congrArg Subtype.val hpq)
    obtain ⟨p, hp⟩ := Finite.injective_iff_surjective.mp hf ⟨q, hq⟩
    exact ⟨p, congrArg Subtype.val hp⟩
  have hrange : c.range = ⊤ := by
    rw [eq_top_iff, ← hPtop]
    exact iSup_le hle
  have hsurj : Function.Surjective c := MonoidHom.range_eq_top.mp hrange
  exact ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩

private lemma mem_of_bijective_conjCommutator {G : Type*} [Group G] [Finite G]
    {B V : Subgroup G} [hN : (V.subgroupOf B).Normal]
    [IsMulCommutative (B ⧸ V.subgroupOf B)] {d : G}
    (hdB : d ∈ Subgroup.normalizer (B : Set G))
    (hdV : d ∈ Subgroup.normalizer (V : Set G))
    (hbij : Function.Bijective (conjCommutatorHom hdB hdV))
    {x : G} (hx : x ∈ B) (hxV : d * x * d⁻¹ * x⁻¹ ∈ V) : x ∈ V := by
  let xB : B := ⟨x, hx⟩
  have hmemV : ((xB * (Subgroup.normalizerMonoidHom B ⟨d, hdB⟩ xB)⁻¹ : B) : G) ∈ V := by
    have hmem' : (x : G) * (d * (x : G) * d⁻¹)⁻¹ ∈ V := by
      have h : (x : G) * (d * (x : G) * d⁻¹)⁻¹ =
          (d * (x : G) * d⁻¹ * (x : G)⁻¹)⁻¹ := by group
      rw [h]
      exact V.inv_mem hxV
    simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using hmem'
  have hcx1 : conjCommutatorHom hdB hdV
      (QuotientGroup.mk' (V.subgroupOf B) xB) = 1 := by
    change conjCommutator hdB hdV (QuotientGroup.mk xB) = 1
    rw [conjCommutator_mk]
    exact (QuotientGroup.eq_one_iff _).mpr ((Subgroup.mem_subgroupOf).mpr hmemV)
  have hq1 : QuotientGroup.mk' (V.subgroupOf B) xB = 1 := by
    apply hbij.1
    rw [hcx1, map_one]
  exact (Subgroup.mem_subgroupOf).mp ((QuotientGroup.eq_one_iff _).mp hq1)

private lemma fixedPointFree_iSup {G : Type*} [Group G] [Finite G] {B V : Subgroup G}
    {𝒮 : Set (Subgroup G)} {d : G} (hB : B = ⨆ A ∈ 𝒮, A)
    (hBB : ⁅B, B⁆ ≤ V) (hVB : V ≤ B)
    (hdV : d ∈ Subgroup.normalizer (V : Set G))
    (hd𝒮 : ∀ A ∈ 𝒮, d ∈ Subgroup.normalizer (A : Set G))
    (hfree : ∀ A ∈ 𝒮, ∀ x ∈ A, d * x * d⁻¹ * x⁻¹ ∈ V → x ∈ V) :
    ∀ x ∈ B, d * x * d⁻¹ * x⁻¹ ∈ V → x ∈ V := by
  have hBVnorm : B ≤ Subgroup.normalizer (V : Set G) :=
    le_normalizer_of_commutator_self hVB hBB
  letI : (V.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVB).mpr hBVnorm
  let Q := B ⧸ V.subgroupOf B
  have hcommB : _root_.commutator B ≤ V.subgroupOf B := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact hBB (Subgroup.commutator_mem_commutator x.2 y.2)
  letI : IsMulCommutative Q :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mpr hcommB
  have hdB : d ∈ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hB, iSup_subtype']
    rw [Subgroup.map_iSup]
    exact iSup_congr fun A =>
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hd𝒮 A.1 A.2)
  let c : Q →* Q := conjCommutatorHom hdB hdV
  let P : {A : Subgroup G // A ∈ 𝒮} → Subgroup Q :=
    fun A => (A.1.subgroupOf B).map (QuotientGroup.mk' (V.subgroupOf B))
  have hPtop : (⨆ A : {A : Subgroup G // A ∈ 𝒮}, P A) = ⊤ := by
    rw [← Subgroup.map_iSup]
    rw [iSup_subgroupOf_eq_top hB]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hcP : ∀ A : {A : Subgroup G // A ∈ 𝒮}, (P A).map c ≤ P A := fun A =>
    conjCommutator_map_section_le hdB hdV (hd𝒮 A.1 A.2)
  have hcinj : ∀ A : {A : Subgroup G // A ∈ 𝒮},
      Function.Injective (fun p : P A => c (p : Q)) := fun A =>
    conjCommutator_injective_on_section hdB hdV (hfree A.1 A.2)
  have hbij : Function.Bijective c := bijective_of_iSup_of_injective hPtop hcP hcinj
  exact fun x hx hxV => mem_of_bijective_conjCommutator hdB hdV hbij hx hxV

theorem mem_of_conj_mem_of_iSup {G : Type*} [Group G] [Finite G] {B V : Subgroup G}
    {𝒮 : Set (Subgroup G)} {d : G} (hB : B = ⨆ A ∈ 𝒮, A) (hBB : ⁅B, B⁆ ≤ V)
    (hVB : V ≤ B) (hdV : d ∈ Subgroup.normalizer (V : Set G))
    (hd𝒮 : ∀ A ∈ 𝒮, d ∈ Subgroup.normalizer (A : Set G))
    (hfree : ∀ A ∈ 𝒮, ∀ x ∈ A, d * x * d⁻¹ * x⁻¹ ∈ V → x ∈ V) :
    ∀ x ∈ B, d * x * d⁻¹ * x⁻¹ ∈ V → x ∈ V :=
  fixedPointFree_iSup hB hBB hVB hdV hd𝒮 hfree

theorem mem_of_conj_mem_of_section {G : Type*} [Group G] [Finite G] {E Z A V : Subgroup G}
    {k : G} (hEE : ⁅E, E⁆ ≤ Z) (hZV : Z ≤ V) (hVA : V ≤ A) (hAE : A ≤ E)
    (hk : ∀ X ∈ ({E, Z, V, A} : Set (Subgroup G)),
      k ∈ Subgroup.normalizer (X : Set G))
    (hfree : ∀ x ∈ E, k * x * k⁻¹ * x⁻¹ ∈ Z → x ∈ Z) :
    ∀ x ∈ A, k * x * k⁻¹ * x⁻¹ ∈ V → x ∈ V := by
  have hZE : Z ≤ E := hZV.trans (hVA.trans hAE)
  exact fun x hx hxV => fixedPointFree_quotient hZE hZV hEE
    (hk E (by simp)) (hk Z (by simp)) (hk V (by simp)) hfree x (hAE hx) hxV

private lemma pow_two_mul_pow_mul_self_eq_one {Q : Type*} [Group Q] [IsMulCommutative Q]
    {w : Q →* Q}
    (hw3 : ∀ q, w (w (w q)) = q) (hfpf : ∀ q, w q = q → q = 1) :
    ∀ q, w (w q) * w q * q = 1 := by
  intro q
  apply hfpf
  calc
    w (w (w q) * w q * q) = w (w (w q)) * w (w q) * w q := by
      simp only [map_mul]
    _ = q * w (w q) * w q := by rw [hw3 q]
    _ = w (w q) * w q * q := by ac_rfl

private lemma s3_identity {Q : Type*} [Group Q] [IsMulCommutative Q] (U V : MulAut Q)
    (hq2 : ∀ q : Q, q * q = 1) (hU2 : ∀ q, U (U q) = q) (hV2 : ∀ q, V (V q) = q)
    (hW3 : ∀ q, (U * V) ((U * V) ((U * V) q)) = q)
    (hfpf : ∀ q, (U * V) q = q → q = 1) :
    ∀ q, q⁻¹ * (U (V q * q⁻¹) * (V q * q⁻¹)⁻¹) *
        (V (U q * q⁻¹) * (U q * q⁻¹)⁻¹) = 1 := by
  intro q
  let W : MulAut Q := U * V
  have hW3' : ∀ q, W (W (W q)) = q := hW3
  have hfpf' : ∀ q, W q = q → q = 1 := hfpf
  have hrel := pow_two_mul_pow_mul_self_eq_one (w := W.toMonoidHom) hW3' hfpf' q
  have hqinv : q⁻¹ = q := (mul_eq_one_iff_eq_inv.mp (hq2 q)).symm
  have hUq2 : U q * U q = 1 := by rw [← map_mul, hq2 q, map_one]
  have hVq2 : V q * V q = 1 := by rw [← map_mul, hq2 q, map_one]
  have hUqinv : (U q)⁻¹ = U q := (mul_eq_one_iff_eq_inv.mp hUq2).symm
  have hVqinv : (V q)⁻¹ = V q := (mul_eq_one_iff_eq_inv.mp hVq2).symm
  have hd : V (U q) = W (W q) := by
    have h1 : W (V (U q)) = q := by
      change U (V (V (U q))) = q
      rw [hV2, hU2]
    have h2 : W (W (W q)) = q := hW3' q
    exact W.injective (h1.trans h2.symm)
  have htarget : q⁻¹ * (U (V q * q⁻¹) * (V q * q⁻¹)⁻¹) *
      (V (U q * q⁻¹) * (U q * q⁻¹)⁻¹) = q * W q * W (W q) := by
    simp only [map_mul, mul_inv_rev, hqinv, hUqinv, hVqinv]
    have h1 : q * (U (V q) * U q * (q * V q)) * (V (U q) * V q * (q * U q)) =
        (q * q) * (U q * U q) * (V q * V q) * (q * U (V q) * V (U q)) := by
      ac_rfl
    rw [h1, hq2, hUq2, hVq2]
    simp only [one_mul, mul_one]
    have hWq : W q = U (V q) := by
      rw [show W = U * V from rfl, MulAut.mul_apply]
    rw [← hd, hWq]
  rw [htarget]
  calc
    q * W q * W (W q) = W (W q) * W q * q := by ac_rfl
    _ = 1 := hrel

private lemma conjQuotient_sq_apply {G : Type*} [Group G] {E Z : Subgroup G}
    [hN : (Z.subgroupOf E).Normal] {k : G}
    (hkE : k ∈ Subgroup.normalizer (E : Set G))
    (hkZ : k ∈ Subgroup.normalizer (Z : Set G))
    (hk2 : ∀ x ∈ E, ⁅k ^ 2, x⁆ ∈ Z) (q : E ⧸ Z.subgroupOf E) :
    conjQuotient hkE hkZ (conjQuotient hkE hkZ q) = q := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [conjQuotient_mk, conjQuotient_mk]
    refine (QuotientGroup.eq_iff_div_mem).mpr ?_
    have h : ((Subgroup.normalizerMonoidHom E ⟨k, hkE⟩
        (Subgroup.normalizerMonoidHom E ⟨k, hkE⟩ x) : E) : G) * (x : G)⁻¹ ∈ Z := by
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have := hk2 x x.2
      simpa [commutatorElement_def, pow_two, mul_assoc] using this
    exact (Subgroup.mem_subgroupOf).mpr (by simpa [div_eq_mul_inv] using h)

private lemma conjQuotient_cube_apply {G : Type*} [Group G] {E Z : Subgroup G}
    [hN : (Z.subgroupOf E).Normal] {k : G}
    (hkE : k ∈ Subgroup.normalizer (E : Set G))
    (hkZ : k ∈ Subgroup.normalizer (Z : Set G))
    (hk3 : ∀ x ∈ E, ⁅k ^ 3, x⁆ ∈ Z) (q : E ⧸ Z.subgroupOf E) :
    conjQuotient hkE hkZ (conjQuotient hkE hkZ (conjQuotient hkE hkZ q)) = q := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [conjQuotient_mk, conjQuotient_mk, conjQuotient_mk]
    refine (QuotientGroup.eq_iff_div_mem).mpr ?_
    have h : ((Subgroup.normalizerMonoidHom E ⟨k, hkE⟩
        (Subgroup.normalizerMonoidHom E ⟨k, hkE⟩
          (Subgroup.normalizerMonoidHom E ⟨k, hkE⟩ x)) : E) : G) * (x : G)⁻¹ ∈ Z := by
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have := hk3 x x.2
      simpa [commutatorElement_def, pow_two, pow_succ, mul_assoc] using this
    exact (Subgroup.mem_subgroupOf).mpr (by simpa [div_eq_mul_inv] using h)

private lemma conjQuotient_eq_self_imp_eq_one {G : Type*} [Group G] {E Z : Subgroup G}
    [hN : (Z.subgroupOf E).Normal] {k : G}
    (hkE : k ∈ Subgroup.normalizer (E : Set G))
    (hkZ : k ∈ Subgroup.normalizer (Z : Set G))
    (hkfree : ∀ x ∈ E, ⁅k, x⁆ ∈ Z → x ∈ Z) (q : E ⧸ Z.subgroupOf E) :
    conjQuotient hkE hkZ q = q → q = 1 := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    intro h
    rw [conjQuotient_mk] at h
    have hdiv : ((Subgroup.normalizerMonoidHom E ⟨k, hkE⟩ x : E) : G) * (x : G)⁻¹ ∈ Z := by
      simpa [div_eq_mul_inv, Subgroup.mem_subgroupOf,
        Subgroup.normalizerMonoidHom_apply_apply_coe] using
        (QuotientGroup.eq_iff_div_mem).mp h
    have hcomm : ⁅k, (x : G)⁆ ∈ Z := by
      simpa [commutatorElement_def, Subgroup.normalizerMonoidHom_apply_apply_coe] using hdiv
    exact (QuotientGroup.eq_one_iff _).mpr (hkfree (x : G) x.2 hcomm)

private lemma mk_commutator_eq {G : Type*} [Group G] {E Z : Subgroup G}
    [hN : (Z.subgroupOf E).Normal] {k : G}
    (hkE : k ∈ Subgroup.normalizer (E : Set G))
    (hkZ : k ∈ Subgroup.normalizer (Z : Set G)) (y : E) :
    QuotientGroup.mk' (Z.subgroupOf E)
        ⟨k * (y : G) * k⁻¹ * (y : G)⁻¹, by
          exact E.mul_mem ((Subgroup.mem_normalizer_iff.mp hkE (y : G)).mp y.2)
            (E.inv_mem y.2)⟩ =
      conjQuotient hkE hkZ (QuotientGroup.mk' (Z.subgroupOf E) y) *
        (QuotientGroup.mk' (Z.subgroupOf E) y)⁻¹ := by
  rw [conjQuotient_mk']
  rw [← map_inv, ← map_mul]
  apply congrArg (QuotientGroup.mk' (Z.subgroupOf E))
  apply Subtype.ext
  simp [Subgroup.normalizerMonoidHom_apply_apply_coe]

private lemma conjQuotient_mul {G : Type*} [Group G] {X W : Subgroup G}
    [hN : (W.subgroupOf X).Normal] {u v : G}
    (huX : u ∈ Subgroup.normalizer (X : Set G))
    (huW : u ∈ Subgroup.normalizer (W : Set G))
    (hvX : v ∈ Subgroup.normalizer (X : Set G))
    (hvW : v ∈ Subgroup.normalizer (W : Set G)) :
    conjQuotient huX huW * conjQuotient hvX hvW =
      conjQuotient (Subgroup.mul_mem _ huX hvX) (Subgroup.mul_mem _ huW hvW) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [MulAut.mul_apply, conjQuotient_mk, conjQuotient_mk, conjQuotient_mk]
    apply congrArg (QuotientGroup.mk' (W.subgroupOf X))
    apply Subtype.ext
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
    group

private lemma quotient_sq_eq_one {G : Type*} [Group G] {E Z : Subgroup G}
    [hN : (Z.subgroupOf E).Normal] (hsq : ∀ x ∈ E, x ^ 2 ∈ Z) :
    ∀ q : E ⧸ Z.subgroupOf E, q * q = 1 := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    change QuotientGroup.mk' (Z.subgroupOf E) x *
      QuotientGroup.mk' (Z.subgroupOf E) x = 1
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr ((Subgroup.mem_subgroupOf).mpr
      (by simpa [pow_two] using hsq (x : G) x.2))

private lemma s3_conj_facts {G : Type*} [Group G] {E Z : Subgroup G}
    [hN : (Z.subgroupOf E).Normal] [IsMulCommutative (E ⧸ Z.subgroupOf E)] {u v : G}
    (huE : u ∈ Subgroup.normalizer (E : Set G))
    (huZ : u ∈ Subgroup.normalizer (Z : Set G))
    (hvE : v ∈ Subgroup.normalizer (E : Set G))
    (hvZ : v ∈ Subgroup.normalizer (Z : Set G))
    (U V : MulAut (E ⧸ Z.subgroupOf E))
    (hU : U = conjQuotient huE huZ) (hV : V = conjQuotient hvE hvZ)
    (hu2 : ∀ x ∈ E, ⁅u ^ 2, x⁆ ∈ Z) (hv2 : ∀ x ∈ E, ⁅v ^ 2, x⁆ ∈ Z)
    (hw3 : ∀ x ∈ E, ⁅(u * v) ^ 3, x⁆ ∈ Z)
    (hwfree : ∀ x ∈ E, ⁅u * v, x⁆ ∈ Z → x ∈ Z) :
    (∀ q, U (U q) = q) ∧ (∀ q, V (V q) = q) ∧
      (∀ q, (U * V) ((U * V) ((U * V) q)) = q) ∧
      (∀ q, (U * V) q = q → q = 1) := by
  have hmulE : u * v ∈ Subgroup.normalizer (E : Set G) :=
    (Subgroup.normalizer (E : Set G)).mul_mem huE hvE
  have hmulZ : u * v ∈ Subgroup.normalizer (Z : Set G) :=
    (Subgroup.normalizer (Z : Set G)).mul_mem huZ hvZ
  have hWmul : U * V = conjQuotient hmulE hmulZ := by
    rw [hU, hV]
    exact conjQuotient_mul huE huZ hvE hvZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q
    rw [hU]
    exact conjQuotient_sq_apply huE huZ hu2 q
  · intro q
    rw [hV]
    exact conjQuotient_sq_apply hvE hvZ hv2 q
  · intro q
    rw [hWmul]
    exact conjQuotient_cube_apply hmulE hmulZ hw3 q
  · intro q h
    rw [hWmul] at h
    exact conjQuotient_eq_self_imp_eq_one hmulE hmulZ hwfree q h

private lemma s3_target {G : Type*} [Group G] {E Z : Subgroup G}
    [hN : (Z.subgroupOf E).Normal] [IsMulCommutative (E ⧸ Z.subgroupOf E)] {u v : G}
    (huE : u ∈ Subgroup.normalizer (E : Set G))
    (huZ : u ∈ Subgroup.normalizer (Z : Set G))
    (hvE : v ∈ Subgroup.normalizer (E : Set G))
    (hvZ : v ∈ Subgroup.normalizer (Z : Set G))
    (U V : MulAut (E ⧸ Z.subgroupOf E))
    (hU : U = conjQuotient huE huZ) (hV : V = conjQuotient hvE hvZ)
    (hq2 : ∀ q : E ⧸ Z.subgroupOf E, q * q = 1)
    (hU2 : ∀ q, U (U q) = q) (hV2 : ∀ q, V (V q) = q)
    (hW3 : ∀ q, (U * V) ((U * V) ((U * V) q)) = q)
    (hfpf : ∀ q, (U * V) q = q → q = 1)
    {x : G} (hx : x ∈ E) :
    x⁻¹ * (⁅u, ⁅v, x⁆⁆ * ⁅v, ⁅u, x⁆⁆) ∈ Z := by
  let xE : E := ⟨x, hx⟩
  let y1 : E := ⟨v * (xE : G) * v⁻¹ * (xE : G)⁻¹, by
    exact E.mul_mem ((Subgroup.mem_normalizer_iff.mp hvE (xE : G)).mp xE.2)
      (E.inv_mem xE.2)⟩
  let y2 : E := ⟨u * (xE : G) * u⁻¹ * (xE : G)⁻¹, by
    exact E.mul_mem ((Subgroup.mem_normalizer_iff.mp huE (xE : G)).mp xE.2)
      (E.inv_mem xE.2)⟩
  let A : E := ⟨u * (y1 : G) * u⁻¹ * (y1 : G)⁻¹, by
    exact E.mul_mem ((Subgroup.mem_normalizer_iff.mp huE (y1 : G)).mp y1.2)
      (E.inv_mem y1.2)⟩
  let B : E := ⟨v * (y2 : G) * v⁻¹ * (y2 : G)⁻¹, by
    exact E.mul_mem ((Subgroup.mem_normalizer_iff.mp hvE (y2 : G)).mp y2.2)
      (E.inv_mem y2.2)⟩
  let q : E ⧸ Z.subgroupOf E := QuotientGroup.mk' (Z.subgroupOf E) xE
  have hqy1 : QuotientGroup.mk' (Z.subgroupOf E) y1 = V q * q⁻¹ := by
    simpa [y1, q, hV] using mk_commutator_eq hvE hvZ xE
  have hqy2 : QuotientGroup.mk' (Z.subgroupOf E) y2 = U q * q⁻¹ := by
    simpa [y2, q, hU] using mk_commutator_eq huE huZ xE
  have hqA : QuotientGroup.mk' (Z.subgroupOf E) A =
      U (QuotientGroup.mk' (Z.subgroupOf E) y1) *
        (QuotientGroup.mk' (Z.subgroupOf E) y1)⁻¹ := by
    simpa [A, hU] using mk_commutator_eq huE huZ y1
  have hqB : QuotientGroup.mk' (Z.subgroupOf E) B =
      V (QuotientGroup.mk' (Z.subgroupOf E) y2) *
        (QuotientGroup.mk' (Z.subgroupOf E) y2)⁻¹ := by
    simpa [B, hV] using mk_commutator_eq hvE hvZ y2
  have hqtarget : QuotientGroup.mk' (Z.subgroupOf E) (xE⁻¹ * (A * B)) =
      q⁻¹ * (U (V q * q⁻¹) * (V q * q⁻¹)⁻¹) *
        (V (U q * q⁻¹) * (U q * q⁻¹)⁻¹) := by
    simp only [map_mul, map_inv, hqA, hqB, hqy1, hqy2,
      show QuotientGroup.mk' (Z.subgroupOf E) xE = q from rfl]; group
  have hmemZ : ((xE⁻¹ * (A * B) : E) : G) ∈ Z :=
    (QuotientGroup.eq_one_iff (N := Z.subgroupOf E) _).mp
      (hqtarget.trans (s3_identity (U := U) (V := V) hq2 hU2 hV2 hW3 hfpf q))
  convert hmemZ using 1

theorem inv_mul_mem_of_s3 {G : Type*} [Group G] {E Z : Subgroup G} {u v : G}
    (hZE : Z ≤ E) (hEE : ⁅E, E⁆ ≤ Z) (hsq : ∀ x ∈ E, x ^ 2 ∈ Z)
    (hu : u ∈ Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hv : v ∈ Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hu2 : ∀ x ∈ E, ⁅u ^ 2, x⁆ ∈ Z) (hv2 : ∀ x ∈ E, ⁅v ^ 2, x⁆ ∈ Z)
    (hw3 : ∀ x ∈ E, ⁅(u * v) ^ 3, x⁆ ∈ Z)
    (hwfree : ∀ x ∈ E, ⁅u * v, x⁆ ∈ Z → x ∈ Z) :
    ∀ x ∈ E, x⁻¹ * (⁅u, ⁅v, x⁆⁆ * ⁅v, ⁅u, x⁆⁆) ∈ Z := by
  have hEZ : E ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_of_commutator_self hZE hEE
  letI : (Z.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZE).mpr hEZ
  let Q := E ⧸ Z.subgroupOf E
  have hcommE : _root_.commutator E ≤ Z.subgroupOf E := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact hEE (Subgroup.commutator_mem_commutator x.2 y.2)
  letI : IsMulCommutative Q :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mpr hcommE
  have huE : u ∈ Subgroup.normalizer (E : Set G) := hu.1
  have huZ : u ∈ Subgroup.normalizer (Z : Set G) := hu.2
  have hvE : v ∈ Subgroup.normalizer (E : Set G) := hv.1
  have hvZ : v ∈ Subgroup.normalizer (Z : Set G) := hv.2
  let U : MulAut Q := conjQuotient huE huZ
  let V : MulAut Q := conjQuotient hvE hvZ
  have hq2 : ∀ q : Q, q * q = 1 := quotient_sq_eq_one hsq
  obtain ⟨hU2, hV2, hW3, hfpf⟩ :=
    s3_conj_facts huE huZ hvE hvZ U V rfl rfl hu2 hv2 hw3 hwfree
  intro x hx
  exact s3_target huE huZ hvE hvZ U V rfl rfl hq2 hU2 hV2 hW3 hfpf hx

end CFSG

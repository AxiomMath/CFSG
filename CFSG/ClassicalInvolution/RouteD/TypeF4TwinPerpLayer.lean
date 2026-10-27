module

public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternLayer
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpBasic

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  isHyperbolicPlane_stdPlane longInv IsLongRootSp2 isLongRootSp2_standard longRootSp2
  isClassicalSL2_longRootSp2 longInv_commute_longRootSp2 minusSpace_longInv_eq
  planeGroup_stdPlane mem_stdPlane_iff mem_coords)

variable {p f : ℕ} [Fact p.Prime]

section Points

theorem commutes_planeGroup_stdPlane_of_le_centralizer {F : Type} [Field F] {n : ℕ}
    (h2 : (2 : F) ≠ 0) (k : Fin n) {P : Submodule F (Fin n ⊕ Fin n → F)}
    (hP : IsHyperbolicPlane P)
    (hle : planeGroup P ≤ Subgroup.centralizer ({longInv F n k} : Set (StatedSp n F)))
    (hne : planeGroup P ≠ planeGroup (stdPlane F n k)) :
    Commutes (planeGroup P) (planeGroup (stdPlane F n k)) := by
  obtain ⟨i, hi, hm⟩ := exists_inv_planeGroup h2 hP
  have hc : Commute i (longInv F n k) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hle (hi.isClassicalSL2 h2).mem)
  have hne' : i ≠ longInv F n k := by
    rintro rfl
    exact hne (by rw [← hm, minusSpace_longInv_eq h2])
  rw [planeGroup_stdPlane]
  exact hi.commute_of_commute h2 (isLongRootSp2_standard k) hc hne'

variable (p f) in
@[expose] noncomputable def f4Node : Subgroup (StatedSp 3 (GaloisField p f)) :=
  planeGroup (stdPlane (GaloisField p f) 3 (Fin.last 2))

variable (p f) in
@[expose] noncomputable def f4Third : Subgroup (StatedSp 3 (GaloisField p f)) :=
  planeGroup (stdPlane (GaloisField p f) 3 0)

theorem f4Node_le_centralizer (hp2 : p ≠ 2) :
    f4Node p f ≤ Subgroup.centralizer ({longInv (GaloisField p f) 3 (Fin.last 2)} : Set _) := by
  have h2 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  rw [f4Node, planeGroup_stdPlane]
  exact (isClassicalSL2_longRootSp2 h2 (Fin.last 2)).le_centralizer

theorem f4Third_le_centralizer (hp2 : p ≠ 2) :
    f4Third p f ≤ Subgroup.centralizer ({longInv (GaloisField p f) 3 (Fin.last 2)} : Set _) := by
  have h2 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  intro x hx
  rw [f4Third, planeGroup_stdPlane] at hx
  exact Subgroup.mem_centralizer_singleton_iff.mpr (longInv_commute_longRootSp2 h2 _ _ hx).symm.eq

theorem f4Third_ne_f4Node (hp2 : p ≠ 2) : f4Third p f ≠ f4Node p f := by
  intro h
  have h2 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hP := planeGroup_injective h2 (isHyperbolicPlane_stdPlane (K := GaloisField p f) (n := 3) 0)
    (isHyperbolicPlane_stdPlane (Fin.last 2)) h
  have hmem : (Pi.single (Sum.inl 0) 1 : Fin 3 ⊕ Fin 3 → GaloisField p f) ∈
      stdPlane (GaloisField p f) 3 0 := Submodule.subset_span (by simp)
  rw [hP, mem_stdPlane_iff] at hmem
  have := hmem (Sum.inl 0) (by rw [mem_coords]; decide)
  simp at this

@[expose] noncomputable def f4NodePoint (hp2 : p ≠ 2) : F4Layer p f :=
  some ⟨f4Node p f, ⟨_, isHyperbolicPlane_stdPlane _, rfl⟩, f4Node_le_centralizer hp2⟩

@[expose] noncomputable def f4ThirdPoint (hp2 : p ≠ 2) : F4Layer p f :=
  some ⟨f4Third p f, ⟨_, isHyperbolicPlane_stdPlane _, rfl⟩, f4Third_le_centralizer hp2⟩

theorem f4NodePoint_ne_none (hp2 : p ≠ 2) : f4NodePoint (p := p) (f := f) hp2 ≠ none :=
  Option.some_ne_none _

theorem f4ThirdPoint_ne_none (hp2 : p ≠ 2) : f4ThirdPoint (p := p) (f := f) hp2 ≠ none :=
  Option.some_ne_none _

theorem f4ThirdPoint_ne_f4NodePoint (hp2 : p ≠ 2) :
    f4ThirdPoint (p := p) (f := f) hp2 ≠ f4NodePoint hp2 := fun h =>
  f4Third_ne_f4Node hp2 (congrArg Subtype.val (Option.some.inj h))

end Points

section Shape

theorem F4Layer.rel_node (hp2 : p ≠ 2) (x : F4Layer p f) (hx : x ≠ f4NodePoint hp2) :
    F4Layer.rel x (f4NodePoint hp2) := by
  rcases x with _ | ⟨R, ⟨P, hP, rfl⟩, hRc⟩
  · exact trivial
  · have h2 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
    exact commutes_planeGroup_stdPlane_of_le_centralizer h2 (Fin.last 2) hP hRc fun h =>
      hx (congrArg some (Subtype.ext h))

theorem F4Layer.rel_none_left (x : F4Layer p f) (hx : x ≠ none) : F4Layer.rel none x := by
  rcases x with _ | R
  · exact absurd rfl hx
  · exact trivial

theorem F4Layer.rel_none_right (x : F4Layer p f) (hx : x ≠ none) : F4Layer.rel x none := by
  rcases x with _ | R
  · exact absurd rfl hx
  · exact trivial

end Shape

section Layer

variable {K : Type*} [Group K]

theorem f4Shape_of_layer (hp2 : p ≠ 2) {Fund : Set (Subgroup K)}
    {R₀ : Subgroup K} {k : K} (hR₀ : R₀ ∈ Fund) (hkR : k ∈ R₀)
    (hk : R₀ ≤ Subgroup.centralizer ({k} : Set K))
    (φ : {R : Subgroup K // R ∈ Fund ∧ R ≤ Subgroup.centralizer ({k} : Set K)} ≃ F4Layer p f)
    (hφ : ∀ R R', Commutes R.1 R'.1 ↔ F4Layer.rel (φ R) (φ R'))
    (h0 : φ ⟨R₀, hR₀, hk⟩ = none) :
    ∃ R₁, UniversalPartner Fund R₀ R₁ ∧ ThirdMember Fund R₀ R₁ := by
  set A : {R : Subgroup K // R ∈ Fund ∧ R ≤ Subgroup.centralizer ({k} : Set K)} :=
    ⟨R₀, hR₀, hk⟩ with hA
  set B := φ.symm (f4NodePoint (p := p) (f := f) hp2) with hB
  set C := φ.symm (f4ThirdPoint (p := p) (f := f) hp2) with hC
  have hBφ : φ B = f4NodePoint hp2 := φ.apply_symm_apply _
  have hCφ : φ C = f4ThirdPoint hp2 := φ.apply_symm_apply _
  have hBA : B ≠ A := fun h => by
    have := congrArg φ h
    rw [hBφ, h0] at this
    exact f4NodePoint_ne_none hp2 this
  have hCA : C ≠ A := fun h => by
    have := congrArg φ h
    rw [hCφ, h0] at this
    exact f4ThirdPoint_ne_none hp2 this
  have hCB : C ≠ B := fun h => by
    have := congrArg φ h
    rw [hCφ, hBφ] at this
    exact f4ThirdPoint_ne_f4NodePoint hp2 this
  refine ⟨B.1, ⟨B.2.1, fun h => hBA (Subtype.ext h), ?_, ?_⟩, C.1, C.2.1,
    fun h => hCA (Subtype.ext h), fun h => hCB (Subtype.ext h), ?_⟩
  · refine (hφ A B).mpr ?_
    rw [h0, hBφ]
    exact F4Layer.rel_none_left _ (f4NodePoint_ne_none hp2)
  · intro S hS hSc
    have hSk : S ≤ Subgroup.centralizer ({k} : Set K) := fun s hs =>
      Subgroup.mem_centralizer_iff.mpr fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact (hSc s hs h hkR).symm
    by_cases hX : φ ⟨S, hS, hSk⟩ = f4NodePoint hp2
    · left
      exact congrArg Subtype.val (φ.injective (hX.trans hBφ.symm))
    · right
      refine (hφ ⟨S, hS, hSk⟩ B).mpr ?_
      rw [hBφ]
      exact F4Layer.rel_node hp2 _ hX
  · refine (hφ C A).mpr ?_
    rw [h0, hCφ]
    exact F4Layer.rel_none_right _ (f4ThirdPoint_ne_none hp2)

theorem f4Card_of_layer [Finite K] {Fund : Set (Subgroup K)} {R₀ : Subgroup K} {k : K}
    (hR₀ : R₀ ∈ Fund) (hkR : k ∈ R₀) (hk : R₀ ≤ Subgroup.centralizer ({k} : Set K))
    (φ : {R : Subgroup K // R ∈ Fund ∧ R ≤ Subgroup.centralizer ({k} : Set K)} ≃ F4Layer p f)
    (hφ : ∀ R R', Commutes R.1 R'.1 ↔ F4Layer.rel (φ R) (φ R'))
    (h0 : φ ⟨R₀, hR₀, hk⟩ = none) :
    Nat.card {S : Subgroup K // S ∈ Fund ∧ Commutes S R₀} + 1 = Nat.card (F4Layer p f) := by
  classical
  set A : {R : Subgroup K // R ∈ Fund ∧ R ≤ Subgroup.centralizer ({k} : Set K)} :=
    ⟨R₀, hR₀, hk⟩ with hA
  have hle : ∀ S : Subgroup K, Commutes S R₀ → S ≤ Subgroup.centralizer ({k} : Set K) :=
    fun S hS s hs => Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hS s hs h hkR).symm
  have hfin : Finite (F4Layer p f) := Finite.of_equiv _ φ
  have e : {S : Subgroup K // S ∈ Fund ∧ Commutes S R₀} ≃ {x : F4Layer p f // x ≠ none} :=
    { toFun := fun S => ⟨φ ⟨S.1, S.2.1, hle S.1 S.2.2⟩, fun h => by
        have hX : (⟨S.1, S.2.1, hle S.1 S.2.2⟩ : {R : Subgroup K // R ∈ Fund ∧
            R ≤ Subgroup.centralizer ({k} : Set K)}) = A := φ.injective (h.trans h0.symm)
        have hS : S.1 = R₀ := congrArg Subtype.val hX
        have hc : Commutes R₀ R₀ := by
          have := S.2.2
          rwa [hS] at this
        have := (hφ A A).mp hc
        rw [h0] at this
        exact this⟩
      invFun := fun x => ⟨(φ.symm x.1).1, (φ.symm x.1).2.1, by
        have := (hφ (φ.symm x.1) A).mpr (by
          rw [φ.apply_symm_apply, h0]
          exact F4Layer.rel_none_right _ x.2)
        exact this⟩
      left_inv := fun S => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  rw [Nat.card_congr e]
  exact card_ne_none_add_one

end Layer

end CFSG.ClassicalInvolution.RouteD.NonClassical

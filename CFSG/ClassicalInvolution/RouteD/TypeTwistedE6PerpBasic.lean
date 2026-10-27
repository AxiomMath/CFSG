module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpLayer
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExc

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime]

section Abstract

variable {K : Type*} [Group K]

@[expose] def UniversalPartner (Fund : Set (Subgroup K)) (R₀ R₁ : Subgroup K) : Prop :=
  R₁ ∈ Fund ∧ R₁ ≠ R₀ ∧ Commutes R₀ R₁ ∧ ∀ S ∈ Fund, Commutes S R₀ → S = R₁ ∨ Commutes S R₁

@[expose] def ThirdMember (Fund : Set (Subgroup K)) (R₀ R₁ : Subgroup K) : Prop :=
  ∃ S ∈ Fund, S ≠ R₀ ∧ S ≠ R₁ ∧ Commutes S R₀

@[expose] def NoThreeCommuting (Fund : Set (Subgroup K)) : Prop :=
  ∀ A ∈ Fund, ∀ B ∈ Fund, ∀ C ∈ Fund, A ≠ B → A ≠ C → B ≠ C → Commutes A B → Commutes A C →
    Commutes B C → False

@[expose] def NoPartner (Fund : Set (Subgroup K)) : Prop :=
  ∀ R₀ ∈ Fund, ∀ S ∈ Fund, S ≠ R₀ → ¬ Commutes S R₀

@[expose] def PairSeparated (Fund : Set (Subgroup K)) : Prop :=
  ∀ R₀ ∈ Fund, ∀ R₁ ∈ Fund, R₁ ≠ R₀ → Commutes R₀ R₁ →
    ∃ S ∈ Fund, Commutes S R₀ ∧ S ≠ R₁ ∧ ¬ Commutes S R₁

theorem UniversalPartner.commutes_symm {Fund : Set (Subgroup K)} {R₀ R₁ : Subgroup K}
    (h : UniversalPartner Fund R₀ R₁) : Commutes R₁ R₀ :=
  h.2.2.1.symm

theorem false_of_noThreeCommuting {Fund : Set (Subgroup K)} (hNo : NoThreeCommuting Fund)
    {R₀ R₁ : Subgroup K} (hR₀ : R₀ ∈ Fund) (hP : UniversalPartner Fund R₀ R₁)
    (hT : ThirdMember Fund R₀ R₁) : False := by
  obtain ⟨S, hS, hS0, hS1, hSc⟩ := hT
  have hc1 : Commutes S R₁ := (hP.2.2.2 S hS hSc).resolve_left hS1
  exact hNo R₀ hR₀ R₁ hP.1 S hS (Ne.symm hP.2.1) (Ne.symm hS0) (Ne.symm hS1) hP.2.2.1
    hSc.symm hc1.symm

theorem false_of_noPartner {Fund : Set (Subgroup K)} (hNo : NoPartner Fund) {R₀ R₁ : Subgroup K}
    (hR₀ : R₀ ∈ Fund) (hP : UniversalPartner Fund R₀ R₁) : False :=
  hNo R₀ hR₀ R₁ hP.1 hP.2.1 hP.commutes_symm

theorem false_of_pairSeparated {Fund : Set (Subgroup K)} (hSep : PairSeparated Fund)
    {R₀ R₁ : Subgroup K} (hR₀ : R₀ ∈ Fund) (hP : UniversalPartner Fund R₀ R₁) : False := by
  obtain ⟨S, hS, hSc, hS1, hn⟩ := hSep R₀ hR₀ R₁ hP.1 hP.2.1 hP.2.2.1
  rcases hP.2.2.2 S hS hSc with h | h
  · exact hS1 h
  · exact hn h

theorem false_of_universalPartner_of_layer {Fund : Set (Subgroup K)}
    (hconj : ∀ R ∈ Fund, ∀ g : K, conjSub g R ∈ Fund) (hperf : ∀ R ∈ Fund, R ≤ ⁅R, R⁆)
    (hnab : ∀ R ∈ Fund, ¬ ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) {R₀ R₁ : Subgroup K}
    (hP : UniversalPartner Fund R₀ R₁)
    (hlayer : ∃ L : Subgroup K, CFSG.Open.IsQuasisimple ↥L ∧
      L ≤ Subgroup.centralizer (R₀ : Set K) ∧
      (∀ P : Subgroup K, P ≤ Subgroup.centralizer (R₀ : Set K) → P ≤ ⁅P, P⁆ → P ≤ L) ∧
      L ∉ Fund) : False := by
  obtain ⟨hR₁, -, hc, huniv⟩ := hP
  obtain ⟨L, hLqs, hLC, hLperf, hLfund⟩ := hlayer
  have hR₁C : R₁ ≤ Subgroup.centralizer (R₀ : Set K) :=
    fun y hy => Subgroup.mem_centralizer_iff.mpr fun x hx => hc x hx y hy
  have hR₁L : R₁ ≤ L := hLperf R₁ hR₁C (hperf R₁ hR₁)
  obtain ⟨g, hgL, hg1, hg2⟩ := exists_conj_not_commutes_of_le hLqs hR₁L (hnab R₁ hR₁)
    (fun hLR => hLfund (le_antisymm hLR hR₁L ▸ hR₁))
  have hSL : conjSub g R₁ ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    exact L.mul_mem (L.mul_mem hgL (hR₁L hy)) (L.inv_mem hgL)
  have hcS : Commutes (conjSub g R₁) R₀ := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hLC (hSL hx)) y hy).symm
  rcases huniv _ (hconj R₁ hR₁ g) hcS with h | h
  · exact hg1 h
  · exact hg2 h

end Abstract

section Layer

variable {K : Type*} [Group K]

theorem te6Shape_of_layer (hp2 : p ≠ 2) (hf : 1 ≤ f) {Fund : Set (Subgroup K)}
    {R₀ : Subgroup K} {k : K} (hR₀ : R₀ ∈ Fund) (hkR : k ∈ R₀)
    (hk : R₀ ≤ Subgroup.centralizer ({k} : Set K))
    (φ : {R : Subgroup K // R ∈ Fund ∧ R ≤ Subgroup.centralizer ({k} : Set K)} ≃ TE6Layer p f)
    (hφ : ∀ R R', Commutes R.1 R'.1 ↔ TE6Layer.rel (φ R) (φ R'))
    (h0 : φ ⟨R₀, hR₀, hk⟩ = none) :
    ∃ R₁, UniversalPartner Fund R₀ R₁ ∧ ThirdMember Fund R₀ R₁ := by
  set A : {R : Subgroup K // R ∈ Fund ∧ R ≤ Subgroup.centralizer ({k} : Set K)} :=
    ⟨R₀, hR₀, hk⟩ with hA
  set B := φ.symm (te6NodePoint (p := p) (f := f) hp2) with hB
  set C := φ.symm (te6PlanePoint (p := p) (f := f) hp2) with hC
  have hBφ : φ B = te6NodePoint hp2 := φ.apply_symm_apply _
  have hCφ : φ C = te6PlanePoint hp2 := φ.apply_symm_apply _
  have hBA : B ≠ A := fun h => by
    have := congrArg φ h
    rw [hBφ, h0] at this
    exact te6NodePoint_ne_none hp2 this
  have hCA : C ≠ A := fun h => by
    have := congrArg φ h
    rw [hCφ, h0] at this
    exact te6PlanePoint_ne_none hp2 this
  have hCB : C ≠ B := fun h => by
    have := congrArg φ h
    rw [hCφ, hBφ] at this
    exact te6PlanePoint_ne_te6NodePoint hp2 hf this
  refine ⟨B.1, ⟨B.2.1, fun h => hBA (Subtype.ext h), ?_, ?_⟩, C.1, C.2.1,
    fun h => hCA (Subtype.ext h), fun h => hCB (Subtype.ext h), ?_⟩
  · refine (hφ A B).mpr ?_
    rw [h0, hBφ]
    exact TE6Layer.rel_none_left _ (te6NodePoint_ne_none hp2)
  · intro S hS hSc
    have hSk : S ≤ Subgroup.centralizer ({k} : Set K) := fun s hs =>
      Subgroup.mem_centralizer_iff.mpr fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact (hSc s hs h hkR).symm
    by_cases hX : φ ⟨S, hS, hSk⟩ = te6NodePoint hp2
    · left
      exact congrArg Subtype.val (φ.injective (hX.trans hBφ.symm))
    · right
      refine (hφ ⟨S, hS, hSk⟩ B).mpr ?_
      rw [hBφ]
      exact TE6Layer.rel_node hp2 hf _ hX
  · refine (hφ C A).mpr ?_
    rw [h0, hCφ]
    exact TE6Layer.rel_none_right _ (te6PlanePoint_ne_none hp2)

theorem card_ne_none_add_one {β : Type*} [Finite β] :
    Nat.card {x : Option β // x ≠ none} + 1 = Nat.card (Option β) := by
  have e : {x : Option β // x ≠ none} ≃ β :=
    { toFun := fun x => x.1.get (Option.ne_none_iff_isSome.mp x.2)
      invFun := fun b => ⟨some b, Option.some_ne_none b⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun b => by simp }
  rw [Nat.card_congr e]
  have := Fintype.ofFinite β
  simp [Nat.card_eq_fintype_card, Fintype.card_option]

theorem te6Card_of_layer [Finite K] {Fund : Set (Subgroup K)} {R₀ : Subgroup K} {k : K}
    (hR₀ : R₀ ∈ Fund) (hkR : k ∈ R₀) (hk : R₀ ≤ Subgroup.centralizer ({k} : Set K))
    (φ : {R : Subgroup K // R ∈ Fund ∧ R ≤ Subgroup.centralizer ({k} : Set K)} ≃ TE6Layer p f)
    (hφ : ∀ R R', Commutes R.1 R'.1 ↔ TE6Layer.rel (φ R) (φ R'))
    (h0 : φ ⟨R₀, hR₀, hk⟩ = none) :
    Nat.card {S : Subgroup K // S ∈ Fund ∧ Commutes S R₀} + 1 = Nat.card (TE6Layer p f) := by
  classical
  set A : {R : Subgroup K // R ∈ Fund ∧ R ≤ Subgroup.centralizer ({k} : Set K)} :=
    ⟨R₀, hR₀, hk⟩ with hA
  have hle : ∀ S : Subgroup K, Commutes S R₀ → S ≤ Subgroup.centralizer ({k} : Set K) :=
    fun S hS s hs => Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hS s hs h hkR).symm
  have hfin : Finite (TE6Layer p f) := Finite.of_equiv _ φ
  have e : {S : Subgroup K // S ∈ Fund ∧ Commutes S R₀} ≃ {x : TE6Layer p f // x ≠ none} :=
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
          exact TE6Layer.rel_none_right _ x.2)
        exact this⟩
      left_inv := fun S => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  rw [Nat.card_congr e]
  exact card_ne_none_add_one

end Layer

end CFSG.ClassicalInvolution.RouteD.NonClassical

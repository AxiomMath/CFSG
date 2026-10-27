module

public import CFSG.ClassicalInvolution.Q3.Q3NMFixed

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.RouteD

section Transport

variable {G A : Type} [Group G] [Group A]

@[expose] noncomputable def inducedAut {S : Subgroup G} (e : A ≃* ↥S) (σ : MulAut G)
    (hS : S.map (σ : G →* G) = S) : MulAut A :=
  MulAut.congr e.symm ((MulEquiv.subgroupMap σ S).trans (MulEquiv.subgroupCongr hS))

theorem coe_inducedAut {S : Subgroup G} (e : A ≃* ↥S) (σ : MulAut G)
    (hS : S.map (σ : G →* G) = S) (a : A) :
    ((e (inducedAut e σ hS a) : ↥S) : G) = σ ((e a : ↥S) : G) := by
  simp [inducedAut, MulAut.congr_apply]

theorem oddCoreIn_inf_fixed_eq_bot_of_equiv_on {S : Subgroup G} (e : A ≃* ↥S)
    (P : MulAut A → Prop)
    (hA : ∀ ρ : MulAut A, ρ * ρ = 1 → P ρ → oddCoreIn (fixedSubgroup ρ) = ⊥)
    (σ : MulAut G) (hσ : σ * σ = 1) (hS : S.map (σ : G →* G) = S)
    (hP : P (inducedAut e σ hS)) : oddCoreIn (S ⊓ fixedSubgroup σ) = ⊥ := by
  set σS : MulAut ↥S := (MulEquiv.subgroupMap σ S).trans (MulEquiv.subgroupCongr hS) with hσS
  have hσSapp : ∀ x : ↥S, ((σS x : ↥S) : G) = σ (x : G) := fun x => rfl
  have hσS2 : σS * σS = 1 := by
    ext x
    show ((σS (σS x) : ↥S) : G) = (x : G)
    rw [hσSapp, hσSapp]
    exact apply_apply_of_mul_eq_one hσ _
  set ρ : MulAut A := inducedAut e σ hS with hρ
  have hρ' : ρ = MulAut.congr e.symm σS := rfl
  have hρ2 : ρ * ρ = 1 := by
    rw [hρ', ← map_mul, hσS2, map_one]
  have hcongr : MulAut.congr e ρ = σS := by
    refine MulEquiv.ext fun x => ?_
    show e (ρ (e.symm x)) = σS x
    simp [hρ', MulAut.congr_apply]
  have h1 := oddCoreIn_fixed_congr_eq_bot' e ρ (hA ρ hρ2 hP)
  rw [hcongr] at h1
  have hmap : (fixedSubgroup σS).map S.subtype = S ⊓ fixedSubgroup σ := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, congrArg Subtype.val (mem_fixedSubgroup_iff.mp hy)⟩
    · rintro ⟨hxS, hx⟩
      exact ⟨⟨x, hxS⟩, Subtype.ext (mem_fixedSubgroup_iff.mp hx), rfl⟩
  have h2 := map_oddCoreIn_subtype (Y := S) (fixedSubgroup σS)
  rw [hmap, h1, Subgroup.map_bot] at h2
  exact h2.symm

theorem oddCoreIn_eq_bot_of_equiv_on {S : Subgroup G} (e : A ≃* ↥S) (P : MulAut A → Prop)
    (hA : ∀ ρ : MulAut A, ρ * ρ = 1 → P ρ → oddCoreIn (fixedSubgroup ρ) = ⊥)
    (hP : ∀ ρ : MulAut A, (∀ a : A, ρ a = a) → P ρ) : oddCoreIn S = ⊥ := by
  have hS1 : S.map ((1 : MulAut G) : G →* G) = S := by ext x; simp
  have hid : ∀ a : A, inducedAut e (1 : MulAut G) hS1 a = a := by
    intro a
    apply e.injective
    apply Subtype.ext
    rw [coe_inducedAut]
    rfl
  have h := oddCoreIn_inf_fixed_eq_bot_of_equiv_on e P hA (1 : MulAut G) (by simp) hS1
    (hP _ hid)
  have hf : fixedSubgroup (1 : MulAut G) = ⊤ := by
    ext x
    simp [mem_fixedSubgroup_iff]
  rwa [hf, inf_top_eq] at h

end Transport

@[expose] def FixedOddFreeFund (c : CompData) : Prop :=
  ∀ ρ : MulAut (c.G ⧸ Subgroup.center c.G), ρ * ρ = 1 →
    (∃ R ∈ c.fund, ∀ r ∈ R, ρ (QuotientGroup.mk r) = QuotientGroup.mk r) →
    oddCoreIn (fixedSubgroup ρ) = ⊥

theorem FixedOddFree.toFund {c : CompData} (h : FixedOddFree (c.G ⧸ Subgroup.center c.G)) :
    FixedOddFreeFund c := fun ρ hρ _ => h ρ hρ

section Lie


variable {ι X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem coe_compBarEquiv_mk (D : LieSystemData3 ι X Φ) {i : ι} (hF : CompFacts (D.kind i))
    (r : (D.kind i).G) :
    ((compBarEquiv D hF (QuotientGroup.mk r) : ↥(compBar D i)) : X ⧸ Subgroup.center X) =
      QuotientGroup.mk (D.hom i r) :=
  rfl

theorem inducedAut_compBar_fix (D : LieSystemData3 ι X Φ) {i : ι} (hF : CompFacts (D.kind i))
    (σ : MulAut X)
    (hS : (compBar D i).map (autToCentralQuotient X σ : (X ⧸ Subgroup.center X) →*
      (X ⧸ Subgroup.center X)) = compBar D i)
    {R : Subgroup (D.kind i).G} (hR : ∀ y ∈ R.map (D.hom i), σ y = y) {r : (D.kind i).G}
    (hr : r ∈ R) :
    inducedAut (compBarEquiv D hF) (autToCentralQuotient X σ) hS (QuotientGroup.mk r) =
      QuotientGroup.mk r := by
  apply (compBarEquiv D hF).injective
  apply Subtype.ext
  rw [coe_inducedAut, coe_compBarEquiv_mk, autToCentralQuotient_mk,
    hR _ (Subgroup.mem_map.mpr ⟨r, hr, rfl⟩)]

variable [Finite ι] [Finite X] {D : LieSystemData3 ι X Φ}

theorem oddCoreIn_fixed_eq_bot_of_lieSystemData3_fund (hF : ∀ i, CompFacts (D.kind i))
    (hO : oddCoreIn (⊤ : Subgroup X) = ⊥) (σ : MulAut X) (hσ : σ * σ = 1)
    (hΦ : ∀ L ∈ Φ, L.map (σ : X →* X) ∈ Φ)
    (hcomp : ∀ i, FixedOddFree ((D.kind i).G ⧸ Subgroup.center (D.kind i).G) ∨
      (FixedOddFreeFund (D.kind i) ∧
        ∃ R ∈ (D.kind i).fund, ∀ y ∈ R.map (D.hom i), σ y = y)) :
    oddCoreIn (fixedSubgroup σ) = ⊥ := by
  obtain ⟨π, hP⟩ := LieSystemData3.permProd (D := D) hF σ hσ hΦ
  refine oddCoreIn_fixed_eq_bot_of_quotient hO σ ?_
  refine oddCoreIn_fixed_eq_bot_of_permProd hP ?_ ?_
  · intro i hi
    have hS : (compBar D i).map (autToCentralQuotient X σ : (X ⧸ Subgroup.center X) →*
        (X ⧸ Subgroup.center X)) = compBar D i := by rw [hP.map i, hi]
    rcases hcomp i with h | ⟨hfund, R, hR, hfix⟩
    · exact oddCoreIn_inf_fixed_eq_bot_of_equiv (compBarEquiv D (hF i)) h _ hP.sq hS
    · exact oddCoreIn_inf_fixed_eq_bot_of_equiv_on (compBarEquiv D (hF i))
        (fun ρ => ∃ R ∈ (D.kind i).fund, ∀ r ∈ R, ρ (QuotientGroup.mk r) = QuotientGroup.mk r)
        (fun ρ hρ hPρ => hfund ρ hρ hPρ) _ hP.sq hS
        ⟨R, hR, fun r hr => inducedAut_compBar_fix D (hF i) σ hS hfix hr⟩
  · intro i _
    rcases hcomp i with h | ⟨hfund, -, -⟩
    · exact oddCoreIn_eq_bot_of_equiv (compBarEquiv D (hF i)) h
    · obtain ⟨R, hR, -⟩ := D.meets i
      exact oddCoreIn_eq_bot_of_equiv_on (compBarEquiv D (hF i))
        (fun ρ => ∃ R ∈ (D.kind i).fund, ∀ r ∈ R, ρ (QuotientGroup.mk r) = QuotientGroup.mk r)
        (fun ρ hρ hPρ => hfund ρ hρ hPρ)
        (fun ρ hρ => ⟨R, hR, fun r _ => hρ _⟩)

end Lie

section Local


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem oddCoreIn_layer_fixed_le_of_components (hΩ : ConjInvariant Ω) (h0 : ModelClauseZero)
    (hM : M11Facts) {a b : G} (hab : a ∈ Subgroup.centralizer ({b} : Set G))
    (ha2 : orderOf a = 2) {ι : Type} [Finite ι]
    (D : LieSystemData3 ι (locQuot Ω b) (locFamily Ω b))
    (hcomp : ∀ i, FixedOddFree ((D.kind i).G ⧸ Subgroup.center (D.kind i).G) ∨
      (FixedOddFreeFund (D.kind i) ∧ ∃ R ∈ (D.kind i).fund, ∃ K ∈ centralizingMembers Ω {b},
        K ≤ Subgroup.centralizer ({a} : Set G) ∧ locImg Ω b K = R.map (D.hom i))) :
    oddCoreIn (centralizingLayer Ω {b} ⊓ Subgroup.centralizer ({a} : Set G)) ≤
      oddCoreIn (centralizingLayer Ω {b}) := by
  set Y : Subgroup G := centralizingLayer Ω {b} with hY
  have haN : a ∈ Subgroup.normalizer (Y : Set G) := mem_normalizer_centralizingLayer hΩ hab
  have haa : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha2, sq] at this
  set σ : MulAut ↥Y := conjAut Y a haN with hσdef
  have hσ : σ * σ = 1 := conjAut_mul_self Y a haN haa
  have hP : (classicalInvolutionOddCore ↥Y).map (σ : ↥Y →* ↥Y) = classicalInvolutionOddCore ↥Y :=
    CFSG.ComponentClassification.OddCore.equiv_invariant σ
  have hpres : ∀ L ∈ restrictFamily (centralizingMembers Ω {b}) Y,
      L.map (σ : ↥Y →* ↥Y) ∈ restrictFamily (centralizingMembers Ω {b}) Y := by
    rintro _ ⟨L₀, hL₀, hLY, rfl⟩
    have hc := conjSub_mem_centralizingMembers hΩ hab hL₀
    refine ⟨conjSub a L₀, hc, le_centralizingLayer hc, ?_⟩
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_subgroupOf, mem_conjSub_iff]
      have e : a⁻¹ * (a * (y : G) * a⁻¹) * a = y := by group
      show a⁻¹ * ((conjAut Y a haN y : ↥Y) : G) * a ∈ L₀
      rw [conjAut_apply, e]
      exact hy
    · intro hz
      refine ⟨(conjAut Y a haN).symm z, ?_, (conjAut Y a haN).apply_symm_apply z⟩
      exact (mem_conjSub_iff).mp (Subgroup.mem_subgroupOf.mp hz)
  have h1 : oddCoreIn (fixedSubgroup σ) ≤ classicalInvolutionOddCore ↥Y := by
    refine oddCoreIn_fixed_le_of_quotient (classicalInvolutionOddCore ↥Y)
      (CFSG.ComponentClassification.OddCore.odd_card ↥Y) σ hσ hP ?_
    refine oddCoreIn_fixed_eq_bot_of_lieSystemData3_fund (D := D)
      (fun i => compFacts_of_valid h0 hM (D.valid i)) (oddCoreIn_top_quotient_eq_bot ↥Y)
      (quotAut _ σ hP) (quotAut_mul_self _ σ hσ hP) ?_ ?_
    · rintro _ ⟨L, hL, rfl⟩
      refine ⟨L.map (σ : ↥Y →* ↥Y), hpres L hL, ?_⟩
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    · intro i
      rcases hcomp i with h | ⟨hfund, R, hR, K, hK, hKa, hKR⟩
      · exact Or.inl h
      · refine Or.inr ⟨hfund, R, hR, ?_⟩
        intro y hy
        rw [← hKR] at hy
        obtain ⟨k, hk, rfl⟩ := hy
        have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
        have hka : a * (k : G) = (k : G) * a :=
          (Subgroup.mem_centralizer_singleton_iff.mp (hKa hkK)).symm
        show QuotientGroup.mk (σ k) = QuotientGroup.mk k
        congr 1
        apply Subtype.ext
        show a * (k : G) * a⁻¹ = k
        calc a * (k : G) * a⁻¹ = ((k : G) * a) * a⁻¹ := by rw [hka]
          _ = k := by group
  have h2 := Subgroup.map_mono (f := Y.subtype) h1
  rw [map_oddCoreIn_subtype, map_fixedSubgroup_conjAut] at h2
  exact h2

end Local

end CFSG.ClassicalInvolution.Q3.Q3PP

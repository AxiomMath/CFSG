module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Interfaces
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Surv27Dual
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.MinOffender
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.BcInvariants
public import CFSG.Sporadic.Schreier.J4SSylowBase

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
  CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.LieType.Chevalley.ExceptionalCover TensorProduct


theorem _root_.CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.IsCoverType.congr_H
    {Ĝ G : Type*} [Group Ĝ] [Group G] {B : Type*} {M : CoxeterMatrix B} {W : Type*} [Group W]
    {cs : CoxeterSystem M W} {p : ℕ} [Finite Ĝ] [Fact p.Prime] {D : CurtisDatum G cs p}
    {π : Ĝ →* G} {C : CentralCoverData D π p} {F : B → Type} [∀ s, Field (F s)]
    {R : CoverRankOne C F} {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k Ĝ V} {y : V} {χ χ' : Ĝ → k} {J : Finset B}
    (ht : IsCoverType R ρ y χ J) (h : ∀ x ∈ D.H.comap π, χ x = χ' x) :
    IsCoverType R ρ y χ' J :=
  ⟨ht.1, ht.2.1, fun x hx => by rw [ht.2.2.1 x hx, h x hx], fun s => by
    rw [ht.2.2.2 s]
    exact and_congr (forall_congr' fun u => by rw [h _ (R.hh_mem s u)]) Iff.rfl⟩

theorem finrank_fixSub_bcRep_le {K k G W : Type*} [Field K] [Field k] [Algebra K k]
    [AddCommGroup W] [Module K W] [Module.Finite K W] [Group G] [Finite G]
    (ρ : Representation K G W) (A : Subgroup G) :
    Module.finrank k ↥(fixSub (bcRep k ρ) A) ≤ Module.finrank K ↥(fixSub ρ A) := by
  have h1 : fixSub (bcRep k ρ) A = Representation.invariants ((bcRep k ρ).comp A.subtype) := by
    ext v
    rw [Representation.mem_invariants]
    exact ⟨fun h g => h g.1 g.2, fun h g hg => h ⟨g, hg⟩⟩
  have h2 : fixSub ρ A = Representation.invariants (ρ.comp A.subtype) := by
    ext v
    rw [Representation.mem_invariants]
    exact ⟨fun h g => h g.1 g.2, fun h g hg => h ⟨g, hg⟩⟩
  rw [h1, h2]
  haveI : Finite ↥A := inferInstance
  exact CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.finrank_invariants_bcRep_le
    (K := K) (k := k) (ρ.comp A.subtype)

theorem finrank_fixSub_of_iso {k G V W : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] {ρ : Representation k G V} {σ : Representation k G W}
    (β : V ≃ₗ[k] W) (hβ : ∀ g v, β (ρ g v) = σ g (β v)) (A : Subgroup G) :
    Module.finrank k ↥(fixSub σ A) = Module.finrank k ↥(fixSub ρ A) := by
  have hm : (fixSub ρ A).map β.toLinearMap = fixSub σ A := by
    ext w
    simp only [Submodule.mem_map, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨v, hv, rfl⟩ g hg
      rw [← hβ, hv g hg]
    · intro hw
      refine ⟨β.symm w, fun g hg => ?_, β.apply_symm_apply w⟩
      apply β.injective
      rw [hβ, β.apply_symm_apply, hw g hg]
  rw [← hm]
  exact (LinearEquiv.finrank_eq ((fixSub ρ A).equivMapOfInjective β.toLinearMap β.injective)).symm

@[expose] def frobEquiv (K : Type) [Field K] [Finite K] [CharP K 2] (b : ℕ) : K ≃+* K :=
  have : ExpChar K 2 := ExpChar.prime Nat.prime_two
  iterateFrobeniusEquiv K 2 b

theorem frobEquiv_apply {K : Type} [Field K] [Finite K] [CharP K 2] (b : ℕ) (c : K) :
    frobEquiv K b c = c ^ (2 ^ b) := by
  have : ExpChar K 2 := ExpChar.prime Nat.prime_two
  exact iterateFrobeniusEquiv_def K 2 b c

section Torus

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem e6_H_le_range_minTorus {h : ↥(e6Data_valid.minGroup K)}
    (hh : h ∈ (chevDatumLD TwistTag.E6 K 2 e6LongestData).H.comap (Isogeny.e6IsogenyT K)) :
    h ∈ (minTorus e6Data_valid K).range := by
  classical
  let N := (minTorus e6Data_valid K).range
  let f : ↥(e6Data_valid.minGroup K) →* ModGL TwistTag.E6.tag K :=
    (adjointGroup TwistTag.E6.tag K).subtype.comp (Isogeny.e6IsogenyT K)
  have hcl : torusGroup TwistTag.E6.tag K ≤ N.map f := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, t⟩, rfl⟩
    refine ⟨e6Data_valid.hm K i t, ⟨Pi.mulSingle i t, minTorus_mulSingle e6Data_valid K i t⟩, ?_⟩
    exact coe_e6IsogenyT_hm i t
  have hh' : f h ∈ torusGroup TwistTag.E6.tag K :=
    Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hh)
  obtain ⟨n, hn, hnh⟩ := hcl hh'
  have hz : n⁻¹ * h ∈ (Isogeny.e6IsogenyT K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    exact Subtype.ext hnh
  have hz' := center_le_range_minTorus e6Data_valid K isFiniteType_cartan_E6
    (e6Datum_isCTGroupDatum K) (e6Datum_steinbergExtras K) (e6Datum_bruhatExtras K)
    (Isogeny.ker_e6IsogenyT_le_center K hz)
  have := mul_mem hn hz'
  rwa [mul_inv_cancel_left] at this

variable {k : Type} [Field k] [Algebra K k] [CharP k 2] {V W : Type*} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

theorem e6_chi_eq_on_H {ρ₁ : Representation k ↥(e6Data_valid.minGroup K) V}
    {ρ₂ : Representation k ↥(e6Data_valid.minGroup K) W} (hρ₁ : IsSimpleRep ρ₁)
    (hρ₂ : IsSimpleRep ρ₂) {y₁ : V} {y₂ : W} {χ₁ χ₂ : ↥(e6Data_valid.minGroup K) → k}
    {J₁ J₂ : Finset (Fin TwistTag.E6.tag.rank)}
    (ht₁ : IsCoverType (e6CoverRankOne K) ρ₁ y₁ χ₁ J₁)
    (ht₂ : IsCoverType (e6CoverRankOne K) ρ₂ y₂ χ₂ J₂)
    (hd : ∀ i u, χ₁ (e6Data_valid.hm K i u) = χ₂ (e6Data_valid.hm K i u)) :
    ∀ h ∈ (chevDatumLD TwistTag.E6 K 2 e6LongestData).H.comap (Isogeny.e6IsogenyT K),
      χ₁ h = χ₂ h := by
  classical
  obtain ⟨μ₁, hμ₁⟩ := ht₁.exists_mu hρ₁ (e6Cover_split k)
  obtain ⟨μ₂, hμ₂⟩ := ht₂.exists_mu hρ₂ (e6Cover_split k)
  have key : ∀ u : Fin Tag.E6.rank → Kˣ,
      minTorus e6Data_valid K u ∈
        (chevDatumLD TwistTag.E6 K 2 e6LongestData).H.comap (Isogeny.e6IsogenyT K) ∧
      χ₁ (minTorus e6Data_valid K u) = χ₂ (minTorus e6Data_valid K u) := by
    intro u
    induction u using torusVec_induction with
    | h1 =>
      rw [map_one]
      exact ⟨one_mem _, by rw [hμ₁.chi_one, hμ₂.chi_one]⟩
    | hmul t t' ht ht' =>
      rw [map_mul]
      refine ⟨mul_mem ht.1 ht'.1, ?_⟩
      rw [hμ₁.chi_mul ht.1 ht'.1, hμ₂.chi_mul ht.1 ht'.1, ht.2, ht'.2]
    | hsingle j s =>
      rw [minTorus_mulSingle]
      exact ⟨e6_hm_mem_H j s, hd j s⟩
  intro h hh
  obtain ⟨u, rfl⟩ := e6_H_le_range_minTorus hh
  exact (key u).2

end Torus

section Models

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : Type} [Field k] [Algebra K k]
  [CharP k 2] {V : Type*} [AddCommGroup V] [Module k V]

theorem isSimpleRep_pullRep_bc' {τ : Tag} {D : MinData τ} {hV : D.Valid} {G : Type*} [Group G]
    [Finite G] {B : Type*} {M : CoxeterMatrix B} {W : Type*} [Group W] {cs : CoxeterSystem M W}
    (ψ : G →* hV.minGroup K) (D' : CurtisDatum G cs 2) {a₀ : Fin D.d}
    (hψ : Function.Surjective ψ) (hX : ∀ i, ∃ g ∈ D'.U, ψ g = hV.xm K (Pi.single i 1) 1)
    (hdom : ∀ a : Fin D.d, (∀ i, D.wt a i ≠ -1) → a = a₀) {N : ℕ}
    (hN : reachCheck D a₀ N = true) : IsSimpleRep (bcRep k (pullRep hV ψ)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  isSimpleRep_bc D' (pullRep hV ψ) (Finsupp.single a₀ 1)
    (fun h => by
      have := congrArg (fun v : Fin D.d →₀ K => v a₀) h
      simp at this)
    (fixU_le_line hV ψ D' hX hdom)
    (by rw [orbitSpan_pullRep hV ψ hψ]; exact orbitSpan_minRep (hV := hV) hN)

theorem isSimpleRep_bc_e6Rep27' : IsSimpleRep (bcRep k (e6Rep27 K)) :=
  isSimpleRep_pullRep_bc' (MonoidHom.id _) (e6CoverData K).datum Function.surjective_id e6_hX
    e6_dominant e6_reach

theorem e6Rep27_bc_isCoverType' :
    IsCoverType (e6CoverRankOne K) (bcRep k (e6Rep27 K)) (bcVec k (e6Y27 : Fin e6Data.d →₀ K))
      (fun g => algebraMap K k (e6Chi27 g)) (Finset.univ.erase e6n0) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsTypeGen.baseChange (e6CoverData K).datum
    (show IsTypeGen (e6CoverData K).datum (e6Rep27 K) e6Y27 e6Chi27 (Finset.univ.erase e6n0)
      _ (fun s => (K)ˣ) (e6CoverRankOne K).hh from e6Rep27_isCoverType)

theorem isSimpleRep_bc_e6Rep27s' : IsSimpleRep (bcRep k (Min.e6Rep27s K)) :=
  isSimpleRep_pullRep_bc' (Min.e6Graph K) (e6CoverData K).datum
    (fun g => ⟨Min.e6Graph K g, Min.e6Graph_involutive g⟩) Min.e6_hXs e6_dominant e6_reach

theorem e6Rep27s_bc_isCoverType' :
    IsCoverType (e6CoverRankOne K) (bcRep k (Min.e6Rep27s K)) (bcVec k (e6Y27 : Fin e6Data.d →₀ K))
      (fun g => algebraMap K k (Min.e6Chi27s g)) (Finset.univ.erase Min.e6n5) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsTypeGen.baseChange (e6CoverData K).datum
    (show IsTypeGen (e6CoverData K).datum (Min.e6Rep27s K) e6Y27 Min.e6Chi27s (Finset.univ.erase Min.e6n5)
      _ (fun s => (K)ˣ) (e6CoverRankOne K).hh from Min.e6Rep27s_isCoverType)

theorem e6_27_iso_bc {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : ↥(e6Data_valid.minGroup K) → k}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ (Finset.univ.erase e6n0))
    (hχ : ∀ i u, χ (e6Data_valid.hm K i u) = algebraMap K k (e6Chi27 (e6Data_valid.hm K i u))) :
    ∃ β : (k ⊗[K] (Fin e6Data.d →₀ K)) ≃ₗ[k] V, ∀ (g : ↥(e6Data_valid.minGroup K))
      (v : k ⊗[K] (Fin e6Data.d →₀ K)), β (bcRep k (e6Rep27 K) g v) = ρ g (β v) := by
  have hρ₂ := isSimpleRep_bc_e6Rep27' (K := K) (k := k)
  have ht₂ := e6Rep27_bc_isCoverType' (K := K) (k := k)
  have hH := e6_chi_eq_on_H hρ hρ₂ ht ht₂ hχ
  exact e6_iso_of_isCoverType hρ₂ hρ ht₂ (CurtisTw.IsCoverType.congr_H ht hH)

theorem e6_27s_iso_bc {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : ↥(e6Data_valid.minGroup K) → k}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ (Finset.univ.erase Min.e6n5))
    (hχ : ∀ i u, χ (e6Data_valid.hm K i u) = algebraMap K k (Min.e6Chi27s (e6Data_valid.hm K i u))) :
    ∃ β : (k ⊗[K] (Fin e6Data.d →₀ K)) ≃ₗ[k] V, ∀ (g : ↥(e6Data_valid.minGroup K))
      (v : k ⊗[K] (Fin e6Data.d →₀ K)), β (bcRep k (Min.e6Rep27s K) g v) = ρ g (β v) := by
  have hρ₂ := isSimpleRep_bc_e6Rep27s' (K := K) (k := k)
  have ht₂ := e6Rep27s_bc_isCoverType' (K := K) (k := k)
  have hH := e6_chi_eq_on_H hρ hρ₂ ht ht₂ hχ
  exact e6_iso_of_isCoverType hρ₂ hρ ht₂ (CurtisTw.IsCoverType.congr_H ht hH)

end Models

section Bound

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem bound27_K (A : Subgroup ↥(e6Data_valid.minGroup K)) (hne : A ≠ ⊥)
    (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A * Nat.card K ^ Module.finrank K ↥(fixSub (e6Rep27 K) A) < Nat.card K ^ 27 := by
  have h := (FFExc.e6_27_no_offender K A hne hel).1
  have e : FFExc.fixedSub (hV := e6Data_valid) (k := K) A = fixSub (e6Rep27 K) A :=
    Submodule.ext fun v => Iff.rfl
  rw [e, Module.natCard_eq_pow_finrank (K := K) (V := ↥(fixSub (e6Rep27 K) A))] at h
  exact h

theorem bound27s_K (A : Subgroup ↥(e6Data_valid.minGroup K)) (hne : A ≠ ⊥)
    (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A * Nat.card K ^ Module.finrank K ↥(fixSub (Min.e6Rep27s K) A) < Nat.card K ^ 27 := by
  have hinj : Function.Injective (Min.e6Graph K) :=
    Function.LeftInverse.injective (g := Min.e6Graph K) Min.e6Graph_involutive
  have h := bound27_K (A.map (Min.e6Graph K)) (by
      intro h
      exact hne ((Subgroup.map_eq_bot_iff_of_injective A hinj).1 h)) (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hel x hx, map_one])
  have hc : Nat.card (A.map (Min.e6Graph K)) = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ hinj).toEquiv).symm
  have e : fixSub (Min.e6Rep27s K) A = fixSub (e6Rep27 K) (A.map (Min.e6Graph K)) := by
    ext v
    constructor
    · intro hv h hh
      obtain ⟨g, hg, rfl⟩ := hh
      exact hv g hg
    · intro hv g hg
      exact hv _ ⟨g, hg, rfl⟩
  rw [hc] at h
  rw [e]
  exact h

end Bound

section Core

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem e6Surv27_core {k : Type} [Field k] [CharP k 2] [inst₀ : Algebra K k] {V : Type*}
    [AddCommGroup V] [Module k V] {ρ : Representation k ↥(e6Data_valid.minGroup K) V} {y : V}
    {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6} {s : N6} {b : ℕ}
    (hρ : IsSimpleRep ρ) (ht : IsCoverType (e6CoverRankOne K) ρ y χ J)
    (hs : s = ⟨0, by decide⟩ ∨ s = ⟨5, by decide⟩) (hJ : J = Finset.univ.erase s)
    (hχ : ∀ (i : N6) (u : Kˣ), χ (e6Data_valid.hm K i u) =
      if i = s then (@algebraMap K k _ _ inst₀ (u : K)) ^ (2 ^ b) else 1) :
    Module.finrank k V = 27 ∧ ∀ A : Subgroup ↥(e6Data_valid.minGroup K), (∀ a ∈ A, a ^ 2 = 1) →
      A ≠ ⊥ → Nat.card A * Nat.card K ^ Module.finrank k ↥(fixSub ρ A) < Nat.card K ^ 27 := by
  letI alg : Algebra K k := ((algebraMap K k).comp (frobEquiv K b).toRingHom).toAlgebra
  have key : ∀ u : K, algebraMap K k u = (@algebraMap K k _ _ inst₀ u) ^ (2 ^ b) := fun u => by
    show @algebraMap K k _ _ inst₀ (frobEquiv K b u) = _
    rw [frobEquiv_apply, map_pow]
  have hd : Module.finrank K (Fin e6Data.d →₀ K) = 27 := by
    rw [Module.finrank_finsupp_self]
    rfl
  have key2 : ∀ (i : Fin TwistTag.E6.tag.rank) (u : Kˣ),
      (if i = e6n0 then (@algebraMap K k _ _ inst₀ (u : K)) ^ (2 ^ b) else 1) =
        algebraMap K k (e6Chi27 (e6Data_valid.hm K i u)) := by
    intro i u
    rw [e6Chi27_hm, key]
    by_cases h : i = e6n0
    · rw [if_pos h, if_pos h, zpow_one]
    · rw [if_neg h, if_neg h, zpow_zero]
      simp
  have key5 : ∀ (i : Fin TwistTag.E6.tag.rank) (u : Kˣ),
      (if i = Min.e6n5 then (@algebraMap K k _ _ inst₀ (u : K)) ^ (2 ^ b) else 1) =
        algebraMap K k (Min.e6Chi27s (e6Data_valid.hm K i u)) := by
    intro i u
    rw [Min.e6Chi27s_hm, key]
    by_cases h : i = Min.e6n5
    · rw [if_pos h, if_pos h, zpow_one]
    · rw [if_neg h, if_neg h, zpow_zero]
      simp
  rcases hs with rfl | rfl
  · subst hJ
    have hχ' : ∀ i u, χ (e6Data_valid.hm K i u) =
        algebraMap K k (e6Chi27 (e6Data_valid.hm K i u)) := fun i u => (hχ i u).trans (key2 i u)
    obtain ⟨β, hβ⟩ := e6_27_iso_bc hρ ht hχ'
    refine ⟨?_, fun A hA hne => ?_⟩
    · rw [← β.finrank_eq, Module.finrank_baseChange, hd]
    · have h1 := finrank_fixSub_of_iso β hβ A
      have h2 := finrank_fixSub_bcRep_le (K := K) (k := k) (e6Rep27 K) A
      have h3 := bound27_K A hne hA
      have h4 : Nat.card K ^ Module.finrank k ↥(fixSub ρ A) ≤
          Nat.card K ^ Module.finrank K ↥(fixSub (e6Rep27 K) A) :=
        Nat.pow_le_pow_right Nat.card_pos (h1.symm ▸ h2)
      exact lt_of_le_of_lt (Nat.mul_le_mul_left _ h4) h3
  · subst hJ
    have hχ' : ∀ i u, χ (e6Data_valid.hm K i u) =
        algebraMap K k (Min.e6Chi27s (e6Data_valid.hm K i u)) := fun i u => (hχ i u).trans (key5 i u)
    obtain ⟨β, hβ⟩ := e6_27s_iso_bc hρ ht hχ'
    refine ⟨?_, fun A hA hne => ?_⟩
    · rw [← β.finrank_eq, Module.finrank_baseChange, hd]
    · have h1 := finrank_fixSub_of_iso β hβ A
      have h2 := finrank_fixSub_bcRep_le (K := K) (k := k) (Min.e6Rep27s K) A
      have h3 := bound27s_K A hne hA
      have h4 : Nat.card K ^ Module.finrank k ↥(fixSub ρ A) ≤
          Nat.card K ^ Module.finrank K ↥(fixSub (Min.e6Rep27s K) A) :=
        Nat.pow_le_pow_right Nat.card_pos (h1.symm ▸ h2)
      exact lt_of_le_of_lt (Nat.mul_le_mul_left _ h4) h3

end Core

theorem e6Surv27_holds : E6Surv27 := by
  intro K _ _ _ n hn hK k _ _ _ _ m ρ y χ J s b hρ ht hs hb hJ hχ
  obtain ⟨h1, h2⟩ := e6Surv27_core hρ ht hs hJ hχ
  exact ⟨by simpa using h1, h2⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

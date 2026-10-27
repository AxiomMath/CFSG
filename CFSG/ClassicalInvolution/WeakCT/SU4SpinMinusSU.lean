module

public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusRoots
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6Generated
public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusInj

public section

namespace CFSG.ClassicalInvolution.WeakCT.SU4

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CliffordAlgebra QuadraticMap
  CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.Timmesfeld
open scoped Matrix MatrixGroups

section General

variable {K : Type} [Field K]

theorem mem_traceZero_of_eq_neg (σ : K ≃+* K) {x : K} (h : σ x = -x) : x ∈ traceZero σ := by
  rw [mem_traceZero, h, add_neg_cancel]

theorem eq_neg_of_mem_traceZero' (σ : K ≃+* K) {x : K} (hx : x ∈ traceZero σ) : σ x = -x :=
  eq_neg_of_add_eq_zero_right ((mem_traceZero σ).mp hx)

@[expose] noncomputable def sulong (σ : K ≃+* K) (i : Fin 4) (hi : i ≠ Fin.rev i) (x : K)
    (hx : σ x = -x) : SU σ 4 :=
  longRootHom σ hi (Multiplicative.ofAdd ⟨x, mem_traceZero_of_eq_neg σ hx⟩)

theorem coe_sulong (σ : K ≃+* K) (i : Fin 4) (hi : i ≠ Fin.rev i) (x : K) (hx : σ x = -x) :
    (((sulong σ i hi x hx : SU σ 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      longRootMatrix i x := rfl

@[expose] noncomputable def suroot (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c) (i j : Fin 4)
    (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) (x : K) : SU σ 4 :=
  rootHom σ hσ hij hi hj (Multiplicative.ofAdd x)

theorem coe_suroot (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c) (i j : Fin 4) (hij : i ≠ j)
    (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) (x : K) :
    (((suroot σ hσ i j hij hi hj x : SU σ 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      rootMatrix σ i j x := rfl

theorem rootMatrix_rev (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c) (i j : Fin 4) (x : K) :
    rootMatrix σ i j x = rootMatrix σ (Fin.rev j) (Fin.rev i) (-σ x) := by
  unfold rootMatrix
  rw [Fin.rev_rev, Fin.rev_rev, map_neg, hσ, ← Matrix.single_neg, ← Matrix.single_neg]
  abel

theorem sl2_mem_of_tv {k G : Type} [Field k] [Group G] (ρ : SL(2, k) →* G) {H : Subgroup G}
    (h1 : ∀ x, ρ (tv 0 1 x) ∈ H) (h2 : ∀ x, ρ (tv 1 0 x) ∈ H) (g : SL(2, k)) : ρ g ∈ H := by
  have : (⊤ : Subgroup SL(2, k)) ≤ H.comap ρ := by
    rw [← closure_tv_two, Subgroup.closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
    exacts [h1 x, h2 x]
  exact this (Subgroup.mem_top g)

end General

namespace KleinData

variable {F K : Type} [Field F] [Field K] [Algebra F K] {σ₀ : K ≃+* K} {b c : F}
  (D : KleinData F K σ₀ b c)

theorem PhiMon_twShortRoot (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (i : Fin (3 - 1)) (s : Bool)
    (p : Fin 2 → F) :
    D.PhiMon (twShortRoot 3 hirr i s (.ofAdd p)) =
      1 + D.Xmat (planeVec 3 p) * D.Hs (D.Xmat (minusVec 3 i s)) := by
  have h : ((twShortRoot 3 hirr i s (.ofAdd p) : spinGroup (quadMinus 3 F b c)) :
      CliffordAlgebra (quadMinus 3 F b c)) = 1 + (1 : F) •
        (ι (quadMinus 3 F b c) (planeVec 3 p) * ι (quadMinus 3 F b c) (minusVec 3 i s)) := by
    rw [coe_twShortRoot, one_smul]
  rw [D.PhiMon_of_coe_eq h, one_smul]

theorem PhiMon_longRoot {i j : Fin (3 - 1)} (hij : i ≠ j) (s t : Bool) (x : F) :
    D.PhiMon ((minusFrame 3 b c).longRoot hij s t (.ofAdd x)) =
      1 + x • (D.Xmat (minusVec 3 i s) * D.Hs (D.Xmat (minusVec 3 j t))) :=
  D.PhiMon_of_coe_eq (by rw [HypFrame.coe_longRoot]; rfl)

theorem PhiMon_long_e0f1 (x : F) :
    D.PhiMon ((minusFrame 3 b c).longRoot fin_zero_ne_one true false (.ofAdd x)) =
      longRootMatrix (1 : Fin 4) (algebraMap F K x * D.ε) := by
  rw [PhiMon_longRoot]
  exact D.long_e0f1 x

theorem PhiMon_long_e1f0 (x : F) :
    D.PhiMon ((minusFrame 3 b c).longRoot fin_zero_ne_one.symm true false (.ofAdd x)) =
      longRootMatrix (2 : Fin 4) (algebraMap F K x * D.δ) := by
  rw [PhiMon_longRoot]
  exact D.long_e1f0 x

theorem PhiMon_long_e0e1 (x : F) :
    D.PhiMon ((minusFrame 3 b c).longRoot fin_zero_ne_one true true (.ofAdd x)) =
      longRootMatrix (0 : Fin 4) (algebraMap F K x * D.δ) := by
  rw [PhiMon_longRoot]
  exact D.long_e0e1 x

theorem PhiMon_long_f0f1 (x : F) :
    D.PhiMon ((minusFrame 3 b c).longRoot fin_zero_ne_one false false (.ofAdd x)) =
      longRootMatrix (3 : Fin 4) (-(algebraMap F K x * D.ε)) := by
  rw [PhiMon_longRoot]
  exact D.long_f0f1 x

theorem PhiMon_short_e1 (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (p : Fin 2 → F) :
    D.PhiMon (twShortRoot 3 hirr iO true (.ofAdd p)) =
      rootMatrix σ₀ (0 : Fin 4) 1
        (-(D.δ * (algebraMap F K (p 0) - algebraMap F K (p 1) * D.ω))) := by
  rw [PhiMon_twShortRoot]
  exact D.short_e1 p

theorem PhiMon_short_f1 (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (p : Fin 2 → F) :
    D.PhiMon (twShortRoot 3 hirr iO false (.ofAdd p)) =
      rootMatrix σ₀ (1 : Fin 4) 0
        (D.ε * (algebraMap F K (p 0) + algebraMap F K (p 1) * algebraMap F K b +
          algebraMap F K (p 1) * D.ω)) := by
  rw [PhiMon_twShortRoot]
  exact D.short_f1 p

theorem PhiMon_short_e0 (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (p : Fin 2 → F) :
    D.PhiMon (twShortRoot 3 hirr iZ true (.ofAdd p)) =
      rootMatrix σ₀ (0 : Fin 4) 2 (algebraMap F K (p 0) - algebraMap F K (p 1) * D.ω) := by
  rw [PhiMon_twShortRoot]
  exact D.short_e0 p

theorem PhiMon_short_f0 (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (p : Fin 2 → F) :
    D.PhiMon (twShortRoot 3 hirr iZ false (.ofAdd p)) =
      rootMatrix σ₀ (3 : Fin 4) 1 (algebraMap F K (p 0) - algebraMap F K (p 1) * D.ω) := by
  rw [PhiMon_twShortRoot]
  exact D.short_f0 p

@[expose] noncomputable def PhiGL : spinGroup (quadMinus 3 F b c) →* GL (Fin 4) K :=
  D.PhiMon.toHomUnits

theorem coe_PhiGL (s : spinGroup (quadMinus 3 F b c)) :
    ((D.PhiGL s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = D.PhiMon s := rfl

theorem σ_ε_mul {r : F} : σ₀ (algebraMap F K r * D.ε) = -(algebraMap F K r * D.ε) := by
  rw [map_mul, D.σ_alg, D.σ_ε]
  ring

theorem σ_δ_mul {r : F} : σ₀ (algebraMap F K r * D.δ) = -(algebraMap F K r * D.δ) := by
  rw [map_mul, D.σ_alg, D.σ_δ]
  ring

theorem PhiGL_eq_of_coe {s : spinGroup (quadMinus 3 F b c)} {g : SU σ₀ 4}
    (h : D.PhiMon s = ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    D.PhiGL s = (g : GL (Fin 4) K) :=
  Units.ext h

theorem PhiGL_mem_SU [Finite F] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : F) ≠ 0)
    (s : spinGroup (quadMinus 3 F b c)) : D.PhiGL s ∈ SU σ₀ 4 := by
  have := fact_shortField hirr
  have hlb : (spinMinusModel hirr).lb.range ≤ (SU σ₀ 4).comap D.PhiGL := by
    rintro _ ⟨A, rfl⟩
    refine sl2_mem_of_tv (D.PhiGL.comp (minusLongBlock b c)) (H := SU σ₀ 4) (fun x => ?_)
      (fun x => ?_) A
    · show D.PhiGL (minusLongBlock b c (tv 0 1 x)) ∈ SU σ₀ 4
      rw [minusLongBlock_tv01,
        D.PhiGL_eq_of_coe (g := sulong σ₀ 1 (by decide) (algebraMap F K x * D.ε) D.σ_ε_mul)
          (D.PhiMon_long_e0f1 x)]
      exact (sulong σ₀ 1 (by decide) (algebraMap F K x * D.ε) D.σ_ε_mul).2
    · show D.PhiGL (minusLongBlock b c (tv 1 0 x)) ∈ SU σ₀ 4
      rw [minusLongBlock_tv10,
        D.PhiGL_eq_of_coe (g := sulong σ₀ 2 (by decide) (algebraMap F K x * D.δ) D.σ_δ_mul)
          (D.PhiMon_long_e1f0 x)]
      exact (sulong σ₀ 2 (by decide) (algebraMap F K x * D.δ) D.σ_δ_mul).2
  have hsb : (spinMinusModel hirr).sb.range ≤ (SU σ₀ 4).comap D.PhiGL := by
    rintro _ ⟨B, rfl⟩
    refine sl2_mem_of_tv (D.PhiGL.comp (shortBlock hirr 3 finOne)) (H := SU σ₀ 4) (fun t => ?_)
      (fun t => ?_) B
    · show D.PhiGL (shortBlock hirr 3 finOne (tv 0 1 t)) ∈ SU σ₀ 4
      rw [shortBlock_tv01]
      change D.PhiGL (twShortRoot 3 hirr iO true (.ofAdd (fieldCoord t))) ∈ SU σ₀ 4
      rw [D.PhiGL_eq_of_coe (g := suroot σ₀ D.σσ 0 1 (by decide) (by decide) (by decide)
          (-(D.δ * (algebraMap F K (fieldCoord t 0) - algebraMap F K (fieldCoord t 1) * D.ω))))
          (D.PhiMon_short_e1 hirr (fieldCoord t))]
      exact (suroot σ₀ D.σσ 0 1 (by decide) (by decide) (by decide) _).2
    · show D.PhiGL (shortBlock hirr 3 finOne (tv 1 0 t)) ∈ SU σ₀ 4
      rw [shortBlock_tv10]
      change D.PhiGL (twShortRoot 3 hirr iO false (.ofAdd (starCoord t))) ∈ SU σ₀ 4
      rw [D.PhiGL_eq_of_coe (g := suroot σ₀ D.σσ 1 0 (by decide) (by decide) (by decide)
          (D.ε * (algebraMap F K (starCoord t 0) + algebraMap F K (starCoord t 1) *
            algebraMap F K b + algebraMap F K (starCoord t 1) * D.ω)))
          (D.PhiMon_short_f1 hirr (starCoord t))]
      exact (suroot σ₀ D.σσ 1 0 (by decide) (by decide) (by decide) _).2
  have htop : (SU σ₀ 4).comap D.PhiGL = ⊤ := by
    rw [eq_top_iff, ← spinMinusModel_blocks_sup_eq_top hirr h2]
    exact sup_le hlb hsb
  have hs : s ∈ (SU σ₀ 4).comap D.PhiGL := by
    rw [htop]
    exact Subgroup.mem_top s
  exact hs

@[expose] noncomputable def PhiSU [Finite F] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (h2 : (2 : F) ≠ 0) : spinGroup (quadMinus 3 F b c) →* SU σ₀ 4 :=
  D.PhiGL.codRestrict (SU σ₀ 4) (D.PhiGL_mem_SU hirr h2)

theorem coe_PhiSU [Finite F] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : F) ≠ 0)
    (s : spinGroup (quadMinus 3 F b c)) :
    (((D.PhiSU hirr h2 s : SU σ₀ 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = D.PhiMon s :=
  rfl

theorem PhiSU_injective [Finite F] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : F) ≠ 0) :
    Function.Injective (D.PhiSU hirr h2) := by
  intro s t h
  apply D.PhiMon_injective hirr
  rw [← coe_PhiSU D hirr h2, ← coe_PhiSU D hirr h2, h]

theorem mem_range_PhiSU [Finite F] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : F) ≠ 0)
    {g : SU σ₀ 4} {s : spinGroup (quadMinus 3 F b c)}
    (h : D.PhiMon s = ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    g ∈ (D.PhiSU hirr h2).range :=
  ⟨s, Subtype.ext (Units.ext h)⟩

include D in
theorem exists_algebraMap_eq_of_σ_eq {y : K} (hy : σ₀ y = y) : ∃ r : F, algebraMap F K r = y := by
  obtain ⟨u, v, rfl⟩ := D.span y
  rw [D.σ_sub_mul] at hy
  have h1 : algebraMap F K v * D.δ = 0 := by
    unfold δ
    linear_combination hy
  have hv : algebraMap F K v = 0 := (mul_eq_zero.mp h1).resolve_right D.δ_ne_zero
  exact ⟨u, by rw [hv, zero_mul, sub_zero]⟩

section RangeLong

variable [Finite F] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : F) ≠ 0)

include hirr h2 in
theorem longRootHom_zero_mem_range (hi : (0 : Fin 4) ≠ Fin.rev 0)
    (x : Multiplicative (traceZero σ₀)) : longRootHom σ₀ hi x ∈ (D.PhiSU hirr h2).range := by
  have hc := eq_neg_of_mem_traceZero' σ₀ x.toAdd.2
  obtain ⟨r, hr⟩ := D.exists_algebraMap_eq_of_σ_eq (y := (x.toAdd : K) * D.ε)
    (by rw [map_mul, hc, D.σ_ε]; ring)
  refine D.mem_range_PhiSU hirr h2
    (s := (minusFrame 3 b c).longRoot fin_zero_ne_one true true (.ofAdd r)) ?_
  rw [D.PhiMon_long_e0e1, hr]
  show longRootMatrix (0 : Fin 4) (↑x.toAdd * D.ε * D.δ) = longRootMatrix (0 : Fin 4) ↑x.toAdd
  rw [mul_assoc, mul_comm D.ε, D.δ_mul_ε, mul_one]

include hirr h2 in
theorem longRootHom_one_mem_range (hi : (1 : Fin 4) ≠ Fin.rev 1)
    (x : Multiplicative (traceZero σ₀)) : longRootHom σ₀ hi x ∈ (D.PhiSU hirr h2).range := by
  have hc := eq_neg_of_mem_traceZero' σ₀ x.toAdd.2
  obtain ⟨r, hr⟩ := D.exists_algebraMap_eq_of_σ_eq (y := (x.toAdd : K) * D.δ)
    (by rw [map_mul, hc, D.σ_δ]; ring)
  refine D.mem_range_PhiSU hirr h2
    (s := (minusFrame 3 b c).longRoot fin_zero_ne_one true false (.ofAdd r)) ?_
  rw [D.PhiMon_long_e0f1, hr]
  show longRootMatrix (1 : Fin 4) (↑x.toAdd * D.δ * D.ε) = longRootMatrix (1 : Fin 4) ↑x.toAdd
  rw [mul_assoc, D.δ_mul_ε, mul_one]

include hirr h2 in
theorem longRootHom_two_mem_range (hi : (2 : Fin 4) ≠ Fin.rev 2)
    (x : Multiplicative (traceZero σ₀)) : longRootHom σ₀ hi x ∈ (D.PhiSU hirr h2).range := by
  have hc := eq_neg_of_mem_traceZero' σ₀ x.toAdd.2
  obtain ⟨r, hr⟩ := D.exists_algebraMap_eq_of_σ_eq (y := (x.toAdd : K) * D.ε)
    (by rw [map_mul, hc, D.σ_ε]; ring)
  refine D.mem_range_PhiSU hirr h2
    (s := (minusFrame 3 b c).longRoot fin_zero_ne_one.symm true false (.ofAdd r)) ?_
  rw [D.PhiMon_long_e1f0, hr]
  show longRootMatrix (2 : Fin 4) (↑x.toAdd * D.ε * D.δ) = longRootMatrix (2 : Fin 4) ↑x.toAdd
  rw [mul_assoc, mul_comm D.ε, D.δ_mul_ε, mul_one]

include hirr h2 in
theorem longRootHom_three_mem_range (hi : (3 : Fin 4) ≠ Fin.rev 3)
    (x : Multiplicative (traceZero σ₀)) : longRootHom σ₀ hi x ∈ (D.PhiSU hirr h2).range := by
  have hc := eq_neg_of_mem_traceZero' σ₀ x.toAdd.2
  obtain ⟨r, hr⟩ := D.exists_algebraMap_eq_of_σ_eq (y := -((x.toAdd : K) * D.δ))
    (by rw [map_neg, map_mul, hc, D.σ_δ]; ring)
  refine D.mem_range_PhiSU hirr h2
    (s := (minusFrame 3 b c).longRoot fin_zero_ne_one false false (.ofAdd r)) ?_
  rw [D.PhiMon_long_f0f1, hr]
  show longRootMatrix (3 : Fin 4) (-(-(↑x.toAdd * D.δ) * D.ε)) = longRootMatrix (3 : Fin 4) ↑x.toAdd
  rw [neg_mul, neg_neg, mul_assoc, D.δ_mul_ε, mul_one]

include hirr h2 in
theorem longRootHom_mem_range_PhiSU (i : Fin 4) (hi : i ≠ Fin.rev i)
    (x : Multiplicative (traceZero σ₀)) : longRootHom σ₀ hi x ∈ (D.PhiSU hirr h2).range := by
  fin_cases i
  · exact D.longRootHom_zero_mem_range hirr h2 hi x
  · exact D.longRootHom_one_mem_range hirr h2 hi x
  · exact D.longRootHom_two_mem_range hirr h2 hi x
  · exact D.longRootHom_three_mem_range hirr h2 hi x

end RangeLong

section RangeShort

variable (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

@[expose] def Rm (i j : Fin 4) (x : K) : Prop :=
  ∃ s : spinGroup (quadMinus 3 F b c), D.PhiMon s = rootMatrix σ₀ i j x

theorem Rm_rev {i j : Fin 4} {x : K} (h : D.Rm (Fin.rev j) (Fin.rev i) (-σ₀ x)) : D.Rm i j x := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, by rw [hs, rootMatrix_rev σ₀ D.σσ i j x]⟩

include hirr in
theorem Rm_zero_one (x : K) : D.Rm (0 : Fin 4) 1 x := by
  obtain ⟨u, v, huv⟩ := D.span (-(x * D.ε))
  refine ⟨twShortRoot 3 hirr iO true (.ofAdd ![u, v]), ?_⟩
  rw [D.PhiMon_short_e1]
  have h : algebraMap F K (![u, v] 0) - algebraMap F K (![u, v] 1) * D.ω = -(x * D.ε) := by
    simpa using huv.symm
  rw [h]
  congr 1
  linear_combination x * D.δ_mul_ε

include hirr in
theorem Rm_one_zero (x : K) : D.Rm (1 : Fin 4) 0 x := by
  obtain ⟨u, v, huv⟩ := D.span (σ₀ (x * D.δ))
  refine ⟨twShortRoot 3 hirr iO false (.ofAdd ![u, v]), ?_⟩
  rw [D.PhiMon_short_f1]
  have h : algebraMap F K (![u, v] 0) + algebraMap F K (![u, v] 1) * algebraMap F K b +
      algebraMap F K (![u, v] 1) * D.ω = x * D.δ := by
    have h1 : algebraMap F K u + algebraMap F K v * algebraMap F K b +
        algebraMap F K v * D.ω = σ₀ (algebraMap F K u - algebraMap F K v * D.ω) :=
      (D.σ_sub_mul u v).symm
    simp [h1, ← huv, D.σσ]
  rw [h]
  congr 1
  linear_combination x * D.δ_mul_ε

include hirr in
theorem Rm_zero_two (x : K) : D.Rm (0 : Fin 4) 2 x := by
  obtain ⟨u, v, huv⟩ := D.span x
  refine ⟨twShortRoot 3 hirr iZ true (.ofAdd ![u, v]), ?_⟩
  rw [D.PhiMon_short_e0]
  have h : algebraMap F K (![u, v] 0) - algebraMap F K (![u, v] 1) * D.ω = x := by
    simpa using huv.symm
  rw [h]

include hirr in
theorem Rm_three_one (x : K) : D.Rm (3 : Fin 4) 1 x := by
  obtain ⟨u, v, huv⟩ := D.span x
  refine ⟨twShortRoot 3 hirr iZ false (.ofAdd ![u, v]), ?_⟩
  rw [D.PhiMon_short_f0]
  have h : algebraMap F K (![u, v] 0) - algebraMap F K (![u, v] 1) * D.ω = x := by
    simpa using huv.symm
  rw [h]

end RangeShort

section RangeShortAll

variable [Finite F] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : F) ≠ 0)

include hirr h2 in
theorem rootHom_mem_range_PhiSU (i j : Fin 4) (hij : i ≠ j) (hi : i ≠ Fin.rev i)
    (hj : j ≠ Fin.rev j) (hji : j ≠ Fin.rev i) (x : Multiplicative K) :
    rootHom σ₀ D.σσ hij hi hj x ∈ (D.PhiSU hirr h2).range := by
  have key : ∀ y : K, D.Rm i j y → rootHom σ₀ D.σσ hij hi hj (Multiplicative.ofAdd y) ∈
      (D.PhiSU hirr h2).range := fun y ⟨s, hs⟩ => D.mem_range_PhiSU hirr h2 hs
  have hx : x = Multiplicative.ofAdd x.toAdd := rfl
  rw [hx]
  apply key
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact D.Rm_zero_one hirr _
  · exact D.Rm_zero_two hirr _
  · exact absurd rfl hji
  · exact D.Rm_one_zero hirr _
  · exact absurd rfl hij
  · exact absurd rfl hji
  · exact D.Rm_rev (D.Rm_zero_two hirr _)
  · exact D.Rm_rev (D.Rm_three_one hirr _)
  · exact absurd rfl hji
  · exact absurd rfl hij
  · exact D.Rm_rev (D.Rm_zero_one hirr _)
  · exact absurd rfl hji
  · exact D.Rm_three_one hirr _
  · exact D.Rm_rev (D.Rm_one_zero hirr _)
  · exact absurd rfl hij

end RangeShortAll

end KleinData

end CFSG.ClassicalInvolution.WeakCT.SU4

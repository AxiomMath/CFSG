module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25
public import CFSG.CGT.PushingUpLit.SolKNA.R4.QuatOddAut
public import CFSG.ClassicalInvolution.SmallCases.A7T22H51
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecDatum

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Inner
open scoped commutatorElement

namespace Perp22

section OddAut

theorem mulAut_eq_one_of_odd_of_equiv {A : Type*} [Group A] {k : ℕ} (hk : 2 ≤ k)
    (e : A ≃* QuaternionGroup (2 ^ k)) (ψ : MulAut A) (hψ : Odd (orderOf ψ)) : ψ = 1 := by
  have h1 : orderOf (MulAut.congr e ψ) = orderOf ψ :=
    orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective ψ
  have h2 := QuaternionGroup.mulAut_eq_one_of_odd hk (MulAut.congr e ψ) (by rwa [h1])
  exact (MulAut.congr e).injective (by rw [h2, map_one])

variable {G : Type} [Group G] [Finite G]

@[expose] def conjAutOfNormalizer (J : Subgroup G) {x : G}
    (hx : x ∈ Subgroup.normalizer (J : Set G)) : ↥J ≃* ↥J where
  toFun y := ⟨x * y * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx y).mp y.2⟩
  invFun y := ⟨x⁻¹ * y * x⁻¹⁻¹,
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) y).mp y.2⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' y z := Subtype.ext (by simp [mul_assoc])

@[expose] noncomputable def actQuot (J : Subgroup G) :
    ↥(Subgroup.normalizer (J : Set G)) →* MulAut (↥J ⧸ classicalInvolutionOddCore ↥J) where
  toFun x := QuotientGroup.congr _ _ (conjAutOfNormalizer J x.2)
    (CFSG.ComponentClassification.OddCore.equiv_invariant _)
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H y => exact congrArg QuotientGroup.mk (Subtype.ext (by simp [conjAutOfNormalizer]))
  map_mul' a b := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H y => exact congrArg QuotientGroup.mk (Subtype.ext (by simp [conjAutOfNormalizer, mul_assoc]))

theorem actQuot_apply_mk (J : Subgroup G) (x : ↥(Subgroup.normalizer (J : Set G))) (y : ↥J) :
    actQuot J x (QuotientGroup.mk y) =
      QuotientGroup.mk (⟨(x : G) * y * (x : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp x.2 y).mp y.2⟩ : ↥J) := rfl

theorem mem_trivialOnQuot_of_odd {k : ℕ} (hk : 2 ≤ k) {J : Subgroup G}
    (e : (↥J ⧸ classicalInvolutionOddCore ↥J) ≃* QuaternionGroup (2 ^ k)) {x : G}
    (hx : x ∈ Subgroup.normalizer (J : Set G)) (hodd : Odd (orderOf x)) :
    x ∈ Balance.Bootstrap.trivialOnQuot J := by
  refine ⟨hx, fun y hy => ?_⟩
  have hord : orderOf (actQuot J ⟨x, hx⟩) ∣ orderOf x := by
    have := orderOf_map_dvd (actQuot J) (⟨x, hx⟩ : ↥(Subgroup.normalizer (J : Set G)))
    rwa [Subgroup.orderOf_mk] at this
  have h1 : actQuot J ⟨x, hx⟩ = 1 :=
    mulAut_eq_one_of_odd_of_equiv hk e _ (Odd.of_dvd_nat hodd hord)
  have h2 : actQuot J ⟨x, hx⟩ (QuotientGroup.mk ⟨y, hy⟩) = QuotientGroup.mk ⟨y, hy⟩ := by
    rw [h1]; rfl
  rw [actQuot_apply_mk] at h2
  have h3 := QuotientGroup.eq_iff_div_mem.mp h2
  refine Subgroup.mem_map.mpr ⟨_, h3, ?_⟩
  simp [commutatorElement_def, div_eq_mul_inv]

end OddAut

end Perp22

namespace Perp22

section Datum

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

theorem orderOf_mul_z {z u : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) (hu2 : u * u = z)
    (hc : z * u = u * z) : orderOf (u * z) = 4 := by
  have h2 : (u * z) ^ 2 = z := by
    rw [pow_two]
    calc (u * z) * (u * z) = u * (z * u) * z := by group
      _ = u * (u * z) * z := by rw [hc]
      _ = (u * u) * (z * z) := by group
      _ = z := by rw [hu2, hz2, mul_one]
  have h4 : (u * z) ^ 4 = 1 := by
    calc (u * z) ^ 4 = ((u * z) ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [h2, pow_two, hz2]
  have h1 : ¬ (u * z) ^ (2 ^ 1) = 1 := by
    rw [pow_one, h2]
    exact hz1
  have := orderOf_eq_prime_pow (p := 2) (n := 1) h1 (by simpa using h4)
  simpa using this

theorem hyp22G_mulZ₂ (h : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    A7T22.Hyp22G Ω K K' K₃ z u₁ (u₂ * z) u₃ := by
  have hu2 : (u₂ * z) ∈ K' := K'.mul_mem h.hu₂.1 h.hzK'.mem
  refine A7T22.Hyp22G.of_core
    { hyp := h.hyp
      memK := h.mem
      memK' := h.hK'.1
      memK₃ := h.hK₃.1
      hz := h.hz
      hz' := h.hzK'
      hz₃ := h.hzK₃
      ne₁₂ := h.hne
      ne₁₃ := h.hK₃K
      ne₂₃ := h.hK₃K'
      hu₁ := h.hu₁
      hu₂ := ⟨hu2, orderOf_mul_z h.hz.sq h.hz.ne_one h.sq₂ h.comm_z₂⟩
      hu₃ := h.hu₃
      c₁₂ := by
        calc u₁ * (u₂ * z) = (u₁ * u₂) * z := by group
          _ = (u₂ * u₁) * z := by rw [h.comm₁₂]
          _ = u₂ * (z * u₁) := by rw [h.comm_z₁]; group
          _ = (u₂ * z) * u₁ := by group
      c₁₃ := h.comm₁₃
      c₂₃ := by
        calc (u₂ * z) * u₃ = u₂ * (z * u₃) := by group
          _ = u₂ * (u₃ * z) := by rw [h.comm_z₃]
          _ = (u₂ * u₃) * z := by group
          _ = (u₃ * u₂) * z := by rw [h.comm₂₃]
          _ = u₃ * (u₂ * z) := by group } h.subn

theorem exists_datum_of_mem_B (h : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) {c : G}
    (hc : c ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) (hc1 : c ≠ 1) (hcz : c ≠ z) :
    ∃ (L L' L₃ : Subgroup G) (x y w : G), A7T22.Hyp22G Ω L L' L₃ z x y w ∧ c = x * y := by
  rcases h.mem_B_cases hc with e | e | e | e | e | e | e | e
  · exact absurd e hc1
  · exact ⟨K, K', K₃, u₁, u₂, u₃, h, e⟩
  · exact absurd e hcz
  · exact ⟨K', K₃, K, u₂, u₃, u₁, h.rotate, e⟩
  · exact ⟨K, K', K₃, u₁, u₂ * z, u₃, hyp22G_mulZ₂ h, by rw [e]; group⟩
  · refine ⟨K₃, K, K', u₃, u₁ * z, u₂, hyp22G_mulZ₂ h.rotate.rotate, ?_⟩
    rw [e]
    calc u₁ * u₂ * (u₂ * u₃) = u₁ * (u₂ * u₂) * u₃ := by group
      _ = u₁ * z * u₃ := by rw [h.sq₂]
      _ = u₁ * (z * u₃) := by group
      _ = u₁ * (u₃ * z) := by rw [h.comm_z₃]
      _ = (u₁ * u₃) * z := by group
      _ = (u₃ * u₁) * z := by rw [h.comm₁₃]
      _ = u₃ * (u₁ * z) := by group
  · refine ⟨K', K₃, K, u₂, u₃ * z, u₁, hyp22G_mulZ₂ h.rotate, ?_⟩
    rw [e]
    calc z * (u₂ * u₃) = (z * u₂) * u₃ := by group
      _ = (u₂ * z) * u₃ := by rw [h.comm_z₂]
      _ = u₂ * (z * u₃) := by group
      _ = u₂ * (u₃ * z) := by rw [h.comm_z₃]
      _ = u₂ * (u₃ * z) := rfl
  · refine ⟨K₃, K, K', u₃, u₁, u₂, h.rotate.rotate, ?_⟩
    rw [e, ← h.comm₁₃]
    calc u₁ * u₂ * z * (u₂ * u₃) = u₁ * (u₂ * z) * (u₂ * u₃) := by group
      _ = u₁ * (z * u₂) * (u₂ * u₃) := by rw [h.comm_z₂]
      _ = u₁ * z * (u₂ * u₂) * u₃ := by group
      _ = u₁ * z * z * u₃ := by rw [h.sq₂]
      _ = u₁ * u₃ := by rw [mul_assoc u₁ z z, h.hz.sq, mul_one]

end Datum

end Perp22

section Standing

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem PerpHypR.exists_hyp22G (h : PerpHypR r n Y R S t) (h3 : ¬ TwinPerp.TwoTwins R) :
    ∃ (K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y),
      A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' K₃ t u₁ u₂ u₃ := by
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core h.core.datum
  obtain ⟨K', hK', hne⟩ := h.core.twin
  have hne2 : KPerp (CoreAssembly.conjClass (tightCore R)) (tightCore R) ≠
      {tightCore R, K'} := fun hP => h3 (TwinPerp.twoTwins_of_eq_pair (h.perp.symm.trans hP))
  obtain ⟨K₃, u₁, u₂, u₃, -, hd⟩ := A7T22.exists_hyp22Core_of_perp h.core.hyp
    (CoreAssembly.mem_conjClass_self _) hU hK' hne h.perp hne2
  exact ⟨K', K₃, u₁, u₂, u₃, A7T22.Hyp22G.of_core hd fun L hL =>
    isSubnormal_of_hypOmegaGen h.core.hyp hL.1 (isUniqueInvolution_of_mem_twinSet hU hL)⟩

theorem PerpHypR.kPerp_datum (h : PerpHypR r n Y R S t) {K : Subgroup Y}
    (hK : K ∈ CoreAssembly.conjClass (tightCore R)) (hz : IsUniqueInvolution K t) :
    KPerp (CoreAssembly.conjClass (tightCore R)) K =
      twinSet (CoreAssembly.conjClass (tightCore R)) K := by
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core h.core.datum
  have hKt : K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := ⟨hK, t, hU, hz⟩
  have e1 := A7T22.kPerp_eq_of_twin h.core.hyp (CoreAssembly.mem_conjClass_self _) hKt
  have e2 : twinSet (CoreAssembly.conjClass (tightCore R)) K =
      twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    ext J
    constructor
    · rintro ⟨hJ, z, hzK, hzJ⟩
      exact ⟨hJ, z, (hzK.eq hz) ▸ hU, hzJ⟩
    · rintro ⟨hJ, z, hzK, hzJ⟩
      exact ⟨hJ, z, (hzK.eq hU) ▸ hz, hzJ⟩
  rw [e1, e2]
  exact h.perp

theorem PerpHypR.quotEquiv_core (h : PerpHypR r n Y R S t) :
    Nonempty (↥(tightCore R) ⧸ classicalInvolutionOddCore ↥(tightCore R) ≃*
      QuaternionGroup (2 ^ (r - 2))) := by
  have h2 : IsPGroup 2 (↥(tightCore R) ⧸ classicalInvolutionOddCore ↥(tightCore R)) :=
    TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) h.core.datum.twoGroup
  obtain ⟨e1⟩ := QuaternionStructure.nonempty_mulEquiv_sylow_of_isPGroup_oddCore_quotient h2
    (TwinEdge.sylowOf h.core.datum.sylow_core)
  obtain ⟨eq⟩ := h.core.quat
  have hle : (S : Subgroup R).map R.subtype ≤ tightCore R := h.core.datum.sylow_core.1
  let e2 : ↥((TwinEdge.sylowOf h.core.datum.sylow_core : Sylow 2 ↥(tightCore R)) :
      Subgroup ↥(tightCore R)) ≃* ↥((S : Subgroup R).map R.subtype) :=
    Subgroup.subgroupOfEquivOfLe hle
  let e3 : ↥((S : Subgroup R).map R.subtype) ≃* ↥(S : Subgroup R) :=
    (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm
  exact ⟨e1.trans (e2.trans (e3.trans eq))⟩

theorem PerpHypR.exists_centralizer_conj (h : PerpHypR r n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    ∃ c ∈ Subgroup.centralizer ({t} : Set Y), conjSub c (tightCore R) = J := by
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core h.core.datum
  obtain ⟨g, hg⟩ := hJ.1
  have hzJ : IsUniqueInvolution J t := isUniqueInvolution_of_mem_twinSet hU hJ
  have h1 : IsUniqueInvolution J (g * t * g⁻¹) := hg ▸ hU.conj g
  have h2 : g * t * g⁻¹ = t := h1.eq hzJ
  refine ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr ?_, hg⟩
  calc g * t = (g * t * g⁻¹) * g := by group
    _ = t * g := by rw [h2]

theorem PerpHypR.conj_mem_twinSet (h : PerpHypR r n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) :
    conjSub c J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core h.core.datum
  have hct : c * t * c⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * t * c⁻¹ = (t * c) * c⁻¹ := by rw [this]
      _ = t := by group
  obtain ⟨hJΩ, z, hzK, hzJ⟩ := hJ
  refine ⟨h.core.hyp.conjInvariant c J hJΩ, t, hU, ?_⟩
  have hz : z = t := (hU.eq hzK).symm
  subst hz
  have := hzJ.conj c
  rwa [hct] at this

theorem PerpHypR.card_twinSet (h : PerpHypR r n Y R S t) :
    Nat.card (twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)) =
      ((Subgroup.centralizer ({t} : Set Y)) ⊓
        Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y)).relIndex
        (Subgroup.centralizer ({t} : Set Y)) := by
  set C := Subgroup.centralizer ({t} : Set Y) with hC
  set K₀ := tightCore R with hK₀
  have hU : IsUniqueInvolution K₀ t := Inner.isUniqueInvolution_core h.core.datum
  have hself : K₀ ∈ twinSet (CoreAssembly.conjClass K₀) K₀ :=
    mem_twinSet_self (CoreAssembly.mem_conjClass_self _) hU
  let f : ↥C → ↥(twinSet (CoreAssembly.conjClass K₀) K₀) := fun c =>
    ⟨conjSub (c : Y) K₀, h.conj_mem_twinSet hself c.2⟩
  have hrel : ∀ a b : ↥C, f a = f b ↔
      a⁻¹ * b ∈ ((C ⊓ Subgroup.normalizer (K₀ : Set Y)).subgroupOf C) := by
    intro a b
    have hfab : f a = f b ↔ conjSub (a : Y) K₀ = conjSub (b : Y) K₀ :=
      ⟨fun hh => congrArg Subtype.val hh, fun hh => Subtype.ext hh⟩
    have e3 : conjSub ((a⁻¹ * b : ↥C) : Y) K₀ = conjSub ((a : Y)⁻¹) (conjSub (b : Y) K₀) := by
      have : ((a⁻¹ * b : ↥C) : Y) = (a : Y)⁻¹ * (b : Y) := by simp
      rw [this, conjSub_mul]
    have e : conjSub (a : Y) K₀ = conjSub (b : Y) K₀ ↔ conjSub ((a⁻¹ * b : ↥C) : Y) K₀ = K₀ := by
      rw [e3]
      constructor
      · intro hh
        rw [← hh, conjSub_inv_conjSub]
      · intro hh
        have h1 := congrArg (conjSub (a : Y)) hh
        rw [conjSub_conjSub_inv] at h1
        exact h1.symm
    rw [hfab, e, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hh
      exact ⟨(a⁻¹ * b).2, mem_normalizer_iff_conjSub_eq.mpr hh⟩
    · intro hh
      exact mem_normalizer_iff_conjSub_eq.mp hh.2
  let g : (↥C ⧸ (C ⊓ Subgroup.normalizer (K₀ : Set Y)).subgroupOf C) →
      ↥(twinSet (CoreAssembly.conjClass K₀) K₀) :=
    Quotient.lift f fun a b hab => (hrel a b).mpr (QuotientGroup.leftRel_apply.mp hab)
  have hg : Function.Bijective g := by
    constructor
    · intro x y
      induction x using Quotient.inductionOn with | _ a => ?_
      induction y using Quotient.inductionOn with | _ b => ?_
      intro hxy
      exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hrel a b).mp hxy))
    · rintro ⟨J, hJ⟩
      obtain ⟨c, hc, hcJ⟩ := h.exists_centralizer_conj hJ
      exact ⟨Quotient.mk _ ⟨c, hc⟩, Subtype.ext hcJ⟩
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_congr (Equiv.ofBijective g hg)]

theorem PerpHypR.quotEquiv (h : PerpHypR r n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ CoreAssembly.conjClass (tightCore R)) :
    Nonempty (↥J ⧸ classicalInvolutionOddCore ↥J ≃* QuaternionGroup (2 ^ (r - 2))) := by
  obtain ⟨g, rfl⟩ := hJ
  obtain ⟨e⟩ := h.quotEquiv_core
  let φ : ↥(tightCore R) ≃* ↥(conjSub g (tightCore R)) :=
    Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact ⟨(QuotientGroup.congr _ _ φ.symm
    (CFSG.ComponentClassification.OddCore.equiv_invariant φ.symm)).trans e⟩

theorem PerpHypR.odd_mem_trivialOnQuot (hr : 4 ≤ r) (h : PerpHypR r n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ CoreAssembly.conjClass (tightCore R)) {x : Y}
    (hx : x ∈ Subgroup.normalizer (J : Set Y)) (hodd : Odd (orderOf x)) :
    x ∈ Balance.Bootstrap.trivialOnQuot J :=
  Perp22.mem_trivialOnQuot_of_odd (k := r - 2) (by omega) (h.quotEquiv hJ).some hx hodd

theorem PerpHypR.conj_mem_twinHull (h : PerpHypR r n Y R S t) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) {x : Y}
    (hx : x ∈ ⨆ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), J) :
    c * x * c⁻¹ ∈ ⨆ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), J := by
  have hle : (⨆ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), J) ≤
      (⨆ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), J).comap
        (MulAut.conj c).toMonoidHom := by
    refine iSup₂_le fun J hJ y hy => ?_
    have hJ' := h.conj_mem_twinSet hJ hc
    have hy' : c * y * c⁻¹ ∈ conjSub c J := conj_mem_conjSub hy
    exact (le_iSup₂ (f := fun (J : Subgroup Y) (_ : J ∈ twinSet (CoreAssembly.conjClass (tightCore R))
      (tightCore R)) => J) (conjSub c J) hJ') hy'
  exact hle hx

end Standing

end CFSG.CGT.PushingUpLit.SolKNA.R4

module

public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreQ8
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPfCore

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal
  CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall CFSG.ClassicalInvolution.Q3.TA3

open scoped MatrixGroups

set_option linter.unusedSectionVars false


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem uniqueInv_core (h : PerpHypS n Y R S t) :
    IsUniqueInvolution (tightCore R) t :=
  Inner.isUniqueInvolution_core h.core.datum

theorem isSolvable_core (h : PerpHypS n Y R S t) : Group.IsSolvable ↥(tightCore R) := by
  haveI := isSolvable_of_quotient_twoGroup h.core.datum.twoGroup
  exact solvable_of_solvable_injective (Subgroup.inclusion_injective (tightCore_le R))

theorem isSubnormal_core (h : PerpHypS n Y R S t) :
    CFSG.Open.IsSubnormal (tightCore R) (Subgroup.centralizer ({t} : Set Y)) :=
  isSubnormal_of_hypOmegaGen h.core.hyp (CoreAssembly.mem_conjClass_self _) (uniqueInv_core h)

theorem exists_twin (h : PerpHypS n Y R S t) :
    ∃ g ∈ Subgroup.centralizer ({t} : Set Y), conjSub g (tightCore R) ≠ tightCore R ∧
      conjSub g (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) ∧
      IsUniqueInvolution (conjSub g (tightCore R)) t := by
  obtain ⟨K', ⟨hK'Ω, z', hz'0, hz'⟩, hne⟩ := h.core.twin
  have hz : IsUniqueInvolution (tightCore R) t := uniqueInv_core h
  have hzt : t = z' := hz.eq hz'0
  rw [← hzt] at hz'
  obtain ⟨g, hg⟩ := hK'Ω
  dsimp only at hg
  have hgc : g ∈ Subgroup.centralizer ({t} : Set Y) := by
    have h1 : g * t * g⁻¹ = t := by
      have := (hz.conj g).eq (hg ▸ hz')
      exact this
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp h1
  refine ⟨g, hgc, ?_, ⟨g, rfl⟩, ?_⟩
  · rw [hg]; exact hne
  · rw [hg]; exact hz'

theorem exists_q8 (h : PerpHypS n Y R S t) :
    ∃ φ : QuaternionGroup 2 →* Y, Function.Injective φ ∧ (∀ x, φ x ∈ tightCore R) := by
  obtain ⟨r', hr', ⟨e'⟩⟩ := h.core.datum.quat
  set S' : Subgroup Y := (S : Subgroup R).map R.subtype with hS'
  have hQ : CFSG.ComponentClassification.AschbacherTheorem3.IsQuaternionTwoGroup S' :=
    ⟨r', hr', ⟨(Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype
      R.subtype_injective).symm.trans e'⟩⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_q8Pair hQ
  have hS'K : S' ≤ tightCore R := h.core.datum.sylow_core.1
  exact ⟨q8Hom hpq, q8Hom_injective hpq, fun x => hS'K (q8Hom_mem hpq hp hq x)⟩


theorem oddCoreOf_core_le (h : PerpHypS n Y R S t) :
    oddCoreOf (tightCore R) ≤ Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) :=
  Balance.oddCoreIn_le_of_isSubnormal (isSubnormal_core h)

theorem isPGroup_core_of_oddCore_eq_bot (h : PerpHypS n Y R S t)
    (hO : classicalInvolutionOddCore ↥(tightCore R) = ⊥) : IsPGroup 2 ↥(tightCore R) := by
  set K := tightCore R with hKdef
  let φ : ↥K →* R ⧸ classicalInvolutionOddCore ↥R :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥R)).comp
      (Subgroup.inclusion (tightCore_le R))
  have hker : φ.ker ≤ classicalInvolutionOddCore ↥K := by
    refine le_sSup ⟨MonoidHom.normal_ker φ, ?_⟩
    have hmem : ∀ x : φ.ker, (⟨(x : K).1, tightCore_le R (x : K).2⟩ : R) ∈
        classicalInvolutionOddCore ↥R := fun x => by
      have := x.2
      rw [MonoidHom.mem_ker] at this
      exact (QuotientGroup.eq_one_iff _).mp this
    have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥R)) :=
      CFSG.ComponentClassification.OddCore.odd_card R
    haveI : Finite (classicalInvolutionOddCore ↥R) := inferInstance
    have hle : Nat.card φ.ker ∣ Nat.card (classicalInvolutionOddCore ↥R) := by
      have : (φ.ker).map (Subgroup.inclusion (tightCore_le R)) ≤ classicalInvolutionOddCore ↥R := by
        rintro _ ⟨x, hx, rfl⟩
        exact hmem ⟨x, hx⟩
      rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective (tightCore_le R))]
      exact Subgroup.card_dvd_of_le this
    exact Odd.of_dvd_nat hodd hle
  have hbot : φ.ker = ⊥ := by
    rw [hO] at hker
    exact le_bot_iff.mp hker
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hbot
  exact h.core.datum.twoGroup.of_injective φ hφinj

theorem isPGroup_core_of_oddCore_centralizer (h : PerpHypS n Y R S t)
    (hO : Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥) :
    IsPGroup 2 ↥(tightCore R) := by
  refine isPGroup_core_of_oddCore_eq_bot h ?_
  have h1 := oddCoreOf_core_le h
  rw [hO, le_bot_iff] at h1
  have h2 : (classicalInvolutionOddCore ↥(tightCore R)).map (tightCore R).subtype = ⊥ := h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ (tightCore R).subtype_injective).mp h2


theorem false_of_omega5 (h : PerpHypS n Y R S t) {g k : Y} (hk : k ∈ tightCore R)
    (hk2 : IsPGroup 2 (Subgroup.zpowers k)) (hknc : ∃ w ∈ tightCore R, k * w ≠ w * k)
    (hvt : (g * k * g⁻¹) * t = t * (g * k * g⁻¹))
    (hvN : g * k * g⁻¹ ∉ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y)) : False := by
  have hΩ := h.core.hyp
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hJ : conjSub g (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨g, rfl⟩
  have hvJ : g * k * g⁻¹ ∈ conjSub g (tightCore R) := conj_mem_conjSub hk
  have hne : tightCore R ≠ conjSub g (tightCore R) := by
    intro heq
    apply hvN
    rw [heq] at hK ⊢
    exact Subgroup.le_normalizer (heq ▸ hvJ)
  have hnc : ¬ ∀ w ∈ conjSub g (tightCore R), (g * k * g⁻¹) * w = w * (g * k * g⁻¹) := by
    intro hall
    obtain ⟨w, hw, hkw⟩ := hknc
    apply hkw
    have := hall (g * w * g⁻¹) (conj_mem_conjSub hw)
    have e1 : (g * k * g⁻¹) * (g * w * g⁻¹) = g * (k * w) * g⁻¹ := by group
    have e2 : (g * w * g⁻¹) * (g * k * g⁻¹) = g * (w * k) * g⁻¹ := by group
    rw [e1, e2] at this
    have h3 : g * (k * w) = g * (w * k) := mul_right_cancel this
    exact mul_left_cancel h3
  have hv2 : IsPGroup 2 (Subgroup.zpowers (g * k * g⁻¹)) := by
    have e : g * k * g⁻¹ = (MulAut.conj g).toMonoidHom k := by simp
    rw [e, ← MonoidHom.map_zpowers]
    exact hk2.map _
  exact hvN (hΩ.omega5 _ hK _ hJ hne t (uniqueInv_core h) _ hvJ hnc hv2 hvt)

theorem twin_facts (h : PerpHypS n Y R S t) (hK2 : IsPGroup 2 ↥(tightCore R)) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) (hne : conjSub c (tightCore R) ≠ tightCore R) :
    (∀ x ∈ tightCore R, ∀ y ∈ conjSub c (tightCore R), x * y = y * x) ∧
      tightCore R ⊓ conjSub c (tightCore R) = Subgroup.zpowers t := by
  have hΩ := h.core.hyp
  have hz := uniqueInv_core h
  have hct : c * t * c⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    rw [hc]; group
  have hz' : IsUniqueInvolution (conjSub c (tightCore R)) t := by
    have := hz.conj c
    rwa [hct] at this
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hJ : conjSub c (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨c, rfl⟩
  exact ⟨twin_commute hΩ hK hJ hne.symm hz hz' hK2, twin_inf_eq hΩ hK hJ hne.symm hz hz' hK2⟩

theorem false_of_omega4_comm (h : PerpHypS n Y R S t) (hK2 : IsPGroup 2 ↥(tightCore R)) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) (hne : conjSub c (tightCore R) ≠ tightCore R)
    {x y : Y} (hx : x ∈ tightCore R) (hy : y ∈ conjSub c (tightCore R)) (hxy : x * y ≠ y * x) :
    False :=
  hxy ((twin_facts h hK2 hc hne).1 x hx y hy)

theorem false_of_omega4_inf (h : PerpHypS n Y R S t) (hK2 : IsPGroup 2 ↥(tightCore R)) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) (hne : conjSub c (tightCore R) ≠ tightCore R)
    (hinf : tightCore R ⊓ conjSub c (tightCore R) ≠ Subgroup.zpowers t) : False :=
  hinf (twin_facts h hK2 hc hne).2


@[expose] def twins (R : Subgroup Y) : Set (Subgroup Y) :=
  twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)

@[expose] def sigmaOf (R : Subgroup Y) (J : Subgroup Y) : Subgroup Y :=
  Subgroup.centralizer {y : Y | ∃ J' ∈ twins R, J' ≠ J ∧ y ∈ J'}

theorem conj_mem_twins (h : PerpHypS n Y R S t) {J : Subgroup Y} (hJ : J ∈ twins R) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) : conjSub c J ∈ twins R :=
  conj_mem_twinSet (uniqueInv_core h) hJ hc

theorem conjSub_sigmaOf (h : PerpHypS n Y R S t) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) (J : Subgroup Y) :
    conjSub c (sigmaOf R J) = sigmaOf R (conjSub c J) := by
  have hc' : c⁻¹ ∈ Subgroup.centralizer ({t} : Set Y) := Subgroup.inv_mem _ hc
  ext x
  rw [mem_conjSub_iff]
  unfold sigmaOf
  simp only [Subgroup.mem_centralizer_iff, Set.mem_setOf_eq]
  constructor
  · rintro hx y ⟨J', hJ', hne, hy⟩
    have hJ'' : conjSub c⁻¹ J' ∈ twins R := conj_mem_twins h hJ' hc'
    have hne'' : conjSub c⁻¹ J' ≠ J := by
      intro heq
      apply hne
      have := congrArg (conjSub c) heq
      rwa [conjSub_conjSub_inv] at this
    have hy' : c⁻¹ * y * c ∈ conjSub c⁻¹ J' := by
      rw [mem_conjSub_iff]
      simpa [mul_assoc] using hy
    have := hx _ ⟨conjSub c⁻¹ J', hJ'', hne'', hy'⟩
    calc y * x = c * ((c⁻¹ * y * c) * (c⁻¹ * x * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * x * c) * (c⁻¹ * y * c)) * c⁻¹ := by rw [← this]
      _ = x * y := by group
  · rintro hx y ⟨J', hJ', hne, hy⟩
    have hJ'' : conjSub c J' ∈ twins R := conj_mem_twins h hJ' hc
    have hne'' : conjSub c J' ≠ conjSub c J := fun heq => hne (conjSub_injective c heq)
    have hy' : c * y * c⁻¹ ∈ conjSub c J' := conj_mem_conjSub hy
    have := hx _ ⟨conjSub c J', hJ'', hne'', hy'⟩
    calc y * (c⁻¹ * x * c) = c⁻¹ * ((c * y * c⁻¹) * x) * c := by group
      _ = c⁻¹ * (x * (c * y * c⁻¹)) * c := by rw [← this]
      _ = (c⁻¹ * x * c) * y := by group


theorem exists_conj_of_mem_twins (h : PerpHypS n Y R S t) {J : Subgroup Y} (hJ : J ∈ twins R) :
    ∃ c ∈ Subgroup.centralizer ({t} : Set Y), J = conjSub c (tightCore R) := by
  have hz := uniqueInv_core h
  have htr : ∀ J ∈ CoreAssembly.conjClass (tightCore R), ∃ g : Y, conjSub g (tightCore R) = J :=
    fun J hJ => hJ
  have := twinSet_eq htr hz
  have hJ' : J ∈ {J | J ∈ CoreAssembly.conjClass (tightCore R) ∧
      ∃ g ∈ Subgroup.centralizer ({t} : Set Y), conjSub g (tightCore R) = J} := by
    rw [← this]; exact hJ
  obtain ⟨-, g, hg, hgJ⟩ := hJ'
  exact ⟨g, hg, hgJ.symm⟩

theorem isPGroup_conjSub {K : Subgroup Y} (hK : IsPGroup 2 ↥K) (c : Y) :
    IsPGroup 2 ↥(conjSub c K) := by
  let e := Subgroup.equivMapOfInjective K (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
  exact hK.of_surjective e.toMonoidHom e.surjective

theorem le_sigmaOf (h : PerpHypS n Y R S t) (hK2 : IsPGroup 2 ↥(tightCore R)) {J : Subgroup Y}
    (hJ : J ∈ twins R) : J ≤ sigmaOf R J := by
  obtain ⟨c, hc, rfl⟩ := exists_conj_of_mem_twins h hJ
  intro x hx
  rw [sigmaOf, Subgroup.mem_centralizer_iff]
  rintro y ⟨J', hJ', hne, hy⟩
  obtain ⟨c', hc', rfl⟩ := exists_conj_of_mem_twins h hJ'
  have hz := uniqueInv_core h
  have hct : ∀ d ∈ Subgroup.centralizer ({t} : Set Y), d * t * d⁻¹ = t := fun d hd => by
    rw [Subgroup.mem_centralizer_singleton_iff] at hd
    rw [hd]; group
  have hzJ : IsUniqueInvolution (conjSub c (tightCore R)) t := by
    have := hz.conj c; rwa [hct c hc] at this
  have hzJ' : IsUniqueInvolution (conjSub c' (tightCore R)) t := by
    have := hz.conj c'; rwa [hct c' hc'] at this
  exact (twin_commute h.core.hyp ⟨c, rfl⟩ ⟨c', rfl⟩ hne.symm hzJ hzJ'
    (isPGroup_conjSub hK2 c) x hx y hy).symm

theorem longFundSetE3_of_sigma (h : PerpHypS n Y R S t) (hK2 : IsPGroup 2 ↥(tightCore R))
    (hcl : IsClassicalMember3 (sigmaOf R (tightCore R)) t)
    (hcomm : ∀ c ∈ Subgroup.centralizer ({t} : Set Y), conjSub c (tightCore R) ≠ tightCore R →
      Commutes (sigmaOf R (tightCore R)) (sigmaOf R (conjSub c (tightCore R)))) :
    LongFundSetE3 R t := by
  have hct : ∀ d ∈ Subgroup.centralizer ({t} : Set Y), d * t * d⁻¹ = t := fun d hd => by
    rw [Subgroup.mem_centralizer_singleton_iff] at hd
    rw [hd]; group
  refine ⟨sigmaOf R, ?_, ?_, ?_⟩
  · intro J hJ
    obtain ⟨c, hc, rfl⟩ := exists_conj_of_mem_twins h hJ
    refine ⟨le_sigmaOf h hK2 hJ, ?_⟩
    have := hcl.conj c
    rw [← conjSub_sigmaOf h hc, ← hct c hc]
    exact this
  · intro J hJ J' hJ' hne x hx y hy
    obtain ⟨c, hc, rfl⟩ := exists_conj_of_mem_twins h hJ
    obtain ⟨c', hc', rfl⟩ := exists_conj_of_mem_twins h hJ'
    have hd : c⁻¹ * c' ∈ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hc'
    have hne' : conjSub (c⁻¹ * c') (tightCore R) ≠ tightCore R := by
      intro heq
      apply hne
      have h1 : conjSub c' (tightCore R) = conjSub c (conjSub (c⁻¹ * c') (tightCore R)) := by
        rw [← conjSub_mul]; simp
      rw [h1, heq]
    have hcm := hcomm _ hd hne'
    have h2 : conjSub c' (tightCore R) = conjSub c (conjSub (c⁻¹ * c') (tightCore R)) := by
      rw [← conjSub_mul]; simp
    have key := hcm.conjSub c
    rw [conjSub_sigmaOf h hc, conjSub_sigmaOf h hc, ← h2] at key
    exact key x hx y hy
  · intro J hJ c hc
    exact conjSub_sigmaOf h hc J

theorem centralizer_le_normalizer_set (K : Subgroup Y) :
    Subgroup.centralizer (K : Set Y) ≤ Subgroup.normalizer (K : Set Y) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 : y * x = x * y := Subgroup.mem_centralizer_iff.mp hx y hy
    rw [show x * y * x⁻¹ = y by rw [← h1]; group]
    exact hy
  · intro hy
    have h2 : x * y * x⁻¹ ∈ (K : Set Y) := hy
    have h3 : (x * y * x⁻¹) * x = x * (x * y * x⁻¹) := by
      have := Subgroup.mem_centralizer_iff.mp hx _ h2
      exact this
    have : y = x * y * x⁻¹ := by
      calc y = x⁻¹ * ((x * y * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * y * x⁻¹)) := by rw [h3]
        _ = x * y * x⁻¹ := by group
    rw [this]
    exact h2

theorem core_mem_twins (h : PerpHypS n Y R S t) : tightCore R ∈ twins R :=
  ⟨CoreAssembly.mem_conjClass_self _, t, uniqueInv_core h, uniqueInv_core h⟩

theorem longFundSetE3_of_two_twins (h : PerpHypS n Y R S t) (hK2 : IsPGroup 2 ↥(tightCore R))
    {K' : Subgroup Y} (hK' : K' ∈ twins R) (hne : K' ≠ tightCore R)
    (hV : ∀ J ∈ twins R, J = tightCore R ∨ J = K')
    (hsl : Nonempty (↥(Subgroup.centralizer (K' : Set Y)) ⧸
      classicalInvolutionOddCore ↥(Subgroup.centralizer (K' : Set Y)) ≃* SL(2, ZMod 3)))
    (hcomm : Commutes (Subgroup.centralizer (K' : Set Y))
      (Subgroup.centralizer ((tightCore R : Subgroup Y) : Set Y))) :
    LongFundSetE3 R t := by
  have hz := uniqueInv_core h
  have hKt : tightCore R ∈ twins R := core_mem_twins h
  have hσK : sigmaOf R (tightCore R) = Subgroup.centralizer (K' : Set Y) := by
    unfold sigmaOf
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · rintro ⟨J, hJ, hJK, hy⟩
      rcases hV J hJ with h1 | h1
      · exact absurd h1 hJK
      · rw [← h1]; exact hy
    · intro hy
      exact ⟨K', hK', hne, hy⟩
  have hσK' : sigmaOf R K' = Subgroup.centralizer ((tightCore R : Subgroup Y) : Set Y) := by
    unfold sigmaOf
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · rintro ⟨J, hJ, hJK, hy⟩
      rcases hV J hJ with h1 | h1
      · rw [← h1]; exact hy
      · exact absurd h1 hJK
    · intro hy
      exact ⟨tightCore R, hKt, hne.symm, hy⟩
  obtain ⟨c₀, hc₀, hK'eq⟩ := exists_conj_of_mem_twins h hK'
  have hcomm0 := (twin_facts h hK2 hc₀ (by rw [← hK'eq]; exact hne)).1
  have hKC : tightCore R ≤ Subgroup.centralizer (K' : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hK'eq] at hy
    exact (hcomm0 x hx y hy).symm
  have htK' : t ∈ K' := by
    obtain ⟨-, z, hzK, hzK'⟩ := hK'
    rw [hz.eq hzK]
    exact hzK'.mem
  set C : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hC
  set N : Subgroup Y := C ⊓ Subgroup.normalizer (K' : Set Y) with hNdef
  have hCK'N : Subgroup.centralizer (K' : Set Y) ≤ N := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨?_, centralizer_le_normalizer_set K' hx⟩
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hx t htK').symm
  have hNC : N ≤ C := inf_le_left
  have hperm : ∀ d ∈ C, conjSub d K' = tightCore R ∨ conjSub d K' = K' := fun d hd =>
    hV _ (conj_mem_twins h hK' hd)
  have hpermK : ∀ d ∈ C, conjSub d (tightCore R) = tightCore R ∨ conjSub d (tightCore R) = K' :=
    fun d hd => hV _ (conj_mem_twins h hKt hd)
  have hfixK : ∀ d ∈ C, conjSub d K' = K' → conjSub d (tightCore R) = tightCore R := by
    intro d hd hdK'
    rcases hpermK d hd with h1 | h1
    · exact h1
    · exfalso
      apply hne
      exact conjSub_injective d (h1.trans hdK'.symm) |>.symm
  have hnormNC : (N.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNC]
    intro n g hn hg
    have hnC : n ∈ C := hNC hn
    have hnK' : conjSub n K' = K' := (mem_normalizer_iff_conjSub_eq).mp (Subgroup.mem_inf.mp hn).2
    have hg' : g⁻¹ ∈ C := Subgroup.inv_mem _ hg
    refine Subgroup.mem_inf.mpr ⟨C.mul_mem (C.mul_mem hg hnC) hg', ?_⟩
    rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, conjSub_mul]
    rcases hperm g⁻¹ hg' with h1 | h1
    · rw [h1, hfixK n hnC hnK']
      have := conjSub_conjSub_inv g K'
      rw [h1] at this
      exact this
    · rw [h1, hnK']
      have := conjSub_conjSub_inv g K'
      rw [h1] at this
      exact this
  have hnormCN : ((Subgroup.centralizer (K' : Set Y)).subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCK'N]
    intro z x hz' hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxK : x⁻¹ * y * x ∈ K' := by
      have := (mem_normalizer_iff_conjSub_eq).mp (Subgroup.mem_inf.mp hx).2
      rw [← this] at hy
      rw [SetLike.mem_coe, mem_conjSub_iff] at hy
      simpa using hy
    have h2 := Subgroup.mem_centralizer_iff.mp hz' _ hxK
    calc y * (x * z * x⁻¹) = x * ((x⁻¹ * y * x) * z) * x⁻¹ := by group
      _ = x * (z * (x⁻¹ * y * x)) * x⁻¹ := by rw [h2]
      _ = (x * z * x⁻¹) * y := by group
  have hsub : CFSG.Open.IsSubnormal (Subgroup.centralizer (K' : Set Y)) C :=
    CFSG.Open.IsSubnormal.step hCK'N hnormCN
      (CFSG.Open.IsSubnormal.step hNC hnormNC (CFSG.Open.IsSubnormal.refl C))
  have hcl : IsClassicalMember3 (sigmaOf R (tightCore R)) t := by
    rw [hσK]
    exact ⟨h.core.datum.order, hKC hz.mem, hsub, hsl⟩
  refine longFundSetE3_of_sigma h hK2 hcl ?_
  intro c hc hcne
  rcases hpermK c hc with h1 | h1
  · exact absurd h1 hcne
  · rw [h1, hσK, hσK']
    exact hcomm

@[expose] def TwinLeafS (n : ℕ) (P : ∀ (F : Type) [Group F], Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypS n Y R S t → TwoSubgroupsFourGenerated ↥(genFittingFStar Y) →
      P ↥(genFittingFStar Y) → LongFundSetE3 R t

@[expose] def NoTwinS (n : ℕ) (P : ∀ (F : Type) [Group F], Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypS n Y R S t → TwoSubgroupsFourGenerated ↥(genFittingFStar Y) →
      P ↥(genFittingFStar Y) → False

theorem TwinLeafS.of_no {n : ℕ} {P : ∀ (F : Type) [Group F], Prop} (h : NoTwinS n P) :
    TwinLeafS n P :=
  fun Y _ _ R S t hP hsmall hPF => (h Y R S t hP hsmall hPF).elim

theorem TwinLeafS.of_split {n : ℕ} {P Q₃ Q : ∀ (F : Type) [Group F], Prop}
    (hsplit : ∀ (F : Type) [Group F], P F → Q₃ F ∨ Q F) (h₃ : TwinLeafS n Q₃)
    (h : TwinLeafS n Q) : TwinLeafS n P :=
  fun Y _ _ R S t hP hsmall hPF =>
    (hsplit _ hPF).elim (fun h3 => h₃ Y R S t hP hsmall h3) (fun h4 => h Y R S t hP hsmall h4)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

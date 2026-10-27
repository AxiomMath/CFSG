module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311c2
public import CFSG.LieType.SeitzGeneration.UnitaryMixing
public import CFSG.LieType.SeitzGeneration.OrthManyBig
public import CFSG.LieType.SeitzGeneration.OrthManyThree
import CFSG.LieType.SeitzGeneration.OuterSpData
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Census.CommonUnipotent
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311e

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
  CFSG.Assembly.LowTwoRank

section SpUni

variable {r : ℕ} {K : Type} [Field K]

theorem spEnd_spTransvection_pow (u : Fin r ⊕ Fin r → K) (t : K) (n : ℕ) (y : Fin r ⊕ Fin r → K) :
    spEnd (spTransvection u t ^ n) y = y + ((n : K) * t * spForm r K y u) • u := by
  induction n generalizing y with
  | zero => simp [spEnd_one]
  | succ n ih =>
    rw [pow_succ, spEnd_mul, Module.End.mul_apply, ih, spEnd_spTransvection, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, spForm_isAlt u, smul_eq_mul, mul_zero, add_zero]
    push_cast
    module

theorem spTransvection_pow_ringChar (u : Fin r ⊕ Fin r → K) (t : K) :
    spTransvection u t ^ ringChar K = 1 := by
  refine eq_one_of_spEnd_fix fun y => ?_
  rw [spEnd_spTransvection_pow, ringChar.Nat.cast_ringChar, zero_mul, zero_mul, zero_smul, add_zero]

@[expose] def spUniSpan (E : Subgroup (StatedSp r K)) : Subgroup (StatedSp r K) :=
  Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ ringChar K = 1}

theorem transCenter_uni_of_fixed {E : Subgroup (StatedSp r K)} {x : StatedSp r K} (hxE : x ∈ E)
    (hx1 : x ≠ 1) {u : Fin r ⊕ Fin r → K} (hu : spEnd x u = u) : TransCenter (spUniSpan E) u :=
  fun t => Subgroup.subset_closure ⟨x, hxE, hx1, commute_spTransvection hu t, spTransvection_pow_ringChar u t⟩

end SpUni

section Lift

theorem uniClosure_of_lift {G Q : Type*} [Group G] [Group Q] [Finite G] {p n : ℕ}
    [Fact p.Prime] (π : G →* Q) (hπ : Function.Surjective π) (hker : ¬ p ∣ Nat.card π.ker)
    (E : Subgroup Q) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hG : ∀ E' : Subgroup G, (∀ a ∈ E', ∀ b ∈ E', a * b = b * a) → (∀ a ∈ E', a ^ p = 1) →
      Nat.card E' = Nat.card E →
      Subgroup.closure {h : G | ∃ x ∈ E', x ≠ 1 ∧ h * x = x * h ∧ h ^ n = 1} = ⊤) :
    Subgroup.closure {k : Q | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k ∧ k ^ n = 1} = ⊤ := by
  classical
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  obtain ⟨E', hE'map, hE'dis⟩ := CFSG.RankThree.PartOne.CTP.SeitzToral.exists_lift_of_coprime_ker π hπ hker E hEp
  have hE'mem : ∀ x ∈ E', π x ∈ E := fun x hx => hE'map ▸ ⟨x, hx, rfl⟩
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ E' := E'.mul_mem (E'.mul_mem (E'.mul_mem ha hb) (E'.inv_mem ha))
      (E'.inv_mem hb)
    have hk : a * b * a⁻¹ * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      have := hcomm _ (hE'mem a ha) _ (hE'mem b hb)
      rw [this]
      group
    have := Subgroup.disjoint_def.mp hE'dis hc hk
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hE'exp : ∀ a ∈ E', a ^ p = 1 := by
    intro a ha
    have hk : a ^ p ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hexp _ (hE'mem a ha)
    exact Subgroup.disjoint_def.mp hE'dis (E'.pow_mem ha p) hk
  let fπ : E' →* E := (π.comp E'.subtype).codRestrict E (fun x => hE'mem x.1 x.2)
  have hfπsurj : Function.Surjective fπ := by
    intro e
    have : (e : Q) ∈ E'.map π := hE'map ▸ e.2
    obtain ⟨x, hx, hxe⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
  have hfπinj : Function.Injective fπ := by
    intro x y hxy
    have h1 : π x.1 = π y.1 := congrArg Subtype.val hxy
    have h2 : x.1⁻¹ * y.1 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : x.1⁻¹ * y.1 = 1 :=
      Subgroup.disjoint_def.mp hE'dis (E'.mul_mem (E'.inv_mem x.2) y.2) h2
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  have hcard : Nat.card E' = Nat.card E :=
    Nat.card_congr (Equiv.ofBijective fπ ⟨hfπinj, hfπsurj⟩)
  have htop := hG E' hE'comm hE'exp hcard
  rw [eq_top_iff]
  have : (Subgroup.closure {h : G | ∃ x ∈ E', x ≠ 1 ∧ h * x = x * h ∧ h ^ n = 1}).map π ≤
      Subgroup.closure {k : Q | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k ∧ k ^ n = 1} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨h, ⟨x, hx, hx1, hxc, hhn⟩, rfl⟩
    refine Subgroup.subset_closure ⟨π x, hE'mem x hx, ?_, by rw [← map_mul, ← map_mul, hxc],
      by rw [← map_pow, hhn, map_one]⟩
    intro hπx
    exact hx1 (Subgroup.disjoint_def.mp hE'dis hx (by rwa [MonoidHom.mem_ker]))
  rw [htop, Subgroup.map_top_of_surjective π hπ] at this
  exact this

end Lift

section TransvectionPow

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

theorem ofLinearEquiv_transvection_pow_apply {f : Module.Dual R W} {v : W} (h : f v = 0) (m : ℕ)
    (y : W) :
    ((LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.transvection h) ^ m :
      LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) y = y + ((m : R) * f y) • v := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Units.val_mul, Module.End.mul_apply, ih]
    change LinearEquiv.transvection h y + ((m : R) * f (LinearEquiv.transvection h y)) • v = _
    rw [LinearEquiv.transvection.apply, map_add, map_smul, h, smul_eq_mul, mul_zero, add_zero]
    push_cast
    module

theorem ofLinearEquiv_transvection_pow_eq_one {f : Module.Dual R W} {v : W} (h : f v = 0) {m : ℕ}
    (hm : (m : R) = 0) :
    LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.transvection h) ^ m = 1 := by
  apply Units.ext
  apply LinearMap.ext
  intro y
  rw [ofLinearEquiv_transvection_pow_apply, hm, zero_mul, zero_smul, add_zero]
  rfl

end TransvectionPow

section UnitaryMixingGeneric

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary

variable {ℓ f : ℕ} {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W]

theorem exists_unitary_transvection_mixing (hE : UnitaryFieldData ℓ f E) (hq : 3 ≤ ℓ ^ f)
    (Hf : W →ₛₗ[hE.bar] W →ₗ[E] E) (hsymm : ∀ a b, hE.bar (Hf a b) = Hf b a)
    {R₁ R₂ : Submodule E W} (horth : ∀ a ∈ R₁, ∀ b ∈ R₂, Hf a b = 0)
    {z₁ z₂ : W} (hz₁R : z₁ ∈ R₁) (hz₂R : z₂ ∈ R₂) (hz₁ : Hf z₁ z₁ ≠ 0) (hz₂ : Hf z₂ z₂ ≠ 0)
    {n : ℕ} (hn : (n : E) = 0) :
    ∃ γ : LinearMap.GeneralLinearGroup E W, γ ∈ sesqUnitaryGroup Hf ∧ γ ^ n = 1 ∧
      ∃ u'' ∈ R₁, ∃ w'' ∈ R₂, u'' ≠ 0 ∧ w'' ≠ 0 ∧ (γ : W →ₗ[E] W) z₂ = u'' + w'' := by
  classical
  have := hE.finite
  have hz₁0 : z₁ ≠ 0 := fun h0 => hz₁ (by rw [h0]; simp)
  have hz₂0 : z₂ ≠ 0 := fun h0 => hz₂ (by rw [h0]; simp)
  have ht₁ : hE.bar (Hf z₁ z₁) = Hf z₁ z₁ := hsymm z₁ z₁
  have ht₂ : hE.bar (Hf z₂ z₂) = Hf z₂ z₂ := hsymm z₂ z₂
  have hmem : (-(Hf z₂ z₂) / Hf z₁ z₁ : E) ∈ hE.fixedField := by
    rw [hE.mem_fixedField, map_div₀, map_neg, ht₁, ht₂]
  obtain ⟨lam, hlam⟩ := hE.normHom_surjective ⟨_, hmem⟩
  have hlam' : lam * hE.bar lam = -(Hf z₂ z₂) / Hf z₁ z₁ := by
    have := congrArg Subtype.val hlam
    simpa [UnitaryFieldData.norm] using this
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hlam'
    exact (div_ne_zero (neg_ne_zero.mpr hz₂) hz₁) hlam'.symm
  have hnorm : Hf (lam • z₁) (lam • z₁) = -(Hf z₂ z₂) := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    calc lam * (hE.bar lam * Hf z₁ z₁) = (lam * hE.bar lam) * Hf z₁ z₁ := by ring
      _ = -(Hf z₂ z₂) := by rw [hlam']; field_simp
  have hlz₁R : lam • z₁ ∈ R₁ := R₁.smul_mem lam hz₁R
  have hH12 : Hf (lam • z₁) z₂ = 0 := horth _ hlz₁R _ hz₂R
  have hH21 : Hf z₂ (lam • z₁) = 0 := by
    rw [← hsymm, hH12, map_zero]
  have hee : Hf (lam • z₁ + z₂) (lam • z₁ + z₂) = 0 := by
    simp only [map_add, LinearMap.add_apply, hnorm, hH12, hH21]
    ring
  have hHe2 : Hf (lam • z₁ + z₂) z₂ = Hf z₂ z₂ := by
    rw [map_add, LinearMap.add_apply, hH12, zero_add]
  obtain ⟨c₁, c₂, hc₁, hc₂, hc₁0, hc₂0, hc12⟩ : ∃ c₁ c₂ : E, hE.bar c₁ = -c₁ ∧ hE.bar c₂ = -c₂ ∧
      c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ c₁ ≠ c₂ := by
    have hcard : 2 < (hE.traceZero : Set E).ncard := by
      rw [← Nat.card_coe_set_eq]
      change 2 < Nat.card hE.traceZero
      rw [hE.card_traceZero]
      omega
    obtain ⟨c₁, c₂, c₃, h₁, h₂, h₃, h12, h13, h23⟩ :=
      (Set.two_lt_ncard_iff (Set.toFinite _)).1 hcard
    have hbar' : ∀ c ∈ hE.traceZero, hE.bar c = -c := fun c hc => by
      have := hE.mem_traceZero.mp hc
      rw [UnitaryFieldData.trace] at this
      linear_combination this
    by_cases h0₁ : c₁ = 0
    · exact ⟨c₂, c₃, hbar' _ h₂, hbar' _ h₃, fun h => h12 (h0₁.trans h.symm),
        fun h => h13 (h0₁.trans h.symm), h23⟩
    · by_cases h0₂ : c₂ = 0
      · exact ⟨c₁, c₃, hbar' _ h₁, hbar' _ h₃, h0₁, fun h => h23 (h0₂.trans h.symm), h13⟩
      · exact ⟨c₁, c₂, hbar' _ h₁, hbar' _ h₂, h0₁, h0₂, h12⟩
  have hmain : ∀ c : E, hE.bar c = -c → c ≠ 0 → (1 + c * Hf z₂ z₂) • z₂ ≠ 0 →
      ∃ γ : LinearMap.GeneralLinearGroup E W, γ ∈ sesqUnitaryGroup Hf ∧ γ ^ n = 1 ∧
        ∃ u'' ∈ R₁, ∃ w'' ∈ R₂, u'' ≠ 0 ∧ w'' ≠ 0 ∧ (γ : W →ₗ[E] W) z₂ = u'' + w'' := by
    intro c hc hc0 hne
    have hfv : (c • Hf (lam • z₁ + z₂)) (lam • z₁ + z₂) = 0 := by
      rw [LinearMap.smul_apply, hee, smul_zero]
    refine ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.transvection hfv), ?_,
      ofLinearEquiv_transvection_pow_eq_one hfv hn, (c * Hf z₂ z₂) • (lam • z₁),
      R₁.smul_mem _ hlz₁R, (1 + c * Hf z₂ z₂) • z₂, R₂.smul_mem _ hz₂R,
      smul_ne_zero (mul_ne_zero hc0 hz₂) (smul_ne_zero hlam0 hz₁0), hne, ?_⟩
    · rw [mem_sesqUnitaryGroup]
      intro y z
      exact Mixing.transvection_isometry Hf hsymm hee hc y z
    · change z₂ + (c * Hf (lam • z₁ + z₂) z₂) • (lam • z₁ + z₂) = _
      rw [hHe2, smul_add, add_smul, one_smul]
      abel
  by_cases h1 : (1 + c₁ * Hf z₂ z₂) • z₂ = 0
  · by_cases h2 : (1 + c₂ * Hf z₂ z₂) • z₂ = 0
    · exfalso
      have e1 : 1 + c₁ * Hf z₂ z₂ = 0 := (smul_eq_zero.mp h1).resolve_right hz₂0
      have e2 : 1 + c₂ * Hf z₂ z₂ = 0 := (smul_eq_zero.mp h2).resolve_right hz₂0
      have e3 : (c₁ - c₂) * Hf z₂ z₂ = 0 := by linear_combination e1 - e2
      exact mul_ne_zero (sub_ne_zero.mpr hc12) hz₂ e3
    · exact hmain c₂ hc₂ hc₂0 h2
  · exact hmain c₁ hc₁ hc₁0 h1

end UnitaryMixingGeneric

section SpPlaneFive

open Polynomial CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.CTP
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {ℓ f p r : ℕ} {K : Type} [Field K] {Ahat : Subgroup (StatedSp r K)}

theorem exists_mixing_element_of_paired_sp_uni (S : SpPlaneSetup ℓ f p r K Ahat) {x : StatedSp r K}
    (hxA : x ∈ Ahat) (hx1 : x ≠ 1) {h : primaryFactors (spEnd x)}
    (hne : (h : K[X]) ≠ reciprocalPolynomial (h : K[X]))
    {u w : Fin r ⊕ Fin r → K} (hu : u ∈ primaryComponent (spEnd x) (h : K[X]))
    (hw : w ∈ primaryComponent (spEnd x) (h : K[X]))
    (hind : LinearIndependent (AdjoinRoot (h : K[X]))
      ![(⟨u, hu⟩ : primaryComponent (spEnd x) (h : K[X])), ⟨w, hw⟩]) :
    ∃ g : StatedSp r K, g * x = x * g ∧ g ^ ringChar K = 1 ∧ spEnd g w = w + u := by
  obtain ⟨φ, hφ1, -⟩ := ((S.blocks hxA hx1).paired h hne).factor
  set W := primaryComponent (spEnd x) (h : K[X]) with hWdef
  set E := AdjoinRoot (h : K[X]) with hEdef
  set u₀ : W := ⟨u, hu⟩ with hu₀
  set w₀ : W := ⟨w, hw⟩ with hw₀
  have hwnot : w₀ ∉ Submodule.span E {u₀} := by
    intro hmem
    obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 := (LinearIndependent.pair_iff.mp hind) e (-1) (by
      simp only [neg_smul, one_smul]
      rw [he]
      exact add_neg_cancel _)
    exact one_ne_zero (neg_eq_zero.mp h1.2)
  obtain ⟨φ₀, hφ₀w, hφ₀u⟩ := Submodule.exists_le_ker_of_notMem hwnot
  set ψ : Module.Dual E W := (φ₀ w₀)⁻¹ • φ₀ with hψ
  have hψw : ψ w₀ = 1 := by
    rw [hψ, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ₀w]
  have hψu : ψ u₀ = 0 := by
    have h1 : φ₀ u₀ = 0 := hφ₀u (Submodule.mem_span_singleton_self u₀)
    rw [hψ, LinearMap.smul_apply, h1, smul_zero]
  let γ₀ : blockGL (spEnd x) (h : K[X]) :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.transvection hψu)
  have hγr : γ₀ ^ ringChar K = 1 := by
    refine ofLinearEquiv_transvection_pow_eq_one hψu ?_
    rw [← map_natCast (algebraMap K E), ringChar.Nat.cast_ringChar, map_zero]
  refine ⟨(φ.symm γ₀ : StatedSp r K), (mem_spSupported.mp (φ.symm γ₀).2).1, ?_, ?_⟩
  · rw [← SubgroupClass.coe_pow, ← map_pow, hγr, map_one, OneMemClass.coe_one]
  · have hg := hφ1 (φ.symm γ₀) w hw
    rw [MulEquiv.apply_symm_apply] at hg
    rw [← hg]
    have hγ : blockApply γ₀ w hw = w + ((ψ w₀ • u₀ : W) : Fin r ⊕ Fin r → K) := rfl
    rw [hγ, hψw, one_smul]

@[expose] def compSub {x : StatedSp r K} (a : K[X]) {M : Submodule K (Fin r ⊕ Fin r → K)}
    (hstab : ∀ s ∈ M, spEnd x s ∈ M) : Submodule (AdjoinRoot a) (primaryComponent (spEnd x) a) where
  carrier := {v | (v : Fin r ⊕ Fin r → K) ∈ M}
  add_mem' := fun {s t} hs ht => M.add_mem hs ht
  zero_mem' := M.zero_mem
  smul_mem' := fun c v hv => coe_smul_mem_of_stable hstab c v hv

theorem exists_anisotropic_compSub (S : SpPlaneSetup ℓ f p r K Ahat) (D : SpPlaneDecomp p Ahat)
    {x : StatedSp r K} (hxA : x ∈ Ahat) {h : primaryFactors (spEnd x)}
    (hself : reciprocalPolynomial (h : K[X]) = h)
    {bar : AdjoinRoot (h : K[X]) →+* AdjoinRoot (h : K[X])}
    (Hf : primaryComponent (spEnd x) (h : K[X]) →ₛₗ[bar]
      primaryComponent (spEnd x) (h : K[X]) →ₗ[AdjoinRoot (h : K[X])] AdjoinRoot (h : K[X]))
    (hsymm : ∀ a b, bar (Hf a b) = Hf b a) (hbarne : ∃ s, bar s ≠ s) {η : AdjoinRoot (h : K[X])}
    (hη0 : η ≠ 0)
    (htrace : ∀ (v w : primaryComponent (spEnd x) (h : K[X])) (c : AdjoinRoot (h : K[X])),
      Algebra.trace K (AdjoinRoot (h : K[X])) (c * Hf v w) =
        spForm r K (v : Fin r ⊕ Fin r → K)
          (((c * η) • w : primaryComponent (spEnd x) (h : K[X])) : Fin r ⊕ Fin r → K))
    {M : Subgroup ↥Ahat} (hM : Nat.card M = p) (hstabM : ∀ s ∈ spLineSpace M, spEnd x s ∈ spLineSpace M)
    {v : Fin r ⊕ Fin r → K} (hvM : v ∈ spLineSpace M)
    (hvh : v ∈ primaryComponent (spEnd x) (h : K[X])) (hv0 : v ≠ 0) :
    ∃ z ∈ compSub (h : K[X]) hstabM, Hf z z ≠ 0 := by
  set v₁ : primaryComponent (spEnd x) (h : K[X]) := ⟨v, hvh⟩ with hv₁
  have hv₁R : v₁ ∈ compSub (h : K[X]) hstabM := hvM
  obtain ⟨y, hyM, hyh, hBy⟩ := exists_pairing_in_component
    (altPrimaryData_spLin S.p_cast_ne_zero (S.pow_eq_one hxA)) h.2 hself hstabM
    (D.nondeg (some ⟨M, hM⟩)) hvM hvh hv0
  set y₁ : primaryComponent (spEnd x) (h : K[X]) := ⟨y, hyh⟩ with hy₁
  have hy₁R : y₁ ∈ compSub (h : K[X]) hstabM := hyM
  have hz : Hf v₁ y₁ ≠ 0 := by
    intro h0
    apply hBy
    have h1 := htrace v₁ (η⁻¹ • y₁) 1
    have e1 : Hf v₁ (η⁻¹ • y₁) = 0 := by rw [map_smul, smul_eq_mul, h0, mul_zero]
    have e2 : ((1 * η) • (η⁻¹ • y₁) : primaryComponent (spEnd x) (h : K[X])) = y₁ := by
      rw [smul_smul, one_mul, mul_inv_cancel₀ hη0, one_smul]
    rw [e1, e2, mul_zero, map_zero] at h1
    exact h1.symm
  exact exists_anisotropic_of_pairing Hf hsymm hbarne _ hv₁R hy₁R hz

theorem exists_mixing_element_of_selfDual_sp_uni (S : SpPlaneSetup ℓ f p r K Ahat)
    (D : SpPlaneDecomp p Ahat) {L N : Subgroup ↥Ahat} (hL : Nat.card L = p)
    (hN : Nat.card N = p) (hLN : L ≠ N) {x : StatedSp r K} (hxA : x ∈ Ahat) (hx1 : x ≠ 1)
    {h : primaryFactors (spEnd x)} (hh1 : (h : K[X]) ≠ X - 1)
    (hself : reciprocalPolynomial (h : K[X]) = h) {u w : Fin r ⊕ Fin r → K}
    (hu : u ∈ spLineSpace L) (huh : u ∈ primaryComponent (spEnd x) (h : K[X])) (hu0 : u ≠ 0)
    (hw : w ∈ spLineSpace N) (hwh : w ∈ primaryComponent (spEnd x) (h : K[X])) (hw0 : w ≠ 0) :
    ∃ g : StatedSp r K, g * x = x * g ∧ g ^ ringChar K = 1 ∧ ∃ w₀ ∈ spLineSpace N, w₀ ≠ 0 ∧
      ∃ u' ∈ spLineSpace L, ∃ w' ∈ spLineSpace N, u' ≠ 0 ∧ w' ≠ 0 ∧
        spEnd g w₀ = u' + w' := by
  classical
  have := S.finite
  have blocks := S.blocks hxA hx1
  obtain ⟨d, hd2, hpd, σ, hσpow, hσne, hσσ, hσroot, hσadj, hE, hbar, Hf, hsymmF, hsep,
    ⟨η, hη0, hηbar, htrace⟩, -, φ, hφ⟩ := (blocks.selfDual h hh1 hself).exists_half
  have hsymm : ∀ a b : primaryComponent (spEnd x) (h : K[X]), hE.bar (Hf a b) = Hf b a :=
    fun a b => hsymmF.eq a b
  have hstabL : ∀ s ∈ spLineSpace L, spEnd x s ∈ spLineSpace L := fun s hs =>
    S.spLineSpace_stable ⟨x, hxA⟩ hs
  have hstabN : ∀ s ∈ spLineSpace N, spEnd x s ∈ spLineSpace N := fun s hs =>
    S.spLineSpace_stable ⟨x, hxA⟩ hs
  have hne : (some ⟨L, hL⟩ : Option {M : Subgroup ↥Ahat // Nat.card M = p}) ≠ some ⟨N, hN⟩ :=
    fun h' => hLN (congrArg Subtype.val (Option.some.inj h'))
  have horth : ∀ a ∈ spLineSpace L, ∀ b ∈ spLineSpace N, spForm r K a b = 0 :=
    fun a ha b hb => D.orth _ _ hne a ha b hb
  have hHf : ∀ a ∈ compSub (h : K[X]) hstabL, ∀ b ∈ compSub (h : K[X]) hstabN, Hf a b = 0 := by
    intro a ha b hb
    refine eq_zero_of_trace_mul_eq_zero (h : K[X]) (Hf a b) fun c => ?_
    rw [htrace a b c]
    exact horth _ ha _ (coe_smul_mem_of_stable hstabN (c * η) b hb)
  have hbarne : ∃ s, hE.bar s ≠ s := by
    by_contra hcon
    push Not at hcon
    refine hσne (AlgEquiv.ext fun z => ?_)
    rw [AlgEquiv.one_apply, ← hbar z]
    exact hcon z
  obtain ⟨z₁, hz₁L, hz₁⟩ :=
    exists_anisotropic_compSub S D hxA hself Hf hsymm hbarne hη0 htrace hL hstabL hu huh hu0
  obtain ⟨z₂, hz₂N, hz₂⟩ :=
    exists_anisotropic_compSub S D hxA hself Hf hsymm hbarne hη0 htrace hN hstabN hw hwh hw0
  have hq : 3 ≤ ℓ ^ (f * d) := by
    have hle : p ≤ (ℓ ^ f) ^ d + 1 := Nat.le_of_dvd (by omega) hpd
    have := S.three_lt_p
    rw [pow_mul]
    omega
  have hn : ((ringChar K : ℕ) : AdjoinRoot (h : K[X])) = 0 := by
    rw [← map_natCast (algebraMap K (AdjoinRoot (h : K[X]))), ringChar.Nat.cast_ringChar, map_zero]
  obtain ⟨γ, hγmem, hγr, u'', hu''L, w'', hw''N, hu''0, hw''0, hγz⟩ :=
    exists_unitary_transvection_mixing hE hq Hf hsymm hHf hz₁L hz₂N hz₁ hz₂ hn
  have hz₂0 : (z₂ : Fin r ⊕ Fin r → K) ≠ 0 := fun h0 => hz₂ (by
    rw [show z₂ = 0 from Subtype.ext h0]
    simp)
  set g := φ.symm ⟨γ, hγmem⟩ with hg
  refine ⟨(g : StatedSp r K), (mem_spSupported.mp g.2).1, ?_, (z₂ : Fin r ⊕ Fin r → K), hz₂N, hz₂0,
    (u'' : Fin r ⊕ Fin r → K), hu''L, (w'' : Fin r ⊕ Fin r → K), hw''N,
    fun h0 => hu''0 (Subtype.ext h0), fun h0 => hw''0 (Subtype.ext h0), ?_⟩
  · have hγr' : (⟨γ, hγmem⟩ : sesqUnitaryGroup Hf) ^ ringChar K = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hγr)
    rw [← SubgroupClass.coe_pow, hg, ← map_pow, hγr', map_one, OneMemClass.coe_one]
  · have h3 := hφ g (z₂ : Fin r ⊕ Fin r → K) z₂.2
    have h4 : φ g = ⟨γ, hγmem⟩ := by rw [hg, MulEquiv.apply_symm_apply]
    rw [h4] at h3
    rw [← h3]
    have h5 : blockApply ((⟨γ, hγmem⟩ : sesqUnitaryGroup Hf) : blockGL (spEnd x) (h : K[X]))
        (z₂ : Fin r ⊕ Fin r → K) z₂.2 =
          (((γ : primaryComponent (spEnd x) (h : K[X]) →ₗ[AdjoinRoot (h : K[X])]
            primaryComponent (spEnd x) (h : K[X])) z₂ : primaryComponent (spEnd x) (h : K[X])) :
              Fin r ⊕ Fin r → K) := rfl
    rw [h5, hγz, Submodule.coe_add]

theorem mem_spUniSpan {x g : StatedSp r K} (hxA : x ∈ Ahat) (hx1 : x ≠ 1) (hg : g * x = x * g)
    (hgr : g ^ ringChar K = 1) : g ∈ spUniSpan Ahat :=
  Subgroup.subset_closure ⟨x, hxA, hx1, hg, hgr⟩

theorem transCenter_of_mem_summand_uni (S : SpPlaneSetup ℓ f p r K Ahat) (D : SpPlaneDecomp p Ahat)
    (i : Option {M : Subgroup ↥Ahat // Nat.card M = p}) {c : Fin r ⊕ Fin r → K}
    (hc : c ∈ spInnerSummand p Ahat i) : TransCenter (spUniSpan Ahat) c := by
  rcases i with _ | ⟨M, hM⟩
  · obtain ⟨a, ha⟩ := spPlane_exists_ne_one S
    refine transCenter_uni_of_fixed a.2 (fun h => ha (Subtype.ext h)) ?_
    exact CFSG.RankThree.Classical.mem_fixSub.mp hc a (Subgroup.mem_top a)
  · obtain ⟨t, htM, ht1⟩ := spPlane_exists_ne_one_of_card S hM
    have hker := (D.ker_eq M hM t htM ht1).1
    have hc' : c ∈ spLineFix M := (inf_le_left : spLineSpace M ≤ spLineFix M) hc
    rw [← hker] at hc'
    exact transCenter_uni_of_fixed t.2 (fun h => ht1 (Subtype.ext h)) (mem_ker_sub_one_iff.mp hc')

theorem transCenter_add_of_mem_summands_uni (S : SpPlaneSetup ℓ f p r K Ahat)
    (D : SpPlaneDecomp p Ahat) {M : Subgroup ↥Ahat} (hM : Nat.card M = p) {y y' : Fin r ⊕ Fin r → K}
    (hy : y ∈ spPlaneFix Ahat) (hy' : y' ∈ spLineSpace M) :
    TransCenter (spUniSpan Ahat) (y + y') := by
  obtain ⟨t, htM, ht1⟩ := spPlane_exists_ne_one_of_card S hM
  have hker := D.ker_eq M hM t htM ht1
  have hmem : y + y' ∈ spLineFix M := by
    rw [hker.2]
    exact Submodule.add_mem_sup hy hy'
  rw [← hker.1] at hmem
  exact transCenter_uni_of_fixed t.2 (fun h => ht1 (Subtype.ext h)) (mem_ker_sub_one_iff.mp hmem)

theorem exists_mixed_transCenter_five_uni (S : SpPlaneSetup ℓ f p r K Ahat) (D : SpPlaneDecomp p Ahat)
    {L N : Subgroup ↥Ahat} (hL : Nat.card L = p) (hN : Nat.card N = p) (hLN : L ≠ N)
    (hVL : spLineSpace L ≠ ⊥) (hVN : spLineSpace N ≠ ⊥) :
    ∃ u ∈ spLineSpace L, ∃ w ∈ spLineSpace N, u ≠ 0 ∧ w ≠ 0 ∧
      TransCenter (spUniSpan Ahat) (u + w) := by
  classical
  obtain ⟨x, hxA, hx1, h, hmem, hh1, hm2, ⟨v, hvL, hvh, hv0⟩, ⟨w, hwN, hwh, hw0⟩⟩ :=
    S.exists_mixing_factor D hL hN hLN hVL hVN
  have hpureN : ∀ c ∈ spLineSpace N, TransCenter (spUniSpan Ahat) c := fun c hc =>
    transCenter_of_mem_summand_uni S D (some ⟨N, hN⟩) hc
  by_cases hself : reciprocalPolynomial h = h
  · obtain ⟨g, hg, hgr, w₀, hw₀N, hw₀0, u', hu'L, w', hw'N, hu'0, hw'0, hgw⟩ :=
      exists_mixing_element_of_selfDual_sp_uni S D hL hN hLN hxA hx1 (h := ⟨h, hmem⟩) hh1 hself
        hvL hvh hv0 hwN hwh hw0
    refine ⟨u', hu'L, w', hw'N, hu'0, hw'0, ?_⟩
    rw [← hgw]
    exact (hpureN w₀ hw₀N).map (mem_spUniSpan hxA hx1 hg hgr)
  · have hne : h ≠ reciprocalPolynomial h := fun h' => hself h'.symm
    have hstabL : ∀ s ∈ spLineSpace L, spEnd x s ∈ spLineSpace L := fun s hs =>
      S.spLineSpace_stable ⟨x, hxA⟩ hs
    have hstabN : ∀ s ∈ spLineSpace N, spEnd x s ∈ spLineSpace N := fun s hs =>
      S.spLineSpace_stable ⟨x, hxA⟩ hs
    have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hmem⟩
    have hind := CFSG.RankThree.PartOne.KCUnitaryMixing.linearIndependent_pair_of_disjoint hstabL
      hstabN (D.disjoint_lineSpace hL hN hLN) hvL hwN hvh hwh hv0 hw0
    obtain ⟨g, hg, hgr, hgw⟩ :=
      exists_mixing_element_of_paired_sp_uni S hxA hx1 (h := ⟨h, hmem⟩) hne hvh hwh hind
    refine ⟨v, hvL, w, hwN, hv0, hw0, ?_⟩
    rw [add_comm, ← hgw]
    exact (hpureN w hwN).map (mem_spUniSpan hxA hx1 hg hgr)

theorem transCenter_pair_uni (S : SpPlaneSetup ℓ f p r K Ahat) (D : SpPlaneDecomp p Ahat)
    (i j : Option {M : Subgroup ↥Ahat // Nat.card M = p}) (hij : i ≠ j)
    {y y' : Fin r ⊕ Fin r → K} (hy : y ∈ spInnerSummand p Ahat i)
    (hy' : y' ∈ spInnerSummand p Ahat j) (hy0 : y ≠ 0) (hy'0 : y' ≠ 0) :
    TransCenter (spUniSpan Ahat) (y + y') := by
  rcases i with _ | ⟨L, hL⟩ <;> rcases j with _ | ⟨N, hN⟩
  · exact absurd rfl hij
  · exact transCenter_add_of_mem_summands_uni S D hN hy hy'
  · rw [add_comm]
    exact transCenter_add_of_mem_summands_uni S D hL hy' hy
  · have hLN : L ≠ N := fun h' => hij (by subst h'; rfl)
    have hVL : spLineSpace L ≠ ⊥ := fun h' => hy0 (by
      have : y ∈ (⊥ : Submodule K (Fin r ⊕ Fin r → K)) := h' ▸ hy
      exact (Submodule.mem_bot K).mp this)
    have hVN : spLineSpace N ≠ ⊥ := fun h' => hy'0 (by
      have : y' ∈ (⊥ : Submodule K (Fin r ⊕ Fin r → K)) := h' ▸ hy'
      exact (Submodule.mem_bot K).mp this)
    obtain ⟨u₀, hu₀, w₀, hw₀, hu₀0, hw₀0, hmix⟩ :=
      exists_mixed_transCenter_five_uni S D hL hN hLN hVL hVN
    have hne : (some ⟨L, hL⟩ : Option {M : Subgroup ↥Ahat // Nat.card M = p}) ≠ some ⟨N, hN⟩ :=
      fun h' => hLN (congrArg Subtype.val (Option.some.inj h'))
    have horth : ∀ a ∈ spLineSpace L, ∀ b ∈ spLineSpace N, spForm r K a b = 0 :=
      fun a ha b hb => D.orth _ _ hne a ha b hb
    have horth' : ∀ b ∈ spLineSpace N, ∀ a ∈ spLineSpace L, spForm r K b a = 0 :=
      fun b hb a ha => by rw [← spForm_isAlt.neg_eq, horth a ha b hb, neg_zero]
    obtain ⟨g₁, hg₁, hg₁u, hg₁fix⟩ := exists_mem_fixing_eq (U := spLineSpace L)
      (D.nondeg (some ⟨L, hL⟩)) (fun c hc => transCenter_of_mem_summand_uni S D (some ⟨L, hL⟩) hc)
      hu₀ hy hu₀0 hy0
    obtain ⟨g₂, hg₂, hg₂w, hg₂fix⟩ := exists_mem_fixing_eq (U := spLineSpace N)
      (D.nondeg (some ⟨N, hN⟩)) (fun c hc => transCenter_of_mem_summand_uni S D (some ⟨N, hN⟩) hc)
      hw₀ hy' hw₀0 hy'0
    have h2 : spEnd g₂ u₀ = u₀ := hg₂fix u₀ (fun c hc => horth u₀ hu₀ c hc)
    have h1 : spEnd g₁ y' = y' := hg₁fix y' (fun c hc => horth' y' hy' c hc)
    have := hmix.map ((spUniSpan Ahat).mul_mem hg₁ hg₂)
    rwa [spEnd_mul, Module.End.mul_apply, map_add, h2, hg₂w, map_add, hg₁u, h1] at this

theorem uniClosure_spPlane_five (S : SpPlaneSetup ℓ f p r K Ahat) : spUniSpan Ahat = ⊤ := by
  classical
  have D := S.decomp
  exact eq_top_of_transCenter (transCenter_of_pairs (Vs := spInnerSummand p Ahat)
    D.internal.submodule_iSup_eq_top D.orth D.nondeg
    (fun i c hc => transCenter_of_mem_summand_uni S D i hc)
    (fun i j hij y hy y' hy' hy0 hy'0 => transCenter_pair_uni S D i j hij hy hy' hy0 hy'0))

end SpPlaneFive

section SpCatFive

open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCSpFull
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem uniPlaneGen_inner_sp_five {d : TauCeti.ValidLieTypeIndex} {r ℓ f p : ℕ} {K : Type}
    [Field K] (e : Cat d ≃* StatedProj (StatedSp r K)) (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (hr : 2 ≤ r)
    (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2))
    {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hinner : InnerPlane d p E) : UniPlaneGen ℓ E := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSp r K)) :=
    isSimpleGroup_statedProj_statedSp_of_two_le hr fun h => hrq ⟨h.1, by rw [← hK]; exact h.2⟩
  have : IsSimpleGroup (Cat d) := MulEquiv.isSimpleGroup e
  have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat d)
    (range_conj_ne_bot_of_inner hp hc hinner)
  have hchar : ringChar K = ℓ := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hℓ hf hK
  rw [← hchar]
  refine uniPlaneGen_of_inner_model hinj e ?_ hE hc hinner
  intro E₁ hE₁ hcard₁
  refine uniClosure_of_lift (proj r K)
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective (r := r) (K := K))
    ?_ E₁ (fun x hx y hy => congrArg Subtype.val (hE₁.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (fun x hx => hE₁.2 x hx) ?_
  · intro hd
    have h1 := coprime_card_ker_proj (r := r) (K := K) (by omega) hp (by omega : p ≠ 2)
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h1 hd (dvd_refl p))
  · intro E' hc' he' hcd'
    have : CFSG.IsElementaryAbelian p E' :=
      { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hc' a a.2 b b.2)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
          Subtype.ext (he' x x.2) }
    exact uniClosure_spPlane_five ⟨hℓ, hf, hK, hp, by omega, hpℓ, hr, hrq, this,
      hcd'.trans hcard₁⟩

theorem uniSeitzPlanes_symplectic_inner_five :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧ IsSymplecticIndex d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, hp5, hsp⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases hsp with ⟨q, rfl⟩ | ⟨n, q, rfl, hn3, hq2⟩ | ⟨n, q, rfl⟩
  ·
    have hq : p ≠ q.p := by simpa using hpd
    have h := uniPlaneGen_inner_sp_five (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
      q.prime_p q.exponent_pos (CFSG.RankThree.PartOne.CTP.card_fixedField_B 2 q hv) hp hp5 hq le_rfl
      (fun h => hrange.2 ⟨h.1, by simpa [TauCeti.PrimePower.card_def] using h.2⟩) hE hc hinner
    simpa using h
  ·
    have hq : p ≠ q.p := by simpa using hpd
    have h := uniPlaneGen_inner_sp_five
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj n q hv hq2 hn3)
      q.prime_p q.exponent_pos (CFSG.RankThree.PartOne.CTP.card_fixedField_B n q hv) hp hp5 hq (by omega)
      (fun h => by omega) hE hc hinner
    simpa using h
  ·
    have hq : p ≠ q.p := by simpa using hpd
    have hn3 : 3 ≤ n := hrange.1
    have h := uniPlaneGen_inner_sp_five (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj n q hv)
      q.prime_p q.exponent_pos (card_fixedField_C n q hv) hp hp5 hq (by omega) (fun h => by omega)
      hE hc hinner
    simpa using h

end SpCatFive

section RPow

variable {G : Type*} [Group G]

theorem pow_sq_eq_one_of_pow_eq_one {g : G} {n : ℕ} (h : g ^ n = 1) : g ^ (n ^ 2) = 1 := by
  rw [sq, pow_mul, h, one_pow]

theorem closure_le_closure_sq (E : Subgroup G) (n : ℕ) :
    Subgroup.closure {g : G | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ n = 1} ≤
      Subgroup.closure {g : G | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ (n ^ 2) = 1} :=
  Subgroup.closure_mono fun _ ⟨x, hx, hx1, hc, hn⟩ => ⟨x, hx, hx1, hc, pow_sq_eq_one_of_pow_eq_one hn⟩

theorem uniPlaneGen_of_pow {r k : ℕ} {E : Subgroup (MulAut G)} (h : UniPlaneGen (r ^ k) E) :
    UniPlaneGen r E := by
  unfold UniPlaneGen uniPlaneClosure at h ⊢
  rw [eq_top_iff] at h ⊢
  refine h.trans (Subgroup.closure_mono ?_)
  rintro s ⟨e, he, he1, hes, n, hn⟩
  exact ⟨e, he, he1, hes, k * n, by rw [pow_mul]; exact hn⟩

end RPow

section Split

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.CTP

section Heis

variable {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ}

theorem heisenbergMatrix_pow {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k)
    (a b : F) (m : ℕ) :
    heisenbergMatrix σ i k a b ^ m =
      heisenbergMatrix σ i k ((m : F) * a) ((m : F) * b - (m.choose 2 : F) * (a * σ a)) := by
  induction m with
  | zero => simp [heisenbergMatrix_zero]
  | succ m ih =>
    rw [pow_succ, ih, heisenbergMatrix_mul σ hi hik hk, Nat.choose_succ_succ', Nat.choose_one_right]
    congr 1
    · push_cast
      ring
    · push_cast
      ring

end Heis

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem rootHom_pow_ringChar [CharP K ℓ] {σ : K ≃+* K} (hσ : ∀ c, σ (σ c) = c) {i j : Fin n}
    (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) (c : Multiplicative K) :
    rootHom σ hσ hij hi hj c ^ ringChar K = 1 := by
  rw [← map_pow]
  have : c ^ ringChar K = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ringChar.Nat.cast_ringChar, zero_mul]
  rw [this, map_one]

theorem longRootHom_pow_ringChar [CharP K ℓ] {σ : K ≃+* K} {i : Fin n} (hi : i ≠ Fin.rev i)
    (c : Multiplicative (traceZero σ)) : longRootHom σ hi c ^ ringChar K = 1 := by
  rw [← map_pow]
  have : c ^ ringChar K = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    apply Subtype.ext
    rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, nsmul_eq_mul, ringChar.Nat.cast_ringChar,
      zero_mul]
  rw [this, map_one]

theorem heisenberg_pow_sq_ringChar [Fact ℓ.Prime] [CharP K ℓ] {σ : K ≃+* K}
    {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k) {g : SU σ n} {a b : K}
    (hg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = heisenbergMatrix σ i k a b) :
    g ^ (ringChar K ^ 2) = 1 := by
  have hℓ : ℓ.Prime := Fact.out
  have hr : ringChar K = ℓ := ringChar.eq K ℓ
  have hsq : ((ℓ ^ 2 : ℕ) : K) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero K ℓ, zero_pow two_ne_zero]
  have hchoose : (((ℓ ^ 2).choose 2 : ℕ) : K) = 0 := by
    rw [CharP.cast_eq_zero_iff K ℓ]
    refine hℓ.dvd_choose_pow (by norm_num) fun h => ?_
    have h4 : 4 ≤ ℓ ^ 2 := by
      have := hℓ.two_le
      nlinarith
    omega
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hg, heisenbergMatrix_pow σ hi hik hk, hr, hsq,
    hchoose, zero_mul, zero_mul, zero_mul, sub_zero, heisenbergMatrix_zero]
  rfl

theorem uniClosure_unitarySU_of_frame_sq [Finite K] [Fact ℓ.Prime] [CharP K ℓ]
    (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f - 1)
    (hn : 2 ≤ n) (E : Subgroup (unitarySU ℓ f K n)) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) (P : GL (Fin n) K)
    (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin n) (Fin n) K) *
      (P : Matrix (Fin n) (Fin n) K) = antidiag n)
    (hdiag : ∀ x ∈ E, (((P⁻¹ * ((x : unitarySU ℓ f K n) : GL (Fin n) K) * P : GL (Fin n) K)) :
      Matrix (Fin n) (Fin n) K).IsDiag) :
    Subgroup.closure {g : unitarySU ℓ f K n |
      ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ (ringChar K ^ 2) = 1} = ⊤ := by
  classical
  set σ := unitaryInvolution K ℓ f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution h.card_eq_sq
  let ε : Su K ℓ f n ≃* unitarySU ℓ f K n :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq n)
  let Φ : SU σ n ≃* unitarySU ℓ f K n := (CFSG.LieType.Universal.Unitary.conjEquiv P hP).trans ε
  let Dg : E → GL (Fin n) K := fun x =>
    P⁻¹ * (((x : unitarySU ℓ f K n)) : GL (Fin n) K) * P
  have hDg : ∀ x : E, ((Φ.symm (x : unitarySU ℓ f K n) : SU σ n) : GL (Fin n) K) = Dg x :=
    fun x => rfl
  have hdiagE : ∀ x : E, ((Dg x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag :=
    fun x => hdiag x x.2
  have hDmul : ∀ x y : E, Dg (x * y) = Dg x * Dg y := by
    intro x y
    simp only [Dg, Subgroup.coe_mul]
    group
  have hD1 : Dg 1 = 1 := by simp [Dg]
  let χ : Fin n → E →* K := fun c =>
    { toFun := fun x => ((Dg x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) c c
      map_one' := by simp [hD1]
      map_mul' := fun x y => by
        simp only [hDmul, Units.val_mul]
        exact mul_apply_diag_of_isDiag (hdiagE x) c }
  have hD : ∀ x : E, ((Dg x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun c => χ c x) := fun x => ((hdiagE x).diagonal_diag).symm
  have hnz : ∀ (c : Fin n) (x : E), χ c x ≠ 0 := by
    intro c x
    have h1 : (((Dg x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((Dg x)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) c c = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [mul_apply_diag_of_isDiag (hdiagE x)] at h1
    exact left_ne_zero_of_mul_eq_one h1
  have hexpE : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  have hχp : ∀ (c : Fin n) (x : E), (χ c x) ^ p = 1 := fun c x => by
    rw [← map_pow, hexpE, map_one]
  have hσχ : ∀ (c : Fin n) (x : E), σ (χ c x) = χ c x := by
    intro c x
    rw [hσdef, unitaryInvolution_apply]
    obtain ⟨k, hk⟩ := hpq
    have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
    have hq : ℓ ^ f = 1 + p * k := by omega
    rw [hq, pow_add, pow_one, pow_mul, hχp, one_pow, mul_one]
  have hrel : ∀ (c : Fin n) (x : E), χ c x * χ (Fin.rev c) x = 1 := by
    intro c x
    have hmem := (Φ.symm (x : unitarySU ℓ f K n)).2.2
    rw [hDg, hD x] at hmem
    have h1 := congrFun (congrFun hmem c) (Fin.rev c)
    have hconj : conjTr σ (Matrix.diagonal (fun c => χ c x)) =
        Matrix.diagonal (fun c => σ (χ c x)) := by
      rw [conjTr, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
    rw [hconj, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    simp only [antidiag, Matrix.of_apply, ite_true, mul_one] at h1
    rw [hσχ] at h1
    exact h1
  set S := Subgroup.closure {g : unitarySU ℓ f K n |
    ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ (ringChar K ^ 2) = 1} with hS
  have hmemS : ∀ (a : SU σ n) (x : E), x ≠ 1 →
      ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((Dg x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((Dg x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → a ^ (ringChar K ^ 2) = 1 → Φ a ∈ S := by
    intro a x hx1 hcomm har
    refine Subgroup.subset_closure ⟨(x : unitarySU ℓ f K n), x.2,
      fun h1 => hx1 (Subtype.ext h1), ?_, by rw [← map_pow, har, map_one]⟩
    apply Subtype.ext
    have hYD : (a : GL (Fin n) K) * Dg x = Dg x * (a : GL (Fin n) K) := by
      apply Units.ext
      simpa only [Units.val_mul] using hcomm
    have hxeq : ((x : unitarySU ℓ f K n) : GL (Fin n) K) = P * Dg x * P⁻¹ := by
      simp [Dg, mul_assoc]
    show P * (a : GL (Fin n) K) * P⁻¹ * ((x : unitarySU ℓ f K n) : GL (Fin n) K) =
      ((x : unitarySU ℓ f K n) : GL (Fin n) K) * (P * (a : GL (Fin n) K) * P⁻¹)
    rw [hxeq]
    calc P * (a : GL (Fin n) K) * P⁻¹ * (P * Dg x * P⁻¹)
        = P * ((a : GL (Fin n) K) * Dg x) * P⁻¹ := by group
      _ = P * (Dg x * (a : GL (Fin n) K)) * P⁻¹ := by rw [hYD]
      _ = P * Dg x * P⁻¹ * (P * (a : GL (Fin n) K) * P⁻¹) := by group
  have hrev : ∀ (i j : Fin n) (x : E), χ i x = χ j x → χ (Fin.rev j) x = χ (Fin.rev i) x := by
    intro i j x hij
    have h1 := hrel i x
    have h2 := hrel j x
    rw [hij] at h1
    exact mul_left_cancel₀ (hnz j x) (h2.trans h1.symm)
  have hR : Subgroup.comap Φ.toMonoidHom S = ⊤ := by
    refine eq_top_of_rootElements_le hσ.invol hσ.exists_traceZero hσ.trace_surj
      (fun x hx => hσ.exists_norm hx) hn _ ?_ ?_ ?_
    · intro i j hij hi hj hjr c
      obtain ⟨x, hx1, -, hxeq⟩ := exists_ne_one_hom_eq hp hexpE hcard (χ i) (χ j)
      refine hmemS _ x hx1 ?_ (pow_sq_eq_one_of_pow_eq_one (rootHom_pow_ringChar hσ.invol hij hi hj c))
      rw [coe_rootHom, hD x]
      exact rootMatrix_comm_diag_of_eq σ (fun c => χ c x) i j _ hxeq (hrev i j x hxeq)
    · intro i hi c
      obtain ⟨x, hx1, -, hxeq⟩ := exists_ne_one_hom_eq hp hexpE hcard (χ i) (χ (Fin.rev i))
      refine hmemS _ x hx1 ?_ (pow_sq_eq_one_of_pow_eq_one (longRootHom_pow_ringChar hi c))
      rw [coe_longRootHom, hD x]
      exact longRootMatrix_comm_diag_of_eq (fun c => χ c x) i _ hxeq
    · intro i k hi hik hk g hg
      obtain ⟨a, b, -, hga⟩ := hg
      have hmid : ∀ x : E, χ k x = 1 := by
        intro x
        have hsq : (χ k x) ^ 2 = 1 := by
          have := hrel k x
          rw [hk] at this
          simpa [sq] using this
        obtain ⟨m, hm⟩ := hp.eq_two_or_odd'.resolve_left hp2
        have h3 : χ k x ^ p = χ k x := by
          rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul]
        rw [← h3]
        exact hχp k x
      obtain ⟨x, hx1, -, hxeq⟩ := exists_ne_one_hom_eq hp hexpE hcard (χ i) (χ k)
      refine hmemS g x hx1 ?_ (heisenberg_pow_sq_ringChar hi hik hk hga)
      have h1i : χ i x = 1 := hxeq.trans (hmid x)
      have hr : χ (Fin.rev i) x = 1 := by
        have := hrel i x
        rwa [h1i, one_mul] at this
      rw [hga, hD x]
      exact heisenbergMatrix_comm_diag_of_eq σ (fun c => χ c x) i k a b hxeq
        ((hmid x).trans hr.symm)
  refine eq_top_iff.2 fun y _ => ?_
  have hy : Φ.symm y ∈ Subgroup.comap Φ.toMonoidHom S := by
    rw [hR]
    exact Subgroup.mem_top _
  simpa using hy

theorem uniClosure_unitarySU_split_sq (h : UnitaryFieldData ℓ f K) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f - 1) (hn : 2 ≤ n) (E : Subgroup (unitarySU ℓ f K n))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {g : unitarySU ℓ f K n |
      ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ (ringChar K ^ 2) = 1} = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε : ℕ, ε ≤ 1 ∧ n = 2 * r + ε :=
    ⟨n / 2, n - 2 * (n / 2), by omega, by omega⟩
  have hB : (stdB h (2 * r + ε)).IsSymm := gramForm_isSymm h (by simp)
  have hBl : (stdB h (2 * r + ε)).SeparatingLeft := gramForm_separatingLeft h (by simp)
  set ρ := unitaryRep (ℓ := ℓ) (f := f) (n := 2 * r + ε) (K := K) E with hρdef
  let S : E → Module.End K (Fin (2 * r + ε) → K) := fun x =>
    ((ρ x : LinearMap.GeneralLinearGroup K (Fin (2 * r + ε) → K)) :
      Module.End K (Fin (2 * r + ε) → K))
  have hScomm : ∀ x y, Commute (S x) (S y) := fun x y => by
    have hxy : x * y = y * x := Subtype.ext (hcomm x x.2 y y.2)
    show S x * S y = S y * S x
    simp only [S, ← Units.val_mul, ← map_mul, hxy]
  have hSpow : ∀ x, S x ^ p = 1 := fun x => by
    have hx : x ^ p = 1 := Subtype.ext (hexp x x.2)
    show ((ρ x : LinearMap.GeneralLinearGroup K (Fin (2 * r + ε) → K)) :
      Module.End K (Fin (2 * r + ε) → K)) ^ p = 1
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hx, map_one, Units.val_one]
  have hSiso : ∀ x v w, stdB h (2 * r + ε) (S x v) (S x w) = stdB h (2 * r + ε) v w :=
    fun x v w => mem_sesqUnitaryGroup.mp (unitaryRep_mem h E x) v w
  obtain ⟨w, hw, hev⟩ := exists_adapted_hypFamily h hp hp2 hpq hε r
    (V := Fin (2 * r + ε) → K) hB hBl (by simp) S hScomm hSpow hSiso
  let e := hypEquivFin r ε
  obtain ⟨P, hPJ, hPdiag⟩ := exists_frame_of_family h E (fun c => w (e.symm c))
    (fun i j => by
      rw [hw, hypGram_apply]
      have : e.symm j = hypPartner (e.symm i) ↔ j = Fin.rev i := by
        rw [Equiv.symm_apply_eq, hypEquivFin_hypPartner hε, Equiv.apply_symm_apply]
      simp only [this])
    (fun x hx => by
      choose d hd using fun c => hev ⟨x, hx⟩ (e.symm c)
      exact ⟨d, hd⟩)
  exact uniClosure_unitarySU_of_frame_sq h hp hp2 hpq hn E hexp hcard P hPJ hPdiag

end Split

section UnitaryInner

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.CTP

theorem uniClosure_statedProj_unitary_of_lift {ℓ f p : ℕ} {K : Type} [Field K] {m n : ℕ}
    (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hm : 1 ≤ m)
    (hker : ¬ p ∣ Nat.gcd m (ℓ ^ f + 1))
    (E : Subgroup (StatedProj (StatedSU m (ℓ ^ f) K))) [CFSG.IsElementaryAbelian p E]
    (hcard : Nat.card E = p ^ 2)
    (hG : ∀ E' : Subgroup (unitarySU ℓ f K m), (∀ x ∈ E', ∀ y ∈ E', x * y = y * x) →
      (∀ x ∈ E', x ^ p = 1) → Nat.card E' = p ^ 2 →
      Subgroup.closure {g : unitarySU ℓ f K m |
        ∃ x ∈ E', x ≠ 1 ∧ g * x = x * g ∧ g ^ n = 1} = ⊤) :
    Subgroup.closure {k : StatedProj (StatedSU m (ℓ ^ f) K) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k ∧ k ^ n = 1} = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact p.Prime := ⟨hp⟩
  let π : unitarySU ℓ f K m →* StatedProj (StatedSU m (ℓ ^ f) K) :=
    QuotientGroup.mk' ((StatedScalars (Fin m) K).subgroupOf (unitarySU ℓ f K m))
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hkerπ : π.ker = unitaryScalars h m := by
    rw [QuotientGroup.ker_mk', unitaryScalars_eq h hm]
  have hker' : ¬ p ∣ Nat.card π.ker := by
    rw [hkerπ, card_unitaryScalars h hm]
    exact hker
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have hexp : ∀ x ∈ E, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  exact uniClosure_of_lift π hπ hker' E hcomm hexp fun E' hc he hcd => hG E' hc he (hcd.trans hcard)

theorem uniPlaneGen_inner_unitary_pow {m k : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) {p : ℕ} (hp : p.Prime)
    (hlift : ¬ (p ∣ q.card + 1 ∧ p ∣ m + 1))
    (hSU : ∀ E : Subgroup (unitarySU (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩)
        (TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩)
        (GaloisField (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩)
          (2 * TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩)) (m + 1)),
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) → Nat.card E = p ^ 2 →
        Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ (ringChar
          (GaloisField (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩)
            (2 * TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩)) ^ k) = 1} = ⊤)
    {E : Subgroup (MulAut (Cat ⟨.twistedA m q, hv⟩))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hinner : InnerPlane ⟨.twistedA m q, hv⟩ p E) : UniPlaneGen q.p E := by
  have : Fact p.Prime := ⟨hp⟩
  set ℓ := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ with hℓ
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩ with hf
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField ℓ f
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  have : Fact ℓ.Prime := ⟨hU.prime⟩
  have hqcard : ℓ ^ f = q.card := by simp [hℓ, hf, TauCeti.ValidLieTypeIndex.characteristic,
    TauCeti.ValidLieTypeIndex.fieldExponent, TauCeti.PrimePower.card_def]
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm2 : 2 ≤ m := hrange.1
  have hfin := hU.finite
  let e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj m q hv
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSU (m + 1) (ℓ ^ f)
      (GaloisField ℓ (2 * f)))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU (GaloisField ℓ (2 * f)) ℓ f
      (by rw [hU.card, pow_mul']) (m + 1) (by omega) (by
        intro h32
        obtain ⟨h31, h2⟩ := Prod.mk.inj h32
        have h3 := hrange.2 (by omega)
        rw [hqcard] at h2
        omega)
  have : IsSimpleGroup (Cat ⟨.twistedA m q, hv⟩) := MulEquiv.isSimpleGroup e
  have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.twistedA m q, hv⟩)
    (range_conj_ne_bot_of_inner hp hc hinner)
  have hchar : ringChar (GaloisField ℓ (2 * f)) = q.p := by
    rw [ringChar.eq (GaloisField ℓ (2 * f)) ℓ]
    simp [hℓ, TauCeti.ValidLieTypeIndex.characteristic]
  refine uniPlaneGen_of_pow (k := k) ?_
  rw [← hchar]
  refine uniPlaneGen_of_inner_model hinj e ?_ hE hc hinner
  intro E₁ hE₁ hcard₁
  have : CFSG.IsElementaryAbelian p E₁ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E₁).mpr hE₁
  exact uniClosure_statedProj_unitary_of_lift hU hp (by omega) (fun hd => hlift ⟨by
      rw [← hqcard]; exact (hd.trans (Nat.gcd_dvd_right _ _)), hd.trans (Nat.gcd_dvd_left _ _)⟩)
    E₁ hcard₁ hSU

theorem uniSeitzPlanes_unitary_inner_five
    (hTor : ∀ {ℓ f n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K), p.Prime → p ∣ ℓ ^ f + 1 →
      ℓ ^ f ≠ 2 → ∀ (E : Subgroup (unitarySU ℓ f K (n + 1))), (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
        (∀ x ∈ E, x ^ p = 1) → Nat.card E = p ^ 2 →
        Subgroup.closure {g : unitarySU ℓ f K (n + 1) |
          ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ ringChar K = 1} = ⊤)
    (hNS : ∀ {ℓ f p n : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData ℓ f K), p.Prime → 5 ≤ p → p ≠ ℓ →
      ¬ p ∣ ℓ ^ f + 1 → ¬ p ∣ ℓ ^ f - 1 → 3 ≤ n → ∀ (E : Subgroup (unitarySU ℓ f K n)),
        (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) → Nat.card E = p ^ 2 →
        Subgroup.closure {g : unitarySU ℓ f K n |
          ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ ringChar K = 1} = ⊤) :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧ IsUnitaryIndex' d.1 ∧ CentralPrimeFree p d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hinner, hp5, ⟨m, q, hd⟩, hlift⟩
  subst hd
  have hpq : p ≠ q.p := by simpa using hpd
  set ℓ := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ with hℓ
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩ with hf
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField ℓ f
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  have hℓq : ℓ = q.p := by simp [hℓ, TauCeti.ValidLieTypeIndex.characteristic]
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm2 : 2 ≤ m := hrange.1
  have hSU : ∀ E' : Subgroup (unitarySU ℓ f (GaloisField ℓ (2 * f)) (m + 1)),
      (∀ x ∈ E', ∀ y ∈ E', x * y = y * x) → (∀ x ∈ E', x ^ p = 1) → Nat.card E' = p ^ 2 →
        Subgroup.closure {g | ∃ x ∈ E', x ≠ 1 ∧ g * x = x * g ∧
          g ^ (ringChar (GaloisField ℓ (2 * f)) ^ 2) = 1} = ⊤ := by
    intro E' hcomm hexp hcard
    by_cases h1 : p ∣ ℓ ^ f + 1
    · have hq : ℓ ^ f ≠ 2 := by
        intro h2
        rw [h2] at h1
        have := Nat.le_of_dvd (by norm_num) h1
        omega
      rw [eq_top_iff, ← hTor hU hp h1 hq E' hcomm hexp hcard]
      exact closure_le_closure_sq _ _
    by_cases h2 : p ∣ ℓ ^ f - 1
    · exact uniClosure_unitarySU_split_sq hU hp hp2 h2 (by omega) E' hcomm hexp hcard
    · rw [eq_top_iff, ← hNS hU hp hp5 (by rw [hℓq]; exact hpq) h1 h2 (by omega) E' hcomm hexp hcard]
      exact closure_le_closure_sq _ _
  have h := uniPlaneGen_inner_unitary_pow (k := 2) hv hp hlift hSU hE hc hinner
  simpa using h

end UnitaryInner

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311e

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311e

section OrthSq

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical
  CFSG.LieType.SeitzGeneration.OrthNS CFSG.LieType.SeitzGeneration.OrthBlk
open CFSG.RankThree.Classical2 (orthDerived)

section Span

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

variable (Q) in
@[expose] def orthSqSpan (E : Subgroup (orthDerived Q)) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure {g : V ≃ₗ[K] V | g ∈ orthDerived Q ∧
    (∃ x ∈ E.map (orthDerived Q).subtype, x ≠ 1 ∧ g * x = x * g) ∧ g ^ (ringChar K ^ 2) = 1}

theorem orthSqSpan_le_orthogonalGroup (E : Subgroup (orthDerived Q)) :
    orthSqSpan Q E ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨hg, -⟩
  exact orthDerived_le_orthogonalGroup Q hg

theorem orthSqSpan_eq_map (E : Subgroup (orthDerived Q)) :
    orthSqSpan Q E =
      (Subgroup.closure {h : orthDerived Q |
        ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ (ringChar K ^ 2) = 1}).map (orthDerived Q).subtype := by
  have hset : (orthDerived Q).subtype '' {h : orthDerived Q |
      ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ (ringChar K ^ 2) = 1} =
      {g : V ≃ₗ[K] V | g ∈ orthDerived Q ∧
        (∃ x ∈ E.map (orthDerived Q).subtype, x ≠ 1 ∧ g * x = x * g) ∧ g ^ (ringChar K ^ 2) = 1} := by
    ext g
    constructor
    · rintro ⟨h, ⟨x, hx, hx1, hhx, hr⟩, rfl⟩
      refine ⟨h.2, ⟨x.1, ⟨x, hx, rfl⟩, fun h' => hx1 (Subtype.ext h'), congrArg Subtype.val hhx⟩,
        ?_⟩
      have := congrArg Subtype.val hr
      simpa using this
    · rintro ⟨hg, ⟨_, ⟨x, hx, rfl⟩, hx1, hgx⟩, hr⟩
      refine ⟨⟨g, hg⟩, ⟨x, hx, fun h => hx1 (congrArg Subtype.val h), Subtype.ext hgx,
        Subtype.ext ?_⟩, rfl⟩
      simpa using hr
  rw [MonoidHom.map_closure, hset]
  rfl

theorem orthSq_closure_eq_top_of_le (E : Subgroup (orthDerived Q))
    (h : orthDerived Q ≤ orthSqSpan Q E) :
    Subgroup.closure {h : orthDerived Q |
      ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ (ringChar K ^ 2) = 1} = ⊤ := by
  rw [orthSqSpan_eq_map] at h
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨g', hg', hgg'⟩ := h g.2
  have : g' = g := Subtype.ext hgg'
  exact this ▸ hg'

theorem orthSq_eichler_pow_nsmul {u w : V} (hu : Q u = 0) (huw : polar Q u w = 0) (n : ℕ) :
    eichler Q u w ^ n = eichler Q u (n • w) := by
  induction n with
  | zero => simp [eichler_zero_right]
  | succ n ih =>
    have hnw : polar Q u (n • w) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul K, polar_smul_right_eq, huw, mul_zero]
    rw [pow_succ, ih, succ_nsmul, eichler_mul hnw huw]

theorem orthSq_eichler_pow_ringChar (u w : V) : eichler Q u w ^ ringChar K = 1 := by
  by_cases hc : Q u = 0 ∧ polar Q u w = 0
  · rw [orthSq_eichler_pow_nsmul hc.1 hc.2]
    have : ringChar K • w = 0 := by
      rw [← Nat.cast_smul_eq_nsmul K, ringChar.Nat.cast_ringChar, zero_smul]
    rw [this, eichler_zero_right]
  · rw [eichler_of_not hc, one_pow]

variable {E : Subgroup (orthDerived Q)}

theorem orthSq_mem_of_commute_sq {g : V ≃ₗ[K] V} (hg : g ∈ orthDerived Q)
    {a : orthDerived Q} (ha : a ∈ E) (ha1 : a ≠ 1)
    (hc : g * (a : V ≃ₗ[K] V) = (a : V ≃ₗ[K] V) * g) (hr : g ^ (ringChar K ^ 2) = 1) :
    g ∈ orthSqSpan Q E :=
  Subgroup.subset_closure ⟨hg, ⟨(a : V ≃ₗ[K] V), ⟨a, ha, rfl⟩, fun h => ha1 (Subtype.ext h), hc⟩,
    hr⟩

theorem orthSq_mem_of_commute {g : V ≃ₗ[K] V} (hg : g ∈ orthDerived Q)
    {a : orthDerived Q} (ha : a ∈ E) (ha1 : a ≠ 1)
    (hc : g * (a : V ≃ₗ[K] V) = (a : V ≃ₗ[K] V) * g) (hr : g ^ ringChar K = 1) :
    g ∈ orthSqSpan Q E :=
  orthSq_mem_of_commute_sq hg ha ha1 hc (pow_sq_eq_one_of_pow_eq_one hr)

theorem orthSq_eichler_mem_of_fix (hEΩ : elementaryGroup Q ≤ orthDerived Q)
    {e w : V} {x : orthDerived Q} (hxE : x ∈ E) (hx1 : x ≠ 1)
    (hxe : ((x : orthDerived Q) : V ≃ₗ[K] V) e = e)
    (hxw : ((x : orthDerived Q) : V ≃ₗ[K] V) w = w) :
    eichler Q e w ∈ orthSqSpan Q E := by
  refine orthSq_mem_of_commute (hEΩ (eichler_mem_elementaryGroup Q e w)) hxE hx1 ?_
    (orthSq_eichler_pow_ringChar e w)
  have hconj := eichler_conj (Q := Q) (orthDerived_le_orthogonalGroup Q x.2) e w
  rw [hxe, hxw] at hconj
  exact (mul_inv_eq_iff_eq_mul.mp hconj).symm

theorem orthSq_eichler_mem_of_lineFix (hEΩ : elementaryGroup Q ≤ orthDerived Q)
    {M : Subgroup E} (hM : M ≠ ⊥) {e w : V} (he : e ∈ lineFixSpace M) (hw : w ∈ lineFixSpace M) :
    eichler Q e w ∈ orthSqSpan Q E := by
  obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hM
  have hmem : ((t : E) : orthDerived Q) ∈ E := (t : E).2
  have hfix : ∀ v ∈ lineFixSpace M, (((t : E) : orthDerived Q) : V ≃ₗ[K] V) v = v := by
    intro v hv
    exact (mem_fixSpace.mp hv) _ ⟨((t : E) : orthDerived Q), ⟨(t : E), t.2, rfl⟩, rfl⟩
  refine orthSq_eichler_mem_of_fix hEΩ (x := ((t : E) : orthDerived Q)) hmem ?_
    (hfix e he) (hfix w hw)
  intro h1
  exact ht1 (Subtype.ext (Subtype.ext h1))

theorem orthSq_eichler_mem_of_mem_sup (hEΩ : elementaryGroup Q ≤ orthDerived Q) {M : Subgroup E}
    (hM : M ≠ ⊥) {e w : V} (he : e ∈ planeFixSpace E ⊔ lineSpace M)
    (hw : w ∈ planeFixSpace E ⊔ lineSpace M) : eichler Q e w ∈ orthSqSpan Q E :=
  orthSq_eichler_mem_of_lineFix hEΩ hM (sup_le_lineFixSpace M he) (sup_le_lineFixSpace M hw)

end Span

section Pivots

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {p : ℕ}
  {E : Subgroup (orthDerived Q)}

open _root_.Classical in
theorem orthSq_isRootCenter_of_pivots (hK : KernelLineData Q p E)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) (hp : p.Prime) {N : Subgroup E}
    (hN : Nat.card N = p) {s : V} (hsN : s ∈ planeFixSpace E ⊔ lineSpace N) (hs0 : s ≠ 0)
    (hsQ : Q s = 0)
    (hpiv : ∀ M : Subgroup E, Nat.card M = p → M ≠ N →
      ∀ v ∈ lineSpace M, v ∈ rootSet Q (orthSqSpan Q E) s) :
    IsRootCenter Q (orthSqSpan Q E) s := by
  refine ⟨hs0, hsQ, fun w hw => ?_⟩
  have hN0 : N ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hN
    exact hp.one_lt.ne' hN.symm
  set T : Submodule K V := ⨆ (M : {M : Subgroup E // Nat.card M = p}) (_ : M.1 ≠ N),
    lineSpace M.1 with hT
  have htop : (⊤ : Submodule K V) ≤ (planeFixSpace E ⊔ lineSpace N) ⊔ T := by
    rw [← hK.internal.submodule_iSup_eq_top]
    refine iSup_le fun i => ?_
    rcases i with _ | ⟨M, hM⟩
    · exact le_sup_of_le_left le_sup_left
    · by_cases hMN : M = N
      · subst hMN
        exact le_sup_of_le_left le_sup_right
      · exact le_sup_of_le_right (le_iSup₂_of_le ⟨M, hM⟩ hMN le_rfl)
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (htop (Submodule.mem_top (x := w)))
  have hsT : polar Q s b = 0 := by
    refine Submodule.iSup_induction (fun M : {M : Subgroup E // Nat.card M = p} =>
      ⨆ (_ : M.1 ≠ N), lineSpace M.1) (motive := fun b => polar Q s b = 0) hb ?_ ?_ ?_
    · intro M b hb'
      refine Submodule.iSup_induction (fun _ : M.1 ≠ N => lineSpace M.1)
        (motive := fun b => polar Q s b = 0) hb' ?_ ?_ ?_
      · intro hMN b hb''
        rw [polar_comm]
        exact polar_eq_zero_of_mem_sup hK hN M.2 hMN hb'' hsN
      · exact polar_zero_right Q s
      · intro x y hx hy
        rw [polar_add_right, hx, hy, add_zero]
    · exact polar_zero_right Q s
    · intro x y hx hy
      rw [polar_add_right, hx, hy, add_zero]
  have hbR : b ∈ rootSet Q (orthSqSpan Q E) s := by
    refine Submodule.iSup_induction (fun M : {M : Subgroup E // Nat.card M = p} =>
      ⨆ (_ : M.1 ≠ N), lineSpace M.1) (motive := fun b => b ∈ rootSet Q (orthSqSpan Q E) s)
      hb ?_ (AddSubgroup.zero_mem _) (fun x y hx hy => AddSubgroup.add_mem _ hx hy)
    intro M b hb'
    refine Submodule.iSup_induction (fun _ : M.1 ≠ N => lineSpace M.1)
      (motive := fun b => b ∈ rootSet Q (orthSqSpan Q E) s) hb' ?_
      (AddSubgroup.zero_mem _) (fun x y hx hy => AddSubgroup.add_mem _ hx hy)
    intro hMN b hb''
    exact hpiv M.1 M.2 hMN b hb''
  have haperp : polar Q s a = 0 := by
    rw [polar_add_right, hsT, add_zero] at hw
    exact hw
  have haR : a ∈ rootSet Q (orthSqSpan Q E) s :=
    ⟨haperp, orthSq_eichler_mem_of_mem_sup hEΩ hN0 hsN ha⟩
  exact ((rootSet Q (orthSqSpan Q E) s).add_mem haR hbR).2

theorem orthSq_rootSet_ge_of_pivot (hK : KernelLineData Q p E)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) (hp : p.Prime) {N M : Subgroup E}
    (hN : Nat.card N = p) (hM : Nat.card M = p) (hMN : M ≠ N)
    (hPN : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace N))
    (hPM : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace M)) {s₀ : V}
    (hs₀N : s₀ ∈ lineSpace N) (hs₀0 : s₀ ≠ 0) (hs₀Q : Q s₀ = 0) {b : V} (hbM : b ∈ lineSpace M)
    (hb0 : b ≠ 0) (hbR : b ∈ rootSet Q (orthSqSpan Q E) s₀) {s : V}
    (hsN : s ∈ planeFixSpace E ⊔ lineSpace N) (hs0 : s ≠ 0) (hsQ : Q s = 0) :
    ∀ v ∈ lineSpace M, v ∈ rootSet Q (orthSqSpan Q E) s := by
  classical
  have hN0 : N ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hN
    exact hp.one_lt.ne' hN.symm
  have hM0 : M ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hM
    exact hp.one_lt.ne' hM.symm
  have hne1 : (some ⟨N, hN⟩ : Option {M : Subgroup E // Nat.card M = p}) ≠ none := by simp
  have hne2 : (some ⟨M, hM⟩ : Option {M : Subgroup E // Nat.card M = p}) ≠ some ⟨N, hN⟩ :=
    fun h' => hMN (congrArg Subtype.val (Option.some.inj h'))
  have hH : orthSqSpan Q E ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthSqSpan_le_orthogonalGroup E
  have hs₀perp : ∀ u ∈ planeFixSpace E ⊔ lineSpace M, polar Q s₀ u = 0 := fun u hu => by
    obtain ⟨u₀, hu₀, u₁, hu₁, rfl⟩ := Submodule.mem_sup.1 hu
    have h0 := hK.orth _ _ hne1 s₀ hs₀N u₀ hu₀
    have h1 := hK.orth _ _ hne2.symm s₀ hs₀N u₁ hu₁
    rw [polarBilin_apply_apply] at h0 h1
    rw [polar_add_right, h0, h1, add_zero]
  have hall : ∀ y ∈ planeFixSpace E ⊔ lineSpace M, y ∈ rootSet Q (orthSqSpan Q E) s₀ := by
    refine mem_of_invariant (regular_sup hK hM) hPM (rootSet Q (orthSqSpan Q E) s₀)
      (fun e he w hw a ha _ => ?_) hbR (Submodule.mem_sup_right hbM) hb0
    have hgH : eichler Q e w ∈ orthSqSpan Q E :=
      orthSq_eichler_mem_of_mem_sup hEΩ hM0 he hw
    have hfix : eichler Q e w s₀ = s₀ :=
      eichler_apply_of_polar_eq_zero (polar_comm Q e s₀ ▸ hs₀perp e he)
        (polar_comm Q w s₀ ▸ hs₀perp w hw)
    have := rootSet_map hH hgH ha
    rwa [hfix] at this
  obtain ⟨g, hg, hgs⟩ := exists_mem_eichlerGroupOn_apply_eq_of_pairs (regular_sup hK hN)
    hPN (Submodule.mem_sup_right hs₀N) hsN hs₀0 hs0 (by rw [hs₀Q, hsQ])
  have hgH : g ∈ orthSqSpan Q E :=
    eichlerGroupOn_le (fun e he w hw => orthSq_eichler_mem_of_mem_sup hEΩ hN0 he hw) hg
  intro v hv
  have hgv : g v = v := eichlerGroupOn_apply_of_orth hg
    (fun u hu => polar_eq_zero_of_mem_sup hK hN hM hMN hv hu)
  have := rootSet_map hH hgH (hall v (Submodule.mem_sup_right hv))
  rwa [hgv, hgs] at this

theorem orthSq_elementaryGroup_le_of_pivots (hK : KernelLineData Q p E)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) (hp : p.Prime)
    (hQ : (polarBilin Q).Nondegenerate) {N : Subgroup E} (hN : Nat.card N = p)
    (hPN : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace N))
    (hpiv : ∀ M : Subgroup E, Nat.card M = p → M ≠ N → lineSpace M ≠ ⊥ →
      HasOrthPairs Q (planeFixSpace E ⊔ lineSpace M) ∧ ∃ s₀ ∈ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧
        ∃ b ∈ lineSpace M, b ≠ 0 ∧ b ∈ rootSet Q (orthSqSpan Q E) s₀) :
    elementaryGroup Q ≤ orthSqSpan Q E := by
  obtain ⟨a₁, f₁, a₂, f₂, ha₁, hf₁, -, -, hQa₁, hQf₁, -, -, h11, -⟩ := id hPN
  have center : ∀ s ∈ planeFixSpace E ⊔ lineSpace N, s ≠ 0 → Q s = 0 →
      IsRootCenter Q (orthSqSpan Q E) s := by
    intro s hsN hs0 hsQ
    refine orthSq_isRootCenter_of_pivots hK hEΩ hp hN hsN hs0 hsQ fun M hM hMN v hv => ?_
    by_cases hbot : lineSpace M = ⊥
    · rw [hbot, Submodule.mem_bot] at hv
      rw [hv]
      exact AddSubgroup.zero_mem _
    · obtain ⟨hPM, s₀, hs₀N, hs₀0, hs₀Q, b, hbM, hb0, hbR⟩ := hpiv M hM hMN hbot
      exact orthSq_rootSet_ge_of_pivot hK hEΩ hp hN hM hMN hPN hPM hs₀N hs₀0 hs₀Q hbM hb0 hbR hsN
        hs0 hsQ v hv
  have ha₁0 : a₁ ≠ 0 := fun h0 => by
    rw [h0, polar_zero_left] at h11
    exact zero_ne_one h11
  have hf₁0 : f₁ ≠ 0 := fun h0 => by
    rw [h0, polar_zero_right] at h11
    exact zero_ne_one h11
  exact elementaryGroup_le_of_hypPair hQ (orthSqSpan_le_orthogonalGroup E)
    ⟨a₁, f₁, hQa₁, hQf₁, h11⟩ (center a₁ ha₁ ha₁0 hQa₁) (center f₁ hf₁ hf₁0 hQf₁)

end Pivots

theorem orthSq_le_closure_of_normalized {P : Type} [Group P] [Finite P] {p n : ℕ}
    (hp : p.Prime) {E : Subgroup P} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    {Q : Subgroup P} (hnorm : ∀ e ∈ E, ∀ v ∈ Q, e * v * e⁻¹ ∈ Q) (hQp : ¬ p ∣ Nat.card Q)
    (hQn : ∀ v ∈ Q, v ^ n = 1) :
    Q ≤ Subgroup.closure {k : P | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k ∧ k ^ n = 1} := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hEel : CFSG.IsElementaryAbelian p E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by rw [Subgroup.coe_pow, hE.2 x x.2, Subgroup.coe_one]) }
  have hnt : Nontrivial E :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hcard]; exact Nat.one_lt_pow (by norm_num) hp.one_lt)
  have hAV : E ≤ Subgroup.normalizer (Q : Set P) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨fun hv => hnorm e he v hv, fun hv => ?_⟩
    have := hnorm e⁻¹ (E.inv_mem he) _ hv
    simpa [mul_assoc] using this
  have hgen := CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers (p := p) (A := E)
    (V := Q) hAV hQp
  refine hgen.trans (iSup₂_le fun B hB => ?_)
  intro k hk
  rw [Subgroup.mem_inf] at hk
  have hBcard : Nat.card B = p := by
    have h := B.card_mul_index
    rw [hB, hcard] at h
    have h2 : Nat.card B * p = p * p := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos h2
  have hBnt : Nontrivial B :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hBcard]; exact hp.one_lt)
  obtain ⟨b, hb⟩ := exists_ne (1 : B)
  refine Subgroup.subset_closure ⟨((b : E) : P), (b : E).2,
    fun h => hb (Subtype.ext (Subtype.ext h)), ?_, hQn k hk.1⟩
  exact (Subgroup.mem_centralizer_iff.1 hk.2 _ (Subgroup.mem_map_of_mem E.subtype b.2)).symm

section Parabolic

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
theorem orthSq_pow_sq_of_mem_qRad {X : Submodule K V}
    {hX : ∀ x ∈ X, Q x = 0} {g : V ≃ₗ[K] V} (hg : g ∈ qRad Q X hX) : g ^ (ringChar K ^ 2) = 1 := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hr : (ringChar K).Prime := by
    have := Fintype.ofFinite K
    exact CharP.char_is_prime K _
  set N : Module.End K V := autToEnd K V g - 1 with hNdef
  have hNx : ∀ x, N x = g x - x := fun x => by simp [hNdef, autToEnd_apply]
  have hN3 : N * N * N = 0 := by
    refine LinearMap.ext fun x => ?_
    have h1 : N x ∈ qPerp Q X := by rw [hNx]; exact hg1 x
    have h2 : N (N x) ∈ X := by rw [hNx]; exact hg2 _ h1
    have h3 : N (N (N x)) = 0 := by rw [hNx, hg3 _ h2, sub_self]
    simpa using h3
  have hg1' : autToEnd K V g = 1 + N := by rw [hNdef]; abel
  have hcast : ((ringChar K ^ 2 : ℕ) : K) = 0 := by
    rw [Nat.cast_pow, ringChar.Nat.cast_ringChar, zero_pow two_ne_zero]
  have hchoose : (((ringChar K ^ 2).choose 2 : ℕ) : K) = 0 :=
    (CharP.cast_eq_zero_iff K (ringChar K) _).mpr
      (hr.dvd_choose_pow two_ne_zero fun h => by have := hr.two_le; nlinarith)
  have hpow : autToEnd K V g ^ (ringChar K ^ 2) = 1 := by
    rw [hg1', unip_pow_of_cube_eq_zero (K := K) hN3, hcast, hchoose, zero_smul, zero_smul, add_zero,
      add_zero]
  have hpow' : autToEnd K V (g ^ (ringChar K ^ 2)) = 1 := by rw [map_pow, hpow]
  refine LinearEquiv.ext fun v => ?_
  have := LinearMap.congr_fun hpow' v
  rw [autToEnd_apply] at this
  exact this

theorem orthSq_closure_eq_top_of_singular_stable (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ringChar K) (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) {W : Submodule K V} (hW0 : W ≠ ⊥) (hW : ∀ x ∈ W, Q x = 0)
    (hstab : ∀ e ∈ E, ∀ w ∈ W, ((e : orthDerived Q) : V ≃ₗ[K] V) w ∈ W) :
    Subgroup.closure {h : orthDerived Q |
      ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ (ringChar K ^ 2) = 1} = ⊤ := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have hℓ : (ringChar K).Prime := by
      have := Fintype.ofFinite K
      exact CharP.char_is_prime K _
    have : ringChar K ∣ p := (CharP.cast_eq_zero_iff K (ringChar K) p).mp h0
    exact hpl ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp this).symm
  have hfinV : Finite V := Module.finite_of_finite K
  have hfinGL : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g => (g : V → V)) DFunLike.coe_injective
  obtain ⟨hGE, -⟩ := orthDerived_eq_and_le_closure hQ hT
  have hEΩ : elementaryGroup Q ≤ orthDerived Q := hGE.ge
  have hGO : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup Q
  have hEG : ∀ u w, eichler Q u w ∈ orthDerived Q := fun u w =>
    hEΩ (eichler_mem_elementaryGroup Q u w)
  set H : Subgroup (V ≃ₗ[K] V) := orthSqSpan Q E with hH
  have hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthSqSpan_le_orthogonalGroup E
  let ρ : E →* Module.End K V := (autToEnd K V).comp ((orthDerived Q).subtype.comp E.subtype)
  have hAc : ∀ a b : E, a * b = b * a := fun a b => Subtype.ext (hcomm _ a.2 _ b.2)
  have hAp : ∀ a : E, a ^ p = 1 := fun a => Subtype.ext (hexp _ a.2)
  have hAstab : ∀ a : E, ∀ w ∈ W, ρ a w ∈ W := fun a w hw => hstab a.1 a.2 w hw
  obtain ⟨F', hF'idx, hW1⟩ : ∃ F' : Subgroup E, F'.index = p ∧ hyperFixed ρ F' ⊓ W ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hmem := mem_iSup_hyperFixed_top hpK hAc hAp ρ W hAstab (k := 2) (by norm_num) hcard hm
    have hbot : (⨆ (F' : Subgroup E) (_ : F'.index = p), hyperFixed ρ F' ⊓ W) = ⊥ :=
      iSup_eq_bot.2 fun F' => iSup_eq_bot.2 fun hF' => hcon F' hF'
    rw [hbot] at hmem
    exact hm0 (by simpa using hmem)
  set C : Submodule K V := hyperFixed ρ F' with hC
  set X₁ : Submodule K V := hyperFixed ρ F' ⊓ W with hX₁
  have hX₁mem : ∀ v, v ∈ X₁ ↔ (∀ f ∈ F', ρ f v = v) ∧ v ∈ W := fun v => by
    rw [hX₁, Submodule.mem_inf, mem_hyperFixed]
  have hX₁C : X₁ ≤ C := inf_le_left
  have hX₁Q : ∀ x ∈ X₁, Q x = 0 := fun x hx => hW x ((hX₁mem x).1 hx).2
  let φ : F' →* (V ≃ₗ[K] V) := ((orthDerived Q).subtype.comp E.subtype).comp F'.subtype
  have hφ : ∀ f, φ f ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun f => hGO f.1.1.2
  have hqfix : qFix φ = C := by
    ext v
    rw [mem_qFix, hC, mem_hyperFixed]
    exact ⟨fun h n hn => h ⟨n, hn⟩, fun h f => h f.1 f.2⟩
  have : Fintype F' := Fintype.ofFinite F'
  have hcardF' : Nat.card F' = p := by
    have h := Subgroup.card_mul_index F'
    rw [hF'idx, hcard] at h
    have h2 : Nat.card F' * p = p * p := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos h2
  have hF : ((Fintype.card F' : ℕ) : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, hcardF']
    exact hpK
  have hF'nt : Nontrivial F' :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardF']; exact hp.one_lt)
  have hS : RootSetup Q H C := by
    refine ⟨hHO, hqfix ▸ polarNondegOn_qFix hQ hφ hF, fun v => ?_, fun u hu w hw => ?_⟩
    · exact ⟨qAvg φ v, hqfix ▸ qAvg_mem φ v, hqfix ▸ sub_qAvg_mem_qPerp hφ hF v⟩
    · obtain ⟨f₀, hf₀⟩ := exists_ne (1 : F')
      exact orthSq_eichler_mem_of_fix hEΩ f₀.1.2
        (fun h => hf₀ (Subtype.ext (Subtype.ext h))) (mem_hyperFixed.1 hu f₀ f₀.2)
        (mem_hyperFixed.1 hw f₀ f₀.2)
  set 𝒜 : Subgroup (V ≃ₗ[K] V) := E.map (orthDerived Q).subtype with h𝒜
  have h𝒜O : 𝒜 ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨x, -, rfl⟩
    exact hGO x.2
  have hC𝒜 : ∀ a ∈ 𝒜, ∀ c ∈ C, a c ∈ C := by
    rintro _ ⟨x, hx, rfl⟩ c hc
    exact apply_mem_hyperFixed hAc ⟨x, hx⟩ hc
  have hX₁𝒜 : ∀ a ∈ 𝒜, ∀ x ∈ X₁, a x ∈ X₁ := by
    rintro _ ⟨y, hy, rfl⟩ x hx
    rw [hX₁mem] at hx ⊢
    exact ⟨fun f hf => mem_hyperFixed.1 (apply_mem_hyperFixed hAc ⟨y, hy⟩
      (mem_hyperFixed.2 hx.1)) f hf, hAstab ⟨y, hy⟩ x hx.2⟩
  have hrad : ∀ X : Submodule K V, X ≤ C → (∀ x ∈ X, Q x = 0) →
      (∀ a ∈ 𝒜, ∀ x ∈ X, a x ∈ X) → ∀ x ∈ X, ∀ d ∈ qPerp Q X, eichler Q x d ∈ H := by
    intro X _ hXQ hX𝒜 x hx d hd
    set Qx : Subgroup (orthDerived Q) := (qRad Q X hXQ).comap (orthDerived Q).subtype with hQx
    have hnorm : ∀ e ∈ E, ∀ v ∈ Qx, e * v * e⁻¹ ∈ Qx := by
      intro e he v hv
      have haS : ∀ y ∈ X, ((e : orthDerived Q) : V ≃ₗ[K] V) y ∈ X := fun y hy =>
        hX𝒜 _ ⟨e, he, rfl⟩ y hy
      have haS' : ∀ y ∈ X, ((e : orthDerived Q) : V ≃ₗ[K] V)⁻¹ y ∈ X := fun y hy =>
        hX𝒜 _ ⟨e⁻¹, E.inv_mem he, rfl⟩ y hy
      exact qRad_conj_mem (hX := hXQ) (hGO e.2) haS haS' hv
    have hQp : ¬ p ∣ Nat.card Qx :=
      not_dvd_card_comap_qRad (hX := hXQ) hp hp2 hpK (orthDerived Q)
    have hQr : ∀ v ∈ Qx, v ^ (ringChar K ^ 2) = 1 := fun v hv =>
      Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact orthSq_pow_sq_of_mem_qRad (Subgroup.mem_comap.mp hv))
    have hle := orthSq_le_closure_of_normalized hp ⟨⟨⟨hAc⟩⟩, hexp⟩ hcard hnorm hQp hQr
    have hmem : (⟨eichler Q x d, hEG x d⟩ : orthDerived Q) ∈ Qx :=
      eichler_mem_qRad (hX := hXQ) hx hd
    rw [hH, orthSqSpan_eq_map]
    exact ⟨_, hle hmem, rfl⟩
  obtain ⟨e₀, he₀, he₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW1
  obtain ⟨a, b, ha, hb, hab⟩ := exists_rootCenter_pair hS h𝒜O hC𝒜 hrad hX₁C hX₁Q hX₁𝒜 he₀ he₀0
  let P₀ : HypPair Q :=
    { e := a
      f := (polar Q a b)⁻¹ • b
      Q_e := ha.2.1
      Q_f := by rw [map_smul_eq_sq, hb.2.1, mul_zero]
      polar_ef := by rw [polar_smul_right_eq, inv_mul_cancel₀ hab] }
  have hle : elementaryGroup Q ≤ H :=
    elementaryGroup_le_of_hypPair hQ hHO P₀ ha (hb.smul (inv_ne_zero hab))
  exact orthSq_closure_eq_top_of_le E (hGE.le.trans hle)

end Parabolic

section ManyTwo

open Polynomial

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)}

theorem orthSq_eichler_mem_of_plane (hEΩ : elementaryGroup Q ≤ orthDerived Q) {z : E}
    (hz1 : z ≠ 1)
    {e : V} (heQ : Q e = 0) {τ : K} (hτ : τ ≠ 0)
    (hrel : ((z : orthDerived Q) : V ≃ₗ[K] V) (((z : orthDerived Q) : V ≃ₗ[K] V) e) =
      τ • ((z : orthDerived Q) : V ≃ₗ[K] V) e - e)
    (hli : LinearIndependent K ![e, ((z : orthDerived Q) : V ≃ₗ[K] V) e]) :
    ∀ w ∈ Submodule.span K (Set.range ![e, ((z : orthDerived Q) : V ≃ₗ[K] V) e]),
      eichler Q e w ∈ orthSqSpan Q E := by
  classical
  set g : V ≃ₗ[K] V := ((z : orthDerived Q) : V ≃ₗ[K] V) with hg
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_mem_orthogonalGroup
  obtain ⟨hTQ, hTp⟩ := manyTwo_plane_facts hgO heQ hτ hrel
  set T := Submodule.span K (Set.range ![e, g e]) with hT
  have he : e ∈ T := Submodule.subset_span ⟨0, rfl⟩
  have hge : g e ∈ T := Submodule.subset_span ⟨1, rfl⟩
  have hT2 : finrank K T = 2 := by rw [hT, finrank_span_eq_card hli]; simp
  have hTg : ∀ t ∈ T, g t ∈ T := by
    intro t ht
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp ht
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul]
    rw [hrel]
    exact T.add_mem (T.smul_mem _ hge) (T.smul_mem _ (T.sub_mem (T.smul_mem _ hge) he))
  have hdet := manyTwo_det_restrict_pair hli hrel hTg
  intro w hw
  have hc := commute_eichler_of_det_one hgO hT2 hTQ hTp hTg hdet he hw
  exact orthSq_mem_of_commute (a := (z : orthDerived Q))
    (hEΩ (eichler_mem_elementaryGroup Q e w)) z.2 (fun h => hz1 (Subtype.ext h)) hc.eq
    (orthSq_eichler_pow_ringChar e w)


theorem orthSq_eichler_mem_of_pair_pieces (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hK : KernelLineData Q p E) (hEΩ : elementaryGroup Q ≤ orthDerived Q)
    (hNS : OrthNoInvariantSingular Q E) {M₁ M₂ : Subgroup E} (hM₁ : Nat.card M₁ = p)
    (hM₂ : Nat.card M₂ = p) (hM : M₁ ≠ M₂) {P₁ P₂ : Submodule K V} (hP₁ : IsPiece Q E P₁)
    (hP₂ : IsPiece Q E P₂) (h₁ : P₁ ≤ lineSpace M₁) (h₂ : P₂ ≤ lineSpace M₂)
    (hperp : OrthSep Q P₁ P₂) (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) :
    ∀ e ∈ P₁ ⊔ P₂, ∀ w ∈ P₁ ⊔ P₂, eichler Q e w ∈ orthSqSpan Q E := by
  classical
  obtain ⟨hp2, hpl⟩ := manyTwo_ne_two_and_ne_ringChar hp h2
  obtain ⟨x, y, τ, hτ, hnoroot, hcl, hx, hy⟩ :=
    exists_two_mixing_elements_aux hK hp hM₁ hM₂ hM hP₁ hP₂ h₁ h₂ h2
  set X : Submodule K V := P₁ ⊔ P₂ with hX
  have hXreg : PolarNondegOn Q X := polarNondegOn_sup hP₁.regular hP₂.regular hperp
  have hd₁ : finrank K P₁ = 2 := by
    obtain ⟨-, -, -, -, h, -⟩ := hP₁.exists_line hK hp hp2 hpl
    exact h.trans h2
  have hd₂ : finrank K P₂ = 2 := by
    obtain ⟨-, -, -, -, h, -⟩ := hP₂.exists_line hK hp hp2 hpl
    exact h.trans h2
  have hX4 : finrank K X = 4 := by
    have hdisj := OrthSep.disjoint hP₁.regular hperp
    have := Submodule.finrank_sup_add_finrank_inf_eq P₁ P₂
    rw [hdisj.eq_bot, finrank_bot, add_zero, ← hX] at this
    omega
  have hXst : ∀ z : E, ∀ u ∈ X, ((z : orthDerived Q) : V ≃ₗ[K] V) u ∈ X := by
    intro z u hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add]
    exact Submodule.add_mem_sup (hP₁.eStable z z.2 u₁ hu₁) (hP₂.eStable z z.2 u₂ hu₂)
  have hroot : ∀ e ∈ X, e ≠ 0 → Q e = 0 → ∀ w ∈ X, polar Q e w = 0 →
      eichler Q e w ∈ orthSqSpan Q E := by
    intro e heX he0 heQ w hwX hew
    have hrx := hx e heX
    have hry := hy e heX
    have hx1 : x ≠ 1 := by
      rintro rfl
      have h1 : e = τ • e - e := hrx
      have h3 : (τ - 2) • e = 0 := by linear_combination (norm := module) -h1
      have h4 : τ = 2 := sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right he0)
      exact hnoroot 1 (by rw [h4]; norm_num)
    have hy1 : y ≠ 1 := by
      rintro rfl
      have h1 : e = τ • e - e := hry
      have h3 : (τ - 2) • e = 0 := by linear_combination (norm := module) -h1
      have h4 : τ = 2 := sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right he0)
      exact hnoroot 1 (by rw [h4]; norm_num)
    have hlix := manyTwo_linearIndependent_pair he0 hrx hnoroot
    have hliy := manyTwo_linearIndependent_pair he0 hry hnoroot
    obtain ⟨hTxQ, hTxp⟩ := manyTwo_plane_facts
      (orthDerived_mem_orthogonalGroup (g := (x : orthDerived Q))) heQ hτ hrx
    obtain ⟨hTyQ, hTyp⟩ := manyTwo_plane_facts
      (orthDerived_mem_orthogonalGroup (g := (y : orthDerived Q))) heQ hτ hry
    set Tx := Submodule.span K (Set.range ![e, ((x : orthDerived Q) : V ≃ₗ[K] V) e]) with hTx
    set Ty := Submodule.span K (Set.range ![e, ((y : orthDerived Q) : V ≃ₗ[K] V) e]) with hTy
    have hexT : e ∈ Tx := Submodule.subset_span ⟨0, rfl⟩
    have hexT' : e ∈ Ty := Submodule.subset_span ⟨0, rfl⟩
    have hTx2 : finrank K Tx = 2 := by rw [hTx, finrank_span_eq_card hlix]; simp
    have hTy2 : finrank K Ty = 2 := by rw [hTy, finrank_span_eq_card hliy]; simp
    set S : Submodule K V := X ⊓ LinearMap.ker (polarBilin Q e) with hS
    have hmemS : ∀ v, v ∈ S ↔ v ∈ X ∧ polar Q e v = 0 := fun v => by
      rw [hS, Submodule.mem_inf, LinearMap.mem_ker, polarBilin_apply_apply]
    have hTxX : Tx ≤ X := by
      rw [hTx, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact heX
      · exact hXst x e heX
    have hTyX : Ty ≤ X := by
      rw [hTy, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact heX
      · exact hXst y e heX
    have hTxS : Tx ≤ S := fun v hv => (hmemS v).mpr ⟨hTxX hv, hTxp e hexT v hv⟩
    have hTyS : Ty ≤ S := fun v hv => (hmemS v).mpr ⟨hTyX hv, hTyp e hexT' v hv⟩
    have hSlt : S < X := by
      refine lt_of_le_of_ne inf_le_left fun hSX => ?_
      obtain ⟨u, huX, hu⟩ := hXreg.exists_polar_ne_zero heX he0
      have : u ∈ S := hSX ▸ huX
      exact hu ((hmemS u).mp this).2
    have hS3 : finrank K S ≤ 3 := by
      have := Submodule.finrank_lt_finrank_of_lt hSlt
      omega
    have hne : Tx ≠ Ty := by
      intro hxy
      have hTstx : ∀ t ∈ Tx, ((x : orthDerived Q) : V ≃ₗ[K] V) t ∈ Tx := by
        intro t ht
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp ht
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul]
        rw [hrx]
        have h1 : ((x : orthDerived Q) : V ≃ₗ[K] V) e ∈ Tx := Submodule.subset_span ⟨1, rfl⟩
        exact Tx.add_mem (Tx.smul_mem _ h1) (Tx.smul_mem _ (Tx.sub_mem (Tx.smul_mem _ h1) hexT))
      have hTsty : ∀ t ∈ Tx, ((y : orthDerived Q) : V ≃ₗ[K] V) t ∈ Tx := by
        intro t ht
        rw [hxy] at ht ⊢
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp ht
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul]
        rw [hry]
        have h1 : ((y : orthDerived Q) : V ≃ₗ[K] V) e ∈ Ty := Submodule.subset_span ⟨1, rfl⟩
        exact Ty.add_mem (Ty.smul_mem _ h1) (Ty.smul_mem _ (Ty.sub_mem (Ty.smul_mem _ h1) hexT'))
      have hst := manyTwo_eStable_of_closure hK hp.pos hcl hTstx hTsty
      have hbot := hNS Tx hst hTxQ
      rw [hbot] at hexT
      exact he0 ((Submodule.mem_bot K).mp hexT)
    have hinf : finrank K ↥(Tx ⊓ Ty) ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have e1 : Tx ⊓ Ty = Tx :=
        Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
      have e2 : Tx ⊓ Ty = Ty :=
        Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
      exact hne (e1.symm.trans e2)
    have hsup3 : 3 ≤ finrank K ↥(Tx ⊔ Ty) := by
      have := Submodule.finrank_sup_add_finrank_inf_eq Tx Ty
      omega
    have hSeq : Tx ⊔ Ty = S :=
      Submodule.eq_of_le_of_finrank_le (sup_le hTxS hTyS) (by omega)
    have hwS : w ∈ Tx ⊔ Ty := by rw [hSeq, hmemS]; exact ⟨hwX, hew⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hwS
    rw [← eichler_mul (hTxp e hexT a ha) (hTyp e hexT' b hb)]
    exact (orthSqSpan Q E).mul_mem
      (orthSq_eichler_mem_of_plane hEΩ hx1 heQ hτ hrx hlix a ha)
      (orthSq_eichler_mem_of_plane hEΩ hy1 heQ hτ hry hliy b hb)
  obtain ⟨u, huX, hu0, huQ⟩ := exists_singular_of_three_le_any (Q := Q) (S := X) (by omega)
  obtain ⟨u', hu'X, hu'Q, huu'⟩ := exists_partner_of_polarNondegOn hXreg huX hu0 huQ
  have hu'0 : u' ≠ 0 := fun h0 => by
    rw [h0, polar_zero_right] at huu'
    exact zero_ne_one huu'
  exact eichler_mem_of_relRoot (orthSqSpan_le_orthogonalGroup E) hXreg huX hu'X huQ hu'Q
    (by rw [huu']; exact one_ne_zero) (fun w hw hpw => hroot u huX hu0 huQ w hw hpw)
    (fun w hw hpw => hroot u' hu'X hu'0 hu'Q w hw hpw)

end ManyTwo

section ManyTwoMain

theorem orthSq_three_le_card {K : Type} [Field K] [Finite K] {p : ℕ} (hp5 : 5 ≤ p)
    (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) : 3 ≤ Nat.card K := by
  by_contra hlt
  push Not at hlt
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have hq : Nat.card K = 2 := by omega
  rw [hq] at h2
  have hsq : ((2 : ℕ) : ZMod p) ^ 2 = 1 := by
    have := pow_orderOf_eq_one ((2 : ℕ) : ZMod p)
    rwa [h2] at this
  have h3 : ((3 : ℕ) : ZMod p) = 0 := by
    have : ((3 : ℕ) : ZMod p) = ((2 : ℕ) : ZMod p) ^ 2 - 1 := by push_cast; ring
    rw [this, hsq, sub_self]
  have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 3 p).mp h3)
  omega

theorem orthSq_closure_eq_top_of_noSingular_two {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ringChar K) (hK3 : 3 ≤ Nat.card K)
    (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) (hNS : OrthNoInvariantSingular Q E)
    (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) :
    Subgroup.closure {h : orthDerived Q |
      ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ (ringChar K ^ 2) = 1} = ⊤ := by
  classical
  haveI : Nontrivial V := nontrivial_of_three_singular hT
  obtain ⟨hK, -⟩ := exists_kernelLineData_of_le hQ hp hp2 hpl E hcomm hexp hcard
  obtain ⟨n, P, hP, hPP, hPV, hPsp⟩ :=
    exists_piece_decomposition hQ hp hp2 hpl E hcomm hexp hcard hNS
  choose M hMc hMP hMk hMf _ _ using fun i => (hP i).exists_line hK hp hp2 hpl
  obtain ⟨a, b, hab⟩ := exists_pieces_diff_lines hK hp hpl hP hPsp (M := M)
    fun i => ⟨hMc i, hMP i⟩
  have hab' : a ≠ b := fun h => hab (h ▸ rfl)
  have hEΩ : elementaryGroup Q ≤ orthDerived Q := (orthDerived_eq_and_le_closure hQ hT).1.ge
  have hH : orthSqSpan Q E ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthSqSpan_le_orthogonalGroup E
  have hdimP : ∀ i, finrank K (P i) = 2 := fun i => (hMf i).trans h2
  have hV0reg : PolarNondegOn Q (planeFixSpace E) := polarNondegOn_planeFixSpace hK
  have haniso : ∀ i, ∀ t ∈ P i, Q t = 0 → t = 0 := fun i =>
    (hP i).anisotropic_of_orderOf_two_of_ne_two hK hp hp2 hpl h2
  have hV02 : finrank K (planeFixSpace E) ≤ 2 := finrank_planeFixSpace_le_two hNS
  have hcount : 7 ≤ finrank K (planeFixSpace E) + 2 * n := by
    have h1 : finrank K V ≤ finrank K ↥(planeFixSpace E ⊔ ⨆ i, P i) := by
      rw [← finrank_top K V]
      exact Submodule.finrank_mono hPsp
    have h3 := Submodule.finrank_add_le_finrank_add_finrank (planeFixSpace E) (⨆ i, P i)
    have h4 := manyTwo_finrank_iSup_fin_le P
    simp only [hdimP, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h4
    omega
  have hEichPair : ∀ i j : Fin n, i ≠ j → ∀ e ∈ P i ⊔ P j, ∀ w ∈ P i ⊔ P j,
      eichler Q e w ∈ orthSqSpan Q E := by
    intro i j hij
    by_cases hM : M i = M j
    · have hle : P i ⊔ P j ≤ planeFixSpace E ⊔ lineSpace (M i) := by
        refine sup_le ((hMP i).trans le_sup_right) ?_
        rw [hM]
        exact (hMP j).trans le_sup_right
      exact fun e he w hw => orthSq_eichler_mem_of_mem_sup hEΩ
        (ne_bot_of_card_prime hp (hMc i)) (hle he) (hle hw)
    · exact orthSq_eichler_mem_of_pair_pieces hQ hp hK hEΩ hNS (hMc i) (hMc j) hM (hP i) (hP j)
        (hMP i) (hMP j) (hPP i j hij) h2
  have hY : ∀ k : Fin n, k ≠ a → k ≠ b → ∃ Y : Submodule K V, P k ≤ Y ∧
      (planeFixSpace E ≠ ⊥ → planeFixSpace E ≤ Y) ∧ OrthSep Q Y (P a ⊔ P b) ∧
      PolarNondegOn Q Y ∧ (∀ e ∈ Y, ∀ w ∈ Y, eichler Q e w ∈ orthSqSpan Q E) ∧
      3 ≤ finrank K Y ∧ (finrank K Y = 3 → (2 : K) ≠ 0) := by
    intro k hka hkb
    have hkab : OrthSep Q (P k) (P a ⊔ P b) :=
      manyTwo_orthSep_sup_right (hPP k a hka) (hPP k b hkb)
    by_cases hV0 : planeFixSpace E = ⊥
    ·
      have hn4 : 4 ≤ n := by
        have : finrank K (planeFixSpace E) = 0 := by rw [hV0]; exact finrank_bot K V
        omega
      obtain ⟨l, hl⟩ := manyTwo_exists_fin_notMem (S := {a, b, k}) (m := 3) (by omega)
        Finset.card_le_three
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      obtain ⟨hla, hlb, hlk⟩ := hl
      have hkl : OrthSep Q (P k) (P l) := hPP k l (Ne.symm hlk)
      have hlab : OrthSep Q (P l) (P a ⊔ P b) :=
        manyTwo_orthSep_sup_right (hPP l a hla) (hPP l b hlb)
      have hdisj := OrthSep.disjoint (hP k).regular hkl
      have hdimY : finrank K ↥(P k ⊔ P l) = 4 := by
        have := Submodule.finrank_sup_add_finrank_inf_eq (P k) (P l)
        rw [hdisj.eq_bot, finrank_bot, add_zero, hdimP k, hdimP l] at this
        omega
      exact ⟨P k ⊔ P l, le_sup_left, fun h => absurd hV0 h, manyTwo_orthSep_sup_left hkab hlab,
        polarNondegOn_sup (hP k).regular (hP l).regular hkl,
        hEichPair k l (Ne.symm hlk), by omega, fun h => absurd h (by omega)⟩
    ·
      have hd0 : 1 ≤ finrank K (planeFixSpace E) := Submodule.one_le_finrank_iff.mpr hV0
      have hdisj := (hP k).disjoint.symm
      have hdimY : finrank K ↥(planeFixSpace E ⊔ P k) = finrank K (planeFixSpace E) + 2 := by
        have := Submodule.finrank_sup_add_finrank_inf_eq (planeFixSpace E) (P k)
        rw [hdisj.eq_bot, finrank_bot, add_zero, hdimP k] at this
        omega
      have hle : planeFixSpace E ⊔ P k ≤ planeFixSpace E ⊔ lineSpace (M k) :=
        sup_le le_sup_left ((hMP k).trans le_sup_right)
      refine ⟨planeFixSpace E ⊔ P k, le_sup_right, fun _ => le_sup_left,
        manyTwo_orthSep_sup_left (manyTwo_orthSep_sup_right (hPV a) (hPV b)) hkab,
        polarNondegOn_sup hV0reg (hP k).regular (hPV k),
        fun e he w hw => orthSq_eichler_mem_of_mem_sup hEΩ (ne_bot_of_card_prime hp (hMc k))
          (hle he) (hle hw), by omega, fun h3 => ?_⟩
      exact two_ne_zero_of_finrank_planeFixSpace hK (by omega)
  have hRoot : ∀ s ∈ P a ⊔ P b, s ≠ 0 → Q s = 0 →
      IsRootCenter Q (orthSqSpan Q E) s := by
    intro s hs hs0 hsQ
    have hrel : ∀ w ∈ P a ⊔ P b, polar Q s w = 0 → w ∈ rootSet Q (orthSqSpan Q E) s :=
      fun w hw hsw => ⟨hsw, hEichPair a b hab' s hs w hw⟩
    have hYR : ∀ k : Fin n, k ≠ a → k ≠ b → ∃ Y : Submodule K V, P k ≤ Y ∧
        (planeFixSpace E ≠ ⊥ → planeFixSpace E ≤ Y) ∧
        ∀ y ∈ Y, y ∈ rootSet Q (orthSqSpan Q E) s := by
      intro k hka hkb
      obtain ⟨Y, hPY, hV0Y, hYP, hYreg, hYH, hY3, h2Y⟩ := hY k hka hkb
      have hsY : ∀ y ∈ Y, polar Q s y = 0 := fun y hy => by
        rw [polar_comm]
        exact hYP y hy s hs
      have hmix := exists_mixed_vector hH (hP a).regular (hP b).regular (hP k).regular
        (hPP a b hab') (hPP a k (Ne.symm hka)) (hPP b k (Ne.symm hkb)) (hdimP a) (hdimP b)
        (hdimP k) (haniso a) (haniso b) (haniso k) hK3 hPY hYP
        (hEichPair b k (Ne.symm hkb)) hs hs0 hsQ hrel
      exact ⟨Y, hPY, hV0Y, manyTwo_subset_rootSet_of_pivot hH hYreg hY3 h2Y hYH hsY hmix⟩
    refine ⟨hs0, hsQ, fun w hsw => ?_⟩
    have hspan : (⊤ : Submodule K V) ≤ (P a ⊔ P b) ⊔
        (planeFixSpace E ⊔ ⨆ k : {k : Fin n // k ≠ a ∧ k ≠ b}, P k.1) := by
      refine hPsp.trans (sup_le ?_ (iSup_le fun i => ?_))
      · exact le_sup_of_le_right le_sup_left
      · by_cases hia : i = a
        · rw [hia]
          exact le_sup_of_le_left le_sup_left
        by_cases hib : i = b
        · rw [hib]
          exact le_sup_of_le_left le_sup_right
        · exact le_sup_of_le_right (le_sup_of_le_right
            (le_iSup (fun k : {k : Fin n // k ≠ a ∧ k ≠ b} => P k.1) ⟨i, hia, hib⟩))
    obtain ⟨w₁, hw₁, z, hz, rfl⟩ := Submodule.mem_sup.mp (hspan (Submodule.mem_top (x := w)))
    have hzR : polar Q s z = 0 ∧ z ∈ rootSet Q (orthSqSpan Q E) s := by
      obtain ⟨v₀, hv₀, z', hz', rfl⟩ := Submodule.mem_sup.mp hz
      have hv₀perp : polar Q s v₀ = 0 := by
        rw [polar_comm]
        exact manyTwo_orthSep_sup_right (hPV a) (hPV b) v₀ hv₀ s hs
      have hz'R : polar Q s z' = 0 ∧ z' ∈ rootSet Q (orthSqSpan Q E) s := by
        refine Submodule.iSup_induction (fun k : {k : Fin n // k ≠ a ∧ k ≠ b} => P k.1)
          (motive := fun x => polar Q s x = 0 ∧ x ∈ rootSet Q (orthSqSpan Q E) s) hz'
          ?_ ⟨polar_zero_right Q s, AddSubgroup.zero_mem _⟩ ?_
        · rintro ⟨k, hka, hkb⟩ x hx
          obtain ⟨Y, hPY, -, hYR'⟩ := hYR k hka hkb
          refine ⟨?_, hYR' x (hPY hx)⟩
          rw [polar_comm]
          exact manyTwo_orthSep_sup_right (hPP k a hka) (hPP k b hkb) x hx s hs
        · rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
          exact ⟨by rw [polar_add_right, hx1, hy1, add_zero], AddSubgroup.add_mem _ hx2 hy2⟩
      have hv₀R : v₀ ∈ rootSet Q (orthSqSpan Q E) s := by
        by_cases hV0 : planeFixSpace E = ⊥
        · rw [hV0] at hv₀
          rw [(Submodule.mem_bot K).mp hv₀]
          exact AddSubgroup.zero_mem _
        · have hn3 : 2 < n := by omega
          obtain ⟨k, hk⟩ := manyTwo_exists_fin_notMem (S := {a, b}) (m := 2) hn3 Finset.card_le_two
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
          obtain ⟨Y, -, hV0Y, hYR'⟩ := hYR k hk.1 hk.2
          exact hYR' v₀ (hV0Y hV0 hv₀)
      exact ⟨by rw [polar_add_right, hv₀perp, hz'R.1, add_zero],
        AddSubgroup.add_mem _ hv₀R hz'R.2⟩
    have hw₁perp : polar Q s w₁ = 0 := by
      rw [polar_add_right, hzR.1, add_zero] at hsw
      exact hsw
    exact (AddSubgroup.add_mem _ (hrel w₁ hw₁ hw₁perp) hzR.2).2
  have hXreg : PolarNondegOn Q (P a ⊔ P b) :=
    polarNondegOn_sup (hP a).regular (hP b).regular (hPP a b hab')
  have hX3 : 3 ≤ finrank K ↥(P a ⊔ P b) := by
    have hdisj := OrthSep.disjoint (hP a).regular (hPP a b hab')
    have := Submodule.finrank_sup_add_finrank_inf_eq (P a) (P b)
    rw [hdisj.eq_bot, finrank_bot, add_zero, hdimP a, hdimP b] at this
    omega
  obtain ⟨u, huX, hu0, huQ⟩ := exists_singular_of_three_le_any (Q := Q) hX3
  obtain ⟨u', hu'X, hu'Q, huu'⟩ := exists_partner_of_polarNondegOn hXreg huX hu0 huQ
  have hu'0 : u' ≠ 0 := fun h0 => by
    rw [h0, polar_zero_right] at huu'
    exact zero_ne_one huu'
  have hle : elementaryGroup Q ≤ orthSqSpan Q E :=
    elementaryGroup_le_of_hypPair hQ hH ⟨u, u', huQ, hu'Q, huu'⟩ (hRoot u huX hu0 huQ)
      (hRoot u' hu'X hu'0 hu'Q)
  exact orthSq_closure_eq_top_of_le E
    ((orthDerived_eq_and_le_closure hQ hT).1.le.trans hle)

end ManyTwoMain

section Mixing

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.ComponentInitial

theorem orthSq_transvectionUnit_pow_ringChar {K E W : Type*} [Field K] [Field E] [Algebra K E]
    [AddCommGroup W] [Module E W] (φ : W →ₗ[E] E) (w : W) (hφ : φ w = 0) :
    transvectionUnit φ w hφ ^ ringChar K = 1 := by
  have h0 : ((ringChar K : ℕ) : E) = 0 := by
    rw [← map_natCast (algebraMap K E), ringChar.Nat.cast_ringChar, map_zero]
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  change (1 + φ.smulRight w) ^ ringChar K = 1
  rw [CFSG.RankThree.PartTwo.Census.one_add_pow_of_mul_self_eq_zero (smulRight_mul_self φ w hφ),
    ← Nat.cast_smul_eq_nsmul E, h0, zero_smul, add_zero]

theorem orthSq_unitaryTransvection_eq {E W : Type*} [Field E] [AddCommGroup W]
    [Module E W] (H : W → W → E) (hadd₂ : ∀ u w w', H u (w + w') = H u w + H u w')
    (hsm₂ : ∀ (c : E) u w, H u (c • w) = c * H u w) {e : W} (he : H e e = 0) (a : E) :
    unitaryTransvection H hadd₂ hsm₂ he a =
      transvectionUnit (hermTransvectionForm H hadd₂ hsm₂ e a) e
        (by simp [hermTransvectionForm, he]) := rfl

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem orthSq_pow_ringChar_of_blockGL_eq (hx : OddOrderIsometry Q p x) {r : K[X]}
    [Fact (Irreducible r)] (hr : r ∈ primaryFactors x.toLinearMap)
    {φ : primaryComponent x.toLinearMap r →ₗ[AdjoinRoot r] AdjoinRoot r}
    {w : primaryComponent x.toLinearMap r} {hφ : φ w = 0} {g : ↥(supportedBlock Q x r)}
    (hg : blockGL Q x r g = transvectionUnit φ w hφ) : (g : V ≃ₗ[K] V) ^ ringChar K = 1 := by
  have h1 : blockGL Q x r (g ^ ringChar K) = blockGL Q x r 1 := by
    rw [map_pow, hg, map_one]
    exact orthSq_transvectionUnit_pow_ringChar (K := K) φ w hφ
  have h2 := hx.blockGL_injective hr h1
  have := congrArg Subtype.val h2
  simpa using this

theorem orthSq_exists_selfdual_mixing_family (hx : OddOrderIsometry Q p x) (hp2 : Odd p) {r : K[X]}
    [Fact (Irreducible r)] (hr : r ∈ primaryFactors x.toLinearMap) (hne1 : r ≠ X - 1)
    (hself : r = reciprocalPolynomial r) {S₁ S₂ : Submodule K V}
    (hS₂ : ∀ v ∈ S₂, x v ∈ S₂) (hperp : ∀ a ∈ S₁, ∀ b ∈ S₂, QuadraticMap.polar Q a b = 0)
    (u w : primaryComponent x.toLinearMap r) (hu : (u : V) ∈ S₁) (hw : (w : V) ∈ S₂)
    (hu0 : u ≠ 0) (hw0 : w ≠ 0) (hureg : PolarNondegOn Q (LinearMap.range (eline x r u)))
    (hwreg : PolarNondegOn Q (LinearMap.range (eline x r w))) :
    ∃ d : ℕ, r.natDegree = 2 * d ∧ ∃ c : AdjoinRoot r, c ≠ 0 ∧
      ∀ θ : AdjoinRoot r, frobPow K (AdjoinRoot r) d θ = -θ →
        ∃ g ∈ specialBlock Q x r, g ^ ringChar K = 1 ∧
          (∀ z : AdjoinRoot r, g (eline x r u z) =
            eline x r u ((1 + θ) * z) + eline x r w ((θ * c) * z)) ∧
          ∀ z z' : AdjoinRoot r, QuadraticMap.polar Q (eline x r u ((1 + θ) * z))
            (eline x r u ((1 + θ) * z')) =
            QuadraticMap.polar Q (eline x r u z) (eline x r u ((1 - θ ^ 2) * z')) := by
  obtain ⟨d, H, hdeg, -, htr, hadd₁, hadd₂, hsm₁, hsm₂, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hr hne1 hself
  have hfin : finrank K (AdjoinRoot r) = 2 * d := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible r).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, -, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot r) hfin
  have hfb : ∀ z, frobPow K (AdjoinRoot r) d z = hU.bar z := fun z => by
    rw [frobPow_apply, hbar]
  have hsm₁' : ∀ (c : AdjoinRoot r) u w, H (c • u) w = hU.bar c * H u w := fun c u w => by
    rw [hsm₁, hfb]
  have hsymm' : ∀ u w, H w u = hU.bar (H u w) := fun u w => by rw [hsymm, hfb]
  have hpolar : ∀ (y : primaryComponent x.toLinearMap r) (z z' : AdjoinRoot r),
      QuadraticMap.polar Q (eline x r y z) (eline x r y z') =
        Algebra.trace K (AdjoinRoot r) (hU.bar z * H y y * z') := by
    intro y z z'
    have h1 := htr (z • y) y z'
    rw [hsm₁'] at h1
    exact h1.symm
  have hHnz : ∀ y : primaryComponent x.toLinearMap r, y ≠ 0 →
      PolarNondegOn Q (LinearMap.range (eline x r y)) → H y y ≠ 0 := by
    intro y hy0 hyreg h0
    apply hy0
    have h1 : eline x r y 1 = 0 := hyreg _ ⟨1, rfl⟩ (by
      rintro _ ⟨z, rfl⟩
      rw [hpolar, h0, mul_zero, zero_mul, map_zero])
    rw [eline_apply, one_smul] at h1
    exact Subtype.ext h1
  have hHuu : H u u ≠ 0 := hHnz u hu0 hureg
  have hHww : H w w ≠ 0 := hHnz w hw0 hwreg
  have hHuw : H u w = 0 := by
    refine eq_zero_of_trace_mul_eq_zero K (AdjoinRoot r) fun c => ?_
    rw [htr u w c]
    exact hperp _ hu _ (smul_mem_of_stable hS₂ c w hw)
  have hHwu : H w u = 0 := by rw [hsymm' u w, hHuw, map_zero]
  have hHuu_fix : hU.bar (H u u) = H u u := (hsymm' u u).symm
  have hHww_fix : hU.bar (H w w) = H w w := (hsymm' w w).symm
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : AdjoinRoot r, f₀ = -(H u u) / H w w := ⟨_, rfl⟩
  have hf₀0 : f₀ ≠ 0 := by
    rw [hf₀]
    exact div_ne_zero (neg_ne_zero.mpr hHuu) hHww
  have hf₀fix : hU.bar f₀ = f₀ := by
    rw [hf₀, map_div₀, map_neg, hHuu_fix, hHww_fix]
  obtain ⟨c, hc⟩ := hU.normHom_surjective ⟨f₀, hU.mem_fixedField.mpr hf₀fix⟩
  have hcn : c * hU.bar c = f₀ := congrArg Subtype.val hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hf₀0 (by rw [← hcn, zero_mul])
  have he : H (u + c • w) (u + c • w) = 0 := by
    simp only [hadd₁, hadd₂, hsm₁', hsm₂, hHuw, hHwu, mul_zero, add_zero, zero_add]
    have : hU.bar c * (c * H w w) = f₀ * H w w := by rw [← hcn]; ring
    rw [this, hf₀, div_mul_cancel₀ _ hHww, add_neg_cancel]
  refine ⟨d, hdeg, c, hc0, fun θ hθ => ?_⟩
  have hθ' : hU.bar θ = -θ := by rw [← hfb]; exact hθ
  obtain ⟨a, ha⟩ : ∃ a : AdjoinRoot r, a = θ * (H u u)⁻¹ := ⟨_, rfl⟩
  have haσ : hU.bar a = -a := by
    rw [ha, map_mul, map_inv₀, hHuu_fix, hθ', neg_mul]
  have haH : a * H u u = θ := by rw [ha, mul_assoc, inv_mul_cancel₀ hHuu, mul_one]
  have hpres : ∀ y y' : primaryComponent x.toLinearMap r,
      H (((unitaryTransvection H hadd₂ hsm₂ he a : BlockGL x r) :
          Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r)) y)
        (((unitaryTransvection H hadd₂ hsm₂ he a : BlockGL x r) :
          Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r)) y') = H y y' := by
    intro y y'
    rw [unitaryTransvection_apply, unitaryTransvection_apply]
    exact hermitian_transvection_preserves hU.bar H hadd₁ hadd₂ hsm₁' hsm₂ hsymm' he haσ y y'
  obtain ⟨g, hg⟩ := (hx.mem_range_blockGL_selfDual_iff hr hne1 hself H htr
    (unitaryTransvection H hadd₂ hsm₂ he a)).mpr hpres
  have hact : ∀ z : AdjoinRoot r,
      (((unitaryTransvection H hadd₂ hsm₂ he a : BlockGL x r) :
          Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r)) (z • u)) =
        ((1 + θ) * z) • u + ((θ * c) * z) • w := by
    intro z
    have hHe : H (u + c • w) (z • u) = z * H u u := by
      rw [hadd₁, hsm₁', hsm₂, hsm₂, hHwu, mul_zero, mul_zero, add_zero]
    rw [unitaryTransvection_apply, hHe, ← haH]
    module
  have hgr : g.1 ^ ringChar K = 1 :=
    orthSq_pow_ringChar_of_blockGL_eq hx hr (orthSq_unitaryTransvection_eq H hadd₂ hsm₂ he a ▸ hg)
  refine ⟨g.1, mem_specialBlock.mpr ⟨g.2, ?_⟩, hgr, fun z => ?_, fun z z' => ?_⟩
  · rw [blockDet_apply, hg]
    exact det_unitaryTransvection H hadd₂ hsm₂ he a
  · have h1 := coe_blockGL (Q := Q) (x := x) r g (z • u)
    rw [hg, hact, Submodule.coe_add] at h1
    exact h1.symm
  · have hbar1 : hU.bar (1 + θ) = 1 - θ := by rw [map_add, map_one, hθ']; ring
    rw [hpolar, hpolar, map_mul hU.bar (1 + θ) z, hbar1]
    congr 1
    ring

theorem orthSq_exists_trace_zero {r : K[X]} [Fact (Irreducible r)] {d : ℕ}
    (hfin : finrank K (AdjoinRoot r) = 2 * d) (hcard : 4 < Nat.card (AdjoinRoot r)) :
    ∃ θ : AdjoinRoot r, frobPow K (AdjoinRoot r) d θ = -θ ∧ θ ≠ 0 ∧ 1 + θ ≠ 0 := by
  classical
  obtain ⟨ℓ, f, hU, -, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot r) hfin
  have hfb : ∀ z, frobPow K (AdjoinRoot r) d z = hU.bar z := fun z => by
    rw [frobPow_apply, hbar]
  by_cases h2 : (2 : AdjoinRoot r) = 0
  · obtain ⟨f₁, hf₁fix, hf₁0, hf₁1⟩ :
        ∃ f₁ : AdjoinRoot r, hU.bar f₁ = f₁ ∧ f₁ ≠ 0 ∧ f₁ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hsub : (Set.univ : Set hU.fixedField) ⊆ {0, 1} := by
        intro y _
        by_cases hy : (y : AdjoinRoot r) = 0
        · exact Or.inl (Subtype.ext hy)
        · exact Or.inr (Subtype.ext (hcon y (hU.mem_fixedField.mp y.2) hy))
      have hle : Nat.card hU.fixedField ≤ 2 := by
        have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
        rw [Set.ncard_univ] at h1
        exact h1.trans ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
      have h3 : Nat.card (AdjoinRoot r) = Nat.card hU.fixedField ^ 2 := by
        rw [hU.card, hU.card_fixedField, ← pow_mul, mul_comm]
      have h4 : Nat.card hU.fixedField ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    refine ⟨f₁, ?_, hf₁0, fun h0 => hf₁1 ?_⟩
    · rw [hfb, hf₁fix]
      linear_combination f₁ * h2
    · linear_combination h0 - h2
  · obtain ⟨z, hz⟩ := hU.exists_bar_ne
    refine ⟨z - hU.bar z, ?_, sub_ne_zero.mpr (Ne.symm hz), fun h0 => h2 ?_⟩
    · rw [hfb, map_sub, hU.bar_bar]
      ring
    · have h1 := congrArg hU.bar h0
      rw [map_add, map_one, map_sub, hU.bar_bar, map_zero] at h1
      linear_combination h0 + h1

end Mixing

section PivotsMix

open Polynomial

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)}

omit [Finite K] [FiniteDimensional K V] in
theorem orthSq_exists_pivot_of_data_gen (hK : KernelLineData Q p E) (hp : p.Prime)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) {L N : Subgroup E} (hL : Nat.card L = p)
    (hN : Nat.card N = p) (hLN : L ≠ N) {g : V ≃ₗ[K] V} (hgH : g ∈ orthSqSpan Q E)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {σ w a₁ a₂ p₁ p₂ s t : V}
    (hσU : σ ∈ planeFixSpace E ⊔ lineSpace L) (hwU : w ∈ planeFixSpace E ⊔ lineSpace L)
    (hQσ : Q σ = 0) (hQw : Q w = 0) (hσw : polar Q σ w = 0) (ha₁ : a₁ ∈ lineSpace L)
    (ha₂ : a₂ ∈ lineSpace L) (hp₂ : p₂ ∈ planeFixSpace E ⊔ lineSpace N)
    (hgσ : g σ = a₁ + p₁) (hgw : g w = a₂ + p₂) (ha₂0 : a₂ ≠ 0)
    (hsP : s ∈ planeFixSpace E ⊔ lineSpace N) (htP : t ∈ planeFixSpace E ⊔ lineSpace N)
    (hs0 : s ≠ 0) (hsQ : Q s = 0) (hs1 : polar Q s p₁ = 0) (hs2 : polar Q s p₂ = 0)
    (hs3 : polar Q s t = 0) (htw : polar Q t p₂ = 0) (htσ : polar Q t p₁ ≠ 0) :
    ∃ s₀ ∈ planeFixSpace E ⊔ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧ ∃ b ∈ lineSpace L, b ≠ 0 ∧
      b ∈ rootSet Q (orthSqSpan Q E) s₀ := by
  classical
  have hN0 : N ≠ ⊥ := ne_bot_of_card_prime hp hN
  have hL0 : L ≠ ⊥ := ne_bot_of_card_prime hp hL
  have hLP : ∀ a ∈ lineSpace L, ∀ y ∈ planeFixSpace E ⊔ lineSpace N, polar Q a y = 0 :=
    fun a ha y hy => polar_eq_zero_of_mem_sup hK hN hL hLN ha hy
  have hOg := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO
  have hQg := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO
  have hθ : polar Q (g σ) t ≠ 0 := by
    rw [hgσ, polar_add_left, hLP a₁ ha₁ t htP, zero_add, polar_comm]
    exact htσ
  have hcomm := eichler_conj_pivot (Q := Q) (σ := g σ) (w := g w) (s := s) (t := t)
    (by rw [hQg, hQσ]) (by rw [hQg, hQw]) hsQ (by rw [hOg, hσw])
    (by rw [hgσ, polar_add_left, hLP a₁ ha₁ s hsP, zero_add, polar_comm, hs1])
    (by rw [hgw, polar_add_left, hLP a₂ ha₂ s hsP, zero_add, polar_comm, hs2]) hs3
    (by rw [hgw, polar_add_left, hLP a₂ ha₂ t htP, zero_add, polar_comm, htw])
  have hY : eichler Q s t ∈ orthSqSpan Q E := orthSq_eichler_mem_of_mem_sup hEΩ hN0 hsP htP
  have hZ : eichler Q (g σ) (g w) ∈ orthSqSpan Q E := by
    rw [← eichler_conj hgO]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgH (orthSq_eichler_mem_of_mem_sup hEΩ hL0 hσU hwU))
      (Subgroup.inv_mem _ hgH)
  have hW : eichler Q (g w) (polar Q (g σ) t • s) ∈ orthSqSpan Q E := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hZ)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hY hZ) (Subgroup.inv_mem _ hY))
    rw [hcomm, ← mul_assoc, inv_mul_cancel, one_mul] at this
    exact this
  set θ : K := polar Q (g σ) t with hθdef
  have hQw' : Q (g w) = 0 := by rw [hQg, hQw]
  have hQs' : Q (θ • s) = 0 := by rw [map_smul_eq_sq, hsQ, mul_zero]
  have hpol : polar Q (g w) (θ • s) = 0 := by
    rw [polar_smul_right_eq, hgw, polar_add_left, hLP a₂ ha₂ s hsP, zero_add, polar_comm, hs2,
      mul_zero]
  have hdec : -(g w) = -p₂ + -a₂ := by
    rw [hgw]
    abel
  have hv1 : polar Q (θ • s) (-p₂) = 0 := by
    rw [polar_smul_left_eq, polar_neg_right, hs2]
    ring
  have hv2 : polar Q (θ • s) (-a₂) = 0 := by
    rw [polar_smul_left_eq, polar_neg_right, polar_comm Q s a₂, hLP a₂ ha₂ s hsP]
    ring
  have hmulE : eichler Q (θ • s) (-p₂) * eichler Q (θ • s) (-a₂) =
      eichler Q (θ • s) (-(g w)) := by
    rw [eichler_mul hv1 hv2, ← hdec]
  have hθsP : θ • s ∈ planeFixSpace E ⊔ lineSpace N := Submodule.smul_mem _ _ hsP
  have hE1 : eichler Q (θ • s) (-p₂) ∈ orthSqSpan Q E :=
    orthSq_eichler_mem_of_mem_sup hEΩ hN0 hθsP (Submodule.neg_mem _ hp₂)
  have hE2 : eichler Q (θ • s) (-(g w)) ∈ orthSqSpan Q E := by
    rw [← eichler_swap hQw' hQs' hpol]
    exact hW
  have hE3 : eichler Q (θ • s) (-a₂) ∈ orthSqSpan Q E := by
    have : eichler Q (θ • s) (-a₂) =
        (eichler Q (θ • s) (-p₂))⁻¹ * eichler Q (θ • s) (-(g w)) := by
      rw [← hmulE]
      group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hE1) hE2
  refine ⟨θ • s, hθsP, smul_ne_zero hθ hs0, hQs', -a₂, (lineSpace L).neg_mem ha₂,
    neg_ne_zero.mpr ha₂0, ?_, hE3⟩
  rw [polar_smul_left_eq, polar_neg_right, polar_comm Q s a₂, hLP a₂ ha₂ s hsP]
  ring

theorem orthSq_exists_pivot_center_lineSpace (hK : KernelLineData Q p E)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) (hp : p.Prime) {L N : Subgroup E}
    (hL : Nat.card L = p) (hN : Nat.card N = p) (hLN : L ≠ N)
    (hPN : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace N)) (h3N : 3 ≤ finrank K ↥(lineSpace N))
    (hpiv : ∃ s₀ ∈ planeFixSpace E ⊔ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧ ∃ b ∈ lineSpace L,
      b ≠ 0 ∧ b ∈ rootSet Q (orthSqSpan Q E) s₀) :
    ∃ s₀ ∈ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧ ∃ b ∈ lineSpace L, b ≠ 0 ∧
      b ∈ rootSet Q (orthSqSpan Q E) s₀ := by
  obtain ⟨s₀, hs₀P, hs₀0, hs₀Q, b, hbL, hb0, hbR⟩ := hpiv
  obtain ⟨s₁, hs₁N, hs₁0, hs₁Q⟩ := exists_singular_of_three_le_any (Q := Q) h3N
  have hN0 : N ≠ ⊥ := ne_bot_of_card_prime hp hN
  obtain ⟨g, hg, hgs⟩ := exists_mem_eichlerGroupOn_apply_eq_of_pairs (regular_sup hK hN) hPN hs₀P
    (Submodule.mem_sup_right hs₁N) hs₀0 hs₁0 (by rw [hs₀Q, hs₁Q])
  have hgH : g ∈ orthSqSpan Q E :=
    eichlerGroupOn_le (fun e he w hw => orthSq_eichler_mem_of_mem_sup hEΩ hN0 he hw) hg
  have hgb : g b = b := eichlerGroupOn_apply_of_orth hg
    (fun u hu => polar_eq_zero_of_mem_sup hK hN hL hLN hbL hu)
  have := rootSet_map (orthSqSpan_le_orthogonalGroup E) hgH hbR
  rw [hgb, hgs] at this
  exact ⟨s₁, hs₁N, hs₁0, hs₁Q, b, hbL, hb0, this⟩

theorem orthSq_exists_pivot_of_triple (hK : KernelLineData Q p E)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) (hp : p.Prime) {L N : Subgroup E}
    (hL : Nat.card L = p) (hN : Nat.card N = p) (hLN : L ≠ N)
    (hPN : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace N)) (h3N : 3 ≤ finrank K ↥(lineSpace N))
    {g : V ≃ₗ[K] V} (hgH : g ∈ orthSqSpan Q E)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {σ w a₁ a₂ p₁ p₂ s : V}
    (hσU : σ ∈ planeFixSpace E ⊔ lineSpace L) (hwU : w ∈ planeFixSpace E ⊔ lineSpace L)
    (hQσ : Q σ = 0) (hQw : Q w = 0) (hσw : polar Q σ w = 0) (ha₁ : a₁ ∈ lineSpace L)
    (ha₂ : a₂ ∈ lineSpace L) (hp₁ : p₁ ∈ planeFixSpace E ⊔ lineSpace N)
    (hp₂ : p₂ ∈ planeFixSpace E ⊔ lineSpace N)
    (hgσ : g σ = a₁ + p₁) (hgw : g w = a₂ + p₂) (ha₂0 : a₂ ≠ 0)
    (hsP : s ∈ planeFixSpace E ⊔ lineSpace N) (hs0 : s ≠ 0) (hsQ : Q s = 0)
    (hs1 : polar Q s p₁ = 0) (hs2 : polar Q s p₂ = 0) (hind : ∀ c₁ c₂ : K, p₁ ≠ c₁ • s + c₂ • p₂) :
    ∃ s₀ ∈ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧ ∃ b ∈ lineSpace L, b ≠ 0 ∧
      b ∈ rootSet Q (orthSqSpan Q E) s₀ := by
  have hPreg : PolarNondegOn Q (planeFixSpace E ⊔ lineSpace N) :=
    OrthBlk.polarNondegOn_of_nondegenerate (regular_sup hK hN)
  obtain ⟨t, htP, hts, htw, htσ⟩ := exists_perp_not_perp_two hPreg hp₁ hsP hp₂ hind
  exact orthSq_exists_pivot_center_lineSpace hK hEΩ hp hL hN hLN hPN h3N
    (orthSq_exists_pivot_of_data_gen hK hp hEΩ hL hN hLN hgH hgO hσU hwU hQσ hQw hσw ha₁ ha₂ hp₂ hgσ
      hgw ha₂0 hsP htP hs0 hsQ hs1 hs2 (by rw [polar_comm]; exact hts) htw htσ)

theorem orthSq_exists_pivot_of_mixing_gen (hK : KernelLineData Q p E) (hp : p.Prime)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) {L N : Subgroup E} (hL : Nat.card L = p)
    (hN : Nat.card N = p) (hLN : L ≠ N) (haniso : ∀ e ∈ planeFixSpace E, Q e = 0 → e = 0)
    {W : Type} [AddCommGroup W] [Module K W] (ιA ιB : W →ₗ[K] V) (α β : W →ₗ[K] W)
    (hιA : Function.Injective ιA) (hιB : Function.Injective ιB) (hα : Function.Injective α)
    (hβ : Function.Injective β) (hLA : lineSpace L = LinearMap.range ιA)
    (g : V ≃ₗ[K] V) (hgH : g ∈ orthSqSpan Q E)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg0 : ∀ v ∈ planeFixSpace E, g v = v)
    (hgact : ∀ z, g (ιA z) = ιA (α z) + ιB (β z)) (hιBN : ∀ z, ιB z ∈ lineSpace N)
    (h5L : 5 ≤ finrank K ↥(planeFixSpace E ⊔ lineSpace L))
    (h5N : 5 ≤ finrank K ↥(planeFixSpace E ⊔ lineSpace N)) (h3N : 3 ≤ finrank K ↥(lineSpace N)) :
    ∃ s₀ ∈ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧ ∃ b ∈ lineSpace L, b ≠ 0 ∧
      b ∈ rootSet Q (orthSqSpan Q E) s₀ := by
  classical
  have hU₀reg : PolarNondegOn Q (planeFixSpace E ⊔ lineSpace L) :=
    OrthBlk.polarNondegOn_of_nondegenerate (regular_sup hK hL)
  have hPreg : PolarNondegOn Q (planeFixSpace E ⊔ lineSpace N) :=
    OrthBlk.polarNondegOn_of_nondegenerate (regular_sup hK hN)
  have hPN : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace N) := hasOrthPairs_of_dim hPreg h5N
  have hιAL : ∀ z, ιA z ∈ lineSpace L := fun z => hLA ▸ ⟨z, rfl⟩
  have hdisj : Disjoint (planeFixSpace E) (lineSpace N) := disjoint_planeFixSpace_lineSpace hK hN
  obtain ⟨σ, f₁, w, f₂, hσU, hf₁U, hwU, hf₂U, hQσ, hQf₁, hQw, hQf₂, h11, h22, h12, h1f2, hf1w,
    hf1f2⟩ := hasOrthPairs_of_dim hU₀reg h5L
  obtain ⟨σ₀, hσ₀, σL, hσL, hσeq⟩ := Submodule.mem_sup.mp hσU
  obtain ⟨w₀, hw₀, wL, hwL, hweq⟩ := Submodule.mem_sup.mp hwU
  rw [hLA] at hσL hwL
  obtain ⟨z₁, hz₁⟩ := hσL
  obtain ⟨z₂, hz₂⟩ := hwL
  have hσdec : σ = σ₀ + ιA z₁ := by rw [hz₁, hσeq]
  have hwdec : w = w₀ + ιA z₂ := by rw [hz₂, hweq]
  have hwf1 : polar Q w f₁ = 0 := by rw [polar_comm]; exact hf1w
  have hz₂0 : z₂ ≠ 0 := by
    intro h0
    have hw0 : w = w₀ := by rw [hwdec, h0, map_zero, add_zero]
    have : w = 0 := haniso w (hw0 ▸ hw₀) hQw
    have := h22
    rw [‹w = 0›, polar_zero_left] at this
    exact zero_ne_one this
  have hind : ∀ c : K, z₁ ≠ c • z₂ := by
    intro c hc
    have hσc : σ - c • w = σ₀ - c • w₀ := by
      rw [hσdec, hwdec, hc, map_smul]
      module
    have hmem : σ - c • w ∈ planeFixSpace E := by
      rw [hσc]; exact (planeFixSpace E).sub_mem hσ₀ ((planeFixSpace E).smul_mem _ hw₀)
    have hQ0 : Q (σ - c • w) = 0 := by
      rw [map_sub_smul', hQσ, hQw, h12]; ring
    have h0 : σ - c • w = 0 := haniso _ hmem hQ0
    have := congrArg (fun v => polar Q v f₁) h0
    simp only [polar_sub_left, polar_smul_left_eq, polar_zero_left, h11, hwf1] at this
    simp at this
  obtain ⟨p₁, hp₁def⟩ : ∃ p₁ : V, p₁ = σ₀ + ιB (β z₁) := ⟨_, rfl⟩
  obtain ⟨p₂, hp₂def⟩ : ∃ p₂ : V, p₂ = w₀ + ιB (β z₂) := ⟨_, rfl⟩
  have hp₁P : p₁ ∈ planeFixSpace E ⊔ lineSpace N := hp₁def ▸ Submodule.add_mem_sup hσ₀ (hιBN _)
  have hp₂P : p₂ ∈ planeFixSpace E ⊔ lineSpace N := hp₂def ▸ Submodule.add_mem_sup hw₀ (hιBN _)
  have hgσ : g σ = ιA (α z₁) + p₁ := by
    rw [hσdec, map_add, hg0 σ₀ hσ₀, hgact, hp₁def]
    abel
  have hgw : g w = ιA (α z₂) + p₂ := by
    rw [hwdec, map_add, hg0 w₀ hw₀, hgact, hp₂def]
    abel
  have hli : ∀ c₁ c₂ : K, c₁ • p₁ + c₂ • p₂ = 0 → c₁ = 0 ∧ c₂ = 0 := by
    intro c₁ c₂ h0
    have h1 : (c₁ • σ₀ + c₂ • w₀) + ιB (β (c₁ • z₁ + c₂ • z₂)) = 0 := by
      rw [← h0, hp₁def, hp₂def]
      simp only [map_add, map_smul]
      module
    have hmem0 : c₁ • σ₀ + c₂ • w₀ ∈ planeFixSpace E :=
      (planeFixSpace E).add_mem ((planeFixSpace E).smul_mem _ hσ₀)
        ((planeFixSpace E).smul_mem _ hw₀)
    have h2 : c₁ • σ₀ + c₂ • w₀ = 0 :=
      Submodule.disjoint_def.mp hdisj _ hmem0 (by
        rw [eq_neg_of_add_eq_zero_left h1]
        exact (lineSpace N).neg_mem (hιBN _))
    have h3 : c₁ • z₁ + c₂ • z₂ = 0 := by
      rw [h2, zero_add] at h1
      have h4 : β (c₁ • z₁ + c₂ • z₂) = 0 := hιB (by rw [h1, map_zero])
      exact hβ (by rw [h4, map_zero])
    have hc₁ : c₁ = 0 := by
      by_contra hc
      refine hind (-(c₁⁻¹ * c₂)) ?_
      have h5 : c₁ • z₁ = -(c₂ • z₂) := eq_neg_of_add_eq_zero_left h3
      calc z₁ = c₁⁻¹ • (c₁ • z₁) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        _ = (-(c₁⁻¹ * c₂)) • z₂ := by rw [h5, smul_neg, smul_smul, neg_smul]
    refine ⟨hc₁, ?_⟩
    rw [hc₁, zero_smul, zero_add] at h3
    exact (smul_eq_zero.mp h3).resolve_right hz₂0
  obtain ⟨s, hsP, hs0, hsQ, hsF⟩ := exists_singular_in_kernel_fin (Q := Q) (n := 2) (by omega)
    ![(polarBilin Q).flip p₁, (polarBilin Q).flip p₂]
  have hs1 : polar Q s p₁ = 0 := by simpa [polarBilin_apply_apply] using hsF 0
  have hs2 : polar Q s p₂ = 0 := by simpa [polarBilin_apply_apply] using hsF 1
  have hss : polar Q s s = 0 := polar_self_eq_zero hsQ
  have ha₂0 : ιA (α z₂) ≠ 0 := (map_ne_zero_iff ιA hιA).mpr ((map_ne_zero_iff α hα).mpr hz₂0)
  by_cases hcase : ∃ c₁ c₂ : K, p₁ = c₁ • s + c₂ • p₂
  · obtain ⟨c₁, c₂, hc⟩ := hcase
    have hc₁ : c₁ ≠ 0 := by
      rintro rfl
      exact one_ne_zero (hli 1 (-c₂) (by rw [hc]; module)).1
    have hŝU : c₁⁻¹ • (σ - c₂ • w) ∈ planeFixSpace E ⊔ lineSpace L :=
      Submodule.smul_mem _ _ (Submodule.sub_mem _ hσU (Submodule.smul_mem _ _ hwU))
    have hQŝ : Q (c₁⁻¹ • (σ - c₂ • w)) = 0 := by
      rw [map_smul_eq_sq, map_sub_smul', hQσ, hQw, h12]
      ring
    have hσŝ : polar Q σ (c₁⁻¹ • (σ - c₂ • w)) = 0 := by
      rw [polar_smul_right_eq, polar_sub_right, polar_smul_right_eq, polar_self_eq_zero hQσ, h12]
      ring
    have hwŝ : polar Q w (c₁⁻¹ • (σ - c₂ • w)) = 0 := by
      rw [polar_smul_right_eq, polar_sub_right, polar_smul_right_eq, polar_self_eq_zero hQw,
        polar_comm Q w σ, h12]
      ring
    have hgŝ : g (c₁⁻¹ • (σ - c₂ • w)) =
        ιA (α (c₁⁻¹ • (z₁ - c₂ • z₂))) + s := by
      have h1 : p₁ - c₂ • p₂ = c₁ • s := by rw [hc]; module
      have h2 : s = c₁⁻¹ • (p₁ - c₂ • p₂) := by rw [h1, smul_smul, inv_mul_cancel₀ hc₁, one_smul]
      rw [map_smul, map_sub, map_smul, hgσ, hgw, h2]
      simp only [map_smul, map_sub]
      module
    have hâ0 : ιA (α (c₁⁻¹ • (z₁ - c₂ • z₂))) ≠ 0 := by
      refine (map_ne_zero_iff ιA hιA).mpr ((map_ne_zero_iff α hα).mpr ?_)
      exact smul_ne_zero (inv_ne_zero hc₁) (sub_ne_zero.mpr (hind c₂))
    by_cases hc₂ : c₂ = 0
    ·
      refine orthSq_exists_pivot_of_triple hK hEΩ hp hL hN hLN hPN h3N hgH hgO (σ := w)
        (w := c₁⁻¹ • (σ - c₂ • w)) hwU hŝU hQw hQŝ hwŝ (hιAL _) (hιAL _) hp₂P hsP hgw hgŝ hâ0
        hsP hs0 hsQ hs2 hss ?_
      intro d₁ d₂ hd
      have h1 : p₂ = (d₁ + d₂) • s := by rw [hd]; module
      have h2 : p₁ = c₁ • s := by rw [hc, hc₂]; module
      have := hli (-(d₁ + d₂)) c₁ (by rw [h2, h1]; module)
      exact hc₁ this.2
    · refine orthSq_exists_pivot_of_triple hK hEΩ hp hL hN hLN hPN h3N hgH hgO (σ := σ)
        (w := c₁⁻¹ • (σ - c₂ • w)) hσU hŝU hQσ hQŝ hσŝ (hιAL _) (hιAL _) hp₁P hsP hgσ hgŝ hâ0
        hsP hs0 hsQ hs1 hss ?_
      intro d₁ d₂ hd
      have hcp : c₂ • p₂ = (d₁ + d₂ - c₁) • s := by
        have : p₁ = (d₁ + d₂) • s := by rw [hd]; module
        rw [this] at hc
        rw [sub_smul, hc]
        module
      have := hli (d₁ + d₂ - c₁) (-((d₁ + d₂) * c₂)) (by
        have hd' : p₁ = (d₁ + d₂) • s := by rw [hd]; module
        rw [hd']
        have : ((d₁ + d₂) * c₂) • p₂ = (d₁ + d₂) • (c₂ • p₂) := by rw [mul_smul]
        rw [neg_smul, this, hcp]
        module)
      obtain ⟨h5, h6⟩ := this
      have h7 : d₁ + d₂ = 0 := (mul_eq_zero.mp (neg_eq_zero.mp h6)).resolve_right hc₂
      exact hc₁ (by linear_combination h7 - h5)
  · push Not at hcase
    exact orthSq_exists_pivot_of_triple hK hEΩ hp hL hN hLN hPN h3N hgH hgO hσU hwU hQσ hQw h12
      (hιAL _) (hιAL _) hp₁P hp₂P hgσ hgw ha₂0 hsP hs0 hsQ hs1 hs2 hcase


theorem orthSq_exists_d4_pivot (hK : KernelLineData Q p E) (hp : p.Prime)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) {L N : Subgroup E} (hL : Nat.card L = p)
    (hN : Nat.card N = p) (hLN : L ≠ N)
    {W : Type} [AddCommGroup W] [Module K W] (ιA ιB : W →ₗ[K] V) (α β : W →ₗ[K] W)
    (hιB : Function.Injective ιB) (hα : Function.Injective α) (hιA : Function.Injective ιA)
    (hβ : Function.Injective β) (hLA : lineSpace L = LinearMap.range ιA)
    (hW4 : 4 ≤ finrank K W) (hsurj : ∀ s ∈ lineSpace N, ∃ z, ιB (β z) = s)
    (g : V ≃ₗ[K] V) (hgH : g ∈ orthSqSpan Q E)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgact : ∀ z, g (ιA z) = ιA (α z) + ιB (β z)) (hιBN : ∀ z, ιB z ∈ lineSpace N)
    (hstar : ∀ z : W, z ≠ 0 → ∀ c : K, ∃ z' : W,
      polar Q (ιA z') (ιA z) ≠ c * polar Q (ιB (β z')) (ιB (β z)))
    {s : V} (hsN : s ∈ lineSpace N) (hs0 : s ≠ 0) (hsQ : Q s = 0) :
    ∃ y ∈ lineSpace L, y ≠ 0 ∧ y ∈ rootSet Q (orthSqSpan Q E) s := by
  classical
  have : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
  have hN0 : N ≠ ⊥ := ne_bot_of_card_prime hp hN
  have hL0 : L ≠ ⊥ := ne_bot_of_card_prime hp hL
  have hAN : ∀ v ∈ lineSpace L, ∀ w ∈ lineSpace N, polar Q v w = 0 :=
    orthSep_lineSpace hK hL hN hLN
  have hNreg : PolarNondegOn Q (lineSpace N) :=
    OrthBlk.polarNondegOn_of_nondegenerate (hK.regular (some ⟨N, hN⟩))
  have hιAL : ∀ z, ιA z ∈ lineSpace L := fun z => hLA ▸ ⟨z, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : W →ₗ[K] V, b = ιB ∘ₗ β := ⟨_, rfl⟩
  have hbapp : ∀ z, b z = ιB (β z) := fun z => by rw [hb]; rfl
  have hbinj : Function.Injective b := fun z z' h =>
    hβ (hιB (by rw [← hbapp, ← hbapp]; exact h))
  have hbN : ∀ z, b z ∈ lineSpace N := fun z => by rw [hbapp]; exact hιBN _
  have hQg := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO
  have hOg := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO
  let QW : QuadraticForm K W := Q.comp ιA
  have hQW : ∀ z, QW z = Q (ιA z) := fun z => rfl
  have hpolW : ∀ z z', polar QW z z' = polar Q (ιA z) (ιA z') := fun z z' => by
    simp only [QuadraticMap.polar, QW, QuadraticMap.comp_apply, map_add]
  let ℓ : W →ₗ[K] K := (polarBilin Q).flip s ∘ₗ b
  have hℓ : ∀ z, ℓ z = polar Q (b z) s := fun z => by simp [ℓ, polarBilin_apply_apply]
  obtain ⟨ŝ, hŝ⟩ := hsurj s hsN
  have hbŝ : b ŝ = s := by rw [hbapp, hŝ]
  have hŝ0 : ŝ ≠ 0 := by
    rintro rfl
    exact hs0 (by rw [← hbŝ, map_zero])
  have hℓŝ : ℓ ŝ = 0 := by rw [hℓ, hbŝ]; exact polar_self_eq_zero hsQ
  have h3 : 3 ≤ finrank K ↥(LinearMap.ker ℓ) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker ℓ
    have h2 : finrank K (LinearMap.range ℓ) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range ℓ)
      simpa using this
    omega
  have hstar' : ∀ c : K, ∃ z, polar QW z ŝ ≠ c * ℓ z := by
    intro c
    obtain ⟨z', hz'⟩ := hstar ŝ hŝ0 c
    refine ⟨z', ?_⟩
    have : polar Q (b z') s = polar Q (ιB (β z')) (ιB (β ŝ)) := by rw [hbapp, hŝ]
    rw [hpolW, hℓ, this]
    exact hz'
  obtain ⟨z₁, z₂, hz₁ℓ, hz₂ℓ, hz₁Q, hz₁0, hz₁z₂, hind, hspan⟩ :=
    exists_d4_choice QW ℓ ŝ h3 hℓŝ hŝ0 hstar'
  have hz₁s : polar Q (b z₁) s = 0 := by rw [← hℓ]; exact hz₁ℓ
  have hz₂s : polar Q (b z₂) s = 0 := by rw [← hℓ]; exact hz₂ℓ
  have hind' : ∀ c₁ c₂ : K, b z₁ ≠ c₁ • s + c₂ • b z₂ := by
    intro c₁ c₂ h
    apply hind c₁ c₂
    apply hbinj
    rw [map_add, map_smul, map_smul, hbŝ]
    exact h
  obtain ⟨t, htN, hts, htb₂, htb₁⟩ := exists_perp_not_perp_two hNreg (hbN z₁) hsN (hbN z₂) hind'
  obtain ⟨u, hu⟩ : ∃ u, u = g (ιA z₁) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = g (ιA z₂) := ⟨_, rfl⟩
  have hu' : u = ιA (α z₁) + b z₁ := by rw [hu, hgact, hbapp]
  have hy' : y = ιA (α z₂) + b z₂ := by rw [hy, hgact, hbapp]
  have huQ : Q u = 0 := by rw [hu, hQg, ← hQW, hz₁Q]
  have huy : polar Q u y = 0 := by rw [hu, hy, hOg, ← hpolW, hz₁z₂]
  have hus : polar Q u s = 0 := by
    rw [hu', polar_add_left, hAN _ (hιAL _) s hsN, zero_add, hz₁s]
  have hsy : polar Q s y = 0 := by
    rw [hy', polar_add_right, polar_comm Q s (ιA (α z₂)), hAN _ (hιAL _) s hsN, zero_add,
      polar_comm, hz₂s]
  have hst : polar Q s t = 0 := by rw [polar_comm]; exact hts
  have hyt : polar Q y t = 0 := by
    rw [hy', polar_add_left, hAN _ (hιAL _) t htN, zero_add, polar_comm, htb₂]
  have hθ : polar Q u t ≠ 0 := by
    rw [hu', polar_add_left, hAN _ (hιAL _) t htN, zero_add, polar_comm]
    exact htb₁
  have hC : eichler Q s t ∈ orthSqSpan Q E :=
    orthSq_eichler_mem_of_mem_sup hEΩ hN0 (Submodule.mem_sup_right hsN) (Submodule.mem_sup_right htN)
  have hE : eichler Q u y ∈ orthSqSpan Q E := by
    rw [hu, hy, ← eichler_conj hgO]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgH (orthSq_eichler_mem_of_mem_sup hEΩ hL0
      (Submodule.mem_sup_right (hιAL z₁)) (Submodule.mem_sup_right (hιAL z₂))))
      (Subgroup.inv_mem _ hgH)
  have hmem := eichler_pivot_mem huQ hsQ hus huy hsy hst hyt hC hE
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = polar Q u t := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = Q y := ⟨_, rfl⟩
  rw [← hθdef, ← hcdef] at hmem
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, y₀ = -(θ • ιA (α (z₂ + c • z₁))) := ⟨_, rfl⟩
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = -(θ • (b z₂ + c • b z₁)) := ⟨_, rfl⟩
  have hsplit : -(θ • (y + c • u)) = y₀ + n₀ := by
    rw [hy', hu', hy₀, hn₀]
    simp only [map_add, map_smul]
    module
  have hy₀L : y₀ ∈ lineSpace L := by
    rw [hy₀]
    exact (lineSpace L).neg_mem ((lineSpace L).smul_mem _ (hιAL _))
  have hn₀N : n₀ ∈ lineSpace N := by
    rw [hn₀]
    exact (lineSpace N).neg_mem ((lineSpace N).smul_mem _ ((lineSpace N).add_mem (hbN _)
      ((lineSpace N).smul_mem _ (hbN _))))
  have hsy₀ : polar Q s y₀ = 0 := by
    rw [polar_comm]
    exact hAN _ hy₀L s hsN
  have hsn₀ : polar Q s n₀ = 0 := by
    rw [hn₀, polar_neg_right, polar_smul_right_eq, polar_add_right, polar_smul_right_eq,
      polar_comm Q s (b z₂), polar_comm Q s (b z₁), hz₂s, hz₁s]
    ring
  have hn₀H : eichler Q s n₀ ∈ orthSqSpan Q E :=
    orthSq_eichler_mem_of_mem_sup hEΩ hN0 (Submodule.mem_sup_right hsN)
      (Submodule.mem_sup_right hn₀N)
  have hy₀H : eichler Q s y₀ ∈ orthSqSpan Q E := by
    have h1 : eichler Q s y₀ * eichler Q s n₀ = eichler Q s (y₀ + n₀) := eichler_mul hsy₀ hsn₀
    have h2 : eichler Q s y₀ = eichler Q s (y₀ + n₀) * (eichler Q s n₀)⁻¹ := by
      rw [← h1]
      group
    rw [h2, ← hsplit]
    exact Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hn₀H)
  refine ⟨y₀, hy₀L, ?_, hsy₀, hy₀H⟩
  rw [hy₀]
  refine neg_ne_zero.mpr (smul_ne_zero (hθdef ▸ hθ) ((map_ne_zero_iff ιA hιA).mpr
    ((map_ne_zero_iff α hα).mpr fun h0 => hspan (-c) ?_)))
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left h0


end PivotsMix

section SelfDual

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.ComponentInitial

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

theorem orthSq_closure_eq_top_of_selfdual_or_D4 (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K)
    (hrank : RankLE2 p (orthDerived Q))
    (E : Subgroup (orthDerived Q)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2)
    (haniso : ∀ e ∈ planeFixSpace E, Q e = 0 → e = 0) (hsd : HasSelfDualFactor Q E) :
    Subgroup.closure {h : orthDerived Q |
      ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ (ringChar K ^ 2) = 1} = ⊤ ∨
      (finrank K ↥(planeFixSpace E) = 0 ∧ finrank K V = 8) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have : Nontrivial V := nontrivial_of_three_singular hT
  obtain ⟨hK, -⟩ := exists_kernelLineData_of_le hQ hp hp2 hpl E hcomm hexp hcard
  have hEΩ : elementaryGroup Q ≤ orthDerived Q := (orthDerived_eq_and_le_closure hQ hT).1.ge
  obtain ⟨L, N, hL, hN, hLN, hVL, hVN⟩ := hK.two_active
  obtain ⟨a, ha, h, hh, hne1, hm2, ⟨v, hvL, hvh, hv0⟩, ⟨w, hwN, hwh, hw0⟩⟩ :=
    exists_mixing_factor_orth hQ hp hpl hK hL hN hLN hVL hVN
  have hx0 := oddOrderIsometry_of_mem hQ hp hpl hK ha
  have haL : a ∉ L := not_mem_line_of_primary hx0 hh hne1 hvL hvh hv0
  have haN : a ∉ N := not_mem_line_of_primary hx0 hh hne1 hwN hwh hw0
  obtain ⟨x, hxa⟩ : ∃ x : V ≃ₗ[K] V, x = (((a : E) : orthDerived Q) : V ≃ₗ[K] V) := ⟨_, rfl⟩
  rw [← hxa] at hh hvh hwh hm2 hx0
  have hx : OddOrderIsometry Q p x := hx0
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hself : h = reciprocalPolynomial h := by
    obtain ⟨a₁, ha₁, ha₁1, h₁, hh₁, hne₁, hself₁⟩ := hsd
    have : Fact (Irreducible h₁) := ⟨irreducible_of_mem_primaryFactors hh₁⟩
    have hx₁ := oddOrderIsometry_of_mem hQ hp hpl hK (x := (⟨a₁, ha₁⟩ : E))
      (fun e => ha₁1 (congrArg Subtype.val e))
    obtain ⟨d, -, -, -, -, -, hroot, -⟩ := hx₁.selfDualModel hodd hh₁ hne₁ hself₁
    exact selfDual_of_dvd hx hh (hx₁.dvd_card_pow_add_one hp hh₁ hne₁ hroot)
  have hStL : ∀ s ∈ lineSpace L, x s ∈ lineSpace L := fun s hs => by
    rw [hxa]; exact lineSpace_stable hK.comm L a hs
  have hStN : ∀ s ∈ lineSpace N, x s ∈ lineSpace N := fun s hs => by
    rw [hxa]; exact lineSpace_stable hK.comm N a hs
  have hneL : lineSpace L ⊓ primaryComponent x.toLinearMap h ≠ ⊥ := fun h0 => hv0 (by
    have : v ∈ (⊥ : Submodule K V) := h0 ▸ ⟨hvL, hvh⟩
    simpa using this)
  have hneN : lineSpace N ⊓ primaryComponent x.toLinearMap h ≠ ⊥ := fun h0 => hw0 (by
    have : w ∈ (⊥ : Submodule K V) := h0 ▸ ⟨hwN, hwh⟩
    simpa using this)
  have hAN : ∀ s ∈ lineSpace L, ∀ t ∈ lineSpace N, polar Q s t = 0 :=
    orthSep_lineSpace hK hL hN hLN
  obtain ⟨u, w', hu, hw', hu0, hw0', hureg, hwreg⟩ : ∃ u w' : primaryComponent x.toLinearMap h,
      (u : V) ∈ lineSpace L ∧ (w' : V) ∈ lineSpace N ∧ u ≠ 0 ∧ w' ≠ 0 ∧
      PolarNondegOn Q (LinearMap.range (eline x h u)) ∧
      PolarNondegOn Q (LinearMap.range (eline x h w')) := by
    by_cases h2 : (2 : K) = 0
    · obtain ⟨-, -, u, w', hu, hw', hu0, hw0', hureg, hwreg, -⟩ :=
        exists_selfdual_mixing_action_even hx hp hp5 hh hne1 hself h2 hStL hStN
          (hK.regular (some ⟨L, hL⟩)) (hK.regular (some ⟨N, hN⟩)) hAN hneL hneN
      exact ⟨u, w', hu, hw', hu0, hw0', hureg, hwreg⟩
    · obtain ⟨u₀, hu₀, hQu₀⟩ := exists_map_ne_zero_of_selfdual hx hh hself hStL
        (hK.regular (some ⟨L, hL⟩)) hneL
      obtain ⟨w₀, hw₀, hQw₀⟩ := exists_map_ne_zero_of_selfdual hx hh hself hStN
        (hK.regular (some ⟨N, hN⟩)) hneN
      obtain ⟨-, -, u, w', hu, hw', hQu, hQw', hureg, hwreg, -⟩ :=
        exists_selfdual_mixing_action hx hodd hh hne1 hself h2 hStN hAN ⟨u₀, hu₀, hQu₀⟩
          ⟨w₀, hw₀, hQw₀⟩
      exact ⟨u, w', hu, hw', fun h0 => hQu (by rw [h0]; simp),
        fun h0 => hQw' (by rw [h0]; simp), hureg, hwreg⟩
  have hfin : finrank K (AdjoinRoot h) = h.natDegree := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
  obtain ⟨d', hdeg', c, hc0, hfam⟩ :=
    orthSq_exists_selfdual_mixing_family hx hodd hh hne1 hself hStN hAN u w' hu hw' hu0 hw0' hureg
      hwreg
  obtain ⟨θ, hθ, hθ0, hlam⟩ := orthSq_exists_trace_zero (r := h) (d := d') (by rw [hfin, hdeg'])
    (by have := hx.p_lt_card_adjoinRoot hp hh hne1; omega)
  obtain ⟨g, hgS, hgr, hact, -⟩ := hfam θ hθ
  have hmu : θ * c ≠ 0 := mul_ne_zero hθ0 hc0
  obtain ⟨d, hdeg, -⟩ := hx.selfDualModel hodd hh hne1 hself
  have hLr : lineSpace L = LinearMap.range (eline x h u) :=
    lineSpace_eq_range_eline hQ hT hp hp2 hrank hK hL hN hLN hVN haL hxa u hu hu0 hureg
  have hNr : lineSpace N = LinearMap.range (eline x h w') :=
    lineSpace_eq_range_eline hQ hT hp hp2 hrank hK hN hL hLN.symm hVL haN hxa w' hw' hw0' hwreg
  have hdimL : finrank K ↥(lineSpace L) = h.natDegree := by
    rw [hLr, LinearMap.finrank_range_of_inj (eline_injective h hu0), hfin]
  have hdimN : finrank K ↥(lineSpace N) = h.natDegree := by
    rw [hNr, LinearMap.finrank_range_of_inj (eline_injective h hw0'), hfin]
  have hother : ∀ M : Subgroup E, Nat.card M = p → M ≠ L → M ≠ N → lineSpace M = ⊥ := by
    intro M hM hML hMN
    by_contra hne
    rcases eq_or_eq_of_active hQ hT hp hp2 hrank hK hL hN hLN hVL hVN hM hne with h' | h'
    · exact hML h'
    · exact hMN h'
  have hn := finrank_eq_of_two_active hK hL hN hLN hother
  have hV₀ : finrank K ↥(planeFixSpace E) ≤ 2 := by
    by_contra hcon
    obtain ⟨e, he, he0, heQ⟩ := exists_singular_of_three_le_any (Q := Q)
      (S := planeFixSpace E) (by omega)
    exact he0 (haniso e he heQ)
  by_cases hD : 0 < finrank K ↥(planeFixSpace E) ∨ 8 < finrank K V
  swap
  · right
    push Not at hD
    omega
  left
  have h3N : 3 ≤ finrank K ↥(lineSpace N) := by omega
  have hdimUL : finrank K ↥(planeFixSpace E ⊔ lineSpace L) =
      finrank K ↥(planeFixSpace E) + h.natDegree := by
    rw [finrank_sup_of_disjoint (disjoint_planeFixSpace_lineSpace hK hL), hdimL]
  have hdimUN : finrank K ↥(planeFixSpace E ⊔ lineSpace N) =
      finrank K ↥(planeFixSpace E) + h.natDegree := by
    rw [finrank_sup_of_disjoint (disjoint_planeFixSpace_lineSpace hK hN), hdimN]
  have h5 : 5 ≤ finrank K ↥(planeFixSpace E) + h.natDegree := by omega
  have hgΩ : g ∈ orthDerived Q := hx.specialBlock_le_orthDerived hp (by omega) hh hne1 hm2 hgS
  obtain ⟨hgQ, hgx⟩ := mem_isometryCentralizer.mp (specialBlock_le_isometryCentralizer h hgS)
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hgQ
  have hgH : g ∈ orthSqSpan Q E := by
    refine orthSq_mem_of_commute (a := (a : orthDerived Q)) hgΩ a.2
      (fun e => ha (Subtype.ext e)) ?_ hgr
    rw [← hxa]
    exact LinearEquiv.ext fun v => hgx v
  have hg0 : ∀ v ∈ planeFixSpace E, g v = v := fun v hv =>
    (mem_supportedBlock.mp (specialBlock_le_supportedBlock h hgS)).2 v
      (fixedSpace_le_othersSpace hne1 hself (mem_fixedSpace.mpr (by
        rw [hxa]; exact apply_eq_of_mem_planeFixSpace a hv)))
  have hpiv := orthSq_exists_pivot_of_mixing_gen hK hp hEΩ hL hN hLN haniso (eline x h u)
    (eline x h w') (LinearMap.mulLeft K (1 + θ)) (LinearMap.mulLeft K (θ * c)) (eline_injective h hu0)
    (eline_injective h hw0') (mul_right_injective₀ hlam) (mul_right_injective₀ hmu) hLr g hgH hgO
    hg0 hact (fun z => smul_mem_of_stable hStN z w' hw') (by omega) (by omega) h3N
  have hPN : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace N) :=
    hasOrthPairs_of_dim (OrthBlk.polarNondegOn_of_nondegenerate (regular_sup hK hN)) (by omega)
  have hPL : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace L) :=
    hasOrthPairs_of_dim (OrthBlk.polarNondegOn_of_nondegenerate (regular_sup hK hL)) (by omega)
  have hle : elementaryGroup Q ≤ orthSqSpan Q E := by
    refine orthSq_elementaryGroup_le_of_pivots hK hEΩ hp hQ hN hPN fun M hM hMN hVM => ?_
    rcases eq_or_eq_of_active hQ hT hp hp2 hrank hK hL hN hLN hVL hVN hM hVM with h' | h'
    · subst h'
      exact ⟨hPL, hpiv⟩
    · exact absurd h' hMN
  exact orthSq_closure_eq_top_of_le E ((orthDerived_eq_and_le_closure hQ hT).1 ▸ hle)

theorem orthSq_closure_eq_top_of_selfdual_D4 (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K) (hrank : RankLE2 p (orthDerived Q))
    (E : Subgroup (orthDerived Q)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2)
    (hsd : HasSelfDualFactor Q E) (hV0 : finrank K ↥(planeFixSpace E) = 0)
    (hV8 : finrank K V = 8) :
    Subgroup.closure {h : orthDerived Q |
      ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ (ringChar K ^ 2) = 1} = ⊤ := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have : Nontrivial V := nontrivial_of_three_singular hT
  obtain ⟨hK, -⟩ := exists_kernelLineData_of_le hQ hp hp2 hpl E hcomm hexp hcard
  have hEΩ : elementaryGroup Q ≤ orthDerived Q := (orthDerived_eq_and_le_closure hQ hT).1.ge
  obtain ⟨L, N, hL, hN, hLN, hVL, hVN⟩ := hK.two_active
  have hN0 : N ≠ ⊥ := ne_bot_of_card_prime hp hN
  have hL0 : L ≠ ⊥ := ne_bot_of_card_prime hp hL
  obtain ⟨a, ha, h, hh, hne1, hm2, ⟨v, hvL, hvh, hv0⟩, ⟨w, hwN, hwh, hw0⟩⟩ :=
    exists_mixing_factor_orth hQ hp hpl hK hL hN hLN hVL hVN
  have hx0 := oddOrderIsometry_of_mem hQ hp hpl hK ha
  have haL : a ∉ L := not_mem_line_of_primary hx0 hh hne1 hvL hvh hv0
  have haN : a ∉ N := not_mem_line_of_primary hx0 hh hne1 hwN hwh hw0
  obtain ⟨x, hxa⟩ : ∃ x : V ≃ₗ[K] V, x = (((a : E) : orthDerived Q) : V ≃ₗ[K] V) := ⟨_, rfl⟩
  rw [← hxa] at hh hvh hwh hm2 hx0
  have hx : OddOrderIsometry Q p x := hx0
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hself : h = reciprocalPolynomial h := by
    obtain ⟨a₁, ha₁, ha₁1, h₁, hh₁, hne₁, hself₁⟩ := hsd
    have : Fact (Irreducible h₁) := ⟨irreducible_of_mem_primaryFactors hh₁⟩
    have hx₁ := oddOrderIsometry_of_mem hQ hp hpl hK (x := (⟨a₁, ha₁⟩ : E))
      (fun e => ha₁1 (congrArg Subtype.val e))
    obtain ⟨d, -, -, -, -, -, hroot, -⟩ := hx₁.selfDualModel hodd hh₁ hne₁ hself₁
    exact selfDual_of_dvd hx hh (hx₁.dvd_card_pow_add_one hp hh₁ hne₁ hroot)
  have hStL : ∀ s ∈ lineSpace L, x s ∈ lineSpace L := fun s hs => by
    rw [hxa]; exact lineSpace_stable hK.comm L a hs
  have hStN : ∀ s ∈ lineSpace N, x s ∈ lineSpace N := fun s hs => by
    rw [hxa]; exact lineSpace_stable hK.comm N a hs
  have hneL : lineSpace L ⊓ primaryComponent x.toLinearMap h ≠ ⊥ := fun h0 => hv0 (by
    have : v ∈ (⊥ : Submodule K V) := h0 ▸ ⟨hvL, hvh⟩
    simpa using this)
  have hneN : lineSpace N ⊓ primaryComponent x.toLinearMap h ≠ ⊥ := fun h0 => hw0 (by
    have : w ∈ (⊥ : Submodule K V) := h0 ▸ ⟨hwN, hwh⟩
    simpa using this)
  have hAN : ∀ s ∈ lineSpace L, ∀ t ∈ lineSpace N, polar Q s t = 0 :=
    orthSep_lineSpace hK hL hN hLN
  obtain ⟨u, w', hu, hw', hu0, hw0', hureg, hwreg⟩ : ∃ u w' : primaryComponent x.toLinearMap h,
      (u : V) ∈ lineSpace L ∧ (w' : V) ∈ lineSpace N ∧ u ≠ 0 ∧ w' ≠ 0 ∧
      PolarNondegOn Q (LinearMap.range (eline x h u)) ∧
      PolarNondegOn Q (LinearMap.range (eline x h w')) := by
    by_cases h2 : (2 : K) = 0
    · obtain ⟨-, -, u, w', hu, hw', hu0, hw0', hureg, hwreg, -⟩ :=
        exists_selfdual_mixing_action_even hx hp hp5 hh hne1 hself h2 hStL hStN
          (hK.regular (some ⟨L, hL⟩)) (hK.regular (some ⟨N, hN⟩)) hAN hneL hneN
      exact ⟨u, w', hu, hw', hu0, hw0', hureg, hwreg⟩
    · obtain ⟨u₀, hu₀, hQu₀⟩ := exists_map_ne_zero_of_selfdual hx hh hself hStL
        (hK.regular (some ⟨L, hL⟩)) hneL
      obtain ⟨w₀, hw₀, hQw₀⟩ := exists_map_ne_zero_of_selfdual hx hh hself hStN
        (hK.regular (some ⟨N, hN⟩)) hneN
      obtain ⟨-, -, u, w', hu, hw', hQu, hQw', hureg, hwreg, -⟩ :=
        exists_selfdual_mixing_action hx hodd hh hne1 hself h2 hStN hAN ⟨u₀, hu₀, hQu₀⟩
          ⟨w₀, hw₀, hQw₀⟩
      exact ⟨u, w', hu, hw', fun h0 => hQu (by rw [h0]; simp),
        fun h0 => hQw' (by rw [h0]; simp), hureg, hwreg⟩
  have hLr : lineSpace L = LinearMap.range (eline x h u) :=
    lineSpace_eq_range_eline hQ hT hp hp2 hrank hK hL hN hLN hVN haL hxa u hu hu0 hureg
  have hNr : lineSpace N = LinearMap.range (eline x h w') :=
    lineSpace_eq_range_eline hQ hT hp hp2 hrank hK hN hL hLN.symm hVL haN hxa w' hw' hw0' hwreg
  have hfin : finrank K (AdjoinRoot h) = h.natDegree := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
  have hdimL : finrank K ↥(lineSpace L) = h.natDegree := by
    rw [hLr, LinearMap.finrank_range_of_inj (eline_injective h hu0), hfin]
  have hdimN : finrank K ↥(lineSpace N) = h.natDegree := by
    rw [hNr, LinearMap.finrank_range_of_inj (eline_injective h hw0'), hfin]
  have hother : ∀ M : Subgroup E, Nat.card M = p → M ≠ L → M ≠ N → lineSpace M = ⊥ := by
    intro M hM hML hMN
    by_contra hne
    rcases eq_or_eq_of_active hQ hT hp hp2 hrank hK hL hN hLN hVL hVN hM hne with h' | h'
    · exact hML h'
    · exact hMN h'
  have hn := finrank_eq_of_two_active hK hL hN hLN hother
  obtain ⟨d, hdeg, -⟩ := hx.selfDualModel hodd hh hne1 hself
  have hn4 : h.natDegree = 4 := by omega
  have hd2 : 2 ≤ d := by omega
  have hV0' : planeFixSpace E = ⊥ := Submodule.finrank_eq_zero.mp hV0
  have htop : lineSpace L ⊔ lineSpace N = ⊤ := by
    have := sup_eq_top_of_two_active hK hL hN hother
    rwa [hV0', bot_sup_eq] at this
  obtain ⟨d', hdeg', c, hc0, hfam⟩ :=
    orthSq_exists_selfdual_mixing_family hx hodd hh hne1 hself hStN hAN
    u w' hu hw' hu0 hw0' hureg hwreg
  have hdd : d' = d := by omega
  subst hdd
  obtain ⟨θ, hθ, hθK⟩ := exists_trace_zero_sq_not_mem hd2 (by rw [hfin, hdeg'])
  obtain ⟨g, hgS, hgr, hact, hbal⟩ := hfam θ hθ
  have hθ0 : θ ≠ 0 := fun h0 => hθK 0 (by rw [h0]; simp)
  have hlam : 1 + θ ≠ 0 := fun h0 => hθK 1 (by
    have : θ = -1 := eq_neg_of_add_eq_zero_right h0
    rw [this]
    simp)
  have hmu : θ * c ≠ 0 := mul_ne_zero hθ0 hc0
  have hgΩ : g ∈ orthDerived Q := hx.specialBlock_le_orthDerived hp (by omega) hh hne1 hm2 hgS
  obtain ⟨hgQ, hgx⟩ := mem_isometryCentralizer.mp (specialBlock_le_isometryCentralizer h hgS)
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hgQ
  have hgH : g ∈ orthSqSpan Q E := by
    refine orthSq_mem_of_commute (a := (a : orthDerived Q)) hgΩ a.2
      (fun e => ha (Subtype.ext e)) ?_ hgr
    rw [← hxa]
    exact LinearEquiv.ext fun v => hgx v
  have hιAL : ∀ z, eline x h u z ∈ lineSpace L := fun z => hLr ▸ ⟨z, rfl⟩
  have hιBN : ∀ z, eline x h w' z ∈ lineSpace N := fun z => smul_mem_of_stable hStN z w' hw'
  have hpivot : ∀ s ∈ lineSpace N, s ≠ 0 → Q s = 0 →
      ∃ y ∈ lineSpace L, y ≠ 0 ∧ y ∈ rootSet Q (orthSqSpan Q E) s := by
    intro s hsN hs0 hsQ
    refine orthSq_exists_d4_pivot hK hp hEΩ hL hN hLN (eline x h u) (eline x h w')
      (LinearMap.mulLeft K (1 + θ)) (LinearMap.mulLeft K (θ * c)) (eline_injective h hw0')
      (mul_right_injective₀ hlam) (eline_injective h hu0) (mul_right_injective₀ hmu) hLr
      (by omega) ?_ g hgH hgO hact hιBN ?_ hsN hs0 hsQ
    · intro s' hs'
      rw [hNr] at hs'
      obtain ⟨z₀, rfl⟩ := hs'
      exact ⟨(θ * c)⁻¹ * z₀, by rw [LinearMap.mulLeft_apply, mul_inv_cancel_left₀ hmu]⟩
    · exact not_proportional_of_mixing (eline x h u) (eline x h w') g hgO (1 + θ) (θ * c)
        (1 - θ ^ 2) hact (fun z z' => hAN _ (hιAL z) _ (hιBN z')) hbal hureg
        (eline_injective h hu0) (fun c' h0 => hθK c' (by rw [← h0]; ring))
  have hAreg : PolarNondegOn Q (lineSpace L) :=
    OrthBlk.polarNondegOn_of_nondegenerate (hK.regular (some ⟨L, hL⟩))
  have hNreg : PolarNondegOn Q (lineSpace N) :=
    OrthBlk.polarNondegOn_of_nondegenerate (hK.regular (some ⟨N, hN⟩))
  have hcenter : ∀ s ∈ lineSpace N, s ≠ 0 → Q s = 0 →
      IsRootCenter Q (orthSqSpan Q E) s := by
    intro s hsN hs0 hsQ
    obtain ⟨y₀, hy₀L, hy₀0, hy₀R⟩ := hpivot s hsN hs0 hsQ
    have hLR : ∀ a' ∈ lineSpace L, a' ∈ rootSet Q (orthSqSpan Q E) s := by
      refine mem_of_invariant_of_ne_zero hAreg (by omega)
        (rootSet Q (orthSqSpan Q E) s) ?_ hy₀R hy₀L hy₀0
      intro x₁ hx₁ z₁ hz₁ _ _ m hm _
      have hH : eichler Q x₁ z₁ ∈ orthSqSpan Q E :=
        orthSq_eichler_mem_of_mem_sup hEΩ hL0 (Submodule.mem_sup_right hx₁)
          (Submodule.mem_sup_right hz₁)
      have hfix : eichler Q x₁ z₁ s = s :=
        eichler_apply_of_polar_eq_zero (by rw [polar_comm]; exact hAN x₁ hx₁ s hsN)
          (by rw [polar_comm]; exact hAN z₁ hz₁ s hsN)
      have := rootSet_map (orthSqSpan_le_orthogonalGroup E) hH hm
      rwa [hfix] at this
    refine ⟨hs0, hsQ, fun w₁ hw₁ => ?_⟩
    obtain ⟨a', ha', b, hb, rfl⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top (x := w₁))
    have hsa : polar Q s a' = 0 := by rw [polar_comm]; exact hAN a' ha' s hsN
    have hsb : polar Q s b = 0 := by
      rw [polar_add_right, hsa, zero_add] at hw₁
      exact hw₁
    have hbR : b ∈ rootSet Q (orthSqSpan Q E) s :=
      ⟨hsb, orthSq_eichler_mem_of_mem_sup hEΩ hN0 (Submodule.mem_sup_right hsN)
        (Submodule.mem_sup_right hb)⟩
    exact ((rootSet Q (orthSqSpan Q E) s).add_mem (hLR a' ha') hbR).2
  obtain ⟨a₁, ha₁N, ha₁0, hQa₁⟩ :=
    exists_singular_of_three_le_any (Q := Q) (S := lineSpace N) (by omega)
  obtain ⟨f₁, hf₁N, hQf₁, h11⟩ := exists_partner_of_polarNondegOn hNreg ha₁N hQa₁ ha₁0
  have hf₁0 : f₁ ≠ 0 := fun h0 => by
    rw [h0, polar_zero_right] at h11
    exact zero_ne_one h11
  have hle : elementaryGroup Q ≤ orthSqSpan Q E :=
    elementaryGroup_le_of_hypPair hQ (orthSqSpan_le_orthogonalGroup E)
      ⟨a₁, f₁, hQa₁, hQf₁, h11⟩ (hcenter a₁ ha₁N ha₁0 hQa₁) (hcenter f₁ hf₁N hf₁0 hQf₁)
  exact orthSq_closure_eq_top_of_le E ((orthDerived_eq_and_le_closure hQ hT).1 ▸ hle)

theorem orthSq_selfDualTwoBlocks (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K)
    (hrank : RankLE2 p (orthDerived Q))
    (E : Subgroup (orthDerived Q)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2)
    (haniso : ∀ e ∈ planeFixSpace E, Q e = 0 → e = 0) (hsd : HasSelfDualFactor Q E) :
    Subgroup.closure {h : orthDerived Q |
      ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ (ringChar K ^ 2) = 1} = ⊤ := by
  rcases orthSq_closure_eq_top_of_selfdual_or_D4 hQ hT hdim hp hp5 hpl hrank E hcomm hexp hcard
    haniso hsd with h | ⟨h0, h8⟩
  · exact h
  · exact orthSq_closure_eq_top_of_selfdual_D4 hQ hT hp hp5 hpl hrank E hcomm hexp hcard hsd h0 h8

end SelfDual

section ManyBig

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)}

theorem orthSq_eichler_mem_of_restricted_plane {U : Submodule K V} (hU : PolarNondegOn Q U)
    (hEU : orthDerived (Q.comp U.subtype) = elementaryGroup (Q.comp U.subtype))
    (E : Subgroup (orthDerived Q))
    (hstab : ∀ x : E, ((x : orthDerived Q) : V ≃ₗ[K] V) ∈ stab U)
    (hΩ : elementaryGroup Q ≤ orthDerived Q)
    (ρ : E →* orthDerived (Q.comp U.subtype))
    (hρ : ∀ (x : E) (u : U), (((ρ x : orthDerived (Q.comp U.subtype)) : U ≃ₗ[K] U) u : V) =
      ((x : orthDerived Q) : V ≃ₗ[K] V) u)
    (hgen : Subgroup.closure {h : orthDerived (Q.comp U.subtype) |
      ∃ x : E, x ≠ 1 ∧ h * ρ x = ρ x * h ∧ h ^ (ringChar K ^ 2) = 1} = ⊤) :
    ∀ e ∈ U, ∀ w ∈ U, eichler Q e w ∈ orthSqSpan Q E := by
  classical
  let φ : orthDerived (Q.comp U.subtype) →* (V ≃ₗ[K] V) :=
    (extU hU).comp (orthDerived (Q.comp U.subtype)).subtype
  have hle : Subgroup.closure {h : orthDerived (Q.comp U.subtype) |
      ∃ x : E, x ≠ 1 ∧ h * ρ x = ρ x * h ∧ h ^ (ringChar K ^ 2) = 1} ≤ (orthSqSpan Q E).comap φ := by
    rw [Subgroup.closure_le]
    rintro h ⟨x, hx1, hhx, hhr⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    have hhE : extU hU (h : U ≃ₗ[K] U) ∈ eichlerGroupOn Q U :=
      extU_mem_eichlerGroupOn hU (hEU ▸ h.2)
    have hΩmem : extU hU (h : U ≃ₗ[K] U) ∈ orthDerived Q :=
      hΩ (eichlerGroupOn_le_elementaryGroup U hhE)
    have hpow : extU hU (h : U ≃ₗ[K] U) ^ (ringChar K ^ 2) = 1 := by
      rw [← map_pow]
      have : (h : U ≃ₗ[K] U) ^ (ringChar K ^ 2) = 1 := by
        have := congrArg Subtype.val hhr
        simpa using this
      rw [this, map_one]
    refine orthSq_mem_of_commute_sq (a := (x : orthDerived Q)) hΩmem x.2
      (fun h1 => hx1 (Subtype.ext h1)) ?_ hpow
    have hc : Commute (extU hU (h : U ≃ₗ[K] U)) ((x : orthDerived Q) : V ≃ₗ[K] V) := by
      refine commute_of_mem_eichlerGroupOn hU hhE (orthDerived_mem_orthogonalGroup) (hstab x) ?_
      intro u hu
      have hxu : ((x : orthDerived Q) : V ≃ₗ[K] V) u ∈ U := ((mem_stab.mp (hstab x)) u hu).1
      rw [extU_apply_mem hU _ hxu, extU_apply_mem hU _ hu]
      have e1 : (⟨((x : orthDerived Q) : V ≃ₗ[K] V) u, hxu⟩ : U) =
          ((ρ x : orthDerived (Q.comp U.subtype)) : U ≃ₗ[K] U) ⟨u, hu⟩ :=
        Subtype.ext (hρ x ⟨u, hu⟩).symm
      rw [e1]
      have e2 := hρ x ((h : U ≃ₗ[K] U) ⟨u, hu⟩)
      rw [← e2]
      exact congrArg (fun y : orthDerived (Q.comp U.subtype) =>
        (((y : U ≃ₗ[K] U) ⟨u, hu⟩ : U) : V)) hhx
    exact hc.eq
  intro e he w hw
  have hmem : eichler (Q.comp U.subtype) ⟨e, he⟩ ⟨w, hw⟩ ∈
      orthDerived (Q.comp U.subtype) := by
    rw [hEU]
    exact eichler_mem_elementaryGroup _ _ _
  have htop : (⟨eichler (Q.comp U.subtype) ⟨e, he⟩ ⟨w, hw⟩, hmem⟩ : orthDerived (Q.comp U.subtype))
      ∈ Subgroup.closure {h : orthDerived (Q.comp U.subtype) |
        ∃ x : E, x ≠ 1 ∧ h * ρ x = ρ x * h ∧ h ^ (ringChar K ^ 2) = 1} := by
    rw [hgen]
    exact Subgroup.mem_top _
  have := Subgroup.mem_comap.mp (hle htop)
  have e3 : φ ⟨eichler (Q.comp U.subtype) ⟨e, he⟩ ⟨w, hw⟩, hmem⟩ = eichler Q e w :=
    extU_eichler hU ⟨e, he⟩ ⟨w, hw⟩
  rwa [e3] at this

theorem orthSq_eichler_mem_of_two_pieces (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpl : p ≠ ringChar K) (hK : KernelLineData Q p E) (hNS : OrthNoInvariantSingular Q E)
    (h4 : 4 ≤ orderOf ((Nat.card K : ℕ) : ZMod p)) {P₁ P₂ : Submodule K V}
    (h₁ : IsPiece Q E P₁) (h₂ : IsPiece Q E P₂) (h12 : OrthSep Q P₁ P₂) {M₁ M₂ : Subgroup E}
    (hM₁ : Nat.card M₁ = p) (hM₂ : Nat.card M₂ = p) (hM12 : M₁ ≠ M₂)
    (hk₁ : ∀ x : E, (∀ u ∈ P₁, ((x : orthDerived Q) : V ≃ₗ[K] V) u = u) → x ∈ M₁)
    (hk₂ : ∀ x : E, (∀ u ∈ P₂, ((x : orthDerived Q) : V ≃ₗ[K] V) u = u) → x ∈ M₂)
    (hf₁ : finrank K P₁ = orderOf ((Nat.card K : ℕ) : ZMod p))
    (hf₂ : finrank K P₂ = orderOf ((Nat.card K : ℕ) : ZMod p)) :
    ∀ x ∈ planeFixSpace E ⊔ P₁ ⊔ P₂, ∀ y ∈ planeFixSpace E ⊔ P₁ ⊔ P₂,
      eichler Q x y ∈ orthSqSpan Q E := by
  classical
  have hp2 : p ≠ 2 := by omega
  set U : Submodule K V := planeFixSpace E ⊔ P₁ ⊔ P₂
  have hV0 : PolarNondegOn Q (planeFixSpace E) := polarNondegOn_planeFixSpace hK
  have hP₁U : P₁ ≤ U := le_sup_of_le_left le_sup_right
  have hP₂U : P₂ ≤ U := le_sup_right
  have hU : PolarNondegOn Q U := polarNondegOn_sup (polarNondegOn_sup hV0 h₁.regular
    h₁.orthSep.symm) h₂.regular (manyBig_orthSep_sup_left h₂.orthSep.symm h12)
  have hdisj : Disjoint P₁ P₂ := OrthSep.disjoint h₁.regular h12
  have hdim12 : finrank K ↥(P₁ ⊔ P₂) = finrank K P₁ + finrank K P₂ := by
    have := Submodule.finrank_sup_add_finrank_inf_eq P₁ P₂
    rwa [hdisj.eq_bot, finrank_bot, add_zero] at this
  have hU8 : 8 ≤ finrank K U := by
    have : finrank K ↥(P₁ ⊔ P₂) ≤ finrank K U :=
      Submodule.finrank_mono (sup_le hP₁U hP₂U)
    omega
  have hUle : finrank K U ≤ finrank K (planeFixSpace E) + finrank K P₁ + finrank K P₂ := by
    have h1 : finrank K U ≤ finrank K ↥(planeFixSpace E ⊔ P₁) + finrank K P₂ :=
      Submodule.finrank_add_le_finrank_add_finrank _ _
    have h2 := Submodule.finrank_add_le_finrank_add_finrank (planeFixSpace E) P₁
    omega
  have hV02 := finrank_planeFixSpace_le_two hNS
  have hlt : finrank K U < 3 * orderOf ((Nat.card K : ℕ) : ZMod p) := by omega
  have hV0st : EStable E (planeFixSpace E) :=
    EStable.of_fixed fun x hx u hu => hu _ ⟨x, hx, rfl⟩
  have hUst : EStable E U := manyBig_eStable_sup (manyBig_eStable_sup hV0st h₁.eStable) h₂.eStable
  have hQU := nondegenerate_comp_subtype hU
  have hTU := exists_ts_three_comp hU hU8
  obtain ⟨ρ, hρ⟩ := manyBig_exists_restrict_hom hK hp hp2 hU hTU hUst
  have hfinE : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hK.card]; exact pow_ne_zero 2 hp.ne_zero)
  have hfix : ∀ x : E, ρ x = 1 → ∀ P : Submodule K V, P ≤ U →
      ∀ u ∈ P, ((x : orthDerived Q) : V ≃ₗ[K] V) u = u := by
    intro x hx P hPU u hu
    have := hρ x ⟨u, hPU hu⟩
    rw [hx] at this
    exact this.symm
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : x ∈ M₁ ⊓ M₂ :=
      ⟨hk₁ x (hfix x hx P₁ hP₁U), hk₂ x (hfix x hx P₂ hP₂U)⟩
    rwa [inf_eq_bot_of_card_prime' hp hM₁ hM₂ hM12, Subgroup.mem_bot] at h1
  have hcomm' : ∀ x ∈ ρ.range, ∀ y ∈ ρ.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, hK.comm a b]
  have hexp' : ∀ x ∈ ρ.range, x ^ p = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, hK.exp a, map_one]
  have hcard' : Nat.card ρ.range = p ^ 2 :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hK.card
  have haniso : ∀ u ∈ planeFixSpace ρ.range, (Q.comp U.subtype) u = 0 → u = 0 := by
    intro u hu hQu
    have hu0 : (u : V) ∈ planeFixSpace E := by
      refine mem_fixSpace.mpr fun g hg => ?_
      obtain ⟨x, hx, rfl⟩ := hg
      have h1 := mem_fixSpace.mp hu ((ρ ⟨x, hx⟩ : orthDerived (Q.comp U.subtype)) : U ≃ₗ[K] U)
        ⟨ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
      have h2 := hρ ⟨x, hx⟩ u
      rw [h1] at h2
      exact h2.symm
    exact Subtype.ext (eq_zero_of_singular_planeFixSpace hNS hu0 hQu)
  have hclos := orthSq_selfDualTwoBlocks (Q := Q.comp U.subtype) hQU hTU (by omega) hp hp5 hpl
    (rankLE2_of_finrank_lt hQU hp hp2 hpl hlt) ρ.range hcomm' hexp' hcard' haniso
    (hasSelfDualFactor_restrict hK hp hpl hU ρ hρ h₁ hP₁U)
  have hgen : Subgroup.closure {h : orthDerived (Q.comp U.subtype) |
      ∃ x : E, x ≠ 1 ∧ h * ρ x = ρ x * h ∧ h ^ (ringChar K ^ 2) = 1} = ⊤ := by
    rw [eq_top_iff, ← hclos]
    refine Subgroup.closure_mono ?_
    rintro h ⟨_, ⟨x, rfl⟩, hx1, hh, hr⟩
    exact ⟨x, fun h1 => hx1 (by rw [h1, map_one]), hh, hr⟩
  have hΩ : elementaryGroup Q ≤ orthDerived Q := (orthDerived_eq_and_le_closure hQ hT).1.ge
  have hEU := (orthDerived_eq_and_le_closure hQU hTU).1
  exact orthSq_eichler_mem_of_restricted_plane hU hEU E (manyBig_mem_stab hK hp.pos hUst) hΩ ρ hρ
    hgen

end ManyBig

section ManyBigMain

theorem orthSq_closure_eq_top_of_noSingular_big {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K)
    (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) (hNS : OrthNoInvariantSingular Q E)
    (h4 : 4 ≤ orderOf ((Nat.card K : ℕ) : ZMod p)) :
    Subgroup.closure {h : orthDerived Q |
      ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ (ringChar K ^ 2) = 1} = ⊤ := by
  classical
  have hp2 : p ≠ 2 := by omega
  haveI : Nontrivial V := nontrivial_of_three_singular hT
  obtain ⟨hK, -⟩ := exists_kernelLineData_of_le hQ hp hp2 hpl E hcomm hexp hcard
  obtain ⟨n, P, hP, hPP, -, hPsp⟩ :=
    exists_piece_decomposition hQ hp hp2 hpl E hcomm hexp hcard hNS
  choose M hMc hMP hMk hMf _ _ using fun i => (hP i).exists_line hK hp hp2 hpl
  obtain ⟨i, j, hij⟩ := exists_pieces_diff_lines hK hp hpl hP hPsp (M := M)
    fun i => ⟨hMc i, hMP i⟩
  have hji : j ≠ i := fun h => hij (h ▸ rfl)
  haveI : Nonempty {k : Fin n // k ≠ i} := ⟨⟨j, hji⟩⟩
  have hEΩ : elementaryGroup Q ≤ orthDerived Q := (orthDerived_eq_and_le_closure hQ hT).1.ge
  have hEich : ∀ k : {k : Fin n // k ≠ i}, ∀ x ∈ planeFixSpace E ⊔ P i ⊔ P k,
      ∀ y ∈ planeFixSpace E ⊔ P i ⊔ P k, eichler Q x y ∈ orthSqSpan Q E := by
    intro k
    by_cases hM : M i = M k
    · have hle : planeFixSpace E ⊔ P i ⊔ P k ≤ planeFixSpace E ⊔ lineSpace (M i) := by
        refine sup_le (sup_le le_sup_left ((hMP i).trans le_sup_right)) ?_
        rw [hM]
        exact (hMP k).trans le_sup_right
      exact fun x hx y hy => orthSq_eichler_mem_of_mem_sup hEΩ
        (ne_bot_of_card_prime hp (hMc i)) (hle hx) (hle hy)
    · exact orthSq_eichler_mem_of_two_pieces hQ hT hp hp5 hpl hK hNS h4 (hP i) (hP k)
        (hPP i k k.2.symm) (hMc i) (hMc k) hM (hMk i) (hMk k) (hMf i) (hMf k)
  have hspan : (⊤ : Submodule K V) ≤
      planeFixSpace E ⊔ P i ⊔ ⨆ k : {k : Fin n // k ≠ i}, P k := by
    refine hPsp.trans (sup_le (le_sup_of_le_left le_sup_left) (iSup_le fun k => ?_))
    by_cases hk : k = i
    · rw [hk]
      exact le_sup_of_le_left le_sup_right
    · exact le_sup_of_le_right (le_iSup (fun k : {k : Fin n // k ≠ i} => P k) ⟨k, hk⟩)
  have hle : elementaryGroup Q ≤ orthSqSpan Q E :=
    elementaryGroup_le_of_pieces hQ (orthSqSpan_le_orthogonalGroup E) (hP i).regular
      (by have := hMf i; omega) (fun k : {k : Fin n // k ≠ i} => P k) (hP i).orthSep
      (fun k => hPP i k k.2.symm) hspan hEich
  exact orthSq_closure_eq_top_of_le E
    ((orthDerived_eq_and_le_closure hQ hT).1.le.trans hle)

end ManyBigMain

section Master

@[expose] def orthSqPlaneGen {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (p : ℕ) : Prop :=
  ∀ E : Subgroup (orthDerived Q), (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) →
    Nat.card E = p ^ 2 →
      Subgroup.closure {h : orthDerived Q |
        ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ (ringChar K ^ 2) = 1} = ⊤

theorem orthSq_master {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K) :
    orthSqPlaneGen Q p := by
  intro E hcomm hexp hcard
  classical
  by_cases hNS : OrthNoInvariantSingular Q E
  · obtain ⟨he2, k, hk⟩ := noSingular_ord hQ hp (by omega) hpl E hcomm hexp hcard hNS
    by_cases h4 : 4 ≤ orderOf ((Nat.card K : ℕ) : ZMod p)
    · exact orthSq_closure_eq_top_of_noSingular_big Q hQ hT hdim hp hp5 hpl E hcomm hexp hcard
        hNS h4
    · have he : orderOf ((Nat.card K : ℕ) : ZMod p) = 2 := by omega
      exact orthSq_closure_eq_top_of_noSingular_two Q hQ hT hdim hp (by omega) hpl
        (orthSq_three_le_card hp5 he) E hcomm hexp hcard hNS he
  · have hNS' : ¬ ∀ T : Submodule K V, (∀ e ∈ E, ∀ vector ∈ T,
        ((e : orthDerived Q) : V ≃ₗ[K] V) vector ∈ T) → (∀ vector ∈ T, Q vector = 0) → T = ⊥ :=
      hNS
    push Not at hNS'
    obtain ⟨W, hWst, hWQ, hW0⟩ := hNS'
    exact orthSq_closure_eq_top_of_singular_stable hQ hT hp (by omega) hpl E hcomm hexp hcard
      hW0 hWQ hWst

end Master

section Lift

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
  {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}

open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank in
theorem orthSq_closure_statedProj_of_gen (hQ : ⇑Q = Q₀)
    (hE : orthDerived Q = elementaryGroup Q) (hnd : (polarBilin Q).Nondegenerate)
    [Nontrivial (ι → K)] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hgen : orthSqPlaneGen Q p)
    (E : Subgroup (StatedProj (StatedOmega Q₀)))
    (hEab : CFSG.Open.IsElemAbelian p E) (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedOmega Q₀) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k ∧ k ^ (ringChar K ^ 2) = 1} = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ι → K) := inferInstance
  have : Finite ((ι → K) ≃ₗ[K] (ι → K)) :=
    Finite.of_injective (fun g => (g : (ι → K) → (ι → K))) DFunLike.coe_injective
  let ψ : StatedOmega Q₀ ≃* orthDerived Q :=
    (statedOmegaEquiv hQ hE).trans (MulEquiv.subgroupCongr hE).symm
  have hψ : ∀ y : StatedOmega Q₀,
      ((ψ y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) =
        toLinEquiv ι K (y : GL ι K) := fun y => rfl
  let π : orthDerived Q →* StatedProj (StatedOmega Q₀) :=
    (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf (StatedOmega Q₀))).comp
      ψ.symm.toMonoidHom
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp ψ.symm.surjective
  have hker : π.ker = (scalars K (ι → K)).subgroupOf (orthDerived Q) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change QuotientGroup.mk (ψ.symm x) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, mem_statedScalars_iff]
    have := hψ (ψ.symm x)
    rw [MulEquiv.apply_symm_apply] at this
    rw [← this]
  have hker' : ¬ p ∣ Nat.card π.ker := by
    rw [hker]
    have h := (scalarKernel_data hnd hp hp2).2
    rw [QuotientGroup.ker_mk'] at h
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 h.symm
  have : IsMulCommutative E := hEab.1
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  exact uniClosure_of_lift π hπ hker' E hcomm hEab.2 fun E' hc he hcd =>
    hgen E' hc he (hcd.trans hcard)

end Lift

section Leaves

open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank

theorem orthSq_oddPlanes {r p : ℕ} {K : Type} [Field K] [Finite K] (hr : 3 ≤ r) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) (h2 : (2 : K) ≠ 0)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadOdd r K)))) (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadOdd r K)) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k ∧ k ^ (ringChar K ^ 2) = 1} = ⊤ := by
  have hreg := regular_quadOdd (K := K) h2 hr
  have hdim : 7 ≤ finrank K (Fin r ⊕ Fin r ⊕ Unit → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  exact orthSq_closure_statedProj_of_gen (coe_quadOdd r K)
    (commutator_orthogonalGroup_quadOdd h2 hr) hreg.1 hp (by omega)
    (orthSq_master (quadOdd r K) hreg.1 hreg.2 hdim hp hp5 (ne_ringChar_of_not_dvd_card hpK)) E hE
    hcard

theorem orthSq_plusPlanes {r p : ℕ} {K : Type} [Field K] [Finite K] (hr : 4 ≤ r) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus r K)))) (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadPlus r K)) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k ∧ k ^ (ringChar K ^ 2) = 1} = ⊤ := by
  have hreg := regular_quadPlus (K := K) (n := r) (by omega)
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hdim : 7 ≤ finrank K (Fin r ⊕ Fin r → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  exact orthSq_closure_statedProj_of_gen (coe_quadPlus r K)
    (commutator_orthogonalGroup_quadPlus (by omega)) hreg.1 hp (by omega)
    (orthSq_master (quadPlus r K) hreg.1 hreg.2 hdim hp hp5 (ne_ringChar_of_not_dvd_card hpK)) E hE
    hcard

theorem orthSq_minusPlanes {r p : ℕ} {K : Type} [Field K] [Finite K] (b c : K) (hr : 4 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpK : ¬ p ∣ Nat.card K)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadMinus r K b c)))) (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadMinus r K b c)) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k ∧ k ^ (ringChar K ^ 2) = 1} = ⊤ := by
  have hreg := regular_quadMinus (K := K) (n := r) hr hirr
  have : Nonempty (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have hdim : 7 ≤ finrank K (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  exact orthSq_closure_statedProj_of_gen (coe_quadMinus r K b c)
    (commutator_orthogonalGroup_quadMinus hr hirr) hreg.1 hp (by omega)
    (orthSq_master (quadMinus r K b c) hreg.1 hreg.2 hdim hp hp5 (ne_ringChar_of_not_dvd_card hpK))
    E hE hcard

end Leaves

section Cat

open CFSG.Assembly.LowTwoRank

theorem orthSq_uniSeitzPlanes_orthogonal :
    Inputs2311c.UniSeitzPlanes fun d p E => CFSG.LieType.SeitzGeneration.InnerPlane d p E ∧ 5 ≤ p ∧
      CFSG.LieType.SeitzGeneration.IsOrthogonalIndex d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, hp5, horth⟩
  rcases horth with ⟨r, q, rfl, hr3, hq⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq
      hr3
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have hring := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p
      q.exponent_pos hcard
    have h2 : (2 : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) ≠ 0 :=
      Ring.two_ne_zero (by rw [hring]; exact hq)
    have : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadOdd r
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)))) :=
      CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadOdd_of_two_ne_zero
        h2 hr3
    have : IsSimpleGroup (Cat ⟨.B r q, hv⟩) := MulEquiv.isSimpleGroup e
    have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.B r q, hv⟩)
      (range_conj_ne_bot_of_inner hp hc hinner)
    suffices h : Inputs2311c.UniPlaneGen (q.p ^ 2) E by simpa using uniPlaneGen_of_pow h
    rw [← hring]
    refine Inputs2311c.uniPlaneGen_of_inner_model hinj e ?_ hE hc hinner
    intro E₁ hE₁ hcard₁
    exact orthSq_oddPlanes hr3 hp hp5 (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq')
      h2 E₁ hE₁ hcard₁
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have hring := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p
      q.exponent_pos hcard
    have : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadPlus r
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)))) :=
      CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (by omega)
    have : IsSimpleGroup (Cat ⟨.D r q, hv⟩) := MulEquiv.isSimpleGroup e
    have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.D r q, hv⟩)
      (range_conj_ne_bot_of_inner hp hc hinner)
    suffices h : Inputs2311c.UniPlaneGen (q.p ^ 2) E by simpa using uniPlaneGen_of_pow h
    rw [← hring]
    refine Inputs2311c.uniPlaneGen_of_inner_model hinj e ?_ hE hc hinner
    intro E₁ hE₁ hcard₁
    exact orthSq_plusPlanes hr4 hp hp5 (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq')
      E₁ hE₁ hcard₁
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    obtain ⟨b, c, hirr, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have hring := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p
      q.exponent_pos hcard
    have : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus r
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) b c))) :=
      CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus hr4 hirr
    have : IsSimpleGroup (Cat ⟨.twistedD r q, hv⟩) := MulEquiv.isSimpleGroup e
    have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.twistedD r q, hv⟩)
      (range_conj_ne_bot_of_inner hp hc hinner)
    suffices h : Inputs2311c.UniPlaneGen (q.p ^ 2) E by simpa using uniPlaneGen_of_pow h
    rw [← hring]
    refine Inputs2311c.uniPlaneGen_of_inner_model hinj e ?_ hE hc hinner
    intro E₁ hE₁ hcard₁
    exact orthSq_minusPlanes b c hr4 hirr hp hp5
      (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq') E₁ hE₁ hcard₁

end Cat

end OrthSq

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311e

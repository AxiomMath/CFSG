module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBTrans
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBString
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBStringWt
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBBridgeSep
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBCopies
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.AdjDispTorus
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Copies
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBExistsDigitF2

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.QuasithinUnique.Setup.SL2Modules


section Helpers

theorem twNdig_cases (f : ℕ) (c : TwN) : twNdig f c = f ∨ twNdig f c = 2 * f := by
  unfold twNdig; split_ifs <;> simp

theorem twNdig_pos {f : ℕ} (hf : 1 ≤ f) (c : TwN) : 1 ≤ twNdig f c := by
  rcases twNdig_cases f c with h | h <;> omega

theorem twPow_dvd (f : ℕ) (c : TwN) : 2 ^ f - 1 ∣ 2 ^ twNdig f c - 1 := by
  rcases twNdig_cases f c with h | h
  · rw [h]
  · rw [h]; exact Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_left f 2)

end Helpers

section UWords

theorem relCs_wordProd_smul (l : List TwN) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    (((relCs TwistTag.E6).wordProd l : ↥(relWeylTwist TwistTag.E6)) : WeylGroup TwistTag.E6.tag) • v =
      l.foldr (fun a w => (TwistTag.E6.orbitWord a).foldr (reflect TwistTag.E6.tag) w) v := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [CoxeterSystem.wordProd_cons, Subgroup.coe_mul, mul_smul, ih, relCs_simple]
    show TwistTag.E6.orbitReflection a • _ = _
    rw [TwistTag.orbitReflection, wordProd_smul_foldr]
    rfl

theorem twUWords_permute_check : ∀ (s : Fin Tag.F4.rank) (j : Fin 8),
    ∀ i ∈ TwistTag.E6.orbit (twNode s), ∃ i' ∈ TwistTag.E6.orbit (twNode s),
      (twWd (F4Exc.uWord s j)).foldr
        (fun a w => (TwistTag.E6.orbitWord a).foldr (reflect TwistTag.E6.tag) w)
        (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single i' 1 := by
  decide +kernel

theorem twUWords_distinct : ∀ (s : Fin Tag.F4.rank) (j j' : Fin 8), j ≠ j' →
    (twWd (F4Exc.uWord s j)).foldr (reflect TwistTag.E6.foldedTag) (f4Weight (twNode s)) ≠
      (twWd (F4Exc.uWord s j')).foldr (reflect TwistTag.E6.foldedTag) (f4Weight (twNode s)) := by
  decide +kernel

end UWords


section Infra

variable {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

include hf hK hσ in
theorem twCard_orbitField (a : TwN) : Nat.card (orbitField TwistTag.E6 K σ a) = 2 ^ twNdig f a := by
  rw [card_orbitField_e6 hf hK σ hσ a]
  have h : (TwistTag.E6.orbit a).card = if a.val < 2 then 2 else 1 := by
    revert a; decide
  unfold twNdig
  split_ifs at h ⊢
  · rw [h, ← pow_mul, mul_comm]
  · rw [h, pow_one]

include hf hK hσ in
theorem twNhat_mul_self (a : TwN) :
    (twistedE6CoverData hf hK σ hσ).nhat a * (twistedE6CoverData hf hK σ hσ).nhat a = 1 := by
  have hsq : (WSL : SL2 (orbitField TwistTag.E6 K σ a)) * WSL = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [WSL, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]
  refine Subtype.ext ?_
  show (((twistedE6CoverData hf hK σ hσ).nhat a : ↥(TwistedE6.fixedGroup K σ)) :
      ↥(e6Data_valid.minGroup K)) * (((twistedE6CoverData hf hK σ hσ).nhat a :
        ↥(TwistedE6.fixedGroup K σ)) : ↥(e6Data_valid.minGroup K)) = 1
  rw [nhat_coe hf hK σ hσ a, ← map_mul, hsq, map_one]

include hf hK hσ in
theorem twNhatW_wordProd (l : List TwN) :
    (twistedE6CoverData hf hK σ hσ).nhatW ((relCs TwistTag.E6).wordProd l) =
      (l.map (twistedE6CoverData hf hK σ hσ).nhat).prod := by
  induction l with
  | nil => simp [CoxeterSystem.wordProd_nil, (twistedE6CoverData hf hK σ hσ).nhatW_one]
  | cons a l ih =>
    rw [CoxeterSystem.wordProd_cons, List.map_cons, List.prod_cons, ← ih]
    set w := (relCs TwistTag.E6).wordProd l with hw
    rcases (relCs TwistTag.E6).length_simple_mul w a with hup | hdown
    · exact (twistedE6CoverData hf hK σ hσ).nhatW_simple_mul w a hup
    · have hw' : w = (relCs TwistTag.E6).simple a * ((relCs TwistTag.E6).simple a * w) := by
        rw [← mul_assoc, (relCs TwistTag.E6).simple_mul_simple_self a, one_mul]
      have hup' : (relCs TwistTag.E6).length ((relCs TwistTag.E6).simple a *
          ((relCs TwistTag.E6).simple a * w)) =
          (relCs TwistTag.E6).length ((relCs TwistTag.E6).simple a * w) + 1 := by
        rw [← hw']; omega
      have h2 := (twistedE6CoverData hf hK σ hσ).nhatW_simple_mul
        ((relCs TwistTag.E6).simple a * w) a hup'
      rw [← hw'] at h2
      rw [h2, ← mul_assoc]
      have := twNhat_mul_self hf K hK σ hσ a
      simp only [CentralCoverData.nhat] at this ⊢
      rw [this, one_mul]

theorem twWSL_HSL {F : Type} [Field F] (z : Fˣ) :
    (HSL z : SL2 F) * WSL * (HSL z)⁻¹ = WSL * HSL (z⁻¹ * z⁻¹) := by
  have h1 : (WSL : SL2 F) * HSL z⁻¹ = HSL z * WSL := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;> simp [WSL, HSL, Matrix.mul_apply, Fin.sum_univ_two]
  have hinv : (HSL z : SL2 F)⁻¹ = HSL z⁻¹ :=
    inv_eq_of_mul_eq_one_right (by rw [← HSL_mul, mul_inv_cancel, HSL_one])
  rw [← h1, hinv, mul_assoc, ← HSL_mul]

include hf hK hσ in
theorem twWt_nhat {k : Type} [Field k] [CharP k 2] [Algebra K k] {V : Type} [AddCommGroup V]
    [Module k V] (ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V) (a : TwN) {e : TwN → ℤ}
    {v : V} (hv : v ∈ twWt hf hK σ hσ ρ e) :
    ρ ((twistedE6CoverData hf hK σ hσ).nhat a) v ∈ twWt hf hK σ hσ ρ (twRefl f a e) := by
  intro b w
  have hσσ := sigma_sigma_eq hK σ hσ
  obtain ⟨z, hz, hconj⟩ := conj_rhat_eq σ hσσ hσ b a w
  have hH : hatH hf hK σ hσ b w * (twistedE6CoverData hf hK σ hσ).nhat a *
      (hatH hf hK σ hσ b w)⁻¹ =
        (twistedE6CoverData hf hK σ hσ).nhat a * hatH hf hK σ hσ a (z⁻¹ * z⁻¹) := by
    refine Subtype.ext ?_
    show minOrbitHom σ b (HSL w) *
        (((twistedE6CoverData hf hK σ hσ).nhat a : ↥(TwistedE6.fixedGroup K σ)) :
          ↥(e6Data_valid.minGroup K)) * (minOrbitHom σ b (HSL w))⁻¹ =
        (((twistedE6CoverData hf hK σ hσ).nhat a : ↥(TwistedE6.fixedGroup K σ)) :
          ↥(e6Data_valid.minGroup K)) * minOrbitHom σ a (HSL (z⁻¹ * z⁻¹))
    rw [nhat_coe hf hK σ hσ a, hconj WSL, twWSL_HSL, map_mul]
  have hG : hatH hf hK σ hσ b w * (twistedE6CoverData hf hK σ hσ).nhat a =
      (twistedE6CoverData hf hK σ hσ).nhat a * hatH hf hK σ hσ a (z⁻¹ * z⁻¹) *
        hatH hf hK σ hσ b w := by
    calc hatH hf hK σ hσ b w * (twistedE6CoverData hf hK σ hσ).nhat a
        = (hatH hf hK σ hσ b w * (twistedE6CoverData hf hK σ hσ).nhat a *
            (hatH hf hK σ hσ b w)⁻¹) * hatH hf hK σ hσ b w := by group
      _ = _ := by rw [hH]
  set ω : k := algebraMap K k ((w : orbitField TwistTag.E6 K σ b) : K) with hω
  set ζ : k := algebraMap K k ((z : orbitField TwistTag.E6 K σ a) : K) with hζ
  have hω0 : ω ≠ 0 := (map_ne_zero _).2 (unit_coe_ne_zero σ w)
  have hζ0 : ζ ≠ 0 := (map_ne_zero _).2 (unit_coe_ne_zero σ z)
  have hζω : ζ ^ 2 = ω ^ (twA f b a) := by
    have := congrArg (algebraMap K k) hz
    rwa [map_pow, map_zpow₀] at this
  have hu : algebraMap K k (((z⁻¹ * z⁻¹ : (orbitField TwistTag.E6 K σ a)ˣ) :
      orbitField TwistTag.E6 K σ a) : K) = (ζ⁻¹) ^ 2 := by
    simp [hζ, sq, map_mul, map_inv₀]
  show ρ (hatH hf hK σ hσ b w) (ρ ((twistedE6CoverData hf hK σ hσ).nhat a) v) =
    ω ^ (e b - twA f b a * e a) • ρ ((twistedE6CoverData hf hK σ hσ).nhat a) v
  rw [← Module.End.mul_apply, ← map_mul, hG, map_mul, map_mul, Module.End.mul_apply,
    Module.End.mul_apply, hv b w, map_smul, hv a (z⁻¹ * z⁻¹), hu, map_smul, map_smul, smul_smul]
  congr 1
  have h2 : ((ζ⁻¹) ^ 2) ^ (e a) = ω ^ (-(twA f b a) * e a) := by
    have h3 : (ζ⁻¹) ^ 2 = ω ^ (-(twA f b a)) := by
      rw [inv_pow, hζω, ← zpow_neg]
    rw [h3, ← zpow_mul]
  rw [h2, ← zpow_add₀ hω0]
  congr 1
  ring

include hf hK hσ in
theorem twWt_nhatProd {k : Type} [Field k] [CharP k 2] [Algebra K k] {V : Type} [AddCommGroup V]
    [Module k V] (ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V) (l : List TwN) {e : TwN → ℤ}
    {v : V} (hv : v ∈ twWt hf hK σ hσ ρ e) :
    ρ ((l.map (twistedE6CoverData hf hK σ hσ).nhat).prod) v ∈ twWt hf hK σ hσ ρ (twAct f l e) := by
  induction l with
  | nil => simpa [twAct] using hv
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply]
    exact twWt_nhat hf K hK σ hσ ρ a ih

@[expose] def twCls (K : Type) [Field K] [Finite K] [CharP K 2] (σ : K →+* K) (k : Type) [Field k]
    [Algebra K k] (e : TwN → ℤ) : (Σ a : TwN, (orbitField TwistTag.E6 K σ a)ˣ) → k :=
  fun p => (algebraMap K k ((p.2 : orbitField TwistTag.E6 K σ p.1) : K)) ^ (e p.1)

include hf hK hσ in
theorem dvd_of_twCls_eq {k : Type} [Field k] [Algebra K k] {e e' : TwN → ℤ}
    (h : twCls K σ k e = twCls K σ k e') (a : TwN) : ((2 ^ twNdig f a - 1 : ℕ) : ℤ) ∣ e a - e' a := by
  obtain ⟨g, hg⟩ := (inferInstance : IsCyclic (orbitField TwistTag.E6 K σ a)ˣ)
  have hord : orderOf g = 2 ^ twNdig f a - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units,
      twCard_orbitField hf K hK σ hσ a]
  have h1 := congrFun h ⟨a, g⟩
  simp only [twCls] at h1
  have hne : (algebraMap K k ((g : orbitField TwistTag.E6 K σ a) : K)) ≠ 0 :=
    (map_ne_zero _).2 (by simp)
  have h2 : (algebraMap K k ((g : orbitField TwistTag.E6 K σ a) : K)) ^ (e a - e' a) = 1 := by
    rw [zpow_sub₀ hne, h1, div_self (zpow_ne_zero _ hne)]
  have h3 : ((g : orbitField TwistTag.E6 K σ a) : K) ^ (e a - e' a) = 1 := by
    apply (algebraMap K k).injective
    rw [map_zpow₀, map_one]
    exact h2
  have h4 : g ^ (e a - e' a) = 1 := by
    apply Units.ext
    rw [Units.val_zpow_eq_zpow_val, Units.val_one]
    apply (orbitField TwistTag.E6 K σ a).subtype.injective
    rw [map_zpow₀, map_one]
    exact h3
  rw [← hord]
  exact orderOf_dvd_iff_zpow_eq_one.2 h4

include hf hK hσ in
theorem twLinearIndependent_of_wt {k : Type} [Field k] [CharP k 2] [Algebra K k] {V : Type}
    [AddCommGroup V] [Module k V] (ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V) {ι : Type*}
    (v : ι → V) (e : ι → TwN → ℤ) (hv : ∀ p, v p ∈ twWt hf hK σ hσ ρ (e p))
    (hin : ∀ c : (Σ a : TwN, (orbitField TwistTag.E6 K σ a)ˣ) → k,
      LinearIndependent k (fun p : {p : ι // twCls K σ k (e p) = c} => v p.1)) :
    LinearIndependent k v := by
  classical
  let T : (Σ a : TwN, (orbitField TwistTag.E6 K σ a)ˣ) → Module.End k V :=
    fun p => ρ (hatH hf hK σ hσ p.1 p.2)
  set G : ((Σ a : TwN, (orbitField TwistTag.E6 K σ a)ˣ) → k) → Submodule k V := fun c =>
    ⨅ p, Module.End.maxGenEigenspace (T p) (c p) with hG
  have hcomm : ∀ p q : (Σ a : TwN, (orbitField TwistTag.E6 K σ a)ˣ),
      hatH hf hK σ hσ q.1 q.2 * hatH hf hK σ hσ p.1 p.2 =
        hatH hf hK σ hσ p.1 p.2 * hatH hf hK σ hσ q.1 q.2 := fun p q =>
    hcomm_cover hf hK σ hσ _ ((twistedE6CoverRankOne hf hK σ hσ).hh_mem q.1 q.2) _
      ((twistedE6CoverRankOne hf hK σ hσ).hh_mem p.1 p.2)
  have hind : iSupIndep G := by
    apply Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    intro p q φ
    apply Module.End.mapsTo_maxGenEigenspace_of_comm
    have := congrArg ρ (hcomm p q)
    rw [map_mul, map_mul] at this
    exact this
  have hle : ∀ c, Submodule.span k (Set.range
      (fun p : {p : ι // twCls K σ k (e p) = c} => v p.1)) ≤ G c := by
    intro c
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    have h1 : v p.1 ∈ ⨅ pt, Module.End.maxGenEigenspace (T pt) (twCls K σ k (e p.1) pt) := by
      rw [Submodule.mem_iInf]
      intro pt
      apply Module.End.eigenspace_le_maxGenEigenspace
      rw [Module.End.mem_eigenspace_iff]
      exact hv p.1 pt.1 pt.2
    rw [p.2] at h1
    exact h1
  have hsig := linearIndependent_iUnion_finite (R := k)
    (f := fun (c : (Σ a : TwN, (orbitField TwistTag.E6 K σ a)ˣ) → k)
      (p : {p : ι // twCls K σ k (e p) = c}) => v p.1) hin
    (fun c t _ hct => (hind.disjoint_biSup hct).mono (hle c) (iSup₂_mono fun i _ => hle i))
  let e' : (Σ c : (Σ a : TwN, (orbitField TwistTag.E6 K σ a)ˣ) → k,
      {p : ι // twCls K σ k (e p) = c}) ≃ ι :=
    Equiv.sigmaFiberEquiv (fun p => twCls K σ k (e p))
  exact (linearIndependent_equiv e').1 hsig

include hf hK hσ in
theorem twCopiesConjX (a : TwN) (w : ↥(relWeylTwist TwistTag.E6))
    (hw : ∀ i ∈ TwistTag.E6.orbit a, ∃ j ∈ TwistTag.E6.orbit a,
      (w : WeylGroup TwistTag.E6.tag) • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single j 1) :
    ∃ φ : orbitField TwistTag.E6 K σ a ≃ orbitField TwistTag.E6 K σ a, ∀ c,
      (twistedE6CoverData hf hK σ hσ).nhatW w * hatX hf hK σ hσ a c *
        ((twistedE6CoverData hf hK σ hσ).nhatW w)⁻¹ = hatX hf hK σ hσ a (φ c) := by
  have h1 : ∀ c : orbitField TwistTag.E6 K σ a, ∃ c' : orbitField TwistTag.E6 K σ a,
      (twistedE6CoverData hf hK σ hσ).nhatW w * hatX hf hK σ hσ a c *
        ((twistedE6CoverData hf hK σ hσ).nhatW w)⁻¹ = hatX hf hK σ hσ a c' := by
    intro c
    obtain ⟨c', hc'⟩ := conj_orbit_prod σ a (w : WeylGroup TwistTag.E6.tag)
      (fun i => Pi.single i 1) (fun i => isRoot_single Tag.E6 i) single_injective
      (fun i hi j hj hij c d => by
        have := commute_slMin (K := K) hi hj hij (uSL c) (uSL d)
        have e1 : e6Data_valid.xm K (Pi.single i 1) c = slMin K i (uSL c) :=
          (slMin_upper i c).symm
        have e2 : e6Data_valid.xm K (Pi.single j 1) d = slMin K j (uSL d) :=
          (slMin_upper j d).symm
        rw [e1, e2]
        exact this) hw c
    refine ⟨c', Subtype.ext ?_⟩
    show canonMin K (w : WeylGroup TwistTag.E6.tag) * minOrbitHom σ a (uSL c) *
      (canonMin K (w : WeylGroup TwistTag.E6.tag))⁻¹ = minOrbitHom σ a (uSL c')
    rw [minOrbitHom_uSL, minOrbitHom_uSL]
    exact hc'
  choose ψ hψ using h1
  have hinj : Function.Injective ψ := by
    intro c₁ c₂ h
    have h2 := hψ c₁
    rw [h, ← hψ c₂] at h2
    have h3 : hatX hf hK σ hσ a c₁ = hatX hf hK σ hσ a c₂ := by
      have := mul_right_cancel h2
      exact mul_left_cancel this
    exact (twistedE6CoverRankOne hf hK σ hσ).x_inj a h3
  exact ⟨Equiv.ofBijective ψ (Finite.injective_iff_bijective.1 hinj), hψ⟩


set_option maxHeartbeats 1600000 in
include hf hK hσ in
theorem twCopies_core (hCop : TwCopiesNormalize hf K hK σ hσ)
    {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k] {m : ℕ}
    {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)} (hρ : IsSimpleRep ρ)
    {y : Fin m → k} {χ : ↥(TwistedE6.fixedGroup K σ) → k} {J : Finset TwN}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J) {s : TwN} {m' : ℕ}
    (u : Fin m' → ↥(relWeylTwist TwistTag.E6))
    (hu : ∀ i, ∀ r ∈ TwistTag.E6.orbit s, ∃ r' ∈ TwistTag.E6.orbit s,
      ((u i : ↥(relWeylTwist TwistTag.E6)) : WeylGroup TwistTag.E6.tag) •
        (Pi.single r 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single r' 1)
    (hli : LinearIndependent k (fun i => ρ ((twistedE6CoverData hf hK σ hσ).nhatW (u i)) y)) :
    (Module.finrank k ↥(⨆ i ∈ (Finset.univ : Finset (Fin m')),
        orbitSpan (ρ.comp (Rhat hf hK σ hσ s)) (ρ ((twistedE6CoverData hf hK σ hσ).nhatW (u i)) y)) =
      ∑ i : Fin m', Module.finrank k
        (orbitSpan (ρ.comp (Rhat hf hK σ hσ s)) (ρ ((twistedE6CoverData hf hK σ hσ).nhatW (u i)) y))) ∧
    iSupIndep (fun i : Fin m' =>
      orbitSpan (ρ.comp (Rhat hf hK σ hσ s)) (ρ ((twistedE6CoverData hf hK σ hσ).nhatW (u i)) y)) ∧
    ∀ i, orbitSpan (ρ.comp (Rhat hf hK σ hσ s)) (ρ ((twistedE6CoverData hf hK σ hσ).nhatW (u i)) y) =
      (orbitSpan (ρ.comp (Rhat hf hK σ hσ s)) y).map
        (ρ ((twistedE6CoverData hf hK σ hσ).nhatW (u i))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Algebra (orbitField TwistTag.E6 K σ s) k :=
    ((algebraMap K k).comp (orbitField TwistTag.E6 K σ s).subtype).toAlgebra
  set C := twistedE6CoverData hf hK σ hσ with hC
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ (twistedCover_split hf hK σ hσ k)
  set σ' : Representation k (SL2 (orbitField TwistTag.E6 K σ s)) (Fin m → k) :=
    ρ.comp (Rhat hf hK σ hσ s) with hσ'
  have hFst0 : ∀ g : SL2 (orbitField TwistTag.E6 K σ s), ∀ w ∈ fixSub ρ (C.datum.Us s),
      ρ (Rhat hf hK σ hσ s g) w ∈ fixSub ρ (C.datum.Us s) := by
    intro g w hw
    refine fixSub_stable_of_hom ρ (Rhat hf hK σ hσ s) (C.datum.Us s) ?_ ?_ ?_ ?_ g hw
    · intro c q hq
      exact (hatX_norm hf K hK σ hσ s c q hq).1
    · intro c q hq
      exact (hatX_norm hf K hK σ hσ s c q hq).2
    · intro c q hq
      exact (hatY_norm hf K hK σ hσ s c q hq).1
    · intro c q hq
      exact (hatY_norm hf K hK σ hσ s c q hq).2
  have hfix0 : ∀ f0 ∈ fixSub ρ (C.datum.Us s),
      (∀ c : orbitField TwistTag.E6 K σ s, ρ (hatX hf hK σ hσ s c) f0 = f0) →
      ∃ c : k, f0 = c • y := by
    intro f0 hf0 hfu
    have hfU : f0 ∈ C.datum.fixU ρ := by
      intro u' hu'
      obtain ⟨x, hx, v, hv, rfl⟩ := C.datum.U_eq s u' hu'
      obtain ⟨c, rfl⟩ := (twistedE6CoverRankOne hf hK σ hσ).mem_lX_iff s |>.1 hx
      rw [← act_mul, hf0 v hv]
      exact hfu c
    exact C.datum.fixU_eq_smul hρ hμ hfU
  have hvu0 : ∀ c : orbitField TwistTag.E6 K σ s, ρ (hatX hf hK σ hσ s c) y = y := fun c =>
    ht.1 _ (C.datum.X_le s ((twistedE6CoverRankOne hf hK σ hσ).x_mem s c))
  have hyFix : y ∈ fixSub ρ (C.datum.Us s) := fun q hq => ht.1 q (C.datum.Us_le s hq)
  set N : Fin m' → ↥(TwistedE6.fixedGroup K σ) := fun i => C.nhatW (u i) with hN
  have hmapR : ∀ i, Subgroup.map (MulAut.conj (N i)).toMonoidHom (Rhat hf hK σ hσ s).range =
      (Rhat hf hK σ hσ s).range := fun i => hCop s (u i) (hu i)
  have hnormF : ∀ i (g : SL2 (orbitField TwistTag.E6 K σ s)),
      ∃ g' : SL2 (orbitField TwistTag.E6 K σ s),
        Rhat hf hK σ hσ s g' = N i * Rhat hf hK σ hσ s g * (N i)⁻¹ := by
    intro i g
    have h1 : (MulAut.conj (N i)) (Rhat hf hK σ hσ s g) ∈
        Subgroup.map (MulAut.conj (N i)).toMonoidHom (Rhat hf hK σ hσ s).range :=
      Subgroup.mem_map_of_mem _ ⟨g, rfl⟩
    rw [hmapR i] at h1
    obtain ⟨g', hg'⟩ := h1
    exact ⟨g', by rw [hg', MulAut.conj_apply]⟩
  have hnormB : ∀ i (g : SL2 (orbitField TwistTag.E6 K σ s)),
      ∃ g' : SL2 (orbitField TwistTag.E6 K σ s),
        Rhat hf hK σ hσ s g' = (N i)⁻¹ * Rhat hf hK σ hσ s g * N i := by
    intro i g
    have h1 : Rhat hf hK σ hσ s g ∈
        Subgroup.map (MulAut.conj (N i)).toMonoidHom (Rhat hf hK σ hσ s).range := by
      rw [hmapR i]
      exact ⟨g, rfl⟩
    obtain ⟨_, ⟨g', rfl⟩, hg'⟩ := h1
    refine ⟨g', ?_⟩
    have h2 : Rhat hf hK σ hσ s g = N i * Rhat hf hK σ hσ s g' * (N i)⁻¹ := by
      rw [← hg']
      simp [MulAut.conj_apply]
    rw [h2]
    group
  have hX : ∀ i, ∃ φ : orbitField TwistTag.E6 K σ s ≃ orbitField TwistTag.E6 K σ s, ∀ c,
      N i * hatX hf hK σ hσ s c * (N i)⁻¹ = hatX hf hK σ hσ s (φ c) :=
    fun i => twCopiesConjX hf K hK σ hσ s (u i) (hu i)
  have hXinv : ∀ i (c : orbitField TwistTag.E6 K σ s), ∃ c' : orbitField TwistTag.E6 K σ s,
      hatX hf hK σ hσ s c * N i = N i * hatX hf hK σ hσ s c' := by
    intro i c
    obtain ⟨φ, hφ⟩ := hX i
    refine ⟨φ.symm c, ?_⟩
    have h1 := hφ (φ.symm c)
    rw [φ.apply_symm_apply] at h1
    rw [← h1]
    group
  have hXsurj : ∀ i (c' : orbitField TwistTag.E6 K σ s),
      ∃ c : orbitField TwistTag.E6 K σ s,
        hatX hf hK σ hσ s c * N i = N i * hatX hf hK σ hσ s c' := by
    intro i c'
    obtain ⟨φ, hφ⟩ := hX i
    refine ⟨φ c', ?_⟩
    rw [← hφ c']
    group
  have hmap_inj : ∀ i, Function.Injective (ρ (N i)) := fun i => (CurtisExc.repEquiv ρ _).injective
  set Fix : Fin m' → Submodule k (Fin m → k) := fun i =>
    (fixSub ρ (C.datum.Us s)).map (ρ (N i)) with hFix
  have hvF : ∀ i, ρ (N i) y ∈ Fix i := fun i => Submodule.mem_map_of_mem hyFix
  have hFst : ∀ i, ∀ g : SL2 (orbitField TwistTag.E6 K σ s), ∀ w ∈ Fix i, σ' g w ∈ Fix i := by
    intro i g w hw
    obtain ⟨f0, hf0, rfl⟩ := hw
    obtain ⟨g', hg'⟩ := hnormB i g
    have h1 : Rhat hf hK σ hσ s g * N i = N i * Rhat hf hK σ hσ s g' := by rw [hg']; group
    refine ⟨ρ (Rhat hf hK σ hσ s g') f0, hFst0 g' f0 hf0, ?_⟩
    show ρ (N i) (ρ (Rhat hf hK σ hσ s g') f0) = ρ (Rhat hf hK σ hσ s g) (ρ (N i) f0)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, h1]
  have hfix : ∀ i, ∀ f ∈ Fix i, (∀ c : orbitField TwistTag.E6 K σ s, σ' (uElt c) f = f) →
      ∃ c : k, f = c • ρ (N i) y := by
    intro i f hf hfu
    obtain ⟨f0, hf0, rfl⟩ := hf
    have hall : ∀ c' : orbitField TwistTag.E6 K σ s, ρ (hatX hf hK σ hσ s c') f0 = f0 := by
      intro c'
      obtain ⟨c, hc⟩ := hXsurj i c'
      have h := hfu c
      have h2 : ρ (N i) (ρ (hatX hf hK σ hσ s c') f0) = ρ (N i) f0 := by
        rw [← Module.End.mul_apply, ← map_mul, ← hc, map_mul, Module.End.mul_apply]
        exact h
      exact hmap_inj i h2
    obtain ⟨c, hc⟩ := hfix0 f0 hf0 hall
    exact ⟨c, by rw [hc, map_smul]⟩
  have hvu : ∀ i, ∀ c : orbitField TwistTag.E6 K σ s, σ' (uElt c) (ρ (N i) y) = ρ (N i) y := by
    intro i c
    obtain ⟨c', hc'⟩ := hXinv i c
    show ρ (hatX hf hK σ hσ s c) (ρ (N i) y) = ρ (N i) y
    rw [← Module.End.mul_apply, ← map_mul, hc', map_mul, Module.End.mul_apply, hvu0 c']
  have hres := CurtisExc.finrank_iSup_orbitSpan σ' (fun i => ρ (N i) y) Fix hvF hFst hfix hvu
    Finset.univ (hli.comp (fun x : (↑(Finset.univ : Finset (Fin m')) : Set (Fin m')) => (x : Fin m'))
      Subtype.val_injective)
  obtain ⟨hdim, -, hsup⟩ := hres
  refine ⟨hdim, Finset.SupIndep.iSupIndep_of_univ hsup, fun i => ?_⟩
  apply le_antisymm
  · rw [orbitSpan, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    obtain ⟨g', hg'⟩ := hnormB i g
    have e1 : Rhat hf hK σ hσ s g * N i = N i * Rhat hf hK σ hσ s g' := by rw [hg']; group
    refine ⟨σ' g' y, Submodule.subset_span ⟨g', rfl⟩, ?_⟩
    show ρ (N i) (ρ (Rhat hf hK σ hσ s g') y) = ρ (Rhat hf hK σ hσ s g) (ρ (N i) y)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, e1]
  · rw [orbitSpan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    obtain ⟨g'', hg''⟩ := hnormF i g
    have e1 : Rhat hf hK σ hσ s g'' * N i = N i * Rhat hf hK σ hσ s g := by rw [hg'']; group
    refine Submodule.subset_span ⟨g'', ?_⟩
    show ρ (Rhat hf hK σ hσ s g'') (ρ (N i) y) = ρ (N i) (ρ (Rhat hf hK σ hσ s g) y)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, e1]

include hf hK hσ in
theorem twCopies_linearIndependent (hCop : TwCopiesNormalize hf K hK σ hσ)
    {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k] {m : ℕ}
    {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)} (hρ : IsSimpleRep ρ)
    {y : Fin m → k} {χ : ↥(TwistedE6.fixedGroup K σ) → k} {J : Finset TwN}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J) {s : TwN} {m' : ℕ}
    (u : Fin m' → ↥(relWeylTwist TwistTag.E6))
    (hu : ∀ i, ∀ r ∈ TwistTag.E6.orbit s, ∃ r' ∈ TwistTag.E6.orbit s,
      ((u i : ↥(relWeylTwist TwistTag.E6)) : WeylGroup TwistTag.E6.tag) •
        (Pi.single r 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single r' 1)
    (hli : LinearIndependent k (fun i => ρ ((twistedE6CoverData hf hK σ hσ).nhatW (u i)) y))
    {e : Fin m → k} (he : e ∈ orbitSpan (ρ.comp (Rhat hf hK σ hσ s)) y) (he0 : e ≠ 0) :
    LinearIndependent k (fun i => ρ ((twistedE6CoverData hf hK σ hσ).nhatW (u i)) e) := by
  obtain ⟨-, hind, hN⟩ := twCopies_core hf K hK σ hσ hCop hρ ht u hu hli
  have hmap_inj : ∀ i, Function.Injective (ρ ((twistedE6CoverData hf hK σ hσ).nhatW (u i))) :=
    fun i => (CurtisExc.repEquiv ρ _).injective
  refine hind.linearIndependent _ (fun i => ?_) (fun i h0 => he0 (hmap_inj i (by rw [h0, map_zero])))
  rw [hN i]
  exact Submodule.mem_map_of_mem he

include hf hK hσ in
theorem twCopies_finrank (hCop : TwCopiesNormalize hf K hK σ hσ)
    {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k] {m : ℕ}
    {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)} (hρ : IsSimpleRep ρ)
    {y : Fin m → k} {χ : ↥(TwistedE6.fixedGroup K σ) → k} {J : Finset TwN}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J) {s : TwN} {m' : ℕ}
    (u : Fin m' → ↥(relWeylTwist TwistTag.E6))
    (hu : ∀ i, ∀ r ∈ TwistTag.E6.orbit s, ∃ r' ∈ TwistTag.E6.orbit s,
      ((u i : ↥(relWeylTwist TwistTag.E6)) : WeylGroup TwistTag.E6.tag) •
        (Pi.single r 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single r' 1)
    (hli : LinearIndependent k (fun i => ρ ((twistedE6CoverData hf hK σ hσ).nhatW (u i)) y)) :
    m' * Module.finrank k (orbitSpan (ρ.comp (Rhat hf hK σ hσ s)) y) ≤ m := by
  obtain ⟨hdim, -, hN⟩ := twCopies_core hf K hK σ hσ hCop hρ ht u hu hli
  have hNdim : ∀ i, Module.finrank k (orbitSpan (ρ.comp (Rhat hf hK σ hσ s))
      (ρ ((twistedE6CoverData hf hK σ hσ).nhatW (u i)) y)) =
      Module.finrank k (orbitSpan (ρ.comp (Rhat hf hK σ hσ s)) y) := by
    intro i
    rw [hN i]
    exact (CurtisExc.repEquiv ρ _).finrank_map_eq _
  calc m' * Module.finrank k (orbitSpan (ρ.comp (Rhat hf hK σ hσ s)) y)
      = ∑ i : Fin m', Module.finrank k (orbitSpan (ρ.comp (Rhat hf hK σ hσ s))
          (ρ ((twistedE6CoverData hf hK σ hσ).nhatW (u i)) y)) := by simp [hNdim]
    _ = Module.finrank k ↥(⨆ i ∈ (Finset.univ : Finset (Fin m')),
        orbitSpan (ρ.comp (Rhat hf hK σ hσ s)) (ρ ((twistedE6CoverData hf hK σ hσ).nhatW (u i)) y)) :=
      hdim.symm
    _ ≤ Module.finrank k (Fin m → k) := Submodule.finrank_le _
    _ = m := Module.finrank_fin_fun k

include hf hK hσ in
theorem twTranslates_linearIndependent {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k]
    {m : ℕ} {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)} (hρ : IsSimpleRep ρ)
    {y : Fin m → k} {χ : ↥(TwistedE6.fixedGroup K σ) → k} {J : Finset TwN}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J) {s : Fin Tag.F4.rank}
    (hs : twNode s ∉ J) :
    LinearIndependent k (fun j : Fin 8 => ρ ((twistedE6CoverData hf hK σ hσ).nhatW
      ((relCs TwistTag.E6).wordProd (twWd (F4Exc.uWord s j)))) y) := by
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ (twistedCover_split hf hK σ hσ k)
  let v : Fin TwistTag.E6.foldedTag.rank → ℤ := f4Weight (twNode s)
  let w : Fin 8 → ↥(relWeylTwist TwistTag.E6) := fun j =>
    (relCs TwistTag.E6).wordProd (twWd (F4Exc.uWord s j))
  have hfw : ∀ j, foldedWeylEquiv TwistTag.E6 (w j) • v =
      (twWd (F4Exc.uWord s j)).foldr (reflect TwistTag.E6.foldedTag) v := fun j => by
    show foldedWeylEquiv TwistTag.E6 ((relCs TwistTag.E6).wordProd _) • v = _
    rw [relCs_wordProd, wordProd_smul_foldr]
  have hinj : ∀ i j : Fin 8, i ≠ j →
      foldedWeylEquiv TwistTag.E6 (w i) • v ≠ foldedWeylEquiv TwistTag.E6 (w j) • v := by
    intro i j hij h
    rw [hfw, hfw] at h
    exact twUWords_distinct s i j hij h
  refine CurtisExc.linearIndependent_translates hρ hμ w (fun i j hij ω hω hωe => ?_)
  have hne : (coxeterSystem TwistTag.E6.foldedTag).wordProd
      (ω : List (Fin TwistTag.E6.foldedTag.rank)) • v ≠ v := by
    intro h
    apply hinj i j hij
    rw [← relCs_wordProd, hωe, map_mul, map_inv, mul_smul] at h
    have := congrArg (fun z => foldedWeylEquiv TwistTag.E6 (w i) • z) h
    simpa [smul_smul] using this.symm
  obtain ⟨l, hl, hlv⟩ := exists_letter_moving hne
  have hl' : l = twNode s := by
    by_contra hne'
    exact hlv (f4Weight_fixed (twNode s) l hne')
  have : Fintype (orbitField TwistTag.E6 K σ l)ˣ := Fintype.ofFinite _
  exact ⟨l, hl, IsCoverType.mu_eq_dScalar (twistedCover_hodd hf hK σ hσ) ht hμ (hl' ▸ hs)⟩

include hf hK hσ in
theorem twDimGeOfSep (hWS : TwWeightShift hf K hK σ hσ) (hCop : TwCopiesNormalize hf K hK σ hσ)
    {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k] {m : ℕ}
    {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)} (hρ : IsSimpleRep ρ)
    {y : Fin m → k} {χ : ↥(TwistedE6.fixedGroup K σ) → k} {J : Finset TwN}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J) {s : Fin Tag.F4.rank}
    (hs : twNode s ∉ J) (lam : TwN → ℤ) (hy : y ∈ twWt hf hK σ hσ ρ lam) (B : Finset ℕ)
    (hE : ∀ b ∈ B, ∃ e ∈ orbitSpan (ρ.comp (Rhat hf hK σ hσ (twNode s))) y, e ≠ 0 ∧
      ∀ z : (orbitField TwistTag.E6 K σ (twNode s))ˣ, ρ (hatH hf hK σ hσ (twNode s) z) e =
        (algebraMap K k ((z : orbitField TwistTag.E6 K σ (twNode s)) : K)) ^
          (lam (twNode s) - 2 ^ (b + 1)) • e)
    (hsep : ∀ (i i' : Fin 12) (j j' : Fin 8) (b b' : ℕ), b ∈ B → b' ∈ B →
      (∀ c : TwN, ((2 ^ twNdig f c - 1 : ℕ) : ℤ) ∣
        twV f s lam b i j c - twV f s lam b' i' j' c) → i = i' ∧ b = b') :
    96 * B.card ≤ m := by
  classical
  have hE' : ∀ b : ℕ, ∃ e : Fin m → k, b ∈ B → (e ∈ orbitSpan (ρ.comp (Rhat hf hK σ hσ (twNode s))) y ∧
      e ≠ 0 ∧ ∀ z : (orbitField TwistTag.E6 K σ (twNode s))ˣ,
        ρ (hatH hf hK σ hσ (twNode s) z) e =
          (algebraMap K k ((z : orbitField TwistTag.E6 K σ (twNode s)) : K)) ^
            (lam (twNode s) - 2 ^ (b + 1)) • e) := by
    intro b
    by_cases hb : b ∈ B
    · obtain ⟨e, he, he0, hes⟩ := hE b hb
      exact ⟨e, fun _ => ⟨he, he0, hes⟩⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose Ev hEv using hE'
  have hEw : ∀ b ∈ B, Ev b ∈ twWt hf hK σ hσ ρ
      (fun c => lam c - 2 ^ b * twRoot f (twNode s) c) := by
    intro b hb
    obtain ⟨he, he0, hes⟩ := hEv b hb
    have h1 := hWS k ρ (twNode s) lam y hy (2 ^ b) (Ev b) he (fun z => by
      rw [hes z]
      congr 2
      push_cast
      ring)
    have h2 : (fun c => lam c - (((2 ^ b : ℕ) : ℤ)) * twA f c (twNode s)) =
        (fun c => lam c - 2 ^ b * twRoot f (twNode s) c) := by
      funext c
      simp [twRoot]
    rw [h2] at h1
    exact h1
  let ι := Fin 12 × Fin 8 × {b : ℕ // b ∈ B}
  let u : Fin 8 → ↥(relWeylTwist TwistTag.E6) := fun j =>
    (relCs TwistTag.E6).wordProd (twWd (F4Exc.uWord s j))
  let w : Fin 12 → ↥(relWeylTwist TwistTag.E6) := fun i =>
    (relCs TwistTag.E6).wordProd (twWd (F4Exc.gamWord s i))
  let ν : ι → TwN → ℤ := fun p => twV f s lam p.2.2 p.1 p.2.1
  let v : ι → (Fin m → k) := fun p =>
    ρ ((twistedE6CoverData hf hK σ hσ).nhatW (w p.1))
      (ρ ((twistedE6CoverData hf hK σ hσ).nhatW (u p.2.1)) (Ev p.2.2))
  have hv : ∀ p, v p ∈ twWt hf hK σ hσ ρ (ν p) := by
    intro p
    have h1 := twWt_nhatProd hf K hK σ hσ ρ (twWd (F4Exc.uWord s p.2.1)) (hEw p.2.2 p.2.2.2)
    have h2 := twWt_nhatProd hf K hK σ hσ ρ (twWd (F4Exc.gamWord s p.1))
      (e := twAct f (twWd (F4Exc.uWord s p.2.1)) (fun c => lam c - 2 ^ (p.2.2 : ℕ) *
        twRoot f (twNode s) c)) h1
    simp only [v, w, u, twNhatW_wordProd]
    exact h2
  have hu : ∀ j : Fin 8, ∀ r ∈ TwistTag.E6.orbit (twNode s), ∃ r' ∈ TwistTag.E6.orbit (twNode s),
      ((u j : ↥(relWeylTwist TwistTag.E6)) : WeylGroup TwistTag.E6.tag) •
        (Pi.single r 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single r' 1 := by
    intro j r hr
    obtain ⟨r', hr', h⟩ := twUWords_permute_check s j r hr
    exact ⟨r', hr', by simp only [u]; rw [relCs_wordProd_smul]; exact h⟩
  have hli := twTranslates_linearIndependent hf K hK σ hσ hρ ht hs
  have hcop : ∀ b : {b : ℕ // b ∈ B}, LinearIndependent k (fun j : Fin 8 =>
      ρ ((twistedE6CoverData hf hK σ hσ).nhatW (u j)) (Ev b)) := fun b =>
    twCopies_linearIndependent hf K hK σ hσ hCop hρ ht u hu hli (hEv b b.2).1 (hEv b b.2).2.1
  have hli2 : LinearIndependent k v := by
    refine twLinearIndependent_of_wt hf K hK σ hσ ρ v ν hv (fun c => ?_)
    rcases isEmpty_or_nonempty {p : ι // twCls K σ k (ν p) = c} with hE0 | ⟨⟨p0, hp0⟩⟩
    · exact linearIndependent_empty_type
    · have hkey : ∀ q : {p : ι // twCls K σ k (ν p) = c},
          q.1 = (p0.1, q.1.2.1, p0.2.2) := by
        intro q
        have hdvd : ∀ c' : TwN, ((2 ^ twNdig f c' - 1 : ℕ) : ℤ) ∣ ν q.1 c' - ν p0 c' := fun c' =>
          dvd_of_twCls_eq hf K hK σ hσ (q.2.trans hp0.symm) c'
        obtain ⟨h1, h2⟩ := hsep q.1.1 p0.1 q.1.2.1 p0.2.1 q.1.2.2 p0.2.2 q.1.2.2.2 p0.2.2.2 hdvd
        exact Prod.ext h1 (Prod.ext rfl (Subtype.ext h2))
      have hf_inj : Function.Injective
          (fun q : {p : ι // twCls K σ k (ν p) = c} => q.1.2.1) := by
        intro q q' hqq'
        apply Subtype.ext
        rw [hkey q, hkey q']
        simp only at hqq'
        rw [hqq']
      have hinj : Function.Injective
          (ρ ((twistedE6CoverData hf hK σ hσ).nhatW (w p0.1))) := by
        intro a b hab
        have := congrArg (ρ ((twistedE6CoverData hf hK σ hσ).nhatW (w p0.1))⁻¹) hab
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
          map_one] at this
        simpa using this
      have := ((hcop p0.2.2).map' (ρ ((twistedE6CoverData hf hK σ hσ).nhatW (w p0.1)))
        (LinearMap.ker_eq_bot.2 hinj)).comp
        (fun q : {p : ι // twCls K σ k (ν p) = c} => q.1.2.1) hf_inj
      convert this using 2 with q
      simp only [Function.comp]
      exact congrArg v (hkey q)
  have hcardι : Fintype.card ι = 96 * B.card := by
    simp only [ι, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
    ring
  have h1 := hli2.fintype_card_le_finrank
  rw [hcardι, Module.finrank_fin_fun] at h1
  exact h1

end Infra

section Pieces

variable {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

include hf hK hσ in
theorem twNoJUniv {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k] {m : ℕ}
    {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)} (hρ : IsSimpleRep ρ)
    (hnt : ∃ x, ρ x ≠ 1) {y : Fin m → k} {χ : ↥(TwistedE6.fixedGroup K σ) → k} {J : Finset TwN}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J) : J ≠ Finset.univ := by
  classical
  intro hJ
  obtain ⟨x, hx⟩ := hnt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥(TwistedE6.fixedGroup K σ) := finite_fixedGroup_inst (K := K) σ
  have hχi : ∀ (a : TwN) (u : (orbitField TwistTag.E6 K σ a)ˣ), χ (hatH hf hK σ hσ a u) = 1 :=
    fun a u => ((ht.2.2.2 a).1 (hJ ▸ Finset.mem_univ a)).1 u
  set ρ0 : Representation k ↥(TwistedE6.fixedGroup K σ) (Unit →₀ k) :=
    Representation.trivial k _ (Unit →₀ k) with hρ0def
  have hρ0 : IsSimpleRep ρ0 := by
    refine ⟨⟨⟨0, Finsupp.single () 1, fun h => by simpa using congrArg (fun f => f ()) h⟩⟩,
      fun W _ => ?_⟩
    by_cases hW : W = ⊥
    · exact Or.inl hW
    right
    obtain ⟨f0, hfW, hf0⟩ := (Submodule.ne_bot_iff W).1 hW
    have hf0' : f0 = f0 () • Finsupp.single () 1 := Finsupp.ext fun u => by cases u; simp
    have hc : f0 () ≠ 0 := fun h => hf0 (by rw [hf0', h, zero_smul])
    generalize f0 () = c at hf0' hc
    have hs : Finsupp.single () (1 : k) ∈ W := by
      have := W.smul_mem c⁻¹ hfW
      rwa [hf0', smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    refine eq_top_iff.2 fun g _ => ?_
    have : g = g () • Finsupp.single () 1 := Finsupp.ext fun u => by cases u; simp
    rw [this]
    exact Submodule.smul_mem _ _ hs
  have hev : ∀ a : TwN, ((Nat.card (orbitField TwistTag.E6 K σ a) : ℕ) : k) = 0 := by
    intro a
    rw [twCard_orbitField hf K hK σ hσ a]
    obtain ⟨n, hn⟩ : ∃ n, twNdig f a = n + 1 := ⟨twNdig f a - 1, by have := twNdig_pos hf a; omega⟩
    rw [hn, pow_succ]; push_cast; rw [CharTwo.two_eq_zero, mul_zero]
  have ht0 : ∀ χ' : ↥(TwistedE6.fixedGroup K σ) → k,
      (∀ h ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ), χ' h = 1) →
      (∀ (a : TwN) (u : (orbitField TwistTag.E6 K σ a)ˣ), χ' (hatH hf hK σ hσ a u) = 1) →
      IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ0 (Finsupp.single () (1 : k)) χ' J := by
    intro χ' hχ'1 hχ'i
    refine ⟨fun u _ => by simp [hρ0def], fun h => by simpa using congrArg (fun f => f ()) h,
      fun h hh => by simp [hρ0def, hχ'1 h hh], fun a => ?_⟩
    refine ⟨fun _ => ⟨hχ'i a, ?_⟩, fun _ => hJ ▸ Finset.mem_univ a⟩
    haveI : ∀ s, Fintype (orbitField TwistTag.E6 K σ s) := fun s => Fintype.ofFinite _
    refine ((twistedE6CoverRankOne hf hK σ hσ).heckeT_datum ρ0 a _).trans ?_
    simp only [hρ0def, Representation.trivial_apply, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul k, hev a, zero_smul]
  have ht1 := ht0 (fun _ => 1) (fun _ _ => rfl) (fun _ _ => rfl)
  have h0J : twN0 ∈ J := hJ ▸ Finset.mem_univ _
  have h1J : twN1 ∈ J := hJ ▸ Finset.mem_univ _
  have hχ1 : ∀ h ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ), χ h = 1 := fun h hh => by
    have := chi_eq_on_Hcover hf hK σ hσ ht ht1 h0J h1J h0J h1J (fun a u => by rw [hχi a u]) h hh
    simpa using this
  obtain ⟨β, hβ⟩ := twisted_iso_of_isCoverType hf hK σ hσ hρ hρ0 ht (ht0 χ hχ1 hχi)
  apply hx
  refine LinearMap.ext fun v => β.injective ?_
  rw [hβ]
  simp [hρ0def]

include hf hK hσ in
theorem twString_nonempty {k : Type} [Field k] [CharP k 2] [Algebra K k] {V : Type} [AddCommGroup V]
    [Module k V] {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V} {y : V}
    {χ : ↥(TwistedE6.fixedGroup K σ) → k} {J : Finset TwN}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J) {s : TwN} (hs : s ∉ J)
    {J' : Finset ℕ}
    (hχ : ∀ z : (orbitField TwistTag.E6 K σ s)ˣ, χ (hatH hf hK σ hσ s z) =
      (algebraMap K k ((z : orbitField TwistTag.E6 K σ s) : K)) ^ (∑ i ∈ J', 2 ^ i))
    (hJ0 : J' = ∅ → ∀ g, ρ (Rhat hf hK σ hσ s g) y = y) : J'.Nonempty := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases J'.eq_empty_or_nonempty with h0 | h0
  · exfalso
    apply hs
    have hfix := hJ0 h0
    refine (ht.2.2.2 s).2 ⟨fun z => ?_, ?_⟩
    · show χ (hatH hf hK σ hσ s z) = 1
      rw [hχ z, h0]; simp
    · haveI : ∀ s, Fintype (orbitField TwistTag.E6 K σ s) := fun s => Fintype.ofFinite _
      refine ((twistedE6CoverRankOne hf hK σ hσ).heckeT_datum ρ s y).trans ?_
      have hn' : ∀ c : orbitField TwistTag.E6 K σ s,
          ρ ((twistedE6CoverRankOne hf hK σ hσ).x s c *
            (twistedE6CoverData hf hK σ hσ).nhat s) y = y := by
        intro c
        have e : (twistedE6CoverRankOne hf hK σ hσ).x s c *
            (twistedE6CoverData hf hK σ hσ).nhat s = Rhat hf hK σ hσ s (uSL c * WSL) := by
          refine Subtype.ext ?_
          show minOrbitHom σ s (uSL c) *
              (((twistedE6CoverData hf hK σ hσ).nhat s : ↥(TwistedE6.fixedGroup K σ)) :
                ↥(e6Data_valid.minGroup K)) = minOrbitHom σ s (uSL c * WSL)
          rw [nhat_coe hf hK σ hσ s, map_mul]
        rw [e]
        exact hfix _
      simp only [hn']
      rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
        twCard_orbitField hf K hK σ hσ s]
      obtain ⟨n, hn⟩ : ∃ n, twNdig f s = n + 1 := ⟨twNdig f s - 1, by
        have := twNdig_pos hf s; omega⟩
      rw [hn, pow_succ, ← Nat.cast_smul_eq_nsmul k]
      push_cast
      rw [CharTwo.two_eq_zero, mul_zero, zero_smul]
  · exact h0

include hf hK hσ in
theorem twPeriodic_dvd {k : Type} [Field k] [CharP k 2] [Algebra K k]
    {χ : ↥(TwistedE6.fixedGroup K σ) → k} (a : TwN) {J' : Finset ℕ} {g : ℕ}
    (hχ : ∀ z : (orbitField TwistTag.E6 K σ a)ˣ, χ (hatH hf hK σ hσ a z) =
      (algebraMap K k ((z : orbitField TwistTag.E6 K σ a) : K)) ^ (∑ i ∈ J', 2 ^ i))
    (hper : ∀ z : (orbitField TwistTag.E6 K σ a)ˣ,
      χ (hatH hf hK σ hσ a z) ^ (2 ^ g) = χ (hatH hf hK σ hσ a z)) :
    (2 ^ twNdig f a - 1) ∣ (2 ^ g - 1) * ∑ i ∈ J', 2 ^ i := by
  classical
  letI : Algebra (orbitField TwistTag.E6 K σ a) k :=
    ((algebraMap K k).comp (orbitField TwistTag.E6 K σ a).subtype).toAlgebra
  set b := ∑ i ∈ J', 2 ^ i with hb
  have h1 : ∀ z : (orbitField TwistTag.E6 K σ a)ˣ,
      (algebraMap K k ((z : orbitField TwistTag.E6 K σ a) : K)) ^ (b * 2 ^ g) =
        (algebraMap K k ((z : orbitField TwistTag.E6 K σ a) : K)) ^ b := by
    intro z
    have := hper z
    rw [hχ z, ← pow_mul] at this
    exact this
  have hle : b ≤ b * 2 ^ g := Nat.le_mul_of_pos_right _ (by positivity)
  have h2 := CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.dvd_of_forall_pow_eq (K := orbitField TwistTag.E6 K σ a) (k := k)
    (twCard_orbitField hf K hK σ hσ a) hle (fun z => (h1 z).symm)
  have : b * 2 ^ g - b = (2 ^ g - 1) * b := by
    rw [Nat.sub_one_mul, mul_comm]
  rwa [this] at h2

@[expose] def Tw78Dim {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) : Prop :=
  ∀ (k : Type) [Field k] [Finite k] [CharP k 2] [Algebra K k] (m : ℕ)
    (ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)) (y : Fin m → k)
    (χ : ↥(TwistedE6.fixedGroup K σ) → k) (J : Finset TwN),
    IsSimpleRep ρ → IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J →
    Tw78Type hf K hK σ hσ k χ J → m = 78

theorem twPow_not_dvd {f g b : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) (hgf : g ≤ f) :
    ¬ (2 ^ (2 * f) - 1) ∣ (2 ^ g - 1) * 2 ^ b := by
  intro h
  have hcop : Nat.Coprime (2 ^ (2 * f) - 1) (2 ^ b) := by
    refine Nat.Coprime.pow_right _ ?_
    rw [Nat.coprime_two_right]
    obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    refine ⟨2 ^ (2 * m + 1) - 1, ?_⟩
    have := Nat.one_le_two_pow (n := 2 * m + 1)
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ]
    omega
  have h1 := hcop.dvd_of_dvd_mul_right h
  have h2 : 0 < 2 ^ g - 1 := by
    have : 2 ^ 1 ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
    omega
  have h3 := Nat.le_of_dvd h2 h1
  have h4 : 2 ^ g < 2 ^ (2 * f) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h5 : 1 ≤ 2 ^ g := Nat.one_le_two_pow
  omega

theorem twF2_card3_not_dvd : ∀ J' ∈ (Finset.range 4).powerset, J'.card = 3 →
    ¬ (15 ∣ 3 * ∑ i ∈ J', 2 ^ i) := by
  decide


include hf hK hσ in
theorem twBoundLarge (hStr : TwStringOfHighest hf K hK σ hσ) (hWS : TwWeightShift hf K hK σ hσ)
    (hCop : TwCopiesNormalize hf K hK σ hσ) (hPA : TwPeriodArith) (hSep : TwSepM0)
    {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k] {m : ℕ}
    {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)} (hρ : IsSimpleRep ρ)
    {y : Fin m → k} {χ : ↥(TwistedE6.fixedGroup K σ) → k} {J : Finset TwN}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J) (hJ : J ≠ Finset.univ)
    {g : ℕ} (hg : 1 ≤ g) (hgf : g ∣ 2 * f)
    (hper : ∀ (a : TwN) (w : (orbitField TwistTag.E6 K σ a)ˣ),
      χ (hatH hf hK σ hσ a w) ^ (2 ^ g) = χ (hatH hf hK σ hσ a w))
    (ht3 : 3 ≤ 2 * f / g) : 39 * (2 * f / g) + 1 ≤ m := by
  classical
  obtain ⟨s0, hs0⟩ : ∃ a : TwN, a ∉ J := by
    by_contra h
    push Not at h
    exact hJ (Finset.eq_univ_of_forall h)
  have hstr := fun a : TwN => hStr k ρ y χ J a hρ ht
  choose Jp hJpn hχ hdim hJ0 hwt using hstr
  have hne : (Jp s0).Nonempty := twString_nonempty hf K hK σ hσ ht hs0 (hχ s0) (hJ0 s0)
  have hperJ : ∀ c : TwN, (2 ^ twNdig f c - 1) ∣ (2 ^ g - 1) * ∑ i ∈ Jp c, 2 ^ i :=
    fun c => twPeriodic_dvd hf K hK σ hσ c (hχ c) (hper c)
  obtain ⟨⟨h3, hodd, hdvd, hord⟩, hdivA, hdigits⟩ := hPA f g hf hg hgf ht3
  set lam : TwN → ℤ := fun c => ((∑ i ∈ Jp c, 2 ^ i : ℕ) : ℤ) with hlam
  have hlam0 : ∀ c, ((twM0 f g : ℕ) : ℤ) ∣ lam c :=
    fun c => Int.natCast_dvd_natCast.2 (hdivA _ _ (twNdig_cases f c) (hperJ c))
  obtain ⟨D, hDsub, hDcard, hDres⟩ := hdigits (twNdig f s0) (Jp s0) (twNdig_cases f s0)
    (hJpn s0) hne (hperJ s0)
  have h4 : s0.val < 4 := s0.2
  obtain ⟨s, hs⟩ : ∃ s : Fin Tag.F4.rank, twNode s = s0 :=
    ⟨⟨3 - s0.val, by show 3 - s0.val < 4; omega⟩, Fin.ext (by simp only [twNode]; omega)⟩
  subst hs
  have hy : y ∈ twWt hf hK σ hσ ρ lam := by
    intro a w
    have h1 : ρ (hatH hf hK σ hσ a w) y = χ (hatH hf hK σ hσ a w) • y :=
      ht.2.2.1 _ ((twistedE6CoverRankOne hf hK σ hσ).hh_mem a w)
    rw [h1, hχ a w, hlam]
    simp only [zpow_natCast]
  have key := twDimGeOfSep hf K hK σ hσ hWS hCop hρ ht hs0 lam hy D
    (fun b hb => hwt (twNode s) b (hDsub hb)) (fun i i' j j' b b' hb hb' hdiv => by
      have hdiv' : ∀ c : TwN, ((twM0 f g : ℕ) : ℤ) ∣
          twV f s lam b i j c - twV f s lam b' i' j' c := fun c =>
        dvd_trans (Int.natCast_dvd_natCast.2 (hdvd.trans (twPow_dvd f c))) (hdiv c)
      obtain ⟨hii, hbb⟩ := hSep f g hf hg hgf ht3 s lam hlam0 b b' i i' j j' hdiv'
      refine ⟨hii, ?_⟩
      by_contra hne'
      exact hDres b hb b' hb' hne' hbb)
  calc 39 * (2 * f / g) + 1 ≤ 96 * ((2 * f / g + 1) / 2) := by omega
    _ ≤ 96 * D.card := Nat.mul_le_mul_left _ hDcard
    _ ≤ m := key


structure TwEndData {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k] {m : ℕ}
    (ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)) (y : Fin m → k)
    (χ : ↥(TwistedE6.fixedGroup K σ) → k) (J : Finset TwN) (s : Fin Tag.F4.rank)
    (J' : Finset ℕ) : Prop where
  hs : s.val = 0 ∨ s.val = 3
  hJ : J = Finset.univ.erase (twNode s)
  nonempty : J'.Nonempty
  digits : ∀ i ∈ J', i < twNdig f (twNode s)
  chi_s : ∀ z : (orbitField TwistTag.E6 K σ (twNode s))ˣ, χ (hatH hf hK σ hσ (twNode s) z) =
    (algebraMap K k ((z : orbitField TwistTag.E6 K σ (twNode s)) : K)) ^ (∑ i ∈ J', 2 ^ i)
  chi_other : ∀ c : TwN, c ≠ twNode s → ∀ z : (orbitField TwistTag.E6 K σ c)ˣ,
    χ (hatH hf hK σ hσ c z) = 1
  string : ∀ b ∈ J', ∃ e ∈ orbitSpan (ρ.comp (Rhat hf hK σ hσ (twNode s))) y, e ≠ 0 ∧
    ∀ z : (orbitField TwistTag.E6 K σ (twNode s))ˣ, ρ (hatH hf hK σ hσ (twNode s) z) e =
      (algebraMap K k ((z : orbitField TwistTag.E6 K σ (twNode s)) : K)) ^
        (((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) - 2 ^ (b + 1)) • e
  dim : Module.finrank k (orbitSpan (ρ.comp (Rhat hf hK σ hσ (twNode s))) y) = 2 ^ J'.card

include hf hK hσ in
theorem twEndData (hStr : TwStringOfHighest hf K hK σ hσ)
    {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k] {m : ℕ}
    {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)} (hρ : IsSimpleRep ρ)
    {y : Fin m → k} {χ : ↥(TwistedE6.fixedGroup K σ) → k} {J : Finset TwN}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J) {s : Fin Tag.F4.rank}
    (hs : s.val = 0 ∨ s.val = 3) (hJ : J = Finset.univ.erase (twNode s)) :
    ∃ J' : Finset ℕ, TwEndData hf K hK σ hσ ρ y χ J s J' := by
  obtain ⟨J', hJ'n, hχ, hdim, hJ0, hwt⟩ := hStr k ρ y χ J (twNode s) hρ ht
  have hsJ : twNode s ∉ J := by rw [hJ]; simp
  exact ⟨J', hs, hJ, twString_nonempty hf K hK σ hσ ht hsJ hχ hJ0, hJ'n, hχ,
    fun c hc z => ((ht.2.2.2 c).1 (by rw [hJ]; simp [hc])).1 z, hwt, hdim⟩

variable {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k] {m : ℕ}
  {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)}
  {y : Fin m → k} {χ : ↥(TwistedE6.fixedGroup K σ) → k} {J : Finset TwN}
  {s : Fin Tag.F4.rank} {J' : Finset ℕ}

include hf hK hσ in
theorem TwEndData.weight (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    (D : TwEndData hf K hK σ hσ ρ y χ J s J') :
    y ∈ twWt hf hK σ hσ ρ
      (fun c => if c = twNode s then ((∑ b ∈ J', 2 ^ b : ℕ) : ℤ) else 0) := by
  intro a w
  have h1 : ρ (hatH hf hK σ hσ a w) y = χ (hatH hf hK σ hσ a w) • y :=
    ht.2.2.1 _ ((twistedE6CoverRankOne hf hK σ hσ).hh_mem a w)
  rw [h1]
  by_cases ha : a = twNode s
  · subst ha
    simp only [if_true]
    rw [D.chi_s w, zpow_natCast]
  · simp only [ha, if_false, zpow_zero, one_smul]
    rw [D.chi_other a ha w, one_smul]

include hf hK hσ in
theorem twEnd_ge96_of_digit (hWS : TwWeightShift hf K hK σ hσ) (hCop : TwCopiesNormalize hf K hK σ hσ)
    (hρ : IsSimpleRep ρ)
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    (D : TwEndData hf K hK σ hσ ρ y χ J s J') {dg : ℕ} (hdg : dg ∈ J')
    (hsepdg : ∀ (i i' : Fin 12), i ≠ i' → ∀ (j j' : Fin 8), ¬ ∀ c : TwN,
      ((2 ^ twNdig f c - 1 : ℕ) : ℤ) ∣
        twV f s (fun c => if c = twNode s then ((∑ b ∈ J', 2 ^ b : ℕ) : ℤ) else 0) dg i j c -
          twV f s (fun c => if c = twNode s then ((∑ b ∈ J', 2 ^ b : ℕ) : ℤ) else 0) dg i' j' c) :
    96 ≤ m := by
  have hsJ : twNode s ∉ J := by rw [D.hJ]; simp
  have key := twDimGeOfSep hf K hK σ hσ hWS hCop hρ ht hsJ _ (D.weight hf K hK σ hσ ht) {dg}
    (fun b hb => by
      rw [Finset.mem_singleton] at hb
      subst hb
      obtain ⟨e, he, he0, hes⟩ := D.string b hdg
      exact ⟨e, he, he0, fun z => by rw [hes z]; simp⟩)
    (fun i i' j j' b b' hb hb' hdiv => by
      rw [Finset.mem_singleton] at hb hb'
      subst hb hb'
      refine ⟨?_, rfl⟩
      by_contra hii
      exact hsepdg i i' hii j j' hdiv)
  simpa using key

include hf hK hσ in
theorem twEnd_ge96 (hWS : TwWeightShift hf K hK σ hσ) (hCop : TwCopiesNormalize hf K hK σ hσ) (hExists : TwExistsDigit)
    (hρ : IsSimpleRep ρ) (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    (D : TwEndData hf K hK σ hσ ρ y χ J s J') (hf3 : 3 ≤ f) (hc : 2 ≤ J'.card) : 96 ≤ m := by
  obtain ⟨dg, hdg, hsepdg⟩ := hExists f s hf3 D.hs J'
    (fun i hi => by have := D.digits i hi; rcases twNdig_cases f (twNode s) with h | h <;> omega) hc
  exact twEnd_ge96_of_digit hf K hK σ hσ hWS hCop hρ ht D hdg fun i i' hii j j' hdiv =>
    hsepdg i i' hii j j' fun c => dvd_trans (Int.natCast_dvd_natCast.2 (twPow_dvd f c)) (hdiv c)

include hf hK hσ in
theorem twEnd_f2_card2 (hWS : TwWeightShift hf K hK σ hσ) (hCop : TwCopiesNormalize hf K hK σ hσ) (hF2 : TwExistsDigitF2)
    (hρ : IsSimpleRep ρ) (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    (D : TwEndData hf K hK σ hσ ρ y χ J s J') (hf2 : f = 2) (hc : J'.card = 2) : 96 ≤ m := by
  subst hf2
  obtain ⟨dg, hdg, hsepdg⟩ := hF2 s D.hs J' D.digits hc
  exact twEnd_ge96_of_digit hf K hK σ hσ hWS hCop hρ ht D hdg hsepdg

include hf hK hσ in
theorem twEnd_copies (hCop : TwCopiesNormalize hf K hK σ hσ) (hρ : IsSimpleRep ρ) (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    (D : TwEndData hf K hK σ hσ ρ y χ J s J') : 8 * 2 ^ J'.card ≤ m := by
  have hsJ : twNode s ∉ J := by rw [D.hJ]; simp
  have hu : ∀ j : Fin 8, ∀ r ∈ TwistTag.E6.orbit (twNode s), ∃ r' ∈ TwistTag.E6.orbit (twNode s),
      (((relCs TwistTag.E6).wordProd (twWd (F4Exc.uWord s j)) : ↥(relWeylTwist TwistTag.E6)) :
        WeylGroup TwistTag.E6.tag) • (Pi.single r 1 : Fin TwistTag.E6.tag.rank → ℤ) =
          Pi.single r' 1 := by
    intro j r hr
    obtain ⟨r', hr', h⟩ := twUWords_permute_check s j r hr
    exact ⟨r', hr', by rw [relCs_wordProd_smul]; exact h⟩
  have := twCopies_finrank hf K hK σ hσ hCop hρ ht (s := twNode s) (m' := 8)
    (fun j => (relCs TwistTag.E6).wordProd (twWd (F4Exc.uWord s j))) hu
    (twTranslates_linearIndependent hf K hK σ hσ hρ ht hsJ)
  rwa [D.dim] at this

include hf hK hσ in
theorem twEnd_f1 (hF1 : TwF1Residual hf K hK σ hσ) (hρ : IsSimpleRep ρ) (hnt : ∃ x, ρ x ≠ 1)
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    (D : TwEndData hf K hK σ hσ ρ y χ J s J') (hf1 : f = 1) (hc : 2 ≤ J'.card) : 79 ≤ m := by
  subst hf1
  have hs3 : s.val = 3 := by
    rcases D.hs with h0 | h3
    · exfalso
      have hn : twNdig 1 (twNode s) = 1 := by simp [twNdig, twNode, h0]
      have hsub : J' ⊆ Finset.range 1 := fun i hi => Finset.mem_range.2 (hn ▸ D.digits i hi)
      have := Finset.card_le_card hsub
      simp at this
      omega
    · exact h3
  have hn : twNdig 1 (twNode s) = 2 := by simp [twNdig, twNode, hs3]
  have hJ' : J' = Finset.range 2 := by
    apply Finset.eq_of_subset_of_card_le (fun i hi => Finset.mem_range.2 (hn ▸ D.digits i hi))
    simp
    omega
  have hsum : ∑ i ∈ J', 2 ^ i = 3 := by rw [hJ']; decide
  have htriv : ∀ (a : TwN) (w : (orbitField TwistTag.E6 K σ a)ˣ), χ (hatH hf hK σ hσ a w) = 1 := by
    intro a w
    by_cases ha : a = twNode s
    · subst ha
      rw [D.chi_s w, hsum]
      have hcard : Nat.card (orbitField TwistTag.E6 K σ (twNode s))ˣ = 3 := by
        rw [Nat.card_units, twCard_orbitField hf K hK σ hσ, hn]
        norm_num
      have h3 : w ^ 3 = 1 := by rw [← hcard]; exact pow_card_eq_one'
      have := congrArg (fun u : (orbitField TwistTag.E6 K σ (twNode s))ˣ =>
        algebraMap K k ((u : orbitField TwistTag.E6 K σ (twNode s)) : K)) h3
      simpa using this
    · exact D.chi_other a ha w
  have hN : twNode s = twN0 := Fin.ext (by simp only [twNode, twN0]; omega)
  have hJ0 : J = Finset.univ.erase twN0 := by rw [D.hJ, hN]
  exact hF1 rfl k m ρ y χ J hρ hnt ht hJ0 htriv

include hf hK hσ in
theorem twEnd_f2 (hWS : TwWeightShift hf K hK σ hσ) (hCop : TwCopiesNormalize hf K hK σ hσ) (hF2 : TwExistsDigitF2) (hρ : IsSimpleRep ρ)
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    (D : TwEndData hf K hK σ hσ ρ y χ J s J') (hf2 : f = 2) (hc : 2 ≤ J'.card)
    {g : ℕ} (hg : 1 ≤ g) (hgf : g ∣ 2 * f)
    (hper : ∀ (a : TwN) (w : (orbitField TwistTag.E6 K σ a)ˣ),
      χ (hatH hf hK σ hσ a w) ^ (2 ^ g) = χ (hatH hf hK σ hσ a w))
    (ht12 : 2 * f / g = 1 ∨ 2 * f / g = 2) : 79 ≤ m ∨ (2 * f / g = 1 ∧ 40 ≤ m) := by
  have h8 := twEnd_copies hf K hK σ hσ hCop hρ ht D
  rcases Nat.lt_or_ge J'.card 3 with hlt | hge
  · left
    have := twEnd_f2_card2 hf K hK σ hσ hWS hCop hF2 hρ ht D hf2 (by omega)
    omega
  rcases Nat.lt_or_ge J'.card 4 with hlt4 | hge4
  · have hc3 : J'.card = 3 := by omega
    have h64 : 64 ≤ m := by rw [hc3] at h8; omega
    rcases ht12 with h1 | h2
    · exact Or.inr ⟨h1, by omega⟩
    · exfalso
      subst hf2
      have hg4 : g ≤ 4 := Nat.le_of_dvd (by norm_num) hgf
      have hg2 : g = 2 := by interval_cases g <;> simp_all
      subst hg2
      have hdvd := twPeriodic_dvd hf K hK σ hσ (twNode s) D.chi_s (hper (twNode s))
      have hn : twNdig 2 (twNode s) = 4 := by
        rcases twNdig_cases 2 (twNode s) with h | h
        · exfalso
          have hsub : J' ⊆ Finset.range 2 := fun i hi =>
            Finset.mem_range.2 (by have := D.digits i hi; omega)
          have := Finset.card_le_card hsub
          simp at this
          omega
        · omega
      have hmem : J' ∈ (Finset.range 4).powerset := Finset.mem_powerset.2 fun i hi =>
        Finset.mem_range.2 (by have := D.digits i hi; omega)
      rw [hn] at hdvd
      exact twF2_card3_not_dvd J' hmem hc3 (by simpa using hdvd)
  · left
    have : 8 * 2 ^ 4 ≤ 8 * 2 ^ J'.card :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hge4)
    omega

include hf hK hσ in
theorem twEndNode (hStr : TwStringOfHighest hf K hK σ hσ) (hWS : TwWeightShift hf K hK σ hσ)
    (hCop : TwCopiesNormalize hf K hK σ hσ) (h78d : Tw78Dim hf K hK σ hσ)
    (hExists : TwExistsDigit) (hF1 : TwF1Residual hf K hK σ hσ) (hF2 : TwExistsDigitF2)
    (hρ : IsSimpleRep ρ) (hnt : ∃ x, ρ x ≠ 1)
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    (hs : s.val = 0 ∨ s.val = 3) (hJ : J = Finset.univ.erase (twNode s))
    {g : ℕ} (hg : 1 ≤ g) (hgf : g ∣ 2 * f)
    (hper : ∀ (a : TwN) (w : (orbitField TwistTag.E6 K σ a)ˣ),
      χ (hatH hf hK σ hσ a w) ^ (2 ^ g) = χ (hatH hf hK σ hσ a w))
    (ht12 : 2 * f / g = 1 ∨ 2 * f / g = 2) :
    (2 * f / g = 1 → 40 ≤ m ∨ Tw27Type hf K hK σ hσ k χ J) ∧
    (2 * f / g = 2 → 78 ≤ m ∧ (79 ≤ m ∨ Tw78Type hf K hK σ hσ k χ J)) := by
  obtain ⟨J', D⟩ := twEndData hf K hK σ hσ hStr hρ ht hs hJ
  by_cases hc1 : J'.card = 1
  · obtain ⟨b, hb⟩ := Finset.card_eq_one.1 hc1
    have hbn : b < twNdig f (twNode s) := D.digits b (by rw [hb]; simp)
    have hχb : ∀ z : (orbitField TwistTag.E6 K σ (twNode s))ˣ,
        χ (hatH hf hK σ hσ (twNode s) z) =
          (algebraMap K k ((z : orbitField TwistTag.E6 K σ (twNode s)) : K)) ^ (2 ^ b) := by
      intro z
      rw [D.chi_s z, hb, Finset.sum_singleton]
    rcases hs with hs0 | hs3
    ·
      have hN : twNode s = twN3 := Fin.ext (by simp only [twNode, twN3]; omega)
      have hn : twNdig f (twNode s) = f := by simp [twNdig, twNode, hs0]
      rw [hN] at hχb
      have h78 : Tw78Type hf K hK σ hσ k χ J :=
        ⟨by rw [hJ, hN], b, by rw [hn] at hbn; exact hbn, hχb⟩
      have hm78 := h78d k m ρ y χ J hρ ht h78
      exact ⟨fun _ => Or.inl (by omega), fun _ => ⟨by omega, Or.inr h78⟩⟩
    ·
      have hN : twNode s = twN0 := Fin.ext (by simp only [twNode, twN0]; omega)
      have hn : twNdig f (twNode s) = 2 * f := by simp [twNdig, twNode, hs3]
      have hdvd := twPeriodic_dvd hf K hK σ hσ (twNode s) D.chi_s (hper (twNode s))
      rw [hn, hb, Finset.sum_singleton] at hdvd
      rw [hN] at hχb
      have h27 : Tw27Type hf K hK σ hσ k χ J :=
        ⟨by rw [hJ, hN], b, by rw [hN] at hbn; simpa [twNdig, twN0] using hbn, hχb⟩
      refine ⟨fun _ => Or.inr h27, fun h2 => ?_⟩
      exfalso
      have hgf' : g ≤ f := by
        have := (Nat.le_div_iff_mul_le (by omega : 0 < g)).1 (by omega : 2 ≤ 2 * f / g)
        omega
      exact twPow_not_dvd hf hg hgf' hdvd
  · have hc : 2 ≤ J'.card := by have := D.nonempty.card_pos; omega
    have key : 79 ≤ m ∨ (2 * f / g = 1 ∧ 40 ≤ m) := by
      rcases Nat.lt_or_ge f 3 with hf3 | hf3
      · rcases (by omega : f = 1 ∨ f = 2) with hf1 | hf2
        · exact Or.inl (twEnd_f1 hf K hK σ hσ hF1 hρ hnt ht D hf1 hc)
        · exact twEnd_f2 hf K hK σ hσ hWS hCop hF2 hρ ht D hf2 hc hg hgf hper ht12
      · exact Or.inl (by have := twEnd_ge96 hf K hK σ hσ hWS hCop hExists hρ ht D hf3 hc; omega)
    refine ⟨fun h1 => ?_, fun h2 => ?_⟩
    · rcases key with h | ⟨-, h⟩
      · exact Or.inl (by omega)
      · exact Or.inl h
    · rcases key with h | ⟨h1, -⟩
      · exact ⟨by omega, Or.inl h⟩
      · omega

include hf hK hσ in
theorem twTypeBoundStmt_of_inputs (hTrans : TwTransBound hf K hK σ hσ)
    (hStr : TwStringOfHighest hf K hK σ hσ) (hWS : TwWeightShift hf K hK σ hσ)
    (hCop : TwCopiesNormalize hf K hK σ hσ) (h78d : Tw78Dim hf K hK σ hσ)
    (hPA : TwPeriodArith) (hExists : TwExistsDigit) (hSep : TwSepM0)
    (hF1 : TwF1Residual hf K hK σ hσ) (hF2 : TwExistsDigitF2) :
    TwTypeBoundStmt hf K hK σ hσ := by
  intro k _ _ _ _ m ρ y χ J g hρ hnt ht hg hgf hper
  have hJne : J ≠ Finset.univ := twNoJUniv hf K hK σ hσ hρ hnt ht
  have hsmall : (2 * f / g = 1 ∨ 2 * f / g = 2) →
      (2 * f / g = 1 → 40 ≤ m ∨ Tw27Type hf K hK σ hσ k χ J) ∧
      (2 * f / g = 2 → 78 ≤ m ∧ (79 ≤ m ∨ Tw78Type hf K hK σ hσ k χ J)) := by
    intro ht12
    by_cases h2 : ∃ a b : TwN, a ≠ b ∧ a ∉ J ∧ b ∉ J
    · have := (hTrans k m ρ y χ J hρ ht).2 h2
      exact ⟨fun _ => Or.inl (by omega), fun _ => ⟨by omega, Or.inl (by omega)⟩⟩
    by_cases h1 : ∃ a : TwN, a ∉ J ∧ (a.val = 1 ∨ a.val = 2)
    · have := (hTrans k m ρ y χ J hρ ht).1 h1
      exact ⟨fun _ => Or.inl (by omega), fun _ => ⟨by omega, Or.inl (by omega)⟩⟩
    obtain ⟨a, ha⟩ : ∃ a : TwN, a ∉ J := by
      by_contra h
      push Not at h
      exact hJne (Finset.eq_univ_of_forall h)
    have hJa : J = Finset.univ.erase a := by
      ext c
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · intro hc hca
        exact ha (hca ▸ hc)
      · intro hca
        by_contra hcJ
        exact h2 ⟨c, a, hca, hcJ, ha⟩
    have ha4 : a.val < 4 := a.2
    have ha03 : a.val = 0 ∨ a.val = 3 := by
      by_contra hh
      push Not at hh
      exact h1 ⟨a, ha, by omega⟩
    obtain ⟨s, hs⟩ : ∃ s : Fin Tag.F4.rank, twNode s = a :=
      ⟨⟨3 - a.val, by show 3 - a.val < 4; omega⟩, Fin.ext (by simp only [twNode]; omega)⟩
    have hs03 : s.val = 0 ∨ s.val = 3 := by
      have hs4 : s.val < 4 := s.2
      have : (twNode s).val = a.val := by rw [hs]
      simp only [twNode] at this
      omega
    exact twEndNode hf K hK σ hσ hStr hWS hCop h78d hExists hF1 hF2 hρ hnt ht hs03 (by rw [hs]; exact hJa)
      hg hgf hper ht12
  refine ⟨fun h1 => (hsmall (Or.inl h1)).1 h1, fun h2 => (hsmall (Or.inr h2)).2 h2, fun h3 => ?_⟩
  exact twBoundLarge hf K hK σ hσ hStr hWS hCop hPA hSep hρ ht hJne hg hgf hper h3

include hf hK hσ in
theorem twTypeBoundStmt_holds (hF1 : TwF1Residual hf K hK σ hσ) (hF2 : TwExistsDigitF2)
    (h78d : Tw78Dim hf K hK σ hσ) : TwTypeBoundStmt hf K hK σ hσ :=
  twTypeBoundStmt_of_inputs hf K hK σ hσ (twTransBound_holds hf K hK σ hσ)
    (twStringOfHighest_holds hf K hK σ hσ) (twWeightShift_holds hf K hK σ hσ)
    (twCopiesNormalize_holds hf K hK σ hσ) h78d twPeriodArith_holds
    twExistsDigit_holds twSepM0_holds hF1 hF2

end Pieces


end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

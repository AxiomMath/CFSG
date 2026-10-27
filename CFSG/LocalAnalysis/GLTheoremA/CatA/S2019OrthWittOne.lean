module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
import CFSG.LocalAnalysis.SolvableSignalizer.CoprimeAction
import CFSG.HardMathSupport.Solomon.Coordinator.Generation228

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

section Avg

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private noncomputable def avgEnd (S : Subgroup (V ≃ₗ[K] V)) [Fintype S] : V →ₗ[K] V :=
  (Fintype.card S : K)⁻¹ • ∑ s : S, ((s : V ≃ₗ[K] V) : V →ₗ[K] V)

private theorem avgEnd_apply (S : Subgroup (V ≃ₗ[K] V)) [Fintype S] (v : V) :
    avgEnd S v = (Fintype.card S : K)⁻¹ • ∑ s : S, (s : V ≃ₗ[K] V) v := by
  simp only [avgEnd, LinearMap.smul_apply, LinearMap.sum_apply, LinearEquiv.coe_coe]

variable {S : Subgroup (V ≃ₗ[K] V)} [Fintype S]

private theorem apply_avgEnd {a : V ≃ₗ[K] V} (ha : a ∈ S) (v : V) :
    a (avgEnd S v) = avgEnd S v := by
  rw [avgEnd_apply, LinearEquiv.map_smul, map_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft (⟨a, ha⟩ : S)) _ _ fun b => rfl

private theorem avgEnd_apply_apply {a : V ≃ₗ[K] V} (ha : a ∈ S) (v : V) :
    avgEnd S (a v) = avgEnd S v := by
  rw [avgEnd_apply, avgEnd_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight (⟨a, ha⟩ : S)) _ _ fun b => rfl

private theorem avgEnd_of_fixed (hS : (Fintype.card S : K) ≠ 0) {v : V}
    (hv : ∀ a ∈ S, a v = v) : avgEnd S v = v := by
  rw [avgEnd_apply, Finset.sum_congr rfl fun (a : S) _ => hv a a.2, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hS, one_smul]

private theorem avgEnd_avgEnd (hS : (Fintype.card S : K) ≠ 0) (v : V) :
    avgEnd S (avgEnd S v) = avgEnd S v :=
  avgEnd_of_fixed hS fun _ ha => apply_avgEnd ha v

private theorem apply_inv_apply'' (g : V ≃ₗ[K] V) (w : V) : g (g⁻¹ w) = w := by
  rw [← LinearEquiv.mul_apply, mul_inv_cancel]
  rfl

private theorem inv_apply_apply'' (g : V ≃ₗ[K] V) (w : V) : g⁻¹ (g w) = w := by
  rw [← LinearEquiv.mul_apply, inv_mul_cancel]
  rfl

private theorem commute_avgEnd {g : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.normalizer (S : Set (V ≃ₗ[K] V))) (v : V) :
    g (avgEnd S v) = avgEnd S (g v) := by
  rw [avgEnd_apply, avgEnd_apply, LinearEquiv.map_smul, map_sum]
  congr 1
  have h1 : ∀ s : S, g * (s : V ≃ₗ[K] V) * g⁻¹ ∈ S := fun s =>
    (Subgroup.mem_normalizer_iff.1 hg s).1 s.2
  have h2 : ∀ s : S, g⁻¹ * (s : V ≃ₗ[K] V) * g ∈ S := fun s => by
    refine (Subgroup.mem_normalizer_iff.1 hg _).2 ?_
    rw [show g * (g⁻¹ * (s : V ≃ₗ[K] V) * g) * g⁻¹ = s by group]
    exact s.2
  let φ : S ≃ S :=
    { toFun := fun s => ⟨g * s * g⁻¹, h1 s⟩
      invFun := fun s => ⟨g⁻¹ * s * g, h2 s⟩
      left_inv := fun s => Subtype.ext (by simp only; group)
      right_inv := fun s => Subtype.ext (by simp only; group) }
  refine Fintype.sum_equiv φ _ _ fun s => ?_
  change g ((s : V ≃ₗ[K] V) v) = (g * s * g⁻¹) (g v)
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, inv_apply_apply'']

end Avg

section Eichler

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_sub_sub_apply {u w : V} (hu : Q u = 0) (hw : polar Q u w = 0) (z : V) :
    eichler Q u w (eichler Q u w z - z) - (eichler Q u w z - z) =
      (-(polar Q z u * polar Q w w)) • u := by
  have huu : polar Q u u = 0 := polar_self_eq_zero hu
  have hwu : polar Q w u = 0 := by rw [polar_comm]; exact hw
  have hN : ∀ y, eichler Q u w y - y =
      polar Q y u • w - (polar Q y w + Q w * polar Q y u) • u := by
    intro y
    rw [eichler_apply hu hw]
    abel
  rw [hN (eichler Q u w z - z), hN z]
  simp only [polar_sub_left, polar_smul_left_eq, huu, hwu, hw]
  module

private theorem idem_fix_eichler_sub (h2 : (2 : K) ≠ 0) {u w : V} (hu : Q u = 0)
    (hw : polar Q u w = 0) (hQw : Q w ≠ 0) {p : V →ₗ[K] V}
    (hpE : ∀ z, p (eichler Q u w z) = eichler Q u w (p z)) {t : V} (ht : p t = t)
    (htu : polar Q t u ≠ 0) (z : V) : p (eichler Q u w z - z) = eichler Q u w z - z := by
  have hww : polar Q w w ≠ 0 := by
    rw [polar_self_eq_two_mul]
    exact mul_ne_zero h2 hQw
  have hpN : ∀ y, p (eichler Q u w y - y) = eichler Q u w (p y) - p y := fun y => by
    rw [map_sub, hpE]
  have hN : ∀ y, eichler Q u w y - y =
      polar Q y u • w - (polar Q y w + Q w * polar Q y u) • u := by
    intro y
    rw [eichler_apply hu hw]
    abel
  have hpu : p u = u := by
    have h1 : p ((-(polar Q t u * polar Q w w)) • u) = (-(polar Q t u * polar Q w w)) • u := by
      rw [← eichler_sub_sub_apply hu hw t, hpN, hpN, ht]
    rw [map_smul] at h1
    exact smul_right_injective V (neg_ne_zero.2 (mul_ne_zero htu hww)) h1
  have hpw : p w = w := by
    have h1 := hpN t
    rw [ht, hN t, map_sub, map_smul, map_smul, hpu] at h1
    exact smul_right_injective V htu (sub_left_injective h1)
  rw [hN z, map_sub, map_smul, map_smul, hpu, hpw]

theorem eichler_fix_range_or_ker (h2 : (2 : K) ≠ 0) {u w : V} (hu : Q u = 0)
    (hw : polar Q u w = 0) (hQw : Q w ≠ 0) (hz : ∃ z, polar Q z u ≠ 0) {p : V →ₗ[K] V}
    (hp : ∀ z, p (p z) = p z) (hpE : ∀ z, p (eichler Q u w z) = eichler Q u w (p z)) :
    (∀ z, p z = z → eichler Q u w z = z) ∨ (∀ z, p z = 0 → eichler Q u w z = z) := by
  obtain ⟨z₀, hz₀⟩ := hz
  by_cases h : polar Q (p z₀) u = 0
  · left
    set q : V →ₗ[K] V := LinearMap.id - p with hq
    have hqE : ∀ z, q (eichler Q u w z) = eichler Q u w (q z) := fun z => by
      simp only [hq, LinearMap.sub_apply, LinearMap.id_apply, hpE, map_sub]
    have ht : q (z₀ - p z₀) = z₀ - p z₀ := by
      simp only [hq, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hp, sub_self, sub_zero]
    have htu : polar Q (z₀ - p z₀) u ≠ 0 := by
      rw [polar_sub_left, h, sub_zero]
      exact hz₀
    intro z hz
    have h1 := idem_fix_eichler_sub h2 hu hw hQw hqE ht htu z
    simp only [hq, LinearMap.sub_apply, LinearMap.id_apply] at h1
    have h3 : p (eichler Q u w z - z) = 0 := sub_eq_self.1 h1
    rw [map_sub, hpE, hz] at h3
    exact sub_eq_zero.1 h3
  · right
    intro z hz
    have h1 := idem_fix_eichler_sub h2 hu hw hQw hpE (hp z₀) h z
    rw [map_sub, hpE, hz, map_zero, sub_zero] at h1
    exact sub_eq_zero.1 h1.symm

private theorem commutatorElement_apply_eq_of_smul {g h : V ≃ₗ[K] V} {z : V} (hz : z ≠ 0)
    {α β : K} (hg : g z = α • z) (hh : h z = β • z) : ⁅g, h⁆ z = z := by
  have hinv : ∀ (k : V ≃ₗ[K] V) {γ : K}, k z = γ • z → γ ≠ 0 ∧ k⁻¹ z = γ⁻¹ • z := by
    intro k γ hk
    have hγ : γ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hk
      exact hz (k.injective (by rw [hk, map_zero]))
    refine ⟨hγ, k.injective ?_⟩
    rw [apply_inv_apply'', map_smul, hk, smul_smul, inv_mul_cancel₀ hγ, one_smul]
  obtain ⟨hα, hg'⟩ := hinv g hg
  obtain ⟨hβ, hh'⟩ := hinv h hh
  have e : ⁅g, h⁆ z = g (h (g⁻¹ (h⁻¹ z))) := by
    rw [commutatorElement_def]
    rfl
  rw [e, hh', map_smul, hg', smul_smul, map_smul, hh, smul_smul, map_smul, hg, smul_smul,
    show β⁻¹ * α⁻¹ * β * α = (β⁻¹ * β) * (α⁻¹ * α) by ring, inv_mul_cancel₀ hβ,
    inv_mul_cancel₀ hα, one_mul, one_smul]

private theorem exists_avg_proj {S : Subgroup (V ≃ₗ[K] V)} [Finite S]
    (hS : (Nat.card S : K) ≠ 0) :
    ∃ pr : V →ₗ[K] V, (∀ v, pr (pr v) = pr v) ∧ (∀ s ∈ S, ∀ v, s (pr v) = pr v) ∧
      (∀ s ∈ S, ∀ v, pr (s v) = pr v) ∧ (∀ v, (∀ s ∈ S, s v = v) → pr v = v) ∧
      ∀ g ∈ Subgroup.normalizer (S : Set (V ≃ₗ[K] V)), ∀ v, g (pr v) = pr (g v) := by
  haveI := Fintype.ofFinite S
  have hS' : (Fintype.card S : K) ≠ 0 := by rwa [Fintype.card_eq_nat_card]
  exact ⟨avgEnd S, avgEnd_avgEnd hS', fun s hs v => apply_avgEnd hs v,
    fun s hs v => avgEnd_apply_apply hs v, fun v hv => avgEnd_of_fixed hS' hv,
    fun g hg v => commute_avgEnd hg v⟩

end Eichler

section Z3

private theorem z3_ofAdd_ne_one : Multiplicative.ofAdd ((1 : ZMod 3), (0 : ZMod 3)) ≠ 1 := by
  decide

private theorem z3_pow_three (x : ZMod 3 × ZMod 3) : (Multiplicative.ofAdd x) ^ 3 = 1 := by
  revert x
  decide

private theorem z3_pow_four : (Multiplicative.ofAdd ((1 : ZMod 3), (0 : ZMod 3))) ^ (2 * 2) =
    Multiplicative.ofAdd ((1 : ZMod 3), (0 : ZMod 3)) := by
  decide

private theorem z3_cases (x : ZMod 3 × ZMod 3) (hx : x ≠ 0) (h2 : x.2 = 0) :
    Multiplicative.ofAdd x = Multiplicative.ofAdd ((1 : ZMod 3), (0 : ZMod 3)) ∨
      Multiplicative.ofAdd x = Multiplicative.ofAdd ((1 : ZMod 3), (0 : ZMod 3)) ^ 2 := by
  revert x
  decide

end Z3

section Main

variable {K V : Type*} [Field K] [Finite K] [CharP K 3] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem eichler_commute_of_isPGroup_two {e₀ w₁ w₂ : V} (he : Q e₀ = 0)
    (hz : ∃ z, polar Q z e₀ ≠ 0) (h₁ : polar Q e₀ w₁ = 0) (h₂ : polar Q e₀ w₂ = 0)
    (hw : ∀ c₁ c₂ : ZMod 3, (c₁, c₂) ≠ 0 →
      Q (ZMod.castHom (dvd_refl 3) K c₁ • w₁ + ZMod.castHom (dvd_refl 3) K c₂ • w₂) ≠ 0)
    {R : Subgroup (V ≃ₗ[K] V)} (hR : IsPGroup 2 R)
    (hRn : ∀ c₁ c₂ : ZMod 3, eichler Q e₀
      (ZMod.castHom (dvd_refl 3) K c₁ • w₁ + ZMod.castHom (dvd_refl 3) K c₂ • w₂) ∈
        Subgroup.normalizer (R : Set (V ≃ₗ[K] V))) :
    ∀ r ∈ R, eichler Q e₀ w₁ * r = r * eichler Q e₀ w₁ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    fun g₁ g₂ h => LinearEquiv.ext (congrFun h)
  have h3K : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have h2 : (2 : K) ≠ 0 := fun h0 => one_ne_zero (by linear_combination h3K - h0 : (1 : K) = 0)
  let wv : ZMod 3 × ZMod 3 → V := fun c =>
    ZMod.castHom (dvd_refl 3) K c.1 • w₁ + ZMod.castHom (dvd_refl 3) K c.2 • w₂
  have hwv0 : wv 0 = 0 := by simp [wv]
  have hwv_add : ∀ c c', wv (c + c') = wv c + wv c' := by
    intro c c'
    simp only [wv, Prod.fst_add, Prod.snd_add, map_add, add_smul]
    abel
  have hpol : ∀ c, polar Q e₀ (wv c) = 0 := by
    intro c
    simp only [wv, polar_add_right, polar_smul_right_eq, h₁, h₂, mul_zero, add_zero]
  let E : Multiplicative (ZMod 3 × ZMod 3) →* (V ≃ₗ[K] V) :=
    { toFun := fun c => eichler Q e₀ (wv (Multiplicative.toAdd c))
      map_one' := by simp only [toAdd_one, hwv0, eichler_zero_right]
      map_mul' := fun c c' => by
        simp only [toAdd_mul, hwv_add, eichler_mul (hpol _) (hpol _)] }
  have hE : ∀ c, E c = eichler Q e₀ (wv (Multiplicative.toAdd c)) := fun c => rfl
  have hEn : ∀ c, E c ∈ Subgroup.normalizer (R : Set (V ≃ₗ[K] V)) := fun c => hRn _ _
  have hAc : ∀ c c', E c * E c' = E c' * E c := fun c c' => by
    rw [← map_mul, ← map_mul, mul_comm]
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Multiplicative (ZMod 3 × ZMod 3),
      c₀ = Multiplicative.ofAdd ((1 : ZMod 3), (0 : ZMod 3)) := ⟨_, rfl⟩
  have hc₀1 : c₀ ≠ 1 := hc₀ ▸ z3_ofAdd_ne_one
  have hy : E c₀ = eichler Q e₀ w₁ := by
    rw [hE, hc₀, toAdd_ofAdd]
    simp only [wv, map_one, map_zero, one_smul, zero_smul, add_zero]
  have hQc : ∀ c : Multiplicative (ZMod 3 × ZMod 3), c ≠ 1 →
      Q (wv (Multiplicative.toAdd c)) ≠ 0 :=
    fun c hc => hw _ _ fun h0 => hc (Multiplicative.toAdd.injective (by rw [toAdd_one]; exact h0))
  obtain ⟨z₀, hz₀⟩ := hz
  have he0 : e₀ ≠ 0 := fun h0 => hz₀ (by rw [h0, polar_zero_right])
  have hsplit : ∀ c, c ≠ 1 → ∀ {p : V →ₗ[K] V}, (∀ z, p (p z) = p z) →
      (∀ z, p (E c z) = E c (p z)) →
      (∀ z, p z = z → E c z = z) ∨ (∀ z, p z = 0 → E c z = z) :=
    fun c hc p hp hpE => eichler_fix_range_or_ker h2 he (hpol _) (hQc c hc) ⟨z₀, hz₀⟩ hp hpE
  have hκ : ∀ c, c ≠ 1 → -(polar Q z₀ e₀ *
      polar Q (wv (Multiplicative.toAdd c)) (wv (Multiplicative.toAdd c))) ≠ 0 :=
    fun c hc => by
      rw [polar_self_eq_two_mul]
      exact neg_ne_zero.2 (mul_ne_zero hz₀ (mul_ne_zero h2 (hQc c hc)))
  have hne1 : ∀ c, c ≠ 1 → E c ≠ 1 := by
    intro c hc h
    have h1 := eichler_sub_sub_apply he (hpol (Multiplicative.toAdd c)) z₀
    rw [← hE, h] at h1
    change z₀ - z₀ - (z₀ - z₀) = _ at h1
    rw [sub_self, eq_comm, smul_eq_zero] at h1
    exact h1.elim (hκ c hc) he0
  let α : Multiplicative (ZMod 3 × ZMod 3) →* MulAut (V ≃ₗ[K] V) := MulAut.conj.comp E
  have hαR : CFSG.SolvableSignalizer.IsInvariant α R := by
    intro c
    have hn := hEn c
    ext g
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hn r).1 hr
    · intro hg
      refine ⟨(E c)⁻¹ * g * E c, (Subgroup.mem_normalizer_iff.1 hn _).2 ?_, ?_⟩
      · rwa [show E c * ((E c)⁻¹ * g * E c) * (E c)⁻¹ = g by group]
      · change E c * ((E c)⁻¹ * g * E c) * (E c)⁻¹ = g
        group
  let β := CFSG.SolvableSignalizer.restrictAction α R hαR
  haveI : @CFSG.IsElementaryAbelian 3 (Multiplicative (ZMod 3 × ZMod 3)) CommGroup.toGroup :=
    { toIsMulCommutative := ⟨⟨mul_comm⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun c => z3_pow_three _ }
  have hcop : ¬ 3 ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := hR.exists_card_eq
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hcard : 3 ^ 2 ≤ Nat.card (Multiplicative (ZMod 3 × ZMod 3)) := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod]
    norm_num
  have htop := CFSG.SolvableSignalizer.iSup_fixedSubgroup_eq_top 3 Nat.prime_three β hcard hcop
  intro r₀ hr₀
  rw [← hy]
  by_contra hne₀
  obtain ⟨c, hc1, r, hrR, hra, hry⟩ : ∃ c : Multiplicative (ZMod 3 × ZMod 3), c ≠ 1 ∧
      ∃ r ∈ R, E c * r = r * E c ∧ E c₀ * r ≠ r * E c₀ := by
    by_contra hall
    push Not at hall
    have hle : (⨆ (c : Multiplicative (ZMod 3 × ZMod 3)) (_ : c ≠ 1),
        CFSG.SolvableSignalizer.fixedSubgroup β c) ≤
          (Subgroup.centralizer {E c₀}).comap R.subtype := by
      refine iSup₂_le fun c hc g hg => ?_
      rw [CFSG.SolvableSignalizer.mem_fixedSubgroup] at hg
      have hg' : E c * (g : V ≃ₗ[K] V) * (E c)⁻¹ = g := congrArg Subtype.val hg
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      refine (hall c hc g g.2 ?_).symm
      calc E c * (g : V ≃ₗ[K] V) = (E c * g * (E c)⁻¹) * E c := by group
        _ = g * E c := by rw [hg']
    have hmem : (⟨r₀, hr₀⟩ : R) ∈ ⨆ (c : Multiplicative (ZMod 3 × ZMod 3)) (_ : c ≠ 1),
        CFSG.SolvableSignalizer.fixedSubgroup β c :=
      htop.ge (Subgroup.mem_top _)
    have h1 := hle hmem
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at h1
    exact hne₀ h1.symm
  have hc2 : (Multiplicative.toAdd c).2 ≠ 0 := by
    intro h0
    have hc' : c = c₀ ∨ c = c₀ ^ 2 := by
      rw [hc₀]
      exact z3_cases (Multiplicative.toAdd c)
        (fun h => hc1 (Multiplicative.toAdd.injective (by rw [toAdd_one]; exact h))) h0
    rcases hc' with rfl | rfl
    · exact hry hra
    · apply hry
      have h4 : E c₀ = E (c₀ ^ 2) ^ 2 := by
        rw [← map_pow, ← pow_mul, hc₀, z3_pow_four]
      rw [h4]
      exact (Commute.pow_left hra 2).eq
  have hcc₀ : c * c₀ ≠ 1 := by
    intro h
    apply hc2
    have := congrArg (fun x => (Multiplicative.toAdd x).2) h
    rw [hc₀] at this
    simpa using this
  have hay : E c * E c₀ = E c₀ * E c := hAc c c₀
  obtain ⟨X, hX⟩ : ∃ X : Subgroup (V ≃ₗ[K] V), X = R ⊓ Subgroup.centralizer {E c} := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Subgroup (V ≃ₗ[K] V), D = Subgroup.zpowers (E c₀) := ⟨_, rfl⟩
  have hyD : E c₀ ∈ D := hD ▸ Subgroup.mem_zpowers _
  have hy3 : E c₀ ^ 3 = 1 := by rw [← map_pow, hc₀, z3_pow_three, map_one]
  have hD3 : IsPGroup 3 D := by
    rintro ⟨d, hd⟩
    rw [hD] at hd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  have hyC : E c₀ ∈ Subgroup.centralizer {E c} :=
    Subgroup.mem_centralizer_singleton_iff.2 hay.symm
  have hDC : D ≤ Subgroup.centralizer {E c} := hD ▸ Subgroup.zpowers_le.2 hyC
  have hDR : D ≤ Subgroup.normalizer (R : Set (V ≃ₗ[K] V)) := hD ▸ Subgroup.zpowers_le.2 (hEn c₀)
  have hDX : D ≤ Subgroup.normalizer (X : Set (V ≃ₗ[K] V)) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have h1 := Subgroup.mem_normalizer_iff.1 (hDR hd) g
    have h2 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer (hDC hd)) g
    rw [hX, Subgroup.mem_inf, Subgroup.mem_inf, h1, h2]
  have hX3 : ¬ 3 ∣ Nat.card X := fun h =>
    hcop (h.trans (Subgroup.card_dvd_of_le (hX ▸ inf_le_left)))
  obtain ⟨S, hS⟩ : ∃ S : Subgroup (V ≃ₗ[K] V), S = ⁅X, D⁆ := ⟨_, rfl⟩
  have hSS : ⁅S, D⁆ = S := by
    rw [hS]
    exact CFSG.HardMathSupport.Solomon.Coordinator.Generation228.comm_comm_eq Nat.prime_three hD3
      hDX hX3
  have hSX : S ≤ X := by
    rw [hS, Subgroup.commutator_le]
    intro g hg d hd
    rw [show ⁅g, d⁆ = g * (d * g⁻¹ * d⁻¹) by rw [commutatorElement_def]; group]
    exact X.mul_mem hg ((Subgroup.mem_normalizer_iff.1 (hDX hd) g⁻¹).1 (X.inv_mem hg))
  have hDS : D ≤ Subgroup.normalizer (S : Set (V ≃ₗ[K] V)) := by
    have hconj : ∀ g ∈ D, ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
      intro g hg s hs
      have hle : S ≤ S.comap (MulAut.conj g).toMonoidHom := by
        rw [hS, Subgroup.commutator_le]
        intro x hx e he'
        rw [Subgroup.mem_comap]
        change g * ⁅x, e⁆ * g⁻¹ ∈ ⁅X, D⁆
        rw [show g * ⁅x, e⁆ * g⁻¹ = ⁅g * x * g⁻¹, g * e * g⁻¹⁆ by
          simp only [commutatorElement_def]
          group]
        exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.1 (hDX hg) x).1 hx)
          (D.mul_mem (D.mul_mem hg he') (D.inv_mem hg))
      exact hle hs
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨hconj d hd s, fun h => ?_⟩
    have := hconj d⁻¹ (D.inv_mem hd) _ h
    rwa [show d⁻¹ * (d * s * d⁻¹) * d⁻¹⁻¹ = s by group] at this
  have hrX : r ∈ X := hX ▸ ⟨hrR, Subgroup.mem_centralizer_singleton_iff.2 hra.symm⟩
  have hSbot : S ≠ ⊥ := by
    intro h
    have h1 : ⁅r, E c₀⁆ ∈ S := hS ▸ Subgroup.commutator_mem_commutator hrX hyD
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact hry h1.symm
  have hSa : ∀ s ∈ S, s * E c = E c * s := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.1 (hX ▸ hSX hs : s ∈ R ⊓ _).2
  have hSc : (Nat.card S : K) ≠ 0 := by
    obtain ⟨k, hk⟩ := (hR.to_le (hSX.trans (hX ▸ inf_le_left))).exists_card_eq
    rw [hk, Nat.cast_pow]
    exact pow_ne_zero _ (by exact_mod_cast h2)
  obtain ⟨pr, hpr_idem, hpr_s, hpr_s', hpr_fix, hpr_comm⟩ := exists_avg_proj (S := S) hSc
  have haN : E c ∈ Subgroup.normalizer (S : Set (V ≃ₗ[K] V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      rwa [show E c * s * (E c)⁻¹ = s by rw [← hSa s hs]; group]
    · intro hs
      have h1 := hSa _ hs
      have h3 : E c * s = E c * (E c * s * (E c)⁻¹) := by
        calc E c * s = E c * s * (E c)⁻¹ * E c := by group
          _ = E c * (E c * s * (E c)⁻¹) := h1
      rwa [mul_left_cancel h3]
  have ha_pr : ∀ v, pr (E c v) = E c (pr v) := fun v => (hpr_comm _ haN v).symm
  have hy_pr : ∀ v, pr (E c₀ v) = E c₀ (pr v) := fun v => (hpr_comm _ (hDS hyD) v).symm
  have hext : ∀ g : V ≃ₗ[K] V, (∀ v, pr v = v → g v = v) → (∀ v, pr v = 0 → g v = v) →
      g = 1 := by
    intro g h1 h2
    refine LinearEquiv.ext fun v => ?_
    change g v = v
    have hv : v = pr v + (v - pr v) := by abel
    rw [hv, map_add, h1 _ (hpr_idem v), h2 _ (by rw [map_sub, hpr_idem, sub_self])]
  have hy_range : ∀ v, pr v = v → E c₀ v = v := by
    rcases hsplit c₀ hc₀1 hpr_idem hy_pr with h | h
    · exact h
    · exfalso
      apply hSbot
      let H₀ : Subgroup (V ≃ₗ[K] V) :=
        { carrier := {g | (∀ v, pr (g v) = g (pr v)) ∧ ∀ v, pr v = 0 → g v = v}
          one_mem' := ⟨fun v => rfl, fun v _ => rfl⟩
          mul_mem' := by
            rintro g g' ⟨hg1, hg2⟩ ⟨hg1', hg2'⟩
            refine ⟨fun v => ?_, fun v hv => ?_⟩
            · change pr (g (g' v)) = g (g' (pr v))
              rw [hg1, hg1']
            · change g (g' v) = v
              rw [hg2' v hv, hg2 v hv]
          inv_mem' := by
            rintro g ⟨hg1, hg2⟩
            refine ⟨fun v => g.injective ?_, fun v hv => g.injective ?_⟩
            · rw [← hg1, apply_inv_apply'', apply_inv_apply'']
            · rw [apply_inv_apply'', hg2 v hv] }
      have hDH : D ≤ H₀ := hD ▸ Subgroup.zpowers_le.2 ⟨hy_pr, h⟩
      have hcomm : ⁅S, D⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro s hs d hd
        rw [Subgroup.mem_bot]
        obtain ⟨hd1, hd2⟩ := hDH hd
        obtain ⟨hdi1, hdi2⟩ := hDH (D.inv_mem hd)
        have hsi : s⁻¹ ∈ S := S.inv_mem hs
        refine LinearEquiv.ext fun v => ?_
        change s (d (s⁻¹ (d⁻¹ v))) = v
        have hu : pr (v - pr v) = 0 := by rw [map_sub, hpr_idem, sub_self]
        have h1 : s (d (s⁻¹ (d⁻¹ (pr v)))) = pr v := by
          rw [← hdi1, hpr_s _ hsi, ← hd1, apply_inv_apply'', hpr_s _ hs]
        have h2 : s (d (s⁻¹ (d⁻¹ (v - pr v)))) = v - pr v := by
          rw [hdi2 _ hu, hd2 _ (by rw [hpr_s' _ hsi]; exact hu), apply_inv_apply'']
        have hv : d⁻¹ v = d⁻¹ (pr v) + d⁻¹ (v - pr v) := by rw [← map_add, add_sub_cancel]
        rw [hv, map_add, map_add, map_add, h1, h2, add_sub_cancel]
      rw [← hSS, hcomm]
  have ha_range : ∀ v, pr v = v → E c v = v := by
    rcases hsplit c hc1 hpr_idem ha_pr with h | h
    · exact h
    · exfalso
      have hE' : E (c * c₀) = E c * E c₀ := map_mul E c c₀
      have hay_pr : ∀ v, pr (E (c * c₀) v) = E (c * c₀) (pr v) := fun v => by
        rw [hE', LinearEquiv.mul_apply, LinearEquiv.mul_apply, ha_pr, hy_pr]
      rcases hsplit (c * c₀) hcc₀ hpr_idem hay_pr with h' | h'
      · refine hne1 c hc1 (hext (E c) (fun v hv => ?_) h)
        have := h' v hv
        rwa [hE', LinearEquiv.mul_apply, hy_range v hv] at this
      · refine hne1 c₀ hc₀1 (hext (E c₀) hy_range fun v hv => ?_)
        have h1 := h' v hv
        have h2 : pr (E c₀ v) = 0 := by rw [hy_pr, hv, map_zero]
        rwa [hE', LinearEquiv.mul_apply, h _ h2] at h1
  have hNN : ∀ z, E c (E c z - z) - (E c z - z) = (-(polar Q z e₀ *
      polar Q (wv (Multiplicative.toAdd c)) (wv (Multiplicative.toAdd c)))) • e₀ :=
    fun z => eichler_sub_sub_apply he (hpol _) z
  have hpr_e₀ : pr e₀ = 0 := by
    have h1 : pr (E c (E c z₀ - z₀) - (E c z₀ - z₀)) = 0 := by
      simp only [map_sub, ha_pr, ha_range _ (hpr_idem z₀), sub_self, map_zero]
    rw [hNN, map_smul] at h1
    exact (smul_eq_zero.1 h1).resolve_left (hκ c hc1)
  let H₁ : Subgroup (V ≃ₗ[K] V) :=
    { carrier := {g | g e₀ = e₀}
      one_mem' := rfl
      mul_mem' := fun {g g'} hg hg' => by
        change g (g' e₀) = e₀
        rw [show g' e₀ = e₀ from hg', show g e₀ = e₀ from hg]
      inv_mem' := fun {g} hg => by
        change g⁻¹ e₀ = e₀
        apply g.injective
        rw [apply_inv_apply'']
        exact hg.symm }
  have hDH₁ : D ≤ H₁ := hD ▸ Subgroup.zpowers_le.2 (eichler_apply_self (Q := Q) e₀ _)
  have hSe₀ : ∀ s ∈ S, ∃ γ : K, s e₀ = γ • e₀ := by
    intro s hs
    have hsa : ∀ v, s (E c v) = E c (s v) := fun v => by
      rw [← LinearEquiv.mul_apply, hSa s hs, LinearEquiv.mul_apply]
    have h2 : s (E c (E c z₀ - z₀) - (E c z₀ - z₀)) =
        E c (E c (s z₀) - s z₀) - (E c (s z₀) - s z₀) := by
      simp only [map_sub, hsa]
    rw [hNN, hNN, map_smul] at h2
    refine ⟨(-(polar Q z₀ e₀ * polar Q (wv (Multiplicative.toAdd c))
      (wv (Multiplicative.toAdd c))))⁻¹ * (-(polar Q (s z₀) e₀ *
        polar Q (wv (Multiplicative.toAdd c)) (wv (Multiplicative.toAdd c)))), ?_⟩
    rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ (hκ c hc1), one_smul]
  have hSH₁ : S ≤ H₁ := by
    rw [← hSS, Subgroup.commutator_le]
    intro s hs d hd
    obtain ⟨γ, hγ⟩ := hSe₀ s hs
    exact commutatorElement_apply_eq_of_smul he0 hγ
      (show d e₀ = (1 : K) • e₀ by rw [one_smul]; exact hDH₁ hd)
  have hfix : pr e₀ = e₀ := hpr_fix e₀ fun s hs => hSH₁ hs
  exact he0 (by rw [← hfix, hpr_e₀])

end Main

end CFSG.LocalAnalysis.GLTheoremA.S2019

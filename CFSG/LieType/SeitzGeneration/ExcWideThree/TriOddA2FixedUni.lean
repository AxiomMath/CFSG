module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddA2Toral

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.A2Uni

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual
  CFSG.HardMathSupport.Lang.E6Descent CFSG.Fischer CFSG.RankThree.PartTwo.Sec19
  CFSG.LieType.SeitzGeneration.ExcWideThree


theorem pos_of_normalizes_U {X : Type*} [Group X] {n : ℕ} {H U : Subgroup X} {r₁ r₂ : X}
    {root : ℤ → Subgroup X} (R : RGD2 n H r₁ r₂ U root) {m : X}
    (hm : ∀ x ∈ U, m * x * m⁻¹ ∈ U) {f : ℤ → ℤ} (hf : ActsPos n root m f) {p : ℤ}
    (hp : 1 ≤ Rt n p ∧ Rt n p ≤ n) : 1 ≤ Rt n (f p) ∧ Rt n (f p) ≤ n := by
  have hn : 0 < n := by have := R.three_le; omega
  have hne := R.ne_bot (Rt n p) (Rt_isRoot hn p)
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyU : y ∈ U := R.root_le_U hp.1 hp.2 hy
  have hmy := hf p y hy
  by_contra hcon
  have hk := Rt_isRoot hn (f p)
  have hneg : Rt n (f p) ≤ -1 := by
    have h1 := hk.1
    have h2 := hk.2
    omega
  have hyneg : m * y * m⁻¹ ∈ negGen n root := by
    refine mem_negGen_of_mem (k := -Rt n (f p)) (by omega) (by have := hk.2; omega) ?_
    rw [neg_neg]
    exact hmy
  have h1 := R.meet_one _ ((le_sup_right : U ≤ H ⊔ U) (hm y hyU)) hyneg
  apply hy1'
  have h3 := congrArg (fun z => m⁻¹ * z * m) h1
  simpa [mul_assoc] using h3

theorem mem_H_of_normalizes_U {X : Type*} [Group X] {n : ℕ} {H U : Subgroup X} {r₁ r₂ : X}
    {root : ℤ → Subgroup X} (R : RGD2 n H r₁ r₂ U root) {m : X} (hmN : m ∈ R.N)
    (hm : ∀ x ∈ U, m * x * m⁻¹ ∈ U) : m ∈ H := by
  have h3 := R.three_le
  obtain ⟨k, h, hh, hk | hk⟩ := R.exists_normal_form hmN
  · have hρnorm : ∀ x ∈ U, ((r₁ * r₂) ^ k) * x * ((r₁ * r₂) ^ k)⁻¹ ∈ U := by
      intro x hx
      have hx' : h⁻¹ * x * (h⁻¹)⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.1 (R.H_le_normalizer_U (H.inv_mem hh)) x).1 hx
      have h1 := hm _ hx'
      have e : (r₁ * r₂) ^ k * x * ((r₁ * r₂) ^ k)⁻¹ =
          m * (h⁻¹ * x * (h⁻¹)⁻¹) * m⁻¹ := by
        rw [hk]; group
      rw [e]
      simpa only [mul_assoc, inv_inv] using h1
    have h1 := pos_of_normalizes_U R hρnorm (R.actsPos_pow k) (p := 0)
      ⟨by rw [Rt_zero (by omega)], by rw [Rt_zero (by omega)]; omega⟩
    have h2 := pos_of_normalizes_U R hρnorm (R.actsPos_pow k) (p := (n : ℤ) - 1)
      ⟨by rw [Rt_pred (by omega)]; omega, by rw [Rt_pred (by omega)]⟩
    have hk0 := rot_pos h3 h1 h2
    have hdvd : (n : ℤ) ∣ (k : ℤ) := Int.dvd_of_emod_eq_zero hk0
    obtain ⟨j, rfl⟩ : n ∣ k := Int.natCast_dvd_natCast.1 hdvd
    have hρH : (r₁ * r₂) ^ (n * j) ∈ H := by
      rw [pow_mul]
      exact H.pow_mem R.pow j
    rw [hk]
    exact H.mul_mem hρH hh
  · have hρnorm : ∀ x ∈ U, (r₁ * (r₁ * r₂) ^ k) * x * (r₁ * (r₁ * r₂) ^ k)⁻¹ ∈ U := by
      intro x hx
      have hx' : h⁻¹ * x * (h⁻¹)⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.1 (R.H_le_normalizer_U (H.inv_mem hh)) x).1 hx
      have h1 := hm _ hx'
      have e : r₁ * (r₁ * r₂) ^ k * x * (r₁ * (r₁ * r₂) ^ k)⁻¹ =
          m * (h⁻¹ * x * (h⁻¹)⁻¹) * m⁻¹ := by
        rw [hk]; group
      rw [e]
      simpa only [mul_assoc, inv_inv] using h1
    have hact := R.actsPos_r₁.mul (R.actsPos_pow k)
    have h1 := pos_of_normalizes_U R hρnorm hact (p := 0)
      ⟨by rw [Rt_zero (by omega)], by rw [Rt_zero (by omega)]; omega⟩
    have h2 := pos_of_normalizes_U R hρnorm hact (p := (n : ℤ) - 1)
      ⟨by rw [Rt_pred (by omega)]; omega, by rw [Rt_pred (by omega)]⟩
    have h1' : 1 ≤ Rt n ((n : ℤ) - 2 * (k : ℤ)) ∧
        Rt n ((n : ℤ) - 2 * (k : ℤ)) ≤ n := by simpa using h1
    have harg : (n : ℤ) - ((n : ℤ) - 1 + 2 * (k : ℤ)) = 1 - 2 * (k : ℤ) := by ring
    rw [harg] at h2
    exact (refl_pos h3 h1' h2).elim

theorem centralizer_U_le {X : Type*} [Group X] {n : ℕ} {H U : Subgroup X} {r₁ r₂ : X}
    {root : ℤ → Subgroup X} (R : RGD2 n H r₁ r₂ U root) {p : ℕ} [Fact p.Prime]
    (hUp : IsPGroup p U)
    (hHcop : Nat.Coprime p (Nat.card H))
    (hC : ∀ h ∈ H, (∀ u ∈ U, h * u = u * h) → h = 1)
    {g : X} (hgB : g ∈ H ⊔ U) (hg : ∀ u ∈ U, g * u = u * g) : g ∈ U := by
  obtain ⟨u, hu, h, hh, rfl⟩ := (R.mem_sup_iff_UH).1 hgB
  let actH : H →* MulAut U := U.normalizerMonoidHom.comp (Subgroup.inclusion R.H_le_normalizer_U)
  let actU : U →* MulAut U :=
    U.normalizerMonoidHom.comp (Subgroup.inclusion (Subgroup.le_normalizer (H := U)))
  have hcomp : actU ⟨u, hu⟩ * actH ⟨h, hh⟩ = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    show ((actU ⟨u, hu⟩ * actH ⟨h, hh⟩) x : X) = (x : X)
    simp only [MulAut.mul_apply, actH, actU, MonoidHom.comp_apply,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    change u * (h * (x : X) * h⁻¹) * u⁻¹ = (x : X)
    have hx := hg (x : X) x.2
    have e : u * (h * (x : X) * h⁻¹) * u⁻¹ = (u * h) * (x : X) * (u * h)⁻¹ := by group
    rw [e, hx]
    group
  have hAeq : actH ⟨h, hh⟩ = (actU ⟨u, hu⟩)⁻¹ := eq_inv_of_mul_eq_one_right hcomp
  have hdivU : orderOf (actH ⟨h, hh⟩) ∣ orderOf u := by
    rw [hAeq, orderOf_inv]
    calc orderOf (actU ⟨u, hu⟩) ∣ orderOf (⟨u, hu⟩ : U) := orderOf_map_dvd actU ⟨u, hu⟩
      _ = orderOf u := (Subgroup.orderOf_coe _).symm
  have hdivH : orderOf (actH ⟨h, hh⟩) ∣ orderOf h := by
    calc orderOf (actH ⟨h, hh⟩) ∣ orderOf (⟨h, hh⟩ : H) :=
          orderOf_map_dvd actH ⟨h, hh⟩
      _ = orderOf h := (Subgroup.orderOf_coe _).symm
  have hord1 : orderOf (actH ⟨h, hh⟩) = 1 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hUp) ⟨u, hu⟩
    have hk' : orderOf u = p ^ k := by
      rw [Subgroup.orderOf_coe (⟨u, hu⟩ : U), hk]
    have hcop : Nat.Coprime p (orderOf h) :=
      hHcop.coprime_dvd_right (Subgroup.orderOf_dvd_natCard H hh)
    have hgcd : Nat.gcd (p ^ k) (orderOf h) = 1 :=
      Nat.Coprime.gcd_eq_one (hcop.pow_left k)
    have hdiv1 : orderOf (actH ⟨h, hh⟩) ∣ 1 := by
      have hd := Nat.dvd_gcd (hk' ▸ hdivU) hdivH
      rwa [hgcd] at hd
    exact Nat.dvd_one.mp hdiv1
  have hcent : ∀ u ∈ U, h * u = u * h := by
    intro y hy
    have h1 := congrArg (fun φ : MulAut U => ((φ ⟨y, hy⟩ : U) : X))
      (orderOf_eq_one_iff.mp hord1)
    simp only [actH, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      MulAut.one_apply] at h1
    have h1' : h * y * h⁻¹ = y := by simpa using h1
    calc h * y = (h * y * h⁻¹) * h := by group
      _ = y * h := by rw [h1']
  have hh1 : h = 1 := hC h hh hcent
  rw [hh1, mul_one]
  exact hu

theorem eq_one_of_mem_pgroup_pow_three {X : Type*} [Group X] {U : Subgroup X} {p : ℕ}
    [Fact p.Prime] (hUp : IsPGroup p U) (hp3 : p ≠ 3) {x : X} (hxU : x ∈ U)
    (hx3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hUp) ⟨x, hxU⟩
  have hord : orderOf x = p ^ k := by
    rw [Subgroup.orderOf_coe (⟨x, hxU⟩ : U), hk]
  have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  rw [hord] at hdvd
  rcases k with _ | k
  · rw [pow_zero] at hord
    exact orderOf_eq_one_iff.mp hord
  · have hpdvd : p ∣ 3 :=
      (dvd_pow_self p (Nat.succ_ne_zero k)).trans hdvd
    exact absurd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1 hpdvd) hp3

theorem fold_fixSub_le_sup {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}
    (hA : A2Std σ d q) (φ : MulAut (C0 σ))
    (hφ : ∀ y : C0 σ,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {x : twistedGroup σ.toRingHom} (hxfix : a2Phi hA φ x = x)
    (hxU : ∀ u ∈ (posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓
      foldFix (a2Phi hA φ), x * u = u * x) :
    x ∈ ((⨆ i, hHat σ.toRingHom i) ⊓ foldFix (a2Phi hA φ)) ⊔
      ((posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (a2Phi hA φ)) := by
  classical
  let H' : Subgroup (twistedGroup σ.toRingHom) :=
    (⨆ i, hHat σ.toRingHom i) ⊓ foldFix (a2Phi hA φ)
  let U' : Subgroup (twistedGroup σ.toRingHom) :=
    (posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (a2Phi hA φ)
  have hfD := a2_foldData hA φ hφ
  have hgen : ((⨆ i, hHat σ.toRingHom i) ⊔
      posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊔
      (d4RGD2 σ.toRingHom hA.cube_apply).N = ⊤ :=
    hexRGD2_gen (twistedData σ.toRingHom hA.cube_apply)
  have hZ : ∀ g ∈ (⨆ i, hHat σ.toRingHom i),
      (∀ i, IsRoot 6 i → ∀ y ∈ hexGroup (twistedX σ.toRingHom) i, g * y = y * g) → g = 1 :=
    fun g _ hcomm => a2_hZ hA hcomm
  obtain ⟨v, hv, n, hn, u, hu, hxvu⟩ :=
    FoldStab.cell (R := d4RGD2 σ.toRingHom hA.cube_apply) (θ := a2Phi hA φ)
      hfD.toStab hgen hZ hxfix
  obtain ⟨r₁', r₂', h1, h2, h1H, h2H, R'⟩ := hfD.exists_rgd2
  have hnN : n ∈ R'.N := by
    simpa [RGD2.N] using hfD.fixed_N_mem (R := d4RGD2 σ.toRingHom hA.cube_apply)
      (φ := a2Phi hA φ) (fun h hh => a2_hz hA φ hφ h hh) h1 h1H h2 h2H hn.1 hn.2
  set x₁ : twistedGroup σ.toRingHom := v⁻¹ * x * v with hx₁
  have hx1U : ∀ w ∈ U', x₁ * w = w * x₁ := by
    intro w hw
    have hw' : v * w * v⁻¹ ∈ U' := U'.mul_mem (U'.mul_mem hv hw) (U'.inv_mem hv)
    have hxw := hxU (v * w * v⁻¹) hw'
    calc x₁ * w = v⁻¹ * x * (v * w * v⁻¹) * v := by rw [hx₁]; group
      _ = v⁻¹ * ((v * w * v⁻¹) * x) * v := by
        rw [show v⁻¹ * x * (v * w * v⁻¹) * v =
          v⁻¹ * (x * (v * w * v⁻¹)) * v by group, hxw]
      _ = w * x₁ := by rw [hx₁]; group
  have hx1invU : ∀ w ∈ U', x₁⁻¹ * w = w * x₁⁻¹ := by
    intro w hw
    calc x₁⁻¹ * w = x₁⁻¹ * (w * x₁) * x₁⁻¹ := by group
      _ = x₁⁻¹ * (x₁ * w) * x₁⁻¹ := by rw [← hx1U w hw]
      _ = w * x₁⁻¹ := by group
  have hx1N : x₁ ∈ Subgroup.normalizer (U' : Set (twistedGroup σ.toRingHom)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      have h := hx1U w hw
      rwa [show x₁ * w * x₁⁻¹ = w by rw [h]; group]
    · intro hw
      have h := hx1invU (x₁ * w * x₁⁻¹) hw
      have heq : w = x₁ * w * x₁⁻¹ := by
        calc w = x₁⁻¹ * (x₁ * w * x₁⁻¹) * x₁ := by group
          _ = (x₁ * w * x₁⁻¹) * x₁⁻¹ * x₁ := by rw [h]
          _ = x₁ * w * x₁⁻¹ := by group
      rwa [heq]
  have hx1eq : x₁ = n * (u * v) := by
    rw [hx₁, hxvu]; group
  have hu1U : u * v ∈ U' := U'.mul_mem hu hv
  have hnN' : n ∈ Subgroup.normalizer (U' : Set (twistedGroup σ.toRingHom)) := by
    have h1 : n = x₁ * (u * v)⁻¹ := by rw [hx1eq]; group
    rw [h1]
    exact (Subgroup.normalizer (U' : Set (twistedGroup σ.toRingHom))).mul_mem hx1N
      ((Subgroup.normalizer (U' : Set (twistedGroup σ.toRingHom))).inv_mem
        (Subgroup.le_normalizer hu1U))
  have hnNorm : ∀ w ∈ U', n * w * n⁻¹ ∈ U' := by
    intro w hw
    exact (Subgroup.mem_normalizer_iff.1 hnN' w).1 hw
  have hnH : n ∈ H' := mem_H_of_normalizes_U R' hnN hnNorm
  have hxB : x ∈ H' ⊔ U' := by
    rw [hxvu]
    exact (H' ⊔ U').mul_mem
      ((H' ⊔ U').mul_mem (Subgroup.mem_sup_right hv) (Subgroup.mem_sup_left hnH))
      (Subgroup.mem_sup_right hu)
  exact hxB

theorem fold_centralizer_trivial {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {d : Kˣ} {q ℓ f : ℕ} (hA : A2Std σ d q) (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hqeq : q = ℓ ^ f)
    (φ : MulAut (C0 σ))
    (hφ : ∀ y : C0 σ,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {x : twistedGroup σ.toRingHom}
    (hxfix : a2Phi hA φ x = x) (hx3 : x ^ 3 = 1)
    (hxU : ∀ u ∈ (posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓
      foldFix (a2Phi hA φ), x * u = u * x) :
    x = 1 := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  let H' : Subgroup (twistedGroup σ.toRingHom) :=
    (⨆ i, hHat σ.toRingHom i) ⊓ foldFix (a2Phi hA φ)
  let U' : Subgroup (twistedGroup σ.toRingHom) :=
    (posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (a2Phi hA φ)
  obtain ⟨r₁', r₂', -, -, -, -, R'⟩ := (a2_foldData hA φ hφ).exists_rgd2
  have hxB : x ∈ H' ⊔ U' := fold_fixSub_le_sup hA φ hφ hxfix hxU
  have hcardH : Nat.card ↥H' = (q - 1) ^ 2 := a2_card_H_fix hA φ hφ
  have hHcop : Nat.Coprime ℓ (Nat.card ↥H') := by
    rw [hcardH, hqeq]
    have hcop1 : Nat.Coprime ℓ (ℓ ^ f - 1) := by
      rw [hℓ.coprime_iff_not_dvd]
      intro hd
      have hdvdq : ℓ ∣ ℓ ^ f := dvd_pow_self ℓ (by omega)
      have hd1 : ℓ ∣ 1 := by
        have hsub := Nat.dvd_sub hdvdq hd
        have hpos : 1 ≤ ℓ ^ f := by have := pow_pos hℓ.pos f; omega
        rwa [show ℓ ^ f - (ℓ ^ f - 1) = 1 by omega] at hsub
      exact hℓ.not_dvd_one hd1
    exact hcop1.pow_right 2
  have hcardU : Nat.card ↥U' = q ^ 3 := a2_card_U_fix hA φ hφ R'
  have hUp : IsPGroup ℓ U' := by
    haveI : Finite ↥U' := Nat.finite_of_card_ne_zero (by
      rw [hcardU, hqeq]
      exact (pow_pos (pow_pos hℓ.pos f) 3).ne')
    refine IsPGroup.of_card (n := 3 * f) ?_
    rw [hcardU, hqeq, ← pow_mul, mul_comm]
  have hxU' : x ∈ U' :=
    centralizer_U_le R' hUp hHcop (fun h hh => a2_hC hA φ hφ h hh) hxB hxU
  exact eq_one_of_mem_pgroup_pow_three hUp hℓ3 hxU' hx3

theorem fold_fixed_centralizer_trivial {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {d : Kˣ} {q ℓ f : ℕ} (hA : A2Std σ d q) (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (hqeq : q = ℓ ^ f)
    (φ : MulAut (C0 σ))
    (hφ : ∀ y : C0 σ,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {x : C0 σ} (hxfix : φ x = x) (hx3 : x ^ 3 = 1)
    (hxU : ∀ v ∈ ((posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓
      foldFix (a2Phi hA φ)).map (a2Equiv hA).toMonoidHom, v * x = x * v) :
    x = 1 := by
  let U' : Subgroup (twistedGroup σ.toRingHom) :=
    (posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (a2Phi hA φ)
  let x' : twistedGroup σ.toRingHom := (a2Equiv hA).symm x
  have hx'fix : a2Phi hA φ x' = x' := by
    show (a2Equiv hA).symm (φ (a2Equiv hA ((a2Equiv hA).symm x))) =
      (a2Equiv hA).symm x
    rw [MulEquiv.apply_symm_apply, hxfix]
  have hx'3 : x' ^ 3 = 1 := by
    apply (a2Equiv hA).injective
    rw [map_pow, map_one, MulEquiv.apply_symm_apply, hx3]
  have hx'U : ∀ u ∈ U', x' * u = u * x' := by
    intro u hu
    have hmem : a2Equiv hA u ∈ U'.map (a2Equiv hA).toMonoidHom := ⟨u, hu, rfl⟩
    have h := hxU (a2Equiv hA u) hmem
    apply (a2Equiv hA).injective
    rw [map_mul, map_mul]
    have hx'val : a2Equiv hA x' = x := by
      show a2Equiv hA ((a2Equiv hA).symm x) = x
      rw [MulEquiv.apply_symm_apply]
    rw [hx'val]
    exact h.symm
  have hx'1 : x' = 1 :=
    fold_centralizer_trivial hA hℓ hℓ3 hf hqeq φ hφ hx'fix hx'3 hx'U
  have hx_eq : x = a2Equiv hA x' := by
    show x = a2Equiv hA ((a2Equiv hA).symm x)
    rw [MulEquiv.apply_symm_apply]
  rw [hx_eq, hx'1, map_one]

theorem comm_conj_of_fold {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ}
    {q ℓ : ℕ} (hA : A2Std σ d q) [Fact ℓ.Prime]
    (φs : MulAut (C0 σ)) (β : MulAut (C0 σ)) (y : C0 σ) (e : ℤ)
    (he : e = 1 ∨ e = -1)
    (hβe_eq : β ^ e = MulAut.conj y⁻¹ * φs * MulAut.conj y)
    {x : C0 σ} (hβe_x : (β ^ e) x = x)
    (U' : Subgroup (twistedGroup σ.toRingHom))
    (hUsp : IsPGroup ℓ (U'.map (a2Equiv hA).toMonoidHom))
    (hUsfix : ∀ v ∈ U'.map (a2Equiv hA).toMonoidHom, φs v = v)
    (hcon : ∀ u : C0 σ, β u = u → (∃ n : ℕ, u ^ (ℓ ^ n) = 1) → u * x = x * u)
    {v : C0 σ} (hv : v ∈ U'.map (a2Equiv hA).toMonoidHom) :
    v * (y * x * y⁻¹) = (y * x * y⁻¹) * v := by
  obtain ⟨u, hu, rfl⟩ := hv
  have hφu : φs (a2Equiv hA u) = a2Equiv hA u :=
    hUsfix (a2Equiv hA u) ⟨u, hu, rfl⟩
  set w : C0 σ := y⁻¹ * (a2Equiv hA u) * y with hw
  have hfixe : (β ^ e) w = w := by
    rw [hβe_eq]
    change y⁻¹ * φs (y * w * y⁻¹) * y = w
    have hyw : y * w * y⁻¹ = a2Equiv hA u := by rw [hw]; group
    rw [hyw, hφu, ← hw]
  have hfixβ : β w = w := by
    rcases he with rfl | rfl
    · simpa using hfixe
    · have h := congrArg (fun z => β z) hfixe
      simpa using h.symm
  have hpow : ∃ n : ℕ, w ^ (ℓ ^ n) = 1 := by
    obtain ⟨n, hn⟩ :=
      (IsPGroup.iff_orderOf.mp hUsp) ⟨a2Equiv hA u, ⟨u, hu, rfl⟩⟩
    have hord_u : orderOf (a2Equiv hA u) = ℓ ^ n := by
      rw [Subgroup.orderOf_coe
        (⟨a2Equiv hA u, ⟨u, hu, rfl⟩⟩ : U'.map (a2Equiv hA).toMonoidHom), hn]
    have hord_w : orderOf w = orderOf (a2Equiv hA u) := by
      rw [hw]
      have h := MulEquiv.orderOf_eq (MulAut.conj y) (y⁻¹ * (a2Equiv hA u) * y)
      have harg : MulAut.conj y (y⁻¹ * (a2Equiv hA u) * y) = a2Equiv hA u := by
        simp only [MulAut.conj_apply]
        group
      rw [harg] at h
      exact h.symm
    exact ⟨n, by rw [← hord_u, ← hord_w]; exact pow_orderOf_eq_one w⟩
  have hcx := hcon w hfixβ hpow
  have hconj' := congrArg (fun z => y * z * y⁻¹) hcx
  have h1 : y * (w * x) * y⁻¹ = a2Equiv hA u * (y * x * y⁻¹) := by
    rw [hw]; group
  have h2 : y * (x * w) * y⁻¹ = (y * x * y⁻¹) * a2Equiv hA u := by
    rw [hw]; group
  rw [h1, h2] at hconj'
  exact hconj'

theorem exists_unipotent_fixed_not_commute {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (β : MulAut (C0 σ)) (hβ3 : β ^ 3 = 1) (hβout : β ∉ innerAut (C0 σ))
    (hβG : ¬ TriOddIsGLine σ β) (x : C0 σ) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxβ : β x = x) :
    ∃ u : C0 σ, β u = u ∧ (∃ n : ℕ, u ^ (ℓ ^ n) = 1) ∧ u * x ≠ x * u := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨y, s, d, e, he, hconj, hd, hd3, hd1, hsd⟩ :=
    exists_conj_toral hℓ hℓ2 hℓ3 hf hq hK σ hσ β hβ3 hβout hβG
  have hA : A2Std σ d (ℓ ^ f) := a2Std_of_class hℓ hℓ2 hf hq hK hσ hd hd3 hd1
  let φs : MulAut (C0 σ) := MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ
  have hφs : ∀ z : C0 σ,
      (φs z : ModGL TwistTag.D4.tag K) = a2Conj σ d (z : ModGL TwistTag.D4.tag K) :=
    fun z => a2_hφ_of_class hsd z
  let U' : Subgroup (twistedGroup σ.toRingHom) :=
    (posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (a2Phi hA φs)
  let Us : Subgroup (C0 σ) := U'.map (a2Equiv hA).toMonoidHom
  obtain ⟨r₁', r₂', -, -, -, -, R'⟩ := (a2_foldData hA φs hφs).exists_rgd2
  have hcardU' : Nat.card ↥U' = (ℓ ^ f) ^ 3 := a2_card_U_fix hA φs hφs R'
  have hUp' : IsPGroup ℓ U' := by
    haveI : Finite ↥U' := Nat.finite_of_card_ne_zero (by
      rw [hcardU']
      exact (pow_pos (pow_pos hℓ.pos f) 3).ne')
    refine IsPGroup.of_card (n := 3 * f) ?_
    rw [hcardU', ← pow_mul, mul_comm]
  have hUsp : IsPGroup ℓ Us :=
    IsPGroup.map hUp' (a2Equiv hA).toMonoidHom
  have hUsfix : ∀ v ∈ Us, φs v = v := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := hv
    have h := congrArg (a2Equiv hA) hu.2
    have h' : a2Equiv hA (a2Phi hA φs u) = φs (a2Equiv hA u) := by
      show a2Equiv hA ((a2Equiv hA).symm (φs (a2Equiv hA u))) = φs (a2Equiv hA u)
      rw [MulEquiv.apply_symm_apply]
    rw [h'] at h
    exact h
  by_contra hno
  have hcon : ∀ u : C0 σ, β u = u → (∃ n : ℕ, u ^ (ℓ ^ n) = 1) → u * x = x * u := by
    intro u hu hp
    by_contra hne
    exact hno ⟨u, hu, hp, hne⟩
  set xy : C0 σ := y * x * y⁻¹ with hxy
  have hβe_x : (β ^ e) x = x := by
    rcases he with rfl | rfl
    · simpa using hxβ
    · have h := congrArg (fun z => β⁻¹ z) hxβ
      simpa using h.symm
  have hβe_eq : β ^ e = MulAut.conj y⁻¹ * φs * MulAut.conj y := by
    rw [show φs = MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ from rfl, ← hconj]
    rw [map_inv]
    group
  have hxy_fix : φs xy = xy := by
    have hφeq : φs = MulAut.conj y * β ^ e * MulAut.conj y⁻¹ := by
      rw [show φs = MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ from rfl]
      exact hconj.symm
    rw [hxy, hφeq]
    change y * (β ^ e) (y⁻¹ * (y * x * y⁻¹) * y) * y⁻¹ = y * x * y⁻¹
    have hyx : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    rw [hyx, hβe_x]
  have hxy3 : xy ^ 3 = 1 := by
    rw [hxy]
    change ((MulAut.conj y) x) ^ 3 = 1
    rw [← map_pow (MulAut.conj y) x 3, hx3, map_one]
  have hxy_ne : xy ≠ 1 := by
    intro h
    apply hx1
    rw [hxy] at h
    have h' : y⁻¹ * (y * x * y⁻¹) * y = 1 := by
      simpa using congrArg (fun z => y⁻¹ * z * y) h
    have hx1' : x = 1 := by
      calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
        _ = 1 := h'
    exact hx1'
  have hxy_comm : ∀ v ∈ Us, v * xy = xy * v := by
    intro v hv
    have h := comm_conj_of_fold (hA := hA) (φs := φs) (β := β) (y := y) (x := x)
      (e := e) (ℓ := ℓ) he hβe_eq hβe_x U' hUsp hUsfix hcon hv
    simpa [hxy] using h
  exact hxy_ne (fold_fixed_centralizer_trivial hA hℓ hℓ3 hf rfl φs hφs hxy_fix hxy3 hxy_comm)

end CFSG.LieType.SeitzGeneration.ExcWideThree.A2Uni

module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddPlusTools
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddA2FixedUni
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.CentralizerLongSub
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF3
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311c2
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.Twist
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddBBridge
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddBSL2
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddOpen

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.TriXPlus

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.Fischer CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartTwo.Sec19 CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
  CFSG.HardMathSupport.Seitz.TrialityOdd.Inner CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.CentL
open CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
open CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.Disconnected.AschTight.S19F
open scoped commutatorElement MatrixGroups

section Generic

variable {Γ G : Type*} [Group Γ] [Group G]

theorem conj_apply_aut (τ : MulAut G) (a : G) :
    MulAut.conj (τ a) = τ * MulAut.conj a * τ⁻¹ := by
  ext z
  show τ a * z * (τ a)⁻¹ = τ (a * τ.symm z * a⁻¹)
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem apply_eq_of_commute_conj (hZ : Subgroup.center G = ⊥) {β : MulAut G} {x : G}
    (h : β * MulAut.conj x = MulAut.conj x * β) : β x = x := by
  have h1 : MulAut.conj (β x) = MulAut.conj x := by
    rw [conj_apply_aut, h, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : (β x)⁻¹ * x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun f : MulAut G => f g) h1
    simp only [MulAut.conj_apply] at this
    calc g * ((β x)⁻¹ * x) = (β x)⁻¹ * (β x * g * (β x)⁻¹) * x := by group
      _ = (β x)⁻¹ * (x * g * x⁻¹) * x := by rw [this]
      _ = (β x)⁻¹ * x * g := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at h2
  exact h2

theorem map_congr_eq_self {E : Subgroup (MulAut G)} {β : MulAut G}
    (h : ∀ e ∈ E, β * e = e * β) : E.map (MulAut.congr β).toMonoidHom = E := by
  have hfix : ∀ e ∈ E, MulAut.congr β e = e := by
    intro e he
    have hc : β * e = e * β := h e he
    apply MulEquiv.ext
    intro y
    calc (MulAut.congr β e) y = β (e (β.symm y)) := by
          simp only [MulAut.congr_apply, MulEquiv.trans_apply]
      _ = (β * e) (β.symm y) := by rw [MulAut.mul_apply]
      _ = (e * β) (β.symm y) := by rw [hc]
      _ = e y := by rw [MulAut.mul_apply, MulEquiv.apply_symm_apply]
  ext e
  constructor
  · rintro ⟨e', he', rfl⟩
    change MulAut.congr β e' ∈ E
    rw [hfix e' he']
    exact he'
  · intro he
    exact ⟨e, he, hfix e he⟩

theorem conj_conj_apply (τ : MulAut G) (k a : G) :
    ((MulAut.conj k)⁻¹ * τ * MulAut.conj k) (k⁻¹ * a * k) = k⁻¹ * τ a * k := by
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [show k * (k⁻¹ * a * k) * k⁻¹ = a by group]
  change (MulEquiv.symm (MulAut.conj k)) (τ a) = k⁻¹ * τ a * k
  rw [MulAut.conj_symm_apply]

theorem conj_mul_apply_inv (τ : MulAut G) (c : G) :
    MulAut.conj (c * τ c⁻¹) * τ = MulAut.conj c * τ * (MulAut.conj c)⁻¹ := by
  ext x
  change c * τ c⁻¹ * τ x * (c * τ c⁻¹)⁻¹ = c * τ (c⁻¹ * x * c) * c⁻¹
  rw [map_mul, map_mul, map_inv]
  group

theorem exists_conj_of_ker {A : Type*} [Group A] (Θ : MulAut G →* A)
    (hA : ∀ a b : A, a * b = b * a) (hker : Θ.ker = (MulAut.conj : G →* MulAut G).range)
    (β τ : MulAut G) : ∃ y : G, β * τ * β⁻¹ = MulAut.conj y * τ := by
  have hcomm : Θ (β * τ * β⁻¹ * τ⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    have h1 : Θ β * Θ τ = Θ τ * Θ β := hA _ _
    rw [h1]
    group
  have hmem : β * τ * β⁻¹ * τ⁻¹ ∈ Θ.ker := MonoidHom.mem_ker.2 hcomm
  rw [hker] at hmem
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, ?_⟩
  calc β * τ * β⁻¹ = (β * τ * β⁻¹ * τ⁻¹) * τ := by group
    _ = MulAut.conj y * τ := by rw [← hy]

theorem commute_of_closure_pair {E : Subgroup G} {a b c : G} (hE : E = Subgroup.closure {a, b})
    (ha : a * c = c * a) (hb : b * c = c * b) : ∀ α ∈ E, α * c = c * α := by
  subst hE
  intro α hα
  induction hα using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  | one => simp
  | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | inv x _ hx =>
    have hxc : Commute x c := hx
    exact hxc.inv_left.eq

theorem conj_mem_of_fixes {β τ : MulAut G} {c : G}
    (h : β * τ * β⁻¹ = MulAut.conj c * τ * (MulAut.conj c)⁻¹) {H : Subgroup G}
    (hH : H.map β.toMonoidHom = H) (hfix : ∀ z, τ z = z → z ∈ H) :
    ∀ z, τ z = z → c * z * c⁻¹ ∈ H := by
  intro z hz
  set d : MulAut G := β⁻¹ * MulAut.conj c with hd
  have hdτ : d * τ = τ * d := by
    have h1 : τ = d * τ * d⁻¹ := by
      have h2 := congrArg (fun f : MulAut G => β⁻¹ * f * β) h
      rw [hd]
      calc τ = β⁻¹ * (β * τ * β⁻¹) * β := by group
        _ = β⁻¹ * (MulAut.conj c * τ * (MulAut.conj c)⁻¹) * β := h2
        _ = (β⁻¹ * MulAut.conj c) * τ * (β⁻¹ * MulAut.conj c)⁻¹ := by group
    calc d * τ = (d * τ * d⁻¹) * d := by group
      _ = τ * d := by rw [← h1]
  have hdz : τ (d z) = d z := by
    have h2 := congrArg (fun f : MulAut G => f z) hdτ
    simp only [MulAut.mul_apply] at h2
    rw [hz] at h2
    exact h2.symm
  have hdzH : d z ∈ H := hfix _ hdz
  have hβ : β (d z) ∈ H := by
    have h3 : β (d z) ∈ H.map β.toMonoidHom :=
      Subgroup.mem_map_of_mem β.toMonoidHom hdzH
    rwa [hH] at h3
  change (MulAut.conj c) z ∈ H
  rw [show MulAut.conj c = β * d by rw [hd]; group]
  simpa using hβ

theorem eq_top_of_map_conj_comap (φ : Γ ≃* G) (n : Γ) {H : Subgroup G}
    (h : (H.comap φ.toMonoidHom).map (MulAut.conj n).toMonoidHom = ⊤) : H = ⊤ := by
  have h1 : H.comap φ.toMonoidHom = ⊤ := by
    have h' : Subgroup.map (MulAut.conj n).toMonoidHom (⊤ : Subgroup Γ) = ⊤ := by
      rw [Subgroup.map_top]
      exact MonoidHom.range_eq_top.2 (MulAut.conj n).surjective
    refine Subgroup.map_injective (f := (MulAut.conj n).toMonoidHom)
      (MulAut.conj n).injective ?_
    rw [h']
    exact h
  rw [eq_top_iff]
  intro z _
  obtain ⟨w, rfl⟩ := φ.surjective z
  have hw : w ∈ H.comap φ.toMonoidHom := by rw [h1]; exact Subgroup.mem_top w
  rwa [Subgroup.mem_comap] at hw

end Generic

theorem five_le_pow {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) : 5 ≤ ℓ ^ f := by
  have h5 : 5 ≤ ℓ := by
    by_contra h
    have h2 := hℓ.two_le
    interval_cases ℓ
    · exact hℓ2 rfl
    · exact hℓ3 rfl
    · norm_num at hℓ
  calc 5 ≤ ℓ := h5
    _ = ℓ ^ 1 := (pow_one ℓ).symm
    _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf

theorem exists_outer_fixed
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (E : Subgroup (MulAut (C0 σ)))
    (x : C0 σ) (hE : CFSG.IsElementaryAbelian 3 E) (hcard : Nat.card E = 3 ^ 2)
    (hout : ¬ E ≤ innerAut (C0 σ)) (hnG : ¬ TriOddHasGLine σ E) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hcx : MulAut.conj x ∈ E) :
    ∃ β ∈ E, β ∉ innerAut (C0 σ) ∧ β ^ 3 = 1 ∧ β ≠ 1 ∧ ¬ TriOddIsGLine σ β
      ∧ β x = x := by
  classical
  obtain ⟨bet, hbetE, hbetout⟩ : ∃ bet ∈ E, bet ∉ innerAut (C0 σ) := by
    by_contra h
    apply hout
    intro e he
    by_contra hne
    exact h ⟨e, he, hne⟩
  have hbet3 : bet ^ 3 = 1 :=
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E) bet hbetE
  have hbet1 : bet ≠ 1 := fun h => hbetout (h ▸ Subgroup.one_mem _)
  have hbetG : ¬ TriOddIsGLine σ bet := fun h => hnG ⟨bet, hbetE, h⟩
  have hZ : Subgroup.center (C0 σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot (t := TwistTag.D4) σ.surjective
  have hcomm : (⟨bet, hbetE⟩ : E) * ⟨MulAut.conj x, hcx⟩ =
      ⟨MulAut.conj x, hcx⟩ * ⟨bet, hbetE⟩ := hE.is_comm.comm _ _
  have hcomm' : bet * MulAut.conj x = MulAut.conj x * bet := congrArg Subtype.val hcomm
  exact ⟨bet, hbetE, hbetout, hbet3, hbet1, hbetG, apply_eq_of_commute_conj hZ hcomm'⟩

theorem exists_conj_eq_slShort
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (x : C0 σ) (hX : TriOddIsClassX σ x) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (t : Kˣ) (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) :
    ∃ g : C0 σ, g * x * g⁻¹ = triOddEqRoot σ (triOdd_ringChar_ne_two hℓ hℓ2 hf hK)
      (triOdd_two_le_pow hℓ hf) hK hσ (slShort σ.toRingHom hσ3 (HSL t)) := by
  classical
  let ε₀ := triOddEqRoot σ (triOdd_ringChar_ne_two hℓ hℓ2 hf hK)
    (triOdd_two_le_pow hℓ hf) hK hσ
  change ∃ g : C0 σ, g * x * g⁻¹ = ε₀ (slShort σ.toRingHom hσ3 (HSL t))
  obtain ⟨h, hh⟩ := hX
  obtain ⟨M, hM⟩ := triOdd_Asub_eq_eqRoot_slShort σ hℓ hℓ2 hℓ3 hf hK hσ hσ3 _ hh
  have hhx3 : (h * x * h⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; group
  have hM3 : M ^ 3 = 1 := by
    apply triOdd_slShort_injective σ hσ3
    apply ε₀.injective
    rw [map_pow, map_pow, hM, hhx3, map_one, map_one]
  have hM1 : M ≠ 1 := by
    intro hM1
    rw [hM1, map_one, map_one] at hM
    apply hx1
    have h1 : h * x * h⁻¹ = 1 := hM.symm
    have h2 : x = h⁻¹ * (h * x * h⁻¹) * h := by group
    rw [h2, h1]
    group
  obtain ⟨P, hP⟩ := triOdd_sl2_conj_hsl t ht3 ht1 M hM3 hM1
  refine ⟨ε₀ (slShort σ.toRingHom hσ3 P) * h, ?_⟩
  rw [← hP, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hM]
  group

theorem longSub_le_comap
    {K : Type} [Field K] [Finite K] {ℓ : ℕ} [CharP K ℓ] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c) (t : Kˣ)
    (hnorm : (t : K) * σ.toRingHom t * σ.toRingHom (σ.toRingHom t) = 1)
    (E : Subgroup (MulAut (C0 σ))) (x : C0 σ) (hcx : MulAut.conj x ∈ E) (hx1 : x ≠ 1)
    (φ : twistedGroup σ.toRingHom ≃* C0 σ)
    (hφv : φ (slShort σ.toRingHom hσ3 (HSL t)) = x) :
    longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤
      (uniPlaneClosure ℓ E).comap φ.toMonoidHom := by
  classical
  have hZ : Subgroup.center (C0 σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot (t := TwistTag.D4) σ.surjective
  have hconj_inj : Function.Injective (MulAut.conj : C0 σ →* MulAut (C0 σ)) :=
    nf1_conj_injective hZ
  have hcx1 : MulAut.conj x ≠ 1 := fun hc => hx1 (hconj_inj (by rw [hc, map_one]))
  refine CFSG.LieType.SeitzGeneration.ExcWideThree.PlusTools.longSub_le_of_forall_mem
    hσ3 t hnorm _ ?_
  intro y hy1 hycomm
  rw [Subgroup.mem_comap]
  have hfix : MulAut.conj x (φ y) = φ y := by
    have h := congrArg φ hycomm
    rw [map_mul, map_mul, hφv] at h
    rw [MulAut.conj_apply, ← h]
    group
  refine mem_uniPlaneClosure (e := MulAut.conj x) hcx hcx1 hfix (n := 1) ?_
  rw [pow_one, ← map_pow, hy1, map_one]

theorem exists_normalizer_short
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 1)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (s : (fixedField σ.toRingHom)ˣ) (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) (t : Kˣ)
    (ht : t = Units.map (fixedField σ.toRingHom).subtype.toMonoidHom s)
    (hnorm : (t : K) * σ.toRingHom t * σ.toRingHom (σ.toRingHom t) = 1)
    (E : Subgroup (MulAut (C0 σ))) (x : C0 σ) (bet : MulAut (C0 σ)) (hbetE : bet ∈ E)
    (hbet3 : bet ^ 3 = 1) (hbetout : bet ∉ innerAut (C0 σ))
    (hbetG : ¬ TriOddIsGLine σ bet) (hbetx : bet x = x) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (ε₀ : twistedGroup σ.toRingHom ≃* C0 σ) (g : C0 σ)
    (φ : twistedGroup σ.toRingHom ≃* C0 σ)
    (hφ_apply : ∀ w, φ w = g⁻¹ * ε₀ w * g)
    (hφv : φ (slShort σ.toRingHom hσ3 (HSL t)) = x)
    (H : Subgroup (C0 σ)) (hH : H = uniPlaneClosure ℓ E)
    (H' : Subgroup (twistedGroup σ.toRingHom)) (hH' : H' = H.comap φ.toMonoidHom)
    (hLle : longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H') :
    ∃ n ∈ Subgroup.normalizer
        (longSub 6 (hexGroup (twistedX σ.toRingHom)) : Set (twistedGroup σ.toRingHom)),
      longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H'.map (MulAut.conj n).toMonoidHom ∧
      (d4X hσ3 2 (1 : K) ∈ H'.map (MulAut.conj n).toMonoidHom ∨
        d4X hσ3 4 (1 : K) ∈ H'.map (MulAut.conj n).toMonoidHom) := by
  classical
  obtain ⟨u, hubet, huPow, hux⟩ :=
    CFSG.LieType.SeitzGeneration.ExcWideThree.A2Uni.exists_unipotent_fixed_not_commute
      hℓ hℓ2 hℓ3 hf hq hK σ hσ bet hbet3 hbetout hbetG x hx3 hx1 hbetx
  obtain ⟨m, hum⟩ := huPow
  have hbet1 : bet ≠ 1 := fun h => hbetout (h ▸ Subgroup.one_mem _)
  have huH : u ∈ H := by
    rw [hH]
    exact mem_uniPlaneClosure (e := bet) hbetE hbet1 hubet (n := m) hum
  set u' : twistedGroup σ.toRingHom := ε₀.symm (g * u * g⁻¹) with hu'def
  have hφu' : φ u' = u := by
    rw [hu'def, hφ_apply, MulEquiv.apply_symm_apply]
    group
  have hu'H : u' ∈ H' := by
    rw [hH', Subgroup.mem_comap]
    change φ u' ∈ H
    rw [hφu']
    exact huH
  have hu'pow : u' ^ (ℓ ^ m) = 1 := by
    rw [hu'def, ← map_pow]
    have h1 : (g * u * g⁻¹) ^ (ℓ ^ m) = 1 := by
      rw [conj_pow, hum]
      group
    rw [h1, map_one]
  have hu'nc : u' * slShort σ.toRingHom hσ3 (HSL t) ≠
      slShort σ.toRingHom hσ3 (HSL t) * u' := by
    intro hc
    apply hux
    have h := congrArg φ hc
    rwa [map_mul, map_mul, hφu', hφv] at h
  have hℓodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have hu'N : u' ∉ Subgroup.normalizer
      (longSub 6 (hexGroup (twistedX σ.toRingHom)) : Set (twistedGroup σ.toRingHom)) :=
    CFSG.LieType.SeitzGeneration.ExcWideThree.PlusTools.not_mem_normalizer_of_not_commute
      σ hσ3 s hs3 hs1 t ht hℓodd u' hu'pow hu'nc
  exact CFSG.LieType.SeitzGeneration.ExcWideThree.PlusTools.exists_conj_short_mem
    σ hσ3 H' hLle u' hu'H hu'N ⟨s, fun h => hs1 (Units.ext h)⟩

theorem chart_hΦ
    (ℓ f : ℕ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 1)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (E : Subgroup (MulAut (C0 σ))) (x : C0 σ) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hcx : MulAut.conj x ∈ E)
    (s : (fixedField σ.toRingHom)ˣ) (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    (t : Kˣ) (ht : t = Units.map (fixedField σ.toRingHom).subtype.toMonoidHom s)
    (hnorm : (t : K) * σ.toRingHom t * σ.toRingHom (σ.toRingHom t) = 1)
    (g : C0 σ)
    (ε₀ : twistedGroup σ.toRingHom ≃* C0 σ)
    (heps : ε₀ = triOddEqRoot σ (triOdd_ringChar_ne_two hℓ hℓ2 hf hK)
      (triOdd_two_le_pow hℓ hf) hK hσ)
    (hgz : g * x * g⁻¹ = ε₀ (slShort σ.toRingHom hσ3 (HSL t)))
    (φ : twistedGroup σ.toRingHom ≃* C0 σ)
    (hφ_apply : ∀ w, φ w = g⁻¹ * ε₀ w * g)
    (hφv : φ (slShort σ.toRingHom hσ3 (HSL t)) = x)
    (H : Subgroup (C0 σ)) (H' : Subgroup (twistedGroup σ.toRingHom))
    (hH' : H' = H.comap φ.toMonoidHom)
    (n : twistedGroup σ.toRingHom)
    (hnN : n ∈ Subgroup.normalizer
      (longSub 6 (hexGroup (twistedX σ.toRingHom)) : Set (twistedGroup σ.toRingHom)))
    (H₁ : Subgroup (twistedGroup σ.toRingHom))
    (hH₁ : H₁ = H'.map (MulAut.conj n).toMonoidHom) :
    ∃ k : C0 σ,
      (∀ w, w ∈ H₁ ↔ k⁻¹ * ε₀ w * k ∈ H) ∧
      (∀ w, k⁻¹ * ε₀ w * k = φ (n⁻¹ * w * n)) ∧
      (k⁻¹ * ε₀ (slShort σ.toRingHom hσ3 (HSL t)) * k = x ∨
        k⁻¹ * ε₀ (slShort σ.toRingHom hσ3 (HSL t)) * k = x⁻¹) := by
  classical
  set v : twistedGroup σ.toRingHom := slShort σ.toRingHom hσ3 (HSL t) with hvv
  set k : C0 σ := ε₀ n * g with hk
  have hΦH : ∀ w, w ∈ H₁ ↔ k⁻¹ * ε₀ w * k ∈ H := by
    intro w
    rw [hH₁, Subgroup.mem_map]
    constructor
    · rintro ⟨h, hh, rfl⟩
      have hh' : φ h ∈ H := by rwa [hH', Subgroup.mem_comap] at hh
      change k⁻¹ * ε₀ (n * h * n⁻¹) * k ∈ H
      have e : k⁻¹ * ε₀ (n * h * n⁻¹) * k = φ h := by
        rw [hφ_apply, hk]
        rw [map_mul, map_mul, map_inv, mul_inv_rev]
        simp only [mul_assoc, inv_mul_cancel_left]
      rw [e]
      exact hh'
    · intro hw
      refine ⟨n⁻¹ * w * n, ?_, ?_⟩
      · rw [hH', Subgroup.mem_comap]
        change φ (n⁻¹ * w * n) ∈ H
        have e : φ (n⁻¹ * w * n) = k⁻¹ * ε₀ w * k := by
          rw [hφ_apply, hk]
          rw [map_mul, map_mul, map_inv]
          group
        rw [e]
        exact hw
      · show n * (n⁻¹ * w * n) * n⁻¹ = w
        group
  have hkφ : ∀ w, k⁻¹ * ε₀ w * k = φ (n⁻¹ * w * n) := by
    intro w
    rw [hφ_apply, hk]
    rw [map_mul, map_mul, map_inv]
    group
  have hΦv : k⁻¹ * ε₀ v * k = x ∨ k⁻¹ * ε₀ v * k = x⁻¹ := by
    rcases CFSG.LieType.SeitzGeneration.ExcWideThree.PlusTools.conj_eq_or_eq_inv_of_mem_normalizer
      σ hσ3 s hs3 hs1 t ht n hnN with h | h
    · left
      rw [hkφ, show n⁻¹ * v * n = v by
        calc n⁻¹ * v * n = n⁻¹ * (n * v * n⁻¹) * n := by rw [h]
          _ = v := by group]
      exact hφv
    · right
      have hv' : n⁻¹ * v⁻¹ * n = v := by
        calc n⁻¹ * v⁻¹ * n = n⁻¹ * (n * v * n⁻¹) * n := by rw [h]
          _ = v := by group
      have h1 : k⁻¹ * ε₀ (v⁻¹) * k = x := by
        rw [hkφ, hv']
        exact hφv
      have h2 : k⁻¹ * ε₀ v * k = (k⁻¹ * ε₀ (v⁻¹) * k)⁻¹ := by
        rw [map_inv]
        group
      rw [h2, h1]
  exact ⟨k, hΦH, hkφ, hΦv⟩

theorem chart_tau
    (ℓ f : ℕ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 1)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (s : (fixedField σ.toRingHom)ˣ)
    (t : Kˣ) (ht : t = Units.map (fixedField σ.toRingHom).subtype.toMonoidHom s)
    (k : C0 σ) (ε₀ : twistedGroup σ.toRingHom ≃* C0 σ)
    (heps : ε₀ = triOddEqRoot σ (triOdd_ringChar_ne_two hℓ hℓ2 hf hK)
      (triOdd_two_le_pow hℓ hf) hK hσ) :
    ∃ τ' : MulAut (C0 σ),
      τ' = (MulAut.conj k)⁻¹ * tauAut σ * MulAut.conj k ∧
      (∀ w, τ' (k⁻¹ * ε₀ w * k) = k⁻¹ * ε₀ w * k ↔ w ∈ FixedSub σ) ∧
      (∀ M : Matrix.SpecialLinearGroup (Fin 2) K,
        τ' (k⁻¹ * ε₀ (slShort σ.toRingHom hσ3 M) * k) =
          k⁻¹ * ε₀ (slShort σ.toRingHom hσ3
            (Matrix.SpecialLinearGroup.map σ.toRingHom M)) * k) ∧
      TriOddIsGLine σ τ' := by
  classical
  have hK2 : ringChar K ≠ 2 := triOdd_ringChar_ne_two hℓ hℓ2 hf hK
  have hq2 : 2 ≤ ℓ ^ f := triOdd_two_le_pow hℓ hf
  subst heps
  set ε₀ := triOddEqRoot σ hK2 hq2 hK hσ with hε₀
  let τ' : MulAut (C0 σ) := (MulAut.conj k)⁻¹ * tauAut σ * MulAut.conj k
  have hτ'k : ∀ w, τ' (k⁻¹ * ε₀ w * k) = k⁻¹ * tauAut σ (ε₀ w) * k := by
    intro w
    have hk1 : k * (k⁻¹ * ε₀ w * k) * k⁻¹ = ε₀ w := by group
    simp only [τ', MulAut.mul_apply, MulAut.conj_apply, inv_inv]
    rw [hk1]
    change (MulAut.conj k).symm (tauAut σ (ε₀ w)) = k⁻¹ * tauAut σ (ε₀ w) * k
    rw [MulAut.conj_symm_apply]
  have hτ'Φ : ∀ w, τ' (k⁻¹ * ε₀ w * k) = k⁻¹ * ε₀ w * k ↔ w ∈ FixedSub σ := by
    intro w
    rw [hτ'k w]
    constructor
    · intro h
      have h' : tauAut σ (ε₀ w) = ε₀ w := by
        calc tauAut σ (ε₀ w) = k * (k⁻¹ * tauAut σ (ε₀ w) * k) * k⁻¹ := by group
          _ = k * (k⁻¹ * ε₀ w * k) * k⁻¹ := by rw [h]
          _ = ε₀ w := by group
      exact (CFSG.LieType.SeitzGeneration.ExcWideThree.PlusTools.tauAut_eqRoot_eq_iff
        σ hσ3 hK2 hq2 hK hσ w).1 h'
    · intro hw
      rw [(CFSG.LieType.SeitzGeneration.ExcWideThree.PlusTools.tauAut_eqRoot_eq_iff
        σ hσ3 hK2 hq2 hK hσ w).2 hw]
  have hτ'_sl : ∀ M : Matrix.SpecialLinearGroup (Fin 2) K,
      τ' (k⁻¹ * ε₀ (slShort σ.toRingHom hσ3 M) * k) =
        k⁻¹ * ε₀ (slShort σ.toRingHom hσ3
          (Matrix.SpecialLinearGroup.map σ.toRingHom M)) * k := by
    intro M
    rw [hτ'k, CFSG.LieType.SeitzGeneration.ExcWideThree.PlusTools.tauAut_eqRoot_slShort
      σ hσ3 hK2 hq2 hK hσ M]
  have hτ'G : TriOddIsGLine σ τ' := by
    refine ⟨MulAut.conj k, Or.inl ?_⟩
    simp only [τ', MulAut.mul_apply]
    group
  exact ⟨τ', rfl, hτ'Φ, hτ'_sl, hτ'G⟩

theorem beta_facts
    (ℓ f : ℕ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 1)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (E : Subgroup (MulAut (C0 σ))) (hE : CFSG.IsElementaryAbelian 3 E)
    (bet : MulAut (C0 σ)) (hbetE : bet ∈ E) (x : C0 σ) (hbetx : bet x = x)
    (s : (fixedField σ.toRingHom)ˣ)
    (t : Kˣ) (ht : t = Units.map (fixedField σ.toRingHom).subtype.toMonoidHom s)
    (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1)
    (hnorm : (t : K) * σ.toRingHom t * σ.toRingHom (σ.toRingHom t) = 1)
    (φ : twistedGroup σ.toRingHom ≃* C0 σ)
    (hφv : φ (slShort σ.toRingHom hσ3 (HSL t)) = x)
    (H : Subgroup (C0 σ)) (hH : H = uniPlaneClosure ℓ E) :
    H.map bet.toMonoidHom = H ∧
      (∀ z, z ∈ (longSub 6 (hexGroup (twistedX σ.toRingHom))).map φ.toMonoidHom ↔
        bet.symm z ∈ (longSub 6 (hexGroup (twistedX σ.toRingHom))).map φ.toMonoidHom) := by
  classical
  have hEfix : E.map (MulAut.congr bet).toMonoidHom = E := by
    apply map_congr_eq_self
    intro e he
    exact congrArg Subtype.val (hE.is_comm.comm (⟨bet, hbetE⟩ : E) ⟨e, he⟩)
  have hHβ : H.map bet.toMonoidHom = H := by
    have hmc := uniPlaneClosure_map_congr bet ℓ E
    rw [hEfix, ← hH] at hmc
    exact hmc.symm
  have hK2 : ringChar K ≠ 2 := triOdd_ringChar_ne_two hℓ hℓ2 hf hK
  have hq2 : 2 ≤ ℓ ^ f := triOdd_two_le_pow hℓ hf
  have ht2 : (t : K) ^ 2 ≠ 1 := by
    intro h2
    have htunit2 : t ^ 2 = 1 := by
      apply Units.ext
      simpa using h2
    have ht1' : t = 1 := by
      have e : t = t ^ 3 * (t ^ 2)⁻¹ := by group
      rw [ht3, htunit2, inv_one, mul_one] at e
      exact e
    exact ht1 ht1'
  set v : twistedGroup σ.toRingHom := slShort σ.toRingHom hσ3 (HSL t) with hvv
  let betb : MulAut (twistedGroup σ.toRingHom) := (φ.trans bet).trans φ.symm
  have hbetbv : betb v = v := by
    apply φ.injective
    have h1 : φ (betb v) = bet (φ v) := by
      simp only [betb, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [h1, hφv]
    exact hbetx
  have hbetbL : (longSub 6 (hexGroup (twistedX σ.toRingHom))).map betb.toMonoidHom =
      longSub 6 (hexGroup (twistedX σ.toRingHom)) :=
    CFSG.LieType.SeitzGeneration.ExcWideThree.PlusTools.map_longSub_eq_of_fix
      σ hσ3 hK2 hq2 hK hσ t hnorm ht2 betb hbetbv
  have hcomp : bet.toMonoidHom.comp φ.toMonoidHom = φ.toMonoidHom.comp betb.toMonoidHom := by
    apply MonoidHom.ext
    intro w
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, betb, MulEquiv.trans_apply,
      MulEquiv.apply_symm_apply]
  have hbetΦL :
      ((longSub 6 (hexGroup (twistedX σ.toRingHom))).map φ.toMonoidHom).map
        bet.toMonoidHom =
      (longSub 6 (hexGroup (twistedX σ.toRingHom))).map φ.toMonoidHom := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hbetbL]
  refine ⟨hHβ, ?_⟩
  intro z
  have h1 : z ∈ ((longSub 6 (hexGroup (twistedX σ.toRingHom))).map
      φ.toMonoidHom).map bet.toMonoidHom ↔
      bet.symm z ∈ (longSub 6 (hexGroup (twistedX σ.toRingHom))).map φ.toMonoidHom :=
    Subgroup.mem_map_equiv
  rwa [hbetΦL] at h1

theorem exists_normal_form_data
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    ∃ Θ : MulAut (C0 σ) →* (K ≃+* K),
      Θ.ker = (MulAut.conj : C0 σ →* MulAut (C0 σ)).range ∧ IsCyclic (K ≃+* K) := by
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -, -, -, -⟩ :=
    odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hK σ hσ
  exact ⟨Θ, hker, hcyc⟩

theorem centralizer_y
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (L : Subgroup (twistedGroup σ.toRingHom))
    (hL : L = longSub 6 (hexGroup (twistedX σ.toRingHom))) (n : twistedGroup σ.toRingHom)
    (hnN : n ∈ Subgroup.normalizer L) (φ : twistedGroup σ.toRingHom ≃* C0 σ) (k : C0 σ)
    (ε₀ : twistedGroup σ.toRingHom ≃* C0 σ) (bet : MulAut (C0 σ)) (τ' : MulAut (C0 σ))
    (y : C0 σ) (hy' : bet * τ' * bet⁻¹ = MulAut.conj y * τ')
    (hτ'Φ : ∀ w, τ' (k⁻¹ * ε₀ w * k) = k⁻¹ * ε₀ w * k ↔ w ∈ FixedSub σ)
    (hβΦL_iff : ∀ z, z ∈ L.map φ.toMonoidHom ↔ bet.symm z ∈ L.map φ.toMonoidHom)
    (hkφ : ∀ w, k⁻¹ * ε₀ w * k = φ (n⁻¹ * w * n)) :
    ∀ w ∈ L, y * (k⁻¹ * ε₀ w * k) * y⁻¹ = k⁻¹ * ε₀ w * k := by
  intro w hw
  have hw₀ : w ∈ longSub 6 (hexGroup (twistedX σ.toRingHom)) := by rwa [hL] at hw
  have hfix_w : τ' (k⁻¹ * ε₀ w * k) = k⁻¹ * ε₀ w * k :=
    (hτ'Φ w).2
      (CFSG.LieType.SeitzGeneration.ExcWideThree.PlusTools.longSub_le_fixedSub σ hσ3 hw₀)
  have hfix_bw : τ' (bet.symm (k⁻¹ * ε₀ w * k)) = bet.symm (k⁻¹ * ε₀ w * k) := by
    have hn'N : n⁻¹ ∈ Subgroup.normalizer L := (Subgroup.normalizer _).inv_mem hnN
    have hwn : n⁻¹ * w * n ∈ L := by
      have h := (Subgroup.mem_normalizer_iff.1 hn'N w).1 hw
      simpa only [inv_inv] using h
    have hmem : k⁻¹ * ε₀ w * k ∈ L.map φ.toMonoidHom := by
      rw [hkφ w]
      exact Subgroup.mem_map_of_mem φ.toMonoidHom hwn
    obtain ⟨w', hw'L, hw'⟩ := Subgroup.mem_map.1 ((hβΦL_iff _).1 hmem)
    have hwn' : n * w' * n⁻¹ ∈ L := by
      have h := (Subgroup.mem_normalizer_iff.1 hnN w').1 hw'L
      simpa only [inv_inv] using h
    have hchart : k⁻¹ * ε₀ (n * w' * n⁻¹) * k = bet.symm (k⁻¹ * ε₀ w * k) := by
      rw [hkφ (n * w' * n⁻¹)]
      have e : n⁻¹ * (n * w' * n⁻¹) * n = w' := by group
      rw [e]
      exact hw'
    have hfix := (hτ'Φ (n * w' * n⁻¹)).2
      (CFSG.LieType.SeitzGeneration.ExcWideThree.PlusTools.longSub_le_fixedSub σ hσ3
        (by rwa [hL] at hwn'))
    rwa [hchart] at hfix
  have happ := congrArg (fun f : MulAut (C0 σ) => f (k⁻¹ * ε₀ w * k)) hy'
  simp only [MulAut.mul_apply] at happ
  rw [show (bet⁻¹ : MulAut (C0 σ)) = bet.symm from rfl] at happ
  rw [hfix_bw, hfix_w] at happ
  have happ' : k⁻¹ * ε₀ w * k = y * (k⁻¹ * ε₀ w * k) * y⁻¹ := by
    rw [MulEquiv.apply_symm_apply, MulAut.conj_apply] at happ
    exact happ
  exact happ'.symm

theorem exists_torus_of_centralizer
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (n : twistedGroup σ.toRingHom) (φ : twistedGroup σ.toRingHom ≃* C0 σ) (y : C0 σ)
    (hy₀cen : n * φ.symm y * n⁻¹ ∈ Subgroup.centralizer
      (longSub 6 (hexGroup (twistedX σ.toRingHom)) : Set (twistedGroup σ.toRingHom))) :
    ∃ t' : Kˣ, (t' : K) * σ.toRingHom t' * σ.toRingHom (σ.toRingHom t') = 1 ∧
      n * φ.symm y * n⁻¹ = slShort σ.toRingHom hσ3 (HSL t') := by
  exact CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.CentL.centralizer_longSub
    (σ := σ.toRingHom) hσ3 (five_le_pow hℓ hℓ2 hℓ3 hf) hK hσ _ hy₀cen

theorem exists_lang_conj
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (k : C0 σ) (ε₀ : twistedGroup σ.toRingHom ≃* C0 σ)
    (hε₀ : ε₀ = triOddEqRoot σ (triOdd_ringChar_ne_two hℓ hℓ2 hf hK)
      (triOdd_two_le_pow hℓ hf) hK hσ) (n : twistedGroup σ.toRingHom)
    (φ : twistedGroup σ.toRingHom ≃* C0 σ) (bet τ' : MulAut (C0 σ)) (y : C0 σ)
    (hy' : bet * τ' * bet⁻¹ = MulAut.conj y * τ')
    (hτ'def : τ' = (MulAut.conj k)⁻¹ * tauAut σ * MulAut.conj k)
    (hkφ : ∀ w, k⁻¹ * ε₀ w * k = φ (n⁻¹ * w * n))
    (t' : Kˣ) (ht'norm : (t' : K) * σ.toRingHom t' * σ.toRingHom (σ.toRingHom t') = 1)
    (hyt' : n * φ.symm y * n⁻¹ = slShort σ.toRingHom hσ3 (HSL t')) :
    ∃ g₀ : Matrix.SpecialLinearGroup (Fin 2) K,
      bet * τ' * bet⁻¹ =
        MulAut.conj (k⁻¹ * ε₀ (slShort σ.toRingHom hσ3 g₀) * k) * τ' *
          (MulAut.conj (k⁻¹ * ε₀ (slShort σ.toRingHom hσ3 g₀) * k))⁻¹ ∧
      (Matrix.SpecialLinearGroup.map σ.toRingHom g₀ = g₀ → bet * τ' = τ' * bet) := by
  classical
  have hq2 : 2 ≤ ℓ ^ f := triOdd_two_le_pow hℓ hf
  have hσpow3 : σ ^ 3 = 1 := triOdd_sigma_pow_three σ (ℓ ^ f) hK hσ
  have hσne1 : σ ≠ 1 := triOdd_sigma_ne_one σ (ℓ ^ f) hq2 hK hσ
  have hHSL : HSL t' * Matrix.SpecialLinearGroup.map σ.toRingHom (HSL t') *
      Matrix.SpecialLinearGroup.map σ.toRingHom
        (Matrix.SpecialLinearGroup.map σ.toRingHom (HSL t')) = 1 := by
    rw [CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.mapSL_HSL,
      CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.mapSL_HSL,
      CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.HSL_mul',
      CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.HSL_mul']
    have hu : t' * Units.map σ.toMonoidHom t' *
        Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t') = 1 := by
      apply Units.ext
      simpa using ht'norm
    rw [hu, CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.HSL_one']
  obtain ⟨g₀, hg₀⟩ := sl2_lang_general σ hσpow3 hσne1 (HSL t') hHSL
  let ĝ : C0 σ := k⁻¹ * ε₀ (slShort σ.toRingHom hσ3 g₀) * k
  have hτ'ĝ : τ' ĝ = k⁻¹ * ε₀ (slShort σ.toRingHom hσ3
      (Matrix.SpecialLinearGroup.map σ.toRingHom g₀)) * k := by
    rw [hτ'def, conj_conj_apply, hε₀,
      CFSG.LieType.SeitzGeneration.ExcWideThree.PlusTools.tauAut_eqRoot_slShort
        σ hσ3 (triOdd_ringChar_ne_two hℓ hℓ2 hf hK) (triOdd_two_le_pow hℓ hf) hK hσ g₀]
  let y₀ : twistedGroup σ.toRingHom := n * φ.symm y * n⁻¹
  have hyΦ : y = k⁻¹ * ε₀ y₀ * k := by
    rw [hkφ y₀]
    have e : n⁻¹ * y₀ * n = φ.symm y := by
      change n⁻¹ * (n * φ.symm y * n⁻¹) * n = φ.symm y
      group
    rw [e, MulEquiv.apply_symm_apply]
  have hy_exp' : y = ĝ * τ' ĝ⁻¹ := by
    rw [hyΦ]
    change k⁻¹ * ε₀ (n * φ.symm y * n⁻¹) * k = ĝ * τ' ĝ⁻¹
    rw [hyt', hg₀]
    simp only [map_mul, map_inv]
    have e : k⁻¹ * (ε₀ (slShort σ.toRingHom hσ3 g₀) *
        (ε₀ (slShort σ.toRingHom hσ3
          (Matrix.SpecialLinearGroup.map σ.toRingHom g₀)))⁻¹) * k =
        (k⁻¹ * ε₀ (slShort σ.toRingHom hσ3 g₀) * k) *
          (k⁻¹ * ε₀ (slShort σ.toRingHom hσ3
            (Matrix.SpecialLinearGroup.map σ.toRingHom g₀)) * k)⁻¹ := by group
    rw [e, hτ'ĝ]
  have hbetτ : bet * τ' * bet⁻¹ = MulAut.conj ĝ * τ' * (MulAut.conj ĝ)⁻¹ := by
    rw [hy']
    calc MulAut.conj y * τ' = MulAut.conj (ĝ * τ' ĝ⁻¹) * τ' := by rw [hy_exp']
      _ = MulAut.conj ĝ * τ' * (MulAut.conj ĝ)⁻¹ := conj_mul_apply_inv τ' ĝ
  refine ⟨g₀, hbetτ, ?_⟩
  intro hfixg
  have hHSL1 : HSL t' = 1 := by rw [hg₀, hfixg, mul_inv_cancel]
  have hy1 : y = 1 := by
    rw [hyΦ]
    change k⁻¹ * ε₀ (n * φ.symm y * n⁻¹) * k = 1
    rw [hyt', hHSL1, map_one, map_one]
    group
  calc bet * τ' = (bet * τ' * bet⁻¹) * bet := by group
    _ = τ' * bet := by rw [hy', hy1, map_one, one_mul]

theorem closing_fixed
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (E : Subgroup (MulAut (C0 σ))) (bet : MulAut (C0 σ)) (x : C0 σ)
    (hcard : Nat.card E = 3 ^ 2) (hbetE : bet ∈ E)
    (hbetout : bet ∉ innerAut (C0 σ)) (hcx : MulAut.conj x ∈ E) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (k : C0 σ) (ε₀ : twistedGroup σ.toRingHom ≃* C0 σ)
    (v : twistedGroup σ.toRingHom) (τ' : MulAut (C0 σ))
    (hΦv : k⁻¹ * ε₀ v * k = x ∨ k⁻¹ * ε₀ v * k = x⁻¹)
    (hτ'Φ : ∀ w, τ' (k⁻¹ * ε₀ w * k) = k⁻¹ * ε₀ w * k ↔ w ∈ FixedSub σ)
    (hτ'G : TriOddIsGLine σ τ') (hτ'bet : τ' * bet = bet * τ')
    (hvL : v ∈ longSub 6 (hexGroup (twistedX σ.toRingHom)))
    (hncent : ∀ γ : MulAut (C0 σ), TriOddIsGLine σ γ → ¬ ∀ α ∈ E, α * γ = γ * α) :
    False := by
  classical
  have hZ : Subgroup.center (C0 σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot (t := TwistTag.D4) σ.surjective
  have hinj : Function.Injective (MulAut.conj : C0 σ →* MulAut (C0 σ)) :=
    nf1_conj_injective hZ
  have hcx1 : MulAut.conj x ≠ 1 := by
    intro hc
    apply hx1
    exact hinj (by rw [hc, map_one])
  have hτ'x : τ' x = x := by
    have hfix : τ' (k⁻¹ * ε₀ v * k) = k⁻¹ * ε₀ v * k :=
      (hτ'Φ v).2
        (CFSG.LieType.SeitzGeneration.ExcWideThree.PlusTools.longSub_le_fixedSub σ hσ3 hvL)
    rcases hΦv with h | h
    · rwa [h] at hfix
    · rw [h] at hfix
      have h2 := congrArg (fun z => z⁻¹) hfix
      simpa using h2
  have hτ'cx : MulAut.conj x * τ' = τ' * MulAut.conj x := by
    have h1 := conj_apply_aut τ' x
    rw [hτ'x] at h1
    calc MulAut.conj x * τ' = (τ' * MulAut.conj x * τ'⁻¹) * τ' := by rw [← h1]
      _ = τ' * MulAut.conj x := by group
  have hbet1 : bet ≠ 1 := fun h => hbetout (h ▸ Subgroup.one_mem _)
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcx3 : MulAut.conj x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hbet_cx : bet ≠ MulAut.conj x := fun h =>
    hbetout (h ▸ (⟨x, rfl⟩ : MulAut.conj x ∈ innerAut (C0 σ)))
  have hbet_cx2 : bet ≠ MulAut.conj x ^ 2 := by
    intro h
    apply hbetout
    rw [h]
    exact ⟨x ^ 2, by rw [map_pow]⟩
  have hEcl : E = Subgroup.closure ({MulAut.conj x, bet} : Set (MulAut (C0 σ))) :=
    nf1_closure_pair_eq E hcard hcx hbetE hcx1 hcx3 hbet1 hbet_cx hbet_cx2
  have hcommE : ∀ α ∈ E, α * τ' = τ' * α :=
    commute_of_closure_pair hEcl hτ'cx hτ'bet.symm
  exact hncent τ' hτ'G hcommE

theorem closing_moving
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (bet τ' : MulAut (C0 σ)) (g₀ : Matrix.SpecialLinearGroup (Fin 2) K)
    (ε₀ : twistedGroup σ.toRingHom ≃* C0 σ) (k : C0 σ)
    (H : Subgroup (C0 σ)) (H₁ : Subgroup (twistedGroup σ.toRingHom))
    (hJle : FixedSub σ ≤ H₁)
    (hbetτ : bet * τ' * bet⁻¹ =
      MulAut.conj (k⁻¹ * ε₀ (slShort σ.toRingHom hσ3 g₀) * k) * τ' *
        (MulAut.conj (k⁻¹ * ε₀ (slShort σ.toRingHom hσ3 g₀) * k))⁻¹)
    (hHβ : H.map bet.toMonoidHom = H)
    (hΦH : ∀ w, w ∈ H₁ ↔ k⁻¹ * ε₀ w * k ∈ H)
    (hτ'Φ : ∀ w, τ' (k⁻¹ * ε₀ w * k) = k⁻¹ * ε₀ w * k ↔ w ∈ FixedSub σ)
    (hfixg : Matrix.SpecialLinearGroup.map σ.toRingHom g₀ ≠ g₀)
    (h3 : Module.finrank (fixedField σ.toRingHom) K = 3)
    (hF5 : 5 ≤ Nat.card (fixedField σ.toRingHom)) (hK2 : ringChar K ≠ 2) :
    H₁ = ⊤ := by
  classical
  let ĝ : C0 σ := k⁻¹ * ε₀ (slShort σ.toRingHom hσ3 g₀) * k
  have hfixH : ∀ z, τ' z = z → z ∈ H := by
    intro z hz
    let w : twistedGroup σ.toRingHom := ε₀.symm (k * z * k⁻¹)
    have hchart : k⁻¹ * ε₀ w * k = z := by
      change k⁻¹ * ε₀ (ε₀.symm (k * z * k⁻¹)) * k = z
      rw [MulEquiv.apply_symm_apply]
      group
    have hw : w ∈ FixedSub σ := by
      apply (hτ'Φ w).1
      rwa [hchart]
    have hwH₁ : w ∈ H₁ := hJle hw
    have hmem := (hΦH w).1 hwH₁
    rwa [hchart] at hmem
  have hconjH : ∀ z, τ' z = z → ĝ * z * ĝ⁻¹ ∈ H :=
    conj_mem_of_fixes hbetτ hHβ hfixH
  have hconj_mem : ∀ w ∈ FixedSub σ, slShort σ.toRingHom hσ3 g₀ * w *
      (slShort σ.toRingHom hσ3 g₀)⁻¹ ∈ H₁ := by
    intro w hw
    have hz : τ' (k⁻¹ * ε₀ w * k) = k⁻¹ * ε₀ w * k := (hτ'Φ w).2 hw
    have hmem := hconjH _ hz
    rw [hΦH (slShort σ.toRingHom hσ3 g₀ * w * (slShort σ.toRingHom hσ3 g₀)⁻¹)]
    have e : k⁻¹ * ε₀ (slShort σ.toRingHom hσ3 g₀ * w *
          (slShort σ.toRingHom hσ3 g₀)⁻¹) * k = ĝ * (k⁻¹ * ε₀ w * k) * ĝ⁻¹ := by
      rw [show ĝ = k⁻¹ * ε₀ (slShort σ.toRingHom hσ3 g₀) * k from rfl]
      simp only [map_mul, map_inv]
      group
    rw [e]
    exact hmem
  obtain ⟨M, hMnot⟩ :=
    CFSG.LieType.SeitzGeneration.ExcWideThree.PlusTools.exists_conj_not_mem_sl2Range
      σ h3 g₀ hfixg
  set j : Matrix.SpecialLinearGroup (Fin 2) K :=
    g₀ * Matrix.SpecialLinearGroup.map (algebraMap (fixedField σ.toRingHom) K) M * g₀⁻¹
    with hj
  have hfixM : Matrix.SpecialLinearGroup.map σ.toRingHom
      (Matrix.SpecialLinearGroup.map (algebraMap (fixedField σ.toRingHom) K) M) =
      Matrix.SpecialLinearGroup.map (algebraMap (fixedField σ.toRingHom) K) M := by
    refine Subtype.ext ?_
    ext i c
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    exact (M i c).2
  have hsj : slShort σ.toRingHom hσ3 j ∈ H₁ := by
    have hmul : slShort σ.toRingHom hσ3 j =
        slShort σ.toRingHom hσ3 g₀ *
          slShort σ.toRingHom hσ3
            (Matrix.SpecialLinearGroup.map (algebraMap (fixedField σ.toRingHom) K) M) *
          (slShort σ.toRingHom hσ3 g₀)⁻¹ := by
      rw [hj, map_mul, map_mul, map_inv]
    rw [hmul]
    exact hconj_mem _ (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.slShort_mem_FixedSub
      σ hσ3 _ hfixM)
  exact CFSG.LieType.SeitzGeneration.ExcWideThree.PlusTools.eq_top_of_fixedSub_le_of_slShort_mem
    σ hσ3 hK2 h3 hF5 H₁ hJle j hMnot hsj

theorem centralizer_y0
    {K : Type} [Field K] (σ : K ≃+* K)
    (L : Subgroup (twistedGroup σ.toRingHom)) (n : twistedGroup σ.toRingHom)
    (φ : twistedGroup σ.toRingHom ≃* C0 σ) (k : C0 σ)
    (ε₀ : twistedGroup σ.toRingHom ≃* C0 σ) (y : C0 σ)
    (hycen : ∀ w ∈ L, y * (k⁻¹ * ε₀ w * k) * y⁻¹ = k⁻¹ * ε₀ w * k)
    (hkφ : ∀ w, k⁻¹ * ε₀ w * k = φ (n⁻¹ * w * n)) :
    n * φ.symm y * n⁻¹ ∈ Subgroup.centralizer L := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h := hycen w hw
  have hc : y * φ (n⁻¹ * w * n) * y⁻¹ = φ (n⁻¹ * w * n) := by
    rw [← hkφ w]
    exact h
  have hc2 : φ.symm y * (n⁻¹ * w * n) * (φ.symm y)⁻¹ = n⁻¹ * w * n := by
    have h2 := congrArg φ.symm hc
    rw [map_mul, map_mul, map_inv] at h2
    rw [MulEquiv.symm_apply_apply] at h2
    exact h2
  have hc3 : (n⁻¹ * w * n) * φ.symm y = φ.symm y * (n⁻¹ * w * n) := by
    have h3 : φ.symm y * (n⁻¹ * w * n) = (n⁻¹ * w * n) * φ.symm y := by
      calc φ.symm y * (n⁻¹ * w * n) =
          (φ.symm y * (n⁻¹ * w * n) * (φ.symm y)⁻¹) * φ.symm y := by group
        _ = (n⁻¹ * w * n) * φ.symm y := by rw [hc2]
    exact h3.symm
  calc w * (n * φ.symm y * n⁻¹) = n * (n⁻¹ * w * n) * (φ.symm y) * n⁻¹ := by group
    _ = n * ((n⁻¹ * w * n) * φ.symm y) * n⁻¹ := by group
    _ = n * (φ.symm y * (n⁻¹ * w * n)) * n⁻¹ := by rw [hc3]
    _ = (n * φ.symm y * n⁻¹) * w := by group

theorem exists_cube_torus
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 1)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    ∃ (s : (fixedField σ.toRingHom)ˣ) (t : Kˣ),
      s ^ 3 = 1 ∧ s ≠ 1 ∧
      t = Units.map (fixedField σ.toRingHom).subtype.toMonoidHom s ∧
      t ^ 3 = 1 ∧ t ≠ 1 ∧
      (t : K) * σ.toRingHom t * σ.toRingHom (σ.toRingHom t) = 1 := by
  classical
  have hq2 : 2 ≤ ℓ ^ f := triOdd_two_le_pow hℓ hf
  have hFcard : Nat.card (fixedField σ.toRingHom) = ℓ ^ f :=
    card_fixedField_of_cube σ.toRingHom hq2 hK hσ
  have h3dvd : 3 ∣ ℓ ^ f - 1 := by
    obtain ⟨k, hk⟩ : ∃ k, ℓ ^ f = 3 * k + 1 := by
      refine ⟨ℓ ^ f / 3, ?_⟩
      have hdm := Nat.div_add_mod (ℓ ^ f) 3
      omega
    exact ⟨k, by omega⟩
  obtain ⟨s, hs3, hs1⟩ := CFSG.HardMathSupport.Lang.E6Descent.exists_cube_root_unit_finite
    (K := fixedField σ.toRingHom) (by rw [hFcard]; exact h3dvd)
  set t : Kˣ := Units.map (fixedField σ.toRingHom).subtype.toMonoidHom s with ht
  have htK : (t : K) = ((s : fixedField σ.toRingHom) : K) := by rw [ht]; rfl
  have htσ : σ.toRingHom (t : K) = t := by
    rw [htK]
    exact (s : fixedField σ.toRingHom).2
  have ht3 : t ^ 3 = 1 := by rw [ht, ← map_pow, hs3, map_one]
  have ht1 : t ≠ 1 := by
    intro h
    apply hs1
    apply Units.ext
    apply Subtype.ext
    rw [← htK, h]
    rfl
  have hnorm : (t : K) * σ.toRingHom t * σ.toRingHom (σ.toRingHom t) = 1 := by
    rw [htσ, htσ]
    have := congrArg Units.val ht3
    simpa [pow_succ, mul_assoc] using this
  exact ⟨s, t, hs3, hs1, rfl, ht3, ht1, hnorm⟩

theorem uniPlaneClosure_eq_top_of_fixedSub
    (ℓ f : ℕ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hq : (ℓ ^ f) % 3 = 1)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (E : Subgroup (MulAut (C0 σ))) (x : C0 σ)
    (hE : CFSG.IsElementaryAbelian 3 E) (hcard : Nat.card E = 3 ^ 2)
    (hout : ¬ E ≤ innerAut (C0 σ)) (hnG : ¬ TriOddHasGLine σ E)
    (hncent : ∀ γ : MulAut (C0 σ), TriOddIsGLine σ γ → ¬ ∀ α ∈ E, α * γ = γ * α)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hcx : MulAut.conj x ∈ E)
    (hX : TriOddIsClassX σ x)
    (hbp : ∀ ψ : MulAut (C0 σ), ¬ ∀ φ ∈ E.map (MulAut.congr ψ).toMonoidHom,
      ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom =
        (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧
      ((graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom =
        (graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hN2 : ∀ (hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
      (H : Subgroup (twistedGroup σ.toRingHom)),
      longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H →
      (d4X hσ3 2 (1 : K) ∈ H ∨ d4X hσ3 4 (1 : K) ∈ H) → FixedSub σ ≤ H) :
    uniPlaneClosure ℓ E = ⊤ := by
  classical
  have hK2 : ringChar K ≠ 2 := triOdd_ringChar_ne_two hℓ hℓ2 hf hK
  have hq2 : 2 ≤ ℓ ^ f := triOdd_two_le_pow hℓ hf
  have hq5 : 5 ≤ ℓ ^ f := five_le_pow hℓ hℓ2 hℓ3 hf
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c :=
    sigma_three_of_card (σ := σ.toRingHom) hK hσ
  have hFcard : Nat.card (fixedField σ.toRingHom) = ℓ ^ f :=
    card_fixedField_of_cube σ.toRingHom hq2 hK hσ
  have h3 : Module.finrank (fixedField σ.toRingHom) K = 3 := by
    have h := Module.natCard_eq_pow_finrank (K := fixedField σ.toRingHom) (V := K)
    rw [hK, hFcard] at h
    exact (Nat.pow_right_injective (by omega : 2 ≤ ℓ ^ f) h).symm
  have hF5 : 5 ≤ Nat.card (fixedField σ.toRingHom) := by rw [hFcard]; exact hq5
  obtain ⟨bet, hbetE, hbetout, hbet3, hbet1, hbetG, hbetx⟩ :=
    exists_outer_fixed σ E x hE hcard hout hnG hx3 hx1 hcx
  obtain ⟨s, t, hs3, hs1, ht, ht3, ht1, hnorm⟩ :=
    exists_cube_torus σ hℓ hℓ2 hf hq hK hσ
  set ε₀ : twistedGroup σ.toRingHom ≃* C0 σ :=
    triOddEqRoot σ hK2 hq2 hK hσ with hε₀
  obtain ⟨g, hgz⟩ :=
    exists_conj_eq_slShort σ hℓ hℓ2 hℓ3 hf hK hσ hσ3 x hX hx3 hx1 t ht3 ht1
  let φ : twistedGroup σ.toRingHom ≃* C0 σ := ε₀.trans (MulAut.conj g⁻¹)
  have hφ_apply : ∀ w, φ w = g⁻¹ * ε₀ w * g := by
    intro w
    simp only [φ, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  have hφv : φ (slShort σ.toRingHom hσ3 (HSL t)) = x := by
    rw [hφ_apply, ← hgz]
    group
  set H : Subgroup (C0 σ) := uniPlaneClosure ℓ E with hHdef
  set H' : Subgroup (twistedGroup σ.toRingHom) := H.comap φ.toMonoidHom with hH'
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  have hLle : longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H' := by
    rw [hH', hHdef]
    exact longSub_le_comap σ hσ3 t hnorm E x hcx hx1 φ hφv
  obtain ⟨n, hnN, hLH₁, hshort⟩ :=
    exists_normalizer_short σ hℓ hℓ2 hℓ3 hf hq hK hσ hσ3 s hs3 hs1 t ht hnorm E x bet
      hbetE hbet3 hbetout hbetG hbetx hx3 hx1 ε₀ g φ hφ_apply hφv H hHdef H' hH' hLle
  set H₁ : Subgroup (twistedGroup σ.toRingHom) := H'.map (MulAut.conj n).toMonoidHom with hH₁
  have hJle : FixedSub σ ≤ H₁ := hN2 hσ3 H₁ hLH₁ hshort
  obtain ⟨k, hΦH, hkφ, hΦv⟩ :=
    chart_hΦ ℓ f hℓ hℓ2 hf hq hK σ hσ hσ3 E x hE hcard hx3 hx1 hcx s hs3 hs1 t ht hnorm
      g ε₀ hε₀ hgz φ hφ_apply hφv H H' hH' n hnN H₁ hH₁
  obtain ⟨τ', hτ'def, hτ'Φ, hτ'_sl, hτ'G⟩ :=
    chart_tau ℓ f hℓ hℓ2 hf hq hK σ hσ hσ3 s t ht k ε₀ hε₀
  obtain ⟨hHβ, hβΦL_iff⟩ :=
    beta_facts ℓ f hℓ hℓ2 hf hq hK σ hσ hσ3 E hE bet hbetE x hbetx s t ht ht3 ht1
      hnorm φ hφv H hHdef
  obtain ⟨Θ, hker, hcyc⟩ := exists_normal_form_data σ hℓ hℓ2 hf hK hσ
  have hcycComm : ∀ a b : K ≃+* K, a * b = b * a := by
    letI : CommGroup (K ≃+* K) := hcyc.commGroup
    intro a b
    exact mul_comm a b
  obtain ⟨y, hy'⟩ := exists_conj_of_ker Θ hcycComm hker bet τ'
  let L : Subgroup (twistedGroup σ.toRingHom) :=
    longSub 6 (hexGroup (twistedX σ.toRingHom))
  have hycen : ∀ w ∈ L, y * (k⁻¹ * ε₀ w * k) * y⁻¹ = k⁻¹ * ε₀ w * k :=
    centralizer_y σ hσ3 L rfl n hnN φ k ε₀ bet τ' y hy' hτ'Φ hβΦL_iff hkφ
  have hy₀cen : n * φ.symm y * n⁻¹ ∈ Subgroup.centralizer L :=
    centralizer_y0 σ L n φ k ε₀ y hycen hkφ
  obtain ⟨t', ht'norm, hyt'⟩ :=
    exists_torus_of_centralizer σ hσ3 hℓ hℓ2 hℓ3 hf hK hσ n φ y hy₀cen
  obtain ⟨g₀, hbetτ, hcond⟩ :=
    exists_lang_conj σ hℓ hℓ2 hf hK hσ hσ3 k ε₀ hε₀ n φ bet τ' y hy' hτ'def hkφ t'
      ht'norm hyt'
  have hvL : slShort σ.toRingHom hσ3 (HSL t) ∈
      longSub 6 (hexGroup (twistedX σ.toRingHom)) := by
    have := CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.slShort_HSL_fixed_mem_longSub
      (σ := σ.toRingHom) hσ3 s
    rwa [← ht] at this
  by_cases hfixg : Matrix.SpecialLinearGroup.map σ.toRingHom g₀ = g₀
  · exact (closing_fixed σ hσ3 E bet x hcard hbetE hbetout hcx hx3 hx1 k ε₀
      (slShort σ.toRingHom hσ3 (HSL t)) τ' hΦv hτ'Φ hτ'G (hcond hfixg).symm hvL hncent).elim
  · have hH₁top : H₁ = ⊤ :=
      closing_moving σ hσ3 bet τ' g₀ ε₀ k H H₁ hJle hbetτ hHβ hΦH hτ'Φ hfixg h3 hF5 hK2
    exact eq_top_of_map_conj_comap φ n (by rw [← hH', ← hH₁]; exact hH₁top)
end CFSG.LocalAnalysis.GLTheoremB.MovingAround.TriXPlus

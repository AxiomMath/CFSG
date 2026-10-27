module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBNonSwap
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapUnique

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.OddStandard.Seitz77 (Datum)
open CFSG.SeitzReduction.LinearPilot (linearSwapDiag linearSwapDiag_apply
  ker_linearSwapDiag_le_center range_linearSwapDiag_le_centralizer
  card_quotient_center_le_card_range_linearSwapDiag conjugate_le_centralizer_of_le_centralizer
  isQuasisimple_conjugate isQuasisimple_map_conj map_conj_conjugate_eq
  card_quotient_center_eq_of_swapFactors conjugateQuotientCenterEquiv
  eq_top_of_sup_center_eq_top_of_perfect)
open scoped commutatorElement

section W

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G} {q : ℕ}

theorem WData.eq_sup_of_lift (w : WData d Vi q) {R : Subgroup G}
    (hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) (hR2 : ∀ x ∈ R, x * x = 1)
    (hRt : ∀ x ∈ R, ∀ y ∈ R, x * (d.t * y * d.t) = d.t * y * d.t * x)
    (hδ : ∀ r ∈ R, r * (d.t * r * d.t) ∈ Vi) (honto : ∀ v ∈ Vi, ∃ r ∈ R, r * (d.t * r * d.t) = v)
    (hinf : R ⊓ R.map (MulAut.conj d.t).toMonoidHom = ⊥) (hcard : Nat.card R * Nat.card R = q ^ 4) :
    w.W = R ⊔ R.map (MulAut.conj d.t).toMonoidHom := by
  have htt := d.t_mul_self
  have tt : ∀ z : G, d.t * (d.t * z * d.t) * d.t = z := fun z => by
    rw [show d.t * (d.t * z * d.t) * d.t = (d.t * d.t) * z * (d.t * d.t) by group, htt, one_mul,
      mul_one]
  set Rt := R.map (MulAut.conj d.t).toMonoidHom with hRtdef
  have hmemRt : ∀ {y : G}, y ∈ Rt ↔ d.t * y * d.t ∈ R := fun {y} => mem_map_conj_iff htt
  have hc : ∀ x ∈ R, ∀ y ∈ Rt, x * y = y * x := by
    intro x hx y hy
    have h := hRt x hx _ (hmemRt.1 hy)
    rwa [tt] at h
  have hRtc : ∀ x ∈ Rt, ∀ y ∈ Rt, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hRc x hx y hy]
  have hC : R ⊔ Rt ≤ centralizer (Vi : Set G) := by
    refine sup_le (fun x hx => mem_centralizer_iff.2 fun v hv => ?_)
      fun y hy => mem_centralizer_iff.2 fun v hv => ?_
    · obtain ⟨r, hr, rfl⟩ := honto v hv
      have h1 := hRc x hx r hr
      have h2 := hRt x hx r hr
      calc r * (d.t * r * d.t) * x = r * x * (d.t * r * d.t) := by rw [mul_assoc, ← h2, ← mul_assoc]
        _ = x * (r * (d.t * r * d.t)) := by rw [← h1, mul_assoc]
    · obtain ⟨r, hr, rfl⟩ := honto v hv
      have h1 := hc r hr y hy
      have hrt : d.t * r * d.t ∈ Rt := hmemRt.2 (by rw [tt]; exact hr)
      have h2 := hRtc y hy _ hrt
      calc r * (d.t * r * d.t) * y = r * y * (d.t * r * d.t) := by rw [mul_assoc, ← h2, ← mul_assoc]
        _ = y * (r * (d.t * r * d.t)) := by rw [h1, mul_assoc]
  set E := Vi ⊔ zpowers d.t with hE
  have htE : d.t ∈ normalizer (E : Set G) := le_normalizer (mem_sup_right (mem_zpowers d.t))
  have hRE : R ≤ normalizer (E : Set G) := by
    intro r hr
    refine CaseBModule.mem_normalizer_of_map_le ?_
    rw [hE, Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le (fun _ ⟨v, hv, hvr⟩ => ?_) (zpowers_le.2 ?_)
    · rw [← hvr, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        ← (mem_centralizer_iff.1 (hC (mem_sup_left hr)) v hv), mul_inv_cancel_right]
      exact mem_sup_left hv
    · have hrr : r⁻¹ = r := inv_eq_of_mul_eq_one_right (hR2 r hr)
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hrr,
        show r * d.t * r = r * (d.t * r * d.t) * d.t by simp only [mul_assoc, htt, mul_one]]
      exact mul_mem (mem_sup_left (hδ r hr)) (mem_sup_right (mem_zpowers d.t))
  have hN : R ⊔ Rt ≤ normalizer (E : Set G) := by
    refine sup_le hRE fun x hx => ?_
    rw [← tt x]
    exact mul_mem (mul_mem htE (hRE (hmemRt.1 hx))) htE
  have hab : ∀ a ∈ R ⊔ Rt, ∀ b ∈ R ⊔ Rt, a * b = b * a := by
    have hle : R ⊔ Rt ≤ centralizer ((R ⊔ Rt : Subgroup G) : Set G) := by
      refine sup_le ?_ ?_
      · rw [le_centralizer_iff]
        exact sup_le (fun x hx => mem_centralizer_iff.2 fun y hy => hRc y hy x hx)
          fun y hy => mem_centralizer_iff.2 fun x hx => hc x hx y hy
      · rw [le_centralizer_iff]
        exact sup_le (fun x hx => mem_centralizer_iff.2 fun y hy => (hc x hx y hy).symm)
          fun y hy => mem_centralizer_iff.2 fun x hx => hRtc x hx y hy
    exact fun a ha b hb => mem_centralizer_iff.1 (hle hb) a ha
  refine (w.unique _ ?_ hab ?_).symm
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hR2' : IsPGroup 2 R := fun x => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one, sq]; exact hR2 x x.2)⟩
    refine w.le_sup_of_isPGroup _ (IsPGroup.to_sup_of_normal_left' hR2' (hR2'.map _)
      fun y hy => Subgroup.mem_normalizer_fintype fun x hx => ?_) (le_inf hN hC)
    rw [← hc x hx y hy, mul_inv_cancel_right]
    exact hx
  · rw [card_sup_of_commute hc hinf, hRtdef,
      Subgroup.card_map_of_injective (MulAut.conj d.t).injective, hcard]

end W

section Swap

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}

omit [Finite G] in
theorem mul_conj_inv_eq {t : G} (htt : t * t = 1) (x : G) :
    x * (t * x * t⁻¹) = x * (t * x * t) := by
  rw [inv_eq_of_mul_eq_one_right htt]

theorem Hyp.eq_one_of_mem_inf (h : Hyp G A f) (d : Datum A) {G₁ : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (d.t * x * d.t) ∈ A)
    (hsurj : ∀ y ∈ A, ∃ x ∈ G₁, x * (d.t * x * d.t) = y) {z : G}
    (hz : z ∈ G₁ ⊓ G₁.map (MulAut.conj d.t).toMonoidHom) (hz2 : z * z = 1) : z = 1 := by
  have htt := d.t_mul_self
  obtain ⟨hz1, hz2'⟩ := hz
  have hzG₁ : ∀ x ∈ G₁, z * x = x * z := fun x hx =>
    (mem_centralizer_iff.1 (h₁₂ hz2') x hx).symm
  have hzG₂ : ∀ x ∈ G₁, z * (d.t * x * d.t) = d.t * x * d.t * z := fun x hx =>
    mem_centralizer_iff.1 (h₁₂ (conj_mem_map_conj htt hx)) z hz1
  have hzA : z ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨x, hx, rfl⟩ := hsurj a ha
    calc x * (d.t * x * d.t) * z = x * (z * (d.t * x * d.t)) := by rw [mul_assoc, ← hzG₂ x hx]
      _ = z * (x * (d.t * x * d.t)) := by rw [← mul_assoc, ← hzG₁ x hx, mul_assoc]
  have htA : d.t ∈ centralizer (A : Set G) := d.t_mem_K
  have hδz : z * (d.t * z * d.t) = 1 := by
    have hmem : z * (d.t * z * d.t) ∈ A ⊓ centralizer (A : Set G) :=
      ⟨hδ z hz1, mul_mem hzA (mul_mem (mul_mem htA hzA) htA)⟩
    rw [h.facts.center_eq_bot, mem_bot] at hmem
    exact hmem
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hztz : d.t * z * d.t = z := by
    rw [eq_inv_of_mul_eq_one_right hδz, hzinv]
  have hzt : z * d.t = d.t * z := by
    calc z * d.t = d.t * z * d.t * d.t := by rw [hztz]
      _ = d.t * z := by rw [mul_assoc, htt, mul_one]
  by_contra hz1'
  have hzz : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1'
  have hc : ∀ x ∈ zpowers z, ∀ y ∈ zpowers d.t, x * y = y * x := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ((Commute.zpow_zpow (show Commute z d.t from hzt) i j)).eq
  have hsq : ∀ {x : G} (y : G), y * y = 1 → x ∈ zpowers y → x * x = 1 := by
    rintro x y hy ⟨i, rfl⟩
    show y ^ i * y ^ i = 1
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hy, one_zpow]
  set H := zpowers z ⊔ zpowers d.t with hH
  have hHC : H ≤ centralizer (A : Set G) := sup_le (zpowers_le.2 hzA) (zpowers_le.2 htA)
  have hH2 : ∀ x ∈ H, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hc hx
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hc a ha b hb]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [hsq z hz2 ha, hsq d.t htt hb, one_mul]
  have hcard := h.card_le_two_of_le_centralizer hHC hH2
  have hzH : zpowers z = H := Subgroup.eq_of_le_of_card_ge le_sup_left
    (by rw [Nat.card_zpowers, hzz]; exact hcard)
  have htz : d.t ∈ zpowers z := hzH ▸ mem_sup_right (mem_zpowers d.t)
  have htG₁ : d.t ∈ G₁ := by
    obtain ⟨i, hi⟩ := htz
    change z ^ i = d.t at hi
    rw [← zpow_mod_orderOf, hzz] at hi
    have h01 : i % (2 : ℕ) = 0 ∨ i % (2 : ℕ) = 1 := by omega
    rcases h01 with h0 | h0
    · rw [h0, zpow_zero] at hi
      exact absurd hi.symm (by
        intro h1
        have := d.sector.t_order
        rw [h1, orderOf_one] at this
        exact absurd this (by norm_num))
    · rw [h0, zpow_one] at hi
      rw [← hi]
      exact hz1
  obtain ⟨hperf, hbot, -⟩ := SeitzReduction.F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hq
  have hG₂ : G₁.map (MulAut.conj d.t).toMonoidHom = G₁ :=
    SeitzReduction.F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.1 (le_normalizer htG₁)
  rw [hG₂] at h₁₂
  exact hbot (by rw [← hperf, commutator_eq_bot_iff_le_centralizer.2 h₁₂])

theorem Hyp.exists_cover (h : Hyp G A f) (d : Datum A) {K : Type} [Field K]
    (e : A ≃* projectiveSL 3 K) {G₁ : Subgroup G} (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (d.t * x * d.t) ∈ A)
    (hsurj : ∀ y ∈ A, ∃ x ∈ G₁, x * (d.t * x * d.t) = y) :
    ∃ π : G₁ →* projectiveSL 3 K, Function.Surjective π ∧ π.ker ≤ center G₁ ∧
      Odd (Nat.card π.ker) := by
  have htt := d.t_mul_self
  set δ := linearSwapDiag h₁₂ with hδdef
  have hδapp : ∀ x : G₁, δ x = x * (d.t * x * d.t) := fun x => by
    rw [hδdef, linearSwapDiag_apply, mul_conj_inv_eq htt]
  have hδA : ∀ x : G₁, δ x ∈ A := fun x => by rw [hδapp]; exact hδ x x.2
  set π : G₁ →* projectiveSL 3 K := e.toMonoidHom.comp (δ.codRestrict A hδA) with hπdef
  have hπ : ∀ x, π x = e ⟨δ x, hδA x⟩ := fun x => rfl
  have hπker : ∀ x, x ∈ π.ker ↔ δ x = 1 := by
    intro x
    rw [MonoidHom.mem_ker, hπ]
    constructor
    · intro hx
      have : (⟨δ x, hδA x⟩ : A) = 1 := e.injective (by rw [map_one]; exact hx)
      exact congrArg Subtype.val this
    · intro hx
      have : (⟨δ x, hδA x⟩ : A) = 1 := Subtype.ext hx
      rw [this, map_one]
  refine ⟨π, ?_, fun x hx =>
    ker_linearSwapDiag_le_center h₁₂ (MonoidHom.mem_ker.2 ((hπker x).1 hx)), ?_⟩
  · intro p
    obtain ⟨x, hx, hxy⟩ := hsurj _ (e.symm p).2
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [hπ]
    have : (⟨δ ⟨x, hx⟩, hδA _⟩ : A) = e.symm p := Subtype.ext ((hδapp ⟨x, hx⟩).trans hxy)
    rw [this, MulEquiv.apply_symm_apply]
  · have hinv : ∀ x ∈ π.ker, x * x = 1 → x = 1 := by
      intro x hx hx2
      have h1 : (x : G) * (d.t * x * d.t) = 1 := by rw [← hδapp]; exact (hπker x).1 hx
      have hx2' : (x : G) * x = 1 := by rw [← Subgroup.coe_mul, hx2, Subgroup.coe_one]
      have hxinv : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_right hx2'
      have h2 : d.t * x * d.t = x := by
        rw [eq_inv_of_mul_eq_one_right h1, hxinv]
      have hmem : (x : G) ∈ G₁ ⊓ G₁.map (MulAut.conj d.t).toMonoidHom :=
        ⟨x.2, (mem_map_conj_iff htt).2 (by rw [h2]; exact x.2)⟩
      exact Subtype.ext (h.eq_one_of_mem_inf d hq h₁₂ hδ hsurj hmem hx2')
    by_contra hev
    have h2 : 2 ∣ Nat.card π.ker := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hev)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) 2 h2
    have hy2 : (y : G₁) * y = 1 := by
      rw [← Subgroup.coe_mul, ← sq, ← hy, pow_orderOf_eq_one, Subgroup.coe_one]
    have hy1 := hinv y y.2 hy2
    have : y = 1 := Subtype.ext hy1
    rw [this, orderOf_one] at hy
    exact absurd hy (by norm_num)

theorem exists_cover_map {G P : Type*} [Group G] [Group P] {X : Subgroup G} (g : G)
    (h : ∃ π : X →* P, Function.Surjective π ∧ π.ker ≤ center X ∧ Odd (Nat.card π.ker)) :
    ∃ π : X.map (MulAut.conj g).toMonoidHom →* P, Function.Surjective π ∧
      π.ker ≤ center (X.map (MulAut.conj g).toMonoidHom) ∧ Odd (Nat.card π.ker) := by
  obtain ⟨π, hπ, hker, hodd⟩ := h
  set ε := X.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  refine ⟨π.comp ε.symm.toMonoidHom, hπ.comp ε.symm.surjective, fun x hx => ?_, ?_⟩
  · have h1 : ε.symm x ∈ center X := hker hx
    rw [mem_center_iff] at h1 ⊢
    intro y
    apply ε.symm.injective
    rw [map_mul, map_mul, h1]
  · have : Nat.card (π.comp ε.symm.toMonoidHom).ker = Nat.card π.ker :=
      Nat.card_congr (Equiv.subtypeEquiv ε.symm.toEquiv fun x => by
        rw [MonoidHom.mem_ker, MonoidHom.mem_ker]; rfl)
    rw [this]
    exact hodd

theorem Hyp.eq_one_of_mem_conjugate_inf (h : Hyp G A f) (d : Datum A) {G₁ : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (d.t * x * d.t) ∈ A)
    (hsurj : ∀ y ∈ A, ∃ x ∈ G₁, x * (d.t * x * d.t) = y) (g : G) {z : G}
    (hz : z ∈ CFSG.conjugate G₁ g ⊓ CFSG.conjugate (G₁.map (MulAut.conj d.t).toMonoidHom) g)
    (hz2 : z * z = 1) : z = 1 := by
  obtain ⟨hzA, hzB⟩ := hz
  have h1 : g * z * g⁻¹ ∈ G₁ := SeitzReduction.F4Pilot.mem_conjugate_iff_of_mul.1 hzA
  have h2 : g * z * g⁻¹ ∈ G₁.map (MulAut.conj d.t).toMonoidHom :=
    SeitzReduction.F4Pilot.mem_conjugate_iff_of_mul.1 hzB
  have h3 := h.eq_one_of_mem_inf d hq h₁₂ hδ hsurj ⟨h1, h2⟩ (by
    rw [show g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, hz2, mul_one,
      mul_inv_cancel])
  calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
    _ = 1 := by rw [h3, mul_one, inv_mul_cancel]

end Swap

section SwapCase

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ} {d : Datum A} {K : Type}
  [Field K] [Finite K] [CharP K 2] {F : Frame A d.V K}

omit [Finite G] in
theorem Frame.radical_facts (F : Frame A d.V K) (i : Fin 2) :
    (∀ a ∈ (projRad K i).map F.φ, ∀ b ∈ (projRad K i).map F.φ, a * b = b * a) ∧
      (∀ a ∈ (projRad K i).map F.φ, a * a = 1) ∧
      Nat.card ((projRad K i).map F.φ) = Nat.card K ^ 2 := by
  have hR := F.radicals
  have key : ∀ {E : Subgroup G}, IsElemAbelian 2 E → Nat.card E = Nat.card K ^ 2 →
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a * a = 1) ∧
        Nat.card E = Nat.card K ^ 2 := fun hE hc =>
    ⟨fun a ha b hb => congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩),
      fun a ha => by rw [← sq]; exact hE.2 a ha, hc⟩
  fin_cases i
  · exact key hR.elem₁ hR.card₁
  · exact key hR.elem₂ hR.card₂

theorem Hyp.lift_le_M_sup (h : Hyp G A f) (hKc : Nat.card K = 2 ^ f) {i : Fin 2}
    {w : WData d ((projRad K i).map F.φ) (2 ^ f)} (N : CaseBNotation w (F.leviData i))
    (hB : w.CaseB (F.leviData i).lev.range) {A' : Subgroup G}
    (hA' : A'.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (A' : Set G))
    (hinv : ∀ z ∈ A' ⊓ A'.map (MulAut.conj d.t).toMonoidHom, z * z = 1 → z = 1)
    (hker : (linearSwapDiag hA').ker ≤ center A') (hodd : Odd (Nat.card (linearSwapDiag hA').ker))
    (hrange : (linearSwapDiag hA').range = A) {X : Subgroup A'} (hXp : ⁅X, X⁆ = X)
    (hXL : X.map (linearSwapDiag hA') ≤ (F.leviData i).lev.range) :
    X.map A'.subtype ≤ N.M₁ ⊔ N.M₁.map (MulAut.conj d.t).toMonoidHom := by
  have htt := d.t_mul_self
  have hf3 := h.three_le
  set δ' := linearSwapDiag hA' with hδ'
  have hδ'app : ∀ x : A', δ' x = x * (d.t * x * d.t) := fun x => by
    rw [hδ', linearSwapDiag_apply, mul_conj_inv_eq htt]
  obtain ⟨hVic, hVi2, hVicard⟩ := F.radical_facts i
  have hViA : ((projRad K i).map F.φ) ≤ A := F.map_le _
  obtain ⟨R, hRmem⟩ := exists_liftSq hker hodd ((projRad K i).map F.φ) hVic
  have hViδ : ((projRad K i).map F.φ) ≤ (linearSwapDiag hA').range := by rw [hrange]; exact hViA
  have hRmap := map_liftSq hodd hViδ hVi2 hRmem
  have hRcard := card_liftSq hodd hViδ hVi2 hRmem
  set R' := R.map A'.subtype with hR'
  have hR'A : R' ≤ A' := map_subtype_le R
  have hR'c : ∀ x ∈ R', ∀ y ∈ R', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (comm_of_liftSq hker hodd hVic hRmem x hx y hy)
  have hR'2 : ∀ x ∈ R', x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val ((hRmem x).1 hx).2
  have hR't : ∀ x ∈ R', ∀ y ∈ R', x * (d.t * y * d.t) = d.t * y * d.t * x := by
    intro x hx y hy
    have hy' : d.t * y * d.t ∈ A'.map (MulAut.conj d.t).toMonoidHom :=
      conj_mem_map_conj htt (hR'A hy)
    exact mem_centralizer_iff.1 (hA' hy') x (hR'A hx)
  have hR'δ : ∀ r ∈ R', r * (d.t * r * d.t) ∈ ((projRad K i).map F.φ) := by
    rintro _ ⟨r, hr, rfl⟩
    have := ((hRmem r).1 hr).1
    rwa [hδ'app] at this
  have hR'onto : ∀ v ∈ ((projRad K i).map F.φ), ∃ r ∈ R', r * (d.t * r * d.t) = v := by
    intro v hv
    rw [← hRmap] at hv
    obtain ⟨r, hr, rfl⟩ := hv
    exact ⟨r, ⟨r, hr, rfl⟩, (hδ'app r).symm⟩
  have hR'inf : R' ⊓ R'.map (MulAut.conj d.t).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    exact mem_bot.2 (hinv z ⟨hR'A hz1, map_mono hR'A hz2⟩ (hR'2 z hz1))
  have hR'card : Nat.card R' * Nat.card R' = (2 ^ f) ^ 4 := by
    rw [hR', Subgroup.card_map_of_injective A'.subtype_injective, hRcard, hVicard, hKc]
    ring
  have hW := w.eq_sup_of_lift hR'c hR'2 hR't hR'δ hR'onto hR'inf hR'card
  have hXN : X.map A'.subtype ≤ w.N := by
    rintro _ ⟨x, hx, rfl⟩
    refine CaseBModule.mem_normalizer_of_map_le ?_
    rw [hW, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      have hxL : δ' x ∈ (F.leviData i).lev.range := hXL ⟨x, hx, rfl⟩
      have hxN := WData.levRange_le_normalizer (F.leviData i) hxL
      have hmem : x * r * x⁻¹ ∈ R := by
        refine (hRmem _).2 ⟨?_, ?_⟩
        · rw [map_mul, map_mul, map_inv]
          exact (mem_normalizer_iff.1 hxN _).1 ((hRmem r).1 hr).1
        · rw [show x * r * x⁻¹ * (x * r * x⁻¹) = x * (r * r) * x⁻¹ by group, ((hRmem r).1 hr).2,
            mul_one, mul_inv_cancel]
      exact mem_sup_left ⟨_, hmem, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      have hyA : y ∈ A'.map (MulAut.conj d.t).toMonoidHom := map_mono hR'A hy
      have hxy : (x : G) * y * (x : G)⁻¹ = y := by
        rw [mem_centralizer_iff.1 (hA' hyA) x x.2, mul_inv_cancel_right]
      change (x : G) * y * (x : G)⁻¹ ∈ R' ⊔ R'.map (MulAut.conj d.t).toMonoidHom
      rw [hxy]
      exact mem_sup_right hy
  have hXp' : ⁅X.map A'.subtype, X.map A'.subtype⁆ = X.map A'.subtype := by
    rw [← map_commutator, hXp]
  exact N.perfect_le_M_sup hB (by omega) hKc hXN hXp'

theorem Hyp.conjugate_eq_of_swap (h : Hyp G A f) (hKc : Nat.card K = 2 ^ f)
    {w₀ : WData d ((projRad K 0).map F.φ) (2 ^ f)} {w₁ : WData d ((projRad K 1).map F.φ) (2 ^ f)}
    (N₀ : CaseBNotation w₀ (F.leviData 0)) (N₁ : CaseBNotation w₁ (F.leviData 1))
    (hB₀ : w₀.CaseB (F.leviData 0).lev.range) (hB₁ : w₁.CaseB (F.leviData 1).lev.range)
    {G₁ : Subgroup G} (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (d.t * x * d.t) ∈ A)
    (hsurj : ∀ y ∈ A, ∃ x ∈ G₁, x * (d.t * x * d.t) = y) (hM₀ : N₀.M₁ ≤ G₁) (hM₁ : N₁.M₁ ≤ G₁)
    (g : G) (hswap : (CFSG.conjugate G₁ g).map (MulAut.conj d.t).toMonoidHom =
      CFSG.conjugate (G₁.map (MulAut.conj d.t).toMonoidHom) g) :
    CFSG.conjugate (G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom) g =
      G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom := by
  have htt := d.t_mul_self
  have hf3 := h.three_le
  set G₂ := G₁.map (MulAut.conj d.t).toMonoidHom with hG₂
  set A' := CFSG.conjugate G₁ g with hA'def
  set B' := CFSG.conjugate G₂ g with hB'def
  have hBA : B' ≤ centralizer (A' : Set G) := conjugate_le_centralizer_of_le_centralizer h₁₂ g
  have hA' : A'.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (A' : Set G) := by
    rw [hswap]; exact hBA
  have hinv : ∀ z ∈ A' ⊓ A'.map (MulAut.conj d.t).toMonoidHom, z * z = 1 → z = 1 := by
    intro z hz hz2
    rw [hswap] at hz
    exact h.eq_one_of_mem_conjugate_inf d hq h₁₂ hδ hsurj g hz hz2
  set δ' := linearSwapDiag hA' with hδ'def
  have hδ'app : ∀ x : A', δ' x = x * (d.t * x * d.t) := fun x => by
    rw [hδ'def, linearSwapDiag_apply, mul_conj_inv_eq htt]
  have hq' : CFSG.Open.IsQuasisimple A' := isQuasisimple_conjugate hq g
  have : Group.IsPerfect A' := ⟨hq'.1⟩
  have hrange : δ'.range = A := by
    have hrp : ⁅δ'.range, δ'.range⁆ = δ'.range := by
      rw [MonoidHom.range_eq_map]
      exact SeitzReduction.LinearPilot.commutator_map_eq_of_commutator_eq δ' (by
        rw [← commutator_def]
        exact Group.IsPerfect.commutator_eq_top)
    have hle : δ'.range ≤ A :=
      h.perfect_le_of_le_centralizer d hrp (range_linearSwapDiag_le_centralizer htt hA')
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hδ₁ : ∀ x ∈ G₁, x * (d.t * x * d.t⁻¹) ∈ A := fun x hx => by
      rw [mul_conj_inv_eq htt]; exact hδ x hx
    have hsurj₁ : ∀ y ∈ A, ∃ x ∈ G₁, x * (d.t * x * d.t⁻¹) = y := fun y hy => by
      obtain ⟨x, hx, hxy⟩ := hsurj y hy
      exact ⟨x, hx, by rw [mul_conj_inv_eq htt]; exact hxy⟩
    calc Nat.card A = Nat.card (G₁ ⧸ center G₁) :=
          (card_quotient_center_eq_of_swapFactors h.center_eq_bot h₁₂ hδ₁ hsurj₁).symm
      _ = Nat.card (A' ⧸ center A') := Nat.card_congr (conjugateQuotientCenterEquiv G₁ g).toEquiv
      _ ≤ Nat.card δ'.range := card_quotient_center_le_card_range_linearSwapDiag hA'
  have hker : δ'.ker ≤ center A' := ker_linearSwapDiag_le_center hA'
  have hodd : Odd (Nat.card δ'.ker) := by
    have hinv' : ∀ x ∈ δ'.ker, x * x = 1 → x = 1 := by
      intro x hx hx2
      have h1 : (x : G) * (d.t * x * d.t) = 1 := by rw [← hδ'app]; exact hx
      have hx2' : (x : G) * x = 1 := by rw [← Subgroup.coe_mul, hx2, Subgroup.coe_one]
      have hxinv : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_right hx2'
      have h2 : d.t * x * d.t = x := by
        rw [eq_inv_of_mul_eq_one_right h1, hxinv]
      have hmem : (x : G) ∈ A' ⊓ A'.map (MulAut.conj d.t).toMonoidHom :=
        ⟨x.2, (mem_map_conj_iff htt).2 (by rw [h2]; exact x.2)⟩
      exact Subtype.ext (hinv _ hmem hx2')
    by_contra hev
    have h2 : 2 ∣ Nat.card δ'.ker := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hev)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := δ'.ker) 2 h2
    have hy2 : (y : A') * y = 1 := by
      rw [← Subgroup.coe_mul, ← sq, ← hy, pow_orderOf_eq_one, Subgroup.coe_one]
    have : y = 1 := Subtype.ext (hinv' y y.2 hy2)
    rw [this, orderOf_one] at hy
    exact absurd hy (by norm_num)
  have hK3 : 3 ≤ Nat.card K := by
    rw [hKc]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlevA : ∀ i : Fin 2, (F.leviData i).lev.range ≤ δ'.range := fun i => by
    rw [hrange]
    rintro _ ⟨B, rfl⟩
    exact (F.leviData i).lev_mem B
  obtain ⟨X₀, hX₀p, hX₀map, -⟩ :=
    exists_liftPerfect hker (WData.commutator_levRange hK3 (F.leviData 0)) (hlevA 0)
  obtain ⟨X₁, hX₁p, hX₁map, -⟩ :=
    exists_liftPerfect hker (WData.commutator_levRange hK3 (F.leviData 1)) (hlevA 1)
  have hle₀ := h.lift_le_M_sup (F := F) (i := 0) hKc N₀ hB₀ hA' hinv hker hodd hrange hX₀p
    (hX₀map.le : X₀.map (linearSwapDiag hA') ≤ (F.leviData 0).lev.range)
  have hle₁ := h.lift_le_M_sup (F := F) (i := 1) hKc N₁ hB₁ hA' hinv hker hodd hrange hX₁p
    (hX₁map.le : X₁.map (linearSwapDiag hA') ≤ (F.leviData 1).lev.range)
  have hMG : ∀ {M : Subgroup G}, M ≤ G₁ →
      M ⊔ M.map (MulAut.conj d.t).toMonoidHom ≤ G₁ ⊔ G₂ := fun hM =>
    sup_le (hM.trans le_sup_left) ((map_mono hM).trans le_sup_right)
  have htop : X₀ ⊔ X₁ = ⊤ := by
    refine eq_top_of_sup_center_eq_top_of_perfect (eq_top_iff.2 fun y _ => ?_)
    have hy : δ' y ∈ (X₀ ⊔ X₁).map δ' := by
      rw [Subgroup.map_sup, hX₀map, hX₁map, F.sup_lev_range, ← hrange]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hy
    have hk : x⁻¹ * y ∈ δ'.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    rw [show y = x * (x⁻¹ * y) by group]
    exact mul_mem (mem_sup_left hx) (mem_sup_right (hker hk))
  have hA'le : A' ≤ G₁ ⊔ G₂ := by
    intro x hx
    have hmem : (⟨x, hx⟩ : A') ∈ X₀ ⊔ X₁ := htop ▸ mem_top _
    have h2 : x ∈ (X₀ ⊔ X₁).map A'.subtype := ⟨⟨x, hx⟩, hmem, rfl⟩
    rw [Subgroup.map_sup] at h2
    exact (sup_le (hle₀.trans (hMG hM₀)) (hle₁.trans (hMG hM₁))) h2
  have htG₀ : d.t ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) :=
    SeitzReduction.F4Pilot.mem_normalizer_sup_of_map_conj_eq htt rfl
  have hB'le : B' ≤ G₁ ⊔ G₂ := by
    rw [← hswap]
    calc A'.map (MulAut.conj d.t).toMonoidHom ≤
          (G₁ ⊔ G₂).map (MulAut.conj d.t).toMonoidHom := map_mono hA'le
      _ = G₁ ⊔ G₂ := SeitzReduction.F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.1 htG₀
  have hle : CFSG.conjugate (G₁ ⊔ G₂) g ≤ G₁ ⊔ G₂ := by
    rw [CFSG.conjugate, Subgroup.map_sup]
    exact sup_le hA'le hB'le
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).ge

theorem Hyp.unique_of_caseB (h : Hyp G A f) (hKc : Nat.card K = 2 ^ f)
    {w₀ : WData d ((projRad K 0).map F.φ) (2 ^ f)} {w₁ : WData d ((projRad K 1).map F.φ) (2 ^ f)}
    (N₀ : CaseBNotation w₀ (F.leviData 0)) (N₁ : CaseBNotation w₁ (F.leviData 1))
    (hB₀ : w₀.CaseB (F.leviData 0).lev.range) (hB₁ : w₁.CaseB (F.leviData 1).lev.range)
    {G₁ : Subgroup G} (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (d.t * x * d.t) ∈ A)
    (hsurj : ∀ y ∈ A, ∃ x ∈ G₁, x * (d.t * x * d.t) = y) (hM₀ : N₀.M₁ ≤ G₁) (hM₁ : N₁.M₁ ≤ G₁) :
    ∀ g : G, g⁻¹ * d.t * g ∈
        normalizer ((G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom : Subgroup G) : Set G) →
      g ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom : Subgroup G) : Set G) := by
  have hcov := h.exists_cover d F.equiv.symm hq h₁₂ hδ hsurj
  refine SeitzReduction.F4Pilot.unique_of_forall_conjugate_eq fun g htM => ?_
  set G₂ := G₁.map (MulAut.conj d.t).toMonoidHom with hG₂
  have hM : CFSG.conjugate (G₁ ⊔ G₂) g = CFSG.conjugate G₁ g ⊔ CFSG.conjugate G₂ g :=
    Subgroup.map_sup _ _ _
  rw [hM] at htM
  have hqA := isQuasisimple_conjugate hq g
  have hqB := isQuasisimple_conjugate (isQuasisimple_map_conj hq d.t) g
  have hAB := conjugate_le_centralizer_of_le_centralizer h₁₂ g
  have hBA := le_centralizer_iff.1 hAB
  obtain ⟨hpA, hbA, hnA⟩ := SeitzReduction.F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hqA
  obtain ⟨hpB, hbB, hnB⟩ := SeitzReduction.F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hqB
  rcases SeitzReduction.F4Pilot.map_conj_eq_or_eq_of_perfect hAB hpA hbA hnA hnB htM with
    hAA | hswap
  · exfalso
    rcases SeitzReduction.F4Pilot.map_conj_eq_or_eq_of_perfect hBA hpB hbB hnB hnA
        (by rw [sup_comm]; exact htM) with hBB | hBA'
    · obtain ⟨πA, hπA, hkA, hoA⟩ := exists_cover_map g⁻¹ hcov
      obtain ⟨πB, hπB, hkB, hoB⟩ := exists_cover_map g⁻¹ (exists_cover_map d.t hcov)
      exact h.false_of_nonswap d hKc πA hπA hkA hoA πB hπB hkB hoB
        (SeitzReduction.F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2 hAA)
        (SeitzReduction.F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2 hBB) hAB
        fun z hz hz2 => h.eq_one_of_mem_conjugate_inf d hq h₁₂ hδ hsurj g hz hz2
    · have hAB' : CFSG.conjugate G₂ g = CFSG.conjugate G₁ g :=
        SeitzReduction.F4Pilot.map_conj_toMonoidHom_inj.1 (hBA'.trans hAA.symm)
      rw [hAB'] at hAB
      exact hbA (by rw [← hpA, commutator_eq_bot_iff_le_centralizer.2 hAB])
  · exact h.conjugate_eq_of_swap hKc N₀ N₁ hB₀ hB₁ hq h₁₂ hδ hsurj hM₀ hM₁ g hswap

end SwapCase

end CFSG.LocalAnalysis.EvenBN.LinearThree

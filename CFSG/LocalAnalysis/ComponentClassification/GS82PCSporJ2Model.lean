module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PCSporJ2Data
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabJ2
public import CFSG.Sporadic.SmallOddCore.J2Local

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.PCSpor

open CFSG Subgroup CFSG.ComponentClassification.J2Cover CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier J2Data

theorem rep_of_eqC {w t u : Array ℕ} {g h : Equiv.Perm (Fin 315)} (hc : eqC w t u = true)
    (ht : Rep 315 t g) (hu : Rep 315 u h) : Rep 315 w (g * h) := by
  intro x
  have h1 := List.all_eq_true.1 hc x.1 (List.mem_range.2 x.2)
  rw [beq_iff_eq] at h1
  rw [h1, hu x, ht (h x), Equiv.Perm.mul_apply]

theorem eq_one_of_isIdC {t u : Array ℕ} {g h : Equiv.Perm (Fin 315)} (hc : isIdC t u = true)
    (ht : Rep 315 t g) (hu : Rep 315 u h) : g * h = 1 := by
  ext x
  have h1 := List.all_eq_true.1 hc x.1 (List.mem_range.2 x.2)
  rw [beq_iff_eq, hu x, ht (h x)] at h1
  simpa using h1

theorem ne_one_of_movesList {t : Array ℕ} {g : Equiv.Perm (Fin 315)}
    (hm : movesList 315 t = true) (ht : Rep 315 t g) : g ≠ 1 := by
  rintro rfl
  obtain ⟨i, hi, h1⟩ := List.any_eq_true.1 hm
  rw [List.mem_range] at hi
  have h2 := ht ⟨i, hi⟩
  rw [Equiv.Perm.one_apply] at h2
  simp [h2] at h1

theorem ne_of_neL {t u : Array ℕ} {g h : Equiv.Perm (Fin 315)} (hn : neL t u = true)
    (ht : Rep 315 t g) (hu : Rep 315 u h) : g ≠ h := by
  rintro rfl
  obtain ⟨i, hi, h1⟩ := List.any_eq_true.1 hn
  rw [List.mem_range] at hi
  rw [ht.apply hi, hu.apply hi] at h1
  simp at h1


theorem rep_cent2B (j : ℕ) (hj : j < cent2BStrong.size) :
    Rep 315 cent2BStrong[j]! (permOfArr 315 cent2BStrong[j]!) :=
  rep_permOfArr_of_chainOK (k := 2) (base := [0, 3]) cent2B_check.1 hj

theorem mem_cent2B (j : ℕ) (hj : j < 2) :
    permOfArr 315 cent2BStrong[j]! ∈ centralizerIn P permA := by
  rw [inner_classes.2.2.1, cent2BChain, ofArrays_originalSubgroup]
  exact subset_closure ⟨j, hj, rfl⟩

theorem j2_2B_elems : ∃ A B : Equiv.Perm (Fin 315), A ∈ centralizerIn P permA ∧
    B ∈ centralizerIn P permA ∧ A ^ 5 = 1 ∧ B ^ 3 = 1 ∧ (A * A * B) * (A * A * B) = 1 ∧
    A * A * B ≠ 1 ∧ Nat.card {i : Fin 315 // (A * A * B) i = i} = 11 ∧
    (A * B * A) * (A * B * A) = 1 ∧ A * B * A ≠ 1 ∧
    Nat.card {i : Fin 315 // (A * B * A) i = i} = 11 ∧ A * A * B ≠ A * B * A := by
  obtain ⟨hA, hA2, hA4, hA5, hB, hB2, hB3⟩ := j2Checks_b₀
  obtain ⟨hX1, hX1i, hX1m, hX1f, hAB, hX2, hX2i, hX2m, hX2f, hne⟩ := j2Checks_b₁
  set c₀ := permOfArr 315 cent2BStrong[0]!
  set c₁ := permOfArr 315 cent2BStrong[1]!
  have r0 : Rep 315 cent2BStrong[0]! c₀ := rep_cent2B 0 (by decide)
  have r1 : Rep 315 cent2BStrong[1]! c₁ := rep_cent2B 1 (by decide)
  have rA := rep_of_eqC hA r0 r0
  have rA2 := rep_of_eqC hA2 rA rA
  have rA4 := rep_of_eqC hA4 rA2 rA2
  have rB := rep_of_eqC hB r1 r1
  have rB2 := rep_of_eqC hB2 rB rB
  have rX1 := rep_of_eqC hX1 rA2 rB
  have rAB := rep_of_eqC hAB rA rB
  have rX2 := rep_of_eqC hX2 rAB rA
  have m0 := mem_cent2B 0 (by norm_num)
  have m1 := mem_cent2B 1 (by norm_num)
  refine ⟨c₀ * c₀, c₁ * c₁, mul_mem m0 m0, mul_mem m1 m1, ?_, ?_, eq_one_of_isIdC hX1i rX1 rX1,
    ne_one_of_movesList hX1m rX1, (card_fixed_eq_fixedCount rX1).trans hX1f,
    eq_one_of_isIdC hX2i rX2 rX2, ne_one_of_movesList hX2m rX2,
    (card_fixed_eq_fixedCount rX2).trans hX2f, ne_of_neL hne rX1 rX2⟩
  · have := eq_one_of_isIdC hA5 rA4 rA
    rw [← this]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  · have := eq_one_of_isIdC hB3 rB2 rB
    rw [← this]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem rep_centOuter (j : ℕ) (hj : j < centOuterStrong.size) :
    Rep 315 centOuterStrong[j]! (permOfArr 315 centOuterStrong[j]!) :=
  rep_permOfArr_of_chainOK (k := 2) (base := [0, 3]) centOuter_check.1 hj

theorem mem_centOuter (j : ℕ) (hj : j < 2) :
    permOfArr 315 centOuterStrong[j]! ∈ centralizerIn P permU := by
  rw [outer_classes.2.2, centOuterChain, ofArrays_originalSubgroup]
  exact subset_closure ⟨j, hj, rfl⟩

theorem j2_outer_elems : ∃ A B : Equiv.Perm (Fin 315), A ∈ centralizerIn P permU ∧
    B ∈ centralizerIn P permU ∧ A ^ 3 = 1 ∧ B ^ 3 = 1 ∧
    (A * A * B * (A * A * B)) * (A * A * B * (A * A * B)) = 1 ∧ A * A * B * (A * A * B) ≠ 1 ∧
    Nat.card {i : Fin 315 // (A * A * B * (A * A * B)) i = i} = 11 := by
  obtain ⟨hA2, hA3, hB, hB2, hB3, hW, hX, hXi, hXm, hXf⟩ := j2Checks_o
  set d₀ := permOfArr 315 centOuterStrong[0]!
  set d₁ := permOfArr 315 centOuterStrong[1]!
  have r0 : Rep 315 centOuterStrong[0]! d₀ := rep_centOuter 0 (by decide)
  have r1 : Rep 315 centOuterStrong[1]! d₁ := rep_centOuter 1 (by decide)
  have rA2 := rep_of_eqC hA2 r0 r0
  have rB := rep_of_eqC hB r1 r1
  have rB2 := rep_of_eqC hB2 rB rB
  have rW := rep_of_eqC hW rA2 rB
  have rX := rep_of_eqC hX rW rW
  have m0 := mem_centOuter 0 (by norm_num)
  have m1 := mem_centOuter 1 (by norm_num)
  refine ⟨d₀, d₁ * d₁, m0, mul_mem m1 m1, ?_, ?_, eq_one_of_isIdC hXi rX rX,
    ne_one_of_movesList hXm rX, (card_fixed_eq_fixedCount rX).trans hXf⟩
  · have := eq_one_of_isIdC hA3 rA2 r0
    rw [← this]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  · have := eq_one_of_isIdC hB3 rB2 rB
    rw [← this]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]

section Transport

variable {S : Type} [Group S] (θ : S ≃* ↥P)

theorem card_centralizer_eq_of_equiv (d : S) :
    Nat.card (centralizer ({d} : Set S)) =
      Nat.card (centralizerIn P (θ d : Equiv.Perm (Fin 315))) := by
  set f : S →* Equiv.Perm (Fin 315) := P.subtype.comp θ.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp θ.injective
  have hrange : f.range = P := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr θ.surjective, ← MonoidHom.range_eq_map,
      range_subtype]
  rw [← Subgroup.card_map_of_injective hf, Sporadic.SmallOddCore.map_centralizer_eq_inf hf, hrange,
    Set.image_singleton]
  rfl

theorem card_centralizer_of_eleven {d : S} (hd : orderOf d = 2)
    (h11 : Models.fixCount (θ d : Equiv.Perm (Fin 315)) = 11) :
    Nat.card (centralizer ({d} : Set S)) = 1920 := by
  rw [card_centralizer_eq_of_equiv θ]
  have hτ : orderOf (θ d : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hd]
  obtain ⟨hcov, -, -, -, h2⟩ := inner_classes
  obtain ⟨r, hr, c, hc, hτc⟩ := hcov _ (θ d).2 hτ
  rw [hτc, centralizerIn_conj P hc, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exfalso
    rw [hτc, Models.fixCount_conj, Models.fixCount, ← Nat.card_eq_fintype_card,
      fixed_points_reps.1] at h11
    norm_num at h11
  · rw [h2]
    exact cent2A_facts.2.1

theorem coe_conj_mul (c X Y : Equiv.Perm (Fin 315)) :
    c * X * c⁻¹ * (c * Y * c⁻¹) = c * (X * Y) * c⁻¹ := by group

theorem orderOf_two_of_conj {x : S} {c X : Equiv.Perm (Fin 315)}
    (hx : ((θ x : ↥P) : Equiv.Perm (Fin 315)) = c * X * c⁻¹) (h2 : X * X = 1) (h1 : X ≠ 1) :
    orderOf x = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · apply θ.injective
    apply Subtype.ext
    rw [map_pow, Subgroup.coe_pow, hx, map_one, Subgroup.coe_one, sq, coe_conj_mul, h2]
    group
  · intro h
    apply h1
    have h3 := congrArg (fun y => ((θ y : ↥P) : Equiv.Perm (Fin 315))) h
    simp only [map_one, Subgroup.coe_one, hx] at h3
    calc X = c⁻¹ * (c * X * c⁻¹) * c := by group
      _ = 1 := by rw [h3]; group

theorem fixCount_of_conj {x : S} {c X : Equiv.Perm (Fin 315)}
    (hx : ((θ x : ↥P) : Equiv.Perm (Fin 315)) = c * X * c⁻¹) :
    Models.fixCount (θ x : Equiv.Perm (Fin 315)) = Nat.card {i : Fin 315 // X i = i} := by
  rw [hx, Models.fixCount_conj, Models.fixCount, Nat.card_eq_fintype_card]

theorem ne_of_conj {x y : S} {c X Y : Equiv.Perm (Fin 315)}
    (hx : ((θ x : ↥P) : Equiv.Perm (Fin 315)) = c * X * c⁻¹)
    (hy : ((θ y : ↥P) : Equiv.Perm (Fin 315)) = c * Y * c⁻¹) (hne : X ≠ Y) : x ≠ y := by
  rintro rfl
  apply hne
  rw [hx] at hy
  calc X = c⁻¹ * (c * X * c⁻¹) * c := by group
    _ = c⁻¹ * (c * Y * c⁻¹) * c := by rw [hy]
    _ = Y := by group

theorem pow_eq_one_of_conj {x : S} {c X : Equiv.Perm (Fin 315)} {n : ℕ}
    (hx : ((θ x : ↥P) : Equiv.Perm (Fin 315)) = c * X * c⁻¹) (h : X ^ n = 1) : x ^ n = 1 := by
  apply θ.injective
  apply Subtype.ext
  rw [map_pow, Subgroup.coe_pow, hx, conj_pow, h, map_one, Subgroup.coe_one]
  group

theorem j2_2B_elems_of_equiv {s : S} (hs : orderOf s = 2)
    (h240 : Nat.card (centralizer ({s} : Set S)) = 240) :
    ∃ a b : S, a ∈ centralizer ({s} : Set S) ∧ b ∈ centralizer ({s} : Set S) ∧ a ^ 5 = 1 ∧
      b ^ 3 = 1 ∧ orderOf (a * a * b) = 2 ∧
      Models.fixCount (θ (a * a * b) : Equiv.Perm (Fin 315)) = 11 ∧ orderOf (a * b * a) = 2 ∧
      Models.fixCount (θ (a * b * a) : Equiv.Perm (Fin 315)) = 11 ∧ a * a * b ≠ a * b * a := by
  have hτ : orderOf (θ s : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hs]
  obtain ⟨hcov, -, -, -, h2⟩ := inner_classes
  obtain ⟨r, hr, c, hc, hτc⟩ := hcov _ (θ s).2 hτ
  have hr' : r = permA := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rfl
    · exfalso
      rw [card_centralizer_eq_of_equiv θ, hτc, centralizerIn_conj P hc,
        Subgroup.card_map_of_injective (MulAut.conj c).injective, h2, cent2A_facts.2.1] at h240
      norm_num at h240
  subst hr'
  obtain ⟨A, B, hA, hB, hA5, hB3, hX1, hX1', hX1f, hX2, hX2', hX2f, hne⟩ := j2_2B_elems
  obtain ⟨hAP, hAc⟩ := mem_centralizerIn.1 hA
  obtain ⟨hBP, hBc⟩ := mem_centralizerIn.1 hB
  set a := θ.symm ⟨c * A * c⁻¹, P.mul_mem (P.mul_mem hc hAP) (P.inv_mem hc)⟩ with hadef
  set b := θ.symm ⟨c * B * c⁻¹, P.mul_mem (P.mul_mem hc hBP) (P.inv_mem hc)⟩ with hbdef
  have hpa : ((θ a : ↥P) : Equiv.Perm (Fin 315)) = c * A * c⁻¹ := by
    rw [hadef, MulEquiv.apply_symm_apply]
  have hpb : ((θ b : ↥P) : Equiv.Perm (Fin 315)) = c * B * c⁻¹ := by
    rw [hbdef, MulEquiv.apply_symm_apply]
  have hcent : ∀ {x : S} {X : Equiv.Perm (Fin 315)},
      ((θ x : ↥P) : Equiv.Perm (Fin 315)) = c * X * c⁻¹ → X * permA = permA * X →
      x ∈ centralizer ({s} : Set S) := by
    intro x X hx hX
    rw [mem_centralizer_singleton_iff]
    apply θ.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hx, hτc, coe_conj_mul,
      coe_conj_mul, hX]
  have h1 : ((θ (a * a * b) : ↥P) : Equiv.Perm (Fin 315)) = c * (A * A * B) * c⁻¹ := by
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hpa, hpb, coe_conj_mul,
      coe_conj_mul]
  have h2' : ((θ (a * b * a) : ↥P) : Equiv.Perm (Fin 315)) = c * (A * B * A) * c⁻¹ := by
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hpa, hpb, coe_conj_mul,
      coe_conj_mul]
  exact ⟨a, b, hcent hpa hAc, hcent hpb hBc, pow_eq_one_of_conj θ hpa hA5,
    pow_eq_one_of_conj θ hpb hB3, orderOf_two_of_conj θ h1 hX1 hX1',
    (fixCount_of_conj θ h1).trans hX1f, orderOf_two_of_conj θ h2' hX2 hX2',
    (fixCount_of_conj θ h2').trans hX2f, ne_of_conj θ h1 h2' hne⟩

theorem j2_outer_elems_of_equiv {σ : MulAut S} (hσ2 : σ * σ = 1)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) :
    Nat.card (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup σ) = 336 ∧
      ∃ a b : S, σ a = a ∧ σ b = b ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧
        orderOf (a * a * b * (a * a * b)) = 2 ∧
        Models.fixCount (θ (a * a * b * (a * a * b)) : Equiv.Perm (Fin 315)) = 11 := by
  set β' := MulAut.congr θ σ with hβ'
  have hβ2 : β' * β' = 1 := by rw [hβ', ← map_mul, hσ2, map_one]
  have hβθ : ∀ x : S, θ (σ x) = β' (θ x) := fun x => by
    rw [hβ', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  have hβout : β' ∉ OuterAutomorphisms.inner P := by
    rintro ⟨q, hq⟩
    apply hout
    refine ⟨θ.symm q, ?_⟩
    apply (MulAut.congr θ).injective
    rw [← hβ', ← hq]
    ext x
    simp [MulAut.congr_apply]
  have hfixeq : (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup σ).map
      θ.toMonoidHom = fixSub β' := by
    ext y
    rw [mem_map_equiv, mem_fixSub, LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff]
    have hc : β' y = θ (σ (θ.symm y)) := by
      rw [hβ', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
    rw [hc]
    constructor
    · intro hy
      rw [hy, MulEquiv.apply_symm_apply]
    · intro hy
      apply θ.injective
      rw [hy, MulEquiv.apply_symm_apply]
  have hcard : Nat.card (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup σ) =
      336 := by
    rw [← Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective, hfixeq]
    exact QuasithinUnique.Ch1.j2_outer_fixSub_card β' hβ2 hβout
  refine ⟨hcard, ?_⟩
  obtain ⟨w, hwP, hw2, hβw⟩ := QuasithinUnique.Id2519.Tab.j2_outer_conj β' hβ2 hβout
  obtain ⟨c, hc, hwc⟩ := outer_classes.1 w hwP hw2
  obtain ⟨A, B, hA, hB, hA3, hB3, hX, hX', hXf⟩ := j2_outer_elems
  obtain ⟨hAP, hAc⟩ := mem_centralizerIn.1 hA
  obtain ⟨hBP, hBc⟩ := mem_centralizerIn.1 hB
  set a := θ.symm ⟨c * A * c⁻¹, P.mul_mem (P.mul_mem hc hAP) (P.inv_mem hc)⟩ with hadef
  set b := θ.symm ⟨c * B * c⁻¹, P.mul_mem (P.mul_mem hc hBP) (P.inv_mem hc)⟩ with hbdef
  have hpa : ((θ a : ↥P) : Equiv.Perm (Fin 315)) = c * A * c⁻¹ := by
    rw [hadef, MulEquiv.apply_symm_apply]
  have hpb : ((θ b : ↥P) : Equiv.Perm (Fin 315)) = c * B * c⁻¹ := by
    rw [hbdef, MulEquiv.apply_symm_apply]
  have hfix : ∀ {x : S} {X : Equiv.Perm (Fin 315)},
      ((θ x : ↥P) : Equiv.Perm (Fin 315)) = c * X * c⁻¹ → X * permU = permU * X → σ x = x := by
    intro x X hx hX
    apply θ.injective
    apply Subtype.ext
    rw [hβθ, hβw, hx, hwc,
      show c * permU * c⁻¹ * (c * X * c⁻¹) * (c * permU * c⁻¹)⁻¹ =
        c * (permU * X) * permU⁻¹ * c⁻¹ by group, ← hX]
    group
  have h1 : ((θ (a * a * b * (a * a * b)) : ↥P) : Equiv.Perm (Fin 315)) =
      c * (A * A * B * (A * A * B)) * c⁻¹ := by
    simp only [map_mul, Subgroup.coe_mul, hpa, hpb]
    group
  exact ⟨a, b, hfix hpa hAc, hfix hpb hBc, pow_eq_one_of_conj θ hpa hA3,
    pow_eq_one_of_conj θ hpb hB3, orderOf_two_of_conj θ h1 hX hX',
    (fixCount_of_conj θ h1).trans hXf⟩

end Transport

end CFSG.ComponentClassification.GS82PumpInputs.PCSpor

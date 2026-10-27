module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerReduction
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLinear

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution.Balance CFSG.ComponentClassification

section Commute

variable {K : Type} [Group K]

theorem commute_of_odd_pow_mem_center (hZ : IsPGroup 2 (Subgroup.center K)) {ν x : K} {k : ℕ}
    (hk : Odd k) (hν : ν ^ k ∈ Subgroup.center K)
    (hc : ν * x * ν⁻¹ * x⁻¹ ∈ Subgroup.center K) : ν * x = x * ν := by
  set z := ν * x * ν⁻¹ * x⁻¹ with hzdef
  have hzx : ν * x * ν⁻¹ = z * x := by rw [hzdef]; group
  have hzp : ∀ j : ℕ, ν * z ^ j * ν⁻¹ = z ^ j := fun j => by
    rw [Subgroup.mem_center_iff.mp (pow_mem hc j) ν]
    group
  have key : ∀ j : ℕ, ν ^ j * x * (ν ^ j)⁻¹ = z ^ j * x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc ν ^ (j + 1) * x * (ν ^ (j + 1))⁻¹
          = ν * (ν ^ j * x * (ν ^ j)⁻¹) * ν⁻¹ := by group
        _ = ν * (z ^ j * x) * ν⁻¹ := by rw [ih]
        _ = (ν * z ^ j * ν⁻¹) * (ν * x * ν⁻¹) := by group
        _ = z ^ j * (z * x) := by rw [hzp, hzx]
        _ = z ^ (j + 1) * x := by group
  have hxk : ν ^ k * x * (ν ^ k)⁻¹ = x := by
    rw [← Subgroup.mem_center_iff.mp hν x]
    group
  have hzk : z ^ k = 1 := by
    have h := key k
    rw [hxk] at h
    exact mul_eq_right.mp h.symm
  obtain ⟨e, he⟩ := hZ ⟨z, hc⟩
  have hze : z ^ (2 ^ e) = 1 := congrArg Subtype.val he
  have h1 : orderOf z ∣ k := orderOf_dvd_of_pow_eq_one hzk
  have h2 : orderOf z ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hze
  have h3 : Nat.Coprime k (2 ^ e) := (Nat.coprime_two_right.mpr hk).pow_right e
  have hz1 : z = 1 := orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (h3.coprime_dvd_left h1) h2)
  rw [hz1] at hzx
  rw [mul_inv_eq_iff_eq_mul] at hzx
  simpa using hzx

end Commute

section Blocks

variable {K : Type} [Group K] [Finite K]

theorem oddCoreIn_centralizer_eq_bot_of_blocks (hZ : IsPGroup 2 (Subgroup.center K)) (g : K)
    {ι : Type} (L : ι → Subgroup K)
    (hLB : ∀ i, L i ≤ Subgroup.centralizer ({g} : Set K))
    (hnorm : ∀ i, ∀ b ∈ Subgroup.centralizer ({g} : Set K), ∀ x ∈ L i, b * x * b⁻¹ ∈ L i)
    (hno : ∀ i, oddCoreIn ((L i).map (QuotientGroup.mk' (Subgroup.center K))) = ⊥)
    (hcent : ∀ ν ∈ Subgroup.centralizer ({g} : Set K), (∀ i, ∀ x ∈ L i, ν * x = x * ν) →
      ∃ e : ℕ, ν ^ (2 ^ e) = 1) :
    oddCoreIn (Subgroup.centralizer
      ({(QuotientGroup.mk g : K ⧸ Subgroup.center K)} : Set (K ⧸ Subgroup.center K))) = ⊥ := by
  set Z := Subgroup.center K with hZdef
  set π := QuotientGroup.mk' Z with hπ
  set C := Subgroup.centralizer ({(QuotientGroup.mk g : K ⧸ Z)} : Set (K ⧸ Z)) with hC
  set N := oddCoreIn C with hN
  have hker : ∀ y : K, π y = 1 → y ∈ Z := fun y hy => (QuotientGroup.eq_one_iff y).mp hy
  have hodd_pow : ∀ ν : K, π ν ∈ N → ∃ k, Odd k ∧ ν ^ k ∈ Z := by
    intro ν hν
    refine ⟨orderOf (π ν), Odd.of_dvd_nat (odd_card_oddCoreIn C)
      (Subgroup.orderOf_dvd_natCard N hν), hker _ ?_⟩
    rw [map_pow, pow_orderOf_eq_one]
  have hB : ∀ ν : K, π ν ∈ N → ν ∈ Subgroup.centralizer ({g} : Set K) := by
    intro ν hν
    obtain ⟨k, hk, hνk⟩ := hodd_pow ν hν
    have hνC : π ν ∈ C := oddCoreIn_le C hν
    have hcomm : π ν * π g = π g * π ν := Subgroup.mem_centralizer_singleton_iff.mp hνC
    have hz : ν * g * ν⁻¹ * g⁻¹ ∈ Z := by
      apply hker
      calc π (ν * g * ν⁻¹ * g⁻¹) = (π ν * π g) * (π ν)⁻¹ * (π g)⁻¹ := by
            simp only [map_mul, map_inv]
        _ = (π g * π ν) * (π ν)⁻¹ * (π g)⁻¹ := by rw [hcomm]
        _ = 1 := by group
    exact Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_odd_pow_mem_center hZ hk hνk hz)
  have hcommL : ∀ ν : K, π ν ∈ N → ∀ i, ∀ x ∈ L i, ν * x = x * ν := by
    intro ν hν i x hx
    obtain ⟨k, hk, hνk⟩ := hodd_pow ν hν
    set Li := (L i).map π with hLi
    have hLiC : Li ≤ C := by
      rintro _ ⟨y, hy, rfl⟩
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      have h2 := congrArg π (Subgroup.mem_centralizer_singleton_iff.mp (hLB i hy))
      rw [map_mul, map_mul] at h2
      exact h2
    have hπx : π x ∈ Li := ⟨x, hx, rfl⟩
    have hconj : ∀ y ∈ Li, π ν * y * (π ν)⁻¹ ∈ Li := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨ν * y * ν⁻¹, hnorm i ν (hB ν hν) y hy, by simp⟩
    have hmemN : π ν * π x * (π ν)⁻¹ * (π x)⁻¹ ∈ N := by
      have h1 : π x * (π ν)⁻¹ * (π x)⁻¹ ∈ N := by
        have := conj_mem_oddCoreIn (hLiC hπx) (N.inv_mem hν)
        simpa [mul_assoc] using this
      have h2 := N.mul_mem hν h1
      simpa [mul_assoc] using h2
    have hmemL : π ν * π x * (π ν)⁻¹ * (π x)⁻¹ ∈ Li :=
      Li.mul_mem (hconj _ hπx) (Li.inv_mem hπx)
    have hnormN : ∀ y ∈ C, ∀ w, w ∈ N ↔ y * w * y⁻¹ ∈ N := by
      intro y hy w
      refine ⟨fun hw => conj_mem_oddCoreIn hy hw, fun hw => ?_⟩
      have := conj_mem_oddCoreIn (C.inv_mem hy) hw
      simpa [mul_assoc] using this
    have hle : N ⊓ Li ≤ oddCoreIn Li := by
      refine le_oddCoreIn_of_normalizes inf_le_right ?_
        ((odd_card_oddCoreIn C).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · rintro ⟨hwN, hwL⟩
        exact ⟨conj_mem_oddCoreIn (hLiC hy) hwN,
          Li.mul_mem (Li.mul_mem hy hwL) (Li.inv_mem hy)⟩
      · rintro ⟨hwN, hwL⟩
        refine ⟨(hnormN y (hLiC hy) w).mpr hwN, ?_⟩
        have := Li.mul_mem (Li.mul_mem (Li.inv_mem hy) hwL) hy
        simpa [mul_assoc] using this
    have hcomm1 : π ν * π x * (π ν)⁻¹ * (π x)⁻¹ = 1 := by
      have h1 := hle ⟨hmemN, hmemL⟩
      rw [hno i, Subgroup.mem_bot] at h1
      exact h1
    have hz : ν * x * ν⁻¹ * x⁻¹ ∈ Z := hker _ (by simpa only [map_mul, map_inv] using hcomm1)
    exact commute_of_odd_pow_mem_center hZ hk hνk hz
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  obtain ⟨ν, rfl⟩ := QuotientGroup.mk'_surjective Z n
  obtain ⟨e, he⟩ := hcent ν (hB ν hn) (hcommL ν hn)
  have h1 : orderOf (π ν) ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, he, map_one])
  have h2 : Odd (orderOf (π ν)) :=
    Odd.of_dvd_nat (odd_card_oddCoreIn C) (Subgroup.orderOf_dvd_natCard N hn)
  exact orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_right.mpr h2).pow_right e) h1)

end Blocks

section Images

variable {S J : Type} [Group S] [Group J]

theorem componentOddCore_eq_bot_of_isQuasisimple [Finite J] (hJ : CFSG.Open.IsQuasisimple J)
    (hZ : IsPGroup 2 (Subgroup.center J)) : componentClassificationOddCore J = ⊥ := by
  have hle := oddCore_le_center_of_isQuasisimple hJ
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := hZ ⟨g, hle hg⟩
  have h1 : g ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h2 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : Odd (orderOf g) :=
    Odd.of_dvd_nat (OddCore.odd_card J) (Subgroup.orderOf_dvd_natCard _ hg)
  exact orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_right.mpr h3).pow_right k) h2)

theorem oddCoreIn_range_eq_bot_of_injective (π : J →* S) (hinj : Function.Injective π)
    (hJ : componentClassificationOddCore J = ⊥) : oddCoreIn π.range = ⊥ := by
  have h1 := OddCore.equiv_invariant (MonoidHom.ofInjective hinj)
  rw [hJ, Subgroup.map_bot] at h1
  unfold oddCoreIn
  rw [← h1, Subgroup.map_bot]

theorem oddCoreIn_range_eq_bot_of_isQuasisimple [Finite J] (π : J →* S)
    (hJ : CFSG.Open.IsQuasisimple J) (hZ : IsPGroup 2 (Subgroup.center J))
    (hker : π.ker ≤ Subgroup.center J) : oddCoreIn π.range = ⊥ := by
  have hsurj : Function.Surjective π.rangeRestrict := π.rangeRestrict_surjective
  have hker' : π.rangeRestrict.ker ≤ Subgroup.center J := by
    rwa [MonoidHom.ker_rangeRestrict]
  have hX : CFSG.Open.IsQuasisimple π.range :=
    isQuasisimple_of_centralQuotient hJ π.rangeRestrict hsurj hker'
  have : Group.IsPerfect J := ⟨hJ.1⟩
  have hcen := center_le_map_center_of_perfect π.rangeRestrict hsurj hker'
  have hZX : IsPGroup 2 (Subgroup.center π.range) := (hZ.map π.rangeRestrict).to_le hcen
  have : Finite π.range := Finite.of_surjective _ hsurj
  unfold oddCoreIn
  rw [componentOddCore_eq_bot_of_isQuasisimple hX hZX, Subgroup.map_bot]

end Images

section SpecialLinear

open scoped MatrixGroups

private theorem sl2Three_centralizer_aux :
    ∀ x : SL(2, ZMod 3), (∀ q : SL(2, ZMod 3), q ^ 4 = 1 → x * q = q * x) → x ^ 4 = 1 := by
  decide +kernel

theorem componentOddCore_eq_bot_of_oddCoreIn_top {P : Type} [Group P]
    (h : oddCoreIn (⊤ : Subgroup P) = ⊥) : componentClassificationOddCore P = ⊥ := by
  have h1 : componentClassificationOddCore (⊤ : Subgroup P) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (⊤ : Subgroup P).subtype_injective).mp h
  have h2 := OddCore.equiv_invariant (Subgroup.topEquiv (G := P))
  rw [h1, Subgroup.map_bot] at h2
  exact h2.symm

theorem componentOddCore_sl2Three : componentClassificationOddCore SL(2, ZMod 3) = ⊥ := by
  have hV : IsPGroup 2 CFSG.ClassicalInvolution.sl2ThreeQ :=
    IsPGroup.of_card (n := 3) (by rw [CFSG.ClassicalInvolution.natCard_sl2ThreeQ]; norm_num)
  have h := oddCoreIn_centralizer_eq_bot_of_normal_isPGroup
    CFSG.ClassicalInvolution.sl2ThreeQ_normal hV (s := 1)
    (fun x hx => CFSG.ClassicalInvolution.mem_sl2ThreeQ_iff.mpr
      (sl2Three_centralizer_aux x fun q hq =>
        (Subgroup.mem_centralizer_iff.mp hx q
          (CFSG.ClassicalInvolution.mem_sl2ThreeQ_iff.mpr hq)).symm))
    (Subgroup.mem_centralizer_iff.mpr fun h _ => by simp)
  have hC1 : Subgroup.centralizer ({(1 : SL(2, ZMod 3))} : Set SL(2, ZMod 3)) = ⊤ := by
    ext g
    simp [Subgroup.mem_centralizer_singleton_iff]
  rw [hC1] at h
  exact componentOddCore_eq_bot_of_oddCoreIn_top h

variable {F : Type} [Field F] [Finite F]

theorem componentOddCore_sl2_eq_bot (hF : Nat.card F = 3) :
    componentClassificationOddCore SL(2, F) = ⊥ := by
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.nonempty_mulEquiv_sl2Three_of_natCard_eq_three hF
  have h1 := OddCore.equiv_invariant e
  rw [componentOddCore_sl2Three] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1

omit [Finite F] in
theorem subsingleton_specialLinear_of_le_one {a : ℕ} (ha : a ≤ 1) : Subsingleton SL(a, F) :=
  CFSG.ClassicalInvolution.ModelFacts.subsingleton_sl_of_le_one ha

theorem centerExp_specialLinear_of_pos {k : ℕ} (hF : Nat.card F = 2 ^ k + 1) {n : ℕ}
    (hn : 1 ≤ n) : CenterExp SL(n, F) k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact centerExp_specialLinear m k F hF

theorem isPGroup_center_specialLinear_of_card {k : ℕ} (hF : Nat.card F = 2 ^ k + 1) {n : ℕ}
    (hn : 1 ≤ n) : IsPGroup 2 (Subgroup.center SL(n, F)) :=
  (centerExp_specialLinear_of_pos hF hn).isPGroup

theorem isPGroup_center_specialLinear (hF : Nat.card F = 3) {n : ℕ} (hn : 1 ≤ n) :
    IsPGroup 2 (Subgroup.center SL(n, F)) :=
  isPGroup_center_specialLinear_of_card (k := 1) (by rw [hF]; norm_num) hn

theorem componentOddCore_specialLinear_eq_bot (hF : Nat.card F = 3) (k : ℕ) :
    componentClassificationOddCore SL(k, F) = ⊥ := by
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k
    · have := subsingleton_specialLinear_of_le_one (F := F) (a := 0) (by omega)
      exact Subsingleton.elim _ _
    · have := subsingleton_specialLinear_of_le_one (F := F) (a := 1) (by omega)
      exact Subsingleton.elim _ _
    · exact componentOddCore_sl2_eq_bot hF
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact componentOddCore_eq_bot_of_isQuasisimple
      (CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple
        (CFSG.LieType.Universal.SpecialLinear.isQuasisimple m F (by omega)))
      (centerExp_specialLinear m 1 F (by rw [hF]; norm_num)).isPGroup

end SpecialLinear

section Transport

variable {X X' : Type} [Group X] [Finite X] [Group X'] [Finite X']

theorem oddCoreIn_centralizer_eq_bot_of_mulEquiv (e : X ≃* X') (z : X)
    (h : oddCoreIn (Subgroup.centralizer ({e z} : Set X')) = ⊥) :
    oddCoreIn (Subgroup.centralizer ({z} : Set X)) = ⊥ := by
  have hmap : (Subgroup.centralizer ({z} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e z} : Set X') := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hy]
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx
  have h1 := map_oddCoreIn_le e.toMonoidHom hmap
  rw [h, le_bot_iff] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1

noncomputable def centralQuotientEquiv (e : X ≃* X') :
    X ⧸ Subgroup.center X ≃* X' ⧸ Subgroup.center X' :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem oddCoreIn_centralizer_eq_bot_of_equiv (e : X ≃* X') (g : X)
    (h : oddCoreIn (Subgroup.centralizer
      ({(QuotientGroup.mk (e g) : X' ⧸ Subgroup.center X')} : Set (X' ⧸ Subgroup.center X'))) =
        ⊥) :
    oddCoreIn (Subgroup.centralizer
      ({(QuotientGroup.mk g : X ⧸ Subgroup.center X)} : Set (X ⧸ Subgroup.center X))) = ⊥ :=
  oddCoreIn_centralizer_eq_bot_of_mulEquiv (centralQuotientEquiv e) _ h

end Transport

end CFSG.ClassicalInvolution.Q3

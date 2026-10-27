module

public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6Sylow

public section

namespace CFSG.AGLEmbedding.ParabHub

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.ClassicalInvolution.WeakCT

theorem eq_one_of_central_odd {Z : Type*} [Group Z] {z a b : Z} {M : ℕ} (hM : Odd M)
    (hzM : z ^ M = 1) (hz : z = a⁻¹ * b) (hab : Commute a b) {r s : ℕ} (ha : a ^ 2 ^ r = 1)
    (hb : b ^ 2 ^ s = 1) : z = 1 := by
  have hz2 : z ^ 2 ^ (max r s) = 1 := by
    have hac : Commute a⁻¹ b := hab.inv_left
    rw [hz, hac.mul_pow, inv_pow]
    have h1 : a ^ 2 ^ max r s = 1 := by
      obtain ⟨k, hk⟩ : 2 ^ r ∣ 2 ^ max r s := pow_dvd_pow 2 (le_max_left r s)
      rw [hk, pow_mul, ha, one_pow]
    have h2 : b ^ 2 ^ max r s = 1 := by
      obtain ⟨k, hk⟩ : 2 ^ s ∣ 2 ^ max r s := pow_dvd_pow 2 (le_max_right r s)
      rw [hk, pow_mul, hb, one_pow]
    rw [h1, h2, inv_one, one_mul]
  have hcop : Nat.Coprime (2 ^ max r s) M := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hM)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hz2)
    (orderOf_dvd_of_pow_eq_one hzM))

theorem pow_eq_one_of_mem_closure {G : Type*} [Group G] {S : Set G} (hS : S.Pairwise Commute)
    {M : ℕ} (hM : ∀ s ∈ S, s ^ M = 1) {g : G} (hg : g ∈ Subgroup.closure S) : g ^ M = 1 := by
  have hcomm : IsMulCommutative (Subgroup.closure S) := Subgroup.isMulCommutative_closure hS
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hM x hx
  | one => exact one_pow M
  | mul x y hx hy hx1 hy1 =>
    have hxy : x * y = y * x := congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hc : Commute x y := hxy
    rw [hc.mul_pow, hx1, hy1, mul_one]
  | inv x hx hx1 => rw [inv_pow, hx1, inv_one]

section Overgroups

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem exists_negRoot_le_of_borel_lt
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {A : Subgroup K} (hBA : borel D H ≤ A)
    (hne : A ≠ borel D H) :
    ∃ i : Fin D.rank, D.rootGroup (-Pi.single i 1) ≤ A := by
  obtain ⟨g, hgA, hgB⟩ : ∃ g ∈ A, g ∉ borel D H := by
    by_contra h
    push Not at h
    exact hne (le_antisymm h hBA)
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mem_bruhatCell hct hext g
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [nrep_one, mul_one] at hgB
    exact hgB (mul_mem hb₁ hb₂)
  have hnA : nrep hct w ∈ A := by
    have := mul_mem (mul_mem (inv_mem (hBA hb₁)) hgA) (inv_mem (hBA hb₂))
    simpa [mul_assoc] using this
  obtain ⟨i, hi⟩ := (coxeterMatrix D.isFiniteType).toCoxeterSystem.exists_leftDescent_of_ne_one hw1
  refine ⟨i, fun x hx => ?_⟩
  have hdesc : (coxeterMatrix D.isFiniteType).toCoxeterSystem.IsRightDescent w⁻¹ i :=
    ((coxeterMatrix D.isFiniteType).toCoxeterSystem.isRightDescent_inv_iff).2 hi
  have hneg := ht_weylAction_single_neg hdesc
  have hαr : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  set β : Fin D.rank → ℤ := weylAction D.isFiniteType w⁻¹ (Pi.single i 1) with hβ
  have hβr : β ∈ D.roots := weylAction_mem_roots D.isFiniteType w⁻¹ hαr
  have hγr : -β ∈ D.roots := (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem β hβr
  have hγpos : 0 < ht (-β) := by rw [ht_neg]; omega
  have hmem : (nrep hct w)⁻¹ * x * nrep hct w ∈ D.rootGroup (-β) := by
    have h1 := nrep_inv_conj_mem hct w ((RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem
      _ hαr) hx
    have h2 : weylAction D.isFiniteType w⁻¹ (-Pi.single i 1) = -β := by
      rw [map_neg]
    rwa [h2] at h1
  have hyB : (nrep hct w)⁻¹ * x * nrep hct w ∈ borel D H :=
    posUnipotent_le_borel (rootGroup_le_posUnipotent hγr hγpos hmem)
  have := mul_mem (mul_mem hnA (hBA hyB)) (inv_mem hnA)
  simpa [mul_assoc] using this

@[expose] def HasOrderThree (D : UniversalRootDatum K) (i : Fin D.rank) : Prop :=
  ∃ x ∈ D.rootGroup (Pi.single i 1), ∃ y ∈ D.rootGroup (-Pi.single i 1),
    (x * y) ^ 3 = 1 ∧ ∃ c : K, x * y * c ≠ c * (x * y)

@[expose] def HasSL2Node (D : UniversalRootDatum K) (i : Fin D.rank) (F : Type*) [Field F] : Prop :=
  ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* K, Function.Injective φ ∧
    (∀ c, φ (sl2Upper c) ∈ D.rootGroup (Pi.single i 1)) ∧
    ∀ c, φ (sl2Lower c) ∈ D.rootGroup (-Pi.single i 1)

end Overgroups

structure BorelQuotient {K Y : Type*} [Group K] [Group Y] (D : UniversalRootDatum K)
    (n : Fin D.rank → K) (H : Fin D.rank → Subgroup K) (π : K →* Y) (M : ℕ) : Prop where
  ct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H
  extras : SteinbergExtras D n H
  pGroup : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ)
  surj : Function.Surjective π
  odd : Odd M
  torus_pow : ∀ i, ∀ g ∈ H i, g ^ M = 1
  ker_central : ∀ z ∈ π.ker, z ∈ Subgroup.center K
  ker_pow : ∀ z ∈ π.ker, z ^ M = 1

section Quotient

variable {K Y : Type*} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

omit [Finite Y] in
theorem BorelQuotient.not_dvd_index (h : BorelQuotient D n H π M) :
    ¬ 2 ∣ (posUnipotent D).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact not_dvd_index_posUnipotent h.ct h.extras h.pGroup (Nat.coprime_two_left.2 h.odd)
    h.torus_pow

omit [Finite Y] in
theorem BorelQuotient.normalizer_map_posUnipotent (h : BorelQuotient D n H π M) :
    Subgroup.normalizer (((posUnipotent D).map π : Subgroup Y) : Set Y) =
      (borel D H).map π := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 (posUnipotent D) := isPGroup_iSup_pos h.extras h.pGroup
  apply le_antisymm
  · intro y hy
    obtain ⟨k, rfl⟩ := h.surj y
    have hk : k ∈ Subgroup.normalizer (posUnipotent D : Set K) := by
      apply Subgroup.mem_normalizer_fintype
      intro u hu
      have hπu : π (k * u * k⁻¹) ∈ (posUnipotent D).map π := by
        have := (Subgroup.mem_normalizer_iff.1 hy (π u)).1 ⟨u, hu, rfl⟩
        simpa using this
      obtain ⟨u', hu', hu'e⟩ := hπu
      have hz : u'⁻¹ * (k * u * k⁻¹) ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hu'e, inv_mul_cancel]
      have hzM := h.ker_pow _ hz
      have hcen := Subgroup.mem_center_iff.1 (h.ker_central _ hz)
      have e : k * u * k⁻¹ = u' * (u'⁻¹ * (k * u * k⁻¹)) := by group
      have hcomm : Commute u' (k * u * k⁻¹) := by
        have hc : Commute u' (u'⁻¹ * (k * u * k⁻¹)) := hcen u'
        rw [e]
        exact (Commute.refl u').mul_right hc
      obtain ⟨r, hr⟩ := hU2 ⟨u', hu'⟩
      obtain ⟨s, hs⟩ := hU2 ⟨u, hu⟩
      have hr' : u' ^ 2 ^ r = 1 := congrArg Subtype.val hr
      have hs' : u ^ 2 ^ s = 1 := congrArg Subtype.val hs
      have hs'' : (k * u * k⁻¹) ^ 2 ^ s = 1 := by
        rw [conj_pow, hs', mul_one, mul_inv_cancel]
      have hz1 := eq_one_of_central_odd h.odd hzM rfl hcomm hr' hs''
      have : k * u * k⁻¹ = u' := by rw [e, hz1, mul_one]
      rw [this]
      exact hu'
    exact ⟨k, normalizer_posUnipotent_le_borel h.ct h.extras hk, rfl⟩
  · exact (Subgroup.map_mono (LieType.Steinberg.borel_le_normalizer_posUnipotent h.ct)).trans
      (Subgroup.le_normalizer_map π)

theorem BorelQuotient.exists_conj_eq (h : BorelQuotient D n H π M) (T : Sylow 2 Y) :
    ∃ π' : K →* Y, Function.Surjective π' ∧ π'.ker = π.ker ∧
      (T : Subgroup Y) = (posUnipotent D).map π' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 (posUnipotent D) := isPGroup_iSup_pos h.extras h.pGroup
  have hidx : ¬ 2 ∣ ((posUnipotent D).map π).index := fun hd =>
    h.not_dvd_index (hd.trans (Subgroup.index_map_dvd _ h.surj))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y ((hU2.map π).toSylow hidx) T
  refine ⟨(MulAut.conj g).toMonoidHom.comp π, (MulAut.conj g).surjective.comp h.surj, ?_, ?_⟩
  · ext z
    simp [MonoidHom.mem_ker]
  · rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    change Subgroup.map (MulAut.conj g).toMonoidHom ((posUnipotent D).map π) = _
    rw [Subgroup.map_map]

theorem BorelQuotient.three_dvd_card (h : BorelQuotient D n H π M)
    (h3 : ∀ i, HasOrderThree D i) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : 3 ∣ Nat.card J := by
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : borel D H ≤ J.comap π' := fun b hb => by
    rw [Subgroup.mem_comap]
    exact hNJ (by rw [hNπ]; exact ⟨b, hb, rfl⟩)
  have hne : J.comap π' ≠ borel D H := by
    intro he
    apply hJ
    rw [hNπ, ← he, Subgroup.map_comap_eq_self_of_surjective hπ']
  obtain ⟨i, hi⟩ := exists_negRoot_le_of_borel_lt h.ct h.extras hBJ hne
  obtain ⟨x, hx, y, hy, h3', c, hc⟩ := h3 i
  have hxB : x ∈ borel D H := posUnipotent_le_borel (rootGroup_le_posUnipotent
    ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i) (ht_single_pos i) hx)
  have hgJ : π' (x * y) ∈ J := mul_mem (hBJ hxB) (hi hy)
  have hne1 : π' (x * y) ≠ 1 := by
    intro h1
    exact hc (Subgroup.mem_center_iff.1 (hQ.ker_central _ h1) c).symm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (π' (x * y)) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, h3', map_one]) hne1
  have := orderOf_dvd_natCard (⟨π' (x * y), hgJ⟩ : J)
  rwa [← Subgroup.orderOf_coe, Subgroup.coe_mk, hord] at this

end Quotient

section SL2

variable {F : Type*} [Field F] [CharP F 2]

theorem coe_sl2_upper_lower : ((sl2Upper (1 : F) * sl2Lower 1 :
    Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 1] := by
  have h2 : (1 : F) + 1 = 0 := by simpa [one_add_one_eq_two] using CharP.cast_eq_zero F 2
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem sl2_upper_lower_cube : (sl2Upper (1 : F) * sl2Lower 1) ^ 3 = 1 := by
  have h2 : (1 : F) + 1 = 0 := by simpa [one_add_one_eq_two] using CharP.cast_eq_zero F 2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_sl2_upper_lower]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem sl2_upper_lower_not_commute :
    (sl2Upper (1 : F) * sl2Lower 1) * sl2Upper 1 ≠ sl2Upper 1 * (sl2Upper 1 * sl2Lower 1) := by
  have h2 : (1 : F) + 1 = 0 := by simpa [one_add_one_eq_two] using CharP.cast_eq_zero F 2
  intro h
  have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [Matrix.mul_apply, Fin.sum_univ_two, coe_sl2Upper, coe_sl2Lower, h2] at this

theorem HasSL2Node.hasOrderThree {K : Type*} [Group K] {D : UniversalRootDatum K}
    {i : Fin D.rank} (h : HasSL2Node D i F) : HasOrderThree D i := by
  obtain ⟨φ, hφ, hx, hy⟩ := h
  exact ⟨φ (sl2Upper 1), hx 1, φ (sl2Lower 1), hy 1, by
    rw [← map_mul, ← map_pow, sl2_upper_lower_cube, map_one],
    φ (sl2Upper 1), fun h => sl2_upper_lower_not_commute (hφ (by simpa [map_mul] using h))⟩

end SL2

theorem sub_one_dvd_sq_sub_one (q : ℕ) : q - 1 ∣ q ^ 2 - 1 := by
  simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow q 1 2

theorem exists_card_eq_two_pow (F : Type*) [Field F] [Finite F] [CharP F 2] :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card F = 2 ^ f := by
  have := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem odd_card_sub_one (F : Type*) [Field F] [Finite F] [CharP F 2] : Odd (Nat.card F - 1) := by
  obtain ⟨f, hf, hcard⟩ := exists_card_eq_two_pow F
  rw [hcard]
  have h1 : 1 ≤ 2 ^ (f - 1) := Nat.one_le_two_pow
  have h2 : (2 : ℕ) ^ f = 2 * 2 ^ (f - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  exact ⟨2 ^ (f - 1) - 1, by omega⟩

end CFSG.AGLEmbedding.ParabHub

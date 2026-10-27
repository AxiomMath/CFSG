module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.RankThree.Native.DerivedGenerators

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge

theorem exists_large_conj_le_of_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Y H A : Subgroup G} (hHY : H ≤ Y) (hAY : A ≤ Y) (hA : IsPGroup p A)
    (hord : (Nat.card Y).factorization p ≤ (Nat.card H).factorization p + 1) :
    ∃ g ∈ Y, ∃ E ≤ A, Nat.card A ≤ p * Nat.card E ∧ ∀ x ∈ E, g * x * g⁻¹ ∈ H := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨S₁⟩ : Nonempty (Sylow p ↥H) := inferInstance
  set C : Subgroup G := (S₁ : Subgroup ↥H).map H.subtype with hCdef
  have hCH : C ≤ H := Subgroup.map_subtype_le _
  have hCcard : Nat.card C = p ^ (Nat.card H).factorization p := by
    rw [hCdef, Subgroup.card_map_of_injective H.subtype_injective, Sylow.card_eq_multiplicity]
  have hCp : IsPGroup p ↥(C.subgroupOf Y) := (S₁.isPGroup'.map H.subtype).comap_subtype
  obtain ⟨S₀, hS₀⟩ := IsPGroup.exists_le_sylow hCp
  have hAp : IsPGroup p ↥(A.subgroupOf Y) := hA.comap_subtype
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hAp
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Y P S₀
  set S : Subgroup G := (S₀ : Subgroup ↥Y).map Y.subtype with hSdef
  have hScard : Nat.card S = p ^ (Nat.card Y).factorization p := by
    rw [hSdef, Subgroup.card_map_of_injective Y.subtype_injective, Sylow.card_eq_multiplicity]
  have hCS : C ≤ S := fun x hx =>
    ⟨⟨x, hHY (hCH hx)⟩, hS₀ (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  set B : Subgroup G := A.map (MulAut.conj (g : G)).toMonoidHom with hBdef
  have hBS : B ≤ S := by
    rintro _ ⟨x, hxA, rfl⟩
    have hxP : (⟨x, hAY hxA⟩ : ↥Y) ∈ P := hP (Subgroup.mem_subgroupOf.2 hxA)
    have h1 : (MulAut.conj g) • (⟨x, hAY hxA⟩ : ↥Y) ∈ (g • P : Sylow p _) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ hxP
    rw [hg] at h1
    exact ⟨_, h1, rfl⟩
  have hCSidx : C.relIndex S ≤ p := by
    have h1 := Subgroup.relIndex_mul_card (H := C) (K := S)
    rw [inf_eq_left.2 hCS, hCcard, hScard] at h1
    have h2 : p ^ (Nat.card Y).factorization p ≤ p * p ^ (Nat.card H).factorization p := by
      rw [← pow_succ']
      exact Nat.pow_le_pow_right hp.pos (by omega)
    rw [← h1] at h2
    exact Nat.le_of_mul_le_mul_right h2 (pow_pos hp.pos _)
  have hCS0 : C.relIndex S ≠ 0 := by
    intro h0
    have h1 := Subgroup.relIndex_mul_card (H := C) (K := S)
    rw [h0, zero_mul, hScard] at h1
    exact (pow_pos hp.pos _).ne h1
  have hCB : C.relIndex B ≤ C.relIndex S := Subgroup.relIndex_le_of_le_right hBS hCS0
  have h2 := Subgroup.relIndex_mul_card (H := C) (K := B)
  refine ⟨g, g.2, (C ⊓ B).map (MulAut.conj (g : G)⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨y, ⟨-, x, hxA, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [show (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g : G)⁻¹⁻¹ = x by group]
  · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]
    have hAB : Nat.card A = Nat.card B :=
      (Subgroup.card_map_of_injective (MulAut.conj _).injective).symm
    rw [hAB, ← h2]
    exact Nat.mul_le_mul_right _ (hCB.trans hCSidx)
  · rintro _ ⟨y, ⟨hyC, -⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show (g : G) * ((g : G)⁻¹ * y * (g : G)⁻¹⁻¹) * (g : G)⁻¹ = y by group]
    exact hCH hyC

section Index

variable {τ : Tag}


theorem isInnerLocallyBalanced_adjoint_of_index (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (hord : (Nat.card (adjointGroup τ K)).factorization p ≤
      (Nat.card (torusGroup τ K)).factorization p + 1) :
    IsInnerLocallyBalanced p (adjointGroup τ K) := by
  intro D hD hcard hDin H hH _
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨t, htp, ht⟩ := exists_orderOf_units_of_dvd hp hp2 hpq
  have hinj := mulAut_conj_injective_adjointGroup (τ := τ) (K := K)
  set D₀ := D.comap (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) with hD₀
  have hDD : D₀.map MulAut.conj = D := Subgroup.map_comap_eq_self hDin
  have hD₀card : Nat.card D₀ = p ^ 3 := by
    rw [← hcard, ← hDD, Subgroup.card_map_of_injective hinj]
  have hpow₀ : ∀ x ∈ D₀, x ^ p = 1 := fun x hx => by
    have hx' : (MulAut.conj x) ^ p = 1 := hD.2 _ hx
    exact hinj (by rw [map_pow, hx', map_one])
  set A : Subgroup (ModGL τ K) := D₀.map (adjointGroup τ K).subtype with hAdef
  have hAcard : Nat.card A = p ^ 3 := by
    rw [hAdef, Subgroup.card_map_of_injective (adjointGroup τ K).subtype_injective, hD₀card]
  have hAp : IsPGroup p A := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    refine ⟨1, Subtype.ext ?_⟩
    have h1 : ((x : ModGL τ K)) ^ p = 1 := by
      rw [← Subgroup.coe_pow, hpow₀ x hx, Subgroup.coe_one]
    simpa using h1
  obtain ⟨g, hg, E, hEA, hEcard, hEH⟩ :=
    exists_large_conj_le_of_sylow CFSG.RankThree.PartOne.K133H.torusGroup_le_adjointGroup'
      (Subgroup.map_subtype_le D₀) hAp hord
  set E₀ : Subgroup (adjointGroup τ K) := E.comap (adjointGroup τ K).subtype with hE₀def
  have hE₀D₀ : E₀ ≤ D₀ := fun x hx => by
    obtain ⟨y, hy, hyx⟩ := hEA hx
    have hxy : y = x := Subtype.ext hyx
    exact hxy ▸ hy
  have hE₀card : Nat.card E₀ = Nat.card E := by
    have hEY : E ≤ (adjointGroup τ K).subtype.range := by
      rw [Subgroup.range_subtype]
      exact hEA.trans (Subgroup.map_subtype_le D₀)
    rw [← Subgroup.card_map_of_injective (adjointGroup τ K).subtype_injective, hE₀def,
      Subgroup.map_comap_eq_self hEY]
  set Ed := E₀.map (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) with hEddef
  have hEdD : Ed ≤ D := by
    rw [← hDD]
    exact Subgroup.map_mono hE₀D₀
  have hEdcard : p < Nat.card Ed := by
    rw [hEddef, Subgroup.card_map_of_injective hinj, hE₀card]
    rw [hAcard] at hEcard
    have h1 : p ^ 2 ≤ Nat.card E := by
      have h3 : p * p ^ 2 ≤ p * Nat.card E := by
        rw [← pow_succ']
        exact hEcard
      exact Nat.le_of_mul_le_mul_left h3 hp.pos
    have h2 : p < p ^ 2 := by
      have := hp.two_le
      nlinarith
    omega
  have hEdtor : ∀ x ∈ Ed.comap (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)),
      (((⟨g, hg⟩ : adjointGroup τ K) * x * (⟨g, hg⟩ : adjointGroup τ K)⁻¹ :
        adjointGroup τ K) : ModGL τ K) ∈ torusGroup τ K := by
    intro x hx
    rw [hEddef, Subgroup.comap_map_eq_self_of_injective hinj] at hx
    have h1 := hEH (x : ModGL τ K) hx
    simpa using h1
  exact le_bot_iff.1 ((localDeltaIn_antitone H hEdD).trans
    (localDeltaIn_eq_bot_of_conj_toral hp htp ht hH (hEdD.trans hDin)
      (fun x hx => hD.2 x (hEdD hx)) hEdcard ⟨g, hg⟩ hEdtor).le)

end Index

section Orders

variable {K : Type} [Field K]

theorem not_five_dvd_of_dvd_sub_one {n : ℕ} (hn : 1 ≤ n) (h5 : 5 ∣ n - 1) : ¬ 5 ∣ n := by
  intro h
  have h1 : 5 ∣ n - (n - 1) := Nat.dvd_sub h h5
  rw [show n - (n - 1) = 1 by omega] at h1
  norm_num at h1

theorem orderOf_natCast_zmod_five_of_dvd {n : ℕ} (h5 : 5 ∣ n - 1) (hn : 1 ≤ n) :
    orderOf ((n : ℕ) : ZMod 5) = 1 := by
  rw [orderOf_eq_one_iff]
  have h1 : ((n - 1 : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h5
  rw [Nat.cast_sub hn, Nat.cast_one, sub_eq_zero] at h1
  exact h1

theorem five_dvd_sq_sub_one_iff_or {n : ℕ} : 5 ∣ n ^ 2 - 1 ↔ 5 ∣ n - 1 ∨ 5 ∣ n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · have h : n ^ 2 - 1 = (n + 1) * (n - 1) := by
      zify [hn, Nat.one_le_pow 2 n hn]
      ring
    rw [h, Nat.Prime.dvd_mul Nat.prime_five, or_comm]

theorem ordProj_five_pow_sub_one [Finite K] (h5 : 5 ∣ Nat.card K - 1) {d : ℕ} (hd : d ≠ 0) :
    5 ^ (Nat.card K ^ d - 1).factorization 5 =
      5 ^ (Nat.card K - 1).factorization 5 * 5 ^ d.factorization 5 := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have h := ordProj_pow_sub_one_of_dvd Nat.prime_five (by norm_num)
    (not_five_dvd_of_dvd_sub_one (by omega) h5) hq2
    (orderOf_natCast_zmod_five_of_dvd h5 (by omega)) hd
  rwa [one_mul, pow_one] at h


theorem factorization_five_card_adjointGroup_E6 (K : Type) [Field K] [Finite K]
    (h5 : 5 ∣ Nat.card K - 1) :
    (Nat.card (adjointGroup Tag.E6 K)).factorization 5 =
      6 * (Nat.card K - 1).factorization 5 + 1 := by
  have h := ordProj_card_adjointGroup_E (τ := Tag.E6) (K := K) (by simp) Nat.prime_five
    (by norm_num) (not_five_dvd_of_dvd_sub_one (Finite.one_lt_card (α := K)).le h5)
  simp only [degreesE, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [ordProj_five_pow_sub_one h5 (by norm_num : (2 : ℕ) ≠ 0),
    ordProj_five_pow_sub_one h5 (by norm_num : (5 : ℕ) ≠ 0),
    ordProj_five_pow_sub_one h5 (by norm_num : (6 : ℕ) ≠ 0),
    ordProj_five_pow_sub_one h5 (by norm_num : (8 : ℕ) ≠ 0),
    ordProj_five_pow_sub_one h5 (by norm_num : (9 : ℕ) ≠ 0),
    ordProj_five_pow_sub_one h5 (by norm_num : (12 : ℕ) ≠ 0),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 2),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 6),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 8),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 9),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 12),
    Nat.Prime.factorization_self Nat.prime_five] at h
  refine Nat.pow_right_injective (by norm_num : 2 ≤ 5) ?_
  change 5 ^ _ = 5 ^ _
  rw [h]
  ring

theorem factorization_five_card_adjointGroup_E7 (K : Type) [Field K] [Finite K]
    (h5 : 5 ∣ Nat.card K - 1) :
    (Nat.card (adjointGroup Tag.E7 K)).factorization 5 =
      7 * (Nat.card K - 1).factorization 5 + 1 := by
  have h := ordProj_card_adjointGroup_E (τ := Tag.E7) (K := K) (by simp) Nat.prime_five
    (by norm_num) (not_five_dvd_of_dvd_sub_one (Finite.one_lt_card (α := K)).le h5)
  simp only [degreesE, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  have h10 : 5 ^ (10 : ℕ).factorization 5 = 5 := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_five,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 2)]
    norm_num
  rw [ordProj_five_pow_sub_one h5 (by norm_num : (2 : ℕ) ≠ 0),
    ordProj_five_pow_sub_one h5 (by norm_num : (6 : ℕ) ≠ 0),
    ordProj_five_pow_sub_one h5 (by norm_num : (8 : ℕ) ≠ 0),
    ordProj_five_pow_sub_one h5 (by norm_num : (10 : ℕ) ≠ 0),
    ordProj_five_pow_sub_one h5 (by norm_num : (12 : ℕ) ≠ 0),
    ordProj_five_pow_sub_one h5 (by norm_num : (14 : ℕ) ≠ 0),
    ordProj_five_pow_sub_one h5 (by norm_num : (18 : ℕ) ≠ 0),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 2),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 6),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 8),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 12),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 14),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 18), h10] at h
  refine Nat.pow_right_injective (by norm_num : 2 ≤ 5) ?_
  change 5 ^ _ = 5 ^ _
  rw [h]
  ring

theorem factorization_five_card_torusGroup_E6 (K : Type) [Field K] [Finite K] :
    (Nat.card (torusGroup Tag.E6 K)).factorization 5 = 6 * (Nat.card K - 1).factorization 5 := by
  have h := CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E6 (K := K)
  have hq1 : Nat.card K - 1 ≠ 0 := by
    have := Finite.one_lt_card (α := K)
    omega
  have hT : Nat.card (torusGroup Tag.E6 K) ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at h
    exact pow_ne_zero 6 hq1 h.symm
  have hg : (Nat.card K - 1).gcd 3 ≠ 0 := Nat.gcd_ne_zero_right (by norm_num)
  have h1 := congrArg (fun n => n.factorization 5) h
  have hg5 : ((Nat.card K - 1).gcd 3).factorization 5 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h5 => by
      have := h5.trans (Nat.gcd_dvd_right _ _)
      norm_num at this
  rw [Nat.factorization_mul hT hg, Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul, hg5, add_zero] at h1
  exact h1

theorem factorization_five_card_torusGroup_E7 (K : Type) [Field K] [Finite K] :
    (Nat.card (torusGroup Tag.E7 K)).factorization 5 = 7 * (Nat.card K - 1).factorization 5 := by
  have h := CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E7 (K := K)
  have hq1 : Nat.card K - 1 ≠ 0 := by
    have := Finite.one_lt_card (α := K)
    omega
  have hT : Nat.card (torusGroup Tag.E7 K) ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at h
    exact pow_ne_zero 7 hq1 h.symm
  have hg : (Nat.card K - 1).gcd 2 ≠ 0 := Nat.gcd_ne_zero_right (by norm_num)
  have h1 := congrArg (fun n => n.factorization 5) h
  have hg5 : ((Nat.card K - 1).gcd 2).factorization 5 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h5 => by
      have := h5.trans (Nat.gcd_dvd_right _ _)
      norm_num at this
  rw [Nat.factorization_mul hT hg, Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul, hg5, add_zero] at h1
  exact h1

end Orders

section Five


theorem isInnerLocallyBalanced_adjointE6_five (K : Type) [Field K] [Finite K]
    (h5 : 5 ∣ Nat.card K - 1) : IsInnerLocallyBalanced 5 (adjointGroup Tag.E6 K) :=
  isInnerLocallyBalanced_adjoint_of_index K Nat.prime_five (by norm_num) h5 (le_of_eq (by
    rw [factorization_five_card_adjointGroup_E6 K h5, factorization_five_card_torusGroup_E6]))

theorem isInnerLocallyBalanced_adjointE7_five (K : Type) [Field K] [Finite K]
    (h5 : 5 ∣ Nat.card K - 1) : IsInnerLocallyBalanced 5 (adjointGroup Tag.E7 K) :=
  isInnerLocallyBalanced_adjoint_of_index K Nat.prime_five (by norm_num) h5 (le_of_eq (by
    rw [factorization_five_card_adjointGroup_E7 K h5, factorization_five_card_torusGroup_E7]))


theorem crossCharInnerAt_E6_five_dvd_sub_one :
    CrossCharInnerAt .E6 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .E6 q ∧ 5 ∣ q.card - 1) ∧ p = 5 := by
  rintro ⟨d, hv⟩ _ p _ _ _ ⟨⟨q, hd, h5⟩, rfl⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  rw [← hK] at h5
  exact (isInnerLocallyBalanced_adjointE6_five K h5).of_mulEquiv e

theorem crossCharInnerAt_E7_five_dvd_sub_one :
    CrossCharInnerAt .E7 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .E7 q ∧ 5 ∣ q.card - 1) ∧ p = 5 := by
  rintro ⟨d, hv⟩ _ p _ _ _ ⟨⟨q, hd, h5⟩, rfl⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  rw [← hK] at h5
  exact (isInnerLocallyBalanced_adjointE7_five K h5).of_mulEquiv e

theorem crossCharInnerAt_E6_five_of_add_one
    (h : CrossCharInnerAt .E6 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .E6 q ∧ 5 ∣ q.card + 1) ∧ p = 5) :
    CrossCharInnerAt .E6 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .E6 q ∧ 5 ∣ q.card ^ 2 - 1) ∧ p = 5 := by
  rintro idx hk p hp hp2 hc ⟨⟨q, hd, h5⟩, hp5⟩
  rcases five_dvd_sq_sub_one_iff_or.1 h5 with h1 | h1
  · exact crossCharInnerAt_E6_five_dvd_sub_one idx hk p hp hp2 hc ⟨⟨q, hd, h1⟩, hp5⟩
  · exact h idx hk p hp hp2 hc ⟨⟨q, hd, h1⟩, hp5⟩

theorem crossCharInnerAt_E7_five_of_add_one
    (h : CrossCharInnerAt .E7 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .E7 q ∧ 5 ∣ q.card + 1) ∧ p = 5) :
    CrossCharInnerAt .E7 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .E7 q ∧ 5 ∣ q.card ^ 2 - 1) ∧ p = 5 := by
  rintro idx hk p hp hp2 hc ⟨⟨q, hd, h5⟩, hp5⟩
  rcases five_dvd_sq_sub_one_iff_or.1 h5 with h1 | h1
  · exact crossCharInnerAt_E7_five_dvd_sub_one idx hk p hp hp2 hc ⟨⟨q, hd, h1⟩, hp5⟩
  · exact h idx hk p hp hp2 hc ⟨⟨q, hd, h1⟩, hp5⟩

end Five

end CFSG.HardMathSupport.Timmesfeld.CrossChar

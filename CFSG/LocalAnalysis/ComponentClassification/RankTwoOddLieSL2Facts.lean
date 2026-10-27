module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.ClassicalInvolution.SL2Facts

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Open CFSG.ComponentClassification.AS76b CFSG.ClassicalInvolution
open scoped MatrixGroups commutatorElement

variable {H : Type*} [Group H] {F : Type*} [Field F]

theorem ringChar_ne_two_of_odd [Finite F] (hF : Odd (Nat.card F)) : ringChar F ≠ 2 := by
  intro h
  apply CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hF
  have := ringChar.Nat.cast_ringChar (R := F)
  rw [h] at this
  exact_mod_cast this

theorem transvection_pow_eq {i j : Fin 2} (hij : i ≠ j) (c : F) (m : ℕ) :
    Matrix.SpecialLinearGroup.transvection hij c ^ m =
      Matrix.SpecialLinearGroup.transvection hij (m • c) := by
  induction m with
  | zero => rw [pow_zero, zero_smul, Matrix.SpecialLinearGroup.transvection_coeff_zero]
  | succ m ih =>
    rw [pow_succ, ih, ← Matrix.SpecialLinearGroup.transvection_add, succ_nsmul]

theorem odd_orderOf_transvection [Finite F] (hF : Odd (Nat.card F)) {i j : Fin 2} (hij : i ≠ j)
    (c : F) :
    Odd (orderOf (Matrix.SpecialLinearGroup.transvection hij c)) := by
  have hp : (ringChar F).Prime := CharP.char_is_prime F _
  have h1 : Matrix.SpecialLinearGroup.transvection hij c ^ ringChar F = 1 := by
    rw [transvection_pow_eq, nsmul_eq_mul, ringChar.Nat.cast_ringChar, zero_mul,
      Matrix.SpecialLinearGroup.transvection_coeff_zero]
  have hodd : Odd (ringChar F) := hp.odd_of_ne_two (ringChar_ne_two_of_odd hF)
  exact hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)

theorem sl2_mem_closure_odd [Finite F] (hF : Odd (Nat.card F)) (A : SL(2, F)) :
    A ∈ closure {x : SL(2, F) | Odd (orderOf x)} :=
  Matrix.SL2.transvection_induction _
    (fun _ _ h c => subset_closure (odd_orderOf_transvection hF h c))
    (fun _ _ => mul_mem) A

theorem le_of_forall_odd_mem [Finite F] {J K : Subgroup H} (e : J ≃* SL(2, F))
    (hF : Odd (Nat.card F))
    (hK : ∀ x ∈ J, Odd (orderOf x) → x ∈ K) : J ≤ K := by
  intro x hx
  have h := sl2_mem_closure_odd hF (e ⟨x, hx⟩)
  have key : ((e.symm (e ⟨x, hx⟩) : J) : H) ∈ K := by
    refine Subgroup.closure_induction (p := fun A _ => ((e.symm A : J) : H) ∈ K) ?_ ?_ ?_ ?_ h
    · intro A hA
      refine hK _ (e.symm A).2 ?_
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact hA
    · simp [K.one_mem]
    · intro A B _ _ hA hB
      simpa using K.mul_mem hA hB
    · intro A _ hA
      simpa using K.inv_mem hA
  simpa using key

abbrev centralInv {J : Subgroup H} (e : J ≃* SL(2, F)) : H := (e.symm (-1) : J)

theorem centralInv_mem {J : Subgroup H} (e : J ≃* SL(2, F)) : centralInv e ∈ J :=
  (e.symm (-1)).2

theorem eq_one_or_centralInv_of_mem_centralizer {J : Subgroup H} (e : J ≃* SL(2, F)) {x : H}
    (hx : x ∈ J) (hc : x ∈ centralizer (J : Set H)) : x = 1 ∨ x = centralInv e := by
  have hz : (⟨x, hx⟩ : J) ∈ center J := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((mem_centralizer_iff.mp hc) g g.2)
  rw [mem_center_iff_of_equiv_sl2 e, mem_center_sl2_iff] at hz
  rcases hz with h | h
  · left
    have := congrArg Subtype.val ((MulEquiv.eq_symm_apply e).mpr h)
    simpa using this
  · right
    have := congrArg Subtype.val ((MulEquiv.eq_symm_apply e).mpr h)
    simpa using this

theorem centralInv_mem_centralizer {J : Subgroup H} (e : J ≃* SL(2, F)) :
    centralInv e ∈ centralizer (J : Set H) := by
  rw [mem_centralizer_iff]
  intro g hg
  have h : e.symm (-1) ∈ center J := by
    rw [mem_center_iff_of_equiv_sl2 e, MulEquiv.apply_symm_apply, mem_center_sl2_iff]
    exact Or.inr rfl
  rw [Subgroup.mem_center_iff] at h
  exact (congrArg Subtype.val (h ⟨g, hg⟩))

theorem centralInv_sq {J : Subgroup H} (e : J ≃* SL(2, F)) : centralInv e ^ 2 = 1 := by
  have : (e.symm (-1)) ^ 2 = 1 := by
    rw [← map_pow, neg_one_sq, map_one]
  have := congrArg Subtype.val this
  simpa using this

theorem centralInv_ne_one [Finite F] {J : Subgroup H} (e : J ≃* SL(2, F)) (hF : Odd (Nat.card F)) :
    centralInv e ≠ 1 := by
  intro h
  apply sl2_neg_one_ne_one hF
  have h1 : e.symm (-1) = 1 := Subtype.ext h
  rw [← e.apply_symm_apply (-1), h1, map_one]

theorem eq_one_or_centralInv_of_sq [Finite F] {J : Subgroup H} (e : J ≃* SL(2, F))
    (hF : Odd (Nat.card F))
    {x : H} (hx : x ∈ J) (hx2 : x ^ 2 = 1) : x = 1 ∨ x = centralInv e := by
  have hx2' : (⟨x, hx⟩ : J) ^ 2 = 1 := Subtype.ext (by simpa using hx2)
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx2') with h | h
  · left
    have := orderOf_eq_one_iff.mp h
    simpa using congrArg Subtype.val this
  · right
    have := (orderOf_eq_two_iff_of_equiv_sl2 hF e _).mp h
    simpa using congrArg Subtype.val this

theorem mem_of_odd_of_relIndex {N O : Subgroup H} (hOn : (O.subgroupOf N).Normal)
    {k : ℕ} (hk : O.relIndex N = 2 ^ k) {x : H} (hxN : x ∈ N) (hx : Odd (orderOf x)) : x ∈ O := by
  set x' : N := ⟨x, hxN⟩
  have h1 : x' ^ (O.subgroupOf N).index ∈ O.subgroupOf N := Subgroup.pow_index_mem _ x'
  rw [← Subgroup.relIndex, hk] at h1
  have hcop : (2 ^ k).Coprime (orderOf x') := by
    rw [Subgroup.orderOf_mk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hx)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have h2 : x' ∈ O.subgroupOf N := by
    rw [← hm]
    exact (O.subgroupOf N).pow_mem h1 m
  exact mem_subgroupOf.mp h2

theorem le_centralizer_of_isTwoNilpotent [Finite H] [Finite F] {J N : Subgroup H}
    (e : J ≃* SL(2, F))
    (hF : Odd (Nat.card F)) (hNJ : N ≤ J) (hJN : J ≤ normalizer (N : Set H))
    (hN : IsTwoNilpotent N) (h2 : ∀ x ∈ N, ∀ k : ℕ, x ^ 2 ^ k = 1 → x ^ 2 = 1) :
    N ≤ centralizer (J : Set H) := by
  obtain ⟨O, hON, hOn, hOodd, k, hk⟩ := hN
  have hJO : ∀ j ∈ J, ∀ x ∈ O, j * x * j⁻¹ ∈ O := by
    intro j hj x hx
    refine mem_of_odd_of_relIndex hOn hk ((mem_normalizer_iff.mp (hJN hj) x).mp (hON hx)) ?_
    rw [show j * x * j⁻¹ = MulAut.conj j x from rfl, MulEquiv.orderOf_eq]
    exact hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hx)
  have hO : O.subgroupOf J = ⊥ := by
    have h3 : 3 ≤ Nat.card F := by
      have h2 : 2 ≤ Nat.card F := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      rcases hF with ⟨m, hm⟩
      omega
    refine normal_odd_of_equiv_sl2 hF h3 e _ ⟨fun x hx j => ?_⟩ ?_
    · rw [mem_subgroupOf] at hx ⊢
      exact hJO j j.2 x hx
    · rwa [Nat.card_congr (subgroupOfEquivOfLe (hON.trans hNJ)).toEquiv]
  have hObot : O = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hNJ (hON hx)⟩ : J) ∈ O.subgroupOf J := mem_subgroupOf.mpr hx
    rw [hO, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  subst hObot
  intro x hx
  have hcard : Nat.card N = 2 ^ k := by
    rw [← hk, Subgroup.relIndex_bot_left]
  have hxk : x ^ 2 ^ k = 1 := by
    have := Subgroup.orderOf_dvd_natCard N hx
    rw [hcard] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  rcases eq_one_or_centralInv_of_sq e hF (hNJ hx) (h2 x hx k hxk) with rfl | rfl
  · exact one_mem _
  · exact centralInv_mem_centralizer e

theorem mem_centralizer_of_commutator_mem [Finite F] {J : Subgroup H} (e : J ≃* SL(2, F))
    (hF : Odd (Nat.card F)) {τ : H} (hτ : τ ∈ normalizer (J : Set H))
    (h : ∀ x ∈ J, τ * x * τ⁻¹ * x⁻¹ ∈ centralizer (J : Set H)) :
    τ ∈ centralizer (J : Set H) := by
  have hle : J ≤ centralizer ({τ} : Set H) := by
    refine le_of_forall_odd_mem e hF fun x hx hodd => ?_
    set c := τ * x * τ⁻¹ * x⁻¹ with hc
    have hcJ : c ∈ J := J.mul_mem ((mem_normalizer_iff.mp hτ x).mp hx) (J.inv_mem hx)
    have hcC := h x hx
    have hcx : c * x = x * c := (mem_centralizer_iff.mp hcC x hx).symm
    have hτx : τ * x * τ⁻¹ = c * x := by rw [hc]; group
    have hcm : c ^ orderOf x = 1 := by
      have h1 : (τ * x * τ⁻¹) ^ orderOf x = 1 := by
        rw [conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
      rw [hτx, (Commute.mul_pow hcx _), pow_orderOf_eq_one, mul_one] at h1
      exact h1
    have hc2 : c ^ 2 = 1 := by
      rcases eq_one_or_centralInv_of_mem_centralizer e hcJ hcC with h1 | h1
      · rw [h1, one_pow]
      · rw [h1, centralInv_sq]
    have hc1 : c = 1 := by
      obtain ⟨m, hm⟩ := hodd
      rw [hm, pow_succ, pow_mul, hc2, one_pow, one_mul] at hcm
      exact hcm
    rw [mem_centralizer_singleton_iff]
    have : τ * x * τ⁻¹ = x := by rw [hτx, hc1, one_mul]
    calc x * τ = τ * x * τ⁻¹ * τ := by rw [this]
      _ = τ * x := by group
  rw [mem_centralizer_iff]
  intro x hx
  exact (mem_centralizer_singleton_iff.mp (hle hx))

@[expose] def tvU (F : Type*) [Field F] : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def tvL (F : Type*) [Field F] : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

theorem tvU_coe : ((tvU F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := rfl

theorem tvL_coe : ((tvL F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := rfl

theorem commutator_tv_coe :
    ((⁅tvU F, tvL F⁆ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![3, -1; 1, 0] := by
  rw [commutatorElement_def]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, tvU_coe,
    tvL_coe, Matrix.adjugate_fin_two_of, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp; ring

theorem commutator_tv_not_mem_center : (⁅tvU F, tvL F⁆ : SL(2, F)) ∉ center SL(2, F) := by
  rw [mem_center_sl2_iff]
  have key := congrFun (congrFun (commutator_tv_coe (F := F)) 1) 0
  rintro (h | h) <;> rw [h] at key <;> simp at key

theorem exists_commutator_not_mem_centralizer {J : Subgroup H} (e : J ≃* SL(2, F)) :
    ∃ a ∈ J, ∃ b ∈ J, ⁅a, b⁆ ∉ centralizer (J : Set H) := by
  refine ⟨e.symm (tvU F), (e.symm (tvU F)).2, e.symm (tvL F), (e.symm (tvL F)).2, fun hc => ?_⟩
  apply commutator_tv_not_mem_center (F := F)
  have hmem : ⁅e.symm (tvU F), e.symm (tvL F)⁆ ∈ center J := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have := (mem_centralizer_iff.mp hc) g g.2
    simpa [commutatorElement_def] using this
  rw [mem_center_iff_of_equiv_sl2 e, map_commutatorElement, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply] at hmem
  exact hmem

private theorem sl2Three_central_aux :
    ∀ c : SL(2, ZMod 3), (∀ g : SL(2, ZMod 3), c * (g * c * g⁻¹) = g * c * g⁻¹ * c) →
      c = 1 ∨ c = -1 := by
  decide +kernel

noncomputable def sl2RingEquiv {R S : Type*} [CommRing R] [CommRing S] (φ : R ≃+* S) :
    SL(2, R) ≃* SL(2, S) where
  toFun := Matrix.SpecialLinearGroup.map φ.toRingHom
  invFun := Matrix.SpecialLinearGroup.map φ.symm.toRingHom
  left_inv A := by ext i j; simp
  right_inv A := by ext i j; simp
  map_mul' := map_mul _

theorem le_centralizer_of_abelian [Finite F] {J N : Subgroup H} (e : J ≃* SL(2, F))
    (hF : Odd (Nat.card F))
    (hNJ : N ≤ J) (hJN : J ≤ normalizer (N : Set H)) (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) :
    N ≤ centralizer (J : Set H) := by
  by_cases h3 : Nat.card F = 3
  · classical
    have : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F = Fintype.card (ZMod 3) := by
      rw [← Nat.card_eq_fintype_card, h3, ZMod.card]
    set e' : J ≃* SL(2, ZMod 3) := e.trans (sl2RingEquiv (FiniteField.ringEquivOfCardEq hcard))
    intro c hc
    have hz : e' ⟨c, hNJ hc⟩ = 1 ∨ e' ⟨c, hNJ hc⟩ = -1 := by
      apply sl2Three_central_aux
      intro g
      set j := e'.symm g
      have hjc : (j : H) * c * (j : H)⁻¹ ∈ N := (mem_normalizer_iff.mp (hJN j.2) c).mp hc
      have h1 := hab c hc _ hjc
      have h2 : (⟨c, hNJ hc⟩ : J) * (j * ⟨c, hNJ hc⟩ * j⁻¹) =
          (j * ⟨c, hNJ hc⟩ * j⁻¹) * ⟨c, hNJ hc⟩ := Subtype.ext (by simpa [mul_assoc] using h1)
      have h3 := congrArg e' h2
      simpa [j, map_mul, map_inv] using h3
    have hcz : (⟨c, hNJ hc⟩ : J) ∈ center J := by
      rw [mem_center_iff_of_equiv_sl2 e', mem_center_sl2_iff]
      exact hz
    rw [mem_centralizer_iff]
    intro g hg
    rw [Subgroup.mem_center_iff] at hcz
    exact congrArg Subtype.val (hcz ⟨g, hg⟩)
  · have h4 : 4 ≤ Nat.card F := by
      have h2 : 2 ≤ Nat.card F := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      rcases hF with ⟨m, hm⟩
      omega
    have hNn : (N.subgroupOf J).Normal := ⟨fun x hx g => by
      rw [mem_subgroupOf] at hx ⊢
      exact (mem_normalizer_iff.mp (hJN g.2) x).mp hx⟩
    rcases normal_cases_of_equiv_sl2 h4 e (N.subgroupOf J) hNn with hb | hc | ht
    · intro x hx
      have : (⟨x, hNJ hx⟩ : J) ∈ N.subgroupOf J := mem_subgroupOf.mpr hx
      rw [hb, Subgroup.mem_bot] at this
      rw [show x = 1 from congrArg Subtype.val this]
      exact one_mem _
    · intro x hx
      have : (⟨x, hNJ hx⟩ : J) ∈ center J := hc ▸ mem_subgroupOf.mpr hx
      rw [mem_centralizer_iff]
      intro g hg
      rw [Subgroup.mem_center_iff] at this
      exact congrArg Subtype.val (this ⟨g, hg⟩)
    · exfalso
      have hJN' : J ≤ N := fun x hx => by
        have : (⟨x, hx⟩ : J) ∈ N.subgroupOf J := ht ▸ Subgroup.mem_top _
        exact mem_subgroupOf.mp this
      obtain ⟨a, ha, b, hb, hab'⟩ := exists_commutator_not_mem_centralizer e
      apply hab'
      have : ⁅a, b⁆ = 1 := by
        rw [commutatorElement_def, hab a (hJN' ha) b (hJN' hb)]
        group
      rw [this]
      exact one_mem _

end CFSG.ComponentClassification.RankTwoOddLie

module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FWN2Model
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Single
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.LocalAnalysis.ComponentInitial.GroupFusion
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LieType.Multipliers.L34Upper
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAutBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InvCls
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrOddOrbitWitness

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.FW

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr GrS4
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem commutatorElement_mul_mul_eq {a b c d : X} (hca : Commute c a) (hcb : Commute c b)
    (hcd : Commute c d) (hda : Commute d a) (hdb : Commute d b) : ⁅c * a, d * b⁆ = ⁅a, b⁆ := by
  have h1 : ⁅c * a, d * b⁆ = c * ⁅a, d * b⁆ * c⁻¹ * ⁅c, d * b⁆ := by
    simp only [commutatorElement_def]
    group
  have h2 : ⁅a, d * b⁆ = ⁅a, d⁆ * (d * ⁅a, b⁆ * d⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hcdb : Commute c (d * b) := hcd.mul_right hcb
  have hc1 : ⁅c, d * b⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr hcdb
  have had1 : ⁅a, d⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr hda.symm
  have hdab : Commute d ⁅a, b⁆ := by
    rw [commutatorElement_def]
    exact ((hda.mul_right hdb).mul_right hda.inv_right).mul_right hdb.inv_right
  have hcadb : Commute c ⁅a, d * b⁆ := by
    rw [commutatorElement_def]
    exact ((hca.mul_right hcdb).mul_right hca.inv_right).mul_right hcdb.inv_right
  rw [h1, hc1, mul_one, hcadb.eq, mul_inv_cancel_right, h2, had1, one_mul, hdab.eq,
    mul_inv_cancel_right]

omit [Finite X] in
theorem mem_centralizer_of_commutator_mem {J : Subgroup X} (hJ : ⁅J, J⁆ = J) {n : X}
    (hnN : n ∈ normalizer (J : Set X))
    (hc : ∀ j ∈ J, n * j * n⁻¹ * j⁻¹ ∈ centralizer (J : Set X)) :
    n ∈ centralizer (J : Set X) := by
  have key : J ≤ centralizer ({n} : Set X) := by
    rw [← hJ, commutator_le]
    intro j₁ hj₁ j₂ hj₂
    rw [mem_centralizer_singleton_iff]
    have hnj : ∀ j ∈ J, n * j * n⁻¹ ∈ J := fun j hj => (mem_normalizer_iff.mp hnN j).mp hj
    have hc₁J : n * j₁ * n⁻¹ * j₁⁻¹ ∈ J := mul_mem (hnj j₁ hj₁) (inv_mem hj₁)
    have hc₂J : n * j₂ * n⁻¹ * j₂⁻¹ ∈ J := mul_mem (hnj j₂ hj₂) (inv_mem hj₂)
    have hcomm : ∀ c ∈ centralizer (J : Set X), ∀ j ∈ J, Commute c j := fun c hc' j hj =>
      (mem_centralizer_iff.mp hc' j hj).symm
    have h := commutatorElement_mul_mul_eq (a := j₁) (b := j₂) (c := n * j₁ * n⁻¹ * j₁⁻¹)
      (d := n * j₂ * n⁻¹ * j₂⁻¹) (hcomm _ (hc j₁ hj₁) _ hj₁) (hcomm _ (hc j₁ hj₁) _ hj₂)
      (hcomm _ (hc j₁ hj₁) _ hc₂J) (hcomm _ (hc j₂ hj₂) _ hj₁) (hcomm _ (hc j₂ hj₂) _ hj₂)
    have e : n * ⁅j₁, j₂⁆ * n⁻¹ = ⁅n * j₁ * n⁻¹ * j₁⁻¹ * j₁, n * j₂ * n⁻¹ * j₂⁻¹ * j₂⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h] at e
    calc ⁅j₁, j₂⁆ * n = n * ⁅j₁, j₂⁆ * n⁻¹ * n := by rw [e]
      _ = n * ⁅j₁, j₂⁆ := by group
  rw [mem_centralizer_iff]
  intro j hj
  exact mem_centralizer_singleton_iff.mp (key hj)

theorem exists_twoPart_map {H Q : Type*} [Group H] [Finite H] [Group Q] (φ : H →* Q) (x : H)
    {k : ℕ} (hk : φ x ^ 2 ^ k = 1) :
    ∃ y ∈ zpowers x, (∃ m : ℕ, y ^ 2 ^ m = 1) ∧ φ y = φ x := by
  set n := orderOf x with hn
  set a := n.factorization 2 with ha
  set o := n / 2 ^ a with ho
  have hn0 : n ≠ 0 := (orderOf_pos x).ne'
  have hno : 2 ^ a * o = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hc2o : Nat.Coprime 2 o := Nat.coprime_ordCompl Nat.prime_two hn0
  have h1 : (x ^ o) ^ 2 ^ a = 1 := by
    rw [← pow_mul, mul_comm, hno, hn, pow_orderOf_eq_one]
  have hcop : Nat.Coprime o (orderOf (φ x)) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    rw [hj]
    exact Nat.Coprime.pow_right j hc2o.symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨(x ^ o) ^ m, pow_mem (pow_mem (mem_zpowers x) _) _, ⟨a, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, h1, one_pow]
  · rw [map_pow, map_pow, hm]

theorem eq_one_of_mem_pPrimeCore_of_two_pow {K : Subgroup X} {x : ↥K}
    (hx : x ∈ pPrimeCore 2 ↥K) {n : ℕ} (hxn : x ^ 2 ^ n = 1) : x = 1 := by
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥K)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have h1 : orderOf (⟨x, hx⟩ : ↥(pPrimeCore 2 ↥K)) ∣ 2 ^ n :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hxn))
  have h2 : orderOf (⟨x, hx⟩ : ↥(pPrimeCore 2 ↥K)) ∣ Nat.card ↥(pPrimeCore 2 ↥K) :=
    orderOf_dvd_natCard _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases j with _ | j
  · rw [pow_zero, orderOf_eq_one_iff] at hj
    exact congrArg Subtype.val hj
  · exfalso
    rw [hj, pow_succ] at h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (dvd_trans (dvd_mul_left 2 _) h2))

theorem odd_orderOf_of_mem_pPrimeCore {K : Subgroup X} {x : ↥K} (hx : x ∈ pPrimeCore 2 ↥K) :
    Odd (orderOf x) := by
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥K)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  exact hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)

@[expose] def fourSubgroup (a v : X) : Subgroup X := Subgroup.closure {a, v}

omit [Finite X] in
theorem mem_fourSubgroup {a v : X} (ha2 : a * a = 1) (hv2 : v * v = 1) (hav : a * v = v * a)
    {x : X} : x ∈ fourSubgroup a v ↔ x = 1 ∨ x = a ∨ x = v ∨ x = a * v := by
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      have e4 : a * (a * v) = v := by rw [← mul_assoc, ha2, one_mul]
      have e5 : v * (a * v) = a := by rw [← mul_assoc, ← hav, mul_assoc, hv2, mul_one]
      have e6 : a * v * a = v := by rw [hav, mul_assoc, ha2, mul_one]
      have e7 : a * v * v = a := by rw [mul_assoc, hv2, mul_one]
      have e8 : a * v * (a * v) = 1 := by
        rw [show a * v * (a * v) = a * (v * a) * v by group, ← hav,
          show a * (a * v) * v = (a * a) * (v * v) by group, ha2, hv2, one_mul]
      have e9 : v * a = a * v := hav.symm
      rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
        simp [ha2, hv2, e4, e5, e6, e7, e8, e9]
    | inv x _ hx =>
      rcases hx with hx | hx | hx | hx <;> rw [hx]
      · simp
      · simp [ha]
      · simp [hv]
      · have : (a * v)⁻¹ = a * v := by rw [mul_inv_rev, ha, hv, hav]
        simp [this]
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

omit [Finite X] in
theorem isKleinFour_fourSubgroup {a v : X} (ha2 : a * a = 1) (hv2 : v * v = 1)
    (hav : a * v = v * a) (ha1 : a ≠ 1) (hv1 : v ≠ 1) (hne : a ≠ v) :
    IsKleinFour ↥(fourSubgroup a v) := by
  have hmem := fun x : X => mem_fourSubgroup ha2 hv2 hav (x := x)
  have hav1 : a * v ≠ 1 := fun h =>
    hne (mul_eq_one_iff_eq_inv.1 h |>.trans (inv_eq_of_mul_eq_one_right hv2))
  have hava : a * v ≠ a := fun h => hv1 (by simpa using h)
  have havv : a * v ≠ v := fun h => ha1 (by simpa using h)
  have hset : (fourSubgroup a v : Set X) = {1, a, v, a * v} := by
    ext x
    simp only [SetLike.mem_coe, hmem, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hcard : Nat.card ↥(fourSubgroup a v) = 4 := by
    have h1 : Nat.card ↥(fourSubgroup a v) = (fourSubgroup a v : Set X).ncard :=
      Nat.card_coe_set_eq (fourSubgroup a v : Set X)
    rw [h1, hset]
    have n1 : (1 : X) ∉ ({a, v, a * v} : Set X) := by simp [ha1.symm, hv1.symm, hav1.symm]
    have n2 : a ∉ ({v, a * v} : Set X) := by simp [hne, hava.symm]
    have n3 : v ∉ ({a * v} : Set X) := by simp [havv.symm]
    rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2,
      Set.ncard_insert_of_notMem n3, Set.ncard_singleton]
  refine ⟨hcard, ?_⟩
  have hsq : ∀ x : ↥(fourSubgroup a v), x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    have hx := (hmem x).1 x.2
    show (x : X) ^ 2 = 1
    rcases hx with h | h | h | h <;> rw [h]
    · simp
    · rw [pow_two]; exact ha2
    · rw [pow_two]; exact hv2
    · rw [pow_two, show a * v * (a * v) = a * (v * a) * v by group, ← hav,
        show a * (a * v) * v = (a * a) * (v * v) by group, ha2, hv2, one_mul]
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
    h | h
  · have : Subsingleton ↥(fourSubgroup a v) := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : ↥(fourSubgroup a v))
    omega
  · exact h

omit [Finite X] in
theorem mem_normalizer_sup {A B : Subgroup X} {g : X} (hA : g ∈ normalizer (A : Set X))
    (hB : g ∈ normalizer (B : Set X)) : g ∈ normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

omit [Finite X] in
theorem mem_normalizer_inf' {A B : Subgroup X} {g : X} (hA : g ∈ normalizer (A : Set X))
    (hB : g ∈ normalizer (B : Set X)) : g ∈ normalizer ((A ⊓ B : Subgroup X) : Set X) :=
  Subgroup.inf_normalizer_le_normalizer_inf ⟨hA, hB⟩

theorem le_sup_inf_centralizer_of_four {O : Subgroup X} (hO : Odd (Nat.card O)) {a v : X}
    (ha2 : a * a = 1) (hv2 : v * v = 1) (hav : a * v = v * a) (ha1 : a ≠ 1) (hv1 : v ≠ 1)
    (hne : a ≠ v) (haO : a ∈ normalizer (O : Set X)) (hvO : v ∈ normalizer (O : Set X)) :
    O ≤ (O ⊓ centralizer {a}) ⊔ (O ⊓ centralizer {v}) ⊔ (O ⊓ centralizer {a * v}) := by
  have : IsKleinFour ↥(fourSubgroup a v) := isKleinFour_fourSubgroup ha2 hv2 hav ha1 hv1 hne
  have haT : a ∈ fourSubgroup a v := Subgroup.subset_closure (by simp)
  have hvT : v ∈ fourSubgroup a v := Subgroup.subset_closure (by simp)
  set Y : Subgroup X := (O ⊓ centralizer {a}) ⊔ (O ⊓ centralizer {v}) ⊔
    (O ⊓ centralizer {a * v}) with hY
  have hYO : Y ≤ O := sup_le (sup_le inf_le_left inf_le_left) inf_le_left
  have hYodd : Odd (Nat.card Y) := Odd.of_dvd_nat hO (Subgroup.card_dvd_of_le hYO)
  have hTO : fourSubgroup a v ≤ normalizer (O : Set X) := by
    rw [fourSubgroup, Subgroup.closure_le]
    rintro x (hx | hx)
    · rw [hx]
      exact haO
    · rw [Set.mem_singleton_iff.mp hx]
      exact hvO
  have hgen : ∀ g ∈ ({a, v} : Set X), g ∈ normalizer (O : Set X) →
      (∀ f ∈ ({a, v, a * v} : Set X), g * f = f * g) → g ∈ normalizer (Y : Set X) := by
    intro g _ hgO hgf
    have hpiece : ∀ f ∈ ({a, v, a * v} : Set X),
        g ∈ normalizer ((O ⊓ centralizer {f} : Subgroup X) : Set X) := fun f hf =>
      mem_normalizer_inf' hgO (le_normalizer (mem_centralizer_singleton_iff.mpr (hgf f hf)))
    exact mem_normalizer_sup (mem_normalizer_sup (hpiece a (by simp)) (hpiece v (by simp)))
      (hpiece (a * v) (by simp))
  have hTY : fourSubgroup a v ≤ normalizer (Y : Set X) := by
    rw [fourSubgroup, Subgroup.closure_le]
    rintro x (hx | hx)
    · rw [hx]
      refine hgen _ (by simp) haO fun f hf => ?_
      rcases hf with hf | hf | hf
      · rw [hf]
      · rw [hf]
        exact hav
      · rw [Set.mem_singleton_iff.mp hf, mul_assoc a v a, ← hav]
    · rw [Set.mem_singleton_iff.mp hx]
      refine hgen _ (by simp) hvO fun f hf => ?_
      rcases hf with hf | hf | hf
      · rw [hf]
        exact hav.symm
      · rw [hf]
      · rw [Set.mem_singleton_iff.mp hf, ← mul_assoc, ← hav]
  have hne' : a ≠ v := hne
  have h1 := ABGLocalTools.card_mul_card_centralizer_four_sq hO hTO haT hvT ha1 hv1 hne'
  have h2 := ABGLocalTools.card_mul_card_centralizer_four_sq hYodd hTY haT hvT ha1 hv1 hne'
  have hpiece : ∀ f : X, O ⊓ centralizer {f} ≤ Y → Y ⊓ centralizer {f} = O ⊓ centralizer {f} :=
    fun f hf => le_antisymm (inf_le_inf_right _ hYO) (le_inf hf inf_le_right)
  have hYa : O ⊓ centralizer {a} ≤ Y := le_sup_left.trans le_sup_left
  have hYv : O ⊓ centralizer {v} ≤ Y := le_sup_right.trans le_sup_left
  have hYav : O ⊓ centralizer {a * v} ≤ Y := le_sup_right
  have hTa : O ⊓ centralizer ((fourSubgroup a v : Subgroup X) : Set X) ≤ Y := by
    refine le_trans (inf_le_inf_left _ (Subgroup.centralizer_le ?_)) hYa
    simpa using haT
  have hpieceT : Y ⊓ centralizer ((fourSubgroup a v : Subgroup X) : Set X) =
      O ⊓ centralizer ((fourSubgroup a v : Subgroup X) : Set X) :=
    le_antisymm (inf_le_inf_right _ hYO) (le_inf hTa inf_le_right)
  rw [hpiece a hYa, hpiece v hYv, hpiece (a * v) hYav, hpieceT] at h2
  have hc : 0 < Nat.card ↥(O ⊓ centralizer ((fourSubgroup a v : Subgroup X) : Set X)) :=
    Nat.card_pos
  have hcard : Nat.card O = Nat.card Y := by
    have h3 := h1.trans h2.symm
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hc 2) h3
  exact (Subgroup.eq_of_le_of_card_ge hYO hcard.le).symm.le

theorem exists_hom_model_self {a : X} {J W K : Subgroup X}
    (hs : SingleComponentSetting X a J W K) (hL34 : IsL34Type (J ⧸ Open.fusionZStar J))
    (hZ : zStarIn J = oddIn J) :
    ∃ ψ : ↥K →* Equiv.Perm (Fin 42), (∀ y, ψ y ∈ PSL3Four.S) ∧
      (∀ s ∈ PSL3Four.S, ∃ y, ψ y = s) ∧ ∀ y, ψ y = 1 ↔ y ∈ pPrimeCore 2 ↥K := by
  obtain ⟨q, hqS, hqsurj, hqker, -⟩ := L34Facts.exists_jq hL34
  have hqinj : ∀ e, q e = 1 → e = 1 := by
    intro e he
    have hc : e ∈ center (L34Facts.Jhat J) := by
      rw [← hqker]
      exact he
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥J) e
    have h1 : (j : X) ∈ zStarIn J := (L34Facts.mem_zStarIn_iff j.2).mpr hc
    rw [hZ] at h1
    obtain ⟨o, ho, hoj⟩ := h1
    have hoj' : o = j := Subtype.ext hoj
    rw [← hoj']
    exact (QuotientGroup.eq_one_iff o).mpr ho
  have hJK := le_of_singleComponentSetting hs
  have hsupK : J ⊔ (pPrimeCore 2 ↥K).map K.subtype = K :=
    (eq_sup_oddIn_of_singleComponentSetting hs).symm
  have hcore : (pPrimeCore 2 ↥J).map J.subtype = J ⊓ (pPrimeCore 2 ↥K).map K.subtype := by
    have h := oddIn_eq_inf_of_singleComponentSetting hs
    have hOKM : oddIn K ≤ oddIn (normalizer (W : Set X)) :=
      GSLit.map_pPrimeCore_le_of_isPComponent hs.le_normalizer hs.isPComponent_K
    refine h.trans (le_antisymm (fun x hx => ?_) (inf_le_inf_left _ hOKM))
    obtain ⟨hxJ, hxM⟩ := mem_inf.mp hx
    exact mem_inf.mpr ⟨hxJ, GrS5.inf_oddIn_le_oddIn hs.le_normalizer
      (mem_inf.mpr ⟨hxM, hJK hxJ⟩)⟩
  obtain ⟨e₁, -⟩ := UnbalancedCorr.exists_quotient_equiv_of_sup hJK hsupK hcore
  refine ⟨q.comp (e₁.symm.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥K))),
    fun y => hqS _, fun s hs' => ?_, fun y => ?_⟩
  · obtain ⟨e, he⟩ := hqsurj s hs'
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) (e₁ e)
    refine ⟨k, ?_⟩
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, hk,
      MulEquiv.symm_apply_apply, he]
  · constructor
    · intro h
      have h1 : e₁.symm (QuotientGroup.mk' (pPrimeCore 2 ↥K) y) = 1 := hqinj _ h
      have h2 : QuotientGroup.mk' (pPrimeCore 2 ↥K) y = 1 := by
        have := congrArg e₁ h1
        rwa [MulEquiv.apply_symm_apply, map_one] at this
      exact (QuotientGroup.eq_one_iff _).mp h2
    · intro h
      have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥K) y = 1 := (QuotientGroup.eq_one_iff y).mpr h
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, h1, map_one]

theorem exists_hom_model {a : X} {J W K : Subgroup X}
    (hs : SingleComponentSetting X a J W K) (hL34 : IsL34Type (J ⧸ Open.fusionZStar J))
    (hZ : zStarIn J = oddIn J) (u : X) :
    ∃ ψ : ↥(conjugate K u) →* Equiv.Perm (Fin 42), (∀ y, ψ y ∈ PSL3Four.S) ∧
      (∀ s ∈ PSL3Four.S, ∃ y, ψ y = s) ∧
      ∀ y, ψ y = 1 ↔ y ∈ pPrimeCore 2 ↥(conjugate K u) := by
  obtain ⟨ψK, hψS, hψsurj, hψker⟩ := exists_hom_model_self hs hL34 hZ
  let c : ↥K ≃* ↥(conjugate K u) :=
    K.equivMapOfInjective (MulAut.conj u⁻¹).toMonoidHom (MulAut.conj u⁻¹).injective
  refine ⟨ψK.comp c.symm.toMonoidHom, fun y => hψS _, fun s hs' => ?_, fun y => ?_⟩
  · obtain ⟨k, hk⟩ := hψsurj s hs'
    refine ⟨c k, ?_⟩
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.symm_apply_apply, hk]
  · constructor
    · intro h
      have h3 : c.symm y ∈ pPrimeCore 2 ↥K := (hψker _).mp h
      rw [← pPrimeCore_map_iso 2 c]
      exact ⟨c.symm y, h3, by simp⟩
    · intro h
      rw [← pPrimeCore_map_iso 2 c] at h
      obtain ⟨k, hk, rfl⟩ := h
      show ψK (c.symm (c k)) = 1
      rw [MulEquiv.symm_apply_apply]
      exact (hψker k).mpr hk

theorem exists_conj_of_psi_eq {L : Subgroup X} {Q : Type*} [Group Q] {ψ : ↥L →* Q}
    (hker : ∀ y, ψ y = 1 ↔ y ∈ pPrimeCore 2 ↥L) {x y : ↥L} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : ψ x = ψ y) : ∃ o : ↥L, ψ o = 1 ∧ o⁻¹ * x * o = y := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hk : x * y ∈ pPrimeCore 2 ↥L := by
    rw [← hker, map_mul, ← hxy, ← map_mul, hx, map_one]
  obtain ⟨n, hn⟩ := LocalAnalysis.ComponentInitial.exists_conj_eq_of_odd hx hy
    (odd_orderOf_of_mem_pPrimeCore hk)
  refine ⟨(x * y) ^ n, ?_, hn⟩
  rw [map_pow, (hker _).mpr hk, one_pow]

theorem exists_lift_commute {L : Subgroup X} {Q : Type*} [Group Q] {ψ : ↥L →* Q}
    (hker : ∀ y, ψ y = 1 ↔ y ∈ pPrimeCore 2 ↥L) {b : ↥L} (hb : b * b = 1) {t : Q} (ht : t * t = 1)
    (htb : t * ψ b = ψ b * t) (y₀ : ↥L) (hy₀ : ψ y₀ = t) :
    ∃ v : ↥L, v * v = 1 ∧ ψ v = t ∧ v * b = b * v := by
  have hxb : (y₀ * b * y₀⁻¹) * (y₀ * b * y₀⁻¹) = 1 := by
    rw [show y₀ * b * y₀⁻¹ * (y₀ * b * y₀⁻¹) = y₀ * (b * b) * y₀⁻¹ by group, hb]
    group
  have hψ : ψ (y₀ * b * y₀⁻¹) = ψ b := by
    rw [map_mul, map_mul, map_inv, hy₀, htb]
    group
  obtain ⟨o, ho, hob⟩ := exists_conj_of_psi_eq hker hxb hb hψ
  set z : ↥L := y₀⁻¹ * o with hz
  have hzb : z⁻¹ * b * z = b := by
    rw [hz, show (y₀⁻¹ * o)⁻¹ * b * (y₀⁻¹ * o) = o⁻¹ * (y₀ * b * y₀⁻¹) * o by group, hob]
  have hψz : ψ z⁻¹ = t := by
    rw [hz, map_inv, map_mul, map_inv, ho, mul_one, inv_inv, hy₀]
  have ht2 : ψ z⁻¹ ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two, hψz, ht]
  obtain ⟨v, hvz, ⟨m, hm⟩, hv⟩ := exists_twoPart_map ψ z⁻¹ ht2
  have hvb : v * b = b * v := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hvz
    have h1 : Commute z⁻¹ b := by
      show z⁻¹ * b = b * z⁻¹
      calc z⁻¹ * b = (z⁻¹ * b * z) * z⁻¹ := by group
        _ = b * z⁻¹ := by rw [hzb]
    exact (h1.zpow_left k).eq
  refine ⟨v, ?_, by rw [hv, hψz], hvb⟩
  have hv2 : v * v ∈ pPrimeCore 2 ↥L := by
    rw [← hker, map_mul, hv, hψz, ht]
  have hvv : (v * v) ^ 2 ^ m = 1 := by
    rw [← pow_two, ← pow_mul, show 2 * 2 ^ m = 2 ^ m * 2 by ring, pow_mul, hm, one_pow]
  exact eq_one_of_mem_pPrimeCore_of_two_pow hv2 hvv

theorem not_oddIn_le_centralizer
    (hMax : MaximalTwoComponentInput) {a : X} {J W K : Subgroup X}
    (hs : SingleComponentSetting X a J W K) (hL34 : IsL34Type (J ⧸ Open.fusionZStar J))
    (hZ : zStarIn J = oddIn J) {u : X} (hu : u ∈ normalizer (W : Set X))
    (hKu : conjugate K u ≠ K) (haKu : a ∈ conjugate K u) :
    ¬ oddIn J ≤ centralizer (J : Set X) := by
  intro hcen
  set M : Subgroup X := normalizer (W : Set X) with hM
  set L : Subgroup X := conjugate K u with hL
  have hgs := hs.toGSMaximalSetting
  have hJK : J ≤ K := le_of_singleComponentSetting hs
  have hKM : K ≤ M := hs.le_normalizer
  have hKc := hs.isPComponent_K
  have hLM : L ≤ M := conjugate_le_of_mem hKM hu
  have hLc : IsPComponent 2 (L.subgroupOf M) := isPComponent_conjugate_subgroupOf hu hKc
  have hcomm : ⁅K, L⁆ ≤ oddIn K ⊓ oddIn L :=
    GrS5.commutator_le_inf_oddIn hKM hLM hKc hLc (Ne.symm hKu)
  have hOJ := oddIn_eq_inf_of_singleComponentSetting hs
  have hOKM : oddIn K ≤ oddIn M := GSLit.map_pPrimeCore_le_of_isPComponent hKM hKc
  have hJperf : ⁅J, J⁆ = J := commutator_eq_self_of_gsMaximalSetting hgs
  have hCaJ := centralizer_le_normalizer_of_gsMaximalSetting hMax hgs
  have haa : a * a = 1 := by rw [← pow_two, ← hgs.orderOf_eq, pow_orderOf_eq_one]
  have haJ : a ∈ centralizer (J : Set X) := by
    rw [mem_centralizer_iff]
    intro j hj
    exact mem_centralizer_singleton_iff.mp (hgs.le_centralizer hj)
  have step1 : ∀ y ∈ L, y ∈ normalizer (J : Set X) → y ∈ centralizer (J : Set X) := by
    intro y hyL hyN
    refine mem_centralizer_of_commutator_mem hJperf hyN fun j hj => hcen ?_
    rw [hOJ]
    refine mem_inf.mpr ⟨mul_mem ((mem_normalizer_iff.mp hyN j).mp hj) (inv_mem hj), hOKM ?_⟩
    have h1 : ⁅y, j⁆ ∈ ⁅L, K⁆ := commutator_mem_commutator hyL (hJK hj)
    rw [commutator_comm] at h1
    exact (mem_inf.mp (hcomm h1)).1
  have step2 : ∀ g : X, J ≤ centralizer ({g⁻¹ * a * g} : Set X) →
      centralizer ({g⁻¹ * a * g} : Set X) ≤ normalizer (J : Set X) := by
    intro g hJb
    have hJg : conjugate J g⁻¹ = J := by
      refine conjugate_eq_of_le_centralizer hMax hgs fun x hx => ?_
      rw [UnbalancedLayer.mem_conjugate_iff, inv_inv] at hx
      have h1 := mem_centralizer_singleton_iff.mp (hJb hx)
      rw [mem_centralizer_singleton_iff]
      calc x * a = g * (g⁻¹ * x * g * (g⁻¹ * a * g)) * g⁻¹ := by group
        _ = g * (g⁻¹ * a * g * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
        _ = a * x := by group
    have hmemJ : ∀ y, y ∈ J ↔ g * y * g⁻¹ ∈ J := by
      intro y
      constructor
      · intro hy
        rw [← hJg, UnbalancedLayer.mem_conjugate_iff, inv_inv]
        rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group]
      · intro hy
        rw [← hJg, UnbalancedLayer.mem_conjugate_iff, inv_inv] at hy
        rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at hy
    intro c hc
    have hca : g * c * g⁻¹ ∈ centralizer ({a} : Set X) := by
      rw [mem_centralizer_singleton_iff] at hc ⊢
      calc g * c * g⁻¹ * a = g * (c * (g⁻¹ * a * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * a * g) * c) * g⁻¹ := by rw [hc]
        _ = a * (g * c * g⁻¹) := by group
    have hd := hCaJ hca
    rw [mem_normalizer_iff] at hd ⊢
    have he : ∀ y, g * c * g⁻¹ * (g * y * g⁻¹) * (g * c * g⁻¹)⁻¹ = g * (c * y * c⁻¹) * g⁻¹ :=
      fun y => by group
    intro y
    constructor
    · intro hy
      have h1 := (hd (g * y * g⁻¹)).mp ((hmemJ y).mp hy)
      rw [he] at h1
      exact (hmemJ _).mpr h1
    · intro hy
      have h1 := (hd (g * y * g⁻¹)).mpr (by rw [he]; exact (hmemJ _).mp hy)
      exact (hmemJ y).mpr h1
  obtain ⟨ψ, hψS, hψsurj, hψker⟩ := exists_hom_model hs hL34 hZ u
  set a' : ↥L := ⟨a, haKu⟩ with ha'
  have ha'2 : a' * a' = 1 := Subtype.ext haa
  have hψne : ∀ b : ↥L, b * b = 1 → b ≠ 1 → ψ b ≠ 1 := by
    intro b hb hb1 h
    apply hb1
    exact eq_one_of_mem_pPrimeCore_of_two_pow ((hψker b).mp h) (n := 1)
      (by rw [pow_one, pow_two]; exact hb)
  have ha'1 : a' ≠ 1 := fun h => by
    have h1 : a = 1 := congrArg Subtype.val h
    have h2 := hgs.orderOf_eq
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have step2' : ∀ b : ↥L, b * b = 1 → b ≠ 1 → (b : X) ∈ centralizer (J : Set X) →
      ∀ y : ↥L, y * b = b * y → (y : X) ∈ centralizer (J : Set X) := by
    intro b hb hb1 hbJ y hyb
    obtain ⟨σ, hσ⟩ := exists_conj_of_involution_S ⟨ψ a', hψS a'⟩ ⟨ψ b, hψS b⟩
      (Subtype.ext (show ψ a' * ψ a' = 1 by rw [← map_mul, ha'2, map_one]))
      (Subtype.ext (show ψ b * ψ b = 1 by rw [← map_mul, hb, map_one]))
      (fun h => hψne a' ha'2 ha'1 (congrArg Subtype.val h))
      (fun h => hψne b hb hb1 (congrArg Subtype.val h))
    obtain ⟨h, hh⟩ := hψsurj σ σ.2
    have hσ' : ψ (h⁻¹ * a' * h) = ψ b := by
      have := congrArg Subtype.val hσ
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      rw [map_mul, map_mul, map_inv, hh]
      exact this
    have hx2 : (h⁻¹ * a' * h) * (h⁻¹ * a' * h) = 1 := by
      rw [show h⁻¹ * a' * h * (h⁻¹ * a' * h) = h⁻¹ * (a' * a') * h by group, ha'2]
      group
    obtain ⟨o, -, ho⟩ := exists_conj_of_psi_eq hψker hx2 hb hσ'
    set g : X := ((h * o : ↥L) : X) with hg
    have hbg : (b : X) = g⁻¹ * a * g := by
      rw [← ho, hg]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ha']
      group
    have hJb : J ≤ centralizer ({g⁻¹ * a * g} : Set X) := by
      intro j hj
      rw [mem_centralizer_singleton_iff, ← hbg]
      exact mem_centralizer_iff.mp hbJ j hj
    have hyC : (y : X) ∈ centralizer ({g⁻¹ * a * g} : Set X) := by
      rw [mem_centralizer_singleton_iff, ← hbg]
      exact congrArg Subtype.val hyb
    exact step1 _ y.2 (step2 g hJb hyC)
  have step3 : ∀ s ∈ PSL3Four.S, s * s = 1 → s ≠ 1 →
      ∃ b : ↥L, b * b = 1 ∧ ψ b = s ∧ (b : X) ∈ centralizer (J : Set X) := by
    refine involution_closure_S
      (fun s => ∃ b : ↥L, b * b = 1 ∧ ψ b = s ∧ (b : X) ∈ centralizer (J : Set X)) ?_
      (hψS a') (by rw [← map_mul, ha'2, map_one]) (hψne a' ha'2 ha'1) ⟨a', ha'2, rfl, haJ⟩
    rintro s t - htS - ht2 hs1 ht1 hst ⟨b, hb, rfl, hbJ⟩
    have hb1 : b ≠ 1 := fun h => hs1 (by rw [h, map_one])
    obtain ⟨y₀, hy₀⟩ := hψsurj t htS
    obtain ⟨v, hv2, hvt, hvb⟩ := exists_lift_commute hψker hb ht2 hst.symm y₀ hy₀
    exact ⟨v, hv2, hvt, step2' b hb hb1 hbJ v hvb⟩
  obtain ⟨t, htS, ht2, ht1, hta, hat⟩ := exists_commute_involution_S (hψS a')
    (by rw [← map_mul, ha'2, map_one]) (hψne a' ha'2 ha'1)
  obtain ⟨y₀, hy₀⟩ := hψsurj t htS
  obtain ⟨v, hv2, hvt, hva⟩ := exists_lift_commute hψker ha'2 ht2 hat.symm y₀ hy₀
  have hv1 : v ≠ 1 := fun h => ht1 (by rw [← hvt, h, map_one])
  have hav : a' ≠ v := fun h => hta (by rw [← hvt, ← h])
  have hvJ : (v : X) ∈ centralizer (J : Set X) := step2' a' ha'2 ha'1 haJ v hva
  have hav2 : (a' * v) * (a' * v) = 1 := by
    rw [show a' * v * (a' * v) = a' * (v * a') * v by group, hva,
      show a' * (a' * v) * v = (a' * a') * (v * v) by group, ha'2, hv2, one_mul]
  have hav1 : a' * v ≠ 1 := fun h => hav (by
    rw [mul_eq_one_iff_eq_inv] at h
    rw [h, inv_eq_of_mul_eq_one_right hv2])
  have havJ : ((a' * v : ↥L) : X) ∈ centralizer (J : Set X) := by
    simp only [Subgroup.coe_mul]
    exact mul_mem haJ hvJ
  have hO : pPrimeCore 2 ↥L ≤ (centralizer (J : Set X)).subgroupOf L := by
    have hle := le_sup_inf_centralizer_of_four (O := pPrimeCore 2 ↥L)
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card) ha'2 hv2 hva.symm ha'1 hv1 hav
      (by rw [normalizer_eq_top]; exact mem_top a') (by rw [normalizer_eq_top]; exact mem_top v)
    refine hle.trans (sup_le (sup_le ?_ ?_) ?_)
    · intro y hy
      exact step2' a' ha'2 ha'1 haJ y (mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2)
    · intro y hy
      exact step2' v hv2 hv1 hvJ y (mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2)
    · intro y hy
      exact step2' (a' * v) hav2 hav1 havJ y (mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2)
  have hLJ : L ≤ centralizer (J : Set X) := by
    intro y hy
    obtain ⟨b₀, hb₀⟩ : ∃ b₀ : ↥L, b₀ ∈ (centralizer (J : Set X)).subgroupOf L ∧
        ψ b₀ = ψ ⟨y, hy⟩ := by
      have hgen : PSL3Four.S ≤ ((centralizer (J : Set X)).subgroupOf L).map ψ := by
        refine le_of_involutions_S fun s hsS hs2 hs1 => ?_
        obtain ⟨b, -, hbs, hbJ⟩ := step3 s hsS hs2 hs1
        exact ⟨b, hbJ, hbs⟩
      obtain ⟨b₀, hb₀, he⟩ := hgen (hψS ⟨y, hy⟩)
      exact ⟨b₀, hb₀, he⟩
    have hk : b₀⁻¹ * ⟨y, hy⟩ ∈ pPrimeCore 2 ↥L := by
      rw [← hψker, map_mul, map_inv, hb₀.2, inv_mul_cancel]
    have hyeq : y = (b₀ : X) * ((b₀⁻¹ * ⟨y, hy⟩ : ↥L) : X) := by simp
    rw [hyeq]
    exact mul_mem hb₀.1 (hO hk)
  apply not_commutator_le_of_gsMaximalSetting hMax hgs u
  have hJu : conjugate J u ≤ L := map_mono hJK
  have h1 : ⁅J, conjugate J u⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer, le_centralizer_iff]
    exact hJu.trans hLJ
  rw [h1]
  exact bot_le

end CFSG.ComponentClassification.GrSLit.FW

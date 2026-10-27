module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Lift
public import CFSG.HardMathSupport.Solomon.Proving.LiftTwoLocalNormalizer
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Norm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA.H1420
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem twoLocal_of_witness_gen {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K A : Subgroup G}
    (hA : IsElemAbelian p A) (hAN : A ≤ Subgroup.normalizer (K : Set G))
    (hAc : ∀ a ∈ A, ∀ k ∈ K, ⁅k, a⁆ ∈ GLAPPrimeCoreOf p K)
    (V E : Subgroup (PQuot p K)) (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (hE : IsElemAbelian p E) (hEV : E ≤ Subgroup.normalizer (V : Set (PQuot p K))) :
    ∃ P W : Subgroup G, P ≠ ⊥ ∧ IsPGroup 2 P ∧ W ≤ Subgroup.normalizer (P : Set G) ∧
      IsElemAbelian p W ∧
        Nat.card E * Nat.card A ≤ Nat.card W * Nat.card (Subgroup.center (PQuot p K)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hOK : GLAPPrimeCoreOf p K ≤ K := by
    unfold GLAPPrimeCoreOf
    exact Subgroup.map_subtype_le _
  have hKJ : K ≤ K ⊔ A := le_sup_left
  have hAJ : A ≤ K ⊔ A := le_sup_right
  have hOJ : GLAPPrimeCoreOf p K ≤ K ⊔ A := hOK.trans hKJ
  have hJN : K ⊔ A ≤ Subgroup.normalizer ((GLAPPrimeCoreOf p K : Subgroup G) : Set G) :=
    sup_le (le_normalizer_glaPPrimeCoreOf p K)
      (hAN.trans (normalizer_le_normalizer_glaPPrimeCoreOf p K))
  set O : Subgroup ↥(K ⊔ A) := (GLAPPrimeCoreOf p K).subgroupOf (K ⊔ A) with hOdef
  haveI hOn : O.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOJ).2 hJN
  let π : ↥(K ⊔ A) →* ↥(K ⊔ A) ⧸ O := QuotientGroup.mk' O
  have hπker : π.ker = O := QuotientGroup.ker_mk' _
  have hOcard : ¬ p ∣ Nat.card (GLAPPrimeCoreOf p K : Subgroup G) :=
    not_dvd_card_glaPPrimeCoreOf hp K
  have hOc : Nat.Coprime p (Nat.card O) := by
    rw [hOdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hOcard
  have hAO : A ⊓ GLAPPrimeCoreOf p K = ⊥ := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (isPGroup_of_isElemAbelian hA)
    have hdvd : Nat.card (A ⊓ GLAPPrimeCoreOf p K : Subgroup G) ∣ p ^ k := by
      rw [← hk]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hj0 : j = 0 := by
      by_contra hne
      apply hOcard
      have h3 : p ∣ Nat.card (A ⊓ GLAPPrimeCoreOf p K : Subgroup G) := by
        rw [hj]
        exact dvd_pow_self p hne
      exact h3.trans (Subgroup.card_dvd_of_le inf_le_right)
    rw [hj0, pow_zero] at hj
    exact Subgroup.eq_bot_of_card_eq _ hj
  have hAel : IsElemAbelian p (A.subgroupOf (K ⊔ A)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · exact Subtype.ext (Subtype.ext (isElemAbelian_commute hA (Subgroup.mem_subgroupOf.1 a.2)
        (Subgroup.mem_subgroupOf.1 b.2)))
    · apply Subtype.ext
      simpa using hA.2 ((x : ↥(K ⊔ A)) : G) (Subgroup.mem_subgroupOf.1 hx)
  have hπA : Function.Injective (π.comp (A.subgroupOf (K ⊔ A)).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxO : ((x : ↥(K ⊔ A)) : G) ∈ GLAPPrimeCoreOf p K := by
      have hxker : ((x : ↥(K ⊔ A))) ∈ π.ker := hx
      rw [hπker] at hxker
      exact Subgroup.mem_subgroupOf.1 hxker
    have hx1 : ((x : ↥(K ⊔ A)) : G) = 1 := by
      have : ((x : ↥(K ⊔ A)) : G) ∈ A ⊓ GLAPPrimeCoreOf p K := ⟨Subgroup.mem_subgroupOf.1 x.2, hxO⟩
      rw [hAO] at this
      exact Subgroup.mem_bot.1 this
    exact Subtype.ext (Subtype.ext hx1)
  have hcore : GLAPPrimeCoreOf p (K.subgroupOf (K ⊔ A)) = π.ker ⊓ K.subgroupOf (K ⊔ A) := by
    apply Subgroup.map_injective (f := (K ⊔ A).subtype) (K ⊔ A).subtype_injective
    rw [map_subtype_glaPPrimeCoreOf_subgroupOf p hKJ, hπker,
      Subgroup.map_inf _ _ _ (K ⊔ A).subtype_injective, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hOJ, inf_eq_left.2 hKJ, inf_eq_left.2 hOK]
  obtain ⟨e₁⟩ := nonempty_pQuot_equiv_map_self (p := p) (ψ := π) (K := K.subgroupOf (K ⊔ A)) hcore
  obtain ⟨e₂⟩ := nonempty_pQuot_equiv_subgroupOf p hKJ
  let ψ : PQuot p K ≃* ↥((K.subgroupOf (K ⊔ A)).map π) := e₂.symm.trans e₁
  set Kp : Subgroup (↥(K ⊔ A) ⧸ O) := (K.subgroupOf (K ⊔ A)).map π with hKp
  let ι : PQuot p K →* (↥(K ⊔ A) ⧸ O) := Kp.subtype.comp ψ.toMonoidHom
  have hι : Function.Injective ι := fun x y hxy => ψ.injective (Subtype.ext hxy)
  have hιK : ∀ x, ι x ∈ Kp := fun x => (ψ x).2
  set Em : Subgroup (↥(K ⊔ A) ⧸ O) := E.map ι with hEm
  set Vm : Subgroup (↥(K ⊔ A) ⧸ O) := V.map ι with hVm
  set Ap : Subgroup (↥(K ⊔ A) ⧸ O) := (A.subgroupOf (K ⊔ A)).map π with hAp
  have hEmKp : Em ≤ Kp := by
    rintro _ ⟨x, -, rfl⟩
    exact hιK x
  have hVmKp : Vm ≤ Kp := by
    rintro _ ⟨x, -, rfl⟩
    exact hιK x
  have hcomm : ∀ x ∈ Kp, ∀ y ∈ Ap, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    have hc : ⁅k, a⁆ ∈ O := by
      rw [hOdef, Subgroup.mem_subgroupOf]
      exact hAc _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hk)
    have h1 : π ⁅k, a⁆ = 1 := (QuotientGroup.eq_one_iff _).2 hc
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hEmel : IsElemAbelian p Em := isElemAbelian_map_of_injOn ι E hE
  have hApel : IsElemAbelian p Ap := isElemAbelian_map_of_injOn π _ hAel
  have hEmAp : Em ⊓ Ap ≤ (Subgroup.center (PQuot p K)).map ι := by
    rintro x ⟨hxE, hxA⟩
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.1 hxE
    refine Subgroup.mem_map.2 ⟨e, Subgroup.mem_center_iff.2 fun z => hι ?_, rfl⟩
    rw [map_mul, map_mul]
    exact hcomm (ι z) (hιK z) (ι e) hxA
  have hE0el : IsElemAbelian p (Em ⊔ Ap) :=
    S8.L84.isElemAbelian_sup_of_commute hEmel hApel (fun w hw d hd => hcomm w (hEmKp hw) d hd)
  have hApN : Ap ≤ Subgroup.normalizer (Em : Set _) := fun y hy =>
    S8.L84.mem_normalizer_of_commute (fun x hx => (hcomm x (hEmKp hx) y hy).symm)
  have hEmN : Em ≤ Subgroup.normalizer (Vm : Set _) := by
    rintro _ ⟨x, hx, rfl⟩
    exact map_mem_normalizer_of_mem ι (hEV hx)
  have hApNV : Ap ≤ Subgroup.normalizer (Vm : Set _) := fun y hy =>
    S8.L84.mem_normalizer_of_commute (fun x hx => (hcomm x (hVmKp hx) y hy).symm)
  have hVm_ne : Vm ≠ ⊥ := fun h =>
    hV (Subgroup.map_injective hι (h.trans (Subgroup.map_bot _).symm))
  have hVm2 : IsPGroup 2 Vm := isPGroup_map_of_isPGroup ι V hV2
  obtain ⟨W, P, hWc, hWp, hWcard, hP, hP2, hWP⟩ :=
    CFSG.HardMathSupport.Solomon.Proving.exists_lift_twoLocal_of_le_normalizer hp hp2 O hOc
      (Em ⊔ Ap) Vm hE0el ⟨hVm_ne, hVm2⟩ (sup_le hEmN hApNV)
  refine ⟨P.map (K ⊔ A).subtype, W.map (K ⊔ A).subtype, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hP (Subgroup.map_injective (K ⊔ A).subtype_injective (h.trans (Subgroup.map_bot _).symm))
  · exact isPGroup_map_of_isPGroup (K ⊔ A).subtype P hP2
  · rintro _ ⟨w, hw, rfl⟩
    exact map_mem_normalizer_of_mem (K ⊔ A).subtype (hWP hw)
  · exact isElemAbelian_map_of_injOn _ W ⟨hWc, hWp⟩
  · have hsum := card_sup_mul_card_inf_of_le_normalizer (A := Em) (B := Ap) hApN
    have hinf : Nat.card (Em ⊓ Ap : Subgroup _) ≤ Nat.card (Subgroup.center (PQuot p K)) := by
      have := Subgroup.card_le_of_le hEmAp
      rwa [Subgroup.card_map_of_injective hι] at this
    rw [Subgroup.card_map_of_injective (K ⊔ A).subtype_injective, hWcard]
    rw [Subgroup.card_map_of_injective hι, card_map_of_injective_comp π (A.subgroupOf (K ⊔ A)) hπA,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAJ).toEquiv] at hsum
    rw [← hsum]
    exact Nat.mul_le_mul_left _ hinf

end CFSG.LocalAnalysis.GLTheoremA.H301B

end

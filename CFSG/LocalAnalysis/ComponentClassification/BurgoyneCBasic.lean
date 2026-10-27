module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinJoins
public import CFSG.GroupTheory.ConjugatePairSubnormality

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open CFSG Subgroup CFSG.ComponentClassification.TBLit
open scoped commutatorElement MatrixGroups

theorem le_derivedSeries_of_commutator_eq {G : Type*} [Group G] {L : Subgroup G}
    (hL : ⁅L, L⁆ = L) (n : ℕ) : L ≤ derivedSeries G n := by
  induction n with
  | zero => exact le_top
  | succ n ih =>
    rw [derivedSeries_succ]
    calc L = ⁅L, L⁆ := hL.symm
      _ ≤ ⁅derivedSeries G n, derivedSeries G n⁆ := commutator_mono ih ih

theorem eq_bot_of_commutator_eq {G : Type*} [Group G] [hG : Group.IsSolvable G]
    {L : Subgroup G} (hL : ⁅L, L⁆ = L) : L = ⊥ := by
  obtain ⟨n, hn⟩ := hG.solvable
  exact eq_bot_iff.2 ((le_derivedSeries_of_commutator_eq hL n).trans hn.le)

section Socle

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem socleAction_refl (x : GeneralizedFitting.subgroup X) :
    socleAction (MulEquiv.refl _) (x : X) = MulAut.conj x :=
  socleAction_symm (MulEquiv.refl _) x

theorem le_socle_of_commutator_eq (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (hout : Group.IsSolvable (OuterAutomorphisms.Outer (GeneralizedFitting.subgroup X)))
    {L : Subgroup X} (hL : ⁅L, L⁆ = L) : L ≤ GeneralizedFitting.subgroup X := by
  have hψi : Function.Injective (socleAction (MulEquiv.refl (GeneralizedFitting.subgroup X))) :=
    socleAction_injective hsimple hnab (MulEquiv.refl _)
  obtain ⟨M, hMdef⟩ : ∃ M : Subgroup (OuterAutomorphisms.Outer (GeneralizedFitting.subgroup X)),
      M = (L.map (socleAction (MulEquiv.refl (GeneralizedFitting.subgroup X)))).map
        (QuotientGroup.mk' (OuterAutomorphisms.inner (GeneralizedFitting.subgroup X))) :=
    ⟨_, rfl⟩
  have hM : ⁅M, M⁆ = M := by
    rw [hMdef, ← map_commutator, ← map_commutator, hL]
  have hM' : M = ⊥ := @eq_bot_of_commutator_eq _ _ hout M hM
  intro l hl
  have hmem : socleAction (MulEquiv.refl (GeneralizedFitting.subgroup X)) l ∈
      OuterAutomorphisms.inner (GeneralizedFitting.subgroup X) := by
    have h1 : QuotientGroup.mk' (OuterAutomorphisms.inner (GeneralizedFitting.subgroup X))
        (socleAction (MulEquiv.refl (GeneralizedFitting.subgroup X)) l) ∈ M := by
      rw [hMdef]
      exact ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    rw [hM', mem_bot] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1
  obtain ⟨f, hf⟩ := hmem
  have hfl : socleAction (MulEquiv.refl (GeneralizedFitting.subgroup X)) (f : X) =
      socleAction (MulEquiv.refl (GeneralizedFitting.subgroup X)) l := by
    rw [socleAction_refl f]
    exact hf
  rw [← hψi hfl]
  exact f.2

end Socle

section Components

variable {G : Type*} [Group G]

theorem isPComponent_subgroupOf_of_le [Finite G] {L M H : Subgroup G} (hLM : L ≤ M)
    (hMH : M ≤ H) (hL : IsPComponent 2 (L.subgroupOf H)) : IsPComponent 2 (L.subgroupOf M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hs, hg, hq⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L H (hLM.trans hMH)).1 hL
  exact (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L M hLM).2
    ⟨GroupTheory.isSubnormal_subgroupOf_of_le hMH hs, hg, hq⟩

theorem commutator_eq_of_isPComponent {L H : Subgroup G} (hLH : L ≤ H)
    (hL : IsPComponent 2 (L.subgroupOf H)) : ⁅L, L⁆ = L := by
  have := CatalogueBAlternating.pComponent_perfect hL
  have : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLH).toMonoidHom) (subgroupOfEquivOfLe hLH).surjective
  exact Subgroup.isPerfect_iff.1 this

theorem ne_bot_of_isPComponent {L H : Subgroup G} (hLH : L ≤ H)
    (hL : IsPComponent 2 (L.subgroupOf H)) : L ≠ ⊥ := by
  have := CatalogueBAlternating.pComponent_nontrivial hL
  have : Nontrivial L := (subgroupOfEquivOfLe hLH).symm.surjective.nontrivial
  exact (nontrivial_iff_ne_bot L).1 this

theorem not_le_of_isSolvable {L H N : Subgroup G} (hLH : L ≤ H)
    (hL : IsPComponent 2 (L.subgroupOf H)) (hN : Group.IsSolvable N) (hLN : L ≤ N) : False := by
  have hsolv : Group.IsSolvable L :=
    @Group.isSolvable_of_isSolvable_injective _ _ _ _ (inclusion hLN) (inclusion_injective hLN) hN
  have hperf : Group.IsPerfect L :=
    Subgroup.isPerfect_iff.2 (commutator_eq_of_isPComponent hLH hL)
  have hnt : Nontrivial L := (nontrivial_iff_ne_bot L).2 (ne_bot_of_isPComponent hLH hL)
  exact @Group.IsPerfect.not_isSolvable L _ hnt hperf hsolv

theorem le_or_le_of_le_sup [Finite G] {H L N₁ N₂ : Subgroup G} (hLH : L ≤ H)
    (hL : IsPComponent 2 (L.subgroupOf H)) (hN₁ : N₁ ≤ H) (hN₂ : N₂ ≤ H)
    (hs₁ : (N₁.subgroupOf H).IsSubnormal) (hs₂ : (N₂.subgroupOf H).IsSubnormal)
    (hle : L ≤ N₁ ⊔ N₂) : L ≤ N₁ ∨ L ≤ N₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup : L.subgroupOf H ≤ sSup {N₁.subgroupOf H, N₂.subgroupOf H} := by
    rw [sSup_pair, ← subgroupOf_sup hN₁ hN₂]
    intro x hx
    exact hle hx
  obtain ⟨N, hN, hLN⟩ := CatalogueBPrimeJoin.exists_le_of_le_sSup 2 _ hL _ (by
    rintro N (rfl | rfl)
    · exact hs₁
    · exact hs₂) hsup
  have hback : ∀ {M : Subgroup G}, L.subgroupOf H ≤ M.subgroupOf H → L ≤ M := by
    intro M h x hx
    exact h (show (⟨x, hLH hx⟩ : H) ∈ L.subgroupOf H from hx)
  rcases hN with rfl | rfl
  · exact Or.inl (hback hLN)
  · exact Or.inr (hback hLN)

theorem eq_of_le_of_isQuasisimple [Finite G] {H L N : Subgroup G} (hLN : L ≤ N) (hNH : N ≤ H)
    (hL : IsPComponent 2 (L.subgroupOf H)) (hN : IsQuasisimple N) : L = N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLN' := isPComponent_subgroupOf_of_le hLN hNH hL
  have hsub := ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L N hLN).1 hLN').1
  rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hN hsub with h | h
  · refine le_antisymm hLN fun x hx => ?_
    have : (⟨x, hx⟩ : N) ∈ L.subgroupOf N := h ▸ mem_top _
    exact this
  · exfalso
    have hcomm : ⁅L, L⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [mem_centralizer_iff]
      intro b hb
      have h1 := mem_center_iff.1 (h (show (⟨a, hLN ha⟩ : N) ∈ L.subgroupOf N from ha))
        ⟨b, hLN hb⟩
      exact congrArg Subtype.val h1
    have hperf := commutator_eq_of_isPComponent (hLN.trans hNH) hL
    exact ne_bot_of_isPComponent (hLN.trans hNH) hL (hperf.symm.trans hcomm)

end Components

section SL2

variable {F : Type*} [Field F]

theorem eq_one_or_eq_neg_one (h2 : (2 : F) ≠ 0) (A : SL(2, F)) (hA : A * A = 1) :
    A = 1 ∨ A = -1 := by
  obtain ⟨M, hM⟩ := A
  have hsq : M * M = 1 := congrArg Subtype.val hA
  rw [Matrix.det_fin_two] at hM
  have e : ∀ i j, (M * M) i j = (1 : Matrix (Fin 2) (Fin 2) F) i j := fun i j => by rw [hsq]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10
  by_cases hs : M 0 0 + M 1 1 = 0
  · exfalso
    apply h2
    linear_combination -hM - e00 + M 0 0 * hs
  have hb : M 0 1 = 0 := by
    have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.1 this).resolve_right hs
  have hc : M 1 0 = 0 := by
    have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.1 this).resolve_right hs
  have ha2 : M 0 0 * M 0 0 = 1 := by linear_combination e00 - M 1 0 * hb
  have had : M 0 0 * M 1 1 = 1 := by linear_combination hM + M 1 0 * hb
  have hda : M 1 1 = M 0 0 := by
    have : M 0 0 * (M 1 1 - M 0 0) = 0 := by linear_combination had - ha2
    rcases mul_eq_zero.1 this with h | h
    · rw [h, zero_mul] at ha2
      exact absurd ha2 zero_ne_one
    · linear_combination h
  have hpm : M 0 0 = 1 ∨ M 0 0 = -1 := by
    have : (M 0 0 - 1) * (M 0 0 + 1) = 0 := by linear_combination ha2
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  rcases hpm with h | h
  · left
    apply Subtype.ext
    change M = (1 : Matrix (Fin 2) (Fin 2) F)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, hda, h]
  · right
    apply Subtype.ext
    change M = -(1 : Matrix (Fin 2) (Fin 2) F)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, hda, h]

end SL2

section OddCore

variable {R : Type*} [Group R] [Finite R]

theorem not_mem_pPrimeCore_of_orderOf {a : R} (ha : orderOf a = 2) : a ∉ pPrimeCore 2 R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hmem
  have hdvd : orderOf (⟨a, hmem⟩ : pPrimeCore 2 R) ∣ Nat.card (pPrimeCore 2 R) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, ha] at hdvd
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 pPrimeCore_coprime_card hdvd

theorem eq_of_involutions {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (e : R ⧸ pPrimeCore 2 R ≃* SL(2, F)) {a b : R} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a * b = b * a) : a = b := by
  have hneg : ∀ {z : R}, orderOf z = 2 → e (QuotientGroup.mk z) = -1 := by
    intro z hz
    have hz2 : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
    rcases eq_one_or_eq_neg_one h2 (e (QuotientGroup.mk z))
      (by rw [← map_mul, ← QuotientGroup.mk_mul, hz2, QuotientGroup.mk_one, map_one]) with h | h
    · exfalso
      apply not_mem_pPrimeCore_of_orderOf hz
      have : (QuotientGroup.mk z : R ⧸ pPrimeCore 2 R) = 1 := e.injective (by rw [h, map_one])
      exact (QuotientGroup.eq_one_iff z).1 this
    · exact h
  have hq : (QuotientGroup.mk a : R ⧸ pPrimeCore 2 R) = QuotientGroup.mk b :=
    e.injective (by rw [hneg ha, hneg hb])
  by_contra hne
  have hmem : a⁻¹ * b ∈ pPrimeCore 2 R := QuotientGroup.eq.1 hq
  have ha2 : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hb2 : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  rw [hainv] at hmem
  have hord : orderOf (a * b) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
        _ = a * (a * b) * b := by rw [hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
    · intro h1
      apply hne
      calc a = a * (a * b) := by rw [h1, mul_one]
        _ = b := by rw [← mul_assoc, ha2, one_mul]
  exact not_mem_pPrimeCore_of_orderOf hord hmem

end OddCore

theorem conj_eq_of_mem_normalizer {G : Type*} [Group G] [Finite G] {R : Subgroup G}
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (e : R ⧸ pPrimeCore 2 R ≃* SL(2, F)) {r y : G}
    (hR : R ≤ centralizer ({r} : Set G)) (hrR : r ∈ R) (hr : orderOf r = 2)
    (hy : y ∈ normalizer (R : Set G)) : y * r * y⁻¹ = r := by
  have hs : y * r * y⁻¹ ∈ R := (mem_normalizer_iff.1 hy r).1 hrR
  have hsr : orderOf (y * r * y⁻¹) = 2 := by
    rw [show y * r * y⁻¹ = MulAut.conj y r from rfl, MulEquiv.orderOf_eq]
    exact hr
  have hcomm : (⟨r, hrR⟩ : R) * ⟨y * r * y⁻¹, hs⟩ = ⟨y * r * y⁻¹, hs⟩ * ⟨r, hrR⟩ :=
    Subtype.ext (mem_centralizer_singleton_iff.1 (hR hs)).symm
  have h := eq_of_involutions h2 e (a := ⟨r, hrR⟩) (b := ⟨y * r * y⁻¹, hs⟩)
    (by rw [Subgroup.orderOf_mk]; exact hr) (by rw [Subgroup.orderOf_mk]; exact hsr) hcomm
  exact (congrArg Subtype.val h).symm

end CFSG.ComponentClassification.Burgoyne.C

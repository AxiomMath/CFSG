module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Split

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem noL2Layer_of_fix_eq {P : Type} [Group P] {ψ ψ' : MulAut P}
    (h : fixSubgroup ψ = fixSubgroup ψ') (hψ' : NoL2Layer ψ') : NoL2Layer ψ := by
  intro A hA r hr hT
  rw [h] at hA
  exact hψ' A hA r hr hT

theorem mulAut_pow_apply_of_fixed {P : Type} [Group P] {β : MulAut P} {x : P} (h : β x = x)
    (n : ℕ) : (β ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, h, ih]

theorem fixSubgroup_pow_eq_of_pow_pow {P : Type} [Group P] {β : MulAut P} {r j : ℕ}
    (hrj : (β ^ r) ^ j = β) : fixSubgroup (β ^ r) = fixSubgroup β := by
  ext x
  constructor
  · intro hx
    have h := mulAut_pow_apply_of_fixed (β := β ^ r) (x := x) hx j
    rw [hrj] at h
    exact h
  · intro hx
    exact mulAut_pow_apply_of_fixed (β := β) (x := x) hx r

theorem noL2Layer_congr {P P' : Type} [Group P] [Finite P] [Group P'] [Finite P'] (θ : P ≃* P')
    {ψ : MulAut P} (h : NoL2Layer (MulAut.congr θ ψ)) : NoL2Layer ψ := by
  intro A hA r hr hT
  have hker : θ.toMonoidHom.ker ≤ Subgroup.center P := by
    intro x hx
    have : x = 1 := θ.injective (by simpa using hx)
    rw [this]
    exact one_mem _
  obtain ⟨A', hA', hT'⟩ := typeL2_barOf_of_central θ.toMonoidHom θ.surjective hker ψ
    (MulAut.congr θ ψ) (fun y => by simp [MulAut.congr_apply]) hA hT
  exact h A' hA' r hr hT'

theorem noL2Layer_of_card_dvd_pp {P : Type} [Group P] [Finite P] (ψ : MulAut P) {N : ℕ}
    (hdvd : Nat.card ↥(fixSubgroup ψ) ∣ N)
    (harith : ∀ r m : ℕ, 10 ≤ r → IsPrimePow r → m + r = r ^ 3 → ¬ m ∣ 2 * N) :
    NoL2Layer ψ := by
  intro A hA r hr hT
  have hpp : IsPrimePow r := by
    obtain ⟨F, hF, hFin, hcard, -⟩ := hT
    have := Fintype.ofFinite F
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.isPrimePow_card F
  obtain ⟨-, hodd, heven⟩ := CFSG.HardMathSupport.Solomon.Proving.typeL2_card (barOf 3 A) hT
  have hc1 : Nat.card (barOf 3 A ⧸ Subgroup.center (barOf 3 A)) ∣ Nat.card (barOf 3 A) :=
    Subgroup.card_quotient_dvd_card _
  have hc2 : Nat.card (barOf 3 A) ∣ Nat.card ↥A := Subgroup.card_quotient_dvd_card _
  have hc3 : Nat.card ↥A ∣ Nat.card ↥(fixSubgroup ψ) := Subgroup.card_dvd_of_le hA.1
  have hc : Nat.card (barOf 3 A ⧸ Subgroup.center (barOf 3 A)) ∣ N :=
    hc1.trans (hc2.trans (hc3.trans hdvd))
  generalize Nat.card (barOf 3 A ⧸ Subgroup.center (barOf 3 A)) = c at hodd heven hc
  rcases Nat.even_or_odd r with he | ho
  · obtain ⟨h1, -⟩ := heven he
    exact harith r c hr hpp h1 (hc.trans (Dvd.intro_left 2 rfl))
  · have h1 := hodd ho
    exact harith r (2 * c) hr hpp (by omega) (Nat.mul_dvd_mul_left 2 hc)

theorem noL2Layer_of_card_dvd {P : Type} [Group P] [Finite P] (ψ : MulAut P) {N : ℕ}
    (hdvd : Nat.card ↥(fixSubgroup ψ) ∣ N)
    (harith : ∀ r m : ℕ, 10 ≤ r → m + r = r ^ 3 → ¬ m ∣ 2 * N) : NoL2Layer ψ :=
  noL2Layer_of_card_dvd_pp ψ hdvd fun r m hr _ hm => harith r m hr hm

theorem noL2Layer_of_conj_pow {P : Type} [Group P] [Finite P] {β η δ : MulAut P} {r j : ℕ}
    (hrj : (β ^ r) ^ j = β) (hδ : δ * β ^ r * δ⁻¹ = η) (h : NoL2Layer η) : NoL2Layer β := by
  have h1 : NoL2Layer (δ⁻¹ * η * δ⁻¹⁻¹) := noL2Layer_conj δ⁻¹ h
  have h2 : δ⁻¹ * η * δ⁻¹⁻¹ = β ^ r := by
    rw [← hδ]
    group
  rw [h2] at h1
  exact noL2Layer_of_fix_eq (fixSubgroup_pow_eq_of_pow_pow hrj).symm h1

theorem noL2_of_simple_normal_comm {P : Type} [Group P] [Finite P] (ψ : MulAut P)
    (S : Subgroup P) (hSle : S ≤ fixSubgroup ψ)
    (hcomm : ⁅fixSubgroup ψ, fixSubgroup ψ⁆ ≤ S) (hs : IsSimpleGroup ↥S)
    (hnab : ∃ a b : ↥S, a * b ≠ b * a) (hL2 : ∀ r : ℕ, 10 ≤ r → ¬ IsTypeL2 r ↥S) :
    NoL2Layer ψ := by
  intro A hA r hr hT
  have hq : CFSG.Open.IsQuasisimple ↥S := isQuasisimple_of_simple hnab
  have hAD : A ≤ fixSubgroup ψ := hA.1
  have hAS : A ≤ S := by
    have hperf := glaPComponent_perfect hA
    calc A = ⁅A, A⁆ := hperf.symm
      _ ≤ ⁅fixSubgroup ψ, fixSubgroup ψ⁆ := Subgroup.commutator_mono hAD hAD
      _ ≤ S := hcomm
  have hsn : IsSubnormal A S := isSubnormal_of_le_of_le hA.2.1 hAS hSle
  have hAeq : A = S :=
    Lemma510Ns.eq_of_isSubnormal_of_quasisimple hq hsn (glaPComponent_perfect hA)
      (glaPComponent_ne_bot hA)
  have hAq := isQuasisimple_barOf_of_glaPComponent Nat.prime_three hA
  subst hAeq
  have hcore : GLAPPrimeCore 3 ↥A = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥A) with h | h
    · exact h
    · exfalso
      have hsub : Subsingleton (barOf 3 A) := by
        refine ⟨fun a b => ?_⟩
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [QuotientGroup.eq]
            rw [h]
            exact Subgroup.mem_top _
      have hs2 : Subsingleton (barOf 3 A ⧸ Subgroup.center (barOf 3 A)) :=
        (QuotientGroup.mk'_surjective (Subgroup.center (barOf 3 A))).subsingleton
      exact (not_nontrivial_iff_subsingleton.2 hs2) hAq.2.toNontrivial
  have e : barOf 3 A ≃* ↥A :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans (QuotientGroup.quotientBot (G := ↥A))
  exact hL2 r hr (l2fld_isTypeL2_of_mulEquiv e hT)

theorem congr_mem_inner_iff_of_equiv {G H : Type*} [Group G] [Group H] (θ : G ≃* H)
    (α : MulAut G) :
    MulAut.congr θ α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner H ↔
      α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner G := by
  have key : ∀ x : G, MulAut.congr θ (MulAut.conj x) = MulAut.conj (θ x) := fun x => by
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨θ.symm y, ?_⟩
    apply (MulAut.congr θ).injective
    rw [key, MulEquiv.apply_symm_apply, hy]
  · rintro ⟨x, rfl⟩
    exact ⟨θ x, (key x).symm⟩

theorem noL2Layer_of_fixed_equiv {P : Type} [Group P] [Finite P] (ψ : MulAut P) {X : Type}
    [Group X] (e : ↥(fixSubgroup ψ) ≃* X) (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) (hL2 : ∀ r : ℕ, 10 ≤ r → ¬ IsTypeL2 r X) :
    NoL2Layer ψ := by
  haveI : IsSimpleGroup ↥(fixSubgroup ψ) := e.isSimpleGroup
  refine noL2_of_simple_fixed ψ inferInstance ?_ fun r hr hT =>
    hL2 r hr (l2fld_isTypeL2_of_mulEquiv e hT)
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩

theorem nonempty_commutator_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nonempty (↥(commutator G) ≃* ↥(commutator H)) := by
  refine ⟨(e.subgroupMap (commutator G)).trans (MulEquiv.subgroupCongr ?_)⟩
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ e.surjective]

theorem noL2Layer_of_fixed_commutator_equiv {P : Type} [Group P] [Finite P] (ψ : MulAut P)
    {X : Type} [Group X] (e : ↥(commutator ↥(fixSubgroup ψ)) ≃* X) (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) (hL2 : ∀ r : ℕ, 10 ≤ r → ¬ IsTypeL2 r X) :
    NoL2Layer ψ := by
  have eS : ↥⁅fixSubgroup ψ, fixSubgroup ψ⁆ ≃* ↥(commutator ↥(fixSubgroup ψ)) :=
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator (fixSubgroup ψ)).symm).trans
      ((commutator ↥(fixSubgroup ψ)).equivMapOfInjective (fixSubgroup ψ).subtype
        (fixSubgroup ψ).subtype_injective).symm
  let e' : ↥⁅fixSubgroup ψ, fixSubgroup ψ⁆ ≃* X := eS.trans e
  haveI : IsSimpleGroup ↥⁅fixSubgroup ψ, fixSubgroup ψ⁆ := e'.isSimpleGroup
  refine noL2_of_simple_commutator_fixed ψ _ rfl inferInstance ?_ fun r hr hT =>
    hL2 r hr (l2fld_isTypeL2_of_mulEquiv e' hT)
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e'.symm a, e'.symm b, fun h => hab (e'.symm.injective (by simpa using h))⟩

theorem exists_noncomm_of_center_bot {G : Type*} [Group G] [Nontrivial G]
    (h : Subgroup.center G = ⊥) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  have hxc : x ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun g => (hcon g x)
  rw [h, Subgroup.mem_bot] at hxc
  exact hx hxc

end CFSG.HardMathSupport.Dickson.Sec6.I923

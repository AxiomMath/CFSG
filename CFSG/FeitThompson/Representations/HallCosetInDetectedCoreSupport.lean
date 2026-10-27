module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers
public import CFSG.FeitThompson.Representations.CoprimePrimeAutFixedConjugacyClasses
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup
import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
import CFSG.FeitThompson.Foundations.SolvableHallConjugacy

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

section Aux

variable {A P : Type*} [Group A] [Group P]

private theorem apply_zpow_eq_self (φ : A →* MulAut P) {a : A} {x : P} (h : φ a x = x) (k : ℤ) :
    φ (a ^ k) x = x := by
  have hmem : φ a ∈ MulAction.stabilizer (MulAut P) x := h
  have h2 := (MulAction.stabilizer (MulAut P) x).zpow_mem hmem k
  rw [map_zpow]
  exact h2

private theorem isInvariantSubgroup_of_forall_apply_mem {ρ : A →* MulAut P} {N : Subgroup P}
    (h : ∀ b : A, ∀ v ∈ N, ρ b v ∈ N) : IsInvariantSubgroup ρ N := by
  refine isInvariantSubgroup_iff_forall_map_eq.2 fun b => le_antisymm ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact h b v hv
  · intro v hv
    refine ⟨ρ b⁻¹ v, h b⁻¹ v hv, ?_⟩
    change ρ b (ρ b⁻¹ v) = v
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

end Aux

section TypeLevel

variable {X : Type*} [Group X] {H I H0 : Subgroup X}

theorem autFixedSubgroup_conjQuotientAut_ne_bot_iff [H.Normal] [H0.Normal] (i : X) :
    autFixedSubgroup (conjQuotientAut H H0 i) ≠ ⊥ ↔
      ∃ h ∈ H, h ∉ H0 ∧ h⁻¹ * (i⁻¹ * h * i) ∈ H0 := by
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  constructor
  · rintro ⟨⟨x, hx⟩, hx1⟩
    rw [mem_autFixedSubgroup] at hx
    have hx1' : x ≠ 1 := fun hc => hx1 (Subtype.ext hc)
    induction x using QuotientGroup.induction_on with
    | _ h =>
      rw [conjQuotientAut_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hx
      have hcoe : (((MulAut.conjNormal (H := H) i h : ↥H))⁻¹ * h : ↥H) =
          ((i * (h : X) * i⁻¹)⁻¹ * (h : X) : X) := rfl
      rw [hcoe] at hx
      refine ⟨(h : X), h.2, ?_, ?_⟩
      · intro hmem
        exact hx1' ((QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hmem))
      · have hc := ‹H0.Normal›.conj_mem _ hx i⁻¹
        have heq : i⁻¹ * ((i * (h : X) * i⁻¹)⁻¹ * (h : X)) * i⁻¹⁻¹
            = (h : X)⁻¹ * (i⁻¹ * (h : X) * i) := by group
        rwa [heq] at hc
  · rintro ⟨h, hh, hhH0, hfix⟩
    refine ⟨⟨QuotientGroup.mk ⟨h, hh⟩, ?_⟩, ?_⟩
    · rw [mem_autFixedSubgroup, conjQuotientAut_apply_mk, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have hcoe : (((MulAut.conjNormal (H := H) i ⟨h, hh⟩ : ↥H))⁻¹ * ⟨h, hh⟩ : ↥H) =
          ((i * h * i⁻¹)⁻¹ * h : X) := rfl
      rw [hcoe]
      have hc := ‹H0.Normal›.conj_mem _ hfix i
      have heq : i * (h⁻¹ * (i⁻¹ * h * i)) * i⁻¹ = ((i * h * i⁻¹)⁻¹ * h : X) := by group
      rwa [heq] at hc
    · intro hcon
      have hone : (QuotientGroup.mk ⟨h, hh⟩ : ↥H ⧸ H0.subgroupOf H) = 1 :=
        congrArg Subtype.val hcon
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hone
      exact hhH0 hone

theorem exists_ne_one_mem_commute_of_conj_mem [Finite X] [H.Normal] [H0.Normal]
    [Group.IsSolvable ↥H] {i : X} (hcop : (orderOf i).Coprime (Nat.card ↥H)) {h : X}
    (hh : h ∈ H) (hhH0 : h ∉ H0) (hfix : h⁻¹ * (i⁻¹ * h * i) ∈ H0) :
    ∃ v ∈ H, v ≠ 1 ∧ v * i = i * v := by
  set A := Subgroup.zpowers i with hA
  set ρ : ↥A →* MulAut ↥H := (MulAut.conjNormal (H := H)).comp A.subtype with hρ
  set N : Subgroup ↥H := H0.subgroupOf H with hN
  have hNnormal : N.Normal := ‹H0.Normal›.subgroupOf H
  have hinv : IsInvariantSubgroup ρ N := by
    refine isInvariantSubgroup_of_forall_apply_mem fun b v hv => ?_
    rw [hN, Subgroup.mem_subgroupOf] at hv ⊢
    have hco : ((ρ b v : ↥H) : X) = (b : X) * (v : X) * (b : X)⁻¹ := rfl
    rw [hco]
    exact ‹H0.Normal›.conj_mem _ hv _
  have hcopA : (Nat.card ↥A).Coprime (Nat.card ↥H) := by rwa [hA, Nat.card_zpowers]
  set a₀ : ↥A := ⟨i, Subgroup.mem_zpowers i⟩ with ha₀
  set x : ↥H ⧸ N := QuotientGroup.mk ⟨h, hh⟩ with hx
  have hbase : hinv.quotientAut a₀ x = x := by
    rw [hx, IsInvariantSubgroup.quotientAut_mk, QuotientGroup.eq, hN, Subgroup.mem_subgroupOf]
    have hcoe : (((ρ a₀ ⟨h, hh⟩ : ↥H))⁻¹ * (⟨h, hh⟩ : ↥H) : ↥H) = ((i * h * i⁻¹)⁻¹ * h : X) := rfl
    rw [hcoe]
    have hconj := ‹H0.Normal›.conj_mem _ hfix i
    have heq : ((i * h * i⁻¹)⁻¹ * h : X) = i * (h⁻¹ * (i⁻¹ * h * i)) * i⁻¹ := by group
    rw [heq]
    exact hconj
  have hxfix : ∀ b : ↥A, hinv.quotientAut b x = x := by
    intro b
    obtain ⟨k, hk⟩ := b.2
    have hb : b = a₀ ^ k := by
      refine Subtype.ext ?_
      rw [SubgroupClass.coe_zpow, ha₀]
      exact hk.symm
    rw [hb]
    exact apply_zpow_eq_self _ hbase k
  have hAsolv : Group.IsSolvable ↥A :=
    Group.isSolvable_of_comm fun a b => (Subgroup.zpowers_isMulCommutative i).is_comm.comm a b
  obtain ⟨v, hv, hvx⟩ := exists_mem_fixedPoints_range_mk_eq hinv hcopA hxfix
  refine ⟨(v : X), v.2, ?_, ?_⟩
  · intro h1
    have hv1 : v = 1 := Subtype.ext h1
    rw [hv1, hx] at hvx
    have hmem : (1 : ↥H)⁻¹ * (⟨h, hh⟩ : ↥H) ∈ N := QuotientGroup.eq.1 hvx
    rw [hN, Subgroup.mem_subgroupOf] at hmem
    simp only [inv_one, one_mul] at hmem
    exact hhH0 hmem
  · have hfixv := (mem_fixedPoints_range_iff ρ).1 hv a₀
    have hcoe : ((ρ a₀ v : ↥H) : X) = i * (v : X) * i⁻¹ := rfl
    have h2 : i * (v : X) * i⁻¹ = (v : X) := by rw [← hcoe, hfixv]
    calc (v : X) * i = (i * (v : X) * i⁻¹) * i := by rw [h2]
      _ = i * (v : X) := by group

theorem exists_ne_one_mem_commute [Finite X] [Group.IsSolvable X] [H.Normal] [H0.Normal]
    (hcomp : H.IsComplement' I) (hcop : (Nat.card ↥H).Coprime (Nat.card ↥I))
    (hfix : ∀ i ∈ I, ∃ h ∈ H, h ∉ H0 ∧ h⁻¹ * (i⁻¹ * h * i) ∈ H0) (y : X) :
    ∃ v ∈ H, v ≠ 1 ∧ v * y = y * v := by
  classical
  set π : Set ℕ := ((Nat.card ↥H).primeFactors : Set ℕ) with hπdef
  have hindexH : H.index = Nat.card ↥I := hcomp.symm.index_eq_card
  have hindexI : I.index = Nat.card ↥H := hcomp.index_eq_card
  have hnotmem : ∀ q ∈ (Nat.card ↥I).primeFactors, q ∉ π := by
    intro q hq hq'
    rw [hπdef, Finset.mem_coe] at hq'
    exact (Nat.prime_of_mem_primeFactors hq).one_lt.ne'
      (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hq')
        (Nat.dvd_of_mem_primeFactors hq)))
  by_cases hπ : ∃ p ∈ (orderOf y).primeFactors, p ∈ π
  ·
    obtain ⟨p, hp, hpπ⟩ := hπ
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    set v : X := y ^ (orderOf y / p) with hv
    have hov : orderOf v = p :=
      orderOf_pow_orderOf_div (orderOf_pos y).ne' (Nat.dvd_of_mem_primeFactors hp)
    have hHall : IsHallPiSubgroup π H := by
      refine ⟨isPiSubgroup_iff.2 fun q hq => by rwa [hπdef, Finset.mem_coe], ?_⟩
      rw [hindexH]
      exact hnotmem
    have hvH : v ∈ H := by
      rw [hHall.mem_iff, hov]
      intro q hq
      rw [hpprime.primeFactors, Finset.mem_singleton] at hq
      rw [hq]
      exact hpπ
    refine ⟨v, hvH, ?_, ?_⟩
    · intro hcon
      rw [hcon, orderOf_one] at hov
      exact hpprime.one_lt.ne hov
    · rw [hv]
      exact (Commute.self_pow y _).symm.eq
  ·
    simp only [not_exists, not_and] at hπ
    have hU : IsPiSubgroup πᶜ (Subgroup.zpowers y) := by
      refine isPiSubgroup_iff.2 fun q hq => ?_
      rw [Nat.card_zpowers] at hq
      exact hπ q hq
    have hIHall : IsHallSubgroup πᶜ I := by
      refine ⟨isPiNumber_iff.2 fun q hq => hnotmem q hq, ?_⟩
      rw [compl_compl, hindexI]
      exact isPiNumber_iff.2 fun q hq => by rwa [hπdef, Finset.mem_coe]
    obtain ⟨J, hJ, hUJ⟩ := exists_isHallSubgroup_ge_of_isPiSubgroup hU
    obtain ⟨g, hg⟩ := exists_conj_smul_eq_of_isHallSubgroup hJ hIHall
    have hyJ : y ∈ J := hUJ (Subgroup.mem_zpowers y)
    have hiI : g * y * g⁻¹ ∈ I := by
      have h1 : MulAut.conj g • y ∈ MulAut.conj g • J :=
        Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) J hyJ
      rw [hg] at h1
      exact h1
    have horder : orderOf (g * y * g⁻¹) = orderOf y :=
      (SemiconjBy.orderOf_eq g (x := y) (y := g * y * g⁻¹) (by simp [SemiconjBy, mul_assoc])).symm
    have hcopH : (orderOf (g * y * g⁻¹)).Coprime (Nat.card ↥H) := by
      rw [horder]
      refine Nat.Coprime.symm (IsPiNumber.coprime_of_compl (π := π) ?_ ?_ Nat.card_pos.ne'
        (orderOf_pos y).ne')
      · exact isPiNumber_iff.2 fun q hq => by rwa [hπdef, Finset.mem_coe]
      · exact isPiNumber_iff.2 fun q hq => hπ q hq
    obtain ⟨h, hh, hhH0, hfix'⟩ := hfix _ hiI
    obtain ⟨v, hv, hv1, hcomm⟩ :=
      exists_ne_one_mem_commute_of_conj_mem (H0 := H0) hcopH hh hhH0 hfix'
    refine ⟨g⁻¹ * v * g, by simpa using ‹H.Normal›.conj_mem v hv g⁻¹, ?_, ?_⟩
    · refine fun hcon => hv1 ?_
      have hvv : v = g * (g⁻¹ * v * g) * g⁻¹ := by group
      rw [hvv, hcon]; group
    · have h2 : v * (g * y * g⁻¹) = (g * y * g⁻¹) * v := hcomm
      calc g⁻¹ * v * g * y = g⁻¹ * (v * (g * y * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * y * g⁻¹) * v) * g := by rw [h2]
        _ = y * (g⁻¹ * v * g) := by group

theorem inf_centralizer_ne_bot [Finite X] [Group.IsSolvable X] [H.Normal] [H0.Normal]
    (hcomp : H.IsComplement' I) (hcop : (Nat.card ↥H).Coprime (Nat.card ↥I))
    (hfix : ∀ i ∈ I, autFixedSubgroup (conjQuotientAut H H0 i) ≠ ⊥) (y : X) :
    H ⊓ Subgroup.centralizer {y} ≠ ⊥ := by
  obtain ⟨v, hv, hv1, hcomm⟩ := exists_ne_one_mem_commute (H0 := H0) hcomp hcop
    (fun i hi => (autFixedSubgroup_conjQuotientAut_ne_bot_iff i).1 (hfix i hi)) y
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  exact ⟨⟨v, Subgroup.mem_inf.2 ⟨hv, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩⟩,
    fun hc => hv1 (congrArg Subtype.val hc)⟩

end TypeLevel

section Ambient

variable {K : Type*} [Group K] {Xs H I H0 : Subgroup K}

theorem exists_ne_one_mem_commute_of_le [Finite ↥Xs] [Group.IsSolvable ↥Xs]
    (hHn : (H.subgroupOf Xs).Normal) (hH0n : (H0.subgroupOf Xs).Normal) (hHX : H ≤ Xs)
    (hIX : I ≤ Xs) (hdisj : Disjoint H I) (hsup : H ⊔ I = Xs)
    (hcop : (Nat.card ↥H).Coprime (Nat.card ↥I))
    (hfix : ∀ i ∈ I, ∃ h ∈ H, h ∉ H0 ∧ h⁻¹ * (i⁻¹ * h * i) ∈ H0) {y : K} (hy : y ∈ Xs) :
    ∃ h ∈ H, h ≠ 1 ∧ h * y = y * h := by
  have _inst := hHn
  have _inst := hH0n
  have hcomp : (H.subgroupOf Xs).IsComplement' (I.subgroupOf Xs) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff, eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
      have hxK : (x : K) ∈ H ⊓ I := Subgroup.mem_inf.2 hx
      rw [disjoint_iff.1 hdisj, Subgroup.mem_bot] at hxK
      exact Subgroup.mem_bot.2 (Subtype.ext hxK)
    · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup hHX hIX, hsup, Subgroup.subgroupOf_self]
      simp
  have hcardH : Nat.card ↥(H.subgroupOf Xs) = Nat.card ↥H :=
    Nat.card_eq_of_bijective _ (Subgroup.subgroupOfEquivOfLe hHX).bijective
  have hcardI : Nat.card ↥(I.subgroupOf Xs) = Nat.card ↥I :=
    Nat.card_eq_of_bijective _ (Subgroup.subgroupOfEquivOfLe hIX).bijective
  have hcop' : (Nat.card ↥(H.subgroupOf Xs)).Coprime (Nat.card ↥(I.subgroupOf Xs)) := by
    rw [hcardH, hcardI]; exact hcop
  have hfix' : ∀ i : ↥Xs, i ∈ I.subgroupOf Xs → ∃ h ∈ H.subgroupOf Xs,
      h ∉ H0.subgroupOf Xs ∧ h⁻¹ * (i⁻¹ * h * i) ∈ H0.subgroupOf Xs := by
    intro i hi
    obtain ⟨h, hh, hhH0, hcon⟩ := hfix (i : K) (Subgroup.mem_subgroupOf.1 hi)
    refine ⟨⟨h, hHX hh⟩, Subgroup.mem_subgroupOf.2 hh, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]; exact hhH0
    · rw [Subgroup.mem_subgroupOf]; push_cast; exact hcon
  obtain ⟨v, hv, hv1, hcomm⟩ :=
    exists_ne_one_mem_commute (H0 := H0.subgroupOf Xs) hcomp hcop' hfix' ⟨y, hy⟩
  exact ⟨(v : K), Subgroup.mem_subgroupOf.1 hv, by simpa using hv1, congrArg Subtype.val hcomm⟩

theorem inf_centralizer_ne_bot_of_le [Finite ↥Xs] [Group.IsSolvable ↥Xs]
    (hHn : (H.subgroupOf Xs).Normal) (hH0n : (H0.subgroupOf Xs).Normal) (hHX : H ≤ Xs)
    (hIX : I ≤ Xs) (hdisj : Disjoint H I) (hsup : H ⊔ I = Xs)
    (hcop : (Nat.card ↥H).Coprime (Nat.card ↥I))
    (hfix : ∀ i ∈ I, ∃ h ∈ H, h ∉ H0 ∧ h⁻¹ * (i⁻¹ * h * i) ∈ H0) {y : K} (hy : y ∈ Xs) :
    H ⊓ Subgroup.centralizer {y} ≠ ⊥ := by
  obtain ⟨h, hh, hh1, hcomm⟩ :=
    exists_ne_one_mem_commute_of_le hHn hH0n hHX hIX hdisj hsup hcop hfix hy
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  exact ⟨⟨h, Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩⟩,
    fun hc => hh1 (congrArg Subtype.val hc)⟩

theorem sdiff_singleton_one_subset_of_centralizer_sdiff_subset [Finite ↥Xs]
    [Group.IsSolvable ↥Xs] (hHn : (H.subgroupOf Xs).Normal) (hH0n : (H0.subgroupOf Xs).Normal)
    (hHX : H ≤ Xs) (hIX : I ≤ Xs) (hdisj : Disjoint H I) (hsup : H ⊔ I = Xs)
    (hcop : (Nat.card ↥H).Coprime (Nat.card ↥I))
    (hfix : ∀ i ∈ I, ∃ h ∈ H, h ∉ H0 ∧ h⁻¹ * (i⁻¹ * h * i) ∈ H0) {A : Set K}
    (hA : ∀ h ∈ H, h ≠ 1 → (Subgroup.centralizer {h} : Set K) \ {1} ⊆ A) :
    (Xs : Set K) \ {1} ⊆ A := by
  rintro y ⟨hy, hy1⟩
  rw [Set.mem_singleton_iff] at hy1
  obtain ⟨h, hh, hh1, hcomm⟩ :=
    exists_ne_one_mem_commute_of_le hHn hH0n hHX hIX hdisj hsup hcop hfix hy
  exact hA h hh hh1 ⟨Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm, hy1⟩

end Ambient

end CFSG.FeitThompson

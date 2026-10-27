module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78AltCentralizer
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.Sol78

variable {N m : ℕ} {H : Subgroup (Perm (Fin N))}

theorem ncard_orbit_le (ω : Fin N) : (MulAction.orbit H ω).ncard ≤ N := by
  calc (MulAction.orbit H ω).ncard ≤ (Set.univ : Set (Fin N)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _)
    _ = N := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem le_ncard_orbit (hm : 5 ≤ m) (e : H ≃* alternatingGroup (Fin m)) {ω : Fin N}
    (hω : MulAction.stabilizer H ω ≠ ⊤) : m ≤ (MulAction.orbit H ω).ncard := by
  rw [← MulAction.index_stabilizer]
  exact le_index_of_mulEquiv_alternating hm e hω

theorem mem_orbit_of_ne_top (hm : 5 ≤ m) (hNm : N < 2 * m) (e : H ≃* alternatingGroup (Fin m))
    {ω ω' : Fin N} (h : MulAction.stabilizer H ω ≠ ⊤) (h' : MulAction.stabilizer H ω' ≠ ⊤) :
    ω' ∈ MulAction.orbit H ω := by
  by_contra hnot
  have hdisj : Disjoint (MulAction.orbit H ω) (MulAction.orbit H ω') := by
    rw [Set.disjoint_left]
    intro x hx hx'
    apply hnot
    have h1 : MulAction.orbit H x = MulAction.orbit H ω := MulAction.orbit_eq_iff.mpr hx
    have h2 : MulAction.orbit H x = MulAction.orbit H ω' := MulAction.orbit_eq_iff.mpr hx'
    rw [← h1, h2]
    exact MulAction.mem_orbit_self ω'
  have h1 := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  have h2 : (MulAction.orbit H ω ∪ MulAction.orbit H ω').ncard ≤ N := by
    calc _ ≤ (Set.univ : Set (Fin N)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
      _ = N := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h3 := le_ncard_orbit hm e h
  have h4 := le_ncard_orbit hm e h'
  omega

theorem normalizer_stabilizer_le (hm : 5 ≤ m) (hNm : N < 2 * m)
    (e : H ≃* alternatingGroup (Fin m)) {ω : Fin N} (hω : MulAction.stabilizer H ω ≠ ⊤) :
    normalizer (MulAction.stabilizer H ω : Set H) ≤ MulAction.stabilizer H ω := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by simpa using hm)
  have : IsSimpleGroup H := e.isSimpleGroup
  have hcardH : Nat.card H = m.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hfac : 2 * N < m.factorial := by
    have h1 : (4 : ℕ).factorial ≤ (m - 1).factorial := Nat.factorial_le (by omega)
    have h2 : m * (m - 1).factorial = m.factorial := Nat.mul_factorial_pred (by omega)
    have h3 : (4 : ℕ).factorial = 24 := rfl
    nlinarith
  have hSN : MulAction.stabilizer H ω ≤ normalizer (MulAction.stabilizer H ω : Set H) :=
    le_normalizer
  have hle := ncard_orbit_le (H := H) ω
  rw [← MulAction.index_stabilizer] at hle
  by_cases hNtop : normalizer (MulAction.stabilizer H ω : Set H) = ⊤
  · exfalso
    have hSn : (MulAction.stabilizer H ω).Normal := normalizer_eq_top_iff.mp hNtop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAction.stabilizer H ω) with h | h
    · rw [h, Subgroup.index_bot, hcardH] at hle
      have heven : m.factorial / 2 * 2 = m.factorial :=
        Nat.div_mul_cancel (Nat.dvd_factorial (by norm_num) (by omega))
      omega
    · exact hω h
  · have h1 := le_index_of_mulEquiv_alternating hm e hNtop
    have h2 := Subgroup.relIndex_mul_index hSN
    rw [← h2] at hle
    have hS0 : (MulAction.stabilizer H ω).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hri : (MulAction.stabilizer H ω).relIndex
        (normalizer (MulAction.stabilizer H ω : Set H)) = 1 := by
      by_contra hne
      have hpos : (MulAction.stabilizer H ω).relIndex
          (normalizer (MulAction.stabilizer H ω : Set H)) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at h2
        exact hS0 h2.symm
      have h3 : 2 ≤ (MulAction.stabilizer H ω).relIndex
          (normalizer (MulAction.stabilizer H ω : Set H)) := by omega
      have h4 := Nat.mul_le_mul h3 h1
      omega
    exact Subgroup.relIndex_eq_one.mp hri

theorem fix_of_commute (hm : 5 ≤ m) (hNm : N < 2 * m) (e : H ≃* alternatingGroup (Fin m))
    {σ : Perm (Fin N)} (hσ : ∀ h ∈ H, h * σ = σ * h) {ω : Fin N}
    (hω : MulAction.stabilizer H ω ≠ ⊤) : σ ω = ω := by
  have hstabσ : ∀ ω : Fin N, MulAction.stabilizer H (σ ω) = MulAction.stabilizer H ω := by
    intro ω
    ext h
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, Subgroup.smul_def,
      Subgroup.smul_def, Perm.smul_def, Perm.smul_def]
    have hc := hσ h h.2
    constructor
    · intro hh
      apply σ.injective
      calc σ ((h : Perm (Fin N)) ω) = ((σ * h : Perm (Fin N))) ω := rfl
        _ = ((h * σ : Perm (Fin N))) ω := by rw [hc]
        _ = σ ω := hh
    · intro hh
      calc (h : Perm (Fin N)) (σ ω) = ((h * σ : Perm (Fin N))) ω := rfl
        _ = ((σ * h : Perm (Fin N))) ω := by rw [hc]
        _ = σ ω := by rw [Perm.mul_apply, hh]
  have hσω : MulAction.stabilizer H (σ ω) ≠ ⊤ := by rw [hstabσ]; exact hω
  obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp (mem_orbit_of_ne_top hm hNm e hω hσω)
  have hconj : (MulAction.stabilizer H ω).map (MulAut.conj h).toMonoidHom =
      MulAction.stabilizer H ω := by
    rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hh, hstabσ]
  have hhN : h ∈ normalizer (MulAction.stabilizer H ω : Set H) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hconj]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hconj] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by
        simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
          mul_left_inj, mul_right_inj] using hyx
      rwa [← this]
  have hhS := MulAction.mem_stabilizer_iff.mp (normalizer_stabilizer_le hm hNm e hω hhN)
  rw [← hh, hhS]

theorem exists_stabilizer_ne_top (hm : 5 ≤ m) (e : H ≃* alternatingGroup (Fin m)) :
    ∃ ω : Fin N, MulAction.stabilizer H ω ≠ ⊤ := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  by_contra hall
  push Not at hall
  have hsub : Subsingleton H := by
    constructor
    intro a b
    have hone : ∀ h : H, h = 1 := by
      intro h
      apply Subtype.ext
      apply Equiv.ext
      intro ω
      have hmem : h ∈ MulAction.stabilizer H ω := by rw [hall ω]; exact mem_top h
      rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, Perm.smul_def] at hmem
      simpa using hmem
    rw [hone a, hone b]
  have h1 : Nat.card H = 1 := Nat.card_unique
  have hcardH : Nat.card H = m.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have h2 : (5 : ℕ).factorial ≤ m.factorial := Nat.factorial_le hm
  have h3 : (5 : ℕ).factorial = 120 := rfl
  omega

theorem card_support_le_of_commute (hm : 5 ≤ m) (hNm : N < 2 * m)
    (e : H ≃* alternatingGroup (Fin m)) {σ : Perm (Fin N)} (hσ : ∀ h ∈ H, h * σ = σ * h) :
    σ.support.card ≤ N - m := by
  obtain ⟨ω₀, hω₀⟩ := exists_stabilizer_ne_top hm e
  have horbbig : ∀ ω ∈ MulAction.orbit H ω₀, MulAction.stabilizer H ω ≠ ⊤ := by
    intro ω hω htop
    have h1 : MulAction.orbit H ω = MulAction.orbit H ω₀ := MulAction.orbit_eq_iff.mpr hω
    have h2 := le_ncard_orbit hm e hω₀
    have h3 : (MulAction.orbit H ω).ncard = 1 := by
      rw [← MulAction.index_stabilizer, htop, Subgroup.index_top]
    rw [h1] at h3
    omega
  have h1 : ((σ.support : Finset (Fin N)) : Set (Fin N)) ⊆ (MulAction.orbit H ω₀)ᶜ := by
    intro ω hω hmem
    exact (mem_support.mp hω) (fix_of_commute hm hNm e hσ (horbbig ω hmem))
  have h2 := Set.ncard_le_ncard h1 (Set.toFinite _)
  rw [Set.ncard_coe_finset] at h2
  have h3 := Set.ncard_add_ncard_compl (MulAction.orbit H ω₀) (Set.toFinite _) (Set.toFinite _)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
  have h4 := le_ncard_orbit hm e hω₀
  omega

theorem isThreeCycle_of_card_support_le_four {σ : Perm (Fin N)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1)
    (h4 : σ.support.card ≤ 4) : σ.IsThreeCycle := by
  have hord : orderOf σ = 3 := orderOf_eq_prime h3 h1
  have hall : ∀ x ∈ σ.cycleType, x = 3 := by
    intro x hx
    have hdvd := dvd_of_mem_cycleType hx
    rw [hord] at hdvd
    have h2 := two_le_of_mem_cycleType hx
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · omega
    · exact h
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 3 :=
    Multiset.eq_replicate_card.mpr hall
  have hsum := sum_cycleType σ
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hne : Multiset.card σ.cycleType ≠ 0 := by
    intro h0
    rw [Multiset.card_eq_zero, cycleType_eq_zero] at h0
    exact h1 h0
  rw [← card_support_eq_three_iff]
  omega

theorem isThreeCycle_of_commute (hm : 5 ≤ m) (hNm : N < 2 * m) (hN4 : N ≤ m + 4)
    (e : H ≃* alternatingGroup (Fin m)) {σ : Perm (Fin N)} (hσ : ∀ h ∈ H, h * σ = σ * h)
    (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) : σ.IsThreeCycle :=
  isThreeCycle_of_card_support_le_four h3 h1
    (by have := card_support_le_of_commute hm hNm e hσ; omega)

@[expose] def altGeThree (m : ℕ) : Subgroup (Perm (Fin m)) :=
  (alternatingGroup {i : Fin m // 3 ≤ (i : ℕ)}).map Perm.ofSubtype

theorem card_geThree (m : ℕ) : Fintype.card {i : Fin m // 3 ≤ (i : ℕ)} = m - 3 := by
  let e : {i : Fin m // 3 ≤ (i : ℕ)} ≃ Fin (m - 3) :=
    { toFun := fun i => ⟨(i : ℕ) - 3, by have := i.1.2; have := i.2; omega⟩
      invFun := fun j => ⟨⟨(j : ℕ) + 3, by have := j.2; omega⟩, by simp⟩
      left_inv := fun i => by
        apply Subtype.ext
        apply Fin.ext
        simp only
        have := i.2
        omega
      right_inv := fun j => by
        apply Fin.ext
        simp }
  rw [Fintype.card_congr e, Fintype.card_fin]

theorem altGeThree_le (m : ℕ) : altGeThree m ≤ alternatingGroup (Fin m) := by
  rintro _ ⟨τ, hτ, rfl⟩
  rw [mem_alternatingGroup, sign_ofSubtype]
  exact hτ

@[expose] noncomputable def altGeThreeEquiv (m : ℕ) :
    altGeThree m ≃* alternatingGroup (Fin (m - 3)) :=
  ((alternatingGroup {i : Fin m // 3 ≤ (i : ℕ)}).equivMapOfInjective _
    Perm.ofSubtype_injective).symm.trans
      (Equiv.altCongrHom (Fintype.equivFinOfCardEq (card_geThree m)))

theorem commute_of_mem_altGeThree {x σ : Perm (Fin m)} (hx : x ∈ altGeThree m)
    (hσ : ∀ i : Fin m, 3 ≤ (i : ℕ) → σ i = i) : x * σ = σ * x := by
  obtain ⟨τ, -, rfl⟩ := hx
  refine Perm.Disjoint.commute (fun i => ?_) |>.eq
  by_cases hi : 3 ≤ (i : ℕ)
  · exact Or.inr (hσ i hi)
  · exact Or.inl (ofSubtype_apply_of_not_mem τ (p := fun i : Fin m => 3 ≤ (i : ℕ)) hi)

theorem exists_fixed_of_mulEquiv_alternating (hm : 8 ≤ m) {H : Subgroup (Perm (Fin (m + 1)))}
    (e : H ≃* alternatingGroup (Fin m)) : ∃ p : Fin (m + 1), ∀ h ∈ H, h p = p := by
  have hm5 : 5 ≤ m := by omega
  by_contra hno
  push Not at hno
  have hne : ∀ p : Fin (m + 1), MulAction.stabilizer H p ≠ ⊤ := by
    intro p htop
    obtain ⟨h, hh, hp⟩ := hno p
    have hmem : (⟨h, hh⟩ : H) ∈ MulAction.stabilizer H p := by rw [htop]; exact mem_top _
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, Perm.smul_def] at hmem
    exact hp hmem
  have : MulAction.IsPretransitive H (Fin (m + 1)) :=
    ⟨fun p q => MulAction.mem_orbit_iff.mp (mem_orbit_of_ne_top hm5 (by omega) e (hne p) (hne q))⟩
  have : Nontrivial (Fin (m + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have horb : MulAction.orbit H (0 : Fin (m + 1)) = Set.univ :=
    Set.eq_univ_of_forall fun q => mem_orbit_of_ne_top hm5 (by omega) e (hne 0) (hne q)
  have hidx : (MulAction.stabilizer H (0 : Fin (m + 1))).index = m + 1 := by
    rw [MulAction.index_stabilizer, horb, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hcoat : IsCoatom (MulAction.stabilizer H (0 : Fin (m + 1))) := by
    refine ⟨hne 0, fun K hK => ?_⟩
    by_contra hKtop
    have h1 := le_index_of_mulEquiv_alternating hm5 e hKtop
    have h2 := Subgroup.relIndex_mul_index hK.le
    rw [hidx] at h2
    have hri1 : (MulAction.stabilizer H (0 : Fin (m + 1))).relIndex K ≠ 1 := fun h =>
      hK.not_ge (Subgroup.relIndex_eq_one.mp h)
    have hri0 : (MulAction.stabilizer H (0 : Fin (m + 1))).relIndex K ≠ 0 := fun h => by
      rw [h, zero_mul] at h2
      omega
    have h3 : 2 ≤ (MulAction.stabilizer H (0 : Fin (m + 1))).relIndex K := by omega
    have h4 := Nat.mul_le_mul h3 h1
    omega
  have hprim : MulAction.IsPreprimitive H (Fin (m + 1)) :=
    (MulAction.isCoatom_stabilizer_iff_preprimitive _ _).mp hcoat
  set c0 : Perm (Fin m) := swap ⟨0, by omega⟩ ⟨1, by omega⟩ * swap ⟨0, by omega⟩ ⟨2, by omega⟩
    with hc0
  have hc03 : c0.IsThreeCycle :=
    isThreeCycle_swap_mul_swap_same (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff])
  have hc0fix : ∀ i : Fin m, 3 ≤ (i : ℕ) → c0 i = i := by
    intro i hi
    have h0 : i ≠ ⟨0, by omega⟩ := fun h => by rw [h] at hi; simp at hi
    have h1 : i ≠ ⟨1, by omega⟩ := fun h => by rw [h] at hi; simp at hi
    have h2 : i ≠ ⟨2, by omega⟩ := fun h => by rw [h] at hi; simp at hi
    rw [hc0, Perm.mul_apply, swap_apply_of_ne_of_ne h0 h2, swap_apply_of_ne_of_ne h0 h1]
  set c0' : alternatingGroup (Fin m) := ⟨c0, hc03.mem_alternatingGroup⟩ with hc0'
  set K' : Subgroup (alternatingGroup (Fin m)) :=
    (altGeThree m).subgroupOf (alternatingGroup (Fin m))
  set H' : Subgroup (Perm (Fin (m + 1))) := (K'.map e.symm.toMonoidHom).map H.subtype with hH'
  let e' : H' ≃* alternatingGroup (Fin (m - 3)) :=
    ((((K'.map e.symm.toMonoidHom).equivMapOfInjective H.subtype H.subtype_injective).symm.trans
      (K'.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm).trans
        (Subgroup.subgroupOfEquivOfLe (altGeThree_le m))).trans (altGeThreeEquiv m)
  set σ : Perm (Fin (m + 1)) := ((e.symm c0' : H) : Perm (Fin (m + 1))) with hσdef
  have hσ : ∀ h ∈ H', h * σ = σ * h := by
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    have hk' : (k : Perm (Fin m)) ∈ altGeThree m := hk
    have hkc : k * c0' = c0' * k := Subtype.ext (commute_of_mem_altGeThree hk' hc0fix)
    simp only [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, hσdef]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hkc]
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσdef, ← Subgroup.coe_pow, ← map_pow]
    have : c0' ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ← hc03.orderOf]
      exact pow_orderOf_eq_one _)
    rw [this, map_one]
    rfl
  have hσ1 : σ ≠ 1 := by
    intro h
    have h1 : e.symm c0' = 1 := Subtype.ext h
    rw [MulEquiv.map_eq_one_iff] at h1
    exact hc03.ne_one (congrArg Subtype.val h1)
  have hσ3c := isThreeCycle_of_commute (N := m + 1) (m := m - 3) (by omega) (by omega)
    (by omega) e' hσ hσ3 hσ1
  have hle := alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim hσ3c (e.symm c0').2
  have hcard := Subgroup.card_le_of_le hle
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, nat_card_alternatingGroup,
    Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card, Fintype.card_fin,
    Nat.factorial_succ] at hcard
  have hpos := Nat.factorial_pos m
  have heven : m.factorial / 2 * 2 = m.factorial :=
    Nat.div_mul_cancel (Nat.dvd_factorial (by norm_num) (by omega))
  have heven' : (m + 1) * m.factorial / 2 * 2 = (m + 1) * m.factorial :=
    Nat.div_mul_cancel (Dvd.dvd.mul_left (Nat.dvd_factorial (by norm_num) (by omega)) _)
  nlinarith

end CFSG.ComponentClassification.RankTwoAlt

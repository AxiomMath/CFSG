module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87AltOrb
public import CFSG.Permutation.FiveTransitive.LargePrimeCyclePrimitive
public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.PCycleJordan

public section

open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

namespace AltFivePerm

open Equiv Equiv.Perm Subgroup
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87.AltOrb

section Basic

variable {α : Type*}

def setStab (O : Set α) : Subgroup (Perm α) where
  carrier := {g | ∀ x, g x ∈ O ↔ x ∈ O}
  mul_mem' {g h} hg hh x := by
    show g (h x) ∈ O ↔ x ∈ O
    rw [hg, hh]
  one_mem' x := Iff.rfl
  inv_mem' {g} hg x := by
    have := hg (g⁻¹ x)
    simpa using this.symm

def restr (O : Set α) : setStab O →* Perm O where
  toFun g := (g : Perm α).subtypePerm (fun x => g.2 x)
  map_one' := by ext; simp
  map_mul' g h := by ext x; rfl

theorem orb_fixed {Q : Subgroup (Perm α)} {c : Perm α} (hQc : ⁅Q, zpowers c⁆ = Q) {a : α}
    (h : ∀ b ∈ Orb Q a, c b = b) : ∀ q ∈ Q, ∀ b ∈ Orb Q a, q b = b := by
  have hle : ⁅Q, zpowers c⁆ ≤ fixingSubgroup (Perm α) (Orb Q a) := by
    refine Subgroup.commutator_le.mpr fun q hq d hd => ?_
    rw [mem_fixingSubgroup_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := hd
    have hy' : q⁻¹ y ∈ Orb Q a := by
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨q⁻¹ * x, Q.mul_mem (Q.inv_mem hq) hx, rfl⟩
    have h2 : (c ^ k)⁻¹ y = y := by
      rw [← zpow_neg]
      exact zpow_apply_eq_self_of_apply_eq_self (h y hy) (-k)
    have h3 : (c ^ k) (q⁻¹ y) = q⁻¹ y := zpow_apply_eq_self_of_apply_eq_self (h _ hy') k
    show (⁅q, c ^ k⁆ : Perm α) y = y
    rw [commutatorElement_def, Perm.mul_apply, Perm.mul_apply, Perm.mul_apply, h2, h3]
    simp
  intro q hq b hb
  have hq' : q ∈ ⁅Q, zpowers c⁆ := by
    rw [hQc]
    exact hq
  exact (mem_fixingSubgroup_iff (Perm α)).mp (hle hq') b hb

theorem orb_invariant {Q : Subgroup (Perm α)} {r : Perm α} (hr : r ∈ Q) {a y : α}
    (hy : y ∈ Orb Q a) : r y ∈ Orb Q a := by
  obtain ⟨u, hu, rfl⟩ := hy
  exact ⟨r * u, Q.mul_mem hr hu, rfl⟩

theorem pair_fix [Finite α] {S : Set α} (hS : S.ncard ≤ 2) {r : Perm α} (hr : ∀ y ∈ S, r y ∈ S) {x : α}
    (hx : x ∈ S) (hrx : r x = x) : ∀ y ∈ S, r y = y := by
  intro y hy
  by_contra hne
  have hyx : y ≠ x := fun h => hne (by rw [h, hrx])
  have hryx : r y ≠ x := fun h => hyx (r.injective (h.trans hrx.symm))
  have hsub : ({x, y, r y} : Set α) ⊆ S := by
    intro z hz
    rcases hz with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hr _ hy
  have h3 : ({x, y, r y} : Set α).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨x, y, r y, hyx.symm, hryx.symm, fun h => hne h.symm, rfl⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite S)
  omega

variable {c : Perm α} {Q : Subgroup (Perm α)}

theorem moved_of_orbit (hcQ : c ∈ normalizer (Q : Set (Perm α))) {a : α} (hca : c a ∉ Orb Q a)
    {b : α} (hb : b ∈ Orb Q a) : c b ≠ b := by
  intro h
  apply hca
  have h1 := image_Orb_eq_self hcQ hb (by rw [h]; exact hb)
  rw [← h1]
  exact Set.mem_image_of_mem c (mem_Orb_self Q a)

theorem pow_mem_orb (hc : orderOf c = 5) (hcQ : c ∈ normalizer (Q : Set (Perm α))) {a : α} {m : ℕ}
    (hm : ¬ 5 ∣ m) (h : (c ^ m) a ∈ Orb Q a) : c a ∈ Orb Q a := by
  have hcm : c ^ m ∈ normalizer (Q : Set (Perm α)) := pow_mem hcQ m
  have himg := image_Orb_eq_self hcm (mem_Orb_self Q a) h
  have hstep : ∀ y ∈ Orb Q a, (c ^ m) y ∈ Orb Q a := fun y hy => by
    rw [← himg]
    exact Set.mem_image_of_mem _ hy
  have hiter : ∀ t : ℕ, ((c ^ m) ^ t) a ∈ Orb Q a := by
    intro t
    induction t with
    | zero => simpa using mem_Orb_self Q a
    | succ t ih => rw [pow_succ', Perm.mul_apply]; exact hstep _ ih
  have hcop : Nat.Coprime m 5 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hm).symm
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num)
  have hck : (c ^ m) ^ k = c := by
    rw [← pow_mul, ← pow_mod_orderOf, hc, hk, pow_one]
  have := hiter k
  rwa [hck] at this

theorem ncard_orb_pow_eq (hcQ : c ∈ normalizer (Q : Set (Perm α))) (a : α) (i : ℕ) :
    (Orb Q ((c ^ i) a)).ncard = (Orb Q a).ncard := by
  rw [← image_Orb (pow_mem hcQ i) a, Set.ncard_image_of_injective _ (c ^ i).injective]

theorem orb_pow_ne (hc : orderOf c = 5) (hcQ : c ∈ normalizer (Q : Set (Perm α))) {a : α}
    (hca : c a ∉ Orb Q a) {i j : ℕ} (hij : i < j) (hj : j < 5) :
    Orb Q ((c ^ i) a) ≠ Orb Q ((c ^ j) a) := by
  intro h
  have hci : c ^ i ∈ normalizer (Q : Set (Perm α)) := pow_mem hcQ i
  have h1 : (c ^ j) a ∈ Orb Q ((c ^ i) a) := by
    rw [h]
    exact mem_Orb_self Q _
  rw [← image_Orb hci a] at h1
  obtain ⟨y, hy, hyj⟩ := h1
  have hy' : y = (c ^ (j - i)) a := by
    apply (c ^ i).injective
    rw [hyj, ← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hij.le]
  apply hca
  refine pow_mem_orb hc hcQ (m := j - i) (by omega) ?_
  rw [← hy']
  exact hy

theorem moved_pow (hcQ : c ∈ normalizer (Q : Set (Perm α))) {a : α} (hca : c a ∉ Orb Q a)
    (i : ℕ) {y : α} (hy : y ∈ Orb Q ((c ^ i) a)) : c y ≠ y := by
  rw [← image_Orb (pow_mem hcQ i) a] at hy
  obtain ⟨b, hb, rfl⟩ := hy
  intro h
  have hcb : c b = b := by
    apply (c ^ i).injective
    rw [← Perm.mul_apply, ← (Commute.self_pow c i).eq, Perm.mul_apply, h]
  exact moved_of_orbit hcQ hca hb hcb

end Basic

section Finite

variable {α : Type*} [Fintype α] [DecidableEq α] {c : Perm α} {Q : Subgroup (Perm α)}

theorem card_le_256 (hα : Fintype.card α ≤ 11) (hQ : IsPGroup 2 Q) : Nat.card Q ≤ 256 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hQ
  have hdvd : Nat.card Q ∣ (Fintype.card α).factorial := by
    have := Subgroup.card_subgroup_dvd_card Q
    rwa [Nat.card_eq_fintype_card (α := Perm α), Fintype.card_perm] at this
  have h11 : (Fintype.card α).factorial ∣ (11 : ℕ).factorial := Nat.factorial_dvd_factorial hα
  by_contra hlt
  push Not at hlt
  rw [hk] at hlt hdvd
  have h9 : 9 ≤ k := by
    by_contra hk9
    push Not at hk9
    have : 2 ^ k ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h2 : 2 ^ 9 ∣ (11 : ℕ).factorial := (pow_dvd_pow 2 h9).trans (hdvd.trans h11)
  norm_num [Nat.factorial] at h2

theorem five_le_ncard_orb (hc : orderOf c = 5) {O : Set α} (hcO : ∀ y, c y ∈ O ↔ y ∈ O) {b : α}
    (hb : b ∈ O) (hcb : c b ≠ b) : 5 ≤ O.ncard := by
  have hcT : c ∈ setStab O := hcO
  have hcyc : (c.cycleOf b).IsCycle := isCycle_cycleOf c hcb
  have hdvd : (c.cycleOf b).support.card ∣ 5 := by
    rw [← hcyc.orderOf, ← hc]
    exact orderOf_cycleOf_dvd_orderOf c b
  have h5 : (c.cycleOf b).support.card = 5 := by
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
    · exact absurd h (card_support_ne_one _)
    · exact h
  have hsub : ((c.cycleOf b).support : Set α) ⊆ O := by
    intro y hy
    rw [Finset.mem_coe, mem_support_cycleOf_iff] at hy
    obtain ⟨i, hi⟩ := hy.1
    rw [← hi]
    exact ((zpow_mem hcT i) b).mpr hb
  calc 5 = ((c.cycleOf b).support : Set α).ncard := by rw [Set.ncard_coe_finset, h5]
    _ ≤ O.ncard := Set.ncard_le_ncard hsub (Set.toFinite O)

theorem Q_le_alt (Q : Subgroup (Perm α)) (c : Perm α) (hQc : ⁅Q, zpowers c⁆ = Q) :
    Q ≤ alternatingGroup α := by
  rw [← hQc]
  refine Subgroup.commutator_le.mpr fun q _ d _ => ?_
  rw [mem_alternatingGroup, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

theorem no_moved_invariant_orbit (hα : Fintype.card α ≤ 11) (hc : orderOf c = 5)
    (hQ : IsPGroup 2 Q) (hcQ : c ∈ normalizer (Q : Set (Perm α))) {a b : α}
    (hcO : ∀ y, c y ∈ Orb Q a ↔ y ∈ Orb Q a) (hb : b ∈ Orb Q a) (hcb : c b ≠ b) : False := by
  classical
  have hcT : c ∈ setStab (Orb Q a) := hcO
  have hQT : Q ≤ setStab (Orb Q a) := by
    intro q hq y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨q⁻¹ * x, Q.mul_mem (Q.inv_mem hq) hx, by rw [Perm.mul_apply, hxy]; simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨q * x, Q.mul_mem hq hx, rfl⟩
  have hzT : zpowers c ≤ setStab (Orb Q a) := (zpowers_le).mpr hcT
  have hGT : Q ⊔ zpowers c ≤ setStab (Orb Q a) := sup_le hQT hzT
  have h5 := five_le_ncard_orb hc hcO hb hcb
  obtain ⟨k, hk⟩ := ncard_Orb_pow (p := 2) hQ a
  have h11 : (Orb Q a).ncard ≤ 11 := by
    calc (Orb Q a).ncard ≤ (Set.univ : Set α).ncard := Set.ncard_le_ncard (Set.subset_univ _)
      _ = Fintype.card α := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]
      _ ≤ 11 := hα
  have h8 : (Orb Q a).ncard = 8 := by
    rw [hk] at h5 h11 ⊢
    have hk3 : k < 4 := by
      by_contra hk4
      push Not at hk4
      have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
      omega
    interval_cases k <;> omega
  set O : Set α := Orb Q a with hO
  let ρ : ↥(Q ⊔ zpowers c) →* Perm O := (restr O).comp (Subgroup.inclusion hGT)
  let A : Subgroup (Perm O) := ρ.range
  have hcG : c ∈ Q ⊔ zpowers c := Subgroup.mem_sup_right (mem_zpowers c)
  let γ : Perm O := ρ ⟨c, hcG⟩
  have hγA : γ ∈ A := ⟨_, rfl⟩
  have hγapply : ∀ y : O, ((γ y : O) : α) = c y := fun y => rfl
  have hNO : Nat.card O = 8 := by rw [Nat.card_coe_set_eq, h8]
  have hFO : Fintype.card O = 8 := by rw [← Nat.card_eq_fintype_card, hNO]
  have hγne : γ ≠ 1 := by
    intro h1
    have := hγapply ⟨b, hb⟩
    rw [h1] at this
    exact hcb this.symm
  have hγord : orderOf γ = 5 := by
    have hd : orderOf γ ∣ 5 := by
      rw [← hc]
      refine (orderOf_map_dvd ρ ⟨c, hcG⟩).trans ?_
      rw [Subgroup.orderOf_mk]
    rcases (Nat.dvd_prime Nat.prime_five).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hγne
    · exact h
  have hγcyc : γ.IsCycle := by
    apply isCycle_of_prime_order'
    · rw [hγord]
      exact Nat.prime_five
    · rw [hFO, hγord]
      norm_num
  have hγsupp : γ.support.card = 5 := by rw [← hγcyc.orderOf, hγord]
  have : MulAction.IsPretransitive A O := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨u, hu, hux⟩ := x.2
    obtain ⟨v, hv, hvy⟩ := y.2
    have huG : v * u⁻¹ ∈ Q ⊔ zpowers c :=
      Subgroup.mem_sup_left (Q.mul_mem hv (Q.inv_mem hu))
    refine ⟨⟨ρ ⟨v * u⁻¹, huG⟩, ⟨_, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    show (v * u⁻¹) (x : α) = (y : α)
    rw [← hux, ← hvy]
    simp
  have hprim : MulAction.IsPreprimitive A O :=
    CFSG.FiveTransitive.LargePrimeCyclePrimitive.isPreprimitive A hγA hγcyc
      (by rw [hγsupp]; exact Nat.prime_five) (by rw [hγsupp, hNO]; norm_num)
  have halt : alternatingGroup O ≤ A :=
    CFSG.FiveTransitive.OddOrder.Isaacs.Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
      hprim Nat.prime_five (by rw [hNO]) hγcyc hγsupp hγA
  have : Nontrivial O := Finite.one_lt_card_iff_nontrivial.mp (by rw [hNO]; norm_num)
  have hAlt : Nat.card (alternatingGroup O) = 20160 := by
    rw [nat_card_alternatingGroup, hNO]
    norm_num [Nat.factorial]
  have hAltle : Nat.card (alternatingGroup O) ≤ Nat.card A := Subgroup.card_le_of_le halt
  have hAG : Nat.card A ≤ Nat.card ↥(Q ⊔ zpowers c) :=
    Nat.card_le_card_of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hle : zpowers c ≤ normalizer (Q : Set (Perm α)) := (zpowers_le).mpr hcQ
  have hmul := coe_mul_of_right_le_normalizer_left Q (zpowers c) hle
  have hGQ : Nat.card ↥(Q ⊔ zpowers c) ≤ Nat.card Q * 5 := by
    have hz : Nat.card (zpowers c) = 5 := by rw [Nat.card_zpowers, hc]
    rw [← hz, ← Nat.card_prod]
    refine Nat.card_le_card_of_surjective
      (fun p : Q × zpowers c => (⟨(p.1 : Perm α) * p.2, ?_⟩ : ↥(Q ⊔ zpowers c))) ?_
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)
    · rintro ⟨g, hg⟩
      have hg' : g ∈ (↑(Q ⊔ zpowers c) : Set (Perm α)) := hg
      rw [hmul] at hg'
      obtain ⟨q, hq, z, hz, rfl⟩ := hg'
      exact ⟨(⟨q, hq⟩, ⟨z, hz⟩), rfl⟩
  have hQ256 := card_le_256 hα hQ
  omega

theorem card_support_le_ten (hα : Fintype.card α ≤ 11) (hc : orderOf c = 5) :
    c.support.card ≤ 10 := by
  have hσ : c ^ 5 ^ 1 = 1 := by
    rw [pow_one, ← hc]
    exact pow_orderOf_eq_one c
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hmod := Equiv.Perm.card_compl_support_modEq hσ
  have hsum : c.supportᶜ.card + c.support.card = Fintype.card α := by
    rw [Finset.card_compl_add_card]
  unfold Nat.ModEq at hmod
  omega

theorem type_one_structure (hα : Fintype.card α ≤ 11) (hc : orderOf c = 5)
    (hcQ : c ∈ normalizer (Q : Set (Perm α))) {a : α} (hca : c a ∉ Orb Q a)
    (hs2 : 2 ≤ (Orb Q a).ncard) :
    (Orb Q a).ncard = 2 ∧ ∀ z, c z ≠ z → ∃ i < 5, z ∈ Orb Q ((c ^ i) a) := by
  classical
  set s := (Orb Q a).ncard with hs
  let F : ℕ → Finset α := fun i => (Set.toFinite (Orb Q ((c ^ i) a))).toFinset
  have hF : ∀ i z, z ∈ F i ↔ z ∈ Orb Q ((c ^ i) a) := fun i z => Set.Finite.mem_toFinset _
  have hFcard : ∀ i, (F i).card = s := fun i => by
    rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _), ncard_orb_pow_eq hcQ a i]
  let U := (Finset.range 5).biUnion F
  have hdisj : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5, i ≠ j → Disjoint (F i) (F j) := by
    intro i hi j hj hij
    rw [Finset.mem_range] at hi hj
    rw [Finset.disjoint_left]
    intro z hzi hzj
    rw [hF] at hzi hzj
    have heq : Orb Q ((c ^ i) a) = Orb Q ((c ^ j) a) := Orb_eq_of_mem_inter hzi hzj
    rcases lt_or_gt_of_ne hij with h | h
    · exact orb_pow_ne hc hcQ hca h hj heq
    · exact orb_pow_ne hc hcQ hca h hi heq.symm
  have hUcard : U.card = 5 * s := by
    rw [Finset.card_biUnion hdisj]
    simp [hFcard]
  have hUsub : U ⊆ c.support := by
    intro z hz
    simp only [U, Finset.mem_biUnion, Finset.mem_range, hF] at hz
    obtain ⟨i, _, hzi⟩ := hz
    exact Equiv.Perm.mem_support.mpr (moved_pow hcQ hca i hzi)
  have hsupp := card_support_le_ten hα hc
  have hUle := Finset.card_le_card hUsub
  have hs_eq : s = 2 := by omega
  refine ⟨hs_eq, ?_⟩
  have hUeq : U = c.support := Finset.eq_of_subset_of_card_le hUsub (by omega)
  intro z hz
  have hzs : z ∈ c.support := Equiv.Perm.mem_support.mpr hz
  rw [← hUeq] at hzs
  simp only [U, Finset.mem_biUnion, Finset.mem_range, hF] at hzs
  obtain ⟨i, hi, hzi⟩ := hzs
  exact ⟨i, hi, hzi⟩

theorem card_le_sixteen_of_orbits {Q : Subgroup (Perm α)} (hQalt : Q ≤ alternatingGroup α)
    {x : ℕ → α} (hO : ∀ i < 5, (Orb Q (x i)).ncard = 2)
    (hcov : ∀ z, (∀ i < 5, z ∉ Orb Q (x i)) → ∀ q ∈ Q, q z = z) : Nat.card Q ≤ 16 := by
  classical
  let e : Q → ∀ i : Fin 4, Orb Q (x i) := fun q i => ⟨q.1 (x i), q.1, q.2, rfl⟩
  have hinj : Function.Injective e := by
    intro q q' hqq'
    set r : Perm α := (q : Perm α)⁻¹ * q' with hr
    have hrQ : r ∈ Q := Q.mul_mem (Q.inv_mem q.2) q'.2
    have hrx : ∀ i : Fin 4, r (x i) = x i := by
      intro i
      have := congrArg Subtype.val (congrFun hqq' i)
      simp only [e] at this
      show (q : Perm α)⁻¹ ((q' : Perm α) (x i)) = x i
      rw [← this]
      simp
    have hrfix : ∀ i : Fin 4, ∀ y ∈ Orb Q (x i), r y = y := fun i =>
      pair_fix (by rw [hO i (by omega)]) (fun y hy => orb_invariant hrQ hy) (mem_Orb_self Q _)
        (hrx i)
    have hr1 : r = 1 := by
      by_contra hne
      have hsupp : r.support ⊆ (Set.toFinite (Orb Q (x 4))).toFinset := by
        intro z hz
        have hz' : r z ≠ z := Equiv.Perm.mem_support.mp hz
        rw [Set.Finite.mem_toFinset]
        by_contra hz4
        have hnot : ¬ ∀ i < 5, z ∉ Orb Q (x i) := fun h => hz' (hcov z h r hrQ)
        push Not at hnot
        obtain ⟨i, hi, hzi⟩ := hnot
        have hi4 : i < 4 := by
          by_contra h4
          have : i = 4 := by omega
          exact hz4 (this ▸ hzi)
        exact hz' (hrfix ⟨i, hi4⟩ z hzi)
      have hc2 : r.support.card ≤ 2 := by
        calc r.support.card ≤ (Set.toFinite (Orb Q (x 4))).toFinset.card :=
              Finset.card_le_card hsupp
          _ = (Orb Q (x 4)).ncard := (Set.ncard_eq_toFinset_card _ (Set.toFinite _)).symm
          _ = 2 := hO 4 (by omega)
      have hc1 : r.support.card ≠ 0 := fun h => hne (Equiv.Perm.card_support_eq_zero.mp h)
      have hc1' := Equiv.Perm.card_support_ne_one r
      have hc2' : r.support.card = 2 := by omega
      have hsw := Equiv.Perm.card_support_eq_two.mp hc2'
      have hsign : Equiv.Perm.sign r = 1 := mem_alternatingGroup.mp (hQalt hrQ)
      rw [hsw.sign_eq] at hsign
      exact absurd hsign (by decide)
    have : (q : Perm α) = q' := by
      have h := hr1
      rw [hr, inv_mul_eq_one] at h
      exact h
    exact Subtype.ext this
  calc Nat.card Q ≤ Nat.card (∀ i : Fin 4, Orb Q (x i)) := Nat.card_le_card_of_injective e hinj
    _ = 16 := by
      rw [Nat.card_pi]
      have : ∀ i : Fin 4, Nat.card (Orb Q (x i)) = 2 := fun i => by
        rw [Nat.card_coe_set_eq]
        exact hO i (by omega)
      rw [Finset.prod_congr rfl (fun i _ => this i)]
      simp

theorem alt5_perm_bound_aux (hα : Fintype.card α ≤ 11) (hc : orderOf c = 5) (hQ : IsPGroup 2 Q)
    (hcQ : c ∈ normalizer (Q : Set (Perm α))) (hQc : ⁅Q, zpowers c⁆ = Q) : Nat.card Q ≤ 16 := by
  classical
  by_cases hfix : ∀ q ∈ Q, ∀ a, q a = a
  · have hQ1 : Q = ⊥ := by
      rw [eq_bot_iff]
      intro q hq
      rw [Subgroup.mem_bot]
      ext a
      exact hfix q hq a
    rw [hQ1, Subgroup.card_bot]
    norm_num
  · push Not at hfix
    obtain ⟨q₀, hq₀, a, hqa⟩ := hfix
    have hs2 : 2 ≤ (Orb Q a).ncard := by
      have hsub : ({a, q₀ a} : Set α) ⊆ Orb Q a := by
        intro z hz
        rcases hz with rfl | rfl
        · exact mem_Orb_self Q _
        · exact ⟨q₀, hq₀, rfl⟩
      have h2 : ({a, q₀ a} : Set α).ncard = 2 := Set.ncard_pair (fun h => hqa h.symm)
      calc 2 = ({a, q₀ a} : Set α).ncard := h2.symm
        _ ≤ (Orb Q a).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hca : c a ∉ Orb Q a := by
      intro hca
      have himg := image_Orb_eq_self hcQ (mem_Orb_self Q a) hca
      have hcO : ∀ y, c y ∈ Orb Q a ↔ y ∈ Orb Q a := by
        intro y
        constructor
        · intro hy
          rw [← himg] at hy
          obtain ⟨y', hy', hyy⟩ := hy
          rw [← c.injective hyy]
          exact hy'
        · intro hy
          rw [← himg]
          exact Set.mem_image_of_mem c hy
      by_cases hall : ∀ b ∈ Orb Q a, c b = b
      · exact hqa (orb_fixed hQc hall q₀ hq₀ a (mem_Orb_self Q a))
      · push Not at hall
        obtain ⟨b, hb, hcb⟩ := hall
        exact no_moved_invariant_orbit hα hc hQ hcQ hcO hb hcb
    obtain ⟨hs, hcov⟩ := type_one_structure hα hc hcQ hca hs2
    refine card_le_sixteen_of_orbits (Q_le_alt Q c hQc) (x := fun i => (c ^ i) a) ?_ ?_
    · intro i _
      rw [ncard_orb_pow_eq hcQ a i, hs]
    · intro z hz q hq
      have hfixz : ∀ y ∈ Orb Q z, c y = y := by
        intro y hy
        by_contra hcy
        obtain ⟨i, hi, hyi⟩ := hcov y hcy
        apply hz i hi
        have h1 : Orb Q y = Orb Q z := Orb_eq_of_mem hy
        have h2 : Orb Q y = Orb Q ((c ^ i) a) := Orb_eq_of_mem hyi
        rw [← h2, h1]
        exact mem_Orb_self Q z
      exact orb_fixed hQc hfixz q hq z (mem_Orb_self Q z)

end Finite

end AltFivePerm

theorem alt5_perm_bound {n : ℕ} (hn : n ≤ 11) (c : Equiv.Perm (Fin n)) (hc : orderOf c = 5)
    (Q : Subgroup (Equiv.Perm (Fin n))) (hQ : IsPGroup 2 Q)
    (hcQ : c ∈ Subgroup.normalizer (Q : Set (Equiv.Perm (Fin n))))
    (hQc : ⁅Q, Subgroup.zpowers c⁆ = Q) : Nat.card Q ≤ 16 :=
  AltFivePerm.alt5_perm_bound_aux (by simpa using hn) hc hQ hcQ hQc

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

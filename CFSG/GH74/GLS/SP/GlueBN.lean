module

public import CFSG.GH74.GLS.SP.GlueN
public import CFSG.GH74.GLS.SP.Pre
public import CFSG.GH74.BNPair.Bridge
public import CFSG.GH74.BNPair.Eq305

public section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair CFSG.GroupActions
open scoped Pointwise

variable {X : Type*} [Group X]

namespace RGD2

variable {n : ℕ} {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X} {root : ℤ → Subgroup X}
  (R : RGD2 n H r₁ r₂ U root)

include R in
theorem cartan_eq : cartan (H ⊔ U) R.N = H.subgroupOf R.N := by
  unfold cartan
  rw [R.B_inf_N]

include R in
theorem cartan_normal : (cartan (H ⊔ U) R.N).Normal := by
  rw [R.cartan_eq]
  exact R.normal_H_subgroupOf

@[expose] def nrep : Fin 2 → R.N := ![⟨r₁, R.r₁_mem_N⟩, ⟨r₂, R.r₂_mem_N⟩]

@[expose] def w₁ : WeylGroup (H ⊔ U) R.N := ((R.nrep 0 : R.N) : WeylGroup (H ⊔ U) R.N)

@[expose] def w₂ : WeylGroup (H ⊔ U) R.N := ((R.nrep 1 : R.N) : WeylGroup (H ⊔ U) R.N)

include R in
theorem weyl_ne : R.w₁ ≠ R.w₂ := by
  intro h
  have h1 : (r₁⁻¹ * r₂) ∈ H ⊔ U := mk_eq_mk_iff.1 h
  have hact := (R.actsPos_inv_of_sq R.sq₁ R.actsPos_r₁).mul R.actsPos_r₂
  have h3 := R.three_le
  have hn : 0 < n := by omega
  have h2 := R.pos_of_mem_B h1 hact (p := (n : ℤ) - 1)
    ⟨by rw [Rt_pred hn]; omega, by rw [Rt_pred hn]⟩
  have e : (n : ℤ) - ((n : ℤ) - 2 - ((n : ℤ) - 1)) = n + 1 := by ring
  rw [e, Rt_of_ge (by omega) (by omega)] at h2
  omega

include R in
theorem orderOf_w [(cartan (H ⊔ U) R.N).Normal] (i : Fin 2) :
    orderOf ((R.nrep i : R.N) : WeylGroup (H ⊔ U) R.N) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : ∀ (a : R.N), (a : X) * a ∈ H ⊔ U →
      ((a : R.N) : WeylGroup (H ⊔ U) R.N) ^ 2 = 1 := by
    intro a ha
    rw [sq, ← QuotientGroup.mk_mul, mk_eq_one_iff]
    exact ha
  fin_cases i
  · refine orderOf_eq_prime (hsq (R.nrep 0) ((le_sup_left : H ≤ H ⊔ U) R.sq₁)) ?_
    intro h
    exact R.r₁_not_mem_B (mk_eq_one_iff.1 h)
  · refine orderOf_eq_prime (hsq (R.nrep 1) ((le_sup_left : H ≤ H ⊔ U) R.sq₂)) ?_
    intro h
    exact R.r₂_not_mem_B (mk_eq_one_iff.1 h)

include R in
theorem closure_w [(cartan (H ⊔ U) R.N).Normal] : Subgroup.closure (Set.range fun i : Fin 2 =>
    ((R.nrep i : R.N) : WeylGroup (H ⊔ U) R.N)) = ⊤ := by
  set K := Subgroup.closure (Set.range fun i : Fin 2 =>
    ((R.nrep i : R.N) : WeylGroup (H ⊔ U) R.N)) with hK
  have hle : R.N ≤ (K.comap (QuotientGroup.mk' (cartan (H ⊔ U) R.N))).map R.N.subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro z (hz | hz)
    · have hzN : z ∈ R.N := R.H_le_N hz
      refine ⟨⟨z, hzN⟩, ?_, rfl⟩
      have h1 : (QuotientGroup.mk' (cartan (H ⊔ U) R.N)) ⟨z, hzN⟩ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, cartan, Subgroup.mem_subgroupOf]
        exact ⟨(le_sup_left : H ≤ H ⊔ U) hz, hzN⟩
      show (QuotientGroup.mk' (cartan (H ⊔ U) R.N)) ⟨z, hzN⟩ ∈ K
      rw [h1]
      exact K.one_mem
    · rcases hz with rfl | rfl
      · exact ⟨R.nrep 0, Subgroup.subset_closure ⟨0, rfl⟩, rfl⟩
      · exact ⟨R.nrep 1, Subgroup.subset_closure ⟨1, rfl⟩, rfl⟩
  rw [eq_top_iff]
  intro q _
  induction q using QuotientGroup.induction_on with
  | H z =>
    obtain ⟨w, hw, hwz⟩ := hle z.2
    have : w = z := Subtype.ext hwz
    subst this
    exact hw

theorem t3_set {B : Subgroup X} {r : X} (x : X)
    (hT3 : ∀ b ∈ B, (∃ b₁ ∈ B, ∃ b₂ ∈ B, r * b * x = b₁ * (r * x) * b₂) ∨
      (∃ b₁ ∈ B, ∃ b₂ ∈ B, r * b * x = b₁ * x * b₂)) :
    ({r} : Set X) * (B : Set X) * {x} ⊆
      (B : Set X) * {r * x} * (B : Set X) ∪ (B : Set X) * {x} * (B : Set X) := by
  intro y hy
  obtain ⟨a, ⟨c, hc, b, hb, hcb⟩, d, hd, had⟩ := hy
  rw [Set.mem_singleton_iff] at hc hd
  rw [hc] at hcb
  rw [hd] at had
  rw [← had, ← hcb]
  rcases hT3 b hb with ⟨b₁, hb₁, b₂, hb₂, he⟩ | ⟨b₁, hb₁, b₂, hb₂, he⟩
  · left
    exact Set.mem_mul.2 ⟨b₁ * (r * x), Set.mem_mul.2 ⟨b₁, hb₁, r * x, rfl, rfl⟩, b₂, hb₂,
      he.symm⟩
  · right
    exact Set.mem_mul.2 ⟨b₁ * x, Set.mem_mul.2 ⟨b₁, hb₁, x, rfl, rfl⟩, b₂, hb₂, he.symm⟩

include R in
theorem splitBN (hgen : (H ⊔ U) ⊔ R.N = ⊤) : SplitBN (H ⊔ U) R.N U R.nrep := by
  have hN := R.cartan_normal
  refine ⟨hN, hgen, ?_, R.orderOf_w, R.closure_w, ?_, ?_, ?_, ?_, R.nilpotent, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (R.weyl_ne hij).elim
    · exact (R.weyl_ne hij.symm).elim
    · rfl
  · intro i x hx
    fin_cases i
    · exact t3_set x (R.t3_r₁ x hx)
    · exact t3_set x (R.t3_r₂ x hx)
  · intro i
    fin_cases i
    · exact R.t4_r₁
    · exact R.t4_r₂
  · exact le_sup_right
  · rw [Subgroup.normal_subgroupOf_iff (le_sup_right : U ≤ H ⊔ U)]
    intro u b hu hb
    exact (Subgroup.mem_normalizer_iff.1 (R.B_le_normalizer_U hb) u).1 hu
  · intro x hx y hy
    rw [R.B_inf_N] at hx hy
    exact R.comm_H x hx y hy
  · rw [R.B_inf_N, sup_comm]
    exact R.coe_sup_UH
  · rw [R.B_inf_N]
    exact R.U_inf_H

open Classical in
include R in
theorem isTitsSystem [(cartan (H ⊔ U) R.N).Normal] (hgen : (H ⊔ U) ⊔ R.N = ⊤) :
    IsTitsSystem (H ⊔ U) R.N {R.w₁, R.w₂} := by
  obtain ⟨S, hS, hSrange⟩ := SplitBN.isTitsSystem (R.splitBN hgen)
  have hSeq : S = {R.w₁, R.w₂} := by
    apply Finset.coe_injective
    rw [hSrange]
    ext x
    simp only [Set.mem_range, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
  rwa [hSeq] at hS

include R in
theorem altWord_mem_N : ∀ (i : ℕ) (a b : X), a ∈ R.N → b ∈ R.N → altWord a b i ∈ R.N
  | 0, a, b, _, _ => by simp [altWord]
  | i + 1, a, b, ha, hb => by
    rw [altWord_succ]
    exact R.N.mul_mem (altWord_mem_N i b a hb ha) ha

include R in
theorem actsPos_altWord : ∀ i : ℕ,
    ActsPos n root (altWord r₁ r₂ i) (tauA n i) ∧ ActsPos n root (altWord r₂ r₁ i) (tauB n i)
  | 0 => by
    have h1 : ActsPos n root (1 : X) (fun q => q) := ActsPos.one
    refine ⟨?_, ?_⟩
    · have e : tauA n 0 = fun q => q := by funext q; simp [tauA]
      rw [e]
      simpa [altWord] using h1
    · have e : tauB n 0 = fun q => q := by funext q; simp [tauB]
      rw [e]
      simpa [altWord] using h1
  | i + 1 => by
    obtain ⟨hA, hB⟩ := actsPos_altWord i
    refine ⟨?_, ?_⟩
    · rw [altWord_succ]
      refine (hB.mul R.actsPos_r₁).congr (fun q => ?_)
      by_cases he : Even i <;> simp [tauA, tauB, he, Nat.even_add_one] <;> ring
    · rw [altWord_succ]
      refine (hA.mul R.actsPos_r₂).congr (fun q => ?_)
      by_cases he : Even i <;> simp [tauA, tauB, he, Nat.even_add_one] <;> ring

include R in
theorem isSaturated : IsSaturated (H ⊔ U) R.N := by
  have h3 := R.three_le
  unfold IsSaturated
  rw [R.B_inf_N]
  refine le_antisymm (le_iInf fun m => ?_) ?_
  · intro x hx
    show x ∈ conjBy (m : X) (H ⊔ U)
    rw [mem_conjBy_iff]
    exact (le_sup_left : H ≤ H ⊔ U) ((R.N_normalizes_H m.2 x hx).1)
  · intro x hx
    rw [Subgroup.mem_iInf] at hx
    have key : ∀ m : X, m ∈ R.N → m * x * m⁻¹ ∈ H ⊔ U := fun m hm =>
      mem_conjBy_iff.1 (hx ⟨m, hm⟩)
    have hxB : x ∈ H ⊔ U := by simpa using key 1 R.N.one_mem
    obtain ⟨u, hu, h, hh, rfl⟩ := (R.mem_sup_iff_UH).1 hxB
    have hm₀ : altWord r₁ r₂ n ∈ R.N := R.altWord_mem_N n r₁ r₂ R.r₁_mem_N R.r₂_mem_N
    have h1 := key _ hm₀
    have h2 : altWord r₁ r₂ n * h * (altWord r₁ r₂ n)⁻¹ ∈ H := (R.N_normalizes_H hm₀ h hh).1
    have hu1 : altWord r₁ r₂ n * u * (altWord r₁ r₂ n)⁻¹ ∈ H ⊔ U := by
      have := (H ⊔ U).mul_mem h1 ((H ⊔ U).inv_mem ((le_sup_left : H ≤ H ⊔ U) h2))
      have e : altWord r₁ r₂ n * (u * h) * (altWord r₁ r₂ n)⁻¹ *
          (altWord r₁ r₂ n * h * (altWord r₁ r₂ n)⁻¹)⁻¹ =
          altWord r₁ r₂ n * u * (altWord r₁ r₂ n)⁻¹ := by group
      rwa [e] at this
    have hu2 : altWord r₁ r₂ n * u * (altWord r₁ r₂ n)⁻¹ ∈ negGen n root := by
      have hu' : u ∈ chainProd root (intList 1 n) := by rw [← R.carrier_eq]; exact hu
      refine chainProd_conj_mem root (negGen n root) (altWord r₁ r₂ n) (intList 1 n)
        (fun k hk y hy => ?_) u hu'
      have hk' := mem_intList_iff.1 hk
      have hy' : y ∈ root (Rt n (k - 1)) := by rw [Rt_pos_idx hk'.1 hk'.2]; exact hy
      have h4 := ((R.actsPos_altWord n).1) (k - 1) y hy'
      have h5 := Rt_tauA_neg (n := n) (i := n) (q := k - 1) (by omega) (by omega) le_rfl
      refine mem_negGen_of_mem (k := -Rt n (tauA n n (k - 1))) (by omega) (by omega) ?_
      rw [neg_neg]
      exact h4
    have h6 := R.meet_one _ hu1 hu2
    have hu0 : u = 1 := by
      have := congrArg (fun z => (altWord r₁ r₂ n)⁻¹ * z * altWord r₁ r₂ n) h6
      simpa [mul_assoc] using this
    rw [hu0, one_mul]
    exact hh

include R in
theorem card_weyl : Nat.card (WeylGroup (H ⊔ U) R.N) = 2 * n := by
  have := R.normal_H_subgroupOf
  have := R.cartan_normal
  rw [← R.card_quotient]
  exact (Nat.card_congr (QuotientGroup.quotientMulEquivOfEq R.cartan_eq.symm).toEquiv).symm

include R in
theorem conjBy_H {h : X} (hh : h ∈ H) {j : ℤ} (hj : IsRoot n j) : conjBy h (root j) = root j := by
  ext x
  rw [mem_conjBy_iff]
  constructor
  · intro hx
    have := R.invariant j hj h⁻¹ (H.inv_mem hh) _ hx
    simpa [mul_assoc] using this
  · intro hx
    exact R.invariant j hj h hh x hx

include R in
theorem conjBy_r₁ {i j : ℤ} (hj : IsRoot n j) (h : conjBy r₁⁻¹ (root i) = root j) :
    conjBy r₁ (root i) = root j := by
  have e : conjBy r₁ (root i) = conjBy (r₁ * r₁) (conjBy r₁⁻¹ (root i)) := by
    rw [← conjBy_mul]
    congr 1
    group
  rw [e, h]
  exact R.conjBy_H R.sq₁ hj

include R in
theorem conjBy_r₂ {i j : ℤ} (hj : IsRoot n j) (h : conjBy r₂⁻¹ (root i) = root j) :
    conjBy r₂ (root i) = root j := by
  have e : conjBy r₂ (root i) = conjBy (r₂ * r₂) (conjBy r₂⁻¹ (root i)) := by
    rw [← conjBy_mul]
    congr 1
    group
  rw [e, h]
  exact R.conjBy_H R.sq₂ hj

include R in
theorem lift_mem_H {m : R.N} {i : Fin 2}
    (hm : (m : WeylGroup (H ⊔ U) R.N) = ((R.nrep i : R.N) : WeylGroup (H ⊔ U) R.N)) :
    ∃ h ∈ H, (m : X) = ((R.nrep i : R.N) : X) * h := by
  have hB := mk_eq_mk_iff.1 hm.symm
  have hN : ((R.nrep i : R.N) : X)⁻¹ * (m : X) ∈ R.N :=
    R.N.mul_mem (R.N.inv_mem (R.nrep i).2) m.2
  have hH : ((R.nrep i : R.N) : X)⁻¹ * (m : X) ∈ H := by
    have h1 : ((R.nrep i : R.N) : X)⁻¹ * (m : X) ∈ (H ⊔ U) ⊓ R.N := ⟨hB, hN⟩
    rwa [R.B_inf_N] at h1
  exact ⟨_, hH, by group⟩

theorem isRoot_neg {n : ℕ} {i : ℤ} (hi : IsRoot n i) : IsRoot n (-i) :=
  ⟨by have := hi.1; omega, by have := hi.2; omega⟩

include R in
theorem action₁_lift {m : R.N}
    (hm : (m : WeylGroup (H ⊔ U) R.N) = R.w₁) :
    conjBy (m : X) (root 1) = root (-1) ∧ conjBy (m : X) (root (-1)) = root 1 ∧
      ∀ i : ℤ, 2 ≤ i → i ≤ n → conjBy (m : X) (root i) = root ((n : ℤ) + 2 - i) ∧
        conjBy (m : X) (root (-i)) = root (-((n : ℤ) + 2 - i)) := by
  have h3 := R.three_le
  obtain ⟨h, hh, hmh⟩ := R.lift_mem_H (i := 0) hm
  obtain ⟨a1, a2, a3⟩ := R.act₁
  have key : ∀ {i j : ℤ}, IsRoot n j → conjBy r₁⁻¹ (root i) = root j →
      conjBy (m : X) (root i) = root j := by
    intro i j hj hij
    rw [hmh]
    show conjBy (r₁ * h) (root i) = root j
    rw [conjBy_mul, R.conjBy_r₁ hj hij, R.conjBy_H hh hj]
  have hr1 : IsRoot n 1 := isRoot_of_pos_le le_rfl (by omega)
  refine ⟨key (isRoot_neg hr1) a1, key hr1 a2, fun i h2 hn => ?_⟩
  have hi : IsRoot n i := isRoot_of_pos_le (by omega) hn
  have hi' : IsRoot n ((n : ℤ) + 2 - i) := isRoot_of_pos_le (by omega) (by omega)
  exact ⟨key hi' (a3 i h2 hn).1, key (isRoot_neg hi') (a3 i h2 hn).2⟩

include R in
theorem action₂_lift {m : R.N}
    (hm : (m : WeylGroup (H ⊔ U) R.N) = R.w₂) :
    conjBy (m : X) (root n) = root (-(n : ℤ)) ∧ conjBy (m : X) (root (-(n : ℤ))) = root n ∧
      ∀ i : ℤ, 1 ≤ i → i ≤ (n : ℤ) - 1 → conjBy (m : X) (root i) = root ((n : ℤ) - i) ∧
        conjBy (m : X) (root (-i)) = root (-((n : ℤ) - i)) := by
  have h3 := R.three_le
  obtain ⟨h, hh, hmh⟩ := R.lift_mem_H (i := 1) hm
  obtain ⟨b1, b2, b3⟩ := R.act₂
  have key : ∀ {i j : ℤ}, IsRoot n j → conjBy r₂⁻¹ (root i) = root j →
      conjBy (m : X) (root i) = root j := by
    intro i j hj hij
    rw [hmh]
    show conjBy (r₂ * h) (root i) = root j
    rw [conjBy_mul, R.conjBy_r₂ hj hij, R.conjBy_H hh hj]
  have hrn : IsRoot n n := isRoot_of_pos_le (by omega) le_rfl
  refine ⟨key (isRoot_neg hrn) b1, key hrn b2, fun i h1 hn => ?_⟩
  have hi : IsRoot n i := isRoot_of_pos_le h1 (by omega)
  have hi' : IsRoot n ((n : ℤ) - i) := isRoot_of_pos_le (by omega) (by omega)
  exact ⟨key hi' (b3 i h1 hn).1, key (isRoot_neg hi') (b3 i h1 hn).2⟩

@[expose] def toPre (hgen : (H ⊔ U) ⊔ R.N = ⊤) : PreRankTwoSystem X n :=
  haveI := R.cartan_normal
  { B := H ⊔ U
    N := R.N
    normal := R.cartan_normal
    w₁ := R.w₁
    w₂ := R.w₂
    U := U
    root := root
    isTits := R.isTitsSystem hgen
    w₁_ne_w₂ := R.weyl_ne
    isSplit := ⟨R.nilpotent, by rw [R.B_inf_N]; exact R.coe_sup_HU⟩
    isSaturated := R.isSaturated
    card_weyl := R.card_weyl
    three_le := R.three_le
    roots :=
      { ne_bot := R.ne_bot
        invariant := fun i hi h hh x hx => R.invariant i hi h (by rwa [R.B_inf_N] at hh) x hx
        carrier_eq := R.carrier_eq
        unique := R.unique
        reverse_eq := R.reverse_eq
        subgroup := R.subgroup
        action₁ := fun m hm => R.action₁_lift hm
        action₂ := fun m hm => R.action₂_lift hm
        meet_one := fun x hx hxc => R.meet_one x hx (by
          refine chainProd_subset root (negGen n root) ((intList 1 n).map Neg.neg) ?_ hxc
          intro k hk
          obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hk
          have hj' := mem_intList_iff.1 hj
          exact fun y hy => mem_negGen_of_mem hj'.1 hj'.2 hy) } }

end RGD2

end CFSG.GH74.GLS.SP

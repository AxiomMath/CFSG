module

public import CFSG.GH74.GLS.Stage2.Local.P34Perf
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Hat
public import CFSG.RankThree.Coprime.InvolutionFixedRankBound

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L182

open Subgroup CFSG CFSG.GroupTheory CFSG.OrderReductions.FrattiniAutomorphisms
  CFSG.BenderSuzuki.External
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (hat_exists_isFourSubgroup_of_involutions)
open scoped commutatorElement

section RankOne

variable {Q : Type} [Group Q] [Finite Q]

theorem two_le_pRank_of_involutions {a b : Q} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) : 2 ≤ CFSG.pRank 2 Q := by
  obtain ⟨V, hV⟩ := hat_exists_isFourSubgroup_of_involutions ha hb hab ha1 hb1 hne
  exact RankThree.Coprime.le_pRank_of_isElementaryAbelian one_lt_two hV.1 (k := 2)
    (by rw [hV.2]; norm_num)

theorem exists_elem_card_pRank (p : ℕ) [Fact p.Prime] (H : Type) [Group H] [Finite H] :
    ∃ A : Subgroup H, IsElementaryAbelian p A ∧ Nat.card A = p ^ CFSG.pRank p H := by
  have hbdd : BddAbove {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian p A ∧
      Nat.card A = p ^ r} := by
    refine ⟨Nat.card H, ?_⟩
    rintro r ⟨A, -, hA⟩
    have h1 : r < p ^ r := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
    have h2 : Nat.card A ≤ Nat.card H := Subgroup.card_le_card_group A
    omega
  have h0 : IsElementaryAbelian p (⊥ : Subgroup H) :=
    { is_comm := ⟨fun a b => Subsingleton.elim _ _⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
        Subsingleton.elim _ _ }
  have hne : {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian p A ∧ Nat.card A = p ^ r}.Nonempty :=
    ⟨0, ⊥, h0, by simp⟩
  exact Nat.sSup_mem hne hbdd

theorem pRank_le_of_le {G : Type} [Group G] [Finite G] {X Y : Subgroup G} (h : X ≤ Y) :
    CFSG.pRank 2 ↥X ≤ CFSG.pRank 2 ↥Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA, hc⟩ := exists_elem_card_pRank 2 ↥X
  let B : Subgroup ↥Y := A.map (Subgroup.inclusion h)
  have hBel : IsElementaryAbelian 2 ↥B :=
    { is_comm := ⟨fun x y => by
        obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 x.2
        obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.1 y.2
        apply Subtype.ext
        have hab : a * b = b * a := congrArg Subtype.val
          (hA.is_comm.comm (⟨a, ha⟩ : ↥A) ⟨b, hb⟩)
        show (x : ↥Y) * (y : ↥Y) = (y : ↥Y) * (x : ↥Y)
        rw [← hax, ← hby, ← map_mul, ← map_mul, hab]⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
        obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 x.2
        apply Subtype.ext
        have ha2 : a ^ 2 = 1 := by
          have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hA.exponent_dvd_p ⟨a, ha⟩
          exact congrArg Subtype.val this
        show (x : ↥Y) ^ 2 = 1
        rw [← hax, ← map_pow, ha2, map_one] }
  have hBcard : Nat.card ↥B = 2 ^ CFSG.pRank 2 ↥X := by
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective h)]
    exact hc
  exact RankThree.Coprime.le_pRank_of_isElementaryAbelian one_lt_two hBel hBcard

theorem exists_unique_order_two (hQ : IsPGroup 2 Q) (hr : CFSG.pRank 2 Q = 1) :
    ∃ U : Subgroup Q, Nat.card U = 2 ∧ ∀ V : Subgroup Q, Nat.card V = 2 → V = U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, -, hAc⟩ := exists_elem_card_pRank 2 Q
  rw [hr, pow_one] at hAc
  have hnt : Nontrivial Q := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : Nat.card A = 1 := Nat.card_unique
    omega
  have : Nontrivial (Subgroup.center Q) := hQ.center_nontrivial
  have hcz : IsPGroup 2 (Subgroup.center Q) := hQ.to_subgroup _
  obtain ⟨n, hn⟩ := hcz.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : Nat.card (Subgroup.center Q) = 1 := by simpa using hn
    have h2 : Subsingleton (Subgroup.center Q) := Nat.card_eq_one_iff_unique.1 this |>.1
    exact not_subsingleton _ h2
  have h2dvd : 2 ∣ Nat.card (Subgroup.center Q) := by rw [hn]; exact dvd_pow_self 2 hn0
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have hc2 : orderOf (c : Q) = 2 := by rw [Subgroup.orderOf_coe]; exact hc
  have hcsq : (c : Q) * c = 1 := by
    have := pow_orderOf_eq_one (c : Q); rwa [hc2, pow_two] at this
  have hc1 : (c : Q) ≠ 1 := by
    intro h; rw [h, orderOf_one] at hc2; exact absurd hc2 (by norm_num)
  have hcc : ∀ x : Q, (c : Q) * x = x * c := fun x =>
    (Subgroup.mem_center_iff.1 c.2 x).symm
  refine ⟨Subgroup.zpowers (c : Q), by rw [Nat.card_zpowers, hc2], ?_⟩
  intro V hV
  have hVnt : Nontrivial V := by
    have : 1 < Nat.card V := by omega
    exact Finite.one_lt_card_iff_nontrivial.1 this
  obtain ⟨⟨v, hvV⟩, hv1⟩ := exists_ne (1 : V)
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hord : orderOf v ∣ 2 := by
    have := orderOf_dvd_natCard (⟨v, hvV⟩ : V)
    rwa [Subgroup.orderOf_mk, hV] at this
  have hv2 : orderOf v = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hv1'
    · exact h
  have hvsq : v * v = 1 := by
    have := pow_orderOf_eq_one v; rwa [hv2, pow_two] at this
  have hVz : V = Subgroup.zpowers v := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact hvV
    · rw [Nat.card_zpowers, hv2, hV]
  by_cases hvc : v = (c : Q)
  · rw [hVz, hvc]
  · exfalso
    have h2 := two_le_pRank_of_involutions hvsq hcsq (hcc v).symm hv1' hc1 hvc
    omega

theorem mulAut_solvable_of_card_le_four (V : Type) [Group V] [Finite V]
    (h : Nat.card V ≤ 4) : Group.IsSolvable (MulAut V) := by
  have := CFSG.OrderReductions.PermutationReduction.permutation_solvable_of_card_le_four V h
  exact Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm V) (fun a b hab =>
    MulEquiv.ext fun x => congrArg (fun σ : Equiv.Perm V => σ x) hab)

def TwoGen (Q : Type) [Group Q] : Prop :=
  ∃ g h : Q, ∀ x : Q, ∃ k : ℕ, x = g ^ k ∨ x = h * g ^ k

omit [Finite Q] in
theorem twoGen_of_cyclic (hc : IsCyclic Q) [Finite Q] : TwoGen Q := by
  obtain ⟨g, hg⟩ := hc.exists_generator
  refine ⟨g, 1, fun x => ?_⟩
  have hx : x ∈ Submonoid.powers g := (mem_powers_iff_mem_zpowers).2 (hg x)
  obtain ⟨k, hk⟩ := Submonoid.mem_powers_iff _ _ |>.1 hx
  exact ⟨k, Or.inl hk.symm⟩

omit [Finite Q] in
theorem twoGen_of_quaternion {m : ℕ} [NeZero m] (e : Q ≃* QuaternionGroup m) : TwoGen Q := by
  refine ⟨e.symm (QuaternionGroup.a 1), e.symm (QuaternionGroup.xa 0), fun x => ?_⟩
  have key : ∀ i : ZMod (2 * m), QuaternionGroup.a i = (QuaternionGroup.a 1) ^ i.val := by
    intro i
    rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
  rcases hx : e x with i | i
  · refine ⟨i.val, Or.inl ?_⟩
    apply e.injective
    rw [map_pow, MulEquiv.apply_symm_apply, ← key, hx]
  · refine ⟨i.val, Or.inr ?_⟩
    apply e.injective
    rw [map_mul, map_pow, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, ← key, hx,
      QuaternionGroup.xa_mul_a, zero_add]

theorem card_frattini_quotient_le_four (hQ : IsPGroup 2 Q) (htg : TwoGen Q) :
    Nat.card (Q ⧸ frattini Q) ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hsq, -⟩ := frattini_elementary_quotient hQ
  obtain ⟨g, h, hgh⟩ := htg
  let π : Q →* Q ⧸ frattini Q := QuotientGroup.mk' (frattini Q)
  let f : Fin 2 × Fin 2 → Q ⧸ frattini Q := fun ij => π h ^ (ij.1 : ℕ) * π g ^ (ij.2 : ℕ)
  have hpow : ∀ k : ℕ, π g ^ k = π g ^ (k % 2) := by
    intro k
    conv_lhs => rw [← Nat.div_add_mod k 2, pow_add, pow_mul, hsq, one_pow, one_mul]
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk | hk⟩ := hgh y
    · refine ⟨(0, ⟨k % 2, Nat.mod_lt _ two_pos⟩), ?_⟩
      simp only [f, Fin.val_zero, pow_zero, one_mul]
      rw [hk, ← hpow]
      rfl
    · refine ⟨(1, ⟨k % 2, Nat.mod_lt _ two_pos⟩), ?_⟩
      simp only [f, Fin.val_one, pow_one]
      rw [hk, ← hpow]
      rfl
  calc Nat.card (Q ⧸ frattini Q) ≤ Nat.card (Fin 2 × Fin 2) :=
        Nat.card_le_card_of_surjective f hsurj
    _ = 4 := by simp

theorem act_trivial_of_pRank_one (hQ : IsPGroup 2 Q) (hr : CFSG.pRank 2 Q = 1)
    {A : Type*} [Group A] [Group.IsPerfect A] (act : A →* MulAut Q) : act = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := exists_unique_order_two hQ hr
  have hH := (huppert_III_8_2_pgroup_unique_order_prime_subgroup Nat.prime_two hQ hU).2 rfl
  have htg : TwoGen Q := by
    rcases hH with hc | ⟨n, hn, ⟨e⟩⟩
    · exact twoGen_of_cyclic hc
    · have : NeZero (2 ^ (n - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
      exact twoGen_of_quaternion e
  have hcard := card_frattini_quotient_le_four hQ htg
  have hsolv := mulAut_solvable_of_card_le_four (Q ⧸ frattini Q) hcard
  have h1 : (quotientAutomorphism (frattini Q)).comp act = 1 :=
    CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one _
  have hker : ∀ a : A, act a ∈ (quotientAutomorphism (frattini Q)).ker := by
    intro a
    rw [MonoidHom.mem_ker]
    simpa using congrArg (fun φ => φ a) h1
  have hK := (frattini_automorphism_kernel (p := 2) hQ).2
  have hnil : Group.IsNilpotent (quotientAutomorphism (frattini Q)).ker := hK.isNilpotent
  have h2 : act.codRestrict _ hker = 1 :=
    CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one _
  refine MonoidHom.ext fun a => ?_
  simpa using congrArg (fun φ => ((φ a : (quotientAutomorphism (frattini Q)).ker) : MulAut Q)) h2

end RankOne

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem centralizes_of_pRank_one {Q X : Subgroup G} (hQ : IsPGroup 2 ↥Q)
    (hr : CFSG.pRank 2 ↥Q = 1) (hX : ⁅X, X⁆ = X) (hXQ : ∀ x ∈ X, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) :
    ∀ x ∈ X, ∀ q ∈ Q, x * q * x⁻¹ = q := by
  have : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.2 hX
  have h1 := act_trivial_of_pRank_one hQ hr (CFSG.GH74.GLS.Stage2.Local.P34.actOn Q X hXQ)
  intro x hx q hq
  have := congrArg (fun φ : MulAut ↥Q => ((φ ⟨q, hq⟩ : ↥Q) : G))
    (congrArg (fun f : ↥X →* MulAut ↥Q => f ⟨x, hx⟩) h1)
  simpa [CFSG.GH74.GLS.Stage2.Local.P34.actOn] using this

theorem exists_orderOf_two_of_perfect {A : Type} [Group A] [Finite A] [Group.IsPerfect A]
    [Nontrivial A] : ∃ a : A, orderOf a = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card A := by
    by_contra hnd
    have hodd : Odd (Nat.card A) := Nat.odd_iff.2 (by omega)
    exact Group.IsPerfect.not_isSolvable (G := A) (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  exact exists_prime_orderOf_dvd_card' 2 h2

end Ambient

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L182

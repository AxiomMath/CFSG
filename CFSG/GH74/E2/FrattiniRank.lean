module

public import CFSG.GH74.E2.Coprime
public import CFSG.GH74.E2.Basic
import CFSG.LocalAnalysis.PreuniquenessRankFour.GeneratorRank
public import CFSG.GH74.EvenRank

public section

namespace CFSG.GH74.E2

open Subgroup

theorem isPGroup_sup_of_commute {G : Type*} [Group G] [Finite G] (Q T : Subgroup G)
    (hQ : IsPGroup 2 Q) (hT : IsPGroup 2 T) (hcomm : ∀ q ∈ Q, ∀ t ∈ T, q * t = t * q) :
    IsPGroup 2 ↥(Q ⊔ T) := by
  have hconj : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ = q := fun t ht q hq => by
    rw [← hcomm q hq t ht, mul_assoc, mul_inv_cancel, mul_one]
  refine IsPGroup.to_sup_of_normal_left' hQ hT fun t ht => ?_
  rw [mem_normalizer_iff]
  intro q
  refine ⟨fun hq => (hconj t ht q hq).symm ▸ hq, fun h => ?_⟩
  have h2 : q = t * q * t⁻¹ := by
    calc q = t⁻¹ * (t * q * t⁻¹) * t⁻¹⁻¹ := by group
      _ = t * q * t⁻¹ := hconj t⁻¹ (T.inv_mem ht) _ h
  rw [h2]
  exact h

open CFSG.PreuniquenessRankFour.Helpers in
theorem two_pow_rank_eq_card_of_exponent_two {Y : Type*} [Group Y] [Finite Y] [IsMulCommutative Y]
    (hY : ∀ y : Y, y ^ 2 = 1) : 2 ^ Group.rank Y = Nat.card Y := by
  let : CommGroup Y := IsMulCommutative.instCommGroup
  let : Module (ZMod 2) (Additive Y) :=
    AddCommGroup.zmodModule (n := 2) (G := Additive Y) fun y => by
      change Additive.ofMul (y.toMul ^ 2) = 0
      rw [hY]
      rfl
  rw [binary_module_group_rank_eq_finrank (source := Y)]
  exact FiniteField.pow_finrank_eq_natCard 2 (Additive Y)

open CFSG.PreuniquenessRankFour.Helpers in
theorem card_frattini_quotient_eq_two_pow_rank {X : Type*} [Group X] [Finite X]
    (hX : IsPGroup 2 X) : Nat.card (X ⧸ frattini X) = 2 ^ Group.rank X := by
  let : IsMulCommutative (X ⧸ frattini X) := pGroup_frattini_quotient_isMulCommutative 2 hX
  let : CommGroup (X ⧸ frattini X) := IsMulCommutative.instCommGroup
  let := pGroup_binary_frattini_quotient_module hX
  have h2 := twoGroup_frattini_finrank_eq_group_rank hX
  rw [← h2]
  exact (FiniteField.pow_finrank_eq_natCard 2 (Additive (X ⧸ frattini X))).symm

open CFSG.PreuniquenessRankFour.Helpers in
theorem rank_add_le_rank_prod {Q T : Type*} [Group Q] [Finite Q] [Group T] [Finite T]
    (hQ : IsPGroup 2 Q) (hT : IsPGroup 2 T) :
    Group.rank Q + Group.rank T ≤ Group.rank (Q × T) := by
  let : IsMulCommutative (Q ⧸ frattini Q) := pGroup_frattini_quotient_isMulCommutative 2 hQ
  let : IsMulCommutative (T ⧸ frattini T) := pGroup_frattini_quotient_isMulCommutative 2 hT
  let : CommGroup (Q ⧸ frattini Q) := IsMulCommutative.instCommGroup
  let : CommGroup (T ⧸ frattini T) := IsMulCommutative.instCommGroup
  let : IsMulCommutative ((Q ⧸ frattini Q) × (T ⧸ frattini T)) :=
    IsMulCommutative.of_comm fun a b => Prod.ext (mul_comm a.1 b.1) (mul_comm a.2 b.2)
  let f : Q × T →* (Q ⧸ frattini Q) × (T ⧸ frattini T) :=
    (QuotientGroup.mk' (frattini Q)).prodMap (QuotientGroup.mk' (frattini T))
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).prodMap (QuotientGroup.mk'_surjective _)
  have hY : ∀ y : (Q ⧸ frattini Q) × (T ⧸ frattini T), y ^ 2 = 1 := fun y =>
    Prod.ext (pGroup_frattini_quotient_pow_eq_one 2 hQ y.1)
      (pGroup_frattini_quotient_pow_eq_one 2 hT y.2)
  have h1 := two_pow_rank_eq_card_of_exponent_two hY
  rw [Nat.card_prod, card_frattini_quotient_eq_two_pow_rank hQ,
    card_frattini_quotient_eq_two_pow_rank hT, ← pow_add] at h1
  have h2 := Nat.pow_right_injective le_rfl h1
  rw [← h2]
  exact Group.rank_le_of_surjective f hf

open CFSG.PreuniquenessRankFour.Helpers in
theorem rank_prod_le_rank_sup_add_rank_inf {G : Type*} [Group G] [Finite G] (Q T : Subgroup G)
    (hcomm : ∀ q ∈ Q, ∀ t ∈ T, q * t = t * q) :
    Group.rank (Q × T) ≤ Group.rank ↥(Q ⊔ T) + Group.rank ↥(Q ⊓ T) := by
  let π : Q × T →* G :=
    MonoidHom.noncommCoprod Q.subtype T.subtype fun q t => hcomm q q.2 t t.2
  have hπ : ∀ q : Q, ∀ t : T, π (q, t) = (q : G) * t := fun q t => rfl
  have hrange : π.range = Q ⊔ T := by
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · rintro _ ⟨⟨q, t⟩, rfl⟩
      rw [hπ]
      exact Subgroup.mul_mem _ (mem_sup_left q.2) (mem_sup_right t.2)
    · intro q hq
      exact ⟨(⟨q, hq⟩, 1), by rw [hπ]; simp⟩
    · intro t ht
      exact ⟨(1, ⟨t, ht⟩), by rw [hπ]; simp⟩
  have h1 := subgroup_rank_le_rank_add_quotient_rank π.ker
  have h2 : Group.rank ((Q × T) ⧸ π.ker) = Group.rank π.range :=
    Group.rank_congr (QuotientGroup.quotientKerEquivRange π)
  have h3 : Group.rank π.range = Group.rank ↥(Q ⊔ T) := Subgroup.rank_congr hrange
  have h4 : Group.rank π.ker ≤ Group.rank ↥(Q ⊓ T) := by
    let δ : ↥(Q ⊓ T) →* π.ker :=
      { toFun := fun x => ⟨(⟨x, x.2.1⟩, ⟨(x : G)⁻¹, T.inv_mem x.2.2⟩), by
          rw [MonoidHom.mem_ker, hπ]
          simp⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := fun x y => by
          apply Subtype.ext
          refine Prod.ext (Subtype.ext rfl) (Subtype.ext ?_)
          change ((x : G) * y)⁻¹ = (x : G)⁻¹ * (y : G)⁻¹
          rw [mul_inv_rev]
          exact (hcomm _ (Q.inv_mem x.2.1) _ (T.inv_mem y.2.2)).symm ▸ rfl }
    refine Group.rank_le_of_surjective δ ?_
    rintro ⟨⟨q, t⟩, hqt⟩
    rw [MonoidHom.mem_ker, hπ] at hqt
    have ht : (t : G) = (q : G)⁻¹ := eq_inv_of_mul_eq_one_right hqt
    have hqT : (q : G) ∈ T := by
      have := T.inv_mem t.2
      rwa [ht, inv_inv] at this
    refine ⟨⟨q, q.2, hqT⟩, Subtype.ext (Prod.ext rfl (Subtype.ext ht.symm))⟩
  omega

theorem rank_sup_add_inf_ge {G : Type*} [Group G] [Finite G] (Q T : Subgroup G)
    (hQ : IsPGroup 2 Q) (hT : IsPGroup 2 T) (hcomm : ∀ q ∈ Q, ∀ t ∈ T, q * t = t * q) :
    Group.rank Q + Group.rank T ≤ Group.rank ↥(Q ⊔ T) + Group.rank ↥(Q ⊓ T) :=
  (rank_add_le_rank_prod hQ hT).trans (rank_prod_le_rank_sup_add_rank_inf Q T hcomm)

theorem gen4_rank_add_le {G : Type*} [Group G] [Finite G] (hG : Gen4 G) (Q T : Subgroup G)
    (hQ : IsPGroup 2 Q) (hT : IsPGroup 2 T) (hcomm : ∀ q ∈ Q, ∀ t ∈ T, q * t = t * q) :
    Group.rank Q + Group.rank T ≤ 4 + Group.rank ↥(Q ⊓ T) := by
  have h1 := rank_sup_add_inf_ge Q T hQ hT hcomm
  have h2 := Gen4.rank_le_four hG (isPGroup_sup_of_commute Q T hQ hT hcomm)
  omega

theorem eq_of_four_relations {G : Type*} [Group G] (V : Subgroup G)
    (hVc : ∀ u ∈ V, ∀ w ∈ V, u * w = w * u) (hV2 : ∀ u ∈ V, u * u = 1)
    {v α α2 γ γ2 δ β : G} (hv : v ∈ V) (hα : α ∈ V) (hα2 : α2 ∈ V) (hγ : γ ∈ V) (hγ2 : γ2 ∈ V)
    (hδ : δ ∈ V) (hβ : β ∈ V)
    (E1 : v * α * α2 = 1) (E2 : v * γ * γ2 = 1) (E3 : α2 * δ * γ2 = 1) (E4 : β * γ * δ = 1) :
    α = β := by
  have : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (hVc a a.2 b b.2)⟩⟩
  let : CommGroup V := IsMulCommutative.instCommGroup
  have hexp : ∀ w : V, w * w = 1 := fun w => Subtype.ext (hV2 w w.2)
  let v' : V := ⟨v, hv⟩
  let α' : V := ⟨α, hα⟩
  let α2' : V := ⟨α2, hα2⟩
  let γ' : V := ⟨γ, hγ⟩
  let γ2' : V := ⟨γ2, hγ2⟩
  let δ' : V := ⟨δ, hδ⟩
  let β' : V := ⟨β, hβ⟩
  have E1' : v' * α' * α2' = 1 := Subtype.ext E1
  have E2' : v' * γ' * γ2' = 1 := Subtype.ext E2
  have E3' : α2' * δ' * γ2' = 1 := Subtype.ext E3
  have E4' : β' * γ' * δ' = 1 := Subtype.ext E4
  have key : (v' * v') * (α' * β') * (α2' * α2') * (γ' * γ') * (γ2' * γ2') * (δ' * δ') = 1 := by
    calc _ = (v' * α' * α2') * (v' * γ' * γ2') * (α2' * δ' * γ2') * (β' * γ' * δ') := by ac_rfl
      _ = 1 := by rw [E1', E2', E3', E4']; simp
  rw [hexp v', hexp α2', hexp γ', hexp γ2', hexp δ', one_mul, mul_one, mul_one, mul_one,
    mul_one] at key
  have h : α' = β' := by
    calc α' = β'⁻¹ := eq_inv_of_mul_eq_one_left key
      _ = β' := inv_eq_of_mul_eq_one_right (hexp β')
  exact congrArg Subtype.val h

theorem exists_fourgroup_of_no_fixed {G : Type*} [Group G] (A V : Subgroup G)
    (hA : ElemAb 3 A) (hAcard : Nat.card A = 27) (hV : ElemAb 2 V) (hVle : Nat.card V ≤ 16)
    (hnorm : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ ∈ V)
    (hfix : ∀ v ∈ V, (∀ a ∈ A, a * v = v * a) → v = 1) (hV1 : V ≠ ⊥) :
    ∃ (t t' a : G) (B : Subgroup G), orderOf t = 2 ∧ orderOf t' = 2 ∧ t ≠ t' ∧ t * t' = t' * t ∧
      t ∈ V ∧ t' ∈ V ∧ a ∈ A ∧ orderOf a = 3 ∧ a * t * a⁻¹ = t' ∧ a * t' * a⁻¹ = t * t' ∧
      B ≤ A ∧ Nat.card B = 9 ∧ (∀ b ∈ B, b * t = t * b) ∧ (∀ b ∈ B, b * t' = t' * b) := by
  classical
  have _hVle : Nat.card V ≤ 16 := hVle
  have hAfin : Finite A := Nat.finite_of_card_ne_zero (by rw [hAcard]; norm_num)
  let : MulAction A G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp A.subtype)
  have hsmul : ∀ (a : A) (x : G), a • x = (a : G) * x * (a : G)⁻¹ := fun a x => rfl
  have hmemstab : ∀ (w : G) (a : A),
      a ∈ MulAction.stabilizer A w ↔ (a : G) * w = w * (a : G) := fun w a => by
    rw [MulAction.mem_stabilizer_iff, hsmul, mul_inv_eq_iff_eq_mul]
  have hVc := hV.1
  have hV2 : ∀ u ∈ V, u * u = 1 := fun u hu => by rw [← pow_two]; exact hV.2 u hu
  have hVinv : ∀ u ∈ V, u⁻¹ = u := fun u hu => inv_eq_of_mul_eq_one_right (hV2 u hu)
  have hAc := hA.1
  have hA3 : ∀ x ∈ A, x * x * x = 1 := fun x hx => by rw [← pow_three']; exact hA.2 x hx
  obtain ⟨v, hvV, hv1, hmax⟩ : ∃ v ∈ V, v ≠ 1 ∧ ∀ w ∈ V, w ≠ 1 →
      Nat.card (MulAction.stabilizer A w) ≤ Nat.card (MulAction.stabilizer A v) := by
    obtain ⟨w0, hw0⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV1
    let S : Set ℕ := {n | ∃ w ∈ V, w ≠ 1 ∧ Nat.card (MulAction.stabilizer A w) = n}
    have hne : S.Nonempty := ⟨_, (w0 : G), w0.2, fun h => hw0 (Subtype.ext h), rfl⟩
    have hbdd : BddAbove S := ⟨27, by
      rintro n ⟨w, -, -, rfl⟩
      rw [← hAcard]
      exact Subgroup.card_le_card_group _⟩
    obtain ⟨v, hvV, hv1, hv⟩ := Nat.sSup_mem hne hbdd
    exact ⟨v, hvV, hv1, fun w hw hw1 => (le_csSup hbdd ⟨w, hw, hw1, rfl⟩).trans_eq hv.symm⟩
  obtain ⟨T, hT⟩ : ∃ T : G → G, ∀ y, T y = y * v * y⁻¹ := ⟨_, fun _ => rfl⟩
  have hTV : ∀ x ∈ A, T x ∈ V := fun x hx => by rw [hT]; exact hnorm x hx v hvV
  have hTmul : ∀ x y : G, T (x * y) = x * T y * x⁻¹ := fun x y => by rw [hT, hT]; group
  have hTone : T 1 = v := by rw [hT]; group
  have hKT : ∀ x : A, x ∈ MulAction.stabilizer A v ↔ T x = v := fun x => by
    rw [MulAction.mem_stabilizer_iff, hsmul, hT]
  have hKfix : ∀ k : A, k ∈ MulAction.stabilizer A v → ∀ y ∈ A, (k : G) * T y * (k : G)⁻¹ = T y := by
    intro k hk y hy
    have hkv : (k : G) * v * (k : G)⁻¹ = v := by
      have h := (hKT k).mp hk
      rwa [hT] at h
    have hky : (k : G) * y = y * k := hAc k k.2 y hy
    calc (k : G) * T y * (k : G)⁻¹ = (k * y) * v * (k * y)⁻¹ := by rw [hT]; group
      _ = (y * k) * v * (y * k)⁻¹ := by rw [hky]
      _ = y * ((k : G) * v * (k : G)⁻¹) * y⁻¹ := by group
      _ = T y := by rw [hkv, hT]
  have hR : ∀ x : A, x ∉ MulAction.stabilizer A v → v * T x * T ((x : G) * x) = 1 := by
    intro x hx
    by_contra hs1
    have hxA : (x : G) ∈ A := x.2
    have hxxA : (x : G) * x ∈ A := A.mul_mem hxA hxA
    have hsV : v * T x * T ((x : G) * x) ∈ V :=
      V.mul_mem (V.mul_mem hvV (hTV x hxA)) (hTV _ hxxA)
    have hle : MulAction.stabilizer A v ≤
        MulAction.stabilizer A (v * T x * T ((x : G) * x)) := fun k hk => by
      rw [hmemstab]
      have h1 := hKfix k hk x hxA
      have h2 := hKfix k hk _ hxxA
      have hkv : (k : G) * v * (k : G)⁻¹ = v := by
        have h := (hKT k).mp hk
        rwa [hT] at h
      have h3 : (k : G) * (v * T x * T ((x : G) * x)) * (k : G)⁻¹ =
          v * T x * T ((x : G) * x) := by
        calc (k : G) * (v * T x * T ((x : G) * x)) * (k : G)⁻¹
            = ((k : G) * v * (k : G)⁻¹) * ((k : G) * T x * (k : G)⁻¹) *
              ((k : G) * T ((x : G) * x) * (k : G)⁻¹) := by group
          _ = v * T x * T ((x : G) * x) := by rw [hkv, h1, h2]
      rwa [mul_inv_eq_iff_eq_mul] at h3
    have hxmem : x ∈ MulAction.stabilizer A (v * T x * T ((x : G) * x)) := by
      rw [hmemstab]
      have h3 : (x : G) * (v * T x * T ((x : G) * x)) * (x : G)⁻¹ =
          T x * T ((x : G) * x) * v := by
        calc (x : G) * (v * T x * T ((x : G) * x)) * (x : G)⁻¹
            = ((x : G) * v * (x : G)⁻¹) * ((x : G) * T x * (x : G)⁻¹) *
              ((x : G) * T ((x : G) * x) * (x : G)⁻¹) := by group
          _ = T x * T ((x : G) * x) * T ((x : G) * ((x : G) * x)) := by
            rw [← hTmul, ← hTmul, ← hT]
          _ = T x * T ((x : G) * x) * v := by
            rw [← mul_assoc (x : G) (x : G) (x : G), hA3 x hxA, hTone]
      have h4 : T x * T ((x : G) * x) * v = v * (T x * T ((x : G) * x)) :=
        hVc _ (V.mul_mem (hTV x hxA) (hTV _ hxxA)) v hvV
      exact mul_inv_eq_iff_eq_mul.mp (h3.trans (h4.trans (mul_assoc _ _ _).symm))
    have hlt : MulAction.stabilizer A v <
        MulAction.stabilizer A (v * T x * T ((x : G) * x)) :=
      lt_of_le_of_ne hle (fun h => hx (by rw [h]; exact hxmem))
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2 := hmax _ hsV hs1
    omega
  have hpair : ∀ a b : A, a ∉ MulAction.stabilizer A v → b ∉ MulAction.stabilizer A v →
      a * b ∉ MulAction.stabilizer A v → T a = T b := by
    intro a b ha hb hab
    have haA : (a : G) ∈ A := a.2
    have hbA : (b : G) ∈ A := b.2
    have habA : (a : G) * b ∈ A := A.mul_mem haA hbA
    have haaA : (a : G) * a ∈ A := A.mul_mem haA haA
    have hcomm : (a : G) * b = b * a := hAc a haA b hbA
    have hee : ((a : G) * b) * ((a : G) * b) = (a : G) * a * ((b : G) * b) := by
      calc ((a : G) * b) * ((a : G) * b) = a * ((b : G) * a) * b := by group
        _ = a * ((a : G) * b) * b := by rw [hcomm]
        _ = (a : G) * a * ((b : G) * b) := by group
    have hee' : (b : G) * ((a : G) * a) = (a : G) * a * b := by
      calc (b : G) * ((a : G) * a) = ((b : G) * a) * a := by group
        _ = ((a : G) * b) * a := by rw [hcomm]
        _ = (a : G) * ((b : G) * a) := by group
        _ = (a : G) * ((a : G) * b) := by rw [hcomm]
        _ = (a : G) * a * b := by group
    have E1 : v * T a * T ((a : G) * a) = 1 := hR a ha
    have E2 : v * T ((a : G) * b) * T (((a : G) * b) * ((a : G) * b)) = 1 := hR (a * b) hab
    have E3 : T ((a : G) * a) * T ((a : G) * a * b) * T ((a : G) * a * ((b : G) * b)) = 1 := by
      rw [hTmul ((a : G) * a) b, hTmul ((a : G) * a) ((b : G) * b), hT ((a : G) * a)]
      calc ((a : G) * a * v * ((a : G) * a)⁻¹) * ((a : G) * a * T b * ((a : G) * a)⁻¹) *
          ((a : G) * a * T ((b : G) * b) * ((a : G) * a)⁻¹)
          = ((a : G) * a) * (v * T b * T ((b : G) * b)) * ((a : G) * a)⁻¹ := by group
        _ = 1 := by rw [hR b hb]; group
    have E4 : T b * T ((b : G) * a) * T ((b : G) * ((a : G) * a)) = 1 := by
      rw [hTmul (b : G) a, hTmul (b : G) ((a : G) * a), hT (b : G)]
      calc ((b : G) * v * (b : G)⁻¹) * ((b : G) * T a * (b : G)⁻¹) *
          ((b : G) * T ((a : G) * a) * (b : G)⁻¹)
          = (b : G) * (v * T a * T ((a : G) * a)) * (b : G)⁻¹ := by group
        _ = 1 := by rw [hR a ha]; group
    rw [← hcomm, hee'] at E4
    rw [← hee] at E3
    exact eq_of_four_relations V hVc hV2 hvV (hTV a haA) (hTV _ haaA) (hTV _ habA)
      (hTV _ (A.mul_mem habA habA)) (hTV _ (A.mul_mem haaA hbA)) (hTV b hbA) E1 E2 E3 E4
  obtain ⟨a, haK⟩ : ∃ a : A, a ∉ MulAction.stabilizer A v := by
    by_contra h
    push Not at h
    exact hv1 (hfix v hvV fun a ha => (hmemstab v ⟨a, ha⟩).mp (h ⟨a, ha⟩))
  have haA : (a : G) ∈ A := a.2
  have haaA : (a : G) * a ∈ A := A.mul_mem haA haA
  have ha3 : (a : G) * a * a = 1 := hA3 a haA
  have hTa_ne : T a ≠ v := fun h => haK ((hKT a).mpr h)
  have horb : ∀ b : A, T b = v ∨ T b = T a ∨ T b = T ((a : G) * a) := by
    intro b
    by_cases hb : b ∈ MulAction.stabilizer A v
    · exact Or.inl ((hKT b).mp hb)
    · by_cases hab : a * b ∈ MulAction.stabilizer A v
      · right
        right
        have h1 : T ((a : G) * b) = v := (hKT (a * b)).mp hab
        have h3 : (a : G)⁻¹ = a * a := by
          calc (a : G)⁻¹ = (a : G)⁻¹ * ((a : G) * a * a) := by rw [ha3, mul_one]
            _ = a * a := by group
        calc T b = (a : G)⁻¹ * T ((a : G) * b) * (a : G) := by rw [hTmul]; group
          _ = (a : G)⁻¹ * v * (a : G) := by rw [h1]
          _ = T ((a : G) * a) := by rw [hT, ← h3]; group
      · right
        left
        exact (hpair a b haK hb hab).symm
  have horbit_sub : MulAction.orbit A v ⊆ ({v, T a, T ((a : G) * a)} : Set G) := by
    rintro _ ⟨b, rfl⟩
    have hb : b • v = T b := (hsmul b v).trans (hT b).symm
    change b • v ∈ _
    rw [hb]
    rcases horb b with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hle3 : (MulAction.orbit A v).ncard ≤ 3 := by
    have h1 := Set.ncard_le_ncard horbit_sub (Set.toFinite _)
    refine h1.trans ?_
    refine (Set.ncard_insert_le _ _).trans ?_
    have h2 := Set.ncard_insert_le (T a) ({T ((a : G) * a)} : Set G)
    rw [Set.ncard_singleton] at h2
    omega
  have hge2 : 2 ≤ (MulAction.orbit A v).ncard := by
    have hfin : (MulAction.orbit A v).Finite := (Set.toFinite _).subset horbit_sub
    have := (Set.one_lt_ncard_iff hfin).mpr
      ⟨v, T a, MulAction.mem_orbit_self v, ⟨a, (hsmul a v).trans (hT a).symm⟩, hTa_ne.symm⟩
    omega
  have hcm := Subgroup.card_mul_index (MulAction.stabilizer A v)
  rw [MulAction.index_stabilizer, hAcard] at hcm
  have hKcard : Nat.card (MulAction.stabilizer A v) = 9 := by
    obtain h | h : (MulAction.orbit A v).ncard = 2 ∨ (MulAction.orbit A v).ncard = 3 := by omega
    · rw [h] at hcm
      omega
    · rw [h] at hcm
      omega
  have hTa1 : T a ≠ 1 := fun h => hv1 (conj_eq_one_iff.mp (by rw [← hT]; exact h))
  have haone : (a : G) ≠ 1 := fun h =>
    haK (by rw [show a = 1 from Subtype.ext h]; exact one_mem _)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmul : T ((a : G) * a) = v * T a := by
    have h := eq_inv_of_mul_eq_one_right (hR a haK)
    rwa [hVinv _ (V.mul_mem hvV (hTV a haA))] at h
  refine ⟨v, T a, a, (MulAction.stabilizer A v).map A.subtype, orderOf_eq_prime (hV.2 v hvV) hv1,
    orderOf_eq_prime (hV.2 _ (hTV a haA)) hTa1, hTa_ne.symm, hVc v hvV _ (hTV a haA), hvV,
    hTV a haA, haA, orderOf_eq_prime (hA.2 a haA) haone, (hT a).symm, ?_,
    Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [← hmul, hTmul]
  · rw [Subgroup.card_map_of_injective A.subtype_injective, hKcard]
  · intro b hb
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hb
    exact (hmemstab v k).mp hk
  · intro b hb
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hb
    exact mul_inv_eq_iff_eq_mul.mp (hKfix k hk a haA)

open CFSG.PreuniquenessRankFour.Helpers in
theorem no_fixed_vector_threeSquared {V B : Type*} [AddCommGroup V] [Finite V]
    [Module (ZMod 2) V] [Group B] [Finite B] (hcomm : ∀ a b : B, a * b = b * a)
    (hcard : Nat.card B = 3 ^ 2) (hpow : ∀ b : B, b ^ 3 = 1) (ρ : B →* (V ≃ₗ[ZMod 2] V))
    (hρ : Function.Injective ρ) (hdim : Module.finrank (ZMod 2) V ≤ 4) (v : V) (hv0 : v ≠ 0)
    (hv : ∀ b : B, ρ b v = v) : False := by
  classical
  let : CommGroup B := { ‹Group B› with mul_comm := hcomm }
  have : NeZero (Nat.card B : ZMod 2) := ⟨fun h => by
    have := (ZMod.natCast_eq_zero_iff (Nat.card B) 2).mp h
    rw [hcard] at this
    norm_num at this⟩
  let π : Representation (ZMod 2) B V := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ
  let C : Submodule (ZMod 2) V :=
    { carrier := {w | ∀ b : B, ρ b w = w}
      add_mem' := fun {a c} ha hc b => by rw [map_add, ha b, hc b]
      zero_mem' := fun b => map_zero _
      smul_mem' := fun r w hw b => by rw [map_smul, hw b] }
  have hC : ∀ w, w ∈ C ↔ ∀ b : B, ρ b w = w := fun w => Iff.rfl
  have hle : ∀ b : B, C ≤ C.comap (π b) := fun b w hw => by
    change π b w ∈ C
    have h1 : π b w = w := hw b
    rw [h1]
    exact hw
  let π' : Representation (ZMod 2) B (V ⧸ C) := π.quotient C hle
  have hπ' : ∀ (b : B) (w : V),
      π' b (Submodule.Quotient.mk w) = Submodule.Quotient.mk (ρ b w) := fun b w => rfl
  have h2 : ∀ c : V, c + c = 0 := fun c => by
    rw [← two_smul (ZMod 2) c]
    have : (2 : ZMod 2) = 0 := rfl
    rw [this, zero_smul]
  have hfaith : Function.Injective π' := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hb2 : ρ (b * b) = 1 := by
      ext w
      have h1 : ρ b w - w ∈ C := by
        have h3 := congrArg (fun f : Module.End (ZMod 2) (V ⧸ C) => f (Submodule.Quotient.mk w)) hb
        simp only [hπ', Module.End.one_apply] at h3
        exact (Submodule.Quotient.eq C).mp h3
      have h4 : ρ b (ρ b w - w) = ρ b w - w := h1 b
      rw [map_sub] at h4
      rw [map_mul]
      change ρ b (ρ b w) = w
      have h5 : ρ b (ρ b w) = ρ b w + (ρ b w - w) := by
        rw [← h4]; abel
      rw [h5]
      calc ρ b w + (ρ b w - w) = w + ((ρ b w - w) + (ρ b w - w)) := by abel
        _ = w := by rw [h2, add_zero]
    have hb2' : b * b = 1 := hρ (by rw [hb2, map_one])
    calc b = b ^ 3 * (b * b)⁻¹ := by group
      _ = 1 := by rw [hpow, hb2', inv_one, mul_one]
  have : Finite (V ⧸ C) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective C)
  have hCpos : 0 < Module.finrank (ZMod 2) C := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨⟨v, (hC v).mpr hv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
  have hquot := Submodule.finrank_quotient_add_finrank C
  have hbound := faithful_binary_elementary_representation_order_dimension_bound
    (acting := B) (space := V ⧸ C) 3 2 hcard π' hpow hfaith
  rw [orderOf_two_zmod_three] at hbound
  omega

open CFSG.PreuniquenessRankFour.Helpers in
theorem threeSquared_faithful {X B : Type*} [Group X] [Finite X] [Group B] [Finite B]
    (hX : IsPGroup 2 X) (hX4 : Group.rank X ≤ 4) (φ : B →* MulAut X)
    (hφ : Function.Injective φ) (hcomm : ∀ a b : B, a * b = b * a) (hpow : ∀ a : B, a ^ 3 = 1)
    (hcard : Nat.card B = 9) :
    Group.rank X = 4 ∧ ∀ x : X, (∀ b : B, (φ b x) * x⁻¹ ∈ frattini X) → x ∈ frattini X := by
  have hcard' : Nat.card B = 3 ^ 2 := hcard.trans (by norm_num)
  have h1 := ord_mul_card_le_rank_hom hX φ hφ Nat.prime_three (by norm_num) hcomm hpow hcard'
  rw [orderOf_two_zmod_three] at h1
  refine ⟨by omega, fun x hx => ?_⟩
  by_contra hxF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : MulDistribMulAction B X := MulDistribMulAction.compHom X φ
  have hinj : Function.Injective (MulDistribMulAction.toMulAut B X) := by
    intro a b hab
    apply hφ
    have h1 : ∀ c, MulDistribMulAction.toMulAut B X c = φ c := fun c => MulEquiv.ext fun x => rfl
    rw [← h1, ← h1]
    exact hab
  have hEp : IsPGroup 3 B := IsPGroup.of_card hcard'
  have hcop : ¬ 3 ∣ Nat.card (frattini X) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hX.to_subgroup (frattini X))
    rw [hk]
    intro hdvd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hdvd)
    omega
  let : IsMulCommutative (X ⧸ frattini X) := pGroup_frattini_quotient_isMulCommutative 2 hX
  let : CommGroup (X ⧸ frattini X) := IsMulCommutative.instCommGroup
  let := pGroup_binary_frattini_quotient_module hX
  let := characteristic_quotient_mulDistribMulAction (acting := B) (frattini X)
  have hfaithfulQ := faithful_coprime_pGroup_action_on_frattini_quotient 3 hEp hcop hinj
  have hdim : Module.finrank (ZMod 2) (Additive (X ⧸ frattini X)) ≤ 4 := by
    rw [twoGroup_frattini_finrank_eq_group_rank hX]
    exact hX4
  refine no_fixed_vector_threeSquared hcomm hcard' hpow
    (multiplicative_action_zmod_linear_aut (acting := B) (source := X ⧸ frattini X) 2)
    (faithful_multiplicative_action_zmod_linear_aut 2 hfaithfulQ) hdim
    (Additive.ofMul (QuotientGroup.mk x)) ?_ ?_
  · intro h0
    exact hxF ((QuotientGroup.eq_one_iff x).mp h0)
  · intro b
    change Additive.ofMul (QuotientGroup.mk (φ b x)) = Additive.ofMul (QuotientGroup.mk x)
    congr 1
    exact QuotientGroup.eq_iff_div_mem.mpr (by simpa [div_eq_mul_inv] using hx b)

end CFSG.GH74.E2

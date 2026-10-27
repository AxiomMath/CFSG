module

public import CFSG.ClassicalInvolution.Q3.TL4MF163Res
public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution QuaternionGroup

@[expose] def Concl163Syl {X : Type} [Group X] (R : Subgroup X) (S : Sylow 2 R) (z : X) : Prop :=
  ∀ β : MulAut X, β * β = 1 → (∀ x ∈ (S : Subgroup R).map R.subtype, β x = x) →
    β = 1 ∨ β = MulAut.conj z

namespace MF163

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem sylow_le_tightCore {R : Subgroup X} (S : Sylow 2 R) :
    (S : Subgroup R).map R.subtype ≤ tightCore R := by
  intro x hx
  have hV : IsPGroup 2 ((S : Subgroup R).map R.subtype) := S.isPGroup'.map _
  exact Subgroup.subset_closure ⟨Subgroup.map_subtype_le _ hx,
    hV.to_le (Subgroup.zpowers_le.mpr hx)⟩

omit [Finite X] in
theorem Concl163Syl.concl163 {R : Subgroup X} {S : Sylow 2 R} {z : X} (h : Concl163Syl R S z) :
    Concl163 R z :=
  fun β hβ2 hβK => h β hβ2 fun x hx => hβK x (sylow_le_tightCore S hx)

theorem concl163Syl_of_aut {R : Subgroup X} {S : Sylow 2 R} {z : X} {N : Subgroup X}
    [N.Normal] [IsSimpleGroup N] (hC : Subgroup.centralizer (N : Set X) = ⊥) {P : Type}
    [Group P] (e : ↥N ≃* P)
    (h : ∀ b : MulAut P, b * b = 1 →
      (∀ k ∈ (S : Subgroup R).map R.subtype, b * MulAut.congr e (MulAut.conjNormal k) =
        MulAut.congr e (MulAut.conjNormal k) * b) →
      b = 1 ∨ b = MulAut.congr e (MulAut.conjNormal z)) :
    Concl163Syl R S z := by
  intro β hβ2 hβK
  have hmap := map_eq_of_centralizer_eq_bot hC β
  let βN : MulAut N := restrictAut β hmap
  let b : MulAut P := MulAut.congr e βN
  have hb : ∀ n : N, b (e n) = e (βN n) := fun n => by simp [b, MulAut.congr_apply]
  have hι : ∀ (x : X) (n : N),
      MulAut.congr e (MulAut.conjNormal x) (e n) = e (MulAut.conjNormal x n) := fun x n => by
    simp [MulAut.congr_apply]
  have hrel : ∀ x : X, b * MulAut.congr e (MulAut.conjNormal x) =
      MulAut.congr e (MulAut.conjNormal (β x)) * b := by
    intro x
    ext w
    obtain ⟨n, rfl⟩ := e.surjective w
    rw [MulAut.mul_apply, MulAut.mul_apply, hι, hb, hb, hι]
    congr 1
    apply Subtype.ext
    rw [coe_restrictAut, MulAut.conjNormal_apply, MulAut.conjNormal_apply, coe_restrictAut,
      map_mul, map_mul, map_inv]
  have hb2 : b * b = 1 := by
    have h1 : βN * βN = 1 := by
      ext n
      rw [MulAut.mul_apply, coe_restrictAut, coe_restrictAut, ← MulAut.mul_apply, hβ2,
        MulAut.one_apply, MulAut.one_apply]
    simp only [b]
    rw [← map_mul, h1, map_one]
  rcases h b hb2 fun k hk => by rw [hrel, hβK k hk] with h1 | h1
  · left
    have hβN : βN = 1 := (MulAut.congr e).injective (h1.trans (map_one _).symm)
    refine eq_of_eqOn hC (map_eq_of_centralizer_eq_bot hC 1) fun n hn => ?_
    have := congrArg (fun φ : MulAut N => ((φ ⟨n, hn⟩ : N) : X)) hβN
    simpa [βN, coe_restrictAut] using this
  · right
    have hβN : βN = MulAut.conjNormal z := (MulAut.congr e).injective h1
    refine eq_of_eqOn hC (map_eq_of_centralizer_eq_bot hC _) fun n hn => ?_
    have := congrArg (fun φ : MulAut N => ((φ ⟨n, hn⟩ : N) : X)) hβN
    simp only [βN, coe_restrictAut, MulAut.conjNormal_apply] at this
    rw [this, MulAut.conj_apply]

theorem exists_quat_of_member_syl {R : Subgroup X} {S : Sylow 2 R} {z : X}
    (hm : EdgelessMember3 R S z) :
    ∃ ι : QuaternionGroup 2 →* X, Function.Injective ι ∧
      (∀ g, ι g ∈ (S : Subgroup R).map R.subtype) ∧ ι (QuaternionGroup.a 2) = z := by
  obtain ⟨eQ⟩ := hm.cls.1
  let ι : QuaternionGroup 2 →* X :=
    R.subtype.comp ((S : Subgroup R).subtype.comp eQ.symm.toMonoidHom)
  have hι : Function.Injective ι := fun g h hgh =>
    eQ.symm.injective (Subtype.ext (Subtype.ext hgh))
  have hmem : ∀ g, ι g ∈ (S : Subgroup R).map R.subtype := fun g => ⟨_, (eQ.symm g).2, rfl⟩
  refine ⟨ι, hι, hmem, ?_⟩
  have h2 : orderOf (ι (QuaternionGroup.a 2)) = 2 := by
    rw [orderOf_injective ι hι]
    exact orderOf_eq_prime (by decide) (by decide)
  exact hm.datum.eq_of_orderOf_eq_two (Subgroup.map_subtype_le _ (hmem _)) h2

omit [Finite X] in
theorem eq_of_sq_eq_one_of_isCyclic {C : Type} [Group C] [Finite C] [IsCyclic C] {u v : C}
    (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) : u = v := by
  classical
  have : Fintype C := Fintype.ofFinite C
  by_contra huv
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  have hsub : ({1, u, v} : Finset C) ⊆ Finset.univ.filter (fun a => a ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · exact hu
    · exact hv
  have hcard : ({1, u, v} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair huv]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hu1, Ne.symm hv1⟩
  have := Finset.card_le_card hsub
  omega

theorem exists_cyclic4_mem_sylow {R : Subgroup X} {S : Sylow 2 R}
    (hq8 : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) {N : Subgroup X} [N.Normal]
    (hC : Subgroup.centralizer (N : Set X) = ⊥) (hO : Nobq.OutTwoCyclic N) :
    ∃ c ∈ (S : Subgroup R).map R.subtype, c ∈ N ∧ orderOf c = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eS⟩ := hq8
  let ιQ : QuaternionGroup 2 →* X :=
    R.subtype.comp ((S : Subgroup R).subtype.comp eS.symm.toMonoidHom)
  have hιQ : Function.Injective ιQ := fun g h hgh =>
    eS.symm.injective (Subtype.ext (Subtype.ext hgh))
  have hmem : ∀ g, ιQ g ∈ (S : Subgroup R).map R.subtype := fun g => ⟨_, (eS.symm g).2, rfl⟩
  let ψ : QuaternionGroup 2 →* X ⧸ N := (QuotientGroup.mk' N).comp ιQ
  have hQ2 : IsPGroup 2 (QuaternionGroup 2) :=
    IsPGroup.of_card (n := 3) (by rw [Nat.card_eq_fintype_card, QuaternionGroup.card]; rfl)
  have hcyc : IsCyclic ↥ψ.range := Nobq.isCyclic_of_outTwoCyclic N hC hO _
    (hQ2.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective)
  have hord : ∀ q : QuaternionGroup 2, ¬ q ^ 2 ^ 1 = 1 → q ^ 2 ^ (1 + 1) = 1 → ψ q = 1 →
      ∃ c ∈ (S : Subgroup R).map R.subtype, c ∈ N ∧ orderOf c = 4 := by
    intro q hq1 hq2 hψq
    refine ⟨ιQ q, hmem q, (QuotientGroup.eq_one_iff _).mp hψq, ?_⟩
    rw [orderOf_injective ιQ hιQ, orderOf_eq_prime_pow hq1 hq2]
    rfl
  by_cases h1 : ψ (a 1) = 1
  · exact hord _ (by decide) (by decide) h1
  by_cases h2 : ψ (xa 0) = 1
  · exact hord _ (by decide) (by decide) h2
  have hc := (IsCyclic.commGroup (α := ↥ψ.range)).mul_comm ⟨_, ⟨a 1, rfl⟩⟩ ⟨_, ⟨xa 0, rfl⟩⟩
  have hcomm : ψ (a 1) * ψ (xa 0) = ψ (xa 0) * ψ (a 1) := congrArg Subtype.val hc
  have hz : ψ (a 2) = 1 := by
    have e : (a 2 : QuaternionGroup 2) = a 1 * xa 0 * (a 1)⁻¹ * (xa 0)⁻¹ := by decide
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have hu2 : (⟨ψ (a 1), ⟨a 1, rfl⟩⟩ : ↥ψ.range) ^ 2 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, ← map_pow, show (a 1 : QuaternionGroup 2) ^ 2 = a 2 by decide, hz]
    rfl)
  have hv2 : (⟨ψ (xa 0), ⟨xa 0, rfl⟩⟩ : ↥ψ.range) ^ 2 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, ← map_pow, show (xa 0 : QuaternionGroup 2) ^ 2 = a 2 by decide, hz]
    rfl)
  have heq := eq_of_sq_eq_one_of_isCyclic hu2 hv2 (fun h => h1 (congrArg Subtype.val h))
    (fun h => h2 (congrArg Subtype.val h))
  have heq' : ψ (a 1) = ψ (xa 0) := congrArg Subtype.val heq
  refine hord (a 1 * (xa 0)⁻¹) (by decide) (by decide) ?_
  rw [map_mul, map_inv, heq', mul_inv_cancel]

end MF163

end CFSG.ClassicalInvolution.Q3.TL4

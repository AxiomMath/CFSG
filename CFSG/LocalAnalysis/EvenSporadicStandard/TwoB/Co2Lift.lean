module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.KStructure

public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22

section Quotient

variable {X : Type*} [Group X] (N : Subgroup X) [N.Normal]

theorem exists_conj_mul_mem_of_forall_inner
    (hinn : ∀ β : MulAut (X ⧸ N), ∃ g, β = MulAut.conj g) (α : MulAut X)
    (hα : N.map (α : X →* X) = N) : ∃ g : X, ∀ x : X, (g * x * g⁻¹)⁻¹ * α x ∈ N := by
  obtain ⟨q, hq⟩ := hinn (QuotientGroup.congr N N α hα)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨g, fun x => ?_⟩
  have h := congrArg (fun β : MulAut (X ⧸ N) => β (x : X ⧸ N)) hq
  simp only [MulAut.conj_apply] at h
  rw [QuotientGroup.congr_mk] at h
  rw [← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  exact h.symm

theorem mem_of_forall_commutator_mem_of_center_eq_bot (hZ : Subgroup.center (X ⧸ N) = ⊥) (w : X)
    (hw : ∀ x : X, w * x * w⁻¹ * x⁻¹ ∈ N) : w ∈ N := by
  have hc : (w : X ⧸ N) ∈ Subgroup.center (X ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : (↑(w * x * w⁻¹) : X ⧸ N) = ↑x := by
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using hw x⁻¹
    calc (↑x : X ⧸ N) * ↑w = ↑(w * x * w⁻¹ * w) := by rw [QuotientGroup.mk_mul, h1]
      _ = ↑w * ↑x := by rw [inv_mul_cancel_right, QuotientGroup.mk_mul]
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hc
  exact hc

end Quotient

section Lift

variable {G : Type} [Group G]

theorem exists_lift_of_complete {K C : Subgroup G} (hKC : K ≤ C) (hidx : K.relIndex C = 2)
    (hRC : ((O2In K).subgroupOf C).Normal)
    (hinn : ∀ β : MulAut (↥K ⧸ CFSG.pCore 2 ↥K), ∃ g, β = MulAut.conj g)
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) :
    ∃ x ∈ C, x ∉ K ∧ (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ O2In K) ∧ x ^ 2 ∈ O2In K := by
  have hKn : (K.subgroupOf C).Normal := Subgroup.normal_of_index_eq_two hidx
  have hKconj : ∀ y ∈ C, ∀ k ∈ K, y * k * y⁻¹ ∈ K := fun y hy k hk =>
    mem_subgroupOf.1 (hKn.conj_mem ⟨k, hKC hk⟩ (mem_subgroupOf.2 hk) ⟨y, hy⟩)
  have hRK : O2In K ≤ K := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hRconj : ∀ y ∈ C, ∀ r ∈ O2In K, y * r * y⁻¹ ∈ O2In K := fun y hy r hr =>
    mem_subgroupOf.1 (hRC.conj_mem ⟨r, hKC (hRK hr)⟩ (mem_subgroupOf.2 hr) ⟨y, hy⟩)
  have hRKconj : ∀ k ∈ K, ∀ r ∈ O2In K, k * r * k⁻¹ ∈ O2In K := fun k hk r hr =>
    mem_subgroupOf.1 ((normal_subgroupOf_O2In K).conj_mem ⟨r, hRK hr⟩ (mem_subgroupOf.2 hr)
      ⟨k, hk⟩)
  obtain ⟨y, hyC, hyK⟩ : ∃ y ∈ C, y ∉ K := by
    by_contra h
    have hCK : C ≤ K := fun y hy => by_contra fun hyK => h ⟨y, hy, hyK⟩
    rw [relIndex_eq_one.2 hCK] at hidx
    exact absurd hidx (by norm_num)
  obtain ⟨α, hα, hα'⟩ : ∃ α : MulAut ↥K, (∀ k : ↥K, (α k : G) = y * k * y⁻¹) ∧
      ∀ k : ↥K, (α.symm k : G) = y⁻¹ * k * y :=
    ⟨{ toFun := fun k => ⟨y * k * y⁻¹, hKconj y hyC k k.2⟩
       invFun := fun k => ⟨y⁻¹ * k * y, by simpa using hKconj y⁻¹ (C.inv_mem hyC) k k.2⟩
       left_inv := fun k => Subtype.ext (by simp [mul_assoc])
       right_inv := fun k => Subtype.ext (by simp [mul_assoc])
       map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }, fun _ => rfl, fun _ => rfl⟩
  have hαN : (CFSG.pCore 2 ↥K).map (α : ↥K →* ↥K) = CFSG.pCore 2 ↥K := by
    ext n
    constructor
    · rintro ⟨m, hm, rfl⟩
      refine (mem_pCore_iff_mem_O2In _).2 ?_
      have := hRconj y hyC _ ((mem_pCore_iff_mem_O2In m).1 hm)
      rw [← hα m] at this
      exact this
    · intro hn
      refine ⟨α.symm n, (mem_pCore_iff_mem_O2In _).2 ?_, α.apply_symm_apply n⟩
      have := hRconj y⁻¹ (C.inv_mem hyC) _ ((mem_pCore_iff_mem_O2In n).1 hn)
      rw [hα']
      simpa using this
  obtain ⟨g, hg⟩ := exists_conj_mul_mem_of_forall_inner (CFSG.pCore 2 ↥K) hinn α hαN
  obtain ⟨x, hxC, hxK, hcomm⟩ : ∃ x ∈ C, x ∉ K ∧ ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ O2In K := by
    refine ⟨(g : G)⁻¹ * y, C.mul_mem (C.inv_mem (hKC g.2)) hyC,
      fun h => hyK (by simpa using K.mul_mem g.2 h), fun k hk => ?_⟩
    have h1 : (g : G) * k⁻¹ * (g : G)⁻¹ * (y * k * y⁻¹) ∈ O2In K := by
      have := (mem_pCore_iff_mem_O2In _).1 (hg ⟨k, hk⟩)
      simpa [mul_assoc, hα] using this
    have h2 := hRKconj (k * (g : G)⁻¹) (K.mul_mem hk (K.inv_mem g.2)) _ h1
    convert h2 using 1
    group
  have hsq : x ^ 2 ∈ K := by
    have h := (K.subgroupOf C).pow_index_mem (⟨x, hxC⟩ : ↥C)
    rw [show (K.subgroupOf C).index = 2 from hidx] at h
    exact mem_subgroupOf.1 h
  refine ⟨x, hxC, hxK, hcomm, ?_⟩
  have hw : (⟨x ^ 2, hsq⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
    refine mem_of_forall_commutator_mem_of_center_eq_bot (CFSG.pCore 2 ↥K) hZ _ fun k => ?_
    rw [mem_pCore_iff_mem_O2In]
    have e1 := hcomm _ (hKconj x hxC k k.2)
    have e2 := hcomm k k.2
    convert (O2In K).mul_mem e1 e2 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, pow_two]
    group
  exact (mem_pCore_iff_mem_O2In _).1 hw

end Lift

section Co2

private theorem center_eq_bot_of_isSimpleGroup_of_not_prime {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (h : ¬ (Nat.card Y).Prime) : Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h0 | h0
  · exact h0
  · exfalso
    let : CommGroup Y := { ‹Group Y› with
      mul_comm := fun a b => (mem_center_iff.mp (h0 ▸ mem_top a) b).symm }
    exact h (IsSimpleGroup.prime_card (α := Y))

private theorem center_eq_bot_of_mulEquiv_aux {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z)
    (h : Subgroup.center Z = ⊥) : Subgroup.center Y = ⊥ := by
  have hmap : (Subgroup.center Y).map e.toMonoidHom = Subgroup.center Z := map_center_eq e
  rw [h] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hmap

theorem center_eq_bot_of_mulEquiv_co2 {Y : Type*} [Group Y]
    (e : Y ≃* Carrier .Co2) : Subgroup.center Y = ⊥ := by
  have := CFSG.Sporadic.Co2.isSimpleGroup_Co2
  exact center_eq_bot_of_mulEquiv_aux (Z := NativeSporadic.Co2) e
    (center_eq_bot_of_isSimpleGroup_of_not_prime (by rw [CFSG.Sporadic.Co2.card_Co2]; norm_num))

variable
  {G : Type} [Group G] {K C : Subgroup G}

theorem exists_lift_centralizing_co2 (hKC : K ≤ C) (hidx : K.relIndex C = 2)
    (hRC : ((O2In K).subgroupOf C).Normal) (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* Carrier .Co2) :
    ∃ x ∈ C, x ∉ K ∧ (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ O2In K) ∧ x ^ 2 ∈ O2In K :=
  exists_lift_of_complete hKC hidx hRC
    (CFSG.Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner_model _ e)
    (center_eq_bot_of_mulEquiv_co2 e)

end Co2

end CFSG.EvenSporadicStandard.TwoB

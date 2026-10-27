module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021Rank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open

private theorem inv_mul_mul_inv_eq_one_iff {M : Type} [Group M] (a t : M) : a⁻¹ * t * a * t⁻¹ = 1 ↔ a * t = t * a := by
  constructor
  · intro h
    have h1 : a⁻¹ * (t * a) = t := by
      have := congrArg (· * t) h
      simpa [mul_assoc] using this
    calc a * t = a * (a⁻¹ * (t * a)) := by rw [h1]
      _ = t * a := by group
  · intro h
    calc a⁻¹ * t * a * t⁻¹ = a⁻¹ * (t * a) * t⁻¹ := by group
      _ = a⁻¹ * (a * t) * t⁻¹ := by rw [h]
      _ = 1 := by group

theorem exists_comm_fail_mod {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {N A T O : Subgroup G}
    (hAN : A ≤ N) (hTN : T ≤ N) (hNO : ∀ n ∈ N, ∀ o ∈ O, n * o * n⁻¹ ∈ O)
    (hOp : ¬ p ∣ Nat.card O) (hA : CFSG.Open.IsElemAbelian p A) (hcardA : Nat.card A = p ^ 2)
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) (hcop : Nat.Coprime p (Nat.card T))
    (hfaith : ∀ a ∈ A, (∀ t ∈ T, a⁻¹ * t * a * t⁻¹ ∈ O) → a = 1)
    {b : G} (hb : b ∈ A) (hb1 : b ≠ 1) :
    ∃ a ∈ A, a ∉ Subgroup.zpowers b ∧ ∃ t ∈ T, a⁻¹ * t * a * t⁻¹ ∈ O ∧ b⁻¹ * t * b * t⁻¹ ∉ O := by
  classical
  haveI := Fact.mk hp
  haveI hÔn : (O.subgroupOf N).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hNO (g : G) g.2 (n : G) hn
    simpa using this
  let π : ↥N →* ↥N ⧸ O.subgroupOf N := QuotientGroup.mk' (O.subgroupOf N)
  have hker : ∀ z : ↥N, π z = 1 ↔ (z : G) ∈ O := fun z => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hAO : ∀ a ∈ A, a ∈ O → a = 1 := by
    intro a ha hao
    by_contra ha1
    have hord : orderOf a = p := orderOf_eq_prime (hA.2 a ha) ha1
    have : p ∣ Nat.card O := by
      rw [← hord]
      exact Subgroup.orderOf_dvd_natCard O hao
    exact hOp this
  have hπinj : Function.Injective (π.comp (A.subgroupOf N).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hz
    have hzO : (((z : ↥(A.subgroupOf N)) : ↥N) : G) ∈ O := (hker _).1 hz
    have hzA : (((z : ↥(A.subgroupOf N)) : ↥N) : G) ∈ A := Subgroup.mem_subgroupOf.1 z.2
    have := hAO _ hzA hzO
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subtype.ext this)
  have hrange : (π.comp (A.subgroupOf N).subtype).range = (A.subgroupOf N).map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardÂ : Nat.card ((A.subgroupOf N).map π) = p ^ 2 := by
    rw [← hrange, ← hcardA]
    have h1 := Nat.card_congr (MonoidHom.ofInjective hπinj).toEquiv
    rw [← h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have hÂel : CFSG.Open.IsElemAbelian p ((A.subgroupOf N).map π) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨x', hx', hxe⟩ := x.2
      obtain ⟨y', hy', hye⟩ := y.2
      have hc : (x' : G) * (y' : G) = (y' : G) * (x' : G) :=
        congrArg Subtype.val (hA.1.is_comm.comm (⟨(x' : G), Subgroup.mem_subgroupOf.1 hx'⟩ : ↥A)
          ⟨(y' : G), Subgroup.mem_subgroupOf.1 hy'⟩)
      have hc' : x' * y' = y' * x' := Subtype.ext hc
      apply Subtype.ext
      change (x : ↥N ⧸ O.subgroupOf N) * (y : ↥N ⧸ O.subgroupOf N) =
        (y : ↥N ⧸ O.subgroupOf N) * (x : ↥N ⧸ O.subgroupOf N)
      rw [← hxe, ← hye, ← map_mul, ← map_mul, hc']
    · intro z hz
      obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.1 hz
      rw [← map_pow]
      have : z' ^ p = 1 := Subtype.ext (hA.2 (z' : G) (Subgroup.mem_subgroupOf.1 hz'))
      rw [this, map_one]
  have hÂT : (A.subgroupOf N).map π ≤ Subgroup.normalizer (((T.subgroupOf N).map π : Subgroup _) : Set _) := by
    intro z hz
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.1 hz
    refine Subgroup.le_normalizer_map π (Subgroup.mem_map.2 ⟨z', ?_, rfl⟩)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.1 (hAT (Subgroup.mem_subgroupOf.1 hz')) (y : G)
  have hcopTq : Nat.Coprime p (Nat.card ((T.subgroupOf N).map π)) := by
    refine Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd (T.subgroupOf N) π) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv]
    exact hcop
  have hfaithÂ : ∀ a ∈ (A.subgroupOf N).map π,
      (∀ t ∈ (T.subgroupOf N).map π, a * t = t * a) → a = 1 := by
    intro a ha hat
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
    have haA : (a' : G) ∈ A := Subgroup.mem_subgroupOf.1 ha'
    have h1 : (a' : G) = 1 := by
      apply hfaith _ haA
      intro t ht
      have htN : t ∈ N := hTN ht
      have hc := hat (π ⟨t, htN⟩) (Subgroup.mem_map.2 ⟨⟨t, htN⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩)
      have hz : π (a'⁻¹ * ⟨t, htN⟩ * a' * ⟨t, htN⟩⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        exact (inv_mul_mul_inv_eq_one_iff _ _).2 hc
      have := (hker _).1 hz
      simpa using this
    have : a' = 1 := Subtype.ext h1
    rw [this, map_one]
  have hbN : b ∈ N := hAN hb
  have hbÂ : π ⟨b, hbN⟩ ∈ (A.subgroupOf N).map π :=
    Subgroup.mem_map.2 ⟨⟨b, hbN⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩
  have hb1' : π ⟨b, hbN⟩ ≠ 1 := by
    intro h
    have hbO : b ∈ O := (hker _).1 h
    exact hb1 (hAO b hb hbO)
  obtain ⟨â, hâÂ, hânb, tq, htq, hcomm, hnc⟩ :=
    exists_comm_fail hp hÂel hcardÂ hÂT hcopTq hfaithÂ hbÂ hb1'
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 hâÂ
  obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 htq
  have haA : (a' : G) ∈ A := Subgroup.mem_subgroupOf.1 ha'
  have htT : (t' : G) ∈ T := Subgroup.mem_subgroupOf.1 ht'
  refine ⟨a', haA, ?_, t', htT, ?_, ?_⟩
  · intro hmem
    apply hânb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have : (⟨b, hbN⟩ : ↥N) ^ k = a' := Subtype.ext (by simpa using hk)
    rw [← map_zpow, this]
  · have hz : π (a'⁻¹ * t' * a' * t'⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      exact (inv_mul_mul_inv_eq_one_iff _ _).2 hcomm
    have := (hker _).1 hz
    simpa using this
  · intro hO
    apply hnc
    have hz : π (⟨b, hbN⟩⁻¹ * t' * ⟨b, hbN⟩ * t'⁻¹) = 1 := (hker _).2 (by simpa using hO)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hz
    exact (inv_mul_mul_inv_eq_one_iff _ _).1 hz

end CFSG.LocalAnalysis.GLTheoremA.T2021

end

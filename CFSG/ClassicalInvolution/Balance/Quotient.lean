module

public import CFSG.ClassicalInvolution.Balance.Delta

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.Assembly.Dichotomy

section CentralizerLifting

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem exists_mem_centralizer_mk_eq {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N)) {f : X}
    (hf : IsPGroup 2 (Subgroup.zpowers f)) {y : X}
    (hy : QuotientGroup.mk' N f * QuotientGroup.mk' N y =
      QuotientGroup.mk' N y * QuotientGroup.mk' N f) :
    ∃ y' ∈ Subgroup.centralizer {f}, QuotientGroup.mk' N y' = QuotientGroup.mk' N y := by
  set π := QuotientGroup.mk' N with hπ
  have hT : Subgroup.zpowers f ≤ (Subgroup.centralizer {π y}).comap π := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hy
  let S := {z : X // π z = π y}
  have hsmul : ∀ (p : Subgroup.zpowers f) (z : S), π (p.1 * z.1 * p.1⁻¹) = π y := fun p z => by
    have hp : π p.1 * π y = π y * π p.1 :=
      Subgroup.mem_centralizer_singleton_iff.mp (hT p.2)
    rw [map_mul, map_mul, map_inv, z.2, hp, mul_assoc, mul_inv_cancel, mul_one]
  let _ : MulAction (Subgroup.zpowers f) S :=
    { smul := fun p z => ⟨p.1 * z.1 * p.1⁻¹, hsmul p z⟩
      one_smul := fun z => Subtype.ext (by
        change (1 : X) * z.1 * (1 : X)⁻¹ = z.1
        simp)
      mul_smul := fun p q z => Subtype.ext (by
        change (p.1 * q.1) * z.1 * (p.1 * q.1)⁻¹ = p.1 * (q.1 * z.1 * q.1⁻¹) * p.1⁻¹
        simp [mul_assoc]) }
  have hcard : Nat.card S = Nat.card N := by
    refine Nat.card_congr
      { toFun := fun z => ⟨y⁻¹ * z.1, QuotientGroup.eq.mp z.2.symm⟩
        invFun := fun n => ⟨y * n.1, ?_⟩
        left_inv := fun z => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp) }
    change ((y * n.1 : X) : X ⧸ N) = (y : X ⧸ N)
    rw [QuotientGroup.eq]
    simp
  have hnd : ¬ 2 ∣ Nat.card S := by
    rw [hcard]
    exact fun h => (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h)
  obtain ⟨z, hz⟩ := hf.nonempty_fixed_point_of_prime_not_dvd_card S hnd
  have hfix := congrArg Subtype.val
    (MulAction.mem_fixedPoints.mp hz ⟨f, Subgroup.mem_zpowers f⟩)
  refine ⟨z.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_, z.2⟩
  change f * z.1 * f⁻¹ = z.1 at hfix
  calc z.1 * f = (f * z.1 * f⁻¹) * f := by rw [hfix]
    _ = f * z.1 := by group

omit [Finite X] in
theorem map_centralizer_singleton_eq {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N)) {f : X}
    (hf : IsPGroup 2 (Subgroup.zpowers f)) :
    (Subgroup.centralizer {f}).map (QuotientGroup.mk' N) =
      Subgroup.centralizer {QuotientGroup.mk' N f} := by
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hc]
  · intro q hq
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨y', hy', hπ⟩ := exists_mem_centralizer_mk_eq hN hf
      (Subgroup.mem_centralizer_singleton_iff.mp hq).symm
    exact ⟨y', hy', hπ⟩

theorem map_oddCoreIn_centralizer_le {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N)) {f : X}
    (hf : IsPGroup 2 (Subgroup.zpowers f)) :
    (oddCoreIn (Subgroup.centralizer {f})).map (QuotientGroup.mk' N) ≤
      oddCoreIn (Subgroup.centralizer {QuotientGroup.mk' N f}) := by
  set π := QuotientGroup.mk' N with hπ
  set C : Subgroup X := Subgroup.centralizer {f} with hC
  have hmap := map_centralizer_singleton_eq hN hf
  refine le_oddCoreIn_of_normalizes ?_ ?_ ?_
  · rw [← hmap]
    exact Subgroup.map_mono (oddCoreIn_le C)
  · have key : ∀ c ∈ C, ∀ y ∈ (oddCoreIn C).map π,
        π c * y * (π c)⁻¹ ∈ (oddCoreIn C).map π := by
      rintro c hc _ ⟨o, ho, rfl⟩
      exact ⟨c * o * c⁻¹, conj_mem_oddCoreIn hc ho, by simp [map_mul, map_inv]⟩
    rw [← hmap]
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key c hc y, fun hy => ?_⟩
    have h2 := key c⁻¹ (inv_mem hc) _ hy
    have h3 : π c⁻¹ * (π c * y * (π c)⁻¹) * (π c⁻¹)⁻¹ = y := by
      rw [map_inv]
      group
    rwa [h3] at h2
  · exact (odd_card_oddCoreIn C).of_dvd_nat (Subgroup.card_map_dvd _ _)

theorem map_deltaCore_le {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N)) {F : Subgroup X}
    (hF : IsPGroup 2 F) :
    (deltaCore F).map (QuotientGroup.mk' N) ≤ deltaCore (F.map (QuotientGroup.mk' N)) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_deltaCore_iff]
  rintro _ ⟨f, hf, rfl⟩ hf1
  have hf1' : f ≠ 1 := fun h => hf1 (by simp [h])
  have hzp : IsPGroup 2 (Subgroup.zpowers f) := hF.to_le (Subgroup.zpowers_le.mpr hf)
  have hx' : x ∈ involutionOddCore f := mem_deltaCore_iff.mp hx f hf hf1'
  exact map_oddCoreIn_centralizer_le hN hzp ⟨x, hx', rfl⟩

end CentralizerLifting

section Ambient

variable {G : Type*} [Group G] [Finite G]

theorem subgroupOf_deltaCore_le {a : G} {F : Subgroup G} :
    (deltaCore F ⊓ Subgroup.centralizer {a}).subgroupOf (Subgroup.centralizer {a}) ≤
      deltaCore (F.subgroupOf (Subgroup.centralizer {a})) := by
  set C : Subgroup G := Subgroup.centralizer {a} with hC
  intro x hx
  rw [mem_deltaCore_iff]
  intro fC hfC hfC1
  have hf : (fC : G) ∈ F := hfC
  have hf1 : (fC : G) ≠ 1 := fun h => hfC1 (Subtype.ext h)
  have hx1 : (x : G) ∈ involutionOddCore (fC : G) :=
    mem_deltaCore_iff.mp (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1 _ hf hf1
  let S : Subgroup C := (involutionOddCore (fC : G)).subgroupOf C
  have key : ∀ c : C, (c : G) * fC = fC * c → ∀ y ∈ S, c * y * c⁻¹ ∈ S := by
    intro c hc y hy
    exact conj_mem_oddCoreIn (X := Subgroup.centralizer {(fC : G)})
      (Subgroup.mem_centralizer_singleton_iff.mpr hc) hy
  have hS : S ≤ oddCoreIn (Subgroup.centralizer {fC}) := by
    refine le_oddCoreIn_of_normalizes ?_ ?_ ?_
    · intro s hs
      refine Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)
      exact Subgroup.mem_centralizer_singleton_iff.mp (involutionOddCore_le_centralizer _ hs)
    · intro c hc
      have hcomm : (c : G) * fC = fC * c :=
        congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨key c hcomm y, fun hy => ?_⟩
      have hcomm' : ((c⁻¹ : C) : G) * fC = fC * (c⁻¹ : C) := by
        have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (inv_mem hc))
        exact this
      have h2 := key c⁻¹ hcomm' _ hy
      have h3 : c⁻¹ * (c * y * c⁻¹) * (c⁻¹)⁻¹ = y := by group
      rwa [h3] at h2
    · exact (odd_card_oddCoreIn (Subgroup.centralizer {(fC : G)})).of_dvd_nat
        (Subgroup.card_comap_dvd_of_injective _ C.subtype C.subtype_injective)
  exact hS hx1

theorem deltaCore_inf_centralizer_le_involutionOddCore {a : G} {F : Subgroup G}
    (hF : IsPGroup 2 F) (hFC : F ≤ Subgroup.centralizer {a})
    (hΔ : deltaCore ((F.subgroupOf (Subgroup.centralizer {a})).map
      (QuotientGroup.mk' (componentClassificationOddCore (Subgroup.centralizer {a})))) = ⊥) :
    deltaCore F ⊓ Subgroup.centralizer {a} ≤ involutionOddCore a := by
  set C : Subgroup G := Subgroup.centralizer {a} with hC
  set N := componentClassificationOddCore C with hN
  intro x hx
  have hxC : (⟨x, hx.2⟩ : C) ∈ (deltaCore F ⊓ C).subgroupOf C := hx
  have h1 := subgroupOf_deltaCore_le hxC
  have hFpg : IsPGroup 2 (F.subgroupOf C) :=
    hF.of_equiv (Subgroup.subgroupOfEquivOfLe hFC).symm
  have h2 := map_deltaCore_le (N := N) (CFSG.ComponentClassification.OddCore.odd_card C) hFpg
    ⟨_, h1, rfl⟩
  rw [hΔ] at h2
  have h3 : (QuotientGroup.mk' N) ⟨x, hx.2⟩ = 1 := Subgroup.mem_bot.mp h2
  have h4 : (⟨x, hx.2⟩ : C) ∈ N := (QuotientGroup.eq_one_iff _).mp h3
  exact ⟨⟨x, hx.2⟩, h4, rfl⟩

theorem twoBalancedWrt_of_quotient_deltaCore_eq_bot {A : Subgroup G} (hA : IsMulCommutative A)
    (h : ∀ a ∈ A, a ≠ 1 → ∀ F ∈ signalizerFunctorEk 2 2 A,
      deltaCore ((F.subgroupOf (Subgroup.centralizer {a})).map
        (QuotientGroup.mk' (componentClassificationOddCore (Subgroup.centralizer {a})))) = ⊥) :
    TwoBalancedWrt A := by
  intro F hF a ha ha1
  have hFC : F ≤ Subgroup.centralizer {a} := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val (hA.is_comm.comm (⟨a, ha⟩ : A) ⟨f, hF.1 hf⟩)).symm
  exact deltaCore_inf_centralizer_le_involutionOddCore (IsPGroup.of_card hF.2) hFC (h a ha ha1 F hF)

end Ambient

end CFSG.ClassicalInvolution.Balance

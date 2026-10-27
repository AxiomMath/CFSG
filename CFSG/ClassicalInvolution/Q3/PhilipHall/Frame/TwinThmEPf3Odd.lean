module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecQuot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent2Quot
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
open scoped commutatorElement MatrixGroups

namespace TwinThmE

section Odd

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} [Finite G] {N : Subgroup G} [N.Normal]

theorem exists_commuting_lift {J : Subgroup G} (hodd : Odd (Nat.card ↥(N ⊓ J))) {u a : G}
    (hu : u ∈ J) (hu2 : IsPGroup 2 (Subgroup.zpowers u)) (ha : a ∈ J)
    (hc : QuotientGroup.mk' N u * QuotientGroup.mk' N a =
      QuotientGroup.mk' N a * QuotientGroup.mk' N u) :
    ∃ a' ∈ J, QuotientGroup.mk' N a' = QuotientGroup.mk' N a ∧ a' * u = u * a' := by
  set mk := QuotientGroup.mk' N with hmk
  set A : Subgroup G := N ⊓ J with hA
  set X : Set G := (fun m => a * m) '' (A : Set G) with hX
  have hclosed : ∀ v ∈ Subgroup.zpowers u, ∀ w ∈ X, v * w * v⁻¹ ∈ X := by
    rintro v hv _ ⟨m, hm, rfl⟩
    have hvJ : v ∈ J := (Subgroup.zpowers_le.mpr hu) hv
    have hcv : mk v * mk a = mk a * mk v := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      rw [map_zpow]
      exact (Commute.zpow_left (show Commute (mk u) (mk a) from hc) k).eq
    have h1 : a⁻¹ * (v * a * v⁻¹) ∈ A := by
      have hk : mk (a⁻¹ * (v * a * v⁻¹)) = 1 := by
        simp only [map_mul, map_inv]
        rw [hcv]
        group
      exact ⟨(QuotientGroup.eq_one_iff _).mp hk,
        J.mul_mem (J.inv_mem ha) (J.mul_mem (J.mul_mem hvJ ha) (J.inv_mem hvJ))⟩
    have h2 : v * m * v⁻¹ ∈ A :=
      ⟨‹N.Normal›.conj_mem _ hm.1 v, J.mul_mem (J.mul_mem hvJ hm.2) (J.inv_mem hvJ)⟩
    refine ⟨a⁻¹ * (v * a * v⁻¹) * (v * m * v⁻¹), A.mul_mem h1 h2, ?_⟩
    simp only
    group
  let _ : MulAction (Subgroup.zpowers u) X :=
    { smul := fun v w => ⟨(v : G) * w.1 * (v : G)⁻¹, hclosed v v.2 w.1 w.2⟩
      one_smul := fun w => Subtype.ext (by
        show ((1 : Subgroup.zpowers u) : G) * w.1 * ((1 : Subgroup.zpowers u) : G)⁻¹ = w.1
        simp)
      mul_smul := fun a b w => Subtype.ext (by
        show ((a * b : Subgroup.zpowers u) : G) * w.1 * ((a * b : Subgroup.zpowers u) : G)⁻¹ =
          (a : G) * ((b : G) * w.1 * (b : G)⁻¹) * (a : G)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group) }
  have hXcard : Nat.card X = Nat.card A := by
    rw [hX, Nat.card_image_of_injective (mul_right_injective a)]
    rfl
  have hodd' : ¬ 2 ∣ Nat.card X := by
    rw [hXcard]
    exact fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hVp : IsPGroup 2 ↥(Subgroup.zpowers u) := hu2
  obtain ⟨w₀, hw₀⟩ := hVp.nonempty_fixed_point_of_prime_not_dvd_card X hodd'
  obtain ⟨m, hm, hw⟩ := w₀.2
  have hfix : u * w₀.1 * u⁻¹ = w₀.1 :=
    congrArg Subtype.val (hw₀ ⟨u, Subgroup.mem_zpowers u⟩)
  have hmN : mk m = 1 := (QuotientGroup.eq_one_iff _).mpr hm.1
  refine ⟨a * m, J.mul_mem ha hm.2, ?_, ?_⟩
  · rw [map_mul, hmN, mul_one]
  · simp only at hw
    rw [← hw] at hfix
    calc a * m * u = u * (a * m) * u⁻¹ * u := by rw [hfix]
      _ = u * (a * m) := by group

theorem classicalClause_quot_odd (hΩ : HypOmegaGen Ω) (hcls : Q3CL.ClassicalClause Ω)
    (hN : Odd (Nat.card N)) : Q3CL.ClassicalClause (quotFamily Ω N) where
  subnormal := by
    rintro _ ⟨K, hK, rfl⟩
    obtain ⟨⟨z, hz⟩, -⟩ := hΩ.omega1 K hK
    have hz' := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K) hz
    refine ⟨QuotientGroup.mk' N z, hz'.mem,
      orderOf_eq_prime (by rw [pow_two]; exact hz'.sq) hz'.ne_one, ?_⟩
    refine AscQuot.isSubnormal_centralizer ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      rw [← map_mul, ← map_mul, hz.commute_of_mem hk]
    · intro c hc hne
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N c
      rw [← AscQuot.map_conjSub] at hne ⊢
      have hJ : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
      obtain ⟨h4, h4'⟩ := TwinEdge.Quot.omega4_quot_odd hΩ hN hK hJ (Ne.symm hne)
      have hzJ : QuotientGroup.mk' N z ∈ (conjSub g K).map (QuotientGroup.mk' N) := by
        have h1 : g * z * g⁻¹ ∈ conjSub g K := conj_mem_conjSub hz.mem
        refine ⟨g * z * g⁻¹, h1, ?_⟩
        rw [map_mul, map_mul, map_inv]
        rw [mul_inv_eq_iff_eq_mul]
        exact hc
      have hdvd : 2 ∣ Nat.card ↥(K.map (QuotientGroup.mk' N) ⊓
          (conjSub g K).map (QuotientGroup.mk' N)) := by
        have := Subgroup.orderOf_dvd_natCard
          (K.map (QuotientGroup.mk' N) ⊓ (conjSub g K).map (QuotientGroup.mk' N))
          (x := QuotientGroup.mk' N z) ⟨hz'.mem, hzJ⟩
        rwa [orderOf_eq_prime (by rw [pow_two]; exact hz'.sq) hz'.ne_one] at this
      have h1 := one_le_padicValNat_of_dvd Nat.card_pos.ne' hdvd
      exact (h4' (le_antisymm h4 h1)).trans inf_le_left
  commOdd := by
    rintro _ ⟨J, hJ, rfl⟩ ub ab bb hub hub2 hubb hab hbb hau hbu
    obtain ⟨u, huJ, hu, hu2⟩ := exists_isPGroup_lift_of_mem_map hub hub2
    obtain ⟨a0, ha0J, rfl⟩ := hab
    obtain ⟨b0, hb0J, rfl⟩ := hbb
    subst hu
    have huu : u * u ≠ 1 := fun h => hubb (by rw [← map_mul, h, map_one])
    obtain ⟨a1, ha1J, ha1, ha1c⟩ :=
      exists_commuting_lift (odd_natCard_inf hN J) huJ hu2 ha0J hau.symm
    obtain ⟨b1, hb1J, hb1, hb1c⟩ :=
      exists_commuting_lift (odd_natCard_inf hN J) huJ hu2 hb0J hbu.symm
    have hc := hcls.commOdd J hJ u a1 b1 huJ hu2 huu ha1J hb1J ha1c hb1c
    have hmem := Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hc
    rw [← oddCoreOf_map_mk_of_odd (odd_natCard_inf hN J)] at hmem
    simpa only [map_mul, map_inv, ha1, hb1] using hmem

theorem q8_quot_odd (hN : Odd (Nat.card N))
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2)) :
    ∀ L ∈ quotFamily Ω N, ∃ P : Subgroup (G ⧸ N),
      IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2) := by
  rintro _ ⟨K, hK, rfl⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hq8 K hK
  have hPN : P ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hP.2.1 hP.1 (odd_natCard_inf hN K)
  exact ⟨P.map (QuotientGroup.mk' N), isSylow2In_map_mk hN hP,
    ⟨(AscQuot.quotRestrictEquiv hPN).symm.trans e⟩⟩

theorem two_quot_odd (h2 : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (hN : Odd (Nat.card N)) :
    ∀ L ∈ quotFamily Ω N, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L) := by
  rintro _ ⟨K, hK, rfl⟩
  obtain ⟨e⟩ := AscQuot.nonempty_quotOddCoreEquiv (odd_natCard_inf hN K)
  exact (h2 K hK).of_equiv e

theorem oddQuotHypQ8 (hΩ : HypOmegaGen Ω) (hcls : Q3CL.ClassicalClause Ω)
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (hN : Odd (Nat.card N)) :
    HypOmegaGen (quotFamily Ω N) ∧ Q3CL.ClassicalClause (quotFamily Ω N) ∧
      (∀ L ∈ quotFamily Ω N, ∃ P : Subgroup (G ⧸ N),
        IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2)) :=
  ⟨TwinEdge.hypOmegaGen_quotFamily_odd hΩ hN, classicalClause_quot_odd hΩ hcls hN,
    q8_quot_odd hN hq8⟩

theorem aEmpty_quot_odd (hΩ : HypOmegaGen Ω) (hN : Odd (Nat.card N))
    (hA : ∀ J ∈ Ω, AEmpty Ω J) : ∀ M ∈ quotFamily Ω N, AEmpty (quotFamily Ω N) M :=
  TwinADescent2.aEmpty_quotFamily_gen hΩ (TwinEdge.hypOmegaGen_quotFamily_odd hΩ hN) hN hA

end Odd

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

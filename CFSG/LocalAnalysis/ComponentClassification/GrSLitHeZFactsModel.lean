module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGSGen

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.HeGS

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.GrSLit.HeldFix CFSG.ComponentClassification.UnbalancedGS

section Layer


theorem heK0_le_heP : heK0 ≤ heP := (gsFixedLayer_le_inf heP _).trans inf_le_left

theorem card_center_heK0 : Nat.card (center ↥heK0) = 4 := by
  have h : heZ0 = HeLay.rho0.ker.map (centralizerIn heP (heGenPerm 0)).subtype := by
    apply le_antisymm
    · intro z hz
      have hz' := hz
      rw [heZ0, LocalAnalysis.ComponentInitial.mem_map_center_iff] at hz'
      obtain ⟨hzK, hzc⟩ := hz'
      rcases eq_of_comm_heK0 (heK0_le_heP hzK) (fun k hk => (hzc k hk).symm) with
        rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact ⟨heGST0, heGST0_mem_ker, rfl⟩
      · exact ⟨heGSU, heGSU_mem_ker, rfl⟩
      · exact ⟨heGST0 * heGSU, mul_mem heGST0_mem_ker heGSU_mem_ker, rfl⟩
    · rintro _ ⟨k, hk, rfl⟩
      exact mem_heZ0_of_mem_ker hk
  have h1 : Nat.card heZ0 = Nat.card (center ↥heK0) :=
    card_map_of_injective heK0.subtype_injective
  rw [← h1, h, card_map_of_injective (subtype_injective _), HeLay.card_rho0_ker]

theorem le_heK0_of_perfect {S : Subgroup (Equiv.Perm (Fin 8330))}
    (hS : S ≤ centralizerIn heP (heGenPerm 0)) (hp : ⁅S, S⁆ = S) : S ≤ heK0 := by
  have hmap : (S.subgroupOf (centralizerIn heP (heGenPerm 0))).map
      (centralizerIn heP (heGenPerm 0)).subtype = S := by
    rw [subgroupOf_map_subtype, inf_of_le_left hS]
  have hp₀ : ⁅S.subgroupOf (centralizerIn heP (heGenPerm 0)),
      S.subgroupOf (centralizerIn heP (heGenPerm 0))⁆ =
      S.subgroupOf (centralizerIn heP (heGenPerm 0)) := by
    apply map_injective (centralizerIn heP (heGenPerm 0)).subtype_injective
    rw [map_commutator, hmap, hp]
  have hD : (S.subgroupOf (centralizerIn heP (heGenPerm 0))).map HeLay.rho0 ≤
      genGroup 105 heDGens heDPerm := by
    rw [← hp₀, map_commutator]
    exact (commutator_mono (map_le_range _ _) (map_le_range _ _)).trans
      HeLay.commutator_rho0_range_le
  intro x hx
  exact mem_heK0_of_rho0_mem (x := ⟨x, hS hx⟩) (hD (mem_map_of_mem _ (mem_subgroupOf.mpr hx)))

end Layer

section Sylow

theorem heT1P_mem_hfT : heT1P ∈ hfT := by
  have h := hfTL_mem_hfT (j := 0) (by norm_num)
  rwa [show hfTL 0 = heT1P by simp [hfTL]] at h


theorem comm_heT1P_of_mem_hfT {x : Equiv.Perm (Fin 8330)} (hx : x ∈ hfT) :
    x * heT1P = heT1P * x :=
  (mem_centralizerIn.mp ((hfT_le_grp1.trans heInnerGrp1_le) hx)).2

theorem exists_four_of_normal_hfT
    {N : Subgroup (Equiv.Perm (Fin 8330))} (hNT : N ≤ hfT) (hn : (N.subgroupOf hfT).Normal)
    (hN4 : 4 ≤ Nat.card N) :
    ∃ y₁ ∈ N, ∃ y₂ ∈ N, y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 ∧ y₁ ≠ 1 ∧ y₂ ≠ 1 ∧ y₁ ≠ y₂ ∧
      y₁ * y₂ = y₂ * y₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥hfT := IsPGroup.of_card (n := 10) (by rw [card_hfT]; norm_num)
  have : Group.IsNilpotent ↥hfT := hT2.isNilpotent
  have hN₀c : Nat.card (N.subgroupOf hfT) = Nat.card N :=
    Nat.card_congr (subgroupOfEquivOfLe hNT).toEquiv
  have hZc : Nat.card (center ↥hfT) = 2 := card_center_hfT
  set t : ↥hfT := ⟨heT1P, heT1P_mem_hfT⟩ with htdef
  have htZ : t ∈ center ↥hfT := mem_center_iff.mpr fun g =>
    Subtype.ext (comm_heT1P_of_mem_hfT g.2)
  have ht1 : t ≠ 1 := fun h => heT1P_ne_one (congrArg Subtype.val h)
  have hZ2 : ∀ c ∈ center ↥hfT, c = 1 ∨ c = t := by
    intro c hc
    by_contra h
    simp only [not_or] at h
    have hS : ({1, t, c} : Set ↥hfT) ⊆ (center ↥hfT : Set ↥hfT) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact one_mem _
      · exact htZ
      · exact hc
    have h3 : ({1, t, c} : Set ↥hfT).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_pair (Ne.symm h.2)]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ht1.symm, Ne.symm h.1⟩
    have h4 := Set.ncard_le_ncard hS (Set.toFinite _)
    rw [h3, ← Nat.card_coe_set_eq] at h4
    have h5 : Nat.card ↥(center ↥hfT : Set ↥hfT) = 2 := hZc
    omega
  have hN₀ne : N.subgroupOf hfT ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hN₀c
    omega
  have : (N.subgroupOf hfT).Normal := hn
  have htN : t ∈ N.subgroupOf hfT := by
    obtain ⟨⟨c, hc⟩, hc1⟩ := (ne_bot_iff_exists_ne_one).mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hN₀ne)
    obtain ⟨hcN, hcZ⟩ := mem_inf.mp hc
    rcases hZ2 c hcZ with rfl | rfl
    · exact absurd rfl hc1
    · exact hcN
  have hQ2 : IsPGroup 2 (↥hfT ⧸ center ↥hfT) := hT2.to_quotient (center ↥hfT)
  have : Group.IsNilpotent (↥hfT ⧸ center ↥hfT) := hQ2.isNilpotent
  have : ((N.subgroupOf hfT).map (QuotientGroup.mk' (center ↥hfT))).Normal :=
    hn.map _ (QuotientGroup.mk'_surjective _)
  have hNπ : (N.subgroupOf hfT).map (QuotientGroup.mk' (center ↥hfT)) ≠ ⊥ := by
    intro h
    have hle : N.subgroupOf hfT ≤ center ↥hfT := by
      intro x hx
      have hx' : QuotientGroup.mk' (center ↥hfT) x ∈
          (N.subgroupOf hfT).map (QuotientGroup.mk' (center ↥hfT)) := mem_map_of_mem _ hx
      rw [h, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
      exact hx'
    have := card_le_of_le hle
    omega
  obtain ⟨⟨q, hq⟩, hq1⟩ := (ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hNπ)
  obtain ⟨hqN, hqZ⟩ := mem_inf.mp hq
  obtain ⟨x, hxN, rfl⟩ := hqN
  have hxZ : x ∉ center ↥hfT := fun h => hq1 (Subtype.ext (by
    show QuotientGroup.mk' (center ↥hfT) x = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h))
  have hcomm : ∀ g : ↥hfT, x * g = g * x ∨ x * g = t * (g * x) := by
    intro g
    have h1 := mem_center_iff.mp hqZ (QuotientGroup.mk' (center ↥hfT) g)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h1
    have e : x * g = g * x * ((g * x)⁻¹ * (x * g)) := by group
    rcases hZ2 _ h1 with h | h
    · left
      rw [e, h, mul_one]
    · right
      rw [e, h]
      exact (mem_center_iff.mp htZ (g * x))
  have hx2 : (x : Equiv.Perm (Fin 8330)) * x = 1 := by
    apply sq_eq_one_of_comm_mod x.2
    intro j hj
    rcases hcomm ⟨hfTL j, hfTL_mem_hfT hj⟩ with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  refine ⟨x, mem_subgroupOf.mp hxN, heT1P, mem_subgroupOf.mp htN, hx2, heT1P_sq, ?_,
    heT1P_ne_one, ?_, comm_heT1P_of_mem_hfT x.2⟩
  · intro h
    apply hxZ
    rw [show x = 1 from Subtype.ext h]
    exact one_mem _
  · intro h
    apply hxZ
    rw [show x = t from Subtype.ext h]
    exact htZ

end Sylow

end CFSG.ComponentClassification.GrSLit.HeGS

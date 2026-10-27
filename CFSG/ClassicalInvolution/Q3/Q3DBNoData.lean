module

public import CFSG.ClassicalInvolution.Q3.Q3DBMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3DB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Uniform


section Lift

variable {G : Type} [Group G]

theorem mem_conjClass_conjSub {K M : Subgroup G} (hM : M ∈ CoreAssembly.conjClass K) (g : G) :
    conjSub g M ∈ CoreAssembly.conjClass K := by
  obtain ⟨x, hx⟩ := hM
  have hx' : conjSub x K = M := hx
  exact ⟨g * x, by rw [← hx']; exact conjSub_mul g x K⟩

theorem omegaConnected_of_le {K K' : Subgroup G} (hle : K ≤ K')
    (h : OmegaConnected (CoreAssembly.conjClass K'))
    (hex : ∃ P ∈ CoreAssembly.conjClass K', Commutes K' P) :
    OmegaConnected (CoreAssembly.conjClass K) := by
  have lift : ∀ {x y : G}, Commutes (conjSub x K') (conjSub y K') →
      Commutes (conjSub x K) (conjSub y K) := fun hxy p hp q hq =>
    hxy p (conjSub_mono hle hp) q (conjSub_mono hle hq)
  have mem : ∀ y : G, conjSub y K ∈ CoreAssembly.conjClass K := fun y => ⟨y, rfl⟩
  have key : ∀ A B : Subgroup G, Relation.ReflTransGen
      (fun M N : Subgroup G => N ∈ CoreAssembly.conjClass K' ∧ Commutes M N) A B → A ≠ B →
      ∀ x y : G, conjSub x K' = A → conjSub y K' = B →
        Relation.ReflTransGen (fun M N : Subgroup G =>
          N ∈ CoreAssembly.conjClass K ∧ Commutes M N) (conjSub x K) (conjSub y K) := by
    intro A B hAB
    induction hAB with
    | refl => exact fun hne => absurd rfl hne
    | @tail b c hAb hbc ih =>
      intro _ x y hx hy
      by_cases hAb' : A = b
      · subst hAb'
        refine Relation.ReflTransGen.single ⟨mem y, lift ?_⟩
        rw [hx, hy]
        exact hbc.2
      · have hbmem : b ∈ CoreAssembly.conjClass K' := by
          rcases hAb.cases_tail with h1 | ⟨c', -, hc'⟩
          · exact absurd h1.symm hAb'
          · exact hc'.1
        obtain ⟨y', hy'⟩ := hbmem
        have hy'' : conjSub y' K' = b := hy'
        refine (ih hAb' x y' hx hy'').tail ⟨mem y, lift ?_⟩
        rw [hy'', hy]
        exact hbc.2
  intro L hL L' hL'
  obtain ⟨g, hg⟩ := hL
  obtain ⟨g', hg'⟩ := hL'
  have hg1 : conjSub g K = L := hg
  have hg2 : conjSub g' K = L' := hg'
  rw [← hg1, ← hg2]
  by_cases hQ : conjSub g K' = conjSub g' K'
  · obtain ⟨P, ⟨p, hp⟩, hP⟩ := hex
    have hp' : conjSub p K' = P := hp
    have h1 : Commutes (conjSub g K') (conjSub (g * p) K') := by
      rw [conjSub_mul, hp']
      exact hP.conjSub g
    refine (Relation.ReflTransGen.single ⟨mem (g * p), lift h1⟩).tail ⟨mem g', lift ?_⟩
    rw [← hQ]
    exact h1.symm
  · exact key _ _ (h _ ⟨g, rfl⟩ _ ⟨g', rfl⟩) hQ g g' rfl rfl

end Lift

section TypeC

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem commute_involutions_of_mem_omegaNbr (hK : IsClassicalMember3 K z)
    (hint : IsIntrinsicU (.sl2 3 1) K z) {M N : Subgroup G}
    (hN : N ∈ omegaNbr (CoreAssembly.conjClass K) M) {a u : G} (ha : IsClassicalMember3 M a)
    (hu : IsClassicalMember3 N u) : a * u = u * a := by
  obtain ⟨h1, -⟩ := fuzzy_of_mem_omegaNbr hK hint hN ha
  have hUN : IsUniqueInvolution N u :=
    (IsClassicalMemberU.ofQ3 hu).isUniqueInvolution (MemberType.cert_sl2 3 1)
  have h2 := hUN.conj_eq h1
  calc a * u = (a * u * a⁻¹) * a := by group
    _ = u * a := by rw [h2]

theorem commutes_of_not_a2 (hK : IsClassicalMember3 K z) (hA2 : ¬ A2Configuration z K)
    {M N : Subgroup G} (hM : M ∈ CoreAssembly.conjClass K) (hN : N ∈ CoreAssembly.conjClass K)
    {a u : G} (ha : IsClassicalMember3 M a) (hu : IsClassicalMember3 N u) (hne : a ≠ u)
    (hcomm : a * u = u * a) : Commutes M N := by
  by_contra hnc
  obtain ⟨g, hg⟩ := hM
  obtain ⟨h, hh⟩ := hN
  have hg' : conjSub g K = M := hg
  have hh' : conjSub h K = N := hh
  have hag : a = g * z * g⁻¹ := involution_unique3 ha (hg' ▸ hK.conj g)
  have hug : u = h * z * h⁻¹ := involution_unique3 hu (hh' ▸ hK.conj h)
  refine hA2 ⟨g⁻¹, h⁻¹, ?_, ?_, ?_, ?_⟩ <;> simp only [inv_inv]
  · intro h'
    have h'' : conjSub g K = conjSub h K := h'
    exact hne (involution_unique3 ha (show IsClassicalMember3 M u by
      rw [← hg', h'', hh']; exact hu))
  · intro h'
    exact hne (hag.trans (h'.trans hug.symm))
  · rw [← hag, ← hug]
    exact hcomm
  · rw [← hg', ← hh'] at hnc
    exact hnc

theorem exists_distinct_commuting_involutions [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (hK : IsClassicalMember3 K z) (hint : IsIntrinsicU (.sl2 3 1) K z)
    (hD : DConnected (CoreAssembly.conjClass K)) :
    ∃ (M N : Subgroup G) (a u : G), M ∈ CoreAssembly.conjClass K ∧
      N ∈ CoreAssembly.conjClass K ∧ IsClassicalMember3 M a ∧ IsClassicalMember3 N u ∧
        a ≠ u ∧ a * u = u * a := by
  by_contra hno
  have key : ∀ X, Relation.ReflTransGen (fun M N : Subgroup G =>
      N ∈ CoreAssembly.conjClass K ∧ dAdj (CoreAssembly.conjClass K) M N) K X →
      X ∈ CoreAssembly.conjClass K ∧ IsClassicalMember3 X z := by
    intro X hX
    induction hX with
    | refl => exact ⟨CoreAssembly.mem_conjClass_self K, hK⟩
    | @tail b c _ hbc ih =>
      obtain ⟨u, hu⟩ := exists_involution_of_mem_class hK hbc.1
      refine ⟨hbc.1, ?_⟩
      have hcomm : z * u = u * z := by
        rcases hbc.2 with h | h
        · exact commute_involutions_of_mem_omegaNbr hK hint h ih.2 hu
        · exact (commute_involutions_of_mem_omegaNbr hK hint h hu ih.2).symm
      have hzu : z = u := by
        by_contra hne
        exact hno ⟨b, c, z, u, ih.1, hbc.1, ih.2, hu, hne, hcomm⟩
      rwa [hzu]
  have hcen : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨-, hz⟩ := key (conjSub g K) (hD K (CoreAssembly.mem_conjClass_self K) _ ⟨g, rfl⟩)
    have hgz : g * z * g⁻¹ = z := involution_unique3 (hK.conj g) hz
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [hgz]
  rw [CoreAssembly.center_eq_bot hnab, Subgroup.mem_bot] at hcen
  exact hK.ne_one hcen

theorem exists_member_commuting_involution_ne [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) (hK : IsClassicalMember3 K z)
    (hint : IsIntrinsicU (.sl2 3 1) K z) (hD : DConnected (CoreAssembly.conjClass K))
    {P : Subgroup G} (hP : P ∈ CoreAssembly.conjClass K) {a : G} (ha : IsClassicalMember3 P a) :
    ∃ (J : Subgroup G) (t : G), J ∈ CoreAssembly.conjClass K ∧ IsClassicalMember3 J t ∧
      t ≠ a ∧ a * t = t * a := by
  obtain ⟨M₁, N₁, a₁, u₁, hM₁, hN₁, ha₁, hu₁, hne₁, hc₁⟩ :=
    exists_distinct_commuting_involutions hnab hK hint hD
  obtain ⟨x, hx⟩ := hP
  obtain ⟨y, hy⟩ := hM₁
  have hx' : conjSub x K = P := hx
  have hy' : conjSub y K = M₁ := hy
  have hax : a = x * z * x⁻¹ := involution_unique3 ha (hx' ▸ hK.conj x)
  have ha₁y : a₁ = y * z * y⁻¹ := involution_unique3 ha₁ (hy' ▸ hK.conj y)
  have hagc : x * y⁻¹ * a₁ * (x * y⁻¹)⁻¹ = a := by
    rw [hax, ha₁y]
    group
  refine ⟨conjSub (x * y⁻¹) N₁, x * y⁻¹ * u₁ * (x * y⁻¹)⁻¹, mem_conjClass_conjSub hN₁ _,
    hu₁.conj _, ?_, ?_⟩
  · intro h'
    apply hne₁
    have h2 : x * y⁻¹ * u₁ * (x * y⁻¹)⁻¹ = x * y⁻¹ * a₁ * (x * y⁻¹)⁻¹ := h'.trans hagc.symm
    exact (mul_left_cancel (mul_right_cancel h2)).symm
  · rw [← hagc]
    calc x * y⁻¹ * a₁ * (x * y⁻¹)⁻¹ * (x * y⁻¹ * u₁ * (x * y⁻¹)⁻¹)
        = x * y⁻¹ * (a₁ * u₁) * (x * y⁻¹)⁻¹ := by group
      _ = x * y⁻¹ * (u₁ * a₁) * (x * y⁻¹)⁻¹ := by rw [hc₁]
      _ = x * y⁻¹ * u₁ * (x * y⁻¹)⁻¹ * (x * y⁻¹ * a₁ * (x * y⁻¹)⁻¹) := by group

theorem omegaConnected_of_dConnected_of_not_a2 [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) (hK : IsClassicalMember3 K z)
    (hint : IsIntrinsicU (.sl2 3 1) K z) (hA2 : ¬ A2Configuration z K)
    (hD : DConnected (CoreAssembly.conjClass K)) : OmegaConnected (CoreAssembly.conjClass K) := by
  intro L hL L' hL'
  have key : ∀ X, Relation.ReflTransGen (fun M N : Subgroup G =>
      N ∈ CoreAssembly.conjClass K ∧ dAdj (CoreAssembly.conjClass K) M N) L X →
      X ∈ CoreAssembly.conjClass K ∧ Relation.ReflTransGen
        (fun M N : Subgroup G => N ∈ CoreAssembly.conjClass K ∧ Commutes M N) L X := by
    intro X hX
    induction hX with
    | refl => exact ⟨hL, Relation.ReflTransGen.refl⟩
    | @tail b c _ hbc ih =>
      refine ⟨hbc.1, ?_⟩
      obtain ⟨ab, hab⟩ := exists_involution_of_mem_class hK ih.1
      obtain ⟨ac, hac⟩ := exists_involution_of_mem_class hK hbc.1
      have hcomm : ab * ac = ac * ab := by
        rcases hbc.2 with h | h
        · exact commute_involutions_of_mem_omegaNbr hK hint h hab hac
        · exact (commute_involutions_of_mem_omegaNbr hK hint h hac hab).symm
      by_cases hne : ab = ac
      · obtain ⟨J, t, hJ, hJt, hta, hcomm'⟩ :=
          exists_member_commuting_involution_ne hnab hK hint hD ih.1 hab
        have h1 : Commutes b J := commutes_of_not_a2 hK hA2 ih.1 hJ hab hJt (Ne.symm hta) hcomm'
        have h2 : Commutes J c := (commutes_of_not_a2 hK hA2 hbc.1 hJ hac hJt
          (by rw [← hne]; exact Ne.symm hta) (by rw [← hne]; exact hcomm')).symm
        exact (ih.2.tail ⟨hJ, h1⟩).tail ⟨hbc.1, h2⟩
      · exact ih.2.tail ⟨hbc.1, commutes_of_not_a2 hK hA2 ih.1 hbc.1 hab hac hne hcomm⟩
  exact (key L' (hD L hL L' hL')).2

theorem exists_commuting_partner_of_not_a2 [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) (hK : IsClassicalMember3 K z)
    (hint : IsIntrinsicU (.sl2 3 1) K z) (hA2 : ¬ A2Configuration z K)
    (hD : DConnected (CoreAssembly.conjClass K)) :
    ∃ P ∈ CoreAssembly.conjClass K, Commutes K P := by
  obtain ⟨M, N, a, u, hM, hN, ha, hu, hne, hcomm⟩ :=
    exists_distinct_commuting_involutions hnab hK hint hD
  have hMN := commutes_of_not_a2 hK hA2 hM hN ha hu hne hcomm
  obtain ⟨x, hx⟩ := hM
  have hx' : conjSub x K = M := hx
  refine ⟨conjSub x⁻¹ N, mem_conjClass_conjSub hN x⁻¹, ?_⟩
  have h1 := hMN.conjSub x⁻¹
  rwa [← hx', conjSub_inv_conjSub] at h1

theorem deltaConnected_of_dConnected_sat_of_not_a2 [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) (hz : IsClassicalMemberU (.sl2 3 1) K z)
    (hA2 : ¬ A2Configuration z (satU (.sl2 3 1) K z))
    (hD : DConnected (CoreAssembly.conjClass (satU (.sl2 3 1) K z))) :
    CFSG.ClassicalInvolution.DeltaConnected K := by
  have hS : IsClassicalMember3 (satU (.sl2 3 1) K z) z := (hz.satU_member).toQ3 (by norm_num)
  have hint := isIntrinsicU_satU (.sl2 3 1) K z
  exact deltaConnected_of_omegaConnected
    (omegaConnected_of_le le_satU (omegaConnected_of_dConnected_of_not_a2 hnab hS hint hA2 hD)
      (exists_commuting_partner_of_not_a2 hnab hS hint hA2 hD))

end TypeC

@[expose] def NoDataA2D3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMemberU (.sl2 3 1) K z →
      CITBelowT (.sl2 3 1) (Nat.card G) → 3 ≤ CFSG.Open.twoRank G →
      ¬ TwoSubgroupsFourGenerated G →
      DConnected (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) →
      ¬ BootData3 (conjClass3 (satU (.sl2 3 1) K z)) →
      A2Configuration z (satU (.sl2 3 1) K z) →
      CFSG.ClassicalInvolution.DeltaConnected K

theorem noDataD3_of_noDataA2D3 (h : NoDataA2D3) : NoDataD3 :=
  fun G _ _ _ hnab K z hz hBelow hr hlarge hD hdata => by
    by_cases hA2 : A2Configuration z (satU (.sl2 3 1) K z)
    · exact h G hnab K z hz hBelow hr hlarge hD hdata hA2
    · exact deltaConnected_of_dConnected_sat_of_not_a2 hnab hz hA2 hD

theorem dBridgeU_three_of_ED_A2 (h1 : BootTriple3ED) (h2 : BootNoTriple3ED) (h3 : NoDataA2D3) :
    DBridgeU 3 1 :=
  dBridgeU_three_of_ED h1 h2 (noDataD3_of_noDataA2D3 h3)

@[expose] def SmallA2EmptyD3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMemberU (.sl2 3 1) K z →
      CITBelowT (.sl2 3 1) (Nat.card G) → 3 ≤ CFSG.Open.twoRank G →
      ¬ TwoSubgroupsFourGenerated G →
      DConnected (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) →
      A2Configuration z (satU (.sl2 3 1) K z) →
      BootData3 (conjClass3 (satU (.sl2 3 1) K z))

theorem noDataA2D3_of_smallA2EmptyD3 (h : SmallA2EmptyD3) : NoDataA2D3 :=
  fun G _ _ _ hnab K z hz hBelow hr hlarge hD hdata hA2 =>
    absurd (h G hnab K z hz hBelow hr hlarge hD hA2) hdata

end CFSG.ClassicalInvolution.Q3.Q3DB

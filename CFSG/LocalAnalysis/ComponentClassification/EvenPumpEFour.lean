module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpETwo
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpEA10
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpHNMain
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Main

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup SemidirectProduct CFSG.ComponentClassification.UnbalancedLayer

theorem centralizer_subgroupOf_singleton {Y : Type*} [Group Y] (X : Subgroup Y) (x : X) :
    centralizer ({x} : Set X) = (centralizer ({(x : Y)} : Set Y)).subgroupOf X := by
  ext y
  rw [mem_subgroupOf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem sq_eq_one_of_mem_zpowers {G : Type*} [Group G] {x e : G} (hx : orderOf x = 2)
    (he : e ∈ zpowers x) : e ^ 2 = 1 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx, pow_orderOf_eq_one,
    one_zpow]

theorem eq_or_eq_of_card_four {G : Type*} [Group G] [Finite G] (hc : Nat.card G = 4)
    (h2 : ∀ g : G, g * g = 1) {q₁ q₂ : G} (h1 : q₁ ≠ 1) (h12 : q₂ ≠ 1) (h21 : q₂ ≠ q₁) :
    ∀ r : G, r = 1 ∨ r = q₁ ∨ r = q₂ ∨ r = q₁ * q₂ := by
  classical
  have : Fintype G := Fintype.ofFinite G
  by_contra hcon
  push Not at hcon
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ := hcon
  have hq : q₁ * q₂ ≠ 1 := fun h => h21 (by rw [← mul_eq_one_iff_inv_eq.mp h,
    inv_eq_of_mul_eq_one_right (h2 q₁)])
  have hq1 : q₁ * q₂ ≠ q₁ := fun h => h12 (mul_eq_left.mp h)
  have hq2 : q₁ * q₂ ≠ q₂ := fun h => h1 (mul_eq_right.mp h)
  have hcard : ({1, q₁, q₂, q₁ * q₂, r} : Finset G).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [h1.symm, h12.symm, hq.symm, hr1.symm]),
      Finset.card_insert_of_notMem (by simp [h21.symm, hq1.symm, hr2.symm]),
      Finset.card_insert_of_notMem (by simp [hq2.symm, hr3.symm]),
      Finset.card_insert_of_notMem (by simp [hr4.symm]), Finset.card_singleton]
  have hle := Finset.card_le_univ ({1, q₁, q₂, q₁ * q₂, r} : Finset G)
  rw [hcard, Fintype.card_eq_nat_card, hc] at hle
  omega

theorem evenAltAut_le_four (hcore : EvenAltPumpInput) (hHN : HNPumpInput) (hA10 : A10PumpInput)
    {L : Type} [Group L] [Finite L] (hK : SectionRank.IsKGroupCat L) (hq : IsQuasisimple L)
    (hO : pPrimeCore 2 L = ⊥) {Q : Subgroup (MulAut L)} (hQ2 : ∀ q ∈ Q, q * q = 1)
    (hQc : Nat.card Q ≤ 4) {T : Subgroup L} (hTF : T ≤ autFixed Q)
    (hT : IsPComponent 2 (T.subgroupOf (autFixed Q)))
    (eT : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin 10)) :
    (∃ n : ℕ, 10 ≤ n ∧ Nonempty (L ≃* alternatingGroup (Fin n))) ∨
      Nonempty (L ⧸ center L ≃* Blueprint.NativeSporadic.Carrier .HN) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 Q := isPGroup_of_mul_self hQ2
  have : Finite (MulAut L) := Finite.of_injective (fun e : MulAut L => e.toEquiv)
    fun _ _ h => MulEquiv.ext fun x => congrArg (fun f : L ≃ L => f x) h
  by_cases hQ2c : Nat.card Q ≤ 2
  · rcases evenAltAut_le_two hcore hK hq hO hQ2 hQ2c hTF hT eT with ⟨n, -, hn, he⟩ | he
    · exact Or.inl ⟨n, hn, he⟩
    · exact Or.inr he
  have hQ4 : Nat.card Q = 4 := by
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    have hk2 : k ≤ 2 := by
      by_contra h
      have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
    · omega
    · omega
    · exact hk
  have : Fintype ↥Q := Fintype.ofFinite _
  obtain ⟨q₁, hq₁⟩ : ∃ q₁ : ↥Q, q₁ ≠ 1 := by
    by_contra h
    push Not at h
    have h1 : Nat.card Q = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩
    omega
  obtain ⟨q₂, hq₂1, hq₂q₁⟩ : ∃ q₂ : ↥Q, q₂ ≠ 1 ∧ q₂ ≠ q₁ := by
    by_contra h
    push Not at h
    have h1 : (Finset.univ : Finset ↥Q) ⊆ {1, q₁} := fun r _ => by
      by_cases hr : r = 1
      · simp [hr]
      · simp [h r hr]
    have h2 := Finset.card_le_card h1
    rw [Finset.card_univ, Fintype.card_eq_nat_card, hQ4] at h2
    have h3 : ({1, q₁} : Finset ↥Q).card ≤ 2 := Finset.card_le_two
    omega
  have hsq : ∀ r : ↥Q, r * r = 1 := fun r => Subtype.ext (hQ2 r r.2)
  have hall := eq_or_eq_of_card_four hQ4 hsq hq₁ hq₂1 hq₂q₁
  have hinv : ∀ r : ↥Q, r⁻¹ = r := fun r => inv_eq_of_mul_eq_one_right (hsq r)
  have hcomm12 : q₁ * q₂ = q₂ * q₁ := by
    calc q₁ * q₂ = (q₁ * q₂)⁻¹ := (hinv _).symm
      _ = q₂ * q₁ := by rw [mul_inv_rev, hinv, hinv]
  have := finite_pumpY Q
  set x₁ : PumpY Q := inr q₁ with hx₁def
  set x₂ : PumpY Q := inr q₂ with hx₂def
  have hx₁ : orderOf x₁ = 2 := orderOf_inr Q (hQ2 _ q₁.2) fun h => hq₁ (Subtype.ext h)
  have hx₁₂ : x₁ * x₂ = x₂ * x₁ := by rw [hx₁def, hx₂def, ← map_mul, ← map_mul, hcomm12]
  have hC : centralizer (((inr : ↥Q →* PumpY Q).range : Subgroup (PumpY Q)) : Set (PumpY Q)) =
      centralizer ({x₁} : Set (PumpY Q)) ⊓ centralizer ({x₂} : Set (PumpY Q)) := by
    apply le_antisymm
    · exact le_inf (centralizer_le (Set.singleton_subset_iff.mpr ⟨q₁, rfl⟩))
        (centralizer_le (Set.singleton_subset_iff.mpr ⟨q₂, rfl⟩))
    · rintro c ⟨hc₁, hc₂⟩
      have h₁ := mem_centralizer_iff.mp hc₁ x₁ rfl
      have h₂ := mem_centralizer_iff.mp hc₂ x₂ rfl
      rw [mem_centralizer_iff]
      rintro _ ⟨r, rfl⟩
      rcases hall r with rfl | rfl | rfl | rfl
      · rw [map_one, one_mul, mul_one]
      · exact h₁
      · exact h₂
      · rw [map_mul, mul_assoc, ← hx₂def, h₂, ← mul_assoc, ← hx₁def, h₁, mul_assoc]
  obtain ⟨hT'C, hT'pc⟩ := isPComponent_centralizer_range Q hTF hT
  rw [hC] at hT'C hT'pc
  set T' := T.map (inl : L →* PumpY Q) with hT'def
  set X := centralizer ({x₁} : Set (PumpY Q)) with hXdef
  have hx₂X : x₂ ∈ X := mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff.mp hh]
    exact hx₁₂
  set y₂ : ↥X := ⟨x₂, hx₂X⟩ with hy₂def
  have hy₂ : orderOf y₂ = 2 := by
    rw [hy₂def, Subgroup.orderOf_mk]
    exact orderOf_inr Q (hQ2 _ q₂.2) fun h => hq₂1 (Subtype.ext h)
  set TX := T'.subgroupOf X with hTXdef
  have hTXC : TX ≤ centralizer ({y₂} : Set ↥X) := by
    rw [centralizer_subgroupOf_singleton]
    intro t ht
    rw [mem_subgroupOf] at ht ⊢
    exact (hT'C ht).2
  have hTXpc : IsPComponent 2 (TX.subgroupOf (centralizer ({y₂} : Set ↥X))) := by
    rw [centralizer_subgroupOf_singleton, ← inf_subgroupOf_left]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two).mpr hT'pc
  have hTXL := CatLeaf.le_pLayer_of_isPComponent_centralizer hy₂ hTXC hTXpc
  obtain ⟨J, hJ, hTJ, hTJpc⟩ := two_layer_fixed_component_orbit_location hy₂ hTXC hTXpc hTXL
  let eTT' : ↥T ≃* ↥T' := T.equivMapOfInjective inl inl_injective
  have hT'X : T' ≤ X := fun t ht => (hT'C ht).1
  let eTXT' : ↥TX ≃* ↥T' := subgroupOfEquivOfLe hT'X
  let eTXq : ↥TX ⧸ pPrimeCore 2 ↥TX ≃* alternatingGroup (Fin 10) :=
    (Sol78.coreQuotCongr (eTXT'.trans eTT'.symm)).trans eT
  have hTXZ : Open.fusionZStar ↥TX = pPrimeCore 2 ↥TX := fusionZStar_eq_of_alt (by norm_num) eTXq
  let eTXZ : ↥TX ⧸ Open.fusionZStar ↥TX ≃* alternatingGroup (Fin 10) :=
    (QuotientGroup.quotientMulEquivOfEq hTXZ).trans eTXq
  have hKY := isKGroupCat_pumpY Q hK hQ
  have hKX : SectionRank.IsKGroupCat ↥X := hKY.subgroup X
  have hMY := isPComponent_pumpL Q hq hO
  set J' := J.map X.subtype with hJ'def
  have hJ'X : J' ≤ X := map_subtype_le J
  have hJ'pc : IsPComponent 2 (J'.subgroupOf X) := by
    rw [show J'.subgroupOf X = J from comap_map_eq_self_of_injective X.subtype_injective J]
    exact hJ
  have : Group.IsPerfect ↥J := CatalogueBHeldSmallCore.pComponent_perfect 2 J hJ
  let eJJ' : ↥J ≃* ↥J' := J.equivMapOfInjective X.subtype X.subtype_injective
  have : Group.IsPerfect ↥J' := Group.IsPerfect.ofSurjective (f := eJJ'.toMonoidHom)
    eJJ'.surjective
  have hJ'M : J' ≤ pumpL Q := le_pumpL_of_isPerfect Q hQ J'
  have hx₁N : x₁ ∈ normalizer ((pumpL Q : Subgroup (PumpY Q)) : Set (PumpY Q)) := by
    have := pumpL_normal Q
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact mem_top _
  obtain ⟨eJZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' eJJ'.symm
  have hout : (∃ n : ℕ, 10 ≤ n ∧ Nonempty (↥(pumpL Q) ⧸ Open.fusionZStar ↥(pumpL Q) ≃*
      alternatingGroup (Fin n))) ∨ Nonempty (↥(pumpL Q) ⧸ Open.fusionZStar ↥(pumpL Q) ≃*
        Blueprint.NativeSporadic.Carrier .HN) := by
    by_cases hstab : J = conjugate J y₂
    ·
      have hTXJ : TX ≤ J := by
        rw [← hstab, sup_idem] at hTJ
        exact hTJ
      have hy₂N : y₂ ∈ normalizer (J : Set ↥X) := by
        have h1 := inv_mem (mem_normalizer_iff_map_conj_eq.mpr hstab.symm)
        rwa [inv_inv] at h1
      have hz2 : IsPGroup 2 (zpowers y₂) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy₂, pow_one])
      have hzK : ∀ e ∈ zpowers y₂, e ^ 2 ∈ coreActionKernel J := fun e he => by
        rw [sq_eq_one_of_mem_zpowers hy₂ he]
        exact one_mem _
      have hzc : Nat.card (zpowers y₂) ≤ 2 * Nat.card ↥(zpowers y₂ ⊓ coreActionKernel J) := by
        rw [Nat.card_zpowers, hy₂]
        have := Nat.card_pos (α := ↥(zpowers y₂ ⊓ coreActionKernel J))
        omega
      have hTXz : TX ≤ centralizer ((zpowers y₂ : Subgroup ↥X) : Set ↥X) := by
        rw [centralizer_zpowers_eq]
        exact hTXC
      have hTXzpc : IsPComponent 2 (TX.subgroupOf
          (centralizer ((zpowers y₂ : Subgroup ↥X) : Set ↥X))) := by
        rw [centralizer_zpowers_eq]
        exact hTXpc
      rcases evenAltPumpUpTwo_of_core hcore ↥X hKX J hJ (zpowers y₂) hz2 (zpowers_le.mpr hy₂N)
          hzK hzc TX hTXJ hTXz hTXzpc ⟨eTXq⟩ with ⟨n₁, hn₁, h10, ⟨eJ⟩⟩ | ⟨⟨eJ⟩⟩
      · let eJ'q : ↥J' ⧸ pPrimeCore 2 ↥J' ≃* alternatingGroup (Fin n₁) :=
          (Sol78.coreQuotCongr eJJ').symm.trans eJ
        have hJ'Z := fusionZStar_eq_of_alt (by omega) eJ'q
        have hex : (Open.fusionZStar ↥J').map J'.subtype ≤ (pPrimeCore 2 ↥J').map J'.subtype ⊔
            (Open.fusionZStar ↥(pumpL Q)).map (pumpL Q).subtype := by
          rw [hJ'Z]
          exact le_sup_left
        rcases hcore (PumpY Q) hKY (pumpL Q) hMY x₁ hx₁ hx₁N J' hJ'M hJ'X hJ'pc hex n₁ hn₁ h10
            ⟨(QuotientGroup.quotientMulEquivOfEq hJ'Z).trans eJ'q⟩ with
          ⟨m', -, hm', ⟨eM⟩⟩ | ⟨-, ⟨eM⟩⟩
        · exact Or.inl ⟨m', h10.trans hm', ⟨eM⟩⟩
        · exact Or.inr ⟨eM⟩
      · exact Or.inr (hHN (PumpY Q) hKY (pumpL Q) hMY x₁ hx₁ hx₁N J' hJ'M hJ'X hJ'pc
          ⟨eJZ.trans eJ⟩)
    ·
      obtain ⟨eS⟩ := CatLeaf.swap_case_type hy₂ J hJ hstab TX (le_inf hTJ hTXC) hTJpc
      exact hA10 (PumpY Q) hKY (pumpL Q) hMY x₁ hx₁ hx₁N J' hJ'M hJ'X hJ'pc
        ⟨eJZ.trans (eS.symm.trans eTXZ)⟩
  obtain ⟨eP⟩ := nonempty_pumpL_fusionZStar_equiv Q hO
  rcases hout with ⟨n, hn, ⟨eM⟩⟩ | ⟨⟨eM⟩⟩
  · let eLZ : L ⧸ center L ≃* alternatingGroup (Fin n) := eP.symm.trans eM
    have hZ := center_eq_bot_of_autFixed_alt hq (by omega) eLZ hQ hTF hT eT
    exact Or.inl ⟨n, hn, ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).symm.trans eLZ⟩⟩
  · exact Or.inr ⟨eP.symm.trans eM⟩

end CFSG.ComponentClassification.EvenPump

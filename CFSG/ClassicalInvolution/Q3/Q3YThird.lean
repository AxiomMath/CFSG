module

public import CFSG.ClassicalInvolution.Q3.Q3YComp
public import CFSG.ClassicalInvolution.Q3.Q3YQuat
public import CFSG.ClassicalInvolution.Q3.Q3YLink

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Y

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.ClassicalInvolution.Balance (oddCoreIn odd_card_oddCoreIn oddCoreIn_le)

section Third

variable {G : Type} [Group G] [Finite G]

theorem mk_involutions_ne {X : Subgroup G} {z₁ z₂ : G} (hz₁X : z₁ ∈ X) (hz₂X : z₂ ∈ X)
    (hz1sq : z₁ * z₁ = 1) (hz2sq : z₂ * z₂ = 1) (hz12 : z₁ * z₂ = z₂ * z₁) (hne : z₁ ≠ z₂) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨z₁, hz₁X⟩ ≠
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨z₂, hz₂X⟩ := by
  intro h
  have hz3X : z₁ * z₂ ∈ X := X.mul_mem hz₁X hz₂X
  have hz3sq : (z₁ * z₂) * (z₁ * z₂) = 1 := by
    calc (z₁ * z₂) * (z₁ * z₂) = z₁ * (z₂ * z₁) * z₂ := by group
      _ = z₁ * (z₁ * z₂) * z₂ := by rw [← hz12]
      _ = (z₁ * z₁) * (z₂ * z₂) := by group
      _ = 1 := by rw [hz1sq, hz2sq, one_mul]
  have hz3ne : z₁ * z₂ ≠ 1 := by
    intro h1
    exact hne (by
      have := eq_inv_of_mul_eq_one_left h1
      rw [this, inv_eq_of_mul_eq_one_right hz2sq])
  refine mk_ne_one_of_involution X hz3X hz3sq hz3ne ?_
  have : (⟨z₁ * z₂, hz3X⟩ : ↥X) = ⟨z₁, hz₁X⟩ * ⟨z₂, hz₂X⟩ := rfl
  rw [this, map_mul, h]
  have hsq2 : (⟨z₂, hz₂X⟩ : ↥X) * ⟨z₂, hz₂X⟩ = 1 := Subtype.ext hz2sq
  rw [← map_mul, hsq2, map_one]

theorem exists_third_of_commuting_nbr {K : Subgroup G} {z : G} (hz : IsClassicalMember3 K z)
    (hΩ : InClass3 (conjClass3 K)) (hB : ¬ BootData3 (conjClass3 K))
    (hA2 : ¬ A2Configuration z K) {K₁ K₂ : Subgroup G} {z₁ z₂ : G}
    (he : IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂) (hz₁X : z₁ ∈ nbrSpan3 (conjClass3 K) K₁)
    {L : Subgroup G} (hL : L ∈ nbrs3 (conjClass3 K) K₁)
    (hcomm : ∀ a ∈ modOddIn (nbrSpan3 (conjClass3 K) K₁) L,
      ∀ b ∈ modOddIn (nbrSpan3 (conjClass3 K) K₁) K₂, a * b = b * a) :
    ∃ (K₃ : Subgroup G) (z₃ : G), K₃ ∈ conjClass3 K ∧ IsClassicalMember3 K₃ z₃ ∧
      Commutes K₁ K₃ ∧ Commutes K₂ K₃ ∧ z₃ ≠ z₁ ∧ z₃ ≠ z₂ := by
  classical
  have hK₁ : IsClassicalMember3 K₁ z₁ := he.cls₁
  have hK₂ : IsClassicalMember3 K₂ z₂ := he.cls₂
  have hz1sq : z₁ * z₁ = 1 := hK₁.isCentralInvolution.sq
  have hz2sq : z₂ * z₂ = 1 := hK₂.isCentralInvolution.sq
  have hz12 : z₁ * z₂ = z₂ * z₁ := he.comm_involutions
  have hK₂nbr : K₂ ∈ nbrs3 (conjClass3 K) K₁ := by
    refine ⟨he.mem₂, fun h => he.ne ?_, he.comm⟩
    rw [h] at hK₂
    exact involution_unique3 hK₁ hK₂
  set X := nbrSpan3 (conjClass3 K) K₁ with hX
  have hK₂X : K₂ ≤ X := le_nbrSpan3 hK₂nbr
  have hz₂X : z₂ ∈ X := hK₂X hK₂.mem
  obtain ⟨w, hw⟩ := hΩ.classical L hL.1
  have hLX : L ≤ X := le_nbrSpan3 hL
  have hwX : w ∈ X := hLX hw.mem
  have hw2 : w * w = 1 := hw.isCentralInvolution.sq
  set ρ := QuotientGroup.mk' (classicalInvolutionOddCore ↥X) with hρ
  have hρ1 : ∀ o : ↥X, o ∈ classicalInvolutionOddCore ↥X → ρ o = 1 := fun o ho =>
    (QuotientGroup.eq_one_iff o).mpr ho
  have hz1ne : ρ ⟨z₁, hz₁X⟩ ≠ 1 := mk_ne_one_of_involution X hz₁X hz1sq hK₁.ne_one
  have hz2ne : ρ ⟨z₂, hz₂X⟩ ≠ 1 := mk_ne_one_of_involution X hz₂X hz2sq hK₂.ne_one
  have hF : ∀ F : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X), IsElemAbelian 2 F →
      Nat.card F = 4 → ρ ⟨z₁, hz₁X⟩ ∈ F := fun F hF hc =>
    (nbhd_fourGroup_mem3 hB he.mem₁ hK₁ hF hc).2
  have hz12ne : ρ ⟨z₁, hz₁X⟩ ≠ ρ ⟨z₂, hz₂X⟩ := mk_involutions_ne hz₁X hz₂X hz1sq hz2sq hz12 he.ne
  have hsqρ : ∀ (x : G) (hx : x ∈ X), x * x = 1 → ρ ⟨x, hx⟩ * ρ ⟨x, hx⟩ = 1 := by
    intro x hx hx2
    rw [← map_mul]
    have : (⟨x, hx⟩ : ↥X) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
    rw [this, map_one]
  have himg : ∀ (x y v : G) (hx : x ∈ X) (hy : y ∈ X) (hv : v ∈ X), x * y = v →
      ρ ⟨x, hx⟩ * ρ ⟨y, hy⟩ = ρ ⟨v, hv⟩ := by
    intro x y v hx hy hv hxyv
    rw [← map_mul]
    exact congrArg ρ (Subtype.ext hxyv)
  have hwm : ρ ⟨w, hwX⟩ ∈ modOddIn X L :=
    ⟨⟨w, hwX⟩, Subgroup.mem_subgroupOf.mpr hw.mem, rfl⟩
  have hz2m : ρ ⟨z₂, hz₂X⟩ ∈ modOddIn X K₂ :=
    ⟨⟨z₂, hz₂X⟩, Subgroup.mem_subgroupOf.mpr hK₂.mem, rfl⟩
  have hcommw : ρ ⟨w, hwX⟩ * ρ ⟨z₂, hz₂X⟩ = ρ ⟨z₂, hz₂X⟩ * ρ ⟨w, hwX⟩ := hcomm _ hwm _ hz2m
  have hwne : ρ ⟨w, hwX⟩ ≠ 1 := mk_ne_one_of_involution X hwX hw2 hw.ne_one
  have hBDX : ∀ p q : ↥X ⧸ classicalInvolutionOddCore ↥X, p * p = 1 → q * q = 1 → p ≠ 1 →
      q ≠ 1 → p ≠ q → p * q = q * p → ρ ⟨z₁, hz₁X⟩ = p ∨ ρ ⟨z₁, hz₁X⟩ = q ∨
        ρ ⟨z₁, hz₁X⟩ = p * q := fun p q hp2 hq2 hp1 hq1 hpq hc =>
    bd_pair_of_forall_fourGroup hz1ne hF hp2 hq2 hp1 hq1 hpq hc
  by_cases hcase : ρ ⟨w, hwX⟩ = ρ ⟨z₂, hz₂X⟩
  ·
    exfalso
    obtain ⟨a, ha, a', ha', haa, ha'a', hcaa'⟩ := hK₂.exists_quaternion_pair_sq
    obtain ⟨b, hb, -, -, hbb, -, -⟩ := hw.exists_quaternion_pair_sq
    have haX : a ∈ X := hK₂X ha
    have ha'X : a' ∈ X := hK₂X ha'
    have hbX : b ∈ X := hLX hb
    have ham : ρ ⟨a, haX⟩ ∈ modOddIn X K₂ :=
      ⟨⟨a, haX⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have ha'm : ρ ⟨a', ha'X⟩ ∈ modOddIn X K₂ :=
      ⟨⟨a', ha'X⟩, Subgroup.mem_subgroupOf.mpr ha', rfl⟩
    have hbm : ρ ⟨b, hbX⟩ ∈ modOddIn X L :=
      ⟨⟨b, hbX⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    refine false_of_quaternion_pair (⊤ : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X))
      (a := ρ ⟨a, haX⟩) (a' := ρ ⟨a', ha'X⟩) (b := ρ ⟨b, hbX⟩) (ζ := ρ ⟨z₂, hz₂X⟩)
      (w := ρ ⟨z₁, hz₁X⟩) hz2ne (hsqρ z₂ hz₂X hz2sq) (himg a a z₂ haX haX hz₂X haa)
      (himg a' a' z₂ ha'X ha'X hz₂X ha'a') ((himg b b w hbX hbX hwX hbb).trans hcase) ?_
      (hcomm _ hbm _ ham).symm (hcomm _ hbm _ ha'm).symm (Subgroup.mem_top _)
      (Subgroup.mem_top _) (Subgroup.mem_top _) hz12ne
      (fun p q _ _ => hBDX p q)
    intro h
    have h1 : ρ ⟨a, haX⟩ * ρ ⟨a', ha'X⟩ * (ρ ⟨a, haX⟩)⁻¹ * (ρ ⟨a', ha'X⟩)⁻¹ =
        ρ ⟨z₂, hz₂X⟩ := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact congrArg ρ (Subtype.ext (by simpa using hcaa'))
    rw [h] at h1
    apply hz2ne
    rw [← h1]
    group
  ·
    have hwb2 := hsqρ w hwX hw2
    have hzb2 := hsqρ z₂ hz₂X hz2sq
    have hFe := isElemAbelian_closure_pair hwb2 hzb2 hcommw
    obtain ⟨H, hH, hHF, -⟩ := Balance.GoodData.exists_isElemAbelian_lift_map
      (classicalInvolutionOddCore ↥X) (CFSG.ComponentClassification.OddCore.odd_card ↥X)
      (Subgroup.closure ({ρ ⟨w, hwX⟩, ρ ⟨z₂, hz₂X⟩} : Set _)) hFe
    have hw'F : ρ ⟨w, hwX⟩ ∈ H.map ρ := by
      rw [hHF]
      exact Subgroup.subset_closure (by simp)
    have hz'F : ρ ⟨z₂, hz₂X⟩ ∈ H.map ρ := by
      rw [hHF]
      exact Subgroup.subset_closure (by simp)
    obtain ⟨h₁, hh₁, hh₁e⟩ := hw'F
    obtain ⟨h₂, hh₂, hh₂e⟩ := hz'F
    have hh₁sq : h₁ * h₁ = 1 := by
      have := hH.2 h₁ hh₁
      rwa [pow_two] at this
    have hh₂sq : h₂ * h₂ = 1 := by
      have := hH.2 h₂ hh₂
      rwa [pow_two] at this
    have hh12 : h₁ * h₂ = h₂ * h₁ :=
      congrArg (fun t : H => (t : ↥X)) (hH.1.is_comm.comm ⟨h₁, hh₁⟩ ⟨h₂, hh₂⟩)
    have hz2sqX : (⟨z₂, hz₂X⟩ : ↥X) * ⟨z₂, hz₂X⟩ = 1 := Subtype.ext hz2sq
    have hwsqX : (⟨w, hwX⟩ : ↥X) * ⟨w, hwX⟩ = 1 := Subtype.ext hw2
    obtain ⟨o₂, ho₂, hz2o⟩ := exists_conj_of_mk_eq_group (u := h₂) (v := ⟨z₂, hz₂X⟩) hh₂sq hz2sqX
      hh₂e
    set wpp : ↥X := o₂ * h₁ * o₂⁻¹ with hwpp
    have hρwpp : ρ wpp = ρ ⟨w, hwX⟩ := by
      rw [hwpp, map_mul, map_mul, map_inv, hρ1 o₂ ho₂, one_mul, inv_one, mul_one, hh₁e]
    have hwppsq : wpp * wpp = 1 := by
      calc wpp * wpp = o₂ * (h₁ * h₁) * o₂⁻¹ := by simp only [hwpp]; group
        _ = 1 := by rw [hh₁sq]; group
    have hwppz : wpp * ⟨z₂, hz₂X⟩ = ⟨z₂, hz₂X⟩ * wpp := by
      rw [hz2o, hwpp]
      calc o₂ * h₁ * o₂⁻¹ * (o₂ * h₂ * o₂⁻¹) = o₂ * (h₁ * h₂) * o₂⁻¹ := by group
        _ = o₂ * (h₂ * h₁) * o₂⁻¹ := by rw [hh12]
        _ = o₂ * h₂ * o₂⁻¹ * (o₂ * h₁ * o₂⁻¹) := by group
    obtain ⟨o₁, ho₁, hwo⟩ := exists_conj_of_mk_eq_group (u := ⟨w, hwX⟩) (v := wpp) hwsqX hwppsq
      hρwpp.symm
    set M := conjSub (o₁ : G) L with hM
    have hMnbr : M ∈ nbrs3 (conjClass3 K) K₁ :=
      conjSub_mem_nbrs3 hΩ.conjInvariant (nbrSpan3_le_centralizer (conjClass3 K) K₁ o₁.2) hL
    have hMw : IsClassicalMember3 M (wpp : G) := by
      have h := hw.conj (o₁ : G)
      have e : ((wpp : ↥X) : G) = (o₁ : G) * w * (o₁ : G)⁻¹ := congrArg Subtype.val hwo
      rw [e]
      exact h
    have hne₂ : z₂ ≠ (wpp : G) := by
      intro h
      apply hcase
      rw [← hρwpp]
      congr 1
      exact Subtype.ext h.symm
    have hcz : z₂ * (wpp : G) = (wpp : G) * z₂ := congrArg Subtype.val hwppz.symm
    have hK₂M : Commutes K₂ M :=
      commutes_of_not_a2Configuration3 hz hA2 he.mem₂ hMnbr.1 hK₂ hMw hne₂ hcz
    have hMz₁ : M ≤ Subgroup.centralizer ({z₁} : Set G) := fun m hm =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hMnbr.2.2 z₁ hK₁.mem m hm).symm
    have hMz₂ : M ≤ Subgroup.centralizer ({z₂} : Set G) := fun m hm =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hK₂M z₂ hK₂.mem m hm).symm
    rcases eq_or_eq_or_eq_mul_of_not_bootData3 hB hMnbr.1 hMw hz1sq hz2sq hK₁.ne_one hK₂.ne_one
      he.ne hz12 hMz₁ hMz₂ with h | h | h
    ·
      exfalso
      obtain ⟨a, ha, a', ha', haa, ha'a', hcaa'⟩ := hK₁.exists_quaternion_pair_sq
      obtain ⟨b, hb, -, -, hbb, -, -⟩ := hMw.exists_quaternion_pair_sq
      rw [h] at hbb
      refine false_of_quaternion_pair (Subgroup.centralizer (K₂ : Set G)) (ζ := z₁) (w := z₂)
        (a := a) (a' := a') (b := b) hK₁.ne_one hz1sq haa ha'a' hbb ?_
        (hMnbr.2.2 a ha b hb) (hMnbr.2.2 a' ha' b hb)
        (Subgroup.mem_centralizer_iff.mpr fun k hk => (he.comm a ha k hk).symm)
        (Subgroup.mem_centralizer_iff.mpr fun k hk => (he.comm a' ha' k hk).symm)
        (Subgroup.mem_centralizer_iff.mpr fun k hk => hK₂M k hk b hb) he.ne.symm ?_
      · intro hc'
        apply hK₁.ne_one
        rw [← hcaa', hc']
        group
      · intro p q hp hq hp2 hq2 hp1 hq1 hpq hc
        exact eq_or_eq_or_eq_mul_of_not_bootData3 hB he.mem₂ hK₂ hp2 hq2 hp1 hq1 hpq hc
          (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hp k hk))
          (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hq k hk))
    · exact absurd h.symm hne₂
    · refine ⟨M, z₁ * z₂, hMnbr.1, h ▸ hMw, hMnbr.2.2, hK₂M, ?_, ?_⟩
      · intro h'
        exact hK₂.ne_one (by simpa using h')
      · intro h'
        exact hK₁.ne_one (by simpa using h')

theorem exists_third_of_nbhd {K : Subgroup G} {z : G} (hz : IsClassicalMember3 K z)
    (hΩ : InClass3 (conjClass3 K)) (hBelow : CIT3Below (Nat.card G))
    (hB : ¬ BootData3 (conjClass3 K)) (hA2 : ¬ A2Configuration z K) {K₁ K₂ : Subgroup G}
    {z₁ z₂ : G} (he : IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂)
    (hz₁X : z₁ ∈ nbrSpan3 (conjClass3 K) K₁) (hM : ModelPairOrCenterless3) :
    ∃ (K₃ : Subgroup G) (z₃ : G), K₃ ∈ conjClass3 K ∧ IsClassicalMember3 K₃ z₃ ∧
      Commutes K₁ K₃ ∧ Commutes K₂ K₃ ∧ z₃ ≠ z₁ ∧ z₃ ≠ z₂ := by
  classical
  have hK₁ : IsClassicalMember3 K₁ z₁ := he.cls₁
  have hK₂ : IsClassicalMember3 K₂ z₂ := he.cls₂
  have hz1sq : z₁ * z₁ = 1 := hK₁.isCentralInvolution.sq
  have hz2sq : z₂ * z₂ = 1 := hK₂.isCentralInvolution.sq
  have hK₂nbr : K₂ ∈ nbrs3 (conjClass3 K) K₁ := by
    refine ⟨he.mem₂, fun h => he.ne ?_, he.comm⟩
    rw [h] at hK₂
    exact involution_unique3 hK₁ hK₂
  set X := nbrSpan3 (conjClass3 K) K₁ with hX
  have hK₂X : K₂ ≤ X := le_nbrSpan3 hK₂nbr
  have hz₂X : z₂ ∈ X := hK₂X hK₂.mem
  obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemMod3_nbrSpan3 hΩ hBelow hK₁ ⟨K₂, hK₂nbr⟩
  set ρ := QuotientGroup.mk' (classicalInvolutionOddCore ↥X) with hρ
  have hz1 : ρ ⟨z₁, hz₁X⟩ ≠ 1 := mk_ne_one_of_involution X hz₁X hz1sq hK₁.ne_one
  have hz1sqX : ρ ⟨z₁, hz₁X⟩ * ρ ⟨z₁, hz₁X⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z₁, hz₁X⟩ : ↥X) * ⟨z₁, hz₁X⟩ = 1 := Subtype.ext hz1sq
    rw [this, map_one]
  have hzc : ∀ x : ↥X ⧸ classicalInvolutionOddCore ↥X,
      x * ρ ⟨z₁, hz₁X⟩ = ρ ⟨z₁, hz₁X⟩ * x := by
    intro x
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective _ x
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (nbrSpan3_le_centralizer (conjClass3 K) K₁ x'.2) z₁
      hK₁.mem).symm
  have hF : ∀ F : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X), IsElemAbelian 2 F →
      Nat.card F = 4 → ρ ⟨z₁, hz₁X⟩ ∈ F := fun F hF hc =>
    (nbhd_fourGroup_mem3 hB he.mem₁ hK₁ hF hc).2
  have hD1 : SingleClassComponents3 D := D.singleClassComponents3_of_central hz1 hzc hF
  have hconj : ∀ g : ↥X ⧸ classicalInvolutionOddCore ↥X,
      ∀ L' ∈ oddQuotientFamily
        {L' : Subgroup ↥X | ∃ L ∈ nbrs3 (conjClass3 K) K₁, L' = L.subgroupOf X},
      conjSub g L' ∈ oddQuotientFamily
        {L' : Subgroup ↥X | ∃ L ∈ nbrs3 (conjClass3 K) K₁, L' = L.subgroupOf X} := by
    intro g L' hL'
    obtain ⟨_, ⟨L, hL, rfl⟩, rfl⟩ := hL'
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ g
    have h1 : conjSub (ρ x) ((L.subgroupOf X).map ρ) = modOddIn X (conjSub (x : G) L) :=
      (modOddIn_conjSub X x L).symm
    rw [h1]
    exact ⟨(conjSub (x : G) L).subgroupOf X, ⟨conjSub (x : G) L,
      conjSub_mem_nbrs3 hΩ.conjInvariant (nbrSpan3_le_centralizer (conjClass3 K) K₁ x.2) hL,
      rfl⟩, rfl⟩
  have hKΦ : modOddIn X K₂ ∈ oddQuotientFamily
      {L' : Subgroup ↥X | ∃ L ∈ nbrs3 (conjClass3 K) K₁, L' = L.subgroupOf X} :=
    ⟨K₂.subgroupOf X, ⟨K₂, hK₂nbr, rfl⟩, rfl⟩
  have hKcl : IsClassicalMember3 (modOddIn X K₂) (ρ ⟨z₂, hz₂X⟩) :=
    (hK₂.subgroupOf hK₂X).map_oddQuotient
  have hz12ne : ρ ⟨z₁, hz₁X⟩ ≠ ρ ⟨z₂, hz₂X⟩ :=
    mk_involutions_ne hz₁X hz₂X hz1sq hz2sq he.comm_involutions he.ne
  obtain ⟨Lb, hLbΦ, hLbcomm⟩ := D.exists_commuting_member hM hD1 hz1 hz1sqX hzc hF hconj hKΦ hKcl
    hz12ne
  obtain ⟨_, ⟨L, hL, rfl⟩, rfl⟩ := hLbΦ
  exact exists_third_of_commuting_nbr hz hΩ hB hA2 he hz₁X hL hLbcomm

end Third

end CFSG.ClassicalInvolution.Q3.Q3Y

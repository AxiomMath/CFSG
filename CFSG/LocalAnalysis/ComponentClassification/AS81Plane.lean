module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15Points

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

section Action

variable (R E : Subgroup G)

omit [Finite G] in
theorem rightConjugate_rightConjugate_inv (Q : Subgroup G) (n : G) :
    rightConjugate (rightConjugate Q n⁻¹) n = Q := by
  rw [rightConjugate_mul, inv_mul_cancel, rightConjugate_one]

omit [Finite G] in
theorem rightConjugate_inv_rightConjugate (Q : Subgroup G) (n : G) :
    rightConjugate (rightConjugate Q n) n⁻¹ = Q := by
  rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]

@[expose] noncomputable def pointsPerm (n : ↥(normalizer (E : Set G))) :
    Equiv.Perm ↥(pointsIn R E) where
  toFun Q := ⟨rightConjugate (Q : Subgroup G) (n : G)⁻¹,
    rightConjugate_mem_pointsIn Q.2 ((normalizer (E : Set G)).inv_mem n.2)⟩
  invFun Q := ⟨rightConjugate (Q : Subgroup G) (n : G), rightConjugate_mem_pointsIn Q.2 n.2⟩
  left_inv _ := Subtype.ext (rightConjugate_rightConjugate_inv _ _)
  right_inv _ := Subtype.ext (rightConjugate_inv_rightConjugate _ _)

omit [Finite G] in
theorem coe_pointsPerm_apply (n : ↥(normalizer (E : Set G))) (Q : ↥(pointsIn R E)) :
    ((pointsPerm R E n Q : ↥(pointsIn R E)) : Subgroup G) =
      rightConjugate (Q : Subgroup G) (n : G)⁻¹ := by
  unfold pointsPerm
  rfl

omit [Finite G] in
theorem coe_pointsPerm_symm_apply (n : ↥(normalizer (E : Set G))) (Q : ↥(pointsIn R E)) :
    (((pointsPerm R E n).symm Q : ↥(pointsIn R E)) : Subgroup G) =
      rightConjugate (Q : Subgroup G) (n : G) := by
  unfold pointsPerm
  rfl

@[expose] noncomputable def pointsAction :
    ↥(normalizer (E : Set G)) →* Equiv.Perm ↥(pointsIn R E) where
  toFun n := pointsPerm R E n
  map_one' := Equiv.ext fun Q => Subtype.ext (by
    rw [coe_pointsPerm_apply]
    simp only [OneMemClass.coe_one, inv_one, Equiv.Perm.coe_one, id_eq]
    exact rightConjugate_one _)
  map_mul' n m := Equiv.ext fun Q => Subtype.ext (by
    rw [Equiv.Perm.coe_mul, Function.comp_apply, coe_pointsPerm_apply, coe_pointsPerm_apply,
      coe_pointsPerm_apply, coe_mul, mul_inv_rev, rightConjugate_mul])

omit [Finite G] in
theorem coe_pointsAction_apply (n : ↥(normalizer (E : Set G))) (Q : ↥(pointsIn R E)) :
    ((pointsAction R E n Q : ↥(pointsIn R E)) : Subgroup G) =
      rightConjugate (Q : Subgroup G) (n : G)⁻¹ := by
  unfold pointsAction
  exact coe_pointsPerm_apply R E n Q

omit [Finite G] in
theorem coe_pointsAction_symm_apply (n : ↥(normalizer (E : Set G))) (Q : ↥(pointsIn R E)) :
    (((pointsAction R E n).symm Q : ↥(pointsIn R E)) : Subgroup G) =
      rightConjugate (Q : Subgroup G) (n : G) := by
  unfold pointsAction
  exact coe_pointsPerm_symm_apply R E n Q

@[expose] def pointLine (Q₁ Q₂ : ↥(pointsIn R E)) : Set ↥(pointsIn R E) :=
  {Q | (Q : Subgroup G) ≤ (Q₁ : Subgroup G) ⊔ (Q₂ : Subgroup G)}

end Action

section Lines

variable {A R E : Subgroup G}

omit [Finite G] in
theorem rightConjugate_sup' (A B : Subgroup G) (g : G) :
    rightConjugate (A ⊔ B) g = rightConjugate A g ⊔ rightConjugate B g :=
  Subgroup.map_sup _ _ _

omit [Finite G] in
theorem rightConjugate_le_iff {A B : Subgroup G} (g : G) :
    rightConjugate A g ≤ rightConjugate B g ↔ A ≤ B :=
  map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective

omit [Finite G] in
theorem image_pointLine (n : ↥(normalizer (E : Set G))) (Q₁ Q₂ : ↥(pointsIn R E)) :
    (pointsAction R E n) '' pointLine R E Q₁ Q₂ =
      pointLine R E (pointsAction R E n Q₁) (pointsAction R E n Q₂) := by
  ext Q
  simp only [Set.mem_image, pointLine, Set.mem_ofPred_eq, coe_pointsAction_apply]
  constructor
  · rintro ⟨Q', hQ', rfl⟩
    rw [coe_pointsAction_apply, ← rightConjugate_sup', rightConjugate_le_iff]
    exact hQ'
  · intro hQ
    refine ⟨(pointsAction R E n).symm Q, ?_, Equiv.apply_symm_apply _ _⟩
    rw [coe_pointsAction_symm_apply, ← rightConjugate_le_iff (n : G)⁻¹, rightConjugate_mul,
      mul_inv_cancel, rightConjugate_one, rightConjugate_sup']
    exact hQ

theorem card_sup_of_mem_pointsIn (hKte : TightlyEmbedded (centralizer (A : Set G)))
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    {Q₁ Q₂ : Subgroup G} (h₁ : Q₁ ∈ pointsIn R E) (h₂ : Q₂ ∈ pointsIn R E) (hne : Q₁ ≠ Q₂) :
    Nat.card (Q₁ ⊔ Q₂ : Subgroup G) = Nat.card R * Nat.card R := by
  have hN : Q₂ ≤ normalizer (Q₁ : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun z hz =>
      hE z (h₁.1 hz) y (h₂.1 hy))
  rw [AschbacherTheorem3.card_sup_of_le_normalizer hN
    (inf_eq_bot_of_mem_pointsIn hKte hR hE h₁ h₂ hne)]
  obtain ⟨-, x₁, rfl⟩ := h₁
  obtain ⟨-, x₂, rfl⟩ := h₂
  rw [rightConjugate_card, rightConjugate_card]

theorem ncard_pointLine_le (hKte : TightlyEmbedded (centralizer (A : Set G)))
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hE : IsElemAbelian 2 E) (hRE : R ≤ E)
    (hEAR : E ≤ A ⊔ R) (hRA1 : R ⊓ A = ⊥) (hpts : ∀ Q ∈ pointsIn R E, Q ≠ R → Q ⊓ A = ⊥)
    (hEcard : Nat.card E = 64) (hR4 : Nat.card R = 4) {Q₁ Q₂ : ↥(pointsIn R E)}
    (hne : Q₁ ≠ Q₂) : (pointLine R E Q₁ Q₂).ncard ≤ 4 := by
  classical
  have := Fintype.ofFinite ↥(pointsIn R E)
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  set M : Subgroup G := (Q₁ : Subgroup G) ⊔ Q₂
  have hne' : (Q₁ : Subgroup G) ≠ Q₂ := fun h => hne (Subtype.ext h)
  have hMcard : Nat.card M = 16 := by
    rw [card_sup_of_mem_pointsIn hKte hR hcomm Q₁.2 Q₂.2 hne', hR4]
  have hME : M ≤ E := sup_le Q₁.2.1 Q₂.2.1
  have hHcard : Nat.card (E ⊓ A : Subgroup G) = 16 := by
    have := card_eq_card_inf_mul hRA hRE hEAR hRA1
    rw [hEcard, hR4] at this
    omega
  have hMA : 4 ≤ Nat.card (M ⊓ A : Subgroup G) := by
    have hN : E ⊓ A ≤ normalizer (M : Set G) := fun y hy =>
      Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun z hz =>
        hcomm z (hME hz) y hy.1)
    have h1 := card_sup_mul_card_inf (H := M) (R := E ⊓ A) hN
    have h2 : Nat.card (M ⊔ (E ⊓ A) : Subgroup G) ≤ 64 :=
      hEcard ▸ Subgroup.card_le_of_le (sup_le hME inf_le_left)
    have h3 : Nat.card (M ⊓ (E ⊓ A) : Subgroup G) ≤ Nat.card (M ⊓ A : Subgroup G) :=
      Subgroup.card_le_of_le (inf_le_inf_left _ inf_le_right)
    rw [hMcard, hHcard] at h1
    have h4 : 0 < Nat.card (M ⊔ (E ⊓ A) : Subgroup G) := Nat.card_pos
    nlinarith
  have hptA : ∀ Q ∈ pointsIn R E, Q ⊓ A = ⊥ := fun Q hQ => by
    by_cases hQR : Q = R
    · rw [hQR]; exact hRA1
    · exact hpts Q hQ hQR
  set lF : Finset ↥(pointsIn R E) := (pointLine R E Q₁ Q₂).toFinset
  set t : ↥(pointsIn R E) → Finset G := fun Q => ((Q : Subgroup G) : Set G).toFinite.toFinset.erase 1
  set SF : Finset G := (((M : Set G) \ (A : Set G))).toFinite.toFinset
  have hsub : lF.biUnion t ⊆ SF := by
    intro x hx
    simp only [lF, t, Finset.mem_biUnion, Set.mem_toFinset, Finset.mem_erase,
      Set.Finite.mem_toFinset, SetLike.mem_coe] at hx
    obtain ⟨Q, hQl, hx1, hxQ⟩ := hx
    simp only [SF, Set.Finite.mem_toFinset, Set.mem_sdiff, SetLike.mem_coe]
    refine ⟨hQl hxQ, fun hxA => hx1 ?_⟩
    have : x ∈ (Q : Subgroup G) ⊓ A := ⟨hxQ, hxA⟩
    rwa [hptA Q Q.2, mem_bot] at this
  have hdisj : (lF : Set ↥(pointsIn R E)).PairwiseDisjoint t := by
    intro Q hQ Q' hQ' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    simp only [t, Finset.mem_erase, Set.Finite.mem_toFinset, SetLike.mem_coe] at hx hx'
    have hbot := inf_eq_bot_of_mem_pointsIn hKte hR hcomm Q.2 Q'.2
      (fun h => hne (Subtype.ext h))
    have : x ∈ (Q : Subgroup G) ⊓ Q' := ⟨hx.2, hx'.2⟩
    rw [hbot, mem_bot] at this
    exact hx.1 this
  have hcardt : ∀ Q ∈ lF, (t Q).card = 3 := fun Q _ => by
    simp only [t]
    rw [Finset.card_erase_of_mem (by simp), ← Set.ncard_eq_toFinset_card,
      (Nat.card_coe_set_eq _).symm]
    obtain ⟨-, x, hx⟩ := Q.2
    change Nat.card (Q : Subgroup G) - 1 = 3
    rw [hx, rightConjugate_card, hR4]
  have hSF : SF.card ≤ 12 := by
    simp only [SF]
    rw [← Set.ncard_eq_toFinset_card, ← Set.sdiff_inter_self_eq_sdiff,
      Set.ncard_sdiff Set.inter_subset_right]
    have h1 : (M : Set G).ncard = 16 := by rw [← Nat.card_coe_set_eq]; exact hMcard
    have h2 : 4 ≤ ((A : Set G) ∩ (M : Set G)).ncard := by
      rw [Set.inter_comm, ← Nat.card_coe_set_eq]
      exact hMA
    omega
  have h := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, Finset.sum_const_nat hcardt] at h
  have hl : (pointLine R E Q₁ Q₂).ncard = lF.card := by
    rw [Set.ncard_eq_toFinset_card']
  omega

end Lines

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem rightConjugate_ne_of_fixedPointFree (h11 : Step11)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) {z : G} (hzA : z ∈ A)
    (hzN : z ∈ normalizer ((E ⊓ F : Subgroup G) : Set G))
    (hz : ∀ w ∈ E ⊓ F ⊓ A, z * w * z⁻¹ = w → w = 1) :
    rightConjugate (rightConjugate R g) z⁻¹ ≠ rightConjugate R g := by
  intro hfix
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB := hF.base
  have hstd := hB.hyp.standard
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hKte := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hR.isPGroup hodd
  have hRgEF : rightConjugate R g ≤ E ⊓ F := hF.inf_eq ▸ le_sup_right
  have hREF : R ≤ E ⊓ F := hF.inf_eq ▸ le_sup_left
  have hRgA : rightConjugate R g ⊓ A = ⊥ :=
    (step13L34_of h11 hE16 G A hB hL R hR g hF.not_mem hF.comm).2.2 hodd
  have hgK : g ∉ normalizer (centralizer (A : Set G) : Set G) := hNK ▸ hF.not_mem
  have hRRg : R ⊓ rightConjugate R g = ⊥ := by
    have h := two_subgroup_inf_conjugate_eq_bot _ (R ⊓ rightConjugate R g) hKte
      (hR.isPGroup.to_le inf_le_left) g hgK
      (inf_le_right.trans (AschbacherTheorem3.rightConjugate_le_rightConjugate hRA g))
    rwa [inf_eq_left.mpr (inf_le_left.trans hRA)] at h
  have hR1 : R ≠ ⊥ := AS76b.isSylowOf_ne_bot_of_even hR hKte.1
  have hRgR : rightConjugate R g ≠ R := fun h => hR1 (by rw [h, inf_idem] at hRRg; exact hRRg)
  obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR1
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hQ₀ : rightConjugate R g ∈ pointsIn R E := ⟨hRgEF.trans inf_le_left, g, rfl⟩
  obtain ⟨h₀, hh₀, hh₀1, hq⟩ := exists_mul_mem_of_mem_pointsIn hR hF.elemE hF.R_le_E hF.E_le
    hRA1 hKte hQ₀ hRgR hRgA hr hr1'
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hh₀EF : h₀ ∈ E ⊓ F := by
    have := (E ⊓ F).mul_mem (hRgEF hq) ((E ⊓ F).inv_mem (hREF hr))
    simpa using this
  have hzh : z * h₀ * z⁻¹ ∈ E ⊓ F := (mem_normalizer_iff.mp hzN h₀).mp hh₀EF
  have hcz : z * r = r * z := mem_centralizer_iff.mp (hRA hr) z hzA
  have hq' : z * h₀ * z⁻¹ * r ∈ rightConjugate R g := by
    rw [← hfix, mem_rightConjugate_iff, inv_inv]
    have : z⁻¹ * (z * h₀ * z⁻¹ * r) * z = h₀ * r := by
      calc z⁻¹ * (z * h₀ * z⁻¹ * r) * z = h₀ * (z⁻¹ * (r * z)) := by group
        _ = h₀ * r := by rw [← hcz, inv_mul_cancel_left]
    rw [this]
    exact hq
  have hu : h₀⁻¹ * (z * h₀ * z⁻¹) ∈ rightConjugate R g ⊓ A := by
    refine ⟨?_, A.mul_mem (A.inv_mem hh₀.2) (A.mul_mem (A.mul_mem hzA hh₀.2) (A.inv_mem hzA))⟩
    have h1 := (rightConjugate R g).mul_mem ((rightConjugate R g).inv_mem hq) hq'
    have h2 : (h₀ * r)⁻¹ * (z * h₀ * z⁻¹ * r) = h₀⁻¹ * (z * h₀ * z⁻¹) := by
      have hc := hcomm _ (hF.R_le_E hr) _ hzh.1
      calc (h₀ * r)⁻¹ * (z * h₀ * z⁻¹ * r) = r⁻¹ * h₀⁻¹ * ((z * h₀ * z⁻¹) * r) := by group
        _ = r⁻¹ * h₀⁻¹ * (r * (z * h₀ * z⁻¹)) := by rw [hc]
        _ = r⁻¹ * (h₀⁻¹ * r) * (z * h₀ * z⁻¹) := by group
        _ = r⁻¹ * (r * h₀⁻¹) * (z * h₀ * z⁻¹) := by
            rw [hcomm _ (E.inv_mem hh₀.1) _ (hF.R_le_E hr)]
        _ = h₀⁻¹ * (z * h₀ * z⁻¹) := by group
    rwa [h2] at h1
  rw [hRgA, mem_bot, inv_mul_eq_one] at hu
  exact hh₀1 (hz h₀ ⟨hh₀EF, hh₀.2⟩ hu.symm)

theorem centerIn_inf_eq (hF : Frame G A A R g E F) :
    E ⊓ F ⊓ A = centerIn ((E ⊔ F) ⊓ A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  obtain ⟨hRD, -, hDeq⟩ := sylow_sup_structure hRA hF.sylowR.isPGroup hF.sylow
  rw [hF.inf_eq_center]
  apply le_antisymm
  · rintro x ⟨⟨hxD, hxC⟩, hxA⟩
    refine ⟨⟨hxD, hxA⟩, ?_⟩
    have hxC' : x ∈ centralizer ((E ⊔ F : Subgroup G) : Set G) := hxC
    show x ∈ centralizer (((E ⊔ F) ⊓ A : Subgroup G) : Set G)
    rw [mem_centralizer_iff]
    exact fun y hy => mem_centralizer_iff.mp hxC' y hy.1
  · rintro x ⟨⟨hxD, hxA⟩, hxC⟩
    have hxC' : x ∈ centralizer (((E ⊔ F) ⊓ A : Subgroup G) : Set G) := hxC
    refine ⟨⟨hxD, ?_⟩, hxA⟩
    have hDx : E ⊔ F ≤ centralizer ({x} : Set G) := by
      rw [hDeq]
      refine sup_le (fun y hy => mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hxC' y hy)) (fun r hr => mem_centralizer_singleton_iff.mpr ?_)
      exact (mem_centralizer_iff.mp (hRA hr) x hxA).symm
    show x ∈ centralizer ((E ⊔ F : Subgroup G) : Set G)
    rw [mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hDx hy)

theorem exists_torus_of_frame (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) :
    ∃ y ∈ A, y ∈ normalizer (E : Set G) ∧ y ∈ normalizer ((E ⊓ F : Subgroup G) : Set G) ∧
      (∀ w ∈ E ⊓ F ⊓ A, y * w * y⁻¹ = w → w = 1) ∧
      (∀ w ∈ E ⊓ F ⊓ A, (y * y) * w * (y * y)⁻¹ = w → w = 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  obtain ⟨hRD, hDA, hDeq⟩ := sylow_sup_structure hRA hR.isPGroup hF.sylow
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hR.isPGroup hodd
  have hEA16 : Nat.card (E ⊓ A : Subgroup G) = 16 := by
    have := card_eq_card_inf_mul hRA hF.R_le_E hF.E_le hRA1
    rw [hF.cardE, hF.cardR] at this
    omega
  obtain ⟨y, ⟨⟨hyA, hyH⟩, hyW⟩, hyfix⟩ := exists_torus_of_card_sixteen hF.base.hyp.standard.1 hL
    hodd hDA (inf_le_inf_right A le_sup_left) (AS76b.IsElemAbelian.mono hF.elemE inf_le_left)
    hEA16
  have hW := centerIn_inf_eq hF
  have hyR : y ∈ normalizer (R : Set G) := Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun r hr => (mem_centralizer_iff.mp (hRA hr) y hyA).symm)
  have hREF : R ≤ E ⊓ F := hF.inf_eq ▸ le_sup_left
  have hEFAR : E ⊓ F ≤ A ⊔ R := inf_le_left.trans hF.E_le
  have hyE : y ∈ normalizer (E : Set G) := by
    rw [eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le]
    exact mem_normalizer_sup hyH hyR
  have hyEF : y ∈ normalizer ((E ⊓ F : Subgroup G) : Set G) := by
    rw [eq_inf_sup_of_le_sup hRA hREF hEFAR, hW]
    exact mem_normalizer_sup hyW hyR
  have hfix : ∀ w ∈ E ⊓ F ⊓ A, y * w * y⁻¹ = w → w = 1 := fun w hw h => hyfix w (hW ▸ hw) h
  refine ⟨y, hyA, hyE, hyEF, hfix, fun w hw h => ?_⟩
  by_contra hw1
  have hcomm : ∀ x ∈ E, ∀ x' ∈ E, x * x' = x' * x := fun x hx x' hx' =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
  have hyw : y * w * y⁻¹ ∈ E ⊓ F ⊓ A :=
    ⟨(mem_normalizer_iff.mp hyEF w).mp hw.1, A.mul_mem (A.mul_mem hyA hw.2) (A.inv_mem hyA)⟩
  have hne : y * w * y⁻¹ ≠ w := fun h' => hw1 (hfix w hw h')
  have hprod : w * (y * w * y⁻¹) ∈ E ⊓ F ⊓ A := (E ⊓ F ⊓ A).mul_mem hw hyw
  have hfix2 : y * (w * (y * w * y⁻¹)) * y⁻¹ = w * (y * w * y⁻¹) := by
    have h1 : y * (y * w * y⁻¹) * y⁻¹ = w := by
      calc y * (y * w * y⁻¹) * y⁻¹ = y * y * w * (y * y)⁻¹ := by group
        _ = w := h
    calc y * (w * (y * w * y⁻¹)) * y⁻¹ = (y * w * y⁻¹) * (y * (y * w * y⁻¹) * y⁻¹) := by group
      _ = (y * w * y⁻¹) * w := by rw [h1]
      _ = w * (y * w * y⁻¹) := hcomm _ hyw.1.1 _ hw.1.1
  have h2 := hfix _ hprod hfix2
  apply hne
  have hw2 : w * w = 1 := by
    have := hF.elemE.2 w hw.1.1
    rwa [sq] at this
  calc y * w * y⁻¹ = w * (w * (y * w * y⁻¹)) := by
        rw [← mul_assoc, hw2, one_mul]
    _ = w := by rw [h2, mul_one]

theorem exists_four_points (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) :
    ∃ Q₁ ∈ pointsIn R E, ∃ Q₂ ∈ pointsIn R E, Q₁ ≤ E ⊓ F ∧ Q₂ ≤ E ⊓ F ∧ Q₁ ≠ R ∧ Q₂ ≠ R ∧
      Q₁ ≠ rightConjugate R g ∧ Q₂ ≠ rightConjugate R g ∧ Q₁ ≠ Q₂ := by
  obtain ⟨y, hyA, hyE, hyEF, hfix, hfix2⟩ := exists_torus_of_frame hF hL hodd
  have hRgEF : rightConjugate R g ≤ E ⊓ F := hF.inf_eq ▸ le_sup_right
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hKte := AS76b.tightlyEmbedded_centralizer hF.base.hyp.standard
  have hR1 : R ≠ ⊥ := AS76b.isSylowOf_ne_bot_of_even hF.sylowR hKte.1
  have hRR : ∀ z ∈ A, rightConjugate R z = R := fun z hz =>
    (rightConjugate_eq_self_iff R z).mpr (Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun r hr => (mem_centralizer_iff.mp (hRA hr) z hz).symm))
  have hRgR : rightConjugate R g ≠ R := by
    intro h
    have hNK := AS76b.normalizer_centralizer_eq hF.base.hyp.standard
    have hgK : g ∉ normalizer (centralizer (A : Set G) : Set G) := hNK ▸ hF.not_mem
    have hRRg := two_subgroup_inf_conjugate_eq_bot _ (R ⊓ rightConjugate R g) hKte
      (hF.sylowR.isPGroup.to_le inf_le_left) g hgK
      (inf_le_right.trans (AschbacherTheorem3.rightConjugate_le_rightConjugate hRA g))
    rw [inf_eq_left.mpr (inf_le_left.trans hRA), h, inf_idem] at hRRg
    exact hR1 hRRg
  have hyyA : y * y ∈ A := A.mul_mem hyA hyA
  have hyyEF : y * y ∈ normalizer ((E ⊓ F : Subgroup G) : Set G) :=
    (normalizer _).mul_mem hyEF hyEF
  have hyyE : y * y ∈ normalizer (E : Set G) := (normalizer _).mul_mem hyE hyE
  have hne₁ := rightConjugate_ne_of_fixedPointFree h11 hE16 hF hL hodd hyA hyEF hfix
  have hne₂ := rightConjugate_ne_of_fixedPointFree h11 hE16 hF hL hodd hyyA hyyEF hfix2
  have hpt : ∀ z ∈ normalizer (E : Set G), rightConjugate (rightConjugate R g) z⁻¹ ∈ pointsIn R E :=
    fun z hz => rightConjugate_mem_pointsIn ⟨hRgEF.trans inf_le_left, g, rfl⟩
      ((normalizer _).inv_mem hz)
  have hle : ∀ z ∈ normalizer ((E ⊓ F : Subgroup G) : Set G),
      rightConjugate (rightConjugate R g) z⁻¹ ≤ E ⊓ F := fun z hz => by
    have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate hRgEF z⁻¹
    rwa [(rightConjugate_eq_self_iff _ _).mpr ((normalizer _).inv_mem hz)] at h1
  have hneR : ∀ z ∈ A, rightConjugate (rightConjugate R g) z⁻¹ ≠ R := fun z hz h => by
    apply hRgR
    have h1 := congrArg (fun H => rightConjugate H z) h
    simp only [rightConjugate_rightConjugate_inv] at h1
    rw [h1, hRR z hz]
  refine ⟨_, hpt y hyE, _, hpt (y * y) hyyE, hle y hyEF, hle (y * y) hyyEF, hneR y hyA,
    hneR (y * y) hyyA, hne₁, hne₂, fun h => hne₁ ?_⟩
  have h1 := congrArg (fun H => rightConjugate H y) h
  simp only [rightConjugate_mul] at h1
  rw [inv_mul_cancel_right, show g * (y * y)⁻¹ * y = g * y⁻¹ by group] at h1
  rw [rightConjugate_mul]
  exact h1.symm

end Frame

end CFSG.ComponentClassification.AS81

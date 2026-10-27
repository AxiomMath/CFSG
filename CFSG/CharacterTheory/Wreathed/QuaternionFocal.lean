module

public import CFSG.CharacterTheory.Wreathed.ActualLocalActions

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical IsKleinFour commutatorElement

universe u v

theorem quaternionEight_mem_intrinsic_center (q : QuaternionGroup 2) :
    q ∈ Subgroup.center (QuaternionGroup 2) ↔ q = 1 ∨ q = QuaternionGroup.a 2 := by
  rw [Subgroup.mem_center_iff]
  exact (show ∀ q : QuaternionGroup 2,
    (∀ r : QuaternionGroup 2, r * q = q * r) ↔ q = 1 ∨ q = QuaternionGroup.a 2
      by decide) q

theorem quaternionEight_intrinsic_center_card :
    Nat.card (Subgroup.center (QuaternionGroup 2)) = 2 := by
  let e : Subgroup.center (QuaternionGroup 2) ≃
      {q : QuaternionGroup 2 // q = 1 ∨ q = QuaternionGroup.a 2} :=
    Equiv.subtypeEquivRight quaternionEight_mem_intrinsic_center
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide

theorem quaternionEight_center_quotient_isKleinFour :
    IsKleinFour (QuaternionGroup 2 ⧸ Subgroup.center (QuaternionGroup 2)) := by
  let E := QuaternionGroup 2 ⧸ Subgroup.center (QuaternionGroup 2)
  have hcard : Nat.card E = 4 := by
    have h := (Subgroup.center (QuaternionGroup 2)).card_eq_card_quotient_mul_card_subgroup
    rw [quaternionEight_intrinsic_center_card, Nat.card_eq_fintype_card,
      QuaternionGroup.card] at h
    change 8 = Nat.card E * 2 at h
    omega
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  refine ⟨hcard, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr ?_⟩
  intro x hx
  apply orderOf_eq_prime
  · induction x using QuotientGroup.induction_on with
    | H q =>
      change (QuotientGroup.mk' (Subgroup.center (QuaternionGroup 2))) q ^ 2 = 1
      rw [← map_pow]
      apply (QuotientGroup.eq_one_iff (q ^ 2)).mpr
      rw [quaternionEight_mem_intrinsic_center]
      exact (show ∀ q : QuaternionGroup 2,
        q ^ 2 = 1 ∨ q ^ 2 = QuaternionGroup.a 2 by decide) q
  · exact hx

@[expose] def intrinsicCenterQuotientEquiv {A : Type u} {B : Type v}
    [Group A] [Group B] (e : A ≃* B) :
    A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem intrinsicCenterQuotientEquiv_mk {A : Type u} {B : Type v}
    [Group A] [Group B] (e : A ≃* B) (a : A) :
    intrinsicCenterQuotientEquiv e ((QuotientGroup.mk' (Subgroup.center A)) a) =
      (QuotientGroup.mk' (Subgroup.center B)) (e a) := rfl

theorem quaternion_center_quotient_isKleinFour {Q : Type u} [Group Q]
    (e : QuaternionGroup 2 ≃* Q) : IsKleinFour (Q ⧸ Subgroup.center Q) := by
  let ec := intrinsicCenterQuotientEquiv e
  have hq := quaternionEight_center_quotient_isKleinFour
  refine ⟨?_, ?_⟩
  · rw [← Nat.card_congr ec.toEquiv]
    exact hq.card_four
  · rw [← Monoid.exponent_eq_of_mulEquiv ec]
    exact hq.exponent_two

@[expose] def automorphismDifferences {Q : Type u} [Group Q] (a : MulAut Q) : Subgroup Q :=
  Subgroup.closure (Set.range (fun q : Q => a q * q⁻¹))

@[expose] def intrinsicCenterQuotientAction (Q : Type u) [Group Q] :
    MulAut Q →* MulAut (Q ⧸ Subgroup.center Q) :=
  CFSG.FiveTransitive.CharacteristicAutomorphism.quotient (Subgroup.center Q)

theorem intrinsicCenterQuotientAction_mk (Q : Type u) [Group Q] (a : MulAut Q) (q : Q) :
    intrinsicCenterQuotientAction Q a ((QuotientGroup.mk' (Subgroup.center Q)) q) =
      (QuotientGroup.mk' (Subgroup.center Q)) (a q) := rfl

theorem kleinFour_order_three_difference_surjective (E : Type u) [Group E] [IsKleinFour E]
    (a : MulAut E) (horder : orderOf a = 3) :
    Function.Surjective (fun x : E => a x * x⁻¹) := by
  let : IsMulCommutative E := IsKleinFour.isMulCommutative
  have hcomm (x y : E) : x * y = y * x := isMulCommutative_iff.mp inferInstance x y
  apply Finite.surjective_of_injective
  intro x y hxy
  have hfix : a (x * y⁻¹) = x * y⁻¹ := by
    rw [map_mul, map_inv]
    have h := congrArg (fun z : E => z * x * (a y)⁻¹) hxy
    have hleft : a x * x⁻¹ * x * (a y)⁻¹ = a x * (a y)⁻¹ := by group
    have hright : a y * y⁻¹ * x * (a y)⁻¹ = x * y⁻¹ := by
      calc
        a y * y⁻¹ * x * (a y)⁻¹ = a y * (y⁻¹ * x) * (a y)⁻¹ := by group
        _ = (y⁻¹ * x) * a y * (a y)⁻¹ := by rw [hcomm (a y) (y⁻¹ * x)]
        _ = y⁻¹ * x := by group
        _ = x * y⁻¹ := hcomm _ _
    rw [hleft, hright] at h
    exact h
  have hone : x * y⁻¹ = 1 := by
    by_contra hne
    exact (CFSG.kleinFour_order_three_cycle E a horder (x * y⁻¹) hne).1 hfix
  exact mul_inv_eq_one.mp hone

theorem quaternion_mem_intrinsic_center {Q : Type u} [Group Q]
    (e : QuaternionGroup 2 ≃* Q) (q : Q) :
    q ∈ Subgroup.center Q ↔ q = 1 ∨ q = e (QuaternionGroup.a 2) := by
  rw [← Subgroup.map_center_eq e]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases (quaternionEight_mem_intrinsic_center p).mp hp with rfl | rfl
    · exact Or.inl (map_one e)
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨1, (Subgroup.center _).one_mem, map_one e⟩
    · exact ⟨QuaternionGroup.a 2,
        (quaternionEight_mem_intrinsic_center _).mpr (Or.inr rfl), rfl⟩

theorem quaternion_noncentral_square {Q : Type u} [Group Q]
    (e : QuaternionGroup 2 ≃* Q) (q : Q) (hq : q ∉ Subgroup.center Q) :
    q ^ 2 = e (QuaternionGroup.a 2) := by
  obtain ⟨p, rfl⟩ := e.surjective q
  have hp : p ∉ Subgroup.center (QuaternionGroup 2) := by
    intro hp
    apply hq
    rw [← Subgroup.map_center_eq e]
    exact ⟨p, hp, rfl⟩
  rw [quaternionEight_mem_intrinsic_center, not_or] at hp
  rw [← map_pow, quaternionEight_noncentral_square p hp]

theorem quaternion_quotient_differences_surjective {Q : Type u} [Group Q]
    (e : QuaternionGroup 2 ≃* Q) (a : MulAut Q)
    (horder : orderOf (intrinsicCenterQuotientAction Q a) = 3) :
    Function.Surjective (fun q : Q =>
      (QuotientGroup.mk' (Subgroup.center Q)) (a q * q⁻¹)) := by
  let : IsKleinFour (Q ⧸ Subgroup.center Q) := quaternion_center_quotient_isKleinFour e
  intro x
  obtain ⟨y, hy⟩ := kleinFour_order_three_difference_surjective
    (Q ⧸ Subgroup.center Q) (intrinsicCenterQuotientAction Q a) horder x
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) y
  refine ⟨q, ?_⟩
  simpa only [intrinsicCenterQuotientAction_mk, map_mul, map_inv] using hy

theorem quaternion_central_involution_mem_differences {Q : Type u} [Group Q]
    (e : QuaternionGroup 2 ≃* Q) (a : MulAut Q)
    (horder : orderOf (intrinsicCenterQuotientAction Q a) = 3) :
    e (QuaternionGroup.a 2) ∈ automorphismDifferences a := by
  let f := QuotientGroup.mk' (Subgroup.center Q)
  have hn : f (e (QuaternionGroup.a 1)) ≠ 1 := by
    intro heq
    have hc : e (QuaternionGroup.a 1) ∈ Subgroup.center Q :=
      (QuotientGroup.eq_one_iff _).mp heq
    rcases (quaternion_mem_intrinsic_center e _).mp hc with hc | hc
    · have hp : QuaternionGroup.a 1 = 1 := e.injective (by simpa using hc)
      exact (by decide : (QuaternionGroup.a 1 : QuaternionGroup 2) ≠ 1) hp
    · have hp : QuaternionGroup.a 1 = QuaternionGroup.a 2 := e.injective hc
      exact (by decide : (QuaternionGroup.a 1 : QuaternionGroup 2) ≠ QuaternionGroup.a 2) hp
  obtain ⟨q, hq⟩ := quaternion_quotient_differences_surjective e a horder
    (f (e (QuaternionGroup.a 1)))
  have hnoncentral : a q * q⁻¹ ∉ Subgroup.center Q := by
    intro hc
    apply hn
    rw [← hq]
    exact (QuotientGroup.eq_one_iff _).mpr hc
  have hd : a q * q⁻¹ ∈ automorphismDifferences a :=
    Subgroup.subset_closure ⟨q, rfl⟩
  rw [← quaternion_noncentral_square e _ hnoncentral]
  exact (automorphismDifferences a).pow_mem hd 2

theorem quaternion_center_le_differences {Q : Type u} [Group Q]
    (e : QuaternionGroup 2 ≃* Q) (a : MulAut Q)
    (horder : orderOf (intrinsicCenterQuotientAction Q a) = 3) :
    Subgroup.center Q ≤ automorphismDifferences a := by
  intro q hq
  rcases (quaternion_mem_intrinsic_center e q).mp hq with rfl | rfl
  · exact (automorphismDifferences a).one_mem
  · exact quaternion_central_involution_mem_differences e a horder

theorem quaternion_differences_eq_top {Q : Type u} [Group Q]
    (e : QuaternionGroup 2 ≃* Q) (a : MulAut Q)
    (horder : orderOf (intrinsicCenterQuotientAction Q a) = 3) :
    automorphismDifferences a = ⊤ := by
  apply (Subgroup.eq_top_iff' _).mpr
  intro q
  obtain ⟨r, hr⟩ := quaternion_quotient_differences_surjective e a horder
    ((QuotientGroup.mk' (Subgroup.center Q)) q)
  have hc : q / (a r * r⁻¹) ∈ Subgroup.center Q :=
    QuotientGroup.eq_iff_div_mem.mp hr.symm
  have hcentral : q / (a r * r⁻¹) ∈ automorphismDifferences a :=
    quaternion_center_le_differences e a horder hc
  have hd : a r * r⁻¹ ∈ automorphismDifferences a :=
    Subgroup.subset_closure ⟨r, rfl⟩
  simpa only [div_mul_cancel] using (automorphismDifferences a).mul_mem hcentral hd

theorem quaternion_difference_map_eq_commutator {Q : Type u} {E : Type v}
    [Group Q] [Group E] (a : MulAut Q) (f : Q →* E) (h : E)
    (hconj : ∀ q : Q, f (a q) = h * f q * h⁻¹) (q : Q) :
    f (a q * q⁻¹) = ⁅h, f q⁆ := by
  rw [map_mul, map_inv, hconj, commutatorElement_def]

theorem quaternion_difference_map_inv_eq_commutator {Q : Type u} {E : Type v}
    [Group Q] [Group E] (a : MulAut Q) (f : Q →* E) (h : E)
    (hconj : ∀ q : Q, f (a q) = h * f q * h⁻¹) (q : Q) :
    (f (a q * q⁻¹))⁻¹ = ⁅f q, h⁆ := by
  rw [quaternion_difference_map_eq_commutator a f h hconj q, commutatorElement_inv]

theorem quaternion_range_le_commutator_of_conjugation {Q : Type u} {E : Type v}
    [Group Q] [Group E] (e : QuaternionGroup 2 ≃* Q) (a : MulAut Q)
    (horder : orderOf (intrinsicCenterQuotientAction Q a) = 3)
    (f : Q →* E) (h : E) (hconj : ∀ q : Q, f (a q) = h * f q * h⁻¹) :
    f.range ≤ commutator E := by
  have hgen : automorphismDifferences a ≤ (commutator E).comap f := by
    rw [automorphismDifferences, Subgroup.closure_le]
    rintro _ ⟨q, rfl⟩
    change f (a q * q⁻¹) ∈ commutator E
    rw [quaternion_difference_map_eq_commutator a f h hconj q]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top h) (Subgroup.mem_top (f q))
  rw [quaternion_differences_eq_top e a horder] at hgen
  rintro _ ⟨q, rfl⟩
  exact hgen (Subgroup.mem_top q)

theorem quaternion_range_le_focal_of_conjugation {Q : Type u} {E : Type v}
    [Group Q] [Group E] (e : QuaternionGroup 2 ≃* Q) (a : MulAut Q)
    (horder : orderOf (intrinsicCenterQuotientAction Q a) = 3)
    (f : Q →* E) (h : E) (hconj : ∀ q : Q, f (a q) = h * f q * h⁻¹)
    (P : Subgroup E) (hQ : f.range ≤ P) : f.range ≤ P.focalSubgroup := by
  have hgen : automorphismDifferences a ≤ P.focalSubgroup.comap f := by
    rw [automorphismDifferences, Subgroup.closure_le]
    rintro _ ⟨q, rfl⟩
    change f (a q * q⁻¹) ∈ P.focalSubgroup
    have hinv : (f (a q * q⁻¹))⁻¹ ∈ P.focalSubgroup := by
      rw [Subgroup.focalSubgroup_def]
      apply Subgroup.subset_closure
      exact ⟨P.inv_mem (hQ ⟨a q * q⁻¹, rfl⟩),
        f q, hQ ⟨q, rfl⟩, h, quaternion_difference_map_inv_eq_commutator a f h hconj q⟩
    exact (P.focalSubgroup.inv_mem_iff).mp hinv
  rw [quaternion_differences_eq_top e a horder] at hgen
  rintro _ ⟨q, rfl⟩
  exact hgen (Subgroup.mem_top q)

@[expose] def quaternionNormalizerQuotientAction {E : Type u} [Group E]
    (Q0 : Subgroup E) : Subgroup.normalizer (Q0 : Set E) →* MulAut (Q0 ⧸ Subgroup.center Q0) :=
  (intrinsicCenterQuotientAction Q0).comp Q0.normalizerMonoidHom

theorem quaternionNormalizerQuotientAction_mk {E : Type u} [Group E]
    (Q0 : Subgroup E) (h : Subgroup.normalizer (Q0 : Set E)) (q : Q0) :
    quaternionNormalizerQuotientAction Q0 h
      ((QuotientGroup.mk' (Subgroup.center Q0)) q) =
      (QuotientGroup.mk' (Subgroup.center Q0)) (Q0.normalizerMonoidHom h q) := rfl

theorem quaternion_normalizer_difference_coe {E : Type u} [Group E]
    (Q0 : Subgroup E) (h : Subgroup.normalizer (Q0 : Set E)) (q : Q0) :
    ((Q0.normalizerMonoidHom h q * q⁻¹ : Q0) : E) = ⁅(h : E), (q : E)⁆ := by
  exact quaternion_difference_map_eq_commutator (Q0.normalizerMonoidHom h) Q0.subtype h
    (fun q => Q0.normalizerMonoidHom_apply_apply_coe h q) q

theorem quaternion_subgroup_le_commutator {E : Type u} [Group E]
    (Q0 : Subgroup E) (e : QuaternionGroup 2 ≃* Q0) (h : E) (hn : h ∈ Subgroup.normalizer (Q0 : Set E))
    (horder : orderOf (quaternionNormalizerQuotientAction Q0 ⟨h, hn⟩) = 3) :
    Q0 ≤ commutator E := by
  have hx := quaternion_range_le_commutator_of_conjugation e
    (Q0.normalizerMonoidHom ⟨h, hn⟩) horder Q0.subtype h
    (fun q => Q0.normalizerMonoidHom_apply_apply_coe ⟨h, hn⟩ q)
  rwa [Subgroup.range_subtype] at hx

theorem quaternion_subgroup_le_relative_commutator {E : Type u} [Group E]
    (Q0 : Subgroup E) (e : QuaternionGroup 2 ≃* Q0) (h : E) (hn : h ∈ Subgroup.normalizer (Q0 : Set E))
    (horder : orderOf (quaternionNormalizerQuotientAction Q0 ⟨h, hn⟩) = 3)
    (D : Subgroup E) (hQD : Q0 ≤ D) (hhD : h ∈ D) :
    Q0 ≤ (commutator D).map D.subtype := by
  let f : Q0 →* D := Subgroup.inclusion hQD
  have hc : ∀ q : Q0, f (Q0.normalizerMonoidHom ⟨h, hn⟩ q) =
      (⟨h, hhD⟩ : D) * f q * (⟨h, hhD⟩ : D)⁻¹ := by
    intro q
    apply Subtype.ext
    exact Q0.normalizerMonoidHom_apply_apply_coe ⟨h, hn⟩ q
  have hx := quaternion_range_le_commutator_of_conjugation e
    (Q0.normalizerMonoidHom ⟨h, hn⟩) horder f (⟨h, hhD⟩ : D) hc
  intro q hq
  exact ⟨f ⟨q, hq⟩, hx ⟨⟨q, hq⟩, rfl⟩, rfl⟩

theorem quaternion_subgroup_le_focal {E : Type u} [Group E]
    (Q0 : Subgroup E) (e : QuaternionGroup 2 ≃* Q0) (h : E) (hn : h ∈ Subgroup.normalizer (Q0 : Set E))
    (horder : orderOf (quaternionNormalizerQuotientAction Q0 ⟨h, hn⟩) = 3)
    (P : Subgroup E) (hQP : Q0 ≤ P) : Q0 ≤ P.focalSubgroup := by
  have hx := quaternion_range_le_focal_of_conjugation e
    (Q0.normalizerMonoidHom ⟨h, hn⟩) horder Q0.subtype h
    (fun q => Q0.normalizerMonoidHom_apply_apply_coe ⟨h, hn⟩ q) P
    (by rwa [Subgroup.range_subtype])
  rwa [Subgroup.range_subtype] at hx

theorem quaternion_subgroup_le_sylow_focal {E : Type u} [Group E]
    {p : ℕ} [Fact p.Prime]
    (Q0 : Subgroup E) (e : QuaternionGroup 2 ≃* Q0) (h : E) (hn : h ∈ Subgroup.normalizer (Q0 : Set E))
    (horder : orderOf (quaternionNormalizerQuotientAction Q0 ⟨h, hn⟩) = 3)
    (P : Sylow p E) (hQP : Q0 ≤ (P : Subgroup E)) :
    Q0 ≤ (P : Subgroup E).focalSubgroup :=
  quaternion_subgroup_le_focal Q0 e h hn horder P hQP

theorem quaternion_subgroup_le_relative_focal {E : Type u} [Group E]
    (Q0 : Subgroup E) (e : QuaternionGroup 2 ≃* Q0) (h : E) (hn : h ∈ Subgroup.normalizer (Q0 : Set E))
    (horder : orderOf (quaternionNormalizerQuotientAction Q0 ⟨h, hn⟩) = 3)
    (D : Subgroup E) (hQD : Q0 ≤ D) (hhD : h ∈ D)
    (P : Subgroup D) (hQP : Q0.subgroupOf D ≤ P) :
    Q0 ≤ P.focalSubgroup.map D.subtype := by
  let f : Q0 →* D := Subgroup.inclusion hQD
  have hc : ∀ q : Q0, f (Q0.normalizerMonoidHom ⟨h, hn⟩ q) =
      (⟨h, hhD⟩ : D) * f q * (⟨h, hhD⟩ : D)⁻¹ := by
    intro q
    apply Subtype.ext
    exact Q0.normalizerMonoidHom_apply_apply_coe ⟨h, hn⟩ q
  have hx := quaternion_range_le_focal_of_conjugation e
    (Q0.normalizerMonoidHom ⟨h, hn⟩) horder f (⟨h, hhD⟩ : D) hc P
    (by simpa only [f, Subgroup.inclusion_range] using hQP)
  intro q hq
  exact ⟨f ⟨q, hq⟩, hx ⟨⟨q, hq⟩, rfl⟩, rfl⟩

theorem quaternion_subgroup_le_relative_sylow_focal {E : Type u} [Group E]
    {p : ℕ} [Fact p.Prime]
    (Q0 : Subgroup E) (e : QuaternionGroup 2 ≃* Q0) (h : E) (hn : h ∈ Subgroup.normalizer (Q0 : Set E))
    (horder : orderOf (quaternionNormalizerQuotientAction Q0 ⟨h, hn⟩) = 3)
    (D : Subgroup E) (hQD : Q0 ≤ D) (hhD : h ∈ D)
    (P : Sylow p D) (hQP : Q0.subgroupOf D ≤ (P : Subgroup D)) :
    Q0 ≤ (P : Subgroup D).focalSubgroup.map D.subtype :=
  quaternion_subgroup_le_relative_focal Q0 e h hn horder D hQD hhD P hQP

theorem intrinsicCenterQuotientAction_intertwines {A : Type u} {B : Type v}
    [Group A] [Group B] (e : A ≃* B) (a : MulAut A)
    (x : A ⧸ Subgroup.center A) :
    intrinsicCenterQuotientAction B (MulAut.congr e a) (intrinsicCenterQuotientEquiv e x) =
      intrinsicCenterQuotientEquiv e (intrinsicCenterQuotientAction A a x) := by
  induction x using QuotientGroup.induction_on with
  | H q =>
    change intrinsicCenterQuotientAction B (MulAut.congr e a)
      (intrinsicCenterQuotientEquiv e ((QuotientGroup.mk' (Subgroup.center A)) q)) = _
    rw [intrinsicCenterQuotientEquiv_mk, intrinsicCenterQuotientAction_mk]
    change (QuotientGroup.mk' (Subgroup.center B)) (MulAut.congr e a (e q)) =
      intrinsicCenterQuotientEquiv e
        ((QuotientGroup.mk' (Subgroup.center A)) (a q))
    rw [intrinsicCenterQuotientEquiv_mk]
    congr 1
    change e (a (e.symm (e q))) = e (a q)
    rw [MulEquiv.symm_apply_apply]

theorem intrinsicCenterQuotientAction_congr {A : Type u} {B : Type v}
    [Group A] [Group B] (e : A ≃* B) (a : MulAut A) :
    intrinsicCenterQuotientAction B (MulAut.congr e a) =
      MulAut.congr (intrinsicCenterQuotientEquiv e) (intrinsicCenterQuotientAction A a) := by
  ext x
  obtain ⟨y, rfl⟩ := (intrinsicCenterQuotientEquiv e).surjective x
  rw [intrinsicCenterQuotientAction_intertwines]
  change intrinsicCenterQuotientEquiv e (intrinsicCenterQuotientAction A a y) =
    intrinsicCenterQuotientEquiv e (intrinsicCenterQuotientAction A a
      ((intrinsicCenterQuotientEquiv e).symm (intrinsicCenterQuotientEquiv e y)))
  rw [MulEquiv.symm_apply_apply]

theorem intrinsicCenterQuotientAction_congr_order {A : Type u} {B : Type v}
    [Group A] [Group B] (e : A ≃* B) (a : MulAut A) :
    orderOf (intrinsicCenterQuotientAction B (MulAut.congr e a)) =
      orderOf (intrinsicCenterQuotientAction A a) := by
  rw [intrinsicCenterQuotientAction_congr]
  exact (MulAut.congr (intrinsicCenterQuotientEquiv e)).orderOf_eq _

theorem quaternion_differences_eq_top_of_equiv {Q : Type u} [Group Q]
    (e : Q ≃* QuaternionGroup 2) (a : MulAut Q)
    (horder : orderOf (intrinsicCenterQuotientAction Q a) = 3) :
    automorphismDifferences a = ⊤ := quaternion_differences_eq_top e.symm a horder

theorem quaternion_normalizer_right_difference_coe {E : Type u} [Group E]
    (Q0 : Subgroup E) (h : Subgroup.normalizer (Q0 : Set E)) (q : Q0) :
    (((Q0.normalizerMonoidHom h).symm q * q⁻¹ : Q0) : E) =
      ⁅(h : E)⁻¹, (q : E)⁆ := by
  rw [Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.normalizerMonoidHom_apply_symm_apply_coe, commutatorElement_def, inv_inv]

theorem quaternion_normalizer_blueprint_focal_difference_coe {E : Type u} [Group E]
    (Q0 : Subgroup E) (h : Subgroup.normalizer (Q0 : Set E)) (q : Q0) :
    ((q⁻¹ * (Q0.normalizerMonoidHom h).symm q : Q0) : E) =
      ⁅(q : E)⁻¹, (h : E)⁻¹⁆ := by
  rw [Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.normalizerMonoidHom_apply_symm_apply_coe, commutatorElement_def, inv_inv]
  group

theorem quaternionNormalizerQuotientAction_right_mk {E : Type u} [Group E]
    (Q0 : Subgroup E) (h : Subgroup.normalizer (Q0 : Set E)) (q : Q0) :
    (quaternionNormalizerQuotientAction Q0 h)⁻¹
      ((QuotientGroup.mk' (Subgroup.center Q0)) q) =
      (QuotientGroup.mk' (Subgroup.center Q0)) ((Q0.normalizerMonoidHom h).symm q) := by
  change (intrinsicCenterQuotientAction Q0 (Q0.normalizerMonoidHom h))⁻¹ _ = _
  rw [← map_inv]
  exact intrinsicCenterQuotientAction_mk Q0 (Q0.normalizerMonoidHom h)⁻¹ q

theorem quaternionNormalizerQuotientAction_right_order {E : Type u} [Group E]
    (Q0 : Subgroup E) (h : Subgroup.normalizer (Q0 : Set E)) :
    orderOf (quaternionNormalizerQuotientAction Q0 h)⁻¹ =
      orderOf (quaternionNormalizerQuotientAction Q0 h) := orderOf_inv _

theorem quaternion_subgroup_le_commutator_of_right_order {E : Type u} [Group E]
    (Q0 : Subgroup E) (e : Q0 ≃* QuaternionGroup 2)
    (h : E) (hn : h ∈ Subgroup.normalizer (Q0 : Set E))
    (horder : orderOf (quaternionNormalizerQuotientAction Q0 ⟨h, hn⟩)⁻¹ = 3) :
    Q0 ≤ commutator E := by
  apply quaternion_subgroup_le_commutator Q0 e.symm h hn
  rwa [orderOf_inv] at horder

theorem intrinsicCenterQuotientAction_order_of_projection {Q : Type u} {B : Type v}
    [Group Q] [Group B] (f : Q →* B) (hf : Function.Surjective f)
    (hker : Subgroup.center Q = f.ker) (a : MulAut Q) (b : MulAut B)
    (hintertwine : ∀ q : Q, f (a q) = b (f q)) :
    orderOf (intrinsicCenterQuotientAction Q a) = orderOf b := by
  let e := QuotientGroup.liftEquiv (Subgroup.center Q) hf hker
  have he (q : Q) : e ((QuotientGroup.mk' (Subgroup.center Q)) q) = f q := rfl
  have ha : MulAut.congr e (intrinsicCenterQuotientAction Q a) = b := by
    ext x
    obtain ⟨q, rfl⟩ := hf x
    rw [← he q]
    change e (intrinsicCenterQuotientAction Q a
      (e.symm (e ((QuotientGroup.mk' (Subgroup.center Q)) q)))) = _
    rw [MulEquiv.symm_apply_apply, intrinsicCenterQuotientAction_mk, he, he]
    exact hintertwine q
  rw [← ha]
  exact ((MulAut.congr e).orderOf_eq _).symm

theorem originalQuaternionCenterProjection_ker_eq_intrinsic_center
    (n : ℕ) (hn : 2 ≤ n) :
    (originalQuaternionCenterProjection n hn).ker = Subgroup.center (Original.Q (2 ^ n)) := by
  ext q
  obtain ⟨p, rfl⟩ := (originalQuaternionProjectionEquiv n hn).surjective q
  rw [MonoidHom.mem_ker, originalQuaternionCenterProjection_kernel,
    quaternion_mem_intrinsic_center (originalQuaternionProjectionEquiv n hn)]
  constructor
  · rintro (rfl | rfl)
    · left; exact map_one _
    · right; rfl
  · rintro (h | h)
    · left
      apply (originalQuaternionProjectionEquiv n hn).injective
      simpa using h
    · right
      exact (originalQuaternionProjectionEquiv n hn).injective h

theorem originalQuaternion_intrinsic_action_order (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n))) :
    orderOf (intrinsicCenterQuotientAction (Original.Q (2 ^ n))
      (originalQuaternionAutomorphism n hn a)) =
        orderOf (originalVQuotientAutomorphism n a) := by
  exact intrinsicCenterQuotientAction_order_of_projection
    (originalQuaternionCenterProjection n hn) (originalQuaternionCenterProjection_surjective n hn)
    (originalQuaternionCenterProjection_ker_eq_intrinsic_center n hn).symm
    (originalQuaternionAutomorphism n hn a) (originalVQuotientAutomorphism n a)
    (originalQuaternionCenterProjection_intertwines n hn a)

theorem originalQuaternion_differences_eq_top (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n)))
    (horder : orderOf (originalVQuotientAutomorphism n a) = 3) :
    automorphismDifferences (originalQuaternionAutomorphism n hn a) = ⊤ := by
  apply quaternion_differences_eq_top (originalQuaternionProjectionEquiv n hn)
  exact (originalQuaternion_intrinsic_action_order n hn a).trans horder

theorem modelQ_intrinsic_action_order {G : Type u} [Group G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G)) :
    orderOf (intrinsicCenterQuotientAction (modelQ S e) (modelQAutomorphism n hn S e g)) =
      orderOf (modelVQuotientAction S e g) := by
  rw [modelQAutomorphism, intrinsicCenterQuotientAction_congr_order]
  exact originalQuaternion_intrinsic_action_order n hn (modelVAction S e g)

theorem modelQ_normalizer_quotient_action_order {G : Type u} [Group G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G)) :
    orderOf (quaternionNormalizerQuotientAction (modelQ S e)
      ⟨g.val, modelVNormalizer_normalizes_modelQ n hn S e g.property⟩) =
        orderOf (modelVQuotientAction S e g) := by
  change orderOf (intrinsicCenterQuotientAction (modelQ S e)
    ((modelQ S e).normalizerMonoidHom
      ⟨g.val, modelVNormalizer_normalizes_modelQ n hn S e g.property⟩)) = _
  rw [← modelQAutomorphism_eq_actual_action]
  exact modelQ_intrinsic_action_order n hn S e g

theorem modelQ_differences_eq_top {G : Type u} [Group G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G))
    (horder : orderOf (modelVQuotientAction S e g) = 3) :
    automorphismDifferences (modelQAutomorphism n hn S e g) = ⊤ := by
  apply quaternion_differences_eq_top
    ((originalQuaternionProjectionEquiv n hn).trans (modelQEquiv S e))
  exact (modelQ_intrinsic_action_order n hn S e g).trans horder

theorem modelQ_le_commutator_of_order_three {G : Type u} [Group G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G))
    (horder : orderOf (modelVQuotientAction S e g) = 3) :
    modelQ S e ≤ commutator G := by
  apply quaternion_subgroup_le_commutator (modelQ S e)
    ((originalQuaternionProjectionEquiv n hn).trans (modelQEquiv S e)) g.val
    (modelVNormalizer_normalizes_modelQ n hn S e g.property)
  exact (modelQ_normalizer_quotient_action_order n hn S e g).trans horder

theorem modelQ_le_relative_commutator_of_order_three {G : Type u} [Group G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G))
    (horder : orderOf (modelVQuotientAction S e g) = 3)
    (D : Subgroup G) (hQD : modelQ S e ≤ D) (hgD : g.val ∈ D) :
    modelQ S e ≤ (commutator D).map D.subtype := by
  exact quaternion_subgroup_le_relative_commutator (modelQ S e)
    ((originalQuaternionProjectionEquiv n hn).trans (modelQEquiv S e)) g.val
    (modelVNormalizer_normalizes_modelQ n hn S e g.property)
    ((modelQ_normalizer_quotient_action_order n hn S e g).trans horder) D hQD hgD

theorem modelQ_le_focal_of_order_three {G : Type u} [Group G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G))
    (horder : orderOf (modelVQuotientAction S e g) = 3)
    (P : Subgroup G) (hQP : modelQ S e ≤ P) : modelQ S e ≤ P.focalSubgroup := by
  exact quaternion_subgroup_le_focal (modelQ S e)
    ((originalQuaternionProjectionEquiv n hn).trans (modelQEquiv S e)) g.val
    (modelVNormalizer_normalizes_modelQ n hn S e g.property)
    ((modelQ_normalizer_quotient_action_order n hn S e g).trans horder) P hQP

theorem modelQ_le_relative_focal_of_order_three {G : Type u} [Group G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G))
    (horder : orderOf (modelVQuotientAction S e g) = 3)
    (D : Subgroup G) (hQD : modelQ S e ≤ D) (hgD : g.val ∈ D)
    (P : Subgroup D) (hQP : (modelQ S e).subgroupOf D ≤ P) :
    modelQ S e ≤ P.focalSubgroup.map D.subtype := by
  exact quaternion_subgroup_le_relative_focal (modelQ S e)
    ((originalQuaternionProjectionEquiv n hn).trans (modelQEquiv S e)) g.val
    (modelVNormalizer_normalizes_modelQ n hn S e g.property)
    ((modelQ_normalizer_quotient_action_order n hn S e g).trans horder) D hQD hgD P hQP

theorem modelVNormalizer_exists_quaternion_commutator_actor {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e ≃* Equiv.Perm (Fin 3))) :
    ∃ g : Subgroup.normalizer (modelV S e : Set G),
      (∃ k : ℕ, 0 < k ∧ orderOf g = 3 ^ k) ∧ Odd (orderOf g) ∧
      orderOf (modelVQuotientAction S e g) = 3 ∧
      orderOf (quaternionNormalizerQuotientAction (modelQ S e)
        ⟨g.val, modelVNormalizer_normalizes_modelQ n hn S e g.property⟩) = 3 ∧
      modelQ S e ≤ commutator G ∧
      (∀ D : Subgroup G, modelQ S e ≤ D → g.val ∈ D →
        modelQ S e ≤ (commutator D).map D.subtype) ∧
      (∀ P : Subgroup G, modelQ S e ≤ P → modelQ S e ≤ P.focalSubgroup) ∧
      (∀ (D : Subgroup G), modelQ S e ≤ D → g.val ∈ D →
        ∀ P : Subgroup D, (modelQ S e).subgroupOf D ≤ P →
          modelQ S e ≤ P.focalSubgroup.map D.subtype) := by
  obtain ⟨g, hpower, hodd, horder⟩ :=
    modelVNormalizer_exists_odd_three_power_actor n hn S e hsix
  exact ⟨g, hpower, hodd, horder,
    (modelQ_normalizer_quotient_action_order n hn S e g).trans horder,
    modelQ_le_commutator_of_order_three n hn S e g horder,
    modelQ_le_relative_commutator_of_order_three n hn S e g horder,
    modelQ_le_focal_of_order_three n hn S e g horder,
    modelQ_le_relative_focal_of_order_three n hn S e g horder⟩

end CFSG.Wreathed

module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitConn

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

variable {G : Type*} [Group G]

theorem abelianConnectedIn_of_normal_eight [Finite G] {T E A : Subgroup G} {z : G}
    (hT : IsPGroup 2 T) (hET : E ≤ T) (hEn : T ≤ normalizer (E : Set G)) (hE : IsElemTwo E)
    (hE8 : Nat.card E = 8) (hzT : z ∈ T) (hzc : ∀ y ∈ T, z * y = y * z) (hz2 : z * z = 1)
    (hzE : z ∉ E) (hAT : A ≤ T) (hA : IsAbelianTwoOfRank 3 A) :
    AbelianConnectedIn T 3 A (E ⊔ zpowers z) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hfE, hf1, hfc⟩ : ∃ f ∈ E, f ≠ 1 ∧ ∀ y ∈ T, f * y = y * f := by
    have hnil : Group.IsNilpotent ↥T := IsPGroup.isNilpotent hT
    have hEn' : (E.subgroupOf T).Normal := ⟨fun e he s => by
      rw [mem_subgroupOf] at he ⊢
      exact (mem_normalizer_iff.mp (hEn s.2) e).mp he⟩
    have hEne : E.subgroupOf T ≠ ⊥ := by
      intro h
      have h1 : Nat.card (E.subgroupOf T) = 1 := by rw [h, card_bot]
      rw [Nat.card_congr (subgroupOfEquivOfLe hET).toEquiv, hE8] at h1
      omega
    obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hEne)
    rw [mem_inf, mem_subgroupOf] at hw
    refine ⟨((w : ↥T) : G), hw.1, ?_, ?_⟩
    · intro h
      apply hw1
      apply Subtype.ext
      apply Subtype.ext
      exact h
    · intro y hy
      exact (congrArg Subtype.val ((mem_center_iff.mp hw.2) ⟨y, hy⟩)).symm
  have hf2 : f * f = 1 := hE.2 f hfE
  have hfT : f ∈ T := hET hfE
  have hzf : Commute z f := (commute_iff_eq z f).2 (hzc f hfT)
  have hz1 : z ≠ 1 := fun h => hzE (h ▸ E.one_mem)
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hcardz : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hzord]
  obtain ⟨F, hFA, hFe, hF8⟩ := exists_isElemTwo_of_isAbelianTwoOfRank hA
  have hFT : F ≤ T := hFA.trans hAT
  set V : Subgroup G := zpowers z ⊔ zpowers f with hVdef
  have hVcomm : ∀ x ∈ zpowers z, ∀ y ∈ zpowers f, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (hzf.zpow_zpow i j).eq
  have hVe : IsElemTwo V := (isElemTwo_zpowers hz2).sup (isElemTwo_zpowers hf2) hVcomm
  have hfnotz : f ∉ zpowers z := by
    intro hfz
    obtain ⟨k, hk, hfk⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hfz)
    have hk2 : k < 2 := by simpa only [Finset.mem_range, hzord] using hk
    have hcases : k = 0 ∨ k = 1 := by omega
    rcases hcases with rfl | rfl
    · exact hf1 (by simpa only [pow_zero] using hfk.symm)
    · have hfz' : f = z := by simpa only [pow_one] using hfk.symm
      exact hzE (hfz' ▸ hfE)
  have hV4 : 4 ≤ Nat.card V := by
    have h := two_mul_card_le_of_not_mem (H := zpowers z) (K := V)
      le_sup_left (mem_sup_right (mem_zpowers f)) hfnotz
    rw [hcardz] at h
    rw [hVdef]
    omega
  have hzC : z ∈ centralizer (zpowers f : Set G) :=
    zpowers_le.mp (commute_iff_le_centralizer.mp hVcomm)
  have hzN : z ∈ normalizer (zpowers f : Set G) :=
    Subgroup.centralizer_le_normalizer (zpowers f : Set G) hzC
  have hVle4 : Nat.card V ≤ 4 := by
    have h := card_zpowers_sup_le (H := zpowers f) hz2 hzN
    have hfcard : Nat.card (zpowers f) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hf2)
    rw [hVdef]
    omega
  obtain ⟨a, haF, haV⟩ : ∃ a ∈ F, a ∉ V := by
    by_contra h
    push Not at h
    have hle : F ≤ V := fun y hy => h y hy
    have := Subgroup.card_le_of_le hle
    omega
  have ha2 : a * a = 1 := hFe.2 a haF
  have haT : a ∈ T := hFT haF
  have haN : a ∈ normalizer (E : Set G) := hEn haT
  have hza : Commute z a := (commute_iff_eq z a).2 (hzc a haT)
  have hfa : Commute f a := (commute_iff_eq f a).2 (hfc a haT)
  have hVa : ∀ x ∈ V, ∀ y ∈ zpowers a, x * y = y * x := by
    refine commute_sup_left ?_ ?_
    · intro x hx y hy
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
      exact (hza.zpow_zpow i j).eq
    · intro x hx y hy
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
      exact (hfa.zpow_zpow i j).eq
  have hB₁e : IsElemTwo (V ⊔ zpowers a) := hVe.sup (isElemTwo_zpowers ha2) hVa
  have hB₁8 : 8 ≤ Nat.card ↥(V ⊔ zpowers a) := by
    have h := two_mul_card_le_of_not_mem (H := V) (K := V ⊔ zpowers a)
      le_sup_left (mem_sup_right (mem_zpowers a)) haV
    omega
  have hB₁T : V ⊔ zpowers a ≤ T :=
    sup_le (sup_le (zpowers_le.mpr hzT) (zpowers_le.mpr hfT)) (zpowers_le.mpr haT)
  have hFz : ∀ x ∈ F, ∀ y ∈ zpowers z, x * y = y * x := by
    intro x hx y hy
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (((commute_iff_eq z x).2 (hzc x (hFT hx))).symm.zpow_right j).eq
  have hFf : ∀ x ∈ F, ∀ y ∈ zpowers f, x * y = y * x := by
    intro x hx y hy
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (((commute_iff_eq f x).2 (hfc x (hFT hx))).symm.zpow_right j).eq
  have hFa : ∀ x ∈ F, ∀ y ∈ zpowers a, x * y = y * x :=
    commute_of_elemTwo hFe le_rfl (zpowers_le.mpr haF)
  have hFB₁ : ∀ x ∈ F, ∀ y ∈ V ⊔ zpowers a, x * y = y * x :=
    commute_sup_right (commute_sup_right hFz hFf) hFa
  set C : Subgroup G := E ⊓ centralizer ({a} : Set G) with hCdef
  have hCe : IsElemTwo C := hE.mono inf_le_left
  have hC4 : 4 ≤ Nat.card C := by
    refine (le_card_of_le_card_sq hCe.isPGroup).1 ?_
    rw [← hE8]
    exact card_le_card_inf_centralizer_sq hE haN ha2
  have hCnotz : z ∉ C := fun h => hzE (mem_inf.mp h).1
  have hzCcomm : ∀ x ∈ C, ∀ y ∈ zpowers z, x * y = y * x :=
    commute_symm (commute_zpowers_left (K := C) (fun y hy => hzc y (hET (mem_inf.mp hy).1)))
  have hB₂e : IsElemTwo (C ⊔ zpowers z) := hCe.sup (isElemTwo_zpowers hz2) hzCcomm
  have hB₂8 : 8 ≤ Nat.card ↥(C ⊔ zpowers z) := by
    have h := two_mul_card_le_of_not_mem (H := C) (K := C ⊔ zpowers z)
      le_sup_left (mem_sup_right (mem_zpowers z)) hCnotz
    omega
  have hB₂T : C ⊔ zpowers z ≤ T :=
    sup_le ((inf_le_left : C ≤ E).trans hET) (zpowers_le.mpr hzT)
  have hzz : ∀ x ∈ zpowers z, ∀ y ∈ zpowers z, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self z i j).eq
  have hzC' : ∀ x ∈ zpowers z, ∀ y ∈ C, x * y = y * x :=
    commute_zpowers_left (K := C) (fun y hy => hzc y (hET (mem_inf.mp hy).1))
  have hfC' : ∀ x ∈ zpowers f, ∀ y ∈ C, x * y = y * x :=
    commute_zpowers_left (K := C) (fun y hy => hfc y (hET (mem_inf.mp hy).1))
  have hfz' : ∀ x ∈ zpowers f, ∀ y ∈ zpowers z, x * y = y * x := by
    intro x hx y hy
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    exact (hzf.symm.zpow_zpow j i).eq
  have hVC : ∀ x ∈ V, ∀ y ∈ C ⊔ zpowers z, x * y = y * x :=
    commute_sup_left (commute_sup_right hzC' hzz) (commute_sup_right hfC' hfz')
  have haC : ∀ x ∈ zpowers a, ∀ y ∈ C, x * y = y * x :=
    commute_zpowers_left (K := C) (fun y hy =>
      (mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2).symm)
  have haz : ∀ x ∈ zpowers a, ∀ y ∈ zpowers z, x * y = y * x := by
    intro x hx y hy
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    exact (hza.symm.zpow_zpow j i).eq
  have hB₁B₂ : ∀ x ∈ V ⊔ zpowers a, ∀ y ∈ C ⊔ zpowers z, x * y = y * x :=
    commute_sup_left hVC (commute_sup_right haC haz)
  have hEZcomm : ∀ x ∈ E, ∀ y ∈ zpowers z, x * y = y * x := by
    intro x hx y hy
    have hle : zpowers z ≤ centralizer ({x} : Set G) :=
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hzc x (hET hx)))
    exact (mem_centralizer_singleton_iff.mp (hle hy)).symm
  have hEZ : IsElemTwo (E ⊔ zpowers z) := hE.sup (isElemTwo_zpowers hz2) hEZcomm
  have hEZT : E ⊔ zpowers z ≤ T := sup_le hET (zpowers_le.mpr hzT)
  have hEZ8 : 8 ≤ Nat.card ↥(E ⊔ zpowers z) := by
    have h := Subgroup.card_le_of_le (le_sup_left : E ≤ E ⊔ zpowers z)
    omega
  have hB₂EZ : C ⊔ zpowers z ≤ E ⊔ zpowers z :=
    sup_le ((inf_le_left : C ≤ E).trans le_sup_left) le_sup_right
  have hB₂EZcomm : ∀ x ∈ C ⊔ zpowers z, ∀ y ∈ E ⊔ zpowers z, x * y = y * x :=
    commute_of_elemTwo hEZ hB₂EZ le_rfl
  have step : ∀ {A' B' : Subgroup G}, B' ≤ T → IsElemTwo B' → 8 ≤ Nat.card B' →
      (∀ x ∈ A', ∀ y ∈ B', x * y = y * x) →
      (fun A' B' : Subgroup G => B' ≤ T ∧ IsAbelianTwoOfRank 3 B' ∧
        ∀ x ∈ A', ∀ y ∈ B', x * y = y * x) A' B' :=
    fun hB hBe hB8 hc => ⟨hB, hBe.isAbelianTwoOfRank hB8, hc⟩
  refine ⟨hAT, hA, ?_⟩
  refine Relation.ReflTransGen.head (step (A' := A) hFT hFe hF8
    (fun x hx y hy => hA.2.1 x hx y (hFA hy))) ?_
  refine Relation.ReflTransGen.head (step (A' := F) hB₁T hB₁e hB₁8 hFB₁) ?_
  refine Relation.ReflTransGen.head (step (A' := V ⊔ zpowers a) hB₂T hB₂e hB₂8 hB₁B₂) ?_
  exact Relation.ReflTransGen.single (step (A' := C ⊔ zpowers z) hEZT hEZ hEZ8 hB₂EZcomm)

theorem isThreeConnected_of_normal_eight [Finite G] {T E : Subgroup G} {z : G}
    (hT : IsPGroup 2 T) (hET : E ≤ T) (hEn : T ≤ normalizer (E : Set G)) (hE : IsElemTwo E)
    (hE8 : Nat.card E = 8) (hzT : z ∈ T) (hzc : ∀ y ∈ T, z * y = y * z) (hz2 : z * z = 1)
    (hzE : z ∉ E) : IsThreeConnected T := fun _ _ hA hB hAr hBr =>
  (abelianConnectedIn_of_normal_eight hT hET hEn hE hE8 hzT hzc hz2 hzE hA hAr).trans
    (abelianConnectedIn_of_normal_eight hT hET hEn hE hE8 hzT hzc hz2 hzE hB hBr).symm

end CFSG.ComponentClassification.GrSLit

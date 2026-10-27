module

public import CFSG.LargeExtraspecial.S3cD
public import CFSG.LargeExtraspecial.S3cFive
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions OrthoF2

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

theorem card_Dbar_eq_one_or_two_or_four (hTI : WeaklyClosedTITransitive.{u}) (hn : 3 ≤ S.width)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hirr : ¬ S.IsReducible) :
    Nat.card (S.Dbar g) = 1 ∨ Nat.card (S.Dbar g) = 2 ∨ Nat.card (S.Dbar g) = 4 := by
  have hdvd : Nat.card (S.Dbar g) ∣ Nat.card (S.Lbar g) :=
    Subgroup.card_dvd_of_le fun _ hs => hs.1
  rw [((S.lemma_3_11_two hTI hn haQ hne hno).resolve_left hirr).1] at hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have h4 := S.card_Dbar_le_four haQ hne hno
  rw [hk] at h4 ⊢
  have hk2 : k ≤ 2 := by
    by_contra h
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> norm_num

theorem apply_cl_eq_add_of_not_mem_Qa (hTI : WeaklyClosedTITransitive.{u}) (hn : 3 ≤ S.width)
    {g h : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hirr : ¬ S.IsReducible) (hh : h ∈ S.M)
    (hab : g * S.z * g⁻¹ * ((h * g) * S.z * (h * g)⁻¹) =
      (h * g) * S.z * (h * g)⁻¹ * (g * S.z * g⁻¹))
    (hbQa : (h * g) * S.z * (h * g)⁻¹ ∉ S.Qa g) {t : S.O} (ht : t ∈ S.Dbar g) (ht1 : t ≠ 1) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h * g) * S.z * (h * g)⁻¹)) =
      S.cl ((h * g) * S.z * (h * g)⁻¹) + S.cl (g * S.z * g⁻¹) := by
  have hbQ := S.conj_mul_mem_QG hh haQ
  have hperp : polar S.q (S.cl (g * S.z * g⁻¹)) (S.cl ((h * g) * S.z * (h * g)⁻¹)) = 0 :=
    (S.polar_cl_eq_zero_iff haQ hbQ).mpr hab
  rcases mem_span_singleton_iff.mp ((mem_pointRadical.mp ht.2).2.2.1 _ hperp) with h0 | h1
  · exact absurd (S.mem_Qa_of_fix hTI hn haQ hne hno hirr hh ht.1 ht1 ht.2 (sub_eq_zero.mp h0))
      hbQa
  · rw [← h1]
    abel

theorem mem_Qa_of_commute_of_card_Dbar_eq_four (hTI : WeaklyClosedTITransitive.{u})
    (hn : 3 ≤ S.width) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hno : ¬ S.HasTypeAInL g) (hirr : ¬ S.IsReducible) (hD4 : Nat.card (S.Dbar g) = 4)
    {h : G} (hh : h ∈ S.M)
    (hab : g * S.z * g⁻¹ * ((h * g) * S.z * (h * g)⁻¹) =
      (h * g) * S.z * (h * g)⁻¹ * (g * S.z * g⁻¹)) :
    (h * g) * S.z * (h * g)⁻¹ ∈ S.Qa g := by
  classical
  by_contra hbQa
  obtain ⟨t₁, ht₁, ht₁'⟩ := exists_mem_not_mem_finset_of_card_lt (H := S.Dbar g) {1}
    (by rw [Finset.card_singleton]; omega)
  obtain ⟨t₂, ht₂, ht₂'⟩ := exists_mem_not_mem_finset_of_card_lt (H := S.Dbar g) {1, t₁}
    (Finset.card_le_two.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht₁' ht₂'
  have hsq : t₁ * t₁ = 1 := by
    have := S.sq_eq_one_of_mem_Lbar haQ ht₁.1
    rwa [pow_two] at this
  have h12 : t₁ * t₂ ≠ 1 := fun h' => ht₂'.2 (by
    calc t₂ = t₁ * t₁ * t₂ := by rw [hsq, one_mul]
      _ = t₁ := by rw [mul_assoc, h', mul_one])
  have hfix : (t₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
    (mem_pointRadical.mp ht₁.2).2.1
  have e := S.apply_cl_eq_add_of_not_mem_Qa hTI hn haQ hne hno hirr hh hab hbQa
    (mul_mem ht₁ ht₂) h12
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply,
    S.apply_cl_eq_add_of_not_mem_Qa hTI hn haQ hne hno hirr hh hab hbQa ht₂ ht₂'.1, map_add,
    S.apply_cl_eq_add_of_not_mem_Qa hTI hn haQ hne hno hirr hh hab hbQa ht₁ ht₁', hfix,
    add_assoc, vec_add_self, add_zero] at e
  exact S.cl_conj_z_ne_zero haQ hne (by simpa using e.symm)

theorem false_of_forall_commute_mem_Qa (hTI : WeaklyClosedTITransitive.{u}) (hn : 4 ≤ S.width)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hirr : ¬ S.IsReducible) {t : S.O} (ht : t ∈ S.Dbar g) (ht1 : t ≠ 1)
    (hP8 : ∀ h ∈ S.M, g * S.z * g⁻¹ * ((h * g) * S.z * (h * g)⁻¹) =
      (h * g) * S.z * (h * g)⁻¹ * (g * S.z * g⁻¹) → (h * g) * S.z * (h * g)⁻¹ ∈ S.Qa g) :
    False := by
  classical
  have h2 : 2 ≤ S.width := by omega
  have hP9 : ∀ h ∈ S.M, g * S.z * g⁻¹ * ((h * g) * S.z * (h * g)⁻¹) =
      (h * g) * S.z * (h * g)⁻¹ * (g * S.z * g⁻¹) →
      (h * g) * S.z * (h * g)⁻¹ = g * S.z * g⁻¹ ∨
        (h * g) * S.z * (h * g)⁻¹ = g * S.z * g⁻¹ * S.z := by
    intro h hh hab
    by_contra h'
    push Not at h'
    exact hirr (S.isReducible_of_commute haQ hne hP8 hh hab h'.1 h'.2)
  set A := (S.Lbar g).subgroupOf S.Mbar with hA
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    Subtype.ext (S.Lbar_comm haQ (mem_subgroupOf.mp hx) (mem_subgroupOf.mp hy))
  have hsqA : ∀ x ∈ A, x ^ 2 = 1 := fun x hx =>
    Subtype.ext (by simpa using S.sq_eq_one_of_mem_Lbar haQ (mem_subgroupOf.mp hx))
  have hTIA : ∀ mb : S.Mbar, A.map (MulAut.conj mb).toMonoidHom = A ∨
      A ⊓ A.map (MulAut.conj mb).toMonoidHom = ⊥ := by
    intro mb
    obtain ⟨⟨h, hh⟩, hmh⟩ := MonoidHom.mem_range.mp mb.2
    rw [hA, S.map_conj_Lbar_subgroupOf hh mb hmh]
    by_cases hL : S.Lbar (h * g) = S.Lbar g
    · left
      rw [hL]
    · right
      have e : (S.Lbar g).subgroupOf S.Mbar ⊓ (S.Lbar (h * g)).subgroupOf S.Mbar =
          (S.Lbar g ⊓ S.Lbar (h * g)).subgroupOf S.Mbar := by
        ext x
        simp only [mem_inf, mem_subgroupOf]
      rw [e, S.Lbar_inf_eq_bot haQ hne hP9 hh hL, bot_subgroupOf]
  have hwc := S.isWeaklyClosedInNormalizer_Lbar h2 haQ hne hno
  have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g ht.1
  have htA : (⟨t, htM⟩ : S.Mbar) ∈ A := mem_subgroupOf.mpr ht.1
  have ht1' : (⟨t, htM⟩ : S.Mbar) ≠ 1 := fun h' => ht1 (congrArg Subtype.val h')
  have hLD : S.Lbar g ≤ S.Dbar g := by
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]
      exact one_mem _
    have hyM : y ∈ S.Mbar := S.Lbar_le_Mbar g hy
    obtain ⟨n, hnN, hnt⟩ := hTI S.Mbar A hcommA hsqA hTIA hwc S.pCore_Mbar_eq_bot _ htA ht1'
      ⟨y, hyM⟩ (mem_subgroupOf.mpr hy) (fun h' => hy1 (congrArg Subtype.val h'))
    have hnN' : (n : S.O) ∈ normalizer (S.Lbar g : Set S.O) := by
      rw [← subgroupOf_normalizer_eq (S.Lbar_le_Mbar g)] at hnN
      exact hnN
    have hna := S.fixes_of_mem_normalizer_Lbar h2 haQ hne hno hnN'
    have hmem := S.conj_mem_Dbar_of_fix haQ hne n.2 hna ht
    have e : (n : S.O) * t * (n : S.O)⁻¹ = y := congrArg Subtype.val hnt
    rwa [e] at hmem
  have : Finite (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    Finite.of_injective (fun e : S.Qt ≃ₗ[ZMod 2] S.Qt => (e : S.Qt → S.Qt))
      (fun _ _ h => LinearEquiv.ext (congrFun h))
  have h1 := Subgroup.card_le_of_le hLD
  rw [((S.lemma_3_11_two hTI (by omega) haQ hne hno).resolve_left hirr).1] at h1
  have h4 := S.card_Dbar_le_four haQ hne hno
  have h8 : 2 ^ 3 ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem exists_commute_not_mem_Qa (hTI : WeaklyClosedTITransitive.{u}) (hn : 4 ≤ S.width)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hirr : ¬ S.IsReducible) {t : S.O} (ht : t ∈ S.Dbar g) (ht1 : t ≠ 1) :
    ∃ h ∈ S.M, g * S.z * g⁻¹ * ((h * g) * S.z * (h * g)⁻¹) =
        (h * g) * S.z * (h * g)⁻¹ * (g * S.z * g⁻¹) ∧
      (h * g) * S.z * (h * g)⁻¹ ∉ S.Qa g ∧
      ∀ s ∈ S.Dbar g, s ≠ 1 → (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h * g) * S.z * (h * g)⁻¹)) =
        S.cl ((h * g) * S.z * (h * g)⁻¹) + S.cl (g * S.z * g⁻¹) := by
  obtain ⟨h, hh, hab, hbQa⟩ : ∃ h ∈ S.M, g * S.z * g⁻¹ * ((h * g) * S.z * (h * g)⁻¹) =
      (h * g) * S.z * (h * g)⁻¹ * (g * S.z * g⁻¹) ∧ (h * g) * S.z * (h * g)⁻¹ ∉ S.Qa g := by
    by_contra hcon
    push Not at hcon
    exact S.false_of_forall_commute_mem_Qa hTI hn haQ hne hno hirr ht ht1 hcon
  exact ⟨h, hh, hab, hbQa, fun s hs hs1 =>
    S.apply_cl_eq_add_of_not_mem_Qa hTI (by omega) haQ hne hno hirr hh hab hbQa hs hs1⟩

theorem card_Dbar_ne_four (hTI : WeaklyClosedTITransitive.{u}) (hn : 4 ≤ S.width) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hirr : ¬ S.IsReducible) : Nat.card (S.Dbar g) ≠ 4 := by
  classical
  intro hD4
  obtain ⟨t, ht, ht1⟩ := exists_mem_not_mem_finset_of_card_lt (H := S.Dbar g) {1}
    (by rw [Finset.card_singleton]; omega)
  simp only [Finset.mem_singleton] at ht1
  exact S.false_of_forall_commute_mem_Qa hTI hn haQ hne hno hirr ht ht1 fun h hh hab =>
    S.mem_Qa_of_commute_of_card_Dbar_eq_four hTI (by omega) haQ hne hno hirr hD4 hh hab

theorem fixLbar_eq_span_or (hTI : WeaklyClosedTITransitive.{u}) (hn : 4 ≤ S.width) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hirr : ¬ S.IsReducible) :
    S.fixLbar g = (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) ∨
      (Nat.card (S.Dbar g) = 2 ∧ ∃ h ∈ S.M, g * S.z * g⁻¹ * ((h * g) * S.z * (h * g)⁻¹) =
          (h * g) * S.z * (h * g)⁻¹ * (g * S.z * g⁻¹) ∧
        (h * g) * S.z * (h * g)⁻¹ ∉ S.Qa g ∧
        ∀ s ∈ S.Dbar g, s ≠ 1 → (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h * g) * S.z * (h * g)⁻¹)) =
          S.cl ((h * g) * S.z * (h * g)⁻¹) + S.cl (g * S.z * g⁻¹)) := by
  by_cases hD : ∀ s ∈ S.Lbar g,
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)) → s = 1
  · exact Or.inl ((S.fixLbar_eq_span_iff hTI (by omega) haQ hne hno hirr).mpr hD)
  right
  push Not at hD
  obtain ⟨t, htL, htN, ht1⟩ := hD
  have ht : t ∈ S.Dbar g := ⟨htL, htN⟩
  refine ⟨?_, S.exists_commute_not_mem_Qa hTI hn haQ hne hno hirr ht ht1⟩
  rcases S.card_Dbar_eq_one_or_two_or_four hTI (by omega) haQ hne hno hirr with h1 | h2 | h4
  · exfalso
    have hbot := Subgroup.card_eq_one.mp h1
    rw [hbot] at ht
    exact ht1 (Subgroup.mem_bot.mp ht)
  · exact h2
  · exact absurd h4 (S.card_Dbar_ne_four hTI hn haQ hne hno hirr)

end Setting

end CFSG.LargeExtraspecial

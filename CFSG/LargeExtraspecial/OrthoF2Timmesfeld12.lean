module

public import CFSG.LargeExtraspecial.OrthoF2Eichler

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply eichler_mul eichler_zero_right
  eichler_mem_orthogonalGroup)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

namespace OrthoF2

theorem orthogonal_sup (U U' : Submodule (ZMod 2) V) :
    LinearMap.BilinForm.orthogonal q.polarBilin (U ⊔ U') =
      LinearMap.BilinForm.orthogonal q.polarBilin U ⊓
        LinearMap.BilinForm.orthogonal q.polarBilin U' := by
  ext x
  simp only [Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    exact ⟨fun n hn => h n (Submodule.mem_sup_left hn),
      fun n hn => h n (Submodule.mem_sup_right hn)⟩
  · rintro ⟨h, h'⟩ n hn
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hn
    rw [map_add, LinearMap.add_apply, h y hy, h' z hz, add_zero]

theorem mem_orthogonalGroup_of_isTypeA {t : V ≃ₗ[ZMod 2] V} {l : ℕ} (h : IsTypeA q t l) :
    t ∈ orthogonalGroup q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr h.1

theorem eq_eichler_of_isTypeA [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {α : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2) {p x : V}
    (hli : LinearIndependent (ZMod 2) ![p, x])
    (hspan : commSpace α = Submodule.span (ZMod 2) {p, x}) :
    q p = 0 ∧ q x = 0 ∧ polar q p x = 0 ∧ α = eichler q p x := by
  have hsing := hα.2.2.2.2
  rw [hspan] at hsing
  have hp : q p = 0 := hsing p (Submodule.subset_span (by simp))
  have hx : q x = 0 := hsing x (Submodule.subset_span (by simp))
  have hpx : polar q p x = 0 := by
    have h := hsing (p + x) (Submodule.add_mem _ (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp)))
    rwa [map_add_eq, hp, hx, zero_add, zero_add] at h
  have hO := mem_orthogonalGroup_of_isTypeA hα
  refine ⟨hp, hx, hpx, ?_⟩
  have hfixα : ∀ y, polar q p y = 0 → polar q x y = 0 → α y = y := by
    intro y hyp hyx
    rw [← mem_fixSpace, fixSpace_eq_orthogonal_commSpace_of_mem hq hO, hspan]
    exact mem_orthogonal_span_pair_iff.mpr ⟨hyp, hyx⟩
  rcases eq_one_or_eq_eichler_of_totallySingular hq hli hp hx hpx hO hspan.le hfixα with h | h
  · exact absurd h hα.2.1
  · exact h

theorem exists_pair_of_mem_of_finrank_eq_two [FiniteDimensional (ZMod 2) V]
    {U : Submodule (ZMod 2) V} (hU2 : finrank (ZMod 2) U = 2) {p : V} (hp : p ∈ U)
    (hp0 : p ≠ 0) :
    ∃ x, LinearIndependent (ZMod 2) ![p, x] ∧ Submodule.span (ZMod 2) {p, x} = U := by
  have hlt : (ZMod 2) ∙ p < U := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem p U).mpr hp) fun h => ?_
    have h1 := finrank_span_singleton (K := ZMod 2) hp0
    rw [h, hU2] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨x, hxU, hxp⟩ := IsConcreteLE.exists_of_lt hlt
  have hli : LinearIndependent (ZMod 2) ![p, x] := by
    refine linearIndependent_pair_iff.mpr ⟨hp0, fun h => hxp (h ▸ Submodule.zero_mem _),
      fun h => hxp (h ▸ Submodule.mem_span_singleton_self p)⟩
  refine ⟨x, hli, Submodule.eq_of_le_of_finrank_eq ?_ (by rw [finrank_span_pair hli, hU2])⟩
  rw [Submodule.span_le]
  rintro y (rfl | rfl)
  · exact hp
  · exact hxU

theorem exists_eichler_of_isTypeA_pair [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2)
    (hβ : IsTypeA q β 2) (hne : commSpace α ≠ commSpace β) (hmeet : commSpace α ⊓ commSpace β ≠ ⊥) :
    ∃ p x y : V, p ≠ 0 ∧ LinearIndependent (ZMod 2) ![p, x] ∧
      LinearIndependent (ZMod 2) ![p, y] ∧ x + y ∉ (ZMod 2) ∙ p ∧
      q p = 0 ∧ q x = 0 ∧ q y = 0 ∧ polar q p x = 0 ∧ polar q p y = 0 ∧
      commSpace α = Submodule.span (ZMod 2) {p, x} ∧ commSpace β = Submodule.span (ZMod 2) {p, y} ∧
      α = eichler q p x ∧ β = eichler q p y := by
  obtain ⟨p, hpI, hp0⟩ := (Submodule.ne_bot_iff _).mp hmeet
  have hpα : p ∈ commSpace α := (Submodule.mem_inf.mp hpI).1
  have hpβ : p ∈ commSpace β := (Submodule.mem_inf.mp hpI).2
  obtain ⟨x, hlix, hspx⟩ := exists_pair_of_mem_of_finrank_eq_two hα.2.2.2.1 hpα hp0
  obtain ⟨y, hliy, hspy⟩ := exists_pair_of_mem_of_finrank_eq_two hβ.2.2.2.1 hpβ hp0
  obtain ⟨hqp, hqx, hpx, hαE⟩ := eq_eichler_of_isTypeA hq hα hlix hspx.symm
  obtain ⟨-, hqy, hpy, hβE⟩ := eq_eichler_of_isTypeA hq hβ hliy hspy.symm
  have hxy : x + y ∉ (ZMod 2) ∙ p := by
    intro hmem
    apply hne
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hyα : y ∈ commSpace α := by
      have : y = c • p + x := by
        rw [hc]
        rw [add_comm x y, add_assoc, vec_add_self, add_zero]
      rw [this]
      exact Submodule.add_mem _ (Submodule.smul_mem _ c hpα)
        (hspx ▸ Submodule.subset_span (by simp))
    have hle : commSpace β ≤ commSpace α := by
      rw [← hspy, Submodule.span_le]
      rintro z (rfl | rfl)
      · exact hpα
      · exact hyα
    exact (Submodule.eq_of_le_of_finrank_eq hle
      (by rw [hα.2.2.2.1, hβ.2.2.2.1])).symm
  exact ⟨p, x, y, hp0, hlix, hliy, hxy, hqp, hqx, hqy, hpx, hpy, hspx.symm, hspy.symm, hαE, hβE⟩

end OrthoF2

theorem isTypeC_mul_of_not_orthogonal [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2)
    (hβ : IsTypeA q β 2) (hne : commSpace α ≠ commSpace β) (hmeet : commSpace α ⊓ commSpace β ≠ ⊥)
    (hnot : ∃ x ∈ commSpace α, ∃ y ∈ commSpace β, polar q x y ≠ 0) :
    α * β = β * α ∧ IsTypeC q (α * β) 2 := by
  obtain ⟨p, x, y, hp0, -, -, hxy, hqp, hqx, hqy, hpx, hpy, hspx, hspy, rfl, rfl⟩ :=
    exists_eichler_of_isTypeA_pair hq hα hβ hne hmeet
  have hmul : eichler q p x * eichler q p y = eichler q p (x + y) := eichler_mul hpx hpy
  have hcomm : eichler q p x * eichler q p y = eichler q p y * eichler q p x := by
    rw [hmul, eichler_mul hpy hpx, add_comm]
  refine ⟨hcomm, ?_⟩
  have hxy1 : polar q x y = 1 := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnot
    rw [hspx] at ha
    rw [hspy] at hb
    obtain ⟨s, r, rfl⟩ := Submodule.mem_span_pair.mp ha
    obtain ⟨s', r', rfl⟩ := Submodule.mem_span_pair.mp hb
    apply zmod2_eq_one_of_ne_zero
    intro h0
    apply hab
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, smul_eq_mul,
      polar_self_eq_zero, polar_comm q x p, hpx, hpy, h0, mul_zero, add_zero]
  have hq1 : q (x + y) = 1 := by rw [map_add_eq, hqx, hqy, hxy1, zero_add, zero_add]
  have hpxy : polar q p (x + y) = 0 := by rw [polar_add_right, hpx, hpy, add_zero]
  rw [hmul]
  exact (eichler_isTypeC hq hp0 hqp hpxy hq1).1

theorem timmesfeld_12_1 [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2) (hβ : IsTypeA q β 2)
    (hαβ : IsTypeA q (α * β) 2) :
    commSpace α ≠ commSpace β ∧ commSpace α ⊓ commSpace β ≠ ⊥ ∧
      finrank (ZMod 2) ↥(commSpace α ⊓ commSpace β) = 1 ∧
      finrank (ZMod 2) ↥(commSpace α ⊔ commSpace β) = 3 ∧
      ∀ z ∈ commSpace α ⊔ commSpace β, q z = 0 := by
  have hαO := mem_orthogonalGroup_of_isTypeA hα
  have hβO := mem_orthogonalGroup_of_isTypeA hβ
  have hαβO := mem_orthogonalGroup_of_isTypeA hαβ
  have hne : commSpace α ≠ commSpace β := by
    intro heq
    have hU : ∀ u ∈ commSpace α, q u = 0 := hα.2.2.2.2
    obtain ⟨t, -, huniq⟩ := existsUnique_of_totallySingular_finrank_two hq hU hα.2.2.2.1
    have hfixα : ∀ x ∈ LinearMap.BilinForm.orthogonal q.polarBilin (commSpace α), α x = x :=
      fun x hx => mem_fixSpace.mp ((fixSpace_eq_orthogonal_commSpace_of_mem hq hαO).symm ▸ hx)
    have hfixβ : ∀ x ∈ LinearMap.BilinForm.orthogonal q.polarBilin (commSpace α), β x = x :=
      fun x hx => mem_fixSpace.mp ((fixSpace_eq_orthogonal_commSpace_of_mem hq hβO).symm ▸
        (heq ▸ hx))
    have h1 := huniq α ⟨hαO, hα.2.1, le_rfl, hfixα⟩
    have h2 := huniq β ⟨hβO, hβ.2.1, heq.symm.le, hfixβ⟩
    have hab : α = β := h1.trans h2.symm
    rw [← hab, hα.2.2.1] at hαβ
    exact hαβ.2.1 rfl
  have hmeet : commSpace α ⊓ commSpace β ≠ ⊥ := by
    intro hbot
    have hfix : fixSpace (α * β) = fixSpace α ⊓ fixSpace β := by
      ext v
      rw [Submodule.mem_inf, mem_fixSpace, mem_fixSpace, mem_fixSpace, LinearEquiv.mul_apply]
      constructor
      · intro h
        have hβv : β v = α v := by
          have := congrArg α h
          rwa [apply_apply_of_mul_self hα.2.2.1] at this
        have hmem : α v - v ∈ commSpace α ⊓ commSpace β :=
          Submodule.mem_inf.mpr ⟨sub_mem_commSpace α v, hβv ▸ sub_mem_commSpace β v⟩
        rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
        exact ⟨hmem, hβv.trans hmem⟩
      · rintro ⟨h1, h2⟩
        rw [h2, h1]
    rw [fixSpace_eq_orthogonal_commSpace_of_mem hq hαO,
      fixSpace_eq_orthogonal_commSpace_of_mem hq hβO, ← orthogonal_sup] at hfix
    have h1 := finrank_commSpace_add_finrank_fixSpace (α * β)
    rw [hfix, LinearMap.BilinForm.finrank_orthogonal hq, hαβ.2.2.2.1] at h1
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (commSpace α) (commSpace β)
    rw [hbot, finrank_bot, hα.2.2.2.1, hβ.2.2.2.1] at h2
    have h3 := Submodule.finrank_le (commSpace α ⊔ commSpace β)
    omega
  have hinf : finrank (ZMod 2) ↥(commSpace α ⊓ commSpace β) = 1 := by
    have h1 : 1 ≤ finrank (ZMod 2) ↥(commSpace α ⊓ commSpace β) :=
      Submodule.one_le_finrank_iff.mpr hmeet
    have h2 := Submodule.finrank_mono (inf_le_left : commSpace α ⊓ commSpace β ≤ commSpace α)
    rw [hα.2.2.2.1] at h2
    by_contra h3
    have h4 : finrank (ZMod 2) ↥(commSpace α ⊓ commSpace β) = 2 := by omega
    apply hne
    have e1 := Submodule.eq_of_le_of_finrank_eq (inf_le_left : commSpace α ⊓ commSpace β ≤ _)
      (by rw [h4, hα.2.2.2.1])
    have e2 := Submodule.eq_of_le_of_finrank_eq (inf_le_right : commSpace α ⊓ commSpace β ≤ _)
      (by rw [h4, hβ.2.2.2.1])
    rw [← e1, e2]
  have hsup : finrank (ZMod 2) ↥(commSpace α ⊔ commSpace β) = 3 := by
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (commSpace α) (commSpace β)
    rw [hinf, hα.2.2.2.1, hβ.2.2.2.1] at h2
    omega
  refine ⟨hne, hmeet, hinf, hsup, ?_⟩
  have horth : ∀ x ∈ commSpace α, ∀ y ∈ commSpace β, polar q x y = 0 := by
    by_contra! h
    obtain ⟨-, hC⟩ := isTypeC_mul_of_not_orthogonal hq hα hβ hne hmeet h
    obtain ⟨-, -, -, -, -, z, hz, hqz⟩ := hC
    exact hqz (hαβ.2.2.2.2 z hz)
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
  rw [map_add_eq, hα.2.2.2.2 a ha, hβ.2.2.2.2 b hb, horth a ha b hb, add_zero, add_zero]

theorem timmesfeld_12_2 [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ orthogonalGroup q) (ht1 : t ≠ 1) {v w : V}
    (hli : LinearIndependent (ZMod 2) ![v, w]) (hv : q v = 0) (hw : q w = 0)
    (hvw : polar q v w = 0) (hfix : ∀ x, polar q v x = 0 → polar q w x = 0 → t x = x) :
    IsTypeA q t 2 ∧ commSpace t = Submodule.span (ZMod 2) {v, w} ∧
      (LinearMap.BilinForm.orthogonal q.polarBilin ((ZMod 2) ∙ v)).map
          ((t : V →ₗ[ZMod 2] V) - 1) = (ZMod 2) ∙ v ∧
      (LinearMap.BilinForm.orthogonal q.polarBilin ((ZMod 2) ∙ w)).map
          ((t : V →ₗ[ZMod 2] V) - 1) = (ZMod 2) ∙ w := by
  have hcomm : commSpace t ≤ Submodule.span (ZMod 2) {v, w} := by
    rw [commSpace_eq_orthogonal_fixSpace_of_mem hq ht]
    have hle : LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {v, w}) ≤
        fixSpace t := fun x hx => by
      obtain ⟨hxv, hxw⟩ := mem_orthogonal_span_pair_iff.mp hx
      exact mem_fixSpace.mpr (hfix x hxv hxw)
    calc LinearMap.BilinForm.orthogonal q.polarBilin (fixSpace t)
        ≤ LinearMap.BilinForm.orthogonal q.polarBilin
            (LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {v, w})) :=
          LinearMap.BilinForm.orthogonal_le hle
      _ = Submodule.span (ZMod 2) {v, w} :=
          LinearMap.BilinForm.orthogonal_orthogonal hq (isRefl_polarBilin q) _
  rcases eq_one_or_eq_eichler_of_totallySingular hq hli hv hw hvw ht hcomm hfix with h | h
  · exact absurd h ht1
  subst h
  obtain ⟨hA, hc, -⟩ := eichler_of_totallySingular hq hli hv hw hvw
  obtain ⟨xv, hxvv, hxvw⟩ := exists_polar_eq_one_polar_eq_zero hq hli
  obtain ⟨xw, hxww, hxwv⟩ :=
    exists_polar_eq_one_polar_eq_zero hq (linearIndependent_pair_symm hli)
  refine ⟨hA, hc, le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxv : polar q v x = 0 := mem_orthogonal_span_singleton_iff.mp hx
    rw [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply,
      eichler_apply_zmod2 hv hvw, polar_comm q x v, hxv, hw]
    simp only [zero_smul, mul_zero, add_zero, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  · rw [Submodule.span_singleton_le_iff_mem]
    refine ⟨xw, mem_orthogonal_span_singleton_iff.mpr (by rw [polar_comm]; exact hxwv), ?_⟩
    rw [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply,
      eichler_apply_zmod2 hv hvw, hxwv, hxww, hw]
    simp
  · rintro _ ⟨x, hx, rfl⟩
    have hxw : polar q w x = 0 := mem_orthogonal_span_singleton_iff.mp hx
    rw [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply,
      eichler_apply_zmod2 hv hvw, polar_comm q x w, hxw, hw]
    simp only [zero_smul, zero_mul, add_zero, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  · rw [Submodule.span_singleton_le_iff_mem]
    refine ⟨xv, mem_orthogonal_span_singleton_iff.mpr (by rw [polar_comm]; exact hxvw), ?_⟩
    rw [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply,
      eichler_apply_zmod2 hv hvw, hxvv, hxvw, hw]
    simp

end CFSG.LargeExtraspecial

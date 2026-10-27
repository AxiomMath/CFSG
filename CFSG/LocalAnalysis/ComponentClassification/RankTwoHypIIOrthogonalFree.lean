module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIOrthogonalLevi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIOrthogonalDefs
public import CFSG.RankThree.OrthogonalInvolutions.Conjugacy
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega

public section

namespace CFSG.ComponentClassification.RankTwoHypIIOrthogonal

open Module QuadraticMap Subgroup CFSG.RankThree.OrthogonalInvolutions
open CFSG.ClassicalGroups.Orthogonal CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.FieldFix (orthDerived_le_omegaGroup omegaGroup_le_orthDerived)

section Abstract

variable {K V : Type*} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem false_of_linearConfig (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : orthDerived Q = elementaryGroup Q) (F : Subgroup (V ≃ₗ[K] V))
    (hFO : F ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (hsq : ∀ a ∈ F, a * a = 1)
    (h4 : 4 ≤ Nat.card F) (hFD : ¬ F ≤ orthDerived Q)
    (hN : ∀ x ∈ F, x ≠ 1 → ∀ g ∈ orthDerived Q, g * x = x * g → ∀ f ∈ F, g * f * g⁻¹ ∈ F) :
    False := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hEich : ∀ u w, eichler Q u w ∈ orthDerived Q := fun u w =>
    hE ▸ eichler_mem_elementaryGroup Q u w
  have hF2 : IsPGroup 2 F := fun g => ⟨1, by rw [pow_one, pow_two]; exact Subtype.ext (hsq g g.2)⟩
  have hin : ∀ g ∈ orthDerived Q, Even (finrank K (commSpace g)) := fun g hg =>
    (orthDerived_le_omegaGroup hQ hg).2
  have hout : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g ∉ orthDerived Q →
      Odd (finrank K (commSpace g)) := fun g hg hgD =>
    Nat.not_even_iff_odd.mp fun he => hgD (omegaGroup_le_orthDerived hQ hT ⟨hg, he⟩)
  have hnz : ∀ y ∈ F, y ∉ orthDerived Q → ∃ a ∈ commSpace y, Q a ≠ 0 := by
    intro y hy hyD
    by_contra! h
    exact Nat.not_even_iff_odd.mpr (hout y (hFO hy) hyD)
      (even_finrank_commSpace_of_forall_eq_zero hQ (hFO hy) (hsq y hy) h)
  have hconj : ∀ y ∈ F, y ≠ 1 → ∀ g ∈ orthDerived Q, g * y = y * g → ∀ f ∈ F,
      g⁻¹ * f * g ∈ F := by
    intro y hy hy1 g hg hgy f hf
    have h1 : g⁻¹ * y = y * g⁻¹ := by
      calc g⁻¹ * y = g⁻¹ * (y * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * y) * g⁻¹ := by rw [hgy]
        _ = y * g⁻¹ := by group
    have h2 := hN y hy hy1 g⁻¹ (inv_mem hg) h1 f hf
    rwa [inv_inv] at h2
  have hA : ∀ y ∈ F, y ∉ orthDerived Q → ∀ f ∈ F, ∀ z ∈ commSpace y, f z = z := by
    intro y hy hyD f hf z hz
    have hy1 : y ≠ 1 := fun h => hyD (h ▸ one_mem _)
    exact apply_eq_of_mem_commSpace hQ (hFO hy) (hsq y hy) (hout y (hFO hy) hyD) hFO hF2
      (fun f hf => hcomm f hf y hy)
      (fun w hw f hf => hconj y hy hy1 _ (hEich _ _)
        (eichler_sub_mul_comm (hFO hy) (hsq y hy) hw) f hf) hf hz
  obtain ⟨t, htF, htD⟩ := Set.not_subset.mp hFD
  have htO := hFO htF
  have htt := hsq t htF
  have ht1 : t ≠ 1 := fun h => htD (h ▸ one_mem _)
  have hB : ∀ g ∈ F, ∀ f ∈ F, ∀ z ∈ commSpace g, f z = z := by
    intro g hg f hf z hz
    by_cases hgD : g ∈ orthDerived Q
    · have htgD : t * g ∉ orthDerived Q := fun h => htD (by
        have h' := mul_mem h (inv_mem hgD)
        rwa [mul_inv_cancel_right] at h')
      have htg : t * g ∈ F := mul_mem htF hg
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hz
      have hrel : g v - v = t ((t * g) v - v - (t v - v)) := by
        rw [LinearEquiv.mul_apply, sub_sub_sub_cancel_right, map_sub,
          apply_apply_of_mul_self htt, apply_apply_of_mul_self htt]
      have h1 := hA (t * g) htg htgD f hf _ (sub_mem_commSpace (t * g) v)
      have h2 := hA t htF htD f hf _ (sub_mem_commSpace t v)
      have h3 : f (t ((t * g) v - v - (t v - v))) = t (f ((t * g) v - v - (t v - v))) := by
        rw [← LinearEquiv.mul_apply, hcomm f hf t htF, LinearEquiv.mul_apply]
      rw [hrel, h3, map_sub, h1, h2]
    · exact hA g hg hgD f hf z hz
  set W : Submodule K V := ⨆ g : F, commSpace (g : V ≃ₗ[K] V) with hWdef
  have hgW : ∀ g ∈ F, commSpace g ≤ W := fun g hg =>
    le_iSup (fun g : F => commSpace (g : V ≃ₗ[K] V)) ⟨g, hg⟩
  have hWfix : ∀ f ∈ F, W ≤ fixSpace f := fun f hf =>
    iSup_le fun g z hz => mem_fixSpace.mpr (hB g g.2 f hf z hz)
  have hWiso : ∀ w₁ ∈ W, ∀ w₂ ∈ W, polar Q w₁ w₂ = 0 := by
    intro w₁ hw₁ w₂ hw₂
    refine Submodule.iSup_induction (fun g : F => commSpace (g : V ≃ₗ[K] V))
      (motive := fun w₂ => polar Q w₁ w₂ = 0) hw₂ ?_ ?_ ?_
    · intro g z hz
      have h := (fixSpace_eq_orthogonal_commSpace hQ (hFO g.2) (hsq g g.2)).le
        (hWfix g g.2 hw₁)
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at h
      have h' : Q.polarBilin z w₁ = 0 := h z hz
      rw [polarBilin_apply_apply, polar_comm] at h'
      exact h'
    · exact polar_zero_right Q w₁
    · intro x y hx hy
      rw [polar_add_right, hx, hy, add_zero]
  have hWinv : ∀ g : V ≃ₗ[K] V, (∀ f ∈ F, g * f * g⁻¹ ∈ F) → ∀ w ∈ W, g w ∈ W := by
    intro g hg w hw
    refine Submodule.iSup_induction (fun g : F => commSpace (g : V ≃ₗ[K] V))
      (motive := fun w => g w ∈ W) hw ?_ ?_ ?_
    · intro f z hz
      apply hgW _ (hg f f.2)
      rw [commSpace_conj]
      exact Submodule.mem_map_of_mem hz
    · rw [map_zero]
      exact W.zero_mem
    · intro x y hx hy
      rw [map_add]
      exact W.add_mem hx hy
  have hEinv : ∀ y ∈ F, y ≠ 1 → ∀ u a : V, u ∈ fixSpace y → a ∈ fixSpace y → ∀ w ∈ W,
      eichler Q u a w ∈ W := fun y hy hy1 u a hu ha w hw =>
    hWinv _ (hN y hy hy1 _ (hEich u a) (eichler_mul_comm (hFO hy) hu ha)) w hw
  obtain ⟨a, haZ, hQa⟩ := hnz t htF htD
  have hWt : W ≤ commSpace t := le_commSpace_of_eichler hQ htO htt haZ hQa (hWfix t htF) hWiso
    (fun u hu _ w hw => hEinv t htF ht1 u a hu (commSpace_le_fixSpace htt haZ) w hw)
  have hWeq : W = commSpace t := le_antisymm hWt (hgW t htF)
  obtain ⟨x, hxF, hxD, hx1⟩ : ∃ x ∈ F, x ∈ orthDerived Q ∧ x ≠ 1 := by
    obtain ⟨f, hfF, hf1, hft⟩ : ∃ f ∈ F, f ≠ 1 ∧ f ≠ t := by
      by_contra! h
      have hsub : (F : Set (V ≃ₗ[K] V)) ⊆ {1, t} := fun f hf => by
        by_cases h1 : f = 1
        · exact Or.inl h1
        · exact Or.inr (h f hf h1)
      have hcard : Nat.card F = (F : Set (V ≃ₗ[K] V)).ncard :=
        Nat.card_coe_set_eq (F : Set (V ≃ₗ[K] V))
      have h2 : (F : Set (V ≃ₗ[K] V)).ncard ≤ 2 :=
        calc (F : Set (V ≃ₗ[K] V)).ncard ≤ ({1, t} : Set (V ≃ₗ[K] V)).ncard :=
              Set.ncard_le_ncard hsub (Set.toFinite _)
          _ ≤ ({t} : Set (V ≃ₗ[K] V)).ncard + 1 := Set.ncard_insert_le 1 {t}
          _ = 2 := by rw [Set.ncard_singleton]
      omega
    by_cases hfD : f ∈ orthDerived Q
    · exact ⟨f, hfF, hfD, hf1⟩
    · refine ⟨t * f, mul_mem htF hfF, ?_, ?_⟩
      · apply omegaGroup_le_orthDerived hQ hT
        refine ⟨mul_mem htO (hFO hfF), ?_⟩
        rw [← ZMod.natCast_eq_zero_iff_even, natCast_finrank_commSpace_mul hQ htO (hFO hfF),
          ZMod.natCast_eq_one_iff_odd.mpr (hout t htO htD),
          ZMod.natCast_eq_one_iff_odd.mpr (hout f (hFO hfF) hfD)]
        decide
      · intro h
        apply hft
        rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right htt]
  have hxO := hFO hxF
  have hxx := hsq x hxF
  have hxW : commSpace x ≤ commSpace t := hWeq ▸ hgW x hxF
  have hx2 : 2 ≤ finrank K (commSpace x) := by
    have h1 := one_le_finrank_commSpace hx1
    obtain ⟨k, hk⟩ := hin x hxD
    omega
  have htodd := hout t htO htD
  by_cases hxa : ∃ a ∈ commSpace x, Q a ≠ 0
  ·
    obtain ⟨a₀, ha₀, hQa₀⟩ := hxa
    have hWx : W ≤ commSpace x := le_commSpace_of_eichler hQ hxO hxx ha₀ hQa₀ (hWfix x hxF)
      hWiso (fun u hu _ w hw => hEinv x hxF hx1 u a₀ hu (commSpace_le_fixSpace hxx ha₀) w hw)
    have h1 := Submodule.finrank_mono hxW
    have h2 : finrank K (commSpace t) ≤ finrank K (commSpace x) := by
      rw [← hWeq]
      exact Submodule.finrank_mono hWx
    obtain ⟨k, hk⟩ := hin x hxD
    obtain ⟨m, hm⟩ := htodd
    omega
  ·
    push Not at hxa
    obtain ⟨v₁, hv₁⟩ : ∃ v, x v ≠ v := by
      by_contra! h
      exact hx1 (LinearEquiv.ext h)
    obtain ⟨v₂, rfl⟩ := mem_commSpace.mp haZ
    have hadd : ∀ p q : V, Q (t (p + q) - (p + q)) = Q (t p - p) + Q (t q - q) := by
      intro p q
      rw [map_add, show t p + t q - (p + q) = (t p - p) + (t q - q) by abel, map_add_eq,
        polar_commSpace_eq_zero htO htt (sub_mem_commSpace t p) (sub_mem_commSpace t q),
        add_zero]
    obtain ⟨v, hxv, hQv⟩ : ∃ v, x v ≠ v ∧ Q (t v - v) ≠ 0 := by
      by_cases h1 : Q (t v₁ - v₁) = 0
      · by_cases h2 : x v₂ = v₂
        · refine ⟨v₁ + v₂, ?_, ?_⟩
          · rw [map_add, h2]
            intro h
            exact hv₁ (add_right_cancel h)
          · rw [hadd, h1, zero_add]
            exact hQa
        · exact ⟨v₂, h2, hQa⟩
      · exact ⟨v₁, hv₁, h1⟩
    set w := x v - v with hwdef
    have hwx : w ∈ commSpace x := sub_mem_commSpace x v
    have hQw : Q w = 0 := hxa w hwx
    have hw0 : w ≠ 0 := sub_ne_zero.mpr hxv
    have hwv : polar Q w v = 0 := by rw [hwdef, polar_sub_self_eq hxO, ← hwdef, hQw]
    have hwW : w ∈ W := hWeq.ge (hxW hwx)
    have hwt : t w = w := mem_fixSpace.mp (hWfix t htF hwW)
    set p := v - t v with hpdef
    have hpW : p ∈ W := by
      rw [hWeq, hpdef, ← neg_sub]
      exact (commSpace t).neg_mem (sub_mem_commSpace t v)
    have hwp : polar Q w p = 0 := hWiso w hwW p hpW
    have hQp : Q p = Q (t v - v) := by rw [hpdef, ← neg_sub, QuadraticMap.map_neg]
    have hgx : eichler Q w v * x = x * eichler Q w v := by
      have h := eichler_conj hxO w v
      have hxw : x w = w := mem_fixSpace.mp (commSpace_le_fixSpace hxx hwx)
      have hxv' : eichler Q (x w) (x v) = eichler Q w v := by
        rw [hxw]
        calc eichler Q w (x v) = eichler Q w (v + (1 : K) • w) := by
              congr 1
              rw [one_smul, hwdef]
              abel
          _ = eichler Q w v := eichler_add_smul_self hQw v 1
      rw [hxv'] at h
      calc eichler Q w v * x = (x * eichler Q w v * x⁻¹) * x := by rw [h]
        _ = x * eichler Q w v := by group
    have hgt := hN x hxF hx1 _ (hEich w v) hgx t htF
    have hkF : eichler Q w p ∈ F := by
      have hwtv : polar Q w (t v) = 0 := by
        have h := polar_map_of_mem htO w v
        rw [hwt] at h
        rw [h, hwv]
      have htg : t * eichler Q w v * t⁻¹ = eichler Q w (t v) := by
        rw [eichler_conj htO, hwt]
      have hk : eichler Q w v * t * (eichler Q w v)⁻¹ * t⁻¹ = eichler Q w p := by
        have h1 : t * (eichler Q w v)⁻¹ * t⁻¹ = (eichler Q w (t v))⁻¹ := by
          rw [← htg]
          group
        calc eichler Q w v * t * (eichler Q w v)⁻¹ * t⁻¹ =
              eichler Q w v * (t * (eichler Q w v)⁻¹ * t⁻¹) := by group
          _ = eichler Q w v * eichler Q w (-(t v)) := by rw [h1, eichler_inv hwtv]
          _ = eichler Q w p := by
            rw [eichler_mul hwv (by rw [polar_neg_right, hwtv, neg_zero]), hpdef, sub_eq_add_neg]
      rw [← hk]
      exact mul_mem hgt (inv_mem htF)
    have hkO := hFO hkF
    have hkk := hsq _ hkF
    have hwp' : polar Q w p = 0 := hwp
    have hkapp : ∀ y, eichler Q w p y - y =
        polar Q y w • p - (polar Q y p + Q p * polar Q y w) • w := by
      intro y
      rw [eichler_apply hQw hwp']
      abel
    obtain ⟨y, hy⟩ := CFSG.ClassicalGroups.Orthogonal.exists_polar_ne_zero hQ hw0
    have hy' : polar Q y w ≠ 0 := by rwa [polar_comm]
    have hpw : polar Q p w = 0 := by rw [polar_comm]; exact hwp
    have hQk : Q (eichler Q w p y - y) ≠ 0 := by
      rw [hkapp, sub_eq_add_vec K, map_add_eq, QuadraticMap.map_smul, QuadraticMap.map_smul, hQw,
        smul_zero, add_zero, polar_smul_left, polar_smul_right, hpw, smul_zero, smul_zero,
        add_zero, smul_eq_mul, hQp]
      exact mul_ne_zero (mul_ne_zero hy' hy') hQv
    have hk1 : eichler Q w p ≠ 1 := by
      intro h
      rw [h] at hQk
      simp at hQk
    have hWk : W ≤ commSpace (eichler Q w p) :=
      le_commSpace_of_eichler hQ hkO hkk (sub_mem_commSpace _ y) hQk (hWfix _ hkF) hWiso
        (fun u hu _ w' hw' => hEinv _ hkF hk1 u _ hu
          (commSpace_le_fixSpace hkk (sub_mem_commSpace _ y)) w' hw')
    have hkspan : commSpace (eichler Q w p) ≤ Submodule.span K ({p, w} : Set V) := by
      intro z hz
      obtain ⟨y', rfl⟩ := mem_commSpace.mp hz
      rw [hkapp]
      exact Submodule.sub_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))
    have hspan : finrank K (Submodule.span K ({p, w} : Set V)) ≤ 2 := by
      have h := finrank_span_finset_le_card (R := K) ({p, w} : Finset V)
      rw [Set.finrank, Finset.coe_insert, Finset.coe_singleton] at h
      exact h.trans (Finset.card_insert_le _ _)
    have h1 : finrank K (commSpace t) ≤ 2 := by
      rw [← hWeq]
      exact (Submodule.finrank_mono (hWk.trans hkspan)).trans hspan
    have h2 := Submodule.finrank_mono hxW
    obtain ⟨m, hm⟩ := htodd
    omega

end Abstract

theorem orthLinearConfigFree : OrthLinearConfigFree := by
  intro K _ _ _ n _ Q hQ hT hE F hFO hFel h4 hFD _ hFN
  set φ : GL (Fin (2 * n)) K ≃* ((Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) :=
    matrixLinearIso with hφ
  have hmapO : (matrixIsometries Q).map φ.toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [matrixIsometries]
    exact Subgroup.map_comap_eq_self_of_surjective φ.surjective _
  have hmapD : (matrixDerived Q).map φ.toMonoidHom = orthDerived Q := by
    rw [matrixDerived, Subgroup.map_commutator, hmapO]
  refine false_of_linearConfig hQ hT hE (F.map φ.toMonoidHom) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← hmapO]
    exact Subgroup.map_mono hFO
  · rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    have h := hFel.1.is_comm.comm ⟨A, hA⟩ ⟨B, hB⟩
    rw [← map_mul, ← map_mul]
    exact congrArg φ.toMonoidHom (congrArg Subtype.val h)
  · rintro _ ⟨A, hA, rfl⟩
    rw [← map_mul, ← pow_two, hFel.2 A hA, map_one]
  · rw [Subgroup.card_map_of_injective φ.injective]
    exact h4
  · intro hle
    apply hFD
    intro A hA
    have hA' : φ.toMonoidHom A ∈ (matrixDerived Q).map φ.toMonoidHom :=
      hmapD ▸ hle ⟨A, hA, rfl⟩
    obtain ⟨B, hB, hBA⟩ := hA'
    rwa [φ.injective hBA] at hB
  · rintro _ ⟨x, hx, rfl⟩ hx1 g' hg' hg'x _ ⟨f, hf, rfl⟩
    rw [← hmapD] at hg'
    obtain ⟨g, hg, rfl⟩ := hg'
    have hx1' : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have hgx : g * x = x * g := by
      apply φ.injective
      have h := hg'x
      rw [← map_mul, ← map_mul] at h
      exact h
    have hgN := hFN x hx hx1' ⟨hg, mem_centralizer_singleton_iff.mpr hgx⟩
    refine ⟨g * f * g⁻¹, (mem_normalizer_iff.mp hgN f).mp hf, ?_⟩
    rw [map_mul, map_mul, map_inv]

end CFSG.ComponentClassification.RankTwoHypIIOrthogonal

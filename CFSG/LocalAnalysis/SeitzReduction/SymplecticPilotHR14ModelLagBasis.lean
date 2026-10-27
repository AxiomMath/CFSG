module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaClasses
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelLagStd
public import CFSG.RankThree.PartOne.KC.AlternatingSymplecticBasis

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.PartOne.KCAlternating (IsSymplecticBasis exists_isSymplecticBasis)

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

section Sums

theorem lag_polar_sum_left {ι : Type*} (S : Finset ι) (u : ι → V) (y : V) :
    polar Q (∑ i ∈ S, u i) y = ∑ i ∈ S, polar Q (u i) y := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, polar_add_left, ih]

theorem lag_polar_sum_right {ι : Type*} (S : Finset ι) (x : V) (u : ι → V) :
    polar Q x (∑ i ∈ S, u i) = ∑ i ∈ S, polar Q x (u i) := by
  rw [polar_comm, lag_polar_sum_left]
  exact Finset.sum_congr rfl fun i _ => polar_comm _ _ _

theorem lag_map_sum_eq_zero {ι : Type*} (S : Finset ι) (u : ι → V) (c : ι → F)
    (hQ : ∀ i ∈ S, Q (u i) = 0) (hp : ∀ i ∈ S, ∀ j ∈ S, polar Q (u i) (u j) = 0) :
    Q (∑ i ∈ S, c i • u i) = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, QuadraticMap.map_add Q, QuadraticMap.map_smul,
      hQ i (Finset.mem_insert_self i S), smul_zero, zero_add,
      ih (fun j hj => hQ j (Finset.mem_insert_of_mem hj))
        (fun j hj k hk => hp j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)),
      zero_add, lag_polar_sum_right]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [polar_smul_left, polar_smul_right,
      hp i (Finset.mem_insert_self i S) j (Finset.mem_insert_of_mem hj), smul_zero, smul_zero]

end Sums

section Coordinates

variable [CharP F 2] [FiniteDimensional F V]

theorem exists_lagBasis (hnd : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[F] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) {m : ℕ}
    (hdimW : finrank F (omegaInvSpace s) = 2 * m) (hdim : finrank F V = 2 * (2 * m))
    (hQW : ∀ w ∈ omegaInvSpace s, Q w = 0) :
    ∃ b : Basis ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F V,
      (∀ x, Q (b x) = 0) ∧
      (∀ a a', polar Q (b (Sum.inl a)) (b (Sum.inl a')) = 0) ∧
      (∀ d d', polar Q (b (Sum.inr d)) (b (Sum.inr d')) = 0) ∧
      (∀ a d, polar Q (b (Sum.inl a)) (b (Sum.inr d)) = if d = a then 1 else 0) ∧
      (∀ a, s (b (Sum.inl a)) = b (Sum.inl a)) ∧
      (∀ d, s (b (Sum.inr d)) = b (Sum.inr d) + b (Sum.inl d.swap)) := by
  classical
  set W := omegaInvSpace s with hWdef
  have hWiso : ∀ v ∈ W, ∀ w ∈ W, polar Q v w = 0 := fun v hv w hw =>
    polar_of_mem_omegaInvSpace hs hss hv hw
  have hNW : ∀ w ∈ W, omegaInvNil s w = 0 := fun w hw => omegaInvNil_of_mem_omegaInvSpace hss hw
  have hker : LinearMap.ker (omegaInvNil s) = W := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq fun w hw => hNW w hw
    have h := LinearMap.finrank_range_add_finrank_ker (omegaInvNil s)
    have h2 : finrank F (LinearMap.range (omegaInvNil s)) = 2 * m := hdimW
    omega
  obtain ⟨W'', hc⟩ := Submodule.exists_isCompl W
  have hW'' : finrank F W'' = 2 * m := by
    have := Submodule.finrank_add_eq_of_isCompl hc
    omega
  set β : LinearMap.BilinForm F V := (polarBilin Q).compl₁₂ (omegaInvNil s) LinearMap.id with hβ
  have hβapp : ∀ x y : W'', β.restrict W'' x y = polar Q (omegaInvNil s x) y := fun x y => rfl
  have hβsymm : ∀ x y : V, polar Q (omegaInvNil s x) y = polar Q (omegaInvNil s y) x :=
    fun x y => by rw [polar_omegaInvNil_left hs hss, polar_comm]
  have hβalt : (β.restrict W'').IsAlt := fun x => by
    rw [hβapp, polar_comm, ← map_omegaInvNil hs, hQW _ (omegaInvNil_mem_omegaInvSpace s _)]
  have hsep : ∀ x : W'', (∀ y : W'', β.restrict W'' x y = 0) → x = 0 := by
    intro x hx
    have h1 : ∀ v, polar Q (omegaInvNil s x) v = 0 := by
      intro v
      obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
      rw [polar_add_right, hWiso _ (omegaInvNil_mem_omegaInvSpace s _) _ hw, zero_add]
      exact hx ⟨y, hy⟩
    have h2 : omegaInvNil s x = 0 := eq_zero_of_polar_eq_zero hnd h1
    have h3 : (x : V) ∈ W := hker ▸ LinearMap.mem_ker.2 h2
    have h4 : (x : V) ∈ W ⊓ W'' := ⟨h3, x.2⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at h4
    exact Subtype.ext h4
  have hβnd : (β.restrict W'').Nondegenerate :=
    ⟨hsep, fun y hy => hsep y fun x => by rw [hβapp, hβsymm]; exact hy x⟩
  obtain ⟨n', g, hn', hg⟩ := exists_isSymplecticBasis hβalt hβnd
  obtain rfl : m = n' := by omega
  obtain ⟨gv, hgv⟩ : ∃ gv : Fin m ⊕ Fin m → V, ∀ c, gv c = ((g c : W'') : V) :=
    ⟨fun c => g c, fun _ => rfl⟩
  have hβg : ∀ c d, polar Q (omegaInvNil s (gv c)) (gv d) = if d = c.swap then 1 else 0 := by
    intro c d
    rw [hgv, hgv]
    rcases c with i | i <;> rcases d with j | j
    · have h := hg.1 i j
      rw [hβapp] at h
      simp [Sum.swap, h]
    · have h := hg.2.2 i j
      rw [hβapp] at h
      rw [h]
      simp [Sum.swap, eq_comm]
    · have h := hg.2.2 j i
      rw [hβapp, hβsymm] at h
      rw [h]
      simp [Sum.swap, eq_comm]
    · have h := hg.2.1 i j
      rw [hβapp] at h
      simp [Sum.swap, h]
  obtain ⟨e, he⟩ : ∃ e : Fin m ⊕ Fin m → V, ∀ a, e a = omegaInvNil s (gv a.swap) :=
    ⟨_, fun _ => rfl⟩
  have heW : ∀ a, e a ∈ W := fun a => he a ▸ omegaInvNil_mem_omegaInvSpace s _
  have heg : ∀ a d, polar Q (e a) (gv d) = if d = a then 1 else 0 := fun a d => by
    rw [he, hβg, Sum.swap_swap]
  obtain ⟨t, ht⟩ : ∃ t : Fin m ⊕ Fin m → Fin m ⊕ Fin m → F, ∀ d c, t d c = if c = d then Q (gv d)
      else if lagNum c < lagNum d then polar Q (gv d) (gv c) else 0 := ⟨_, fun _ _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin m ⊕ Fin m → V, ∀ d, w d = ∑ c, t d c • e c := ⟨_, fun _ => rfl⟩
  have hwW : ∀ d, w d ∈ W := fun d => hw d ▸
    Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (heW c)
  have hgw : ∀ c d, polar Q (gv c) (w d) = t d c := by
    intro c d
    rw [hw, lag_polar_sum_right]
    simp_rw [polar_smul_right, polar_comm Q (gv c), heg]
    simp
  obtain ⟨f, hf⟩ : ∃ f : Fin m ⊕ Fin m → V, ∀ d, f d = gv d + w d := ⟨_, fun _ => rfl⟩
  have hQf : ∀ d, Q (f d) = 0 := by
    intro d
    rw [hf, QuadraticMap.map_add Q, hQW _ (hwW d), add_zero, hgw, ht, ite_eq_left rfl]
    exact CharTwo.add_self_eq_zero _
  have hff : ∀ c d, polar Q (f c) (f d) = 0 := by
    intro c d
    by_cases hcd : c = d
    · rw [hcd, polar_self, hQf, smul_zero]
    rw [hf, hf, polar_add_left, polar_add_right, polar_add_right, hgw, polar_comm Q (w c), hgw,
      hWiso _ (hwW c) _ (hwW d), add_zero, ht, ht, ite_eq_right hcd, ite_eq_right (Ne.symm hcd)]
    rcases lt_or_gt_of_ne (fun h => hcd (lagNum_injective h)) with h | h
    · rw [ite_eq_left h, ite_eq_right (by omega), add_zero, polar_comm Q (gv d),
        CharTwo.add_self_eq_zero]
    · rw [ite_eq_right (by omega), ite_eq_left h, add_zero, CharTwo.add_self_eq_zero]
  have hef : ∀ a d, polar Q (e a) (f d) = if d = a then 1 else 0 := by
    intro a d
    rw [hf, polar_add_right, heg, hWiso _ (heW a) _ (hwW d), add_zero]
  have hee : ∀ a a', polar Q (e a) (e a') = 0 := fun a a' => hWiso _ (heW a) _ (heW a')
  have hli : LinearIndependent F (Sum.elim e f) := by
    rw [Fintype.linearIndependent_iff]
    intro c hsum x
    rw [Fintype.sum_sum_type] at hsum
    rcases x with a₀ | d₀
    · have h := congrArg (fun v => polar Q v (f a₀)) hsum
      simp only [polar_zero_left, polar_add_left, lag_polar_sum_left, polar_smul_left,
        Sum.elim_inl, Sum.elim_inr, hef, hff, smul_eq_mul, mul_zero, Finset.sum_const_zero,
        add_zero, mul_ite, mul_one] at h
      simpa using h
    · have h := congrArg (fun v => polar Q v (e d₀)) hsum
      simp only [polar_zero_left, polar_add_left, lag_polar_sum_left, polar_smul_left,
        Sum.elim_inl, Sum.elim_inr, hee, polar_comm Q (f _) (e d₀), hef, smul_eq_mul, mul_zero,
        Finset.sum_const_zero, zero_add, mul_ite, mul_one] at h
      simpa [eq_comm] using h
  have hcard : Fintype.card ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) = finrank F V := by
    simp only [Fintype.card_sum, Fintype.card_fin, hdim]
    ring
  set b := basisOfLinearIndependentOfCardEqFinrank' (Sum.elim e f) hli hcard with hbdef
  have hbl : ∀ a, b (Sum.inl a) = e a := fun a => by
    rw [hbdef, coe_basisOfLinearIndependentOfCardEqFinrank', Sum.elim_inl]
  have hbr : ∀ d, b (Sum.inr d) = f d := fun d => by
    rw [hbdef, coe_basisOfLinearIndependentOfCardEqFinrank', Sum.elim_inr]
  refine ⟨b, fun x => ?_, fun a a' => ?_, fun d d' => ?_, fun a d => ?_, fun a => ?_, fun d => ?_⟩
  · rcases x with a | d
    · rw [hbl]
      exact hQW _ (heW a)
    · rw [hbr]
      exact hQf d
  · rw [hbl, hbl]
    exact hee a a'
  · rw [hbr, hbr]
    exact hff d d'
  · rw [hbl, hbr]
    exact hef a d
  · rw [hbl]
    exact apply_of_mem_omegaInvSpace hss (heW a)
  · rw [hbr, hbl, he, Sum.swap_swap]
    have h1 : s (f d) = f d + omegaInvNil s (f d) := by
      rw [omegaInvNil_apply]
      abel
    rw [h1, hf, map_add, hNW _ (hwW d), add_zero]

end Coordinates

end CFSG.SeitzReduction.SymplecticPilot

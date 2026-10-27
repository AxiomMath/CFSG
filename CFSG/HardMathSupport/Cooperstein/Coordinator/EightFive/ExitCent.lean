module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolRestrict
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleFaith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.NineFix

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

section Perm

theorem isThreeCycle_conj {α : Type*} [Fintype α] [DecidableEq α] {π : Perm α}
    (h : π.IsThreeCycle) (g : Perm α) : (g * π * g⁻¹).IsThreeCycle := by
  unfold IsThreeCycle at h ⊢
  rw [cycleType_conj]
  exact h

theorem cycleType_viaEmbedding {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (σ : Perm α) (ι : α ↪ β) : (viaEmbedding σ ι).cycleType = σ.cycleType := by
  classical
  rw [viaEmbedding]
  convert cycleType_extendDomain (Equiv.ofInjective ι.1 ι.2) (g := σ)

variable {m n : ℕ}

theorem exists_alt_mapsTo (Δ Δ' : Finset (Fin n)) (hcard : Δ'.card = Δ.card)
    (h2 : Δ.card + 2 ≤ n) : ∃ g ∈ alternatingGroup (Fin n), ∀ i ∈ Δ, g i ∈ Δ' := by
  classical
  have hk : Δ.card ≤ Nat.card (Fin n) - 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have := alternatingGroup.isMultiplyPretransitive (Fin n)
  have : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin n)) (Fin n) Δ.card :=
    MulAction.isMultiplyPretransitive_of_le hk (Nat.sub_le _ _)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin n))
    (Δ.orderEmbOfFin rfl).toEmbedding (Δ'.orderEmbOfFin hcard).toEmbedding
  refine ⟨g, g.2, fun i hi => ?_⟩
  have hi' : i ∈ Set.range (Δ.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hi
  obtain ⟨j, rfl⟩ := hi'
  have h1 := congrArg (fun f : Fin Δ.card ↪ Fin n => f j) hg
  simp only [Function.Embedding.smul_apply] at h1
  have h2 : (g : Perm (Fin n)) ((Δ.orderEmbOfFin rfl) j) = (Δ'.orderEmbOfFin hcard) j := h1
  rw [h2]
  exact Finset.orderEmbOfFin_mem _ _ _

theorem exists_isThreeCycle_commute_commute_of_fix (Δ : Finset (Fin n)) (hn : Δ.card + 8 ≤ n)
    {σ τ : Perm (Fin n)} (hσ : σ.IsThreeCycle) (hτ : τ.IsThreeCycle) (hσΔ : ∀ i ∈ Δ, σ i = i) :
    ∃ ρ : Perm (Fin n), ρ.IsThreeCycle ∧ (∀ i ∈ Δ, ρ i = i) ∧ Commute ρ σ ∧ Commute ρ τ := by
  classical
  by_cases hd : _root_.Disjoint σ.support τ.support
  · exact ⟨σ, hσ, hσΔ, Commute.refl σ, (disjoint_iff_disjoint_support.2 hd).commute⟩
  · obtain ⟨i, hi⟩ := Finset.not_disjoint_iff_nonempty_inter.1 hd
    have hcard : (σ.support ∪ τ.support).card ≤ 5 := by
      have h1 := Finset.card_union_add_card_inter σ.support τ.support
      have h2 : 1 ≤ (σ.support ∩ τ.support).card := Finset.card_pos.2 ⟨i, hi⟩
      rw [hσ.card_support, hτ.card_support] at h1
      omega
    have hcompl : 2 < (σ.support ∪ τ.support ∪ Δ)ᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin]
      have := Finset.card_union_le (σ.support ∪ τ.support) Δ
      omega
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 hcompl
    simp only [Finset.mem_compl, Finset.mem_union, not_or] at ha hb hc
    have hsub : ∀ x, x ∈ (swap a b * swap a c).support → x = a ∨ x = b ∨ x = c := by
      intro x hx
      have hx' := support_mul_le (swap a b) (swap a c) hx
      rw [Finset.sup_eq_union, support_swap hab, support_swap hac] at hx'
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with (h | h) | (h | h) <;> simp [h]
    have hdσ : (swap a b * swap a c).Disjoint σ := by
      rw [disjoint_iff_disjoint_support]
      refine Finset.disjoint_left.2 fun x hx hxσ => ?_
      rcases hsub x hx with rfl | rfl | rfl
      · exact ha.1.1 hxσ
      · exact hb.1.1 hxσ
      · exact hc.1.1 hxσ
    have hdτ : (swap a b * swap a c).Disjoint τ := by
      rw [disjoint_iff_disjoint_support]
      refine Finset.disjoint_left.2 fun x hx hxτ => ?_
      rcases hsub x hx with rfl | rfl | rfl
      · exact ha.1.2 hxτ
      · exact hb.1.2 hxτ
      · exact hc.1.2 hxτ
    refine ⟨_, isThreeCycle_swap_mul_swap_same hab hac hbc, fun j hj => ?_, hdσ.commute,
      hdτ.commute⟩
    have hja : j ≠ a := fun h => ha.2 (h ▸ hj)
    have hjb : j ≠ b := fun h => hb.2 (h ▸ hj)
    have hjc : j ≠ c := fun h => hc.2 (h ▸ hj)
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hja hjc, swap_apply_of_ne_of_ne hja hjb]

end Perm

section Fix

variable {X : Type} [CommGroup X]

theorem mem_of_mul_inv_mem (hX : ∀ v : X, v ^ 2 = 1) {x : MulAut X} (hx3 : x ^ 3 = 1)
    {C : Subgroup X} (hC : fixV (Subgroup.zpowers x) = C) {v : X} (hv : x v * v⁻¹ ∈ C) :
    v ∈ C := by
  set c := x v * v⁻¹ with hc_def
  have hxc : x c = c := mem_fixV_zpowers_iff.1 (hC ▸ hv)
  have hxv : x v = c * v := by rw [hc_def, inv_mul_cancel_right]
  have hcc : c * c = 1 := by rw [← pow_two]; exact hX c
  have hx2 : x (x v) = v := by
    rw [hxv, map_mul, hxc, hxv, ← mul_assoc, hcc, one_mul]
  have hx3v : x (x (x v)) = v := by
    have h1 := congrArg (fun φ : MulAut X => φ v) hx3
    simpa [pow_succ, MulAut.mul_apply] using h1
  have hfix : x v = v := by
    calc x v = x (x (x v)) := by rw [hx2]
      _ = v := hx3v
  rw [← hC]
  exact mem_fixV_zpowers_iff.2 hfix

theorem fixV_zpowers_eq_of_exotic {G : Subgroup (MulAut X)} {m : ℕ} {φ : ↥G →* Perm (Fin m)}
    (hE1 : commV (altPre φ) ⊔ fixV (altPre φ) = ⊤)
    (hE2 : ∀ x : ↥G, (φ x).IsThreeCycle →
      fixV (Subgroup.zpowers (x : MulAut X)) ⊓ commV (altPre φ) = ⊥)
    {x : ↥G} (h3 : (φ x).IsThreeCycle) :
    fixV (Subgroup.zpowers (x : MulAut X)) = fixV (altPre φ) := by
  have hxL : (x : MulAut X) ∈ altPre φ := coe_mem_altPre_iff.2 h3.mem_alternatingGroup
  refine le_antisymm (fun v hv => ?_) (fixV_zpowers_le hxL)
  have hvt : v ∈ commV (altPre φ) ⊔ fixV (altPre φ) := hE1 ▸ Subgroup.mem_top v
  obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 hvt
  have hxc : (x : MulAut X) c = c := hc _ hxL
  have hxu : (x : MulAut X) u = u := by
    have h1 : (x : MulAut X) (u * c) = u * c := mem_fixV_zpowers_iff.1 hv
    rw [map_mul, hxc] at h1
    exact mul_right_cancel h1
  have hu1 : u = 1 := by
    have : u ∈ fixV (Subgroup.zpowers (x : MulAut X)) ⊓ commV (altPre φ) :=
      ⟨mem_fixV_zpowers_iff.2 hxu, hu⟩
    rw [hE2 x h3] at this
    exact this
  rw [hu1, one_mul]
  exact hc

end Fix

section Restrict

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {m n : ℕ} {ψ : ↥H →* Perm (Fin n)}
  {ι : Fin m ↪ Fin n} {K : Subgroup (MulAut V)} {hK : K ≤ preSub ψ (permSetStab (Set.range ι))}

theorem viaEmbedding_restrictHom (k : ↥K)
    (hfix : ∀ x, x ∉ Set.range ι → ψ (Subgroup.inclusion (hK.trans preSub_le) k) x = x) :
    viaEmbedding (restrictHom ψ ι K hK k) ι = ψ (Subgroup.inclusion (hK.trans preSub_le) k) := by
  ext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    rw [viaEmbedding_apply, restrictHom_apply_apply]
  · rw [viaEmbedding_apply_of_notMem _ _ _ hx, hfix x hx]

theorem isThreeCycle_restrictHom (k : ↥K)
    (h3 : (ψ (Subgroup.inclusion (hK.trans preSub_le) k)).IsThreeCycle)
    (hfix : ∀ x, x ∉ Set.range ι → ψ (Subgroup.inclusion (hK.trans preSub_le) k) x = x) :
    (restrictHom ψ ι K hK k).IsThreeCycle := by
  unfold IsThreeCycle at h3 ⊢
  rw [← cycleType_viaEmbedding _ ι, viaEmbedding_restrictHom k hfix]
  exact h3

end Restrict

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ} {ψ : ↥H →* Perm (Fin n)}

theorem fixV_zpowers_eq_of_fix (hA : alternatingGroup (Fin n) ≤ ψ.range) (Δ : Finset (Fin n))
    (hΔ : Δ.card + 6 ≤ n) {C₀ : Subgroup V}
    (hC : ∀ x : ↥H, (ψ x).IsThreeCycle → (∀ i ∈ Δ, ψ x i = i) →
      fixV (Subgroup.zpowers (x : MulAut V)) = C₀)
    {y : ↥H} (hy : (ψ y).IsThreeCycle) : fixV (Subgroup.zpowers (y : MulAut V)) = C₀ := by
  classical
  set T := (ψ y).support with hT
  have hTc : T.card = 3 := hy.card_support
  have hc1 : 2 < (Δ ∪ T)ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_union_le Δ T
    omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 hc1
  simp only [Finset.mem_compl, Finset.mem_union, not_or] at ha hb hc
  have hc2 : Δ.card ≤ (T ∪ {a, b, c})ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    have h1 := Finset.card_union_le T {a, b, c}
    have h2 : ({a, b, c} : Finset (Fin n)).card ≤ 3 := Finset.card_le_three
    omega
  obtain ⟨Δ', hΔ'sub, hΔ'card⟩ := Finset.exists_subset_card_eq hc2
  have hΔ' : ∀ i ∈ Δ', i ∉ T ∧ i ≠ a ∧ i ≠ b ∧ i ≠ c := fun i hi => by
    have h := Finset.mem_compl.1 (hΔ'sub hi)
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact h
  obtain ⟨g, hgA, hgΔ⟩ := exists_alt_mapsTo Δ Δ' hΔ'card (by omega)
  obtain ⟨gH, hgH⟩ := hA hgA
  have key : ∀ w : ↥H, (ψ w).IsThreeCycle → (∀ i ∈ Δ', ψ w i = i) →
      ∀ v : V, (w : MulAut V) v = v ↔ (gH : MulAut V)⁻¹ v ∈ C₀ := by
    intro w hw3 hwΔ v
    have hψ' : ψ (gH⁻¹ * w * gH) = g⁻¹ * ψ w * g := by rw [map_mul, map_mul, map_inv, hgH]
    have h3 : (ψ (gH⁻¹ * w * gH)).IsThreeCycle := by
      rw [hψ']
      simpa using isThreeCycle_conj hw3 g⁻¹
    have hfix : ∀ i ∈ Δ, ψ (gH⁻¹ * w * gH) i = i := fun i hi => by
      rw [hψ', Perm.mul_apply, Perm.mul_apply, hwΔ _ (hgΔ i hi), perm_inv_apply_apply]
    rw [← hC _ h3 hfix, mem_fixV_zpowers_iff]
    change _ ↔ (gH : MulAut V)⁻¹ ((w : MulAut V) ((gH : MulAut V) ((gH : MulAut V)⁻¹ v))) =
      (gH : MulAut V)⁻¹ v
    rw [MulAut.apply_inv_self]
    exact ⟨fun h => by rw [h], fun h => (gH : MulAut V)⁻¹.injective h⟩
  have hζ3 : (swap a b * swap a c).IsThreeCycle := isThreeCycle_swap_mul_swap_same hab hac hbc
  obtain ⟨z, hz⟩ := hA hζ3.mem_alternatingGroup
  have hz3 : (ψ z).IsThreeCycle := hz ▸ hζ3
  have hzfix : ∀ i, i ≠ a → i ≠ b → i ≠ c → ψ z i = i := fun i h1 h2 h3 => by
    rw [hz, Perm.mul_apply, swap_apply_of_ne_of_ne h1 h3, swap_apply_of_ne_of_ne h1 h2]
  have hz1 : fixV (Subgroup.zpowers (z : MulAut V)) = C₀ :=
    hC z hz3 fun i hi => hzfix i (fun h => ha.1 (h ▸ hi)) (fun h => hb.1 (h ▸ hi))
      (fun h => hc.1 (h ▸ hi))
  have hz2 := key z hz3 fun i hi => hzfix i (hΔ' i hi).2.1 (hΔ' i hi).2.2.1 (hΔ' i hi).2.2.2
  have hg0 : ∀ v, (gH : MulAut V)⁻¹ v ∈ C₀ ↔ v ∈ C₀ := fun v => by
    rw [← hz2 v, ← mem_fixV_zpowers_iff, hz1]
  have hyΔ' : ∀ i ∈ Δ', ψ y i = i := fun i hi => by
    by_contra h
    exact (hΔ' i hi).1 (Perm.mem_support.2 h)
  ext v
  rw [mem_fixV_zpowers_iff, key y hy hyΔ' v, hg0]

theorem fixV_altPre_eq_of_forall (h3n : 3 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) {C₀ : Subgroup V}
    (hC : ∀ y : ↥H, (ψ y).IsThreeCycle → fixV (Subgroup.zpowers (y : MulAut V)) = C₀) :
    fixV (altPre ψ) = C₀ := by
  have hab : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hac : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have hbc : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have hσ := isThreeCycle_swap_mul_swap_same hab hac hbc
  obtain ⟨y, hy⟩ := hA hσ.mem_alternatingGroup
  have hy3 : (ψ y).IsThreeCycle := hy ▸ hσ
  have hyL : (y : MulAut V) ∈ altPre ψ := coe_mem_altPre_iff.2 hy3.mem_alternatingGroup
  refine le_antisymm ((fixV_zpowers_le hyL).trans (hC y hy3).le) fun v hv => ?_
  have hle : altPre ψ ≤ MulAction.stabilizer (MulAut V) v :=
    le_of_isThreeCycle_mem (altPreEquiv hψ hA) fun x hx h3x => by
      rw [coe_altPreEquiv] at h3x
      have hv' : v ∈ fixV (Subgroup.zpowers
          ((Subgroup.inclusion altPre_le ⟨x, hx⟩ : ↥H) : MulAut V)) := (hC _ h3x).symm ▸ hv
      exact MulAction.mem_stabilizer_iff.2 (mem_fixV_zpowers_iff.1 hv')
  exact fun g hg => MulAction.mem_stabilizer_iff.1 (hle hg)

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

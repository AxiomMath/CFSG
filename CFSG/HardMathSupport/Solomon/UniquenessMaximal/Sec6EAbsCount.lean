module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E

namespace Datum
variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V] (D : Datum V)


theorem count_apply_inv (x : V ≃ₗ[ZMod 3] V) (v : V) : x (x⁻¹ v) = v := by
  simp

theorem count_inv_apply (x : V ≃ₗ[ZMod 3] V) (v : V) : x⁻¹ (x v) = v := by
  simp

theorem count_mem_conjSub {x : V ≃ₗ[ZMod 3] V} {H : Subgroup (V ≃ₗ[ZMod 3] V)}
    {y : V ≃ₗ[ZMod 3] V} : y ∈ conjSub x H ↔ ∃ q ∈ H, y = x⁻¹ * q * x := by
  unfold conjSub
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor <;> rintro ⟨q, hq, h⟩ <;> exact ⟨q, hq, h.symm⟩

theorem count_exists_ne_zero (S : Submodule (ZMod 3) V) (h : Nat.card S = 9) :
    ∃ s ∈ S, s ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have : Nat.card S ≤ 1 := by
    rw [Finite.card_le_one_iff_subsingleton]
    refine ⟨fun a b => Subtype.ext ?_⟩
    rw [hcon a a.2, hcon b b.2]
  omega

theorem count_img_eq_of_le (g : V ≃ₗ[ZMod 3] V) (S T : Submodule (ZMod 3) V)
    (hle : ∀ s ∈ S, g s ∈ T) (hc : Nat.card S = Nat.card T) : img g S = T := by
  have h1 : (img g S : Set V) ⊆ T := by
    intro v hv
    obtain ⟨s, hs, rfl⟩ := mem_img.1 hv
    exact hle s hs
  have hcard : Nat.card (img g S) = Nat.card S :=
    (Nat.card_congr (g.submoduleMap S).toEquiv).symm
  have h2 : (T : Set V).ncard ≤ (img g S : Set V).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact le_of_eq (hc.symm.trans hcard.symm)
  exact SetLike.coe_injective (Set.eq_of_subset_of_ncard_le h1 h2 (Set.toFinite _))

theorem count_split_of_maps (w : V ≃ₗ[ZMod 3] V) (S A' F' : Submodule (ZMod 3) V)
    (h : ∀ s ∈ S, w s ∈ A' ∨ w s ∈ F') : (∀ s ∈ S, w s ∈ A') ∨ (∀ s ∈ S, w s ∈ F') := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨a1, ha1, ha1'⟩, ⟨a2, ha2, ha2'⟩⟩ := hcon
  have h1 : w a1 ∈ F' := (h a1 ha1).resolve_left ha1'
  have h2 : w a2 ∈ A' := (h a2 ha2).resolve_right ha2'
  rcases h (a1 + a2) (S.add_mem ha1 ha2) with h3 | h3
  · apply ha1'
    have : w a1 = w (a1 + a2) - w a2 := by rw [map_add]; abel
    rw [this]; exact A'.sub_mem h3 h2
  · apply ha2'
    have : w a2 = w (a1 + a2) - w a1 := by rw [map_add]; abel
    rw [this]; exact F'.sub_mem h3 h1

theorem count_permutes_of_maps (w : V ≃ₗ[ZMod 3] V)
    (h : ∀ v, (v ∈ D.A ∨ v ∈ D.F) → (w v ∈ D.A ∨ w v ∈ D.F)) : D.PermutesAF w := by
  have hA := count_split_of_maps w D.A D.A D.F (fun s hs => h s (Or.inl hs))
  have hF := count_split_of_maps w D.F D.A D.F (fun s hs => h s (Or.inr hs))
  obtain ⟨a0, ha0, ha00⟩ := count_exists_ne_zero D.A D.card_A
  obtain ⟨f0, hf0, hf00⟩ := count_exists_ne_zero D.F D.card_F
  rcases hA with hA | hA <;> rcases hF with hF | hF
  · exfalso
    have hAA := count_img_eq_of_le w D.A D.A hA rfl
    have : w f0 ∈ img w D.A := by rw [hAA]; exact hF f0 hf0
    obtain ⟨a, ha, haf⟩ := mem_img.1 this
    have := w.injective haf
    subst this
    exact hf00 (D.inter_eq_zero ha hf0)
  · left
    exact ⟨count_img_eq_of_le w D.A D.A hA rfl, count_img_eq_of_le w D.F D.F hF rfl⟩
  · right
    exact ⟨count_img_eq_of_le w D.A D.F hA (by rw [D.card_A, D.card_F]),
      count_img_eq_of_le w D.F D.A hF (by rw [D.card_A, D.card_F])⟩
  · exfalso
    have hFF := count_img_eq_of_le w D.F D.F hF rfl
    have : w a0 ∈ img w D.F := by rw [hFF]; exact hA a0 ha0
    obtain ⟨f, hf, hfa⟩ := mem_img.1 this
    have := w.injective hfa
    subst this
    exact ha00 (D.inter_eq_zero ha0 hf)

theorem count_exists_bad (w : V ≃ₗ[ZMod 3] V) (h : ¬ D.PermutesAF w) :
    ∃ v, v ≠ 0 ∧ (v ∈ D.A ∨ v ∈ D.F) ∧ ∃ a ∈ D.A, ∃ f ∈ D.F, a ≠ 0 ∧ f ≠ 0 ∧ w v = a + f := by
  by_contra hcon
  push Not at hcon
  apply h
  apply count_permutes_of_maps
  intro v hv
  by_cases hv0 : v = 0
  · subst hv0; simp
  obtain ⟨a, ha, f, hf, hwv⟩ := D.exists_decomp (w v)
  by_cases ha0 : a = 0
  · right; rw [hwv, ha0, zero_add]; exact hf
  by_cases hf0 : f = 0
  · left; rw [hwv, hf0, add_zero]; exact ha
  exact absurd hwv (hcon v hv0 hv a ha f hf ha0 hf0)

section WithX
variable (x : V ≃ₗ[ZMod 3] V) (hAF : img x⁻¹ D.A = D.F ∧ img x⁻¹ D.F = D.A)
include hAF

theorem count_x_A {a : V} (ha : a ∈ D.A) : x a ∈ D.F := by
  have : a ∈ img x⁻¹ D.F := by rw [hAF.2]; exact ha
  obtain ⟨f, hf, rfl⟩ := mem_img.1 this
  rw [count_apply_inv]; exact hf

theorem count_x_F {f : V} (hf : f ∈ D.F) : x f ∈ D.A := by
  have : f ∈ img x⁻¹ D.A := by rw [hAF.1]; exact hf
  obtain ⟨a, ha, rfl⟩ := mem_img.1 this
  rw [count_apply_inv]; exact ha

theorem count_xinv_A {a : V} (ha : a ∈ D.A) : x⁻¹ a ∈ D.F := by
  rw [← hAF.1]; exact mem_img.2 ⟨a, ha, rfl⟩

theorem count_xinv_F {f : V} (hf : f ∈ D.F) : x⁻¹ f ∈ D.A := by
  rw [← hAF.2]; exact mem_img.2 ⟨f, hf, rfl⟩

theorem count_x_perm : D.PermutesAF x :=
  Or.inr ⟨count_img_eq_of_le x D.A D.F (fun _ ha => D.count_x_A x hAF ha)
      (by rw [D.card_A, D.card_F]),
    count_img_eq_of_le x D.F D.A (fun _ hf => D.count_x_F x hAF hf)
      (by rw [D.card_A, D.card_F])⟩

theorem count_conj_F {y : V ≃ₗ[ZMod 3] V} (hy : y ∈ conjSub x D.Q) : ∀ f ∈ D.F, y f = f := by
  obtain ⟨q, hq, rfl⟩ := count_mem_conjSub.1 hy
  intro f hf
  show x⁻¹ (q (x f)) = f
  rw [D.Q_fix_A q hq _ (D.count_x_F x hAF hf), count_inv_apply]

theorem count_conj_A {y : V ≃ₗ[ZMod 3] V} (hy : y ∈ conjSub x D.Q) : ∀ a ∈ D.A, y a ∈ D.A := by
  obtain ⟨q, hq, rfl⟩ := count_mem_conjSub.1 hy
  intro a ha
  exact D.count_xinv_F x hAF (D.planeQ.mem q hq _ (D.count_x_A x hAF ha))

theorem count_conj_trans {a a' : V} (ha : a ∈ D.A) (ha' : a' ∈ D.A) (ha0 : a ≠ 0) (ha0' : a' ≠ 0) :
    ∃ y ∈ conjSub x D.Q, y a = a' := by
  obtain ⟨q, hq, hqa⟩ := D.planeQ.trans (x a) (D.count_x_A x hAF ha) (x a')
    (D.count_x_A x hAF ha') (fun h => ha0 (x.map_eq_zero_iff.1 h)) (fun h => ha0' (x.map_eq_zero_iff.1 h))
  refine ⟨x⁻¹ * q * x, count_mem_conjSub.2 ⟨q, hq, rfl⟩, ?_⟩
  show x⁻¹ (q (x a)) = a'
  rw [hqa, count_inv_apply]

theorem count_H_trans {a a' f f' : V} (ha : a ∈ D.A) (ha' : a' ∈ D.A) (hf : f ∈ D.F)
    (hf' : f' ∈ D.F) (ha0 : a ≠ 0) (ha0' : a' ≠ 0) (hf0 : f ≠ 0) (hf0' : f' ≠ 0) :
    ∃ h ∈ D.Q ⊔ conjSub x D.Q, h (a + f) = a' + f' := by
  obtain ⟨q, hq, hqf⟩ := D.planeQ.trans f hf f' hf' hf0 hf0'
  obtain ⟨y, hy, hya⟩ := D.count_conj_trans x hAF ha ha' ha0 ha0'
  refine ⟨q * y, Subgroup.mul_mem_sup hq hy, ?_⟩
  show q (y (a + f)) = _
  rw [map_add, hya, D.count_conj_F x hAF hy f hf, map_add, D.Q_fix_A q hq a' ha', hqf]

theorem count_conj_le_W (hxW : x ∈ D.W) : conjSub x D.Q ≤ D.W := by
  intro y hy
  obtain ⟨q, hq, rfl⟩ := count_mem_conjSub.1 hy
  exact D.W.mul_mem (D.W.mul_mem (D.W.inv_mem hxW) (D.Q_le_W hq)) hxW

theorem count_H_le_N (hxW : x ∈ D.W) :
    D.Q ⊔ conjSub x D.Q ≤ D.NW (D.Q ⊔ conjSub x D.Q) := by
  intro h hh
  exact Subgroup.mem_inf.2 ⟨sup_le D.Q_le_W (D.count_conj_le_W x hAF hxW) hh,
    Subgroup.le_normalizer hh⟩

theorem count_N_trans (hxW : x ∈ D.W)
    (hperm' : ∀ g ∈ D.W, D.PermutesAF g → g ∈ D.NW (D.Q ⊔ conjSub x D.Q))
    {u v : V} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu : u ∈ D.A ∨ u ∈ D.F) (hv : v ∈ D.A ∨ v ∈ D.F) :
    ∃ n ∈ D.NW (D.Q ⊔ conjSub x D.Q), n u = v := by
  have hxN : x ∈ D.NW (D.Q ⊔ conjSub x D.Q) := hperm' x hxW (D.count_x_perm x hAF)
  have hHN := D.count_H_le_N x hAF hxW
  have hxne : ∀ w, w ≠ 0 → x w ≠ 0 := fun w hw h => hw (x.map_eq_zero_iff.1 h)
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · obtain ⟨y, hy, hyu⟩ := D.count_conj_trans x hAF hu hv hu0 hv0
    exact ⟨y, hHN (Subgroup.mem_sup_right hy), hyu⟩
  · obtain ⟨q, hq, hqu⟩ := D.planeQ.trans (x u) (D.count_x_A x hAF hu) v hv (hxne u hu0) hv0
    exact ⟨q * x, Subgroup.mul_mem _ (hHN (Subgroup.mem_sup_left hq)) hxN, hqu⟩
  · obtain ⟨y, hy, hyu⟩ := D.count_conj_trans x hAF (D.count_x_F x hAF hu) hv (hxne u hu0) hv0
    exact ⟨y * x, Subgroup.mul_mem _ (hHN (Subgroup.mem_sup_right hy)) hxN, hyu⟩
  · obtain ⟨q, hq, hqu⟩ := D.planeQ.trans u hu v hv hu0 hv0
    exact ⟨q, hHN (Subgroup.mem_sup_left hq), hqu⟩

theorem count_W_trans (hxW : x ∈ D.W)
    (hperm' : ∀ g ∈ D.W, D.PermutesAF g → g ∈ D.NW (D.Q ⊔ conjSub x D.Q))
    (hnot : ¬ D.W ≤ Subgroup.normalizer ((D.Q ⊔ conjSub x D.Q : Subgroup (V ≃ₗ[ZMod 3] V)) : Set _)) :
    ∀ u v : V, u ≠ 0 → v ≠ 0 → ∃ w ∈ D.W, w u = v := by
  obtain ⟨w, hwW, hw⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
  have hwP : ¬ D.PermutesAF w := fun hP => hw (Subgroup.mem_inf.1 (hperm' w hwW hP)).2
  obtain ⟨v0, hv00, hv0, a0, ha0, f0, hf0, ha00, hf00, hwv0⟩ := D.count_exists_bad w hwP
  have key : ∀ u, u ≠ 0 → ∃ g ∈ D.W, g u = w v0 := by
    intro u hu0
    obtain ⟨a, ha, f, hf, rfl⟩ := D.exists_decomp u
    by_cases ha0' : a = 0
    · subst ha0'
      rw [zero_add] at hu0 ⊢
      obtain ⟨n, hn, hnu⟩ := D.count_N_trans x hAF hxW hperm' hu0 hv00 (Or.inr hf) hv0
      exact ⟨w * n, D.W.mul_mem hwW (Subgroup.mem_inf.1 hn).1, by
        show w (n _) = _
        rw [hnu]⟩
    by_cases hf0' : f = 0
    · subst hf0'
      rw [add_zero] at hu0 ⊢
      obtain ⟨n, hn, hnu⟩ := D.count_N_trans x hAF hxW hperm' hu0 hv00 (Or.inl ha) hv0
      exact ⟨w * n, D.W.mul_mem hwW (Subgroup.mem_inf.1 hn).1, by
        show w (n _) = _
        rw [hnu]⟩
    · obtain ⟨h, hh, hhu⟩ := D.count_H_trans x hAF ha ha0 hf hf0 ha0' ha00 hf0' hf00
      refine ⟨h, sup_le D.Q_le_W (D.count_conj_le_W x hAF hxW) hh, ?_⟩
      rw [hhu, hwv0]
  intro u v hu hv
  obtain ⟨g1, hg1, h1⟩ := key u hu
  obtain ⟨g2, hg2, h2⟩ := key v hv
  refine ⟨g2⁻¹ * g1, D.W.mul_mem (D.W.inv_mem hg2) hg1, ?_⟩
  show g2⁻¹ (g1 u) = v
  rw [h1, ← h2, count_inv_apply]

end WithX

theorem count_relIndex_stab (K : Subgroup (V ≃ₗ[ZMod 3] V)) (a : V) :
    (MulAction.stabilizer (V ≃ₗ[ZMod 3] V) a ⊓ K).relIndex K =
      (MulAction.orbit K a).ncard := by
  rw [Subgroup.inf_relIndex_right, ← MulAction.index_stabilizer]
  unfold Subgroup.relIndex
  congr 1

theorem count_orbit_W (htrans : ∀ u v : V, u ≠ 0 → v ≠ 0 → ∃ w ∈ D.W, w u = v) {a : V}
    (ha : a ≠ 0) : (MulAction.orbit D.W a).ncard = 80 := by
  have h : MulAction.orbit D.W a = {v : V | v ≠ 0} := by
    ext v
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, rfl⟩ h
      exact ha ((g : V ≃ₗ[ZMod 3] V).map_eq_zero_iff.1 h)
    · intro hv
      obtain ⟨w, hw, hwa⟩ := htrans a v ha hv
      exact ⟨⟨w, hw⟩, hwa⟩
  rw [h]
  have h1 := Set.ncard_add_ncard_compl ({0} : Set V)
  rw [Set.ncard_singleton] at h1
  have h2 : ({0} : Set V)ᶜ = {v : V | v ≠ 0} := rfl
  rw [h2] at h1
  have := D.card_V
  omega

theorem count_card_S1 : ({v : V | v ≠ 0 ∧ (v ∈ D.A ∨ v ∈ D.F)} : Set V).ncard = 16 := by
  have hA : (D.A : Set V).ncard = 9 := by rw [← Nat.card_coe_set_eq]; exact D.card_A
  have hF : (D.F : Set V).ncard = 9 := by rw [← Nat.card_coe_set_eq]; exact D.card_F
  have hint : (D.A : Set V) ∩ D.F = {0} := by
    ext v
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_singleton_iff]
    exact ⟨fun h => D.inter_eq_zero h.1 h.2, fun h => by subst h; exact ⟨D.A.zero_mem, D.F.zero_mem⟩⟩
  have hu := Set.ncard_union_add_ncard_inter (D.A : Set V) D.F
  rw [hint, Set.ncard_singleton, hA, hF] at hu
  have hS : {v : V | v ≠ 0 ∧ (v ∈ D.A ∨ v ∈ D.F)} = ((D.A : Set V) ∪ D.F) \ {0} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe,
      Set.mem_singleton_iff]
    tauto
  rw [hS, Set.ncard_sdiff_singleton_of_mem (by simp : (0 : V) ∈ (D.A : Set V) ∪ D.F)]
  omega

theorem count_C_le_N (x : V ≃ₗ[ZMod 3] V)
    (hN1 : ∀ a ∈ D.A, a ≠ 0 → ∀ w ∈ D.W, (w a = a ∨ w a = -a) → ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q)
    (hperm' : ∀ g ∈ D.W, D.PermutesAF g → g ∈ D.NW (D.Q ⊔ conjSub x D.Q))
    {a : V} (ha : a ∈ D.A) (ha0 : a ≠ 0) {g : V ≃ₗ[ZMod 3] V} (hgW : g ∈ D.W) (hga : g a = a) :
    g ∈ D.NW (D.Q ⊔ conjSub x D.Q) := by
  have hmem : g * D.t * g⁻¹ ∈ D.Q := hN1 a ha ha0 g hgW (Or.inl hga) D.t D.t_mem
  have hsq : (g * D.t * g⁻¹) * (g * D.t * g⁻¹) = 1 := by
    have : (g * D.t * g⁻¹) * (g * D.t * g⁻¹) = g * (D.t * D.t) * g⁻¹ := by group
    rw [this, D.t_mul_self]; group
  have hcomm : g * D.t = D.t * g := by
    rcases D.t_unique _ hmem hsq with h | h
    · exfalso; apply D.t_ne_one
      have : D.t = g⁻¹ * (g * D.t * g⁻¹) * g := by group
      rw [this, h]; group
    · exact mul_inv_eq_iff_eq_mul.1 h
  obtain ⟨hA, hF⟩ := D.t_comm_preserves hcomm
  exact hperm' g hgW (Or.inl ⟨count_img_eq_of_le g D.A D.A hA rfl,
    count_img_eq_of_le g D.F D.F hF rfl⟩)

theorem count_dichotomy (x : V ≃ₗ[ZMod 3] V) (hxW : x ∈ D.W)
    (hAF : img x⁻¹ D.A = D.F ∧ img x⁻¹ D.F = D.A)
    (hN1 : ∀ a ∈ D.A, a ≠ 0 → ∀ w ∈ D.W, (w a = a ∨ w a = -a) → ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q)
    (hperm : ∀ g ∈ D.NW (D.Q ⊔ conjSub x D.Q), D.PermutesAF g)
    (hperm' : ∀ g ∈ D.W, D.PermutesAF g → g ∈ D.NW (D.Q ⊔ conjSub x D.Q)) :
    D.W ≤ Subgroup.normalizer ((D.Q ⊔ conjSub x D.Q : Subgroup (V ≃ₗ[ZMod 3] V)) : Set _) ∨
      ((D.NW (D.Q ⊔ conjSub x D.Q)).relIndex D.W = 5 ∧
        ∀ u v : V, u ≠ 0 → v ≠ 0 → ∃ w ∈ D.W, w u = v) := by
  by_cases hW : D.W ≤ Subgroup.normalizer
      ((D.Q ⊔ conjSub x D.Q : Subgroup (V ≃ₗ[ZMod 3] V)) : Set _)
  · exact Or.inl hW
  right
  have htrans := D.count_W_trans x hAF hxW hperm' hW
  refine ⟨?_, htrans⟩
  obtain ⟨a, ha, ha0⟩ := count_exists_ne_zero D.A D.card_A
  have hNW : D.NW (D.Q ⊔ conjSub x D.Q) ≤ D.W := inf_le_left
  have hCW : MulAction.stabilizer (V ≃ₗ[ZMod 3] V) a ⊓ D.W =
      MulAction.stabilizer (V ≃ₗ[ZMod 3] V) a ⊓ D.NW (D.Q ⊔ conjSub x D.Q) := by
    refine le_antisymm (fun g hg => ?_) (inf_le_inf_left _ hNW)
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
    exact Subgroup.mem_inf.2 ⟨hg1, D.count_C_le_N x hN1 hperm' ha ha0 hg2
      (MulAction.mem_stabilizer_iff.1 hg1)⟩
  have h2 : (MulAction.stabilizer (V ≃ₗ[ZMod 3] V) a ⊓ D.NW (D.Q ⊔ conjSub x D.Q)).relIndex
      D.W = 80 := by
    rw [← hCW, count_relIndex_stab]
    exact D.count_orbit_W htrans ha0
  have h1 : (MulAction.stabilizer (V ≃ₗ[ZMod 3] V) a ⊓ D.NW (D.Q ⊔ conjSub x D.Q)).relIndex
      (D.NW (D.Q ⊔ conjSub x D.Q)) = 16 := by
    rw [count_relIndex_stab]
    have h : MulAction.orbit (D.NW (D.Q ⊔ conjSub x D.Q)) a =
        {v : V | v ≠ 0 ∧ (v ∈ D.A ∨ v ∈ D.F)} := by
      ext v
      rw [MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨g, rfl⟩
        refine ⟨fun h => ha0 ((g : V ≃ₗ[ZMod 3] V).map_eq_zero_iff.1 h), ?_⟩
        rcases hperm g g.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left
          rw [← h1]; exact mem_img.2 ⟨a, ha, rfl⟩
        · right
          rw [← h1]; exact mem_img.2 ⟨a, ha, rfl⟩
      · rintro ⟨hv0, hv⟩
        obtain ⟨n, hn, hnv⟩ := D.count_N_trans x hAF hxW hperm' ha0 hv0 (Or.inl ha) hv
        exact ⟨⟨n, hn⟩, hnv⟩
    rw [h]
    exact D.count_card_S1
  have h3 := Subgroup.relIndex_mul_relIndex
    (MulAction.stabilizer (V ≃ₗ[ZMod 3] V) a ⊓ D.NW (D.Q ⊔ conjSub x D.Q))
    (D.NW (D.Q ⊔ conjSub x D.Q)) D.W inf_le_right hNW
  rw [h1, h2] at h3
  omega

end Datum
end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E

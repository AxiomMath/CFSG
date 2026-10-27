module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NK

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

structure Sec5Hyp (T₁ : Subgroup X) : Prop where
  isPGroup : IsPGroup 2 T₁
  le : S.data.T ≤ T₁
  le_normalizer : T₁ ≤ normalizer (S.data.T : Set X)
  maximal : ∀ Q : Subgroup X, IsPGroup 2 Q → T₁ ≤ Q → Q ≤ normalizer (S.data.T : Set X) →
    Q = T₁
  card : Nat.card T₁ = 4 * Nat.card S.data.T
  fus : S.Fus
  swap : ∃ g ∈ T₁, (S.E (S.x * S.y)).map (MulAut.conj g).toMonoidHom = S.E S.y

@[expose] noncomputable def T₂of (T₁ : Subgroup X) : Subgroup X :=
  T₁ ⊓ normalizer (S.E (S.x * S.y) : Set X)

variable {S}

theorem Sec5Hyp.of_sec4 {F : S.Frame} {T₁ : Subgroup X} (h4 : S.Sec4 F T₁) (hF : F.Normal)
    (hg : ∃ g ∈ T₁, F.E₁.map (MulAut.conj g).toMonoidHom = F.E₂) : S.Sec5Hyp T₁ := by
  obtain ⟨hx, hy, hk⟩ := hF
  have h1 : F.E₁ = S.E (S.x * S.y) := by rw [Frame.E₁, hy]
  have h2 : F.E₂ = S.E S.y := by rw [Frame.E₂, hx, hy, inv_mul_cancel_left]
  refine ⟨h4.isPGroup, h4.le, h4.le_normalizer, h4.maximal, h4.card, fun b hb => ?_, ?_⟩
  · rw [h4.fusion b hb, hk]
  · rwa [h1, h2] at hg

theorem E_y_ne_E_xy : S.E S.y ≠ S.E (S.x * S.y) := fun h =>
  S.not_conj_E_y_E_xy (one_mem _) fun e he => by rw [← h]; simpa using he

omit [Finite X] in
theorem map_conj_inv {P Q : Subgroup X} {g : X} (h : P.map (MulAut.conj g).toMonoidHom = Q) :
    Q.map (MulAut.conj g⁻¹).toMonoidHom = P := by
  rw [← h, Subgroup.map_map]
  have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id X := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [this, Subgroup.map_id]

omit [Finite X] in
theorem map_conj_mul (P : Subgroup X) (g h : X) :
    P.map (MulAut.conj (g * h)).toMonoidHom =
      (P.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

namespace Sec5Hyp

variable {T₁ : Subgroup X} (H : S.Sec5Hyp T₁)
include H

theorem inf_centralizer : T₁ ⊓ centralizer ({S.t} : Set X) = S.data.T :=
  S.eq_T_of_le' (H.isPGroup.to_le inf_le_left) (le_inf H.le S.data.T_le_centralizer)
    inf_le_right

theorem map_E (I : S.Inst) {g : X} (hg : g ∈ T₁) :
    I.E.map (MulAut.conj g).toMonoidHom = S.E S.y ∨
      I.E.map (MulAut.conj g).toMonoidHom = S.E (S.x * S.y) := by
  have hgN := H.le_normalizer hg
  have hel : ElemAbelianTwo I.E := ⟨fun a ha b hb => I.comm ha hb, fun a ha => I.sq_eq_one ha⟩
  have hmap : I.E.map (MulAut.conj g).toMonoidHom ≤ S.data.T := by
    rintro _ ⟨e, he, rfl⟩
    exact (mem_normalizer_iff.mp hgN e).mp (I.E_le_T he)
  have hel' : ElemAbelianTwo (I.E.map (MulAut.conj g).toMonoidHom) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hel.comm a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, hel.sq_eq_one a ha, map_one]
  have hc16 : Nat.card (I.E.map (MulAut.conj g).toMonoidHom) = 16 := by
    rw [card_map_of_injective (MulAut.conj g).injective, Inst.E,
      S.card_E I.yi_mem I.yi_sq I.yi_not_mem_B]
  exact S.eq_E_of_elem hmap hel' hc16

omit H in
theorem mem_normalizer_of_map_eq {P : Subgroup X} {g : X}
    (h : P.map (MulAut.conj g).toMonoidHom = P) : g ∈ normalizer (P : Set X) :=
  mem_normalizer_of_conj_mem fun e he => by
    have : g * e * g⁻¹ ∈ P.map (MulAut.conj g).toMonoidHom := ⟨e, he, rfl⟩
    rwa [h] at this

omit H in
theorem map_eq_of_mem_normalizer {P : Subgroup X} {g : X} (h : g ∈ normalizer (P : Set X)) :
    P.map (MulAut.conj g).toMonoidHom = P := by
  have hle : P.map (MulAut.conj g).toMonoidHom ≤ P := by
    rintro _ ⟨p, hp, rfl⟩
    exact (mem_normalizer_iff.mp h p).mp hp
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective])

theorem swap_of_not_mem {g : X} (hg : g ∈ T₁)
    (hgN : g ∉ normalizer (S.E (S.x * S.y) : Set X)) :
    (S.E (S.x * S.y)).map (MulAut.conj g).toMonoidHom = S.E S.y ∧
      (S.E S.y).map (MulAut.conj g).toMonoidHom = S.E (S.x * S.y) := by
  have h1 : (S.E (S.x * S.y)).map (MulAut.conj g).toMonoidHom = S.E S.y := by
    rcases H.map_E S.inst₁ hg with h | h
    · exact h
    · exact absurd (mem_normalizer_of_map_eq h) hgN
  refine ⟨h1, ?_⟩
  rcases H.map_E S.inst₂ hg with h | h
  · exfalso
    have heq : S.E (S.x * S.y) = S.E S.y :=
      Subgroup.map_injective (MulAut.conj g).injective (h1.trans h.symm)
    exact E_y_ne_E_xy heq.symm
  · exact h

theorem mem_normalizer_E₂ {g : X} (hg : g ∈ T₁)
    (hgN : g ∈ normalizer (S.E (S.x * S.y) : Set X)) : g ∈ normalizer (S.E S.y : Set X) := by
  rcases H.map_E S.inst₂ hg with h | h
  · exact mem_normalizer_of_map_eq h
  · exfalso
    have h1 : (S.E (S.x * S.y)).map (MulAut.conj g).toMonoidHom = S.E (S.x * S.y) :=
      map_eq_of_mem_normalizer hgN
    have heq : S.E S.y = S.E (S.x * S.y) :=
      Subgroup.map_injective (MulAut.conj g).injective (h.trans h1.symm)
    exact E_y_ne_E_xy heq

theorem exists_g₀ : ∃ g ∈ T₁, g ∉ S.T₂of T₁ ∧
    (S.E (S.x * S.y)).map (MulAut.conj g).toMonoidHom = S.E S.y := by
  obtain ⟨g, hg, hgE⟩ := H.swap
  refine ⟨g, hg, fun h => ?_, hgE⟩
  have h1 := map_eq_of_mem_normalizer (mem_inf.mp h).2
  rw [h1] at hgE
  exact E_y_ne_E_xy hgE.symm

omit H in
theorem T₂of_le : S.T₂of T₁ ≤ T₁ := inf_le_left

theorem T_le_T₂of : S.data.T ≤ S.T₂of T₁ :=
  le_inf H.le (S.T_le_normalizer_E S.xy_mem)

theorem T₂of_le_normalizer_E₂ : S.T₂of T₁ ≤ normalizer (S.E S.y : Set X) := fun _ hg =>
  H.mem_normalizer_E₂ (mem_inf.mp hg).1 (mem_inf.mp hg).2

theorem mem_or_of_mem {g₀ : X} (hg₀ : g₀ ∈ T₁) (hg₀T : g₀ ∉ S.T₂of T₁) {h : X} (hh : h ∈ T₁) :
    h ∈ S.T₂of T₁ ∨ g₀⁻¹ * h ∈ S.T₂of T₁ := by
  by_cases hN : h ∈ normalizer (S.E (S.x * S.y) : Set X)
  · exact Or.inl (mem_inf.mpr ⟨hh, hN⟩)
  · right
    have hg₀N : g₀ ∉ normalizer (S.E (S.x * S.y) : Set X) := fun h' =>
      hg₀T (mem_inf.mpr ⟨hg₀, h'⟩)
    obtain ⟨h1, -⟩ := H.swap_of_not_mem hh hN
    obtain ⟨g1, -⟩ := H.swap_of_not_mem hg₀ hg₀N
    refine mem_inf.mpr ⟨mul_mem (inv_mem hg₀) hh, mem_normalizer_of_map_eq ?_⟩
    rw [map_conj_mul, h1, map_conj_inv g1]

theorem conj_mem_T₂of {g h : X} (hg : g ∈ T₁) (hh : h ∈ S.T₂of T₁) :
    g * h * g⁻¹ ∈ S.T₂of T₁ := by
  obtain ⟨hhT, hhN⟩ := mem_inf.mp hh
  refine mem_inf.mpr ⟨mul_mem (mul_mem hg hhT) (inv_mem hg), ?_⟩
  by_cases hgN : g ∈ normalizer (S.E (S.x * S.y) : Set X)
  · exact mul_mem (mul_mem hgN hhN) (inv_mem hgN)
  · obtain ⟨h1, h2⟩ := H.swap_of_not_mem hg hgN
    have hhN₂ := H.mem_normalizer_E₂ hhT hhN
    refine mem_normalizer_of_map_eq ?_
    rw [map_conj_mul, map_conj_mul, map_conj_inv h2, map_eq_of_mem_normalizer hhN₂, h2]

theorem card_T₁_eq : Nat.card T₁ = 2 * Nat.card (S.T₂of T₁) := by
  obtain ⟨g₀, hg₀, hg₀T, -⟩ := H.exists_g₀
  have hN : g₀ ∈ normalizer (S.T₂of T₁ : Set X) :=
    mem_normalizer_of_conj_mem fun h hh => H.conj_mem_T₂of hg₀ hh
  have hsq : g₀ ^ 2 ∈ S.T₂of T₁ := by
    rcases H.mem_or_of_mem hg₀ hg₀T (pow_mem hg₀ 2) with h | h
    · exact h
    · exfalso
      apply hg₀T
      rwa [pow_two, inv_mul_cancel_left] at h
  have heq : S.T₂of T₁ ⊔ zpowers g₀ = T₁ := by
    apply le_antisymm (sup_le T₂of_le (zpowers_le.mpr hg₀))
    intro h hh
    rw [mem_sup_zpowers_iff hN hsq]
    exact H.mem_or_of_mem hg₀ hg₀T hh
  have h2 := card_sup_zpowers hN hsq hg₀T
  rwa [heq] at h2

theorem card_T₂of : Nat.card (S.T₂of T₁) = 64 := by
  have h1 := H.card_T₁_eq
  rw [H.card, S.card_T] at h1
  omega

theorem relIndex_T : (S.data.T.subgroupOf (S.T₂of T₁)).index = 2 := by
  have h := Subgroup.card_mul_index (S.data.T.subgroupOf (S.T₂of T₁))
  rw [Nat.card_congr (subgroupOfEquivOfLe H.T_le_T₂of).toEquiv, S.card_T, H.card_T₂of] at h
  omega

theorem sq_mem_T {g : X} (hg : g ∈ S.T₂of T₁) : g ^ 2 ∈ S.data.T := by
  have := Subgroup.sq_mem_of_index_two H.relIndex_T ⟨g, hg⟩
  rw [mem_subgroupOf] at this
  simpa using this

theorem exists_w₀ : ∃ w₀ ∈ S.T₂of T₁, w₀ ∉ S.data.T := by
  by_contra h
  push Not at h
  have hle : S.T₂of T₁ ≤ S.data.T := fun g hg => h g hg
  have := Subgroup.card_le_of_le hle
  rw [H.card_T₂of, S.card_T] at this
  omega

theorem mem_T₂of_iff {w₀ : X} (hw₀ : w₀ ∈ S.T₂of T₁) (hw₀T : w₀ ∉ S.data.T) {g : X} :
    g ∈ S.T₂of T₁ ↔ g ∈ S.data.T ∨ w₀⁻¹ * g ∈ S.data.T := by
  have hN : w₀ ∈ normalizer (S.data.T : Set X) := H.le_normalizer (T₂of_le hw₀)
  have hsq := H.sq_mem_T hw₀
  have heq : S.data.T ⊔ zpowers w₀ = S.T₂of T₁ := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le H.T_le_T₂of (zpowers_le.mpr hw₀)) ?_
    rw [card_sup_zpowers hN hsq hw₀T, H.card_T₂of, S.card_T]
  rw [← heq, mem_sup_zpowers_iff hN hsq]

theorem exists_conj_T₁ {b : X} (hb : b ∈ S.B) (hcb : ConjTo S.t b) :
    ∃ g ∈ T₁, g * S.t * g⁻¹ = b := by
  have htB : S.t ∈ S.B := subset_closure (by simp)
  set O₁ : Set X := {b | ∃ g ∈ T₁, g * S.t * g⁻¹ = b} with hO₁
  have hidx := relIndex_inf_centralizer_eq_ncard T₁ S.t
  rw [H.inf_centralizer] at hidx
  have hrel : S.data.T.relIndex T₁ * Nat.card S.data.T = Nat.card T₁ := by
    have := relIndex_mul_card (H := S.data.T) (K := T₁)
    rwa [inf_of_le_left H.le] at this
  have hO₁4 : O₁.ncard = 4 := by
    rw [← hidx]
    have hpos : 0 < Nat.card S.data.T := Nat.card_pos
    rw [H.card] at hrel
    exact Nat.eq_of_mul_eq_mul_right hpos hrel
  have hO₁sub : O₁ ⊆ ({S.t, S.t * S.z, S.t * S.k, S.t * S.z * S.k} : Set X) := by
    rintro _ ⟨g, hg, rfl⟩
    have hb' := S.conj_mem_B (H.le_normalizer hg) htB
    rcases (H.fus _ hb').mp ⟨g, rfl⟩ with h | h | h | h <;> simp [h]
  have hO₁eq : O₁ = ({S.t, S.t * S.z, S.t * S.k, S.t * S.z * S.k} : Set X) := by
    refine Set.eq_of_subset_of_ncard_le hO₁sub ?_ (Set.toFinite _)
    rw [hO₁4]
    refine (Set.ncard_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
    rw [Set.ncard_singleton]
  have hbO : b ∈ O₁ := by
    rw [hO₁eq]
    rcases (H.fus b hb).mp hcb with h | h | h | h <;> simp [h]
  exact hbO

theorem mem_T₂_iff {w₀ : X} (hw₀ : w₀ ∈ S.T₂of T₁) (hw₀T : w₀ ∉ S.data.T) {g : X}
    (hg : g ∈ T₁) :
    g ∈ S.T₂of T₁ ↔ (g * S.t * g⁻¹ = S.t ∨ g * S.t * g⁻¹ = w₀ * S.t * w₀⁻¹) := by
  constructor
  · intro h
    rcases (H.mem_T₂of_iff hw₀ hw₀T).mp h with h' | h'
    · left
      rw [(S.data.commute_t h')]
      group
    · right
      have hc := S.data.commute_t h'
      calc g * S.t * g⁻¹ = w₀ * ((w₀⁻¹ * g) * S.t) * g⁻¹ := by group
        _ = w₀ * (S.t * (w₀⁻¹ * g)) * g⁻¹ := by rw [hc]
        _ = w₀ * S.t * w₀⁻¹ := by group
  · rintro (h | h)
    · have hgC : g ∈ centralizer ({S.t} : Set X) := by
        rw [mem_centralizer_singleton_iff]
        calc g * S.t = g * S.t * g⁻¹ * g := by group
          _ = S.t * g := by rw [h]
      have : g ∈ T₁ ⊓ centralizer ({S.t} : Set X) := mem_inf.mpr ⟨hg, hgC⟩
      rw [H.inf_centralizer] at this
      exact H.T_le_T₂of this
    · have hgC : w₀⁻¹ * g ∈ centralizer ({S.t} : Set X) := by
        rw [mem_centralizer_singleton_iff]
        calc w₀⁻¹ * g * S.t = w₀⁻¹ * (g * S.t * g⁻¹) * g := by group
          _ = w₀⁻¹ * (w₀ * S.t * w₀⁻¹) * g := by rw [h]
          _ = S.t * (w₀⁻¹ * g) := by group
      have : w₀⁻¹ * g ∈ T₁ ⊓ centralizer ({S.t} : Set X) :=
        mem_inf.mpr ⟨mul_mem (inv_mem (T₂of_le hw₀)) hg, hgC⟩
      rw [H.inf_centralizer] at this
      have h2 := mul_mem hw₀ (H.T_le_T₂of this)
      rwa [mul_inv_cancel_left] at h2

end Sec5Hyp

end A7Base

end CFSG.ComponentClassification.HSFLit

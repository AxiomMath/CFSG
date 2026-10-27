module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModDefs

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.Cons

open CFSG.Quasithin

theorem normal_le_center_or_eq_top {G : Type*} [Group G] (hG : CFSG.Open.IsQuasisimple G)
    (N : Subgroup G) [N.Normal] : N ≤ Subgroup.center G ∨ N = ⊤ := by
  obtain ⟨hperf, hsimple⟩ := hG
  have hN : (N.map (QuotientGroup.mk' (Subgroup.center G))).Normal :=
    Subgroup.Normal.map ‹N.Normal› _ (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center G))) with
    h | h
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · right
    have h1 : N ⊔ Subgroup.center G = ⊤ := by
      have h2 : N.map (QuotientGroup.mk' (Subgroup.center G)) =
          (⊤ : Subgroup G).map (QuotientGroup.mk' (Subgroup.center G)) := by
        rw [h, Subgroup.map_top, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
      rw [Subgroup.map_eq_map_iff, QuotientGroup.ker_mk'] at h2
      simpa using h2
    have h3 := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top h1 inferInstance
    rw [hperf] at h3
    exact top_le_iff.mp h3

theorem closure_eq_of_conj_invariant {G : Type*} [Group G] {Y : Subgroup G}
    (hY : IsSimpleGroup ↥Y) {S : Set G} (hSY : S ⊆ (Y : Set G)) (hne : ∃ s ∈ S, s ≠ 1)
    (hconj : ∀ s ∈ S, ∀ g ∈ Y, g * s * g⁻¹ ∈ S) : Subgroup.closure S = Y := by
  refine le_antisymm ((Subgroup.closure_le Y).mpr hSY) ?_
  have key : ∀ g ∈ Y, ∀ n ∈ Subgroup.closure S, g * n * g⁻¹ ∈ Subgroup.closure S := by
    intro g hg n hn
    induction hn using Subgroup.closure_induction with
    | mem s hs => exact Subgroup.subset_closure (hconj s hs g hg)
    | one => simp
    | mul a b _ _ ha hb =>
      have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ha
  have hnorm : ((Subgroup.closure S).subgroupOf Y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact key g g.2 n hn
  rcases hY.eq_bot_or_eq_top_of_normal ((Subgroup.closure S).subgroupOf Y) with h | h
  · exfalso
    obtain ⟨s, hs, hs1⟩ := hne
    have : (⟨s, hSY hs⟩ : ↥Y) ∈ (Subgroup.closure S).subgroupOf Y :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure hs)
    rw [h, Subgroup.mem_bot] at this
    exact hs1 (congrArg Subtype.val this)
  · intro y hy
    have : (⟨y, hy⟩ : ↥Y) ∈ (Subgroup.closure S).subgroupOf Y := by rw [h]; trivial
    exact Subgroup.mem_subgroupOf.mp this

theorem orderOf_conj_eq {G : Type*} [Group G] (g s : G) : orderOf (g * s * g⁻¹) = orderOf s := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective s
  simpa [MulAut.conj_apply] using this

variable {V : Type} [CommGroup V]

theorem exists_apply_ne {g : MulAut V} (hg : g ≠ 1) : ∃ v : V, g v ≠ v := by
  by_contra hcon
  push Not at hcon
  exact hg (MulEquiv.ext fun v => hcon v)

theorem exists_move_of_fixV {K : Subgroup (MulAut V)} (hfix : fixV K = ⊥) {W : Subgroup V}
    (hW : W ≠ ⊥) : ∃ k ∈ K, ∃ w ∈ W, k w ≠ w := by
  by_contra hcon
  push Not at hcon
  apply hW
  rw [eq_bot_iff, ← hfix]
  exact fun w hw k hk => hcon k hk w hw

theorem apply_comm {a b : MulAut V} (hab : a * b = b * a) (v : V) : a (b v) = b (a v) := by
  have := congrArg (fun φ : MulAut V => φ v) hab
  simpa [MulAut.mul_apply] using this

@[expose] def stabV (A : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | ∀ a : V, g a ∈ A ↔ a ∈ A}
  one_mem' := fun a => Iff.rfl
  mul_mem' := fun {g h} hg hh a => by
    rw [MulAut.mul_apply, hg, hh]
  inv_mem' := fun {g} hg a => by
    have := hg (g⁻¹ a)
    rw [show g (g⁻¹ a) = a by simp] at this
    exact this.symm

theorem ginv_iff_le_stabV {G : Subgroup (MulAut V)} {A : Subgroup V} :
    GInv G A ↔ G ≤ stabV A := by
  constructor
  · intro h g hg a
    refine ⟨fun ha => ?_, fun ha => h g hg a ha⟩
    have := h g⁻¹ (G.inv_mem hg) _ ha
    simpa using this
  · intro h g hg a ha
    exact (h hg a).mpr ha

theorem ginv_sup_iff {K K' : Subgroup (MulAut V)} {A : Subgroup V} :
    GInv (K ⊔ K') A ↔ GInv K A ∧ GInv K' A := by
  rw [ginv_iff_le_stabV, ginv_iff_le_stabV, ginv_iff_le_stabV, sup_le_iff]

theorem ginv_sup {K : Subgroup (MulAut V)} {A B : Subgroup V} (hA : GInv K A) (hB : GInv K B) :
    GInv K (A ⊔ B) := by
  intro g hg x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hx
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hA g hg a ha) (hB g hg b hb)

@[expose] def actTrivMod (A : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | ∀ v : V, g v * v⁻¹ ∈ A}
  one_mem' := fun v => by simp
  mul_mem' := fun {g h} hg hh v => by
    have : (g * h) v * v⁻¹ = (g (h v) * (h v)⁻¹) * (h v * v⁻¹) := by
      simp [MulAut.mul_apply]
    rw [this]
    exact A.mul_mem (hg _) (hh v)
  inv_mem' := fun {g} hg v => by
    have : g⁻¹ v * v⁻¹ = (g (g⁻¹ v) * (g⁻¹ v)⁻¹)⁻¹ := by simp
    rw [this]
    exact A.inv_mem (hg _)

theorem conj_mem_actTrivMod {K : Subgroup (MulAut V)} {A : Subgroup V} (hA : GInv K A)
    {x g : MulAut V} (hx : x ∈ K) (hg : g ∈ actTrivMod A) : x * g * x⁻¹ ∈ actTrivMod A := by
  intro v
  have : (x * g * x⁻¹) v * v⁻¹ = x (g (x⁻¹ v) * (x⁻¹ v)⁻¹) := by
    simp [MulAut.mul_apply]
  rw [this]
  exact hA x hx _ (hg _)

theorem commV_zpowers_conj_le (y g : MulAut V) :
    commV (Subgroup.zpowers (g * y * g⁻¹)) ≤ (commV (Subgroup.zpowers y)).map g.toMonoidHom := by
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨x, hx, v, rfl⟩
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine ⟨(y ^ j) (g⁻¹ v) * (g⁻¹ v)⁻¹, Subgroup.subset_closure
    ⟨y ^ j, Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) j, g⁻¹ v, rfl⟩, ?_⟩
  rw [conj_zpow]
  simp [MulAut.mul_apply]

theorem card_commV_zpowers_conj_le [Finite V] (y g : MulAut V) :
    Nat.card ↥(commV (Subgroup.zpowers (g * y * g⁻¹))) ≤
      Nat.card ↥(commV (Subgroup.zpowers y)) :=
  calc Nat.card ↥(commV (Subgroup.zpowers (g * y * g⁻¹)))
      ≤ Nat.card ↥((commV (Subgroup.zpowers y)).map g.toMonoidHom) :=
        Subgroup.card_le_of_le (commV_zpowers_conj_le y g)
    _ = Nat.card ↥(commV (Subgroup.zpowers y)) := Subgroup.card_map_of_injective g.injective

theorem apply_mem_commV_of_commute {K : Subgroup (MulAut V)} {b : MulAut V}
    (hcomm : ∀ a ∈ K, a * b = b * a) {w : V} (hw : w ∈ commV K) : b w ∈ commV K := by
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    have h1 : b (x v * v⁻¹) = x (b v) * (b v)⁻¹ := by
      rw [map_mul, map_inv, apply_comm (hcomm x hx) v]
    rw [h1]
    exact Subgroup.subset_closure ⟨x, hx, b v, rfl⟩
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

end CFSG.CGT.PushingUpLit.CGT6.Diag.Cons

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

public section

namespace CFSG.GH74.GLS.LU.Local.Five

section KLinear

variable {V : Type} [AddCommGroup V] [Module (ZMod 5) V]

private theorem kl_smul_eq_zero {a : ZMod 5} {v : V} (ha : a ≠ 0) (h : a • v = 0) : v = 0 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact (smul_eq_zero.mp h).resolve_left ha

private theorem kl_eq_zero_of_add_self {v : V} (h : v + v = 0) : v = 0 := by
  have h2 : (2 : ZMod 5) • v = 0 := by rw [two_smul]; exact h
  exact kl_smul_eq_zero (by decide) h2

private theorem kl_eps_injective (x : V ≃ₗ[ZMod 5] V) (hx5 : ∀ v, x (x (x (x (x v)))) = v) {v : V}
    (h : x v + v = 0) : v = 0 := by
  have h1 : x v = -v := eq_neg_of_add_eq_zero_left h
  have h2 : x (x v) = v := by rw [h1, map_neg, h1, neg_neg]
  have h3 : x (x (x v)) = -v := by rw [h2, h1]
  have h4 : x (x (x (x v))) = v := by rw [h3, map_neg, h1, neg_neg]
  have h5 : x (x (x (x (x v)))) = -v := by rw [h4, h1]
  have h6 := hx5 v
  rw [h5] at h6
  refine kl_eq_zero_of_add_self ?_
  calc v + v = -v + v := by rw [h6]
    _ = 0 := neg_add_cancel v

private theorem kl_eps_surjective [Finite V] (x : V ≃ₗ[ZMod 5] V) (hx5 : ∀ v, x (x (x (x (x v)))) = v)
    (v : V) : ∃ y, x y + y = v := by
  have hinj : Function.Injective (fun y : V => x y + y) := by
    intro a b hab
    have : x (a - b) + (a - b) = 0 := by
      have hab' : x a + a = x b + b := hab
      simp only [map_sub]
      rw [show x a - x b + (a - b) = (x a + a) - (x b + b) by abel, hab', sub_self]
    exact sub_eq_zero.mp (kl_eps_injective x hx5 this)
  exact Finite.injective_iff_surjective.mp hinj v

private theorem kl_mem_of_neg_eigen (u : V ≃ₗ[ZMod 5] V) {F F' : Submodule (ZMod 5) V} (hc : IsCompl F F')
    (huF : ∀ v ∈ F, u v = -v) (huF' : ∀ v ∈ F', u v = v) {g : V} (hg : u g = -g) : g ∈ F := by
  obtain ⟨f, hf, f', hf', rfl⟩ :=
    Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top : g ∈ F ⊔ F')
  rw [map_add, huF f hf, huF' f' hf', neg_add] at hg
  have h3 : f' = -f' := add_left_cancel hg
  have h4 : f' = 0 := kl_eq_zero_of_add_self (eq_neg_iff_add_eq_zero.mp h3)
  rw [h4, add_zero]
  exact hf

private theorem kl_n_mem (x u : V ≃ₗ[ZMod 5] V) {F F' : Submodule (ZMod 5) V} (hc : IsCompl F F')
    (hxF : ∀ v ∈ F, x v = v) (huF : ∀ v ∈ F, u v = -v) (huF' : ∀ v ∈ F', u v = v)
    (hux : ∀ v, u (x v) = x.symm (u v)) (v : V) : x v - x.symm v ∈ F := by
  obtain ⟨f, hf, f', hf', rfl⟩ :=
    Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top : v ∈ F ⊔ F')
  have h1 : x f - x.symm f = 0 := by
    have : x.symm f = f := (LinearEquiv.symm_apply_eq x).mpr (hxF f hf).symm
    rw [hxF f hf, this, sub_self]
  have hux' : ∀ y, u (x.symm y) = x (u y) := by
    intro y
    have := hux (x.symm y)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [this, LinearEquiv.apply_symm_apply]
  have h2 : u (x f' - x.symm f') = -(x f' - x.symm f') := by
    rw [map_sub, hux, hux', huF' f' hf', neg_sub]
  have h3 : x (f + f') - x.symm (f + f') = (x f - x.symm f) + (x f' - x.symm f') := by
    rw [map_add, map_add]; abel
  rw [h3, h1, zero_add]
  exact kl_mem_of_neg_eigen u hc huF huF' h2

private theorem kl_phi_mem [Finite V] (x u : V ≃ₗ[ZMod 5] V) {F F' : Submodule (ZMod 5) V}
    (hc : IsCompl F F') (hxF : ∀ v ∈ F, x v = v) (huF : ∀ v ∈ F, u v = -v)
    (huF' : ∀ v ∈ F', u v = v) (hux : ∀ v, u (x v) = x.symm (u v))
    (hx5 : ∀ v, x (x (x (x (x v)))) = v) (v : V) : x v - v ∈ F := by
  obtain ⟨y, rfl⟩ := kl_eps_surjective x hx5 v
  have h1 := kl_n_mem x u hc hxF huF huF' hux y
  have h2 : x (x y + y) - (x y + y) = x (x y - x.symm y) := by
    rw [map_add, map_sub, LinearEquiv.apply_symm_apply]; abel
  rw [h2, hxF _ h1]
  exact h1

private theorem kl_phi_phi {F : Submodule (ZMod 5) V} (x : V ≃ₗ[ZMod 5] V) (hxF : ∀ v ∈ F, x v = v)
    (hphi : ∀ v, x v - v ∈ F) (v : V) : x (x v) - 2 • x v + v = 0 := by
  have h := hxF _ (hphi v)
  rw [map_sub] at h
  calc x (x v) - 2 • x v + v = (x (x v) - x v) - (x v - v) := by rw [two_nsmul]; abel
    _ = 0 := by rw [h, sub_self]

private theorem kl_fixed_zero (x w : V ≃ₗ[ZMod 5] V) (L3 L4 L5 L6 : Submodule (ZMod 5) V)
    (hxF : ∀ v ∈ L3 ⊔ L4, x v = v) (hww : ∀ v, w (w v) = -v)
    (hw3 : L3.map (w : V →ₗ[ZMod 5] V) = L5) (hw4 : L4.map (w : V →ₗ[ZMod 5] V) = L6)
    (hgen : w ∈ Subgroup.closure ({x, w * x * w⁻¹} : Set (V ≃ₗ[ZMod 5] V)))
    {m : V} (hm : m ∈ L5 ⊔ L6) (hxm : x m = m) : m = 0 := by
  have hmap : (L3 ⊔ L4).map (w : V →ₗ[ZMod 5] V) = L5 ⊔ L6 := by
    rw [Submodule.map_sup, hw3, hw4]
  rw [← hmap] at hm
  obtain ⟨f, hf, hfm⟩ := hm
  have hfm' : w f = m := hfm
  have hwinv : w⁻¹ m = f := by
    show w.symm m = f
    rw [LinearEquiv.symm_apply_eq]
    exact hfm'.symm
  have hy : (w * x * w⁻¹) m = m := by
    show w (x (w⁻¹ m)) = m
    rw [hwinv, hxF f hf, hfm']
  have hle : Subgroup.closure ({x, w * x * w⁻¹} : Set (V ≃ₗ[ZMod 5] V)) ≤
      MulAction.stabilizer (V ≃ₗ[ZMod 5] V) m := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact (MulAction.mem_stabilizer_iff).mpr hxm
    · exact (MulAction.mem_stabilizer_iff).mpr hy
  have hwm : w m = m := (MulAction.mem_stabilizer_iff).mp (hle hgen)
  have h6 : -m = m := by rw [← hww m, hwm, hwm]
  refine kl_eq_zero_of_add_self ?_
  calc m + m = -m + m := by rw [h6]
    _ = 0 := neg_add_cancel m

private theorem kl_pow_apply {F : Submodule (ZMod 5) V} (x : V ≃ₗ[ZMod 5] V) (hxF : ∀ v ∈ F, x v = v)
    (hphi : ∀ v, x v - v ∈ F) (k : ℕ) (v : V) :
    ((x : V →ₗ[ZMod 5] V) ^ k) v = v + k • (x v - v) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    show x (v + n • (x v - v)) = _
    rw [map_add, map_nsmul, hxF _ (hphi v), succ_nsmul]
    abel

private theorem kl_h_phi {F : Submodule (ZMod 5) V} (x h : V ≃ₗ[ZMod 5] V) (hxF : ∀ v ∈ F, x v = v)
    (hphi : ∀ v, x v - v ∈ F) (k : ℕ)
    (hhx : ∀ v, h (x v) = ((x : V →ₗ[ZMod 5] V) ^ k) (h v)) {a : ZMod 5} {m : V}
    (hm : h m = a • m) : h (x m - m) = ((k : ZMod 5) * a) • (x m - m) := by
  rw [map_sub, hhx, hm, map_smul, kl_pow_apply x hxF hphi k m, smul_add, add_sub_cancel_left,
    smul_comm, ← Nat.cast_smul_eq_nsmul (ZMod 5), ← mul_smul]

private theorem kl_eigen_sup {L3 L4 : Submodule (ZMod 5) V} (h34 : Disjoint L3 L4) (h : V ≃ₗ[ZMod 5] V)
    {a3 a4 : ZMod 5} (hh3 : ∀ v ∈ L3, h v = a3 • v) (hh4 : ∀ v ∈ L4, h v = a4 • v)
    {c : ZMod 5} {m : V} (hm : m ∈ L3 ⊔ L4) (hhm : h m = c • m) :
    (a3 ≠ c → m ∈ L4) ∧ (a4 ≠ c → m ∈ L3) := by
  obtain ⟨m3, h3, m4, h4, rfl⟩ := Submodule.mem_sup.mp hm
  rw [map_add, hh3 m3 h3, hh4 m4 h4, smul_add] at hhm
  have key : (a3 - c) • m3 = (c - a4) • m4 := by
    rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add, hhm]
    exact add_comm _ _
  have hz3 : (a3 - c) • m3 = 0 :=
    Submodule.disjoint_def.mp h34 _ (Submodule.smul_mem _ _ h3)
      (key ▸ Submodule.smul_mem _ _ h4)
  have hz4 : (c - a4) • m4 = 0 := key ▸ hz3
  constructor
  · intro ha
    have : m3 = 0 := kl_smul_eq_zero (sub_ne_zero.mpr ha) hz3
    rw [this, zero_add]
    exact h4
  · intro ha
    have : m4 = 0 := kl_smul_eq_zero (sub_ne_zero.mpr (Ne.symm ha)) hz4
    rw [this, add_zero]
    exact h3

private theorem kl_dichotomy {L3 L4 L : Submodule (ZMod 5) V} (x h : V ≃ₗ[ZMod 5] V)
    (hxF : ∀ v ∈ L3 ⊔ L4, x v = v) (hphi : ∀ v, x v - v ∈ L3 ⊔ L4) (h34 : Disjoint L3 L4)
    {a3 a4 : ZMod 5} (hh3 : ∀ v ∈ L3, h v = a3 • v) (hh4 : ∀ v ∈ L4, h v = a4 • v)
    (h34' : a3 ≠ a4) (k : ℕ) (hhx : ∀ v, h (x v) = ((x : V →ₗ[ZMod 5] V) ^ k) (h v))
    {a : ZMod 5} (hL : ∀ v ∈ L, h v = a • v) :
    (∀ m ∈ L, x m - m ∈ L3) ∨ (∀ m ∈ L, x m - m ∈ L4) := by
  by_cases ha : a3 = (k : ZMod 5) * a
  · left
    have ha4 : a4 ≠ (k : ZMod 5) * a := fun h => h34' (ha.trans h.symm)
    intro m hm
    exact (kl_eigen_sup h34 h hh3 hh4 (hphi m)
      (kl_h_phi x h hxF hphi k hhx (hL m hm))).2 ha4
  · right
    intro m hm
    exact (kl_eigen_sup h34 h hh3 hh4 (hphi m)
      (kl_h_phi x h hxF hphi k hhx (hL m hm))).1 ha

private theorem kl_exists_ne_zero {L : Submodule (ZMod 5) V} (hL : Module.finrank (ZMod 5) L = 1) :
    ∃ m ∈ L, m ≠ 0 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨m, hm⟩, hne, -⟩ := finrank_eq_one_iff'.mp hL
  exact ⟨m, hm, fun h => hne (Subtype.ext h)⟩

private theorem kl_same_line {L5 L6 M : Submodule (ZMod 5) V} (x : V ≃ₗ[ZMod 5] V)
    (h56 : Disjoint L5 L6) (d5 : Module.finrank (ZMod 5) L5 = 1)
    (d6 : Module.finrank (ZMod 5) L6 = 1) (dM : Module.finrank (ZMod 5) M = 1)
    (hinj : ∀ m ∈ L5 ⊔ L6, x m = m → m = 0)
    (h5 : ∀ m ∈ L5, x m - m ∈ M) (h6 : ∀ m ∈ L6, x m - m ∈ M) : False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨m5, hm5, hne5⟩ := kl_exists_ne_zero d5
  obtain ⟨m6, hm6, hne6⟩ := kl_exists_ne_zero d6
  have hphi5 : x m5 - m5 ≠ 0 := fun h =>
    hne5 (hinj m5 (Submodule.mem_sup_left hm5) (sub_eq_zero.mp h))
  have hnz : (⟨x m5 - m5, h5 m5 hm5⟩ : M) ≠ 0 := fun h => hphi5 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hnz).mp dM ⟨x m6 - m6, h6 m6 hm6⟩
  have hc' : c • x m5 - c • m5 = x m6 - m6 := by
    rw [← smul_sub]; exact congrArg Subtype.val hc
  have hz : m6 - c • m5 = 0 := by
    refine hinj _ (Submodule.sub_mem _ (Submodule.mem_sup_right hm6)
      (Submodule.smul_mem _ _ (Submodule.mem_sup_left hm5))) ?_
    rw [map_sub, map_smul, ← sub_eq_zero]
    have e : x m6 - c • x m5 - (m6 - c • m5) = (x m6 - m6) - (c • x m5 - c • m5) := by abel
    rw [e, ← hc', sub_self]
  have hm6' : m6 ∈ L5 := by
    rw [sub_eq_zero] at hz
    rw [hz]
    exact Submodule.smul_mem _ _ hm5
  exact hne6 (Submodule.disjoint_def.mp h56 m6 hm6' hm6)

private theorem kl_inv_mem [Finite V] (S : Submodule (ZMod 5) V) (e : V ≃ₗ[ZMod 5] V)
    (he : ∀ s ∈ S, e s ∈ S) {s : V} (hs : s ∈ S) : e⁻¹ s ∈ S := by
  have hinj : Function.Injective (fun t : S => (⟨e t, he t t.2⟩ : S)) := by
    intro t1 t2 h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))
  obtain ⟨t, ht⟩ := Finite.injective_iff_surjective.mp hinj ⟨s, hs⟩
  have h1 : e t = s := congrArg Subtype.val ht
  have h2 : e⁻¹ s = t := by
    rw [← h1]
    exact e.symm_apply_apply t
  rw [h2]
  exact t.2

private theorem kl_preserve_of_closure [Finite V] (S : Submodule (ZMod 5) V) {a b g : V ≃ₗ[ZMod 5] V}
    (ha : ∀ s ∈ S, a s ∈ S) (hb : ∀ s ∈ S, b s ∈ S)
    (hg : g ∈ Subgroup.closure ({a, b} : Set (V ≃ₗ[ZMod 5] V))) : ∀ s ∈ S, g s ∈ S := by
  let P : Subgroup (V ≃ₗ[ZMod 5] V) :=
    { carrier := {e | (∀ s ∈ S, e s ∈ S) ∧ ∀ s ∈ S, e⁻¹ s ∈ S}
      mul_mem' := by
        rintro e1 e2 ⟨h1, h1'⟩ ⟨h2, h2'⟩
        refine ⟨fun s hs => h1 _ (h2 s hs), fun s hs => ?_⟩
        rw [mul_inv_rev]
        exact h2' _ (h1' s hs)
      one_mem' := ⟨fun s hs => hs, fun s hs => hs⟩
      inv_mem' := by
        rintro e ⟨h1, h1'⟩
        exact ⟨h1', fun s hs => by rw [inv_inv]; exact h1 s hs⟩ }
  have hle : Subgroup.closure ({a, b} : Set (V ≃ₗ[ZMod 5] V)) ≤ P := by
    rw [Subgroup.closure_le]
    intro e he
    rcases he with rfl | rfl
    · exact ⟨ha, fun s hs => kl_inv_mem S _ ha hs⟩
    · exact ⟨hb, fun s hs => kl_inv_mem S _ hb hs⟩
  exact (hle hg).1

private theorem kl_cross_x {L3 L4 L6 : Submodule (ZMod 5) V} (x : V ≃ₗ[ZMod 5] V)
    (hxF : ∀ v ∈ L3 ⊔ L4, x v = v) (h6 : ∀ m ∈ L6, x m - m ∈ L3) :
    ∀ s ∈ L3 ⊔ L6, x s ∈ L3 ⊔ L6 := by
  intro s hs
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hs
  have : x (p + q) = (p + (x q - q)) + q := by
    rw [map_add, hxF p (Submodule.mem_sup_left hp)]
    abel
  rw [this]
  exact Submodule.add_mem_sup (Submodule.add_mem _ hp (h6 q hq)) hq

private theorem kl_cross_y {L3 L4 L5 L6 : Submodule (ZMod 5) V} (x w : V ≃ₗ[ZMod 5] V)
    (hxF : ∀ v ∈ L3 ⊔ L4, x v = v) (hww : ∀ v, w (w v) = -v)
    (hw3 : L3.map (w : V →ₗ[ZMod 5] V) = L5) (hw4 : L4.map (w : V →ₗ[ZMod 5] V) = L6)
    (h5 : ∀ m ∈ L5, x m - m ∈ L4) :
    ∀ s ∈ L3 ⊔ L6, (w * x * w⁻¹) s ∈ L3 ⊔ L6 := by
  have hinv : ∀ v, w⁻¹ v = -(w v) := by
    intro v
    show w.symm v = -(w v)
    rw [LinearEquiv.symm_apply_eq, map_neg, hww, neg_neg]
  have hw3' : ∀ a ∈ L3, w a ∈ L5 := fun a ha => hw3 ▸ Submodule.mem_map_of_mem ha
  have hw4' : ∀ a ∈ L4, w a ∈ L6 := fun a ha => hw4 ▸ Submodule.mem_map_of_mem ha
  intro s hs
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hs
  have hp5 : w⁻¹ p ∈ L5 := by
    rw [hinv]
    exact Submodule.neg_mem _ (hw3' p hp)
  have hyp : (w * x * w⁻¹) p = p + w (x (w⁻¹ p) - w⁻¹ p) := by
    show w (x (w⁻¹ p)) = _
    have : w (w⁻¹ p) = p := w.apply_symm_apply p
    rw [map_sub, this]
    abel
  obtain ⟨c, hc, hcq⟩ : ∃ c ∈ L4, w c = q := by
    rw [← hw4] at hq
    exact hq
  have hyq : (w * x * w⁻¹) q = q := by
    have : w⁻¹ q = c := by
      show w.symm q = c
      rw [LinearEquiv.symm_apply_eq]
      exact hcq.symm
    show w (x (w⁻¹ q)) = q
    rw [this, hxF c (Submodule.mem_sup_right hc), hcq]
  rw [map_add, hyp, hyq, add_assoc]
  exact Submodule.add_mem_sup hp (Submodule.add_mem _ (hw4' _ (h5 _ hp5)) hq)

private theorem kl_cross [Finite V] (x w : V ≃ₗ[ZMod 5] V) {L3 L4 L5 L6 : Submodule (ZMod 5) V}
    (hF : Disjoint (L3 ⊔ L4) (L5 ⊔ L6)) (h56 : Disjoint L5 L6)
    (d5 : Module.finrank (ZMod 5) L5 = 1)
    (hxF : ∀ v ∈ L3 ⊔ L4, x v = v) (hww : ∀ v, w (w v) = -v)
    (hw3 : L3.map (w : V →ₗ[ZMod 5] V) = L5) (hw4 : L4.map (w : V →ₗ[ZMod 5] V) = L6)
    (hgen : w ∈ Subgroup.closure ({x, w * x * w⁻¹} : Set (V ≃ₗ[ZMod 5] V)))
    (h5 : ∀ m ∈ L5, x m - m ∈ L4) (h6 : ∀ m ∈ L6, x m - m ∈ L3) : False := by
  have hwS := kl_preserve_of_closure (L3 ⊔ L6) (kl_cross_x x hxF h6)
    (kl_cross_y x w hxF hww hw3 hw4 h5) hgen
  obtain ⟨m5, hm5, hne5⟩ := kl_exists_ne_zero d5
  obtain ⟨a, ha, hwa⟩ : ∃ a ∈ L3, w a = m5 := by
    rw [← hw3] at hm5
    exact hm5
  have hm5S : m5 ∈ L3 ⊔ L6 := by
    rw [← hwa]
    exact hwS a (Submodule.mem_sup_left ha)
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hm5S
  have hpF' : p ∈ L5 ⊔ L6 := by
    have : p = m5 - q := by rw [← hpq]; abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hm5) (Submodule.mem_sup_right hq)
  have hp0 : p = 0 := Submodule.disjoint_def.mp hF p (Submodule.mem_sup_left hp) hpF'
  rw [hp0, zero_add] at hpq
  exact hne5 (Submodule.disjoint_def.mp h56 m5 hm5 (hpq ▸ hq))

end KLinear

theorem K_linear {V : Type} [AddCommGroup V] [Module (ZMod 5) V] [Finite V]
    (x u w h : V ≃ₗ[ZMod 5] V)
    (L3 L4 L5 L6 : Submodule (ZMod 5) V)
    (hc : IsCompl (L3 ⊔ L4) (L5 ⊔ L6))
    (h34 : Disjoint L3 L4) (h56 : Disjoint L5 L6)
    (d3 : Module.finrank (ZMod 5) L3 = 1) (d4 : Module.finrank (ZMod 5) L4 = 1)
    (d5 : Module.finrank (ZMod 5) L5 = 1) (d6 : Module.finrank (ZMod 5) L6 = 1)
    (hxF : ∀ v ∈ L3 ⊔ L4, x v = v)
    (hx5 : ∀ v, x (x (x (x (x v)))) = v)
    (huF : ∀ v ∈ L3 ⊔ L4, u v = -v) (huF' : ∀ v ∈ L5 ⊔ L6, u v = v)
    (hux : ∀ v, u (x v) = x.symm (u v))
    (hww : ∀ v, w (w v) = -v)
    (hw3 : L3.map (w : V →ₗ[ZMod 5] V) = L5) (hw4 : L4.map (w : V →ₗ[ZMod 5] V) = L6)
    (hgen : w ∈ Subgroup.closure ({x, w * x * w⁻¹} : Set (V ≃ₗ[ZMod 5] V)))
    (k : ℕ) (a3 a4 a5 a6 : ZMod 5)
    (hh3 : ∀ v ∈ L3, h v = a3 • v) (hh4 : ∀ v ∈ L4, h v = a4 • v)
    (hh5 : ∀ v ∈ L5, h v = a5 • v) (hh6 : ∀ v ∈ L6, h v = a6 • v) (h34' : a3 ≠ a4)
    (hhx : ∀ v, h (x v) = ((x : V →ₗ[ZMod 5] V) ^ k) (h v)) :
    (∀ v, x (x v) - 2 • x v + v = 0) ∧
    (∀ m ∈ L5, x m - m ∈ L3) ∧ (∀ m ∈ L6, x m - m ∈ L4) ∧
    (∀ m ∈ L5 ⊔ L6, x m = m → m = 0) := by
  have hphi : ∀ v, x v - v ∈ L3 ⊔ L4 := kl_phi_mem x u hc hxF huF huF' hux hx5
  have hinj : ∀ m ∈ L5 ⊔ L6, x m = m → m = 0 := fun m hm hxm =>
    kl_fixed_zero x w L3 L4 L5 L6 hxF hww hw3 hw4 hgen hm hxm
  have hd5 := kl_dichotomy x h hxF hphi h34 hh3 hh4 h34' k hhx hh5
  have hd6 := kl_dichotomy x h hxF hphi h34 hh3 hh4 h34' k hhx hh6
  refine ⟨kl_phi_phi x hxF hphi, ?_⟩
  have hmain : (∀ m ∈ L5, x m - m ∈ L3) ∧ (∀ m ∈ L6, x m - m ∈ L4) := by
    rcases hd5 with h5 | h5 <;> rcases hd6 with h6 | h6
    · exact (kl_same_line x h56 d5 d6 d3 hinj h5 h6).elim
    · exact ⟨h5, h6⟩
    · exact (kl_cross x w hc.disjoint h56 d5 hxF hww hw3 hw4 hgen h5 h6).elim
    · exact (kl_same_line x h56 d5 d6 d4 hinj h5 h6).elim
  exact ⟨hmain.1, hmain.2, hinj⟩

end CFSG.GH74.GLS.LU.Local.Five

module

public import CFSG.Quasithin.MS93.S5A53
import CFSG.Quasithin.Background.A1cA133Lemmas

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Quasithin SemidirectProduct
open scoped commutatorElement

variable {V : Type*} [CommGroup V]

private theorem altNat_cg_cancel {G : Type*} [CommGroup G] (x y z w : G) :
    (z * w⁻¹) * (x * z⁻¹ * (w * y⁻¹)) = x * y⁻¹ := by
  calc (z * w⁻¹) * (x * z⁻¹ * (w * y⁻¹)) = (z * z⁻¹) * (w⁻¹ * w) * (x * y⁻¹) := by ac_rfl
    _ = x * y⁻¹ := by rw [mul_inv_cancel, inv_mul_cancel, one_mul, one_mul]

private theorem altNat_cg_perf {G : Type*} [CommGroup G] (x y z w : G) :
    x * w⁻¹ = (x * y⁻¹ * (z * w⁻¹)⁻¹) * ((z * w⁻¹) * (y * w⁻¹)) := by
  calc x * w⁻¹ = (x * w⁻¹) * (y⁻¹ * y) * ((z * w⁻¹)⁻¹ * (z * w⁻¹)) := by
        rw [inv_mul_cancel, inv_mul_cancel, mul_one, mul_one]
    _ = (x * y⁻¹ * (z * w⁻¹)⁻¹) * ((z * w⁻¹) * (y * w⁻¹)) := by ac_rfl

@[expose] def altNatStep (A₀ : Subgroup (MulAut V)) (S : Subgroup V) : Subgroup V where
  carrier := {v | ∀ a ∈ A₀, a v * v⁻¹ ∈ S}
  one_mem' := fun a _ => by simp
  mul_mem' := fun {x y} hx hy a ha => by
    have : a (x * y) * (x * y)⁻¹ = (a x * x⁻¹) * (a y * y⁻¹) := by
      simp only [map_mul, mul_inv_rev]; ac_rfl
    rw [this]
    exact S.mul_mem (hx a ha) (hy a ha)
  inv_mem' := fun {x} hx a ha => by
    have : a x⁻¹ * (x⁻¹)⁻¹ = (a x * x⁻¹)⁻¹ := by
      simp only [map_inv, inv_inv, mul_inv_rev]; ac_rfl
    rw [this]
    exact S.inv_mem (hx a ha)

@[expose] def altNatF (A₀ : Subgroup (MulAut V)) : ℕ → Subgroup V
  | 0 => fixV A₀
  | k + 1 => altNatStep A₀ (altNatF A₀ k)

theorem mem_altNatF_succ {A₀ : Subgroup (MulAut V)} {k : ℕ} {v : V} :
    v ∈ altNatF A₀ (k + 1) ↔ ∀ a ∈ A₀, a v * v⁻¹ ∈ altNatF A₀ k := Iff.rfl

theorem mem_altNatF_zero {A₀ : Subgroup (MulAut V)} {v : V} :
    v ∈ altNatF A₀ 0 ↔ ∀ a ∈ A₀, a v = v := Iff.rfl

theorem altNatF_smul (A₀ : Subgroup (MulAut V)) :
    ∀ (k : ℕ), ∀ a ∈ A₀, ∀ v ∈ altNatF A₀ k, a v ∈ altNatF A₀ k := by
  intro k
  induction k with
  | zero =>
    intro a ha v hv
    rw [(mem_altNatF_zero.1 hv) a ha]
    exact hv
  | succ k ih =>
    intro a ha v hv b hb
    have hc : a v * v⁻¹ ∈ altNatF A₀ k := hv a ha
    have e : b (a v) * (a v)⁻¹ = (b v * v⁻¹) * (b (a v * v⁻¹) * (a v * v⁻¹)⁻¹) := by
      simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
      exact (altNat_cg_cancel (b (a v)) (a v) (b v) v).symm
    rw [e]
    exact (altNatF A₀ k).mul_mem (hv b hb)
      ((altNatF A₀ k).mul_mem (ih b hb _ hc) ((altNatF A₀ k).inv_mem hc))

theorem altNatF_mono (A₀ : Subgroup (MulAut V)) (k : ℕ) : altNatF A₀ k ≤ altNatF A₀ (k + 1) :=
  fun v hv a ha =>
    (altNatF A₀ k).mul_mem (altNatF_smul A₀ k a ha v hv) ((altNatF A₀ k).inv_mem hv)

theorem altNatF_of_comm {A₀ L : Subgroup (MulAut V)}
    (hcomm : ∀ l ∈ L, ∀ a ∈ A₀, l * a = a * l) :
    ∀ (k : ℕ), ∀ l ∈ L, ∀ v ∈ altNatF A₀ k, l v ∈ altNatF A₀ k := by
  intro k
  induction k with
  | zero =>
    intro l hl v hv b hb
    have h1 : b (l v) = l (b v) :=
      (congrArg (fun f : MulAut V => f v) (hcomm l hl b hb)).symm
    rw [h1, (mem_altNatF_zero.1 hv) b hb]
  | succ k ih =>
    intro l hl v hv b hb
    have h1 : b (l v) = l (b v) :=
      (congrArg (fun f : MulAut V => f v) (hcomm l hl b hb)).symm
    have e : b (l v) * (l v)⁻¹ = l (b v * v⁻¹) := by
      rw [h1]; simp only [map_mul, map_inv]
    rw [e]
    exact ih l hl _ (hv b hb)

section Exhaust

variable {V : Type} [CommGroup V]

theorem altNat_exists_fixed_mod [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {A₀ : Subgroup (MulAut V)}
    (hA₀ : IsPGroup 2 ↥A₀) {N : Subgroup V} (hN : ∀ a ∈ A₀, ∀ x ∈ N, a x ∈ N) (hne : N ≠ ⊤) :
    ∃ v : V, v ∉ N ∧ ∀ a ∈ A₀, a v * v⁻¹ ∈ N := by
  classical
  let φ : MulAut V →* MulAut V := MonoidHom.id _
  let P : Subgroup (V ⋊[φ] MulAut V) := A₀.map inr
  let Y : Subgroup (V ⋊[φ] MulAut V) := (⊤ : Subgroup V).map inl
  let N' : Subgroup (V ⋊[φ] MulAut V) := N.map inl
  have hconj : ∀ (a : MulAut V) (x : V),
      (inl (a x) : V ⋊[φ] MulAut V) = inr a * inl x * (inr a)⁻¹ := fun a x => by
    rw [← map_inv inr a]; exact inl_aut a x
  have hPp : IsPGroup 2 ↥P := hA₀.map inr
  have hVp : IsPGroup 2 V := fun v => ⟨1, by rw [pow_one]; exact hV2 v⟩
  have hYp : IsPGroup 2 ↥Y := (hVp.to_subgroup ⊤).map inl
  have hN'Y : N' ≤ Y := Subgroup.map_mono le_top
  have hYN : IsPGroup 2 ↥(Y ⊔ N') := by rwa [sup_eq_left.2 hN'Y]
  have hnorm : ∀ Q : Subgroup V, (∀ a ∈ A₀, ∀ x ∈ Q, a x ∈ Q) →
      P ≤ Subgroup.normalizer ((Q.map inl : Subgroup (V ⋊[φ] MulAut V)) :
        Set (V ⋊[φ] MulAut V)) := by
    intro Q hQ
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨a x, hQ a ha x hx, hconj a x⟩
    · rintro ⟨y, hy, hyeq⟩
      refine ⟨(a⁻¹) y, hQ a⁻¹ (A₀.inv_mem ha) y hy, ?_⟩
      have h2 : g = inr a⁻¹ * inl y * inr a := by
        rw [hyeq, map_inv]; group
      rw [hconj a⁻¹ y, map_inv inr a, inv_inv, h2, map_inv]
  have hcent : Y ≤ Subgroup.centralizer (N' : Set (V ⋊[φ] MulAut V)) := by
    rintro _ ⟨x, -, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, -, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hY : ¬ Y ≤ N' := by
    intro h
    apply hne
    rw [eq_top_iff]
    intro x _
    obtain ⟨n, hn, hnx⟩ := h (⟨x, trivial, rfl⟩ : (inl x : V ⋊[φ] MulAut V) ∈ Y)
    rwa [← inl_injective hnx]
  obtain ⟨y, hyY, hyN, hyP⟩ := CFSG.Quasithin.MS93.S5.exists_fixed_mod_of_isPGroup hPp hYN
    (hnorm ⊤ fun a _ x _ => trivial) (hnorm N hN) (fun g hg => (Subgroup.centralizer_le_normalizer _) (hcent hg)) (hN'Y.trans Subgroup.le_normalizer) hY
  obtain ⟨v, -, rfl⟩ := hyY
  refine ⟨v, fun hv => hyN ⟨v, hv, rfl⟩, fun a ha => ?_⟩
  obtain ⟨n, hn, hne'⟩ := hyP (inr a) ⟨a, ha, rfl⟩
  have e : (⁅(inr a : V ⋊[φ] MulAut V), inl v⁆ : V ⋊[φ] MulAut V) = inl (a v * v⁻¹) := by
    rw [commutatorElement_def, ← hconj a v, ← map_inv, ← map_mul]
  rw [e] at hne'
  rw [← inl_injective hne']
  exact hn

theorem altNat_exists_mem_F [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {A₀ : Subgroup (MulAut V)}
    (hA₀ : IsPGroup 2 ↥A₀) (v : V) : ∃ k, v ∈ altNatF A₀ k := by
  by_contra hcon
  push Not at hcon
  have hne : ∀ k, altNatF A₀ k ≠ ⊤ := fun k h => hcon k (by rw [h]; trivial)
  have hlt : ∀ k, altNatF A₀ k < altNatF A₀ (k + 1) := fun k => by
    refine lt_of_le_of_ne (altNatF_mono A₀ k) fun h => ?_
    obtain ⟨w, hw, hwa⟩ := altNat_exists_fixed_mod hV2 hA₀ (altNatF_smul A₀ k) (hne k)
    apply hw
    rw [h]
    exact mem_altNatF_succ.2 hwa
  have hcard : ∀ k, k + 1 ≤ Nat.card (altNatF A₀ k) := by
    intro k
    induction k with
    | zero => exact Nat.card_pos
    | succ k ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (Subgroup.card_lt_of_lt (hlt k)))
  have h1 := hcard (Nat.card V)
  have h2 : Nat.card (altNatF A₀ (Nat.card V)) ≤ Nat.card V :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  omega

end Exhaust

theorem altNat_perf_step {L : Subgroup (MulAut V)} (hL : Group.IsPerfect ↥L) {N₀ D N : Subgroup V}
    (hN : ∀ v ∈ N, ∀ l ∈ L, l v * v⁻¹ ∈ D) (hD : ∀ d ∈ D, ∀ l ∈ L, l d * d⁻¹ ∈ N₀) :
    ∀ v ∈ N, ∀ l ∈ L, l v * v⁻¹ ∈ N₀ := by
  intro v hv
  let δ : ↥L →* V ⧸ N₀ :=
    MonoidHom.mk' (fun l => (QuotientGroup.mk ((l : MulAut V) v * v⁻¹) : V ⧸ N₀)) (fun l l' => by
      have hd : (l' : MulAut V) v * v⁻¹ ∈ D := hN v hv l' l'.2
      have he := hD _ hd l l.2
      have key : ((l * l' : ↥L) : MulAut V) v * v⁻¹ =
          ((l : MulAut V) ((l' : MulAut V) v * v⁻¹) * ((l' : MulAut V) v * v⁻¹)⁻¹) *
            (((l' : MulAut V) v * v⁻¹) * ((l : MulAut V) v * v⁻¹)) := by
        simp only [Subgroup.coe_mul, MulAut.mul_apply, map_mul, map_inv]
        exact altNat_cg_perf _ _ _ _
      show (QuotientGroup.mk (((l * l' : ↥L) : MulAut V) v * v⁻¹) : V ⧸ N₀) =
        QuotientGroup.mk ((l : MulAut V) v * v⁻¹) * QuotientGroup.mk ((l' : MulAut V) v * v⁻¹)
      rw [key, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 he, one_mul,
        QuotientGroup.mk_mul, mul_comm])
  have h1 : δ = 1 := CFSG.Quasithin.A1c.hom_eq_one_of_perfect_quotient (MonoidHom.id ↥L)
    Function.surjective_id hL δ (by simp)
  intro l hl
  have h2 := DFunLike.congr_fun h1 ⟨l, hl⟩
  exact (QuotientGroup.eq_one_iff _).1 h2

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

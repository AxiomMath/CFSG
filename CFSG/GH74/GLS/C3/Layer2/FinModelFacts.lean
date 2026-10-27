module

public import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GH74.GLS.C3.Layer2.FinModelFactsData
public import CFSG.GH74.GLS.C3.Layer2.FinModelFactsGeneric
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2

open scoped Classical in
structure ModelFacts (n : ℕ) (R : Subgroup (alternatingGroup (Fin (n + 4))))
    (a₀ y0 : alternatingGroup (Fin (n + 4))) : Prop where
  sq : a₀ ^ 2 = 1
  notin : a₀ ∉ R
  norm : ∀ r ∈ R, a₀ * r * a₀⁻¹ ∈ R
  odd : ∀ r ∈ R, orderOf (r * a₀) = 2 →
    numMoved (((r * a₀ : alternatingGroup (Fin (n + 4)))) : Perm (Fin (n + 4))) = 8
  eta : ∀ η : ↥(Subgroup.centralizer {a₀} ⊓ (R ⊔ Subgroup.zpowers a₀)) →*
        alternatingGroup (Fin (n + 4)),
      Function.Injective η →
      (∀ h : a₀ ∈ Subgroup.centralizer {a₀} ⊓ (R ⊔ Subgroup.zpowers a₀), η ⟨a₀, h⟩ = y0) →
      (∀ w, η w ∈ R) →
      ∃ w : ↥(Subgroup.centralizer {a₀} ⊓ (R ⊔ Subgroup.zpowers a₀)), orderOf w = 2 ∧
        numMoved ((η w : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) ≠
          (if (w : alternatingGroup (Fin (n + 4))) ∈ R then
            numMoved ((w : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) else 4)
  conj : ∀ w ∈ R ⊔ Subgroup.zpowers a₀, w ∉ R → orderOf w = 2 → ∃ r ∈ R, r * a₀ * r⁻¹ = w
  cent : ∀ y ∈ R ⊔ Subgroup.zpowers a₀, orderOf y = 2 →
    Nat.card ↥(Subgroup.centralizer ({y} : Set (alternatingGroup (Fin (n + 4)))) ⊓
      (R ⊔ Subgroup.zpowers a₀)) = 64 → y = y0 ∨ y = a₀ * y0 * a₀⁻¹

namespace Facts

theorem sign_a0perm (n : ℕ) [NeZero n] : sign (a0perm n) = 1 := by
  have hne : ∀ (i : Fin n) (j : Fin 4), Fin.castAdd 4 i ≠ Fin.natAdd n j := by
    intro i j h
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    have := i.isLt
    omega
  rw [a0perm, map_mul, map_mul, map_mul, sign_swap (hne 0 0), sign_swap (hne 1 1),
    sign_swap (hne 2 2), sign_swap (hne 3 3)]
  decide

def a0A (n : ℕ) [NeZero n] : alternatingGroup (Fin (n + 4)) :=
  ⟨a0perm n, mem_alternatingGroup.2 (sign_a0perm n)⟩

theorem coe_sq_eq_one {m : ℕ} (x : alternatingGroup (Fin m)) :
    x ^ 2 = 1 ↔ (x : Perm (Fin m)) * x = 1 := by
  rw [sq]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

variable {n : ℕ} [NeZero n]

theorem a0A_mul_self (F : FactsProp n) : a0A n * a0A n = 1 := Subtype.ext F.sq

theorem mem_range_iff
    (hn : n = 6 ∨ n = 7) (z : alternatingGroup (Fin (n + 4))) :
    z ∈ (embT n).range ↔ (z : Perm (Fin (n + 4))) ∈ Rl n := by
  rw [mem_Rl_iff]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨(t : Amb n), (mem_T0_iff n hn _).1 t.2, rfl⟩
  · rintro ⟨q, hq, hz⟩
    exact ⟨⟨q, (mem_T0_iff n hn q).2 hq⟩, Subtype.ext hz⟩

theorem exists_lift_Rl
    (hn : n = 6 ∨ n = 7) {p : Perm (Fin (n + 4))} (hp : p ∈ Rl n) :
    ∃ z : alternatingGroup (Fin (n + 4)), z ∈ (embT n).range ∧ (z : Perm (Fin (n + 4))) = p := by
  obtain ⟨z, hz⟩ : ∃ z : alternatingGroup (Fin (n + 4)), (z : Perm (Fin (n + 4))) = p := by
    obtain ⟨t, ht, rfl⟩ := (mem_Rl_iff n p).1 hp
    exact ⟨embT n ⟨t, (mem_T0_iff n hn t).2 ht⟩, rfl⟩
  exact ⟨z, (mem_range_iff hn z).2 (hz ▸ hp), hz⟩

theorem a0A_norm (hn : n = 6 ∨ n = 7) (F : FactsProp n) :
    ∀ r ∈ (embT n).range, a0A n * r * (a0A n)⁻¹ ∈ (embT n).range := by
  intro r hr
  rw [mem_range_iff hn] at hr ⊢
  exact F.norm _ hr

theorem mem_S_iff
    (hn : n = 6 ∨ n = 7) (F : FactsProp n) (z : alternatingGroup (Fin (n + 4))) :
    z ∈ (embT n).range ⊔ Subgroup.zpowers (a0A n) ↔ (z : Perm (Fin (n + 4))) ∈ Sl n := by
  rw [mem_sup_zpowers_iff_mul_self _ _ (a0A_mul_self F) (a0A_norm hn F), mem_Sl_iff n F.sq,
    mem_range_iff hn, mem_range_iff hn]
  rfl

theorem exists_lift_Sl
    (hn : n = 6 ∨ n = 7) (F : FactsProp n) {p : Perm (Fin (n + 4))}
    (hp : p ∈ Sl n) : ∃ z : alternatingGroup (Fin (n + 4)), (z : Perm (Fin (n + 4))) = p := by
  rw [mem_Sl_iff n F.sq] at hp
  rcases hp with hp | hp
  · obtain ⟨z, -, hz⟩ := exists_lift_Rl hn hp
    exact ⟨z, hz⟩
  · obtain ⟨z, -, hz⟩ := exists_lift_Rl hn hp
    refine ⟨z * a0A n, ?_⟩
    show (z : Perm (Fin (n + 4))) * a0perm n = p
    rw [hz, mul_assoc, F.sq, mul_one]

theorem mem_CS_iff
    (hn : n = 6 ∨ n = 7) (F : FactsProp n) (z : alternatingGroup (Fin (n + 4))) :
    z ∈ Subgroup.centralizer {a0A n} ⊓ ((embT n).range ⊔ Subgroup.zpowers (a0A n)) ↔
      (z : Perm (Fin (n + 4))) ∈ Cl n := by
  rw [mem_Cl_iff, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, mem_S_iff hn F]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, congrArg Subtype.val h1⟩
  · rintro ⟨h2, h1⟩
    exact ⟨Subtype.ext h1, h2⟩

end Facts

open Facts

theorem model_facts
    (n : ℕ) [NeZero n] (hn : n = 6 ∨ n = 7) :
    ∃ a₀ : alternatingGroup (Fin (n + 4)), (a₀ : Perm (Fin (n + 4))) = a0perm n ∧
      ModelFacts n (embT n).range a₀ (embT n (x0T n)) := by
  have F := factsProp n hn
  refine ⟨a0A n, rfl, ?_, ?_, a0A_norm hn F, ?_, ?_, ?_, ?_⟩
  · rw [sq]
    exact a0A_mul_self F
  · rw [mem_range_iff hn]
    exact F.notin
  · intro r hr ho
    have hr' := (mem_range_iff hn r).1 hr
    obtain ⟨h1, h2⟩ := orderOf_eq_prime_iff.1 ho
    exact F.odd _ hr' ((coe_sq_eq_one _).1 h1) (fun h => h2 (Subtype.ext h))
  · intro η hinj h0 hR
    obtain ⟨x, hx, hne⟩ := F.eta _
      ((alternatingGroup (Fin (n + 4))).subtype.comp (Subgroup.subtype _))
      ((alternatingGroup (Fin (n + 4))).subtype.comp η)
      (fun x y h => Subtype.ext (Subtype.ext h))
      (fun p hp => by
        obtain ⟨z, hz⟩ := exists_lift_Sl hn F ((mem_Cl_iff n p).1 hp).1
        exact ⟨⟨z, (mem_CS_iff hn F z).2 (hz ▸ hp)⟩, hz⟩)
      (fun x => (mem_range_iff hn _).1 (hR x))
      (fun c hc => by
        have hca : (c : alternatingGroup (Fin (n + 4))) = a0A n := Subtype.ext hc
        have hmem : a0A n ∈
            Subgroup.centralizer {a0A n} ⊓ ((embT n).range ⊔ Subgroup.zpowers (a0A n)) := by
          have h := c.2
          rw [hca] at h
          exact h
        have hcc : c = ⟨a0A n, hmem⟩ := Subtype.ext hca
        show ((η c : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) = emb n (x0 n)
        rw [hcc, h0 hmem]
        rfl)
    refine ⟨x, hx, fun h1 => hne ?_⟩
    show numMoved ((η x : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) =
      if ((x : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) ∈ Rl n then
        numMoved ((x : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) else 4
    by_cases hxR : (x : alternatingGroup (Fin (n + 4))) ∈ (embT n).range
    · have hxR' := (mem_range_iff hn _).1 hxR
      simp only [hxR', ↓reduceIte]
      simp only [hxR, ↓reduceIte] at h1
      exact h1
    · have hxR' : ¬ ((x : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) ∈ Rl n :=
        fun h => hxR ((mem_range_iff hn _).2 h)
      simp only [hxR', ↓reduceIte]
      simp only [hxR, ↓reduceIte] at h1
      exact h1
  · intro w hw hwR hwo
    rw [mem_sup_zpowers_iff_mul_self _ _ (a0A_mul_self F) (a0A_norm hn F)] at hw
    have hw' : w * a0A n ∈ (embT n).range := hw.resolve_left hwR
    have hp : ((w * a0A n : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) ∈ Rl n :=
      (mem_range_iff hn _).1 hw'
    have e : ((w * a0A n : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) * a0perm n =
        (w : Perm (Fin (n + 4))) := by
      show (w : Perm (Fin (n + 4))) * a0perm n * a0perm n = (w : Perm (Fin (n + 4)))
      rw [mul_assoc, F.sq, mul_one]
    have hww : (w : Perm (Fin (n + 4))) * w = 1 :=
      (coe_sq_eq_one w).1 (orderOf_eq_prime_iff.1 hwo).1
    obtain ⟨r, hr, hrw⟩ := F.conj _ hp (by rw [e]; exact hww)
    rw [e] at hrw
    obtain ⟨z, hzR, hz⟩ := exists_lift_Rl hn hr
    refine ⟨z, hzR, Subtype.ext ?_⟩
    show (z : Perm (Fin (n + 4))) * a0perm n * (z : Perm (Fin (n + 4)))⁻¹ = (w : Perm (Fin (n + 4)))
    rw [hz]
    exact hrw
  · intro y hy hyo hcard
    have hy' : (y : Perm (Fin (n + 4))) ∈ Sl n := (mem_S_iff hn F y).1 hy
    obtain ⟨hy1, hy2⟩ := orderOf_eq_prime_iff.1 hyo
    have hlen : ((Sl n).filter fun p =>
        decide ((y : Perm (Fin (n + 4))) * p = p * (y : Perm (Fin (n + 4))))).length = 64 := by
      rw [← hcard]
      symm
      apply natCard_subgroup_eq_length
      · exact F.nodup.filter _
      · intro z
        rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, mem_S_iff hn F, List.mem_filter,
          decide_eq_true_eq]
        simp only [Set.mem_singleton_iff, forall_eq]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h2, congrArg Subtype.val h1⟩
        · rintro ⟨h2, h1⟩
          exact ⟨Subtype.ext h1, h2⟩
      · intro p hp
        exact exists_lift_Sl hn F (List.mem_filter.1 hp).1
    rcases F.cent _ hy' ((coe_sq_eq_one y).1 hy1) (fun h => hy2 (Subtype.ext h)) hlen with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

end CFSG.GH74.GLS.C3.Layer2.Model

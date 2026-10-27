module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Act
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitAct

public section

namespace CFSG.EvenSmallLie.OmegaEight.NSplit

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type*} [Group G]

structure Branch (ε : Eps) (t : G) (Q TH : Subgroup G) (ψ : V6 → G) : Prop where
  orderOf_t : orderOf t = 2
  ψ_add : ∀ v w, ψ (v + w) = ψ v * ψ w
  ψ_inj : Function.Injective ψ
  ψ_mem : ∀ v, ψ v ∈ Q
  mem_ψ : ∀ x ∈ Q, ∃ v, ψ v = x
  commute_ψ : ∀ v, ψ v * t = t * ψ v
  t_not_mem : t ∉ Q
  centralizer_E : centralizer ((Q ⊔ zpowers t : Subgroup G) : Set G) = Q ⊔ zpowers t
  normalizer_le : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (Q : Set G)
  Zset_eq : ∀ v, v ∈ Zset t Q ψ ↔ qfV ε v = 0
  onto : ∀ σ ∈ affGroup ε, ∃ g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G),
    ∀ v, affF t ψ g v = σ v
  levi : ∃ X : Subgroup G, X ≤ centralizer ({t} : Set G) ⊓ normalizer (Q : Set G) ∧
    X ⊓ (Q ⊔ zpowers t) = ⊥ ∧ ∀ σ ∈ orthGroup ε, ∃ g ∈ X, ∀ v, lin ψ g v = σ v
  TH_le : TH ≤ centralizer ({t} : Set G)
  TH_pgroup : IsPGroup 2 TH
  TH_max : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V → TH ≤ V → V = TH
  TH_le_normalizer : TH ≤ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)

namespace Branch

variable {ε : Eps} {t : G} {Q TH : Subgroup G} {ψ : V6 → G} (hB : Branch ε t Q TH ψ)
include hB

theorem t_mul_t : t * t = 1 := by
  rw [← pow_two, ← hB.orderOf_t, pow_orderOf_eq_one]

theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hB.t_mul_t

theorem ψ_zero : ψ 0 = 1 := by
  have h := hB.ψ_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem ψ_mul_self (v : V6) : ψ v * ψ v = 1 := by
  rw [← hB.ψ_add, CharTwo.add_self_eq_zero, hB.ψ_zero]

theorem ψ_coord {x : G} (hx : x ∈ Q) : ψ (coord ψ x) = x := by
  obtain ⟨v, rfl⟩ := hB.mem_ψ x hx
  rw [coord, Function.leftInverse_invFun hB.ψ_inj v]

theorem coord_ψ (v : V6) : coord ψ (ψ v) = v := Function.leftInverse_invFun hB.ψ_inj v

theorem commute_sup : ∀ a ∈ Q, ∀ b ∈ zpowers t, a * b = b * a := by
  intro a ha b hb
  obtain ⟨v, rfl⟩ := hB.mem_ψ a ha
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
  exact ((Commute.zpow_right (hB.commute_ψ v) k))

theorem mem_zpowers_t {z : G} (hz : z ∈ zpowers t) : z = 1 ∨ z = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
  rw [← zpow_mod_orderOf, hB.orderOf_t]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [Nat.cast_ofNat, h]
  · exact Or.inl (zpow_zero t)
  · exact Or.inr (zpow_one t)

theorem mem_E_iff {x : G} : x ∈ Q ⊔ zpowers t ↔ ∃ v, x = ψ v ∨ x = t * ψ v := by
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      hB.commute_sup hx
    obtain ⟨v, rfl⟩ := hB.mem_ψ a ha
    rcases hB.mem_zpowers_t hb with rfl | rfl
    · exact ⟨v, Or.inl (mul_one _)⟩
    · exact ⟨v, Or.inr (hB.commute_ψ v)⟩
  · rintro ⟨v, rfl | rfl⟩
    · exact mem_sup_left (hB.ψ_mem v)
    · exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left (hB.ψ_mem v))

omit hB in
theorem t_mem_E : t ∈ Q ⊔ zpowers t := mem_sup_right (mem_zpowers t)

theorem conj_t_eq {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) :
    ∃ v, g * t * g⁻¹ = t * ψ v := by
  obtain ⟨v, h | h⟩ := hB.mem_E_iff.1 ((mem_normalizer_iff.1 hg t).1 t_mem_E)
  · exfalso
    apply hB.t_not_mem
    have hQ := (mem_normalizer_iff.1 (hB.normalizer_le (inv_mem hg))) (ψ v)
    have h1 : g⁻¹ * ψ v * g⁻¹⁻¹ = t := by rw [← h]; group
    rw [← h1]
    exact hQ.1 (hB.ψ_mem v)
  · exact ⟨v, h⟩

theorem conj_ψ_mem {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    (v : V6) : g * ψ v * g⁻¹ ∈ Q :=
  (mem_normalizer_iff.1 (hB.normalizer_le hg) (ψ v)).1 (hB.ψ_mem v)

theorem ψ_lin {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) (v : V6) :
    ψ (lin ψ g v) = g * ψ v * g⁻¹ :=
  hB.ψ_coord (hB.conj_ψ_mem hg v)

theorem t_affF {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) (v : V6) :
    t * ψ (affF t ψ g v) = g * (t * ψ v) * g⁻¹ := by
  have hmem : t * (g * (t * ψ v) * g⁻¹) ∈ Q := by
    obtain ⟨w, hw⟩ := hB.conj_t_eq hg
    have h1 : t * (g * (t * ψ v) * g⁻¹) = ψ w * (g * ψ v * g⁻¹) :=
      calc t * (g * (t * ψ v) * g⁻¹) = t * (g * t * g⁻¹) * (g * ψ v * g⁻¹) := by group
        _ = t * (t * ψ w) * (g * ψ v * g⁻¹) := by rw [hw]
        _ = (t * t) * ψ w * (g * ψ v * g⁻¹) := by group
        _ = ψ w * (g * ψ v * g⁻¹) := by rw [hB.t_mul_t, one_mul]
    rw [h1]
    exact mul_mem (hB.ψ_mem w) (hB.conj_ψ_mem hg v)
  rw [affF, hB.ψ_coord hmem, ← mul_assoc, hB.t_mul_t, one_mul]

theorem affF_eq_iff {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    (v w : V6) : affF t ψ g v = w ↔ g * (t * ψ v) * g⁻¹ = t * ψ w := by
  rw [← hB.t_affF hg]
  constructor
  · rintro rfl; rfl
  · intro h; exact hB.ψ_inj (mul_left_cancel h)

theorem affF_mul {g h : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    (hh : h ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) (v : V6) :
    affF t ψ (g * h) v = affF t ψ g (affF t ψ h v) := by
  rw [hB.affF_eq_iff (mul_mem hg hh), hB.t_affF hg, hB.t_affF hh]
  group

theorem affF_one (v : V6) : affF t ψ 1 v = v := by
  rw [hB.affF_eq_iff (one_mem _)]
  group

theorem affF_eq_add {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    (v : V6) : affF t ψ g v = affF t ψ g 0 + lin ψ g v := by
  rw [hB.affF_eq_iff hg]
  calc g * (t * ψ v) * g⁻¹ = (g * (t * ψ 0) * g⁻¹) * (g * ψ v * g⁻¹) := by
        rw [hB.ψ_zero]; group
    _ = t * ψ (affF t ψ g 0) * ψ (lin ψ g v) := by
        rw [hB.t_affF hg, hB.ψ_lin hg]
    _ = t * ψ (affF t ψ g 0 + lin ψ g v) := by rw [hB.ψ_add, mul_assoc]

theorem lin_add {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) (v w : V6) :
    lin ψ g (v + w) = lin ψ g v + lin ψ g w := by
  apply hB.ψ_inj
  rw [hB.ψ_lin hg, hB.ψ_add, hB.ψ_add, hB.ψ_lin hg, hB.ψ_lin hg]
  group

theorem affF_mem_Zset_iff {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    (v : V6) : affF t ψ g v ∈ Zset t Q ψ ↔ v ∈ Zset t Q ψ := by
  constructor
  · rintro ⟨h, hh, hht⟩
    refine ⟨g⁻¹ * h, mul_mem (inv_mem hg) hh, ?_⟩
    have : g * (t * ψ v) * g⁻¹ = h * t * h⁻¹ := by rw [hht, hB.t_affF hg]
    calc g⁻¹ * h * t * (g⁻¹ * h)⁻¹ = g⁻¹ * (h * t * h⁻¹) * g := by group
      _ = g⁻¹ * (g * (t * ψ v) * g⁻¹) * g := by rw [this]
      _ = t * ψ v := by group
  · rintro ⟨h, hh, hht⟩
    refine ⟨g * h, mul_mem hg hh, ?_⟩
    calc g * h * t * (g * h)⁻¹ = g * (h * t * h⁻¹) * g⁻¹ := by group
      _ = g * (t * ψ v) * g⁻¹ := by rw [hht]
      _ = t * ψ (affF t ψ g v) := (hB.t_affF hg v).symm

@[expose] noncomputable def affHomB :
    normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) →* Equiv.Perm V6 where
  toFun g :=
    { toFun := affF t ψ g
      invFun := affF t ψ (g : G)⁻¹
      left_inv := fun v => by
        rw [← hB.affF_mul (inv_mem g.2) g.2, inv_mul_cancel, hB.affF_one]
      right_inv := fun v => by
        rw [← hB.affF_mul g.2 (inv_mem g.2), mul_inv_cancel, hB.affF_one] }
  map_one' := Equiv.ext hB.affF_one
  map_mul' g h := Equiv.ext (hB.affF_mul g.2 h.2)

theorem affHomB_apply (g : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) (v : V6) :
    hB.affHomB g v = affF t ψ g v := rfl

theorem affHomB_mem (g : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) :
    hB.affHomB g ∈ affGroup ε := by
  refine ⟨fun v => ?_, fun x y z => ?_⟩
  · have h := hB.affF_mem_Zset_iff g.2 v
    rw [hB.Zset_eq, hB.Zset_eq] at h
    rw [hB.affHomB_apply]
    rcases qfV_cases ε v with hv | hv <;> rcases qfV_cases ε (affF t ψ g v) with hw | hw
    · rw [hv, hw]
    · exact absurd (h.2 hv) (by rw [hw]; exact one_ne_zero)
    · exact absurd (h.1 hw) (by rw [hv]; exact one_ne_zero)
    · rw [hv, hw]
  · simp only [hB.affHomB_apply]
    rw [hB.affF_eq_add g.2, hB.affF_eq_add g.2 x, hB.affF_eq_add g.2 y,
      hB.affF_eq_add g.2 z, hB.lin_add g.2, hB.lin_add g.2]
    set c := affF t ψ (g : G) 0
    have hc : c + c = 0 := CharTwo.add_self_eq_zero c
    calc c + (lin ψ g x + lin ψ g y + lin ψ g z) =
        (c + c) + c + (lin ψ g x + lin ψ g y + lin ψ g z) := by rw [hc, zero_add]
      _ = c + lin ψ g x + (c + lin ψ g y) + (c + lin ψ g z) := by abel

@[expose] noncomputable def piHom :
    normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) →* affGroup ε :=
  hB.affHomB.codRestrict (affGroup ε) hB.affHomB_mem

theorem piHom_apply (g : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) (v : V6) :
    ((hB.piHom g : affGroup ε) : Equiv.Perm V6) v = affF t ψ g v := rfl

theorem piHom_surjective : Function.Surjective hB.piHom := by
  rintro ⟨σ, hσ⟩
  obtain ⟨g, hg, hgσ⟩ := hB.onto σ hσ
  exact ⟨⟨g, hg⟩, Subtype.ext (Equiv.ext hgσ)⟩

theorem piHom_eq_one_iff (g : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) :
    hB.piHom g = 1 ↔ (g : G) ∈ Q ⊔ zpowers t := by
  have key : hB.piHom g = 1 ↔ ∀ v, affF t ψ g v = v := by
    constructor
    · intro h v
      have := congrArg (fun σ : affGroup ε => (σ : Equiv.Perm V6) v) h
      exact this
    · intro h
      exact Subtype.ext (Equiv.ext h)
  rw [key]
  constructor
  · intro h
    have hc : ∀ v, (g : G) * (t * ψ v) * (g : G)⁻¹ = t * ψ v := fun v =>
      (hB.affF_eq_iff g.2 v v).1 (h v)
    have ht : (g : G) * t * (g : G)⁻¹ = t := by simpa [hB.ψ_zero] using hc 0
    have hq : ∀ v, (g : G) * ψ v * (g : G)⁻¹ = ψ v := by
      intro v
      have h1 := hc v
      have h2 : (g : G) * (t * ψ v) * (g : G)⁻¹ = ((g : G) * t * (g : G)⁻¹) *
          ((g : G) * ψ v * (g : G)⁻¹) := by group
      rw [h2, ht] at h1
      exact mul_left_cancel h1
    have hcen : (g : G) ∈ centralizer ((Q ⊔ zpowers t : Subgroup G) : Set G) := by
      refine mem_centralizer_iff.2 fun y hy => ?_
      obtain ⟨v, rfl | rfl⟩ := hB.mem_E_iff.1 hy
      · calc ψ v * g = (g : G) * ψ v * (g : G)⁻¹ * g := by rw [hq]
          _ = g * ψ v := by group
      · calc t * ψ v * g = (g : G) * (t * ψ v) * (g : G)⁻¹ * g := by rw [hc]
          _ = g * (t * ψ v) := by group
    exact hB.centralizer_E.le hcen
  · intro hgE v
    rw [hB.affF_eq_iff g.2]
    have hc : (t * ψ v) * g = g * (t * ψ v) := by
      have h1 : t * ψ v ∈ Q ⊔ zpowers t := hB.mem_E_iff.2 ⟨v, Or.inr rfl⟩
      exact (mem_centralizer_iff.1 (hB.centralizer_E.ge hgE) _ h1)
    rw [← hc, mul_inv_cancel_right]

omit hB in
@[expose] def tPow (t : G) (c : ZMod 2) : G := if c = 1 then t else 1

theorem tPow_add (c d : ZMod 2) : tPow t (c + d) = tPow t c * tPow t d := by
  rcases zmod2_cases c with rfl | rfl <;> rcases zmod2_cases d with rfl | rfl <;>
    simp [tPow, hB.t_mul_t, show (1 : ZMod 2) + 1 = 0 from rfl]

theorem tPow_commute_ψ (c : ZMod 2) (v : V6) : tPow t c * ψ v = ψ v * tPow t c := by
  rcases zmod2_cases c with rfl | rfl <;> simp [tPow, hB.commute_ψ v]

omit hB in
@[expose] def ιG (t : G) (ψ : V6 → G) (x : V7) : G := tPow t (x 6) * ψ (vOf x)

theorem ιG_mem_E (x : V7) : ιG t ψ x ∈ Q ⊔ zpowers t := by
  rw [ιG, tPow]
  split
  · exact hB.mem_E_iff.2 ⟨vOf x, Or.inr rfl⟩
  · rw [one_mul]; exact hB.mem_E_iff.2 ⟨vOf x, Or.inl rfl⟩

omit hB in
theorem E_le_N : Q ⊔ zpowers t ≤ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
  Subgroup.le_normalizer

@[expose] def ι (x : V7) : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
  ⟨ιG t ψ x, E_le_N (hB.ιG_mem_E x)⟩

theorem ι_coe (x : V7) : (hB.ι x : G) = ιG t ψ x := rfl

theorem ι_add (x y : V7) : hB.ι (x + y) = hB.ι x * hB.ι y := by
  apply Subtype.ext
  simp only [ι_coe, ιG, Subgroup.coe_mul, Pi.add_apply, vOf_add, hB.ψ_add, hB.tPow_add]
  rw [mul_assoc, ← mul_assoc (tPow t (y 6)), hB.tPow_commute_ψ, mul_assoc, mul_assoc]

theorem not_t_mul_eq (v w : V6) : t * ψ v ≠ ψ w := by
  intro h
  apply hB.t_not_mem
  have : t = ψ w * (ψ v)⁻¹ := by rw [← h]; group
  rw [this]
  exact mul_mem (hB.ψ_mem w) (inv_mem (hB.ψ_mem v))

theorem ι_inj : Function.Injective hB.ι := by
  intro x y h
  have h' : ιG t ψ x = ιG t ψ y := congrArg Subtype.val h
  have hc : x 6 = y 6 := by
    rcases zmod2_cases (x 6) with hx | hx <;> rcases zmod2_cases (y 6) with hy | hy
    · rw [hx, hy]
    · simp only [ιG, tPow, hx, hy, zero_ne_one, ite_false, ite_true, one_mul] at h'
      exact absurd h'.symm (hB.not_t_mul_eq _ _)
    · simp only [ιG, tPow, hx, hy, zero_ne_one, ite_false, ite_true, one_mul] at h'
      exact absurd h' (hB.not_t_mul_eq _ _)
    · rw [hx, hy]
  have hv : vOf x = vOf y := by
    apply hB.ψ_inj
    have h2 := h'
    rw [ιG, ιG, hc] at h2
    exact mul_left_cancel h2
  rw [← mk7_vOf x, ← mk7_vOf y, hv, hc]

theorem piHom_ι (x : V7) : hB.piHom (hB.ι x) = 1 :=
  (hB.piHom_eq_one_iff _).2 (hB.ιG_mem_E x)

theorem exists_ι_of_piHom (n : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    (hn : hB.piHom n = 1) : ∃ x, hB.ι x = n := by
  obtain ⟨v, h | h⟩ := hB.mem_E_iff.1 ((hB.piHom_eq_one_iff n).1 hn)
  · refine ⟨mk7 v 0, Subtype.ext ?_⟩
    rw [ι_coe, ιG, vOf_mk7, mk7_last, h]
    simp [tPow]
  · refine ⟨mk7 v 1, Subtype.ext ?_⟩
    rw [ι_coe, ιG, vOf_mk7, mk7_last, h]
    simp [tPow]

theorem conj_ι (n : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) (x : V7) :
    n * hB.ι x * n⁻¹ = hB.ι (rhoE ε (hB.piHom n) x) := by
  apply Subtype.ext
  rw [rhoE_apply, ← mk7_vOf x, actV7_mk7]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, ι_coe, ιG, vOf_mk7, mk7_last]
  rw [hB.piHom_apply, hB.piHom_apply]
  rcases zmod2_cases (x 6) with hx | hx <;> simp only [hx]
  · simp only [tPow, zero_ne_one, ite_false, one_mul, zero_add, one_smul]
    rw [hB.affF_eq_add n.2 (vOf x), add_comm (affF t ψ (↑n) 0), add_assoc,
      CharTwo.add_self_eq_zero, add_zero, hB.ψ_lin n.2]
  · simp only [tPow, ite_true, show (1 : ZMod 2) + 1 = 0 from rfl, zero_smul, add_zero]
    rw [hB.t_affF n.2]

end Branch

end CFSG.EvenSmallLie.OmegaEight.NSplit

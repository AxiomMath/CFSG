module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Wreathed

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped Pointwise commutatorElement

variable {X : Type} [Group X] [Finite X]
variable {G T S Q H : Subgroup X} {g y : X}

theorem V_inf_G (e : Elem47 G T S Q H g y) : rightConjugate T y ⊓ G = ⊥ := by
  rw [← rightConjugate_eq_of_mem (A := G) e.mem, ← rightConjugate_inf,
    e.hyp45.frame.inf_eq_bot, rightConjugate_bot]

theorem V_le_normalizer_Z (e : Elem47 G T S Q H g y) :
    rightConjugate T y ≤
      Subgroup.normalizer (((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) : Set X) := by
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    rw [e.V_centralizes_Z hv hz]
    simpa using hz
  · intro hz
    have h1 : v * z * v⁻¹ * v = v * z := by group
    have hcomm := e.V_centralizes_Z hv hz
    have : z = v * z * v⁻¹ := by
      calc z = v⁻¹ * (v * z * v⁻¹) * v := by group
        _ = v⁻¹ * v * (v * z * v⁻¹) := by rw [mul_assoc, ← hcomm, ← mul_assoc]
        _ = v * z * v⁻¹ := by group
    rw [this]
    exact hz

theorem VZ_inf_G (e : Elem47 G T S Q H g y) :
    (rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ⊓ G) ⊓ G = (T ⊔ rightConjugate T g) ⊓ G := by
  apply le_antisymm _ (le_inf le_sup_right inf_le_right)
  rintro x ⟨hx, hxG⟩
  have hx' : x ∈ (rightConjugate T y : Set X) * (((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) :
      Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ (V_le_normalizer_Z e)]
    exact hx
  obtain ⟨v, hv, z, hz, rfl⟩ := Set.mem_mul.mp hx'
  have hvG : v ∈ G := by simpa using G.mul_mem hxG (G.inv_mem hz.2)
  have hv1 : v ∈ rightConjugate T y ⊓ G := ⟨hv, hvG⟩
  rw [V_inf_G e, Subgroup.mem_bot] at hv1
  rw [hv1, one_mul]
  exact hz

theorem mem_Z_of_sq (e : Elem47 G T S Q H g y) {r : X}
    (hr : r ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) (hrG : r ∈ G) (hr2 : r ^ 2 = 1) :
    r ∈ (T ⊔ rightConjugate T g) ⊓ G := by
  rcases e.sq_eq_one_mem hr hr2 with h | h
  · exact ⟨h, hrG⟩
  · rw [← VZ_inf_G e]
    exact ⟨h, hrG⟩

theorem W_le_sup (e : Elem47 G T S Q H g y) :
    rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ≤ G ⊔ T :=
  e.A_le_S.trans e.hyp45.le_sup

theorem card_R (e : Elem47 G T S Q H g y) :
    Nat.card ((rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G : Subgroup X) =
      Nat.card T * Nat.card T := by
  have h1 := e.hyp45.frame.card_eq_mul (W_le_sup e) (le_sup_left.trans le_sup_right)
  rw [e.card_A] at h1
  have hpos : 0 < Nat.card T := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [← h1]
  ring

theorem card_S (e : Elem47 G T S Q H g y) :
    Nat.card S = 2 * Nat.card (rightConjugate T y ⊔ (T ⊔ rightConjugate T g) : Subgroup X) := by
  have h := Subgroup.relIndex_mul_card (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) S
  rw [inf_eq_left.mpr e.A_le_S, e.index_eq] at h
  exact h.symm

theorem card_SG (e : Elem47 G T S Q H g y) :
    Nat.card (S ⊓ G : Subgroup X) = 2 * (Nat.card T * Nat.card T) := by
  have h1 := e.hyp45.frame.card_eq_mul e.hyp45.le_sup e.hyp45.le_S
  rw [card_S e, e.card_A] at h1
  have hpos : 0 < Nat.card T := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [← h1]
  ring

theorem S_le_normalizer_W (e : Elem47 G T S Q H g y) :
    S ≤ Subgroup.normalizer
      ((rightConjugate T y ⊔ (T ⊔ rightConjugate T g) : Subgroup X) : Set X) := by
  rw [← e.weakClosure_eq]
  exact le_normalizer_relativeWeakClosure e.hyp45.frame e.hyp45.le_sup e.hyp45.le_S

theorem W_le_normalizer_M (e : Elem47 G T S Q H g y) :
    rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ≤
      Subgroup.normalizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X) := by
  rw [← e.normalizer_M]
  exact inf_le_right

theorem relIndex_W_S (e : Elem47 G T S Q H g y) :
    ((rightConjugate T y ⊔ (T ⊔ rightConjugate T g)).subgroupOf S).index = 2 := by
  rw [← Subgroup.relIndex]
  exact e.index_eq

theorem sq_mem_W (e : Elem47 G T S Q H g y) {x : X} (hx : x ∈ S) :
    x ^ 2 ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := by
  have h := Subgroup.sq_mem_of_index_two (relIndex_W_S e) (⟨x, hx⟩ : S)
  rw [Subgroup.mem_subgroupOf] at h
  simpa using h

theorem mul_inv_mem_W (e : Elem47 G T S Q H g y) {x x' : X} (hx : x ∈ S) (hx' : x' ∈ S)
    (hxW : x ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g))
    (hx'W : x' ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) :
    x' * x⁻¹ ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := by
  have h := (Subgroup.mul_mem_iff_of_index_two (relIndex_W_S e) (a := (⟨x', hx'⟩ : S))
    (b := (⟨x, hx⟩ : S)⁻¹))
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h
  apply h.mpr
  constructor
  · intro h1
    exact absurd h1 hx'W
  · intro h1
    exact absurd (by simpa using (Subgroup.inv_mem _ h1)) hxW

theorem conj_M_eq_VZ (e : Elem47 G T S Q H g y) {x : X} (hx : x ∈ S)
    (hxW : x ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) :
    rightConjugate (T ⊔ rightConjugate T g) x =
      rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ⊓ G := by
  rcases e.conj_M_eq (S_le_normalizer_W e hx) with h | h
  · exact absurd (e.mem_A_of_conj_eq hx h) hxW
  · exact h

theorem conj_VZ_eq_M (e : Elem47 G T S Q H g y) {x : X} (hx : x ∈ S)
    (hxW : x ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) :
    rightConjugate (rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ⊓ G) x =
      T ⊔ rightConjugate T g := by
  rw [← conj_M_eq_VZ e hx hxW, rightConjugate_mul, ← pow_two]
  exact (rightConjugate_eq_self_iff _ _).mpr (W_le_normalizer_M e (sq_mem_W e hx))

theorem commute_iff_of_not_mem (e : Elem47 G T S Q H g y) {x x' : X} (hx : x ∈ S)
    (hx' : x' ∈ S) (hxW : x ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g))
    (hx'W : x' ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) {z : X}
    (hz : z ∈ (T ⊔ rightConjugate T g) ⊓ G) : Commute z x ↔ Commute z x' := by
  have hw := mul_inv_mem_W e hx hx' hxW hx'W
  have hzw : Commute z (x' * x⁻¹) := e.Z_comm hz hw
  have hx'eq : x' = (x' * x⁻¹) * x := by group
  constructor
  · intro h
    rw [hx'eq]
    exact hzw.mul_right h
  · intro h
    have hx'' : x = (x' * x⁻¹)⁻¹ * x' := by group
    rw [hx'']
    exact hzw.inv_right.mul_right h

theorem inv_mul_conj_mem (e : Elem47 G T S Q H g y) {x w : X} (hx : x ∈ G) (hw : w ∈ G ⊔ T) :
    w⁻¹ * (x⁻¹ * w * x) ∈ G := by
  have hN : G ⊔ T ≤ Subgroup.normalizer (G : Set X) :=
    sup_le Subgroup.le_normalizer e.hyp45.frame.le_normalizer
  have h1 : w⁻¹ * x⁻¹ * w⁻¹⁻¹ ∈ G :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hN hw)) _).mp (G.inv_mem hx)
  have h2 := G.mul_mem h1 hx
  simpa [mul_assoc] using h2

theorem mem_M_iff (e : Elem47 G T S Q H g y) {m : X} (hm : m ∈ T ⊔ rightConjugate T g) :
    ∃ t ∈ T, ∃ z ∈ (T ⊔ rightConjugate T g) ⊓ G, m = t * z := by
  have hmGT : m ∈ G ⊔ T := e.hyp45.le_sup (e.M_le_S hm)
  obtain ⟨t, ht, h, hh, rfl⟩ := e.hyp45.frame.mem_sup_iff.mp hmGT
  refine ⟨t, ht, h, ⟨?_, hh⟩, rfl⟩
  have htM : t ∈ T ⊔ rightConjugate T g := Subgroup.mem_sup_left ht
  simpa using (T ⊔ rightConjugate T g).mul_mem ((T ⊔ rightConjugate T g).inv_mem htM) hm

theorem mem_VZ_iff (e : Elem47 G T S Q H g y) {n : X}
    (hn : n ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ⊓ G) :
    ∃ v ∈ rightConjugate T y, ∃ z ∈ (T ⊔ rightConjugate T g) ⊓ G, n = v * z := by
  have hn' : n ∈ (rightConjugate T y : Set X) *
      (((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ (V_le_normalizer_Z e)]
    exact hn
  obtain ⟨v, hv, z, hz, rfl⟩ := Set.mem_mul.mp hn'
  exact ⟨v, hv, z, hz, rfl⟩

theorem S_le_normalizer_Z (e : Elem47 G T S Q H g y) :
    S ≤ Subgroup.normalizer (((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) : Set X) := by
  intro x hx
  rw [← e.center_eq]
  have hxN := S_le_normalizer_W e hx
  rw [Subgroup.mem_normalizer_iff] at hxN ⊢
  intro c
  simp only [centerOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨hc, hcC⟩
    refine ⟨(hxN c).mp hc, fun w hw => ?_⟩
    have hw' : x⁻¹ * w * x ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) :=
      (hxN (x⁻¹ * w * x)).mpr (by simpa [mul_assoc] using hw)
    have h1 := hcC _ hw'
    calc w * (x * c * x⁻¹) = x * ((x⁻¹ * w * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * w * x)) * x⁻¹ := by rw [h1]
      _ = x * c * x⁻¹ * w := by group
  · rintro ⟨hc, hcC⟩
    refine ⟨(hxN c).mpr hc, fun w hw => ?_⟩
    have hw' : x * w * x⁻¹ ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := (hxN w).mp hw
    have h1 := hcC _ hw'
    calc w * c = x⁻¹ * ((x * w * x⁻¹) * (x * c * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * c * x⁻¹) * (x * w * x⁻¹)) * x := by rw [h1]
      _ = c * w := by group

theorem comm_mem_Z_of_mem_G (e : Elem47 G T S Q H g y) {x : X} (hxS : x ∈ S) (hxG : x ∈ G)
    (hxW : x ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) {r : X}
    (hrW : r ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) (hrG : r ∈ G) :
    r⁻¹ * (x⁻¹ * r * x) ∈ (T ⊔ rightConjugate T g) ⊓ G := by
  have hF := e.hyp45.frame
  set Z := (T ⊔ rightConjugate T g) ⊓ G with hZdef
  obtain ⟨v, hv, t, ht, z, hz, rfl⟩ := e.mem_A hrW
  have htM : t ∈ T ⊔ rightConjugate T g := Subgroup.mem_sup_left ht
  have hvVZ : v ∈ rightConjugate T y ⊔ Z := Subgroup.mem_sup_left hv
  have htx : x⁻¹ * t * x ∈ rightConjugate T y ⊔ Z := by
    rw [← conj_M_eq_VZ e hxS hxW]
    exact conj_mem_rightConjugate htM x
  have hvx : x⁻¹ * v * x ∈ T ⊔ rightConjugate T g := by
    rw [← conj_VZ_eq_M e hxS hxW]
    exact conj_mem_rightConjugate hvVZ x
  obtain ⟨v₁, hv₁, z₁, hz₁, htx'⟩ := mem_VZ_iff e htx
  obtain ⟨t₁, ht₁, z₂, hz₂, hvx'⟩ := mem_M_iff e hvx
  have hWGT := W_le_sup e
  have hvW : v ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := Subgroup.mem_sup_left hv
  have htW : t ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) :=
    Subgroup.mem_sup_right (Subgroup.mem_sup_left ht)
  have hc1 : t⁻¹ * (v₁ * z₁) ∈ G := by
    rw [← htx']
    exact inv_mul_conj_mem e hxG (hWGT htW)
  have hc2 : v⁻¹ * (t₁ * z₂) ∈ G := by
    rw [← hvx']
    exact inv_mul_conj_mem e hxG (hWGT hvW)
  have hc1' : t⁻¹ * v₁ ∈ G := by
    simpa [mul_assoc] using G.mul_mem hc1 (G.inv_mem hz₁.2)
  have hc2' : v⁻¹ * t₁ ∈ G := by
    simpa [mul_assoc] using G.mul_mem hc2 (G.inv_mem hz₂.2)
  have hvt : v * t ∈ G := by
    simpa [mul_assoc] using G.mul_mem hrG (G.inv_mem hz.2)
  have hv2 : v * v = 1 := by rw [← pow_two]; exact e.sq_V v hv
  have ht₁ : t₁ = t := by
    have hmem : t⁻¹ * t₁ ∈ T ⊓ G := by
      refine ⟨T.mul_mem (T.inv_mem ht) ht₁, ?_⟩
      have := G.mul_mem (G.inv_mem hvt) hc2'
      have heq : (v * t)⁻¹ * (v⁻¹ * t₁) = t⁻¹ * t₁ := by
        calc (v * t)⁻¹ * (v⁻¹ * t₁) = t⁻¹ * (v * v)⁻¹ * t₁ := by group
          _ = t⁻¹ * t₁ := by rw [hv2, inv_one, mul_one]
      rw [heq] at this
      exact this
    rw [hF.inf_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem.symm
  have hv₁ : v₁ = v := by
    have hmem : v * v₁ ∈ rightConjugate T y ⊓ G := by
      refine ⟨Subgroup.mul_mem _ hv hv₁, ?_⟩
      have := G.mul_mem hvt hc1'
      simpa [mul_assoc] using this
    rw [V_inf_G e, Subgroup.mem_bot] at hmem
    have : v₁ = v⁻¹ := eq_inv_of_mul_eq_one_right hmem
    rw [this, inv_eq_of_mul_eq_one_right hv2]
  rw [ht₁] at hvx'
  rw [hv₁] at htx'
  have hzx : x⁻¹ * z * x ∈ Z := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (S_le_normalizer_Z e hxS))
      z).mp hz
    rwa [inv_inv] at this
  have hcomm : t⁻¹ * (v⁻¹ * t * v) ∈ Z := e.comm_mem_Z hv ht
  have hconj : x⁻¹ * (v * t * z) * x =
      (x⁻¹ * v * x) * (x⁻¹ * t * x) * (x⁻¹ * z * x) := by group
  rw [hconj, hvx', htx']
  have hz₂v : z₂ * v = v * z₂ := e.Z_comm hz₂ hvW
  have hzc : z⁻¹ * (t⁻¹ * (v⁻¹ * t * v)) = (t⁻¹ * (v⁻¹ * t * v)) * z⁻¹ :=
    e.Z_comm (Z.inv_mem hz) (Subgroup.mem_sup_right hcomm.1)
  set z' := x⁻¹ * z * x with hz'def
  have key : (v * t * z)⁻¹ * (t * z₂ * (v * z₁) * z') =
      (t⁻¹ * (v⁻¹ * t * v)) * (z⁻¹ * (z₂ * (z₁ * z'))) := by
    calc (v * t * z)⁻¹ * (t * z₂ * (v * z₁) * z')
        = z⁻¹ * (t⁻¹ * (v⁻¹ * t * (z₂ * v)) * (z₁ * z')) := by group
      _ = z⁻¹ * (t⁻¹ * (v⁻¹ * t * v) * (z₂ * (z₁ * z'))) := by
          rw [hz₂v]; group
      _ = (z⁻¹ * (t⁻¹ * (v⁻¹ * t * v))) * (z₂ * (z₁ * z')) := by group
      _ = (t⁻¹ * (v⁻¹ * t * v)) * (z⁻¹ * (z₂ * (z₁ * z'))) := by
          rw [hzc]; group
  rw [key]
  exact Z.mul_mem hcomm (Z.mul_mem (Z.inv_mem hz) (Z.mul_mem hz₂ (Z.mul_mem hz₁ hzx)))

theorem inf_centralizer_eq_Z (e : Elem47 G T S Q H g y) {t : X} (ht : t ∈ T) (ht1 : t ≠ 1) :
    S ⊓ G ⊓ Subgroup.centralizer {t} = (T ⊔ rightConjugate T g) ⊓ G := by
  have hC := lemma_4_5_one e.hyp45 ht ht1
  rw [e.inf_eq] at hC
  rw [inf_right_comm, ← hC]

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight

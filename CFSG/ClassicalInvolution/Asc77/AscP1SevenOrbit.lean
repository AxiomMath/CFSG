module

public import CFSG.ClassicalInvolution.Asc77.AscL62Quat
public import CFSG.ClassicalInvolution.Asc77.ModOApi

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

namespace Thompson

variable {G : Type} [Group G]

theorem eq_of_mem_closure_pair {z j x : G} (hz : z * z = 1) (hj : j * j = 1) (hc : z * j = j * z)
    (hx : x ∈ Subgroup.closure ({z, j} : Set G)) : x = 1 ∨ x = z ∨ x = j ∨ x = z * j := by
  have e1 : z * (z * j) = j := by rw [← mul_assoc, hz, one_mul]
  have e2 : j * z = z * j := hc.symm
  have e3 : j * (z * j) = z := by rw [← mul_assoc, e2, mul_assoc, hj, mul_one]
  have e4 : (z * j) * z = j := by rw [mul_assoc, e2, ← mul_assoc, hz, one_mul]
  have e5 : (z * j) * j = z := by rw [mul_assoc, hj, mul_one]
  have e6 : (z * j) * (z * j) = 1 := by rw [mul_assoc, e3, hz]
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hji : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj
  have hzji : (z * j)⁻¹ = z * j := by rw [mul_inv_rev, hji, hzi, e2]
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · rw [hx]; simp
    · rw [hx]; simp
  | one => left; rfl
  | mul a b _ _ ha hb =>
    rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> rw [ha, hb] <;>
      simp [e1, e2, e3, e4, e5, e6, hz, hj]
  | inv a _ ha =>
    rcases ha with ha | ha | ha | ha <;> rw [ha] <;> simp [hzi, hji, hzji]

theorem conjSub_sup_le {A B C : Subgroup G} (g : G) (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ C)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ C) : conjSub g (A ⊔ B) ≤ C := by
  unfold conjSub
  rw [Subgroup.map_le_iff_le_comap]
  exact sup_le (fun a ha => hA a ha) (fun b hb => hB b hb)

theorem mem_normalizer_of_conjSub_le [Finite G] {X : Subgroup G} {g : G} (h : conjSub g X ≤ X) :
    g ∈ Subgroup.normalizer (X : Set G) :=
  mem_normalizer_iff_conjSub_eq.mpr
    (Subgroup.eq_of_le_of_card_ge h (by rw [AscL62.natCard_conjSub]))

theorem exists_mul_of_mem_sup_of_le_normalizer {Γ X P Q : Subgroup G}
    (hΓ : Γ ≤ Subgroup.normalizer (X : Set G))
    (hP : ∀ a ∈ P, ∃ w ∈ Γ, ∃ x ∈ X, a = w * x) (hQ : ∀ a ∈ Q, ∃ w ∈ Γ, ∃ x ∈ X, a = w * x) :
    ∀ a ∈ P ⊔ Q, ∃ w ∈ Γ, ∃ x ∈ X, a = w * x := by
  let S : Subgroup G :=
    { carrier := {a | ∃ w ∈ Γ, ∃ x ∈ X, a = w * x}
      one_mem' := ⟨1, Γ.one_mem, 1, X.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨w₁, hw₁, x₁, hx₁, rfl⟩ ⟨w₂, hw₂, x₂, hx₂, rfl⟩
        refine ⟨w₁ * w₂, Γ.mul_mem hw₁ hw₂, (w₂⁻¹ * x₁ * w₂) * x₂, X.mul_mem ?_ hx₂, by group⟩
        have := (Subgroup.mem_normalizer_iff.mp (hΓ (Γ.inv_mem hw₂)) x₁).mp hx₁
        simpa using this
      inv_mem' := by
        rintro _ ⟨w, hw, x, hx, rfl⟩
        refine ⟨w⁻¹, Γ.inv_mem hw, w * x⁻¹ * w⁻¹, ?_, by group⟩
        have := (Subgroup.mem_normalizer_iff.mp (hΓ hw) x⁻¹).mp (X.inv_mem hx)
        exact this }
  have hle : P ⊔ Q ≤ S := sup_le hP hQ
  exact fun a ha => hle ha

variable [Finite G] {K J : Subgroup G} {z j r t : G}

theorem exists_mem_closure_conj_eq (hz : IsUniqueInvolution K z) (hj : IsUniqueInvolution J j)
    (hzj : z ≠ j) (hcomm : z * j = j * z)
    (hKN : K ⊓ Subgroup.centralizer ({j} : Set G) ≤ Subgroup.normalizer (J : Set G))
    (hJN : J ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hr : r ∈ K) (ht : t ∈ J) (hrj : r * j * r⁻¹ = z * j) (htz : t * z * t⁻¹ = z * j)
    (hAE : ∃ g ∈ pairNormalizers K J z j, conjSub g K = J) :
    ∃ w ∈ Subgroup.closure ({r, t} : Set G), conjSub w K = J := by
  set A : Subgroup G := K ⊓ Subgroup.centralizer ({j} : Set G) with hA
  set B : Subgroup G := J ⊓ Subgroup.centralizer ({z} : Set G) with hB
  set X : Subgroup G := A ⊔ B with hX
  have hzz := hz.sq
  have hjj := hj.sq
  have hKz : ∀ k ∈ K, k * z * k⁻¹ = z := fun k hk => by
    have := hz.commute_of_mem hk
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have hJj : ∀ y ∈ J, y * j * y⁻¹ = j := fun y hy => by
    have := hj.commute_of_mem hy
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have hAj : ∀ a ∈ A, a * j * a⁻¹ = j := fun a ha => by
    have := Subgroup.mem_centralizer_singleton_iff.mp ha.2
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hBz : ∀ b ∈ B, b * z * b⁻¹ = z := fun b hb => by
    have := Subgroup.mem_centralizer_singleton_iff.mp hb.2
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hmemA : ∀ k ∈ K, k * j * k⁻¹ = j → k ∈ A := fun k hk h =>
    ⟨hk, Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc k * j = (k * j * k⁻¹) * k := by group
        _ = j * k := by rw [h])⟩
  have hmemB : ∀ y ∈ J, y * z * y⁻¹ = z → y ∈ B := fun y hy h =>
    ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc y * z = (y * z * y⁻¹) * y := by group
        _ = z * y := by rw [h])⟩
  have hrz : r * z * r⁻¹ = z := hKz r hr
  have hzr : r⁻¹ * z * r = z := by
    calc r⁻¹ * z * r = r⁻¹ * (r * z * r⁻¹) * r := by rw [hrz]
      _ = z := by group
  have hr' : r⁻¹ * j * r = z * j := by
    have h2 : j = z * (r⁻¹ * j * r) := by
      calc j = r⁻¹ * (r * j * r⁻¹) * r := by group
        _ = r⁻¹ * (z * j) * r := by rw [hrj]
        _ = (r⁻¹ * z * r) * (r⁻¹ * j * r) := by group
        _ = z * (r⁻¹ * j * r) := by rw [hzr]
    calc r⁻¹ * j * r = z * (z * (r⁻¹ * j * r)) := by
          rw [← mul_assoc z z (r⁻¹ * j * r), hzz, one_mul]
      _ = z * j := by rw [← h2]
  have htj : t * j * t⁻¹ = j := hJj t ht
  have hjt : t⁻¹ * j * t = j := by simpa using hJj t⁻¹ (J.inv_mem ht)
  have ht' : t⁻¹ * z * t = z * j := by
    have h2 : z = (t⁻¹ * z * t) * j := by
      calc z = t⁻¹ * (t * z * t⁻¹) * t := by group
        _ = t⁻¹ * (z * j) * t := by rw [htz]
        _ = (t⁻¹ * z * t) * (t⁻¹ * j * t) := by group
        _ = (t⁻¹ * z * t) * j := by rw [hjt]
    calc t⁻¹ * z * t = ((t⁻¹ * z * t) * j) * j := by
          rw [mul_assoc (t⁻¹ * z * t) j j, hjj, mul_one]
      _ = z * j := by rw [← h2]
  have hconjA : ∀ a ∈ A, r * a * r⁻¹ ∈ A := by
    intro a ha
    refine hmemA _ (K.mul_mem (K.mul_mem hr ha.1) (K.inv_mem hr)) ?_
    calc r * a * r⁻¹ * j * (r * a * r⁻¹)⁻¹ = r * a * (r⁻¹ * j * r) * a⁻¹ * r⁻¹ := by group
      _ = r * a * (z * j) * a⁻¹ * r⁻¹ := by rw [hr']
      _ = r * ((a * z * a⁻¹) * (a * j * a⁻¹)) * r⁻¹ := by group
      _ = r * (z * j) * r⁻¹ := by rw [hKz a ha.1, hAj a ha]
      _ = (r * z * r⁻¹) * (r * j * r⁻¹) := by group
      _ = z * (z * j) := by rw [hrz, hrj]
      _ = j := by rw [← mul_assoc, hzz, one_mul]
  have hconjB : ∀ b ∈ B, r * b * r⁻¹ ∈ X := by
    intro b hb
    have hbN : b ∈ Subgroup.normalizer (K : Set G) := hJN hb
    have hbj : b⁻¹ * j * b = j := by simpa using hJj b⁻¹ (J.inv_mem hb.1)
    have hcK : r * b * r⁻¹ * b⁻¹ ∈ K := by
      have h1 : b * r⁻¹ * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hbN r⁻¹).mp (K.inv_mem hr)
      have e : r * b * r⁻¹ * b⁻¹ = r * (b * r⁻¹ * b⁻¹) := by group
      rw [e]
      exact K.mul_mem hr h1
    have hcA : r * b * r⁻¹ * b⁻¹ ∈ A := hmemA _ hcK (by
      calc (r * b * r⁻¹ * b⁻¹) * j * (r * b * r⁻¹ * b⁻¹)⁻¹
          = r * b * r⁻¹ * (b⁻¹ * j * b) * r * b⁻¹ * r⁻¹ := by group
        _ = r * b * (r⁻¹ * j * r) * b⁻¹ * r⁻¹ := by rw [hbj]; group
        _ = r * b * (z * j) * b⁻¹ * r⁻¹ := by rw [hr']
        _ = r * ((b * z * b⁻¹) * (b * j * b⁻¹)) * r⁻¹ := by group
        _ = r * (z * j) * r⁻¹ := by rw [hBz b hb, hJj b hb.1]
        _ = (r * z * r⁻¹) * (r * j * r⁻¹) := by group
        _ = z * (z * j) := by rw [hrz, hrj]
        _ = j := by rw [← mul_assoc, hzz, one_mul])
    have e : r * b * r⁻¹ = (r * b * r⁻¹ * b⁻¹) * b := by group
    rw [e]
    exact X.mul_mem (Subgroup.mem_sup_left hcA) (Subgroup.mem_sup_right hb)
  have hrX : conjSub r X ≤ X :=
    conjSub_sup_le r (fun a ha => Subgroup.mem_sup_left (hconjA a ha)) hconjB
  have hconjB' : ∀ b ∈ B, t * b * t⁻¹ ∈ B := by
    intro b hb
    refine hmemB _ (J.mul_mem (J.mul_mem ht hb.1) (J.inv_mem ht)) ?_
    calc t * b * t⁻¹ * z * (t * b * t⁻¹)⁻¹ = t * b * (t⁻¹ * z * t) * b⁻¹ * t⁻¹ := by group
      _ = t * b * (z * j) * b⁻¹ * t⁻¹ := by rw [ht']
      _ = t * ((b * z * b⁻¹) * (b * j * b⁻¹)) * t⁻¹ := by group
      _ = t * (z * j) * t⁻¹ := by rw [hBz b hb, hJj b hb.1]
      _ = (t * z * t⁻¹) * (t * j * t⁻¹) := by group
      _ = (z * j) * j := by rw [htz, htj]
      _ = z := by rw [mul_assoc, hjj, mul_one]
  have hconjA' : ∀ a ∈ A, t * a * t⁻¹ ∈ X := by
    intro a ha
    have haN : a ∈ Subgroup.normalizer (J : Set G) := hKN ha
    have haz : a⁻¹ * z * a = z := by simpa using hKz a⁻¹ (K.inv_mem ha.1)
    have hcJ : t * a * t⁻¹ * a⁻¹ ∈ J := by
      have h1 : a * t⁻¹ * a⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp haN t⁻¹).mp (J.inv_mem ht)
      have e : t * a * t⁻¹ * a⁻¹ = t * (a * t⁻¹ * a⁻¹) := by group
      rw [e]
      exact J.mul_mem ht h1
    have hcB : t * a * t⁻¹ * a⁻¹ ∈ B := hmemB _ hcJ (by
      calc (t * a * t⁻¹ * a⁻¹) * z * (t * a * t⁻¹ * a⁻¹)⁻¹
          = t * a * t⁻¹ * (a⁻¹ * z * a) * t * a⁻¹ * t⁻¹ := by group
        _ = t * a * (t⁻¹ * z * t) * a⁻¹ * t⁻¹ := by rw [haz]; group
        _ = t * a * (z * j) * a⁻¹ * t⁻¹ := by rw [ht']
        _ = t * ((a * z * a⁻¹) * (a * j * a⁻¹)) * t⁻¹ := by group
        _ = t * (z * j) * t⁻¹ := by rw [hKz a ha.1, hAj a ha]
        _ = (t * z * t⁻¹) * (t * j * t⁻¹) := by group
        _ = (z * j) * j := by rw [htz, htj]
        _ = z := by rw [mul_assoc, hjj, mul_one])
    have e : t * a * t⁻¹ = (t * a * t⁻¹ * a⁻¹) * a := by group
    rw [e]
    exact X.mul_mem (Subgroup.mem_sup_right hcB) (Subgroup.mem_sup_left ha)
  have htX : conjSub t X ≤ X :=
    conjSub_sup_le t hconjA' (fun b hb => Subgroup.mem_sup_right (hconjB' b hb))
  set Γ : Subgroup G := Subgroup.closure ({r, t} : Set G) with hΓ
  have hrΓ : r ∈ Γ := Subgroup.subset_closure (by simp)
  have htΓ : t ∈ Γ := Subgroup.subset_closure (by simp)
  have hΓX : Γ ≤ Subgroup.normalizer (X : Set G) := by
    rw [hΓ, Subgroup.closure_le]
    intro y hy
    rcases hy with hy | hy
    · rw [hy]
      exact mem_normalizer_of_conjSub_le hrX
    · rw [Set.mem_singleton_iff.mp hy]
      exact mem_normalizer_of_conjSub_le htX
  have hrXi : ∀ x ∈ X, r⁻¹ * x * r ∈ X := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (hΓX (Γ.inv_mem hrΓ)) x).mp hx
    simpa using this
  have htXi : ∀ x ∈ X, t⁻¹ * x * t ∈ X := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (hΓX (Γ.inv_mem htΓ)) x).mp hx
    simpa using this
  have hK1 : ∀ k ∈ K ⊓ Subgroup.normalizer
      ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G),
      ∃ w ∈ Γ, ∃ x ∈ X, k = w * x := by
    intro k hk
    have hkj : k * j * k⁻¹ ∈ Subgroup.closure ({z, j} : Set G) :=
      (Subgroup.mem_normalizer_iff.mp hk.2 j).mp (Subgroup.subset_closure (by simp))
    rcases eq_of_mem_closure_pair hzz hjj hcomm hkj with h | h | h | h
    · exfalso
      apply hj.ne_one
      have := mul_inv_eq_one.mp h
      simpa using this
    · exfalso
      apply hzj
      have h1 : k * j * k⁻¹ = k * z * k⁻¹ := h.trans (hKz k hk.1).symm
      exact (mul_left_cancel (mul_right_cancel h1)).symm
    · exact ⟨1, Γ.one_mem, k, Subgroup.mem_sup_left (hmemA k hk.1 h), by simp⟩
    · have haA : k * r⁻¹ ∈ A := hmemA _ (K.mul_mem hk.1 (K.inv_mem hr)) (by
        calc k * r⁻¹ * j * (k * r⁻¹)⁻¹ = k * (r⁻¹ * j * r) * k⁻¹ := by group
          _ = k * (z * j) * k⁻¹ := by rw [hr']
          _ = (k * z * k⁻¹) * (k * j * k⁻¹) := by group
          _ = z * (z * j) := by rw [hKz k hk.1, h]
          _ = j := by rw [← mul_assoc, hzz, one_mul])
      refine ⟨r, hrΓ, r⁻¹ * (k * r⁻¹) * r, hrXi _ (Subgroup.mem_sup_left haA), by group⟩
  have hJ1 : ∀ y ∈ J ⊓ Subgroup.normalizer
      ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G),
      ∃ w ∈ Γ, ∃ x ∈ X, y = w * x := by
    intro y hy
    have hyz : y * z * y⁻¹ ∈ Subgroup.closure ({z, j} : Set G) :=
      (Subgroup.mem_normalizer_iff.mp hy.2 z).mp (Subgroup.subset_closure (by simp))
    rcases eq_of_mem_closure_pair hzz hjj hcomm hyz with h | h | h | h
    · exfalso
      apply hz.ne_one
      have := mul_inv_eq_one.mp h
      simpa using this
    · exact ⟨1, Γ.one_mem, y, Subgroup.mem_sup_right (hmemB y hy.1 h), by simp⟩
    · exfalso
      apply hzj
      have h1 : y * z * y⁻¹ = y * j * y⁻¹ := h.trans (hJj y hy.1).symm
      exact mul_left_cancel (mul_right_cancel h1)
    · have hbB : y * t⁻¹ ∈ B := hmemB _ (J.mul_mem hy.1 (J.inv_mem ht)) (by
        calc y * t⁻¹ * z * (y * t⁻¹)⁻¹ = y * (t⁻¹ * z * t) * y⁻¹ := by group
          _ = y * (z * j) * y⁻¹ := by rw [ht']
          _ = (y * z * y⁻¹) * (y * j * y⁻¹) := by group
          _ = (z * j) * j := by rw [h, hJj y hy.1]
          _ = z := by rw [mul_assoc, hjj, mul_one])
      refine ⟨t, htΓ, t⁻¹ * (y * t⁻¹) * t, htXi _ (Subgroup.mem_sup_right hbB), by group⟩
  have hY := exists_mul_of_mem_sup_of_le_normalizer hΓX hK1 hJ1
  have hXN : X ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (fun a ha => Subgroup.le_normalizer ha.1) hJN
  obtain ⟨g, hg, hgK⟩ := hAE
  obtain ⟨w, hw, x, hx, rfl⟩ := hY g hg
  have hxK : conjSub x K = K := mem_normalizer_iff_conjSub_eq.mp (hXN hx)
  rw [conjSub_mul, hxK] at hgK
  exact ⟨w, hw, hgK⟩

end Thompson

end CFSG.ClassicalInvolution.Asc77

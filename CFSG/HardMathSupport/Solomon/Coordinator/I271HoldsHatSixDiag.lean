module

public import CFSG.HardMathSupport.Solomon.Coordinator.C25ON
public import CFSG.SignalizerFunctorTheorem.ElementaryAbelian
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Family
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Struct
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance

section Algebra

variable {X : Type*} [Group X]

@[expose] def i271dFun (b x : X) : X := x * (b * x * b⁻¹) * (b * b * x * (b * b)⁻¹)

theorem i271_mul_shuffle (x y a b c d : X) (h1 : y * a = a * y) (h2 : y * c = c * y)
    (h3 : b * c = c * b) : x * y * (a * b) * (c * d) = (x * a * c) * (y * b * d) := by
  calc x * y * (a * b) * (c * d) = x * (y * a) * (b * c) * d := by group
    _ = x * (a * y) * (c * b) * d := by rw [h1, h3]
    _ = x * a * (y * c) * b * d := by group
    _ = x * a * (c * y) * b * d := by rw [h2]
    _ = (x * a * c) * (y * b * d) := by group

structure I271Comm (K : Subgroup X) (b : X) : Prop where
  c1 : ∀ x ∈ K, ∀ y ∈ K, x * (b * y * b⁻¹) = (b * y * b⁻¹) * x
  c2 : ∀ x ∈ K, ∀ y ∈ K, x * (b * b * y * (b * b)⁻¹) = (b * b * y * (b * b)⁻¹) * x

variable {K : Subgroup X} {b : X}

theorem I271Comm.c3 (h : I271Comm K b) {x y : X} (hx : x ∈ K) (hy : y ∈ K) :
    (b * x * b⁻¹) * (b * b * y * (b * b)⁻¹) = (b * b * y * (b * b)⁻¹) * (b * x * b⁻¹) := by
  have := h.c1 x hx y hy
  calc (b * x * b⁻¹) * (b * b * y * (b * b)⁻¹) = b * (x * (b * y * b⁻¹)) * b⁻¹ := by group
    _ = b * ((b * y * b⁻¹) * x) * b⁻¹ := by rw [this]
    _ = (b * b * y * (b * b)⁻¹) * (b * x * b⁻¹) := by group

theorem i271dFun_mul (h : I271Comm K b) {x y : X} (hx : x ∈ K) (hy : y ∈ K) :
    i271dFun b (x * y) = i271dFun b x * i271dFun b y := by
  unfold i271dFun
  have e1 : b * (x * y) * b⁻¹ = (b * x * b⁻¹) * (b * y * b⁻¹) := by group
  have e2 : b * b * (x * y) * (b * b)⁻¹ = (b * b * x * (b * b)⁻¹) * (b * b * y * (b * b)⁻¹) := by
    group
  rw [e1, e2]
  exact i271_mul_shuffle x y _ _ _ _ (h.c1 y hy x hx) (h.c2 y hy x hx) (h.c3 hy hx)

theorem i271dFun_one : i271dFun b (1 : X) = 1 := by
  simp [i271dFun]

theorem i271dFun_pow_three (h : I271Comm K b) {x : X} (hx : x ∈ K) :
    i271dFun b (x ^ 3) = i271dFun b x ^ 3 := by
  rw [pow_three, pow_three, i271dFun_mul h hx (K.mul_mem hx hx), i271dFun_mul h hx hx]

theorem i271dFun_conj_b (h : I271Comm K b) (hb3 : b ^ 3 = 1) {x : X} (hx : x ∈ K) :
    b * i271dFun b x * b⁻¹ = i271dFun b x := by
  have hbbb : b * b * b = 1 := by rw [← pow_three'] ; exact hb3
  have e : b * i271dFun b x * b⁻¹ =
      (b * x * b⁻¹) * (b * b * x * (b * b)⁻¹) * (b * b * b * x * (b * b * b)⁻¹) := by
    unfold i271dFun; group
  rw [hbbb] at e
  have h1 := h.c1 x hx x hx
  have h2 := h.c2 x hx x hx
  rw [e]
  unfold i271dFun
  simp only [inv_one, mul_one, one_mul]
  calc b * x * b⁻¹ * (b * b * x * (b * b)⁻¹) * x
      = (b * x * b⁻¹ * (b * b * x * (b * b)⁻¹)) * x := rfl
    _ = x * (b * x * b⁻¹) * (b * b * x * (b * b)⁻¹) := by
        rw [mul_assoc (b * x * b⁻¹), ← h2, ← mul_assoc, ← h1, mul_assoc]

theorem i271dFun_conj_of_comm {a : X} (hab : a * b = b * a) (x : X) :
    a * i271dFun b x * a⁻¹ = i271dFun b (a * x * a⁻¹) := by
  have hab2 : a * (b * b) = (b * b) * a := by
    calc a * (b * b) = (a * b) * b := by group
      _ = (b * a) * b := by rw [hab]
      _ = b * (a * b) := by group
      _ = b * (b * a) := by rw [hab]
      _ = (b * b) * a := by group
  have e1 : a * (b * x * b⁻¹) * a⁻¹ = b * (a * x * a⁻¹) * b⁻¹ := by
    calc a * (b * x * b⁻¹) * a⁻¹ = (a * b) * x * (a * b)⁻¹ := by group
      _ = (b * a) * x * (b * a)⁻¹ := by rw [hab]
      _ = b * (a * x * a⁻¹) * b⁻¹ := by group
  have e2 : a * (b * b * x * (b * b)⁻¹) * a⁻¹ = b * b * (a * x * a⁻¹) * (b * b)⁻¹ := by
    calc a * (b * b * x * (b * b)⁻¹) * a⁻¹ = (a * (b * b)) * x * (a * (b * b))⁻¹ := by group
      _ = ((b * b) * a) * x * ((b * b) * a)⁻¹ := by rw [hab2]
      _ = b * b * (a * x * a⁻¹) * (b * b)⁻¹ := by group
  unfold i271dFun
  calc a * (x * (b * x * b⁻¹) * (b * b * x * (b * b)⁻¹)) * a⁻¹
      = (a * x * a⁻¹) * (a * (b * x * b⁻¹) * a⁻¹) * (a * (b * b * x * (b * b)⁻¹) * a⁻¹) := by
        group
    _ = _ := by rw [e1, e2]

theorem i271dFun_action (h : I271Comm K b) {x : X} (hx : x ∈ K) {y : X} (hy : y ∈ K) :
    i271dFun b x * y * (i271dFun b x)⁻¹ = x * y * x⁻¹ := by
  have h1 := h.c1 y hy x hx
  have h2 := h.c2 y hy x hx
  have hc : y * ((b * x * b⁻¹) * (b * b * x * (b * b)⁻¹)) =
      ((b * x * b⁻¹) * (b * b * x * (b * b)⁻¹)) * y := by
    rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]
  unfold i271dFun
  calc x * (b * x * b⁻¹) * (b * b * x * (b * b)⁻¹) * y *
        (x * (b * x * b⁻¹) * (b * b * x * (b * b)⁻¹))⁻¹
      = x * (((b * x * b⁻¹) * (b * b * x * (b * b)⁻¹)) * y *
        ((b * x * b⁻¹) * (b * b * x * (b * b)⁻¹))⁻¹) * x⁻¹ := by group
    _ = x * y * x⁻¹ := by
        rw [← hc]
        group

end Algebra

section Diag

variable {X : Type} [Group X] [Finite X] {K B : Subgroup X} {b : X}

theorem i271h_conj_commute (hL : IsComponentOf K ⊤) {g : X} (hg : g ∈ B)
    (hgN : g ∉ Subgroup.normalizer (K : Set X)) :
    ∀ x ∈ K, ∀ y ∈ K, x * (g * y * g⁻¹) = (g * y * g⁻¹) * x := by
  have hgi : g⁻¹ ∈ B := B.inv_mem hg
  have h := i112_conj_eq_or_commute (B := B) hL (i112_self_mem_orbit) (i112_gLBConj_mem_orbit hgi)
  rcases h with h | h
  · exfalso
    apply hgN
    have : g⁻¹ ∈ Subgroup.normalizer (K : Set X) := mem_normalizer_iff_gLBConj_eq.2 h.symm
    simpa using Subgroup.inv_mem _ this
  · intro x hx y hy
    exact h x hx (g * y * g⁻¹) (by rw [mem_gLBConj]; simpa [mul_assoc] using hy)

theorem i271h_sq_not_mem {b : X} (hb3 : b ^ 3 = 1) (hbN : b ∉ Subgroup.normalizer (K : Set X)) :
    b * b ∉ Subgroup.normalizer (K : Set X) := by
  intro h
  apply hbN
  have : (b * b) * (b * b) = b := by
    have : b * b * b = 1 := by rw [← pow_three']; exact hb3
    calc b * b * (b * b) = (b * b * b) * b := by group
      _ = b := by rw [this, one_mul]
  rw [← this]
  exact Subgroup.mul_mem _ h h

theorem i271h_comm_of_not_mem (hL : IsComponentOf K ⊤) (hb : b ∈ B) (hb3 : b ^ 3 = 1)
    (hbN : b ∉ Subgroup.normalizer (K : Set X)) : I271Comm K b :=
  ⟨i271h_conj_commute hL hb hbN,
    i271h_conj_commute hL (B.mul_mem hb hb) (i271h_sq_not_mem hb3 hbN)⟩

theorem i271h_B_le_sup (hBel : IsElemAbelian 3 B) (hb : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (K : Set X))
    (hidx : (Subgroup.normalizer (K : Set X)).relIndex B = 3) :
    B ≤ Subgroup.zpowers b ⊔ (B ⊓ Subgroup.normalizer (K : Set X)) := by
  have hb3 : b ^ 3 = 1 := hBel.2 b hb
  have hb1 : b ≠ 1 := fun h => hbN (h ▸ Subgroup.one_mem _)
  have : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
  have hzB : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.2 hb
  have hAB : B ⊓ Subgroup.normalizer (K : Set X) ≤ B := inf_le_left
  have hz3 : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have hdisj : Subgroup.zpowers b ⊓ (B ⊓ Subgroup.normalizer (K : Set X)) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    by_contra hy1
    have hy1' : y ≠ 1 := fun h => hy1 (h ▸ Subgroup.one_mem _)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy.1
    have hy3 : (b ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
    have hyo : orderOf (b ^ k) = 3 := orderOf_eq_prime hy3 hy1'
    have hle : Subgroup.zpowers (b ^ k) ≤ Subgroup.zpowers b := Subgroup.zpowers_le.2 hy.1
    have heq : Subgroup.zpowers (b ^ k) = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge hle
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hyo, orderOf_eq_prime hb3 hb1])
    have hbmem : b ∈ B ⊓ Subgroup.normalizer (K : Set X) :=
      Subgroup.zpowers_le.2 hy.2 (heq ▸ Subgroup.mem_zpowers b)
    exact hbN hbmem.2
  have hcardB := Subgroup.relIndex_mul_card (H := Subgroup.normalizer (K : Set X)) (K := B)
  rw [hidx, inf_comm] at hcardB
  have hM := SignalizerFunctorTheorem.card_sup_of_le_elemAbelian hBel hzB hAB hdisj
  have hle : Subgroup.zpowers b ⊔ (B ⊓ Subgroup.normalizer (K : Set X)) ≤ B := sup_le hzB hAB
  have heq : Subgroup.zpowers b ⊔ (B ⊓ Subgroup.normalizer (K : Set X)) = B :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hM, hz3, hcardB])
  exact heq.ge

theorem i271h_diag (hL : IsComponentOf K ⊤) (hBel : IsElemAbelian 3 B) (hmax : IsSCp 3 ⊤ B)
    (hb : b ∈ B) (hbN : b ∉ Subgroup.normalizer (K : Set X))
    (hidx : (Subgroup.normalizer (K : Set X)).relIndex B = 3)
    (hz : ∀ z ∈ centreIn K, i271dFun b z = 1)
    {x : X} (hx : x ∈ K) (hx3 : x ^ 3 = 1)
    (hfix : ∀ a ∈ B ⊓ Subgroup.normalizer (K : Set X), a * x * a⁻¹ * x⁻¹ ∈ centreIn K) :
    ∃ y ∈ B ⊓ Subgroup.normalizer (K : Set X), ∀ k ∈ K, y * k * y⁻¹ = x * k * x⁻¹ := by
  have hb3 : b ^ 3 = 1 := hBel.2 b hb
  have hcomm : I271Comm K b := i271h_comm_of_not_mem hL hb hb3 hbN
  set d : X := i271dFun b x with hd
  have hd1 : b * d * b⁻¹ = d := i271dFun_conj_b hcomm hb3 hx
  have hdA : ∀ a ∈ B ⊓ Subgroup.normalizer (K : Set X), a * d * a⁻¹ = d := by
    intro a ha
    have hab : a * b = b * a := CFSG.Open.IsElemAbelian.comm hBel ha.1 hb
    have hax : a * x * a⁻¹ ∈ K := by
      have := (Subgroup.mem_normalizer_iff.1 ha.2 x).1 hx
      exact this
    rw [hd, i271dFun_conj_of_comm hab x]
    obtain ⟨hzK, -⟩ := mem_centreIn.1 (hfix a ha)
    have hzx : a * x * a⁻¹ = (a * x * a⁻¹ * x⁻¹) * x := by group
    rw [hzx, i271dFun_mul hcomm hzK hx, hz _ (hfix a ha), one_mul]
  have hBle := i271h_B_le_sup hBel hb hbN hidx
  have hCle : Subgroup.zpowers b ⊔ (B ⊓ Subgroup.normalizer (K : Set X)) ≤
      Subgroup.centralizer ({d} : Set X) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) ?_
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have := hd1
      calc b * d = (b * d * b⁻¹) * b := by group
        _ = d * b := by rw [this]
    · intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hdA a ha
      calc a * d = (a * d * a⁻¹) * a := by group
        _ = d * a := by rw [this]
  have hdB : ∀ β ∈ B, β * d = d * β := fun β hβ =>
    Subgroup.mem_centralizer_singleton_iff.1 (hCle (hBle hβ))
  have hd3 : d ^ 3 = 1 := by
    rw [hd, ← i271dFun_pow_three hcomm hx, hx3, i271dFun_one]
  have hdC : d ∈ Subgroup.centralizer (B : Set X) :=
    Subgroup.mem_centralizer_iff.2 fun β hβ => hdB β hβ
  have hE := c25_isElemAbelian_sup_zpowers hBel hd3 hdC
  have hEB : Subgroup.zpowers d ⊔ B = B := hmax.2.2 _ le_top hE le_sup_right
  have hdBm : d ∈ B := by
    rw [← hEB]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers d)
  have hact : ∀ k ∈ K, d * k * d⁻¹ = x * k * x⁻¹ := fun k hk =>
    i271dFun_action hcomm hx hk
  have hdN : d ∈ Subgroup.normalizer (K : Set X) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    rw [hact n hn]
    exact K.mul_mem (K.mul_mem hx hn) (K.inv_mem hx)
  exact ⟨d, ⟨hdBm, hdN⟩, hact⟩

end Diag

end CFSG.HardMathSupport.Solomon.Coordinator

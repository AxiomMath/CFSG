module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Core
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Squares
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.QuasithinUnique.C5

open CFSG.Quasithin Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def NoCommonNormal (R H M₀ : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≤ R → X ≠ ⊥ → H ≤ normalizer (X : Set G) → M₀ ≤ normalizer (X : Set G) →
    False

theorem eq_bot_of_noCommonNormal {R H M₀ K X : Subgroup G} {x : G} (hC : NoCommonNormal R H M₀)
    (hXR : X ≤ R) (hXK : X ≤ centralizer (K : Set G)) (hRX : R ≤ normalizer (X : Set G))
    (hxX : x ∈ normalizer (X : Set G)) (hHKR : H ≤ K ⊔ R) (hM₀ : M₀ ≤ R ⊔ Subgroup.zpowers x) :
    X = ⊥ := by
  by_contra hne
  refine hC X hXR hne ?_ ?_
  · refine hHKR.trans (sup_le ?_ hRX)
    exact (Subgroup.le_centralizer_iff.mp hXK).trans (Subgroup.centralizer_le_normalizer _)
  · exact hM₀.trans (sup_le hRX (Subgroup.zpowers_le.mpr hxX))

namespace Rank1

variable {B Q U W : Subgroup G} {q : ℕ} (h : Rank1 B Q U W q)
include h

theorem conj_sqSub [Finite G] (hU2 : ∀ u ∈ U, u ^ 2 = 1) {D : Subgroup G} (hD : Q = U ⊔ D)
    (hDc : ∀ u ∈ U, ∀ a ∈ D, u * a = a * u) {x : G} (hx : x ∈ normalizer (B : Set G))
    (hx1 : ¬ conjSubgroup U x ≤ Q) (hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q) :
    conjSubgroup (sqSub D) x = sqSub D := by
  have hQ : sqSub D = sqSub Q := by rw [hD, sqSub_sup_eq hU2 hDc]
  have e1 : sqSub Q = sqSub (Q ⊓ conjSubgroup Q x) := by
    conv_lhs => rw [← (h.relIndex_inf_conj hx hx1).2]
    exact sqSub_sup_eq hU2 fun u hu a ha => h.Q_cent a ha.1 u hu
  have e2 : sqSub Q = sqSub (Q ⊓ conjSubgroup Q x⁻¹) := by
    conv_lhs => rw [← (h.relIndex_inf_conj (inv_mem hx) hx2).2]
    exact sqSub_sup_eq hU2 fun u hu a ha => h.Q_cent a ha.1 u hu
  calc conjSubgroup (sqSub D) x = conjSubgroup (sqSub (Q ⊓ conjSubgroup Q x⁻¹)) x := by
        rw [hQ, e2]
    _ = sqSub (conjSubgroup (Q ⊓ conjSubgroup Q x⁻¹) x) := conjSubgroup_sqSub _ _
    _ = sqSub (Q ⊓ conjSubgroup Q x) := by
        rw [conjSubgroup_inf, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one,
          inf_comm]
    _ = sqSub D := by rw [← e1, hQ]

theorem sqSub_centralizer_eq_bot [Finite G] {R H M₀ K : Subgroup G} {x : G}
    (hC : NoCommonNormal R H M₀) (hBR : B ≤ R) (hRQ : R ≤ normalizer (Q : Set G))
    (hRK : R ≤ normalizer (K : Set G))
    (hHKR : H ≤ K ⊔ R) (hM₀ : M₀ ≤ R ⊔ Subgroup.zpowers x) (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hUK : U ≤ K) (hx : x ∈ normalizer (B : Set G)) (hx1 : ¬ conjSubgroup U x ≤ Q)
    (hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q)
    (hD : Q = U ⊔ (Q ⊓ centralizer (K : Set G))) :
    sqSub (Q ⊓ centralizer (K : Set G)) = ⊥ := by
  have hDc : ∀ u ∈ U, ∀ a ∈ Q ⊓ centralizer (K : Set G), u * a = a * u := fun u hu a ha =>
    Subgroup.mem_centralizer_iff.mp ha.2 u (hUK hu)
  have hDR : Q ⊓ centralizer (K : Set G) ≤ R := inf_le_left.trans (h.Q_le_B.trans hBR)
  have hRD : R ≤ normalizer ((Q ⊓ centralizer (K : Set G) : Subgroup G) : Set G) := fun r hr =>
    mem_normalizer_inf (hRQ hr) (mem_normalizer_centralizer (hRK hr))
  refine eq_bot_of_noCommonNormal hC (sqSub_le_self.trans hDR)
    (sqSub_le_self.trans inf_le_right) (fun r hr => ?_) ?_ hHKR hM₀
  · exact conjSubgroup_eq_iff_mem_normalizer.mp (conjSubgroup_sqSub_of_mem_normalizer (hRD hr))
  · exact conjSubgroup_eq_iff_mem_normalizer.mp (h.conj_sqSub hU2 hD hDc hx hx1 hx2)

theorem inf_conj_centralizer_eq_bot {R H M₀ K : Subgroup G} {x : G}
    (hC : NoCommonNormal R H M₀) (hBR : B ≤ R) (hRQ : R ≤ normalizer (Q : Set G))
    (hRK : R ≤ normalizer (K : Set G)) (hxR : x ∈ normalizer (R : Set G)) (hxx : x * x ∈ R)
    (hHKR : H ≤ K ⊔ R) (hM₀ : M₀ ≤ R ⊔ Subgroup.zpowers x) :
    (Q ⊓ centralizer (K : Set G)) ⊓ conjSubgroup (Q ⊓ centralizer (K : Set G)) x = ⊥ := by
  set D := Q ⊓ centralizer (K : Set G) with hDdef
  have hDR : D ≤ R := inf_le_left.trans (h.Q_le_B.trans hBR)
  have hRD : R ≤ normalizer (D : Set G) := fun r hr =>
    mem_normalizer_inf (hRQ hr) (mem_normalizer_centralizer (hRK hr))
  have hRDx : R ≤ normalizer ((conjSubgroup D x : Subgroup G) : Set G) := by
    intro r hr
    rw [← conjSubgroup_normalizer, mem_conjSubgroup_iff]
    exact hRD ((Subgroup.mem_normalizer_iff.mp hxR r).mp hr)
  have hxxD : x * x ∈ normalizer (D : Set G) := hRD hxx
  refine eq_bot_of_noCommonNormal hC (inf_le_left.trans hDR)
    (inf_le_left.trans inf_le_right) (fun r hr => mem_normalizer_inf (hRD hr) (hRDx hr)) ?_ hHKR
    hM₀
  rw [← conjSubgroup_eq_iff_mem_normalizer, conjSubgroup_inf, conjSubgroup_conjSubgroup,
    conjSubgroup_eq_self hxxD, inf_comm]

end Rank1

theorem commute_of_central_mul {c c₂ d d₂ : G} (hdc₂ : d * c₂ = c₂ * d) (hd₂c : d₂ * c = c * d₂)
    (hdd : d * d₂ = d₂ * d) (h : c * d * (c₂ * d₂) = c₂ * d₂ * (c * d)) : c * c₂ = c₂ * c := by
  have e1 : c * d * (c₂ * d₂) = c * c₂ * (d * d₂) := by
    calc c * d * (c₂ * d₂) = c * (d * c₂) * d₂ := by simp [mul_assoc]
      _ = c * (c₂ * d) * d₂ := by rw [hdc₂]
      _ = c * c₂ * (d * d₂) := by simp [mul_assoc]
  have e2 : c₂ * d₂ * (c * d) = c₂ * c * (d * d₂) := by
    calc c₂ * d₂ * (c * d) = c₂ * (d₂ * c) * d := by simp [mul_assoc]
      _ = c₂ * (c * d₂) * d := by rw [hd₂c]
      _ = c₂ * c * (d₂ * d) := by simp [mul_assoc]
      _ = c₂ * c * (d * d₂) := by rw [hdd]
  rw [e1, e2] at h
  exact mul_right_cancel h

namespace Rank1

variable {B Q U W : Subgroup G} {q : ℕ} (h : Rank1 B Q U W q)
include h

theorem exists_mem_B_not_mem_Q [Finite G] (hq2 : 2 ≤ q) : ∃ y ∈ B, y ∉ Q := by
  by_contra hcon
  push Not at hcon
  have : B ≤ Q := fun y hy => hcon y hy
  have h1 : Q.relIndex B = 1 := Subgroup.relIndex_eq_one.mpr this
  rw [h.idx_Q] at h1
  omega

variable {D : Subgroup G} {x : G}

theorem D_central [Finite G] (hx : x ∈ normalizer (B : Set G))
    (hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q) (hD : Q = U ⊔ D) (hDc : ∀ u ∈ U, ∀ a ∈ D, u * a = a * u)
    (hD2 : ElemAb2 D) (hDx : D ≤ conjSubgroup Q x) :
    ∀ d ∈ D, ∀ b ∈ B, d * b = b * d := by
  intro d hd b hb
  have hdU : U ≤ centralizer ({d} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hDc u hu d hd)
  have hdD : D ≤ centralizer ({d} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD2.1 a ha d hd)
  have hdQ : Q ≤ centralizer ({d} : Set G) := hD ▸ sup_le hdU hdD
  have hdUx : conjSubgroup U x ≤ centralizer ({d} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (by
        have := hDx hd
        rw [h.conj_Q_eq hx] at this
        exact this.2) y hy)
  have hdB : B ≤ centralizer ({d} : Set G) := (h.sup_Q_conj hx hx2) ▸ sup_le hdUx hdQ
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hdB hb)).symm

theorem D_inf_U_le_W [Finite G] (hq2 : 2 ≤ q)
    (hDB : ∀ d ∈ D, ∀ b ∈ B, d * b = b * d) : D ⊓ U ≤ W := by
  obtain ⟨y, hyB, hyQ⟩ := h.exists_mem_B_not_mem_Q hq2
  intro w hw
  exact (h.cent_y y hyB hyQ w hw.2).mpr (hDB w hw.1 y hyB)

theorem W_le_conj [Finite G] (hx : x ∈ normalizer (B : Set G)) (hx1 : ¬ conjSubgroup U x ≤ Q)
    (hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q) : W ≤ conjSubgroup U x := by
  rw [← (h.commutator_conj hx hx1 hx2).2]; exact inf_le_right

theorem D_inf_conj [Finite G] (hq2 : 2 ≤ q) (hx : x ∈ normalizer (B : Set G))
    (hx1 : ¬ conjSubgroup U x ≤ Q) (hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q) (hD : Q = U ⊔ D)
    (hDB : ∀ d ∈ D, ∀ b ∈ B, d * b = b * d) : D ⊓ conjSubgroup U x = D ⊓ U := by
  refine le_antisymm ?_ ?_
  · intro y hy
    have hyQ : y ∈ Q := hD ▸ Subgroup.mem_sup_right hy.1
    have : y ∈ conjSubgroup U x ⊓ Q := ⟨hy.2, hyQ⟩
    rw [h.inf_Q_conj hx hx2, h.conj_W hx hx1 hx2] at this
    exact ⟨hy.1, h.W_le_U this⟩
  · intro y hy
    exact ⟨hy.1, h.W_le_conj hx hx1 hx2 (h.D_inf_U_le_W hq2 hDB hy)⟩

theorem card_D_sup_conj [Finite G] (hq2 : 2 ≤ q) (hx : x ∈ normalizer (B : Set G))
    (hx1 : ¬ conjSubgroup U x ≤ Q) (hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q) (hD : Q = U ⊔ D)
    (hDc : ∀ u ∈ U, ∀ a ∈ D, u * a = a * u)
    (hDB : ∀ d ∈ D, ∀ b ∈ B, d * b = b * d) :
    Nat.card ↥(D ⊔ conjSubgroup U x) = Nat.card ↥Q := by
  have hDN : D ≤ normalizer ((conjSubgroup U x : Subgroup G) : Set G) :=
    le_normalizer_of_commute fun d hd y hy => by
      have := hDB d hd y (h.conj_le_B hx hy)
      exact this
  have hUN : U ≤ normalizer (D : Set G) := le_normalizer_of_commute hDc
  have e1 := card_sup_mul_card_inf_of_le_normalizer hDN
  have e2 := card_sup_mul_card_inf_of_le_normalizer hUN
  rw [h.D_inf_conj hq2 hx hx1 hx2 hD hDB, card_conjSubgroup] at e1
  rw [inf_comm] at e2
  have hpos : 0 < Nat.card ↥(D ⊓ U) := Nat.card_pos
  rw [← hD] at e2
  have : Nat.card ↥(D ⊔ conjSubgroup U x) * Nat.card ↥(D ⊓ U) = Nat.card ↥Q * Nat.card ↥(D ⊓ U) := by
    rw [e1, mul_comm (Nat.card ↥D), e2]
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem mem_B_decomp [Finite G] (hx : x ∈ normalizer (B : Set G))
    (hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q) (hD : Q = U ⊔ D)
    (hDc : ∀ u ∈ U, ∀ a ∈ D, u * a = a * u) {a : G} (ha : a ∈ B) :
    ∃ u' ∈ conjSubgroup U x, ∃ u₁ ∈ U, ∃ d ∈ D, a = u' * (u₁ * d) := by
  have hUxN : conjSubgroup U x ≤ normalizer (Q : Set G) := (h.conj_le_B hx).trans h.B_le_normQ
  have ha' : a ∈ conjSubgroup U x ⊔ Q := (h.sup_Q_conj hx hx2).symm ▸ ha
  obtain ⟨u', hu', q₀, hq₀, rfl⟩ := mem_sup_of_le_normalizer hUxN ha'
  rw [hD] at hq₀
  obtain ⟨u₁, hu₁, d, hd, rfl⟩ := mem_sup_of_commute hDc hq₀
  exact ⟨u', hu', u₁, hu₁, d, hd, rfl⟩

theorem mem_sup_of_sq_eq_one [Finite G] (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hx : x ∈ normalizer (B : Set G))
    (hx1 : ¬ conjSubgroup U x ≤ Q) (hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q) (hD : Q = U ⊔ D)
    (hDc : ∀ u ∈ U, ∀ a ∈ D, u * a = a * u) (hD2 : ElemAb2 D)
    (hDB : ∀ d ∈ D, ∀ b ∈ B, d * b = b * d) {a : G} (haB : a ∈ B) (haQ : a ∉ Q)
    (ha2 : a ^ 2 = 1) : a ∈ D ⊔ conjSubgroup U x := by
  obtain ⟨u', hu', u₁, hu₁, d, hd, rfl⟩ := h.mem_B_decomp hx hx2 hD hDc haB
  have hu'B : u' ∈ B := h.conj_le_B hx hu'
  have hu₁B : u₁ ∈ B := h.U_le_B hu₁
  have hdQ : d ∈ Q := hD ▸ Subgroup.mem_sup_right hd
  have hu'Q : u' ∉ Q := by
    intro hq
    exact haQ (Q.mul_mem hq (Q.mul_mem (h.U_le_Q hu₁) hdQ))
  have hu'2 : u' ^ 2 = 1 := ((ElemAb2.conjSubgroup ⟨h.U_comm, hU2⟩ x)).2 u' hu'
  have hu₁2 := hU2 u₁ hu₁
  have hc : (u' * u₁) * d = d * (u' * u₁) := (hDB d hd (u' * u₁) (B.mul_mem hu'B hu₁B)).symm
  have h1 : (u' * u₁) ^ 2 = 1 := by
    have e : (u' * (u₁ * d)) ^ 2 = (u' * u₁) ^ 2 * d ^ 2 := by
      rw [← mul_assoc]
      exact (Commute.mul_pow hc 2)
    rw [e, hD2.2 d hd, mul_one] at ha2
    exact ha2
  have h2 : u₁ * u' = u' * u₁ := by
    have h3 : u' * u₁ = (u' * u₁)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_two]; exact h1
    have h4 : u₁⁻¹ = u₁ := by rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact hu₁2
    have h5 : u'⁻¹ = u' := by rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact hu'2
    rw [mul_inv_rev, h4, h5] at h3
    exact h3.symm
  have hW : u₁ ∈ W := (h.cent_y u' hu'B hu'Q u₁ hu₁).mpr h2
  have hWx := h.W_le_conj hx hx1 hx2 hW
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hu')
    (Subgroup.mul_mem _ (Subgroup.mem_sup_right hWx) (Subgroup.mem_sup_left hd))

theorem mem_sup_of_commute_B [Finite G] (hx : x ∈ normalizer (B : Set G))
    (hx1 : ¬ conjSubgroup U x ≤ Q) (hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q) (hD : Q = U ⊔ D)
    (hDc : ∀ u ∈ U, ∀ a ∈ D, u * a = a * u) (hD2 : ElemAb2 D)
    (hDB : ∀ d ∈ D, ∀ b ∈ B, d * b = b * d) {a b : G} (haB : a ∈ B) (haQ : a ∉ Q) (hbQ : b ∈ Q)
    (hab : a * b = b * a) : b ∈ D ⊔ conjSubgroup U x := by
  obtain ⟨u', hu', u₁, hu₁, d, hd, rfl⟩ := h.mem_B_decomp hx hx2 hD hDc haB
  have hbQ' := hbQ
  rw [hD] at hbQ'
  obtain ⟨u₂, hu₂, d₂, hd₂, rfl⟩ := mem_sup_of_commute hDc hbQ'
  have hu'B : u' ∈ B := h.conj_le_B hx hu'
  have hu₁B : u₁ ∈ B := h.U_le_B hu₁
  have hu₂B : u₂ ∈ B := h.U_le_B hu₂
  have hdQ : d ∈ Q := hD ▸ Subgroup.mem_sup_right hd
  have hd₂Q : d₂ ∈ Q := hD ▸ Subgroup.mem_sup_right hd₂
  have hu'Q : u' ∉ Q := by
    intro hq
    exact haQ (Q.mul_mem hq (Q.mul_mem (h.U_le_Q hu₁) hdQ))
  have hcc : (u' * u₁) * u₂ = u₂ * (u' * u₁) := by
    refine commute_of_central_mul (c := u' * u₁) (c₂ := u₂) (d := d) (d₂ := d₂) ?_ ?_ ?_ ?_
    · exact hDB d hd u₂ hu₂B
    · exact hDB d₂ hd₂ (u' * u₁) (B.mul_mem hu'B hu₁B)
    · exact hD2.1 d hd d₂ hd₂
    · simpa [mul_assoc] using hab
  have hU12 : u₁ * u₂ = u₂ * u₁ := h.U_comm u₁ hu₁ u₂ hu₂
  have h3 : u₂ * u' = u' * u₂ := by
    have : u' * (u₂ * u₁) = u₂ * u' * u₁ := by
      calc u' * (u₂ * u₁) = u' * (u₁ * u₂) := by rw [hU12]
        _ = u' * u₁ * u₂ := by rw [mul_assoc]
        _ = u₂ * (u' * u₁) := hcc
        _ = u₂ * u' * u₁ := by rw [mul_assoc]
    have h4 : u' * u₂ * u₁ = u₂ * u' * u₁ := by rw [mul_assoc]; exact this
    exact (mul_right_cancel h4).symm
  have hW : u₂ ∈ W := (h.cent_y u' hu'B hu'Q u₂ hu₂).mpr h3
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (h.W_le_conj hx hx1 hx2 hW))
    (Subgroup.mem_sup_left hd₂)

theorem elemAb_le [Finite G] (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hx : x ∈ normalizer (B : Set G))
    (hx1 : ¬ conjSubgroup U x ≤ Q) (hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q) (hD : Q = U ⊔ D)
    (hDc : ∀ u ∈ U, ∀ a ∈ D, u * a = a * u) (hD2 : ElemAb2 D)
    (hDB : ∀ d ∈ D, ∀ b ∈ B, d * b = b * d) {A : Subgroup G} (hA : ElemAb2 A) (hAB : A ≤ B) :
    A ≤ Q ∨ A ≤ D ⊔ conjSubgroup U x := by
  by_cases hAQ : A ≤ Q
  · exact Or.inl hAQ
  right
  obtain ⟨a, haA, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
  intro b hb
  by_cases hbQ : b ∈ Q
  · exact h.mem_sup_of_commute_B hx hx1 hx2 hD hDc hD2 hDB (hAB haA) haQ hbQ (hA.1 a haA b hb)
  · exact h.mem_sup_of_sq_eq_one hU2 hx hx1 hx2 hD hDc hD2 hDB (hAB hb) hbQ (hA.2 b hb)

theorem A_R_structure [Finite G] {R : Subgroup G} (hBR : B ≤ R)
    (hA : ∀ A, IsMaxElemAbelian R A → A ≤ B) (hq2 : 2 ≤ q) (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hx : x ∈ normalizer (B : Set G)) (hx1 : ¬ conjSubgroup U x ≤ Q)
    (hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q) (hD : Q = U ⊔ D) (hDc : ∀ u ∈ U, ∀ a ∈ D, u * a = a * u)
    (hD2 : ElemAb2 D) (hDx : D ≤ conjSubgroup Q x) :
    IsMaxElemAbelian R Q ∧ IsMaxElemAbelian R (conjSubgroup Q x) ∧
      conjSubgroup Q x = D ⊔ conjSubgroup U x ∧
      (∀ A, IsMaxElemAbelian R A ↔ A = Q ∨ A = conjSubgroup Q x) ∧
      B = Q ⊔ conjSubgroup Q x ∧ thompsonJ R = B := by
  have hDB := h.D_central hx hx2 hD hDc hD2 hDx
  have hUe : ElemAb2 U := ⟨h.U_comm, hU2⟩
  have hQe : ElemAb2 Q := hD ▸ ElemAb2.sup hUe hD2 hDc
  have hDUx : ElemAb2 (D ⊔ conjSubgroup U x) :=
    ElemAb2.sup hD2 (hUe.conjSubgroup x) fun d hd y hy => hDB d hd y (h.conj_le_B hx hy)
  have hcard := h.card_D_sup_conj hq2 hx hx1 hx2 hD hDc hDB
  have hmax : ∀ A, ElemAb2 A → A ≤ B → Nat.card A ≤ Nat.card Q := by
    intro A hAe hAB
    rcases h.elemAb_le hU2 hx hx1 hx2 hD hDc hD2 hDB hAe hAB with hle | hle
    · exact Subgroup.card_le_of_le hle
    · exact hcard ▸ Subgroup.card_le_of_le hle
  have hQB : Q ≤ B := h.Q_le_B
  obtain ⟨A₀, ⟨hA₀R, hA₀e⟩, hA₀max⟩ := exists_max_card (fun A : Subgroup G => A ≤ R ∧ ElemAb2 A)
    ⟨bot_le, ⟨fun a ha b hb => by simp_all, fun a ha => by simp_all⟩⟩
  have hA₀B : A₀ ≤ B := hA A₀ ⟨hA₀R, isElemAbelian_two_iff.mpr hA₀e, fun B' hB' hB'e =>
    hA₀max B' ⟨hB', isElemAbelian_two_iff.mp hB'e⟩⟩
  have hA₀Q : Nat.card A₀ ≤ Nat.card Q := hmax A₀ hA₀e hA₀B
  have hQmax : IsMaxElemAbelian R Q := ⟨hQB.trans hBR, isElemAbelian_two_iff.mpr hQe,
    fun B' hB' hB'e => (hA₀max B' ⟨hB', isElemAbelian_two_iff.mp hB'e⟩).trans hA₀Q⟩
  have hQxB : conjSubgroup Q x ≤ B := by
    have := conjSubgroup_mono hQB x
    rwa [conjSubgroup_eq_self hx] at this
  have hQxe : ElemAb2 (conjSubgroup Q x) := hQe.conjSubgroup x
  have hQxcard : Nat.card (conjSubgroup Q x) = Nat.card Q := card_conjSubgroup Q x
  have hQxne : conjSubgroup Q x ≠ Q := by
    intro heq
    apply hx1
    have := conjSubgroup_mono h.U_le_Q x
    rw [heq] at this
    exact this
  have hQxeq : conjSubgroup Q x = D ⊔ conjSubgroup U x := by
    rcases h.elemAb_le hU2 hx hx1 hx2 hD hDc hD2 hDB hQxe hQxB with hle | hle
    · exact absurd (Subgroup.eq_of_le_of_card_ge hle hQxcard.ge) hQxne
    · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hQxcard])).symm ▸ rfl
  have hQxmax : IsMaxElemAbelian R (conjSubgroup Q x) := by
    refine ⟨hQxB.trans hBR, isElemAbelian_two_iff.mpr hQxe, fun B' hB' hB'e => ?_⟩
    rw [hQxcard]
    exact (hA₀max B' ⟨hB', isElemAbelian_two_iff.mp hB'e⟩).trans hA₀Q
  have hall : ∀ A, IsMaxElemAbelian R A ↔ A = Q ∨ A = conjSubgroup Q x := by
    intro A
    constructor
    · intro hAmax
      have hAB := hA A hAmax
      have hAe : ElemAb2 A := isElemAbelian_two_iff.mp hAmax.2.1
      have hge : Nat.card Q ≤ Nat.card A := hAmax.2.2 Q (hQB.trans hBR) (isElemAbelian_two_iff.mpr hQe)
      rcases h.elemAb_le hU2 hx hx1 hx2 hD hDc hD2 hDB hAe hAB with hle | hle
      · exact Or.inl (Subgroup.eq_of_le_of_card_ge hle hge)
      · right
        rw [hQxeq]
        exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact hge)
    · rintro (rfl | rfl)
      · exact hQmax
      · exact hQxmax
  have hBeq : B = Q ⊔ conjSubgroup Q x := by
    refine le_antisymm ?_ (sup_le hQB hQxB)
    rw [← h.sup_Q_conj hx hx2]
    exact sup_le (le_sup_of_le_right (conjSubgroup_mono h.U_le_Q x)) le_sup_left
  have hJ : thompsonJ R = B := by
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun A hAmax => ?_
      rcases (hall A).mp hAmax with rfl | rfl
      · exact hQB
      · exact hQxB
    · rw [hBeq]
      exact sup_le (le_iSup₂_of_le Q hQmax le_rfl) (le_iSup₂_of_le _ hQxmax le_rfl)
  exact ⟨hQmax, hQxmax, hQxeq, hall, hBeq, hJ⟩

end Rank1

end CFSG.QuasithinUnique.C5

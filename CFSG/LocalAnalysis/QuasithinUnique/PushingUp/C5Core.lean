module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Conj
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting

public section

namespace CFSG.QuasithinUnique.C5

open CFSG.Quasithin Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

structure Rank1 (B Q U W : Subgroup G) (q : ℕ) : Prop where
  U_le_Q : U ≤ Q
  Q_le_B : Q ≤ B
  B_le_normQ : B ≤ normalizer (Q : Set G)
  B_le_normU : B ≤ normalizer (U : Set G)
  Q_eq : Q = B ⊓ centralizer (U : Set G)
  W_le_U : W ≤ U
  idx_Q : Q.relIndex B = q
  idx_W : W.relIndex U = q
  q_ne_zero : q ≠ 0
  cent_y : ∀ y ∈ B, y ∉ Q → ∀ u ∈ U, (u ∈ W ↔ u * y = y * u)
  comm_UB : ⁅U, B⁆ = W
  U_comm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a

namespace Rank1

variable {B Q U W : Subgroup G} {q : ℕ} (h : Rank1 B Q U W q)
include h

theorem U_le_B : U ≤ B := h.U_le_Q.trans h.Q_le_B

theorem conj_le_B {x : G} (hx : x ∈ normalizer (B : Set G)) : conjSubgroup U x ≤ B := by
  have := conjSubgroup_mono h.U_le_B x
  rwa [conjSubgroup_eq_self hx] at this

theorem B_le_normQ_conj {x : G} (hx : x ∈ normalizer (B : Set G)) :
    B ≤ normalizer ((conjSubgroup Q x : Subgroup G) : Set G) := by
  have := conjSubgroup_mono h.B_le_normQ x
  rwa [conjSubgroup_eq_self hx, conjSubgroup_normalizer] at this

theorem B_le_normU_conj {x : G} (hx : x ∈ normalizer (B : Set G)) :
    B ≤ normalizer ((conjSubgroup U x : Subgroup G) : Set G) := by
  have := conjSubgroup_mono h.B_le_normU x
  rwa [conjSubgroup_eq_self hx, conjSubgroup_normalizer] at this

theorem Q_cent : ∀ y ∈ Q, ∀ u ∈ U, u * y = y * u := by
  intro y hy u hu
  have : y ∈ B ⊓ centralizer (U : Set G) := h.Q_eq ▸ hy
  exact Subgroup.mem_centralizer_iff.mp this.2 u hu

theorem conj_comm (x : G) : ∀ a ∈ conjSubgroup U x, ∀ b ∈ conjSubgroup U x, a * b = b * a := by
  intro a ha b hb
  rw [mem_conjSubgroup_iff] at ha hb
  have := h.U_comm _ ha _ hb
  have h2 : x * (a * b) * x⁻¹ = x * (b * a) * x⁻¹ := by
    calc x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      _ = (x * b * x⁻¹) * (x * a * x⁻¹) := this
      _ = x * (b * a) * x⁻¹ := by group
  simpa using h2

theorem inf_centralizer_conj {x : G} (hx : x ∈ normalizer (B : Set G))
    (hx1 : ¬ conjSubgroup U x ≤ Q) :
    U ⊓ centralizer ((conjSubgroup U x : Subgroup G) : Set G) = W := by
  ext u
  constructor
  · rintro ⟨huU, huC⟩
    obtain ⟨y, hyU, hyQ⟩ := IsConcreteLE.not_le_iff_exists.mp hx1
    have hyB : y ∈ B := h.conj_le_B hx hyU
    have hcomm : y * u = u * y := Subgroup.mem_centralizer_iff.mp huC y hyU
    exact (h.cent_y y hyB hyQ u huU).mpr hcomm.symm
  · intro huW
    have huU : u ∈ U := h.W_le_U huW
    refine ⟨huU, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hyB : y ∈ B := h.conj_le_B hx hy
    by_cases hyQ : y ∈ Q
    · exact (h.Q_cent y hyQ u huU).symm
    · exact ((h.cent_y y hyB hyQ u huU).mp huW).symm

theorem inf_Q_conj {x : G} (hx : x ∈ normalizer (B : Set G))
    (hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q) :
    conjSubgroup U x ⊓ Q = conjSubgroup W x := by
  have h1 := h.inf_centralizer_conj (inv_mem hx) hx2
  have h2 := congrArg (fun A => conjSubgroup A x) h1
  simp only [conjSubgroup_inf, conjSubgroup_centralizer, conjSubgroup_conjSubgroup,
    inv_mul_cancel, conjSubgroup_one] at h2
  rw [← h2]
  refine le_antisymm (inf_le_inf_left _ ?_) (fun y hy => ⟨hy.1, ?_⟩)
  · intro y hy
    exact (h.Q_eq ▸ hy : y ∈ B ⊓ centralizer (U : Set G)).2
  · rw [h.Q_eq]
    exact ⟨h.conj_le_B hx hy.1, hy.2⟩

theorem sup_Q_conj [Finite G] {x : G} (hx : x ∈ normalizer (B : Set G))
    (hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q) : conjSubgroup U x ⊔ Q = B := by
  have hUxN : conjSubgroup U x ≤ normalizer (Q : Set G) := (h.conj_le_B hx).trans h.B_le_normQ
  have e1 : Q.relIndex (conjSubgroup U x ⊔ Q) = q := by
    rw [relIndex_sup_eq_of_le_normalizer hUxN, ← Subgroup.inf_relIndex_right Q (conjSubgroup U x),
      inf_comm, h.inf_Q_conj hx hx2, relIndex_conjSubgroup, h.idx_W]
  refine eq_of_relIndex_eq le_sup_right (sup_le (h.conj_le_B hx) h.Q_le_B) ?_ ?_
  · rw [e1, h.idx_Q]
  · rw [h.idx_Q]; exact h.q_ne_zero

theorem commutator_conj [Finite G] {x : G} (hx : x ∈ normalizer (B : Set G))
    (hx1 : ¬ conjSubgroup U x ≤ Q) (hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q) :
    ⁅U, conjSubgroup U x⁆ = W ∧ U ⊓ conjSubgroup U x = W := by
  have hUxB := h.conj_le_B hx
  have hB : B = conjSubgroup U x ⊔ Q := (h.sup_Q_conj hx hx2).symm
  have hUxN : conjSubgroup U x ≤ normalizer (Q : Set G) := hUxB.trans h.B_le_normQ
  have hle1 : ⁅U, conjSubgroup U x⁆ ≤ W :=
    h.comm_UB ▸ Subgroup.commutator_mono le_rfl hUxB
  have hle2 : W ≤ ⁅U, conjSubgroup U x⁆ := by
    rw [← h.comm_UB, Subgroup.commutator_le]
    intro u hu b hb
    have hbmem : b ∈ ((conjSubgroup U x ⊔ Q : Subgroup G) : Set G) := by
      rw [← hB]; exact hb
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (conjSubgroup U x) Q hUxN] at hbmem
    obtain ⟨a, ha, q', hq', rfl⟩ := hbmem
    have hc : Commute q' u := (h.Q_cent q' hq' u hu).symm
    have e : ⁅u, a * q'⁆ = ⁅u, a⁆ := by
      have h1 : q' * u⁻¹ = u⁻¹ * q' := (Commute.inv_right hc).eq
      calc ⁅u, a * q'⁆ = u * a * (q' * u⁻¹) * q'⁻¹ * a⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = u * a * (u⁻¹ * q') * q'⁻¹ * a⁻¹ := by rw [h1]
        _ = ⁅u, a⁆ := by simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.commutator_mem_commutator hu ha
  have hWeq : ⁅U, conjSubgroup U x⁆ = W := le_antisymm hle1 hle2
  refine ⟨hWeq, le_antisymm ?_ ?_⟩
  · intro v hv
    rw [← h.inf_centralizer_conj hx hx1]
    refine ⟨hv.1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact h.conj_comm x y hy v hv.2
  · intro w hw
    refine ⟨h.W_le_U hw, ?_⟩
    have hw' : w ∈ ⁅U, conjSubgroup U x⁆ := hWeq ▸ hw
    have hnorm : U ≤ normalizer ((conjSubgroup U x : Subgroup G) : Set G) :=
      h.U_le_B.trans (h.B_le_normU_conj hx)
    have : ⁅U, conjSubgroup U x⁆ ≤ conjSubgroup U x := by
      rw [Subgroup.commutator_le]
      intro u hu a ha
      have h1 : u * a * u⁻¹ ∈ conjSubgroup U x :=
        (Subgroup.mem_normalizer_iff.mp (hnorm hu) a).mp ha
      have h2 : u * a * u⁻¹ * a⁻¹ ∈ conjSubgroup U x :=
        Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ ha)
      simpa [commutatorElement_def, mul_assoc] using h2
    exact this hw'

theorem conj_W [Finite G] {x : G} (hx : x ∈ normalizer (B : Set G))
    (hx1 : ¬ conjSubgroup U x ≤ Q) (hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q) :
    conjSubgroup W x = W := by
  have hWU : W ≤ conjSubgroup U x := by
    rw [← (h.commutator_conj hx hx1 hx2).2]; exact inf_le_right
  have hle : W ≤ conjSubgroup W x := by
    rw [← h.inf_Q_conj hx hx2]
    exact le_inf hWU (h.W_le_U.trans h.U_le_Q)
  symm
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])

theorem conj_Q_eq {x : G} (hx : x ∈ normalizer (B : Set G)) :
    conjSubgroup Q x = B ⊓ centralizer ((conjSubgroup U x : Subgroup G) : Set G) := by
  rw [h.Q_eq, conjSubgroup_inf, conjSubgroup_eq_self hx, conjSubgroup_centralizer]

theorem relIndex_inf_conj [Finite G] {x : G} (hx : x ∈ normalizer (B : Set G))
    (hx1 : ¬ conjSubgroup U x ≤ Q) :
    (Q ⊓ conjSubgroup Q x).relIndex Q = q ∧ U ⊔ (Q ⊓ conjSubgroup Q x) = Q := by
  have hQx_le : conjSubgroup Q x ≤ B := by rw [h.conj_Q_eq hx]; exact inf_le_left
  have hQN : Q ≤ normalizer ((conjSubgroup Q x : Subgroup G) : Set G) :=
    h.Q_le_B.trans (h.B_le_normQ_conj hx)
  have hA : (Q ⊓ conjSubgroup Q x).relIndex Q ≤ q := by
    have e1 : (Q ⊓ conjSubgroup Q x).relIndex Q =
        (conjSubgroup Q x).relIndex (Q ⊔ conjSubgroup Q x) :=
      relIndex_inf_eq_of_le_normalizer hQN
    have e2 : (conjSubgroup Q x).relIndex B = q := by
      have := relIndex_conjSubgroup Q B x
      rwa [conjSubgroup_eq_self hx, h.idx_Q] at this
    rw [e1, ← e2]
    exact relIndex_le_of_le le_sup_right (sup_le h.Q_le_B hQx_le)
  have hCU : (Q ⊓ conjSubgroup Q x) ⊓ U = W := by
    refine le_antisymm ?_ ?_
    · rintro v ⟨⟨-, hvQx⟩, hvU⟩
      rw [← h.inf_centralizer_conj hx hx1]
      refine ⟨hvU, ?_⟩
      rw [h.conj_Q_eq hx] at hvQx
      exact hvQx.2
    · intro w hw
      have hwU : w ∈ U := h.W_le_U hw
      have hwC : w ∈ centralizer ((conjSubgroup U x : Subgroup G) : Set G) :=
        ((h.inf_centralizer_conj hx hx1).symm ▸ hw : w ∈ U ⊓ centralizer
          ((conjSubgroup U x : Subgroup G) : Set G)).2
      refine ⟨⟨h.U_le_Q hwU, ?_⟩, hwU⟩
      rw [h.conj_Q_eq hx]
      exact ⟨h.U_le_B hwU, hwC⟩
  have hUC : U ≤ normalizer ((Q ⊓ conjSubgroup Q x : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_inf (h.B_le_normQ (h.U_le_B hg)) (h.B_le_normQ_conj hx (h.U_le_B hg))
  have hb : (Q ⊓ conjSubgroup Q x).relIndex (U ⊔ (Q ⊓ conjSubgroup Q x)) = q := by
    rw [relIndex_sup_eq_of_le_normalizer hUC,
      ← Subgroup.inf_relIndex_right (Q ⊓ conjSubgroup Q x) U, hCU, h.idx_W]
  have hsup : U ⊔ (Q ⊓ conjSubgroup Q x) ≤ Q := sup_le h.U_le_Q inf_le_left
  have hle : (Q ⊓ conjSubgroup Q x).relIndex (U ⊔ (Q ⊓ conjSubgroup Q x)) ≤
      (Q ⊓ conjSubgroup Q x).relIndex Q := relIndex_le_of_le le_sup_right hsup
  have hq : (Q ⊓ conjSubgroup Q x).relIndex Q = q := le_antisymm hA (hb ▸ hle)
  refine ⟨hq, eq_of_relIndex_eq le_sup_right hsup (hb.trans hq.symm) ?_⟩
  exact Subgroup.index_ne_zero_of_finite (H := (Q ⊓ conjSubgroup Q x).subgroupOf Q)

theorem Q_eq_sup_centralizer [Finite G] {x : G} (hx : x ∈ normalizer (B : Set G))
    (hx1 : ¬ conjSubgroup U x ≤ Q) {K : Subgroup G} (hUK : U ≤ K)
    (hKQ : K ≤ normalizer (Q : Set G))
    (hZ : (U ⊓ centralizer (K : Set G)).relIndex U = q ^ 2)
    (hgen : ∃ k ∈ K, K ≤ conjSubgroup U x ⊔ conjSubgroup (conjSubgroup U x) k) :
    Q = U ⊔ (Q ⊓ centralizer (K : Set G)) ∧ Q ⊓ centralizer (K : Set G) ≤ conjSubgroup Q x := by
  obtain ⟨k, hkK, hgen⟩ := hgen
  have hk : k ∈ normalizer (Q : Set G) := hKQ hkK
  set X₁ := Q ⊓ conjSubgroup Q x with hX₁
  set C := Q ⊓ centralizer (K : Set G) with hC
  set Y₂ := Q ⊓ centralizer ((conjSubgroup (conjSubgroup U x) k : Subgroup G) : Set G) with hY₂
  have hX₁c : X₁ = Q ⊓ centralizer ((conjSubgroup U x : Subgroup G) : Set G) := by
    rw [hX₁, h.conj_Q_eq hx]
    ext y
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hyQ, -, hyc⟩; exact ⟨hyQ, hyc⟩
    · rintro ⟨hyQ, hyc⟩; exact ⟨hyQ, h.Q_le_B hyQ, hyc⟩
  have hY₂eq : conjSubgroup X₁ k = Y₂ := by
    rw [hX₁c, conjSubgroup_inf, conjSubgroup_eq_self hk, conjSubgroup_centralizer]
  have hq1 : X₁.relIndex Q = q := (h.relIndex_inf_conj hx hx1).1
  have hq2 : Y₂.relIndex Q = q := by
    have := relIndex_conjSubgroup X₁ Q k
    rwa [conjSubgroup_eq_self hk, hY₂eq, hq1] at this
  have hleC : X₁ ⊓ Y₂ ≤ C := by
    intro c hc
    refine ⟨hc.1.1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hcc : c ∈ centralizer ((conjSubgroup U x : Subgroup G) : Set G) := by
      rw [hX₁c] at hc; exact hc.1.2
    have hcc2 : c ∈ centralizer ((conjSubgroup (conjSubgroup U x) k : Subgroup G) : Set G) :=
      hc.2.2
    have : conjSubgroup U x ⊔ conjSubgroup (conjSubgroup U x) k ≤
        centralizer ({c} : Set G) := by
      refine sup_le (fun p hp => ?_) (fun p hp => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hcc p hp)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hcc2 p hp)
    exact Subgroup.mem_centralizer_singleton_iff.mp (this (hgen hy))
  have hrel : (X₁ ⊓ Y₂).relIndex Q ≤ q * q := by
    calc (X₁ ⊓ Y₂).relIndex Q ≤ X₁.relIndex Q * Y₂.relIndex Q := Subgroup.relIndex_inf_le
      _ = q * q := by rw [hq1, hq2]
  have hCle : C.relIndex Q ≤ q * q := (relIndex_le_of_le_left hleC Q).trans hrel
  have hUN : U ≤ normalizer (C : Set G) := fun g hg =>
    mem_normalizer_inf (hKQ (hUK hg)) (le_normalizer_centralizer_self K (hUK hg))
  have hCU : C ⊓ U = U ⊓ centralizer (K : Set G) := by
    ext y
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨_, hyc⟩, hyU⟩; exact ⟨hyU, hyc⟩
    · rintro ⟨hyU, hyc⟩; exact ⟨⟨h.U_le_Q hyU, hyc⟩, hyU⟩
  have hb : C.relIndex (U ⊔ C) = q ^ 2 := by
    rw [relIndex_sup_eq_of_le_normalizer hUN, ← Subgroup.inf_relIndex_right C U, hCU, hZ]
  have hsup : U ⊔ C ≤ Q := sup_le h.U_le_Q inf_le_left
  have hle : C.relIndex (U ⊔ C) ≤ C.relIndex Q := relIndex_le_of_le le_sup_right hsup
  have hCq : C.relIndex Q = q ^ 2 := le_antisymm (by rw [sq]; exact hCle) (hb ▸ hle)
  have hCfin : C.relIndex Q ≠ 0 := Subgroup.index_ne_zero_of_finite (H := C.subgroupOf Q)
  have hQ : U ⊔ C = Q := eq_of_relIndex_eq le_sup_right hsup (hb.trans hCq.symm) hCfin
  have hmul := Subgroup.relIndex_mul_relIndex (X₁ ⊓ Y₂) C Q hleC inf_le_left
  have hpos : 0 < (X₁ ⊓ Y₂).relIndex C :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := (X₁ ⊓ Y₂).subgroupOf C))
  have hqq : 0 < q * q := Nat.mul_pos (Nat.pos_of_ne_zero h.q_ne_zero) (Nat.pos_of_ne_zero h.q_ne_zero)
  have h1 : (X₁ ⊓ Y₂).relIndex C = 1 := by
    rw [hCq, sq] at hmul
    have h3 : (X₁ ⊓ Y₂).relIndex C * (q * q) ≤ 1 * (q * q) := by rw [hmul, one_mul]; exact hrel
    have := Nat.le_of_mul_le_mul_right h3 hqq
    omega
  have hCle' : C ≤ X₁ ⊓ Y₂ := Subgroup.relIndex_eq_one.mp h1
  exact ⟨hQ.symm, hCle'.trans (inf_le_left.trans inf_le_right)⟩

end Rank1

end CFSG.QuasithinUnique.C5

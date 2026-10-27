module

public import CFSG.LocalAnalysis.OddStandard.Seitz77WBridgeSetup

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement

abbrev Q25 {G : Type} [Group G] (X O : Subgroup G) [(O.subgroupOf X).Normal] : Type :=
  ↥X ⧸ O.subgroupOf X

namespace IsSetting25

variable {G : Type} [Group G] [Finite G] {A W X O : Subgroup G} {t : G}
  (S : IsSetting25 A W t X O) [(O.subgroupOf X).Normal]

@[expose] def phiW : ↥W →* Q25 X O :=
  (QuotientGroup.mk' (O.subgroupOf X)).comp (Subgroup.inclusion S.W_le_X)

@[expose] def tbar : Q25 X O := QuotientGroup.mk ⟨t, S.t_mem_X⟩

include S

theorem card_Q25 : Nat.card (Q25 X O) = 2 ^ 9 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (O.subgroupOf X)
  have h2 : Nat.card ↥(O.subgroupOf X) = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.O_le_X).toEquiv
  have hpos : 0 < Nat.card O := Nat.card_pos
  rw [h2, S.card_X] at h1
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [← h1, mul_comm]

theorem phiW_injective : Function.Injective S.phiW := by
  intro w w' h
  have h' : (QuotientGroup.mk (⟨(w : G), S.W_le_X w.2⟩ : X) : Q25 X O) =
      QuotientGroup.mk ⟨(w' : G), S.W_le_X w'.2⟩ := h
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h'
  have h1 : ((w⁻¹ * w' : W) : G) ∈ O := h'
  have h2 : ((w⁻¹ * w' : W) : G) ∈ W := (w⁻¹ * w').2
  have h3 : ((w⁻¹ * w' : W) : G) = 1 :=
    Subgroup.disjoint_def.mp (S.disjoint_O_of_isPGroup S.isPGroup_W) h1 h2
  exact inv_mul_eq_one.mp (Subtype.ext h3)

theorem phiW_range_le_center : S.phiW.range ≤ center (Q25 X O) := by
  rintro _ ⟨w, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  change (QuotientGroup.mk x : Q25 X O) * QuotientGroup.mk ⟨(w : G), S.W_le_X w.2⟩ =
    QuotientGroup.mk ⟨(w : G), S.W_le_X w.2⟩ * QuotientGroup.mk x
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  exact mul_inv_eq_iff_eq_mul.mp (S.X_cent x x.2 w w.2)

theorem card_phiW_range : Nat.card S.phiW.range = 16 := by
  rw [← S.W_card]
  exact (Nat.card_congr (MonoidHom.ofInjective S.phiW_injective).toEquiv).symm

theorem elem_phiW_range : IsElemAbelian 2 S.phiW.range := by
  refine L34.isElemAbelian_of_forall ?_ ?_
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (L34.comm_of_isElemAbelian S.W_elem a.2 b.2)
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (S.W_elem.2 a a.2)
    rw [this, map_one]

theorem tbar_mul_self : S.tbar * S.tbar = 1 := by
  unfold tbar
  rw [← QuotientGroup.mk_mul]
  have : (⟨t, S.t_mem_X⟩ * ⟨t, S.t_mem_X⟩ : ↥X) = 1 := Subtype.ext S.t_sq
  rw [this, QuotientGroup.mk_one]

theorem tbar_not_mem : S.tbar ∉ S.phiW.range := by
  rintro ⟨w, hw⟩
  have h' : (QuotientGroup.mk (⟨(w : G), S.W_le_X w.2⟩ : X) : Q25 X O) =
      QuotientGroup.mk ⟨t, S.t_mem_X⟩ := hw
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h'
  have hwo : (w : G)⁻¹ * t ∈ O := h'
  have hwE : (w : G) ∈ W ⊔ zpowers t := Subgroup.mem_sup_left w.2
  have hord_w : ∃ n : ℕ, orderOf (w : G) = 2 ^ n := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp S.isPGroup_W w
    exact ⟨n, by rw [Subgroup.orderOf_coe]; exact hn⟩
  have hwt : (w : G) * ((w : G)⁻¹ * t) = t := by group
  have h1 : (w : G)⁻¹ * t = 1 := by
    refine S.eq_one_of_two_power hwo ?_ hord_w ?_
    · exact (S.O_comm hwo hwE).symm
    · rw [hwt]; exact S.orderOf_t_two_power
  have h2 : (w : G) = t := by
    have := congrArg ((w : G) * ·) h1
    simpa [hwt] using this.symm
  exact S.t_not_mem (h2 ▸ w.2)

theorem centralizer_tbar :
    centralizer ({S.tbar} : Set (Q25 X O)) = S.phiW.range ⊔ zpowers S.tbar := by
  apply le_antisymm
  · intro x hx
    have hx' : S.tbar * x = x * S.tbar :=
      Subgroup.mem_centralizer_iff.mp hx S.tbar (Set.mem_singleton _)
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective x
    have hd : t * y * t⁻¹ * y⁻¹ ∈ W := S.commutator_t_mem_W (S.X_le hy)
    have hdX : t * y * t⁻¹ * y⁻¹ ∈ X :=
      X.mul_mem (X.mul_mem (X.mul_mem S.t_mem_X hy) (X.inv_mem S.t_mem_X)) (X.inv_mem hy)
    have hdO : t * y * t⁻¹ * y⁻¹ ∈ O := by
      have h1 : (QuotientGroup.mk ⟨t * y * t⁻¹ * y⁻¹, hdX⟩ : Q25 X O) = 1 := by
        have e : (⟨t * y * t⁻¹ * y⁻¹, hdX⟩ : ↥X) =
            ⟨t, S.t_mem_X⟩ * ⟨y, hy⟩ * ⟨t, S.t_mem_X⟩⁻¹ * ⟨y, hy⟩⁻¹ := rfl
        rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv, QuotientGroup.mk_inv]
        change S.tbar * _ * S.tbar⁻¹ * _ = 1
        rw [hx']
        group
      have h2 : (⟨t * y * t⁻¹ * y⁻¹, hdX⟩ : ↥X) ∈ O.subgroupOf X :=
        (QuotientGroup.eq_one_iff (N := O.subgroupOf X) _).mp h1
      exact h2
    have h1 : t * y * t⁻¹ * y⁻¹ = 1 :=
      Subgroup.disjoint_def.mp (S.disjoint_O_of_isPGroup S.isPGroup_W) hdO hd
    have hty : t * y = y * t := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
    have hyC : y ∈ centralizer ((W ⊔ zpowers t : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      rcases S.mem_E_iff.mp he with hew | ⟨w, hw, rfl⟩
      · exact (mul_inv_eq_iff_eq_mul.mp (S.X_cent y hy e hew)).symm
      · have h2 : y * w = w * y := mul_inv_eq_iff_eq_mul.mp (S.X_cent y hy w hw)
        calc w * t * y = w * (t * y) := by rw [mul_assoc]
          _ = w * (y * t) := by rw [hty]
          _ = (w * y) * t := by rw [mul_assoc]
          _ = (y * w) * t := by rw [h2]
          _ = y * (w * t) := by rw [mul_assoc]
    have hEN : (W ⊔ zpowers t : Subgroup G) ≤ normalizer (O : Set G) := by
      intro e he
      rw [Subgroup.mem_normalizer_iff]
      intro o
      have he' : e⁻¹ ∈ W ⊔ zpowers t := Subgroup.inv_mem _ he
      constructor
      · intro ho
        rw [← S.O_comm ho he, mul_inv_cancel_right]
        exact ho
      · intro ho
        have h2 : (e * o * e⁻¹) * e⁻¹ = e⁻¹ * (e * o * e⁻¹) := S.O_comm ho he'
        have h3 : o = e * o * e⁻¹ := by
          calc o = e⁻¹ * (e * o * e⁻¹) * e := by group
            _ = ((e * o * e⁻¹) * e⁻¹) * e := by rw [h2]
            _ = e * o * e⁻¹ := by group
        rw [h3]
        exact ho
    have hmem : y ∈ ((O ⊔ (W ⊔ zpowers t) : Subgroup G) : Set G) := by
      rw [S.O_sup]
      exact hyC
    rw [Subgroup.coe_mul_of_right_le_normalizer_left O _ hEN] at hmem
    obtain ⟨o, ho, e, he, hoe⟩ := hmem
    replace hoe : o * e = y := hoe
    have hmk : (QuotientGroup.mk ⟨y, hy⟩ : Q25 X O) = QuotientGroup.mk ⟨e, S.E_le_X he⟩ := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      show y⁻¹ * e ∈ O
      have hc : o⁻¹ * e = e * o⁻¹ := S.O_comm (O.inv_mem ho) he
      have : y⁻¹ * e = o⁻¹ := by
        calc y⁻¹ * e = (o * e)⁻¹ * e := by rw [hoe]
          _ = e⁻¹ * (o⁻¹ * e) := by rw [mul_inv_rev, mul_assoc]
          _ = o⁻¹ := by rw [hc, inv_mul_cancel_left]
      rw [this]
      exact O.inv_mem ho
    rw [hmk]
    rcases S.mem_E_iff.mp he with hew | ⟨w, hw, rfl⟩
    · exact Subgroup.mem_sup_left ⟨⟨e, hew⟩, rfl⟩
    · have : (QuotientGroup.mk ⟨w * t, S.E_le_X he⟩ : Q25 X O) = S.phiW ⟨w, hw⟩ * S.tbar := rfl
      rw [this]
      exact Subgroup.mul_mem_sup ⟨⟨w, hw⟩, rfl⟩ (Subgroup.mem_zpowers _)
  · apply sup_le
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact Subgroup.mem_center_iff.mp (S.phiW_range_le_center hx) S.tbar
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]

theorem comm_tbar (x : Q25 X O) : ⁅S.tbar, x⁆ ∈ S.phiW.range := by
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective x
  have hd : t * y * t⁻¹ * y⁻¹ ∈ W := S.commutator_t_mem_W (S.X_le hy)
  refine ⟨⟨t * y * t⁻¹ * y⁻¹, hd⟩, ?_⟩
  have e : S.phiW ⟨t * y * t⁻¹ * y⁻¹, hd⟩ = (QuotientGroup.mk
      (⟨t, S.t_mem_X⟩ * ⟨y, hy⟩ * ⟨t, S.t_mem_X⟩⁻¹ * ⟨y, hy⟩⁻¹ : ↥X) : Q25 X O) := rfl
  rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv, commutatorElement_def]
  rfl

end IsSetting25

section Conj

variable {G : Type} [Group G]

@[expose] def conjX (X : Subgroup G) (n : G) (hn : n ∈ normalizer (X : Set G)) : ↥X ≃* ↥X where
  toFun x := ⟨n * x * n⁻¹, (mem_normalizer_iff.mp hn x).mp x.2⟩
  invFun x := ⟨n⁻¹ * x * n, (mem_normalizer_iff''.mp hn x).mp x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

variable (X O : Subgroup G) [(O.subgroupOf X).Normal]

omit [(O.subgroupOf X).Normal] in
theorem map_conjX (n : G) (hX : n ∈ normalizer (X : Set G)) (hO : n ∈ normalizer (O : Set G)) :
    (O.subgroupOf X).map (conjX X n hX : ↥X →* ↥X) = O.subgroupOf X := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ O := hx
    show n * (x : G) * n⁻¹ ∈ O
    exact (mem_normalizer_iff.mp hO x).mp hx'
  · intro y hy
    have hy' : (y : G) ∈ O := hy
    refine ⟨(conjX X n hX).symm y, ?_, (conjX X n hX).apply_symm_apply y⟩
    show n⁻¹ * (y : G) * n ∈ O
    exact (mem_normalizer_iff''.mp hO y).mp hy'

@[expose] noncomputable def conjQ :
    ↥(normalizer (X : Set G) ⊓ normalizer (O : Set G)) →* MulAut (Q25 X O) where
  toFun n := QuotientGroup.congr (O.subgroupOf X) (O.subgroupOf X) (conjX X n n.2.1)
    (map_conjX X O n n.2.1 n.2.2)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => simp [conjX]
  map_mul' n m := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => simp [conjX, mul_assoc]

theorem conjQ_mk (n : ↥(normalizer (X : Set G) ⊓ normalizer (O : Set G))) (x : ↥X)
    (hx : (n : G) * x * (n : G)⁻¹ ∈ X) :
    conjQ X O n (QuotientGroup.mk x) = QuotientGroup.mk ⟨(n : G) * x * (n : G)⁻¹, hx⟩ := by
  show QuotientGroup.congr (O.subgroupOf X) (O.subgroupOf X) (conjX X n n.2.1)
    (map_conjX X O n n.2.1 n.2.2) (QuotientGroup.mk x) = _
  rw [QuotientGroup.congr_mk]
  rfl

end Conj

end CFSG.OddStandard.Seitz77

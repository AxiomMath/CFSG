module

public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Sylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement

structure IsSetting25 {G : Type} [Group G] [Finite G] (A W : Subgroup G) (t : G)
    (X O : Subgroup G) : Prop where
  W_le_A : W ≤ A
  W_elem : IsElemAbelian 2 W
  W_card : Nat.card W = 16
  t_sq : t * t = 1
  t_cent : t ∈ centralizer (A : Set G)
  t_not_mem : t ∉ W
  E_elem : IsElemAbelian 2 (W ⊔ zpowers t)
  E_card : Nat.card ↥(W ⊔ zpowers t) = 32
  norm_le : normalizer ((W ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (W : Set G)
  X_le : X ≤ normalizer ((W ⊔ zpowers t : Subgroup G) : Set G)
  normalizer_le : normalizer ((W ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (X : Set G)
  cent_le : centralizer ((W ⊔ zpowers t : Subgroup G) : Set G) ≤ X
  index_cent : (X ⊓ centralizer ((W ⊔ zpowers t : Subgroup G) : Set G)).relIndex X = 16
  conj_t : ∀ x ∈ normalizer ((W ⊔ zpowers t : Subgroup G) : Set G), ∃ w ∈ W, x * t * x⁻¹ = t * w
  trans : ∀ w ∈ W, ∃ p ∈ X, p * t * p⁻¹ = t * w
  X_cent : ∀ x ∈ X, ∀ w ∈ W, x * w * x⁻¹ = w
  O_odd : Odd (Nat.card O)
  O_norm : ∀ n ∈ normalizer ((W ⊔ zpowers t : Subgroup G) : Set G), ∀ o ∈ O, n * o * n⁻¹ ∈ O
  O_sup : O ⊔ (W ⊔ zpowers t) = centralizer ((W ⊔ zpowers t : Subgroup G) : Set G)
  odd_inf : Odd (Nat.card ↥(A ⊓ centralizer (A : Set G)))
  cent_t : centralizer ({t} : Set G) ≤ normalizer (A : Set G)

structure ActionFacts {G : Type} [Group G] (A W : Subgroup G) : Prop where
  cent : ∀ x ∈ normalizer (A : Set G), (∀ w ∈ W, x * w = w * x) → x ∈ W ⊔ centralizer (A : Set G)
  fix : ∀ x ∈ normalizer (A : Set G) ⊓ normalizer (W : Set G),
    x ∉ W ⊔ centralizer (A : Set G) → Nat.card ↥(W ⊓ centralizer ({x} : Set G)) ≤ 4
  rel : ∀ E' : Subgroup G, E' ≤ normalizer (A : Set G) ⊓ normalizer (W : Set G) →
    (∀ x ∈ E', ∀ y ∈ E', ⁅x, y⁆ ∈ centralizer (W : Set G) ∧ x * x ∈ centralizer (W : Set G)) →
      (centralizer (W : Set G)).relIndex E' ≤ 4


namespace IsSetting25

variable {G : Type} [Group G] [Finite G] {A W X O : Subgroup G} {t : G}
  (S : IsSetting25 A W t X O)

include S

theorem t_comm_W {w : G} (hw : w ∈ W) : t * w = w * t :=
  (mem_centralizer_iff.mp S.t_cent w (S.W_le_A hw)).symm

theorem isPGroup_W : IsPGroup 2 W :=
  IsPGroup.of_card (n := 4) (by rw [S.W_card]; norm_num)

theorem isPGroup_E : IsPGroup 2 ↥(W ⊔ zpowers t) :=
  IsPGroup.of_card (n := 5) (by rw [S.E_card]; norm_num)

theorem orderOf_t_two_power : ∃ n : ℕ, orderOf t = 2 ^ n := by
  have hd : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact S.t_sq)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact ⟨0, by rw [h]; norm_num⟩
  · exact ⟨1, by rw [h]; norm_num⟩

theorem mem_E_iff {x : G} : x ∈ W ⊔ zpowers t ↔ x ∈ W ∨ ∃ w ∈ W, x = w * t := by
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right S.t_sq
  let K : Subgroup G :=
    { carrier := {x | x ∈ W ∨ ∃ w ∈ W, x = w * t}
      one_mem' := Or.inl W.one_mem
      mul_mem' := by
        rintro a b (ha | ⟨u, hu, rfl⟩) (hb | ⟨v, hv, rfl⟩)
        · exact Or.inl (W.mul_mem ha hb)
        · exact Or.inr ⟨a * v, W.mul_mem ha hv, by rw [mul_assoc]⟩
        · refine Or.inr ⟨u * b, W.mul_mem hu hb, ?_⟩
          rw [mul_assoc, S.t_comm_W hb, ← mul_assoc]
        · refine Or.inl ?_
          have h : u * t * (v * t) = u * v := by
            calc u * t * (v * t) = u * (t * v) * t := by group
              _ = u * (v * t) * t := by rw [S.t_comm_W hv]
              _ = u * v * (t * t) := by group
              _ = u * v := by rw [S.t_sq, mul_one]
          rw [h]
          exact W.mul_mem hu hv
      inv_mem' := by
        rintro a (ha | ⟨u, hu, rfl⟩)
        · exact Or.inl (W.inv_mem ha)
        · exact Or.inr ⟨u⁻¹, W.inv_mem hu, by rw [mul_inv_rev, ht1, S.t_comm_W (W.inv_mem hu)]⟩ }
  constructor
  · intro hx
    have hle : W ⊔ zpowers t ≤ K :=
      sup_le (fun w hw => Or.inl hw)
        ((zpowers_le).mpr (Or.inr ⟨1, W.one_mem, (one_mul t).symm⟩))
    exact hle hx
  · rintro (hx | ⟨w, hw, rfl⟩)
    · exact mem_sup_left hx
    · exact mul_mem (mem_sup_left hw) (mem_sup_right (mem_zpowers t))

theorem comm_of_mem_E {x y : G} (hx : x ∈ W ⊔ zpowers t) (hy : y ∈ W ⊔ zpowers t) :
    x * y = y * x :=
  L34.comm_of_isElemAbelian S.E_elem hx hy

theorem E_le_centralizer :
    (W ⊔ zpowers t : Subgroup G) ≤ centralizer ((W ⊔ zpowers t : Subgroup G) : Set G) :=
  fun _ hx => mem_centralizer_iff.mpr fun _ hy => S.comm_of_mem_E hy hx

theorem E_le_X : W ⊔ zpowers t ≤ X :=
  S.E_le_centralizer.trans S.cent_le

theorem W_le_X : W ≤ X :=
  le_sup_left.trans S.E_le_X

theorem t_mem_X : t ∈ X :=
  S.E_le_X (mem_sup_right (mem_zpowers t))

theorem O_le_centralizer :
    O ≤ centralizer ((W ⊔ zpowers t : Subgroup G) : Set G) :=
  le_sup_left.trans S.O_sup.le

theorem O_le_X : O ≤ X :=
  S.O_le_centralizer.trans S.cent_le

theorem O_comm {o e : G} (ho : o ∈ O) (he : e ∈ W ⊔ zpowers t) : o * e = e * o :=
  (mem_centralizer_iff.mp (S.O_le_centralizer ho) e he).symm

theorem odd_orderOf_of_mem_O {o : G} (ho : o ∈ O) : Odd (orderOf o) :=
  S.O_odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard O ho)

theorem disjoint_O_of_isPGroup {P : Subgroup G} (hP : IsPGroup 2 P) : Disjoint O P := by
  rw [Subgroup.disjoint_def]
  intro x hxO hxP
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hP ⟨x, hxP⟩
  rw [Subgroup.orderOf_mk] at hn
  have hodd := S.odd_orderOf_of_mem_O hxO
  rcases n with _ | n
  · exact orderOf_eq_one_iff.mp (by rw [hn]; norm_num)
  · exfalso
    rw [hn] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero n⟩)

theorem disjoint_O_E : Disjoint O (W ⊔ zpowers t) :=
  S.disjoint_O_of_isPGroup S.isPGroup_E

theorem eq_one_of_two_power {v o : G} (ho : o ∈ O) (hvo : v * o = o * v)
    (hv : ∃ n, orderOf v = 2 ^ n) (hvo2 : ∃ m, orderOf (v * o) = 2 ^ m) : o = 1 :=
  L34.eq_one_of_two_power_of_odd (y := v * o) (v := v) (k := o) rfl hv hvo2 hvo
    (S.odd_orderOf_of_mem_O ho)

theorem card_centralizer :
    Nat.card ↥(centralizer ((W ⊔ zpowers t : Subgroup G) : Set G)) = Nat.card O * 32 := by
  have hnorm : (W ⊔ zpowers t : Subgroup G) ≤ normalizer (O : Set G) := by
    intro e he
    refine Subgroup.mem_normalizer_fintype fun o ho => ?_
    have h1 : e * o * e⁻¹ = o := by
      rw [← S.O_comm ho he, mul_inv_cancel_right]
    rw [h1]
    exact ho
  have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer O
    (W ⊔ zpowers t) hnorm S.disjoint_O_E
  rw [S.O_sup, S.E_card] at h
  exact h

theorem card_X : Nat.card X = Nat.card O * 2 ^ 9 := by
  have h := Subgroup.relIndex_mul_card
    (X ⊓ centralizer ((W ⊔ zpowers t : Subgroup G) : Set G)) X
  have hXC : X ⊓ centralizer ((W ⊔ zpowers t : Subgroup G) : Set G) =
      centralizer ((W ⊔ zpowers t : Subgroup G) : Set G) := inf_eq_right.mpr S.cent_le
  have hinf : (X ⊓ centralizer ((W ⊔ zpowers t : Subgroup G) : Set G)) ⊓ X =
      centralizer ((W ⊔ zpowers t : Subgroup G) : Set G) := by
    rw [hXC]
    exact inf_eq_left.mpr S.cent_le
  rw [S.index_cent, hinf, S.card_centralizer] at h
  rw [← h]
  ring

theorem normal_subgroupOf : (O.subgroupOf X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using S.O_norm (g : G) (S.X_le g.2) (n : G) hn

theorem normalizer_inf_centralizer_le :
    normalizer ((W ⊔ zpowers t : Subgroup G) : Set G) ⊓ centralizer (W : Set G) ≤ X := by
  intro x hx
  obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨w, hw, hxt⟩ := S.conj_t x hxN
  obtain ⟨p, hp, hpt⟩ := S.trans w hw
  have hle : (W ⊔ zpowers t : Subgroup G) ≤ centralizer ({p⁻¹ * x} : Set G) := by
    refine sup_le (fun v hv => ?_) ?_
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hpv : Commute p v := mul_inv_eq_iff_eq_mul.mp (S.X_cent p hp v hv)
      have hvx : Commute v x := Subgroup.mem_centralizer_iff.mp hxC v hv
      exact (hpv.symm.inv_right.mul_right hvx).eq
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      calc t * (p⁻¹ * x) = p⁻¹ * (p * t * p⁻¹) * x := by group
        _ = p⁻¹ * (x * t * x⁻¹) * x := by rw [hxt, hpt]
        _ = p⁻¹ * x * t := by group
  have hy : p⁻¹ * x ∈ centralizer ((W ⊔ zpowers t : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle he)
  have hyX : p⁻¹ * x ∈ X := S.cent_le hy
  have hpy := X.mul_mem hp hyX
  rwa [mul_inv_cancel_left] at hpy

theorem commutator_t_mem_W {x : G} (hx : x ∈ normalizer ((W ⊔ zpowers t : Subgroup G) : Set G)) :
    t * x * t⁻¹ * x⁻¹ ∈ W := by
  obtain ⟨w, hw, hxt⟩ := S.conj_t x hx
  have h1 : t * x * t⁻¹ * x⁻¹ = t * (t * w)⁻¹ := by
    rw [← hxt]
    group
  have h2 : t * (t * w)⁻¹ = w⁻¹ := by
    rw [mul_inv_rev, ← mul_assoc, S.t_comm_W (W.inv_mem hw), mul_inv_cancel_right]
  rw [h1, h2]
  exact W.inv_mem hw

theorem eq_mul_of_card {Z P : Subgroup G} (hOZ : O ≤ Z) (hPZ : P ≤ Z) {k : ℕ}
    (hPcard : Nat.card P = 2 ^ k) (hZcard : Nat.card Z = Nat.card O * 2 ^ k)
    (hPO : P ≤ normalizer (O : Set G)) : ∀ z ∈ Z, ∃ o ∈ O, ∃ p ∈ P, z = o * p := by
  have hdisj : Disjoint O P := S.disjoint_O_of_isPGroup (IsPGroup.of_card hPcard)
  have hcard : Nat.card ↥(O ⊔ P) = Nat.card Z := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer O P hPO hdisj,
      hPcard, hZcard]
  have hZ : O ⊔ P = Z := Subgroup.eq_of_le_of_card_ge (sup_le hOZ hPZ) hcard.ge
  intro z hz
  rw [← hZ] at hz
  open scoped Pointwise in
  have hz' : z ∈ (O : Set G) * (P : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left O P hPO]
    exact hz
  obtain ⟨o, ho, p, hp, rfl⟩ := hz'
  exact ⟨o, ho, p, hp, rfl⟩

theorem mem_sup_W_O {x : G} (hx : x ∈ W ⊔ O) : ∃ v ∈ W, ∃ o ∈ O, x = v * o := by
  have hWN : W ≤ normalizer (O : Set G) := by
    intro v hv
    refine Subgroup.mem_normalizer_fintype fun o ho => ?_
    have hvE : v ∈ W ⊔ zpowers t := Subgroup.mem_sup_left hv
    have h1 : v * o * v⁻¹ = o := by
      rw [← S.O_comm ho hvE, mul_inv_cancel_right]
    rw [h1]
    exact ho
  rw [sup_comm] at hx
  open scoped Pointwise in
  have hx' : x ∈ (O : Set G) * (W : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left O W hWN]
    exact hx
  obtain ⟨o, ho, v, hv, rfl⟩ := hx'
  exact ⟨v, hv, o, ho, S.O_comm ho (Subgroup.mem_sup_left hv)⟩

end IsSetting25

section Counting

variable {G : Type} [Group G] [Finite G]

theorem relIndex_le_of_le_sup {K E' B : Subgroup G} (hE : E' ≤ normalizer (K : Set G))
    (hB : B ≤ E' ⊔ K) : K.relIndex B ≤ K.relIndex E' := by
  have hK : K ≤ normalizer (K : Set G) := le_normalizer
  have hEK : E' ⊔ K ≤ normalizer (K : Set G) := sup_le hE hK
  have hne : K.relIndex (E' ⊔ K) ≠ 0 := by
    have : K.IsFiniteRelIndex (E' ⊔ K) := isFiniteRelIndex_of_finiteIndex
    exact relIndex_ne_zero
  have hnormal : (K.subgroupOf (normalizer (K : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hK).mpr le_rfl
  have h2 : K.relIndex (E' ⊔ K) = K.relIndex E' := by
    rw [← relIndex_subgroupOf hEK, ← relIndex_subgroupOf hE, subgroupOf_sup hE hK]
    exact relIndex_sup_right _ _
  exact (relIndex_le_of_le_right hB hne).trans h2.le

theorem relIndex_le_mul {W₂ Y B : Subgroup G} (hW₂Y : W₂ ≤ Y) :
    W₂.relIndex B ≤ Y.relIndex B * W₂.relIndex Y := by
  have hne : W₂.relIndex Y ≠ 0 := by
    have : W₂.IsFiniteRelIndex Y := isFiniteRelIndex_of_finiteIndex
    exact relIndex_ne_zero
  have h1 : (W₂ ⊓ B).relIndex (Y ⊓ B) * (Y ⊓ B).relIndex B = (W₂ ⊓ B).relIndex B :=
    relIndex_mul_relIndex _ _ _ (inf_le_inf_right B hW₂Y) inf_le_right
  have h2 : (W₂ ⊓ B).relIndex (Y ⊓ B) = W₂.relIndex (Y ⊓ B) := by
    rw [← inf_relIndex_right W₂ (Y ⊓ B), ← inf_assoc, inf_eq_left.mpr hW₂Y]
  rw [inf_relIndex_right W₂ B, inf_relIndex_right Y B, h2] at h1
  rw [← h1, mul_comm]
  exact Nat.mul_le_mul_left _ (relIndex_le_of_le_right inf_le_left hne)

omit [Finite G] in
theorem mem_centralizer_of_mem_sup {A W : Subgroup G} (hW : W ≤ A)
    (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {z : G}
    (hz : z ∈ W ⊔ centralizer (A : Set G)) (w : G) (hw : w ∈ W) : z * w = w * z := by
  have hle : W ⊔ centralizer (A : Set G) ≤ centralizer ({w} : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      exact hWab w hw x hx
    · rw [mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      exact mem_centralizer_iff.mp hx w (hW hw)
  exact ((mem_centralizer_iff.mp (hle hz)) w (Set.mem_singleton w)).symm

omit [Finite G] in
theorem mem_sup_of_forall_comm {O E : Subgroup G} (h : ∀ o ∈ O, ∀ e ∈ E, o * e = e * o) {x : G}
    (hx : x ∈ O ⊔ E) : ∃ o ∈ O, ∃ e ∈ E, x = o * e := by
  have hnorm : E ≤ normalizer (O : Set G) := by
    rw [le_normalizer_iff]
    intro e he o ho
    rw [← h o ho e he, mul_inv_cancel_right]
    exact ho
  have hx' : x ∈ ((O ⊔ E : Subgroup G) : Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left O E hnorm] at hx'
  obtain ⟨o, ho, e, he, rfl⟩ := hx'
  exact ⟨o, ho, e, he, rfl⟩

omit [Finite G] in
theorem mem_sup_centralizer {A W : Subgroup G} (hW : W ≤ A) {z : G}
    (hz : z ∈ W ⊔ centralizer (A : Set G)) :
    ∃ w ∈ W, ∃ k ∈ centralizer (A : Set G), z = w * k :=
  mem_sup_of_forall_comm (fun o ho _ he => mem_centralizer_iff.mp he o (hW ho)) hz

end Counting

theorem card_le_mul_self_of_mul_map {G : Type} [Group G] [Finite G] (Z V : Subgroup G) (d : G → G)
    (hV : ∀ z ∈ Z, d z ∈ V) (hmul : ∀ z ∈ Z, ∀ z' ∈ Z, d (z * z') = d z * d z')
    (hker : ∀ z ∈ Z, d z = 1 → z ∈ V) : Nat.card Z ≤ Nat.card V * Nat.card V := by
  have h1 : d 1 = 1 := by
    have h := hmul 1 Z.one_mem 1 Z.one_mem
    rw [mul_one] at h
    exact (mul_eq_left.mp h.symm)
  let δ : ↥Z →* ↥V :=
    { toFun := fun z => ⟨d z, hV z z.2⟩
      map_one' := Subtype.ext h1
      map_mul' := fun z z' => Subtype.ext (hmul z z.2 z' z'.2) }
  have hker_le : Nat.card δ.ker ≤ Nat.card V := by
    refine Nat.card_le_card_of_injective
      (fun z => (⟨(z : Z), hker z z.1.2 (congrArg Subtype.val z.2)⟩ : V)) ?_
    intro z z' hzz'
    have h : ((z : Z) : G) = ((z' : Z) : G) := congrArg (fun v : V => (v : G)) hzz'
    exact Subtype.ext (Subtype.ext h)
  calc Nat.card Z = Nat.card δ.ker * Nat.card δ.range := (Subgroup.card_ker_mul_card_range δ).symm
    _ ≤ Nat.card V * Nat.card V := Nat.mul_le_mul hker_le (Subgroup.card_le_card_group _)


section CentralizerAction

variable {G : Type} [Group G]

theorem normalizer_le_normalizer_centralizer_W (W : Subgroup G) :
    normalizer (W : Set G) ≤ normalizer (centralizer (W : Set G) : Set G) := by
  have h := (Subgroup.normal_subgroupOf_iff (Subgroup.centralizer_le_normalizer (W : Set G))).mp
    (Subgroup.normal_subgroupOf_centralizer_normalizer (W : Set G))
  intro g hg
  refine mem_set_normalizer_iff.mpr fun k => ⟨fun hk => h k g hk hg, fun hk => ?_⟩
  simpa [mul_assoc] using h _ g⁻¹ hk (inv_mem hg)

theorem comm_sq_mem_centralizer_of_mem_sup {W B : Subgroup G}
    (hB : B ≤ normalizer (W : Set G)) (hBe : IsElemAbelian 2 B) {x y : G}
    (hx : x ∈ B ⊔ centralizer (W : Set G)) (hy : y ∈ B ⊔ centralizer (W : Set G)) :
    ⁅x, y⁆ ∈ centralizer (W : Set G) ∧ x * x ∈ centralizer (W : Set G) := by
  have hKN : centralizer (W : Set G) ≤ normalizer (W : Set G) := centralizer_le_normalizer _
  have hBK : B ≤ normalizer (centralizer (W : Set G) : Set G) :=
    hB.trans (normalizer_le_normalizer_centralizer_W W)
  have key : ∀ z ∈ B ⊔ centralizer (W : Set G), ∃ b ∈ B, ∃ (hz : z ∈ normalizer (W : Set G))
      (hb : b ∈ normalizer (W : Set G)),
      W.normalizerMonoidHom ⟨z, hz⟩ = W.normalizerMonoidHom ⟨b, hb⟩ := by
    intro z hz
    rw [sup_comm] at hz
    open scoped Pointwise in
    have hz' : z ∈ (centralizer (W : Set G) : Set G) * (B : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hBK]
      exact hz
    obtain ⟨k, hk, b, hb, rfl⟩ := hz'
    have hkN := hKN hk
    have hbN := hB hb
    refine ⟨b, hb, mul_mem hkN hbN, hbN, ?_⟩
    have h1 : (⟨k * b, mul_mem hkN hbN⟩ : normalizer (W : Set G)) = ⟨k, hkN⟩ * ⟨b, hbN⟩ := rfl
    have h2 : W.normalizerMonoidHom ⟨k, hkN⟩ = 1 := by
      rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
      exact hk
    rw [h1, map_mul, h2, one_mul]
  obtain ⟨b₁, hb₁, hxN, hb₁N, h1⟩ := key x hx
  obtain ⟨b₂, hb₂, hyN, hb₂N, h2⟩ := key y hy
  have hcomm : b₁ * b₂ = b₂ * b₁ := L34.comm_of_isElemAbelian hBe hb₁ hb₂
  have hsq : b₁ * b₁ = 1 := by rw [← sq]; exact hBe.2 b₁ hb₁
  have hker : ∀ (g : G) (hg : g ∈ normalizer (W : Set G)),
      W.normalizerMonoidHom ⟨g, hg⟩ = 1 → g ∈ centralizer (W : Set G) := by
    intro g hg h
    have h' : (⟨g, hg⟩ : normalizer (W : Set G)) ∈ W.normalizerMonoidHom.ker := h
    rw [normalizerMonoidHom_ker] at h'
    exact h'
  have hc : ⁅x, y⁆ ∈ normalizer (W : Set G) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hxN hyN) (inv_mem hxN)) (inv_mem hyN)
  set nx : normalizer (W : Set G) := ⟨x, hxN⟩
  set ny : normalizer (W : Set G) := ⟨y, hyN⟩
  set nb₁ : normalizer (W : Set G) := ⟨b₁, hb₁N⟩
  set nb₂ : normalizer (W : Set G) := ⟨b₂, hb₂N⟩
  refine ⟨hker _ hc ?_, hker _ (mul_mem hxN hxN) ?_⟩
  · have e1 : (⟨⁅x, y⁆, hc⟩ : normalizer (W : Set G)) = ⁅nx, ny⁆ := rfl
    rw [e1, map_commutatorElement, h1, h2, ← map_commutatorElement]
    have e2 : ⁅nb₁, nb₂⁆ = 1 :=
      Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr hcomm)
    rw [e2, map_one]
  · have e1 : (⟨x * x, mul_mem hxN hxN⟩ : normalizer (W : Set G)) = nx * nx := rfl
    rw [e1, map_mul, h1, ← map_mul]
    have e2 : nb₁ * nb₁ = 1 := Subtype.ext hsq
    rw [e2, map_one]

end CentralizerAction

end CFSG.OddStandard.Seitz77

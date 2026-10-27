module

public import CFSG.GH74.GLS.C3.Layer1.U1aSetup
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.GLS.C3.Layer1.U1a

open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] {M L N W Q T : Subgroup G}

theorem mem_closure_pair {a b x : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (hx : x ∈ closure ({a, b} : Set G)) : x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have ha' : ∀ y : G, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have hb' : ∀ y : G, b * (b * y) = y := fun y => by rw [← mul_assoc, hb, one_mul]
  have hba' : ∀ y : G, b * (a * y) = a * (b * y) := fun y => by
    rw [← mul_assoc, ← hab, mul_assoc]
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
      simp [mul_assoc, ha, hb, ha', hba', hab.symm]
  | inv x _ hx =>
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · simp
    · right; left; exact inv_eq_of_mul_eq_one_right ha
    · right; right; left; exact inv_eq_of_mul_eq_one_right hb
    · right; right; right
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb, ← hab]

theorem isPGroup_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    IsPGroup 2 ↥(closure ({a, b} : Set G)) := by
  intro x
  refine ⟨1, ?_⟩
  have hx := mem_closure_pair ha hb hab x.2
  apply Subtype.ext
  show (x : G) ^ 2 ^ 1 = 1
  rw [pow_one, sq]
  rcases hx with hx | hx | hx | hx <;> rw [hx]
  · simp
  · exact ha
  · exact hb
  · calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, one_mul]

theorem mul_self_pair {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b)
    (hcomm : a * b = b * a) : orderOf (a * b) = 2 := by
  have ha1 := mul_self_eq_one_of_orderOf_eq_two ha
  have hb1 := mul_self_eq_one_of_orderOf_eq_two hb
  refine orderOf_eq_prime ?_ ?_
  · calc (a * b) ^ 2 = a * b * (a * b) := sq _
      _ = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hcomm]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha1, hb1, one_mul]
  · intro h
    apply hab
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_self_of_orderOf_eq_two hb]

@[expose] def A2 (M Q : Subgroup G) : Prop :=
  ∀ a ∈ Q, ∀ b ∈ Q, orderOf a = 2 → orderOf b = 2 → a ≠ b → a * b = b * a →
    ∀ g : G, g⁻¹ * a * g ∈ M → g⁻¹ * b * g ∈ M → g ∈ M

@[expose] def Yset (M Q : Subgroup G) (y : G) : Prop :=
  orderOf y = 2 ∧ y ∈ M ∧ ∃ x ∈ Q, orderOf x = 2 ∧ ∃ g : G, g ∉ M ∧ y = g⁻¹ * x * g

@[expose] def Vset (Q : Subgroup G) (v : G) : Prop := orderOf v = 2 ∧ ∃ g : G, g⁻¹ * v * g ∈ Q

theorem Yset.conj {y : G} (hy : Yset M Q y) {m : G} (hm : m ∈ M) : Yset M Q (m⁻¹ * y * m) := by
  obtain ⟨h2, hyM, x, hx, hx2, g, hg, hyg⟩ := hy
  refine ⟨(orderOf_conj_eq m).trans h2, ?_, x, hx, hx2, g * m, fun h => hg ?_, ?_⟩
  · exact M.mul_mem (M.mul_mem (M.inv_mem hm) hyM) hm
  · have := M.mul_mem h (M.inv_mem hm)
    simpa using this
  · rw [hyg]; group

theorem Yset.conj' {y : G} (hy : Yset M Q y) {m : G} (hm : m ∈ M) : Yset M Q (m * y * m⁻¹) := by
  have := Yset.conj hy (M.inv_mem hm)
  simpa using this

theorem Vset.conj {v : G} (hv : Vset Q v) (g : G) : Vset Q (g⁻¹ * v * g) := by
  obtain ⟨h2, h, hh⟩ := hv
  refine ⟨(orderOf_conj_eq g).trans h2, g⁻¹ * h, ?_⟩
  have e : (g⁻¹ * h)⁻¹ * (g⁻¹ * v * g) * (g⁻¹ * h) = h⁻¹ * v * h := by group
  rw [e]
  exact hh

theorem Vset.conj' {v : G} (hv : Vset Q v) (g : G) : Vset Q (g * v * g⁻¹) := by
  have := Vset.conj hv g⁻¹
  simpa using this

theorem Vset.of_mem {x : G} (hx : x ∈ Q) (h2 : orderOf x = 2) : Vset Q x :=
  ⟨h2, 1, by simpa using hx⟩

theorem Yset.vset {y : G} (hy : Yset M Q y) : Vset Q y := by
  obtain ⟨h2, -, x, hx, -, g, -, hyg⟩ := hy
  refine ⟨h2, g⁻¹, ?_⟩
  have e : (g⁻¹)⁻¹ * y * g⁻¹ = x := by rw [hyg]; group
  rw [e]
  exact hx

theorem Y_no_four_minimal [Finite G] {M W Q : Subgroup G}
    (hWM : W ≤ M) (hQ : IsSylowOf 2 Q W)
    (hpreuniq : ∀ x ∈ Q, orderOf x = 2 → centralizer ({x} : Set G) ≤ M)
    (hA2 : A2 M Q) {y : G} (hy : Yset M Q y) {a b : G} (ha : a ∈ W) (hb : b ∈ W)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a ≠ b) (hcomm : a * b = b * a)
    (hay : a * y = y * a) (hby : b * y = y * b) : False := by
  have ha1 := mul_self_eq_one_of_orderOf_eq_two ha2
  have hb1 := mul_self_eq_one_of_orderOf_eq_two hb2
  have hXW : closure ({a, b} : Set G) ≤ W := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact ha
    · exact hb
  obtain ⟨c, hcW, hc⟩ := exists_mem_conj_le hQ (hXW.trans le_rfl)
    (isPGroup_closure_pair ha1 hb1 hcomm)
  have ha' : c⁻¹ * a * c ∈ Q := hc a (subset_closure (by simp))
  have hb' : c⁻¹ * b * c ∈ Q := hc b (subset_closure (by simp))
  have hy' : Yset M Q (c⁻¹ * y * c) := hy.conj (hWM hcW)
  obtain ⟨-, -, x, hxQ, hx2, g, hgM, hyg⟩ := hy'
  have hcent : ∀ e : G, e * y = y * e → g * (c⁻¹ * e * c) * g⁻¹ ∈ M := by
    intro e hey
    have h1 : (c⁻¹ * e * c) * (c⁻¹ * y * c) = (c⁻¹ * y * c) * (c⁻¹ * e * c) := by
      calc (c⁻¹ * e * c) * (c⁻¹ * y * c) = c⁻¹ * (e * y) * c := by group
        _ = c⁻¹ * (y * e) * c := by rw [hey]
        _ = (c⁻¹ * y * c) * (c⁻¹ * e * c) := by group
    rw [hyg] at h1
    have h2 : (g * (c⁻¹ * e * c) * g⁻¹) ∈ centralizer ({x} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc g * (c⁻¹ * e * c) * g⁻¹ * x
          = g * ((c⁻¹ * e * c) * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * (c⁻¹ * e * c)) * g⁻¹ := by rw [h1]
        _ = x * (g * (c⁻¹ * e * c) * g⁻¹) := by group
    exact hpreuniq x hxQ hx2 h2
  have hne : c⁻¹ * a * c ≠ c⁻¹ * b * c := by
    intro h
    apply hab
    simpa using h
  have hcomm' : (c⁻¹ * a * c) * (c⁻¹ * b * c) = (c⁻¹ * b * c) * (c⁻¹ * a * c) := by
    calc (c⁻¹ * a * c) * (c⁻¹ * b * c) = c⁻¹ * (a * b) * c := by group
      _ = c⁻¹ * (b * a) * c := by rw [hcomm]
      _ = (c⁻¹ * b * c) * (c⁻¹ * a * c) := by group
  have := hA2 _ ha' _ hb' ((orderOf_conj_eq c).trans ha2) ((orderOf_conj_eq c).trans hb2) hne hcomm' g⁻¹
    (by simpa using hcent a hay) (by simpa using hcent b hby)
  exact hgM (by simpa using M.inv_mem this)

namespace Setup

variable (S : Setup M L N W Q T)
include S

theorem vset_of_W [Finite G] {w : G} (hw : w ∈ W) (hw2 : orderOf w = 2) : Vset Q w := by
  obtain ⟨c, -, hc⟩ := S.exists_conj_Q hw hw2
  exact ⟨hw2, c, hc⟩

theorem mem_W_or_Yset {v : G} (hv : Vset Q v) (hvM : v ∈ M) : v ∈ W ∨ Yset M Q v := by
  obtain ⟨hv2, g, hg⟩ := hv
  have hgv : v = g * (g⁻¹ * v * g) * g⁻¹ := by group
  by_cases hgM : g ∈ M
  · left
    rw [hgv]
    exact S.W_norm g hgM _ (S.Q_le_W hg)
  · right
    refine ⟨hv2, hvM, g⁻¹ * v * g, hg, (orderOf_conj_eq g).trans hv2, g⁻¹, fun h => hgM ?_, ?_⟩
    · simpa using M.inv_mem h
    · simp [mul_assoc]

theorem Y_no_four [Finite G] (hA2 : A2 M Q) {y : G} (hy : Yset M Q y) {a b : G} (ha : a ∈ W) (hb : b ∈ W)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a ≠ b) (hcomm : a * b = b * a)
    (hay : a * y = y * a) (hby : b * y = y * b) : False :=
  Y_no_four_minimal S.W_le S.sylowQ (fun x hxQ hx2 => S.preuniq x (S.Q_le_W hxQ) hx2) hA2 hy ha hb ha2 hb2 hab hcomm hay hby

theorem exists_central_involution [Finite G] :
    ∃ z ∈ Q, orderOf z = 2 ∧ ∀ t ∈ T, t * z = z * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, haQ, -, -, ha2, -, -, -⟩ := S.rankQ
  have : Group.IsNilpotent ↥T := S.T_isPGroup.isNilpotent
  let H : Subgroup ↥T := Q.subgroupOf T
  have hHn : H.Normal := ⟨fun n hn g => by
    have := S.Q_norm_T (g : G) g.2 (n : G) (Subgroup.mem_subgroupOf.mp hn)
    rw [Subgroup.mem_subgroupOf]
    simpa using this⟩
  have hH : H ≠ ⊥ := by
    intro h
    have haH : (⟨a, S.Q_le_T haQ⟩ : ↥T) ∈ H := haQ
    rw [h, Subgroup.mem_bot] at haH
    have : a = 1 := congrArg Subtype.val haH
    rw [this, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have hK := Group.IsNilpotent.inf_center_ne_bot_of_normal hH
  set K := H ⊓ center ↥T with hKdef
  have hKp : IsPGroup 2 ↥K := S.T_isPGroup.to_subgroup K
  have h2 : 2 ∣ Nat.card ↥K := by
    rcases hKp.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq K h) hK
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 h2
  have hxT : ((x : ↥K) : ↥T) ∈ H ⊓ center ↥T := x.2
  refine ⟨(((x : ↥K) : ↥T) : G), hxT.1, ?_, fun t ht => ?_⟩
  · have e1 : orderOf ((x : ↥K) : ↥T) = 2 := by rw [Subgroup.orderOf_coe, hx]
    rw [← e1, Subgroup.orderOf_coe]
  · have := Subgroup.mem_center_iff.mp hxT.2 ⟨t, ht⟩
    exact congrArg Subtype.val this

theorem eq_of_cent [Finite G] (hA2 : A2 M Q) {z : G} (hzQ : z ∈ Q) (hz2 : orderOf z = 2)
    (hzT : ∀ t ∈ T, t * z = z * t) {y : G} (hyT : y ∈ T) (hy : Yset M Q y) {u : G} (huQ : u ∈ Q)
    (hu2 : orderOf u = 2) (huy : u * y = y * u) : u = z := by
  by_contra hne
  exact S.Y_no_four hA2 hy (S.Q_le_W huQ) (S.Q_le_W hzQ) hu2 hz2 hne (hzT u (S.Q_le_T huQ)) huy
    (hzT y hyT).symm

theorem Y_not_mem_Q [Finite G] (hA2 : A2 M Q) {z : G} (hzQ : z ∈ Q) (hz2 : orderOf z = 2)
    (hzT : ∀ t ∈ T, t * z = z * t) {y : G} (hy : Yset M Q y) (hyQ : y ∈ Q) : False := by
  have hyT : y ∈ T := S.Q_le_T hyQ
  by_cases hzy : z = y
  · rw [← hzy] at hy
    obtain ⟨a, haQ, b, hbQ, ha2, hb2, hab, hcomm⟩ := S.rankQ
    exact S.Y_no_four hA2 hy (S.Q_le_W haQ) (S.Q_le_W hbQ) ha2 hb2 hab hcomm
      (hzT a (S.Q_le_T haQ)) (hzT b (S.Q_le_T hbQ))
  · exact S.Y_no_four hA2 hy (S.Q_le_W hyQ) (S.Q_le_W hzQ) hy.1 hz2 (Ne.symm hzy) (hzT y hyT)
      rfl (hzT y hyT).symm

theorem exists_swap [Finite G] (hA2 : A2 M Q) {z : G} (hzQ : z ∈ Q) (hz2 : orderOf z = 2)
    (hzT : ∀ t ∈ T, t * z = z * t) {y : G} (hyT : y ∈ T) (hy : Yset M Q y) :
    ∃ a ∈ Q, a * y * a⁻¹ = z * y := by
  have hy2 := hy.1
  have hyy := mul_self_eq_one_of_orderOf_eq_two hy2
  have hyinv := inv_eq_self_of_orderOf_eq_two hy2
  have hnormQ : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := S.Q_norm_T y hyT
  obtain ⟨q₁, hq₁Q, hq₁⟩ : ∃ q₁ ∈ Q, q₁ * y ≠ y * q₁ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, haQ, b, hbQ, ha2, hb2, hab, hcomm⟩ := S.rankQ
    exact S.Y_no_four hA2 hy (S.Q_le_W haQ) (S.Q_le_W hbQ) ha2 hb2 hab hcomm (hcon a haQ)
      (hcon b hbQ)
  set P' : Subgroup G := Q ⊔ zpowers y with hP'
  have hyP' : y ∈ P' := mem_sup_right (mem_zpowers y)
  have hP'T : P' ≤ T := sup_le S.Q_le_T (zpowers_le.mpr hyT)
  have hnil : Group.IsNilpotent ↥P' := (S.T_isPGroup.to_le hP'T).isNilpotent
  set C : Subgroup G := P' ⊓ centralizer ({y} : Set G) with hC
  have hlt : C.subgroupOf P' < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hq₁ ?_
    have hq₁P : q₁ ∈ P' := mem_sup_left hq₁Q
    have : (⟨q₁, hq₁P⟩ : ↥P') ∈ C.subgroupOf P' := htop ▸ Subgroup.mem_top _
    have h2 : q₁ ∈ centralizer ({y} : Set G) := (Subgroup.mem_inf.mp this).2
    exact mem_centralizer_singleton_iff.mp h2
  obtain ⟨r, hrN, hrC⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hyC : (⟨y, hyP'⟩ : ↥P') ∈ C.subgroupOf P' := ⟨hyP', mem_centralizer_singleton_iff.mpr rfl⟩
  have h1 := (Subgroup.mem_normalizer_iff.mp hrN ⟨y, hyP'⟩).mp hyC
  have h1' : (r : G) * y * (r : G)⁻¹ ∈ centralizer ({y} : Set G) := by
    have := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h1)).2
    simpa using this
  have hynorm : zpowers y ≤ normalizer (Q : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro h
    refine ⟨hnormQ h, fun hh => ?_⟩
    have h2 := hnormQ _ hh
    have e : y * (y * h * y⁻¹) * y⁻¹ = h := by
      rw [hyinv, ← mul_assoc, ← mul_assoc, hyy, one_mul, mul_assoc, hyy, mul_one]
    rwa [e] at h2
  have hr' : (r : G) ∈ ((Q ⊔ zpowers y : Subgroup G) : Set G) := r.2
  rw [coe_mul_of_right_le_normalizer_left Q (zpowers y) hynorm] at hr'
  obtain ⟨q, hq, w, hw, hrw⟩ := hr'
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  have hzy : y ^ k * y = y * y ^ k := (Commute.self_zpow y k).eq.symm
  have hy' : q * y * q⁻¹ ∈ centralizer ({y} : Set G) := by
    have e : q * y ^ k * y * (q * y ^ k)⁻¹ = q * y * q⁻¹ := by
      calc q * y ^ k * y * (q * y ^ k)⁻¹ = q * (y ^ k * y * (y ^ k)⁻¹) * q⁻¹ := by group
        _ = q * y * q⁻¹ := by rw [hzy]; group
    have hrw' : q * y ^ k = (r : G) := hrw
    rw [← e, hrw']
    exact h1'
  have hqnc : q * y ≠ y * q := by
    intro hcomm
    apply hrC
    refine ⟨r.2, ?_⟩
    have hrw' : q * y ^ k = (r : G) := hrw
    show (r : G) ∈ centralizer ({y} : Set G)
    rw [mem_centralizer_singleton_iff, ← hrw']
    symm
    calc y * (q * y ^ k) = (y * q) * y ^ k := by group
      _ = (q * y) * y ^ k := by rw [hcomm]
      _ = q * (y * y ^ k) := by group
      _ = q * (y ^ k * y) := by rw [hzy]
      _ = q * y ^ k * y := by group
  have hyc : y * (q * y * q⁻¹) = (q * y * q⁻¹) * y := (mem_centralizer_singleton_iff.mp hy').symm
  have hc : q * y * q⁻¹ * y ∈ Q := by
    have h := S.Q_norm_T y hyT q⁻¹ (Q.inv_mem hq)
    rw [hyinv] at h
    have : q * (y * q⁻¹ * y) ∈ Q := Q.mul_mem hq h
    simpa [mul_assoc] using this
  have hcy : (q * y * q⁻¹ * y) * y = y * (q * y * q⁻¹ * y) := by
    calc (q * y * q⁻¹ * y) * y = q * y * q⁻¹ := by
          calc (q * y * q⁻¹ * y) * y = q * y * q⁻¹ * (y * y) := by group
            _ = q * y * q⁻¹ := by rw [hyy, mul_one]
      _ = y * (q * y * q⁻¹ * y) := by
          calc q * y * q⁻¹ = (q * y * q⁻¹) * (y * y) := by rw [hyy, mul_one]
            _ = ((q * y * q⁻¹) * y) * y := by group
            _ = (y * (q * y * q⁻¹)) * y := by rw [hyc]
            _ = y * (q * y * q⁻¹ * y) := by group
  have hc2 : orderOf (q * y * q⁻¹ * y) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · have hy'2 : (q * y * q⁻¹) * (q * y * q⁻¹) = 1 := by
        calc (q * y * q⁻¹) * (q * y * q⁻¹) = q * (y * y) * q⁻¹ := by group
          _ = 1 := by rw [hyy]; group
      calc (q * y * q⁻¹ * y) ^ 2 = (q * y * q⁻¹) * (y * (q * y * q⁻¹)) * y := by rw [sq]; group
        _ = (q * y * q⁻¹) * ((q * y * q⁻¹) * y) * y := by rw [hyc]
        _ = ((q * y * q⁻¹) * (q * y * q⁻¹)) * (y * y) := by group
        _ = 1 := by rw [hy'2, hyy, one_mul]
    · intro h
      apply hqnc
      calc q * y = (q * y * q⁻¹ * y) * (y * q) := by
            calc q * y = q * y * q⁻¹ * (y * y) * q := by rw [hyy]; group
              _ = (q * y * q⁻¹ * y) * (y * q) := by group
        _ = y * q := by rw [h, one_mul]
  have hcz := S.eq_of_cent hA2 hzQ hz2 hzT hyT hy hc hc2 hcy
  refine ⟨q, hq, ?_⟩
  calc q * y * q⁻¹ = (q * y * q⁻¹ * y) * y := by
        calc q * y * q⁻¹ = (q * y * q⁻¹) * (y * y) := by rw [hyy, mul_one]
          _ = (q * y * q⁻¹ * y) * y := by group
    _ = z * y := by rw [hcz]

theorem vset_mul [Finite G] (hA2 : A2 M Q) {u v : G} (hu : Vset Q u) (hv : Vset Q v) (hne : u ≠ v)
    (hcomm : u * v = v * u) : Vset Q (u * v) := by
  obtain ⟨z, hzQ, hz2, hzT⟩ := S.exists_central_involution
  obtain ⟨g, hg⟩ := hu.2
  suffices h : ∀ u v : G, Vset Q v → u ∈ Q → orderOf u = 2 → u ≠ v → u * v = v * u →
      Vset Q (u * v) by
    have := h (g⁻¹ * u * g) (g⁻¹ * v * g) (hv.conj g) hg ((orderOf_conj_eq g).trans hu.1)
      (fun h => hne (by simpa using h))
      (by
        calc g⁻¹ * u * g * (g⁻¹ * v * g) = g⁻¹ * (u * v) * g := by group
          _ = g⁻¹ * (v * u) * g := by rw [hcomm]
          _ = g⁻¹ * v * g * (g⁻¹ * u * g) := by group)
    have e : g⁻¹ * u * g * (g⁻¹ * v * g) = g⁻¹ * (u * v) * g := by group
    rw [e] at this
    have h2 := this.conj' g
    have e2 : g * (g⁻¹ * (u * v) * g) * g⁻¹ = u * v := by group
    rwa [e2] at h2
  intro u v hv huQ hu2 hne hcomm
  have huW : u ∈ W := S.Q_le_W huQ
  have hvM : v ∈ M := by
    have : v ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr hcomm.symm
    exact S.preuniq u huW hu2 this
  have hv2 := hv.1
  have hprod : orderOf (u * v) = 2 := mul_self_pair hu2 hv2 hne hcomm
  rcases S.mem_W_or_Yset hv hvM with hvW | hvY
  · exact S.vset_of_W (W.mul_mem huW hvW) hprod
  · have hu1 := mul_self_eq_one_of_orderOf_eq_two hu2
    have hv1 := mul_self_eq_one_of_orderOf_eq_two hv2
    have hXM : closure ({u, v} : Set G) ≤ M := by
      rw [closure_le]
      rintro x (rfl | rfl)
      · exact S.W_le huW
      · exact hvM
    obtain ⟨m, hmM, hm⟩ := exists_mem_conj_le S.sylowT hXM (isPGroup_closure_pair hu1 hv1 hcomm)
    have hu' : m⁻¹ * u * m ∈ T := hm u (subset_closure (by simp))
    have hv' : m⁻¹ * v * m ∈ T := hm v (subset_closure (by simp))
    have hu'W : m⁻¹ * u * m ∈ W := S.W_norm _ (M.inv_mem hmM) _ huW |> fun h => by simpa using h
    have hu'Q : m⁻¹ * u * m ∈ Q := by
      rw [S.Q_eq]
      exact ⟨hu', hu'W⟩
    have hv'Y : Yset M Q (m⁻¹ * v * m) := hvY.conj hmM
    have hcomm' : (m⁻¹ * u * m) * (m⁻¹ * v * m) = (m⁻¹ * v * m) * (m⁻¹ * u * m) := by
      calc (m⁻¹ * u * m) * (m⁻¹ * v * m) = m⁻¹ * (u * v) * m := by group
        _ = m⁻¹ * (v * u) * m := by rw [hcomm]
        _ = (m⁻¹ * v * m) * (m⁻¹ * u * m) := by group
    have hz := S.eq_of_cent hA2 hzQ hz2 hzT hv' hv'Y hu'Q ((orderOf_conj_eq m).trans hu2) hcomm'
    obtain ⟨a, haQ, ha⟩ := S.exists_swap hA2 hzQ hz2 hzT hv' hv'Y
    rw [hz] at hcomm'
    have h3 : Vset Q (m⁻¹ * v * m) := hv'Y.vset
    have h4 := h3.conj' a
    rw [ha] at h4
    have h5 : Vset Q (m⁻¹ * (u * v) * m) := by
      have e : m⁻¹ * (u * v) * m = (m⁻¹ * u * m) * (m⁻¹ * v * m) := by group
      rw [e, hz]
      exact h4
    have h6 := h5.conj' m
    have e3 : m * (m⁻¹ * (u * v) * m) * m⁻¹ = u * v := by group
    rwa [e3] at h6

end Setup

end CFSG.GH74.GLS.C3.Layer1.U1a

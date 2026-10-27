module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.TwoFour
public import CFSG.LocalAnalysis.EvenBN.LinearThree.WLocalElementary

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.OddStandard.Seitz77 (Datum)

structure WData {G : Type} [Group G] {A : Subgroup G} (d : Datum A) (Vi : Subgroup G) (q : ℕ) where
  W : Subgroup G
  elem : IsElemAbelian 2 W
  card : Nat.card W = q ^ 4
  lt : Vi < W
  t_not_mem : d.t ∉ W
  t_norm : d.t ∈ normalizer (W : Set G)
  fix : W ⊓ centralizer ({d.t} : Set G) = Vi
  comm_mem : ∀ w ∈ W, d.t * w * d.t * w⁻¹ ∈ Vi
  comm_onto : ∀ v ∈ Vi, ∃ w ∈ W, d.t * w * d.t * w⁻¹ = v
  normal : normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (W : Set G)
  levi_norm : A ⊓ normalizer (Vi : Set G) ≤ normalizer (W : Set G)
  sup_le_inf_centralizer : W ⊔ zpowers d.t ≤
    normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ⊓ centralizer (Vi : Set G)
  le_sup_of_isPGroup : ∀ P : Subgroup G, IsPGroup 2 P →
    P ≤ normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ⊓ centralizer (Vi : Set G) →
    P ≤ W ⊔ zpowers d.t
  unique : ∀ W' : Subgroup G, W' ≤ W ⊔ zpowers d.t → (∀ a ∈ W', ∀ b ∈ W', a * b = b * a) →
    Nat.card W' = q ^ 4 → W' = W

namespace Hyp

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}

theorem centralizer_adj_eq (h : Hyp G A f) (d : Datum A) {V₁ V₂ W : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : W = V₁ ∨ W = V₂) :
    centralizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) = W ⊔ zpowers d.t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hWV, hWe, -⟩ := hR.property hW
  have hKt : IsPGroup 2 (centralizer (A : Set G) ⊓ centralizer ({d.t} : Set G) : Subgroup G) :=
    (CFSG.SeitzReduction.inf_centralizer_isCyclic_of_standard h.standard ⟨d.R, h.cyc d.R⟩
      d.t_mem_K d.sector.t_order (h.core d.t d.sector.t_order)).2
  have htE : d.t ∈ (W ⊔ zpowers d.t : Subgroup G) := mem_sup_right (mem_zpowers _)
  have h2 : IsPGroup 2 (centralizer ((W ⊔ zpowers d.t : Subgroup G) : Set G)) := by
    rw [IsPGroup.iff_orderOf]
    rintro ⟨x, hx⟩
    have hxt : x * d.t = d.t * x := (mem_centralizer_iff.mp hx d.t htE).symm
    have hxN : x ∈ normalizer (A : Set G) :=
      (OddStandard.centralizer_t_facts d.sector).1 (mem_centralizer_singleton_iff.mpr hxt)
    have hxW : x ∈ centralizer (W : Set G) :=
      mem_centralizer_iff.mpr fun w hw => mem_centralizer_iff.mp hx w (mem_sup_left hw)
    obtain ⟨w, hw, k, hk, rfl⟩ := OddStandard.Seitz77.mem_sup_of_commute
      (fun a ha k hk => mem_centralizer_iff.mp hk a (hWV ha).2)
      (h.facts.cent_radical d.V V₁ V₂ d.V_isSylow hR W hW ⟨hxN, hxW⟩)
    have hwk : w * k = k * w := mem_centralizer_iff.mp hk w (hWV hw).2
    have hkt : k ∈ centralizer ({d.t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have hwt := d.V_comm_t (hWV hw)
      have hwt' : w⁻¹ * d.t = d.t * w⁻¹ := (Commute.inv_left (show Commute w d.t from hwt)).eq
      calc k * d.t = w⁻¹ * ((w * k) * d.t) := by group
        _ = w⁻¹ * (d.t * (w * k)) := by rw [hxt]
        _ = (w⁻¹ * d.t) * (w * k) := by group
        _ = (d.t * w⁻¹) * (w * k) := by rw [hwt']
        _ = d.t * k := by group
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hKt ⟨k, hk, hkt⟩
    have hk1 : k ^ (2 ^ m) = 1 := by
      have := pow_orderOf_eq_one
        (⟨k, hk, hkt⟩ : ↥(centralizer (A : Set G) ⊓ centralizer ({d.t} : Set G)))
      rw [hm] at this
      simpa using congrArg Subtype.val this
    have hw2 : w ^ 2 = 1 := hWe.2 w hw
    have hpow : (w * k) ^ (2 ^ (m + 1)) = 1 := by
      rw [(show Commute w k from hwk).mul_pow, pow_succ, pow_mul' w, pow_mul k, hw2, hk1, one_pow,
        one_pow, one_mul]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
    exact ⟨j, by rw [Subgroup.orderOf_mk, hj]⟩
  exact (h.isSylowOf_centralizer d hR hW).eq_of_le
    (fun x hx => mem_centralizer_iff.mpr fun y hy => by
      obtain ⟨-, hEe, -⟩ := (SylowSetting.of_datum d).adj_properties h.facts.toFusionFacts hR hW
      exact comm_of_isElemAbelian hEe hy hx) le_rfl h2

end Hyp

namespace WLocal

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}

theorem exists_xSetting (h : Hyp G A f) (d : Datum A) {V₁ V₂ W : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : W = V₁ ∨ W = V₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (S : WLocal.XSetting G K),
      Nat.card K = 2 ^ f ∧
      S.X = normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) ⊓ centralizer (W : Set G) ∧
      S.t = d.t ∧ (∀ v, S.ι v ∈ W) ∧ (∀ x ∈ W, ∃ v, S.ι v = x) := by
  obtain ⟨hWV, hWe, -⟩ := hR.property hW
  obtain ⟨-, hEe, -⟩ := (SylowSetting.of_datum d).adj_properties h.facts.toFusionFacts hR hW
  obtain ⟨X, hX, hXeq, -, φ, hφ, hker, hsurj, -⟩ := h.exists_regularNormal d hR hW
  have hNX := hX.normalizer_le
  subst hXeq
  have hCE := h.centralizer_adj_eq d hR hW
  obtain ⟨K, _, hK, ⟨D⟩⟩ := h.facts.levi d.V V₁ V₂ d.V_isSylow hR W hW
  have hf1 : 1 ≤ f := by have := h.three_le; omega
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf1 hK
  have hW' : ∀ y, y ∈ W ↔ y ∈ D.ι.range := fun y => by rw [D.range_ι]
  have hEC : ∀ x ∈ (W ⊔ zpowers d.t : Subgroup G),
      x ∈ centralizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) := fun x hx =>
    mem_centralizer_iff.mpr fun y hy => comm_of_isElemAbelian hEe hy hx
  have hEN : ∀ x ∈ (W ⊔ zpowers d.t : Subgroup G),
      x ∈ normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) := fun x hx =>
    centralizer_le_normalizer _ (hEC x hx)
  have hWC : ∀ x ∈ W, x ∈ centralizer (W : Set G) := fun x hx =>
    mem_centralizer_iff.mpr fun y hy => comm_of_isElemAbelian hWe hy hx
  have hconjX : ∀ g ∈ normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G),
      ∀ x ∈ normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) ⊓ centralizer (W : Set G),
        g * x * g⁻¹ ∈ normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) ⊓
          centralizer (W : Set G) :=
    fun g hg x hx => (mem_normalizer_iff.mp (hNX hg) x).mp hx
  have hlevN : ∀ B, D.lev B ∈ normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) := fun B =>
    mem_normalizer_adj_of_mem_A d hWV ⟨D.lev_mem B, D.lev_mem_normalizer B⟩
  have htorN : ∀ l, D.tor l ∈ normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) := fun l =>
    mem_normalizer_adj_of_mem_A d hWV ⟨D.tor_mem l, D.tor_mem_normalizer l⟩
  have hφW : ∀ x (hx : x ∈ normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) ⊓
      centralizer (W : Set G)), d.t * x * d.t * x⁻¹ = ((φ ⟨x, hx⟩ : W) : G) := fun x hx => by
    rw [hφ]; group
  refine ⟨K, inferInstance, inferInstance, inferInstance,
    { X := normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) ⊓ centralizer (W : Set G)
      t := d.t
      ι := fun v => D.ι (Multiplicative.ofAdd v)
      lev := D.lev
      tor := D.tor
      ι_add := fun u v => by rw [ofAdd_add, map_mul]
      ι_injective := D.ι_injective.comp Multiplicative.ofAdd.injective
      ι_mem := fun v => ⟨hEN _ (mem_sup_left (D.ι_mem_W _)), hWC _ (D.ι_mem_W _)⟩
      ι_comm := fun v x hx => mem_centralizer_iff.mp hx.2 _ (D.ι_mem_W _)
      t_mem := ⟨hEN _ (mem_sup_right (mem_zpowers _)),
        mem_centralizer_iff.mpr fun y hy => d.V_comm_t (hWV hy)⟩
      t_mul_self := d.t_mul_self
      comm_mem := fun x hx => by
        obtain ⟨w, hw⟩ := (hW' _).mp (φ ⟨x, hx⟩).2
        exact ⟨Multiplicative.toAdd w, by rw [hφW x hx, ← hw]; rfl⟩
      comm_surj := fun v => by
        obtain ⟨⟨x, hx⟩, hxv⟩ := hsurj ⟨_, D.ι_mem_W (Multiplicative.ofAdd v)⟩
        exact ⟨x, hx, by rw [hφW x hx, hxv]⟩
      comm_eq_one := fun x hx h1 => by
        have h2 : φ ⟨x, hx⟩ = 1 := Subtype.ext (by rw [← hφW x hx, h1]; rfl)
        have h3 := (hker ⟨x, hx⟩).mp h2
        rw [hCE] at h3
        rcases (d.mem_adj_iff hWV).mp h3 with h4 | h4
        · obtain ⟨w, hw⟩ := (hW' _).mp h4
          exact ⟨Multiplicative.toAdd w, Or.inl hw.symm⟩
        · obtain ⟨w, hw⟩ := (hW' _).mp h4
          refine ⟨Multiplicative.toAdd w, Or.inr ?_⟩
          change x = D.ι w * d.t
          rw [hw, mul_assoc, d.t_mul_self, mul_one]
      lev_mem := fun B x hx => hconjX _ (hlevN B) x hx
      lev_t := fun B => d.comm_t_of_mem (D.lev_mem B)
      lev_ι := fun B v => by rw [D.lev_conj, toAdd_ofAdd]
      tor_mem := fun l x hx => hconjX _ (htorN l) x hx
      tor_t := fun l => d.comm_t_of_mem (D.tor_mem l)
      tor_ι := fun l v => by rw [D.tor_conj, toAdd_ofAdd]
      tor_lev := D.tor_comm }, hK, rfl, rfl, fun v => D.ι_mem_W _, fun x hx => ?_⟩
  obtain ⟨w, hw⟩ := (hW' x).mp hx
  exact ⟨Multiplicative.toAdd w, hw⟩

end WLocal

namespace Hyp

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}

theorem exists_WData (h : Hyp G A f) (d : Datum A) {V₁ V₂ Vi : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂) :
    Nonempty (WData d Vi (2 ^ f)) := by
  obtain ⟨hWV, hWe, hWc⟩ := hR.property hW
  obtain ⟨K, _, _, _, S, hK, hX, ht, hι, hι'⟩ := WLocal.exists_xSetting h d hR hW
  have hK8 : 8 ≤ Nat.card K := by
    rw [hK]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.three_le
  obtain ⟨W, hWX, hcomm, hsq, hcard, hιW, htW, hor, htc, hfix, honto, huniq⟩ := S.exists_W hK8
  rw [hX] at hWX hor huniq
  rw [ht] at htW hor htc hfix honto
  have htX : d.t ∈ normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ⊓
      centralizer (Vi : Set G) := by
    rw [← hX, ← ht]; exact S.t_mem
  have hcard' : Nat.card W = (2 ^ f) ^ 4 := by rw [hcard, hK]
  have hViW : Vi ≤ W := fun x hx => by
    obtain ⟨v, rfl⟩ := hι' x hx
    exact hιW v
  obtain ⟨X', hX', hX'eq, -⟩ := h.exists_regularNormal d hR hW
  have hNX := hX'.normalizer_le
  rw [hX'eq] at hNX
  have hnormal : normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ≤
      normalizer (W : Set G) := by
    intro n hn
    have hW'X : W.map (MulAut.conj n).toMonoidHom ≤
        normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ⊓ centralizer (Vi : Set G) := by
      rintro _ ⟨w, hw, rfl⟩
      exact (mem_normalizer_iff.mp (hNX hn) w).mp (hWX hw)
    have hc : ∀ a ∈ W.map (MulAut.conj n).toMonoidHom, ∀ b ∈ W.map (MulAut.conj n).toMonoidHom,
        a * b = b * a := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hcomm a ha b hb]
    have hcd : Nat.card (W.map (MulAut.conj n).toMonoidHom) = Nat.card K ^ 4 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hcard]
    have heq := huniq _ hW'X hc hcd
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    rw [← heq]
    exact ⟨w, hw, rfl⟩
  have hlt : Vi < W := by
    refine lt_of_le_of_ne hViW fun heq => ?_
    have h1 := hWc
    rw [heq, hcard'] at h1
    have h2 : (2 ^ f) ^ 2 < (2 ^ f) ^ 4 :=
      Nat.pow_lt_pow_right (Nat.one_lt_two_pow (by have := h.three_le; omega)) (by norm_num)
    omega
  refine ⟨{ W := W
            elem := isElemAbelian_of_forall hcomm fun x hx => by rw [sq]; exact hsq x hx
            card := hcard'
            lt := hlt
            t_not_mem := htW
            t_norm := Subgroup.mem_normalizer_fintype fun x hx => htc x hx
            fix := ?_
            comm_mem := ?_
            comm_onto := ?_
            normal := hnormal
            levi_norm := fun a ha => hnormal (mem_normalizer_adj_of_mem_A d hWV ha)
            sup_le_inf_centralizer := sup_le hWX ((zpowers_le).mpr htX)
            le_sup_of_isPGroup := ?_
            unique := ?_ }⟩
  · refine le_antisymm (fun x hx => ?_) (le_inf hViW fun x hx =>
      mem_centralizer_singleton_iff.mpr (d.V_comm_t (hWV hx)))
    have hxt := mem_centralizer_singleton_iff.mp hx.2
    obtain ⟨v, rfl⟩ := hfix x hx.1 (by rw [mul_assoc d.t x, hxt, ← mul_assoc,
      d.t_mul_self, one_mul, mul_inv_cancel])
    exact hι v
  · intro w hw
    obtain ⟨v, hv⟩ := S.comm_mem w (by rw [hX]; exact hWX hw)
    rw [ht] at hv
    rw [hv]
    exact hι v
  · intro v hv
    obtain ⟨u, rfl⟩ := hι' v hv
    exact honto u
  · intro P _ hP x hx
    rcases hor x (hP hx) with hxW | hxW
    · exact mem_sup_left hxW
    · have e : x = x * d.t * d.t := by rw [mul_assoc, d.t_mul_self, mul_one]
      rw [e]
      exact mul_mem (mem_sup_left hxW) (mem_sup_right (mem_zpowers _))
  · intro W' hW' hc hcd
    refine huniq W' (hW'.trans (sup_le hWX ((zpowers_le).mpr htX))) hc (by rw [hcd, hK])

theorem isPGroup_normalizer_inf_centralizer (h : Hyp G A f) (d : Datum A)
    {V₁ V₂ Vi : Subgroup G} (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂) :
    IsPGroup 2 (normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ⊓
      centralizer (Vi : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, _, S, hK, hX, ht, -, -⟩ := WLocal.exists_xSetting h d hR hW
  have hK8 : 8 ≤ Nat.card K := by
    rw [hK]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.three_le
  obtain ⟨W, -, -, hsq, -, -, -, hor, htc, -, -, -⟩ := S.exists_W hK8
  rw [hX] at hor
  rw [ht] at hor htc
  have hW2 : IsPGroup 2 W := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one, sq]; exact hsq x x.2)⟩
  have ht2 : IsPGroup 2 (zpowers d.t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, d.sector.t_order, pow_one])
  refine (IsPGroup.to_sup_of_normal_left' hW2 ht2 ((zpowers_le).mpr
    (Subgroup.mem_normalizer_fintype fun x hx => htc x hx))).to_le fun x hx => ?_
  rcases hor x hx with hxW | hxW
  · exact mem_sup_left hxW
  · have e : x = x * d.t * d.t := by rw [mul_assoc, d.t_mul_self, mul_one]
    rw [e]
    exact mul_mem (mem_sup_left hxW) (mem_sup_right (mem_zpowers _))

theorem sup_eq (h : Hyp G A f) (d : Datum A) {V₁ V₂ Vi : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂) (w : WData d Vi (2 ^ f)) :
    w.W ⊔ zpowers d.t =
      normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ⊓ centralizer (Vi : Set G) :=
  le_antisymm w.sup_le_inf_centralizer
    (w.le_sup_of_isPGroup _ (h.isPGroup_normalizer_inf_centralizer d hR hW) le_rfl)

end Hyp

namespace WData

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G}
  {q : ℕ}

omit [Finite G] in
theorem mem_sup_iff (w : WData d Vi q) {x : G} :
    x ∈ w.W ⊔ zpowers d.t ↔ x ∈ w.W ∨ x * d.t ∈ w.W := by
  have ht2 := d.t_mul_self
  have htinv : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right ht2
  have hconj : ∀ y ∈ w.W, d.t * y * d.t ∈ w.W := fun y hy => by
    have := (mem_normalizer_iff.mp w.t_norm y).mp hy
    rwa [htinv] at this
  let S : Subgroup G :=
    { carrier := {x | x ∈ w.W ∨ x * d.t ∈ w.W}
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (mul_mem ha hb)
        · exact Or.inr (by rw [mul_assoc]; exact mul_mem ha hb)
        · right
          have e : a * b * d.t = (a * d.t) * (d.t * b * d.t) := by
            rw [show (a * d.t) * (d.t * b * d.t) = a * (d.t * d.t) * b * d.t by group, ht2]
            group
          rw [e]
          exact mul_mem ha (hconj b hb)
        · left
          have e : a * b = (a * d.t) * (d.t * (b * d.t) * d.t) := by
            rw [show (a * d.t) * (d.t * (b * d.t) * d.t) =
              a * (d.t * d.t) * b * (d.t * d.t) by group, ht2]
            group
          rw [e]
          exact mul_mem ha (hconj _ hb)
      one_mem' := Or.inl (one_mem _)
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (inv_mem ha)
        · right
          have e : a⁻¹ * d.t = d.t * (a * d.t)⁻¹ * d.t := by
            rw [_root_.mul_inv_rev, htinv]
            rw [show d.t * (d.t * a⁻¹) * d.t = (d.t * d.t) * a⁻¹ * d.t by group, ht2, one_mul]
          rw [e]
          exact hconj _ (inv_mem ha) }
  constructor
  · intro hx
    have hle : w.W ⊔ zpowers d.t ≤ S := sup_le (fun y hy => Or.inl hy) ((zpowers_le).mpr
      (Or.inr (by rw [ht2]; exact one_mem _)))
    exact hle hx
  · rintro (hx | hx)
    · exact mem_sup_left hx
    · have e : x = x * d.t * d.t := by rw [mul_assoc, ht2, mul_one]
      rw [e]
      exact mul_mem (mem_sup_left hx) (mem_sup_right (mem_zpowers _))

omit [Finite G] in
theorem le_centralizer_t (w : WData d Vi q) : Vi ≤ centralizer ({d.t} : Set G) := by
  rw [← w.fix]
  exact inf_le_right

omit [Finite G] in
theorem le_W (w : WData d Vi q) : Vi ≤ w.W := w.lt.le

omit [Finite G] in
theorem mem_adj_iff (w : WData d Vi q) {x : G} :
    x ∈ Vi ⊔ zpowers d.t ↔ x ∈ Vi ∨ x * d.t ∈ Vi :=
  OddStandard.Seitz77.mem_sup_zpowers_iff
    (fun _ hv => (mem_centralizer_singleton_iff.mp (w.le_centralizer_t hv)))
    d.t_mul_self

omit [Finite G] in
theorem comm_conj (w : WData d Vi q) {n : G}
    (hn : n ∈ normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G)) {x : G} (hx : x ∈ w.W) :
    n * (d.t * x * d.t * x⁻¹) * n⁻¹ =
      d.t * (n * x * n⁻¹) * d.t * (n * x * n⁻¹)⁻¹ := by
  have hnW := w.normal hn
  have hy : n * x * n⁻¹ ∈ w.W := (mem_normalizer_iff.mp hnW x).mp hx
  have ht' : n * d.t * n⁻¹ ∈ Vi ⊔ zpowers d.t :=
    (mem_normalizer_iff.mp hn d.t).mp (mem_sup_right (mem_zpowers _))
  have htW : n * d.t * n⁻¹ ∉ Vi := fun h => w.t_not_mem (by
    have h1 := (mem_normalizer_iff.mp hnW d.t).mpr (w.le_W h)
    exact h1)
  have hvt := (w.mem_adj_iff.mp ht').resolve_left htW
  set v := n * d.t * n⁻¹ * d.t with hv
  have hv' : n * d.t * n⁻¹ = v * d.t := by
    rw [hv, mul_assoc (n * d.t * n⁻¹) d.t d.t, d.t_mul_self, mul_one]
  have hvW := w.le_W hvt
  have hvt' : v * d.t = d.t * v := mem_centralizer_singleton_iff.mp (w.le_centralizer_t hvt)
  have hv2 : v * v = 1 := by rw [← sq]; exact w.elem.2 v hvW
  have htconj : d.t * (n * x * n⁻¹) * d.t ∈ w.W := by
    have := (mem_normalizer_iff.mp w.t_norm _).mp hy
    rwa [inv_eq_of_mul_eq_one_right d.t_mul_self] at this
  have hc : v * (d.t * (n * x * n⁻¹) * d.t) = (d.t * (n * x * n⁻¹) * d.t) * v :=
    comm_of_isElemAbelian w.elem hvW htconj
  calc n * (d.t * x * d.t * x⁻¹) * n⁻¹ =
      (n * d.t * n⁻¹) * (n * x * n⁻¹) * (n * d.t * n⁻¹) * (n * x * n⁻¹)⁻¹ := by group
    _ = v * (d.t * (n * x * n⁻¹) * d.t) * v * (n * x * n⁻¹)⁻¹ := by
      rw [hv', show v * d.t * (n * x * n⁻¹) * (v * d.t) =
        v * (d.t * (n * x * n⁻¹) * (v * d.t)) by group, hvt']
      group
    _ = d.t * (n * x * n⁻¹) * d.t * (n * x * n⁻¹)⁻¹ := by
      rw [hc, mul_assoc _ v v, hv2, mul_one]

omit [Finite G] in
theorem isPGroup_sup (w : WData d Vi q) : IsPGroup 2 (w.W ⊔ zpowers d.t : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW2 : IsPGroup 2 w.W := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]; exact w.elem.2 x x.2)⟩
  have ht2 : IsPGroup 2 (zpowers d.t) := fun x => by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp x.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one, ← hk, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, sq, d.t_mul_self, one_zpow]
  exact IsPGroup.to_sup_of_normal_left' hW2 ht2 ((zpowers_le).mpr w.t_norm)

theorem mem_of_mem_normalizer (w : WData d Vi q) {n : G} (hnC : n ∈ centralizer (Vi : Set G))
    (hnX : n ∈ normalizer ((w.W ⊔ zpowers d.t : Subgroup G) : Set G))
    (hn2 : IsPGroup 2 (zpowers n)) : n ∈ w.W ⊔ zpowers d.t := by
  have hWn : w.W.map (MulAut.conj n).toMonoidHom = w.W := by
    refine w.unique _ ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.mp hnX y).mp (mem_sup_left hy)
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, comm_of_isElemAbelian w.elem ha hb]
    · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, w.card]
  have ht' : n * d.t * n⁻¹ ∈ w.W ⊔ zpowers d.t :=
    (mem_normalizer_iff.mp hnX d.t).mp (mem_sup_right (mem_zpowers _))
  have htW : n * d.t * n⁻¹ ∉ w.W := fun h => by
    rw [← hWn] at h
    obtain ⟨y, hy, hyt⟩ := h
    have hyt' : y = d.t := by
      simpa [MulAut.conj_apply] using hyt
    exact w.t_not_mem (hyt' ▸ hy)
  have hw0 := (w.mem_sup_iff.mp ht').resolve_left htW
  set a := n * d.t * n⁻¹ with ha
  have ha2 : a * a = 1 := by
    rw [ha, show n * d.t * n⁻¹ * (n * d.t * n⁻¹) = n * (d.t * d.t) * n⁻¹ by group, d.t_mul_self]
    group
  have hw02 : a * d.t * (a * d.t) = 1 := by rw [← sq]; exact w.elem.2 _ hw0
  have hw0t : a * d.t ∈ Vi := by
    rw [← w.fix]
    refine ⟨hw0, mem_centralizer_singleton_iff.mpr ?_⟩
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have h1 : d.t * a * d.t = a := by
      calc d.t * a * d.t = a⁻¹ * (a * d.t * (a * d.t)) := by group
        _ = a := by rw [hw02, mul_one, hainv]
    calc a * d.t * d.t = a := by rw [mul_assoc, d.t_mul_self, mul_one]
      _ = d.t * a * d.t := h1.symm
      _ = d.t * (a * d.t) := by group
  have hnE : n ∈ normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun e he => ?_
    rcases w.mem_adj_iff.mp he with he' | he'
    · rw [← mem_centralizer_iff.mp hnC e he', mul_inv_cancel_right]
      exact mem_sup_left he'
    · have e1 : n * e * n⁻¹ = (n * (e * d.t) * n⁻¹) * a := by
        rw [ha]
        calc n * e * n⁻¹ = n * (e * (d.t * d.t)) * n⁻¹ := by rw [d.t_mul_self, mul_one]
          _ = _ := by group
      rw [e1, ← mem_centralizer_iff.mp hnC _ he', mul_inv_cancel_right]
      have e2 : a = (a * d.t) * d.t := by rw [mul_assoc, d.t_mul_self, mul_one]
      rw [e2]
      exact mul_mem (mem_sup_left he') (mul_mem (mem_sup_left hw0t) (mem_sup_right (mem_zpowers _)))
  exact w.le_sup_of_isPGroup _ hn2 (zpowers_le.mpr ⟨hnE, hnC⟩) (mem_zpowers n)

theorem isSylowOf_centralizer (w : WData d Vi q) :
    IsSylowOf 2 (w.W ⊔ zpowers d.t : Subgroup G) (centralizer (Vi : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXC : w.W ⊔ zpowers d.t ≤ centralizer (Vi : Set G) :=
    w.sup_le_inf_centralizer.trans inf_le_right
  have hX2 : IsPGroup 2 (w.W ⊔ zpowers d.t : Subgroup G) := w.isPGroup_sup
  obtain ⟨T, hT⟩ := (hX2.comap_subtype (K := centralizer (Vi : Set G))).exists_le_sylow
  refine ⟨T, ?_⟩
  set T' : Subgroup G := (T : Subgroup (centralizer (Vi : Set G))).map
    (centralizer (Vi : Set G)).subtype with hT'
  have hXT : w.W ⊔ zpowers d.t ≤ T' := fun x hx =>
    ⟨⟨x, hXC hx⟩, hT (mem_subgroupOf.mpr hx), rfl⟩
  by_contra hne
  have hlt : w.W ⊔ zpowers d.t < T' := lt_of_le_of_ne hXT (Ne.symm hne)
  have hT'2 : IsPGroup 2 T' := T.isPGroup'.map _
  have : Group.IsNilpotent T' := hT'2.isNilpotent
  have hlt' : (w.W ⊔ zpowers d.t).subgroupOf T' < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hlt.not_ge (subgroupOf_eq_top.mp h)
  obtain ⟨x, hx, hxX⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt')
  rw [← subgroupOf_normalizer_eq hlt.le] at hx
  exact hxX (w.mem_of_mem_normalizer (map_subtype_le _ x.2) hx (hT'2.to_le (zpowers_le.mpr x.2)))

end WData

end CFSG.LocalAnalysis.EvenBN.LinearThree

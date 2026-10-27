module

public import CFSG.GH74.Generic.S3.Nontriv1
public import CFSG.GH74.Generic.S3.L3Class
public import CFSG.GH74.Generic.S3.NbrR

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.Generic.S1 (barConj barConj_xbar barConj_barOf)

section Basic

variable {G : Type} [Group G] [Finite G]

theorem eq_of_commuting_involutions {x : G} {K : Subgroup (CentralizerBar x)} {M : Subgroup G}
    (hx : orderOf x = 2) (honly : OnlyInvX x K) (himg : imgBar x M = K) {a b : G}
    (ha : a ∈ centralizer ({x} : Set G)) (hb : b ∈ centralizer ({x} : Set G))
    (haM : a ∈ centralizer (M : Set G)) (hbM : b ∈ centralizer (M : Set G))
    (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a * b = b * a) :
    a = b := by
  have key : ∀ c (hcz : c ∈ centralizer ({x} : Set G)), c ∈ centralizer (M : Set G) → c * c = 1 →
      c ≠ 1 → proj x ⟨c, hcz⟩ = xbar x := by
    intro c hcz hcM hc2 hc1
    have hcb1 : proj x ⟨c, hcz⟩ ≠ 1 := fun h => hc1 (S45.eq_one_of_proj_eq_one_of_sq hcz h hc2)
    have hcb2 : proj x ⟨c, hcz⟩ * proj x ⟨c, hcz⟩ = 1 := by
      rw [← map_mul]
      have : (⟨c, hcz⟩ : ↥(centralizer ({x} : Set G))) * ⟨c, hcz⟩ = 1 := Subtype.ext hc2
      rw [this, map_one]
    have hord : orderOf (proj x ⟨c, hcz⟩) = 2 := orderOf_eq_prime (by rw [sq]; exact hcb2) hcb1
    have hcent : proj x ⟨c, hcz⟩ ∈ centralizer (K : Set (CentralizerBar x)) := by
      rw [mem_centralizer_iff]
      intro l hl
      have hl' : l ∈ imgBar x M := by rw [himg]; exact hl
      obtain ⟨g, hg, rfl⟩ := mem_imgBar.1 hl'
      have h1 : (g : G) * c = c * (g : G) := mem_centralizer_iff.1 hcM (g : G) hg
      have h2 : g * ⟨c, hcz⟩ = ⟨c, hcz⟩ * g := Subtype.ext h1
      rw [← map_mul, ← map_mul, h2]
    exact honly _ hcent hord
  have h1 := key a ha haM ha2 ha1
  have h2 := key b hb hbM hb2 hb1
  have habz : a * b ∈ centralizer ({x} : Set G) := (centralizer ({x} : Set G)).mul_mem ha hb
  have hab2 : (a * b) * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  have himgab : proj x ⟨a * b, habz⟩ = 1 := by
    have : (⟨a * b, habz⟩ : ↥(centralizer ({x} : Set G))) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul, h1, h2]
    exact xbar_mul_self hx
  have h3 := S45.eq_one_of_proj_eq_one_of_sq habz himgab hab2
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  calc a = a * b * b⁻¹ := by group
    _ = b := by rw [h3, one_mul, hb']

omit [Finite G] in
theorem exists_split_of_inner {Iw : Subgroup G} (hodd : Odd (Nat.card ↥(center ↥Iw))) {x' a : G}
    (hx' : x' * x' = 1) (ha : a ∈ Iw) (hact : ∀ m ∈ Iw, x' * m * x'⁻¹ = a * m * a⁻¹) :
    ∃ a₂ ∈ Iw, ∃ c₂ ∈ centralizer (Iw : Set G), a₂ * a₂ = 1 ∧ c₂ * c₂ = 1 ∧ x' = a₂ * c₂ := by
  set c : G := a⁻¹ * x' with hc
  have hcC : c ∈ centralizer (Iw : Set G) := by
    rw [mem_centralizer_iff]
    intro m hm
    have h1 := hact m hm
    have h2 : x' * m = a * m * a⁻¹ * x' := by rw [← h1]; group
    calc m * c = m * (a⁻¹ * x') := rfl
      _ = a⁻¹ * (a * m * a⁻¹ * x') := by group
      _ = a⁻¹ * (x' * m) := by rw [h2]
      _ = c * m := by rw [hc]; group
  have hxac : x' = a * c := by rw [hc]; group
  have hac : a * c = c * a := mem_centralizer_iff.1 hcC a ha
  have hsq : a * a * (c * c) = 1 := by
    calc a * a * (c * c) = a * c * (a * c) := by
          calc a * a * (c * c) = a * (a * c) * c := by group
            _ = a * (c * a) * c := by rw [hac]
            _ = a * c * (a * c) := by group
      _ = x' * x' := by rw [← hxac]
      _ = 1 := hx'
  have hcc : c * c = (a * a)⁻¹ := eq_inv_of_mul_eq_one_right hsq
  have hzC : a * a ∈ centralizer (Iw : Set G) := by
    have : a * a = (c * c)⁻¹ := by rw [hcc, inv_inv]
    rw [this]
    exact Subgroup.inv_mem _ ((centralizer (Iw : Set G)).mul_mem hcC hcC)
  have hzI : a * a ∈ Iw := Iw.mul_mem ha ha
  have hzcen : (⟨a * a, hzI⟩ : ↥Iw) ∈ center ↥Iw := by
    rw [Subgroup.mem_center_iff]
    intro m
    exact Subtype.ext (mem_centralizer_iff.1 hzC m m.2)
  have hodd_ord : Odd (orderOf (a * a)) := by
    have h1 : orderOf (⟨⟨a * a, hzI⟩, hzcen⟩ : ↥(center ↥Iw)) ∣ Nat.card ↥(center ↥Iw) :=
      orderOf_dvd_natCard _
    have h2 : orderOf (⟨⟨a * a, hzI⟩, hzcen⟩ : ↥(center ↥Iw)) = orderOf (a * a) := by
      have e1 := Subgroup.orderOf_coe (⟨⟨a * a, hzI⟩, hzcen⟩ : ↥(center ↥Iw))
      have e2 := Subgroup.orderOf_coe (⟨a * a, hzI⟩ : ↥Iw)
      exact e1.symm.trans e2.symm
    rw [h2] at h1
    exact Odd.of_dvd_nat hodd h1
  set o := orderOf (a * a) with ho
  have hao : a ^ o * a ^ o = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, sq]
    exact pow_orderOf_eq_one (a * a)
  have hco : c ^ o * c ^ o = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, sq, hcc, inv_pow]
    rw [pow_orderOf_eq_one (a * a), inv_one]
  refine ⟨a ^ o, Subgroup.pow_mem _ ha _, c ^ o, Subgroup.pow_mem _ hcC _, hao, hco, ?_⟩
  obtain ⟨k, hk⟩ := hodd_ord
  have hxo : x' ^ o = x' := by
    rw [hk, pow_succ, pow_mul, sq, hx', one_pow, one_mul]
  calc x' = x' ^ o := hxo.symm
    _ = (a * c) ^ o := by rw [← hxac]
    _ = a ^ o * c ^ o := (Commute.mul_pow hac) o

theorem NbrData.exists_bridge {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}
    {K : Subgroup (CentralizerBar x)} (hset : S3Setup G x K) (hnd : NbrData G t p f x y Iw Iv) :
    ∃ g : G, g * x * g⁻¹ ≠ x ∧ (g * x * g⁻¹) * x = x * (g * x * g⁻¹) ∧
      (g * x * g⁻¹) * y = y * (g * x * g⁻¹) := by
  obtain ⟨g, hne, hcomm⟩ := exists_commuting_conj_ne hset.simple hset.nonab hset.inv
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hset.inv, pow_two] at this
  have hu2 : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hxx]; group
  have huC : g * x * g⁻¹ ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hcomm
  have hnorm : ∀ m ∈ Iw, (g * x * g⁻¹) * m * (g * x * g⁻¹)⁻¹ ∈ Iw := fun m hm => by
    have := hnd.comp_w.conj _ huC m hm
    simpa using this
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hnd.y_inv, pow_two] at this
  have hy1 : y ≠ 1 := by
    intro h
    have := hnd.y_inv
    rw [h, orderOf_one] at this
    omega
  have hyIw : y ∈ Iw := hnd.Iv_le hnd.y_Iv
  have heven : 2 ∣ Nat.card Iw := by
    have h1 : orderOf (⟨y, hyIw⟩ : ↥Iw) ∣ Nat.card Iw := orderOf_dvd_natCard _
    have h2 : orderOf (⟨y, hyIw⟩ : ↥Iw) = 2 := by rw [← hnd.y_inv, ← Subgroup.orderOf_coe]
    rwa [h2] at h1
  have hu2' : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := hu2
  have hnorm' : ∀ m ∈ Iw, (g * x * g⁻¹) * m * (g * x * g⁻¹)⁻¹ ∈ Iw := hnorm
  obtain ⟨t', htI, ht2, ht1, htu⟩ := exists_involution_mem_centralizer hu2' hnorm' heven
  obtain ⟨h, hhI, hht⟩ := b_L3_class G t p f hnd.tag hnd.prime.1 hnd.prime.2.1 hnd.prime.2.2 Iw
    hnd.comp_w.1.isQuasisimple hnd.odd_w hnd.model_w y hyIw t' htI hy2 hy1 ht2 ht1
  have hxh : h * x = x * h :=
    Subgroup.mem_centralizer_singleton_iff.1 (hnd.comp_w.1.1 hhI)
  have hxh' : x * h⁻¹ = h⁻¹ * x := by
    calc x * h⁻¹ = h⁻¹ * (h * x) * h⁻¹ := by group
      _ = h⁻¹ * (x * h) * h⁻¹ := by rw [hxh]
      _ = h⁻¹ * x := by group
  refine ⟨h⁻¹ * g, ?_, ?_, ?_⟩
  · intro hx'
    apply hne
    have h1 : (h⁻¹ * g) * x * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * x * g⁻¹) * h := by group
    rw [h1] at hx'
    calc g * x * g⁻¹ = h * (h⁻¹ * (g * x * g⁻¹) * h) * h⁻¹ := by group
      _ = h * x * h⁻¹ := by rw [hx']
      _ = x := by rw [hxh]; group
  · have h1 : (h⁻¹ * g) * x * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * x * g⁻¹) * h := by group
    rw [h1]
    calc h⁻¹ * (g * x * g⁻¹) * h * x = h⁻¹ * (g * x * g⁻¹) * (h * x) := by group
      _ = h⁻¹ * ((g * x * g⁻¹) * x) * h := by rw [hxh]; group
      _ = h⁻¹ * (x * (g * x * g⁻¹)) * h := by rw [hcomm]
      _ = x * (h⁻¹ * (g * x * g⁻¹) * h) := by rw [← mul_assoc, ← mul_assoc, ← hxh']; group
  · have h1 : (h⁻¹ * g) * x * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * x * g⁻¹) * h := by group
    rw [h1]
    have h2 : (g * x * g⁻¹) * (h * y * h⁻¹) = (h * y * h⁻¹) * (g * x * g⁻¹) := by
      rw [hht]; exact htu.symm
    calc h⁻¹ * (g * x * g⁻¹) * h * y = h⁻¹ * ((g * x * g⁻¹) * (h * y * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * y * h⁻¹) * (g * x * g⁻¹)) * h := by rw [h2]
      _ = y * (h⁻¹ * (g * x * g⁻¹) * h) := by group

end Basic

end CFSG.GH74.Generic.S3

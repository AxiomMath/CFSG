module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L114A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A2Gen

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G]

structure Sec11dCl (D Y : Subgroup G) (t z : G) : Prop where
  cyc : IsCyclic ↥Y
  le : Y ≤ D
  idx : Y.relIndex D = 2
  p2 : IsPGroup 2 ↥D
  t_mem : t ∈ D
  z_mem : z ∈ D
  t_sq : t * t = 1
  z_sq : z * z = 1
  t_ne : t ≠ 1
  z_ne : z ≠ 1
  tz_ne : t ≠ z
  tz_comm : t * z = z * t
  z_cent : ∀ d ∈ D, d * z = z * d
  cent : ∀ d ∈ D, d * t = t * d → d ∈ zpowers t ⊔ zpowers z
  big : ¬ D ≤ zpowers t ⊔ zpowers z

namespace Sec11dCl

variable {D Y : Subgroup G} {t z : G} (h : Sec11dCl D Y t z)

include h

theorem idx2 {a b : G} (ha : a ∈ D) (hb : b ∈ D) (haY : a ∉ Y) (hbY : b ∉ Y) : a⁻¹ * b ∈ Y :=
  sec10A2_idx2_mul h.idx ha hb haY hbY

theorem mem_or {g d : G} (hg : g ∈ D) (hgY : g ∉ Y) (hd : d ∈ D) : d ∈ Y ∨ g⁻¹ * d ∈ Y := by
  by_cases hdY : d ∈ Y
  · exact Or.inl hdY
  · exact Or.inr (h.idx2 hg hd hgY hdY)

theorem normal {d y : G} (hd : d ∈ D) (hy : y ∈ Y) : d * y * d⁻¹ ∈ Y := by
  by_cases hdY : d ∈ Y
  · exact Y.mul_mem (Y.mul_mem hdY hy) (Y.inv_mem hdY)
  · have h1 : d * y ∉ Y := fun h' => hdY (by simpa using Y.mul_mem h' (Y.inv_mem hy))
    have h2 : (d * y)⁻¹ ∉ Y := fun h' => h1 (by simpa using Y.inv_mem h')
    have h3 : d⁻¹ ∉ Y := fun h' => hdY (by simpa using Y.inv_mem h')
    have := h.idx2 (D.inv_mem (D.mul_mem hd (h.le hy))) (D.inv_mem hd) h2 h3
    simpa using this

theorem comm_Y {a b : G} (ha : a ∈ Y) (hb : b ∈ Y) : a * b = b * a := by
  haveI := h.cyc
  exact congrArg Subtype.val
    ((inferInstance : IsMulCommutative ↥Y).is_comm.comm (⟨a, ha⟩ : ↥Y) ⟨b, hb⟩)

theorem z_mem_Y : z ∈ Y := by
  by_contra hzY
  apply h.big
  intro d hd
  apply h.cent d hd
  have hcz : ∀ e ∈ D, Commute z e := fun e he => (h.z_cent e he).symm
  have key : ∀ e ∈ D, ∃ y ∈ Y, e = y ∨ e = z * y := by
    intro e he
    rcases h.mem_or h.z_mem hzY he with hY | hY
    · exact ⟨e, hY, Or.inl rfl⟩
    · exact ⟨z⁻¹ * e, hY, Or.inr (by group)⟩
  obtain ⟨y, hy, hd'⟩ := key d hd
  obtain ⟨y', hy', ht'⟩ := key t h.t_mem
  have hyy : Commute y y' := h.comm_Y hy hy'
  have hzy : Commute z y := hcz y (h.le hy)
  have hzy' : Commute z y' := hcz y' (h.le hy')
  have hzz : Commute z z := Commute.refl z
  have hc : Commute d t := by
    rcases hd' with hd' | hd' <;> rcases ht' with ht' | ht' <;> rw [hd', ht']
    · exact hyy
    · exact Commute.mul_right hzy.symm hyy
    · exact Commute.mul_left hzy' hyy
    · exact Commute.mul_left (Commute.mul_right hzz hzy') (Commute.mul_right hzy.symm hyy)
  exact hc.eq

theorem t_not_mem_Y : t ∉ Y := by
  intro htY
  apply h.big
  have hW : zpowers t ⊔ zpowers z ≤ D := sup_le (zpowers_le.2 h.t_mem) (zpowers_le.2 h.z_mem)
  have hYW : Y ≤ zpowers t ⊔ zpowers z := fun y hy => h.cent y (h.le hy) (h.comm_Y hy htY)
  have hW4 : Nat.card ↥(zpowers t ⊔ zpowers z) = 4 :=
    sec11L114_pair_card h.t_sq h.z_sq h.tz_comm h.t_ne h.z_ne h.tz_ne
  have hD2Y : Nat.card ↥D = 2 * Nat.card ↥Y := by
    have h1 := Subgroup.relIndex_mul_card (H := Y) (K := D)
    rw [inf_of_le_left h.le, h.idx] at h1
    exact h1.symm
  have hY2 : Nat.card ↥Y ≤ 2 := by
    haveI := h.cyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥Y)
    have hg2 : (g : G) * (g : G) = 1 :=
      sec11L114_pair_sq h.t_sq h.z_sq h.tz_comm (hYW g.2)
    have hg2' : g ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hg2)
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg2')
  have hDle : Nat.card ↥D ≤ 4 := by omega
  have heq : zpowers t ⊔ zpowers z = D :=
    Subgroup.eq_of_le_of_card_ge hW (by rw [hW4]; exact hDle)
  exact le_of_eq heq.symm

def phi : ↥Y →* ↥Y where
  toFun y := ⟨(y : G) * t * (y : G)⁻¹ * t⁻¹, by
    have e : (y : G) * t * (y : G)⁻¹ * t⁻¹ = (y : G) * (t * (y : G)⁻¹ * t⁻¹) := by group
    rw [e]
    exact Y.mul_mem y.2 (h.normal h.t_mem (Y.inv_mem y.2))⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    show ((a : G) * (b : G)) * t * ((a : G) * (b : G))⁻¹ * t⁻¹ =
      ((a : G) * t * (a : G)⁻¹ * t⁻¹) * ((b : G) * t * (b : G)⁻¹ * t⁻¹)
    have hA : t * (a : G)⁻¹ * t⁻¹ ∈ Y := h.normal h.t_mem (Y.inv_mem a.2)
    have hB : t * (b : G)⁻¹ * t⁻¹ ∈ Y := h.normal h.t_mem (Y.inv_mem b.2)
    have hAB := h.comm_Y hA hB
    have hAb := h.comm_Y hA b.2
    calc ((a : G) * (b : G)) * t * ((a : G) * (b : G))⁻¹ * t⁻¹
        = (a : G) * (b : G) * (t * (b : G)⁻¹ * t⁻¹) * (t * (a : G)⁻¹ * t⁻¹) := by group
      _ = (a : G) * (b : G) * ((t * (b : G)⁻¹ * t⁻¹) * (t * (a : G)⁻¹ * t⁻¹)) := by group
      _ = (a : G) * (b : G) * ((t * (a : G)⁻¹ * t⁻¹) * (t * (b : G)⁻¹ * t⁻¹)) := by rw [hAB]
      _ = (a : G) * ((t * (a : G)⁻¹ * t⁻¹) * (b : G)) * (t * (b : G)⁻¹ * t⁻¹) := by
        rw [hAb]; group
      _ = ((a : G) * t * (a : G)⁻¹ * t⁻¹) * ((b : G) * t * (b : G)⁻¹ * t⁻¹) := by group

theorem ker_le (y : ↥Y) (hy : h.phi y = 1) : (y : G) = 1 ∨ (y : G) = z := by
  have hy' : (y : G) * t * (y : G)⁻¹ * t⁻¹ = 1 := congrArg Subtype.val hy
  have hcomm : (y : G) * t = t * (y : G) :=
    mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hy')
  have hmem : (y : G) ∈ zpowers t ⊔ zpowers z := h.cent y (h.le y.2) hcomm
  rcases (sec11L114_pair_mem h.t_sq h.z_sq h.tz_comm).1 hmem with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact absurd (h1 ▸ y.2) h.t_not_mem_Y
  · exact Or.inr h1
  · exfalso
    apply h.t_not_mem_Y
    have e : t = (y : G) * z := by rw [h1, mul_assoc, h.z_sq, mul_one]
    rw [e]
    exact Y.mul_mem y.2 h.z_mem_Y

theorem ker_card : Nat.card ↥(h.phi).ker ≤ 2 := by
  have hz : (⟨z, h.z_mem_Y⟩ : ↥Y) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using h.z_sq)
  have hle : (h.phi).ker ≤ zpowers (⟨z, h.z_mem_Y⟩ : ↥Y) := by
    intro y hy
    rcases h.ker_le y hy with h1 | h1
    · have e : y = 1 := Subtype.ext h1
      rw [e]
      exact one_mem _
    · have e : y = ⟨z, h.z_mem_Y⟩ := Subtype.ext h1
      rw [e]
      exact mem_zpowers _
  calc Nat.card ↥(h.phi).ker ≤ Nat.card ↥(zpowers (⟨z, h.z_mem_Y⟩ : ↥Y)) :=
        Subgroup.card_le_of_le hle
    _ = orderOf (⟨z, h.z_mem_Y⟩ : ↥Y) := Nat.card_zpowers _
    _ ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hz)

theorem range_index_dvd : (h.phi).range.index ∣ 2 := by
  have h1 := Subgroup.card_ker_mul_card_range h.phi
  have h2 := Subgroup.card_mul_index (h.phi).range
  have hpos : 0 < Nat.card ↥(h.phi).range := Nat.card_pos
  have h3 : Nat.card ↥(h.phi).ker = (h.phi).range.index := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, mul_comm (h.phi).range.index, h2]
  have h4 : (h.phi).range.index ≤ 2 := h3 ▸ h.ker_card
  have h5 : 0 < (h.phi).range.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  exact (Nat.dvd_prime Nat.prime_two).mpr (by omega)

theorem range_mul (c c' : ↥Y) (hc : c ∉ (h.phi).range) (hc' : c' ∉ (h.phi).range) :
    c⁻¹ * c' ∈ (h.phi).range := by
  rcases (Nat.dvd_prime Nat.prime_two).mp h.range_index_dvd with h1 | h1
  · exfalso
    apply hc
    rw [Subgroup.index_eq_one.mp h1]
    exact Subgroup.mem_top _
  · exact (Subgroup.mul_mem_iff_of_index_two h1).mpr
      ⟨fun hh => absurd (inv_mem_iff.mp hh) hc, fun hh => absurd hh hc'⟩

theorem range_sq (c : ↥Y) : c * c ∈ (h.phi).range := by
  rcases (Nat.dvd_prime Nat.prime_two).mp h.range_index_dvd with h1 | h1
  · rw [Subgroup.index_eq_one.mp h1]
    exact Subgroup.mem_top _
  · exact Subgroup.mul_self_mem_of_index_two h1 c

theorem mul_t_mem {u : G} (hu : u ∈ D) (huY : u ∉ Y) : u * t⁻¹ ∈ Y := by
  have hu' : u⁻¹ ∉ Y := fun h' => huY (by simpa using Y.inv_mem h')
  have ht' : t⁻¹ ∉ Y := fun h' => h.t_not_mem_Y (by simpa using Y.inv_mem h')
  have := h.idx2 (D.inv_mem hu) (D.inv_mem h.t_mem) hu' ht'
  simpa using this

theorem not_mem_range {u : G} (hu : u ∈ D) (huY : u ∉ Y)
    (hut : ∀ d ∈ D, u ≠ d * t * d⁻¹) :
    (⟨u * t⁻¹, h.mul_t_mem hu huY⟩ : ↥Y) ∉ (h.phi).range := by
  rintro ⟨y, hy⟩
  have h1 : (y : G) * t * (y : G)⁻¹ * t⁻¹ = u * t⁻¹ := congrArg Subtype.val hy
  exact hut y (h.le y.2) (mul_right_cancel h1).symm

theorem conj_of_not_cl {u u' : G} (hu : u ∈ D) (huY : u ∉ Y) (hut : ∀ d ∈ D, u ≠ d * t * d⁻¹)
    (hu' : u' ∈ D) (hu'Y : u' ∉ Y) (hut' : ∀ d ∈ D, u' ≠ d * t * d⁻¹) :
    ∃ d ∈ D, u' = d * u * d⁻¹ := by
  obtain ⟨y, hy⟩ := h.range_mul ⟨u * t⁻¹, h.mul_t_mem hu huY⟩ ⟨u' * t⁻¹, h.mul_t_mem hu' hu'Y⟩
    (h.not_mem_range hu huY hut) (h.not_mem_range hu' hu'Y hut')
  have h1 : (y : G) * t * (y : G)⁻¹ * t⁻¹ = (u * t⁻¹)⁻¹ * (u' * t⁻¹) := congrArg Subtype.val hy
  refine ⟨y, h.le y.2, ?_⟩
  have hcy : (u * t⁻¹) * (y : G) = (y : G) * (u * t⁻¹) := h.comm_Y (h.mul_t_mem hu huY) y.2
  have h2 : (y : G) * t * (y : G)⁻¹ = (u * t⁻¹)⁻¹ * (u' * t⁻¹) * t :=
    mul_inv_eq_iff_eq_mul.mp h1
  calc u' = (u * t⁻¹) * ((u * t⁻¹)⁻¹ * (u' * t⁻¹) * t) := by group
    _ = (u * t⁻¹) * ((y : G) * t * (y : G)⁻¹) := by rw [h2]
    _ = ((u * t⁻¹) * (y : G)) * t * (y : G)⁻¹ := by group
    _ = ((y : G) * (u * t⁻¹)) * t * (y : G)⁻¹ := by rw [hcy]
    _ = (y : G) * u * (y : G)⁻¹ := by group

theorem gen_of_not_cl {u : G} (hu : u ∈ D) (huY : u ∉ Y) (hut : ∀ d ∈ D, u ≠ d * t * d⁻¹) :
    zpowers t ⊔ zpowers u = D := by
  set c : ↥Y := ⟨u * t⁻¹, h.mul_t_mem hu huY⟩ with hc
  have hcM : c ∉ (h.phi).range := h.not_mem_range hu huY hut
  haveI := h.cyc
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := ↥Y)
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp
    ((mem_powers_iff_mem_zpowers (x := r) (y := c)).mpr (hr c))
  have hjodd : Odd j := by
    rcases Nat.even_or_odd j with he | ho
    · exfalso
      obtain ⟨m, hm⟩ := he
      apply hcM
      rw [← hj, hm, pow_add]
      exact h.range_sq _
    · exact ho
  have hY2 : IsPGroup 2 ↥Y := h.p2.to_le h.le
  obtain ⟨n, hn⟩ := hY2.exists_card_eq
  have hord : orderOf r = Nat.card ↥Y := orderOf_eq_card_of_forall_mem_zpowers hr
  have hcop : Nat.Coprime (orderOf r) j := by
    rw [hord, hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hjodd)
  have hordc : orderOf c = Nat.card ↥Y := by
    rw [← hj, Nat.Coprime.orderOf_pow hcop, hord]
  have htop : zpowers c = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hordc])
  have htu : t ∈ zpowers t ⊔ zpowers u := mem_sup_left (mem_zpowers t)
  have huu : u ∈ zpowers t ⊔ zpowers u := mem_sup_right (mem_zpowers u)
  have hcu : u * t⁻¹ ∈ zpowers t ⊔ zpowers u := Subgroup.mul_mem _ huu (Subgroup.inv_mem _ htu)
  have hYle : Y ≤ zpowers t ⊔ zpowers u := by
    intro y hy
    have hy' : (⟨y, hy⟩ : ↥Y) ∈ zpowers c := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'
    have hk' : (u * t⁻¹) ^ k = y := congrArg Subtype.val hk
    rw [← hk']
    exact Subgroup.zpow_mem _ hcu k
  refine le_antisymm (sup_le (zpowers_le.2 h.t_mem) (zpowers_le.2 hu)) (fun d hd => ?_)
  by_cases hdY : d ∈ Y
  · exact hYle hdY
  · have h1 : d * t⁻¹ ∈ Y := h.mul_t_mem hd hdY
    have e : d = (d * t⁻¹) * t := by group
    rw [e]
    exact Subgroup.mul_mem _ (hYle h1) htu

theorem not_mem_Y {u : G} (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ z) : u ∉ Y := by
  intro huY
  haveI := h.cyc
  classical
  haveI : Fintype ↥Y := Fintype.ofFinite _
  have hsq : ∀ x : G, x * x = 1 → x ^ 2 = 1 := fun x hx => by rw [pow_two]; exact hx
  let a : ↥Y := ⟨u, huY⟩
  let b : ↥Y := ⟨z, h.z_mem_Y⟩
  have ha2 : a ^ 2 = 1 := Subtype.ext (hsq u hu2)
  have hb2 : b ^ 2 = 1 := Subtype.ext (hsq z h.z_sq)
  have hne1 : (1 : ↥Y) ≠ b := fun e => h.z_ne (congrArg Subtype.val e).symm
  have hne2 : (1 : ↥Y) ≠ a := fun e => hu1 (congrArg Subtype.val e).symm
  have hne3 : b ≠ a := fun e => huz (congrArg Subtype.val e).symm
  have hcard : ({1, b, a} : Finset ↥Y).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, b, a, hne1, hne2, hne3, rfl⟩
  have hsub : ({1, b, a} : Finset ↥Y) ⊆ Finset.univ.filter (fun x : ↥Y => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · exact hb2
    · exact ha2
  have hle := IsCyclic.card_pow_eq_one_le (α := ↥Y) (n := 2) (by norm_num)
  have := Finset.card_le_card hsub
  omega

end Sec11dCl

end CFSG.OddStandard.SmallF3.Omega

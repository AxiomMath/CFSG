module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section ZCtx

variable {G : Type} [Group G]

theorem pow_four_eq (a : G) : a ^ 4 = (a * a) * (a * a) := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

structure ZCtx (K Ki : Subgroup G) (t i : G) : Prop where
  t_sq : t * t = 1
  i_sq : i * i = 1
  ti : t * i = i * t
  i_ne_one : i ≠ 1
  Ki_le_Ci : Ki ≤ Subgroup.centralizer ({i} : Set G)
  K_le : K ≤ Ki
  K_le_Ct : K ≤ Subgroup.centralizer ({t} : Set G)
  tN : t ∈ Subgroup.normalizer (Ki : Set G)
  not_le : ¬ Ki ≤ Subgroup.centralizer ({t} : Set G)
  z2 : IsPGroup 2 (Subgroup.center ↥Ki)
  card4 : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer ({t} : Set G) →
    P ≤ Subgroup.centralizer (K : Set G) → P ≤ Subgroup.centralizer ({i} : Set G) →
      Nat.card P ≤ 4
  four : Nat.card (Subgroup.closure ({t, i} : Set G)) = 4
  noconj : ∀ g : G, g⁻¹ * t * g ≠ t * i

namespace ZCtx

variable {K Ki : Subgroup G} {t i : G} (c : ZCtx K Ki t i)

include c

theorem iinv : i⁻¹ = i := inv_eq_of_mul_eq_one_right c.i_sq

theorem i_cK : i ∈ Subgroup.centralizer (K : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (c.Ki_le_Ci (c.K_le hk))

theorem t_cK : t ∈ Subgroup.centralizer (K : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (c.K_le_Ct hk)

theorem z_comm_i {z : G} (hz : z ∈ centerOf Ki) : z * i = i * z :=
  Subgroup.mem_centralizer_singleton_iff.mp (c.Ki_le_Ci hz.1)

theorem z_cK {z : G} (hz : z ∈ centerOf Ki) : z ∈ Subgroup.centralizer (K : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hk => Subgroup.mem_centralizer_iff.mp hz.2 _ (c.K_le hk)

theorem mem_closure_cases {x : G} (hx : x ∈ Subgroup.closure ({t, i} : Set G)) :
    x = 1 ∨ x = t ∨ x = i ∨ x = t * i :=
  mem_closure_pair_of_involutions c.t_sq c.i_sq c.ti hx

theorem tconj_mem {z : G} (hz : z ∈ centerOf Ki) : t⁻¹ * z * t ∈ centerOf Ki := by
  have hN : ∀ y ∈ Ki, t⁻¹ * y * t ∈ Ki := fun y hy => by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Ki : Set G)).inv_mem c.tN) y).mp hy
    simpa using this
  refine ⟨hN z hz.1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hy' : t * y * t⁻¹ ∈ Ki := by
    have := (Subgroup.mem_normalizer_iff.mp c.tN y).mp hy
    exact this
  have h1 := Subgroup.mem_centralizer_iff.mp hz.2 _ hy'
  calc y * (t⁻¹ * z * t) = t⁻¹ * ((t * y * t⁻¹) * z) * t := by group
    _ = t⁻¹ * (z * (t * y * t⁻¹)) * t := by rw [h1]
    _ = (t⁻¹ * z * t) * y := by group

theorem closure_le_centralizers :
    Subgroup.closure ({t, i} : Set G) ≤ Subgroup.centralizer ({t} : Set G) ∧
      Subgroup.closure ({t, i} : Set G) ≤ Subgroup.centralizer (K : Set G) ∧
      Subgroup.closure ({t, i} : Set G) ≤ Subgroup.centralizer ({i} : Set G) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [Subgroup.closure_le] <;> intro x hx <;>
    rcases hx with rfl | hx
  · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · rw [Set.mem_singleton_iff.mp hx]
    exact Subgroup.mem_centralizer_singleton_iff.mpr c.ti.symm
  · exact c.t_cK
  · rw [Set.mem_singleton_iff.mp hx]; exact c.i_cK
  · exact Subgroup.mem_centralizer_singleton_iff.mpr c.ti
  · rw [Set.mem_singleton_iff.mp hx]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl

variable [Finite G]

theorem bound_w {w : G} (hwt : w * t = t * w) (hwi : w * i = i * w)
    (hwK : w ∈ Subgroup.centralizer (K : Set G)) (hw4 : w ^ 4 = 1)
    (hw : w ∉ Subgroup.closure ({t, i} : Set G)) : False := by
  set R : Subgroup G := Subgroup.closure ({t, i} : Set G) with hR
  have hRp : IsPGroup 2 R := IsPGroup.of_card (n := 2) (by rw [hR, c.four]; norm_num)
  have hord : orderOf w ∣ 2 ^ 2 := by simpa using orderOf_dvd_of_pow_eq_one hw4
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hwp : IsPGroup 2 (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hcomm : ∀ x : G, w * x = x * w →
      x ∈ Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hy)
    exact (Commute.zpow_left (show Commute w x from hx) n).eq
  have hRN : R ≤ Subgroup.normalizer ((Subgroup.zpowers w : Subgroup G) : Set G) := by
    rw [hR, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact Subgroup.centralizer_le_normalizer _ (hcomm _ hwt)
    · rw [Set.mem_singleton_iff.mp hx]
      exact Subgroup.centralizer_le_normalizer _ (hcomm _ hwi)
  have hQp : IsPGroup 2 (R ⊔ Subgroup.zpowers w : Subgroup G) := hRp.to_sup_of_normal_right' hwp hRN
  obtain ⟨hRt, hRK, hRi⟩ := c.closure_le_centralizers
  have hwC : ∀ {x : G}, x * w = w * x → w ∈ Subgroup.centralizer ({x} : Set G) := fun {x} hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr hx.symm
  have h1 := c.card4 (R ⊔ Subgroup.zpowers w) hQp
    (sup_le hRt (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hwt)))
    (sup_le hRK (Subgroup.zpowers_le.mpr hwK))
    (sup_le hRi (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hwi)))
  have hlt : R < R ⊔ Subgroup.zpowers w := by
    refine lt_of_le_of_ne le_sup_left fun heq => hw ?_
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  have h2 := Subgroup.card_lt_of_lt hlt
  have h4 : Nat.card R = 4 := c.four
  omega

theorem inv_fixed {z : G} (hz : z ∈ centerOf Ki) (hz2 : z * z = 1) (hzt : z * t = t * z)
    (hz1 : z ≠ 1) (hzi : z ≠ i) : False := by
  refine c.bound_w hzt (c.z_comm_i hz) (c.z_cK hz) ?_ ?_
  · rw [pow_four_eq, hz2, one_mul]
  · intro hmem
    rcases c.mem_closure_cases hmem with h | h | h | h
    · exact hz1 h
    · apply c.not_le
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_iff.mp hz.2 y hy
      rw [h] at this
      exact this
    · exact hzi h
    · apply c.not_le
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_iff.mp hz.2 y hy
      have h2 := Subgroup.mem_centralizer_singleton_iff.mp (c.Ki_le_Ci hy)
      have ht : t = z * i := by
        rw [h]
        calc t = t * (i * i) := by rw [c.i_sq, mul_one]
          _ = t * i * i := by group
      calc y * t = y * (z * i) := by rw [← ht]
        _ = (y * z) * i := by group
        _ = z * (y * i) := by rw [h1]; group
        _ = z * (i * y) := by rw [h2]
        _ = t * y := by rw [ht]; group

theorem inv_invol {z : G} (hz : z ∈ centerOf Ki) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzi : z ≠ i) :
    False := by
  by_cases ht : z * t = t * z
  · exact c.inv_fixed hz hz2 ht hz1 hzi
  have hztZ : t⁻¹ * z * t ∈ centerOf Ki := c.tconj_mem hz
  have hcomm : z * (t⁻¹ * z * t) = (t⁻¹ * z * t) * z :=
    (Subgroup.mem_centralizer_iff.mp hz.2 _ hztZ.1).symm
  have hzt2 : (t⁻¹ * z * t) * (t⁻¹ * z * t) = 1 := by
    calc (t⁻¹ * z * t) * (t⁻¹ * z * t) = t⁻¹ * (z * z) * t := by group
      _ = 1 := by rw [hz2]; group
  have hu2 : (z * (t⁻¹ * z * t)) * (z * (t⁻¹ * z * t)) = 1 := by
    calc (z * (t⁻¹ * z * t)) * (z * (t⁻¹ * z * t)) = z * ((t⁻¹ * z * t) * z) * (t⁻¹ * z * t) := by group
      _ = z * (z * (t⁻¹ * z * t)) * (t⁻¹ * z * t) := by rw [← hcomm]
      _ = (z * z) * ((t⁻¹ * z * t) * (t⁻¹ * z * t)) := by group
      _ = 1 := by rw [hz2, hzt2, one_mul]
  have hconjzt : t⁻¹ * (t⁻¹ * z * t) * t = z := by
    calc t⁻¹ * (t⁻¹ * z * t) * t = (t * t)⁻¹ * z * (t * t) := by group
      _ = z := by rw [c.t_sq]; group
  have hut : (z * (t⁻¹ * z * t)) * t = t * (z * (t⁻¹ * z * t)) := by
    have h1 : t⁻¹ * (z * (t⁻¹ * z * t)) * t = z * (t⁻¹ * z * t) := by
      calc t⁻¹ * (z * (t⁻¹ * z * t)) * t = (t⁻¹ * z * t) * (t⁻¹ * (t⁻¹ * z * t) * t) := by group
        _ = (t⁻¹ * z * t) * z := by rw [hconjzt]
        _ = z * (t⁻¹ * z * t) := hcomm.symm
    calc (z * (t⁻¹ * z * t)) * t = t * (t⁻¹ * (z * (t⁻¹ * z * t)) * t) := by group
      _ = t * (z * (t⁻¹ * z * t)) := by rw [h1]
  have huZ : z * (t⁻¹ * z * t) ∈ centerOf Ki := (centerOf Ki).mul_mem hz hztZ
  have hu1 : z * (t⁻¹ * z * t) ≠ 1 := by
    intro h1
    apply ht
    have h2 : t⁻¹ * z * t = z := by
      have h3 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
      calc t⁻¹ * z * t = z⁻¹ * (z * (t⁻¹ * z * t)) := by group
        _ = z := by rw [h1, mul_one, h3]
    calc z * t = t * (t⁻¹ * z * t) := by group
      _ = t * z := by rw [h2]
  by_cases hui : z * (t⁻¹ * z * t) = i
  · exfalso
    apply c.noconj z
    have h3 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    calc z⁻¹ * t * z = t * ((t⁻¹ * z * t) * z) := by rw [h3]; group
      _ = t * (z * (t⁻¹ * z * t)) := by rw [hcomm]
      _ = t * i := by rw [hui]
  · exact c.inv_fixed huZ hu2 hut hu1 hui

theorem ord4 {z : G} (hz : z ∈ centerOf Ki) (hz2 : z * z = i) : False := by
  have hz4 : z ^ 4 = 1 := by
    rw [pow_four_eq, hz2, c.i_sq]
  have hzi : z * i = i * z := c.z_comm_i hz
  have hztZ : t⁻¹ * z * t ∈ centerOf Ki := c.tconj_mem hz
  have hit : t⁻¹ * i * t = i := by
    calc t⁻¹ * i * t = t⁻¹ * (i * t) := by group
      _ = t⁻¹ * (t * i) := by rw [c.ti]
      _ = i := by group
  have hztsq : (t⁻¹ * z * t) * (t⁻¹ * z * t) = i := by
    calc (t⁻¹ * z * t) * (t⁻¹ * z * t) = t⁻¹ * (z * z) * t := by group
      _ = t⁻¹ * i * t := by rw [hz2]
      _ = i := hit
  have hvZ : (t⁻¹ * z * t) * z⁻¹ ∈ centerOf Ki := (centerOf Ki).mul_mem hztZ ((centerOf Ki).inv_mem hz)
  have hcommzt : (t⁻¹ * z * t) * z⁻¹ = z⁻¹ * (t⁻¹ * z * t) := by
    have h1 : (t⁻¹ * z * t) * z = z * (t⁻¹ * z * t) := Subgroup.mem_centralizer_iff.mp hz.2 _ hztZ.1
    calc (t⁻¹ * z * t) * z⁻¹ = z⁻¹ * (z * (t⁻¹ * z * t)) * z⁻¹ := by group
      _ = z⁻¹ * ((t⁻¹ * z * t) * z) * z⁻¹ := by rw [h1]
      _ = z⁻¹ * (t⁻¹ * z * t) := by group
  have hzinvsq : z⁻¹ * z⁻¹ = i := by
    have h3 : i⁻¹ = i := c.iinv
    calc z⁻¹ * z⁻¹ = (z * z)⁻¹ := by group
      _ = i := by rw [hz2, h3]
  have hv2 : ((t⁻¹ * z * t) * z⁻¹) * ((t⁻¹ * z * t) * z⁻¹) = 1 := by
    calc ((t⁻¹ * z * t) * z⁻¹) * ((t⁻¹ * z * t) * z⁻¹)
        = (t⁻¹ * z * t) * ((z⁻¹ * (t⁻¹ * z * t)) * z⁻¹) := by group
      _ = (t⁻¹ * z * t) * (((t⁻¹ * z * t) * z⁻¹) * z⁻¹) := by rw [← hcommzt]
      _ = ((t⁻¹ * z * t) * (t⁻¹ * z * t)) * (z⁻¹ * z⁻¹) := by group
      _ = 1 := by rw [hztsq, hzinvsq, c.i_sq]
  have hv : (t⁻¹ * z * t) * z⁻¹ = 1 ∨ (t⁻¹ * z * t) * z⁻¹ = i := by
    by_contra hcon
    push Not at hcon
    exact c.inv_invol hvZ hv2 hcon.1 hcon.2
  rcases hv with hv | hv
  · have hzt : t⁻¹ * z * t = z := mul_inv_eq_one.mp hv
    refine c.bound_w ?_ hzi (c.z_cK hz) hz4 ?_
    · calc z * t = t * (t⁻¹ * z * t) := by group
        _ = t * z := by rw [hzt]
    · intro hmem
      have : z * z = 1 := by
        rcases c.mem_closure_cases hmem with h | h | h | h <;> rw [h]
        · simp
        · exact c.t_sq
        · exact c.i_sq
        · calc t * i * (t * i) = t * (i * t) * i := by group
            _ = t * (t * i) * i := by rw [c.ti]
            _ = (t * t) * (i * i) := by group
            _ = 1 := by rw [c.t_sq, c.i_sq, one_mul]
      exact c.i_ne_one (hz2.symm.trans this)
  · apply c.noconj z
    have hzt : t⁻¹ * z * t = i * z := by
      calc t⁻¹ * z * t = ((t⁻¹ * z * t) * z⁻¹) * z := by group
        _ = i * z := by rw [hv]
    have hcz : Commute z i := hzi
    calc z⁻¹ * t * z = t * (t⁻¹ * z * t)⁻¹ * z := by group
      _ = t * (i * z)⁻¹ * z := by rw [hzt]
      _ = t * (z⁻¹ * i⁻¹) * z := by group
      _ = t * (i * z⁻¹) * z := by rw [c.iinv, hcz.inv_left.eq]
      _ = t * i := by group

theorem center_sub {z : G} (hz : z ∈ centerOf Ki) : z = 1 ∨ z = i := by
  have hpow : ∀ m : ℕ, ∀ z : G, z ∈ centerOf Ki → z ^ (2 ^ m) = 1 → z = 1 ∨ z = i := by
    intro m
    induction m with
    | zero => intro z _ h; left; simpa using h
    | succ m ih =>
        intro z hz hzm
        have h2 : (z * z) ^ (2 ^ m) = 1 := by
          calc (z * z) ^ (2 ^ m) = (z ^ 2) ^ (2 ^ m) := by rw [sq]
            _ = z ^ (2 ^ (m + 1)) := by rw [← pow_mul, pow_succ, mul_comm]
            _ = 1 := hzm
        have hzzZ : z * z ∈ centerOf Ki := (centerOf Ki).mul_mem hz hz
        rcases ih (z * z) hzzZ h2 with h3 | h3
        · by_contra hcon
          push Not at hcon
          exact c.inv_invol hz h3 hcon.1 hcon.2
        · exact (c.ord4 hz h3).elim
  have hmem : (⟨z, hz.1⟩ : ↥Ki) ∈ Subgroup.center ↥Ki := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 g g.2)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp c.z2 ⟨⟨z, hz.1⟩, hmem⟩
  have hk' : orderOf z = 2 ^ k := by
    have h1 : orderOf (⟨z, hz.1⟩ : ↥Ki) = 2 ^ k := (Subgroup.orderOf_coe
      (⟨(⟨z, hz.1⟩ : ↥Ki), hmem⟩ : Subgroup.center ↥Ki)).trans hk
    exact (Subgroup.orderOf_coe (⟨z, hz.1⟩ : ↥Ki)).trans h1
  apply hpow k z hz
  rw [← hk']
  exact pow_orderOf_eq_one z

theorem i_mem_center (hne : Subgroup.center ↥Ki ≠ ⊥) : i ∈ centerOf Ki := by
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hzK : ((z : ↥Ki) : G) ∈ centerOf Ki :=
    ⟨(z : ↥Ki).2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩)⟩
  rcases c.center_sub hzK with h | h
  · exfalso
    apply hz1
    apply Subtype.ext
    apply Subtype.ext
    exact h
  · rw [← h]; exact hzK

theorem mem_of_inner (hiKi : i ∈ Ki) {l : G} (hl : l ∈ Ki)
    (hlt : ∀ x ∈ Ki, t⁻¹ * x * t = l⁻¹ * x * l) : t ∈ Ki := by
  have hc0 : ∀ x ∈ Ki, x * (t * l⁻¹) = (t * l⁻¹) * x := by
    intro x hx
    have h1 := hlt x hx
    calc x * (t * l⁻¹) = t * (t⁻¹ * x * t) * l⁻¹ := by group
      _ = t * (l⁻¹ * x * l) * l⁻¹ := by rw [h1]
      _ = (t * l⁻¹) * x := by group
  have hlt' : l * t = t * l := by
    have h1 := hlt l hl
    calc l * t = t * (t⁻¹ * l * t) := by group
      _ = t * (l⁻¹ * l * l) := by rw [h1]
      _ = t * l := by group
  have hc0t : (t * l⁻¹) * t = t * (t * l⁻¹) := by
    calc (t * l⁻¹) * t = t * (l⁻¹ * t) := by group
      _ = t * (t * l⁻¹) := by rw [(Commute.inv_left (show Commute l t from hlt')).eq]
  have hli : l * i = i * l := Subgroup.mem_centralizer_singleton_iff.mp (c.Ki_le_Ci hl)
  have hc0i : (t * l⁻¹) * i = i * (t * l⁻¹) := by
    calc (t * l⁻¹) * i = t * (l⁻¹ * i) := by group
      _ = t * (i * l⁻¹) := by rw [(Commute.inv_left (show Commute l i from hli)).eq]
      _ = (t * i) * l⁻¹ := by group
      _ = (i * t) * l⁻¹ := by rw [c.ti]
      _ = i * (t * l⁻¹) := by group
  have hc0K : t * l⁻¹ ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => hc0 k (c.K_le hk)
  have hsqZ : (t * l⁻¹) * (t * l⁻¹) ∈ centerOf Ki := by
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    · have : (t * l⁻¹) * (t * l⁻¹) = l⁻¹ * l⁻¹ := by
        calc (t * l⁻¹) * (t * l⁻¹) = t * (l⁻¹ * t) * l⁻¹ := by group
          _ = t * (t * l⁻¹) * l⁻¹ := by rw [(Commute.inv_left (show Commute l t from hlt')).eq]
          _ = (t * t) * (l⁻¹ * l⁻¹) := by group
          _ = l⁻¹ * l⁻¹ := by rw [c.t_sq, one_mul]
      rw [this]
      exact Ki.mul_mem (Ki.inv_mem hl) (Ki.inv_mem hl)
    · have h1 := hc0 y hy
      calc y * ((t * l⁻¹) * (t * l⁻¹)) = ((y * (t * l⁻¹)) * (t * l⁻¹)) := by group
        _ = ((t * l⁻¹) * y) * (t * l⁻¹) := by rw [h1]
        _ = (t * l⁻¹) * (y * (t * l⁻¹)) := by group
        _ = (t * l⁻¹) * ((t * l⁻¹) * y) := by rw [h1]
        _ = ((t * l⁻¹) * (t * l⁻¹)) * y := by group
  have hc04 : (t * l⁻¹) ^ 4 = 1 := by
    have hsq : ((t * l⁻¹) * (t * l⁻¹)) * ((t * l⁻¹) * (t * l⁻¹)) = 1 := by
      rcases c.center_sub hsqZ with h | h
      · rw [h, one_mul]
      · rw [h]; exact c.i_sq
    rw [pow_four_eq]
    exact hsq
  by_cases hmem : t * l⁻¹ ∈ Subgroup.closure ({t, i} : Set G)
  · have ht : t = (t * l⁻¹) * l := by group
    rcases c.mem_closure_cases hmem with h | h | h | h
    · rw [ht, h, one_mul]; exact hl
    · exfalso
      apply c.not_le
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hc0 x hx
      rw [h] at this
      exact this
    · rw [ht, h]; exact Ki.mul_mem hiKi hl
    · exfalso
      apply c.not_le
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hc0 x hx
      have h2 := Subgroup.mem_centralizer_singleton_iff.mp (c.Ki_le_Ci hx)
      have ht2 : t = (t * l⁻¹) * i := by
        rw [h]
        calc t = t * (i * i) := by rw [c.i_sq, mul_one]
          _ = t * i * i := by group
      calc x * t = x * ((t * l⁻¹) * i) := by rw [← ht2]
        _ = (x * (t * l⁻¹)) * i := by group
        _ = ((t * l⁻¹) * x) * i := by rw [h1]
        _ = (t * l⁻¹) * (x * i) := by group
        _ = (t * l⁻¹) * (i * x) := by rw [h2]
        _ = ((t * l⁻¹) * i) * x := by group
        _ = t * x := by rw [← ht2]
  · exact (c.bound_w hc0t hc0i hc0K hc04 hmem).elim

theorem card_center_le_two : Nat.card (Subgroup.center ↥Ki) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hiord : orderOf i = 2 := orderOf_eq_prime (by rw [sq]; exact c.i_sq) c.i_ne_one
  have hle : (Subgroup.center ↥Ki).map Ki.subtype ≤ Subgroup.zpowers i := by
    rintro x ⟨z, hz, rfl⟩
    have hzK : ((z : ↥Ki) : G) ∈ centerOf Ki :=
      ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)⟩
    show (z : G) ∈ Subgroup.zpowers i
    rcases c.center_sub hzK with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers i
  have h1 := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective Ki.subtype_injective, Nat.card_zpowers, hiord] at h1
  exact h1

end ZCtx

end ZCtx

end CFSG.QuasithinUnique.Id2519

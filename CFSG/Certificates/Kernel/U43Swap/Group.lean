module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.KS.U43Swap

variable {G : Type*} [Group G] [Finite G]

theorem isPGroup_zpowers {K : Subgroup G} {o : K} (h9 : o ^ 9 = 1) :
    IsPGroup 3 (Subgroup.zpowers o) := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd : orderOf o ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one h9
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp.out).1 hd
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

theorem conj_into {K S : Subgroup G} (hSK : S ≤ K) (hS : Nat.card S = 9) (hK : Nat.card K ∣ 1152)
    {o : G} (ho : o ∈ K) (h9 : o ^ 9 = 1) : ∃ c ∈ K, c⁻¹ * o * c ∈ S := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S' := S.subgroupOf K
  have hS' : Nat.card S' = 9 := by
    rw [← hS]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv
  have h9K : 9 ∣ Nat.card K := by
    rw [← hS']
    exact Subgroup.card_subgroup_dvd_card S'
  obtain ⟨m, hm⟩ := h9K
  have hm128 : m ∣ 128 := by
    rw [hm, show (1152 : ℕ) = 9 * 128 by norm_num] at hK
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hK
  have hm3 : ¬ 3 ∣ m := fun h => by
    have := dvd_trans h hm128
    omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd hm (Nat.card_pos (α := K)).ne'
  have hfac : (Nat.card K).factorization 3 = 2 := by
    rw [hm, Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hm3, show (9 : ℕ) = 3 ^ 2 by norm_num,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self hp.out]
    rfl
  let T : Sylow 3 K := Sylow.ofCard S' (by rw [hS', hfac]; norm_num)
  have hz : (⟨o, ho⟩ : K) ^ 9 = 1 := Subtype.ext (by simpa using h9)
  obtain ⟨P, hP⟩ := (isPGroup_zpowers hz).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T P
  have hmem : (⟨o, ho⟩ : K) ∈ ((g • T : Sylow 3 K) : Subgroup K) := by
    rw [hg]
    exact hP (Subgroup.mem_zpowers _)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨y, hy, hyo⟩ := hmem
  rw [MulAut.smul_def, MulAut.conj_apply] at hyo
  refine ⟨g, g.2, ?_⟩
  have e : (g : G)⁻¹ * o * g = (y : G) := by
    have := congrArg Subtype.val hyo
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [← this]
    group
  rw [e]
  exact hy

theorem closure_induction_fin {S : Set G} {p : G → Prop} (h1 : p 1) (hS : ∀ x ∈ S, p x)
    (hmul : ∀ x y, p x → p y → p (x * y)) {x : G} (hx : x ∈ Subgroup.closure S) : p x := by
  have hpow : ∀ x, p x → ∀ k : ℕ, p (x ^ k) := by
    intro x hx k
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact h1
  | mul x y _ _ hx hy => exact hmul x y hx hy
  | inv x _ hx =>
    have e : x⁻¹ = x ^ (orderOf x - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel (orderOf_pos x),
        pow_orderOf_eq_one]
    rw [e]
    exact hpow x hx _

theorem conj_pow9 (c o : G) : (c * o * c⁻¹) ^ 9 = 1 ↔ o ^ 9 = 1 := by
  rw [show c * o * c⁻¹ = MulAut.conj c o from rfl, ← map_pow,
    map_eq_one_iff _ (MulAut.conj c).injective]

@[expose] def PCen (H : Subgroup G) (g : G) : Set G :=
  {h | h ∈ H ∧ ∀ o ∈ H, o ^ 9 = 1 → h * (o * g * o⁻¹) = o * g * o⁻¹ * h}

theorem mem_pCen_conj {H : Subgroup G} {c g h : G} (hc : c ∈ H) :
    h ∈ PCen H (c * g * c⁻¹) ↔ c⁻¹ * h * c ∈ PCen H g := by
  constructor
  · rintro ⟨hh, hcom⟩
    refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hc) hh) hc, fun o ho h9 => ?_⟩
    have := hcom (c * o * c⁻¹) (H.mul_mem (H.mul_mem hc ho) (H.inv_mem hc)) ((conj_pow9 c o).2 h9)
    have e1 : c * o * c⁻¹ * (c * g * c⁻¹) * (c * o * c⁻¹)⁻¹ = c * (o * g * o⁻¹) * c⁻¹ := by group
    rw [e1] at this
    calc c⁻¹ * h * c * (o * g * o⁻¹) = c⁻¹ * (h * (c * (o * g * o⁻¹) * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * (o * g * o⁻¹) * c⁻¹ * h) * c := by rw [this]
      _ = o * g * o⁻¹ * (c⁻¹ * h * c) := by group
  · rintro ⟨hh, hcom⟩
    have hh' : h ∈ H := by
      have := H.mul_mem (H.mul_mem hc hh) (H.inv_mem hc)
      rwa [show c * (c⁻¹ * h * c) * c⁻¹ = h by group] at this
    refine ⟨hh', fun o ho h9 => ?_⟩
    have := hcom (c⁻¹ * o * c) (H.mul_mem (H.mul_mem (H.inv_mem hc) ho) hc)
      (by simpa using (conj_pow9 c⁻¹ o).2 h9)
    have e1 : c⁻¹ * o * c * g * (c⁻¹ * o * c)⁻¹ = c⁻¹ * (o * (c * g * c⁻¹) * o⁻¹) * c := by group
    rw [e1] at this
    calc h * (o * (c * g * c⁻¹) * o⁻¹) =
          c * (c⁻¹ * h * c * (c⁻¹ * (o * (c * g * c⁻¹) * o⁻¹) * c)) * c⁻¹ := by group
      _ = c * (c⁻¹ * (o * (c * g * c⁻¹) * o⁻¹) * c * (c⁻¹ * h * c)) * c⁻¹ := by rw [this]
      _ = o * (c * g * c⁻¹) * o⁻¹ * h := by group

theorem pCen_sq {H : Subgroup G} {g : G} (hg : g ^ 3 = 1) : PCen H (g ^ 2) = PCen H g := by
  have key : ∀ h x : G, h * x = x * h → h * x ^ 2 = x ^ 2 * h := fun h x hx => by
    rw [pow_two, ← mul_assoc, hx, mul_assoc, hx, mul_assoc]
  ext h
  refine ⟨fun ⟨hh, hc⟩ => ⟨hh, fun o ho h9 => ?_⟩, fun ⟨hh, hc⟩ => ⟨hh, fun o ho h9 => ?_⟩⟩
  · have := key h _ (hc o ho h9)
    have e : (o * g ^ 2 * o⁻¹) ^ 2 = o * g * o⁻¹ := by
      rw [show o * g ^ 2 * o⁻¹ = MulAut.conj o (g ^ 2) from rfl, ← map_pow, ← pow_mul,
        show g ^ (2 * 2) = g ^ 3 * g by group, hg, one_mul]
      rfl
    rwa [e] at this
  · have := key h _ (hc o ho h9)
    have e : (o * g * o⁻¹) ^ 2 = o * g ^ 2 * o⁻¹ := by
      rw [show o * g * o⁻¹ = MulAut.conj o g from rfl, ← map_pow]
      rfl
    rwa [e] at this

@[expose] def yE (s t : G) (e : ℕ) : G := s ^ (e % 3) * t ^ (e / 3)

theorem pow_mod3 {s : G} (hs : s ^ 3 = 1) (n : ℕ) : s ^ n = s ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hs, one_pow, mul_one]

section S0

variable {s t : G} (hs : s ^ 3 = 1) (ht : t ^ 3 = 1) (hst : s * t = t * s)
include hs ht hst

theorem yE_mul (e f : ℕ) : yE s t e * yE s t f =
    yE s t ((e % 3 + f % 3) % 3 + 3 * ((e / 3 + f / 3) % 3)) := by
  have hc : Commute s t := hst
  have h1 : (e % 3 + f % 3) % 3 + 3 * ((e / 3 + f / 3) % 3) = _ := rfl
  unfold yE
  rw [show ((e % 3 + f % 3) % 3 + 3 * ((e / 3 + f / 3) % 3)) % 3 = (e % 3 + f % 3) % 3 by omega,
    show ((e % 3 + f % 3) % 3 + 3 * ((e / 3 + f / 3) % 3)) / 3 = (e / 3 + f / 3) % 3 by omega,
    (pow_mod3 hs (e % 3 + f % 3)).symm, (pow_mod3 ht (e / 3 + f / 3)).symm, pow_add, pow_add]
  have := (hc.pow_pow (f % 3) (e / 3)).eq
  calc s ^ (e % 3) * t ^ (e / 3) * (s ^ (f % 3) * t ^ (f / 3))
      = s ^ (e % 3) * (t ^ (e / 3) * s ^ (f % 3)) * t ^ (f / 3) := by group
    _ = s ^ (e % 3) * (s ^ (f % 3) * t ^ (e / 3)) * t ^ (f / 3) := by rw [this]
    _ = _ := by group

theorem yE_comm (e f : ℕ) : yE s t e * yE s t f = yE s t f * yE s t e := by
  rw [yE_mul hs ht hst, yE_mul hs ht hst, Nat.add_comm (e % 3), Nat.add_comm (e / 3)]

theorem yE_pow9 (e : ℕ) : yE s t e ^ 9 = 1 := by
  have hc : Commute (s ^ (e % 3)) (t ^ (e / 3)) := (Commute.pow_pow hst _ _)
  unfold yE
  rw [hc.mul_pow, ← pow_mul, ← pow_mul, show e % 3 * 9 = 3 * (3 * (e % 3)) by ring,
    show e / 3 * 9 = 3 * (3 * (e / 3)) by ring, pow_mul s, pow_mul t, hs, ht]
  simp

theorem mem_S0 {x : G} (hx : x ∈ Subgroup.closure {s, t}) : ∃ e < 9, x = yE s t e := by
  refine closure_induction_fin (p := fun x => ∃ e < 9, x = yE s t e) ⟨0, by norm_num, by simp [yE]⟩
    ?_ ?_ hx
  · rintro x (rfl | rfl)
    · exact ⟨1, by norm_num, by simp [yE]⟩
    · exact ⟨3, by norm_num, by simp [yE]⟩
  · rintro x y ⟨e, -, rfl⟩ ⟨f, -, rfl⟩
    exact ⟨_, by omega, yE_mul hs ht hst e f⟩

theorem yE_mem (e : ℕ) : yE s t e ∈ Subgroup.closure {s, t} :=
  Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem card_S0 (h9 : 9 ∣ Nat.card (Subgroup.closure {s, t})) :
    Nat.card (Subgroup.closure {s, t}) = 9 := by
  have hsub : ((Subgroup.closure {s, t} : Subgroup G) : Set G) ⊆ yE s t '' Set.Iio 9 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := mem_S0 hs ht hst hx
    exact ⟨e, he, rfl⟩
  have hle : Nat.card (Subgroup.closure {s, t}) ≤ 9 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    calc (((Subgroup.closure {s, t} : Subgroup G) : Set G)).ncard ≤ (yE s t '' Set.Iio 9).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (Set.Iio 9).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = 9 := by rw [← Nat.card_coe_set_eq]; simp
  exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos h9)

end S0

@[expose] def Mut (e f : ℕ) : Prop := (e = 1 ∨ e = 2) ∧ (f = 3 ∨ f = 6) ∨ (e = 3 ∨ e = 6) ∧ (f = 1 ∨ f = 2)

structure SwFacts (G : Type*) [Group G] where
  H : Subgroup G
  g : ℕ → G
  a : G
  s : G
  t : G
  u : G
  X : ℕ → G
  Y : ℕ → G
  hH : Nat.card H = 1152
  hHg : H = Subgroup.closure (g '' Set.Iio 4)
  ha : a ∈ H
  haz : ∀ h ∈ H, h * a = a * h
  ha1 : a ≠ 1
  ha2 : a * a = 1
  hs : s ∈ H
  ht : t ∈ H
  hu : u ∈ H
  hs3 : s ^ 3 = 1
  ht3 : t ^ 3 = 1
  hst : s * t = t * s
  hu2 : u * u = 1
  hS9 : 9 ∣ Nat.card (Subgroup.closure {s, t})
  hXH : ∀ i < 81, X i ∈ H
  hX9 : ∀ i < 81, X i ^ 9 = 1
  hZ : ∀ e < 9, ∃ z < 81, X z = yE s t e
  hCl : ∀ i < 81, ∀ j < 4, ∃ c < 81, X c = g j * X i * (g j)⁻¹
  hYs : ∀ i < 81, ∃ m < 4, X i * s * (X i)⁻¹ = Y m
  hYt : ∀ i < 81, ∃ m < 4, X i * t * (X i)⁻¹ = Y (4 + m)
  hYr : ∀ k < 8, ∃ o < 81, Y k = X o * (if k < 4 then s else t) * (X o)⁻¹
  hT2a : ∀ i < 81, (∃ k < 4, X i * Y (4 + k) ≠ Y (4 + k) * X i) ∨
    ∀ k < 4, u * X i * u * Y k = Y k * (u * X i * u)
  hT2b : ∀ i < 81, (∃ k < 4, X i * Y k ≠ Y k * X i) ∨
    ∀ k < 4, u * X i * u * Y (4 + k) = Y (4 + k) * (u * X i * u)
  hTw : ∀ e, 1 ≤ e → e < 9 → ∃ k < 8, yE s t e * Y k ≠ Y k * yE s t e
  hN : ∀ e f, 1 ≤ e → e < 9 → 1 ≤ f → f < 9 → ¬ Mut e f → ∃ o < 81,
    yE s t e * (X o * yE s t f * (X o)⁻¹) ≠ X o * yE s t f * (X o)⁻¹ * yE s t e ∨
    yE s t f * (X o * yE s t e * (X o)⁻¹) ≠ X o * yE s t e * (X o)⁻¹ * yE s t f
  hQ : ∃ d : ℕ → G, (∀ i < 64, d i ∈ H) ∧ ∀ i < 64, ∀ j < 64,
    d i * s * (d i)⁻¹ = d j * s * (d j)⁻¹ → d i * t * (d i)⁻¹ = d j * t * (d j)⁻¹ → i = j
  hK : ∀ e, 1 ≤ e → e < 9 → ∃ d : ℕ → G, (∀ i < 16, d i ∈ H) ∧ ∀ i < 16, ∀ j < 16,
    d i * yE s t e * (d i)⁻¹ = d j * yE s t e * (d j)⁻¹ → i = j

namespace SwFacts

variable (F : SwFacts G)

theorem card_S0 : Nat.card (Subgroup.closure {F.s, F.t}) = 9 :=
  CFSG.KS.U43Swap.card_S0 F.hs3 F.ht3 F.hst F.hS9

theorem S0_le : Subgroup.closure {F.s, F.t} ≤ F.H := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact F.hs
  · exact F.ht

theorem yE_memH (e : ℕ) : yE F.s F.t e ∈ F.H := F.S0_le (yE_mem F.hs3 F.ht3 F.hst e)

theorem odd_conj {o : G} (ho : o ∈ F.H) (h9 : o ^ 9 = 1) :
    ∃ c ∈ F.H, ∃ e < 9, o = c * yE F.s F.t e * c⁻¹ := by
  obtain ⟨c, hc, hco⟩ := conj_into F.S0_le F.card_S0 (by rw [F.hH]) ho h9
  obtain ⟨e, he, hee⟩ := mem_S0 F.hs3 F.ht3 F.hst hco
  exact ⟨c, hc, e, he, by rw [← hee]; group⟩

theorem odd_mem {o : G} (ho : o ∈ F.H) (h9 : o ^ 9 = 1) : ∃ i < 81, o = F.X i := by
  have hfin : (F.X '' Set.Iio 81).Finite := (Set.finite_Iio 81).image _
  have hmaps : ∀ j < 4, Set.MapsTo (fun x => F.g j * x * (F.g j)⁻¹) (F.X '' Set.Iio 81)
      (F.X '' Set.Iio 81) := by
    rintro j hj _ ⟨i, hi, rfl⟩
    obtain ⟨c, hc, hce⟩ := F.hCl i hi j hj
    exact ⟨c, hc, hce⟩
  have hinv : ∀ j < 4, Set.MapsTo (fun x => (F.g j)⁻¹ * x * (F.g j)⁻¹⁻¹) (F.X '' Set.Iio 81)
      (F.X '' Set.Iio 81) := by
    intro j hj x hx
    have hbij := (hfin.injOn_iff_bijOn_of_mapsTo (hmaps j hj)).1
      (fun x _ y _ hxy => by simpa using hxy)
    obtain ⟨x', hx', hxe⟩ := hbij.surjOn hx
    simp only at hxe
    rw [← hxe]
    simpa [mul_assoc] using hx'
  have hall : ∀ c ∈ F.H, ∀ x ∈ F.X '' Set.Iio 81, c * x * c⁻¹ ∈ F.X '' Set.Iio 81 := by
    intro c hc
    rw [F.hHg] at hc
    refine closure_induction_fin (p := fun c => ∀ x ∈ F.X '' Set.Iio 81,
      c * x * c⁻¹ ∈ F.X '' Set.Iio 81) (fun x hx => by simpa using hx) ?_ ?_ hc
    · rintro _ ⟨j, hj, rfl⟩ x hx
      exact hmaps j hj hx
    · intro c d hc hd x hx
      have := hc _ (hd x hx)
      rwa [show c * (d * x * d⁻¹) * c⁻¹ = c * d * x * (c * d)⁻¹ by group] at this
  obtain ⟨c, hc, e, he, rfl⟩ := F.odd_conj ho h9
  obtain ⟨z, hz, hze⟩ := F.hZ e he
  obtain ⟨i, hi, hie⟩ := hall c hc (F.X z) ⟨z, hz, rfl⟩
  exact ⟨i, hi, by rw [hie, hze]⟩

theorem Y_mem {k : ℕ} (hk : k < 8) : F.Y k ∈ F.H := by
  obtain ⟨o, ho, he⟩ := F.hYr k hk
  rw [he]
  refine F.H.mul_mem (F.H.mul_mem (F.hXH o ho) ?_) (F.H.inv_mem (F.hXH o ho))
  split_ifs
  · exact F.hs
  · exact F.ht

theorem memS_iff {h : G} : h ∈ PCen F.H F.s ↔ h ∈ F.H ∧ ∀ k < 4, h * F.Y k = F.Y k * h := by
  constructor
  · rintro ⟨hh, hc⟩
    refine ⟨hh, fun k hk => ?_⟩
    obtain ⟨o, ho, he⟩ := F.hYr k (by omega)
    rw [if_pos hk] at he
    rw [he]
    exact hc _ (F.hXH o ho) (F.hX9 o ho)
  · rintro ⟨hh, hc⟩
    refine ⟨hh, fun o ho h9 => ?_⟩
    obtain ⟨i, hi, rfl⟩ := F.odd_mem ho h9
    obtain ⟨m, hm, hme⟩ := F.hYs i hi
    rw [hme]
    exact hc m hm

theorem memT_iff {h : G} :
    h ∈ PCen F.H F.t ↔ h ∈ F.H ∧ ∀ k < 4, h * F.Y (4 + k) = F.Y (4 + k) * h := by
  constructor
  · rintro ⟨hh, hc⟩
    refine ⟨hh, fun k hk => ?_⟩
    obtain ⟨o, ho, he⟩ := F.hYr (4 + k) (by omega)
    rw [if_neg (by omega)] at he
    rw [he]
    exact hc _ (F.hXH o ho) (F.hX9 o ho)
  · rintro ⟨hh, hc⟩
    refine ⟨hh, fun o ho h9 => ?_⟩
    obtain ⟨i, hi, rfl⟩ := F.odd_mem ho h9
    obtain ⟨m, hm, hme⟩ := F.hYt i hi
    rw [hme]
    exact hc m hm

theorem swapTS {o : G} (ho : o ∈ F.H) (h9 : o ^ 9 = 1) (hoT : o ∈ PCen F.H F.t) :
    F.u * o * F.u ∈ PCen F.H F.s := by
  obtain ⟨i, hi, rfl⟩ := F.odd_mem ho h9
  rcases F.hT2a i hi with ⟨k, hk, hne⟩ | hall
  · exact absurd ((F.memT_iff.1 hoT).2 k hk) hne
  · exact F.memS_iff.2 ⟨F.H.mul_mem (F.H.mul_mem F.hu ho) F.hu, hall⟩

theorem swapST {o : G} (ho : o ∈ F.H) (h9 : o ^ 9 = 1) (hoS : o ∈ PCen F.H F.s) :
    F.u * o * F.u ∈ PCen F.H F.t := by
  obtain ⟨i, hi, rfl⟩ := F.odd_mem ho h9
  rcases F.hT2b i hi with ⟨k, hk, hne⟩ | hall
  · exact absurd ((F.memS_iff.1 hoS).2 k hk) hne
  · exact F.memT_iff.2 ⟨F.H.mul_mem (F.H.mul_mem F.hu ho) F.hu, hall⟩

@[expose] def Zst : Subgroup G := F.H ⊓ Subgroup.centralizer {F.s, F.t}

theorem card_Zst_le : Nat.card F.Zst ≤ 18 := by
  obtain ⟨d, hdH, hd⟩ := F.hQ
  let φ : Fin 64 × F.Zst → F.H := fun p => ⟨d p.1 * p.2, F.H.mul_mem (hdH _ p.1.2)
    (Subgroup.mem_inf.1 p.2.2).1⟩
  have hcz : ∀ z : F.Zst, ∀ x ∈ ({F.s, F.t} : Set G), (z : G) * x = x * z := fun z x hx =>
    ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 z.2).2) x hx).symm
  have hφ : Function.Injective φ := by
    rintro ⟨i, z⟩ ⟨j, z'⟩ hij
    have e : d i * z = d j * z' := congrArg Subtype.val hij
    have key : ∀ x ∈ ({F.s, F.t} : Set G), d i * x * (d i)⁻¹ = d j * x * (d j)⁻¹ := by
      intro x hx
      calc d i * x * (d i)⁻¹ = d i * z * x * (d i * z)⁻¹ := by
            rw [mul_assoc (d i) z, hcz z x hx]
            group
        _ = d j * z' * x * (d j * z')⁻¹ := by rw [e]
        _ = d j * x * (d j)⁻¹ := by
            rw [mul_assoc (d j) z', hcz z' x hx]
            group
    have hij' : i = j := Fin.ext (hd i i.2 j j.2 (key _ (by simp)) (key _ (by simp)))
    subst hij'
    have : (z : G) = z' := mul_left_cancel e
    rw [Subtype.ext this]
  have := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 64), Fintype.card_fin, F.hH] at this
  omega

theorem t1 {h : G} (hS : h ∈ PCen F.H F.s) (hT : h ∈ PCen F.H F.t) : h = 1 ∨ h = F.a := by
  set S0 := Subgroup.closure {F.s, F.t}
  have hS0abel : ∀ x ∈ S0, ∀ y ∈ S0, x * y = y * x := by
    intro x hx y hy
    obtain ⟨e, -, rfl⟩ := mem_S0 F.hs3 F.ht3 F.hst hx
    obtain ⟨f, -, rfl⟩ := mem_S0 F.hs3 F.ht3 F.hst hy
    exact yE_comm F.hs3 F.ht3 F.hst e f
  have hS0Z : S0 ≤ F.Zst := fun x hx => Subgroup.mem_inf.2 ⟨F.S0_le hx,
    Subgroup.mem_centralizer_iff.2 fun y hy => (hS0abel x hx y (Subgroup.subset_closure hy)).symm⟩
  have haZ : F.a ∈ F.Zst := Subgroup.mem_inf.2 ⟨F.ha, Subgroup.mem_centralizer_iff.2
    fun y hy => by
      rcases hy with rfl | rfl
      · exact F.haz _ F.hs
      · exact F.haz _ F.ht⟩
  have haS : F.a ∉ S0 := fun h => by
    obtain ⟨e, -, he⟩ := mem_S0 F.hs3 F.ht3 F.hst h
    have h9 := yE_pow9 F.hs3 F.ht3 F.hst e
    rw [← he] at h9
    have : F.a ^ 9 = F.a := by
      rw [show (9 : ℕ) = 2 * 4 + 1 by norm_num, pow_succ, pow_mul, sq, F.ha2, one_pow, one_mul]
    exact F.ha1 (this ▸ h9)
  have hhZ : h ∈ F.Zst := Subgroup.mem_inf.2 ⟨hS.1, Subgroup.mem_centralizer_iff.2 fun y hy => by
    rcases hy with rfl | rfl
    · simpa using (hS.2 1 F.H.one_mem (by simp)).symm
    · simpa using (hT.2 1 F.H.one_mem (by simp)).symm⟩
  set S' := S0.subgroupOf F.Zst
  have hS' : Nat.card S' = 9 := by
    rw [← F.card_S0]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS0Z).toEquiv
  have hidx : S'.index = 2 := by
    have hmul := S'.card_mul_index
    rw [hS'] at hmul
    have hle := F.card_Zst_le
    have hne : S'.index ≠ 1 := fun h1 => by
      rw [Subgroup.index_eq_one] at h1
      have : (⟨F.a, haZ⟩ : F.Zst) ∈ S' := by rw [h1]; trivial
      exact haS this
    have hpos : S'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hY : ∀ k < 8, Commute h (F.Y k) := by
    intro k hk
    rcases Nat.lt_or_ge k 4 with h4 | h4
    · exact (F.memS_iff.1 hS).2 k h4
    · have := (F.memT_iff.1 hT).2 (k - 4) (by omega)
      rwa [show 4 + (k - 4) = k by omega] at this
  have hy0 : ∀ e < 9, (∀ k < 8, Commute (yE F.s F.t e) (F.Y k)) → e = 0 := by
    intro e he hc
    by_contra h0
    obtain ⟨k, hk, hne⟩ := F.hTw e (by omega) he
    exact hne (hc k hk)
  have hmem := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨F.a, haZ⟩ : F.Zst)⁻¹)
    (b := ⟨h, hhZ⟩))
  by_cases hhS : h ∈ S0
  · obtain ⟨e, he, rfl⟩ := mem_S0 F.hs3 F.ht3 F.hst hhS
    left
    rw [hy0 e he hY]
    simp [yE]
  · right
    have haS' : (⟨F.a, haZ⟩ : F.Zst)⁻¹ ∉ S' := fun h' => haS (by
      have := S'.inv_mem h'
      simpa [S', Subgroup.mem_subgroupOf] using this)
    have hhS' : (⟨h, hhZ⟩ : F.Zst) ∉ S' := fun h' => hhS (by
      simpa [S', Subgroup.mem_subgroupOf] using h')
    have hin : F.a⁻¹ * h ∈ S0 := by
      have := hmem.2 (iff_of_false haS' hhS')
      simpa [S', Subgroup.mem_subgroupOf] using this
    obtain ⟨e, he, hee⟩ := mem_S0 F.hs3 F.ht3 F.hst hin
    have hc : ∀ k < 8, Commute (yE F.s F.t e) (F.Y k) := by
      intro k hk
      rw [← hee]
      exact (Commute.symm (F.haz _ (F.Y_mem hk))).inv_left.mul_left (hY k hk)
    rw [hy0 e he hc] at hee
    have : F.a⁻¹ * h = 1 := by simpa [yE] using hee
    rw [inv_mul_eq_one] at this
    exact this.symm

theorem yE_one : yE F.s F.t 1 = F.s := by simp [yE]

theorem yE_two : yE F.s F.t 2 = F.s ^ 2 := by simp [yE]

theorem yE_three : yE F.s F.t 3 = F.t := by simp [yE]

theorem yE_six : yE F.s F.t 6 = F.t ^ 2 := by simp [yE]

theorem yE_zero : yE F.s F.t 0 = 1 := by simp [yE]

theorem mut_cases {e f : ℕ} (he1 : 1 ≤ e) (he : e < 9) (hf1 : 1 ≤ f) (hf : f < 9)
    (h1 : yE F.s F.t e ∈ PCen F.H (yE F.s F.t f)) (h2 : yE F.s F.t f ∈ PCen F.H (yE F.s F.t e)) :
    (PCen F.H (yE F.s F.t e) = PCen F.H F.s ∧ PCen F.H (yE F.s F.t f) = PCen F.H F.t) ∨
      (PCen F.H (yE F.s F.t e) = PCen F.H F.t ∧ PCen F.H (yE F.s F.t f) = PCen F.H F.s) := by
  have hM : Mut e f := by
    by_contra hM
    obtain ⟨o, ho, hne | hne⟩ := F.hN e f he1 he hf1 hf hM
    · exact hne (h1.2 _ (F.hXH o ho) (F.hX9 o ho))
    · exact hne (h2.2 _ (F.hXH o ho) (F.hX9 o ho))
  have hS : ∀ e, (e = 1 ∨ e = 2) → PCen F.H (yE F.s F.t e) = PCen F.H F.s := by
    rintro e (rfl | rfl)
    · rw [F.yE_one]
    · rw [F.yE_two, pCen_sq F.hs3]
  have hT : ∀ e, (e = 3 ∨ e = 6) → PCen F.H (yE F.s F.t e) = PCen F.H F.t := by
    rintro e (rfl | rfl)
    · rw [F.yE_three]
    · rw [F.yE_six, pCen_sq F.ht3]
  rcases hM with ⟨he', hf'⟩ | ⟨he', hf'⟩
  · exact Or.inl ⟨hS e he', hT f hf'⟩
  · exact Or.inr ⟨hT e he', hS f hf'⟩

theorem tables {g₁ g₂ : G} (hg₁ : g₁ ∈ F.H) (hg₂ : g₂ ∈ F.H) (h9₁ : g₁ ^ 9 = 1)
    (h9₂ : g₂ ^ 9 = 1) (hn₁ : g₁ ≠ 1) (hn₂ : g₂ ≠ 1) (hm₁ : g₁ ∈ PCen F.H g₂)
    (hm₂ : g₂ ∈ PCen F.H g₁) :
    (∀ h ∈ PCen F.H g₁, h ∈ PCen F.H g₂ → h = 1 ∨ h = F.a) ∧
    ∃ c ∈ F.H, (∀ o ∈ F.H, o ^ 9 = 1 → o ∈ PCen F.H g₂ → c⁻¹ * o * c ∈ PCen F.H g₁) ∧
      (∀ o ∈ F.H, o ^ 9 = 1 → o ∈ PCen F.H g₁ → c * o * c⁻¹ ∈ PCen F.H g₂) := by
  obtain ⟨c₁, hc₁, f, hf, rfl⟩ := F.odd_conj hg₂ h9₂
  have hcomm : g₁ * (c₁ * yE F.s F.t f * c₁⁻¹) = c₁ * yE F.s F.t f * c₁⁻¹ * g₁ := by
    simpa using hm₁.2 1 F.H.one_mem (by simp)
  set K := F.H ⊓ Subgroup.centralizer {yE F.s F.t f}
  have hg₁' : c₁⁻¹ * g₁ * c₁ ∈ K := by
    refine Subgroup.mem_inf.2 ⟨F.H.mul_mem (F.H.mul_mem (F.H.inv_mem hc₁) hg₁) hc₁,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc c₁⁻¹ * g₁ * c₁ * yE F.s F.t f = c₁⁻¹ * (g₁ * (c₁ * yE F.s F.t f * c₁⁻¹)) * c₁ := by group
      _ = c₁⁻¹ * (c₁ * yE F.s F.t f * c₁⁻¹ * g₁) * c₁ := by rw [hcomm]
      _ = yE F.s F.t f * (c₁⁻¹ * g₁ * c₁) := by group
  have hSK : Subgroup.closure {F.s, F.t} ≤ K := fun x hx => by
    obtain ⟨e, -, rfl⟩ := mem_S0 F.hs3 F.ht3 F.hst hx
    exact Subgroup.mem_inf.2 ⟨F.yE_memH e,
      Subgroup.mem_centralizer_singleton_iff.2 (yE_comm F.hs3 F.ht3 F.hst e f)⟩
  have hKd : Nat.card K ∣ 1152 := F.hH ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨c₂, hc₂K, hc₂⟩ := conj_into hSK F.card_S0 hKd hg₁'
    (by simpa using (conj_pow9 c₁⁻¹ g₁).2 h9₁)
  obtain ⟨e, he, hee⟩ := mem_S0 F.hs3 F.ht3 F.hst hc₂
  obtain ⟨hc₂H, hc₂c⟩ := Subgroup.mem_inf.1 hc₂K
  have hc₂f : c₂ * yE F.s F.t f * c₂⁻¹ = yE F.s F.t f := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hc₂c]
    group
  set c := c₁ * c₂ with hcdef
  have hc : c ∈ F.H := F.H.mul_mem hc₁ hc₂H
  have eq1 : g₁ = c * yE F.s F.t e * c⁻¹ := by
    rw [← hee, hcdef]
    group
  have eq2 : c₁ * yE F.s F.t f * c₁⁻¹ = c * yE F.s F.t f * c⁻¹ := by
    calc c₁ * yE F.s F.t f * c₁⁻¹ = c₁ * (c₂ * yE F.s F.t f * c₂⁻¹) * c₁⁻¹ := by rw [hc₂f]
      _ = c * yE F.s F.t f * c⁻¹ := by rw [hcdef]; group
  rw [eq2] at hm₁ hm₂ hn₂ ⊢
  rw [eq1] at hm₁ hm₂ hn₁ ⊢
  have he0 : 1 ≤ e := by
    by_contra h0
    rw [show e = 0 by omega, F.yE_zero] at hn₁
    exact hn₁ (by group)
  have hf0 : 1 ≤ f := by
    by_contra h0
    rw [show f = 0 by omega, F.yE_zero] at hn₂
    exact hn₂ (by group)
  have hye : yE F.s F.t e ∈ PCen F.H (yE F.s F.t f) := by
    have := (mem_pCen_conj hc).1 hm₁
    rwa [show c⁻¹ * (c * yE F.s F.t e * c⁻¹) * c = yE F.s F.t e by group] at this
  have hyf : yE F.s F.t f ∈ PCen F.H (yE F.s F.t e) := by
    have := (mem_pCen_conj hc).1 hm₂
    rwa [show c⁻¹ * (c * yE F.s F.t f * c⁻¹) * c = yE F.s F.t f by group] at this
  have hu' : F.u⁻¹ = F.u := (eq_inv_of_mul_eq_one_left F.hu2).symm
  have key : ∀ A B : Set G, PCen F.H (yE F.s F.t e) = A → PCen F.H (yE F.s F.t f) = B →
      (∀ h ∈ A, h ∈ B → h = 1 ∨ h = F.a) →
      (∀ o ∈ F.H, o ^ 9 = 1 → o ∈ B → F.u * o * F.u ∈ A) →
      (∀ o ∈ F.H, o ^ 9 = 1 → o ∈ A → F.u * o * F.u ∈ B) →
      (∀ h ∈ PCen F.H (c * yE F.s F.t e * c⁻¹), h ∈ PCen F.H (c * yE F.s F.t f * c⁻¹) →
        h = 1 ∨ h = F.a) ∧
      ∃ c' ∈ F.H, (∀ o ∈ F.H, o ^ 9 = 1 → o ∈ PCen F.H (c * yE F.s F.t f * c⁻¹) →
          c'⁻¹ * o * c' ∈ PCen F.H (c * yE F.s F.t e * c⁻¹)) ∧
        (∀ o ∈ F.H, o ^ 9 = 1 → o ∈ PCen F.H (c * yE F.s F.t e * c⁻¹) →
          c' * o * c'⁻¹ ∈ PCen F.H (c * yE F.s F.t f * c⁻¹)) := by
    intro A B hA hB hT1 hBA hAB
    refine ⟨fun h h1 h2 => ?_, c * F.u * c⁻¹, F.H.mul_mem (F.H.mul_mem hc F.hu) (F.H.inv_mem hc),
      fun o ho h9 hoB => ?_, fun o ho h9 hoA => ?_⟩
    · rw [mem_pCen_conj hc, hA] at h1
      rw [mem_pCen_conj hc, hB] at h2
      rcases hT1 _ h1 h2 with h' | h'
      · left
        calc h = c * (c⁻¹ * h * c) * c⁻¹ := by group
          _ = 1 := by rw [h']; group
      · right
        calc h = c * (c⁻¹ * h * c) * c⁻¹ := by group
          _ = F.a := by rw [h', F.haz c hc]; group
    · rw [mem_pCen_conj hc, hB] at hoB
      have h' := hBA _ (F.H.mul_mem (F.H.mul_mem (F.H.inv_mem hc) ho) hc)
        (by simpa using (conj_pow9 c⁻¹ o).2 h9) hoB
      rw [mem_pCen_conj hc, hA]
      have e : c⁻¹ * ((c * F.u * c⁻¹)⁻¹ * o * (c * F.u * c⁻¹)) * c =
          F.u⁻¹ * (c⁻¹ * o * c) * F.u := by group
      rwa [e, hu']
    · rw [mem_pCen_conj hc, hA] at hoA
      have h' := hAB _ (F.H.mul_mem (F.H.mul_mem (F.H.inv_mem hc) ho) hc)
        (by simpa using (conj_pow9 c⁻¹ o).2 h9) hoA
      rw [mem_pCen_conj hc, hB]
      have e : c⁻¹ * ((c * F.u * c⁻¹) * o * (c * F.u * c⁻¹)⁻¹) * c =
          F.u * (c⁻¹ * o * c) * F.u⁻¹ := by group
      rwa [e, hu']
  rcases F.mut_cases he0 he hf0 hf hye hyf with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · exact key _ _ hA hB (fun h h1 h2 => F.t1 h1 h2) (fun o ho h9 h => F.swapTS ho h9 h)
      (fun o ho h9 h => F.swapST ho h9 h)
  · exact key _ _ hA hB (fun h h1 h2 => F.t1 h2 h1) (fun o ho h9 h => F.swapST ho h9 h)
      (fun o ho h9 h => F.swapTS ho h9 h)

theorem oddCard {y : G} (hy : y ∈ F.H) (h9 : y ^ 9 = 1) (hn : y ≠ 1) :
    Nat.card ↥(F.H ⊓ Subgroup.centralizer {y}) % 16 ≠ 0 := by
  obtain ⟨c, hc, e, he, rfl⟩ := F.odd_conj hy h9
  have he0 : 1 ≤ e := by
    by_contra h0
    rw [show e = 0 by omega, F.yE_zero] at hn
    exact hn (by group)
  set K := F.H ⊓ Subgroup.centralizer {c * yE F.s F.t e * c⁻¹}
  have h9K : 9 ∣ Nat.card K := by
    let S1 := (Subgroup.closure {F.s, F.t}).map (MulAut.conj c).toMonoidHom
    have hS1 : Nat.card S1 = 9 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, F.card_S0]
    have hle : S1 ≤ K := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨f, -, rfl⟩ := mem_S0 F.hs3 F.ht3 F.hst hz
      refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      · change c * yE F.s F.t f * c⁻¹ ∈ F.H
        exact F.H.mul_mem (F.H.mul_mem hc (F.yE_memH f)) (F.H.inv_mem hc)
      · change c * yE F.s F.t f * c⁻¹ * (c * yE F.s F.t e * c⁻¹) =
          c * yE F.s F.t e * c⁻¹ * (c * yE F.s F.t f * c⁻¹)
        have := yE_comm F.hs3 F.ht3 F.hst f e
        calc c * yE F.s F.t f * c⁻¹ * (c * yE F.s F.t e * c⁻¹) =
              c * (yE F.s F.t f * yE F.s F.t e) * c⁻¹ := by group
          _ = c * (yE F.s F.t e * yE F.s F.t f) * c⁻¹ := by rw [this]
          _ = _ := by group
    rw [← hS1]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨d, hdH, hd⟩ := F.hK e he0 he
  let φ : Fin 16 × K → F.H := fun p => ⟨c * d p.1 * c⁻¹ * p.2,
    F.H.mul_mem (F.H.mul_mem (F.H.mul_mem hc (hdH _ p.1.2)) (F.H.inv_mem hc))
      (Subgroup.mem_inf.1 p.2.2).1⟩
  have hφ : Function.Injective φ := by
    rintro ⟨i, z⟩ ⟨j, z'⟩ hij
    have e1 : c * d i * c⁻¹ * z = c * d j * c⁻¹ * z' := congrArg Subtype.val hij
    have hz : ∀ w : K, (w : G) * (c * yE F.s F.t e * c⁻¹) * (w : G)⁻¹ = c * yE F.s F.t e * c⁻¹ :=
      fun w => by
        rw [Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 w.2).2]
        group
    have key : d i * yE F.s F.t e * (d i)⁻¹ = d j * yE F.s F.t e * (d j)⁻¹ := by
      have h2 : c * d i * c⁻¹ * z * (c * yE F.s F.t e * c⁻¹) * (c * d i * c⁻¹ * z)⁻¹ =
          c * d j * c⁻¹ * z' * (c * yE F.s F.t e * c⁻¹) * (c * d j * c⁻¹ * z')⁻¹ := by rw [e1]
      have h3 : ∀ (w : K) (k : ℕ), c * d k * c⁻¹ * w * (c * yE F.s F.t e * c⁻¹) *
          (c * d k * c⁻¹ * w)⁻¹ = c * (d k * yE F.s F.t e * (d k)⁻¹) * c⁻¹ := by
        intro w k
        calc c * d k * c⁻¹ * w * (c * yE F.s F.t e * c⁻¹) * (c * d k * c⁻¹ * w)⁻¹ =
              c * d k * c⁻¹ * ((w : G) * (c * yE F.s F.t e * c⁻¹) * (w : G)⁻¹) *
                (c * d k * c⁻¹)⁻¹ := by group
          _ = _ := by rw [hz w]; group
      rw [h3, h3] at h2
      simpa using h2
    have hij' : i = j := Fin.ext (hd i i.2 j j.2 key)
    subst hij'
    have : (z : G) = z' := mul_left_cancel e1
    rw [Subtype.ext this]
  have hle := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 16), Fintype.card_fin, F.hH] at hle
  have hKd : Nat.card K ∣ 1152 := F.hH ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨m, hm⟩ := h9K
  rw [hm] at hle hKd ⊢
  have hm8 : m ≤ 8 := by omega
  interval_cases m <;> omega

end SwFacts

end CFSG.KS.U43Swap

end

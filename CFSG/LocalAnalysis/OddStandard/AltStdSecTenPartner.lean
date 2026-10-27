module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenPerm
public import CFSG.LocalAnalysis.OddStandard.AltStdSecOverCent
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarMain
public import CFSG.LocalAnalysis.OddStandard.AltStdSmallSylow

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z u : G}

theorem permHom_surjective (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) : Function.Surjective (permHom h d e) :=
  fun σ => ⟨⟨_, swapIota_mem_centralizer h d T e σ⟩, permOf_swapIota h d T e σ⟩

theorem card_comap_permHom (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) (K : Subgroup (Perm (Fin n))) :
    Nat.card (K.comap (permHom h d e)) = 2 * Nat.card K := by
  have hidx := Subgroup.index_comap_of_surjective (H := K) (permHom_surjective h d T e)
  have h1 := Subgroup.card_mul_index (K.comap (permHom h d e))
  have h2 := Subgroup.card_mul_index K
  have hCz := card_centralizer_eq_two_mul_factorial h d T.card T.cent T.outer T.sq e
  rw [hidx, hCz] at h1
  rw [Nat.card_perm, Nat.card_fin] at h2
  have hpos : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h3 : Nat.card (K.comap (permHom h d e)) * K.index = (2 * Nat.card K) * K.index := by
    rw [h1, ← h2]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos) h3

theorem comm_iff_permOf_comm (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {x y : G} (hx : x ∈ centralizer ({z} : Set G))
    (hy : y ∈ centralizer ({z} : Set G)) :
    x * y = y * x ↔ permOf h d e hx * permOf h d e hy = permOf h d e hy * permOf h d e hx := by
  constructor
  · intro hxy
    have h1 : (⟨x, hx⟩ : centralizer ({z} : Set G)) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ :=
      Subtype.ext hxy
    have h2 := congrArg (permHom h d e) h1
    rw [map_mul, map_mul] at h2
    exact h2
  · exact comm_of_permOf_comm h d T.card e hx hy

theorem card_inf_centralizer (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {b : G} (hb : b ∈ centralizer ({z} : Set G)) :
    Nat.card (centralizer ({z} : Set G) ⊓ centralizer ({b} : Set G) : Subgroup G) =
      2 * Nat.card (centralizer ({permOf h d e hb} : Set (Perm (Fin n)))) := by
  have key : (centralizer ({z} : Set G) ⊓ centralizer ({b} : Set G)).subgroupOf
      (centralizer ({z} : Set G)) =
      (centralizer ({permOf h d e hb} : Set (Perm (Fin n)))).comap (permHom h d e) := by
    ext y
    simp only [mem_subgroupOf, Subgroup.mem_comap, mem_inf, permHom_apply]
    constructor
    · rintro ⟨-, hyb⟩
      rw [mem_centralizer_singleton_iff] at hyb ⊢
      exact (comm_iff_permOf_comm h d T e y.2 hb).1 hyb
    · intro hy'
      rw [mem_centralizer_singleton_iff] at hy'
      exact ⟨y.2, mem_centralizer_singleton_iff.2 ((comm_iff_permOf_comm h d T e y.2 hb).2 hy')⟩
  rw [← card_comap_permHom h d T e, ← key]
  exact (Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv).symm

theorem card_inf_inf_centralizer (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {b c : G} (hb : b ∈ centralizer ({z} : Set G))
    (hc : c ∈ centralizer ({z} : Set G)) :
    Nat.card (centralizer ({z} : Set G) ⊓ centralizer ({b} : Set G) ⊓
        centralizer ({c} : Set G) : Subgroup G) =
      2 * Nat.card (centralizer ({permOf h d e hb} : Set (Perm (Fin n))) ⊓
        centralizer ({permOf h d e hc} : Set (Perm (Fin n))) : Subgroup (Perm (Fin n))) := by
  have key : (centralizer ({z} : Set G) ⊓ centralizer ({b} : Set G) ⊓
      centralizer ({c} : Set G)).subgroupOf (centralizer ({z} : Set G)) =
      (centralizer ({permOf h d e hb} : Set (Perm (Fin n))) ⊓
        centralizer ({permOf h d e hc} : Set (Perm (Fin n)))).comap (permHom h d e) := by
    ext y
    simp only [mem_subgroupOf, Subgroup.mem_comap, mem_inf, permHom_apply]
    constructor
    · rintro ⟨⟨-, hyb⟩, hyc⟩
      rw [mem_centralizer_singleton_iff] at hyb hyc
      exact ⟨mem_centralizer_singleton_iff.2 ((comm_iff_permOf_comm h d T e y.2 hb).1 hyb),
        mem_centralizer_singleton_iff.2 ((comm_iff_permOf_comm h d T e y.2 hc).1 hyc)⟩
    · rintro ⟨hyb, hyc⟩
      rw [mem_centralizer_singleton_iff] at hyb hyc
      exact ⟨⟨y.2, mem_centralizer_singleton_iff.2 ((comm_iff_permOf_comm h d T e y.2 hb).2 hyb)⟩,
        mem_centralizer_singleton_iff.2 ((comm_iff_permOf_comm h d T e y.2 hc).2 hyc)⟩
  rw [← card_comap_permHom h d T e, ← key]
  exact (Nat.card_congr (subgroupOfEquivOfLe (le_trans inf_le_left inf_le_left)).toEquiv).symm

omit [Finite G] in
theorem card_inf_centralizer_conj (g a b : G) :
    Nat.card (centralizer ({g * a * g⁻¹} : Set G) ⊓ centralizer ({g * b * g⁻¹} : Set G) :
        Subgroup G) =
      Nat.card (centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) : Subgroup G) := by
  have hconj : ∀ (x w : G), x * (g * w * g⁻¹) = (g * w * g⁻¹) * x →
      g⁻¹ * x * g * w = w * (g⁻¹ * x * g) := by
    intro x w hx
    calc g⁻¹ * x * g * w = g⁻¹ * (x * (g * w * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * w * g⁻¹) * x) * g := by rw [hx]
      _ = w * (g⁻¹ * x * g) := by group
  have hconj' : ∀ (y w : G), y * w = w * y →
      g * y * g⁻¹ * (g * w * g⁻¹) = (g * w * g⁻¹) * (g * y * g⁻¹) := by
    intro y w hy
    calc g * y * g⁻¹ * (g * w * g⁻¹) = g * (y * w) * g⁻¹ := by group
      _ = g * (w * y) * g⁻¹ := by rw [hy]
      _ = g * w * g⁻¹ * (g * y * g⁻¹) := by group
  refine Nat.card_congr ⟨fun x => ⟨g⁻¹ * x * g, ?_⟩, fun y => ⟨g * y * g⁻¹, ?_⟩, ?_, ?_⟩
  · obtain ⟨hxa, hxb⟩ := mem_inf.1 x.2
    exact mem_inf.2 ⟨mem_centralizer_singleton_iff.2
      (hconj x a (mem_centralizer_singleton_iff.1 hxa)),
      mem_centralizer_singleton_iff.2 (hconj x b (mem_centralizer_singleton_iff.1 hxb))⟩
  · obtain ⟨hya, hyb⟩ := mem_inf.1 y.2
    exact mem_inf.2 ⟨mem_centralizer_singleton_iff.2
      (hconj' y a (mem_centralizer_singleton_iff.1 hya)),
      mem_centralizer_singleton_iff.2 (hconj' y b (mem_centralizer_singleton_iff.1 hyb))⟩
  · intro x; ext; simp [mul_assoc]
  · intro y; ext; simp [mul_assoc]

section Ten

theorem card_centralizer_ten {σ : Perm (Fin 10)} (h2 : σ * σ = 1) :
    Nat.card (centralizer ({σ} : Set (Perm (Fin 10)))) =
      (10 - 2 * Multiset.card σ.cycleType).factorial * 2 ^ Multiset.card σ.cycleType *
        (Multiset.card σ.cycleType).factorial := by
  rw [nat_card_centralizer_of_mul_self h2, Fintype.card_fin]

theorem card_cycleType_le_five {σ : Perm (Fin 10)} (h2 : σ * σ = 1) :
    Multiset.card σ.cycleType ≤ 5 := by
  have h1 := card_support_eq_two_mul_card_cycleType h2
  have h3 : σ.support.card ≤ 10 := by
    have := Finset.card_le_univ σ.support
    rwa [Fintype.card_fin] at this
  omega

theorem eq_of_card_centralizer_ten {k j : ℕ} (hk : k ≤ 5) (hj : j ≤ 5)
    (h : (10 - 2 * k).factorial * 2 ^ k * k.factorial =
      (10 - 2 * j).factorial * 2 ^ j * j.factorial) : k = j := by
  interval_cases k <;> interval_cases j <;> simp_all [Nat.factorial]

theorem eq_five_four_of_card_ten {k m : ℕ} (hk2 : 2 ≤ k) (hk : k ≤ 5) (hm : m ≤ 5)
    (h : (10 - 2 * k).factorial * 2 ^ k * k.factorial =
      k * ((10 - 2 * m).factorial * 2 ^ m * m.factorial)) : k = 5 ∧ m = 4 := by
  interval_cases k <;> interval_cases m <;> simp_all [Nat.factorial]

end Ten

theorem false_of_centralizer_swap_le (h : Setting G L 10) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin 10))
    (hC : ∀ (x : G) (hx : x ∈ centralizer ({z} : Set G)), (permOf h d e hx).IsSwap →
      centralizer ({x} : Set G) ≤ centralizer ({z} : Set G)) : False := by
  classical
  have hz2 : z * z = 1 := d.mul_self
  obtain ⟨g, hne, hcomm, -, -⟩ := exists_partner h d
  set a : G := g⁻¹ * z * g with ha
  have haC : a ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hcomm
  have hga : g * a * g⁻¹ = z := by rw [ha]; group
  have ha2 : a * a = 1 := by
    calc a * a = g⁻¹ * (z * z) * g := by rw [ha]; group
      _ = 1 := by rw [hz2]; group
  set z' : G := g * z * g⁻¹ with hz'
  have hz'C : z' ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : g * (a * z) * g⁻¹ = g * (z * a) * g⁻¹ := by rw [hcomm]
    calc z' * z = g * (z * a) * g⁻¹ := by rw [hz', ← hga]; group
      _ = g * (a * z) * g⁻¹ := h1.symm
      _ = z * z' := by rw [hz', ← hga]; group
  have hz'2 : z' * z' = 1 := by
    calc z' * z' = g * (z * z) * g⁻¹ := by rw [hz']; group
      _ = 1 := by rw [hz2]; group
  set σ := permOf h d e haC with hσ
  set ζ := permOf h d e hz'C with hζ
  have hperm2 : ∀ {y : G} (hy : y ∈ centralizer ({z} : Set G)), y * y = 1 →
      permOf h d e hy * permOf h d e hy = 1 := by
    intro y hy hy2
    rw [← permOf_mul h d e hy hy (mul_mem hy hy)]
    rw [permOf_congr' hy2 (mul_mem hy hy) (one_mem _) h d e]
    unfold permOf
    exact map_one _
  have hσ2 : σ * σ = 1 := hperm2 haC ha2
  have hζ2 : ζ * ζ = 1 := hperm2 hz'C hz'2
  have hN₁ := card_inf_centralizer h d T e haC
  have hN₁' := card_inf_centralizer h d T e hz'C
  have hconjza := card_inf_centralizer_conj g a z
  rw [hga, ← hz', inf_comm (centralizer ({a} : Set G))] at hconjza
  have hσζ : Nat.card (centralizer ({σ} : Set (Perm (Fin 10)))) =
      Nat.card (centralizer ({ζ} : Set (Perm (Fin 10)))) := by
    have h1 : 2 * Nat.card (centralizer ({σ} : Set (Perm (Fin 10)))) =
        2 * Nat.card (centralizer ({ζ} : Set (Perm (Fin 10)))) := by
      rw [← hN₁, ← hN₁', hconjza]
    omega
  set k := Multiset.card σ.cycleType with hk
  have hk5 : k ≤ 5 := card_cycleType_le_five hσ2
  have hj5 := card_cycleType_le_five hζ2
  have hkj : k = Multiset.card ζ.cycleType := by
    rw [card_centralizer_ten hσ2, card_centralizer_ten hζ2] at hσζ
    exact eq_of_card_centralizer_ten hk5 hj5 hσζ
  have hσ1 : σ ≠ 1 := by
    intro h1
    rcases eq_swapIota_or h d T e haC with h2 | h2
    · rw [← hσ, h1, map_one] at h2
      apply hne
      have : a = 1 := h2
      have ho := d.order
      have : z = 1 := by
        calc z = g * a * g⁻¹ := hga.symm
          _ = 1 := by rw [this]; group
      rw [this, orderOf_one] at ho
      omega
    · rw [← hσ, h1, map_one] at h2
      exact hne (by simpa using h2)
  have hk0 : k ≠ 0 := fun h0 => hσ1 (card_cycleType_eq_zero.1 h0)
  have hk1 : k ≠ 1 := by
    intro h1
    have hsw : σ.IsSwap := by
      rw [← card_support_eq_two, card_support_eq_two_mul_card_cycleType hσ2, ← hk, h1]
    have hle := hC a haC hsw
    have hCa : Nat.card (centralizer ({a} : Set G)) = 2 * Nat.factorial 10 := by
      have := nat_card_centralizer_conj g⁻¹ z
      rw [inv_inv] at this
      rw [ha, this]
      exact card_centralizer_eq_two_mul_factorial h d T.card T.cent T.outer T.sq e
    have heq : centralizer ({z} : Set G) ⊓ centralizer ({a} : Set G) =
        centralizer ({a} : Set G) := inf_eq_right.2 hle
    rw [heq, hCa, card_centralizer_ten hσ2, ← hk, h1] at hN₁
    norm_num [Nat.factorial] at hN₁
  obtain ⟨τ, hτ⟩ : (σ.cycleFactorsFinset).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, cycleFactorsFinset_eq_empty_iff]
    exact hσ1
  have hτsw : τ.IsSwap := card_support_eq_two.1 (card_supp_eq_two_of_mem_cycleFactorsFinset hσ2 hτ)
  have hτσ : τ * σ = σ * τ := (self_mem_cycle_factors_commute hτ).eq
  set x : G := (swapIota h d T e τ : G) with hx
  have hxC : x ∈ centralizer ({z} : Set G) := swapIota_mem_centralizer h d T e τ
  have hxπ : permOf h d e hxC = τ := permOf_swapIota h d T e τ
  have hxa : x * a = a * x := by
    rw [comm_iff_permOf_comm h d T e hxC haC, hxπ]
    exact hτσ
  obtain ⟨hx2, -, -⟩ := swap_elt_facts h d T e hxC (by rw [hxπ]; exact hτsw)
  have hzxC : z * x ∈ centralizer ({z} : Set G) :=
    mul_mem (mem_centralizer_singleton_iff.2 rfl) hxC
  have hzxπ : permOf h d e hzxC = τ := by
    rw [permOf_mul h d e (mem_centralizer_singleton_iff.2 rfl) hxC hzxC, permOf_self, one_mul, hxπ]
  have hzxa : z * x * a = a * (z * x) := by
    rw [comm_iff_permOf_comm h d T e hzxC haC, hzxπ]
    exact hτσ
  have hzx2 : z * x * (z * x) = 1 := by
    have hxz : x * z = z * x := mem_centralizer_singleton_iff.1 hxC
    calc z * x * (z * x) = z * (x * z) * x := by group
      _ = z * (z * x) * x := by rw [hxz]
      _ = (z * z) * (x * x) := by group
      _ = 1 := by rw [hz2, hx2, one_mul]
  have hcompute : ∀ (y : G) (hy : y ∈ centralizer ({z} : Set G)), permOf h d e hy = τ →
      y * a = a * y → y * y = 1 →
      ∃ (hy' : g * y * g⁻¹ ∈ centralizer ({z} : Set G)),
        k = 5 ∧ Multiset.card (permOf h d e hy').cycleType = 4 := by
    intro y hy hyπ hya hy2
    have hy' : g * y * g⁻¹ ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc g * y * g⁻¹ * z = g * (y * a) * g⁻¹ := by rw [← hga]; group
        _ = g * (a * y) * g⁻¹ := by rw [hya]
        _ = z * (g * y * g⁻¹) := by rw [← hga]; group
    refine ⟨hy', ?_⟩
    have hy'2 : g * y * g⁻¹ * (g * y * g⁻¹) = 1 := by
      calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
        _ = 1 := by rw [hy2]; group
    set ξ := permOf h d e hy' with hξ
    have hξ2 : ξ * ξ = 1 := hperm2 hy' hy'2
    have hle := hC y hy (by rw [hyπ]; exact hτsw)
    have hN₂ := card_inf_inf_centralizer h d T e hy haC
    rw [hyπ] at hN₂
    have heq : centralizer ({z} : Set G) ⊓ centralizer ({y} : Set G) ⊓ centralizer ({a} : Set G) =
        centralizer ({y} : Set G) ⊓ centralizer ({a} : Set G) := by
      rw [inf_comm (centralizer ({z} : Set G)), inf_assoc, inf_comm (centralizer ({z} : Set G)),
        ← inf_assoc, inf_eq_left.2 (le_trans inf_le_left hle)]
    have hconj := card_inf_centralizer_conj g a y
    rw [hga, inf_comm (centralizer ({a} : Set G))] at hconj
    have hN₃ := card_inf_centralizer h d T e hy'
    have hmain := card_centralizer_inf_mul_card_cycleType hσ2 hτ
    have h1 : Nat.card (centralizer ({σ} : Set (Perm (Fin 10))) ⊓
        centralizer ({τ} : Set (Perm (Fin 10))) : Subgroup (Perm (Fin 10))) =
        Nat.card (centralizer ({ξ} : Set (Perm (Fin 10)))) := by
      have h2 : 2 * Nat.card (centralizer ({τ} : Set (Perm (Fin 10))) ⊓
          centralizer ({σ} : Set (Perm (Fin 10))) : Subgroup (Perm (Fin 10))) =
          2 * Nat.card (centralizer ({ξ} : Set (Perm (Fin 10)))) := by
        rw [← hN₂, heq, ← hconj, hN₃]
      rw [inf_comm]
      omega
    rw [h1, card_centralizer_ten hσ2, card_centralizer_ten hξ2, ← hk, mul_comm] at hmain
    have hkm := eq_five_four_of_card_ten (by omega) hk5 (card_cycleType_le_five hξ2) hmain.symm
    exact hkm
  obtain ⟨hgx, hk5', hξ4⟩ := hcompute x hxC hxπ hxa hx2
  obtain ⟨hgzx, -, hη4⟩ := hcompute (z * x) hzxC hzxπ hzxa hzx2
  have hsplit : g * (z * x) * g⁻¹ = z' * (g * x * g⁻¹) := by rw [hz']; group
  have hη : permOf h d e hgzx = ζ * permOf h d e hgx := by
    rw [permOf_congr' hsplit hgzx (mul_mem hz'C hgx) h d e,
      permOf_mul h d e hz'C hgx (mul_mem hz'C hgx)]
  have hgx2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hgzx2 : g * (z * x) * g⁻¹ * (g * (z * x) * g⁻¹) = 1 := by
    calc g * (z * x) * g⁻¹ * (g * (z * x) * g⁻¹) = g * (z * x * (z * x)) * g⁻¹ := by group
      _ = 1 := by rw [hzx2]; group
  have hs1 := AltStdSmall.sign_eq_neg_one_pow_of_mul_self (hperm2 hgzx hgzx2)
  have hs2 := AltStdSmall.sign_eq_neg_one_pow_of_mul_self hζ2
  have hs3 := AltStdSmall.sign_eq_neg_one_pow_of_mul_self (hperm2 hgx hgx2)
  rw [hη4] at hs1
  rw [← hkj, hk5'] at hs2
  rw [hξ4] at hs3
  rw [hη, map_mul, hs2, hs3] at hs1
  exact absurd hs1 (by decide)

end CFSG.OddStandard.AltStdSec

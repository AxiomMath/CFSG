module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G]
private def Ycong (Y : Subgroup G) (a b : G) : Prop := a⁻¹ * b ∈ Y

private lemma ycong_refl (Y : Subgroup G) (a : G) : Ycong Y a a := by
  show a⁻¹ * a ∈ Y
  rw [inv_mul_cancel]; exact Subgroup.one_mem Y
private lemma ycong_trans {Y : Subgroup G} {a b c : G}
    (h1 : Ycong Y a b) (h2 : Ycong Y b c) : Ycong Y a c := by
  show a⁻¹ * c ∈ Y
  rw [show a⁻¹ * c = (a⁻¹ * b) * (b⁻¹ * c) by group]
  exact Subgroup.mul_mem _ h1 h2
private lemma ycong_swap {Y K : Subgroup G}
    (hYc : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y)
    (hKc : ∀ a ∈ K, ∀ b ∈ K, a * b * a⁻¹ * b⁻¹ ∈ Y)
    {a b : G} (ha : a ∈ K) (hb : b ∈ K) : Ycong Y (a * b) (b * a) := by
  let z : G := a * b * a⁻¹ * b⁻¹
  have hzi : z ∈ Y := hKc a ha b hb
  have hcy := hYc z⁻¹ (Subgroup.inv_mem _ hzi) (b * a) (Subgroup.mul_mem _ hb ha)
  have hzab : a * b = z * (b * a) := by show a * b = (a * b * a⁻¹ * b⁻¹) * (b * a); group
  have heq : (a * b)⁻¹ * (b * a) = z⁻¹ := by
    calc (a * b)⁻¹ * (b * a) = (z * (b * a))⁻¹ * (b * a) := by rw [hzab]
      _ = ((b * a)⁻¹ * z⁻¹) * (b * a) := by rw [mul_inv_rev]
      _ = (b * a)⁻¹ * (z⁻¹ * (b * a)) := by group
      _ = (b * a)⁻¹ * ((b * a) * z⁻¹) := by rw [hcy]
      _ = z⁻¹ := by group
  show (a * b)⁻¹ * (b * a) ∈ Y
  rw [heq]; exact Subgroup.inv_mem _ hzi
private lemma ycong_mul {Y K : Subgroup G}
    (hYc : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y)
    {a a' b b' : G} (ha : Ycong Y a a') (hb : Ycong Y b b') (hb' : b' ∈ K) :
    Ycong Y (a * b) (a' * b') := by
  have hy : a⁻¹ * a' ∈ Y := ha
  have hcy := hYc (a⁻¹ * a') hy b' hb'
  have h2 : b⁻¹ * (a⁻¹ * a') * b' = (b⁻¹ * b') * (a⁻¹ * a') := by
    calc b⁻¹ * (a⁻¹ * a') * b' = b⁻¹ * ((a⁻¹ * a') * b') := by group
      _ = b⁻¹ * (b' * (a⁻¹ * a')) := by rw [hcy]
      _ = (b⁻¹ * b') * (a⁻¹ * a') := by group
  show (a * b)⁻¹ * (a' * b') ∈ Y
  rw [show (a * b)⁻¹ * (a' * b') = b⁻¹ * (a⁻¹ * a') * b' by group, h2]
  exact Subgroup.mul_mem _ hb hy
private lemma ycong_conj {Y : Subgroup G} {c : G}
    (hcY : ∀ y ∈ Y, c * y * c⁻¹ ∈ Y)
    {a b : G} (h : Ycong Y a b) : Ycong Y (c * a * c⁻¹) (c * b * c⁻¹) := by
  have key : (c * a * c⁻¹)⁻¹ * (c * b * c⁻¹) = c * (a⁻¹ * b) * c⁻¹ := by group
  show (c * a * c⁻¹)⁻¹ * (c * b * c⁻¹) ∈ Y
  rw [key]; exact hcY _ h
private lemma mem_of_ycong_of_mem {Y : Subgroup G} {a b : G}
    (h : Ycong Y a b) (hb : b ∈ Y) : a ∈ Y := by
  rw [show a = b * (a⁻¹ * b)⁻¹ by group]
  exact Subgroup.mul_mem _ hb (Subgroup.inv_mem _ h)
private lemma ycong_rotate3 {Y K : Subgroup G}
    (hYc : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y)
    (hKc : ∀ a ∈ K, ∀ b ∈ K, a * b * a⁻¹ * b⁻¹ ∈ Y)
    {a b c : G} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) :
    Ycong Y (a * b * c) (b * c * a) := by
  have hs : Ycong Y (a * b) (b * a) := ycong_swap hYc hKc ha hb
  have hs1 : (a * b * c)⁻¹ * (b * a * c) ∈ Y := by
    rw [show (a * b * c)⁻¹ * (b * a * c)
      = c⁻¹ * ((a * b)⁻¹ * (b * a)) * c by group]
    have hcy := hYc ((a * b)⁻¹ * (b * a)) hs c hc
    rw [show c⁻¹ * ((a * b)⁻¹ * (b * a)) * c = (a * b)⁻¹ * (b * a) by
      calc c⁻¹ * ((a * b)⁻¹ * (b * a)) * c
          = c⁻¹ * (((a * b)⁻¹ * (b * a)) * c) := by group
        _ = c⁻¹ * (c * ((a * b)⁻¹ * (b * a))) := by rw [hcy]
        _ = (a * b)⁻¹ * (b * a) := by group]
    exact hs
  have hs2 : (b * a * c)⁻¹ * (b * c * a) ∈ Y := by
    rw [show (b * a * c)⁻¹ * (b * c * a) = (a * c)⁻¹ * (c * a) by group]
    exact ycong_swap hYc hKc ha hc
  show (a * b * c)⁻¹ * (b * c * a) ∈ Y
  rw [show (a * b * c)⁻¹ * (b * c * a)
      = ((a * b * c)⁻¹ * (b * a * c)) * ((b * a * c)⁻¹ * (b * c * a)) by group]
  exact Subgroup.mul_mem _ hs1 hs2
theorem z18_norm_surj {Y : Subgroup G} (hY2 : ∀ y ∈ Y, y * y = 1)
    (hYc : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y) {a : G} (haY : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y)
    (ha2 : a * a = 1)
    (hcard : Nat.card Y = Nat.card ↥(Y ⊓ centralizer ({a} : Set G)) *
      Nat.card ↥(Y ⊓ centralizer ({a} : Set G))) :
    ∀ c ∈ Y, a * c = c * a → ∃ v ∈ Y, c = v * (a * v * a⁻¹) := by
  let nm : ↥Y →* ↥Y := MonoidHom.mk'
    (fun v => ⟨(v : G) * (a * (v : G) * a⁻¹),
      Subgroup.mul_mem _ v.2 (haY _ v.2)⟩) (fun u v => by
      apply Subtype.ext
      have hc : (a * (u : G) * a⁻¹) * (v : G) = (v : G) * (a * (u : G) * a⁻¹) :=
        hYc _ (haY _ u.2) _ v.2
      show (u : G) * (v : G) * (a * ((u : G) * (v : G)) * a⁻¹) =
        (u : G) * (a * (u : G) * a⁻¹) * ((v : G) * (a * (v : G) * a⁻¹))
      calc (u : G) * (v : G) * (a * ((u : G) * (v : G)) * a⁻¹)
          = (u : G) * ((v : G) * (a * (u : G) * a⁻¹)) *
              (a * (v : G) * a⁻¹) := by group
        _ = (u : G) * ((a * (u : G) * a⁻¹) * (v : G)) *
              (a * (v : G) * a⁻¹) := by rw [hc]
        _ = (u : G) * (a * (u : G) * a⁻¹) *
              ((v : G) * (a * (v : G) * a⁻¹)) := by group)
  have hker : nm.ker = (Y ⊓ centralizer ({a} : Set G)).subgroupOf Y := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h1
      have h2 : (v : G) * (a * (v : G) * a⁻¹) = 1 := congrArg Subtype.val h1
      refine ⟨v.2, ?_⟩
      have h3 : a * (v : G) * a⁻¹ = (v : G)⁻¹ := eq_inv_of_mul_eq_one_right h2
      have h4 : (v : G)⁻¹ = (v : G) := inv_eq_of_mul_eq_one_right (hY2 _ v.2)
      exact (mul_inv_eq_iff_eq_mul.mp (h3.trans h4)).symm
    · rintro ⟨-, h1⟩
      apply Subtype.ext
      show (v : G) * (a * (v : G) * a⁻¹) = 1
      have hvconj : a * (v : G) * a⁻¹ = (v : G) := by rw [← h1]; group
      rw [hvconj]; exact hY2 _ v.2
  have hrange : nm.range ≤ (Y ⊓ centralizer ({a} : Set G)).subgroupOf Y := by
    rintro _ ⟨v, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨(nm v).2, ?_⟩
    show (v : G) * (a * (v : G) * a⁻¹) * a = a * ((v : G) * (a * (v : G) * a⁻¹))
    have hc : (v : G) * (a * (v : G) * a⁻¹) = (a * (v : G) * a⁻¹) * (v : G) :=
      hYc _ v.2 _ (haY _ v.2)
    have key : a * ((v : G) * (a * (v : G) * a⁻¹)) * a⁻¹ =
        (v : G) * (a * (v : G) * a⁻¹) := by
      calc a * ((v : G) * (a * (v : G) * a⁻¹)) * a⁻¹
          = (a * (v : G) * a⁻¹) * ((a * a) * (v : G) * (a * a)⁻¹) := by group
        _ = (a * (v : G) * a⁻¹) * (v : G) := by rw [ha2]; group
        _ = (v : G) * (a * (v : G) * a⁻¹) := hc.symm
    exact (mul_inv_eq_iff_eq_mul.mp key).symm
  have hsub : Nat.card ↥((Y ⊓ centralizer ({a} : Set G)).subgroupOf Y) =
      Nat.card ↥(Y ⊓ centralizer ({a} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left)).toEquiv
  have hcardker : Nat.card nm.ker = Nat.card ↥(Y ⊓ centralizer ({a} : Set G)) := by
    rw [hker, hsub]
  have hcardrange : Nat.card nm.range ≤ Nat.card ↥(Y ⊓ centralizer ({a} : Set G)) := by
    have := Subgroup.card_le_of_le hrange
    rwa [hsub] at this
  have hlow := card_ker_mul_card_range nm
  rw [hcard, hcardker] at hlow
  have hCpos : 0 < Nat.card ↥(Y ⊓ centralizer ({a} : Set G)) :=
    Finite.card_pos_iff.mpr (Nonempty.intro (1 : ↥(Y ⊓ centralizer ({a} : Set G))))
  have hrangeeq : Nat.card nm.range = Nat.card ↥(Y ⊓ centralizer ({a} : Set G)) :=
    Nat.mul_left_cancel hCpos hlow
  have hrange_eq : nm.range = (Y ⊓ centralizer ({a} : Set G)).subgroupOf Y :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [hsub, hrangeeq])
  intro c hcY hca
  have hcC : c ∈ Y ⊓ centralizer ({a} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hcY, Subgroup.mem_centralizer_singleton_iff.mpr hca.symm⟩
  have hc_mem : (⟨c, hcY⟩ : ↥Y) ∈ (Y ⊓ centralizer ({a} : Set G)).subgroupOf Y := by
    rw [Subgroup.mem_subgroupOf]; exact hcC
  have hc_range : (⟨c, hcY⟩ : ↥Y) ∈ nm.range := by rw [hrange_eq]; exact hc_mem
  obtain ⟨v, hv⟩ := hc_range
  exact ⟨(v : G), v.2, (congrArg Subtype.val hv).symm⟩
theorem z18_coh_step {K Y : Subgroup G} {u ρ : G} (hYK : Y ≤ K)
    (hYc : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y)
    (hK2 : ∀ k ∈ K, k * k ∈ Y) (hKc : ∀ a ∈ K, ∀ b ∈ K, a * b * a⁻¹ * b⁻¹ ∈ Y)
    (hρK : ∀ k ∈ K, ρ * k * ρ⁻¹ ∈ K) (hρY : ∀ y ∈ Y, ρ * y * ρ⁻¹ ∈ Y)
    (huK : ∀ k ∈ K, u * k * u⁻¹ ∈ K) (huY : ∀ y ∈ Y, u * y * u⁻¹ ∈ Y)
    (hρ3 : ρ ^ 3 = 1) (hu2 : u * u = 1) (huρ : u * ρ * u⁻¹ = ρ⁻¹)
    (hfix : ∀ k ∈ K, ρ * k * ρ⁻¹ * k⁻¹ ∈ Y → k ∈ Y)
    {k : G} (hk : k ∈ K) (hkinv : (u * k) * (u * k) = 1) :
    ∃ w ∈ K, (u * w * u⁻¹)⁻¹ * k * w ∈ Y := by
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have huk : u * k * u⁻¹ = k⁻¹ := by
    have h1 : (u * k * u) * k = 1 := by
      calc (u * k * u) * k = (u * k) * (u * k) := by group
        _ = 1 := hkinv
    rw [hu_inv, eq_inv_of_mul_eq_one_left h1]
  let k1 : G := ρ * k * ρ⁻¹
  let k2 : G := ρ * k1 * ρ⁻¹
  have hk1K : k1 ∈ K := hρK k hk
  have hk2K : k2 ∈ K := hρK k1 hk1K
  have hρ3' : ρ * ρ * ρ = 1 := by simpa [pow_succ, pow_two] using hρ3
  have hρinv : ρ⁻¹ = ρ * ρ :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hρ3')
  have hρinv2 : ρ⁻¹ * ρ⁻¹ = ρ := by
    rw [hρinv]
    calc ρ * ρ * (ρ * ρ) = ρ * (ρ * ρ * ρ) := by group
      _ = ρ := by rw [hρ3']; group
  have hρinv3 : ρ⁻¹ * ρ⁻¹ * ρ⁻¹ = 1 := by
    rw [hρinv]
    calc ρ * ρ * (ρ * ρ) * (ρ * ρ) = (ρ * ρ * ρ) * (ρ * ρ * ρ) := by group
      _ = 1 := by rw [hρ3']; group
  have hk3 : ρ * k2 * ρ⁻¹ = k := by
    show ρ * (ρ * (ρ * k * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ = k
    calc ρ * (ρ * (ρ * k * ρ⁻¹) * ρ⁻¹) * ρ⁻¹
        = (ρ * ρ * ρ) * k * (ρ⁻¹ * ρ⁻¹ * ρ⁻¹) := by group
      _ = 1 * k * 1 := by rw [hρ3', hρinv3]
      _ = k := by group
  let p : G := k * k1 * k2
  have hpK : p ∈ K := Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hk1K) hk2K
  have hpconj : ρ * p * ρ⁻¹ = k1 * k2 * k := by
    show ρ * (k * k1 * k2) * ρ⁻¹ = k1 * k2 * k
    calc ρ * (k * k1 * k2) * ρ⁻¹
        = (ρ * k * ρ⁻¹) * (ρ * k1 * ρ⁻¹) * (ρ * k2 * ρ⁻¹) := by group
      _ = k1 * k2 * k := by rw [hk3]
  have hcong_a : Ycong Y (u * k * u⁻¹) k := by
    show (u * k * u⁻¹)⁻¹ * k ∈ Y
    rw [huk]; simpa using hK2 k hk
  have hρinvY : ∀ y ∈ Y, ρ⁻¹ * y * (ρ⁻¹)⁻¹ ∈ Y := by
    intro y hy
    have h2 : ρ * (ρ * y * ρ⁻¹) * ρ⁻¹ ∈ Y := hρY _ (hρY y hy)
    have e1 : ρ⁻¹ * y * ρ = (ρ * ρ) * y * ρ := congrArg (fun t => t * y * ρ) hρinv
    have e2 : (ρ * ρ) * y * ρ = (ρ * ρ) * y * (ρ⁻¹ * ρ⁻¹) :=
      congrArg (fun t => (ρ * ρ) * y * t) hρinv2.symm
    have he : ρ⁻¹ * y * ρ = ρ * (ρ * y * ρ⁻¹) * ρ⁻¹ := by rw [e1, e2]; group
    rw [← he] at h2
    simpa [inv_inv] using h2
  have hρinv_k : ρ⁻¹ * k * ρ = ρ * (ρ * k * ρ⁻¹) * ρ⁻¹ := by
    have e1 : ρ⁻¹ * k * ρ = (ρ * ρ) * k * ρ := congrArg (fun t => t * k * ρ) hρinv
    have e2 : (ρ * ρ) * k * ρ = (ρ * ρ) * k * (ρ⁻¹ * ρ⁻¹) :=
      congrArg (fun t => (ρ * ρ) * k * t) hρinv2.symm
    rw [e1, e2]; group
  have huw : u * k1 * u⁻¹ = ρ⁻¹ * (u * k * u⁻¹) * ρ := by
    show u * (ρ * k * ρ⁻¹) * u⁻¹ = ρ⁻¹ * (u * k * u⁻¹) * ρ
    calc u * (ρ * k * ρ⁻¹) * u⁻¹
        = (u * ρ * u⁻¹) * (u * k * u⁻¹) * (u * ρ * u⁻¹)⁻¹ := by group
      _ = ρ⁻¹ * (u * k * u⁻¹) * (ρ⁻¹)⁻¹ := by rw [huρ]
      _ = ρ⁻¹ * (u * k * u⁻¹) * ρ := by rw [inv_inv]
  have hcong_c : Ycong Y (u * k1 * u⁻¹) k2 := by
    rw [huw]
    have h := ycong_conj (c := ρ⁻¹) hρinvY hcong_a
    rw [inv_inv] at h
    rwa [hρinv_k] at h
  have hxK : u * k1 * u⁻¹ ∈ K := huK k1 hk1K
  have hcx : Ycong Y (u * k1 * u⁻¹)⁻¹ k2 := by
    show ((u * k1 * u⁻¹)⁻¹)⁻¹ * k2 ∈ Y
    have hx2 : (u * k1 * u⁻¹) * (u * k1 * u⁻¹) ∈ Y := hK2 _ hxK
    have key : ((u * k1 * u⁻¹)⁻¹)⁻¹ * k2 =
        ((u * k1 * u⁻¹) * (u * k1 * u⁻¹)) * ((u * k1 * u⁻¹)⁻¹ * k2) := by group
    rw [key]; exact Subgroup.mul_mem _ hx2 hcong_c
  have hstep : Ycong Y ((u * k1 * u⁻¹)⁻¹ * k) (k2 * k) :=
    ycong_mul hYc hcx (ycong_refl Y k) hk
  have hmul : Ycong Y ((u * k1 * u⁻¹)⁻¹ * k * k1) (k2 * k * k1) :=
    ycong_mul hYc hstep (ycong_refl Y k1) hk1K
  have hrot : Ycong Y (k2 * k * k1) (k * k1 * k2) :=
    ycong_rotate3 hYc hKc hk2K hk hk1K
  have hs : p⁻¹ * (k1 * k2 * k) ∈ Y := ycong_rotate3 hYc hKc hk hk1K hk2K
  have hfixin : ρ * p * ρ⁻¹ * p⁻¹ ∈ Y := by
    have hcy := hYc _ hs p hpK
    have heq : ρ * p * ρ⁻¹ * p⁻¹ = p * (p⁻¹ * (k1 * k2 * k)) * p⁻¹ := by
      rw [hpconj]; group
    have hy : p * (p⁻¹ * (k1 * k2 * k)) * p⁻¹ = p⁻¹ * (k1 * k2 * k) := by
      rw [← hcy]; group
    rw [heq, hy]; exact hs
  have hpY : p ∈ Y := hfix p hpK hfixin
  exact ⟨k1, hk1K, mem_of_ycong_of_mem (ycong_trans hmul hrot) hpY⟩
theorem z18_coh {K Y : Subgroup G} {u ρ : G} (hYK : Y ≤ K)
    (hYc : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y) (hY2 : ∀ y ∈ Y, y * y = 1)
    (hK2 : ∀ k ∈ K, k * k ∈ Y) (hKc : ∀ a ∈ K, ∀ b ∈ K, a * b * a⁻¹ * b⁻¹ ∈ Y)
    (hρK : ∀ k ∈ K, ρ * k * ρ⁻¹ ∈ K) (hρY : ∀ y ∈ Y, ρ * y * ρ⁻¹ ∈ Y)
    (huK : ∀ k ∈ K, u * k * u⁻¹ ∈ K) (huY : ∀ y ∈ Y, u * y * u⁻¹ ∈ Y)
    (hρ3 : ρ ^ 3 = 1) (hu2 : u * u = 1) (huρ : u * ρ * u⁻¹ = ρ⁻¹)
    (hfix : ∀ k ∈ K, ρ * k * ρ⁻¹ * k⁻¹ ∈ Y → k ∈ Y)
    (hcard : Nat.card Y = Nat.card ↥(Y ⊓ centralizer ({u} : Set G)) *
      Nat.card ↥(Y ⊓ centralizer ({u} : Set G))) :
    ∀ k ∈ K, (u * k) * (u * k) = 1 → ∃ w ∈ K, w * u * w⁻¹ = u * k := by
  intro k hk hkinv
  obtain ⟨w₁, hw₁K, hk2Y⟩ := z18_coh_step hYK hYc hK2 hKc hρK hρY huK huY
    hρ3 hu2 huρ hfix hk hkinv
  let k₂ : G := (u * w₁ * u⁻¹)⁻¹ * k * w₁
  have hk2K : k₂ ∈ K := hYK hk2Y
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hw1u : w₁⁻¹ * u = u * (u * w₁ * u⁻¹)⁻¹ := by
    rw [show (u * w₁ * u⁻¹)⁻¹ = u * w₁⁻¹ * u by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, hu_inv]; group]
    calc w₁⁻¹ * u = (u * u) * w₁⁻¹ * u := by rw [hu2]; group
      _ = u * (u * w₁⁻¹ * u) := by group
  have hconj : w₁⁻¹ * (u * k) * w₁ = u * k₂ := by
    have h1 : w₁⁻¹ * (u * k) * w₁ = (w₁⁻¹ * u) * k * w₁ := by group
    rw [h1, hw1u]
    show u * (u * w₁ * u⁻¹)⁻¹ * k * w₁ = u * ((u * w₁ * u⁻¹)⁻¹ * k * w₁)
    group
  have huk2sq : (u * k₂) * (u * k₂) = 1 := by
    rw [← hconj]
    calc (w₁⁻¹ * (u * k) * w₁) * (w₁⁻¹ * (u * k) * w₁)
        = w₁⁻¹ * ((u * k) * (u * k)) * w₁ := by group
      _ = 1 := by rw [hkinv]; group
  have huk2 : u * k₂ * u⁻¹ = k₂ := by
    have h1 : (u * k₂ * u) * k₂ = 1 := by
      calc (u * k₂ * u) * k₂ = (u * k₂) * (u * k₂) := by group
        _ = 1 := huk2sq
    have h2 : u * k₂ * u = k₂⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [hu_inv, h2]
    exact inv_eq_of_mul_eq_one_right (hY2 k₂ hk2Y)
  have hcomm : u * k₂ = k₂ * u := by
    have h2 : u * k₂ * u = k₂ := by simpa [hu_inv] using huk2
    calc u * k₂ = (u * k₂) * (u * u) := by rw [hu2]; group
      _ = (u * k₂ * u) * u := by group
      _ = k₂ * u := by rw [h2]
  have hYcY : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y :=
    fun y hy y' hy' => hYc y hy y' (hYK hy')
  obtain ⟨v, hvY, hnorm⟩ := z18_norm_surj hY2 hYcY huY hu2 hcard k₂ hk2Y hcomm
  have hvK : v ∈ K := hYK hvY
  have hv_inv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hY2 v hvY)
  have hvu : v * u * v⁻¹ = u * k₂ := by
    have hcommY : (u * v * u⁻¹) * v = v * (u * v * u⁻¹) :=
      hYcY (u * v * u⁻¹) (huY v hvY) v hvY
    calc v * u * v⁻¹ = u * ((u * v * u⁻¹) * v) := by
          rw [hv_inv]
          calc v * u * v = (u * u) * v * u⁻¹ * v := by rw [hu2, hu_inv]; group
            _ = u * ((u * v * u⁻¹) * v) := by group
      _ = u * (v * (u * v * u⁻¹)) := by rw [hcommY]
      _ = u * k₂ := by rw [← hnorm]
  have hk2wi : k₂ * w₁⁻¹ = w₁⁻¹ * k₂ :=
    hYc k₂ hk2Y w₁⁻¹ (Subgroup.inv_mem _ hw₁K)
  have hwu : (w₁ * v) * u * (w₁ * v)⁻¹ = (w₁ * u * w₁⁻¹) * k₂ := by
    calc (w₁ * v) * u * (w₁ * v)⁻¹ = w₁ * (v * u * v⁻¹) * w₁⁻¹ := by group
      _ = w₁ * (u * k₂) * w₁⁻¹ := by rw [hvu]
      _ = w₁ * u * (k₂ * w₁⁻¹) := by group
      _ = w₁ * u * (w₁⁻¹ * k₂) := by rw [hk2wi]
      _ = (w₁ * u * w₁⁻¹) * k₂ := by group
  have huk : u * k = (w₁ * u * w₁⁻¹) * k₂ := by
    have h1 : u * k = w₁ * (w₁⁻¹ * (u * k) * w₁) * w₁⁻¹ := by group
    rw [h1, hconj]
    calc w₁ * (u * k₂) * w₁⁻¹ = w₁ * u * (k₂ * w₁⁻¹) := by group
      _ = w₁ * u * (w₁⁻¹ * k₂) := by rw [hk2wi]
      _ = (w₁ * u * w₁⁻¹) * k₂ := by group
  exact ⟨w₁ * v, Subgroup.mul_mem _ hw₁K hvK, hwu.trans huk.symm⟩
end CFSG.OddStandard.SmallF3.HarrisU33.S4A

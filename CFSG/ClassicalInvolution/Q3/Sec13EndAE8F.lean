module

public import CFSG.ClassicalInvolution.Q3.Sec13End18D
public import CFSG.ClassicalInvolution.Q3.Sec13End15F
public import CFSG.ClassicalInvolution.Q3.Sec13EndS3E8
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf52Aut
import CFSG.ClassicalInvolution.Q3.Sec13PerpPair

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

private theorem e8f_pow_conj_fix {c k z : G} (hc1 : c * k * c⁻¹ = k) (hc2 : c * z * c⁻¹ = z)
    (n : ℕ) : c ^ n * k * (c ^ n)⁻¹ = k ∧ c ^ n * z * (c ^ n)⁻¹ = z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    constructor
    · calc c ^ n * c * k * (c ^ n * c)⁻¹ = c ^ n * (c * k * c⁻¹) * (c ^ n)⁻¹ := by group
        _ = c ^ n * k * (c ^ n)⁻¹ := by rw [hc1]
        _ = k := ih.1
    · calc c ^ n * c * z * (c ^ n * c)⁻¹ = c ^ n * (c * z * c⁻¹) * (c ^ n)⁻¹ := by group
        _ = c ^ n * z * (c ^ n)⁻¹ := by rw [hc2]
        _ = z := ih.2

private theorem e8f_sq_of_q8 {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) {x : G}
    (hx : x ∈ K) (hxz : x ∉ Subgroup.zpowers z) : x * x = z := by
  have hzz : z * z = 1 := hQ.inv.sq
  have hzi : z * i = i * z := by rw [← hQ.sq_i]; group
  have hzj : z * j = j * z := by rw [← hQ.sq_j]; group
  have hww : (i * j) * (i * j) = z := by
    calc (i * j) * (i * j) = i * (j * i) * j := by group
      _ = i * (z * (i * j)) * j := by rw [hQ.comm]
      _ = (i * z) * (i * j) * j := by group
      _ = (z * i) * (i * j) * j := by rw [← hzi]
      _ = z * (i * i) * (j * j) := by group
      _ = z := by rw [hQ.sq_i, hQ.sq_j, hzz, one_mul]
  have hwz : (i * j) * z = z * (i * j) := by
    calc (i * j) * z = i * (j * z) := by group
      _ = i * (z * j) := by rw [← hzj]
      _ = (i * z) * j := by group
      _ = (z * i) * j := by rw [← hzi]
      _ = z * (i * j) := by group
  rcases hQ.nf x hx with h | h | h | h | h | h | h | h <;> rw [h]
  · exact absurd (Subgroup.one_mem _) (h ▸ hxz)
  · exact absurd (Subgroup.mem_zpowers z) (h ▸ hxz)
  · exact hQ.sq_i
  · calc z * i * (z * i) = z * (i * z) * i := by group
      _ = z * (z * i) * i := by rw [← hzi]
      _ = (z * z) * (i * i) := by group
      _ = z := by rw [hzz, hQ.sq_i, one_mul]
  · exact hQ.sq_j
  · calc z * j * (z * j) = z * (j * z) * j := by group
      _ = z * (z * j) * j := by rw [← hzj]
      _ = (z * z) * (j * j) := by group
      _ = z := by rw [hzz, hQ.sq_j, one_mul]
  · exact hww
  · calc z * (i * j) * (z * (i * j)) = z * ((i * j) * z) * (i * j) := by group
      _ = z * (z * (i * j)) * (i * j) := by rw [hwz]
      _ = (z * z) * ((i * j) * (i * j)) := by group
      _ = z := by rw [hzz, hww, one_mul]

private theorem e8f_ij_sq {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) :
    (i * j) * (i * j) = z := by
  have hzz : z * z = 1 := hQ.inv.sq
  have hzi : z * i = i * z := by rw [← hQ.sq_i]; group
  calc (i * j) * (i * j) = i * (j * i) * j := by group
    _ = i * (z * (i * j)) * j := by rw [hQ.comm]
    _ = (i * z) * (i * j) * j := by group
    _ = (z * i) * (i * j) * j := by rw [← hzi]
    _ = z * (i * i) * (j * j) := by group
    _ = z := by rw [hQ.sq_i, hQ.sq_j, hzz, one_mul]

private theorem e8f_orderOf_four {k z : G} (hzz : z * z = 1) (hz1 : z ≠ 1) (hkk : k * k = z) :
    orderOf k = 4 := by
  have hnot : ¬ k ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq, hkk]
    exact hz1
  have hfin : k ^ 2 ^ (1 + 1) = 1 := by
    rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 from rfl, pow_add, sq, hkk, hzz]
  have h := orderOf_eq_prime_pow hnot hfin
  simpa using h

private theorem e8f_card_q8 {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) :
    Nat.card K = 8 := by
  classical
  have hzz : z * z = 1 := hQ.inv.sq
  have hz1 : z ≠ 1 := hQ.inv.ne_one
  have hup : Nat.card K ≤ 8 := by
    have hsub : (K : Set G) ⊆ ↑([1, z, i, z * i, j, z * j, i * j, z * (i * j)].toFinset) := by
      intro x hx
      rcases hQ.nf x hx with h | h | h | h | h | h | h | h <;> simp [h]
    have hS := List.toFinset_card_le [1, z, i, z * i, j, z * j, i * j, z * (i * j)]
    calc Nat.card K = (K : Set G).ncard := Nat.card_coe_set_eq (K : Set G)
      _ ≤ (↑([1, z, i, z * i, j, z * j, i * j, z * (i * j)].toFinset) : Set G).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ([1, z, i, z * i, j, z * j, i * j, z * (i * j)].toFinset).card :=
          Set.ncard_coe_finset _
      _ ≤ 8 := by simpa using hS
  have hlow : 8 ≤ Nat.card K := by
    have hi4 : orderOf i = 4 := e8f_orderOf_four hzz hz1 hQ.sq_i
    have hHK : Subgroup.zpowers i ≤ K := Subgroup.zpowers_le.mpr hQ.mem_i
    have hcard : Nat.card (Subgroup.zpowers i) = 4 := by rw [Nat.card_zpowers, hi4]
    have hjH : j ∉ Subgroup.zpowers i := by
      intro hj
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hj
      have hc : Commute i j := by
        rw [← hn]
        exact (Commute.refl i).zpow_right n
      have h3 : (1 : G) * (i * j) = z * (i * j) := by
        rw [one_mul]
        exact hc.eq.trans hQ.comm
      exact hz1 (mul_right_cancel h3).symm
    have hrel1 : (Subgroup.zpowers i).relIndex K ≠ 1 := fun h =>
      hjH ((Subgroup.relIndex_eq_one.mp h) hQ.mem_j)
    have hmul := Subgroup.relIndex_mul_card (H := Subgroup.zpowers i) (K := K)
    rw [inf_of_le_left hHK, hcard] at hmul
    have hpos : 0 < Nat.card K := Nat.card_pos
    have hrel0 : (Subgroup.zpowers i).relIndex K ≠ 0 := by
      intro h
      rw [h, zero_mul] at hmul
      omega
    have hrel2 : 2 ≤ (Subgroup.zpowers i).relIndex K := by omega
    omega
  omega

theorem q8_centralizes_of_odd_fixes {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) {y : G}
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) (hodd : Odd (orderOf y)) {k : G} (hk : k ∈ K)
    (hkz : k ∉ Subgroup.zpowers z)
    (hfix : y * k * y⁻¹ = k ∨ y * k * y⁻¹ = k * z) : ∀ k' ∈ K, y * k' * y⁻¹ = k' := by
  have hz := hQ.inv
  have hzz : z * z = 1 := hz.sq
  have hz1 : z ≠ 1 := hz.ne_one
  have hK8 : Nat.card K = 8 := e8f_card_q8 hQ
  have hkk : k * k = z := e8f_sq_of_q8 hQ hk hkz
  have hk4 : orderOf k = 4 := e8f_orderOf_four hzz hz1 hkk
  have hyz : y * z * y⁻¹ = z := conj_eq_self_of_normalizer hz hyN
  have hfix' : y * k * y⁻¹ = k := by
    rcases hfix with h | h
    · exact h
    · exfalso
      obtain ⟨s, hs⟩ := hodd
      have h2k : y * y * k * (y * y)⁻¹ = k := by
        calc y * y * k * (y * y)⁻¹ = y * (y * k * y⁻¹) * y⁻¹ := by group
          _ = y * (k * z) * y⁻¹ := by rw [h]
          _ = (y * k * y⁻¹) * (y * z * y⁻¹) := by group
          _ = (k * z) * z := by rw [h, hyz]
          _ = k := by rw [mul_assoc, hzz, mul_one]
      have h2z : y * y * z * (y * y)⁻¹ = z := by
        calc y * y * z * (y * y)⁻¹ = y * (y * z * y⁻¹) * y⁻¹ := by group
          _ = z := by rw [hyz, hyz]
      obtain ⟨hpk, -⟩ := e8f_pow_conj_fix h2k h2z s
      have hpow : y ^ (2 * s + 1) = (y * y) ^ s * y := by
        rw [pow_succ, pow_mul, sq]
      have hyn : y ^ (2 * s + 1) = 1 := by
        rw [← hs]
        exact pow_orderOf_eq_one y
      have hk' : y ^ (2 * s + 1) * k * (y ^ (2 * s + 1))⁻¹ = k * z := by
        rw [hpow]
        calc (y * y) ^ s * y * k * ((y * y) ^ s * y)⁻¹
            = (y * y) ^ s * (y * k * y⁻¹) * ((y * y) ^ s)⁻¹ := by group
          _ = (y * y) ^ s * (k * z) * ((y * y) ^ s)⁻¹ := by rw [h]
          _ = ((y * y) ^ s * k * ((y * y) ^ s)⁻¹) * ((y * y) ^ s * z * ((y * y) ^ s)⁻¹) := by
              group
          _ = k * z := by
              rw [hpk, (e8f_pow_conj_fix h2k h2z s).2]
      rw [hyn] at hk'
      simp only [inv_one, mul_one, one_mul] at hk'
      have hz' : z = 1 := by
        have h3 := congrArg (fun t => k⁻¹ * t) hk'
        simpa using h3.symm
      exact hz1 hz'
  have hc := PhilipHall.Frame.TwinPerpV3.centralizes_of_odd_fix' hK8 hk hk4 hyN hodd hfix'
  intro k' hk'
  have h := hc k' hk'
  calc y * k' * y⁻¹ = k' * y * y⁻¹ := by rw [← h]
    _ = k' := by group


namespace End18

namespace Hyp

variable {Ω : Set (Subgroup G)}

private theorem e8f_map_one {V : Type*} [Group V] {F : V → ZMod 2}
    (hF : ∀ x y, F (x * y) = F x + F y) : F 1 = 0 := by
  have e : F 1 = F 1 + F 1 := by
    have h := hF 1 1
    rwa [mul_one] at h
  have key : ∀ t : ZMod 2, t = t + t → t = 0 := by decide
  exact key _ e

private theorem e8f_map_inv {V : Type*} [Group V] {F : V → ZMod 2}
    (hF : ∀ x y, F (x * y) = F x + F y) (y : V) : F y⁻¹ = F y := by
  have e : 0 = F y⁻¹ + F y := by
    have h := hF y⁻¹ y
    rwa [inv_mul_cancel, e8f_map_one hF] at h
  have key : ∀ p q : ZMod 2, 0 = p + q → p = q := by decide
  exact key _ _ e

private theorem e8f_symm {V : Type*} [Group V] {bf : V → V → ZMod 2}
    (hL : ∀ a a' b : V, bf (a * a') b = bf a b + bf a' b)
    (hR : ∀ a b b' : V, bf a (b * b') = bf a b + bf a b') (halt : ∀ a : V, bf a a = 0)
    (a b : V) : bf a b = bf b a := by
  have h := halt (a * b)
  simp only [hL, hR, halt, zero_add, add_zero] at h
  have key : ∀ p q : ZMod 2, p + q = 0 → p = q := by decide
  exact key _ _ h

private theorem e8f_closure_zPoints (Ω : Set (Subgroup G)) :
    Subgroup.closure (zPoints Ω) = ⊤ :=
  Subgroup.closure_closure_coe_preimage (k := zSet Ω)

private theorem e8f_eq_of_eq_on_zPoints {Ω : Set (Subgroup G)}
    (hgen : Subgroup.closure (zPoints Ω) = ⊤) {F F' : zGroup Ω → ZMod 2}
    (hF : ∀ x y, F (x * y) = F x + F y) (hF' : ∀ x y, F' (x * y) = F' x + F' y)
    (h : ∀ x ∈ zPoints Ω, F x = F' x) (x : zGroup Ω) : F x = F' x := by
  have hx : x ∈ Subgroup.closure (zPoints Ω) := by
    rw [hgen]
    exact Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact h y hy
  | one => rw [e8f_map_one hF, e8f_map_one hF']
  | mul y z _ _ hy hz => rw [hF, hF', hy, hz]
  | inv y _ hy => rw [e8f_map_inv hF, e8f_map_inv hF', hy]

private theorem e8f_conj_mem {Ω : Set (Subgroup G)} (h : EndHyp Ω) (g : G) {a : G}
    (ha : a ∈ zGroup Ω) : g * a * g⁻¹ ∈ zGroup Ω :=
  (zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant).conj_mem a ha g

private def e8f_cj {Ω : Set (Subgroup G)} (h : EndHyp Ω) (g : G) (a : zGroup Ω) : zGroup Ω :=
  ⟨g * a.1 * g⁻¹, e8f_conj_mem h g a.2⟩

private theorem e8f_cj_val {Ω : Set (Subgroup G)} (h : EndHyp Ω) (g : G) (a : zGroup Ω) :
    (e8f_cj h g a).1 = g * a.1 * g⁻¹ :=
  rfl

private theorem e8f_normalizer_conj (g d : G) (A : Subgroup G) :
    g * d * g⁻¹ ∈ Subgroup.normalizer (conjSub g A : Set G) ↔
      d ∈ Subgroup.normalizer (A : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq, mem_normalizer_iff_conjSub_eq]
  have e : conjSub (g * d * g⁻¹) (conjSub g A) = conjSub g (conjSub d A) := by
    rw [conjSub_mul, conjSub_mul, conjSub_inv_conjSub]
  rw [e]
  exact (conjSub_injective g).eq_iff

open Classical in
private theorem e8f_bnorm_eq_zero_iff (M : Subgroup G) (d : G) :
    bnorm M d = 0 ↔ d ∈ Subgroup.normalizer (M : Set G) := by
  unfold bnorm
  by_cases hd : d ∈ Subgroup.normalizer (M : Set G)
  · rw [if_pos hd]
    exact ⟨fun _ => hd, fun _ => rfl⟩
  · rw [if_neg hd]
    exact ⟨fun h1 => absurd h1 (by decide), fun h1 => absurd h1 hd⟩

private theorem e8f_mul_normalizer (H : Hyp Ω) {B : Subgroup G} (hB : B ∈ Ω) {x y : G}
    (hx : x ∈ zGroup Ω) (hy : y ∈ zGroup Ω)
    (hxN : x ∉ Subgroup.normalizer (B : Set G)) (hyN : y ∉ Subgroup.normalizer (B : Set G)) :
    x * y ∈ Subgroup.normalizer (B : Set G) := by
  have hN := H.relIndex_inf_normalizer hB
  obtain ⟨a, ha, -, hall⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp hN
  have hxa : x * a ∈ zGroup Ω ⊓ Subgroup.normalizer (B : Set G) :=
    (hall x hx).resolve_right (fun h => hxN (Subgroup.mem_inf.mp h).2)
  have hya : y * a ∈ zGroup Ω ⊓ Subgroup.normalizer (B : Set G) :=
    (hall y hy).resolve_right (fun h => hyN (Subgroup.mem_inf.mp h).2)
  have hcomm : ∀ p ∈ zGroup Ω, ∀ q ∈ zGroup Ω, p * q = q * p := fun p hp q hq =>
    H.endHyp.zGroup_comm H.perp9 p hp q hq
  have hsq : a * a = 1 := H.endHyp.zGroup_mul_self H.perp9 a ha
  have e : (x * a) * (y * a) = x * y := by
    calc (x * a) * (y * a) = x * (a * y) * a := by group
      _ = x * (y * a) * a := by rw [hcomm a ha y hy]
      _ = x * y * (a * a) := by group
      _ = x * y := by rw [hsq, mul_one]
  have hmem := (zGroup Ω ⊓ Subgroup.normalizer (B : Set G)).mul_mem hxa hya
  rw [e] at hmem
  exact (Subgroup.mem_inf.mp hmem).2

open Classical in
private theorem e8f_bnorm_mul (H : Hyp Ω) {B : Subgroup G} (hB : B ∈ Ω) {d d' : G}
    (hd : d ∈ zGroup Ω) (hd' : d' ∈ zGroup Ω) :
    bnorm B (d * d') = bnorm B d + bnorm B d' := by
  unfold bnorm
  by_cases h1 : d ∈ Subgroup.normalizer (B : Set G) <;>
    by_cases h2 : d' ∈ Subgroup.normalizer (B : Set G)
  · rw [if_pos h1, if_pos h2, if_pos (Subgroup.mul_mem _ h1 h2)]
    decide
  · have h3 : d * d' ∉ Subgroup.normalizer (B : Set G) := fun h => h2 (by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) h
      simpa using this)
    rw [if_pos h1, if_neg h2, if_neg h3]
    decide
  · have h3 : d * d' ∉ Subgroup.normalizer (B : Set G) := fun h => h1 (by
      have := Subgroup.mul_mem _ h (Subgroup.inv_mem _ h2)
      simpa using this)
    rw [if_neg h1, if_pos h2, if_neg h3]
    decide
  · have h3 := e8f_mul_normalizer H hB hd hd' h1 h2
    rw [if_neg h1, if_neg h2, if_pos h3]
    decide

open Classical in
private theorem e8f_betaPt_eq (H : Hyp Ω) {M : Subgroup G} (hM : M ∈ Ω) {b : G}
    (hb : IsUniqueInvolution M b) {d : G} (hd : d ∈ zGroup Ω) :
    betaPt Ω b d = bnorm M d := by
  have hex : ∃ M₀ ∈ Ω, IsUniqueInvolution M₀ b := ⟨M, hM, hb⟩
  obtain ⟨hM₀, hb₀⟩ := hex.choose_spec
  have hT : M ∈ twinSet Ω hex.choose := ⟨hM, b, hb₀, hb⟩
  have hN := H.zGroup_inf_normalizer_eq hM₀ hT
  have hiff : d ∈ Subgroup.normalizer (hex.choose : Set G) ↔
      d ∈ Subgroup.normalizer (M : Set G) := by
    have h' : d ∈ zGroup Ω ⊓ Subgroup.normalizer (hex.choose : Set G) ↔
        d ∈ zGroup Ω ⊓ Subgroup.normalizer (M : Set G) := by
      rw [hN]
    constructor
    · intro h
      exact (Subgroup.mem_inf.mp (h'.mp (Subgroup.mem_inf.mpr ⟨hd, h⟩))).2
    · intro h
      exact (Subgroup.mem_inf.mp (h'.mpr (Subgroup.mem_inf.mpr ⟨hd, h⟩))).2
  unfold betaPt
  rw [dif_pos hex]
  unfold bnorm
  by_cases h0 : d ∈ Subgroup.normalizer (hex.choose : Set G)
  · rw [if_pos h0, if_pos (hiff.mp h0)]
  · rw [if_neg h0, if_neg (fun h1 => h0 (hiff.mpr h1))]

private theorem e8f_betaPt_mul (H : Hyp Ω) {b : G} (hb : b ∈ zSet Ω) {d d' : G}
    (hd : d ∈ zGroup Ω) (hd' : d' ∈ zGroup Ω) :
    betaPt Ω b (d * d') = betaPt Ω b d + betaPt Ω b d' := by
  obtain ⟨B, hB, hbB⟩ := hb
  rw [e8f_betaPt_eq H hB hbB ((zGroup Ω).mul_mem hd hd'), e8f_betaPt_eq H hB hbB hd,
    e8f_betaPt_eq H hB hbB hd']
  exact e8f_bnorm_mul H hB hd hd'

private theorem e8f_betaPt_self (H : Hyp Ω) {b : G} (hb : b ∈ zSet Ω) :
    betaPt Ω b b = 0 := by
  obtain ⟨B, hB, hbB⟩ := hb
  rw [e8f_betaPt_eq H hB hbB (Subgroup.subset_closure ⟨B, hB, hbB⟩)]
  exact (e8f_bnorm_eq_zero_iff B b).mpr (Subgroup.le_normalizer hbB.mem)

private theorem e8f_betaPt_conj (H : Hyp Ω) (g : G) {b : G} (hb : b ∈ zSet Ω) {d : G}
    (hd : d ∈ zGroup Ω) : betaPt Ω (g * b * g⁻¹) (g * d * g⁻¹) = betaPt Ω b d := by
  obtain ⟨B, hB, hbB⟩ := hb
  have hgd : g * d * g⁻¹ ∈ zGroup Ω := e8f_conj_mem H.endHyp g hd
  rw [e8f_betaPt_eq H (H.endHyp.thmD.hyp.conjInvariant g B hB) (hbB.conj g) hgd,
    e8f_betaPt_eq H hB hbB hd]
  unfold bnorm
  by_cases hdN : d ∈ Subgroup.normalizer (B : Set G)
  · rw [if_pos hdN, if_pos ((e8f_normalizer_conj g d B).mpr hdN)]
  · rw [if_neg hdN, if_neg (fun h' => hdN ((e8f_normalizer_conj g d B).mp h'))]

private theorem e8f_betaPt_symm (H : Hyp Ω) {a b : G} (ha : a ∈ zSet Ω) (hb : b ∈ zSet Ω) :
    betaPt Ω b a = betaPt Ω a b := by
  obtain ⟨A, hA, hau⟩ := ha
  obtain ⟨B, hB, hbu⟩ := hb
  have hiff := H.endHyp.mem_normalizer_comm H.perp9 hB hA hbu hau
  rw [e8f_betaPt_eq H hB hbu (Subgroup.subset_closure ⟨A, hA, hau⟩),
    e8f_betaPt_eq H hA hau (Subgroup.subset_closure ⟨B, hB, hbu⟩)]
  unfold bnorm
  by_cases hd : a ∈ Subgroup.normalizer (B : Set G)
  · rw [if_pos hd, if_pos (hiff.mp hd)]
  · rw [if_neg hd, if_neg (fun h' => hd (hiff.mpr h'))]

private noncomputable def e8f_beta (Ω : Set (Subgroup G)) (a x : zGroup Ω) : ZMod 2 :=
  betaPt Ω a.1 x.1

private theorem e8f_exists_biadditive (H : Hyp Ω) :
    ∃ bf : zGroup Ω → zGroup Ω → ZMod 2,
      (∀ a a' b : zGroup Ω, bf (a * a') b = bf a b + bf a' b) ∧
      (∀ a b b' : zGroup Ω, bf a (b * b') = bf a b + bf a b') ∧ (∀ a : zGroup Ω, bf a a = 0) ∧
      (∀ (g : G) (a b a' b' : zGroup Ω), a'.1 = g * a.1 * g⁻¹ → b'.1 = g * b.1 * g⁻¹ →
        bf a' b' = bf a b) ∧
      ∀ M ∈ Ω, ∀ b : zGroup Ω, IsUniqueInvolution M b.1 → ∀ a : zGroup Ω,
        bf a b = 0 ↔ a.1 ∈ Subgroup.normalizer (M : Set G) := by
  obtain ⟨B, hB1₀, hB2₀, hB3₀, hB4⟩ := @Polar.exists_form_of_symmetric (zGroup Ω)
    (H.endHyp.zGroupCommGroup H.perp9) (zPoints Ω) (e8f_closure_zPoints Ω)
    (fun a => Subtype.ext (H.endHyp.zGroup_mul_self H.perp9 a.1 a.2)) (e8f_beta Ω)
    (fun a ha b b' => e8f_betaPt_mul H (b := a.1) ha b.2 b'.2)
    (fun a ha b hb => (e8f_betaPt_symm H (a := a.1) (b := b.1) ha hb).symm)
    (fun a ha => e8f_betaPt_self H (b := a.1) ha)
  have hB1 : ∀ a a' b : zGroup Ω, B (a * a') b = B a b + B a' b := hB1₀
  have hB2 : ∀ a b b' : zGroup Ω, B a (b * b') = B a b + B a b' := hB2₀
  have hB3 : ∀ a : zGroup Ω, B a a = 0 := hB3₀
  have hsymm : ∀ a b, B a b = B b a := fun a b => e8f_symm (bf := B) hB1 hB2 hB3 a b
  have hcj_pts : ∀ g : G, ∀ a ∈ zPoints Ω, e8f_cj H.endHyp g a ∈ zPoints Ω := by
    intro g a ha
    obtain ⟨A, hA, hau⟩ := ha
    exact ⟨conjSub g A, H.endHyp.thmD.hyp.conjInvariant g A hA, hau.conj g⟩
  have hcj_mul : ∀ (g : G) (a b : zGroup Ω),
      e8f_cj H.endHyp g (a * b) = e8f_cj H.endHyp g a * e8f_cj H.endHyp g b := by
    intro g a b
    apply Subtype.ext
    simp only [e8f_cj, Subgroup.coe_mul]
    group
  have hpts : ∀ g : G, ∀ a ∈ zPoints Ω, ∀ b : zGroup Ω,
      B (e8f_cj H.endHyp g a) (e8f_cj H.endHyp g b) = B a b := by
    intro g a ha b
    rw [hB4 _ (hcj_pts g a ha), hB4 a ha]
    exact e8f_betaPt_conj H g (b := a.1) ha b.2
  have step1 : ∀ g : G, ∀ a ∈ zPoints Ω, ∀ b : zGroup Ω,
      B (e8f_cj H.endHyp g a) (e8f_cj H.endHyp g b) = B a b := by
    intro g a ha b
    exact e8f_eq_of_eq_on_zPoints (e8f_closure_zPoints Ω)
      (F := fun x => B (e8f_cj H.endHyp g a) (e8f_cj H.endHyp g x)) (F' := fun x => B a x)
      (fun x y => by simp only [hcj_mul, hB2]) (fun x y => hB2 a x y)
      (fun x _ => hpts g a ha x) b
  have hall : ∀ (g : G) (a b : zGroup Ω),
      B (e8f_cj H.endHyp g a) (e8f_cj H.endHyp g b) = B a b := by
    intro g a b
    exact e8f_eq_of_eq_on_zPoints (e8f_closure_zPoints Ω)
      (F := fun x => B (e8f_cj H.endHyp g x) (e8f_cj H.endHyp g b)) (F' := fun x => B x b)
      (fun x y => by simp only [hcj_mul, hB1]) (fun x y => hB1 x y b)
      (fun x hx => step1 g x hx b) a
  refine ⟨B, hB1, hB2, hB3, ?_, ?_⟩
  · intro g a b a' b' ha hb
    rw [show a' = e8f_cj H.endHyp g a from Subtype.ext ha,
      show b' = e8f_cj H.endHyp g b from Subtype.ext hb]
    exact hall g a b
  · intro M hM b hb a
    have hbS : b ∈ zPoints Ω := ⟨M, hM, hb⟩
    rw [hsymm a b, hB4 b hbS a]
    unfold e8f_beta
    rw [e8f_betaPt_eq H hM hb a.2]
    exact e8f_bnorm_eq_zero_iff M a.1

private theorem e8f_nondeg (H : Hyp Ω) (bf : zGroup Ω → zGroup Ω → ZMod 2)
    (hmulL : ∀ a a' b : zGroup Ω, bf (a * a') b = bf a b + bf a' b)
    (hinv : ∀ (g : G) (a b a' b' : zGroup Ω), a'.1 = g * a.1 * g⁻¹ → b'.1 = g * b.1 * g⁻¹ →
      bf a' b' = bf a b)
    (hspec : ∀ M ∈ Ω, ∀ b : zGroup Ω, IsUniqueInvolution M b.1 → ∀ a : zGroup Ω,
      bf a b = 0 ↔ a.1 ∈ Subgroup.normalizer (M : Set G)) :
    ∀ a : zGroup Ω, (∀ b : zGroup Ω, bf a b = 0) → a = 1 := by
  obtain ⟨K, hK, -⟩ := H.endHyp.exists_ne
  obtain ⟨z, hz⟩ := H.endHyp.exists_isUniqueInvolution hK
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, hK, hz⟩
  obtain ⟨J, hJ, s, hs, hsK⟩ := H.exists_swap hK
  have hsD : s ∈ zGroup Ω := Subgroup.subset_closure ⟨J, hJ, hs⟩
  have hone : ∀ b : zGroup Ω, bf 1 b = 0 := fun b =>
    e8f_map_one (F := fun x => bf x b) (fun x y => hmulL x y b)
  have hinvL : ∀ a b : zGroup Ω, bf a⁻¹ b = bf a b := fun a b =>
    e8f_map_inv (F := fun x => bf x b) (fun x y => hmulL x y b) a
  have hconjR : ∀ (g : G) (a : zGroup Ω), (∀ b, bf a b = 0) →
      ∀ b : zGroup Ω, bf (e8f_cj H.endHyp g a) b = 0 := by
    intro g a ha b
    have hcond : b.1 = g * (e8f_cj H.endHyp g⁻¹ b).1 * g⁻¹ := by
      rw [e8f_cj_val]
      group
    rw [hinv g a (e8f_cj H.endHyp g⁻¹ b) (e8f_cj H.endHyp g a) b rfl hcond]
    exact ha _
  have hnopt : ∀ p : zGroup Ω, p.1 ∈ zSet Ω → (∀ b, bf p b = 0) → False := by
    intro p hp hpR
    have hpts : ∀ x : zGroup Ω, x.1 ∈ zSet Ω → ∀ b, bf x b = 0 := by
      intro x hx
      obtain ⟨L, hL, hLp⟩ := hp
      obtain ⟨M, hM, hMx⟩ := hx
      obtain ⟨g, hg⟩ := H.endHyp.thmD.trans L hL M hM
      have hc : IsUniqueInvolution M (g * p.1 * g⁻¹) := by
        rw [← hg]
        exact hLp.conj g
      have hxg : x = e8f_cj H.endHyp g p := Subtype.ext (hMx.eq hc)
      rw [hxg]
      exact hconjR g p hpR
    have hdall : ∀ d : zGroup Ω, ∀ b, bf d b = 0 := by
      intro d
      have hd : d ∈ Subgroup.closure (zPoints Ω) := by
        rw [e8f_closure_zPoints]
        exact Subgroup.mem_top d
      induction hd using Subgroup.closure_induction with
      | mem x hx => exact hpts x hx
      | one => exact hone
      | mul x y _ _ hx hy => exact fun b => by rw [hmulL, hx b, hy b, add_zero]
      | inv x _ hx => exact fun b => by rw [hinvL, hx b]
    have hdN := (hspec K hK ⟨z, hzD⟩ hz ⟨s, hsD⟩).mp (hdall ⟨s, hsD⟩ ⟨z, hzD⟩)
    exact hsK (mem_normalizer_iff_conjSub_eq.mp hdN)
  have hcomm : ∀ (L : Subgroup G), L ∈ Ω → ∀ r : zGroup Ω, (∀ b, bf r b = 0) →
      ∀ l ∈ L, l * r.1 = r.1 * l := by
    intro L hL r hr l hl
    obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution H.endHyp.thmD.hyp hL
    have huD : u ∈ zGroup Ω := Subgroup.subset_closure ⟨L, hL, hu⟩
    have hrN : r.1 ∈ Subgroup.normalizer (L : Set G) :=
      (hspec L hL ⟨u, huD⟩ hu r).mp (hr _)
    have hcL : l * r.1 * l⁻¹ * r.1⁻¹ ∈ L := by
      have h1 : r.1 * l⁻¹ * r.1⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp hrN l⁻¹).mp (L.inv_mem hl)
      have e : l * r.1 * l⁻¹ * r.1⁻¹ = l * (r.1 * l⁻¹ * r.1⁻¹) := by group
      rw [e]
      exact L.mul_mem hl h1
    have hcD : l * r.1 * l⁻¹ * r.1⁻¹ ∈ zGroup Ω :=
      (zGroup Ω).mul_mem (e8f_conj_mem H.endHyp l r.2) ((zGroup Ω).inv_mem r.2)
    have hcR : ∀ b, bf ⟨l * r.1 * l⁻¹ * r.1⁻¹, hcD⟩ b = 0 := by
      have e : (⟨l * r.1 * l⁻¹ * r.1⁻¹, hcD⟩ : zGroup Ω) = e8f_cj H.endHyp l r * r⁻¹ := rfl
      rw [e]
      intro b
      rw [hmulL, hconjR l r hr b, hinvL, hr b, add_zero]
    have hsq : (l * r.1 * l⁻¹ * r.1⁻¹) * (l * r.1 * l⁻¹ * r.1⁻¹) = 1 :=
      H.endHyp.zGroup_mul_self H.perp9 _ hcD
    rcases hu.unique _ hcL hsq with h1 | h1
    · calc l * r.1 = (l * r.1 * l⁻¹ * r.1⁻¹) * (r.1 * l) := by group
        _ = r.1 * l := by rw [h1, one_mul]
    · exfalso
      have hpu : (⟨u, huD⟩ : zGroup Ω) = ⟨l * r.1 * l⁻¹ * r.1⁻¹, hcD⟩ :=
        Subtype.ext h1.symm
      exact hnopt ⟨u, huD⟩ ⟨L, hL, hu⟩ (by rw [hpu]; exact hcR)
  intro r hr
  have hcent : ∀ L ∈ Ω, L ≤ Subgroup.centralizer ({r.1} : Set G) := by
    intro L hL l hl
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm L hL r hr l hl)
  have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({r.1} : Set G) := by
    have hp := pSpan_le hcent
    rwa [H.endHyp.thmD.gen] at hp
  have hc : r.1 ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (htop (Subgroup.mem_top g))
  rw [H.endHyp.center, Subgroup.mem_bot] at hc
  exact Subtype.ext hc

theorem exists_endForm (H : Hyp Ω) :
    ∃ bf : zGroup Ω → zGroup Ω → ZMod 2, IsEndForm Ω bf := by
  obtain ⟨bf, hL, hR, halt, hinv, hspec⟩ := e8f_exists_biadditive H
  exact ⟨bf, hL, hR, halt, e8f_nondeg H bf hL hinv hspec, hinv, hspec⟩

theorem exists_member_mul_of_normalizes (H : Hyp Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) {a b : G} (ha : IsUniqueInvolution K a) (hb : IsUniqueInvolution J b)
    (hJK : J ∉ twinSet Ω K) (hbN : b ∈ Subgroup.normalizer (K : Set G)) :
    ∃ M ∈ Ω, IsUniqueInvolution M (a * b) := by
  have hstar : J ∈ omegaStarNbr Ω K := by
    rcases (H.normalizes_iff hK hJ hb).mp hbN with h | h
    · exact absurd h hJK
    · exact h
  have hJn : J ∉ omegaNbr Ω K := fun h =>
    hJK (by
      rw [← H.kPerp_eq_twinSet hK]
      exact Set.mem_insert_of_mem _ h)
  have hJne : J ≠ K := fun e =>
    hJK (by
      rw [e]
      exact ⟨hK, a, ha, ha⟩)
  have hnotle : ¬ J ≤ Subgroup.normalizer (K : Set G) := fun hle =>
    hJn ((TC.mem_omegaNbr_iff H.endHyp.thmD.hyp H.endHyp.thmD.two).mpr ⟨hJ, hJne, hle⟩)
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ J, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push_neg at hcon
    exact hnotle hcon
  have hmul : t * a * t⁻¹ = a * b :=
    conj_involution_eq_mul H.endHyp hK hstar hJn ha hb ht htn
  refine ⟨conjSub t K, H.endHyp.thmD.hyp.conjInvariant t K hK, ?_⟩
  rw [← hmul]
  exact ha.conj t

theorem twin_of_involution_mem_centralizer (H : Hyp Ω) {L M : Subgroup G} (hL : L ∈ Ω)
    (hM : M ∈ Ω) {z : G} (hz : IsUniqueInvolution L z)
    (hzM : ∀ m ∈ M, m * z = z * m) : M ∈ twinSet Ω L := by
  by_cases hLM : L = M
  · subst hLM
    exact ⟨hL, z, hz, hz⟩
  · rw [← H.kPerp_eq_twinSet hL]
    refine Set.mem_insert_of_mem _ ((TC.mem_omegaNbr_iff H.endHyp.thmD.hyp H.endHyp.thmD.two).mpr
      ⟨hM, fun e => hLM e.symm, ?_⟩)
    obtain ⟨c, i, j, hQ⟩ := H.endHyp.exists_q8Data hM
    have hi4 : orderOf i = 4 := e8f_orderOf_four hQ.inv.sq hQ.inv.ne_one hQ.sq_i
    have hj4 : orderOf j = 4 := e8f_orderOf_four hQ.inv.sq hQ.inv.ne_one hQ.sq_j
    have hPi : IsPGroup 2 (Subgroup.zpowers i) :=
      IsPGroup.of_card (n := 2) (by norm_num [Nat.card_zpowers, hi4])
    have hPj : IsPGroup 2 (Subgroup.zpowers j) :=
      IsPGroup.of_card (n := 2) (by norm_num [Nat.card_zpowers, hj4])
    have hnci : ¬ ∀ w ∈ M, i * w = w * i := by
      intro h
      have h1 := h j hQ.mem_j
      have h2 : (1 : G) * (i * j) = c * (i * j) := by
        rw [one_mul]
        exact h1.trans hQ.comm
      exact hQ.inv.ne_one (mul_right_cancel h2).symm
    have hncj : ¬ ∀ w ∈ M, j * w = w * j := by
      intro h
      have h1 := h i hQ.mem_i
      have h2 : (1 : G) * (i * j) = c * (i * j) := by
        rw [one_mul]
        exact h1.symm.trans hQ.comm
      exact hQ.inv.ne_one (mul_right_cancel h2).symm
    have hLN : ∀ v ∈ M, ¬ (∀ w ∈ M, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) →
        v ∈ Subgroup.normalizer (L : Set G) := fun v hv hnc hP =>
      H.endHyp.thmD.hyp.omega5 L hL M hM hLM z hz v hv hnc hP (hzM v hv)
    have hi : i ∈ Subgroup.normalizer (L : Set G) := hLN i hQ.mem_i hnci hPi
    have hj : j ∈ Subgroup.normalizer (L : Set G) := hLN j hQ.mem_j hncj hPj
    have hcN : c ∈ Subgroup.normalizer (L : Set G) := by
      rw [← hQ.sq_i]
      exact Subgroup.mul_mem _ hi hi
    intro x hx
    rcases hQ.nf x hx with h | h | h | h | h | h | h | h <;> rw [h]
    · exact Subgroup.one_mem _
    · exact hcN
    · exact hi
    · exact Subgroup.mul_mem _ hcN hi
    · exact hj
    · exact Subgroup.mul_mem _ hcN hj
    · exact Subgroup.mul_mem _ hi hj
    · exact Subgroup.mul_mem _ hcN (Subgroup.mul_mem _ hi hj)

theorem not_point_of_mem_dZero (H : Hyp Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {s : G} (hs : s ∈ zGroup Ω) (hsK : conjSub s K ≠ K) {d : G}
    (hd : d ∈ zGroup Ω ⊓ (K ⊔ conjSub s K)) (hdz : d ∉ Subgroup.zpowers z) :
    ¬ ∃ L ∈ Ω, IsUniqueInvolution L d := by
  rintro ⟨L, hL, hLd⟩
  obtain ⟨K₃, hK₃V, hK₃K, hK₃s, -, -, -, -⟩ := H.exists_twin_frame hK hs hsK
  have hKt : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  have hKs : conjSub s K ∈ twinSet Ω K := H.conjSub_mem_twinSet hK hs
  have hK₃Ω : K₃ ∈ Ω := hK₃V.1
  have hc1 : Commutes K K₃ := (H.sup_twin hz hKt hK₃V (Ne.symm hK₃K)).1
  have hc2 : Commutes (conjSub s K) K₃ := (H.sup_twin hz hKs hK₃V (Ne.symm hK₃s)).1
  have hcent : K ⊔ conjSub s K ≤ Subgroup.centralizer (K₃ : Set G) := by
    refine sup_le ?_ ?_
    · intro k hk
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      exact (hc1 k hk h hh).symm
    · intro k hk
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      exact (hc2 k hk h hh).symm
  have hdK₃ : ∀ m ∈ K₃, m * d = d * m := fun m hm =>
    Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_inf.mp hd).2) m hm
  obtain ⟨-, w, hwL, hwK₃⟩ := H.twin_of_involution_mem_centralizer hL hK₃Ω hLd hdK₃
  obtain ⟨-, w', hw'K, hw'K₃⟩ := hK₃V
  have hdz' : d = z := (hLd.eq hwL).trans ((hw'K₃.eq hwK₃).symm.trans (hz.eq hw'K).symm)
  exact hdz (by rw [hdz']; exact Subgroup.mem_zpowers z)

theorem exists_order_four_centralizes (H : Hyp Ω) {L : Subgroup G} (hL : L ∈ Ω) {d : G}
    (hd : d ∈ zGroup Ω) (hdN : d ∈ Subgroup.normalizer (L : Set G)) :
    ∃ x ∈ L, orderOf x = 4 ∧ x * d = d * x := by
  obtain ⟨z, i, j, hQ⟩ := H.endHyp.exists_q8Data hL
  have hzz : z * z = 1 := hQ.inv.sq
  have hz1 : z ≠ 1 := hQ.inv.ne_one
  have hcL : ∀ x ∈ L, x * d * x⁻¹ * d⁻¹ = 1 ∨ x * d * x⁻¹ * d⁻¹ = z := by
    intro x hx
    have hmemL : x * d * x⁻¹ * d⁻¹ ∈ L := by
      have e : x * d * x⁻¹ * d⁻¹ = x * (d * x⁻¹ * d⁻¹) := by group
      rw [e]
      exact L.mul_mem hx ((Subgroup.mem_normalizer_iff.mp hdN x⁻¹).mp (L.inv_mem hx))
    have hmemD : x * d * x⁻¹ * d⁻¹ ∈ zGroup Ω :=
      (zGroup Ω).mul_mem
        ((zGroup_normal_of_conjInvariant H.endHyp.thmD.hyp.conjInvariant).conj_mem d hd x)
        ((zGroup Ω).inv_mem hd)
    exact hQ.inv.unique _ hmemL (H.endHyp.zGroup_mul_self H.perp9 _ hmemD)
  have hfix_t : ∀ x ∈ L, ∀ t : G, (t = 1 ∨ t = z) → x * t * x⁻¹ = t := by
    intro x hx t ht
    rcases ht with h | h
    · rw [h]
      simp
    · rw [h]
      exact conj_eq_self_of_normalizer hQ.inv (Subgroup.le_normalizer hx)
  have hmulc : ∀ x y : G, x ∈ L → y ∈ L → (x * y) * d * (x * y)⁻¹ * d⁻¹ =
      (y * d * y⁻¹ * d⁻¹) * (x * d * x⁻¹ * d⁻¹) := by
    intro x y hx hy
    calc (x * y) * d * (x * y)⁻¹ * d⁻¹
        = x * (y * d * y⁻¹ * d⁻¹) * x⁻¹ * (x * d * x⁻¹ * d⁻¹) := by group
      _ = (y * d * y⁻¹ * d⁻¹) * (x * d * x⁻¹ * d⁻¹) := by
          rw [hfix_t x hx _ (hcL y hy)]
  have hcomm_of : ∀ x : G, x * d * x⁻¹ * d⁻¹ = 1 → x * d = d * x := fun x hx => by
    calc x * d = (x * d * x⁻¹ * d⁻¹) * (d * x) := by group
      _ = d * x := by rw [hx, one_mul]
  have hi4 : orderOf i = 4 := e8f_orderOf_four hzz hz1 hQ.sq_i
  have hj4 : orderOf j = 4 := e8f_orderOf_four hzz hz1 hQ.sq_j
  have hij4 : orderOf (i * j) = 4 := e8f_orderOf_four hzz hz1 (e8f_ij_sq hQ)
  rcases hcL i hQ.mem_i with hi1 | hiz
  · exact ⟨i, hQ.mem_i, hi4, hcomm_of i hi1⟩
  · rcases hcL j hQ.mem_j with hj1 | hjz
    · exact ⟨j, hQ.mem_j, hj4, hcomm_of j hj1⟩
    · refine ⟨i * j, L.mul_mem hQ.mem_i hQ.mem_j, hij4, hcomm_of (i * j) ?_⟩
      rw [hmulc i j hQ.mem_i hQ.mem_j, hjz, hiz]
      exact hzz

private theorem e8f_conj_twin (H : Hyp Ω) {K : Subgroup G} (hK : K ∈ Ω) {s : G}
    (hs : s ∈ zGroup Ω) {L : Subgroup G} (hL : L ∈ twinSet Ω K) : conjSub s L ∈ twinSet Ω K := by
  obtain ⟨hLΩ, w, hwK, hwL⟩ := hL
  have hwD : w ∈ zGroup Ω := Subgroup.subset_closure ⟨K, hK, hwK⟩
  have hcomm : s * w = w * s := H.endHyp.zGroup_comm H.perp9 s hs w hwD
  have e : s * w * s⁻¹ = w := by
    rw [hcomm]
    group
  have hc := hwL.conj s
  rw [e] at hc
  exact ⟨H.endHyp.thmD.hyp.conjInvariant s L hLΩ, w, hwK, hc⟩

private theorem e8f_le_normalizer_of_comm {A B : Subgroup G}
    (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) : A ≤ Subgroup.normalizer (B : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : x * h * x⁻¹ = h := by
      rw [hc x hx h hh]
      group
    rw [e]
    exact hh
  · intro hh
    have e2 := hc x⁻¹ (A.inv_mem hx) (x * h * x⁻¹) hh
    have e3 : h = x * h * x⁻¹ := by
      have e4 : h * x⁻¹ = (x * h * x⁻¹) * x⁻¹ := by
        rw [← e2]
        group
      exact mul_right_cancel e4
    rw [e3]
    exact hh

theorem zGroup_inf_span_twin_eq (H : Hyp Ω) {K K₃ : Subgroup G} (hK : K ∈ Ω) {s : G}
    (hs : s ∈ zGroup Ω) (hsK : conjSub s K ≠ K) (h₃ : K₃ ∈ twinSet Ω K)
    (hne₃ : K₃ ≠ K) (hne₃' : K₃ ≠ conjSub s K) :
    zGroup Ω ⊓ pSpan (twinSet Ω K) =
      (zGroup Ω ⊓ (K ⊔ conjSub s K)) ⊔ (zGroup Ω ⊓ (K₃ ⊔ conjSub s K₃)) := by
  obtain ⟨z, hz⟩ := H.endHyp.exists_isUniqueInvolution hK
  have hzz : z * z = 1 := hz.sq
  have hz1 : z ≠ 1 := hz.ne_one
  have hK₃Ω : K₃ ∈ Ω := h₃.1
  have hKt : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  have hKs : conjSub s K ∈ twinSet Ω K := H.conjSub_mem_twinSet hK hs
  have hK₃s : conjSub s K₃ ∈ twinSet Ω K := e8f_conj_twin H hK hs h₃
  have hsq : s * s = 1 := H.endHyp.zGroup_mul_self H.perp9 s hs
  have hss : ∀ A : Subgroup G, conjSub s (conjSub s A) = A := fun A => by
    rw [← conjSub_mul, hsq, conjSub_one]
  have hsK₃ : conjSub s K₃ ≠ K₃ := by
    intro e
    apply hsK
    have hmem : s ∈ zGroup Ω ⊓ Subgroup.normalizer (K₃ : Set G) :=
      Subgroup.mem_inf.mpr ⟨hs, mem_normalizer_iff_conjSub_eq.mpr e⟩
    rw [← H.zGroup_inf_normalizer_eq hK h₃] at hmem
    exact mem_normalizer_iff_conjSub_eq.mp (Subgroup.mem_inf.mp hmem).2
  have hcard1 : Nat.card ↥(zGroup Ω ⊓ (K ⊔ conjSub s K)) = 8 := H.card_dZero hK hs hsK
  have hcard2 : Nat.card ↥(zGroup Ω ⊓ (K₃ ⊔ conjSub s K₃)) = 8 :=
    H.card_dZero hK₃Ω hs hsK₃
  have hdist : ({K, conjSub s K, K₃, conjSub s K₃} : Set (Subgroup G)).ncard = 4 := by
    have hA : conjSub s K ∉ ({K₃, conjSub s K₃} : Set (Subgroup G)) := by
      intro hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with e | e
      · exact hne₃' e.symm
      · exact hne₃ (conjSub_injective s e).symm
    have hB : K₃ ∉ ({conjSub s K₃} : Set (Subgroup G)) := fun e =>
      hsK₃ (Set.mem_singleton_iff.mp e).symm
    have hK' : K ∉ ({conjSub s K, K₃, conjSub s K₃} : Set (Subgroup G)) := by
      intro hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with e | e | e
      · exact hsK e.symm
      · exact hne₃ e.symm
      · exact hne₃' (by rw [e, hss])
    rw [Set.ncard_insert_of_notMem hK', Set.ncard_insert_of_notMem hA,
      Set.ncard_pair hsK₃.symm]
  have hsup : (K ⊔ conjSub s K) ⊓ (K₃ ⊔ conjSub s K₃) = Subgroup.zpowers z :=
    H.sup_twin_inf_sup_twin hK hz hKs h₃ hK₃s hdist
  have hinter : (zGroup Ω ⊓ (K ⊔ conjSub s K)) ⊓ (zGroup Ω ⊓ (K₃ ⊔ conjSub s K₃)) ≤
      Subgroup.zpowers z := by
    intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
    rw [← hsup]
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp h1).2, (Subgroup.mem_inf.mp h2).2⟩
  have hcardI : Nat.card ↥((zGroup Ω ⊓ (K ⊔ conjSub s K)) ⊓
      (zGroup Ω ⊓ (K₃ ⊔ conjSub s K₃))) ≤ 2 := by
    have h := Subgroup.card_le_of_le hinter
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hzz) hz1] at h
    exact h
  have hcomm : ∀ x ∈ zGroup Ω, ∀ y ∈ zGroup Ω, x * y = y * x := fun x hx y hy =>
    H.endHyp.zGroup_comm H.perp9 x hx y hy
  have hprod := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer
    (e8f_le_normalizer_of_comm (A := zGroup Ω ⊓ (K ⊔ conjSub s K))
      (B := zGroup Ω ⊓ (K₃ ⊔ conjSub s K₃))
      (fun x hx y hy => hcomm x (Subgroup.mem_inf.mp hx).1 y (Subgroup.mem_inf.mp hy).1))
  rw [hcard1, hcard2] at hprod
  have hpos : 0 < Nat.card ↥((zGroup Ω ⊓ (K ⊔ conjSub s K)) ⊓
      (zGroup Ω ⊓ (K₃ ⊔ conjSub s K₃))) := Nat.card_pos
  have hge : 32 ≤ Nat.card ↥((zGroup Ω ⊓ (K ⊔ conjSub s K)) ⊔
      (zGroup Ω ⊓ (K₃ ⊔ conjSub s K₃))) := by
    have h12 : Nat.card ↥((zGroup Ω ⊓ (K ⊔ conjSub s K)) ⊓
        (zGroup Ω ⊓ (K₃ ⊔ conjSub s K₃))) = 1 ∨
        Nat.card ↥((zGroup Ω ⊓ (K ⊔ conjSub s K)) ⊓
        (zGroup Ω ⊓ (K₃ ⊔ conjSub s K₃))) = 2 := by
      omega
    rcases h12 with h12 | h12 <;> rw [h12] at hprod <;> omega
  have hle : (zGroup Ω ⊓ (K ⊔ conjSub s K)) ⊔ (zGroup Ω ⊓ (K₃ ⊔ conjSub s K₃)) ≤
      zGroup Ω ⊓ pSpan (twinSet Ω K) := by
    refine sup_le (inf_le_inf_left _ (sup_le (le_pSpan hKt) (le_pSpan hKs))) ?_
    exact inf_le_inf_left _ (sup_le (le_pSpan h₃) (le_pSpan hK₃s))
  have hcardA : Nat.card ↥(zGroup Ω ⊓ pSpan (twinSet Ω K)) ≤ 32 :=
    card_abelian_le_span H hK inf_le_right
      (fun a ha b hb => hcomm a (Subgroup.mem_inf.mp ha).1 b (Subgroup.mem_inf.mp hb).1)
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

end Hyp

end End18

end CFSG.ClassicalInvolution.Q3.Sec13

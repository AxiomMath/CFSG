module

public import CFSG.GH74.GLS.C3.Layer1.Th2P617O
public import CFSG.GH74.GLS.C3.Layer1.Th2P617N

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

omit [Finite G] in
theorem central_cases {P Q T : Subgroup G} {z x : G} (hcd : CommDisj P Q)
    (hdec : ∀ s ∈ T, ∃ p ∈ P, ∃ q ∈ Q, s = p * q) (hPT : P ≤ T) (hQT : Q ≤ T)
    (hzu : ∀ w ∈ P, (∀ p ∈ P, p * w = w * p) → w = 1 ∨ w = z)
    (hxu : ∀ w ∈ Q, (∀ q ∈ Q, q * w = w * q) → w = 1 ∨ w = x) {g : G} (hgT : g ∈ T)
    (hg : ∀ s ∈ T, s * g = g * s) : g = 1 ∨ g = z ∨ g = x ∨ g = z * x := by
  obtain ⟨p, hp, q, hq, rfl⟩ := hdec g hgT
  have hpc : ∀ p' ∈ P, p' * p = p * p' := by
    intro p' hp'
    have h1 := hg p' (hPT hp')
    have h2 : p' * p * q = p * p' * q := by
      calc p' * p * q = p' * (p * q) := by group
        _ = (p * q) * p' := h1
        _ = p * (q * p') := by group
        _ = p * (p' * q) := by rw [← hcd.comm p' hp' q hq]
        _ = p * p' * q := by group
    exact mul_right_cancel h2
  have hqc : ∀ q' ∈ Q, q' * q = q * q' := by
    intro q' hq'
    have h1 := hg q' (hQT hq')
    have h2 : p * (q' * q) = p * (q * q') := by
      calc p * (q' * q) = (p * q') * q := by group
        _ = (q' * p) * q := by rw [hcd.comm p hp q' hq']
        _ = q' * (p * q) := by group
        _ = (p * q) * q' := h1
        _ = p * (q * q') := by group
    exact mul_left_cancel h2
  rcases hzu p hp hpc with h1 | h1 <;> rcases hxu q hq hqc with h2 | h2
  · left; rw [h1, h2]; simp
  · right; right; left; rw [h1, h2]; simp
  · right; left; rw [h1, h2]; simp
  · right; right; right; rw [h1, h2]


theorem false_of_z
    (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) (hG : C3Hyp G)
    (hs : Th2Std x y K T S) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hQ2 : pRank 2 ↥(T ⊓ CxK x K) ≤ 2) (h4 : 4 < Nat.card ↥(T ⊓ CxK x K))
    {B : Subgroup G} (hB : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B) {b : G} {J : Subgroup G}
    (hobs : Obstr52 B b J) {U E : Subgroup G} (hU : IsFourSub (T ⊓ K) U)
    (hES : IsS (T ⊓ CxK x K) E) (hE2 : 2 ≤ pRank 2 ↥E) (hBdef : B = U ⊔ E) {z : G}
    (hzU : z ∈ U) (hz1 : z ≠ 1) (hzz : z * z = 1) (hzc : ∀ p ∈ T ⊓ K, p * z = z * p)
    (hzu : ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, p * w = w * p) → w = 1 ∨ w = z)
    (hP8 : Nat.card ↥(T ⊓ K) = 8) (hb : b = z) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eK⟩ := h7
  have hcen := centerlessBar_of_A7 ⟨eK⟩
  have hcd := hs.commDisj hcen
  have hG4 : pRank 2 G ≤ 4 := hG.pRank_eq_four.le
  have hE4 : IsE 4 ⊤ B := isE_of_isSn le_top hB le_rfl
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := hE4.2.1
  obtain ⟨eJ⟩ := hobs.nonempty_A7_of_rank_four hG4 hBel
  obtain ⟨Q'', hQQ, hQT, hQc, hPQ, hdec⟩ := exists_Qpp hG hs ⟨eK⟩
  obtain ⟨hD8, hQeq⟩ := Qpp_dihedral_of_z hL34 h102 hG hs ⟨eK⟩ hQ2 h4 hB hobs hU hES hE2 hBdef hzU
    hz1 hzc hb hQQ hQT hQc hPQ hdec
  subst hQeq
  obtain ⟨e8⟩ := hD8
  have hQ8 : Nat.card ↥(T ⊓ CxK x K) = 8 := by
    rw [Nat.card_congr e8.toEquiv, DihedralGroup.nat_card]
  have hzP : z ∈ T ⊓ K := hU.1 hzU
  have hxo := hs.orderOf_x
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hxo; omega
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxo, sq] at this
  have hxQ : x ∈ T ⊓ CxK x K := ⟨hs.x_mem_T, hs.x_mem_CxK⟩
  have hxcT : ∀ s ∈ T, s * x = x * s := fun s hs' =>
    mem_centralizer_singleton_iff.1 (hs.T_le_C hs')
  have hD4c : ∀ g : DihedralGroup 4, (∀ h : DihedralGroup 4, g * h = h * g) →
      g = 1 ∨ g = DihedralGroup.r 2 := by decide
  have hcenterQ : ∀ w : ↥(T ⊓ CxK x K), (∀ q : ↥(T ⊓ CxK x K), q * w = w * q) →
      w = 1 ∨ w = e8.symm (DihedralGroup.r 2) := by
    intro w hw
    have hc : ∀ h : DihedralGroup 4, e8 w * h = h * e8 w := by
      intro h
      obtain ⟨q, rfl⟩ := e8.surjective h
      rw [← map_mul, ← map_mul, hw q]
    rcases hD4c (e8 w) hc with h | h
    · left
      exact e8.injective (by rw [h, map_one])
    · right
      rw [← h]
      exact (e8.symm_apply_apply w).symm
  have hxe : (⟨x, hxQ⟩ : ↥(T ⊓ CxK x K)) = e8.symm (DihedralGroup.r 2) := by
    rcases hcenterQ ⟨x, hxQ⟩ (fun q => Subtype.ext (hxcT q.1 q.2.1)) with h | h
    · exact absurd (congrArg Subtype.val h) hx1
    · exact h
  have hxu : ∀ w ∈ T ⊓ CxK x K, (∀ q ∈ T ⊓ CxK x K, q * w = w * q) → w = 1 ∨ w = x := by
    intro w hw hwc
    rcases hcenterQ ⟨w, hw⟩ (fun q => Subtype.ext (hwc q.1 q.2)) with h | h
    · left
      exact congrArg Subtype.val h
    · right
      exact congrArg Subtype.val (h.trans hxe.symm)
  have hcQ : ((e8.symm (DihedralGroup.r 1) : ↥(T ⊓ CxK x K)) : G) ∈ T ⊓ CxK x K :=
    (e8.symm (DihedralGroup.r 1)).2
  have hcc : ((e8.symm (DihedralGroup.r 1) : ↥(T ⊓ CxK x K)) : G) *
      ((e8.symm (DihedralGroup.r 1) : ↥(T ⊓ CxK x K)) : G) = x := by
    have h1 : e8.symm (DihedralGroup.r 1) * e8.symm (DihedralGroup.r 1) =
        e8.symm (DihedralGroup.r 2) := by
      rw [← map_mul]
      congr 1
    exact congrArg Subtype.val (h1.trans hxe.symm)
  have hTeq : T = (T ⊓ K) ⊔ (T ⊓ CxK x K) := le_antisymm (fun s hs' => by
      obtain ⟨p, hp, q, hq, rfl⟩ := hdec s hs'
      exact Subgroup.mul_mem_sup hp hq) (sup_le inf_le_left inf_le_left)
  have hT64 : Nat.card ↥T = 64 := by
    rw [hTeq, hcd.card_sup le_rfl le_rfl, hP8, hQ8]
  have hzT : ∀ s ∈ T, s * z = z * s := by
    intro s hsT
    obtain ⟨p, hp, q, hq, rfl⟩ := hdec s hsT
    calc p * q * z = p * (q * z) := by group
      _ = p * (z * q) := by rw [← hcd.comm z hzP q hq]
      _ = (p * z) * q := by group
      _ = (z * p) * q := by rw [hzc p hp]
      _ = z * (p * q) := by group
  by_cases hTS : T = S
  · have hbo : orderOf b = 2 := by
      rw [hb]
      exact orderOf_eq_prime (by rw [sq]; exact hzz) hz1
    have hbT : b ∈ T := by rw [hb]; exact hzP.1
    have hcardT : Nat.card ↥T = 2 ^ (Nat.card G).factorization 2 := by
      have h1 := hs.sylowS.card_eq
      rw [Subgroup.card_top] at h1
      rw [hTS]
      exact h1
    have hc : IsCentralInvolution b :=
      isCentralInvolution_of_card hbo hbT (fun s hs' => by rw [hb]; exact hzT s hs') hcardT
    have h64 : twoPartCard (⊤ : Subgroup G) = 64 := by
      have : twoPartCard (⊤ : Subgroup G) = Nat.card ↥T := by
        unfold twoPartCard
        rw [Subgroup.card_top]
        exact hcardT.symm
      rw [this, hT64]
    have hq4 : twoPartCard (CxK b J) ≤ 4 := by
      have h1 := hobs.twoPartCard_centralizer hG4 hBel eJ
      have h2 := twoPartCard_le_top (centralizer ({b} : Set G))
      omega
    exact hobs.false_of_isCentralInvolution hG hBel ⟨eJ⟩ hq4 hc
  · have hTlt : T < S := lt_of_le_of_ne hs.T_le_S hTS
    obtain ⟨a, haS, haN, haT⟩ := exists_mem_normalizer_of_lt hs.sylowS.isPGroup hTlt
    have hconjT : ∀ g ∈ T, a * g * a⁻¹ ∈ T := fun g hg => (Subgroup.mem_normalizer_iff.1 haN g).1 hg
    have hconjT' : ∀ g ∈ T, a⁻¹ * g * a ∈ T := fun g hg => by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ haN) g).1 hg
      simpa using this
    have hx'T : a * x * a⁻¹ ∈ T := hconjT x hs.x_mem_T
    have hx'c : ∀ s ∈ T, s * (a * x * a⁻¹) = (a * x * a⁻¹) * s := by
      intro s hsT
      have h1 := hxcT (a⁻¹ * s * a) (hconjT' s hsT)
      calc s * (a * x * a⁻¹) = a * ((a⁻¹ * s * a) * x) * a⁻¹ := by group
        _ = a * (x * (a⁻¹ * s * a)) * a⁻¹ := by rw [h1]
        _ = (a * x * a⁻¹) * s := by group
    rcases central_cases hcd hdec inf_le_left inf_le_left hzu hxu hx'T hx'c with h | h | h | h
    · apply hx1
      have : x = a⁻¹ * (a * x * a⁻¹) * a := by group
      rw [h] at this
      simpa using this
    · exact false_of_conj_x_eq_z hG hs hBel (hb ▸ hobs) hT64 hQ8 hP8 h
    · exact conj_x_ne_x hs haS haT h
    · exact conj_ne_zx hcd hdec inf_le_left inf_le_left hP8 hQ8 hzP hz1 hzz hzu hxQ hx1 hxx hxu
        hcQ hcc haN h

end CFSG.GH74.GLS.Th2.Obs

module

public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveInvert
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCBCyclicFourIsolation

public section

namespace CFSG.OddStandard

open Subgroup Equiv CFSG.Open
open scoped Pointwise
open CFSG.LocalAnalysis.ComponentInitial
  (cyclic_times_four_inversion_sylow_central_normalizer_forces_isolation)

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}
  {S : Sylow 2 (centralizer (L : Set G))} {t : G} {e : L ≃* alternatingGroup (Fin 5)}

theorem Full.normalizer_fixes_t_of_inversion (hf : Full L S t e)
    (Q : Sylow 2 (centralizer ({t} : Set G))) (hSQ : sg L S ≤ qg t Q) {x : G} (hx : x ∈ qg t Q)
    (hxA : x ∉ (qg t Q ⊓ L) ⊔ sg L S) (_hx2 : x * x = 1)
    (hinv : ∀ u ∈ sg L S, x * u * x⁻¹ = u⁻¹) :
    ∀ n ∈ normalizer ((qg t Q : Subgroup G) : Set G), n * t * n⁻¹ = t := by
  classical
  intro n hn
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, a, hgen, hord, ha1, hcard, ht⟩ := exists_generator_sg hf.sector
  have ha2 : 2 ≤ a := by
    by_contra h
    have h1 : a = 1 := by omega
    have h4 := hf.four_le
    rw [hcard, h1] at h4
    norm_num at h4
  have hsS : s ∈ sg L S := hgen ▸ mem_zpowers s
  have hs'Q : n * s * n⁻¹ ∈ qg t Q := (mem_normalizer_iff.mp hn s).mp (hSQ hsS)
  have hnt : n * t * n⁻¹ = (n * s * n⁻¹) ^ 2 ^ (a - 1) := by rw [ht, conj_pow]
  have hs'ord : orderOf (n * s * n⁻¹) = 2 ^ a := by
    rw [show n * s * n⁻¹ = MulAut.conj n s from rfl, MulEquiv.orderOf_eq, hord]
  have hcomm : ∀ u ∈ sg L S, u * (n * s * n⁻¹) = (n * s * n⁻¹) * u := by
    intro u hu
    have hq' : n⁻¹ * u * n ∈ qg t Q := by
      have := (mem_normalizer_iff.mp (inv_mem hn) u).mp (hSQ hu)
      rwa [inv_inv] at this
    have h2 : (n⁻¹ * u * n) * s * (n⁻¹ * u * n)⁻¹ ∈ sg L S := hf.conj_mem_sg Q hSQ hq' hsS
    rw [hgen] at h2
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 h2
    have h3 : u * (n * s * n⁻¹) * u⁻¹ = (n * s * n⁻¹) ^ m := by
      rw [conj_zpow, hm]
      group
    have h4 : (n * s * n⁻¹) * u⁻¹ * (n * s * n⁻¹)⁻¹ ∈ sg L S :=
      hf.conj_mem_sg Q hSQ hs'Q (Subgroup.inv_mem _ hu)
    set c : G := u * (n * s * n⁻¹) * u⁻¹ * (n * s * n⁻¹)⁻¹ with hc
    have hcS : c ∈ sg L S := by
      have : c = u * ((n * s * n⁻¹) * u⁻¹ * (n * s * n⁻¹)⁻¹) := by rw [hc]; group
      rw [this]
      exact Subgroup.mul_mem _ hu h4
    have hcS' : c ∈ zpowers (n * s * n⁻¹) := by
      rw [hc, h3]
      exact Subgroup.mul_mem _ (zpow_mem_zpowers _ _) (Subgroup.inv_mem _ (mem_zpowers _))
    have hc1 : c = 1 := by
      by_contra hc1
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (isPGroup_sg (L := L) (S := S)) ⟨c, hcS⟩
      rw [Subgroup.orderOf_mk] at hk
      obtain ⟨m', hm'⟩ := exists_pow_orderOf_eq_two hk hc1
      have hy1 : c ^ m' ∈ sg L S := pow_mem hcS m'
      have hy2 : c ^ m' ∈ zpowers (n * s * n⁻¹) := pow_mem hcS' m'
      have e1 := eq_pow_of_mem_zpowers_of_orderOf_eq_two hs'ord hy2 hm'
      have e2 := eq_t_of_orderOf_eq_two hf.sector hy1 hm'
      exact hne (by rw [hnt, ← e1, e2])
    have : u * (n * s * n⁻¹) = (n * s * n⁻¹) * u := by
      have h5 : u * (n * s * n⁻¹) * u⁻¹ * (n * s * n⁻¹)⁻¹ = 1 := hc1
      calc u * (n * s * n⁻¹)
          = (u * (n * s * n⁻¹) * u⁻¹ * (n * s * n⁻¹)⁻¹) * ((n * s * n⁻¹) * u) := by group
        _ = (n * s * n⁻¹) * u := by rw [h5, one_mul]
    exact this
  have hs'A : n * s * n⁻¹ ∈ (qg t Q ⊓ L) ⊔ sg L S := by
    by_contra hs'A
    have hidx := hf.index_PS Q hSQ
    have hxinv : x⁻¹ ∉ (qg t Q ⊓ L) ⊔ sg L S := fun hmem =>
      hxA (by simpa using Subgroup.inv_mem _ hmem)
    have hmul := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨n * s * n⁻¹, hs'Q⟩)
      (b := ⟨x⁻¹, Subgroup.inv_mem _ hx⟩)).2 (by
        simp only [mem_subgroupOf]
        exact iff_of_false hs'A hxinv)
    rw [mem_subgroupOf] at hmul
    have ha : (n * s * n⁻¹) * x⁻¹ ∈ (qg t Q ⊓ L) ⊔ sg L S := hmul
    have hac := hf.PS_comm Q ha (mem_sup_right (Subgroup.inv_mem _ hsS))
    have h1 : (n * s * n⁻¹) * s * (n * s * n⁻¹)⁻¹ = s⁻¹ := by
      have e1 : n * s * n⁻¹ = ((n * s * n⁻¹) * x⁻¹) * x := by group
      have e2 := hinv s hsS
      calc (n * s * n⁻¹) * s * (n * s * n⁻¹)⁻¹
          = ((n * s * n⁻¹) * x⁻¹) * (x * s * x⁻¹) * ((n * s * n⁻¹) * x⁻¹)⁻¹ := by group
        _ = ((n * s * n⁻¹) * x⁻¹) * s⁻¹ * ((n * s * n⁻¹) * x⁻¹)⁻¹ := by rw [e2]
        _ = s⁻¹ := by rw [hac]; group
    have h2 := hcomm s hsS
    have h3 : (n * s * n⁻¹) * s * (n * s * n⁻¹)⁻¹ = s := by
      calc (n * s * n⁻¹) * s * (n * s * n⁻¹)⁻¹ = ((n * s * n⁻¹) * s) * (n * s * n⁻¹)⁻¹ := rfl
        _ = (s * (n * s * n⁻¹)) * (n * s * n⁻¹)⁻¹ := by rw [← h2]
        _ = s := by group
    have h4 : s = s⁻¹ := h3.symm.trans h1
    have h5 : s * s = 1 := by
      calc s * s = s * s⁻¹ := by rw [← h4]
        _ = 1 := mul_inv_cancel s
    have h6 : 2 ^ a ∣ 2 := hord ▸ orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h5)
    have h7 : 2 ^ a ≤ 2 := Nat.le_of_dvd (by norm_num) h6
    have h8 : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha2
    omega
  obtain ⟨p, hp, u, hu, hpu⟩ :=
    (mem_sup_iff_of_commute (A := qg t Q ⊓ L) (B := sg L S)
      (fun a ha b hb => hf.L_comm_sg ha.2 hb) _).1 hs'A
  have hpu2 : (n * s * n⁻¹) ^ 2 ^ (a - 1) = u ^ 2 ^ (a - 1) := by
    rw [hpu, (Commute.mul_pow (show Commute p u from hf.L_comm_sg hp.2 hu) _)]
    have : p ^ 2 ^ (a - 1) = 1 := by
      obtain ⟨b, hb⟩ : ∃ b, 2 ^ (a - 1) = 2 * b := ⟨2 ^ (a - 2), by
        rw [← pow_succ']; congr 1; omega⟩
      rw [hb, pow_mul, sq, hf.mul_self_P Q hp, one_pow]
    rw [this, one_mul]
  have hmem : n * t * n⁻¹ ∈ sg L S := by
    rw [hnt, hpu2]
    exact pow_mem hu _
  have hord2 : orderOf (n * t * n⁻¹) = 2 := by
    rw [show n * t * n⁻¹ = MulAut.conj n t from rfl, MulEquiv.orderOf_eq]
    exact hf.sector.t_order
  exact hne (eq_t_of_orderOf_eq_two hf.sector hmem hord2)

omit [Finite G] in
theorem exists_sylow_ge_sg (hs : Sector L S t) :
    ∃ Q : Sylow 2 (centralizer ({t} : Set G)), sg L S ≤ qg t Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSgH := sg_le_centralizer_t hs
  have hp : IsPGroup 2 ((sg L S).subgroupOf (centralizer ({t} : Set G))) :=
    isPGroup_sg.of_equiv (Subgroup.subgroupOfEquivOfLe hSgH).symm
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  refine ⟨Q, fun u hu => ⟨⟨u, hSgH hu⟩, hQ (mem_subgroupOf.mpr hu), rfl⟩⟩

theorem Full.false_of_four_le (hf : Full L S t e) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hSQ⟩ := exists_sylow_ge_sg hf.sector
  obtain ⟨x, hx, hxA, hx2⟩ := hf.exists_involution Q hSQ
  have hinv := hf.x_inverts Q hSQ hx hxA hx2
  have hNt := hf.normalizer_fixes_t_of_inversion Q hSQ hx hxA hx2 hinv
  obtain ⟨s, a, hgen, hord, ha1, hcard, ht⟩ := exists_generator_sg hf.sector
  have ha2 : 2 ≤ a := by
    by_contra h
    have h1 : a = 1 := by omega
    have h4 := hf.four_le
    rw [hcard, h1] at h4
    norm_num at h4
  have hd := hf.qdata Q hSQ hx hxA hx2 hgen hord ha2
  have hNle : normalizer ((qg t Q : Subgroup G) : Set G) ≤ centralizer ({t} : Set G) :=
    fun n hn => mem_centralizer_singleton_iff.mpr (by
      have h := hNt n hn
      calc n * t = (n * t * n⁻¹) * n := by group
        _ = t * n := by rw [h])
  have hQG : Nat.card (qg t Q) = 2 ^ (Nat.card G).factorization 2 :=
    card_eq_of_normalizer_le (qg_le_H t Q) (card_qg t Q) hNle
  let Qsyl : Sylow 2 G := Sylow.ofCard (qg t Q) hQG
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hx1 : x ≠ 1 := fun h => hxA (h ▸ one_mem _)
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  have hxP : x ∈ normalizer ((qg t Q ⊓ L : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro p
    refine ⟨fun hp => hf.conj_mem_P Q hx hp, fun hp => ?_⟩
    have := hf.conj_mem_P Q hx hp
    have e1 : x * (x * p * x⁻¹) * x⁻¹ = p := by
      calc x * (x * p * x⁻¹) * x⁻¹ = (x * x) * p * (x * x)⁻¹ := by group
        _ = p := by rw [hx2]; group
    rwa [e1] at this
  obtain ⟨p₁, hp₁, hne⟩ := hd.x_acts_nontrivially
  have hHS := hf.sector
  have key := cyclic_times_four_inversion_sylow_central_normalizer_forces_isolation
      (G := G) Qsyl (P := qg t Q ⊓ L) (S := sg L S) (x := x) (a := a) hd.P_klein
      (isCyclic_sg hf.sector) hcard ha2 hxo (fun p hp s hs => hf.L_comm_sg hp.2 hs) hd.P_inf_S
      ((inf_comm _ _).trans hd.PS_inf_zpowers_x)
      (hf.qg_eq_PS_sup Q hSQ hx hxA) hxP ⟨p₁, hp₁, by rw [hxinv] at hne ⊢; exact hne⟩
      (fun u hu => by have := hinv u hu; rw [hxinv] at this ⊢; exact this) (t := t)
      (t_mem_sg hf.sector) hf.sector.t_order hNle
  exact hf.false_of_zStar key.2.1

theorem small_alt_five_original_cyclic_sylow_centralizer_has_order_two [Group.IsPerfect G]
    {L : Subgroup G} (hL : standardComponentIsStandard L)
    (hodd : Odd (Nat.card (Subgroup.center L)))
    (θ : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G)))) :
    Nat.card (S : Subgroup (centralizer (L : Set G))) = 2 := by
  classical
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCeven : Even (Nat.card (centralizer (L : Set G))) := hL.2.1
  have hcard : Nat.card (S : Subgroup (centralizer (L : Set G))) =
      2 ^ (Nat.card (centralizer (L : Set G))).factorization 2 := Sylow.card_eq_multiplicity S
  have hv : 1 ≤ (Nat.card (centralizer (L : Set G))).factorization 2 := by
    have h2 : 2 ∣ Nat.card (centralizer (L : Set G)) := even_iff_two_dvd.mp hCeven
    have hpos : 0 < Nat.card (centralizer (L : Set G)) := Nat.card_pos
    exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hpos.ne').mp h2
  have h2S : 2 ∣ Nat.card (S : Subgroup (centralizer (L : Set G))) := by
    rw [hcard]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' (G := (S : Subgroup (centralizer (L : Set G))))
    2 h2S
  have htS : ((t' : centralizer (L : Set G)) : G) ∈
      (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype :=
    ⟨t', t'.2, rfl⟩
  have ht : orderOf ((t' : centralizer (L : Set G)) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht']
  have hs : Sector L S ((t' : centralizer (L : Set G)) : G) := ⟨hL, hS, htS, ht⟩
  have hbot := center_eq_bot hL hodd θ
  have hZ := inf_centralizer_eq_bot_of_center_eq_bot hbot
  have h4 : 4 ≤ Nat.card (sg L S) := by
    rw [card_sg, hcard]
    have h1 : 2 ^ (Nat.card (centralizer (L : Set G))).factorization 2 ≠ 2 := hcard ▸ hne
    have h3 : 2 ≤ (Nat.card (centralizer (L : Set G))).factorization 2 := by
      by_contra h
      have : (Nat.card (centralizer (L : Set G))).factorization 2 = 1 := by omega
      rw [this] at h1
      exact h1 (by norm_num)
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) h3
  have e := MulEquiv.ofBijective (thetaZero θ) (thetaZero_bijective hL hodd θ)
  have hf := full_of_basic e hs (Group.IsPerfect.commutator_eq_top) hZ h4
  exact hf.false_of_four_le

end CFSG.OddStandard

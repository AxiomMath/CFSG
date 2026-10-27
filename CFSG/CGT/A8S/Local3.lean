module

public import CFSG.CGT.A8S.LocalStmt
public import CFSG.CGT.A8S.NaturalSL3
import CFSG.CGT.M24S.Local

public section

namespace CFSG.CGT.A8S

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.Holt.General

variable {G : Type} [Group G] {T H : Subgroup G}

structure LocalFacts3 (T H : Subgroup G) : Prop where
  card_T : Nat.card T = 8
  card_H : Nat.card H = 1344
  card_sylow : ∀ S : Sylow 2 G, Nat.card S = 2 ^ 6
  le_normalizer : H ≤ Subgroup.normalizer (T : Set G)
  inf_centralizer : H ⊓ Subgroup.centralizer (T : Set G) = T
  normalizer_eq : Subgroup.normalizer (T : Set G) = H ⊔ Subgroup.centralizer (T : Set G)
  transitive : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ H, h * x * h⁻¹ = y
  isTI : IsTI T
  centralizer_le : ∀ x ∈ T, x ≠ 1 →
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (T : Set G)
  centralizer_T_eq : Subgroup.centralizer (T : Set G) =
    T ⊔ oddCoreOf (Subgroup.centralizer (T : Set G))
  centralizer_eq : ∀ x ∈ T, x ≠ 1 → Subgroup.centralizer ({x} : Set G) =
    (H ⊓ Subgroup.centralizer ({x} : Set G)) ⊔ oddCoreOf (Subgroup.centralizer (T : Set G))
  card_inf_centralizer : ∀ x ∈ T, x ≠ 1 →
    Nat.card ↥(H ⊓ Subgroup.centralizer ({x} : Set G)) = 192
  oddCore_eq : ∀ x ∈ T, x ≠ 1 → oddCoreOf (Subgroup.centralizer ({x} : Set G)) =
    oddCoreOf (Subgroup.centralizer (T : Set G))
  sylow : ∃ S : Sylow 2 G, T ≤ (S : Subgroup G) ∧ (S : Subgroup G) ≤ H ∧ ∃ z₀ ∈ T, z₀ ≠ 1 ∧
    ∀ x ∈ (S : Subgroup G), ((∀ y ∈ (S : Subgroup G), x * y = y * x) ↔ (x = 1 ∨ x = z₀))

private theorem factorization_two_eq_six {m : ℕ} (hm : Odd m) :
    (1344 * m).factorization 2 = 6 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hm
  have h21 : ¬ 2 ∣ 21 * m := (Odd.mul (by decide) hm).not_two_dvd_nat
  rw [show 1344 * m = 2 ^ 6 * (21 * m) by ring,
    Nat.factorization_mul (by norm_num) (by positivity), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h21, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.prime_two.factorization_self]
  rfl

theorem card_sylow_of_naturalSL3 [Finite G] (hTH : T ≤ H) (hN : NaturalSL T H 3 1)
    (hodd : Odd H.index) (S : Sylow 2 G) : Nat.card S = 2 ^ 6 := by
  rw [Sylow.card_eq_multiplicity, ← H.card_mul_index, card_H_of_naturalSL3 hTH hN,
    factorization_two_eq_six hodd]

theorem odd_relIndex_centralizer_of_naturalSL3 (hTH : T ≤ H) (hN : NaturalSL T H 3 1)
    (hodd : Odd H.index) : Odd (T.relIndex (Subgroup.centralizer (T : Set G))) := by
  rw [relIndex_centralizer_of_naturalSL3 hTH hN]
  exact hodd.of_dvd_nat (Subgroup.relIndex_dvd_index_of_le (le_normalizer_of_naturalSL3 hTH hN))

theorem exists_mul_of_mem_centralizer_of_naturalSL3 [Finite G] (hTH : T ≤ H)
    (hN : NaturalSL T H 3 1) (hodd : Odd H.index) {c : G}
    (hc : c ∈ Subgroup.centralizer (T : Set G)) :
    ∃ t ∈ T, ∃ k ∈ oddCoreOf (Subgroup.centralizer (T : Set G)), c = t * k := by
  have hodd' := odd_relIndex_centralizer_of_naturalSL3 hTH hN hodd
  refine CFSG.CGT.M24S.exists_mul_mem_oddCoreOf_of_central (le_centralizer_of_naturalSL3 hTH hN)
    (fun z hz c hc => Subgroup.mem_centralizer_iff.1 hc z hz) ?_ hodd' hc
  rw [card_T_of_naturalSL3 hN]
  exact (Nat.coprime_two_left.2 hodd').pow_left 3

theorem centralizer_T_eq_of_naturalSL3 [Finite G] (hTH : T ≤ H) (hN : NaturalSL T H 3 1)
    (hodd : Odd H.index) :
    Subgroup.centralizer (T : Set G) = T ⊔ oddCoreOf (Subgroup.centralizer (T : Set G)) := by
  refine le_antisymm (fun c hc => ?_) (sup_le (le_centralizer_of_naturalSL3 hTH hN)
    (Subgroup.map_subtype_le _))
  obtain ⟨t, ht, k, hk, rfl⟩ := exists_mul_of_mem_centralizer_of_naturalSL3 hTH hN hodd hc
  exact Subgroup.mul_mem_sup ht hk

theorem centralizer_eq_of_naturalSL3 [Finite G] (hTH : T ≤ H) (hT : IsWC T)
    (hN : NaturalSL T H 3 1) (hodd : Odd H.index) {x : G} (hx : x ∈ T) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) =
      (H ⊓ Subgroup.centralizer ({x} : Set G)) ⊔
        oddCoreOf (Subgroup.centralizer (T : Set G)) := by
  have hCx : Subgroup.centralizer (T : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hx)
  refine le_antisymm (fun c hc => ?_) (sup_le inf_le_right
    ((Subgroup.map_subtype_le _).trans hCx))
  obtain ⟨h, hh, k, hk, rfl⟩ := CFSG.CGT.T75P.exists_mul_of_natural
    (le_normalizer_of_naturalSL3 hTH hN) hN (hT.centralizer_le_normalizer hx hx1 hc)
  obtain ⟨t, ht, o, ho, rfl⟩ := exists_mul_of_mem_centralizer_of_naturalSL3 hTH hN hodd hk
  have hoC : o ∈ Subgroup.centralizer ({x} : Set G) := hCx (Subgroup.map_subtype_le _ ho)
  have hht : h * t ∈ H ⊓ Subgroup.centralizer ({x} : Set G) := by
    refine ⟨H.mul_mem hh (hTH ht), ?_⟩
    have e : h * t = h * (t * o) * o⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hoC)
  rw [← mul_assoc]
  exact Subgroup.mul_mem_sup hht ho

theorem sylow_of_naturalSL3 [Finite G] (hTH : T ≤ H) (hN : NaturalSL T H 3 1)
    (hodd : Odd H.index) :
    ∃ S : Sylow 2 G, T ≤ (S : Subgroup G) ∧ (S : Subgroup G) ≤ H ∧ ∃ z₀ ∈ T, z₀ ≠ 1 ∧
      ∀ x ∈ (S : Subgroup G), ((∀ y ∈ (S : Subgroup G), x * y = y * x) ↔ (x = 1 ∨ x = z₀)) := by
  classical
  have hN' := hN
  obtain ⟨hn, -, -, -⟩ := hN'
  obtain ⟨S₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 ↥H))
  have hS₁card : Nat.card ((S₀ : Subgroup ↥H).map H.subtype) =
      2 ^ (Nat.card G).factorization 2 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, Sylow.card_eq_multiplicity,
      ← H.card_mul_index, card_H_of_naturalSL3 hTH hN, factorization_two_eq_six hodd,
      ← factorization_two_eq_six odd_one, mul_one]
  set S : Sylow 2 G := Sylow.ofCard _ hS₁card with hSdef
  have hS : (S : Subgroup G) = (S₀ : Subgroup ↥H).map H.subtype := Sylow.coe_ofCard _ _
  have hSH : (S : Subgroup G) ≤ H := hS ▸ Subgroup.map_subtype_le _
  have hTS : T ≤ (S : Subgroup G) := by
    have hTp : IsPGroup 2 (T.subgroupOf H) := IsPGroup.of_card (n := 3) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv, card_T_of_naturalSL3 hN]
      rfl)
    have hle := hTp.le_sylow_of_normal S₀
    intro t ht
    rw [hS]
    exact ⟨⟨t, hTH ht⟩, hle (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  have hcentT : ∀ x ∈ (S : Subgroup G), (∀ y ∈ (S : Subgroup G), x * y = y * x) → x ∈ T := by
    intro x hx hxc
    rw [← inf_centralizer_of_naturalSL3 hTH hN]
    exact ⟨hSH hx, Subgroup.mem_centralizer_iff.2 fun t ht => (hxc t (hTS ht)).symm⟩
  have hcardS := card_sylow_of_naturalSL3 hTH hN hodd S
  have : Nontrivial ↥(S : Subgroup G) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcardS]
    norm_num
  have := S.isPGroup'.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥(S : Subgroup G)))
  have hzc : ∀ y ∈ (S : Subgroup G), ((z : ↥(S : Subgroup G)) : G) * y = y * z := fun y hy =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨y, hy⟩)).symm
  have hz0 : ((z : ↥(S : Subgroup G)) : G) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  have hzT := hcentT _ (z : ↥(S : Subgroup G)).2 hzc
  refine ⟨S, hTS, hSH, _, hzT, hz0, fun x hx => ⟨fun hxc => ?_, ?_⟩⟩
  · by_contra hne
    obtain ⟨hx1, hxz⟩ := not_or.1 hne
    have hxT := hcentT x hx hxc
    have hle : (S : Subgroup G) ≤ H ⊓ Subgroup.centralizer ({((z : ↥(S : Subgroup G)) : G)} :
        Set G) ⊓ Subgroup.centralizer ({x} : Set G) := fun y hy =>
      ⟨⟨hSH hy, Subgroup.mem_centralizer_singleton_iff.2 (hzc y hy).symm⟩,
        Subgroup.mem_centralizer_singleton_iff.2 (hxc y hy).symm⟩
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcardS, card_inf_centralizer_pair_of_naturalSL3 hTH hN hzT hz0 hxT hx1
      (Ne.symm hxz)] at hdvd
    norm_num at hdvd
  · rintro (rfl | rfl)
    · exact fun y _ => by rw [one_mul, mul_one]
    · exact hzc

theorem A8Hyp.localFacts3 [Finite G] (h : A8Hyp T H) : LocalFacts3 T H where
  card_T := card_T_of_naturalSL3 h.nat
  card_H := card_H_of_naturalSL3 h.le h.nat
  card_sylow := card_sylow_of_naturalSL3 h.le h.nat h.odd
  le_normalizer := le_normalizer_of_naturalSL3 h.le h.nat
  inf_centralizer := inf_centralizer_of_naturalSL3 h.le h.nat
  normalizer_eq := normalizer_eq_of_naturalSL3 h.le h.nat
  transitive := transitive_of_naturalSL3 h.le h.nat
  isTI := h.wc.isTI
  centralizer_le := fun _ hx hx1 => h.wc.centralizer_le_normalizer hx hx1
  centralizer_T_eq := centralizer_T_eq_of_naturalSL3 h.le h.nat h.odd
  centralizer_eq := fun _ hx hx1 => centralizer_eq_of_naturalSL3 h.le h.wc h.nat h.odd hx hx1
  card_inf_centralizer := fun _ hx hx1 => card_inf_centralizer_of_naturalSL3 h.le h.nat hx hx1
  oddCore_eq := fun _ hx hx1 => CFSG.CGT.M24S.oddCore_eq_of_isWC h.wc hx hx1
  sylow := sylow_of_naturalSL3 h.le h.nat h.odd

theorem LocalFacts3.normalizer_eq_of_centralizer_eq (hL : LocalFacts3 T H) (hTH : T ≤ H)
    (hC : Subgroup.centralizer (T : Set G) = T) : Subgroup.normalizer (T : Set G) = H := by
  rw [hL.normalizer_eq, hC, sup_eq_left.mpr hTH]

end CFSG.CGT.A8S

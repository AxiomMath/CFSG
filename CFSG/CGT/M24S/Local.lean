module

public import CFSG.CGT.M24S.NaturalSL
public import CFSG.CGT.M24S.Defs

public section

namespace CFSG.CGT.M24S

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.Holt.General

variable {G : Type} [Group G] {T H : Subgroup G}

private theorem odd_card_oddCoreOf [Finite G] (B : Subgroup G) :
    Odd (Nat.card (oddCoreOf B)) := by
  rw [oddCoreOf, Subgroup.card_map_of_injective B.subtype_injective]
  exact Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card

private theorem conj_mem_oddCoreOf {B : Subgroup G} {b x : G} (hb : b ∈ B)
    (hx : x ∈ oddCoreOf B) : b * x * b⁻¹ ∈ oddCoreOf B := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨b, hb⟩ * y * ⟨b, hb⟩⁻¹,
    (CFSG.pPrimeCore_normal (p := 2) (G := ↥B)).conj_mem y hy ⟨b, hb⟩, rfl⟩

private theorem conj_mem_oddCoreOf_of_mem_normalizer {B : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (B : Set G)) (hx : x ∈ oddCoreOf B) :
    g * x * g⁻¹ ∈ oddCoreOf B := by
  obtain ⟨y, hy, rfl⟩ := hx
  let α : MulAut ↥B := B.normalizerMonoidHom ⟨g, hg⟩
  have h1 : α y ∈ CFSG.pPrimeCore 2 ↥B := by
    rw [← (inferInstance : (CFSG.pPrimeCore 2 ↥B).Characteristic).fixed α.symm]
    rw [Subgroup.mem_comap]
    simpa using hy
  exact ⟨α y, h1, rfl⟩

private theorem le_oddCoreOf_of_conj_mem {B K : Subgroup G} (hKB : K ≤ B)
    (hconj : ∀ b ∈ B, ∀ k ∈ K, b * k * b⁻¹ ∈ K) (hodd : Odd (Nat.card K)) : K ≤ oddCoreOf B := by
  have hn : (K.subgroupOf B).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hconj g g.2 n hn⟩
  have hcop : Nat.Coprime 2 (Nat.card (K.subgroupOf B)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKB).toEquiv]
    exact Nat.coprime_two_left.2 hodd
  have hle : K.subgroupOf B ≤ CFSG.pPrimeCore 2 ↥B := le_sSup ⟨hn, hcop⟩
  have h := Subgroup.map_mono (f := B.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hKB] at h

theorem exists_mul_mem_oddCoreOf_of_central [Finite G] {Z C : Subgroup G} (hZC : Z ≤ C)
    (hcomm : ∀ z ∈ Z, ∀ c ∈ C, z * c = c * z)
    (hcop : Nat.Coprime (Nat.card Z) (Z.relIndex C)) (hodd : Odd (Z.relIndex C)) {c : G}
    (hc : c ∈ C) : ∃ z ∈ Z, ∃ k ∈ oddCoreOf C, c = z * k := by
  classical
  set N₀ : Subgroup ↥C := Z.subgroupOf C with hN₀def
  have hcentral : ∀ n : ↥C, (n : G) ∈ Z → ∀ x : ↥C, n * x = x * n := fun n hn x =>
    Subtype.ext (hcomm n hn x x.2)
  have hN₀ : N₀.Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      rw [← hcentral n hn g, mul_inv_cancel_right]
      exact hn⟩
  have hcard : Nat.card N₀ = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv
  obtain ⟨K₀, hK₀⟩ := Subgroup.exists_right_complement'_of_coprime (N := N₀)
    (by rw [hcard]; exact hcop)
  have hK₀n : K₀.Normal := by
    refine ⟨fun k hk g => ?_⟩
    obtain ⟨⟨n, k'⟩, hnk⟩ := (hK₀.existsUnique g).exists
    rw [← hnk]
    have hconj : (n : ↥C) * k' * k * ((n : ↥C) * k')⁻¹ = k' * k * (k' : ↥C)⁻¹ := by
      have e : (n : ↥C) * k' * k * ((n : ↥C) * k')⁻¹ =
          (n : ↥C) * (k' * k * (k' : ↥C)⁻¹) * (n : ↥C)⁻¹ := by group
      rw [e, hcentral n n.2, mul_inv_cancel_right]
    rw [hconj]
    exact K₀.mul_mem (K₀.mul_mem k'.2 hk) (K₀.inv_mem k'.2)
  have hK₀card : Nat.card K₀ = Z.relIndex C := by
    have h1 := hK₀.card_mul_card
    have h2 := N₀.card_mul_index
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  set K : Subgroup G := K₀.map C.subtype with hKdef
  have hKC : K ≤ C := Subgroup.map_subtype_le _
  have hKO : K ≤ oddCoreOf C := by
    refine le_oddCoreOf_of_conj_mem hKC (fun b hb x hx => ?_) ?_
    · obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨⟨b, hb⟩ * y * ⟨b, hb⟩⁻¹, hK₀n.conj_mem y hy ⟨b, hb⟩, rfl⟩
    · rw [hKdef, Subgroup.card_map_of_injective C.subtype_injective, hK₀card]
      exact hodd
  obtain ⟨⟨n, k⟩, hnk⟩ := (hK₀.existsUnique ⟨c, hc⟩).exists
  refine ⟨n, n.2, k, hKO ⟨k, k.2, rfl⟩, ?_⟩
  exact (congrArg Subtype.val hnk).symm

private theorem factorization_two_eq_ten {m : ℕ} (hm : Odd m) :
    (322560 * m).factorization 2 = 10 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hm
  have h315 : ¬ 2 ∣ 315 * m := (Odd.mul (by decide) hm).not_two_dvd_nat
  rw [show 322560 * m = 2 ^ 10 * (315 * m) by ring,
    Nat.factorization_mul (by norm_num) (by positivity), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h315, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.prime_two.factorization_self]
  rfl

theorem card_sylow_of_naturalSL [Finite G] (hTH : T ≤ H) (hN : NaturalSL T H 4 1)
    (hodd : Odd H.index) (S : Sylow 2 G) : Nat.card S = 2 ^ 10 := by
  rw [Sylow.card_eq_multiplicity, ← H.card_mul_index, card_H_of_naturalSL hTH hN,
    factorization_two_eq_ten hodd]

theorem odd_relIndex_centralizer_of_naturalSL (hTH : T ≤ H) (hN : NaturalSL T H 4 1)
    (hodd : Odd H.index) : Odd (T.relIndex (Subgroup.centralizer (T : Set G))) := by
  rw [relIndex_centralizer_of_naturalSL hTH hN]
  exact hodd.of_dvd_nat (Subgroup.relIndex_dvd_index_of_le (le_normalizer_of_naturalSL_four hTH hN))

theorem exists_mul_of_mem_centralizer_of_naturalSL [Finite G] (hTH : T ≤ H)
    (hN : NaturalSL T H 4 1) (hodd : Odd H.index) {c : G}
    (hc : c ∈ Subgroup.centralizer (T : Set G)) :
    ∃ t ∈ T, ∃ k ∈ oddCoreOf (Subgroup.centralizer (T : Set G)), c = t * k := by
  have hodd' := odd_relIndex_centralizer_of_naturalSL hTH hN hodd
  refine exists_mul_mem_oddCoreOf_of_central (le_centralizer_of_naturalSL hTH hN)
    (fun z hz c hc => Subgroup.mem_centralizer_iff.1 hc z hz) ?_ hodd' hc
  rw [card_T_of_naturalSL hN]
  exact (Nat.coprime_two_left.2 hodd').pow_left 4

theorem centralizer_T_eq_of_naturalSL [Finite G] (hTH : T ≤ H) (hN : NaturalSL T H 4 1)
    (hodd : Odd H.index) :
    Subgroup.centralizer (T : Set G) = T ⊔ oddCoreOf (Subgroup.centralizer (T : Set G)) := by
  refine le_antisymm (fun c hc => ?_) (sup_le (le_centralizer_of_naturalSL hTH hN)
    (Subgroup.map_subtype_le _))
  obtain ⟨t, ht, k, hk, rfl⟩ := exists_mul_of_mem_centralizer_of_naturalSL hTH hN hodd hc
  exact Subgroup.mul_mem_sup ht hk

theorem centralizer_eq_of_naturalSL [Finite G] (hTH : T ≤ H) (hT : IsWC T)
    (hN : NaturalSL T H 4 1) (hodd : Odd H.index) {x : G} (hx : x ∈ T) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) =
      (H ⊓ Subgroup.centralizer ({x} : Set G)) ⊔
        oddCoreOf (Subgroup.centralizer (T : Set G)) := by
  have hCx : Subgroup.centralizer (T : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hx)
  refine le_antisymm (fun c hc => ?_) (sup_le inf_le_right
    ((Subgroup.map_subtype_le _).trans hCx))
  obtain ⟨h, hh, k, hk, rfl⟩ := CFSG.CGT.T75P.exists_mul_of_natural
    (le_normalizer_of_naturalSL_four hTH hN) hN (hT.centralizer_le_normalizer hx hx1 hc)
  obtain ⟨t, ht, o, ho, rfl⟩ := exists_mul_of_mem_centralizer_of_naturalSL hTH hN hodd hk
  have hoC : o ∈ Subgroup.centralizer ({x} : Set G) := hCx (Subgroup.map_subtype_le _ ho)
  have hht : h * t ∈ H ⊓ Subgroup.centralizer ({x} : Set G) := by
    refine ⟨H.mul_mem hh (hTH ht), ?_⟩
    have e : h * t = h * (t * o) * o⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hoC)
  rw [← mul_assoc]
  exact Subgroup.mul_mem_sup hht ho

theorem oddCore_eq_of_isWC [Finite G] (hT : IsWC T) {x : G} (hx : x ∈ T) (hx1 : x ≠ 1) :
    oddCoreOf (Subgroup.centralizer ({x} : Set G)) =
      oddCoreOf (Subgroup.centralizer (T : Set G)) := by
  set X := Subgroup.centralizer ({x} : Set G) with hXdef
  set C := Subgroup.centralizer (T : Set G) with hCdef
  have hCX : C ≤ X := Subgroup.centralizer_le (Set.singleton_subset_iff.2 hx)
  have hXN : X ≤ Subgroup.normalizer (T : Set G) := hT.centralizer_le_normalizer hx hx1
  have hTX : T ≤ X := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.2 (elemAbelian_mul_comm hT.1 ht hx)
  have hNC : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).1
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  apply le_antisymm
  · refine le_oddCoreOf_of_conj_mem (fun o ho => ?_)
      (fun b hb k hk => conj_mem_oddCoreOf (hCX hb) hk) (odd_card_oddCoreOf X)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hoX : o ∈ X := Subgroup.map_subtype_le _ ho
    have h3 : o * t * o⁻¹ * t⁻¹ ∈ T :=
      T.mul_mem (conj_mem_of_mem_normalizer (hXN hoX) ht) (T.inv_mem ht)
    have h4 : o * t * o⁻¹ * t⁻¹ ∈ oddCoreOf X := by
      have h2 := (oddCoreOf X).mul_mem ho (conj_mem_oddCoreOf (hTX ht) ((oddCoreOf X).inv_mem ho))
      simpa [mul_assoc] using h2
    have hcop : Nat.Coprime (Nat.card T) (Nat.card (oddCoreOf X)) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (isPGroup_two_of_isElemAbelian hT.1)
      rw [hn]
      exact (Nat.coprime_two_left.2 (odd_card_oddCoreOf X)).pow_left n
    have h5 : o * t * o⁻¹ * t⁻¹ = 1 :=
      (Subgroup.disjoint_def.1 (Subgroup.disjoint_of_coprime_natCard hcop)) h3 h4
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h5
    exact h5.symm
  · exact le_oddCoreOf_of_conj_mem ((Subgroup.map_subtype_le _).trans hCX)
      (fun b hb k hk => conj_mem_oddCoreOf_of_mem_normalizer (hNC (hXN hb)) hk)
      (odd_card_oddCoreOf C)

theorem sylow_of_naturalSL [Finite G] (hTH : T ≤ H) (hN : NaturalSL T H 4 1)
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
      ← H.card_mul_index, card_H_of_naturalSL hTH hN, factorization_two_eq_ten hodd,
      ← factorization_two_eq_ten odd_one, mul_one]
  set S : Sylow 2 G := Sylow.ofCard _ hS₁card with hSdef
  have hS : (S : Subgroup G) = (S₀ : Subgroup ↥H).map H.subtype := Sylow.coe_ofCard _ _
  have hSH : (S : Subgroup G) ≤ H := hS ▸ Subgroup.map_subtype_le _
  have hTS : T ≤ (S : Subgroup G) := by
    have hTp : IsPGroup 2 (T.subgroupOf H) := IsPGroup.of_card (n := 4) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv, card_T_of_naturalSL hN]
      rfl)
    have hle := hTp.le_sylow_of_normal S₀
    intro t ht
    rw [hS]
    exact ⟨⟨t, hTH ht⟩, hle (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  have hcentT : ∀ x ∈ (S : Subgroup G), (∀ y ∈ (S : Subgroup G), x * y = y * x) → x ∈ T := by
    intro x hx hxc
    rw [← inf_centralizer_of_naturalSL hTH hN]
    exact ⟨hSH hx, Subgroup.mem_centralizer_iff.2 fun t ht => (hxc t (hTS ht)).symm⟩
  have hcardS := card_sylow_of_naturalSL hTH hN hodd S
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
    rw [hcardS, card_inf_centralizer_pair_of_naturalSL hTH hN hzT hz0 hxT hx1
      (Ne.symm hxz)] at hdvd
    norm_num at hdvd
  · rintro (rfl | rfl)
    · exact fun y _ => by rw [one_mul, mul_one]
    · exact hzc

theorem Hyp.card_T (h : Hyp T H) : Nat.card T = 16 := card_T_of_naturalSL h.nat

theorem Hyp.card_H (h : Hyp T H) : Nat.card H = 322560 := card_H_of_naturalSL h.le h.nat

theorem Hyp.card_sylow [Finite G] (h : Hyp T H) : ∀ S : Sylow 2 G, Nat.card S = 2 ^ 10 :=
  card_sylow_of_naturalSL h.le h.nat h.odd

theorem Hyp.le_normalizer (h : Hyp T H) : H ≤ Subgroup.normalizer (T : Set G) :=
  le_normalizer_of_naturalSL_four h.le h.nat

theorem Hyp.inf_centralizer (h : Hyp T H) : H ⊓ Subgroup.centralizer (T : Set G) = T :=
  inf_centralizer_of_naturalSL h.le h.nat

theorem Hyp.normalizer_eq (h : Hyp T H) :
    Subgroup.normalizer (T : Set G) = H ⊔ Subgroup.centralizer (T : Set G) :=
  normalizer_eq_of_naturalSL h.le h.nat

theorem Hyp.transitive (h : Hyp T H) :
    ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ g ∈ H, g * x * g⁻¹ = y :=
  transitive_of_naturalSL h.le h.nat

theorem Hyp.isTI (h : Hyp T H) : IsTI T := h.wc.isTI

theorem Hyp.centralizer_le (h : Hyp T H) : ∀ x ∈ T, x ≠ 1 →
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (T : Set G) :=
  fun _ hx hx1 => h.wc.centralizer_le_normalizer hx hx1

theorem Hyp.centralizer_T_eq [Finite G] (h : Hyp T H) :
    Subgroup.centralizer (T : Set G) = T ⊔ oddCoreOf (Subgroup.centralizer (T : Set G)) :=
  centralizer_T_eq_of_naturalSL h.le h.nat h.odd

theorem Hyp.centralizer_eq [Finite G] (h : Hyp T H) : ∀ x ∈ T, x ≠ 1 →
    Subgroup.centralizer ({x} : Set G) =
      (H ⊓ Subgroup.centralizer ({x} : Set G)) ⊔ oddCoreOf (Subgroup.centralizer (T : Set G)) :=
  fun _ hx hx1 => centralizer_eq_of_naturalSL h.le h.wc h.nat h.odd hx hx1

theorem Hyp.oddCore_eq [Finite G] (h : Hyp T H) : ∀ x ∈ T, x ≠ 1 →
    oddCoreOf (Subgroup.centralizer ({x} : Set G)) =
      oddCoreOf (Subgroup.centralizer (T : Set G)) :=
  fun _ hx hx1 => oddCore_eq_of_isWC h.wc hx hx1

theorem Hyp.sylow [Finite G] (h : Hyp T H) :
    ∃ S : Sylow 2 G, T ≤ (S : Subgroup G) ∧ (S : Subgroup G) ≤ H ∧ ∃ z₀ ∈ T, z₀ ≠ 1 ∧
      ∀ x ∈ (S : Subgroup G), ((∀ y ∈ (S : Subgroup G), x * y = y * x) ↔ (x = 1 ∨ x = z₀)) :=
  sylow_of_naturalSL h.le h.nat h.odd

end CFSG.CGT.M24S

namespace CFSG.CGT.M24S

theorem Hyp.localFacts {G : Type} [Group G] [Finite G] {T H : Subgroup G} (h : Hyp T H) :
    LocalFacts T H where
  card_T := h.card_T
  card_H := h.card_H
  card_sylow := h.card_sylow
  le_normalizer := h.le_normalizer
  inf_centralizer := h.inf_centralizer
  normalizer_eq := h.normalizer_eq
  transitive := h.transitive
  isTI := h.isTI
  centralizer_le := h.centralizer_le
  centralizer_T_eq := h.centralizer_T_eq
  centralizer_eq := h.centralizer_eq
  oddCore_eq := h.oddCore_eq
  sylow := h.sylow

end CFSG.CGT.M24S

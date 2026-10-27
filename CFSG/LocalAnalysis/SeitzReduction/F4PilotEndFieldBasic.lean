module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTransferCyclic

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup

variable {G X : Type*} [Group G] [Group X] {G₀ : Subgroup G}

@[expose] def normalizerMulAut (e : G₀ ≃* X) : normalizer (G₀ : Set G) →* MulAut X :=
  (MulAut.congr e).toMonoidHom.comp G₀.normalizerMonoidHom

theorem coe_symm_normalizerMulAut_apply (e : G₀ ≃* X) (n : normalizer (G₀ : Set G)) (x : X) :
    ((e.symm (normalizerMulAut e n x) : G₀) : G) = n * (e.symm x : G) * (n : G)⁻¹ := by
  change ((e.symm (e (G₀.normalizerMonoidHom n (e.symm x))) : G₀) : G) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem normalizerMulAut_of_mem (e : G₀ ≃* X) {z : G} (hz : z ∈ G₀) :
    normalizerMulAut e ⟨z, le_normalizer hz⟩ = MulAut.conj (e ⟨z, hz⟩) := by
  apply MulEquiv.ext
  intro w
  apply e.symm.injective
  apply Subtype.ext
  rw [coe_symm_normalizerMulAut_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    MulEquiv.symm_apply_apply]
  rfl

theorem normalizerMulAut_injective (hC : centralizer (G₀ : Set G) = ⊥) (e : G₀ ≃* X) :
    Function.Injective (normalizerMulAut e) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro n hn
  have h2 : n ∈ G₀.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker] at hn ⊢
    apply (MulAut.congr e).injective
    rw [map_one]
    exact hn
  rw [normalizerMonoidHom_ker, mem_subgroupOf, hC, mem_bot] at h2
  exact mem_bot.2 (Subtype.ext h2)

theorem normalizerMulAut_mem_range_conj_iff (hC : centralizer (G₀ : Set G) = ⊥) (e : G₀ ≃* X)
    (n : normalizer (G₀ : Set G)) :
    normalizerMulAut e n ∈ (MulAut.conj : X →* MulAut X).range ↔ (n : G) ∈ G₀ := by
  constructor
  · rintro ⟨w, hw⟩
    have h1 : normalizerMulAut e ⟨(e.symm w : G), le_normalizer (e.symm w).2⟩ =
        normalizerMulAut e n := by
      rw [normalizerMulAut_of_mem e (e.symm w).2, ← hw]
      congr 1
      exact e.apply_symm_apply w
    rw [← normalizerMulAut_injective hC e h1]
    exact (e.symm w).2
  · intro hn
    exact ⟨e ⟨n, hn⟩, (normalizerMulAut_of_mem e hn).symm⟩

section Complement

variable (hC : centralizer (G₀ : Set G) = ⊥) (e : G₀ ≃* X) {C : Subgroup (MulAut X)}
  (hCInn : ∀ β ∈ C, β ∈ (MulAut.conj : X →* MulAut X).range → β = 1)
  (hNF : ∀ α : MulAut X, ∃ g : X, ∃ β ∈ C, α = MulAut.conj g * β)

include hC hCInn in
theorem inf_comap_normalizerMulAut_eq_bot :
    C.comap (normalizerMulAut e) ⊓ G₀.subgroupOf (normalizer (G₀ : Set G)) = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨hnP, hnG⟩ := mem_inf.1 hn
  rw [mem_comap] at hnP
  rw [mem_subgroupOf] at hnG
  have h1 := hCInn _ hnP ((normalizerMulAut_mem_range_conj_iff hC e n).2 hnG)
  exact mem_bot.2 (normalizerMulAut_injective hC e (h1.trans (map_one _).symm))

include hNF in
theorem exists_mem_inv_mul_mem_comap_normalizerMulAut (n : normalizer (G₀ : Set G)) :
    ∃ z ∈ G₀.subgroupOf (normalizer (G₀ : Set G)), z⁻¹ * n ∈ C.comap (normalizerMulAut e) := by
  obtain ⟨g, β, hβ, hn⟩ := hNF (normalizerMulAut e n)
  refine ⟨⟨(e.symm g : G), le_normalizer (e.symm g).2⟩, mem_subgroupOf.2 (e.symm g).2, ?_⟩
  rw [mem_comap, map_mul, map_inv, normalizerMulAut_of_mem e (e.symm g).2, hn]
  have he : e ⟨(e.symm g : G), (e.symm g).2⟩ = g := e.apply_symm_apply g
  rw [he, inv_mul_cancel_left]
  exact hβ

include hC hCInn hNF in
theorem bijective_mk_comp_subtype_comap_normalizerMulAut :
    Function.Bijective ((QuotientGroup.mk' (G₀.subgroupOf (normalizer (G₀ : Set G)))).comp
      (C.comap (normalizerMulAut e)).subtype) := by
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hp
    have h : (p : normalizer (G₀ : Set G)) ∈
        C.comap (normalizerMulAut e) ⊓ G₀.subgroupOf (normalizer (G₀ : Set G)) :=
      mem_inf.2 ⟨p.2, hp⟩
    rw [inf_comap_normalizerMulAut_eq_bot hC e hCInn, mem_bot] at h
    exact mem_bot.2 (Subtype.ext h)
  · intro q
    induction q using QuotientGroup.induction_on with
    | H n =>
      obtain ⟨z, hz, hzn⟩ := exists_mem_inv_mul_mem_comap_normalizerMulAut e hNF n
      refine ⟨⟨z⁻¹ * n, hzn⟩, ?_⟩
      have hz1 : QuotientGroup.mk' (G₀.subgroupOf (normalizer (G₀ : Set G))) z = 1 :=
        (QuotientGroup.eq_one_iff z).2 hz
      change QuotientGroup.mk' (G₀.subgroupOf (normalizer (G₀ : Set G))) (z⁻¹ * n) =
        QuotientGroup.mk' (G₀.subgroupOf (normalizer (G₀ : Set G))) n
      rw [map_mul, map_inv, hz1, inv_one, one_mul]

include hC in
theorem injective_subgroupComap_normalizerMulAut :
    Function.Injective ((normalizerMulAut e).subgroupComap C) :=
  (normalizerMulAut e).subgroupComap_injective C (normalizerMulAut_injective hC e)

include hC e hCInn hNF in
theorem isCyclic_quotient_normalizer_of_complement [IsCyclic C] :
    IsCyclic (normalizer (G₀ : Set G) ⧸ G₀.subgroupOf (normalizer (G₀ : Set G))) := by
  have : IsCyclic (C.comap (normalizerMulAut e)) :=
    isCyclic_of_injective _ (injective_subgroupComap_normalizerMulAut hC e)
  exact isCyclic_of_surjective _ (bijective_mk_comp_subtype_comap_normalizerMulAut hC e hCInn hNF).2

include hC e hCInn hNF in
theorem card_quotient_normalizer_dvd_of_complement :
    Nat.card (normalizer (G₀ : Set G) ⧸ G₀.subgroupOf (normalizer (G₀ : Set G))) ∣
      Nat.card C := by
  rw [← Nat.card_congr (Equiv.ofBijective _
    (bijective_mk_comp_subtype_comap_normalizerMulAut hC e hCInn hNF))]
  exact Subgroup.card_dvd_of_injective _ (injective_subgroupComap_normalizerMulAut hC e)

include hC hCInn hNF in
theorem exists_lift_orderOf_eq_of_complement
    (q : normalizer (G₀ : Set G) ⧸ G₀.subgroupOf (normalizer (G₀ : Set G))) :
    ∃ n : normalizer (G₀ : Set G), QuotientGroup.mk' _ n = q ∧ normalizerMulAut e n ∈ C ∧
      orderOf n = orderOf q := by
  have hb := bijective_mk_comp_subtype_comap_normalizerMulAut hC e hCInn hNF
  obtain ⟨p, hp⟩ := hb.2 q
  refine ⟨p, hp, p.2, ?_⟩
  rw [← hp, orderOf_injective _ hb.1 p, Subgroup.orderOf_coe]

end Complement

theorem two_lt_card_of_centralizer_eq_bot [Finite G] (hC : centralizer (G₀ : Set G) = ⊥) {t : G}
    (ht : orderOf t = 2) (htG : t ∉ G₀) : 2 < Nat.card G := by
  have hbot : G₀ ≠ ⊥ := by
    intro hG₀
    have htC : t ∈ centralizer (G₀ : Set G) := by
      rw [mem_centralizer_iff]
      intro h hh
      rw [hG₀, coe_bot, Set.mem_singleton_iff] at hh
      rw [hh, one_mul, mul_one]
    rw [hC, mem_bot] at htC
    rw [htC, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have h1 : 1 < Nat.card G₀ := (Subgroup.one_lt_card_iff_ne_bot _).2 hbot
  have h2 : 1 < G₀.index := Subgroup.one_lt_index_of_ne_top (fun h => htG (h ▸ mem_top t))
  rw [← G₀.card_mul_index]
  nlinarith

section Endgame

variable [Finite G] (hC : centralizer (G₀ : Set G) = ⊥) (e : G₀ ≃* X) {C : Subgroup (MulAut X)}
  [IsCyclic C] (hCInn : ∀ β ∈ C, β ∈ (MulAut.conj : X →* MulAut X).range → β = 1)
  (hNF : ∀ α : MulAut X, ∃ g : X, ∃ β ∈ C, α = MulAut.conj g * β)

include hC e hCInn hNF in
theorem exists_normal_index_two_of_complement {t : G} (htN : t ∈ normalizer (G₀ : Set G))
    (ht : orderOf t = 2) (htG : t ∉ G₀)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G))
    (hfus : ∀ y ∈ normalizer (G₀ : Set G), orderOf y = 2 → y ∉ G₀ → IsConj t y) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  have hb := bijective_mk_comp_subtype_comap_normalizerMulAut hC e hCInn hNF
  have hPcyc : IsCyclic (C.comap (normalizerMulAut e)) :=
    isCyclic_of_injective _ (injective_subgroupComap_normalizerMulAut hC e)
  have hcard : Nat.card (C.comap (normalizerMulAut e)) =
      Nat.card (normalizer (G₀ : Set G) ⧸ G₀.subgroupOf (normalizer (G₀ : Set G))) :=
    Nat.card_congr (Equiv.ofBijective _ hb)
  have htQ : orderOf (QuotientGroup.mk' (G₀.subgroupOf (normalizer (G₀ : Set G)))
      ⟨t, htN⟩) = 2 := by
    have h1 : orderOf (QuotientGroup.mk' (G₀.subgroupOf (normalizer (G₀ : Set G)))
        ⟨t, htN⟩) ∣ 2 := by
      refine (orderOf_map_dvd _ _).trans ?_
      rw [Subgroup.orderOf_mk, ht]
    have h2 : QuotientGroup.mk' (G₀.subgroupOf (normalizer (G₀ : Set G))) ⟨t, htN⟩ ≠ 1 := by
      rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact htG
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) h2
    · exact h
  set Q := normalizer (G₀ : Set G) ⧸ G₀.subgroupOf (normalizer (G₀ : Set G))
  have hQpos : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have h2Q : 2 ∣ Nat.card Q := htQ ▸ orderOf_dvd_natCard _
  set a := (Nat.card Q).factorization 2
  have ha : 1 ≤ a := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hQpos h2Q
  have hQ : ¬ 2 ^ (a + 1) ∣ Nat.card Q := Nat.pow_succ_factorization_not_dvd hQpos Nat.prime_two
  have haQ : 2 ^ a ∣ Nat.card Q := Nat.ordProj_dvd _ _
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := C.comap (normalizerMulAut e))
  have hk : Nat.card Q / 2 ^ a ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hQpos) haQ) (by positivity)).ne'
  have hx₀ : orderOf (g ^ (Nat.card Q / 2 ^ a)) = 2 ^ a := by
    rw [orderOf_pow_of_dvd hk (by rw [hg, hcard]; exact Nat.div_dvd_of_dvd haQ), hg, hcard,
      Nat.div_div_self haQ hQpos]
  set x₀ := g ^ (Nat.card Q / 2 ^ a)
  set x : G := ((x₀ : normalizer (G₀ : Set G)) : G) with hxdef
  have hxN : x ∈ normalizer (G₀ : Set G) := (x₀ : normalizer (G₀ : Set G)).2
  have hxo : orderOf x = 2 ^ a := by
    rw [hxdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx₀]
  have hxQ : orderOf (QuotientGroup.mk' (G₀.subgroupOf (normalizer (G₀ : Set G)))
      ⟨x, hxN⟩) = 2 ^ a := by
    change orderOf (((QuotientGroup.mk' (G₀.subgroupOf (normalizer (G₀ : Set G)))).comp
      (C.comap (normalizerMulAut e)).subtype) x₀) = 2 ^ a
    rw [orderOf_injective _ hb.1 x₀, hx₀]
  have hlt : 2 ^ (a - 1) < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hpow : IsConj t (x ^ 2 ^ (a - 1)) := by
    refine hfus _ (pow_mem hxN _) ?_ ?_
    · rw [orderOf_pow_of_dvd (by positivity) (by rw [hxo]; exact pow_dvd_pow 2 (by omega)), hxo,
        Nat.pow_div (by omega) (by norm_num), Nat.sub_sub_self ha, pow_one]
    · intro hy
      have h1 : (QuotientGroup.mk' (G₀.subgroupOf (normalizer (G₀ : Set G))) ⟨x, hxN⟩) ^
          2 ^ (a - 1) = 1 := by
        rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf,
          SubgroupClass.coe_pow]
        exact hy
      have h2 := Nat.le_of_dvd (by positivity) (hxQ ▸ orderOf_dvd_of_pow_eq_one h1)
      omega
  exact exists_normal_index_two_of_unique_of_quotient huniq hxN ha hxo hxQ hQ hpow

include hC e hCInn hNF in
theorem false_of_simple_of_complement [IsSimpleGroup G] {t : G}
    (htN : t ∈ normalizer (G₀ : Set G)) (ht : orderOf t = 2) (htG : t ∉ G₀)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G))
    (hfus : ∀ y ∈ normalizer (G₀ : Set G), orderOf y = 2 → y ∉ G₀ → IsConj t y) : False :=
  CFSG.SeitzReduction.not_exists_normal_index_two_of_simple
    (two_lt_card_of_centralizer_eq_bot hC ht htG)
    (exists_normal_index_two_of_complement hC e hCInn hNF htN ht htG huniq hfus)

end Endgame

end CFSG.SeitzReduction.F4Pilot

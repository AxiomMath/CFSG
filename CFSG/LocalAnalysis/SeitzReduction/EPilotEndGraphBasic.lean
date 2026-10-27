module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndFieldBasic

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.SeitzReduction.F4Pilot

variable {G : Type*} [Group G]

section Outer

variable {X : Type*} [Group X] {G₀ : Subgroup G}

theorem not_mem_of_normalizerMulAut_not_mem_range (e : G₀ ≃* X) {t : G}
    (htN : t ∈ normalizer (G₀ : Set G))
    (hout : normalizerMulAut e ⟨t, htN⟩ ∉ (MulAut.conj : X →* MulAut X).range) : t ∉ G₀ :=
  fun htG => hout ⟨e ⟨t, htG⟩, (normalizerMulAut_of_mem e htG).symm⟩

theorem ne_bot_of_normalizerMulAut_not_mem_range (e : G₀ ≃* X) {t : G}
    (htN : t ∈ normalizer (G₀ : Set G))
    (hout : normalizerMulAut e ⟨t, htN⟩ ∉ (MulAut.conj : X →* MulAut X).range) : G₀ ≠ ⊥ := by
  intro hbot
  have hX : ∀ x : X, x = 1 := fun x => by
    have h1 : ((e.symm x : G₀) : G) = 1 :=
      (Subgroup.eq_bot_iff_forall G₀).1 hbot _ (e.symm x).2
    rw [← e.apply_symm_apply x, show e.symm x = 1 from Subtype.ext h1, map_one]
  exact hout ⟨1, MulEquiv.ext fun x => (hX _).trans (hX _).symm⟩

theorem two_lt_card_of_normalizerMulAut_not_mem_range [Finite G] (e : G₀ ≃* X) {t : G}
    (htN : t ∈ normalizer (G₀ : Set G))
    (hout : normalizerMulAut e ⟨t, htN⟩ ∉ (MulAut.conj : X →* MulAut X).range) :
    2 < Nat.card G := by
  have h1 : 1 < Nat.card G₀ :=
    (Subgroup.one_lt_card_iff_ne_bot _).2 (ne_bot_of_normalizerMulAut_not_mem_range e htN hout)
  have h2 : 1 < G₀.index := Subgroup.one_lt_index_of_ne_top fun h =>
    not_mem_of_normalizerMulAut_not_mem_range e htN hout (h ▸ mem_top t)
  rw [← G₀.card_mul_index]
  nlinarith

end Outer

variable [Finite G]

theorem exists_normal_index_two_of_unique_of_not_four_dvd {M : Subgroup G} {t : G} (htM : t ∈ M)
    (ht : orderOf t = 2) (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M)
    {Q : Type*} [Group Q] [Finite Q] (ψ : M →* Q) (hQ : ¬ 4 ∣ Nat.card Q)
    (hψt : ψ ⟨t, htM⟩ ≠ 1) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  set z : ψ.range := ψ.rangeRestrict ⟨t, htM⟩ with hz
  have hzo : orderOf z = 2 ^ 1 := by
    have h1 : orderOf z ∣ 2 := by
      refine (orderOf_map_dvd _ _).trans ?_
      rw [Subgroup.orderOf_mk, ht]
    have h2 : z ≠ 1 := fun h => hψt (congrArg Subtype.val h)
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) h2
    · rw [h, pow_one]
  have hQ' : ¬ 2 ^ (1 + 1) ∣ Nat.card ψ.range := fun h =>
    hQ (h.trans (Subgroup.card_subgroup_dvd_card _))
  obtain ⟨R, hRidx, hzR, -⟩ := exists_index_two_of_orderOf_eq_two_pow le_rfl hzo hQ'
  set Y := (R.comap ψ.rangeRestrict).map M.subtype with hY
  have hYM : Y ≤ M := map_subtype_le _
  have hYidx : Y.relIndex M = 2 := by
    rw [relIndex, hY, ← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective,
      index_comap_of_surjective _ ψ.rangeRestrict_surjective, hRidx]
  have htY : t ∉ Y := by
    rintro ⟨m, hm, hmt⟩
    have hm' : m = ⟨t, htM⟩ := Subtype.ext hmt
    subst hm'
    exact hzR hm
  refine exists_normal_index_two_of_unique_of_relIndex_eq_two hYM hYidx huniq htM htY
    (a := 1) (by rw [ht, pow_one]) (fun y _ hyY _ => ?_) (n := 1)
    (isConj_iff.2 ⟨1, by simp⟩)
  have hy1 : y ≠ 1 := fun h => hyY (h ▸ Y.one_mem)
  have hy2 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
  have := orderOf_pos y
  omega

theorem exists_normal_index_two_of_mulAut_hom {X : Type*} [Group X] {G₀ : Subgroup G}
    (e : G₀ ≃* X) {t : G} (htN : t ∈ normalizer (G₀ : Set G)) (ht : orderOf t = 2)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G))
    {Q : Type*} [Group Q] [Finite Q] (χ : MulAut X →* Q) (hQ : ¬ 4 ∣ Nat.card Q)
    (hχt : χ (normalizerMulAut e ⟨t, htN⟩) ≠ 1) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 :=
  exists_normal_index_two_of_unique_of_not_four_dvd htN ht huniq (χ.comp (normalizerMulAut e)) hQ
    hχt

theorem false_of_simple_of_mulAut_hom [IsSimpleGroup G] {X : Type*} [Group X] {G₀ : Subgroup G}
    (e : G₀ ≃* X) {t : G} (htN : t ∈ normalizer (G₀ : Set G)) (ht : orderOf t = 2)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G))
    {Q : Type*} [Group Q] [Finite Q] (χ : MulAut X →* Q) (hQ : ¬ 4 ∣ Nat.card Q)
    (hχInn : ∀ x : X, χ (MulAut.conj x) = 1) (hχt : χ (normalizerMulAut e ⟨t, htN⟩) ≠ 1) :
    False := by
  have hout : normalizerMulAut e ⟨t, htN⟩ ∉ (MulAut.conj : X →* MulAut X).range := by
    rintro ⟨x, hx⟩
    exact hχt (hx ▸ hχInn x)
  exact CFSG.SeitzReduction.not_exists_normal_index_two_of_simple
    (two_lt_card_of_normalizerMulAut_not_mem_range e htN hout)
    (exists_normal_index_two_of_mulAut_hom e htN ht huniq χ hQ hχt)

section Complement

variable {X : Type*} [Group X] {G₀ : Subgroup G} (hC : centralizer (G₀ : Set G) = ⊥)
  (e : G₀ ≃* X) {C : Subgroup (MulAut X)} [IsCyclic C]
  (hCInn : ∀ β ∈ C, β ∈ (MulAut.conj : X →* MulAut X).range → β = 1)
  (hNF : ∀ α : MulAut X, ∃ g : X, ∃ β ∈ C, α = MulAut.conj g * β)

include hC e hCInn hNF in
theorem exists_normal_index_two_of_complement_of_fus {t : G}
    (htN : t ∈ normalizer (G₀ : Set G)) (ht : orderOf t = 2) (htG : t ∉ G₀)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G))
    (hfus : ∀ y (hy : y ∈ normalizer (G₀ : Set G)), orderOf y = 2 → y ∉ G₀ →
      normalizerMulAut e ⟨y, hy⟩ ∈ C → IsConj t y) :
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
    refine hfus _ (pow_mem hxN _) ?_ ?_ ?_
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
    · have e1 : (⟨x ^ 2 ^ (a - 1), pow_mem hxN _⟩ : normalizer (G₀ : Set G)) =
          (x₀ : normalizer (G₀ : Set G)) ^ 2 ^ (a - 1) := Subtype.ext (by
        rw [SubgroupClass.coe_pow])
      rw [e1, map_pow]
      exact pow_mem (mem_comap.1 x₀.2) _
  exact exists_normal_index_two_of_unique_of_quotient huniq hxN ha hxo hxQ hQ hpow

include hC e hCInn hNF in
theorem false_of_simple_of_complement_of_fus [IsSimpleGroup G] {t : G}
    (htN : t ∈ normalizer (G₀ : Set G)) (ht : orderOf t = 2) (htG : t ∉ G₀)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G))
    (hfus : ∀ y (hy : y ∈ normalizer (G₀ : Set G)), orderOf y = 2 → y ∉ G₀ →
      normalizerMulAut e ⟨y, hy⟩ ∈ C → IsConj t y) : False :=
  CFSG.SeitzReduction.not_exists_normal_index_two_of_simple
    (two_lt_card_of_centralizer_eq_bot hC ht htG)
    (exists_normal_index_two_of_complement_of_fus hC e hCInn hNF htN ht htG huniq hfus)

theorem eq_of_sq_eq_one_of_ne_one_of_isCyclic {C' : Type*} [Group C'] [Finite C'] [IsCyclic C']
    {u z : C'} (hu : u ^ 2 = 1) (hz : z ^ 2 = 1) (hu1 : u ≠ 1) (hz1 : z ≠ 1) : u = z := by
  classical
  have := Fintype.ofFinite C'
  by_contra h
  have hsub : ({1, z, u} : Finset C') ⊆ Finset.univ.filter (fun a : C' => a ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter]
    rcases hx with rfl | rfl | rfl
    · exact ⟨Finset.mem_univ _, one_pow 2⟩
    · exact ⟨Finset.mem_univ _, hz⟩
    · exact ⟨Finset.mem_univ _, hu⟩
  have h3 : ({1, z, u} : Finset C').card = 3 :=
    Finset.card_eq_three.2 ⟨1, z, u, hz1.symm, hu1.symm, fun e => h e.symm, rfl⟩
  have hle := IsCyclic.card_pow_eq_one_le (α := C') (n := 2) (by norm_num)
  have := Finset.card_le_card hsub
  omega

include hC e hCInn hNF in
theorem exists_normal_index_two_of_complement_of_isConj {t : G}
    (htN : t ∈ normalizer (G₀ : Set G)) (ht : orderOf t = 2) (htG : t ∉ G₀)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G))
    (hconj : ∃ φ : MulAut X, φ * normalizerMulAut e ⟨t, htN⟩ * φ⁻¹ ∈ C) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  have : Finite X := Finite.of_equiv _ e.toEquiv
  have : Finite (MulAut X) :=
    Finite.of_injective (fun f : MulAut X => (f : X → X)) DFunLike.coe_injective
  have hAinj := normalizerMulAut_injective hC e
  obtain ⟨φ, hφC⟩ := hconj
  set τ := normalizerMulAut e ⟨t, htN⟩ with hτdef
  set ι := φ * τ * φ⁻¹ with hιdef
  have ht2 : (⟨t, htN⟩ : normalizer (G₀ : Set G)) ^ 2 = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow, ← ht, pow_orderOf_eq_one]; rfl)
  have hτ2 : τ ^ 2 = 1 := by rw [hτdef, ← map_pow, ht2, map_one]
  have hι2 : ι ^ 2 = 1 := by rw [hιdef, conj_pow, hτ2, mul_one, mul_inv_cancel]
  have hτ1 : τ ≠ 1 := by
    intro h
    have h1 : (⟨t, htN⟩ : normalizer (G₀ : Set G)) = 1 := hAinj (h.trans (map_one _).symm)
    have h2 : t = 1 := congrArg Subtype.val h1
    rw [h2, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hι1 : ι ≠ 1 := by
    intro h
    apply hτ1
    have h1 : τ = φ⁻¹ * ι * φ := by rw [hιdef]; group
    rw [h1, h, mul_one, inv_mul_cancel]
  obtain ⟨g, β, hβ, hφg⟩ := hNF φ⁻¹
  have hcomm : β * ι = ι * β :=
    congrArg Subtype.val ((IsCyclic.commGroup (α := C)).mul_comm ⟨β, hβ⟩ ⟨ι, hφC⟩)
  have hτg : τ = MulAut.conj g * ι * (MulAut.conj g)⁻¹ := by
    calc τ = φ⁻¹ * ι * φ⁻¹⁻¹ := by rw [hιdef]; group
      _ = MulAut.conj g * (β * ι) * β⁻¹ * (MulAut.conj g)⁻¹ := by rw [hφg]; group
      _ = MulAut.conj g * ι * (MulAut.conj g)⁻¹ := by rw [hcomm]; group
  set z : normalizer (G₀ : Set G) := ⟨(e.symm g : G), le_normalizer (e.symm g).2⟩ with hzdef
  have hAz : normalizerMulAut e z = MulAut.conj g := by
    rw [hzdef, normalizerMulAut_of_mem e (e.symm g).2]
    exact congrArg MulAut.conj (e.apply_symm_apply g)
  have hAs : normalizerMulAut e (z⁻¹ * ⟨t, htN⟩ * z) = ι := by
    rw [map_mul, map_mul, map_inv, hAz, ← hτdef, hτg]
    group
  refine exists_normal_index_two_of_complement_of_fus hC e hCInn hNF htN ht htG huniq
    fun y hyN hy2 hyG hyC => ?_
  have hy2' : (⟨y, hyN⟩ : normalizer (G₀ : Set G)) ^ 2 = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow, ← hy2, pow_orderOf_eq_one]; rfl)
  have hAy1 : normalizerMulAut e ⟨y, hyN⟩ ≠ 1 := by
    intro h
    have h1 : (⟨y, hyN⟩ : normalizer (G₀ : Set G)) = 1 := hAinj (h.trans (map_one _).symm)
    exact hyG (by rw [show y = 1 from congrArg Subtype.val h1]; exact G₀.one_mem)
  have hAyι : normalizerMulAut e ⟨y, hyN⟩ = ι := by
    have h := eq_of_sq_eq_one_of_ne_one_of_isCyclic (C' := C) (u := ⟨_, hyC⟩) (z := ⟨ι, hφC⟩)
      (Subtype.ext (by rw [SubgroupClass.coe_pow, ← map_pow, hy2', map_one]; rfl))
      (Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hι2))
      (fun h => hAy1 (congrArg Subtype.val h)) (fun h => hι1 (congrArg Subtype.val h))
    exact congrArg Subtype.val h
  have hy : (⟨y, hyN⟩ : normalizer (G₀ : Set G)) = z⁻¹ * ⟨t, htN⟩ * z :=
    hAinj (hAyι.trans hAs.symm)
  refine isConj_iff.2 ⟨((z : normalizer (G₀ : Set G)) : G)⁻¹, ?_⟩
  have h1 := congrArg Subtype.val hy
  simp only [coe_mul, coe_inv] at h1
  rw [h1]
  group

end Complement

end CFSG.SeitzReduction.EPilot

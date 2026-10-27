module

public import CFSG.ClassicalInvolution.AschTight.Hall196Idx
public import CFSG.ClassicalInvolution.AschTight.E3StarD
public import CFSG.ClassicalInvolution.Asc77.AscSixModCent
public import CFSG.ClassicalInvolution.Q3.Q3T6AutInn
public import CFSG.ClassicalInvolution.Q3.Q3T6AutTwo
public import CFSG.ClassicalInvolution.Asc77.WP2Defs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Action

variable {G : Type} [Group G] {K : Subgroup G}

@[expose] def normalizerToAutSL3 (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3)) :
    Subgroup.normalizer (K : Set G) →* MulAut SL(2, ZMod 3) :=
  (MulAut.congr e).toMonoidHom.comp ((oddCoreQuotientAut K).comp (normalizerConj K))

variable (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3))

theorem normalizerToAutSL3_apply (n : Subgroup.normalizer (K : Set G)) (y : K) :
    normalizerToAutSL3 e n (e (QuotientGroup.mk y)) =
      e (QuotientGroup.mk (normalizerConj K n y)) := by
  simp [normalizerToAutSL3, MulAut.congr_apply, oddCoreQuotientAut_mk]

theorem normalizerToAutSL3_eq_one_iff_oddCoreQuotientAut (n : Subgroup.normalizer (K : Set G)) :
    normalizerToAutSL3 e n = 1 ↔ oddCoreQuotientAut K (normalizerConj K n) = 1 := by
  change MulAut.congr e (oddCoreQuotientAut K (normalizerConj K n)) = 1 ↔ _
  rw [← map_one (MulAut.congr e)]
  exact (MulAut.congr e).injective.eq_iff

theorem normalizerToAutSL3_eq_one_iff (n : Subgroup.normalizer (K : Set G)) :
    normalizerToAutSL3 e n = 1 ↔ ∀ l ∈ K, ⁅(n : G), l⁆ ∈ Asc77.oddCoreOf K := by
  rw [normalizerToAutSL3_eq_one_iff_oddCoreQuotientAut,
    Hall196.oddCoreQuotientAut_normalizerConj_eq_one_iff]

theorem normalizerToAutSL3_of_mem {k : G} (hk : k ∈ K) :
    normalizerToAutSL3 e ⟨k, Subgroup.le_normalizer hk⟩ =
      MulAut.conj (e (QuotientGroup.mk ⟨k, hk⟩)) :=
  Hall196.congr_oddCoreQuotientAut_of_mem e hk

theorem mem_cStar_iff_normalizerToAutSL3_eq_one (n : Subgroup.normalizer (K : Set G)) :
    (n : G) ∈ cStar K ↔ normalizerToAutSL3 e n = 1 := by
  rw [normalizerToAutSL3_eq_one_iff_oddCoreQuotientAut]
  constructor
  · rintro ⟨n', hn', hn'n⟩
    have : n' = n := Subtype.ext hn'n
    rw [← this]
    exact hn'
  · intro h
    exact ⟨n, h, rfl⟩

theorem map_subgroupOf_eq_inn3 :
    (K.subgroupOf (Subgroup.normalizer (K : Set G))).map (normalizerToAutSL3 e) = inn3 := by
  apply le_antisymm
  · rintro _ ⟨n, hn, rfl⟩
    have hn' : (n : G) ∈ K := Subgroup.mem_subgroupOf.mp hn
    have : n = ⟨(n : G), Subgroup.le_normalizer hn'⟩ := rfl
    rw [this, normalizerToAutSL3_of_mem e hn']
    exact conj_mem_inn3 _
  · rintro _ ⟨s, rfl⟩
    obtain ⟨κ, hκ⟩ := QuotientGroup.mk_surjective (e.symm s)
    refine ⟨⟨κ, Subgroup.le_normalizer κ.2⟩, Subgroup.mem_subgroupOf.mpr κ.2, ?_⟩
    rw [normalizerToAutSL3_of_mem e κ.2]
    have hs : e (QuotientGroup.mk κ) = s := by rw [hκ, MulEquiv.apply_symm_apply]
    rw [hs]

theorem exists_conj_gl3_of_normalizer (n : Subgroup.normalizer (K : Set G)) :
    ∃ g : GL (Fin 2) (ZMod 3), ∀ y : K,
      ((e (QuotientGroup.mk (normalizerConj K n y)) : SL(2, ZMod 3)) :
        Matrix (Fin 2) (Fin 2) (ZMod 3)) =
        (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
          ((e (QuotientGroup.mk y) : SL(2, ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
          ((g⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
  obtain ⟨g, hg⟩ := sl2Three_aut_eq_conj (normalizerToAutSL3 e n)
  refine ⟨g, fun y => ?_⟩
  rw [← normalizerToAutSL3_apply e n y]
  exact hg _

theorem exists_conjSL_eq_normalizerToAutSL3 (n : Subgroup.normalizer (K : Set G)) :
    ∃ g : GL (Fin 2) (ZMod 3), ∀ b, normalizerToAutSL3 e n b = conjSL g b := by
  obtain ⟨g, hg⟩ := sl2Three_aut_eq_conj (normalizerToAutSL3 e n)
  exact ⟨g, fun b => Subtype.ext (by rw [coe_conjSL]; exact hg b)⟩

end Action

section E3

variable {G : Type} [Group G] {K : Subgroup G}

theorem normalizerQuotientTwoGeneratedStar_three
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3)) :
    NormalizerQuotientTwoGeneratedStar K := by
  intro P hP hPN
  have hP' : IsPGroup 2 (P.subgroupOf (Subgroup.normalizer (K : Set G))) := hP.comap_subtype
  obtain ⟨a, b, hab⟩ :=
    sl2Three_mulAut_isPGroup_exists_closure_pair (hP'.map (normalizerToAutSL3 e))
  exact closure_pair_sup_eq_of_map (C := cStar K)
    (fun n hn => (mem_cStar_iff_normalizerToAutSL3_eq_one e n).mpr hn) hPN hab

theorem normalizerQuotientTwoGeneratedStar_of_member3 {z : G} (h : IsClassicalMember3 K z) :
    NormalizerQuotientTwoGeneratedStar K := by
  obtain ⟨e⟩ := h.nonempty_equiv
  exact normalizerQuotientTwoGeneratedStar_three e

theorem centSylow_three [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : ∀ K ∈ Ω, Nonempty (K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3))) :
    Asc77.AscL62.CentSylow Ω := by
  intro K R V hK hR _ hVK hcomm k hk v hv
  obtain ⟨e⟩ := hΩ K hK
  have hvN : v ∈ Subgroup.normalizer (K : Set G) :=
    Asc77.mem_normalizer_iff_conjSub_eq.mpr (hVK v hv)
  set φ : ↥K →* SL(2, ZMod 3) :=
    (e : ↥K ⧸ classicalInvolutionOddCore ↥K →* SL(2, ZMod 3)).comp
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥K)) with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P : Sylow 2 SL(2, ZMod 3) :=
    Sylow.mapSurjective (f := φ) hφs (Asc77.AscL62.sylowOfIsSylow2In'' hR)
  have hfix : ∀ x ∈ P, normalizerToAutSL3 e ⟨v, hvN⟩ x = x := by
    intro x hx
    have hx' : x ∈ ((Asc77.AscL62.sylowOfIsSylow2In'' hR : Subgroup ↥K)).map φ := by
      have := Sylow.coe_mapSurjective (f := φ) hφs (Asc77.AscL62.sylowOfIsSylow2In'' hR)
      rw [← this]
      exact hx
    obtain ⟨r, hr, rfl⟩ := hx'
    have hrR : (r : G) ∈ R := hr
    have hαr : normalizerConj K ⟨v, hvN⟩ r = r := by
      apply Subtype.ext
      rw [normalizerConj_apply_coe, ← hcomm r hrR v hv]
      group
    show normalizerToAutSL3 e ⟨v, hvN⟩ (e (QuotientGroup.mk r)) = e (QuotientGroup.mk r)
    rw [normalizerToAutSL3_apply, hαr]
  exact (normalizerToAutSL3_eq_one_iff e ⟨v, hvN⟩).mp
    (sl2Three_mulAut_eq_one_of_fixes_sylow P _ hfix) k hk

end E3

section Hall

variable {G : Type} [Group G] {K : Subgroup G}
  (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3))

private theorem subgroupOf_le_aux {A B : Subgroup G} (h : A ≤ B) (N : Subgroup G) :
    A.subgroupOf N ≤ B.subgroupOf N := fun _ hx =>
  Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hx))

theorem map_eq_top_of_not_map_le_inn {X V : Subgroup G} (hKX : K ≤ X) (hVX : V ≤ X)
    (hV : ¬ (V.subgroupOf (Subgroup.normalizer (K : Set G))).map (normalizerToAutSL3 e) ≤ inn3) :
    (X.subgroupOf (Subgroup.normalizer (K : Set G))).map (normalizerToAutSL3 e) = ⊤ := by
  have hPSL : inn3 ≤ (X.subgroupOf (Subgroup.normalizer (K : Set G))).map
      (normalizerToAutSL3 e) := by
    rw [← map_subgroupOf_eq_inn3 e]
    exact Subgroup.map_mono (subgroupOf_le_aux hKX _)
  refine Hall196.eq_of_relIndex_eq_two hPSL le_top ?_ fun h => hV
    ((Subgroup.map_mono (subgroupOf_le_aux hVX _)).trans h)
  rw [Subgroup.relIndex_top_right, inn3_index]

theorem subgroupOf_sup_eq_three {X Y : Subgroup G} (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hYX : Y ≤ X)
    (hY : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (K : Set G)),
      x ∈ Y ↔ x ∈ X ∧ normalizerToAutSL3 e ⟨x, hx⟩ = 1) :
    (K ⊔ Y).subgroupOf (Subgroup.normalizer (K : Set G)) =
      inn3.comap (normalizerToAutSL3 e) ⊓
        X.subgroupOf (Subgroup.normalizer (K : Set G)) := by
  set N := Subgroup.normalizer (K : Set G) with hN
  set Ψ := normalizerToAutSL3 e with hΨ
  apply le_antisymm
  · have hle : K ⊔ Y ≤ (inn3.comap Ψ).map N.subtype := by
      refine sup_le (fun k hk => ⟨⟨k, Subgroup.le_normalizer hk⟩, ?_, rfl⟩) (fun y hy => ?_)
      · change Ψ ⟨k, Subgroup.le_normalizer hk⟩ ∈ inn3
        rw [hΨ, normalizerToAutSL3_of_mem e hk]
        exact conj_mem_inn3 _
      · have hyN := hXN (hYX hy)
        refine ⟨⟨y, hyN⟩, ?_, rfl⟩
        change Ψ ⟨y, hyN⟩ ∈ inn3
        rw [((hY y hyN).mp hy).2]
        exact inn3.one_mem
    intro x hx
    refine ⟨?_, Subgroup.mem_subgroupOf.mpr (sup_le hKX hYX (Subgroup.mem_subgroupOf.mp hx))⟩
    obtain ⟨y, hy, hyx⟩ := hle (Subgroup.mem_subgroupOf.mp hx)
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  · rintro x ⟨hxP, hxX⟩
    have hxP' : Ψ x ∈ (K.subgroupOf N).map Ψ := by
      rw [hΨ, map_subgroupOf_eq_inn3 e]
      exact hxP
    obtain ⟨k, hk, hkx⟩ := hxP'
    have hk' : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have h1 : Ψ (k⁻¹ * x) = 1 := by rw [map_mul, map_inv, hkx, inv_mul_cancel]
    have h2 : ((k⁻¹ * x : N) : G) ∈ Y := by
      refine (hY _ (k⁻¹ * x).2).mpr ⟨?_, h1⟩
      exact X.mul_mem (X.inv_mem (hKX hk')) (Subgroup.mem_subgroupOf.mp hxX)
    have e1 : (x : G) = k * ((k⁻¹ * x : N) : G) := by simp
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [e1]
    exact (K ⊔ Y).mul_mem (Subgroup.mem_sup_left hk') (Subgroup.mem_sup_right h2)

theorem relIndex_sup_eq_two_three {X Y V : Subgroup G} (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hYX : Y ≤ X) (hVX : V ≤ X)
    (hY : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (K : Set G)),
      x ∈ Y ↔ x ∈ X ∧ normalizerToAutSL3 e ⟨x, hx⟩ = 1)
    (hV : ¬ (V.subgroupOf (Subgroup.normalizer (K : Set G))).map (normalizerToAutSL3 e) ≤ inn3) :
    (K ⊔ Y).relIndex X = 2 ∧ ¬ V ≤ K ⊔ Y ∧ K ⊔ Y ⊔ V = X := by
  have hKY := subgroupOf_sup_eq_three e hKX hXN hYX hY
  have hXeq := map_eq_top_of_not_map_le_inn e hKX hVX hV
  have hidx : (K ⊔ Y).relIndex X = 2 := by
    rw [← Subgroup.relIndex_subgroupOf hXN, hKY, Subgroup.inf_relIndex_right,
      Subgroup.relIndex_comap, hXeq, Subgroup.relIndex_top_right, inn3_index]
  have hnot : ¬ V ≤ K ⊔ Y := by
    intro hVKY
    apply hV
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v ∈ (K ⊔ Y).subgroupOf (Subgroup.normalizer (K : Set G)) :=
      Subgroup.mem_subgroupOf.mpr (hVKY (Subgroup.mem_subgroupOf.mp hv))
    rw [hKY] at hv'
    exact hv'.1
  exact ⟨hidx, hnot, Hall196.eq_of_relIndex_eq_two le_sup_left
    (sup_le (sup_le hKX hYX) hVX) hidx fun h => hnot (le_sup_right.trans h)⟩

theorem not_map_le_inn3_of_orderOf_four {V : Subgroup G} {v : G} (hvV : v ∈ V)
    (hvN : v ∈ Subgroup.normalizer (K : Set G))
    (h4 : orderOf (normalizerToAutSL3 e ⟨v, hvN⟩) = 4) :
    ¬ (V.subgroupOf (Subgroup.normalizer (K : Set G))).map (normalizerToAutSL3 e) ≤ inn3 :=
  fun h => orderOf_ne_four_of_mem_inn3
    (h ⟨⟨v, hvN⟩, Subgroup.mem_subgroupOf.mpr hvV, rfl⟩) h4

theorem normalizer_le_sup_of_map_eq_top {X C : Subgroup G}
    (hX : (X.subgroupOf (Subgroup.normalizer (K : Set G))).map (normalizerToAutSL3 e) = ⊤)
    (hC : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (K : Set G)),
      normalizerToAutSL3 e ⟨x, hx⟩ = 1 → x ∈ C) (n : Subgroup.normalizer (K : Set G)) :
    (n : G) ∈ X ⊔ C := by
  have hn : normalizerToAutSL3 e n ∈ (X.subgroupOf (Subgroup.normalizer (K : Set G))).map
      (normalizerToAutSL3 e) := by
    rw [hX]
    exact Subgroup.mem_top _
  obtain ⟨x, hx, hxn⟩ := hn
  have h1 : normalizerToAutSL3 e (x⁻¹ * n) = 1 := by
    rw [map_mul, map_inv, hxn, inv_mul_cancel]
  have e1 : (n : G) = (x : G) * ((x⁻¹ * n : Subgroup.normalizer (K : Set G)) : G) := by simp
  rw [e1]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hx) (hC _ (x⁻¹ * n).2 h1)

end Hall

section Extras

variable {G : Type} [Group G] {K : Subgroup G}
  (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3))

private theorem mem_normalizer_oddCoreOf_aux {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    n ∈ Subgroup.normalizer (Asc77.oddCoreOf K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => Asc77.mem_normalizer_oddCoreOf_of_mem_normalizer hn hh, fun hh => ?_⟩
  have := Asc77.mem_normalizer_oddCoreOf_of_mem_normalizer
    ((Subgroup.normalizer (K : Set G)).inv_mem hn) hh
  simpa [mul_assoc] using this

theorem normalizerToAutSL3_eq_one_iff_mem_centralizerModOdd
    (n : Subgroup.normalizer (K : Set G)) :
    normalizerToAutSL3 e n = 1 ↔ (n : G) ∈ Asc77.centralizerModOdd ⊤ K := by
  rw [normalizerToAutSL3_eq_one_iff]
  exact ⟨fun h => ⟨Subgroup.mem_top _, n.2, mem_normalizer_oddCoreOf_aux n.2, h⟩,
    fun h => h.2.2.2⟩

theorem mem_centralizerModOdd_iff_normalizerToAutSL3 (X : Subgroup G) {x : G}
    (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    x ∈ Asc77.centralizerModOdd X K ↔ x ∈ X ∧ normalizerToAutSL3 e ⟨x, hx⟩ = 1 := by
  rw [normalizerToAutSL3_eq_one_iff]
  exact ⟨fun h => ⟨h.1, h.2.2.2⟩, fun h => ⟨h.1, hx, mem_normalizer_oddCoreOf_aux hx, h.2⟩⟩

theorem Aut.centralizerModOdd_le_self (X : Subgroup G) : Asc77.centralizerModOdd X K ≤ X :=
  fun _ h => h.1

theorem orderOf_normalizerToAutSL3_eq_four {v : G} (hvN : v ∈ Subgroup.normalizer (K : Set G))
    (hv4 : orderOf v = 4)
    (h2 : normalizerToAutSL3 e ⟨v ^ 2, (Subgroup.normalizer (K : Set G)).pow_mem hvN 2⟩ ≠ 1) :
    orderOf (normalizerToAutSL3 e ⟨v, hvN⟩) = 4 := by
  have hpow : ∀ m : ℕ, (⟨v, hvN⟩ : Subgroup.normalizer (K : Set G)) ^ m =
      ⟨v ^ m, (Subgroup.normalizer (K : Set G)).pow_mem hvN m⟩ := fun m => rfl
  have e1 : (normalizerToAutSL3 e ⟨v, hvN⟩) ^ 2 ^ 1 ≠ 1 := by
    rw [pow_one, ← map_pow, hpow]
    exact h2
  have e2 : (normalizerToAutSL3 e ⟨v, hvN⟩) ^ 2 ^ (1 + 1) = 1 := by
    rw [← map_pow, hpow, show 2 ^ (1 + 1) = orderOf v by rw [hv4]; norm_num]
    simp only [pow_orderOf_eq_one]
    exact map_one _
  have := orderOf_eq_prime_pow e1 e2
  rwa [show 2 ^ (1 + 1) = 4 by norm_num] at this

theorem not_map_le_inn3_of_cyclic {V : Subgroup G} (hVN : V ≤ Subgroup.normalizer (K : Set G))
    (hV2 : IsPGroup 2 V) (hVc : IsCyclic V) (h4 : 4 ≤ Nat.card V)
    (hinj : ∀ (v : G) (hv : v ∈ V), normalizerToAutSL3 e ⟨v, hVN hv⟩ = 1 → v = 1) :
    ¬ (V.subgroupOf (Subgroup.normalizer (K : Set G))).map (normalizerToAutSL3 e) ≤ inn3 := by
  have : Finite V := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨g, hg⟩ := hVc.exists_generator
  obtain ⟨k, hk⟩ := hV2.exists_card_eq
  have hord : orderOf (g : G) = 2 ^ k := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hk]
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hu4 : orderOf ((g : G) ^ 2 ^ (k - 2)) = 4 := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hord]; exact pow_dvd_pow 2 (by omega)), hord,
      show 2 ^ k = 2 ^ (k - 2) * 4 by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega]
    exact Nat.mul_div_cancel_left 4 (by positivity)
  have huV : (g : G) ^ 2 ^ (k - 2) ∈ V := V.pow_mem g.2 _
  refine not_map_le_inn3_of_orderOf_four e huV (hVN huV)
    (orderOf_normalizerToAutSL3_eq_four e (hVN huV) hu4 ?_)
  intro h
  have h1 : ((g : G) ^ 2 ^ (k - 2)) ^ 2 = 1 := hinj _ (V.pow_mem huV 2) h
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hu4] at h2
  omega

theorem not_map_le_inn3_of_inf_eq_bot {X Y V : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hVX : V ≤ X)
    (hY : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (K : Set G)),
      x ∈ Y ↔ x ∈ X ∧ normalizerToAutSL3 e ⟨x, hx⟩ = 1)
    (hVY : V ⊓ Y = ⊥) (hV2 : IsPGroup 2 V) (hVc : IsCyclic V) (h4 : 4 ≤ Nat.card V) :
    ¬ (V.subgroupOf (Subgroup.normalizer (K : Set G))).map (normalizerToAutSL3 e) ≤ inn3 := by
  refine not_map_le_inn3_of_cyclic e (hVX.trans hXN) hV2 hVc h4 fun v hv h1 => ?_
  have hvY : v ∈ Y := (hY v (hXN (hVX hv))).mpr ⟨hVX hv, h1⟩
  have : v ∈ V ⊓ Y := ⟨hv, hvY⟩
  rwa [hVY, Subgroup.mem_bot] at this

theorem relIndex_sup_eq_two_three_of_cyclic {X Y V : Subgroup G} (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hYX : Y ≤ X) (hVX : V ≤ X)
    (hY : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (K : Set G)),
      x ∈ Y ↔ x ∈ X ∧ normalizerToAutSL3 e ⟨x, hx⟩ = 1)
    (hVY : V ⊓ Y = ⊥) (hV2 : IsPGroup 2 V) (hVc : IsCyclic V) (h4 : 4 ≤ Nat.card V) :
    (K ⊔ Y).relIndex X = 2 ∧ ¬ V ≤ K ⊔ Y ∧ K ⊔ Y ⊔ V = X :=
  relIndex_sup_eq_two_three e hKX hXN hYX hVX hY
    (not_map_le_inn3_of_inf_eq_bot e hXN hVX hY hVY hV2 hVc h4)

end Extras

end CFSG.ClassicalInvolution.Q3.Q3T6

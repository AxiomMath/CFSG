module

public import CFSG.GroupTheory.PCore.Defs
import CFSG.GroupTheory.CyclicSylowNormalOddComplement
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup

section OddCoreFree

variable {Q : Type*} [Group Q] [Finite Q]

theorem card_le_two_of_normal_of_oddCore_eq_bot (hO : oddCore Q = ⊥) {C : Subgroup Q}
    (hC : C.Normal) (h2 : ∀ U : Subgroup Q, IsPGroup 2 U → U ≤ C → Nat.card U ≤ 2) :
    Nat.card C ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 C) := inferInstance
  have hScard : Nat.card S ≤ 2 := by
    rw [← card_map_of_injective C.subtype_injective]
    exact h2 _ (S.isPGroup'.map _) (map_subtype_le _)
  have hScyc : IsCyclic (S : Subgroup C) := by
    refine isCyclic_of_card_dvd_prime (p := 2) ?_
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    rw [hk] at hScard ⊢
    rcases k with _ | _ | k
    · exact one_dvd _
    · exact dvd_refl _
    · exfalso
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [pow_succ, pow_succ] at hScard
      omega
  obtain ⟨-, -, -, ⟨-, hodd, hidx, -⟩, hchar⟩ := CFSG.cyclic_sylow_normal_odd_complement S hScyc
  have hKn : ((pPrimeCore 2 C).map C.subtype).Normal := by
    have := hC
    infer_instance
  have hKodd : Odd (Nat.card ((pPrimeCore 2 C).map C.subtype)) := by
    rwa [card_map_of_injective C.subtype_injective]
  have hKbot : (pPrimeCore 2 C).map C.subtype = ⊥ := by
    rw [eq_bot_iff, ← hO]
    exact le_sSup ⟨hKn, hKodd⟩
  have hK1 : Nat.card (pPrimeCore 2 C) = 1 := by
    rw [← card_map_of_injective C.subtype_injective, hKbot, card_bot]
  have hCS := (pPrimeCore 2 C).card_mul_index
  rw [hK1, hidx, one_mul] at hCS
  rw [← hCS]
  exact hScard

theorem le_center_of_normal_of_card_le_two {C : Subgroup Q} (hC : C.Normal)
    (h : Nat.card C ≤ 2) : C ≤ center Q := by
  intro c hc
  rw [mem_center_iff]
  intro q
  by_cases hc1 : c = 1
  · rw [hc1, mul_one, one_mul]
  have hcard : Nat.card C = 2 := by
    have h1 : 1 < Nat.card C := by
      rw [Finite.one_lt_card_iff_nontrivial]
      exact ⟨⟨⟨c, hc⟩, 1, fun h' => hc1 (congrArg Subtype.val h')⟩⟩
    omega
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : C)).1 hcard
  have hconj : q * c * q⁻¹ ∈ C := hC.conj_mem c hc q
  have e1 : (⟨c, hc⟩ : C) = y := huniq _ (fun h' => hc1 (congrArg Subtype.val h'))
  have e2 : (⟨q * c * q⁻¹, hconj⟩ : C) = y := huniq _ (by
    intro h'
    apply hc1
    have h'' : q * c * q⁻¹ = 1 := congrArg Subtype.val h'
    rw [mul_inv_eq_one] at h''
    simpa using h'')
  have e3 : q * c * q⁻¹ = c := congrArg Subtype.val (e2.trans e1.symm)
  rw [mul_inv_eq_iff_eq_mul] at e3
  exact e3

theorem centralizer_le_center_of_oddCore_eq_bot (hO : oddCore Q = ⊥) {E : Subgroup Q}
    (hE : E.Normal)
    (h2 : ∀ U : Subgroup Q, IsPGroup 2 U → U ≤ centralizer (E : Set Q) → Nat.card U ≤ 2) :
    centralizer (E : Set Q) ≤ center Q := by
  have hn : (centralizer (E : Set Q)).Normal := by
    have := hE
    infer_instance
  exact le_center_of_normal_of_card_le_two hn (card_le_two_of_normal_of_oddCore_eq_bot hO hn h2)

end OddCoreFree

section Quasisimple

private theorem isSimpleGroup_of_isQuasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) (hZ : center Q = ⊥) : IsSimpleGroup Q := by
  have := hQ.2
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

private theorem isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B :=
  hA.of_mulEquiv e.symm

end Quasisimple

section Quotient

variable {H : Type*} [Group H] [Finite H]

private theorem odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (oddCore X)) :=
  CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd

private theorem oddCore_quotient_eq_bot : oddCore (H ⧸ oddCore H) = ⊥ := by
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set N := (oddCore (H ⧸ oddCore H)).comap π with hN
  have hNn : N.Normal := (CFSG.oddCore_normal _).comap π
  have hidx : N.index = (oddCore (H ⧸ oddCore H)).index :=
    index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h1 := N.card_mul_index
  have h2 := (oddCore (H ⧸ oddCore H)).card_mul_index
  have h3 := card_eq_card_quotient_mul_card_subgroup (oddCore H)
  have hcard : Nat.card N = Nat.card (oddCore (H ⧸ oddCore H)) * Nat.card (oddCore H) := by
    have hidx0 : N.index ≠ 0 := index_ne_zero_of_finite
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hidx0)
    rw [h1, h3, ← h2, hidx]
    ring
  have hNodd : Odd (Nat.card N) := by
    rw [hcard]
    exact (odd_card_oddCore _).mul (odd_card_oddCore H)
  have hNle : N ≤ oddCore H := le_sSup ⟨hNn, hNodd⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (oddCore H) x
  rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hNle hx

omit [Finite H] in
private theorem mk_mem_centralizer_map_oddCore {t : H} {D : Subgroup H}
    (hDt : D ≤ centralizer ({t} : Set H)) :
    QuotientGroup.mk' (oddCore H) t ∈
      centralizer (D.map (QuotientGroup.mk' (oddCore H)) : Set (H ⧸ oddCore H)) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨d, hd, rfl⟩
  rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 (hDt hd)]

theorem mk_mem_center_of_normal_map_oddCore {t : H} {D : Subgroup H}
    (hDt : D ≤ centralizer ({t} : Set H))
    (hsyl : ∀ U : Subgroup (H ⧸ oddCore H), IsPGroup 2 U →
      U ≤ centralizer (D.map (QuotientGroup.mk' (oddCore H)) : Set (H ⧸ oddCore H)) →
      Nat.card U ≤ 2)
    (hnorm : (D.map (QuotientGroup.mk' (oddCore H))).Normal) :
    QuotientGroup.mk' (oddCore H) t ∈ center (H ⧸ oddCore H) :=
  centralizer_le_center_of_oddCore_eq_bot oddCore_quotient_eq_bot hnorm hsyl
    (mk_mem_centralizer_map_oddCore hDt)

theorem centralizer_map_oddCore_eq_zpowers {t : H} (ht : orderOf t = 2) {D : Subgroup H}
    (hDt : D ≤ centralizer ({t} : Set H))
    (hsyl : ∀ U : Subgroup (H ⧸ oddCore H), IsPGroup 2 U →
      U ≤ centralizer (D.map (QuotientGroup.mk' (oddCore H)) : Set (H ⧸ oddCore H)) →
      Nat.card U ≤ 2)
    (hnorm : (D.map (QuotientGroup.mk' (oddCore H))).Normal) :
    centralizer (D.map (QuotientGroup.mk' (oddCore H)) : Set (H ⧸ oddCore H)) =
      zpowers (QuotientGroup.mk' (oddCore H) t) := by
  have hn : (centralizer (D.map (QuotientGroup.mk' (oddCore H)) :
      Set (H ⧸ oddCore H))).Normal := by
    have := hnorm
    infer_instance
  have hcard := card_le_two_of_normal_of_oddCore_eq_bot oddCore_quotient_eq_bot hn hsyl
  have hord : orderOf (QuotientGroup.mk' (oddCore H) t) = 2 := by
    refine orderOf_eq_prime (by rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]) ?_
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 := (oddCore H).orderOf_dvd_natCard h1
    rw [ht] at h2
    exact (Nat.not_even_iff_odd.2 (odd_card_oddCore H)) (even_iff_two_dvd.2 h2)
  symm
  refine eq_of_le_of_card_ge (zpowers_le.2 (mk_mem_centralizer_map_oddCore hDt)) ?_
  rw [Nat.card_zpowers, hord]
  exact hcard

theorem mk_apply_mem_center_of_mk_mem_center (h : MulAut H) {t : H}
    (ht : QuotientGroup.mk' (oddCore H) t ∈ center (H ⧸ oddCore H)) :
    QuotientGroup.mk' (oddCore H) (h t) ∈ center (H ⧸ oddCore H) := by
  have hOh : ∀ z ∈ oddCore H, h z ∈ oddCore H := by
    intro z hz
    have hn : ((oddCore H).map h.toMonoidHom).Normal :=
      (CFSG.oddCore_normal H).map h.toMonoidHom h.surjective
    have hodd : Odd (Nat.card ((oddCore H).map h.toMonoidHom)) := by
      rw [card_map_of_injective h.injective]
      exact odd_card_oddCore H
    have hle : (oddCore H).map h.toMonoidHom ≤ oddCore H := le_sSup ⟨hn, hodd⟩
    exact hle ⟨z, hz, rfl⟩
  rw [mem_center_iff]
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (oddCore H) q
  obtain ⟨x', rfl⟩ := h.surjective x
  have hc := mem_center_iff.1 ht (QuotientGroup.mk' (oddCore H) x')
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at hc
  rw [← map_mul (QuotientGroup.mk' (oddCore H)), ← map_mul (QuotientGroup.mk' (oddCore H)),
    QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have e : h ((x' * t)⁻¹ * (t * x')) = (h x' * h t)⁻¹ * (h t * h x') := by
    rw [map_mul, map_inv, map_mul, map_mul]
  rw [← e]
  exact hOh _ hc

theorem mk_not_mem_center_of_mem {D : Subgroup H} (hDq : CFSG.Open.IsQuasisimple D)
    (hZD : center D = ⊥) {y : H} (hyD : y ∈ D) (hy : orderOf y = 2) :
    QuotientGroup.mk' (oddCore H) y ∉ center (H ⧸ oddCore H) := by
  intro hyc
  have hsimple : IsSimpleGroup D := isSimpleGroup_of_isQuasisimple hDq hZD
  have hN : (oddCore H).subgroupOf D = ⊥ := by
    have hn : ((oddCore H).subgroupOf D).Normal := (CFSG.oddCore_normal H).subgroupOf D
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((oddCore H).subgroupOf D) with h | h
    · exact h
    · exfalso
      have hyO : y ∈ oddCore H := by
        have : (⟨y, hyD⟩ : D) ∈ (oddCore H).subgroupOf D := h ▸ mem_top _
        exact mem_subgroupOf.1 this
      have h2 := (oddCore H).orderOf_dvd_natCard hyO
      rw [hy] at h2
      exact (Nat.not_even_iff_odd.2 (odd_card_oddCore H)) (even_iff_two_dvd.2 h2)
  have hyZ : (⟨y, hyD⟩ : D) ∈ center D := by
    rw [mem_center_iff]
    intro d
    have hc := mem_center_iff.1 hyc (QuotientGroup.mk' (oddCore H) d)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at hc
    have hmem : (⟨((d : H) * y)⁻¹ * (y * d), D.mul_mem (D.inv_mem (D.mul_mem d.2 hyD))
        (D.mul_mem hyD d.2)⟩ : D) ∈ (oddCore H).subgroupOf D := mem_subgroupOf.2 hc
    rw [hN, mem_bot] at hmem
    have h1 : ((d : H) * y)⁻¹ * (y * d) = 1 := congrArg Subtype.val hmem
    apply Subtype.ext
    exact inv_mul_eq_one.1 h1
  rw [hZD, mem_bot] at hyZ
  have hy1 : y = 1 := congrArg Subtype.val hyZ
  rw [hy1, orderOf_one] at hy
  exact absurd hy (by decide)

theorem false_of_normal_of_conj {t : H} {D : Subgroup H} (hDq : CFSG.Open.IsQuasisimple D)
    (hZD : center D = ⊥)
    (hsyl : ∀ U : Subgroup (H ⧸ oddCore H), IsPGroup 2 U →
      U ≤ centralizer (D.map (QuotientGroup.mk' (oddCore H)) : Set (H ⧸ oddCore H)) →
      Nat.card U ≤ 2)
    (hDt : D ≤ centralizer ({t} : Set H))
    (hnorm : (D.map (QuotientGroup.mk' (oddCore H))).Normal)
    (h : MulAut H) {y : H} (hyD : y ∈ D) (hy : orderOf y = 2)
    (hty : h t = t * y ∨ h t = y) : False := by
  have ht := mk_mem_center_of_normal_map_oddCore hDt hsyl hnorm
  have hht := mk_apply_mem_center_of_mk_mem_center h ht
  apply mk_not_mem_center_of_mem hDq hZD hyD hy
  rcases hty with e | e
  · rw [e, map_mul] at hht
    simpa using (center _).mul_mem ((center _).inv_mem ht) hht
  · rwa [e] at hht

theorem not_normal_map_oddCore_of_conj {t : H} {D : Subgroup H}
    (hDq : CFSG.Open.IsQuasisimple D) (hZD : center D = ⊥)
    (hsyl : ∀ U : Subgroup (H ⧸ oddCore H), IsPGroup 2 U →
      U ≤ centralizer (D.map (QuotientGroup.mk' (oddCore H)) : Set (H ⧸ oddCore H)) →
      Nat.card U ≤ 2)
    (hDt : D ≤ centralizer ({t} : Set H)) (h : MulAut H) {y : H} (hyD : y ∈ D)
    (hy : orderOf y = 2) (hty : h t = t * y ∨ h t = y) :
    ¬ (D.map (QuotientGroup.mk' (oddCore H))).Normal :=
  fun hnorm => false_of_normal_of_conj hDq hZD hsyl hDt hnorm h hyD hy hty

end Quotient

section Neighbour

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem mem_normalizer_centralizer_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) : g ∈ normalizer (centralizer (X : Set G) : Set G) := by
  have hX : ∀ x, x ∈ X ↔ g * x * g⁻¹ ∈ X := mem_normalizer_iff.1 hg
  rw [mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : g⁻¹ * x * g ∈ X := by
      rw [hX]
      have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [e]
      exact hx
    have hcx := mem_centralizer_iff.1 hc _ hx'
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [hcx]
      _ = g * c * g⁻¹ * x := by group
  · intro hc
    rw [mem_centralizer_iff]
    intro x hx
    have hcx := mem_centralizer_iff.1 hc _ ((hX x).1 hx)
    calc x * c = g⁻¹ * ((g * x * g⁻¹) * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * (g * x * g⁻¹)) * g := by rw [hcx]
      _ = c * x := by group

theorem not_normal_map_oddCore_of_mem_normalizer {H : Subgroup G} {t : G} (htH : t ∈ H)
    {D : Subgroup G} (hDH : D ≤ H) (hDq : CFSG.Open.IsQuasisimple D) (hZD : center D = ⊥)
    (hDt : D ≤ centralizer ({t} : Set G))
    (hsyl : ∀ U : Subgroup (H ⧸ oddCore H), IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) :
        Set (H ⧸ oddCore H)) → Nat.card U ≤ 2)
    {g : G} (hg : g ∈ normalizer (H : Set G)) {y : G} (hyD : y ∈ D) (hy : orderOf y = 2)
    (hty : g⁻¹ * t * g = t * y ∨ g⁻¹ * t * g = y) :
    ¬ ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H))).Normal := by
  set e : D ≃* D.subgroupOf H := (subgroupOfEquivOfLe hDH).symm with he
  have hDq' : CFSG.Open.IsQuasisimple (D.subgroupOf H) := isQuasisimple_of_mulEquiv e hDq
  have hZD' : center (D.subgroupOf H) = ⊥ := by
    rw [← map_center_eq e, hZD, Subgroup.map_bot]
  have hDt' : D.subgroupOf H ≤ centralizer ({⟨t, htH⟩} : Set H) := fun d hd =>
    mem_centralizer_singleton_iff.2 (Subtype.ext
      (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd))))
  set φ : MulAut H := H.normalizerMonoidHom ⟨g⁻¹, inv_mem hg⟩ with hφdef
  have hφ : ∀ x : H, ((φ x : H) : G) = g⁻¹ * x * g := by
    intro x
    simp [hφdef, normalizerMonoidHom_apply_apply_coe]
  refine not_normal_map_oddCore_of_conj hDq' hZD' hsyl hDt' φ (y := ⟨y, hDH hyD⟩)
    (mem_subgroupOf.2 hyD) (by rw [orderOf_mk, hy]) ?_
  rcases hty with h1 | h1
  · exact Or.inl (Subtype.ext (by rw [hφ]; exact h1))
  · exact Or.inr (Subtype.ext (by rw [hφ]; exact h1))

theorem not_normal_map_oddCore_centralizer {X : Subgroup G} {t : G}
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDX : D ≤ centralizer (X : Set G))
    (hDq : CFSG.Open.IsQuasisimple D) (hZD : center D = ⊥) (hDt : D ≤ centralizer ({t} : Set G))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    {g : G} (hg : g ∈ normalizer (X : Set G)) {y : G} (hyD : y ∈ D) (hy : orderOf y = 2)
    (hty : g⁻¹ * t * g = t * y ∨ g⁻¹ * t * g = y) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal :=
  not_normal_map_oddCore_of_mem_normalizer htX hDX hDq hZD hDt hsyl
    (mem_normalizer_centralizer_of_mem_normalizer hg) hyD hy hty

end Neighbour

end CFSG.SeitzReduction.F4Pilot

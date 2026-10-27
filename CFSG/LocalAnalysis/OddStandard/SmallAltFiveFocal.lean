module

public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveSector
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveRho
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveAlt5
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveGeneral
public import CFSG.Mathlib.GroupTheory.Focal

public section

namespace CFSG.OddStandard

open Subgroup Equiv CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G]

theorem exists_klein_sylow {L : Subgroup G} (e : L ≃* alternatingGroup (Fin 5)) :
    ∃ P₀ : Subgroup G, P₀ ≤ L ∧ Nat.card P₀ = 4 ∧ ∀ p ∈ P₀, p * p = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite L := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨P⟩ : Nonempty (Sylow 2 L) := inferInstance
  have hcard : Nat.card (P : Subgroup L) = 4 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv, card_alternatingGroup_five]
    decide +kernel
  refine ⟨(P : Subgroup L).map L.subtype, map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hcard]
  · rintro _ ⟨x, hx, rfl⟩
    have h1 : orderOf x ∣ 4 := hcard ▸ Subgroup.orderOf_dvd_natCard _ hx
    have h2 : orderOf x ≠ 4 := fun h => orderOf_ne_four_alternatingGroup_five (e x) (by
      rw [MulEquiv.orderOf_eq, h])
    have h3 : orderOf x ∣ 2 := by
      have h4 : orderOf x ∣ 2 ^ 2 := by simpa using h1
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
      interval_cases k
      · simp [hk']
      · simp [hk']
      · exact absurd (by simpa using hk') h2
    have h5 : x * x = 1 := by
      rw [← sq]
      exact orderOf_dvd_iff_pow_eq_one.mp h3
    exact congrArg Subtype.val h5

@[expose] noncomputable def rhoH (L : Subgroup G) (t : G)
    (hHM : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (e : L ≃* alternatingGroup (Fin 5)) : centralizer ({t} : Set G) →* Perm (Fin 5) :=
  (rhoOf e).comp (Subgroup.inclusion hHM)

theorem ker_rhoH (L : Subgroup G) (t : G) (hHM : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (e : L ≃* alternatingGroup (Fin 5)) :
    (rhoH L t hHM e).ker = (centralizer (L : Set G)).subgroupOf (centralizer ({t} : Set G)) := by
  ext h
  have := rhoOf_ker e
  rw [MonoidHom.mem_ker, rhoH, MonoidHom.comp_apply, ← MonoidHom.mem_ker, this, mem_subgroupOf]
  rfl

structure AltCase (L : Subgroup G) (S : Sylow 2 (centralizer (L : Set G))) (t : G)
    (e : L ≃* alternatingGroup (Fin 5)) : Prop where
  sector : Sector L S t
  perfect : commutator G = ⊤
  trivial_inter : L ⊓ centralizer (L : Set G) = ⊥
  four_le : 4 ≤ Nat.card (sg L S)
  even : ∀ h : normalizer (L : Set G), (h : G) ∈ centralizer ({t} : Set G) →
    rhoOf e h ∈ alternatingGroup (Fin 5)

section AltCase

variable [Finite G] {L : Subgroup G} {S : Sylow 2 (centralizer (L : Set G))} {t : G}
  {e : L ≃* alternatingGroup (Fin 5)}

theorem AltCase.H_le_M (hc : AltCase L S t e) :
    centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
  (centralizer_t_facts hc.sector).1

theorem AltCase.L_le_H (hc : AltCase L S t e) : L ≤ centralizer ({t} : Set G) :=
  (centralizer_t_facts hc.sector).2.1

theorem AltCase.exists_mul (hc : AltCase L S t e) {h : G} (hh : h ∈ centralizer ({t} : Set G)) :
    ∃ l ∈ L, ∃ r ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G), h = l * r := by
  have hM : h ∈ normalizer (L : Set G) := hc.H_le_M hh
  obtain ⟨l, hl⟩ := e.surjective ⟨rhoOf e ⟨h, hM⟩, hc.even ⟨h, hM⟩ hh⟩
  have h1 : rhoOf e ⟨(l : G), Subgroup.le_normalizer l.2⟩ = rhoOf e ⟨h, hM⟩ := by
    rw [rhoOf_apply_of_mem e l.2]
    exact congrArg Subtype.val hl
  have h2 : (⟨(l : G), Subgroup.le_normalizer l.2⟩ : normalizer (L : Set G))⁻¹ * ⟨h, hM⟩ ∈
      (rhoOf e).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  rw [rhoOf_ker, mem_subgroupOf] at h2
  have h3 : (l : G)⁻¹ * h ∈ centralizer (L : Set G) := h2
  refine ⟨l, l.2, (l : G)⁻¹ * h, ⟨h3, ?_⟩, by group⟩
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hc.L_le_H l.2)) hh

theorem AltCase.card_H (hc : AltCase L S t e) :
    Nat.card (centralizer ({t} : Set G)) =
      60 * Nat.card (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  have hrange : (rhoH L t hc.H_le_M e).range = alternatingGroup (Fin 5) := by
    apply le_antisymm
    · rintro _ ⟨h, rfl⟩
      exact hc.even ⟨h, hc.H_le_M h.2⟩ h.2
    · intro g hg
      obtain ⟨l, hl⟩ := e.surjective ⟨g, hg⟩
      refine ⟨⟨l, hc.L_le_H l.2⟩, ?_⟩
      show rhoOf e ⟨(l : G), Subgroup.le_normalizer l.2⟩ = g
      rw [rhoOf_apply_of_mem e l.2]
      exact congrArg Subtype.val hl
  have hker := ker_rhoH L t hc.H_le_M e
  have h1 := card_eq_card_range_mul_card_ker (rhoH L t hc.H_le_M e)
  rw [hrange, hker, card_alternatingGroup_five] at h1
  rw [h1]
  congr 1
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) ≤ centralizer ({t} : Set G))).toEquiv]
  congr 2
  ext x
  simp [mem_subgroupOf]

theorem AltCase.false (hc : AltCase L S t e) : False := by
  classical
  have hs := hc.sector
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀L, hP₀card, hP₀sq⟩ := exists_klein_sylow e
  have hPC : ∀ p ∈ P₀, ∀ u ∈ sg L S, p * u = u * p := fun p hp u hu =>
    mem_centralizer_iff.mp (sg_le_centralizer hu) p (hP₀L hp)
  have hPsg : P₀ ⊓ sg L S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ L ⊓ centralizer (L : Set G) := ⟨hP₀L hx.1, sg_le_centralizer hx.2⟩
    rw [hc.trivial_inter, mem_bot] at h1
    exact mem_bot.mpr h1
  have hPcomm : ∀ p ∈ P₀, ∀ q ∈ P₀, p * q = q * p := fun p hp q hq =>
    comm_of_mul_self_eq_one (hP₀sq p hp) (hP₀sq q hq) (hP₀sq _ (Subgroup.mul_mem _ hp hq))
  have hPnS : P₀ ≤ normalizer ((sg L S : Subgroup G) : Set G) := fun p hp =>
    centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun u hu => (hPC p hp u hu).symm)
  have hTmem : ∀ x : G, x ∈ P₀ ⊔ sg L S ↔ ∃ p ∈ P₀, ∃ u ∈ sg L S, x = p * u := fun x => by
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right P₀ (sg L S) hPnS,
      Set.mem_mul]
    constructor
    · rintro ⟨p, hp, u, hu, rfl⟩
      exact ⟨p, hp, u, hu, rfl⟩
    · rintro ⟨p, hp, u, hu, rfl⟩
      exact ⟨p, hp, u, hu, rfl⟩
  have hTcomm : ∀ x ∈ P₀ ⊔ sg L S, ∀ y ∈ P₀ ⊔ sg L S, x * y = y * x := by
    intro x hx y hy
    obtain ⟨p, hp, u, hu, rfl⟩ := (hTmem x).1 hx
    obtain ⟨p', hp', u', hu', rfl⟩ := (hTmem y).1 hy
    calc p * u * (p' * u') = p * (u * p') * u' := by group
      _ = p * (p' * u) * u' := by rw [← hPC p' hp' u hu]
      _ = (p * p') * (u * u') := by group
      _ = (p' * p) * (u' * u) := by rw [hPcomm p hp p' hp', sg_comm hs u hu u' hu']
      _ = p' * (p * u') * u := by group
      _ = p' * (u' * p) * u := by rw [hPC p hp u' hu']
      _ = p' * u' * (p * u) := by group
  obtain ⟨a, ha⟩ := (isPGroup_sg (L := L) (S := S)).exists_card_eq
  have hcardT : Nat.card (P₀ ⊔ sg L S : Subgroup G) = 4 * 2 ^ a := by
    rw [card_sup_of_commute hPC hPsg, hP₀card, ha]
  have hSR : sg L S ≤ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) :=
    le_inf sg_le_centralizer (sg_le_centralizer_t hs)
  have hsgR : Nat.card (sg L S) = 2 ^ (Nat.card
      (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G)).factorization 2 :=
    card_eq_of_maximal hSR isPGroup_sg fun Q' hQ' hQ'2 hle =>
      sg_maximal (hQ'.trans inf_le_left) hQ'2 hle
  have hcardH := hc.card_H
  have hRpos : Nat.card (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ≠ 0 :=
    Nat.card_pos.ne'
  have hfacH : (Nat.card (centralizer ({t} : Set G))).factorization 2 =
      2 + (Nat.card (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) :
        Subgroup G)).factorization 2 := by
    rw [hcardH, Nat.factorization_mul (by norm_num) hRpos, Finsupp.add_apply]
    congr 1
    decide +kernel
  have hTsyl : Nat.card (P₀ ⊔ sg L S : Subgroup G) =
      2 ^ (Nat.card (centralizer ({t} : Set G))).factorization 2 := by
    rw [hcardT, hfacH, pow_add, ← hsgR, ha]
    norm_num
  have hTH : P₀ ⊔ sg L S ≤ centralizer ({t} : Set G) :=
    sup_le (fun p hp => hc.L_le_H (hP₀L hp)) (sg_le_centralizer_t hs)
  have htt : t * t = 1 := by
    rw [← sq, ← hs.t_order, pow_orderOf_eq_one]
  have hNt : ∀ n ∈ normalizer ((P₀ ⊔ sg L S : Subgroup G) : Set G), n * t * n⁻¹ = t := by
    intro n hn
    obtain ⟨w, hw, hwt⟩ := exists_sq_eq_t hs hc.four_le
    have hnw : n * w * n⁻¹ ∈ P₀ ⊔ sg L S :=
      (mem_normalizer_iff.mp hn w).mp (mem_sup_right hw)
    obtain ⟨p', hp', u', hu', hv⟩ := (hTmem _).1 hnw
    have hsq : n * t * n⁻¹ = u' * u' := by
      have h1 : n * t * n⁻¹ = (n * w * n⁻¹) * (n * w * n⁻¹) := by rw [← hwt]; group
      rw [h1, hv]
      calc p' * u' * (p' * u') = p' * (u' * p') * u' := by group
        _ = p' * (p' * u') * u' := by rw [← hPC p' hp' u' hu']
        _ = (p' * p') * (u' * u') := by group
        _ = u' * u' := by rw [hP₀sq p' hp', one_mul]
    have hmem : n * t * n⁻¹ ∈ sg L S := hsq ▸ Subgroup.mul_mem _ hu' hu'
    have hne : n * t * n⁻¹ ≠ 1 := by
      intro h
      have : t = 1 := by
        have := congrArg (fun y => n⁻¹ * y * n) h
        simpa [mul_assoc] using this
      have h2 := hs.t_order
      rw [this, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    have hord : orderOf (n * t * n⁻¹) = 2 := by
      refine orderOf_eq_prime ?_ hne
      rw [conj_pow, sq, ← sq, ← hs.t_order, pow_orderOf_eq_one]
      group
    exact eq_t_of_orderOf_eq_two hs hmem hord
  have hNle : normalizer ((P₀ ⊔ sg L S : Subgroup G) : Set G) ≤ centralizer ({t} : Set G) :=
    fun n hn => mem_centralizer_singleton_iff.mpr (by
      have h := hNt n hn
      calc n * t = (n * t * n⁻¹) * n := by group
        _ = t * n := by rw [h])
  have hTG : Nat.card (P₀ ⊔ sg L S : Subgroup G) = 2 ^ (Nat.card G).factorization 2 :=
    card_eq_of_normalizer_le hTH hTsyl hNle
  let Tsyl : Sylow 2 G := Sylow.ofCard (P₀ ⊔ sg L S) hTG
  have hTsylcoe : (Tsyl : Subgroup G) = P₀ ⊔ sg L S := rfl
  have hfus : ∀ x ∈ P₀ ⊔ sg L S, ∀ y ∈ P₀ ⊔ sg L S, ∀ g : G, g⁻¹ * x * g = y →
      ∃ n ∈ normalizer ((P₀ ⊔ sg L S : Subgroup G) : Set G), n⁻¹ * x * n = y := by
    intro x hx y hy g hg
    have hx' : ∀ u ∈ (Tsyl : Subgroup G), u * x = x * u := fun u hu => hTcomm u hu x hx
    have hy' : ∀ u ∈ (Tsyl : Subgroup G), u * y = y * u := fun u hu => hTcomm u hu y hy
    obtain ⟨n, hn, hnxy⟩ := exists_mem_normalizer_conj Tsyl hx' hy' hg
    exact ⟨n, hn, hnxy⟩
  have hgen : ∀ n ∈ normalizer ((P₀ ⊔ sg L S : Subgroup G) : Set G),
      ∀ x ∈ P₀ ⊔ sg L S, x⁻¹ * (n⁻¹ * x * n) ∈ P₀ := by
    intro n hn x hx
    have hconjT : ∀ y ∈ P₀ ⊔ sg L S, n⁻¹ * y * n ∈ P₀ ⊔ sg L S := fun y hy => by
      have := (mem_normalizer_iff.mp (inv_mem hn) y).mp hy
      rwa [inv_inv] at this
    have hnH : n ∈ centralizer ({t} : Set G) := hNle hn
    obtain ⟨l, hl, r, hr, rfl⟩ := hc.exists_mul hnH
    obtain ⟨p, hp, u, hu, rfl⟩ := (hTmem x).1 hx
    have hrC : r ∈ centralizer (L : Set G) := hr.1
    have hlu : ∀ u ∈ sg L S, l * u = u * l := fun u hu =>
      mem_centralizer_iff.mp (sg_le_centralizer hu) l hl
    have hrL : ∀ y ∈ L, y * r = r * y := fun y hy => mem_centralizer_iff.mp hrC y hy
    have hm : l⁻¹ * p * l ∈ L :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hl) (hP₀L hp)) hl
    have h1 : (l * r)⁻¹ * p * (l * r) = l⁻¹ * p * l := by
      have := hrL _ hm
      calc (l * r)⁻¹ * p * (l * r) = r⁻¹ * ((l⁻¹ * p * l) * r) := by group
        _ = r⁻¹ * (r * (l⁻¹ * p * l)) := by rw [this]
        _ = l⁻¹ * p * l := by group
    have h2 : ∀ u ∈ sg L S, (l * r)⁻¹ * u * (l * r) = r⁻¹ * u * r := fun u hu => by
      have h := hlu u hu
      have h' : l⁻¹ * u * l = u := by
        calc l⁻¹ * u * l = l⁻¹ * (u * l) := by group
          _ = l⁻¹ * (l * u) := by rw [h]
          _ = u := by group
      calc (l * r)⁻¹ * u * (l * r) = r⁻¹ * (l⁻¹ * u * l) * r := by group
        _ = r⁻¹ * u * r := by rw [h']
    have h3 : ∀ u ∈ sg L S, r⁻¹ * u * r ∈ sg L S := by
      intro u hu
      have hT' : r⁻¹ * u * r ∈ P₀ ⊔ sg L S := by
        rw [← h2 u hu]
        exact hconjT u (mem_sup_right hu)
      obtain ⟨p', hp', u', hu', hv⟩ := (hTmem _).1 hT'
      have hvC : r⁻¹ * u * r ∈ centralizer (L : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hrC) (sg_le_centralizer hu)) hrC
      have hp'C : p' ∈ centralizer (L : Set G) := by
        have : p' = (r⁻¹ * u * r) * u'⁻¹ := by rw [hv]; group
        rw [this]
        exact Subgroup.mul_mem _ hvC (Subgroup.inv_mem _ (sg_le_centralizer hu'))
      have h5 : p' ∈ L ⊓ centralizer (L : Set G) := ⟨hP₀L hp', hp'C⟩
      rw [hc.trivial_inter, mem_bot] at h5
      rw [hv, h5, one_mul]
      exact hu'
    have h4 : ∀ u ∈ sg L S, r⁻¹ * u * r = u := fun u hu => by
      have := commute_of_mem_centralizer_of_normalizes hs (Subgroup.inv_mem _ hrC)
        (fun u hu => by simpa using h3 u hu) u hu
      calc r⁻¹ * u * r = (r⁻¹ * u) * r := rfl
        _ = (u * r⁻¹) * r := by rw [this]
        _ = u := by group
    have h5 : l⁻¹ * p * l ∈ P₀ := by
      have hT' : l⁻¹ * p * l ∈ P₀ ⊔ sg L S := by
        rw [← h1]
        exact hconjT p (mem_sup_left hp)
      obtain ⟨p', hp', u', hu', hv⟩ := (hTmem _).1 hT'
      have hu'L : u' ∈ L := by
        have : u' = p'⁻¹ * (l⁻¹ * p * l) := by rw [hv]; group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hP₀L hp')) hm
      have h6 : u' ∈ L ⊓ centralizer (L : Set G) := ⟨hu'L, sg_le_centralizer hu'⟩
      rw [hc.trivial_inter, mem_bot] at h6
      rw [hv, h6, mul_one]
      exact hp'
    have hc2 : (p⁻¹ * (l⁻¹ * p * l)) * u = u * (p⁻¹ * (l⁻¹ * p * l)) :=
      mem_centralizer_iff.mp (sg_le_centralizer hu) _
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hP₀L hp)) hm)
    have hEq : (p * u)⁻¹ * ((l * r)⁻¹ * (p * u) * (l * r)) = p⁻¹ * (l⁻¹ * p * l) := by
      calc (p * u)⁻¹ * ((l * r)⁻¹ * (p * u) * (l * r))
          = (p * u)⁻¹ * (((l * r)⁻¹ * p * (l * r)) * ((l * r)⁻¹ * u * (l * r))) := by group
        _ = (p * u)⁻¹ * ((l⁻¹ * p * l) * u) := by rw [h1, h2 u hu, h4 u hu]
        _ = u⁻¹ * ((p⁻¹ * (l⁻¹ * p * l)) * u) := by group
        _ = u⁻¹ * (u * (p⁻¹ * (l⁻¹ * p * l))) := by rw [hc2]
        _ = p⁻¹ * (l⁻¹ * p * l) := by group
    rw [hEq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hp) h5
  have hfoc : (P₀ ⊔ sg L S).focalSubgroup ≤ P₀ := by
    rw [Subgroup.focalSubgroup_eq_closure_isConj, closure_le]
    rintro z ⟨x, hx, y, hy, hxy, rfl⟩
    obtain ⟨c, hcxy⟩ := isConj_iff.mp hxy
    obtain ⟨n, hn, hnxy⟩ := hfus x hx y hy c⁻¹ (by simpa using hcxy)
    rw [← hnxy]
    exact hgen n hn x hx
  have hperf : (P₀ ⊔ sg L S).focalSubgroup = P₀ ⊔ sg L S := by
    have h1 := Subgroup.commutator_inf_eq_focalSubgroup Tsyl
    rw [hTsylcoe, hc.perfect, top_inf_eq] at h1
    exact h1.symm
  have hTP : P₀ ⊔ sg L S ≤ P₀ := hperf ▸ hfoc
  have htT : t ∈ P₀ ⊔ sg L S := mem_sup_right (t_mem_sg hs)
  have h6 : t ∈ L ⊓ centralizer (L : Set G) := ⟨hP₀L (hTP htT), t_mem_centralizer hs⟩
  rw [hc.trivial_inter, mem_bot] at h6
  have h2 := hs.t_order
  rw [h6, orderOf_one] at h2
  exact absurd h2 (by norm_num)


end AltCase

end CFSG.OddStandard

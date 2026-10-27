module

public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveEndCentral
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveEndFour
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveEndConfig

public section

namespace CFSG.OddStandard

open Equiv Equiv.Perm Subgroup CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G] {L : Subgroup G}

@[expose] def altIncl (e : L ≃* alternatingGroup (Fin 5)) : alternatingGroup (Fin 5) →* G :=
  L.subtype.comp e.symm.toMonoidHom

theorem altIncl_injective (e : L ≃* alternatingGroup (Fin 5)) : Function.Injective (altIncl e) :=
  L.subtype_injective.comp e.symm.injective

theorem altIncl_mem (e : L ≃* alternatingGroup (Fin 5)) (w : alternatingGroup (Fin 5)) :
    altIncl e w ∈ L := (e.symm w).2

theorem rhoOf_altIncl (e : L ≃* alternatingGroup (Fin 5)) (w : alternatingGroup (Fin 5)) :
    rhoOf e ⟨altIncl e w, le_normalizer (altIncl_mem e w)⟩ = (w : Perm (Fin 5)) := by
  rw [rhoOf_apply_of_mem e (altIncl_mem e w)]
  have h : (⟨altIncl e w, altIncl_mem e w⟩ : L) = e.symm w := rfl
  rw [h, MulEquiv.apply_symm_apply]

@[expose] def kleinIn (e : L ≃* alternatingGroup (Fin 5)) : Subgroup G :=
  (kleinFive.subgroupOf (alternatingGroup (Fin 5))).map (altIncl e)

theorem mem_kleinIn_iff (e : L ≃* alternatingGroup (Fin 5)) {g : G} :
    g ∈ kleinIn e ↔
      ∃ w : alternatingGroup (Fin 5), (w : Perm (Fin 5)) ∈ kleinFive ∧ altIncl e w = g := by
  simp only [kleinIn, Subgroup.mem_map, mem_subgroupOf]

theorem kleinIn_le (e : L ≃* alternatingGroup (Fin 5)) : kleinIn e ≤ L := by
  rintro _ ⟨w, -, rfl⟩
  exact altIncl_mem e w

theorem card_kleinIn (e : L ≃* alternatingGroup (Fin 5)) : Nat.card (kleinIn e) = 4 := by
  rw [kleinIn, Subgroup.card_map_of_injective (altIncl_injective e),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe kleinFive_le_alternatingGroup).toEquiv,
    card_kleinFive]

theorem mul_self_of_mem_kleinIn (e : L ≃* alternatingGroup (Fin 5)) {v : G}
    (hv : v ∈ kleinIn e) : v * v = 1 := by
  obtain ⟨w, hw, rfl⟩ := (mem_kleinIn_iff e).1 hv
  have h : w * w = 1 := Subtype.ext (mul_self_eq_one_of_mem_kleinFive hw)
  rw [← map_mul, h, map_one]

theorem mul_comm_of_mem_kleinIn (e : L ≃* alternatingGroup (Fin 5)) {v v' : G}
    (hv : v ∈ kleinIn e) (hv' : v' ∈ kleinIn e) : v * v' = v' * v := by
  obtain ⟨w, hw, rfl⟩ := (mem_kleinIn_iff e).1 hv
  obtain ⟨w', hw', rfl⟩ := (mem_kleinIn_iff e).1 hv'
  have h : w * w' = w' * w := Subtype.ext (mul_comm_of_mem_kleinFive hw hw')
  rw [← map_mul, ← map_mul, h]

section Core

variable {S : Sylow 2 (centralizer (L : Set G))} {t : G}

theorem kleinIn_comm_zpowers (hs : Sector L S t) (e : L ≃* alternatingGroup (Fin 5)) :
    ∀ v ∈ kleinIn e, ∀ s ∈ zpowers t, v * s = s * v := by
  intro v hv s hs'
  have hvt : Commute v t := mem_centralizer_iff.1 (t_mem_centralizer hs) v (kleinIn_le e hv)
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hs'
  exact (hvt.zpow_right k).eq

theorem kleinIn_inf_zpowers (hs : Sector L S t) (hZ : L ⊓ centralizer (L : Set G) = ⊥)
    (e : L ≃* alternatingGroup (Fin 5)) : kleinIn e ⊓ zpowers t = ⊥ := by
  rw [eq_bot_iff, ← hZ]
  exact inf_le_inf (kleinIn_le e) (zpowers_le.2 (t_mem_centralizer hs))

theorem card_kleinIn_sup (hs : Sector L S t) (hZ : L ⊓ centralizer (L : Set G) = ⊥)
    (e : L ≃* alternatingGroup (Fin 5)) : Nat.card (kleinIn e ⊔ zpowers t : Subgroup G) = 8 := by
  rw [card_sup_of_commute (kleinIn_comm_zpowers hs e) (kleinIn_inf_zpowers hs hZ e),
    card_kleinIn, Nat.card_zpowers, hs.t_order]

theorem mul_comm_kleinIn_sup (hs : Sector L S t) (e : L ≃* alternatingGroup (Fin 5)) :
    ∀ x ∈ kleinIn e ⊔ zpowers t, ∀ y ∈ kleinIn e ⊔ zpowers t, x * y = y * x := by
  have hcomm := kleinIn_comm_zpowers hs e
  intro x hx y hy
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := (mem_sup_iff_of_commute hcomm x).1 hx
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := (mem_sup_iff_of_commute hcomm y).1 hy
  have hbb : Commute b₁ b₂ := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb₁
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hb₂
    exact Commute.zpow_zpow_self t k m
  have hab₁ : Commute a₁ b₂ := hcomm a₁ ha₁ b₂ hb₂
  have hba₂ : Commute b₁ a₂ := (hcomm a₂ ha₂ b₁ hb₁).symm
  have haa : Commute a₁ a₂ := mul_comm_of_mem_kleinIn e ha₁ ha₂
  exact ((haa.mul_right hab₁).mul_left (hba₂.mul_right hbb)).eq

theorem mul_self_kleinIn_sup (hs : Sector L S t) (e : L ≃* alternatingGroup (Fin 5)) :
    ∀ x ∈ kleinIn e ⊔ zpowers t, x * x = 1 := by
  have hcomm := kleinIn_comm_zpowers hs e
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hcomm x).1 hx
  have htt : t * t = 1 := by rw [← sq, ← hs.t_order, pow_orderOf_eq_one]
  have hbb : b * b = 1 := by
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self htt hb with rfl | rfl
    · exact one_mul 1
    · exact htt
  have haa : a * a = 1 := mul_self_of_mem_kleinIn e ha
  have hba : Commute b a := (hcomm a ha b hb).symm
  calc a * b * (a * b) = (a * a) * (b * b) := hba.mul_mul_mul_comm a b
    _ = 1 := by rw [haa, hbb, one_mul]

theorem exists_mem_kleinIn_mul_inv_mem_centralizer [Finite G]
    {L : Subgroup G} {S : Sylow 2 (centralizer (L : Set G))} {t : G}
    (hs : Sector L S t) (e : L ≃* alternatingGroup (Fin 5)) {g : G}
    (hgH : g ∈ centralizer ({t} : Set G))
    (hgE : ∀ x ∈ (kleinIn e ⊔ zpowers t : Subgroup G), x * g = g * x) :
    ∃ v ∈ kleinIn e, g * v⁻¹ ∈ centralizer (L : Set G) := by
  classical
  obtain ⟨hHM, -, -, -⟩ := centralizer_t_facts hs
  let gM : normalizer (L : Set G) := ⟨g, hHM hgH⟩
  have hρ : ∀ w : alternatingGroup (Fin 5), (w : Perm (Fin 5)) ∈ kleinFive →
      rhoOf e gM * (w : Perm (Fin 5)) = (w : Perm (Fin 5)) * rhoOf e gM := by
    intro w hw
    have hv : altIncl e w ∈ kleinIn e := (mem_kleinIn_iff e).2 ⟨w, hw, rfl⟩
    have hvg : altIncl e w * g = g * altIncl e w := hgE _ (mem_sup_left hv)
    let vM : normalizer (L : Set G) := ⟨altIncl e w, le_normalizer (altIncl_mem e w)⟩
    have h1 : vM * gM = gM * vM := Subtype.ext hvg
    have h2 := congrArg (rhoOf e) h1
    rw [map_mul, map_mul, show rhoOf e vM = (w : Perm (Fin 5)) from rhoOf_altIncl e w] at h2
    exact h2.symm
  have hσ : rhoOf e gM ∈ kleinFive :=
    mem_kleinFive_of_commute
      (hρ ⟨pairA, kleinFive_le_alternatingGroup pairA_mem_kleinFive⟩ pairA_mem_kleinFive)
      (hρ ⟨pairB, kleinFive_le_alternatingGroup pairB_mem_kleinFive⟩ pairB_mem_kleinFive)
  obtain ⟨w₀, hw₀, hrho⟩ : ∃ w₀ : alternatingGroup (Fin 5),
      (w₀ : Perm (Fin 5)) ∈ kleinFive ∧ (w₀ : Perm (Fin 5)) = rhoOf e gM :=
    ⟨⟨rhoOf e gM, kleinFive_le_alternatingGroup hσ⟩, hσ, rfl⟩
  refine ⟨altIncl e w₀, (mem_kleinIn_iff e).2 ⟨w₀, hw₀, rfl⟩, ?_⟩
  let v₀M : normalizer (L : Set G) := ⟨altIncl e w₀, le_normalizer (altIncl_mem e w₀)⟩
  have hker : gM * v₀M⁻¹ ∈ (rhoOf e).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv,
      show rhoOf e v₀M = (w₀ : Perm (Fin 5)) from rhoOf_altIncl e w₀, hrho, mul_inv_cancel]
  rw [rhoOf_ker, mem_subgroupOf] at hker
  exact hker

theorem centralizer_kleinIn_sup [Finite G] (hs : Sector L S t) (hcard : Nat.card (sg L S) = 2)
    (hbal : CFSG.oddCore (centralizer ({t} : Set G)) = ⊥) (e : L ≃* alternatingGroup (Fin 5)) :
    centralizer ((kleinIn e ⊔ zpowers t : Subgroup G) : Set G) = kleinIn e ⊔ zpowers t := by
  apply le_antisymm
  · intro g hg
    have hgE : ∀ x ∈ kleinIn e ⊔ zpowers t, x * g = g * x := mem_centralizer_iff.1 hg
    have htg : t * g = g * t := hgE t (mem_sup_right (mem_zpowers t))
    have hgH : g ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 htg.symm
    obtain ⟨v, hv, hrC⟩ :=
      exists_mem_kleinIn_mul_inv_mem_centralizer hs e hgH hgE
    have hLH := (centralizer_t_facts hs).2.1
    have hrH : g * v⁻¹ ∈ centralizer ({t} : Set G) :=
      Subgroup.mul_mem _ hgH (Subgroup.inv_mem _ (hLH (kleinIn_le e hv)))
    rcases eq_one_or_eq_t_of_mem_centralizer hs hcard hbal hrC hrH with h1 | h1
    · have hg1 : g = v := by
        have := congrArg (· * v) h1
        simpa using this
      rw [hg1]
      exact mem_sup_left hv
    · have hg1 : g = t * v := by
        have := congrArg (· * v) h1
        simpa using this
      rw [hg1]
      exact Subgroup.mul_mem _ (mem_sup_right (mem_zpowers t)) (mem_sup_left hv)
  · intro x hx
    exact mem_centralizer_iff.2 fun y hy => mul_comm_kleinIn_sup hs e y hy x hx

theorem card_centralizer_t_eq [Finite G] (hs : Sector L S t) (hcard : Nat.card (sg L S) = 2)
    (hbal : CFSG.oddCore (centralizer ({t} : Set G)) = ⊥) (e : L ≃* alternatingGroup (Fin 5)) :
    Nat.card (centralizer ({t} : Set G)) = 120 ∨ Nat.card (centralizer ({t} : Set G)) = 240 := by
  obtain ⟨hHM, hLH, -, -⟩ := centralizer_t_facts hs
  set H := centralizer ({t} : Set G) with hH
  let ρH : H →* Perm (Fin 5) := (rhoOf e).comp (inclusion hHM)
  have hker : ρH.ker = (centralizer (L : Set G) ⊓ H).subgroupOf H :=
    ker_rhoOf_comp_inclusion e hHM
  have htH : t ∈ H := mem_centralizer_singleton_iff.2 rfl
  have hR : centralizer (L : Set G) ⊓ H = zpowers t := by
    refine le_antisymm (fun r hr => ?_) (le_inf (zpowers_le.2 (t_mem_centralizer hs))
      (zpowers_le.2 htH))
    rcases eq_one_or_eq_t_of_mem_centralizer hs hcard hbal hr.1 hr.2 with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  have hkercard : Nat.card ρH.ker = 2 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hR,
      Nat.card_zpowers, hs.t_order]
  have hrange : alternatingGroup (Fin 5) ≤ ρH.range := by
    intro σ hσ
    have hl : altIncl e ⟨σ, hσ⟩ ∈ H := hLH (altIncl_mem e ⟨σ, hσ⟩)
    refine ⟨⟨altIncl e ⟨σ, hσ⟩, hl⟩, ?_⟩
    exact rhoOf_altIncl e ⟨σ, hσ⟩
  have hidx : ρH.range.index ∣ 2 := by
    have := Subgroup.index_dvd_of_le hrange
    rwa [alternatingGroup.index_eq_two] at this
  have hmul := Subgroup.card_mul_index ρH.range
  have h120 : Nat.card (Perm (Fin 5)) = 120 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [h120] at hmul
  have hH' := card_eq_card_range_mul_card_ker ρH
  rw [hkercard] at hH'
  rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h1 | h1
  · rw [h1] at hmul
    right
    rw [hH']
    omega
  · rw [h1] at hmul
    left
    rw [hH']
    omega

theorem fiveConfig_of_balanced [Finite G] (hs : Sector L S t) (hcard : Nat.card (sg L S) = 2)
    (hbal : CFSG.oddCore (centralizer ({t} : Set G)) = ⊥) (e : L ≃* alternatingGroup (Fin 5)) :
    FiveConfig t := by
  obtain ⟨hHM, hLH, hLn, -⟩ := centralizer_t_facts hs
  refine ⟨hs.t_order, ⟨L, hLH, ?_, ⟨e⟩⟩, card_centralizer_t_eq hs hcard hbal e⟩
  intro c hc l hl
  have := hLn.conj_mem ⟨l, hLH hl⟩ (by rw [mem_subgroupOf]; exact hl) ⟨c, hc⟩
  simpa [mem_subgroupOf] using this

theorem exists_selfCentralizing_klein_sup [Finite G] (hs : Sector L S t)
    (hcard : Nat.card (sg L S) = 2) (hbal : CFSG.oddCore (centralizer ({t} : Set G)) = ⊥)
    (hZ : L ⊓ centralizer (L : Set G) = ⊥) (e : L ≃* alternatingGroup (Fin 5)) :
    ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ Open.IsElemAbelian 2 E ∧ Nat.card E = 8 ∧
      centralizer (E : Set G) = E := by
  have hc := mul_comm_kleinIn_sup hs e
  have hsq := mul_self_kleinIn_sup hs e
  refine ⟨kleinIn e ⊔ zpowers t, ?_, ?_, card_kleinIn_sup hs hZ e,
    centralizer_kleinIn_sup hs hcard hbal e⟩
  · exact
      { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (hc x x.2 y y.2)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
          Subtype.ext (by simpa [pow_two] using hsq x x.2) }
  · exact ⟨⟨⟨fun x y => Subtype.ext (hc x x.2 y y.2)⟩⟩, fun x hx => by
      rw [pow_two]
      exact hsq x hx⟩

end Core

end CFSG.OddStandard

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L125Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

namespace Sec125Core

variable {t : G} {V E : Subgroup G}

theorem V_le_centralizer (h : Sec125Core t V E) : V ≤ centralizer (V : Set G) := by
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact h.comm w hw v hv

theorem conj_mem_centralizer {x d : G} (hx : x ∈ normalizer (V : Set G))
    (hd : d ∈ centralizer (V : Set G)) : x * d * x⁻¹ ∈ centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' : x⁻¹ * v * x ∈ V := by
    refine (Subgroup.mem_normalizer_iff.mp hx (x⁻¹ * v * x)).mpr ?_
    have e : x * (x⁻¹ * v * x) * x⁻¹ = v := by group
    rw [e]
    exact hv
  have hcomm : (x⁻¹ * v * x) * d = d * (x⁻¹ * v * x) :=
    Subgroup.mem_centralizer_iff.mp hd _ hv'
  calc v * (x * d * x⁻¹) = x * ((x⁻¹ * v * x) * d) * x⁻¹ := by group
    _ = x * (d * (x⁻¹ * v * x)) * x⁻¹ := by rw [hcomm]
    _ = x * d * x⁻¹ * v := by group

theorem conj_mem_centralizer' {x d : G} (hx : x ∈ normalizer (V : Set G))
    (hd : d ∈ centralizer (V : Set G)) : x⁻¹ * d * x ∈ centralizer (V : Set G) := by
  have := conj_mem_centralizer (inv_mem hx) hd
  simpa using this

theorem zpowers_le_normalizer_centralizer (h : Sec125Core t V E) :
    zpowers t ≤ normalizer (centralizer (V : Set G) : Set G) := by
  intro s hs
  have hsN : s ∈ normalizer (V : Set G) := h.zpowers_le_normalizer hs
  rw [Subgroup.mem_normalizer_iff]
  intro d
  exact ⟨fun hd => conj_mem_centralizer hsN hd, fun hd => by
    have h1 := conj_mem_centralizer' hsN hd
    have e : s⁻¹ * (s * d * s⁻¹) * s = d := by group
    rwa [e] at h1⟩

theorem sup_le_normalizer (h : Sec125Core t V E) :
    centralizer (V : Set G) ⊔ zpowers t ≤ normalizer (V : Set G) :=
  sup_le (fun x hx => Subgroup.centralizer_le_normalizer _ hx) h.zpowers_le_normalizer

theorem mem_sup (h : Sec125Core t V E) {x : G}
    (hx : x ∈ centralizer (V : Set G) ⊔ zpowers t) :
    ∃ δ ∈ centralizer (V : Set G), ∃ s ∈ zpowers t, x = δ * s := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
    h.zpowers_le_normalizer_centralizer] at hx
  obtain ⟨δ, hδ, s, hs, rfl⟩ := hx
  exact ⟨δ, hδ, s, hs, rfl⟩

theorem mem_E_of_normalizes (h : Sec125Core t V E) {Q : Subgroup G}
    (hQH : Q ≤ centralizer (V : Set G) ⊔ zpowers t) (hQ : IsPGroup 2 Q) (hEQ : E ≤ Q) {x : G}
    (hxQ : x ∈ Q) (hx : ∀ e ∈ E, x * e * x⁻¹ ∈ E) : x ∈ E := by
  have hxN : x ∈ normalizer (V : Set G) := h.sup_le_normalizer (hQH hxQ)
  obtain ⟨w, hw, hwc⟩ := h.exists_comm (hx t h.t_mem) hxN
  obtain ⟨δ, hδ, s, hs, hxs⟩ := h.mem_sup (hQH hxQ)
  have hsE : s ∈ E := h.sup ▸ (le_sup_right : zpowers t ≤ V ⊔ zpowers t) hs
  have hst : s * t = t * s := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    exact ((Commute.refl t).zpow_left n).eq
  have hwx : w⁻¹ * x = (w⁻¹ * δ) * s := by rw [hxs]; group
  have hdt : (w⁻¹ * δ) * t = t * (w⁻¹ * δ) := by
    have h1 : ((w⁻¹ * δ) * s) * t = t * ((w⁻¹ * δ) * s) := by rw [← hwx]; exact hwc
    have h2 : (w⁻¹ * δ) * t * s = t * (w⁻¹ * δ) * s := by
      calc (w⁻¹ * δ) * t * s = (w⁻¹ * δ) * (t * s) := by group
        _ = (w⁻¹ * δ) * (s * t) := by rw [hst]
        _ = ((w⁻¹ * δ) * s) * t := by group
        _ = t * ((w⁻¹ * δ) * s) := h1
        _ = t * (w⁻¹ * δ) * s := by group
    exact mul_right_cancel h2
  have hwD : w ∈ centralizer (V : Set G) := h.V_le_centralizer hw
  have hdD : w⁻¹ * δ ∈ centralizer (V : Set G) := mul_mem (inv_mem hwD) hδ
  have hdE : w⁻¹ * δ ∈ centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    rcases h.mem_E.mp he with hV | ⟨v, hv, rfl⟩
    · exact Subgroup.mem_centralizer_iff.mp hdD e hV
    · have hvd : v * (w⁻¹ * δ) = (w⁻¹ * δ) * v := Subgroup.mem_centralizer_iff.mp hdD v hv
      calc v * t * (w⁻¹ * δ) = v * (t * (w⁻¹ * δ)) := by group
        _ = v * ((w⁻¹ * δ) * t) := by rw [hdt]
        _ = (v * (w⁻¹ * δ)) * t := by group
        _ = ((w⁻¹ * δ) * v) * t := by rw [hvd]
        _ = (w⁻¹ * δ) * (v * t) := by group
  have hdQ : w⁻¹ * δ ∈ Q := by
    have hwQ : w ∈ Q := hEQ (h.V_le hw)
    have hsQ : s ∈ Q := hEQ hsE
    have e : w⁻¹ * δ = w⁻¹ * x * s⁻¹ := by rw [hxs]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hwQ) hxQ) (inv_mem hsQ)
  obtain ⟨k, hk⟩ := hQ ⟨w⁻¹ * δ, hdQ⟩
  have hdV : w⁻¹ * δ ∈ V :=
    h.two _ hdE ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hxeq : x = w * (w⁻¹ * δ) * s := by rw [hxs]; group
  rw [hxeq]
  exact mul_mem (mul_mem (h.V_le hw) (h.V_le hdV)) hsE

theorem eq_of_le [Finite G] (h : Sec125Core t V E) {Q : Subgroup G}
    (hQH : Q ≤ centralizer (V : Set G) ⊔ zpowers t) (hQ : IsPGroup 2 Q) (hEQ : E ≤ Q) :
    Q = E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  haveI : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hlt : E.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr (fun htop => hne ?_)
    refine le_antisymm ?_ hEQ
    intro q hq
    have : (⟨q, hq⟩ : ↥Q) ∈ E.subgroupOf Q := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  have hlt' := Group.normalizerCondition_of_isNilpotent (E.subgroupOf Q) hlt
  obtain ⟨x, hxN, hxn⟩ := SetLike.exists_of_lt hlt'
  apply hxn
  rw [Subgroup.mem_subgroupOf]
  refine h.mem_E_of_normalizes hQH hQ hEQ x.2 ?_
  intro e he
  have hmem := (Subgroup.mem_normalizer_iff.mp hxN) ⟨e, hEQ he⟩
  have h1 : (⟨e, hEQ he⟩ : ↥Q) ∈ E.subgroupOf Q := Subgroup.mem_subgroupOf.mpr he
  exact Subgroup.mem_subgroupOf.mp (hmem.mp h1)

theorem two_mem [Finite G] (h : Sec125Core t V E) (hE2 : IsPGroup 2 E) {g : G}
    (hg : g ∈ centralizer (V : Set G)) (h2 : ∃ k : ℕ, g ^ (2 ^ k) = 1) : g ∈ V := by
  have hDH : centralizer (V : Set G) ≤ centralizer (V : Set G) ⊔ zpowers t := le_sup_left
  have hEH : E ≤ centralizer (V : Set G) ⊔ zpowers t := by
    rw [← h.sup]
    exact sup_le (h.V_le_centralizer.trans hDH) le_sup_right
  obtain ⟨U, hU, hEU⟩ := exists_isSylow2Of_ge hE2 hEH
  have hUE : U = E := h.eq_of_le hU.1 hU.2.1 hEU
  have hg2 : IsPGroup 2 (zpowers g) := by
    obtain ⟨k, hk⟩ := h2
    apply IsPGroup.of_card_dvd_pow (n := k)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hk
  have hgH : zpowers g ≤ centralizer (V : Set G) ⊔ zpowers t :=
    (Subgroup.zpowers_le.mpr hg).trans hDH
  obtain ⟨Q, hQ, hgQ⟩ := exists_isSylow2Of_ge hg2 hgH
  obtain ⟨a, haH, ha⟩ := hU.exists_conj_mem hQ
  have haN : a ∈ normalizer (V : Set G) := h.sup_le_normalizer haH
  have hgU : a⁻¹ * g * a ∈ E := hUE ▸ (ha g).1 (hgQ (Subgroup.mem_zpowers g))
  have hgD : a⁻¹ * g * a ∈ centralizer (V : Set G) := conj_mem_centralizer' haN hg
  have hgV : a⁻¹ * g * a ∈ V :=
    h.mem_V_of_centralizes hgU (fun v hv => (Subgroup.mem_centralizer_iff.mp hgD v hv).symm)
  have e : g = a * (a⁻¹ * g * a) * a⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp haN _).mp hgV

theorem sylow [Finite G] (h : Sec125Core t V E) (hE2 : IsPGroup 2 E) :
    IsSylow2Of V (centralizer (V : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVD : V ≤ centralizer (V : Set G) := h.V_le_centralizer
  have hV2 : IsPGroup 2 V := hE2.to_le h.V_le
  let P : Sylow 2 ↥(centralizer (V : Set G)) := default
  have hT := isSylow2Of_map_sylow P
  have hnorm : (V.subgroupOf (centralizer (V : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hVD]
    intro v k hv hk
    have hc : v * k = k * v := Subgroup.mem_centralizer_iff.mp hk v hv
    have e : k * v * k⁻¹ = v := by rw [← hc]; group
    rw [e]
    exact hv
  have hVsub : IsPGroup 2 (V.subgroupOf (centralizer (V : Set G))) :=
    hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVD).symm
  have hle : V.subgroupOf (centralizer (V : Set G)) ≤ (P : Subgroup ↥(centralizer (V : Set G))) :=
    hVsub.le_sylow_of_normal P
  have hTV : (P : Subgroup ↥(centralizer (V : Set G))).map (centralizer (V : Set G)).subtype
      = V := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨k, hk⟩ := P.isPGroup' ⟨y, hy⟩
      have hk' : (y : G) ^ (2 ^ k) = 1 := by
        have := congrArg
          (fun z : ↥(P : Subgroup ↥(centralizer (V : Set G))) =>
            (((z : ↥(centralizer (V : Set G))) : G))) hk
        simpa using this
      exact h.two_mem hE2 y.2 ⟨k, hk'⟩
    · intro v hv
      exact ⟨⟨v, hVD hv⟩, hle (Subgroup.mem_subgroupOf.mpr hv), rfl⟩
  rw [hTV] at hT
  exact hT

end Sec125Core

end CFSG.OddStandard.SmallF3.Omega

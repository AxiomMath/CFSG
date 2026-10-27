module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMK1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMK2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMK3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMK4
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMX2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYLD

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G}

theorem mem_OG_iff {a : G} (ha : a ∈ centralizer ({β} : Set G)) :
    a ∈ OG β ↔ (⟨a, ha⟩ : ↥(centralizer ({β} : Set G))) ∈
      fusionOddCore ↥(centralizer ({β} : Set G)) := by
  constructor
  · rintro ⟨o, ho, rfl⟩
    exact ho
  · intro h
    exact ⟨⟨a, ha⟩, h, rfl⟩

theorem OuterS16Hyp.mem_OG_of_central
    (h : OuterS16Hyp G L z t T E Q x B β) {y : G} (hy : y ∈ centralizer ({β} : Set G))
    (hcomm : ∀ a ∈ centralizer ({β} : Set G), y * a * y⁻¹ * a⁻¹ ∈ OG β) : y ∈ OG β := by
  have hM := h.m10Config
  have hg : ∀ w : ↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G)),
      w * (QuotientGroup.mk (⟨y, hy⟩ : ↥(centralizer ({β} : Set G)))) =
        (QuotientGroup.mk (⟨y, hy⟩ : ↥(centralizer ({β} : Set G)))) * w := by
    intro w
    induction w using QuotientGroup.induction_on with
    | _ a =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have ha := a.2
      have h1 : y * (a : G)⁻¹ * y⁻¹ * ((a : G)⁻¹)⁻¹ ∈ OG β := hcomm _ (inv_mem ha)
      have h2 : y⁻¹ * (y * (a : G)⁻¹ * y⁻¹ * ((a : G)⁻¹)⁻¹) * (y⁻¹)⁻¹ ∈ OG β :=
        OG_normal_conj (inv_mem hy) h1
      have h3 : ((a : G)⁻¹ * y⁻¹ * (a : G) * y)⁻¹ ∈ OG β := by
        refine inv_mem ?_
        convert h2 using 1
        group
      have h4 : (⟨((a : G) * y)⁻¹ * (y * (a : G)), by
          exact mul_mem (inv_mem (mul_mem ha hy)) (mul_mem hy ha)⟩ : ↥(centralizer ({β} : Set G))) ∈
          fusionOddCore ↥(centralizer ({β} : Set G)) := by
        rw [← mem_OG_iff]
        convert h3 using 1
        group
      exact h4
  have h1 := hM.center_bar_trivial hg
  exact (mem_OG_iff hy).2 ((QuotientGroup.eq_one_iff _).1 h1)

theorem OuterS16Hyp.nf
    (h : OuterS16Hyp G L z t T E Q x B β) :
    ∀ y ∈ normalizer ((zpowers β : Subgroup G) : Set G), y ∉ centralizer ({β} : Set G) →
      ∃ k ∈ centralizer ({β} : Set G), y * k * y⁻¹ * k⁻¹ ∉ OG β := by
  intro y hyN hyK
  by_contra hcon
  push Not at hcon
  have hβ3 : orderOf β = 3 := h.outerB.beta_order
  have hcfg := h.outerE.cfg
  have hzK : z ∈ centralizer ({β} : Set G) := h.z_mem_cent_beta
  obtain ⟨σ₀, v, ξ, hD0, -⟩ := h.exists_lData
  have hξL : ξ ∈ L := hD0.ξ_L
  have hξβ : ξ * β * ξ⁻¹ = β⁻¹ := hD0.ξ_β
  have hξ2 : ξ * ξ = 1 := hD0.ξ_sq
  have hξi : ξ⁻¹ = ξ := inv_eq_of_mul_eq_one_right hξ2
  have hξz : ξ * z = z * ξ := hcfg.z_comm_of_mem_A hξL
  have hξN : ξ ∈ normalizer ((centralizer ({β} : Set G) : Subgroup G) : Set G) :=
    normalizer_cent_of_conj (Or.inr hξβ)
  have hyβ : y * β * y⁻¹ = β⁻¹ := inv_of_mem_normalizer_zpowers hβ3 hyN hyK
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : G, k₀ = y⁻¹ * ξ := ⟨_, rfl⟩
  have hξk : ξ = y * k₀ := by rw [hk₀]; group
  have hyb : y⁻¹ * β⁻¹ * y = β := by
    calc y⁻¹ * β⁻¹ * y = y⁻¹ * (y * β * y⁻¹) * y := by rw [hyβ]
      _ = β := by group
  have hk0β : k₀ * β * k₀⁻¹ = β := by
    calc k₀ * β * k₀⁻¹ = y⁻¹ * (ξ * β * ξ⁻¹) * y := by rw [hk₀]; group
      _ = y⁻¹ * β⁻¹ * y := by rw [hξβ]
      _ = β := hyb
  have hk₀K : k₀ ∈ centralizer ({β} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc k₀ * β = (k₀ * β * k₀⁻¹) * k₀ := by group
      _ = β * k₀ := by rw [hk0β]
  have hA : ∀ a ∈ centralizer ({β} : Set G), ξ * a * ξ⁻¹ * (k₀ * a * k₀⁻¹)⁻¹ ∈ OG β := by
    intro a ha
    have hu : k₀ * a * k₀⁻¹ ∈ centralizer ({β} : Set G) :=
      mul_mem (mul_mem hk₀K ha) (inv_mem hk₀K)
    have e : ξ * a * ξ⁻¹ * (k₀ * a * k₀⁻¹)⁻¹ =
        y * (k₀ * a * k₀⁻¹) * y⁻¹ * (k₀ * a * k₀⁻¹)⁻¹ := by
      rw [hξk]; group
    rw [e]
    exact hcon _ hu
  have hkz : k₀ * z * k₀⁻¹ * z⁻¹ ∈ OG β := by
    have h1 := hA z hzK
    have hz' : ξ * z * ξ⁻¹ = z := by rw [hξz]; group
    rw [hz'] at h1
    have h2 := inv_mem h1
    convert h2 using 1
    group
  have hcomm2 : ∀ a ∈ centralizer ({β} : Set G),
      (k₀ * k₀) * a * (k₀ * k₀)⁻¹ * a⁻¹ ∈ OG β := by
    intro a ha
    obtain ⟨a', ha'⟩ : ∃ a' : G, a' = k₀ * a * k₀⁻¹ := ⟨_, rfl⟩
    have ha'K : a' ∈ centralizer ({β} : Set G) := by
      rw [ha']; exact mul_mem (mul_mem hk₀K ha) (inv_mem hk₀K)
    have c1 : ξ * a * ξ⁻¹ * a'⁻¹ ∈ OG β := by rw [ha']; exact hA a ha
    have c2 : ξ * a' * ξ⁻¹ * (k₀ * a' * k₀⁻¹)⁻¹ ∈ OG β := hA a' ha'K
    have c1' := conj_mem_OG hξN c1
    have key : ξ * (ξ * a * ξ⁻¹) * ξ⁻¹ = a := by
      calc ξ * (ξ * a * ξ⁻¹) * ξ⁻¹ = (ξ * ξ) * a * (ξ⁻¹ * ξ⁻¹) := by group
        _ = a := by rw [hξ2, hξi, hξ2]; group
    have e0 : (ξ * (ξ * a * ξ⁻¹ * a'⁻¹) * ξ⁻¹) * (ξ * a' * ξ⁻¹ * (k₀ * a' * k₀⁻¹)⁻¹) *
        (k₀ * a' * k₀⁻¹) = ξ * (ξ * a * ξ⁻¹) * ξ⁻¹ := by group
    have e := e0.trans key
    have hw : k₀ * a' * k₀⁻¹ = (k₀ * k₀) * a * (k₀ * k₀)⁻¹ := by rw [ha']; group
    have hC : (ξ * (ξ * a * ξ⁻¹ * a'⁻¹) * ξ⁻¹) * (ξ * a' * ξ⁻¹ * (k₀ * a' * k₀⁻¹)⁻¹) ∈ OG β :=
      mul_mem c1' c2
    obtain ⟨C, hCdef⟩ : ∃ C : G, C = (ξ * (ξ * a * ξ⁻¹ * a'⁻¹) * ξ⁻¹) *
        (ξ * a' * ξ⁻¹ * (k₀ * a' * k₀⁻¹)⁻¹) := ⟨_, rfl⟩
    rw [← hCdef] at hC e
    have e2 : (k₀ * a' * k₀⁻¹) * a⁻¹ = C⁻¹ := by
      calc (k₀ * a' * k₀⁻¹) * a⁻¹ = C⁻¹ * (C * (k₀ * a' * k₀⁻¹)) * a⁻¹ := by group
        _ = C⁻¹ * a * a⁻¹ := by rw [e]
        _ = C⁻¹ := by group
    rw [← hw, e2]
    exact inv_mem hC
  have hk2K : k₀ * k₀ ∈ centralizer ({β} : Set G) := mul_mem hk₀K hk₀K
  have hk2 : k₀ * k₀ ∈ OG β := h.mem_OG_of_central hk2K hcomm2
  have hM := h.m10Config
  have hkzK : k₀ * z * k₀⁻¹ * z⁻¹ ∈ centralizer ({β} : Set G) :=
    mul_mem (mul_mem (mul_mem hk₀K hzK) (inv_mem hk₀K)) (inv_mem hzK)
  obtain ⟨d', hd'D, j, hj⟩ := hM.exists_mem_zD
    (k := (⟨k₀, hk₀K⟩ : ↥(centralizer ({β} : Set G))))
    ((mem_OG_iff hkzK).1 hkz) ((mem_OG_iff hk2K).1 hk2)
  have hdD : (d' : G) ∈ L ⊓ centralizer ({β} : Set G) := Subgroup.mem_subgroupOf.1 hd'D
  obtain ⟨d, hd⟩ : ∃ d : G, d = (d' : G) := ⟨_, rfl⟩
  rw [← hd] at hdD
  have hdL : d ∈ L := hdD.1
  have hdK : d ∈ centralizer ({β} : Set G) := hdD.2
  have hzdK : z ^ j * d ∈ centralizer ({β} : Set G) := mul_mem (zpow_mem hzK j) hdK
  obtain ⟨e, he_def⟩ : ∃ e : G, e = (z ^ j * d)⁻¹ * k₀ := ⟨_, rfl⟩
  have heK : e ∈ centralizer ({β} : Set G) := by
    rw [he_def]; exact mul_mem (inv_mem hzdK) hk₀K
  have heO : e ∈ OG β := by
    rw [mem_OG_iff heK]
    have : (⟨e, heK⟩ : ↥(centralizer ({β} : Set G))) =
        ((⟨z, hzK⟩ : ↥(centralizer ({β} : Set G))) ^ j * d')⁻¹ * ⟨k₀, hk₀K⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, he_def, hd]
    rw [this]
    exact hj
  have hk0e : k₀ = (z ^ j * d) * e := by rw [he_def]; group
  obtain ⟨y₁, hy₁D, hy₁⟩ := h.xiOuter hξL hξβ d hdD
  apply hy₁
  have hxL : y₁ ∈ L := hy₁D.1
  have hxK : y₁ ∈ centralizer ({β} : Set G) := hy₁D.2
  have hmL : d * y₁ * d⁻¹ ∈ L := mul_mem (mul_mem hdL hxL) (inv_mem hdL)
  have hmK : d * y₁ * d⁻¹ ∈ centralizer ({β} : Set G) :=
    mul_mem (mul_mem hdK hxK) (inv_mem hdK)
  have hzm : (d * y₁ * d⁻¹) * z ^ j = z ^ j * (d * y₁ * d⁻¹) :=
    (Commute.zpow_right (show Commute (d * y₁ * d⁻¹) z from hcfg.z_comm_of_mem_A hmL) j).eq
  have ho₁ : e * (y₁ * e⁻¹ * y₁⁻¹) ∈ OG β := mul_mem heO (OG_normal_conj hxK (inv_mem heO))
  have ho₂ : (z ^ j * d) * (e * (y₁ * e⁻¹ * y₁⁻¹)) * (z ^ j * d)⁻¹ ∈ OG β :=
    OG_normal_conj hzdK ho₁
  have hxk : k₀ * y₁ * k₀⁻¹ =
      ((z ^ j * d) * (e * (y₁ * e⁻¹ * y₁⁻¹)) * (z ^ j * d)⁻¹) * (d * y₁ * d⁻¹) := by
    calc k₀ * y₁ * k₀⁻¹ = (z ^ j * d) * (e * y₁ * e⁻¹) * (z ^ j * d)⁻¹ := by rw [hk0e]; group
      _ = ((z ^ j * d) * (e * (y₁ * e⁻¹ * y₁⁻¹)) * (z ^ j * d)⁻¹) *
          ((z ^ j * d) * y₁ * (z ^ j * d)⁻¹) := by group
      _ = ((z ^ j * d) * (e * (y₁ * e⁻¹ * y₁⁻¹)) * (z ^ j * d)⁻¹) * (d * y₁ * d⁻¹) := by
          rw [show (z ^ j * d) * y₁ * (z ^ j * d)⁻¹ = z ^ j * (d * y₁ * d⁻¹) * (z ^ j)⁻¹ by group,
            ← hzm]
          group
  have hc₁ := hA y₁ hxK
  have hmem : (ξ * y₁ * ξ⁻¹)⁻¹ * (d * y₁ * d⁻¹) ∈ OG β := by
    have e3 : (ξ * y₁ * ξ⁻¹)⁻¹ * (d * y₁ * d⁻¹) =
        (d * y₁ * d⁻¹)⁻¹ * ((ξ * y₁ * ξ⁻¹ * (k₀ * y₁ * k₀⁻¹)⁻¹) *
          ((z ^ j * d) * (e * (y₁ * e⁻¹ * y₁⁻¹)) * (z ^ j * d)⁻¹))⁻¹ * ((d * y₁ * d⁻¹)⁻¹)⁻¹ := by
      have e4 : ξ * y₁ * ξ⁻¹ = (ξ * y₁ * ξ⁻¹ * (k₀ * y₁ * k₀⁻¹)⁻¹) * (k₀ * y₁ * k₀⁻¹) := by group
      rw [e4, hxk]
      group
    rw [e3]
    exact OG_normal_conj (inv_mem hmK) (inv_mem (mul_mem hc₁ ho₂))
  have hξxL : ξ * y₁ * ξ⁻¹ ∈ L := mul_mem (mul_mem hξL hxL) (inv_mem hξL)
  have hξxK : ξ * y₁ * ξ⁻¹ ∈ centralizer ({β} : Set G) := (mem_normalizer_iff.1 hξN y₁).1 hxK
  have hDmem : (ξ * y₁ * ξ⁻¹)⁻¹ * (d * y₁ * d⁻¹) ∈ L ⊓ centralizer ({β} : Set G) :=
    Subgroup.mem_inf.2 ⟨Subgroup.mul_mem L (Subgroup.inv_mem L hξxL) hmL,
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hξxK) hmK⟩
  exact h.inf_odd_le hDmem hmem

theorem OuterS16Hyp.ker_action
    (h : OuterS16Hyp G L z t T E Q x B β) {y : G}
    (hy : y ∈ normalizer ((zpowers β : Subgroup G) : Set G))
    (htriv : ∀ k ∈ centralizer ({β} : Set G), y * k * y⁻¹ * k⁻¹ ∈ OG β) : y ∈ OG β := by
  by_cases hyK : y ∈ centralizer ({β} : Set G)
  · exact h.mem_OG_of_central hyK htriv
  · obtain ⟨k, hk, hbad⟩ := h.nf y hy hyK
    exact absurd (htriv k hk) hbad

end CFSG.EvenSporadicStandard.Fin76b

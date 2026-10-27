module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnbalModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOuter

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G]

theorem comm_mem_oddCore {x c d : G} (hc : c ∈ centralizer ({x} : Set G))
    (hd : d ∈ (pPrimeCore 2 (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype) :
    c⁻¹ * d⁻¹ * c * d ∈ (pPrimeCore 2 (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype := by
  have h1 := conj_mem_oddCore (inv_mem hc) (inv_mem hd)
  rw [inv_inv] at h1
  exact mul_mem h1 hd

theorem mem_centralizer_of_mem_oddCore {x d : G}
    (hd : d ∈ (pPrimeCore 2 (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype) : d ∈ centralizer ({x} : Set G) := by
  obtain ⟨d', -, rfl⟩ := hd
  exact d'.2

variable {J : Subgroup G} {q : Jhat J →* Equiv.Perm (Fin 42)}

theorem image_comm_eq {d : G} (hdN : d ∈ normalizer (J : Set G)) {ρ : Equiv.Perm (Fin 42)}
    (hρ : ∀ e, q (betaHat J hdN e) = ρ * q e * ρ⁻¹) {c : G} (hcJ : c ∈ J)
    (hm : c⁻¹ * d⁻¹ * c * d ∈ J) :
    q (jq J ⟨c⁻¹ * d⁻¹ * c * d, hm⟩) = (q (jq J ⟨c, hcJ⟩))⁻¹ * ρ * q (jq J ⟨c, hcJ⟩) * ρ⁻¹ := by
  have e1 : (⟨c⁻¹ * d⁻¹ * c * d, hm⟩ : J) = (⟨c, hcJ⟩ : J)⁻¹ * conjJ J hdN ⟨c, hcJ⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjJ]
    group
  rw [e1, map_mul, map_inv, map_mul, map_inv, ← betaHat_jq, hρ]
  group

theorem orderOf_image_dvd {g : G} (hg : g ∈ J) : orderOf (q (jq J ⟨g, hg⟩)) ∣ orderOf g := by
  have h := orderOf_map_dvd (q.comp (jq J)) ⟨g, hg⟩
  rw [Subgroup.orderOf_mk] at h
  exact h

theorem comm_of_image_two [Finite G] {x : G} {d : G} (hdN : d ∈ normalizer (J : Set G))
    (hd : d ∈ (pPrimeCore 2 (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype)
    {ρ : Equiv.Perm (Fin 42)} (hρ : ∀ e, q (betaHat J hdN e) = ρ * q e * ρ⁻¹)
    {C : Subgroup (Equiv.Perm (Fin 42))} {k : ℕ} (hC : Nat.card C = 2 ^ k)
    (hCJ : ∀ {g : G} (hg : g ∈ J), g ∈ centralizer ({x} : Set G) → q (jq J ⟨g, hg⟩) ∈ C)
    {c : G} (hcJ : c ∈ J) (hcx : c ∈ centralizer ({x} : Set G)) :
    ρ * q (jq J ⟨c, hcJ⟩) = q (jq J ⟨c, hcJ⟩) * ρ := by
  have hm : c⁻¹ * d⁻¹ * c * d ∈ J := by
    have := conj_mem_of_mem_normalizer hdN hcJ
    have h2 := (mem_normalizer_iff.mp (inv_mem hdN) c).mp hcJ
    rw [inv_inv] at h2
    rw [show c⁻¹ * d⁻¹ * c * d = c⁻¹ * (d⁻¹ * c * d) by group]
    exact J.mul_mem (J.inv_mem hcJ) this
  have hdx := mem_centralizer_of_mem_oddCore hd
  have hmo := comm_mem_oddCore hcx hd
  have hmx := mem_centralizer_of_mem_oddCore hmo
  have hu := image_comm_eq hdN hρ hcJ hm
  have hodd : Nat.Coprime 2 (orderOf (q (jq J ⟨c⁻¹ * d⁻¹ * c * d, hm⟩))) :=
    (coprime_orderOf_of_mem_oddCore hmo).coprime_dvd_right (orderOf_image_dvd hm)
  have hmem := hCJ hm hmx
  have h2 : orderOf (⟨_, hmem⟩ : C) ∣ 2 ^ k := hC ▸ orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h2
  have h1 : orderOf (q (jq J ⟨c⁻¹ * d⁻¹ * c * d, hm⟩)) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hodd.symm) h2
  rw [orderOf_eq_one_iff, hu] at h1
  generalize q (jq J ⟨c, hcJ⟩) = s at h1 ⊢
  calc ρ * s = s * (s⁻¹ * ρ * s * ρ⁻¹) * ρ := by group
    _ = s * ρ := by rw [h1, mul_one]


theorem false_of_inner [Finite G] (hJ : ⁅J, J⁆ = J)
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) {x : G} (hxN : x ∈ normalizer (J : Set G))
    (hx2 : x * x = 1) (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    (hqker : q.ker = center (Jhat J)) (h3 : ∀ e ∈ q.ker, e ^ 3 = 1 → e = 1)
    (hβ : ∀ e, q (betaHat J hxN e) = r₁ * q e * r₁⁻¹) {D : Set G}
    (hDJ : closure {y | ∃ j ∈ J, ∃ d ∈ D, y = j⁻¹ * d⁻¹ * j * d} = J)
    (hDo : ∀ d ∈ D, d ∈ (pPrimeCore 2 (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype) : False := by
  obtain ⟨l, hl, hls⟩ := exists_lam (commutator_jhat hJ) q hqS hqsurj (hqker ▸ le_refl _)
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  obtain ⟨e₀, he₀, hβe⟩ := eq_conj_of_realization hJ hqsurj hqker r₁_mem_S hβ
  have hC₁r : ∀ t ∈ C₁, r₁ * t = t * r₁ := fun t ht =>
    (mem_centralizer_singleton_iff.mp (mem_inf.mp ht).1).symm
  set ε := epsHom q hQ.ker_le (betaHat J hxN) r₁ hβ C₁ hC₁r with hεd
  have hε2 : ∀ p : C₁.comap q, (ε p : Jhat J) * ε p = 1 := by
    intro p
    have hc := (ε p).2
    have hcc := mem_center_iff.mp (hQ.ker_le hc)
    have hεp : (ε p : Jhat J) = (p : Jhat J)⁻¹ * betaHat J hxN p := by rw [hεd, epsHom_apply]
    have hfix : betaHat J hxN (ε p) = ε p := by rw [hβe, hcc e₀]; group
    have h1 := betaHat_betaHat J hxN hx2 p
    have hβp : betaHat J hxN p = p * ε p := by rw [hεp]; group
    rw [hβp, map_mul, hβp, hfix] at h1
    calc (ε p : Jhat J) * ε p = (p : Jhat J)⁻¹ * (p * ε p * ε p) := by group
      _ = 1 := by rw [h1, inv_mul_cancel]
  have hrange : Nat.card ε.range ≤ 4 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun z => (⟨(z : q.ker), (z : q.ker).2, ?_⟩ : {e : Jhat J // e ∈ q.ker ∧ e * e = 1}))
      fun a b hab => ?_) hQ.card_omega_ker_le
    · obtain ⟨p, hp⟩ := z.2
      rw [← hp]
      exact hε2 p
    · have h := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h)
  have hcomap : Nat.card (C₁.comap q) = 64 * Nat.card q.ker := by
    rw [card_comap_eq q C₁ (fun t ht => hqsurj t (mem_inf.mp ht).2), card_C₁]
  have hkerε := Subgroup.card_ker_mul_card_range ε
  rw [hcomap] at hkerε
  set φ : ε.ker →* Equiv.Perm (Fin 42) := q.comp ((C₁.comap q).subtype.comp ε.ker.subtype)
    with hφ
  have hφk : Nat.card φ.ker ≤ Nat.card q.ker := by
    refine Nat.card_le_card_of_injective (fun p => (⟨((p : ε.ker) : C₁.comap q), ?_⟩ : q.ker))
      fun a b hab => ?_
    · exact p.2
    · have h := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext (Subtype.ext h))
  have hφc := Subgroup.card_ker_mul_card_range φ
  have hpos : 0 < Nat.card q.ker := Nat.card_pos
  have hH16 : 16 ≤ Nat.card φ.range := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card ε.ker * Nat.card ε.range ≤ Nat.card q.ker * 15 * 4 := by
      rw [← hφc]
      exact Nat.mul_le_mul (Nat.mul_le_mul hφk (by omega)) hrange
    nlinarith
  have hHC : φ.range ≤ C₁ := by
    rintro _ ⟨p, rfl⟩
    exact ((p : ε.ker) : C₁.comap q).2
  have hDN := fun d (hd : d ∈ D) => mem_normalizer_of_closure hDJ hd
  refine false_of_closure_le hL hDJ fun d hd j hj => ?_
  obtain ⟨ρ, hρR, hρ⟩ := exists_realization q hqS hqsurj (betaHat J (hDN d hd)) (fun e => by
    rw [hqker]
    exact mulEquiv_mem_center_iff _ e)
  have hxd : x * d = d * x :=
    (mem_centralizer_singleton_iff.mp (mem_centralizer_of_mem_oddCore (hDo d hd))).symm
  have hρr := realization_comm hqsurj hxN (hDN d hd) hxd r₁_mem_R hρR hβ hρ
  have h945 := realization_pow_odd hqsurj (hDN d hd)
    (coprime_orderOf_of_mem_oddCore (hDo d hd)) hρR hρ
  have hρ1 : ρ = 1 := by
    by_contra hne
    have hcen : ∀ h ∈ φ.range, ρ * h = h * ρ := by
      rintro _ ⟨p, rfl⟩
      have hpfix : betaHat J hxN (((p : ε.ker) : C₁.comap q) : Jhat J) =
          ((p : ε.ker) : C₁.comap q) := by
        have h1 := p.2
        rw [MonoidHom.mem_ker] at h1
        have h2 : (((ε (p : C₁.comap q)) : q.ker) : Jhat J) = 1 := congrArg Subtype.val h1
        have h3 : (((p : ε.ker) : C₁.comap q) : Jhat J)⁻¹ *
            betaHat J hxN (((p : ε.ker) : C₁.comap q) : Jhat J) = 1 := by
          rw [← epsHom_apply q hQ.ker_le (betaHat J hxN) r₁ hβ C₁ hC₁r]
          exact h2
        exact (inv_mul_eq_one.mp h3).symm
      obtain ⟨c, hce, hcx⟩ := exists_fixed_lift hxN hx2 hpfix
      have hcx' : (c : G) ∈ centralizer ({x} : Set G) := mem_centralizer_of_conj_eq (by
        have := congrArg Subtype.val hcx
        rwa [coe_conjJ] at this)
      have hk := comm_of_image_two (hDN d hd) (hDo d hd) hρ (C := C₁) (k := 6)
        (by rw [card_C₁]; norm_num) (fun {g} hg hgx =>
          range_le_of_realization hxN hqS hβ ⟨⟨g, hg, hgx⟩, rfl⟩) c.2 hcx'
      have e1 : (⟨(c : G), c.2⟩ : J) = c := rfl
      rw [e1, hce] at hk
      exact hk
    have := card_le_four_of_odd hρR hρr.symm h945 hne hHC hcen
    omega
  refine comm_mem_zStarIn_of_realization hqker (hDN d hd) (fun e => ?_) hj
  rw [hρ e, hρ1]
  group

end CFSG.ComponentClassification.GrSLit.L34Facts

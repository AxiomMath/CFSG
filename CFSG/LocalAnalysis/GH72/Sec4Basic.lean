module

public import CFSG.LocalAnalysis.GH72.DDSubgroups
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.GroupTheory.ABGLocalTools.Constraint

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools

section Conj

variable {G : Type*} [Group G]

theorem map_conj_inv_map_conj (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  ext x
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e]
  · intro hx
    exact ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, by group⟩

theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem IsIsolatedIn.map_conj {H : Subgroup G} {t : G} (ht : IsIsolatedIn H t) (g : G) :
    IsIsolatedIn (H.map (MulAut.conj g).toMonoidHom) (g * t * g⁻¹) := by
  obtain ⟨htH, ht2, hiso⟩ := ht
  refine ⟨⟨t, htH, rfl⟩, by rw [orderOf_conj_eq]; exact ht2, ?_⟩
  rintro _ ⟨h, hh, rfl⟩ hc
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hc ⊢
  have hc' : Commute (h * t * h⁻¹) t := by
    have e := hc.eq
    have e' : g⁻¹ * (g * h * g⁻¹ * (g * t * g⁻¹) * (g * h * g⁻¹)⁻¹ * (g * t * g⁻¹)) * g =
        g⁻¹ * (g * t * g⁻¹ * (g * h * g⁻¹ * (g * t * g⁻¹) * (g * h * g⁻¹)⁻¹)) * g := by
      rw [e]
    show h * t * h⁻¹ * t = t * (h * t * h⁻¹)
    calc h * t * h⁻¹ * t
        = g⁻¹ * (g * h * g⁻¹ * (g * t * g⁻¹) * (g * h * g⁻¹)⁻¹ * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹ * (g * h * g⁻¹ * (g * t * g⁻¹) * (g * h * g⁻¹)⁻¹)) * g := e'
      _ = t * (h * t * h⁻¹) := by group
  have h1 := hiso h hh hc'
  calc g * h * g⁻¹ * (g * t * g⁻¹) * (g * h * g⁻¹)⁻¹ = g * (h * t * h⁻¹) * g⁻¹ := by group
    _ = g * t * g⁻¹ := by rw [h1]

theorem eq_one_of_mul_self_of_odd {K : Subgroup G} (hK : Odd (Nat.card K)) {x : G} (hx : x ∈ K)
    (hx2 : x * x = 1) : x = 1 := by
  have h2 : orderOf (⟨x, hx⟩ : K) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simp [pow_two, hx2]))
  have hdvd : orderOf (⟨x, hx⟩ : K) ∣ Nat.card K := orderOf_dvd_natCard _
  have h1 : orderOf (⟨x, hx⟩ : K) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · rw [h] at hdvd
      exact absurd (even_iff_two_dvd.2 hdvd) (Nat.not_even_iff_odd.2 hK)
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 h1)

end Conj

section Sylow

variable {G : Type*} [Group G] [Finite G]

private theorem coe_smul_sylow' {p : ℕ} (g : G) (P : Sylow p G) :
    ((g • P : Sylow p G) : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
  rfl

theorem exists_map_conj_le_sylow {p : ℕ} [Fact p.Prime] (P : Sylow p G) {R : Subgroup G}
    (hR : IsPGroup p R) : ∃ g : G, R.map (MulAut.conj g).toMonoidHom ≤ P := by
  obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g, ?_⟩
  rw [← hg, coe_smul_sylow']
  exact map_mono hRQ

theorem exists_mem_map_conj_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {R K Q : Subgroup G}
    (hR : IsSylowOf p R K) (hQK : Q ≤ K) (hQ : IsPGroup p Q) :
    ∃ c ∈ K, Q.map (MulAut.conj c).toMonoidHom ≤ R := by
  obtain ⟨R', hR'⟩ := hR
  obtain ⟨P, hP⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K P R'
  refine ⟨c, c.2, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  rw [← hR']
  refine ⟨c * ⟨q, hQK hq⟩ * c⁻¹, ?_, rfl⟩
  rw [← hc, coe_smul_sylow']
  exact ⟨⟨q, hQK hq⟩, hP (show (⟨q, hQK hq⟩ : K) ∈ Q.comap K.subtype from hq), rfl⟩

theorem exists_mem_conj_mem_of_isSylowOf {p : ℕ} [Fact p.Prime] {R K : Subgroup G}
    (hR : IsSylowOf p R K) {x : G} (hxK : x ∈ K) (hx : IsPGroup p (zpowers x)) :
    ∃ c ∈ K, c * x * c⁻¹ ∈ R := by
  obtain ⟨c, hcK, hc⟩ := exists_mem_map_conj_le_of_isSylowOf hR (zpowers_le.2 hxK) hx
  exact ⟨c, hcK, hc ⟨x, mem_zpowers x, rfl⟩⟩

theorem isSylowOf_map_hom {G' : Type*} [Group G'] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (h : IsSylowOf p P K) (f : G →* G') : IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem pRank_eq_of_isSylowOf_two {R H : Subgroup G} (hR : IsSylowOf 2 R H) :
    CFSG.Open.pRank 2 R = CFSG.Open.pRank 2 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (CFSG.SectionRank.pRank_mono one_lt_two hR.le) ?_
  obtain ⟨E, hEH, hE, hEc⟩ := CFSG.SectionRank.exists_pRank one_lt_two H
  obtain ⟨c, -, hc⟩ := exists_mem_map_conj_le_of_isSylowOf hR hEH (IsPGroup.of_card hEc)
  exact CFSG.SectionRank.le_pRank one_lt_two hc (CFSG.SectionRank.isElemAbelian_map hE _)
    (by rw [card_map_of_injective (MulAut.conj c).injective, hEc])

end Sylow

section OddCore

theorem card_O_odd {G : Type*} [Group G] [Finite G] (H : Subgroup G) : Odd (Nat.card (O H)) := by
  show Odd (Nat.card ((CFSG.oddCore H).map H.subtype))
  rw [card_map_of_injective H.subtype_injective]
  exact odd_card_oddCore

theorem le_normalizer_O {G : Type*} [Group G] (H : Subgroup G) :
    H ≤ normalizer (O H : Set G) :=
  le_normalizer_map_subtype H (CFSG.oddCore H)

variable {P Q : Type*} [Group P] [Group Q] [Finite P]

theorem comap_oddCore_eq_of_odd_ker (f : P →* Q) (hf : Function.Surjective f)
    (hker : Odd (Nat.card f.ker)) : (CFSG.oddCore Q).comap f = CFSG.oddCore P := by
  haveI : Finite Q := Finite.of_surjective f hf
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine le_oddCore_of_normal ((CFSG.oddCore_normal Q).comap f) ?_
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥((CFSG.oddCore Q).comap f)) 2 h2
    have hx2 : (x : P) * x = 1 := by
      have h := pow_orderOf_eq_one x
      rw [hx, pow_two] at h
      exact congrArg Subtype.val h
    have hfx : f x = 1 :=
      eq_one_of_mul_self_of_odd odd_card_oddCore (Subgroup.mem_comap.1 x.2)
        (by rw [← map_mul, hx2, map_one])
    have hx1 : (x : P) = 1 := eq_one_of_mul_self_of_odd hker (f.mem_ker.2 hfx) hx2
    have : x = 1 := Subtype.ext hx1
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  · rw [← Subgroup.map_le_iff_le_comap]
    exact le_oddCore_of_normal ((CFSG.oddCore_normal P).map f hf)
      (Odd.of_dvd_nat odd_card_oddCore (Subgroup.card_map_dvd _ f))

theorem oddCore_quotient_oddCore_eq_bot (X : Type*) [Group X] [Finite X] :
    CFSG.oddCore (X ⧸ CFSG.oddCore X) = ⊥ := by
  have h := comap_oddCore_eq_of_odd_ker (QuotientGroup.mk' (CFSG.oddCore X))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact odd_card_oddCore)
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
  have hx : x ∈ CFSG.oddCore X := by
    rw [← h]
    exact hy
  exact (QuotientGroup.eq_one_iff x).2 hx

theorem isPGroup_of_surjective_of_odd_normal {X : Type*} [Group X] [Finite X]
    (hQ : CFSG.oddCore Q = ⊥) (α : X →* Q) (hα : Function.Surjective α) (N : Subgroup X)
    (hNn : N.Normal) (hN : Odd (Nat.card N)) (hpow : ∀ x : X, ∃ k : ℕ, x ^ 2 ^ k ∈ N) :
    IsPGroup 2 Q := by
  haveI : Finite Q := Finite.of_surjective α hα
  have hle : N.map α ≤ CFSG.oddCore Q :=
    le_oddCore_of_normal (hNn.map α hα) (Odd.of_dvd_nat hN (Subgroup.card_map_dvd _ α))
  rw [hQ] at hle
  intro q
  obtain ⟨x, rfl⟩ := hα q
  obtain ⟨k, hk⟩ := hpow x
  exact ⟨k, by rw [← map_pow]; exact mem_bot.1 (hle ⟨_, hk, rfl⟩)⟩

end OddCore

section Quotient

variable {G : Type*} [Group G] [Finite G]

theorem isIsolatedIn_of_mk_mem_center {H : Subgroup G} {t : G} (htH : t ∈ H) (ht2 : orderOf t = 2)
    (hc : (QuotientGroup.mk ⟨t, htH⟩ : Bar H) ∈ center (Bar H)) : IsIsolatedIn H t := by
  refine ⟨htH, ht2, fun h hh hcomm => ?_⟩
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hmk : (QuotientGroup.mk ((⟨t, htH⟩ : H)⁻¹ * ((⟨h, hh⟩ : H) * ⟨t, htH⟩ * (⟨h, hh⟩ : H)⁻¹)) :
      Bar H) = 1 := by
    have hz := mem_center_iff.1 hc (QuotientGroup.mk ⟨h, hh⟩)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hz]
    group
  have ho : t⁻¹ * (h * t * h⁻¹) ∈ O H := ⟨_, (QuotientGroup.eq_one_iff _).1 hmk, rfl⟩
  have hu2 : h * t * h⁻¹ * (h * t * h⁻¹) = 1 := by
    calc h * t * h⁻¹ * (h * t * h⁻¹) = h * (t * t) * h⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have ho2 : t⁻¹ * (h * t * h⁻¹) * (t⁻¹ * (h * t * h⁻¹)) = 1 := by
    rw [htinv]
    calc t * (h * t * h⁻¹) * (t * (h * t * h⁻¹)) = t * (h * t * h⁻¹ * t) * (h * t * h⁻¹) := by
          group
      _ = t * (t * (h * t * h⁻¹)) * (h * t * h⁻¹) := by rw [hcomm.eq]
      _ = (t * t) * (h * t * h⁻¹ * (h * t * h⁻¹)) := by group
      _ = 1 := by rw [htt, hu2, one_mul]
  have h1 := eq_one_of_mul_self_of_odd (card_O_odd H) ho ho2
  exact (inv_mul_eq_one.1 h1).symm

theorem pow_mem_of_relIndex_eq {Y K : Subgroup G} (hK : (K.subgroupOf Y).Normal) {n : ℕ}
    (hn : K.relIndex Y = 2 ^ n) {y : G} (hy : y ∈ Y) : y ^ 2 ^ n ∈ K := by
  have h := pow_card_eq_one' (G := ↥Y ⧸ K.subgroupOf Y) (x := QuotientGroup.mk ⟨y, hy⟩)
  have hc : Nat.card (↥Y ⧸ K.subgroupOf Y) = 2 ^ n := hn
  rw [hc, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
  simpa using mem_subgroupOf.1 h

theorem surjective_of_covers {H P : Subgroup G} (hPH : P ≤ H)
    (hcov : ∀ h ∈ H, ∃ p ∈ P, p⁻¹ * h ∈ O H) :
    Function.Surjective ((QuotientGroup.mk' (CFSG.oddCore H)).comp (inclusion hPH)) := by
  intro y
  obtain ⟨⟨h, hh⟩, rfl⟩ := QuotientGroup.mk'_surjective _ y
  obtain ⟨p, hp, hpO⟩ := hcov h hh
  obtain ⟨o, ho, hoe⟩ := hpO
  refine ⟨⟨p, hp⟩, ?_⟩
  show (QuotientGroup.mk (inclusion hPH ⟨p, hp⟩) : Bar H) = QuotientGroup.mk ⟨h, hh⟩
  rw [QuotientGroup.eq]
  have e : (inclusion hPH ⟨p, hp⟩)⁻¹ * ⟨h, hh⟩ = o := Subtype.ext (by
    rw [coe_subtype] at hoe
    rw [hoe]
    rfl)
  rw [e]
  exact ho

end Quotient

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G)

theorem S_le_C_z₁ : (𝔖.S : Subgroup G) ≤ C 𝔖.z₁ := by
  rw [← 𝔖.decomp.sup_eq]
  exact sup_le 𝔖.hz₁.2.2
    (𝔖.decomp.commute.trans (centralizer_le (Set.singleton_subset_iff.2 𝔖.hz₁.1)))

theorem conj_mem_of_mem_factor {P : Subgroup G} (hP : P = 𝔖.S₁ ∨ P = 𝔖.S₂) {x k : G}
    (hx : x ∈ P) (hx2 : orderOf x = 2) (hk : k * x * k⁻¹ ∈ (𝔖.S : Subgroup G)) :
    k * x * k⁻¹ ∈ P := by
  have hxS : x ∈ 𝔖.S₁ ⊔ 𝔖.S₂ := by
    rcases hP with rfl | rfl
    exacts [mem_sup_left hx, mem_sup_right hx]
  have hkS : k * x * k⁻¹ ∈ 𝔖.S₁ ⊔ 𝔖.S₂ := by
    rw [𝔖.decomp.sup_eq]
    exact hk
  have h := 𝔖.fusion.separate x hxS (k * x * k⁻¹) hkS hx2 (isConj_iff.2 ⟨k, rfl⟩)
  rcases hP with rfl | rfl
  · exact h.1.1 hx
  · exact h.2.1 hx

theorem z_mul_z_spec :
    𝔖.z₁ * 𝔖.z₂ ∈ 𝔖.S₁ ⊔ 𝔖.S₂ ∧ 𝔖.z₁ * 𝔖.z₂ ∉ 𝔖.S₁ ∧ 𝔖.z₁ * 𝔖.z₂ ∉ 𝔖.S₂ ∧
      orderOf (𝔖.z₁ * 𝔖.z₂) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h₁ := 𝔖.hz₁
  have h₂ := 𝔖.hz₂
  have hz₁1 : 𝔖.z₁ ≠ 1 := fun h => by rw [h, orderOf_one] at h₁; exact absurd h₁.2.1 (by norm_num)
  have hz₂1 : 𝔖.z₂ ≠ 1 := fun h => by rw [h, orderOf_one] at h₂; exact absurd h₂.2.1 (by norm_num)
  have hsq : ∀ x : G, orderOf x = 2 → x * x = 1 := fun x hx => by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  refine ⟨mul_mem_sup h₁.1 h₂.1, fun h => hz₂1 ((𝔖.decomp.mul_mem_left_iff h₁.1 h₂.1).1 h),
    fun h => hz₁1 ((𝔖.decomp.mul_mem_right_iff h₁.1 h₂.1).1 h), ?_⟩
  refine orderOf_eq_prime ?_ fun h => hz₂1 ?_
  · rw [pow_two]
    exact (𝔖.decomp.mul_self_iff h₁.1 h₂.1).2 ⟨hsq _ h₁.2.1, hsq _ h₂.2.1⟩
  · exact (𝔖.decomp.mul_mem_left_iff h₁.1 h₂.1).1 (by rw [h]; exact one_mem _)

theorem isConj_z {t : G} (ht : orderOf t = 2) :
    IsConj t 𝔖.z₁ ∨ IsConj t 𝔖.z₂ ∨ IsConj t (𝔖.z₁ * 𝔖.z₂) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨g, hg⟩ := exists_map_conj_le_sylow 𝔖.S hT
  have hgt : g * t * g⁻¹ ∈ (𝔖.S : Subgroup G) := hg ⟨t, mem_zpowers t, rfl⟩
  have hconj : IsConj t (g * t * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
  have ht2' : orderOf (g * t * g⁻¹) = 2 := by rw [orderOf_conj_eq]; exact ht
  have hS : g * t * g⁻¹ ∈ 𝔖.S₁ ⊔ 𝔖.S₂ := by
    rw [𝔖.decomp.sup_eq]
    exact hgt
  by_cases h₁ : g * t * g⁻¹ ∈ 𝔖.S₁
  · exact Or.inl (hconj.trans (𝔖.fusion.conj₁ _ h₁ _ 𝔖.hz₁.1 ht2' 𝔖.hz₁.2.1))
  by_cases h₂ : g * t * g⁻¹ ∈ 𝔖.S₂
  · exact Or.inr (Or.inl (hconj.trans (𝔖.fusion.conj₂ _ h₂ _ 𝔖.hz₂.1 ht2' 𝔖.hz₂.2.1)))
  obtain ⟨hm, hm₁, hm₂, hm2⟩ := 𝔖.z_mul_z_spec
  exact Or.inr (Or.inr (hconj.trans (𝔖.fusion.conj₃ _ hS _ hm h₁ h₂ hm₁ hm₂ ht2' hm2)))

theorem isIsolatedIn_of_unique {H N R P : Subgroup G} (hR : IsSylowOf 2 R H)
    (hRS : R ≤ 𝔖.S) (hHN : H ≤ normalizer (N : Set G)) (hP : P = 𝔖.S₁ ∨ P = 𝔖.S₂) {z : G}
    (hz : z ∈ R ⊓ N ⊓ P) (hz2 : orderOf z = 2) (huniq : ∀ t ∈ R ⊓ N ⊓ P, orderOf t = 2 → t = z) :
    IsIsolatedIn H z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hzRN, hzP⟩ := mem_inf.1 hz
  obtain ⟨hzR, hzN⟩ := mem_inf.1 hzRN
  have hzH : z ∈ H := hR.le hzR
  have hfix : ∀ k ∈ H, k * z * k⁻¹ ∈ R → k * z * k⁻¹ = z := by
    intro k hk hkR
    refine huniq _ (mem_inf.2 ⟨mem_inf.2 ⟨hkR, ?_⟩, ?_⟩) (by rw [orderOf_conj_eq]; exact hz2)
    · exact (mem_normalizer_iff.1 (hHN hk) z).1 hzN
    · exact 𝔖.conj_mem_of_mem_factor hP hzP hz2 (hRS hkR)
  have hRC : R ≤ C z := by
    intro r hr
    have h := hfix r (hR.le hr) (mul_mem (mul_mem hr hzR) (inv_mem hr))
    rw [mem_centralizer_singleton_iff]
    calc r * z = r * z * r⁻¹ * r := by group
      _ = z * r := by rw [h]
  have hRsyl : IsSylowOf 2 R (H ⊓ C z) := hR.of_le (le_inf hR.le hRC) inf_le_left
  refine ⟨hzH, hz2, fun h hh hc => ?_⟩
  have hu2 : orderOf (h * z * h⁻¹) = 2 := by rw [orderOf_conj_eq]; exact hz2
  have huC : h * z * h⁻¹ ∈ H ⊓ C z :=
    mem_inf.2 ⟨mul_mem (mul_mem hh hzH) (inv_mem hh), mem_centralizer_singleton_iff.2 hc.eq⟩
  obtain ⟨c, hcC, hcR⟩ := exists_mem_conj_mem_of_isSylowOf hRsyl huC
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one]))
  obtain ⟨hcH, hcz⟩ := mem_inf.1 hcC
  have hk : c * h * z * (c * h)⁻¹ = c * (h * z * h⁻¹) * c⁻¹ := by group
  have h1 := hfix (c * h) (mul_mem hcH hh) (by rw [hk]; exact hcR)
  rw [hk] at h1
  have hcz' : c * z = z * c := mem_centralizer_singleton_iff.1 hcz
  calc h * z * h⁻¹ = c⁻¹ * (c * (h * z * h⁻¹) * c⁻¹) * c := by group
    _ = c⁻¹ * (z * c) := by rw [h1, mul_assoc]
    _ = c⁻¹ * (c * z) := by rw [hcz']
    _ = z := by group

end Sec4Setting

end CFSG.GH72

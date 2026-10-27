module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineFour

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace SixNineFour

theorem exists_three_cycle {Q : Type*} [Group Q] {P : Subgroup Q} {a b : Q}
    (hP4 : ∀ x ∈ P, x = 1 ∨ x = a ∨ x = b ∨ x = a * b) (hab : a * b = b * a)
    (ha2 : a * a = 1) (hb1 : b ≠ 1) (hne : a ≠ b) (hbP : b ∈ P)
    {m₁ m₂ : Q} (hm₁ : m₁ ∈ normalizer (P : Set Q)) (hm₂ : m₂ ∈ normalizer (P : Set Q))
    (h₁ : m₁⁻¹ * a * m₁ = b) (h₂ : m₂⁻¹ * a * m₂ = a * b) :
    ∃ y ∈ normalizer (P : Set Q), y⁻¹ * a * y = b ∧ y⁻¹ * b * y = a * b := by
  have hinj : ∀ m x y : Q, m⁻¹ * x * m = m⁻¹ * y * m → x = y := fun m x y h => by
    have := congrArg (fun z => m * z * m⁻¹) h
    simpa [mul_assoc] using this
  have hc : ∀ m x y : Q, m⁻¹ * (x * y) * m = (m⁻¹ * x * m) * (m⁻¹ * y * m) := fun m x y => by
    group
  have hcomp : ∀ m n x : Q, (m * n)⁻¹ * x * (m * n) = n⁻¹ * (m⁻¹ * x * m) * n := fun m n x => by
    group
  have hb₁ := (mem_normalizer_iff''.mp hm₁ b).mp hbP
  have hb₂ := (mem_normalizer_iff''.mp hm₂ b).mp hbP
  rcases hP4 _ hb₁ with h3 | h3 | h3 | h3
  · exact absurd (hinj m₁ b 1 (by rw [h3]; group)) hb1
  · rcases hP4 _ hb₂ with h4 | h4 | h4 | h4
    · exact absurd (hinj m₂ b 1 (by rw [h4]; group)) hb1
    · refine ⟨m₂ * m₂, mul_mem hm₂ hm₂, ?_, ?_⟩
      · rw [hcomp, h₂, hc, h₂, h4, mul_assoc, ← hab, ← mul_assoc, ha2, one_mul]
      · rw [hcomp, h4, h₂]
    · refine ⟨m₁ * m₂, mul_mem hm₁ hm₂, ?_, ?_⟩
      · rw [hcomp, h₁, h4]
      · rw [hcomp, h3, h₂]
    · exact absurd (hinj m₂ a b (by rw [h₂, h4])) hne
  · exact absurd (hinj m₁ a b (by rw [h₁, h3])) hne
  · exact ⟨m₁, hm₁, h₁, h3⟩

end SixNineFour

namespace U3U1Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}

theorem normalizer_le_normalizer_R₂ (hU : U3U1Data G L f t T R₂ U₁) :
    normalizer (U₁ : Set G) ≤ normalizer (R₂ : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
  rw [← hU.commutator_eq, map_commutator, hg]

section Certificates


theorem exists_three_cycle_of_four (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hS : ∃ S : Sylow 2 G, (S : Subgroup G) = U₁ ⊔ T)
    (hfour : ∀ c ∈ T, c ^ 2 ∈ szT₁ L T ⊔ zpowers t) {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1)
    (hvS : v ∉ szT₁ L T ⊔ zpowers t)
    (hall : ∀ w ∈ T, w ^ 2 = 1 → w ∉ szT₁ L T ⊔ zpowers t →
      ∃ g ∈ normalizer (U₁ : Set G), g⁻¹ * t * g = w) :
    ∃ y ∈ normalizer (U₁ : Set G) ⊓ normalizer ((U₁ ⊔ T : Subgroup G) : Set G),
      v⁻¹ * (y⁻¹ * t * y) ∈ U₁ ∧ (t * v)⁻¹ * (y⁻¹ * v * y) ∈ U₁ := by
  classical
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := hU.fourData_of_four h hS2 hR hS hfour hvT hv2 hvS
  obtain ⟨S₀, hS₀⟩ := hS
  set Y := normalizer (U₁ : Set G) with hYdef
  set K := U₁.subgroupOf Y with hKdef
  set π := QuotientGroup.mk' K with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective K
  have hSY : U₁ ⊔ T ≤ Y := hD.normU
  set Sb := ((U₁ ⊔ T).subgroupOf Y).map π with hSb
  have memS : ∀ x : Y, π x ∈ Sb ↔ (x : G) ∈ U₁ ⊔ T := StrongClosureMod.mem_map_mk_iff hD.le_S
  have hone : ∀ x : Y, π x = 1 ↔ (x : G) ∈ U₁ := fun x =>
    (QuotientGroup.eq_one_iff x).trans mem_subgroupOf
  have hS₀Y : (S₀ : Subgroup G) ≤ Y := by rw [hS₀]; exact hSY
  set P : Sylow 2 (Y ⧸ K) := (S₀.subtype hS₀Y).mapSurjective hπs with hPdef
  have hP : (P : Subgroup (Y ⧸ K)) = Sb := by
    rw [hPdef, Sylow.coe_mapSurjective, Sylow.coe_subtype, hS₀]
  have hSbcomm : ∀ a ∈ Sb, ∀ b ∈ Sb, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    refine QuotientGroup.eq.mpr (mem_subgroupOf.mpr ?_)
    have h1 := hD.commS _ (inv_mem (mem_subgroupOf.mp hy)) _ (inv_mem (mem_subgroupOf.mp hx))
    have e : (((x * y)⁻¹ * (y * x) : Y) : G) =
        (y : G)⁻¹ * (x : G)⁻¹ * (y : G)⁻¹⁻¹ * (x : G)⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e]
    exact h1
  have hcent : ∀ z ∈ Sb, z ∈ centralizer ((P : Subgroup (Y ⧸ K)) : Set (Y ⧸ K)) := fun z hz =>
    mem_centralizer_iff.mpr fun w hw => hSbcomm w (by rw [← hP]; exact hw) z hz
  set tY : Y := ⟨t, hSY hD.t_mem⟩ with htY
  set vY : Y := ⟨v, hSY hD.v_mem⟩ with hvY
  have htvS : t * v ∈ U₁ ⊔ T := mul_mem hD.t_mem hD.v_mem
  set tvY : Y := ⟨t * v, hSY htvS⟩ with htvY
  have hconj : ∀ (wY : Y), (wY : G) ∈ T → (wY : G) ^ 2 = 1 →
      (wY : G) ∉ szT₁ L T ⊔ zpowers t →
      ∃ m ∈ normalizer (Sb : Set (Y ⧸ K)), m⁻¹ * π tY * m = π wY := by
    intro wY hwT hw2 hwS
    obtain ⟨g, hg, hgw⟩ := hall _ hwT hw2 hwS
    set gY : Y := ⟨g, hg⟩ with hgY
    have hgw' : (π gY)⁻¹ * π tY * π gY = π wY := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (by simpa [htY, hgY] using hgw)
    obtain ⟨n, hn, hnw⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer P (π tY) (π gY)
      (hcent _ ((memS tY).mpr hD.t_mem))
      (by rw [hgw']; exact hcent _ ((memS wY).mpr (mem_sup_right hwT)))
    have hn' : n ∈ normalizer (Sb : Set (Y ⧸ K)) := by rw [← hP]; exact hn
    exact ⟨n, hn', by rw [← hnw, hgw']⟩
  obtain ⟨htvT, htv2, htvS'⟩ := h.mul_outer_of_card_sylow hS2 hvT hv2 hvS
  obtain ⟨m₁, hm₁, h₁⟩ := hconj vY hvT hv2 hvS
  obtain ⟨m₂, hm₂, h₂⟩ := hconj tvY htvT htv2 htvS'
  rw [show π tvY = π tY * π vY from map_mul π tY vY] at h₂
  have hP4 : ∀ x ∈ Sb, x = 1 ∨ x = π tY ∨ x = π vY ∨ x = π tY * π vY := by
    rintro _ ⟨x, hx, rfl⟩
    have hxS : (x : G) ∈ U₁ ⊔ T := mem_subgroupOf.mp hx
    have key : ∀ wY : Y, (wY : G)⁻¹ * x ∈ U₁ → π x = π wY := fun wY hw => by
      refine (QuotientGroup.eq.mpr (mem_subgroupOf.mpr ?_)).symm
      simpa using hw
    rcases hD.cases _ hxS with h1 | h1 | h1 | h1
    · exact Or.inl ((hone x).mpr h1)
    · exact Or.inr (Or.inl (key tY h1))
    · exact Or.inr (Or.inr (Or.inl (key vY h1)))
    · exact Or.inr (Or.inr (Or.inr ((key tvY h1).trans (map_mul π tY vY))))
  have htt : t * t = 1 := by rw [← pow_two, h.sq_eq_one]
  have ha2 : π tY * π tY = 1 := by rw [← map_mul, hone]; simp [htY, htt]
  have hb1 : π vY ≠ 1 := fun h1 => hD.v_not_mem ((hone vY).mp h1)
  have hne : π tY ≠ π vY := by
    intro h1
    apply hD.tv_not_mem
    have h2 : π (tY * vY) = 1 := by rw [map_mul, ← h1, ha2]
    simpa [htY, hvY] using (hone _).mp h2
  obtain ⟨yb, hyb, hy1, hy2⟩ := SixNineFour.exists_three_cycle hP4
    (hSbcomm _ ((memS tY).mpr hD.t_mem) _ ((memS vY).mpr hD.v_mem)) ha2 hb1 hne
    ((memS vY).mpr hD.v_mem) hm₁ hm₂ h₁ h₂
  obtain ⟨y, rfl⟩ := hπs yb
  refine ⟨y, mem_inf.mpr ⟨y.2, ?_⟩, ?_, ?_⟩
  · refine mem_normalizer_of_forall_inv_mul_mul_mem fun s hs => ?_
    have h1 : (π y)⁻¹ * π ⟨s, hSY hs⟩ * π y ∈ Sb :=
      (mem_normalizer_iff''.mp hyb _).mp ((memS _).mpr hs)
    rw [← map_inv, ← map_mul, ← map_mul, memS] at h1
    simpa using h1
  · have h1 : π (vY⁻¹ * (y⁻¹ * tY * y)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, hy1, inv_mul_cancel]
    simpa [hvY, htY] using (hone _).mp h1
  · have h1 : π ((tY * vY)⁻¹ * (y⁻¹ * vY * y)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_mul, map_inv, hy2, inv_mul_cancel]
    simpa [hvY, htY] using (hone _).mp h1

theorem isSylowOf_normalizer_inf_centralizer (hU : U3U1Data G L f t T R₂ U₁)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hS : ∃ S : Sylow 2 G, (S : Subgroup G) = U₁ ⊔ T)
    (hC : (U₁ ⊔ T) ⊓ centralizer (R₂ : Set G) ≤ U₁) :
    IsSylowOf 2 U₁ (normalizer (U₁ : Set G) ⊓ centralizer (R₂ : Set G)) := by
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := hS
  have hSN : U₁ ⊔ T ≤ normalizer (U₁ : Set G) :=
    sup_le Subgroup.le_normalizer (hU.le_normalizer h hS2 hR)
  have hSyl : IsSylowOf 2 (U₁ ⊔ T) (normalizer (U₁ : Set G)) := by
    rw [← hS₀]
    exact (SixNineFour.isSylowOf_top S₀).of_le (by rw [hS₀]; exact hSN) le_top
  have hCN : normalizer (U₁ : Set G) ≤
      normalizer ((normalizer (U₁ : Set G) ⊓ centralizer (R₂ : Set G) : Subgroup G) : Set G) := by
    intro g hg
    refine mem_normalizer_iff.mpr fun x => ?_
    have hgR := hU.normalizer_le_normalizer_R₂ hg
    simp only [mem_inf]
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨mul_mem (mul_mem hg hx1) (inv_mem hg), mem_centralizer_iff.mpr fun r hr => ?_⟩
      have hr' : g⁻¹ * r * g ∈ R₂ := (mem_normalizer_iff''.mp hgR r).mp hr
      have := mem_centralizer_iff.mp hx2 _ hr'
      calc r * (g * x * g⁻¹) = g * ((g⁻¹ * r * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * r * g)) * g⁻¹ := by rw [this]
        _ = g * x * g⁻¹ * r := by group
    · rintro ⟨hx1, hx2⟩
      refine ⟨?_, mem_centralizer_iff.mpr fun r hr => ?_⟩
      · have := mul_mem (mul_mem (inv_mem hg) hx1) hg
        simpa [mul_assoc] using this
      · have hr' : g * r * g⁻¹ ∈ R₂ := (mem_normalizer_iff.mp hgR r).mp hr
        have := mem_centralizer_iff.mp hx2 _ hr'
        calc r * x = g⁻¹ * ((g * r * g⁻¹) * (g * x * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * x * g⁻¹) * (g * r * g⁻¹)) * g := by rw [this]
          _ = x * r := by group
  have h1 := hSyl.inf_of_le_normalizer inf_le_left hCN
  have h2 : (U₁ ⊔ T) ⊓ (normalizer (U₁ : Set G) ⊓ centralizer (R₂ : Set G)) = U₁ := by
    refine le_antisymm (fun x hx => hC ?_) (le_inf le_sup_left
      (le_inf Subgroup.le_normalizer hU.le_centralizer))
    obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
    exact mem_inf.mpr ⟨hx1, (mem_inf.mp hx2).2⟩
  rwa [h2] at h1

theorem exists_odd_mem_normalizer_centralizer (hU : U3U1Data G L f t T R₂ U₁)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) :
    ∃ k ∈ L, Odd (orderOf k) ∧ k ∈ normalizer (U₁ : Set G) ∧
      k ∈ normalizer (szT₁ L T : Set G) ∧ k ∈ centralizer (R₂ : Set G) ∧ k * t = t * k ∧
      ∀ y ∈ szT₁ L T, ∃ y' ∈ szT₁ L T, y⁻¹ * (k * y' * k⁻¹ * y'⁻¹) ∈ szA₁ (szT₁ L T) := by
  obtain ⟨hR₁, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  obtain ⟨d, k, hdL, hd⟩ := h.exists_u3RTorus_of_card_sylow hS2
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hd.k_mem
  have hdU : d ∈ normalizer (U₁ : Set G) := by
    refine hU.normalizer_le ?_
    have := hd.mem_normalizer_R₁
    rwa [← hR₁] at this
  have hkL : d ^ j ∈ L := zpow_mem hdL j
  have hkN : d ^ j ∈ normalizer (szT₁ L T : Set G) := zpow_mem hd.mem_normalizer_T₁ j
  have hodd : Odd (orderOf (d ^ j)) := by
    obtain ⟨m, hm⟩ := hd.odd
    have hdvd : orderOf (d ^ j) ∣ orderOf d := orderOf_dvd_of_pow_eq_one (by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
        one_zpow])
    exact Odd.of_dvd_nat hd.odd hdvd
  refine ⟨d ^ j, hkL, hodd, zpow_mem hdU j, hkN,
    h.mem_centralizer_of_mem_borel_of_card_sylow hS2 hR hkL hkN hd.k_centralizer,
    (Commute.zpow_left hd.comm_t j).eq, hd.k_surj⟩

end Certificates

end U3U1Data

end CFSG.SeitzReduction.RankOne

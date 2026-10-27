module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryTransfer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandard
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryCases

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G] [Finite G]

theorem coset_involutions {P : Subgroup G} {x : G} (hxP : x ∈ normalizer (P : Set G))
    (hx2 : x * x = 1) (hcard : Nat.card ↥(P ⊓ centralizer ({x} : Set G)) = 8)
    (hbound : 8 * Nat.card {p : P // (p : G) * x * (p * x) = 1} ≤ Nat.card P) :
    ∀ p ∈ P, p * x * (p * x) = 1 → ∃ r ∈ P, p * x = r⁻¹ * x * r := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set Pf := (P : Set G).toFinset with hPf
  set I := Pf.filter (fun p => p * x * (p * x) = 1) with hI
  set g : G → G := fun r => r⁻¹ * x * r * x⁻¹ with hg
  have hgI : Pf.image g ⊆ I := by
    intro b hb
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hb
    rw [hPf, Set.mem_toFinset, SetLike.mem_coe] at hr
    rw [hI, Finset.mem_filter, hPf, Set.mem_toFinset, SetLike.mem_coe]
    refine ⟨?_, ?_⟩
    · have h1 := (mem_normalizer_iff.mp hxP r).mp hr
      have e : g r = r⁻¹ * (x * r * x⁻¹) := by
        simp only [hg]
        group
      rw [e]
      exact P.mul_mem (P.inv_mem hr) h1
    · simp only [hg]
      calc r⁻¹ * x * r * x⁻¹ * x * (r⁻¹ * x * r * x⁻¹ * x) = r⁻¹ * (x * x) * r := by group
        _ = 1 := by rw [hx2]; group
  have hfib : ∀ b ∈ Pf.image g, (Pf.filter fun a => g a = b).card ≤ 8 := by
    intro b hb
    obtain ⟨r₀, hr₀, rfl⟩ := Finset.mem_image.mp hb
    rw [hPf, Set.mem_toFinset, SetLike.mem_coe] at hr₀
    have hC : ((P ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G).toFinset.card = 8 := by
      rw [← Nat.card_eq_card_toFinset]
      exact hcard
    rw [← hC]
    refine Finset.card_le_card_of_injOn (fun a => a * r₀⁻¹) ?_ ?_
    · intro a ha
      rw [Finset.mem_coe, Finset.mem_filter, hPf, Set.mem_toFinset, SetLike.mem_coe] at ha
      obtain ⟨haP, hga⟩ := ha
      rw [Finset.mem_coe, Set.mem_toFinset, SetLike.mem_coe, mem_inf,
        mem_centralizer_singleton_iff]
      refine ⟨P.mul_mem haP (P.inv_mem hr₀), ?_⟩
      have h1 : a⁻¹ * x * a = r₀⁻¹ * x * r₀ := by
        have := hga
        simp only [hg] at this
        exact mul_right_cancel this
      calc a * r₀⁻¹ * x = a * (r₀⁻¹ * x * r₀) * r₀⁻¹ := by group
        _ = a * (a⁻¹ * x * a) * r₀⁻¹ := by rw [h1]
        _ = x * (a * r₀⁻¹) := by group
    · intro a _ b _ hab
      exact mul_right_cancel hab
  have h1 := Finset.card_le_mul_card_image Pf 8 hfib
  have hPcard : Pf.card = Nat.card P := by
    rw [hPf, ← Nat.card_eq_card_toFinset]
    rfl
  have hIcard : I.card = Nat.card {p : P // (p : G) * x * (p * x) = 1} := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr
      { toFun := fun i => ⟨⟨i.1, by
            have := (Finset.mem_filter.mp i.2).1
            rwa [hPf, Set.mem_toFinset, SetLike.mem_coe] at this⟩,
          (Finset.mem_filter.mp i.2).2⟩
        invFun := fun p => ⟨p.1.1, Finset.mem_filter.mpr ⟨by
            rw [hPf, Set.mem_toFinset, SetLike.mem_coe]
            exact p.1.2, p.2⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hle : I.card ≤ (Pf.image g).card := by
    rw [hIcard]
    rw [← hPcard] at hbound
    omega
  have heq := Finset.eq_of_subset_of_card_le hgI hle
  intro p hp hpx
  have hpI : p ∈ I := by
    rw [hI, Finset.mem_filter, hPf, Set.mem_toFinset, SetLike.mem_coe]
    exact ⟨hp, hpx⟩
  rw [← heq] at hpI
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hpI
  rw [hPf, Set.mem_toFinset, SetLike.mem_coe] at hr
  refine ⟨r, hr, ?_⟩
  simp only [hg]
  group

theorem l34UnitaryCentralizerFact :
    L34UnitaryCentralizerFact := by
  intro G _ _ J P x hJ hL hx hP hxP
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hβ, hT⟩ := exists_standard hJ hL hx hP hxP
  have hxN := hx.1
  have hx2 := hx.2.1
  have hU : IsUSetting q l (betaHat J hxN) := ⟨hqS, hqsurj, hqker, h3, hl, hls, hβ⟩
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  obtain ⟨θ, hθ⟩ := exists_theta hxN hP hxP hT
  obtain ⟨ζ, hζ⟩ := exists_zeta hP hqker
  have hcard8 : Nat.card ↥(P ⊓ centralizer ({x} : Set G)) = 8 := by
    rw [Nat.card_congr θ.toEquiv, hU.card_fixT0]
  have hkerZ : P ⊓ zStarIn J = ⊥ ↔ q.ker = ⊥ := by
    constructor
    · intro hZ
      rw [eq_bot_iff]
      intro e he
      obtain ⟨z, hz⟩ := ζ.surjective ⟨e, he⟩
      have hz1 : (z : G) = 1 := mem_bot.mp ((eq_bot_iff.mp hZ) z.2)
      have h1 : jq J ⟨z, hP.1 z.2.1⟩ = e := (hζ z).symm.trans (congrArg Subtype.val hz)
      rw [mem_bot, ← h1]
      have : (⟨(z : G), hP.1 z.2.1⟩ : J) = 1 := Subtype.ext hz1
      rw [this, map_one]
    · intro hk
      rw [eq_bot_iff]
      intro z hz
      have h2 : jq J ⟨z, hP.1 hz.1⟩ = 1 :=
        (hζ ⟨z, hz⟩).symm.trans (mem_bot.mp ((eq_bot_iff.mp hk) (ζ ⟨z, hz⟩).2))
      exact mem_bot.mpr (eq_one_of_jq_eq_one hP.1 hP2 hz.1 h2)
  refine ⟨fun z hz => ?_, hcard8, ?_, fun hZ => ?_, fun hZ hcyc => ?_, fun hcyc => ?_, ?_, ?_⟩
  ·
    obtain ⟨hzP, hzZ⟩ := mem_inf.mp hz
    have hk : jq J ⟨z, hP.1 hzP⟩ ∈ q.ker := by
      rw [hqker]
      exact (mem_zStarIn_iff _).1 hzZ
    have h1 := hU.beta_ker hk
    rw [betaHat_mk, ← map_inv] at h1
    exact eq_of_jq_eq hP.1 hP2 (conj_mem_of_mem_normalizer hxP hzP) (P.inv_mem hzP) h1
  ·
    rw [card_centralizer_J hxN hx2, hU.card_fixed]
  ·
    obtain ⟨e⟩ := hU.nonempty_fixT0_equiv (hkerZ.1 hZ)
    exact ⟨θ.trans e⟩
  ·
    have hk : q.ker ≠ ⊥ := fun h => hZ (hkerZ.2 h)
    have hcyc' : IsCyclic q.ker := isCyclic_of_surjective ζ.toMonoidHom ζ.surjective
    obtain ⟨-, hcomm, hexp, -⟩ := hU.cyclic_case hk hcyc'
    refine ⟨fun u hu v hv => ?_, ?_⟩
    · have h1 := hcomm _ (θ ⟨u, hu⟩).2 _ (θ ⟨v, hv⟩).2
      have h2 : θ (⟨u, hu⟩ * ⟨v, hv⟩) = θ (⟨v, hv⟩ * ⟨u, hu⟩) := by
        rw [map_mul, map_mul]
        exact Subtype.ext h1
      exact congrArg Subtype.val (θ.injective h2)
    · rw [Monoid.exponent_eq_of_mulEquiv θ, hexp]
  ·
    have hcyc' : ¬ IsCyclic q.ker := fun h =>
      hcyc (isCyclic_of_surjective ζ.symm.toMonoidHom ζ.symm.surjective)
    obtain ⟨-, hsq, -⟩ := hU.noncyclic_case hcyc'
    have hsq' : ∀ u ∈ P ⊓ centralizer ({x} : Set G), u * u = 1 := by
      intro u hu
      have h1 := hsq _ (θ ⟨u, hu⟩).2
      have h2 : θ (⟨u, hu⟩ * ⟨u, hu⟩) = θ 1 := by
        rw [map_mul, map_one]
        exact Subtype.ext h1
      exact congrArg Subtype.val (θ.injective h2)
    refine ⟨fun u hu v hv => ?_, hsq'⟩
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hsq' u hu)
    have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hsq' v hv)
    have huvinv : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right (hsq' _ (mul_mem hu hv))
    calc u * v = (u * v)⁻¹ := huvinv.symm
      _ = v⁻¹ * u⁻¹ := mul_inv_rev u v
      _ = v * u := by rw [huinv, hvinv]
  ·
    by_cases hZ : P ⊓ zStarIn J = ⊥
    · refine ⟨P ⊓ centralizer ({x} : Set G), le_rfl, ?_, ?_⟩
      · rw [hZ, bot_inf_eq, bot_inf_eq]
      · rw [hZ, bot_inf_eq, bot_sup_eq]
    · have hk : q.ker ≠ ⊥ := fun h => hZ (hkerZ.2 h)
      obtain ⟨m, hm, hmo, hcards⟩ : ∃ m ∈ fixT0 q (betaHat J hxN), orderOf (q m) = orderOf m ∧
          ((Nat.card ↥(fixT0 q (betaHat J hxN) ⊓ q.ker) = 2 ∧ orderOf m = 4) ∨
            (Nat.card ↥(fixT0 q (betaHat J hxN) ⊓ q.ker) = 4 ∧ orderOf m = 2)) := by
        by_cases hcyc : IsCyclic q.ker
        · obtain ⟨hK2, -, -, m, hm, hm4, hqm4⟩ := hU.cyclic_case hk hcyc
          exact ⟨m, hm, hqm4.trans hm4.symm, Or.inl ⟨hK2, hm4⟩⟩
        · obtain ⟨hK4, -, m, hm, hm2, hqm2⟩ := hU.noncyclic_case hcyc
          exact ⟨m, hm, hqm2.trans hm2.symm, Or.inr ⟨hK4, hm2⟩⟩
      set y₀ := θ.symm ⟨m, hm⟩ with hy₀
      have hy₀m : jq J ⟨y₀, hP.1 y₀.2.1⟩ = m := by
        rw [← hθ y₀, hy₀, MulEquiv.apply_symm_apply]
      have hoy : orderOf (y₀ : G) = orderOf m := by
        rw [orderOf_coe, ← MulEquiv.orderOf_eq θ y₀, hy₀, MulEquiv.apply_symm_apply, orderOf_mk]
      have hdisj : P ⊓ zStarIn J ⊓ centralizer ({x} : Set G) ⊓ zpowers (y₀ : G) = ⊥ := by
        rw [eq_bot_iff]
        rintro g ⟨⟨⟨hgP, hgZ⟩, -⟩, hgY⟩
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hgY
        have heq : jq J ⟨(y₀ : G) ^ k, hP.1 hgP⟩ = m ^ k := by
          rw [← hy₀m, ← map_zpow]
          rfl
        have hkq : jq J ⟨(y₀ : G) ^ k, hP.1 hgP⟩ ∈ q.ker := by
          rw [hqker]
          exact (mem_zStarIn_iff _).1 hgZ
        rw [heq] at hkq
        have h1 := eq_one_of_mem_zpowers_ker q hmo (zpow_mem (mem_zpowers m) k) hkq
        rw [← heq] at h1
        exact mem_bot.mpr (eq_one_of_jq_eq_one hP.1 hP2 hgP h1)
      refine ⟨zpowers (y₀ : G), (zpowers_le).2 y₀.2, hdisj, ?_⟩
      have hcz := card_CZ hxN hP hxP hqker hT
      refine sup_eq_of_card (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        ((zpowers_le).2 y₀.2) hdisj hcard8 ?_
      rw [hcz, Nat.card_zpowers, hoy]
      exact hcards
  ·
    refine coset_involutions hxP hx2 hcard8 ?_
    have h1 := card_inv_P hxN hx2 hP hT
    have h2 := hU.card_inv_le
    have h3 := card_P hP hT
    rw [hU.card_comap_T0] at h3
    omega

end CFSG.ComponentClassification.GrSLit.L34Facts

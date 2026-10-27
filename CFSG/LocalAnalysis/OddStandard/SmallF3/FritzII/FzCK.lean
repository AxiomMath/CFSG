module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A
public import CFSG.LocalAnalysis.RankTwoShapes.FixedPointFreeThree
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelBasic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRS3C

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G]

theorem fzc_core42_of {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
    (h : FzCCtx G t L S x₁ x₂ lam rho) (hz : ∀ g : G, g * t * g⁻¹ ≠ (x₁ * x₂) ^ 2)
    {X : Subgroup G} (hX : IsPGroup 2 X)
    (hrX : ∀ x ∈ X, rho * x * rho⁻¹ ∈ X) (hlX : ∀ x ∈ X, lam * x * lam⁻¹ ∈ X)
    (hfpf : ∀ x ∈ X, rho * x * rho⁻¹ = x → x = 1) (g : G) :
    g * t * g⁻¹ ∉ X ⊔ zpowers lam := by
  intro hmem
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hctx := h.ctx
  have hlam_ord : orderOf lam = 2 := hctx.wreath.ord_lam
  have hlam2 : lam * lam = 1 := by
    have h1 := pow_orderOf_eq_one lam
    rw [hlam_ord] at h1
    simpa [pow_two] using h1
  have hr3 : rho ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one rho
    rwa [hctx.ord_rho] at h1
  have ht2 : t * t = 1 := S4A.t_mul_self hctx.hyp
  have htne : t ≠ 1 := S4A.t_ne_one hctx.hyp
  have hlN : lam ∈ normalizer (X : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    refine ⟨hlX y, fun hy => ?_⟩
    have h1 := hlX _ hy
    have h2 : lam * (lam * y * lam⁻¹) * lam⁻¹ = y := by
      have hli : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right hlam2
      rw [hli]
      calc lam * (lam * y * lam) * lam = (lam * lam) * y * (lam * lam) := by group
        _ = y := by rw [hlam2]; group
    rwa [h2] at h1
  have hp2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hpne : g * t * g⁻¹ ≠ 1 := fun h1 => htne (by simpa using h1)
  have hzz : ((x₁ * x₂) ^ 2) * ((x₁ * x₂) ^ 2) = 1 := (S4A.z_mul_self_ne_one hctx).1
  rcases CFSG.ComponentClassification.M12Cover.CyclicKernel.mem_or_mul_mem_of_mem_sup_zpowers
      hlN hlam2 hmem with hpX | hpl
  ·
    have hρN : rho ∈ normalizer (X : Set G) := by
      rw [mem_normalizer_iff]
      intro y
      refine ⟨hrX y, fun hy => ?_⟩
      have h1 := hrX _ (hrX _ hy)
      have h3 : rho * (rho * rho) = 1 := by rw [← pow_three]; exact hr3
      have h2 : rho * (rho * (rho * y * rho⁻¹) * rho⁻¹) * rho⁻¹ = y := by
        calc rho * (rho * (rho * y * rho⁻¹) * rho⁻¹) * rho⁻¹
            = (rho * (rho * rho)) * y * (rho * (rho * rho))⁻¹ := by
              simp only [mul_inv_rev, mul_assoc]
          _ = y := by rw [h3]; simp
      rwa [h2] at h1
    let α : MulAut X := X.normalizerMonoidHom ⟨rho, hρN⟩
    have hα : ∀ x : X, ((α x : X) : G) = rho * x * rho⁻¹ := fun x =>
      Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨rho, hρN⟩ x
    have hα3 : α ^ 3 = 1 := by
      have h1 : (⟨rho, hρN⟩ : normalizer (X : Set G)) ^ 3 = 1 := by
        apply Subtype.ext
        simpa using hr3
      calc α ^ 3 = X.normalizerMonoidHom ((⟨rho, hρN⟩ : normalizer (X : Set G)) ^ 3) := by
            rw [map_pow]
        _ = 1 := by rw [h1, map_one]
    have hfp : ∀ x : X, α x = x → x = 1 := by
      intro x hx
      apply Subtype.ext
      have h1 : rho * (x : G) * rho⁻¹ = x := by rw [← hα x]; exact congrArg Subtype.val hx
      simpa using hfpf x x.2 h1
    obtain ⟨-, -, -, hcomm, hnorm⟩ :=
      CFSG.RankTwoShapes.fixedPointFree_three_class_two α hα3 hfp
    let p' : X := ⟨g * t * g⁻¹, hpX⟩
    have hc1 := congrArg Subtype.val (hcomm p')
    have hn1 := congrArg Subtype.val (hnorm p')
    obtain ⟨u, hu⟩ : ∃ u : G, u = rho * (g * t * g⁻¹) * rho⁻¹ := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : G, v = rho * u * rho⁻¹ := ⟨_, rfl⟩
    have hu1 : ((α p' : X) : G) = u := by rw [hα, hu]
    have hv1 : ((α (α p') : X) : G) = v := by rw [hα, hu1, hv]
    have hcomm' : (g * t * g⁻¹) * u = u * (g * t * g⁻¹) := by
      have h3 : (g * t * g⁻¹)⁻¹ * u⁻¹ * (g * t * g⁻¹) * u = 1 := by
        simpa [CFSG.RankTwoShapes.rcomm_def, hu1, p'] using hc1
      calc (g * t * g⁻¹) * u
          = (u * (g * t * g⁻¹)) * ((g * t * g⁻¹)⁻¹ * u⁻¹ * (g * t * g⁻¹) * u) := by group
        _ = u * (g * t * g⁻¹) := by rw [h3, mul_one]
    have hn2 : (g * t * g⁻¹) * u * v = 1 := by
      simpa [hu1, hv1, p'] using hn1
    have hup : u ≠ g * t * g⁻¹ := by
      intro h1
      have h2 := hfp p' (Subtype.ext (by rw [hu1]; exact h1))
      exact hpne (by simpa [p'] using congrArg Subtype.val h2)
    have hu2 : u * u = 1 := by
      rw [hu]
      calc rho * (g * t * g⁻¹) * rho⁻¹ * (rho * (g * t * g⁻¹) * rho⁻¹)
          = rho * ((g * t * g⁻¹) * (g * t * g⁻¹)) * rho⁻¹ := by group
        _ = 1 := by rw [hp2]; group
    have hune : u ≠ 1 := by
      intro h1
      rw [hu] at h1
      exact hpne (by simpa using h1)
    have hqc : t * (g⁻¹ * u * g) = (g⁻¹ * u * g) * t := by
      calc t * (g⁻¹ * u * g) = g⁻¹ * ((g * t * g⁻¹) * u) * g := by group
        _ = g⁻¹ * (u * (g * t * g⁻¹)) * g := by rw [hcomm']
        _ = (g⁻¹ * u * g) * t := by group
    have hq_cent : g⁻¹ * u * g ∈ invCent t :=
      Subgroup.mem_centralizer_iff.mpr fun m hm => by
        rw [Set.mem_singleton_iff.mp hm]; exact hqc
    have hqPL : g⁻¹ * u * g ∈ twoCore t ⊔ L := by rw [← h.eq_PL]; exact hq_cent
    have hq2 : (g⁻¹ * u * g) * (g⁻¹ * u * g) = 1 := by
      calc (g⁻¹ * u * g) * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g := by group
        _ = 1 := by rw [hu2]; group
    have hq1 : g⁻¹ * u * g ≠ 1 := fun h1 => hune (by
      calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group)
    obtain ⟨h', hh', hcase⟩ := hctx.invol_PL _ hqPL hq2 hq1
    have hh'c : t * h' = h' * t := Subgroup.mem_centralizer_iff.mp hh' t (Set.mem_singleton t)
    have hconj_t : h'⁻¹ * t * h' = t := by
      calc h'⁻¹ * t * h' = h'⁻¹ * (t * h') := by group
        _ = h'⁻¹ * (h' * t) := by rw [hh'c]
        _ = t := by group
    rcases hcase with ha | hb | hc3
    ·
      have hqt : g⁻¹ * u * g = t := by
        calc g⁻¹ * u * g = h'⁻¹ * (h' * (g⁻¹ * u * g) * h'⁻¹) * h' := by group
          _ = h'⁻¹ * t * h' := by rw [ha]
          _ = t := hconj_t
      exact hup (by calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
                         _ = g * t * g⁻¹ := by rw [hqt])
    · refine hz (h' * g⁻¹ * rho * g) ?_
      calc h' * g⁻¹ * rho * g * t * (h' * g⁻¹ * rho * g)⁻¹
          = h' * (g⁻¹ * (rho * (g * t * g⁻¹) * rho⁻¹) * g) * h'⁻¹ := by group
        _ = h' * (g⁻¹ * u * g) * h'⁻¹ := by rw [hu]
        _ = (x₁ * x₂) ^ 2 := hb
    · have hq_eq : g⁻¹ * u * g = t * (h'⁻¹ * (x₁ * x₂) ^ 2 * h') := by
        calc g⁻¹ * u * g = h'⁻¹ * (h' * (g⁻¹ * u * g) * h'⁻¹) * h' := by group
          _ = h'⁻¹ * (t * (x₁ * x₂) ^ 2) * h' := by rw [hc3]
          _ = (h'⁻¹ * t * h') * (h'⁻¹ * (x₁ * x₂) ^ 2 * h') := by group
          _ = t * (h'⁻¹ * (x₁ * x₂) ^ 2 * h') := by rw [hconj_t]
      have hu_eq : u = (g * t * g⁻¹) *
          ((g * h'⁻¹) * (x₁ * x₂) ^ 2 * (g * h'⁻¹)⁻¹) := by
        calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
          _ = g * (t * (h'⁻¹ * (x₁ * x₂) ^ 2 * h')) * g⁻¹ := by rw [hq_eq]
          _ = _ := by group
      have h5 : ((g * h'⁻¹) * (x₁ * x₂) ^ 2 * (g * h'⁻¹)⁻¹) * v = 1 := by
        calc ((g * h'⁻¹) * (x₁ * x₂) ^ 2 * (g * h'⁻¹)⁻¹) * v
            = ((g * t * g⁻¹) * (g * t * g⁻¹)) *
              ((g * h'⁻¹) * (x₁ * x₂) ^ 2 * (g * h'⁻¹)⁻¹) * v := by rw [hp2]; group
          _ = (g * t * g⁻¹) * ((g * t * g⁻¹) *
              ((g * h'⁻¹) * (x₁ * x₂) ^ 2 * (g * h'⁻¹)⁻¹)) * v := by group
          _ = (g * t * g⁻¹) * u * v := by rw [← hu_eq]
          _ = 1 := hn2
      have hv_eq : v = (g * h'⁻¹) * (x₁ * x₂) ^ 2 * (g * h'⁻¹)⁻¹ := by
        have h6 := eq_inv_of_mul_eq_one_right h5
        have hzi : ((x₁ * x₂) ^ 2)⁻¹ = (x₁ * x₂) ^ 2 := inv_eq_of_mul_eq_one_right hzz
        rw [h6]
        calc ((g * h'⁻¹) * (x₁ * x₂) ^ 2 * (g * h'⁻¹)⁻¹)⁻¹
            = (g * h'⁻¹) * ((x₁ * x₂) ^ 2)⁻¹ * (g * h'⁻¹)⁻¹ := by group
          _ = _ := by rw [hzi]
      refine hz (h' * g⁻¹ * rho * rho * g) ?_
      calc h' * g⁻¹ * rho * rho * g * t * (h' * g⁻¹ * rho * rho * g)⁻¹
          = (g * h'⁻¹)⁻¹ * (rho * (rho * (g * t * g⁻¹) * rho⁻¹) * rho⁻¹) * (g * h'⁻¹) := by
            group
        _ = (g * h'⁻¹)⁻¹ * v * (g * h'⁻¹) := by rw [hv, hu]
        _ = (x₁ * x₂) ^ 2 := by rw [hv_eq]; group
  ·
    have hp_ord : orderOf (g * t * g⁻¹) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hp2) hpne
    have hpll : g * t * g⁻¹ * lam * lam = g * t * g⁻¹ := by
      rw [mul_assoc _ lam lam, hlam2, mul_one]
    have hlr : lam * rho * lam⁻¹ = rho⁻¹ := hctx.lam_rho
    obtain ⟨w, hwX, hw⟩ := fzr_conj_of_invol_mul hX hrX hlX hr3 hlam_ord hlr hfpf hpl
      (by rw [hpll]; exact hp_ord)
    have hlamL : lam ∈ L := by
      have h1 : lam ∈ S ⊓ L := by
        rw [hctx.inf_eq]
        exact Subgroup.subset_closure (by simp)
      exact h1.2
    have hlam_ne : lam ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hlam_ord; omega
    obtain ⟨c, -, hc⟩ := hctx.invol_L lam hlamL hlam2 hlam_ne
    refine hz (c⁻¹ * w⁻¹ * g) ?_
    have hw' : w * lam * w⁻¹ = g * t * g⁻¹ := by rw [hw, hpll]
    calc c⁻¹ * w⁻¹ * g * t * (c⁻¹ * w⁻¹ * g)⁻¹
        = c⁻¹ * w⁻¹ * (g * t * g⁻¹) * w * c := by group
      _ = c⁻¹ * w⁻¹ * (w * lam * w⁻¹) * w * c := by rw [hw']
      _ = c⁻¹ * lam * c := by group
      _ = c⁻¹ * (c * (x₁ * x₂) ^ 2 * c⁻¹) * c := by rw [hc]
      _ = (x₁ * x₂) ^ 2 := by group

end CFSG.OddStandard.SmallF3.FritzII

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.FixedSpace
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.CenterCentral

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.RankThree.Literature.FSmith

variable {C : Type} [Group C] [Finite C] {Q : Subgroup C} [Q.Normal]

private lemma neg_eq_self_of_zmod_two {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (v : V) :
    -v = v := by
  have h : (2 : ZMod 2) • v = 0 := by
    rw [show (2 : ZMod 2) = 0 from by decide, zero_smul]
  rw [two_smul] at h
  exact neg_eq_of_add_eq_zero_right h

theorem AschbacherHyp.exists_conj_of_sq_mem_centerOf (hC : AschbacherHyp C Q) {τ₁ τ₂ : C}
    (h₁ : τ₁ ∉ commutator C) (h₂ : τ₂ ∉ commutator C) (h₁2 : τ₁ ^ 2 ∈ centerOf Q)
    (h₂2 : τ₂ ^ 2 ∈ centerOf Q) : ∃ g : C, ∃ z ∈ centerOf Q, g * τ₁ * g⁻¹ = τ₂ * z := by
  have hE : IsExtraspecialPGroup 2 ↥Q := hC.plus.isExtraspecialPGroup
  haveI : Finite ↥Q := hC.plus.finite
  letI : Module (ZMod 2) (Additive (Abelianization ↥Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hE
  have hQn : Q.Normal := inferInstance
  have hQcomm : Q ≤ commutator C := hC.le_commutator
  obtain ⟨e⟩ := hC.quotient
  let mk : C →* C ⧸ Q := QuotientGroup.mk' Q
  let f : C →* A5WrTwo := e.toMonoidHom.comp mk
  have hmap_mk : (commutator C).map mk = commutator (C ⧸ Q) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective mk (QuotientGroup.mk'_surjective Q)]
    exact (commutator_def (C ⧸ Q)).symm
  have hmap_e : (commutator (C ⧸ Q)).map e.toMonoidHom = commutator A5WrTwo := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective e.toMonoidHom e.surjective]
    exact (commutator_def A5WrTwo).symm
  have hmapf : (commutator C).map f = commutator A5WrTwo := by
    have h := Subgroup.map_map (commutator C) e.toMonoidHom mk
    rw [hmap_mk, hmap_e] at h
    change (commutator C).map (e.toMonoidHom.comp mk) = commutator A5WrTwo
    exact h.symm
  have hker : f.ker = Q := by
    ext x
    rw [MonoidHom.mem_ker, ← QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      have : e (mk x) = e 1 := by simpa [f] using hx
      have hmk : mk x = 1 := e.injective this
      simpa [mk] using hmk
    · intro hx
      have hmk : mk x = 1 := by simpa [mk] using hx
      change e (mk x) = 1
      rw [hmk, map_one]
  have hmem : ∀ τ : C, f τ ∈ commutator A5WrTwo ↔ τ ∈ commutator C := by
    intro τ
    constructor
    · intro hτ
      rw [← hmapf] at hτ
      obtain ⟨c, hc, hcf⟩ := Subgroup.mem_map.mp hτ
      have hcτ : c⁻¹ * τ ∈ Q := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hcf]
        group
      have := (commutator C).mul_mem hc (hQcomm hcτ)
      convert this using 1
      group
    · intro hτ
      rw [← hmapf]
      exact Subgroup.mem_map_of_mem f hτ
  have hu : f τ₁ ∉ commutator A5WrTwo := fun h => h₁ ((hmem τ₁).mp h)
  have hv : f τ₂ ∉ commutator A5WrTwo := fun h => h₂ ((hmem τ₂).mp h)
  have h1Q : τ₁ ^ 2 ∈ Q := (Subgroup.mem_inf.mp h₁2).1
  have h2Q : τ₂ ^ 2 ∈ Q := (Subgroup.mem_inf.mp h₂2).1
  have hu2 : (f τ₁) ^ 2 = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.mp (by rw [hker]; exact h1Q)
  have hv2 : (f τ₂) ^ 2 = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.mp (by rw [hker]; exact h2Q)
  obtain ⟨b, hb, hbu⟩ := A5WrTwo.exists_conj_of_outer_involutions hu hv hu2 hv2
  have hbK : e.symm b ∈ commutator (C ⧸ Q) := by
    have hbmap : b ∈ (commutator (C ⧸ Q)).map e.toMonoidHom := by rw [hmap_e]; exact hb
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp hbmap
    have : c = e.symm b := by
      have h := congrArg (fun y => e.symm y) hce
      simpa using h
    rwa [this] at hc
  obtain ⟨g₀, hg₀, hg₀b⟩ :=
    Subgroup.mem_map.mp (show e.symm b ∈ (commutator C).map mk by rw [hmap_mk]; exact hbK)
  have hfg : f g₀ = b := by
    change e (mk g₀) = b
    rw [hg₀b]
    simp
  set τ : C := g₀ * τ₁ * g₀⁻¹ with hτdef
  have hmkeq : mk τ = mk τ₂ := by
    rw [hτdef]
    apply e.injective
    calc e (mk (g₀ * τ₁ * g₀⁻¹)) = f (g₀ * τ₁ * g₀⁻¹) := rfl
      _ = f g₀ * f τ₁ * (f g₀)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = b * f τ₁ * b⁻¹ := by rw [hfg]
      _ = f τ₂ := hbu
      _ = e (mk τ₂) := rfl
  have hτ : τ ∉ commutator C := by
    intro hτmem
    apply h₁
    have hconj : g₀⁻¹ * (g₀ * τ₁ * g₀⁻¹) * g₀ ∈ commutator C := by
      simpa [hτdef] using (inferInstance : (commutator C).Normal).conj_mem τ hτmem g₀⁻¹
    have hval : g₀⁻¹ * (g₀ * τ₁ * g₀⁻¹) * g₀ = τ₁ := by group
    rwa [hval] at hconj
  have hτ2 : τ ^ 2 ∈ centerOf Q := by
    rw [hτdef]
    have hcen := hC.centerOf_le_center h₁2
    rw [Subgroup.mem_center_iff] at hcen
    have hg : g₀ * τ₁ ^ 2 = τ₁ ^ 2 * g₀ := hcen g₀
    have hval : (g₀ * τ₁ * g₀⁻¹) ^ 2 = τ₁ ^ 2 := by
      calc (g₀ * τ₁ * g₀⁻¹) ^ 2
          = g₀ * τ₁ ^ 2 * g₀⁻¹ := by rw [pow_two, pow_two]; group
        _ = τ₁ ^ 2 := by rw [hg]; group
    rwa [hval]
  let x : C := τ⁻¹ * τ₂
  have hfτ : f τ = f τ₂ := by
    change e (mk τ) = e (mk τ₂)
    rw [hmkeq]
  have hxQ : x ∈ Q := by
    rw [← hker, MonoidHom.mem_ker]
    change f (τ⁻¹ * τ₂) = 1
    rw [map_mul, map_inv, hfτ]
    group
  let xQ : Q := ⟨x, hxQ⟩
  have hcC : τ⁻¹ * x * τ * x ∈ centerOf Q := by
    have hτ₂x : τ₂ = τ * x := by
      change τ₂ = τ * (τ⁻¹ * τ₂)
      group
    have hτ₂sq : τ₂ ^ 2 = τ ^ 2 * (τ⁻¹ * x * τ * x) := by
      rw [hτ₂x, pow_two, pow_two]
      group
    rw [hτ₂sq] at h₂2
    have := (centerOf Q).mul_mem ((centerOf Q).inv_mem hτ2) h₂2
    simpa [mul_assoc] using this
  have hc_center : (conjAut hQn τ⁻¹ xQ * xQ : Q) ∈ Subgroup.center Q := by
    rw [← mem_centerOf_iff]
    have hval : ((conjAut hQn τ⁻¹ xQ * xQ : Q) : C) = τ⁻¹ * x * τ * x := by
      rw [Subgroup.coe_mul, conjAut_apply]
      change τ⁻¹ * x * (τ⁻¹)⁻¹ * x = τ⁻¹ * x * τ * x
      group
    rw [hval]
    exact hcC
  have hpi0 : Additive.ofMul (Abelianization.of (conjAut hQn τ⁻¹ xQ * xQ)) = 0 :=
    (ofMul_of_eq_zero_iff hE _).mpr hc_center
  have hsum : conjLinEquiv hQn τ⁻¹ (Additive.ofMul (Abelianization.of xQ)) +
      Additive.ofMul (Abelianization.of xQ) = 0 := by
    have h1 := ofMul_of_mul (conjAut hQn τ⁻¹ xQ) xQ
    rw [hpi0] at h1
    rw [← conjLinEquiv_apply hQn τ⁻¹ xQ] at h1
    exact h1.symm
  have hτ2Q : τ ^ 2 ∈ Q := (Subgroup.mem_inf.mp hτ2).1
  have hρτ2 : conjLinEquiv hQn (τ ^ 2) = 1 :=
    conjLinEquiv_eq_one_of_mem (hQn := hQn) hτ2Q
  have hρsq : conjLinEquiv hQn τ * conjLinEquiv hQn τ = 1 := by
    rw [← pow_two, ← map_pow, hρτ2]
  have hρinv : conjLinEquiv hQn τ⁻¹ = conjLinEquiv hQn τ := by
    rw [map_inv]
    exact inv_eq_of_mul_eq_one_right hρsq
  have hfix : conjLinEquiv hQn τ (Additive.ofMul (Abelianization.of xQ)) =
      Additive.ofMul (Abelianization.of xQ) := by
    have hA : conjLinEquiv hQn τ (Additive.ofMul (Abelianization.of xQ)) +
        Additive.ofMul (Abelianization.of xQ) = 0 := by
      simpa [hρinv] using hsum
    have hxx : Additive.ofMul (Abelianization.of xQ) +
        Additive.ofMul (Abelianization.of xQ) = 0 := by
      have ht : (2 : ZMod 2) • (Additive.ofMul (Abelianization.of xQ)) = 0 := by
        rw [show (2 : ZMod 2) = 0 from by decide, zero_smul]
      simpa [two_smul] using ht
    calc conjLinEquiv hQn τ (Additive.ofMul (Abelianization.of xQ))
        = conjLinEquiv hQn τ (Additive.ofMul (Abelianization.of xQ)) + 0 := (add_zero _).symm
      _ = conjLinEquiv hQn τ (Additive.ofMul (Abelianization.of xQ)) +
            (Additive.ofMul (Abelianization.of xQ) +
              Additive.ofMul (Abelianization.of xQ)) := by rw [hxx]
      _ = (conjLinEquiv hQn τ (Additive.ofMul (Abelianization.of xQ)) +
            Additive.ofMul (Abelianization.of xQ)) +
              Additive.ofMul (Abelianization.of xQ) := by abel
      _ = 0 + Additive.ofMul (Abelianization.of xQ) := by rw [hA]
      _ = Additive.ofMul (Abelianization.of xQ) := zero_add _
  obtain ⟨y, hy⟩ := AschbacherHyp.exists_eq_add_of_fixed hC hτ hτ2
    (Additive.ofMul (Abelianization.of xQ)) hfix
  obtain ⟨yQ, hyQ⟩ := exists_ofMul_of y
  let w : Q := conjAut hQn τ⁻¹ yQ * yQ⁻¹
  have hpiw : Additive.ofMul (Abelianization.of w) =
      Additive.ofMul (Abelianization.of xQ) := by
    have h1 := ofMul_of_mul (conjAut hQn τ⁻¹ yQ) (yQ⁻¹)
    rw [← conjLinEquiv_apply hQn τ⁻¹ yQ] at h1
    rw [hρinv] at h1
    rw [map_inv, ofMul_inv] at h1
    rw [hyQ] at h1
    rw [neg_eq_self_of_zmod_two y] at h1
    rw [add_comm] at h1
    have hy' : Additive.ofMul (Abelianization.of xQ) = y + conjLinEquiv hQn τ y := hy
    exact h1.trans hy'.symm
  let z₀ : Q := w * xQ⁻¹
  have hz0_center : z₀ ∈ Subgroup.center Q := by
    change w * xQ⁻¹ ∈ Subgroup.center Q
    rw [← ofMul_of_eq_zero_iff hE, ofMul_of_mul, hpiw, map_inv, ofMul_inv, add_neg_cancel]
  have hz0_centerOf : (z₀ : C) ∈ centerOf Q := (mem_centerOf_iff z₀).mpr hz0_center
  have hw_eq : w = z₀ * xQ := by
    change w = (w * xQ⁻¹) * xQ
    group
  refine ⟨(yQ : C) * g₀, (z₀ : C), hz0_centerOf, ?_⟩
  have hz0c : (z₀ : C) ∈ Subgroup.center C := hC.centerOf_le_center hz0_centerOf
  rw [Subgroup.mem_center_iff] at hz0c
  have hwC : (w : C) = τ⁻¹ * (yQ : C) * τ * (yQ : C)⁻¹ := by
    change ((conjAut hQn τ⁻¹ yQ * yQ⁻¹ : Q) : C) = τ⁻¹ * (yQ : C) * τ * (yQ : C)⁻¹
    rw [Subgroup.coe_mul, conjAut_apply, Subgroup.coe_inv]
    group
  have hmain : (yQ : C) * τ * (yQ : C)⁻¹ = τ₂ * (z₀ : C) := by
    have h1 : (yQ : C) * τ * (yQ : C)⁻¹ = τ * (w : C) := by
      rw [hwC]
      group
    rw [h1]
    have h2 : (w : C) = (z₀ : C) * x := by
      have hh := congrArg Subtype.val hw_eq
      simpa [Subgroup.coe_mul] using hh
    rw [h2]
    have hτ₂x : τ₂ = τ * x := by
      change τ₂ = τ * (τ⁻¹ * τ₂)
      group
    rw [hτ₂x, ← hz0c x]
    group
  calc ((yQ : C) * g₀) * τ₁ * ((yQ : C) * g₀)⁻¹
      = (yQ : C) * (g₀ * τ₁ * g₀⁻¹) * (yQ : C)⁻¹ := by group
    _ = (yQ : C) * τ * (yQ : C)⁻¹ := by rw [← hτdef]
    _ = τ₂ * (z₀ : C) := hmain

end CFSG.EvenSporadicStandard.HNRecog

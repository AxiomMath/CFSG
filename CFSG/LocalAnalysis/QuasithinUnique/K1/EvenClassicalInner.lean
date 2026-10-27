module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.RankOneRecog

theorem exists_witness_of_normal {Ñ : Type} [Group Ñ] [Finite Ñ] (Lb R Ub : Subgroup Ñ)
    [Lb.Normal] (hR : IsSylowTwoOf R ⊤) (hUR : Ub ≤ R) (hUe : IsElemAbelian 2 Ub)
    (hcl : ∀ a ∈ Ub, ∀ g : Ñ, g⁻¹ * a * g ∈ R → g⁻¹ * a * g ∈ Ub)
    {u : Ñ} (hu : u ∈ Ub) (huL : u ∈ Lb) (hu1 : u ≠ 1) :
    ∃ P A : Subgroup Lb, StronglyClosedWitness Lb P A ∧ A ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hi⟩ := isSylowTwoOf_top_iff.mp hR
  let RS : Sylow 2 Ñ := hp.toSylow hi
  obtain ⟨P', hP'⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal RS Lb
  have hRS : (RS : Subgroup Ñ) = R := rfl
  rw [hRS] at hP'
  have hmemP : ∀ x : Lb, x ∈ (P' : Subgroup Lb) ↔ (x : Ñ) ∈ R := by
    intro x
    constructor
    · intro hx
      have : (x : Ñ) ∈ (P' : Subgroup Lb).map Lb.subtype := ⟨x, hx, rfl⟩
      rw [hP'] at this
      exact this.1
    · intro hx
      have : (x : Ñ) ∈ (P' : Subgroup Lb).map Lb.subtype := by
        rw [hP']
        exact ⟨hx, x.2⟩
      obtain ⟨y, hy, hyx⟩ := this
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
  refine ⟨(P' : Subgroup Lb), (Ub ⊓ Lb).subgroupOf Lb, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact isSylowTwoOf_top_iff.mpr ⟨P'.isPGroup', P'.not_dvd_index⟩
  · intro x hx
    exact (hmemP x).mpr (hUR (Subgroup.mem_subgroupOf.mp hx).1)
  · exact isElemAbelian_subgroupOf (isElemAbelian_mono inf_le_left hUe)
  · intro a ha g hg
    have ha' : (a : Ñ) ∈ Ub ⊓ Lb := Subgroup.mem_subgroupOf.mp ha
    have hgR : (g : Ñ)⁻¹ * (a : Ñ) * (g : Ñ) ∈ R := (hmemP _).mp hg
    have h1 := hcl (a : Ñ) ha'.1 (g : Ñ) hgR
    exact Subgroup.mem_subgroupOf.mpr ⟨h1, (g⁻¹ * a * g : Lb).2⟩
  · intro hbot
    have hu' : (⟨u, huL⟩ : Lb) ∈ (Ub ⊓ Lb).subgroupOf Lb := Subgroup.mem_subgroupOf.mpr ⟨hu, huL⟩
    rw [hbot, Subgroup.mem_bot] at hu'
    exact hu1 (congrArg Subtype.val hu')

theorem exists_stronglyClosedWitness_of_inner_action {G : Type} [Group G] [Finite G]
    {H S U L : Subgroup G} (hS : IsSylowTwoOf S H) (hUS : U ≤ S) (hU : IsElemAbelian 2 U)
    (hcl : ∀ a ∈ U, ∀ g ∈ H, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ U) (hLH : L ≤ H)
    (hUL : U ≤ Subgroup.normalizer (L : Set G)) {w : G} (hw : w ∈ U)
    (hinner : ∃ x ∈ L, ∀ y ∈ L, w⁻¹ * y * w = x⁻¹ * y * x)
    (hnc : ¬ L ≤ Subgroup.centralizer ({w} : Set G)) :
    ∃ P A : Subgroup (L ⧸ Subgroup.center L),
      StronglyClosedWitness (L ⧸ Subgroup.center L) P A ∧ A ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G := H ⊓ Subgroup.normalizer (L : Set G)
  have hNH : N ≤ H := inf_le_left
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hLN : L ≤ N := le_inf hLH Subgroup.le_normalizer
  have hUN : U ≤ N := le_inf (hUS.trans hS.1) hUL
  have hU2 : IsPGroup 2 U := fun x => ⟨1, Subtype.ext (by simpa using hU.2 x x.2)⟩
  obtain ⟨R, hR, hUR⟩ := EscapingLocal.exists_isSylowTwoOf_ge hUN hU2
  obtain ⟨S₁, hS₁, hRS₁⟩ := EscapingLocal.exists_isSylowTwoOf_ge (hR.1.trans hNH) hR.2.1
  have hcl₁ := stronglyClosed_of_le_pGroup hS hS₁.1 hS₁.2.1 (hUR.trans hRS₁) hcl
  have hclR : ∀ a ∈ U, ∀ g ∈ N, g⁻¹ * a * g ∈ R → g⁻¹ * a * g ∈ U := fun a ha g hg hgR =>
    hcl₁ a ha g (hNH hg) (hRS₁ hgR)
  let C : Subgroup N := (Subgroup.centralizer (L : Set G)).subgroupOf N
  have hCmem : ∀ n : N, n ∈ C ↔ ∀ y ∈ L, y * (n : G) = (n : G) * y := fun n => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    exact Iff.rfl
  have hCn : C.Normal := by
    refine ⟨fun c hc n => ?_⟩
    rw [hCmem] at hc ⊢
    intro y hy
    have hn : (n : G) ∈ Subgroup.normalizer (L : Set G) := hNL n.2
    have hy' : (n : G)⁻¹ * y * (n : G) ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (L : Set G)).inv_mem hn) y).mp hy
      simpa using this
    have h1 := hc _ hy'
    change y * ((n : G) * (c : G) * (n : G)⁻¹) = ((n : G) * (c : G) * (n : G)⁻¹) * y
    calc y * ((n : G) * (c : G) * (n : G)⁻¹)
        = (n : G) * (((n : G)⁻¹ * y * (n : G)) * (c : G)) * (n : G)⁻¹ := by group
      _ = (n : G) * ((c : G) * ((n : G)⁻¹ * y * (n : G))) * (n : G)⁻¹ := by rw [h1]
      _ = ((n : G) * (c : G) * (n : G)⁻¹) * y := by group
  let π : N →* N ⧸ C := QuotientGroup.mk' C
  obtain ⟨R', hR'⟩ := isSylowTwoOf_iff_exists.mp hR
  have hU'R' : U.subgroupOf N ≤ (R' : Subgroup N) := subgroupOf_le_of_map_eq hR' hUR
  obtain ⟨Rbar, hRbar, hclbar⟩ := CFSG.ShultStronglyClosedTI.quotient_stronglyClosed R'
    (U.subgroupOf N) C hU'R' (stronglyClosed_subgroupOf hR' hclR)
  let φ : L →* N ⧸ C := π.comp (Subgroup.inclusion hLN)
  have hφker : φ.ker = Subgroup.center L := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    change π (Subgroup.inclusion hLN y) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hCmem]
    constructor
    · intro h z
      exact Subtype.ext (h (z : G) z.2)
    · intro h z hz
      exact congrArg Subtype.val (h ⟨z, hz⟩)
  let Lbar : Subgroup (N ⧸ C) := φ.range
  have hLbarN : Lbar.Normal := by
    refine ⟨fun x hx n => ?_⟩
    obtain ⟨n', rfl⟩ := QuotientGroup.mk_surjective n
    obtain ⟨x', rfl⟩ := hx
    have hn : (n' : G) ∈ Subgroup.normalizer (L : Set G) := hNL n'.2
    have hnx : (n' : G) * (x' : G) * (n' : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hn x').mp x'.2
    refine ⟨⟨_, hnx⟩, ?_⟩
    have e : Subgroup.inclusion hLN ⟨(n' : G) * (x' : G) * (n' : G)⁻¹, hnx⟩ =
        n' * Subgroup.inclusion hLN x' * n'⁻¹ := Subtype.ext rfl
    show π (Subgroup.inclusion hLN ⟨_, hnx⟩) = _
    rw [e, map_mul, map_mul, map_inv]
    rfl
  let Ubar : Subgroup (N ⧸ C) := (U.subgroupOf N).map π
  have hRbar' : (Rbar : Subgroup (N ⧸ C)) = (R' : Subgroup N).map π := hRbar
  have hUbar_le : Ubar ≤ (Rbar : Subgroup (N ⧸ C)) := by
    rw [hRbar']
    exact Subgroup.map_mono hU'R'
  have hSbar : IsSylowTwoOf (Rbar : Subgroup (N ⧸ C)) ⊤ :=
    isSylowTwoOf_top_iff.mpr ⟨Rbar.isPGroup', Rbar.not_dvd_index⟩
  obtain ⟨x, hxL, hx⟩ := hinner
  have hwN : w ∈ N := hUN hw
  let u' : N := ⟨w, hwN⟩
  have hu'Ubar : π u' ∈ Ubar := Subgroup.mem_map_of_mem π (show u' ∈ U.subgroupOf N from hw)
  have hxN : x ∈ N := hLN hxL
  have hcx : (⟨w * x⁻¹, N.mul_mem hwN (N.inv_mem hxN)⟩ : N) ∈ C := by
    rw [hCmem]
    intro y hy
    have h1 := hx y hy
    change y * (w * x⁻¹) = (w * x⁻¹) * y
    calc y * (w * x⁻¹) = w * (w⁻¹ * y * w) * x⁻¹ := by group
      _ = w * (x⁻¹ * y * x) * x⁻¹ := by rw [h1]
      _ = (w * x⁻¹) * y := by group
  have hu'L : π u' ∈ Lbar := by
    refine ⟨⟨x, hxL⟩, ?_⟩
    have e : u' = ⟨w * x⁻¹, N.mul_mem hwN (N.inv_mem hxN)⟩ * Subgroup.inclusion hLN ⟨x, hxL⟩ :=
      Subtype.ext (by simp [u', Subgroup.inclusion])
    have h1 : π ⟨w * x⁻¹, N.mul_mem hwN (N.inv_mem hxN)⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hcx
    change π (Subgroup.inclusion hLN ⟨x, hxL⟩) = π u'
    rw [e, map_mul, h1, one_mul]
  have hu'1 : π u' ≠ 1 := by
    intro h
    have hu'C : u' ∈ C := (QuotientGroup.eq_one_iff u').mp h
    rw [hCmem] at hu'C
    apply hnc
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hu'C y hy
  have := hLbarN
  obtain ⟨P, A, hW, hA⟩ := exists_witness_of_normal Lbar (Rbar : Subgroup (N ⧸ C)) Ubar hSbar
    hUbar_le (isElemAbelian_map (isElemAbelian_subgroupOf hU) π)
    (fun a ha g hg => hclbar a ha g hg) hu'Ubar hu'L hu'1
  let e₀ : L ⧸ Subgroup.center L ≃* Lbar :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans (QuotientGroup.quotientKerEquivRange φ)
  refine ⟨P.map e₀.symm.toMonoidHom, A.map e₀.symm.toMonoidHom, hW.map e₀.symm, ?_⟩
  intro hbot
  exact hA ((Subgroup.map_eq_bot_iff_of_injective (f := e₀.symm.toMonoidHom) _
    e₀.symm.injective).mp hbot)

end CFSG.QuasithinUnique.K1

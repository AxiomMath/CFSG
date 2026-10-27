module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Step6

open scoped Pointwise

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

private lemma conj_smul_eq_map {G : Type*} [Group G] (g : G) (H : Subgroup G) :
    MulAut.conj g • H = H.map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  congr 1

private lemma map_centralizer_conj {G : Type*} [Group G] (g t : G) :
    (Subgroup.centralizer ({t} : Set G)).map (MulAut.conj g).toMonoidHom
      = Subgroup.centralizer ({g * t * g⁻¹} : Set G) := by
  have hkey : ∀ a b : G,
      (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹) ↔
        a * b = b * a := by
    intro a b
    rw [conj_mul, conj_mul]
    exact (conj_injective (x := g)).eq_iff
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (hkey t y).mpr (hy t (by simp))
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have hxeq : (g * t * g⁻¹) * x = x * (g * t * g⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hx) (g * t * g⁻¹) (by simp)
      have hkey' : ∀ a b : G,
          (g⁻¹ * a * (g⁻¹)⁻¹) * (g⁻¹ * b * (g⁻¹)⁻¹) =
            (g⁻¹ * b * (g⁻¹)⁻¹) * (g⁻¹ * a * (g⁻¹)⁻¹) ↔ a * b = b * a := by
        intro a b
        rw [conj_mul, conj_mul]
        exact (conj_injective (x := g⁻¹)).eq_iff
      have hmain := (hkey' (g * t * g⁻¹) x).mpr hxeq
      convert hmain using 2 <;> group
    · show g * (g⁻¹ * x * g) * g⁻¹ = x
      group

private theorem exists_conj_map_le_of_isPGroup2 {K : Type*} [Group K] [Finite K]
    {T₁ F : Subgroup K} (hT₁ : IsPGroup 2 T₁) (hodd : ¬ 2 ∣ T₁.index)
    (hF : IsPGroup 2 F) :
    ∃ c : K, F ≤ T₁.map (MulAut.conj c).toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 K := hT₁.toSylow hodd
  have hPcoe : (P : Subgroup K) = T₁ := IsPGroup.toSylow_coe hT₁ hodd
  obtain ⟨Q, hFQ⟩ := hF.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K P Q
  refine ⟨c, hFQ.trans (le_of_eq ?_)⟩
  rw [← hc, Sylow.coe_subgroup_smul, hPcoe, conj_smul_eq_map]

theorem exists_mem_D {G : Type*} [Group G] [Finite G] {S T : Subgroup G} {t₀ u : G}
    (ht₀S : t₀ ∈ S) (hT : IsSylow2In (S ⊓ Subgroup.centralizer ({t₀} : Set G)) T)
    (ht₀T : t₀ ∈ T) (ht₀c : ∀ x ∈ T, x * t₀ = t₀ * x) (ht₀2 : orderOf t₀ = 2)
    (huT : u ∈ T) (hu2 : orderOf u = 2) (hut : u ≠ t₀)
    (hC8 : ∀ v ∈ T, orderOf v = 2 → v ≠ t₀ →
      ∃ x ∈ T, x * v * x⁻¹ = u ∨ x * v * x⁻¹ = t₀ * u)
    {g : G} (hgS : g ∈ S) (hg : g * t₀ * g⁻¹ = u) :
    ∃ h ∈ S, h * t₀ * h⁻¹ = u ∧ (h * u * h⁻¹ = t₀ ∨ h * u * h⁻¹ = t₀ * u) := by
  classical
  let Y : Subgroup G := S ⊓ Subgroup.centralizer ({t₀} : Set G)
  let Cu : Subgroup G := S ⊓ Subgroup.centralizer ({u} : Set G)
  let T₁ : Subgroup G := T.map (MulAut.conj g).toMonoidHom
  let F : Subgroup G := Subgroup.closure ({t₀, u} : Set G)
  have hTY : T ≤ Y := hT.1
  have huS : u ∈ S := (hTY huT).1
  have ht₀Cu : t₀ ∈ Cu := by
    refine ⟨ht₀S, ?_⟩
    change t₀ ∈ Subgroup.centralizer ({u} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact ht₀c u huT
  have huCu : u ∈ Cu := by
    refine ⟨huS, ?_⟩
    change u ∈ Subgroup.centralizer ({u} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
  have hF_le_T : F ≤ T := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ht₀T
    · exact huT
  have hF_le_Cu : F ≤ Cu := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ht₀Cu
    · exact huCu
  have hT_pg : IsPGroup 2 T := hT.2.1
  have hF_pg : IsPGroup 2 F := hT_pg.to_le hF_le_T
  have hYmap : Y.map (MulAut.conj g).toMonoidHom = Cu := by
    change (S ⊓ Subgroup.centralizer ({t₀} : Set G)).map (MulAut.conj g).toMonoidHom
      = S ⊓ Subgroup.centralizer ({u} : Set G)
    rw [Subgroup.map_inf S (Subgroup.centralizer ({t₀} : Set G)) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective]
    have hS : S.map (MulAut.conj g).toMonoidHom = S := by
      rw [← conj_smul_eq_map g S]
      exact Subgroup.conj_smul_eq_self_of_mem hgS
    have hC : (Subgroup.centralizer ({t₀} : Set G)).map (MulAut.conj g).toMonoidHom
        = Subgroup.centralizer ({u} : Set G) := by
      rw [map_centralizer_conj g t₀, hg]
    rw [hS, hC]
  have hT₁_le_Cu : T₁ ≤ Cu := by
    change T.map (MulAut.conj g).toMonoidHom ≤ Cu
    rw [← hYmap]
    exact Subgroup.map_mono hTY
  have hT₁_pg : IsPGroup 2 T₁ := hT_pg.map (MulAut.conj g).toMonoidHom
  have hT₁_odd : ¬ 2 ∣ T₁.relIndex Cu := by
    change ¬ 2 ∣ (T.map (MulAut.conj g).toMonoidHom).relIndex Cu
    rw [← hYmap]
    rw [Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      T Y (MulAut.conj g).injective]
    exact hT.2.2
  have hT₁'_pg : IsPGroup 2 (T₁.subgroupOf Cu) := hT₁_pg.comap_subtype
  have hT₁'_odd : ¬ 2 ∣ (T₁.subgroupOf Cu).index := hT₁_odd
  have hF'_pg : IsPGroup 2 (F.subgroupOf Cu) := hF_pg.comap_subtype
  obtain ⟨c, hc⟩ := exists_conj_map_le_of_isPGroup2 hT₁'_pg hT₁'_odd hF'_pg
  have hF_le_map : F ≤ T₁.map (MulAut.conj (c : G)).toMonoidHom := by
    have hmap := Subgroup.map_mono (f := Cu.subtype) hc
    rw [Subgroup.map_subgroupOf_eq_of_le hF_le_Cu] at hmap
    rw [Subgroup.map_map] at hmap
    have hcomp : Cu.subtype.comp (MulAut.conj c).toMonoidHom
        = (MulAut.conj (c : G)).toMonoidHom.comp Cu.subtype := by
      ext k
      simp [MulAut.conj_apply]
    rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hT₁_le_Cu] at hmap
    exact hmap
  let g₁ : G := (c : G) * g
  let v : G := g₁⁻¹ * t₀ * g₁
  have hhom : (MulAut.conj (c : G)).toMonoidHom.comp (MulAut.conj g).toMonoidHom
      = (MulAut.conj g₁).toMonoidHom := by
    ext z
    show (c : G) * (g * z * g⁻¹) * (c : G)⁻¹ = (c : G) * g * z * ((c : G) * g)⁻¹
    group
  have hF_le_map2 : F ≤ T.map (MulAut.conj g₁).toMonoidHom := by
    have := hF_le_map
    change F ≤ (T.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (c : G)).toMonoidHom at this
    rwa [Subgroup.map_map, hhom] at this
  have ht₀F : t₀ ∈ F := Subgroup.subset_closure (by simp)
  have hvT : v ∈ T := by
    have hfv : (MulAut.conj g₁) v = t₀ := by
      show g₁ * v * g₁⁻¹ = t₀
      simp only [v]
      group
    have hmem : (MulAut.conj g₁) v ∈ T.map (MulAut.conj g₁).toMonoidHom :=
      hfv ▸ hF_le_map2 ht₀F
    exact (Subgroup.mem_map_iff_mem (MulAut.conj g₁).injective).mp hmem
  have hv2 : orderOf v = 2 := by
    have h : SemiconjBy g₁⁻¹ t₀ v := by
      rw [SemiconjBy]
      simp only [v]
      group
    rw [← SemiconjBy.orderOf_eq g₁⁻¹ h, ht₀2]
  have hcCu : (c : G) ∈ Cu := c.2
  have hcu : (c : G) * u * (c : G)⁻¹ = u := by
    have hmem : (c : G) ∈ Subgroup.centralizer ({u} : Set G) := c.2.2
    have hcomm : u * (c : G) = (c : G) * u :=
      (Subgroup.mem_centralizer_iff.mp hmem) u (by simp)
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hg₁ : g₁ * t₀ * g₁⁻¹ = u := by
    have h1 : g₁ * t₀ * g₁⁻¹ = (c : G) * (g * t₀ * g⁻¹) * (c : G)⁻¹ := by
      simp only [g₁]
      group
    rw [h1, hg, hcu]
  have hvne : v ≠ t₀ := by
    intro hv
    have hfinal : g₁ * t₀ * g₁⁻¹ = t₀ := by
      have hvt : g₁⁻¹ * t₀ * g₁ = t₀ := by
        simpa only [v] using hv
      have hL : t₀ = g₁ * (g₁⁻¹ * t₀ * g₁) * g₁⁻¹ := by group
      rw [hvt] at hL
      exact hL.symm
    exact hut (hg₁.symm.trans hfinal)
  obtain ⟨x, hxT, hx⟩ := hC8 v hvT hv2 hvne
  have hg₁S : g₁ ∈ S := by
    show (c : G) * g ∈ S
    exact S.mul_mem c.2.1 hgS
  have hxS : x⁻¹ ∈ S := S.inv_mem ((hTY hxT).1)
  have hxt : x⁻¹ * t₀ * x = t₀ := by
    rw [mul_assoc, (ht₀c x hxT).symm]
    group
  have hh_t₀ : (g₁ * x⁻¹) * t₀ * (g₁ * x⁻¹)⁻¹ = u := by
    have h1 : (g₁ * x⁻¹) * t₀ * (g₁ * x⁻¹)⁻¹ = g₁ * (x⁻¹ * t₀ * x) * g₁⁻¹ := by
      group
    rw [h1, hxt, hg₁]
  have hh_inv : (g₁ * x⁻¹)⁻¹ * t₀ * (g₁ * x⁻¹) = x * v * x⁻¹ := by
    simp only [v]
    group
  refine ⟨g₁ * x⁻¹, S.mul_mem hg₁S hxS, hh_t₀, ?_⟩
  rcases hx with hx | hx
  · left
    have hh_inv' : (g₁ * x⁻¹)⁻¹ * t₀ * (g₁ * x⁻¹) = u := hh_inv.trans hx
    have hconj := congrArg (fun z => (g₁ * x⁻¹) * z * (g₁ * x⁻¹)⁻¹) hh_inv'
    have hL : (g₁ * x⁻¹) * ((g₁ * x⁻¹)⁻¹ * t₀ * (g₁ * x⁻¹)) * (g₁ * x⁻¹)⁻¹ = t₀ := by
      group
    rw [hL] at hconj
    exact hconj.symm
  · right
    have hh_inv' : (g₁ * x⁻¹)⁻¹ * t₀ * (g₁ * x⁻¹) = t₀ * u := hh_inv.trans hx
    have hconj := congrArg (fun z => (g₁ * x⁻¹) * z * (g₁ * x⁻¹)⁻¹) hh_inv'
    have hL : (g₁ * x⁻¹) * ((g₁ * x⁻¹)⁻¹ * t₀ * (g₁ * x⁻¹)) * (g₁ * x⁻¹)⁻¹ = t₀ := by
      group
    rw [hL] at hconj
    have hR : (g₁ * x⁻¹) * (t₀ * u) * (g₁ * x⁻¹)⁻¹
        = u * ((g₁ * x⁻¹) * u * (g₁ * x⁻¹)⁻¹) := by
      rw [show (g₁ * x⁻¹) * (t₀ * u) * (g₁ * x⁻¹)⁻¹
            = ((g₁ * x⁻¹) * t₀ * (g₁ * x⁻¹)⁻¹) * ((g₁ * x⁻¹) * u * (g₁ * x⁻¹)⁻¹) by
          group]
      rw [hh_t₀]
    rw [hR] at hconj
    have huu : u * u = 1 := by
      rw [← pow_two, ← hu2]
      exact pow_orderOf_eq_one u
    have hcomm_tu : u * t₀ = t₀ * u := ht₀c u huT
    calc (g₁ * x⁻¹) * u * (g₁ * x⁻¹)⁻¹
        = u * (u * ((g₁ * x⁻¹) * u * (g₁ * x⁻¹)⁻¹)) := by
          rw [← mul_assoc, huu, one_mul]
      _ = u * t₀ := by rw [← hconj]
      _ = t₀ * u := hcomm_tu

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5

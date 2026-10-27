module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54D
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54P
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56P

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem exists_three_elt {G : Type} [Group G] [Finite G] {K A : Subgroup G}
    (hK : SecProp K A (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3)))) :
    ∃ k ∈ K, orderOf k = 3 := by
  obtain ⟨hn, ⟨e⟩⟩ := hK
  have hcard : Nat.card (↥K ⧸ A.subgroupOf K) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hdvd : 3 ∣ Nat.card ↥K := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf K)
    rw [hcard] at h
    rw [h]
    exact dvd_mul_of_dvd_left (by norm_num : 3 ∣ 6) _
  obtain ⟨k₀, hk₀⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥K) 3 (hp := ⟨Nat.prime_three⟩) hdvd
  exact ⟨k₀, k₀.2, (Subgroup.orderOf_coe k₀).trans hk₀⟩

private theorem fpf_of_trans {G : Type} [Group G] [Finite G]
    {F : Subgroup G} {z k : G} (hz2 : orderOf z = 2) (hzF : z ∈ F)
    (hzc : ∀ f ∈ F, f * z = z * f) (hF8 : Nat.card F = 8)
    (hkz : k * z * k⁻¹ = z) (hkN : k ∈ normalizer (F : Set G))
    (htrans : ActsTransitively (zpowers k) F (zpowers z)) :
    ∀ f ∈ F, k * f * k⁻¹ * f⁻¹ ∈ zpowers z → f ∈ zpowers z := by
  intro f hfF hfk
  by_contra hfZ
  have hZcent : ∀ w ∈ zpowers z, ∀ f' ∈ F, w * f' = f' * w := by
    have hzC : z ∈ centralizer (F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      exact fun f' hf' => hzc f' hf'
    intro w hw f' hf'
    exact ((Subgroup.mem_centralizer_iff.mp ((Subgroup.zpowers_le.mpr hzC) hw)) f' hf').symm
  have hkC : k ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp hkz
  have hfix : ∀ κ, κ ∈ centralizer ({z} : Set G) → ∀ w ∈ zpowers z, κ * w * κ⁻¹ = w := by
    intro κ hκ w hw
    have hcomm : κ * z = z * κ := Subgroup.mem_centralizer_singleton_iff.mp hκ
    have hsub : zpowers z ≤ centralizer ({κ} : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
    have hwcomm : w * κ = κ * w := Subgroup.mem_centralizer_singleton_iff.mp (hsub hw)
    rw [hwcomm.symm]
    group
  have hclaim : ∀ κ ∈ zpowers k, f⁻¹ * (κ * f * κ⁻¹) ∈ zpowers z := by
    intro κ hκ
    rw [Subgroup.zpowers_eq_closure k] at hκ
    refine Subgroup.closure_induction (p := fun κ _ => f⁻¹ * (κ * f * κ⁻¹) ∈ zpowers z)
      ?_ ?_ ?_ ?_ hκ
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      have hz0 : k * f * k⁻¹ * f⁻¹ ∈ zpowers z := hfk
      have hconj : f⁻¹ * (k * f * k⁻¹ * f⁻¹) * f = k * f * k⁻¹ * f⁻¹ := by
        rw [mul_assoc f⁻¹ (k * f * k⁻¹ * f⁻¹) f,
          hZcent (k * f * k⁻¹ * f⁻¹) hz0 f hfF]
        group
      rw [show f⁻¹ * (k * f * k⁻¹) = f⁻¹ * (k * f * k⁻¹ * f⁻¹) * f from by group, hconj]
      exact hz0
    · simp
    · intro x y hx hy hpx hpy
      have hxK : x ∈ zpowers k := by simpa [Subgroup.zpowers_eq_closure k] using hx
      have hyK : y ∈ zpowers k := by simpa [Subgroup.zpowers_eq_closure k] using hy
      have hxZ : x ∈ centralizer ({z} : Set G) := (Subgroup.zpowers_le.mpr hkC) hxK
      let zx := f⁻¹ * (x * f * x⁻¹)
      let zy := f⁻¹ * (y * f * y⁻¹)
      have hzx : zx ∈ zpowers z := hpx
      have hzy : zy ∈ zpowers z := hpy
      have hx1 : x * f * x⁻¹ = f * zx := by
        show x * f * x⁻¹ = f * (f⁻¹ * (x * f * x⁻¹))
        group
      have hy1 : y * f * y⁻¹ = f * zy := by
        show y * f * y⁻¹ = f * (f⁻¹ * (y * f * y⁻¹))
        group
      have hxy : (x * y) * f * (x * y)⁻¹ = f * (zx * zy) := by
        calc (x * y) * f * (x * y)⁻¹ = x * (y * f * y⁻¹) * x⁻¹ := by group
          _ = x * (f * zy) * x⁻¹ := by rw [hy1]
          _ = (x * f * x⁻¹) * (x * zy * x⁻¹) := by group
          _ = (x * f * x⁻¹) * zy := by rw [hfix x hxZ zy hzy]
          _ = (f * zx) * zy := by rw [hx1]
          _ = f * (zx * zy) := by group
      rw [hxy]
      have hred : f⁻¹ * (f * (zx * zy)) = zx * zy := by group
      rw [hred]
      exact Subgroup.mul_mem _ hzx hzy
    · intro x hx hpx
      have hxK : x ∈ zpowers k := by simpa [Subgroup.zpowers_eq_closure k] using hx
      have hxiZ : x⁻¹ ∈ centralizer ({z} : Set G) :=
        (Subgroup.zpowers_le.mpr hkC) (Subgroup.inv_mem _ hxK)
      let zx := f⁻¹ * (x * f * x⁻¹)
      have hzx : zx ∈ zpowers z := hpx
      have hx1 : x * f * x⁻¹ = f * zx := by
        show x * f * x⁻¹ = f * (f⁻¹ * (x * f * x⁻¹))
        group
      have hconj := congrArg (fun t => x⁻¹ * t * x) hx1
      have hleft : x⁻¹ * (x * f * x⁻¹) * x = f := by group
      have hright : x⁻¹ * (f * zx) * x = (x⁻¹ * f * x) * zx := by
        have hz' : x⁻¹ * zx * x = zx := by simpa using hfix x⁻¹ hxiZ zx hzx
        calc x⁻¹ * (f * zx) * x = (x⁻¹ * f * x) * (x⁻¹ * zx * x) := by group
          _ = (x⁻¹ * f * x) * zx := by rw [hz']
      have hfeq : (x⁻¹ * f * x) * zx = f := by rw [← hright, ← hconj, hleft]
      have hfinv : x⁻¹ * f * x = f * zx⁻¹ := eq_mul_inv_iff_mul_eq.mpr hfeq
      show f⁻¹ * (x⁻¹ * f * (x⁻¹)⁻¹) ∈ zpowers z
      rw [inv_inv, hfinv]
      have hred : f⁻¹ * (f * zx⁻¹) = zx⁻¹ := by group
      rw [hred]
      exact Subgroup.inv_mem _ hzx
  have hsub : (F : Set G) ⊆
      (zpowers z : Set G) ∪ ((fun w => f * w) '' (zpowers z : Set G)) := by
    intro v hvF
    by_cases hvZ : v ∈ zpowers z
    · exact Or.inl hvZ
    · right
      obtain ⟨κ, hκ, hκv⟩ := htrans.2.2 f hfF hfZ v hvF hvZ
      have hc := hclaim κ hκ
      have hvf : v⁻¹ * f ∈ zpowers z := by
        have h1 := Subgroup.mul_mem _ hκv (Subgroup.inv_mem _ hc)
        have h2 : v⁻¹ * (κ * f * κ⁻¹) * (f⁻¹ * (κ * f * κ⁻¹))⁻¹ = v⁻¹ * f := by group
        rw [h2] at h1
        exact h1
      exact ⟨(v⁻¹ * f)⁻¹, Subgroup.inv_mem _ hvf, by group⟩
  have hZcard : (zpowers z : Set G).ncard = 2 := by
    show Nat.card (zpowers z) = 2
    rw [Nat.card_zpowers, hz2]
  have hTcard : ((fun w => f * w) '' (zpowers z : Set G)).ncard ≤ 2 := by
    calc ((fun w => f * w) '' (zpowers z : Set G)).ncard ≤ (zpowers z : Set G).ncard :=
          Set.ncard_image_le
      _ = 2 := hZcard
  have hFcard : (F : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact hF8
  have hle : (F : Set G).ncard ≤
      (zpowers z : Set G).ncard + ((fun w => f * w) '' (zpowers z : Set G)).ncard :=
    (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le _ _)
  omega

theorem y7a_exists_k_F {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∃ k : G, k ∈ normIn L s.fr.A ⊓ normIn L s.fr.F ∧ k ^ 3 = 1 ∧
      ∀ f ∈ s.fr.F, k * f * k⁻¹ * f⁻¹ ∈ s.fr.Z → f ∈ s.fr.Z := by
  obtain ⟨⟨h2a, h2b, h2c⟩, ⟨h3a, h3b, h3c, h3d, h3e, h3f⟩,
    ⟨h4a, h4b, h4c, h4d, h4e⟩, ⟨h5a, h5b, h5c, h5d, h5e, h5f⟩⟩ := hH.hLF.fact18
  rw [f3_zL_eq_bot hH, bot_sup_eq] at h5e
  obtain ⟨k, hk, hk3⟩ := exists_three_elt h5e
  have hk1 : k ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hk3
    norm_num at hk3
  have hkzL : k ∉ zL L := by
    rw [f3_zL_eq_bot hH]
    exact fun h => hk1 (Subgroup.mem_bot.mp h)
  have hpg : IsPGroup 3 ↥(zpowers k) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hk3]; norm_num)
  have htrans : ActsTransitively (zpowers k) s.fr.F (zpowers s.fr.z) :=
    (h5f k hk hpg hkzL).1
  have hz2 : orderOf s.fr.z = 2 := s3_z_order s (lfactsA_of_setting hH.hS hH.hZ s)
  have hzF : s.fr.z ∈ s.fr.F := y54_z_mem_F s
  have hzc : ∀ f ∈ s.fr.F, f * s.fr.z = s.fr.z * f :=
    fun f hf => y54_F_comm hH f hf s.fr.z hzF
  have hF8 : Nat.card ↥s.fr.F = 8 := by simpa using (y54_F_isE3 hH).2
  have hkz : k * s.fr.z * k⁻¹ = s.fr.z := by
    have hkA : k ∈ normIn L s.fr.A := hk.1
    rw [h2a] at hkA
    have hcomm : k * s.fr.z = s.fr.z * k :=
      Subgroup.mem_centralizer_singleton_iff.mp hkA.2
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hkN : k ∈ normalizer (s.fr.F : Set G) := hk.2.2
  refine ⟨k, hk, ?_, ?_⟩
  · rw [← hk3]
    exact pow_orderOf_eq_one k
  · intro f hf hfk
    exact fpf_of_trans hz2 hzF hzc hF8 hkz hkN htrans f hf hfk

theorem y7a_exists_k_E {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∃ k : G, k ∈ normIn L s.fr.A ⊓ normIn L s.fr.E ∧ k ^ 3 = 1 ∧
      ∀ f ∈ s.fr.E, k * f * k⁻¹ * f⁻¹ ∈ s.fr.Z → f ∈ s.fr.Z := by
  obtain ⟨⟨h2a, h2b, h2c⟩, ⟨h3a, h3b, h3c, h3d, h3e, h3f⟩,
    ⟨h4a, h4b, h4c, h4d, h4e⟩, ⟨h5a, h5b, h5c, h5d, h5e, h5f⟩⟩ := hH.hLF.fact18
  rw [f3_zL_eq_bot hH, bot_sup_eq] at h4c
  obtain ⟨k, hkE, hk3⟩ := exists_three_elt h4c
  have hkA : k ∈ normIn L s.fr.A := h4b hkE
  have hk : k ∈ normIn L s.fr.A ⊓ normIn L s.fr.E := ⟨hkA, hkE⟩
  have hk1 : k ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hk3
    norm_num at hk3
  have hkzL : k ∉ zL L := by
    rw [f3_zL_eq_bot hH]
    exact fun h => hk1 (Subgroup.mem_bot.mp h)
  have hpg : IsPGroup 3 ↥(zpowers k) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hk3]; norm_num)
  have htrans : ActsTransitively (zpowers k) s.fr.E (zpowers s.fr.z) :=
    (h4e k hkE hpg hkzL).1
  have hz2 : orderOf s.fr.z = 2 := s3_z_order s (lfactsA_of_setting hH.hS hH.hZ s)
  have hzE : s.fr.z ∈ s.fr.E := y56_z_mem_E hH
  have hzc : ∀ f ∈ s.fr.E, f * s.fr.z = s.fr.z * f :=
    fun f hf => y56_E_comm hH f hf s.fr.z hzE
  have hE8 : Nat.card ↥s.fr.E = 8 := by simpa using (y56_E_isE3 hH).2
  have hkz : k * s.fr.z * k⁻¹ = s.fr.z := by
    have hkA' : k ∈ centEl L s.fr.z := by
      rw [← h2a]
      exact hkA
    have hcomm : k * s.fr.z = s.fr.z * k :=
      Subgroup.mem_centralizer_singleton_iff.mp hkA'.2
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hkN : k ∈ normalizer (s.fr.E : Set G) := hk.2.2
  refine ⟨k, hk, ?_, ?_⟩
  · rw [← hk3]
    exact pow_orderOf_eq_one k
  · intro f hf hfk
    exact fpf_of_trans hz2 hzE hzc hE8 hkz hkN htrans f hf hfk

end CFSG.OddStandard.HigherRank.YamadaG23

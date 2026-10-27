module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.MFusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.MFusionConj

public section

namespace CFSG.EvenSporadicStandard.J4Std.MFusion

open Subgroup CFSG.EvenSporadicStandard.J4Std

variable {G : Type} [Group G] {L U T0 : Subgroup G} {z : G} {Y : Subgroup G}

theorem exists_m0 [Finite G] (hS : Setting L z) (hD : LocalData L U T0) (hW : WeakData U z Y)
    {y : G} (hyM : y ∈ normalizer (Y : Set G)) (hy2 : y * y = 1) (hyY : y ∉ Y) {g' : G}
    (hg'U : ∀ u ∈ U, g' * u * g'⁻¹ ∈ cenIn Y y) :
    ∃ m₀ ∈ normalizer (Y : Set G), ∃ y₁ ∈ cenIn Y y, m₀ * z * m₀⁻¹ = y * y₁ := by
  have hyn : ∀ a ∈ Y, y * a * y⁻¹ ∈ Y := fun a ha => (mem_normalizer_iff.1 hyM a).1 ha
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hcardQ : Nat.card (adjoinInv Y y hy2 hyn) = 2 ^ 23 := by
    rw [card_adjoinInv hyY, hW.card_Y]
    norm_num
  have hcardP : Nat.card (conjSub g'⁻¹ (adjoinInv Y y hy2 hyn)) = 2 ^ 23 := by
    rw [card_conjSub, hcardQ]
  have hPp : IsPGroup 2 (conjSub g'⁻¹ (adjoinInv Y y hy2 hyn)) := IsPGroup.of_card hcardP
  have hQcomm : ∀ u ∈ U, ∀ q ∈ adjoinInv Y y hy2 hyn,
      (g' * u * g'⁻¹) * q = q * (g' * u * g'⁻¹) := by
    intro u hu q hq
    obtain ⟨hcY, hcy⟩ := mem_cenIn.1 (hg'U u hu)
    rcases mem_adjoinInv_iff.1 hq with hq | ⟨b, hb, rfl⟩
    · exact hW.Y_comm _ hcY q hq
    · calc g' * u * g'⁻¹ * (y * b) = ((g' * u * g'⁻¹) * y) * b := by group
        _ = (y * (g' * u * g'⁻¹)) * b := by rw [hcy]
        _ = y * ((g' * u * g'⁻¹) * b) := by group
        _ = y * (b * (g' * u * g'⁻¹)) := by rw [hW.Y_comm _ hcY b hb]
        _ = y * b * (g' * u * g'⁻¹) := by group
  have hPc : conjSub g'⁻¹ (adjoinInv Y y hy2 hyn) ≤ centralizer (U : Set G) := by
    intro p hp
    rw [mem_centralizer_iff]
    intro u hu
    have hq : g' * p * g'⁻¹ ∈ adjoinInv Y y hy2 hyn := mem_conjSub_inv_iff.1 hp
    have := hQcomm u hu _ hq
    apply conj_injective g'
    calc g' * (u * p) * g'⁻¹ = (g' * u * g'⁻¹) * (g' * p * g'⁻¹) := by group
      _ = (g' * p * g'⁻¹) * (g' * u * g'⁻¹) := this
      _ = g' * (p * u) * g'⁻¹ := by group
  obtain ⟨c, -, hPc'⟩ := hW.sylow_W _ hPc hPp
  have hQle : ∀ q ∈ adjoinInv Y y hy2 hyn, (g' * c)⁻¹ * q * (g' * c) ∈ Csub U z := by
    intro q hq
    have h1 : g'⁻¹ * q * g' ∈ conjSub g'⁻¹ (adjoinInv Y y hy2 hyn) :=
      mem_conjSub_inv_iff.2 (by rw [show g' * (g'⁻¹ * q * g') * g'⁻¹ = q by group]; exact hq)
    have h2 := mem_conjSub_iff.1 (hPc' h1)
    rwa [show (g' * c)⁻¹ * q * (g' * c) = c⁻¹ * (g'⁻¹ * q * g') * c by group]
  have hQeq : adjoinInv Y y hy2 hyn = conjSub (g' * c) (Csub U z) := by
    apply eq_of_le_of_card_ge
    · intro q hq
      exact mem_conjSub_iff.2 (hQle q hq)
    · rw [card_conjSub, hW.card_W, hcardQ]
  have hm₀M : g' * c ∈ normalizer (Y : Set G) := by
    have : (g' * c)⁻¹ ∈ normalizer (Y : Set G) := by
      apply mem_normalizer_of_conj_mem hW
      intro y' hy'
      have := hQle y' (le_adjoinInv hy')
      rwa [inv_inv]
    simpa using inv_mem this
  have hzQ : (g' * c) * z * (g' * c)⁻¹ ∈ adjoinInv Y y hy2 hyn := by
    rw [hQeq]
    exact conj_mem_conjSub (z_mem_Csub hS hD)
  rcases mem_adjoinInv_iff.1 hzQ with hzY | ⟨y₁, hy₁, hzy⟩
  · exact absurd rfl (hW.noconj_Y (g' * c) _ hzY)
  · refine ⟨g' * c, hm₀M, y₁, mem_cenIn.2 ⟨hy₁, ?_⟩, hzy⟩
    have hinv : (g' * c) * z * (g' * c)⁻¹ * ((g' * c) * z * (g' * c)⁻¹) = 1 := by
      calc (g' * c) * z * (g' * c)⁻¹ * ((g' * c) * z * (g' * c)⁻¹)
          = (g' * c) * (z * z) * (g' * c)⁻¹ := by group
        _ = 1 := by rw [hS.z_mul_self]; group
    rw [hzy] at hinv
    have h1 : (y * y₁)⁻¹ = y * y₁ := inv_eq_of_mul_eq_one_right hinv
    rwa [mul_inv_rev, hyi, inv_eq_of_mul_eq_one_right (hW.Y_sq y₁ hy₁)] at h1

theorem fuse_of [Finite G] (hS : Setting L z) (hD : LocalData L U T0)
    (htrans : ∀ u ∈ U, ∃ n ∈ Nsub U z, n * z * n⁻¹ = z * u) (hR : RankData L U z)
    (hW : WeakData U z Y) {y : G} (hyM : y ∈ normalizer (Y : Set G)) {g : G}
    (hg : g * z * g⁻¹ = y) : ∃ m ∈ normalizer (Y : Set G), m * z * m⁻¹ = y := by
  have hy2 : y * y = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hS.z_mul_self]; group
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hyY : y ∉ Y := fun h => hW.noconj_Y g y h hg
  have hyn : ∀ a ∈ Y, y * a * y⁻¹ ∈ Y := fun a ha => (mem_normalizer_iff.1 hyM a).1 ha
  obtain ⟨g', hg'U, hCcard⟩ := exists_conj_cenIn hS hD htrans hR hW hyM hg
  obtain ⟨m₀, hm₀M, y₁, hy₁C, hm₀z⟩ := exists_m0 hS hD hW hyM hy2 hyY hg'U
  have hcardY : Nat.card Y = Nat.card (cenIn Y y) ^ 2 := by
    rw [hW.card_Y, hCcard]
    norm_num
  obtain ⟨a, haY, hya⟩ :=
    exists_psi_eq (hy := hyn) (hc := hW.Y_comm) hW.Y_sq hy2 hcardY hy₁C
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hW.Y_sq a haY)
  have hsqa : a * a = 1 := hW.Y_sq a haY
  have hab : a * (y * a * y⁻¹) = (y * a * y⁻¹) * a := hW.Y_comm _ haY _ (hyn a haY)
  rw [hyi] at hab
  refine ⟨a⁻¹ * m₀, mul_mem (inv_mem (Subgroup.le_normalizer haY)) hm₀M, ?_⟩
  calc a⁻¹ * m₀ * z * (a⁻¹ * m₀)⁻¹ = a⁻¹ * (m₀ * z * m₀⁻¹) * a := by group
    _ = a⁻¹ * (y * (a * (y * a * y⁻¹))) * a := by rw [hm₀z, hya]
    _ = a * (y * (a * (y * a * y))) * a := by rw [hai, hyi]
    _ = a * (y * ((y * a * y) * a)) * a := by rw [hab]
    _ = (a * (y * y) * a) * (y * (a * a)) := by group
    _ = y := by simp only [hy2, hsqa, mul_one, one_mul]

end CFSG.EvenSporadicStandard.J4Std.MFusion

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup

theorem fusionData_of {G : Type} [Group G] [Finite G] {L U T0 : Subgroup G} {z : G}
    {Y : Subgroup G} (hS : Setting L z) (hD : LocalData L U T0)
    (htrans : ∀ u ∈ U, ∃ n ∈ Nsub U z, n * z * n⁻¹ = z * u) (hY : YStruct L U z Y)
    (hR : RankData L U z) (hW : WeakData U z Y) : FusionData L U z Y where
  N_le_M := MFusion.N_le_M hS hD htrans hY hW
  cent_le_N := fun _ hm _ hy hmz => MFusion.cent_le_N hS hD htrans hY hW hm hy hmz
  N_eq := fun _ hn => MFusion.N_eq hS hD hW hn
  fuse := fun _ hyM ⟨_, hg⟩ => MFusion.fuse_of hS hD htrans hR hW hyM hg

end CFSG.EvenSporadicStandard.J4Std

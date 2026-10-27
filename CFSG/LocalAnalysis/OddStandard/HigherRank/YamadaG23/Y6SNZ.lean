module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Setting
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Inv
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6O2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y6_conj_mem_normIn (c : Ctx6 G L) (hH : F33Hyp c.s c.e) {g n : G}
    (hgL : g ∈ normalizer (L : Set G)) (hgz : g * c.s.fr.z * g⁻¹ = c.s.fr.z)
    (hn : n ∈ normIn L c.s.fr.A) : g * n * g⁻¹ ∈ normIn L c.s.fr.A := by
  have hgiz : g⁻¹ * c.s.fr.z * g = c.s.fr.z := by
    calc g⁻¹ * c.s.fr.z * g = g⁻¹ * (g * c.s.fr.z * g⁻¹) * g := by rw [hgz]
      _ = c.s.fr.z := by group
  rw [hH.hLF.fact18.1.1] at hn ⊢
  simp only [centEl, Subgroup.mem_inf] at hn ⊢
  obtain ⟨hnL, hnC⟩ := hn
  refine ⟨(Subgroup.mem_set_normalizer_iff.mp hgL n).mp hnL, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hnC ⊢
  calc g * n * g⁻¹ * c.s.fr.z = g * n * (g⁻¹ * c.s.fr.z * g) * g⁻¹ := by group
    _ = g * n * c.s.fr.z * g⁻¹ := by rw [hgiz]
    _ = g * (n * c.s.fr.z) * g⁻¹ := by group
    _ = g * (c.s.fr.z * n) * g⁻¹ := by rw [hnC]
    _ = g * c.s.fr.z * n * g⁻¹ := by group
    _ = g * c.s.fr.z * g⁻¹ * (g * n * g⁻¹) := by group
    _ = c.s.fr.z * (g * n * g⁻¹) := by rw [hgz]

private lemma y6_mem_Y_of_conj (c : Ctx6 G L) (hH : F33Hyp c.s c.e) {y : G}
    (hyt : y * c.s.t * y⁻¹ = c.s.t) (hyz : y * c.s.fr.z * y⁻¹ = c.s.fr.z) :
    y ∈ y6Y c := by
  have hyt' : y * c.s.t = c.s.t * y := by
    calc y * c.s.t = y * c.s.t * y⁻¹ * y := by group
      _ = c.s.t * y := by rw [hyt]
  have hyH : y ∈ c.s.H := Subgroup.mem_centralizer_singleton_iff.mpr hyt'
  have hyL : y ∈ normalizer (L : Set G) := s3_H_le_N c.s hH.hS hyH
  have hyiz : y⁻¹ * c.s.fr.z * y = c.s.fr.z := by
    calc y⁻¹ * c.s.fr.z * y = y⁻¹ * (y * c.s.fr.z * y⁻¹) * y := by rw [hyz]
      _ = c.s.fr.z := by group
  have hyNorm : y ∈ normalizer (normIn L c.s.fr.A : Set G) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro n
    constructor
    · exact y6_conj_mem_normIn c hH hyL hyz
    · intro hn
      have h1 := y6_conj_mem_normIn c hH (g := y⁻¹) (Subgroup.inv_mem _ hyL)
        (by simpa using hyiz) hn
      have h2 : y⁻¹ * (y * n * y⁻¹) * y⁻¹⁻¹ = n := by group
      rwa [h2] at h1
  have hAN : c.s.fr.A ≤ normIn L c.s.fr.A :=
    le_inf (s3_A_le_L c.s) Subgroup.le_normalizer
  set M : Subgroup G := c.s.fr.A.map (MulAut.conj y) with hMdef
  have hMN : M ≤ normIn L c.s.fr.A := by
    intro m hm
    rw [hMdef, Subgroup.mem_map] at hm
    obtain ⟨a, ha, rfl⟩ := hm
    change y * a * y⁻¹ ∈ normIn L c.s.fr.A
    exact (Subgroup.mem_set_normalizer_iff.mp hyNorm a).mp (hAN ha)
  have hMnorm : ∀ n ∈ normIn L c.s.fr.A, ∀ m ∈ M, n * m * n⁻¹ ∈ M := by
    intro n hn m hm
    rw [hMdef, Subgroup.mem_map] at hm
    obtain ⟨a, ha, rfl⟩ := hm
    rw [hMdef, Subgroup.mem_map]
    have hcN : y⁻¹ * n * y ∈ normIn L c.s.fr.A := by
      simpa using y6_conj_mem_normIn c hH (g := y⁻¹) (Subgroup.inv_mem _ hyL)
        (by simpa using hyiz) hn
    have hcNnorm : y⁻¹ * n * y ∈ normalizer (c.s.fr.A : Set G) := by
      have h := hcN
      simp only [normIn, Subgroup.mem_inf] at h
      exact h.2
    have hcA : (y⁻¹ * n * y) * a * (y⁻¹ * n * y)⁻¹ ∈ c.s.fr.A :=
      (Subgroup.mem_set_normalizer_iff.mp hcNnorm a).mp ha
    refine ⟨(y⁻¹ * n * y) * a * (y⁻¹ * n * y)⁻¹, hcA, ?_⟩
    change y * ((y⁻¹ * n * y) * a * (y⁻¹ * n * y)⁻¹) * y⁻¹ =
      n * (y * a * y⁻¹) * n⁻¹
    group
  have hcardA : Nat.card ↥c.s.fr.A = 32 :=
    (lfactsA_of_setting hH.hS hH.hZ c.s).card_A
  have hcardM : Nat.card ↥M = 32 := by
    rw [hMdef, Subgroup.card_map_of_injective (MulAut.conj y).injective, hcardA]
  have hM2 : IsPGroup 2 ↥M := by
    apply IsPGroup.of_card (p := 2) (n := 5)
    rw [hcardM]
    norm_num
  have hfrob : SecProp (normIn L c.s.fr.A) c.s.fr.A
      (fun Y _ _ _ => IsFrobeniusOfOrder 18 Y) := by
    have h := hH.hLF.fact18.1.2.1
    rwa [f3_zL_eq_bot hH, bot_sup_eq] at h
  have hMleA : M ≤ c.s.fr.A :=
    y6_O2_le (N := normIn L c.s.fr.A) (A := c.s.fr.A) (M := M)
      hAN hfrob hMN hMnorm hM2
  have hMA : M = c.s.fr.A := by
    apply Subgroup.eq_of_le_of_card_ge hMleA
    rw [hcardA, hcardM]
  have hyA : y ∈ normalizer (c.s.fr.A : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa only [hMdef] using hMA
  exact s6_NHA_le_Y c hH ⟨hyH, hyA⟩

theorem y6_NZ_le_Y (c : Ctx6 G L) (hH : F33Hyp c.s c.e) {x : G}
    (hxV : x ∈ normalizer (V1 c.e : Set G))
    (hxt : x * c.s.t * x⁻¹ = c.s.t ∨ x * c.s.t * x⁻¹ = c.s.fr.z * c.s.t) : x ∈ y6Y c := by
  have hz : x * c.s.fr.z * x⁻¹ = c.s.fr.z := y6_fix_z (c.y6cfg hH) hxV
  rcases hxt with hxt | hxt
  · exact y6_mem_Y_of_conj c hH hxt hz
  · have hd2 : c.d * c.d = 1 := by
      have h := pow_orderOf_eq_one c.d
      rw [c.d_order] at h
      simpa [pow_two] using h
    have hz2 : c.s.fr.z * c.s.fr.z = 1 := by
      simpa [pow_two] using (c.y6cfg hH).rel.z_sq
    set y : G := c.d * x with hydef
    have hyt : y * c.s.t * y⁻¹ = c.s.t := by
      rw [hydef]
      calc c.d * x * c.s.t * (c.d * x)⁻¹
          = c.d * (x * c.s.t * x⁻¹) * c.d⁻¹ := by group
        _ = c.d * (c.s.fr.z * c.s.t) * c.d⁻¹ := by rw [hxt]
        _ = (c.d * c.s.fr.z * c.d⁻¹) * (c.d * c.s.t * c.d⁻¹) := by group
        _ = c.s.fr.z * (c.s.fr.z * c.s.t) := by rw [y5_dz (c := c.toCtx5) hH,
            y5_dtd (c := c.toCtx5) hH]
        _ = c.s.t := by rw [← mul_assoc, hz2, one_mul]
    have hyz : y * c.s.fr.z * y⁻¹ = c.s.fr.z := by
      rw [hydef]
      calc c.d * x * c.s.fr.z * (c.d * x)⁻¹
          = c.d * (x * c.s.fr.z * x⁻¹) * c.d⁻¹ := by group
        _ = c.d * c.s.fr.z * c.d⁻¹ := by rw [hz]
        _ = c.s.fr.z := y5_dz (c := c.toCtx5) hH
    have hdy : c.d * y = x := by
      rw [hydef, ← mul_assoc, hd2, one_mul]
    rw [← hdy]
    exact mul_mem (s6_d_mem_Y c hH) (y6_mem_Y_of_conj c hH hyt hyz)

end CFSG.OddStandard.HigherRank.YamadaG23

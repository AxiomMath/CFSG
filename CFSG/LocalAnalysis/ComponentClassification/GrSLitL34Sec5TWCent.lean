module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5TWGen

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
  CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G] [Finite G]

theorem wGroup_eq_of_central_eight (hGW : GWTwoBalanced G) {S₁ A D W : Subgroup G}
    (hA : IsEightGroup A) (hAc : ∀ x ∈ A, ∀ b ∈ S₁, x * b = b * x)
    (hDS : D ≤ S₁) (hD : IsEightGroup D) (hWD : wGroup D = W) {B : Subgroup G} (hBS : B ≤ S₁)
    (hB : IsAbelianTwoOfRank 3 B) : wGroup B = W := by
  have hA3 := hA.1.isAbelianTwoOfRank hA.2.ge
  rw [← hWD, wGroup_eq_of_commute hGW hB hA3 fun u hu v hv => (hAc v hv u (hBS hu)).symm,
    wGroup_eq_of_commute hGW hA3 (hD.1.isAbelianTwoOfRank hD.2.ge) fun u hu v hv =>
      hAc u hu v (hDS hv)]


omit [Finite G]
  in
theorem wordPerm_tg_mul_self_of_mem {d : ℕ × ℕ × ℕ × ℕ} (hd : d ∈ sqData) (hk : d.1 < 64) :
    wordPerm (tg d.1) * wordPerm (tg d.1) = 1 := by
  have h := congrArg sigma (sq_spec hd)
  rw [map_pow, sigma_tw _ hk, map_mul, map_mul, map_pow, map_pow, map_pow, sigma_z₁, sigma_z₂,
    sigma_z₃, one_pow, one_pow, one_pow, mul_one, mul_one] at h
  rw [← pow_two]
  exact h

theorem exists_central_eight {K S : Subgroup G} {hSN : S ≤ normalizer (K : Set G)}
    (D : WStd K S hSN) (hK : ⁅K, K⁆ = K) (hS2 : IsPGroup 2 S) (hZ : S ⊓ zStarIn K = ⊥)
    {a : G} (haS : a ∈ S) (haa : a * a = 1) (ha1 : a ≠ 1) (hcent : ∀ s ∈ S, s * a = a * s)
    (haK : a ∈ coreActionKernel K) :
    ∃ A : Subgroup G, A ≤ S ⊓ withKernel K ∧ IsEightGroup A ∧
      ∀ x ∈ A, ∀ b ∈ S ⊓ withKernel K, x * b = b * x := by
  have hinj : ∀ p (hp : p ∈ S), p ∈ K → D.ψ ⟨p, hp⟩ = 1 → p = 1 := by
    intro p hp hpK h1
    have hpC := (D.ψ_eq_one_iff hK hp).1 h1
    have := mem_inf.mpr ⟨hp, mem_zStarIn_of_mem_coreActionKernel hpK hpC⟩
    rwa [hZ, mem_bot] at this
  have hlift : ∀ k < 64, ∃ p, ∃ hp : p ∈ S, p ∈ K ∧ D.ψ ⟨p, hp⟩ = wordPerm (tg k) := by
    intro k hk
    obtain ⟨p, hp, hpK, hpe⟩ := (D.hT0 (nfM D.l (k, 0, 0))).1 (by
      rw [q_nfM D.hQ (show (k, (0 : ZMod 4), (0 : ZMod 4)).1 < 64 from hk)]
      exact tg_mem_T0 k hk)
    refine ⟨p, (mem_inf.mp hp).1, hpK, ?_⟩
    rw [D.ψ_eq_q (mem_inf.mp hp).1 hpK, hpe,
      q_nfM D.hQ (show (k, (0 : ZMod 4), (0 : ZMod 4)).1 < 64 from hk)]
  have hcomm : ∀ p (hp : p ∈ S), p ∈ K →
      D.ψ ⟨p, hp⟩ ∈ centralizer (T0 : Set (Equiv.Perm (Fin 42))) →
      ∀ b ∈ S ⊓ withKernel K, p * b = b * p := by
    intro p hp hpK hpc b hb
    obtain ⟨hbS, hbK⟩ := mem_inf.mp hb
    have hbT := D.ψ_mem_T0 hS2 hbS hbK
    have hcS : p * b * p⁻¹ * b⁻¹ ∈ S :=
      mul_mem (mul_mem (mul_mem hp hbS) (inv_mem hp)) (inv_mem hbS)
    have hcK : p * b * p⁻¹ * b⁻¹ ∈ K := by
      have h1 : b * p⁻¹ * b⁻¹ ∈ K := (mem_normalizer_iff.mp (hSN hbS) _).mp (inv_mem hpK)
      have := mul_mem hpK h1
      rwa [show p * (b * p⁻¹ * b⁻¹) = p * b * p⁻¹ * b⁻¹ by group] at this
    have hψ : D.ψ ⟨p * b * p⁻¹ * b⁻¹, hcS⟩ = 1 := by
      have he : (⟨p * b * p⁻¹ * b⁻¹, hcS⟩ : ↥S) =
          ⟨p, hp⟩ * ⟨b, hbS⟩ * (⟨p, hp⟩ : ↥S)⁻¹ * (⟨b, hbS⟩ : ↥S)⁻¹ := rfl
      rw [he, map_mul, map_mul, map_mul, map_inv, map_inv,
        ← (mem_centralizer_iff.mp hpc _ hbT), mul_inv_cancel_right, mul_inv_cancel]
    have h1 := hinj _ hcS hcK hψ
    calc p * b = p * b * p⁻¹ * b⁻¹ * (b * p) := by group
      _ = b * p := by rw [h1, one_mul]
  obtain ⟨z₄, hz₄S, hz₄K, hz₄⟩ := hlift 4 (by norm_num)
  obtain ⟨z₈, hz₈S, hz₈K, hz₈⟩ := hlift 8 (by norm_num)
  have hc₄ : D.ψ ⟨z₄, hz₄S⟩ ∈ centralizer (T0 : Set (Equiv.Perm (Fin 42))) := by
    rw [hz₄]; exact tg_mem_centralizer_T0 (by decide)
  have hc₈ : D.ψ ⟨z₈, hz₈S⟩ ∈ centralizer (T0 : Set (Equiv.Perm (Fin 42))) := by
    rw [hz₈]; exact tg_mem_centralizer_T0 (by decide)
  have hsq : ∀ p (hp : p ∈ S), p ∈ K → D.ψ ⟨p, hp⟩ * D.ψ ⟨p, hp⟩ = 1 → p * p = 1 := by
    intro p hp hpK h
    refine hinj _ (mul_mem hp hp) (mul_mem hpK hpK) ?_
    rw [show (⟨p * p, mul_mem hp hp⟩ : ↥S) = ⟨p, hp⟩ * ⟨p, hp⟩ from rfl, map_mul, h]
  have hq₄ : z₄ * z₄ = 1 := hsq _ hz₄S hz₄K (by
    rw [hz₄]; exact wordPerm_tg_mul_self_of_mem (d := (4, 1, 1, 1)) (by decide) (by norm_num))
  have hq₈ : z₈ * z₈ = 1 := hsq _ hz₈S hz₈K (by
    rw [hz₈]; exact wordPerm_tg_mul_self_of_mem (d := (8, 1, 0, 0)) (by decide) (by norm_num))
  have hne1 : ∀ p (hp : p ∈ S) (k : ℕ), k < 64 → k ≠ 0 → D.ψ ⟨p, hp⟩ = wordPerm (tg k) →
      p ≠ 1 := by
    intro p hp k hk hk0 hψp h1
    subst h1
    have h0 : D.ψ ⟨1, hp⟩ = 1 := map_one D.ψ
    rw [hψp, ← wordPerm_tg_zero'] at h0
    exact hk0 (tg_injective hk (by norm_num) h0)
  have hz₄1 : z₄ ≠ 1 := hne1 _ hz₄S 4 (by norm_num) (by norm_num) hz₄
  have hz₈1 : z₈ ≠ 1 := hne1 _ hz₈S 8 (by norm_num) (by norm_num) hz₈
  have hz₈₄ : z₈ ≠ z₄ := by
    rintro rfl
    rw [hz₄] at hz₈
    exact absurd (tg_injective (by norm_num) (by norm_num) hz₈) (by norm_num)
  have hz₄₈ : z₄ * z₈ = z₈ * z₄ :=
    hcomm _ hz₄S hz₄K hc₄ z₈ (mem_inf.mpr ⟨hz₈S, mem_sup_left hz₈K⟩)
  have hz₈B : z₈ ∉ zpowers z₄ := fun h =>
    (GrS4.eq_one_or_eq_of_mem_zpowers hq₄ h).elim hz₈1 hz₈₄
  obtain ⟨hB, hBc⟩ := GrS4.isElemTwo_sup_zpowers (isElemTwo_zpowers hq₄) hq₈ hz₈B
    (fun e he => by
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp he
      exact (Commute.zpow_left hz₄₈ n))
  have hBSK : zpowers z₄ ⊔ zpowers z₈ ≤ S ⊓ K :=
    sup_le (zpowers_le.mpr (mem_inf.mpr ⟨hz₄S, hz₄K⟩))
      (zpowers_le.mpr (mem_inf.mpr ⟨hz₈S, hz₈K⟩))
  have haB : a ∉ zpowers z₄ ⊔ zpowers z₈ := fun h => by
    have haK' : a ∈ K := (hBSK h).2
    exact ha1 (hinj a haS haK' ((D.ψ_eq_one_iff hK haS).2 haK))
  obtain ⟨hA, hAc⟩ := GrS4.isElemTwo_sup_zpowers hB haa haB fun e he => hcent e ((hBSK he).1)
  have hcard4 : Nat.card ↥(zpowers z₄) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hq₄) hz₄1]
  have hAS : zpowers z₄ ⊔ zpowers z₈ ⊔ zpowers a ≤ S ⊓ withKernel K :=
    sup_le (hBSK.trans (inf_le_inf_left _ le_sup_left))
      (zpowers_le.mpr (mem_inf.mpr ⟨haS, mem_sup_right haK⟩))
  refine ⟨_, hAS, ⟨hA, by rw [hAc, hBc, hcard4]⟩, fun x hx b hb => ?_⟩
  have hle : zpowers z₄ ⊔ zpowers z₈ ⊔ zpowers a ≤ centralizer ({b} : Set G) :=
    sup_le (sup_le
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hcomm _ hz₄S hz₄K hc₄ b hb)))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hcomm _ hz₈S hz₈K hc₈ b hb))))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hcent b (mem_inf.mp hb).1).symm))
  exact mem_centralizer_singleton_iff.mp (hle hx)

end CFSG.ComponentClassification.GrSLit.GrS5S

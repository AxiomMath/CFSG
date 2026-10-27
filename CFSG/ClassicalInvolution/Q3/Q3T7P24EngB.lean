module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24A02
public import CFSG.ClassicalInvolution.Asc77.AscS24CGraph

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem mul_nf_of {x₁ x₃ : G} (hc : Commute x₁ x₃) (a b c d : ℤ) :
    x₁ ^ a * x₃ ^ b * (x₁ ^ c * x₃ ^ d) = x₁ ^ (a + c) * x₃ ^ (b + d) := by
  have h := (hc.zpow_zpow c b).eq
  calc x₁ ^ a * x₃ ^ b * (x₁ ^ c * x₃ ^ d)
      = x₁ ^ a * (x₃ ^ b * x₁ ^ c) * x₃ ^ d := by group
    _ = x₁ ^ a * (x₁ ^ c * x₃ ^ b) * x₃ ^ d := by rw [← h]
    _ = x₁ ^ (a + c) * x₃ ^ (b + d) := by rw [zpow_add, zpow_add]; group

theorem conj_x₃_zpow_r_of {x₁ x₃ r : G} (hr₃ : r * x₃ * r⁻¹ = x₃ * x₁) (hc : Commute x₁ x₃)
    (n : ℤ) : x₃ ^ n * r * (x₃ ^ n)⁻¹ = x₁ ^ (-n) * r := by
  have h1 : r * x₃ ^ (-n) * r⁻¹ = x₃ ^ (-n) * x₁ ^ (-n) := by
    rw [← conj_zpow, hr₃, hc.symm.mul_zpow]
  calc x₃ ^ n * r * (x₃ ^ n)⁻¹
      = x₃ ^ n * (r * x₃ ^ (-n) * r⁻¹) * r := by group
    _ = x₁ ^ (-n) * r := by rw [h1]; group

theorem fix_of_trivMu_of (c : Q3CL.Thompson.Ctx Ω W) {t : G}
    (htN : t ∈ Subgroup.normalizer (W : Set G)) (hT : TrivMu Ω W t) (ρ : Thompson.Rep Ω W) :
    conjSub t ρ.K = ρ.K := by
  have hrM : ρ.r ∈ MGrp Ω W := Thompson.le_MGrp_of_mem_D ρ.hR ρ.hr
  have h := hT ρ.r hrM
  have hN1 : t * ρ.r * t⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ htN ρ.r_mem_normalizer) (Subgroup.inv_mem _ htN)
  have h1 := Thompson.piG_of_mem_sup h
  rw [Thompson.piG_mul hN1 (Subgroup.inv_mem _ ρ.r_mem_normalizer),
    Thompson.piG_mul (Subgroup.mul_mem _ htN ρ.r_mem_normalizer) (Subgroup.inv_mem _ htN),
    Thompson.piG_mul htN ρ.r_mem_normalizer, Thompson.piG_inv htN,
    Thompson.piG_inv ρ.r_mem_normalizer] at h1
  refine (T7D.conj_stable c htN ρ ?_).1
  unfold Thompson.Rep.img
  exact mul_inv_eq_one.mp h1

theorem fix_J_of_of (c : Q3CL.Thompson.Ctx Ω W) (ρ₃ : Thompson.Rep Ω W) {y w : G}
    (hy : y ∈ Subgroup.normalizer (W : Set G)) (hw : w ∈ Subgroup.normalizer (W : Set G))
    (h : Thompson.piG W y * ρ₃.img * (Thompson.piG W y)⁻¹ =
      Thompson.piG W w * ρ₃.img * (Thompson.piG W w)⁻¹) :
    conjSub (w⁻¹ * y) ρ₃.K = ρ₃.K := by
  have hn : w⁻¹ * y ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hw) hy
  refine (T7D.conj_stable c hn ρ₃ ?_).1
  rw [Thompson.piG_mul (Subgroup.inv_mem _ hw) hy, Thompson.piG_inv hw]
  calc (Thompson.piG W w)⁻¹ * Thompson.piG W y * ρ₃.img *
        ((Thompson.piG W w)⁻¹ * Thompson.piG W y)⁻¹
      = (Thompson.piG W w)⁻¹ * (Thompson.piG W y * ρ₃.img * (Thompson.piG W y)⁻¹) *
          Thompson.piG W w := by group
    _ = ρ₃.img := by rw [h]; group

theorem closure_frame_eq_top_of (F : T7E.Frame4 Ω W) (φ : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4))
    (hφ : ∀ x, x ∈ Thompson.muDelta Ω W ↔ (φ x).IsSwap)
    (hab₀ : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ')
    (hcomm₀ : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ)
    (hac₀ : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ) :
    Subgroup.closure ({T7D.imgQ F.ρ, T7D.imgQ F.ρ', T7D.imgQ F.ρ₃} :
      Set ↥(muGroup Ω W)) = ⊤ := by
  have hφmem : ∀ ρ : Thompson.Rep Ω W, φ (T7D.imgQ ρ) ∈ S4.swaps4 := fun ρ =>
    S4.mem_swaps4_of_isSwap ((hφ _).mp (T7D.imgQ_mem ρ))
  set a := φ (T7D.imgQ F.ρ)
  set b := φ (T7D.imgQ F.ρ')
  set c := φ (T7D.imgQ F.ρ₃)
  have hab : a ≠ b := fun h => hab₀ (φ.injective h)
  have hcomm : a * b = b * a := by
    simp only [a, b, ← map_mul, hcomm₀]
  have hac : a * c ≠ c * a := by
    intro h
    apply hac₀
    apply φ.injective
    simpa only [a, c, map_mul] using h
  have htop : Subgroup.closure ({a, b, c} : Set (Equiv.Perm (Fin 4))) = ⊤ := by
    rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
    intro t ht
    have ht' := S4.mem_swaps4_of_isSwap ht
    have hmem : ∀ x ∈ ({a, b, c} : Set (Equiv.Perm (Fin 4))),
        x ∈ Subgroup.closure ({a, b, c} : Set (Equiv.Perm (Fin 4))) :=
      fun x hx => Subgroup.subset_closure hx
    have ha := hmem a (by simp)
    have hb := hmem b (by simp)
    have hc := hmem c (by simp)
    rcases S4.swap_word a (hφmem _) b (hφmem _) c (hφmem _) hab hcomm hac t
        ht' with h | h | h | h | h | h <;> rw [h]
    · exact ha
    · exact hb
    · exact hc
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hc) ha
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb hc) hb
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mul_mem _ ha hb) hc) hb) ha
  have hmap := congrArg (Subgroup.map φ.symm.toMonoidHom) htop
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ φ.symm.surjective] at hmap
  rw [← hmap]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨a, Or.inl rfl, by simp [a]⟩
    · exact ⟨b, Or.inr (Or.inl rfl), by simp [b]⟩
    · exact ⟨c, Or.inr (Or.inr rfl), by simp [c]⟩
  · rintro ⟨y, hy | hy | hy, rfl⟩ <;> subst hy <;> simp [a, b, c]
end S24B
open scoped Pointwise
namespace S24
open CFSG.ClassicalInvolution.Asc77.S24
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem conj_t_zpow_of {x₂ x₃ r : G} (ht₃ : r * x₃ * r⁻¹ = x₃ * x₂) (hc : Commute x₂ x₃)
    (n : ℤ) : x₃ ^ n * r * (x₃ ^ n)⁻¹ = x₂ ^ (-n) * r := by
  have h1 : r * x₃ ^ (-n) * r⁻¹ = x₃ ^ (-n) * x₂ ^ (-n) := by
    rw [← conj_zpow, ht₃, hc.symm.mul_zpow]
  calc x₃ ^ n * r * (x₃ ^ n)⁻¹
      = x₃ ^ n * (r * x₃ ^ (-n) * r⁻¹) * r := by group
    _ = x₂ ^ (-n) * r := by rw [h1]; group

theorem piG_eq_one_of_trivMu_of (φ : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)) {m : G}
    (hm : m ∈ MGrp Ω W) (hT : S24B.TrivMu Ω W m) : Thompson.piG W m = 1 := by
  have hcent : ∀ y : ↥(muGroup Ω W), S24B.piM Ω W ⟨m, hm⟩ * y = y * S24B.piM Ω W ⟨m, hm⟩ := by
    intro y
    obtain ⟨n, rfl⟩ := S24B.piM_surjective W y
    have h1 : S24B.piM Ω W (⟨m, hm⟩ * n * (⟨m, hm⟩)⁻¹ * n⁻¹) = 1 := by
      apply Subtype.ext
      rw [S24B.piM_apply]
      exact Thompson.piG_of_mem_sup (hT n n.2)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 := mul_inv_eq_one.mp h1
    calc S24B.piM Ω W ⟨m, hm⟩ * S24B.piM Ω W n
        = S24B.piM Ω W ⟨m, hm⟩ * S24B.piM Ω W n * (S24B.piM Ω W ⟨m, hm⟩)⁻¹ *
            S24B.piM Ω W ⟨m, hm⟩ := by group
      _ = S24B.piM Ω W n * S24B.piM Ω W ⟨m, hm⟩ := by rw [h2]
  have hφ : ∀ σ : Equiv.Perm (Fin 4),
      φ (S24B.piM Ω W ⟨m, hm⟩) * σ = σ * φ (S24B.piM Ω W ⟨m, hm⟩) := by
    intro σ
    have h2 := congrArg φ (hcent (φ.symm σ))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  have hq1 : S24B.piM Ω W ⟨m, hm⟩ = 1 := by
    have h := S24B.perm4_center _ (hφ _) (hφ _) (hφ _)
    exact φ.injective (h.trans (map_one φ).symm)
  have h := congrArg Subtype.val hq1
  rw [S24B.piM_apply] at h
  exact h

theorem conjSub_eq_of_conj_of (hΩ : HypOmegaMod Ω) {L : Subgroup G} (hL : L ∈ Ω) {x m : G}
    (hx : x ∈ L) (o : orderOf x = 4) (h : m⁻¹ * x * m = x ∨ m⁻¹ * x * m = x⁻¹) :
    conjSub m L = L := by
  have hxm : x ∈ conjSub m L := by
    rw [mem_conjSub_iff]
    rcases h with h | h <;> rw [h]
    · exact hx
    · exact L.inv_mem hx
  have h2 : IsPGroup 2 ↥(Subgroup.zpowers x) := T7A.isPGroup_zpowers_of_orderOf_four o
  have h4 : 4 ≤ Nat.card ↥(Subgroup.zpowers x) := by rw [Nat.card_zpowers, o]
  exact hΩ.eq_of_le_of_le (hΩ.conjInvariant m L hL) hL h2 h4
    (Subgroup.zpowers_le.mpr hxm) (Subgroup.zpowers_le.mpr hx)

theorem conj_mem_sZero_of {S : Sylow 2 G}
    (hN : ∀ {s : G}, s ∈ (S : Subgroup G) → s ∈ Subgroup.normalizer (W : Set G))
    (hMN : ∀ {s : G}, s ∈ Subgroup.normalizer (W : Set G) →
      s ∈ Subgroup.normalizer (MGrp Ω W : Set G)) {s x : G}
    (hs : s ∈ (S : Subgroup G)) (hx : x ∈ sZero Ω W S) : s * x * s⁻¹ ∈ sZero Ω W S := by
  obtain ⟨hxS, m, hm, h⟩ := hx
  have hsN := hN hs
  have hsM : s ∈ Subgroup.normalizer (MGrp Ω W : Set G) := hMN hsN
  refine ⟨S.mul_mem (S.mul_mem hs hxS) (S.inv_mem hs), s * m * s⁻¹,
    (Subgroup.mem_normalizer_iff.mp hsM m).mp hm, fun w hw => ?_⟩
  have hw' : s⁻¹ * w * s⁻¹⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsN) w).mp hw
  calc s * x * s⁻¹ * w * (s * x * s⁻¹)⁻¹ = s * (x * (s⁻¹ * w * s⁻¹⁻¹) * x⁻¹) * s⁻¹ := by group
    _ = s * (m * (s⁻¹ * w * s⁻¹⁻¹) * m⁻¹) * s⁻¹ := by rw [h _ hw']
    _ = s * m * s⁻¹ * w * (s * m * s⁻¹)⁻¹ := by group
end S24
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8

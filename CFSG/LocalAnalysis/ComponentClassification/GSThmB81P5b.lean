module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81P5

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Eight

variable {G : Type*} [Group G]

theorem conj_mul_of_comm {x y w : G} (hxy : x * y = y * x) :
    x * (w * y) * x⁻¹ = x * w * x⁻¹ * y := by
  have hyx : y * x⁻¹ = x⁻¹ * y := by
    calc y * x⁻¹ = x⁻¹ * (x * y) * x⁻¹ := by group
      _ = x⁻¹ * (y * x) * x⁻¹ := by rw [hxy]
      _ = x⁻¹ * y := by group
  calc x * (w * y) * x⁻¹ = x * w * (y * x⁻¹) := by group
    _ = x * w * (x⁻¹ * y) := by rw [hyx]
    _ = x * w * x⁻¹ * y := by group

end Eight

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

theorem center_D_cases (hSy : CFL2Sylow) (F : d.Facts) {e : H} (he : e ∈ h.D)
    (hec : ∀ u ∈ h.D, e * u = u * e) : e = 1 ∨ e = d.z := by
  obtain ⟨T, hT, hTD⟩ := h.toHyp52.sec8_exists_sylow_Dbar
  obtain ⟨p', f', hp', hp2', hf', hJL⟩ := H₁.exists_lieModel_Jbar
  obtain ⟨hZ2, -, -⟩ := hSy _ p' f' hp' hp2' hf' hJL T (hTD ▸ F.eight_le)
  set q := QuotientGroup.mk' (pPrimeCore 2 ↥h.J) with hq
  have hinj := injOn_D (h := h)
  have hDJ : h.D ≤ h.J := inf_le_right
  set Z := (T : Subgroup (h.J ⧸ pPrimeCore 2 h.J)) ⊓
    centralizer ((T : Subgroup (h.J ⧸ pPrimeCore 2 h.J)) : Set (h.J ⧸ pPrimeCore 2 h.J)) with hZ
  have hmapZ : ∀ x (hx : x ∈ h.D), (∀ u ∈ h.D, x * u = u * x) → q ⟨x, hDJ hx⟩ ∈ Z := by
    intro x hx hxc
    refine mem_inf.mpr ⟨?_, mem_centralizer_iff.mpr ?_⟩
    · rw [hT]; exact mem_map_of_mem _ (mem_subgroupOf.mpr hx)
    · intro y hy
      rw [hT] at hy
      obtain ⟨u, hu, rfl⟩ := mem_map.mp hy
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hxc u (mem_subgroupOf.mp hu)).symm
  have hqz := hmapZ d.z d.z_D (fun u hu => (mem_centralizer_iff.mp d.z_S u
    (h.toHyp52.D_le_S hu)).symm)
  have hqz1 : q ⟨d.z, hDJ d.z_D⟩ ≠ 1 := by
    intro h1
    apply d.z_ne_one
    have := hinj (mem_subgroupOf.mpr d.z_D) (mem_subgroupOf.mpr (one_mem h.D))
      (h1.trans (map_one q).symm)
    exact congrArg Subtype.val this
  have hord : orderOf (q ⟨d.z, hDJ d.z_D⟩) = 2 := by
    have h1 : orderOf (q ⟨d.z, hDJ d.z_D⟩) ∣ 2 := by
      have := Subgroup.card_dvd_of_le (zpowers_le.mpr hqz)
      rwa [Nat.card_zpowers, hZ2] at this
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.mp h2) hqz1
    · exact h2
  have hZeq : zpowers (q ⟨d.z, hDJ d.z_D⟩) = Z :=
    eq_of_le_of_card_ge (zpowers_le.mpr hqz) (by rw [hZ2, Nat.card_zpowers, hord])
  have hzz : q ⟨d.z, hDJ d.z_D⟩ * q ⟨d.z, hDJ d.z_D⟩ = 1 := by
    have := pow_orderOf_eq_one (q ⟨d.z, hDJ d.z_D⟩)
    rwa [hord, pow_two] at this
  by_cases he1 : e = 1
  · exact Or.inl he1
  · right
    have hqe : q ⟨e, hDJ he⟩ ∈ zpowers (q ⟨d.z, hDJ d.z_D⟩) := hZeq ▸ hmapZ e he hec
    rcases eq_one_or_of_mem_zpowers_of_mul_self hzz hqe with h1 | h1
    · exfalso
      apply he1
      have := hinj (mem_subgroupOf.mpr he) (mem_subgroupOf.mpr (one_mem h.D))
        (h1.trans (map_one q).symm)
      exact congrArg Subtype.val this
    · have := hinj (mem_subgroupOf.mpr he) (mem_subgroupOf.mpr d.z_D) h1
      exact congrArg Subtype.val this

theorem D_comm_sigma (F : d.Facts) : ∀ x ∈ h.D, ∀ y ∈ zpowers d.sigma, x * y = y * x := by
  intro x hx y hy
  rcases eq_one_or_of_mem_zpowers_of_mul_self d.sigma_mul_self hy with rfl | rfl
  · rw [one_mul, mul_one]
  · exact d.D_comm_R0 F x hx d.sigma sigma_mem_R0

theorem a_not_mem_D_sup_sigma (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (F : d.Facts) : h.a ∉ h.D ⊔ zpowers d.sigma := by
  intro ha
  obtain ⟨e, he, w, hw, hew⟩ := Eight.exists_mul_of_mem_sup₂ (D_comm_sigma F) ha
  rcases eq_one_or_of_mem_zpowers_of_mul_self d.sigma_mul_self hw with rfl | rfl
  · rw [mul_one] at hew
    have := (h.toHyp52.D_inf_P_eq_bot H₁.center_J) ▸
      mem_inf.mpr ⟨hew ▸ he, h.toHyp52.a_mem_P⟩
    exact a_ne_one' (h := h) (mem_bot.mp this)
  · apply d.sigma_not_mem_DP hCF1 hCF2 F
    have := mul_mem_sup (inv_mem he) h.toHyp52.a_mem_P
    rwa [hew, inv_mul_cancel_left] at this

theorem F32_le_D_sup_R0 (I : In81) (F : d.Facts) : h.F32 ≤ h.D ⊔ d.R0 :=
  Eight.JeN_le_of fun _ hES hE2 hE32 => d.le_D_sup_R0 I.rk I.j I.c I.cf1 I.cf2 F hES hE2 hE32

section Five

variable {v : H} (hv : d.IsV v) (I : In81) (F : d.Facts)
  (h3 : ∀ c : H, c⁻¹ * (h.a * d.sigma) * c ≠ d.sigma)
include hv I F

omit I F in
theorem conjugate_D_le_F (hDF : h.D ≤ h.F32) : conjugate h.D v ≤ h.F32 := by
  intro x hx
  rw [mem_conjugate_iff] at hx
  have h1 := (mem_normalizer_iff.mp (inv_mem (h.normalizer_S_le_normalizer_F32 hv.mem_N)) _).mp
    (hDF hx)
  rwa [inv_inv, show v⁻¹ * (v * x * v⁻¹) * v = x by group] at h1

theorem conjugate_D_inf_eq_bot : conjugate h.D v ⊓ (h.D ⊔ zpowers d.sigma) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDvF := conjugate_D_le_F hv (d.D_le_F I.sy I.cf1 I.cf2 F)
  have hDvS : conjugate h.D v ≤ h.S := hDvF.trans h.F32_le_S
  have hDv2 : IsPGroup 2 (conjugate h.D v) := h.toHyp52.isPGroup_S.to_le hDvS
  have hσF := d.F32_le_centralizer_sigma I.rk I.j I.c I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 F
  by_contra hne
  obtain ⟨x, hx, hx1, hxZ⟩ := Seven.exists_mem_center_of_normal hDv2 inf_le_left
    (fun s hs n hn => by
      obtain ⟨hnDv, hnB⟩ := mem_inf.mp hn
      refine mem_inf.mpr ⟨mul_mem (mul_mem hs hnDv) (inv_mem hs), ?_⟩
      have hsS := hDvS hs
      have hsσ : s * d.sigma = d.sigma * s := mem_centralizer_singleton_iff.mp (hσF (hDvF hs))
      obtain ⟨e, he, w, hw, rfl⟩ := Eight.exists_mul_of_mem_sup₂ (D_comm_sigma F) hnB
      have hse : s * e * s⁻¹ ∈ h.D := mem_inf.mpr ⟨mul_mem (mul_mem hsS (mem_inf.mp he).1)
        (inv_mem hsS), (mem_normalizer_iff.mp (h.toHyp52.S_le_normalizer hsS) e).mp
          (mem_inf.mp he).2⟩
      rcases eq_one_or_of_mem_zpowers_of_mul_self d.sigma_mul_self hw with rfl | rfl
      · rw [mul_one]; exact mem_sup_left hse
      · rw [Eight.conj_mul_of_comm hsσ]
        exact mul_mem (mem_sup_left hse) (mem_sup_right (mem_zpowers _))) hne
  obtain ⟨hxDv, hxB⟩ := mem_inf.mp hx
  have hx' : v * x * v⁻¹ ∈ h.D := mem_conjugate_iff.mp hxDv
  have hxc : ∀ u ∈ h.D, v * x * v⁻¹ * u = u * (v * x * v⁻¹) := by
    intro u hu
    have hu' : v⁻¹ * u * v ∈ conjugate h.D v := by
      rw [mem_conjugate_iff, show v * (v⁻¹ * u * v) * v⁻¹ = u by group]
      exact hu
    have h1 := hxZ _ hu'
    calc v * x * v⁻¹ * u = v * (x * (v⁻¹ * u * v)) * v⁻¹ := by group
      _ = v * ((v⁻¹ * u * v) * x) * v⁻¹ := by rw [h1]
      _ = u * (v * x * v⁻¹) := by group
  rcases center_D_cases I.sy F hx' hxc with h1 | h1
  · apply hx1
    calc x = v⁻¹ * (v * x * v⁻¹) * v := by group
      _ = 1 := by rw [h1]; group
  · have hxa : x = h.a := by
      calc x = v⁻¹ * (v * x * v⁻¹) * v := by group
        _ = v⁻¹ * d.z * v := by rw [h1]
        _ = h.a := hv.conj_z
    rw [hxa] at hxB
    exact d.a_not_mem_D_sup_sigma I.cf1 I.cf2 F hxB

include h3

theorem card_D_le_card_FP : Nat.card h.D ≤ Nat.card ↥(h.F32 ⊓ h.P) := by
  set B := h.D ⊔ zpowers d.sigma with hB
  set M := B ⊔ (h.F32 ⊓ h.P) with hM
  have hσP : ∀ π ∈ h.P, d.sigma * π = π * d.sigma := fun π hπ => sigma_comm_P I F h3 hπ
  have hcBP : ∀ x ∈ B, ∀ y ∈ h.F32 ⊓ h.P, x * y = y * x := by
    intro x hx y hy
    obtain ⟨e, he, w, hw, rfl⟩ := Eight.exists_mul_of_mem_sup₂ (D_comm_sigma F) hx
    have hyP := (mem_inf.mp hy).2
    have hey : e * y = y * e := H₁.D_comm_P he hyP
    have hwy : w * y = y * w := by
      rcases eq_one_or_of_mem_zpowers_of_mul_self d.sigma_mul_self hw with rfl | rfl
      · rw [one_mul, mul_one]
      · exact hσP y hyP
    rw [mul_assoc, hwy, ← mul_assoc, hey, mul_assoc]
  have hdBP : B ⊓ (h.F32 ⊓ h.P) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxB, hxFP⟩ := mem_inf.mp hx
    obtain ⟨e, he, w, hw, rfl⟩ := Eight.exists_mul_of_mem_sup₂ (D_comm_sigma F) hxB
    have hxP := (mem_inf.mp hxFP).2
    rcases eq_one_or_of_mem_zpowers_of_mul_self d.sigma_mul_self hw with rfl | rfl
    · rw [mul_one] at hxP ⊢
      have := (h.toHyp52.D_inf_P_eq_bot H₁.center_J) ▸ mem_inf.mpr ⟨he, hxP⟩
      exact this
    · exfalso
      apply d.sigma_not_mem_DP I.cf1 I.cf2 F
      have := mul_mem_sup (inv_mem he) hxP
      rwa [inv_mul_cancel_left] at this
  have hMcard := Seven.card_sup_of_commute hcBP hdBP
  have hDvM : conjugate h.D v ≤ M := by
    intro x hx
    have hxF := conjugate_D_le_F hv (d.D_le_F I.sy I.cf1 I.cf2 F) hx
    obtain ⟨e, he, r, hr, rfl⟩ := Eight.exists_mul_of_mem_sup₂ (d.D_comm_R0 F)
      (F32_le_D_sup_R0 I F hxF)
    have hrF : r ∈ h.F32 := by
      have := mul_mem (inv_mem (d.D_le_F I.sy I.cf1 I.cf2 F he)) hxF
      rwa [inv_mul_cancel_left] at this
    have hσF : d.sigma ∈ h.F32 := sigma_mem_F I F
    obtain ⟨π, hπ, hr' | hr'⟩ := d.mem_R0_cases hr
    · subst hr'
      exact mul_mem (mem_sup_left (mem_sup_left he)) (mem_sup_right (mem_inf.mpr ⟨hrF, hπ⟩))
    · have hπF : π ∈ h.F32 := by
        have := mul_mem hrF (inv_mem hσF)
        rwa [hr', mul_inv_cancel_right] at this
      rw [hr', ← hσP π hπ, ← mul_assoc]
      exact mul_mem (mem_sup_left (mul_mem (mem_sup_left he) (mem_sup_right (mem_zpowers _))))
        (mem_sup_right (mem_inf.mpr ⟨hπF, hπ⟩))
  have hdisj := conjugate_D_inf_eq_bot hv I F
  let φ : ↥(conjugate h.D v) × ↥B → ↥M := fun x =>
    ⟨x.1 * x.2, mul_mem (hDvM x.1.2) (mem_sup_left x.2.2)⟩
  have hφ : Function.Injective φ := by
    rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ heq
    have h1 : (x₁ : H) * y₁ = x₂ * y₂ := congrArg Subtype.val heq
    have h2 : (x₂ : H)⁻¹ * x₁ = y₂ * (y₁ : H)⁻¹ := by
      calc (x₂ : H)⁻¹ * x₁ = (x₂ : H)⁻¹ * (x₁ * y₁) * (y₁ : H)⁻¹ := by group
        _ = (x₂ : H)⁻¹ * (x₂ * y₂) * (y₁ : H)⁻¹ := by rw [h1]
        _ = y₂ * (y₁ : H)⁻¹ := by group
    have hmem : (x₂ : H)⁻¹ * x₁ ∈ conjugate h.D v ⊓ B :=
      mem_inf.mpr ⟨mul_mem (inv_mem x₂.2) x₁.2, h2 ▸ mul_mem y₂.2 (inv_mem y₁.2)⟩
    rw [hdisj] at hmem
    have hx : (x₁ : H) = x₂ := by
      have h3' := mem_bot.mp hmem
      calc (x₁ : H) = x₂ * ((x₂ : H)⁻¹ * x₁) := by group
        _ = x₂ := by rw [h3', mul_one]
    have hy : (y₁ : H) = y₂ := by
      rw [hx] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  have hcard := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, hMcard, Eight.card_conjugate', mul_comm] at hcard
  exact Nat.le_of_mul_le_mul_left hcard Nat.card_pos

theorem P_le_F (hFO : CF81FieldOrd) : h.P ≤ h.F32 := by
  have h1 := card_P_le_card_D hv I F h3 hFO
  have h2 := card_D_le_card_FP hv I F h3
  have h4 : Nat.card h.P ≤ Nat.card ↥(h.F32 ⊓ h.P) := h1.trans h2
  have heq := eq_of_le_of_card_ge (inf_le_right : h.F32 ⊓ h.P ≤ h.P) h4
  rw [← heq]
  exact inf_le_left

theorem card_P_eq_card_D (hFO : CF81FieldOrd) : Nat.card h.P = Nat.card h.D :=
  le_antisymm (card_P_le_card_D hv I F h3 hFO)
    ((card_D_le_card_FP hv I F h3).trans (Subgroup.card_le_of_le inf_le_right))

end Five

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB

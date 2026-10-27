module

public import CFSG.CGT.Stroth77.Stroth34T201Normal
public import CFSG.CGT.Stroth77.Stroth34Arith

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)
open Stroth34T201

namespace Stroth34T201

theorem not_dvd_one_add_sub_one {m : ℕ} : ¬ (2 : ℤ) ^ (m + 2) ∣ (1 + 2 ^ (m + 1)) - 1 := by
  rw [show (1 + 2 ^ (m + 1) : ℤ) - 1 = 2 ^ (m + 1) * 1 by ring]
  exact Stroth34T200.not_two_pow_succ_dvd_mul_odd (m + 1) (by norm_num)

theorem not_dvd_one_add_add_one {m : ℕ} (hm : 1 ≤ m) :
    ¬ (2 : ℤ) ^ (m + 2) ∣ (1 + 2 ^ (m + 1)) - (-1) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rintro ⟨k, hk⟩
  have h2 : (2 : ℤ) * 1 = 2 * (2 * (2 * 2 ^ j * k - 2 ^ j)) := by linear_combination hk
  have h1 := mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0) h2
  generalize 2 * 2 ^ j * k - 2 ^ j = w at h1
  omega

theorem not_dvd_two' {m : ℕ} : ¬ (2 : ℤ) ^ (m + 2) ∣ (1 + 2 ^ (m + 1)) - (-1 + 2 ^ (m + 1)) := by
  rintro ⟨k, hk⟩
  have h2 : (2 : ℤ) * 1 = 2 * (2 * (2 ^ m * k)) := by linear_combination hk
  have h1 := mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0) h2
  generalize 2 ^ m * k = w at h1
  omega

end Stroth34T201

namespace Normal201

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t201 m)} {hS : Local.Setting (F.S : Subgroup G) D}

theorem odd {e : G} {y p : ℤ} (hn : Normal201 hS dD e y p) : y % 2 = 1 := by
  by_contra hy
  obtain ⟨k, hk⟩ : (2 : ℤ) ∣ y := Int.dvd_of_emod_eq_zero (by omega)
  have heN := hS.R_le_normalizer hn.mem.1
  have h1 := hn.scalar ((2 ^ (m + 1) : ℤ) • Torus.ofInt (StrothTypeIndex.t201 m).k ![0, 1, 0])
  have h2 : (y * 2 ^ (m + 1)) • Torus.ofInt (StrothTypeIndex.t201 m).k ![0, 1, 0] = 0 := by
    rw [hk, t201_zsmul_vec, t201_vec_eq_zero_iff]
    exact ⟨⟨0, by ring⟩, ⟨k, by ring⟩, ⟨0, by ring⟩⟩
  rw [smul_smul, h2] at h1
  have h3 := congrArg (dD.thetaT (inv_mem heN)) h1
  rw [dD.thetaT_inv_thetaT, map_zero, t201_zsmul_vec, t201_vec_eq_zero_iff] at h3
  exact Stroth34T200.not_two_pow_succ_dvd_mul_odd (m + 1) (z := 1) (by norm_num) h3.2.1

end Normal201

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t201 m)}

theorem t201_conj_mem_R1_of_scalar (hS : Local.Setting (F.S : Subgroup G) D)
    (hsc : ∀ f (hf : f ∈ hS.R1 dD.uv dD.t), ∃ y : ℤ,
      ∀ v, dD.thetaT (hS.R_le_normalizer hf.1) v = y • v)
    {g e : G} (hg : g ∈ hS.R) (he : e ∈ hS.R1 dD.uv dD.t) :
    g⁻¹ * e * g ∈ hS.R1 dD.uv dD.t := by
  obtain ⟨y, hy⟩ := hsc e he
  have hgN := hS.R_le_normalizer hg
  have heN := hS.R_le_normalizer he.1
  have hcR : g⁻¹ * e * g ∈ hS.R := mul_mem (mul_mem (inv_mem hg) he.1) hg
  have hcN := hS.R_le_normalizer hcR
  have h1 : ∀ v, dD.thetaT hcN v = dD.thetaT heN v := fun v => by
    rw [dD.thetaT_congr hcN (mul_mem (mul_mem (inv_mem hgN) heN) hgN) rfl, dD.thetaT_conj heN hgN]
    simp only [hy]
    rw [map_zsmul, dD.thetaT_thetaT_inv]
  have h2 : g⁻¹ * e * g * e⁻¹ ∈ D := by
    refine dD.mem_of_thetaT_id hS (mul_mem (hS.R_le_S hcR) (inv_mem (hS.R_le_S he.1)))
      (mul_mem hcN (inv_mem heN)) fun v => ?_
    rw [dD.thetaT_mul hcN (inv_mem heN), h1, dD.thetaT_inv_thetaT]
  have := mul_mem (t201_D_le_R1 hS h2) he
  simpa using this

theorem t201_R_le_normalizer_R1 (hS : Local.Setting (F.S : Subgroup G) D)
    (hsc : ∀ f (hf : f ∈ hS.R1 dD.uv dD.t), ∃ y : ℤ,
      ∀ v, dD.thetaT (hS.R_le_normalizer hf.1) v = y • v) :
    hS.R ≤ Subgroup.normalizer ((hS.R1 dD.uv dD.t : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff'']
  intro e
  refine ⟨fun he => t201_conj_mem_R1_of_scalar hS hsc hg he, fun he => ?_⟩
  have := t201_conj_mem_R1_of_scalar hS hsc (inv_mem hg) he
  rwa [show g⁻¹⁻¹ * (g⁻¹ * e * g) * g⁻¹ = e by group] at this

theorem t201_normal_of_scalar (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hm : 1 ≤ m) (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {g : G}
    (hg : g ∈ hS.R1 dD.uv dD.t) {y : ℤ}
    (hy : ∀ v, dD.thetaT (hS.R_le_normalizer hg.1) v = y • v) :
    ∃ d ∈ D, ∃ p : ℤ, Normal201 hS dD (g * d) y (2 * p) := by
  obtain ⟨d, hd, y', p, hn⟩ := h.exists_normal201 hS hm hfus hg
    (h.t201_conj_u_mul_inv_mem_of_scalar hS hg.1 hy)
  refine ⟨d, hd, p, hn.mem, hn.proj, hn.comm, fun v => ?_, hn.ruv, hn.rt⟩
  have hgN := hS.R_le_normalizer hg.1
  have hdN : d ∈ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer hd
  rw [dD.thetaT_congr _ (mul_mem hgN hdN) rfl, dD.thetaT_mul hgN hdN, dD.thetaT_of_mem hdN hd, hy]

theorem t201_exists_normal_two (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hm : 1 ≤ m) (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {f : G}
    (hf : f ∈ hS.R1 dD.uv dD.t) (hfD : f ∉ D) :
    ∃ e : G, ∃ y : ℤ, Normal201 hS dD e y 2 ∧ e ∉ D := by
  have two : ∀ {g : G} {y p : ℤ}, Normal201 hS dD g y (2 * p) → g ∉ D →
      ∃ e : G, ∃ y : ℤ, Normal201 hS dD e y 2 ∧ e ∉ D := by
    intro g y p hn hgD
    have hp2 : (4 : ℤ) ∣ 2 * p - 2 := by
      rcases Int.even_or_odd p with ⟨q, hq⟩ | ⟨q, hq⟩
      · exact absurd (hn.mem_of_dvd h ⟨q, by rw [hq]; ring⟩) hgD
      · exact ⟨q, by rw [hq]; ring⟩
    obtain ⟨d', hd', hn'⟩ := hn.renorm hp2
    exact ⟨g * d', y, hn', fun h' => hgD (by simpa using mul_mem h' (inv_mem hd'))⟩
  by_cases hue : dD.u⁻¹ * f * dD.u * f⁻¹ ∈ D
  · obtain ⟨d, hd, y, p, hn⟩ := h.exists_normal201 hS hm hfus hf hue
    exact two hn fun h' => hfD (by simpa using mul_mem h' (inv_mem hd))
  · obtain ⟨hg, hθ⟩ := h.t201_comm_u_scalar hS hm hf hue
    obtain ⟨d, hd, p, hn⟩ := h.t201_normal_of_scalar hS hm hfus hg hθ
    exact two hn fun h' => not_dvd_one_add_sub_one (hn.scalar_dvd_of_mem h')

theorem t201_case_inv (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {e : G} {y : ℤ}
    (hn : Normal201 hS dD e y 2)
    (hy : (2 : ℤ) ^ (m + 2) ∣ y + 1 ∨ (2 : ℤ) ^ (m + 2) ∣ y - (-1 + 2 ^ (m + 1))) :
    hS.R = D ⊔ Subgroup.zpowers e := by
  have hy1 : ¬ (2 : ℤ) ^ (m + 2) ∣ (1 + 2 ^ (m + 1)) - y := by
    rintro hd
    rcases hy with hy | hy
    · exact not_dvd_one_add_add_one hm (by
        have := dvd_add hd hy; rwa [show (1 + 2 ^ (m + 1) : ℤ) - y + (y + 1) =
          (1 + 2 ^ (m + 1)) - -1 by ring] at this)
    · exact not_dvd_two' (by have := dvd_add hd hy; rwa [sub_add_sub_cancel] at this)
  have hcls : ∀ {g : G} {y' p : ℤ}, Normal201 hS dD g y' (2 * p) → g ∈ D ∨ g * e⁻¹ ∈ D := by
    intro g y' p hg
    rcases Int.even_or_odd p with ⟨q, hq⟩ | ⟨q, hq⟩
    · exact Or.inl (hg.mem_of_dvd h ⟨q, by rw [hq]; ring⟩)
    · exact Or.inr (hg.mul_inv_mem h hn ⟨q, by rw [hq]; ring⟩)
  have hB1 : ∀ f ∈ hS.R1 dD.uv dD.t, dD.u⁻¹ * f * dD.u * f⁻¹ ∈ D := by
    intro f hf
    by_contra hue
    obtain ⟨hg, hθ⟩ := h.t201_comm_u_scalar hS hm hf hue
    obtain ⟨d, hd, p, hgn⟩ := h.t201_normal_of_scalar hS hm hfus hg hθ
    rcases hcls hgn with h1 | h1
    · exact not_dvd_one_add_sub_one (hgn.scalar_dvd_of_mem h1)
    · exact hy1 (hgn.scalar_dvd hn h1)
  have hB2 : ∀ f ∈ hS.R1 dD.uv dD.t, f ∈ D ⊔ Subgroup.zpowers e := by
    intro f hf
    obtain ⟨d, hd, y', p, hfn⟩ := h.exists_normal201 hS hm hfus hf (hB1 f hf)
    rcases hcls hfn with h1 | h1
    · have : f = f * d * d⁻¹ := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_left (inv_mem hd))
    · have : f = f * d * e⁻¹ * e * d⁻¹ := by group
      rw [this]
      exact mul_mem (mul_mem (Subgroup.mem_sup_left h1)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))) (Subgroup.mem_sup_left (inv_mem hd))
  have hB3 : ∀ g (hg : g ∈ hS.R1 dD.uv dD.t), g ∉ D → ∃ y₀ : ℤ,
      (y₀ = -1 ∨ y₀ = -1 + 2 ^ (m + 1)) ∧
        ∀ (hgN : g ∈ Subgroup.normalizer (D : Set G)) v, dD.thetaT hgN v = y₀ • v := by
    intro g hg hgD
    obtain ⟨d, hd, y', p, hgn⟩ := h.exists_normal201 hS hm hfus hg (hB1 g hg)
    have hdN : d ∈ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer hd
    have hθ : ∀ (hgN : g ∈ Subgroup.normalizer (D : Set G)) v, dD.thetaT hgN v = y' • v :=
      fun hgN v => by
        rw [← hgn.scalar v, dD.thetaT_congr _ (mul_mem hgN hdN) rfl, dD.thetaT_mul hgN hdN,
          dD.thetaT_of_mem hdN hd]
    rcases hcls hgn with h1 | h1
    · exact absurd (by simpa using mul_mem h1 (inv_mem hd)) hgD
    · have hyy := hgn.scalar_dvd hn h1
      rcases hy with hy | hy
      · refine ⟨-1, Or.inl rfl, fun hgN v => (hθ hgN v).trans (zsmul_congr ?_ v)⟩
        have := dvd_add hyy hy
        rwa [show y' - y + (y + 1) = y' - -1 by ring] at this
      · refine ⟨-1 + 2 ^ (m + 1), Or.inr rfl,
          fun hgN v => (hθ hgN v).trans (zsmul_congr ?_ v)⟩
        have := dvd_add hyy hy
        rwa [sub_add_sub_cancel] at this
  have hsc : ∀ f (hf : f ∈ hS.R1 dD.uv dD.t), ∃ y : ℤ,
      ∀ v, dD.thetaT (hS.R_le_normalizer hf.1) v = y • v :=
    fun f hf => h.t201_scalar_R1 hS hm hf (hB1 f hf)
  have hRR1 : hS.R1 dD.uv dD.t = hS.R := by
    refine le_antisymm (fun f hf => hf.1) fun f hfR => ?_
    by_contra hf
    have hlt : hS.R1 dD.uv dD.t < hS.R :=
      lt_of_le_of_ne (fun e he => he.1) fun heq => hf (by rw [heq]; exact hfR)
    obtain ⟨f, hfR, hfR1, huv, ht⟩ :=
      h.exists_mem_R_conj_mem_R1 hS (t201_R_le_normalizer_R1 hS hsc) hlt
    have hfN := hS.R_le_normalizer hfR
    have key : ∀ {x : G} (hxN : x ∈ Subgroup.normalizer (D : Set G))
        {φ : Torus (StrothTypeIndex.t201 m).k →+ Torus (StrothTypeIndex.t201 m).k},
        (∀ v, dD.thetaT hxN v = φ v) → (∀ w, φ w = w → (2 ^ (m + 1) : ℤ) • w = 0) →
        (∀ y : ℤ, (y = -1 ∨ y = -1 + 2 ^ (m + 1)) →
          ∃ v, y • φ v = v ∧ (2 ^ (m + 1) : ℤ) • v ≠ 0) →
        f⁻¹ * x * f * x⁻¹ ∈ hS.R1 dD.uv dD.t → f⁻¹ * x * f * x⁻¹ ∉ D → False := by
      intro x hxN φ hφ hexp htw hg hgD
      obtain ⟨y₀, hy₀, hθ⟩ := hB3 _ hg hgD
      obtain ⟨v, hv, hv0⟩ := htw y₀ hy₀
      exact dD.false_of_twist_fix hfN hxN hφ (hS.R_le_normalizer hg.1) (by group) (hθ _) hexp
        hv hv0
    by_cases huvD : f⁻¹ * dD.uv * f * dD.uv⁻¹ ∈ D
    · by_cases htD : f⁻¹ * dD.t * f * dD.t⁻¹ ∈ D
      · exact hfR1 ⟨hfR, huvD, htD⟩
      · exact key dD.t_mem dD.thetaT_t (t201_fix_t_exp hm) (fun _ hy => t201_twist_fix_t hm hy)
          ht htD
    · exact key dD.uv_mem dD.thetaT_uv (t201_fix_uv_exp hm) (fun _ hy => t201_twist_fix_uv hm hy)
        huv huvD
  rw [← hRR1]
  exact le_antisymm hB2 (sup_le (t201_D_le_R1 hS) ((Subgroup.zpowers_le).mpr hn.mem))

theorem t201_classify (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) :
    hS.R = D ∨ (∃ e ∈ hS.R, Rel34i dD e (2 ^ (m + 1))) ∨
      (∃ e ∈ hS.R, hS.R = D ⊔ Subgroup.zpowers e ∧
        (Rel34inv dD e 0 1 2 ∨ Rel34inv dD e (2 ^ (m + 1)) 1 2)) := by
  by_cases hR1 : ∃ f ∈ hS.R1 dD.uv dD.t, f ∉ D
  · obtain ⟨f, hf, hfD⟩ := hR1
    obtain ⟨e, y, hn, heD⟩ := h.t201_exists_normal_two hS hm hfus hf hfD
    have heR := hn.mem.1
    have hodd := hn.odd
    have hsq := hn.mul hn
    have hyy : (2 : ℤ) ^ (m + 2) ∣ y ^ 2 - 1 := by
      have := hsq.scalar_dvd_of_mem (hsq.mem_of_dvd h (by
        obtain ⟨c, hc⟩ : ∃ c, y = 2 * c + 1 := ⟨y / 2, by omega⟩
        exact ⟨c + 1, by rw [hc]; ring⟩))
      rwa [sq]
    rcases Stroth34Arith.sq_cases' hyy with hy | hy | hy | hy
    · exact absurd (hn.mem_of_scalar hy) heD
    · refine Or.inr (Or.inr ⟨e, heR, h.t201_case_inv hS hm hfus hn (Or.inl hy), Or.inl ?_⟩)
      exact hn.rel34inv 0 (by simp) (by simpa using hy)
        (by rw [hn.sq_eq h (μ := 0) (by simpa using dvd_mul_of_dvd_left hy 2), zero_zsmul,
          dD.ofT_zero])
    · exact Or.inr (Or.inl ⟨e, heR, hn.rel34i h hy⟩)
    · refine Or.inr (Or.inr ⟨e, heR, h.t201_case_inv hS hm hfus hn (Or.inr hy), Or.inr ?_⟩)
      refine hn.rel34inv _ (by push_cast; exact pow_dvd_pow 2 (by omega))
        (by push_cast; exact hy) ?_
      rw [hn.sq_eq h (μ := 0) (by
          obtain ⟨k, hk⟩ := hy
          exact ⟨1 + 2 * k, by linear_combination 2 * hk⟩), zero_zsmul, dD.ofT_zero]
  ·
    push Not at hR1
    left
    refine le_antisymm (fun f hfR => ?_) hS.D_le_R
    by_contra hfD
    have hlt : hS.R1 dD.uv dD.t < hS.R :=
      lt_of_le_of_ne (fun e he => he.1) fun heq => hfD (hR1 f (by rw [heq]; exact hfR))
    have hnorm : hS.R ≤ Subgroup.normalizer ((hS.R1 dD.uv dD.t : Subgroup G) : Set G) := by
      intro g hg
      have hgN := hS.R_le_normalizer hg
      rw [Subgroup.mem_normalizer_iff'']
      intro e
      constructor
      · intro he
        exact t201_D_le_R1 hS ((Subgroup.mem_normalizer_iff''.mp hgN e).mp (hR1 e he))
      · intro he
        exact t201_D_le_R1 hS ((Subgroup.mem_normalizer_iff''.mp hgN e).mpr (hR1 _ he))
    obtain ⟨f', hf'R, hf'R1, huv, ht⟩ := h.exists_mem_R_conj_mem_R1 hS hnorm hlt
    exact hf'R1 ⟨hf'R, hR1 _ huv, hR1 _ ht⟩

end StrothFrame.IsD

theorem stroth_3_4_t201 {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G}
    {m : ℕ} (dD : StrothWeakTypeData D (StrothTypeIndex.t201 m)) (h : F.IsD D dD) (hm : 1 ≤ m)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      (∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        Rel34i dD e (2 ^ (m + 1))) ∨
      (∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e ∧
        (Rel34inv dD e 0 1 2 ∨ Rel34inv dD e (2 ^ (m + 1)) 1 2)) :=
  h.t201_classify (h.setting hns) hm hfus

end CFSG.CGT.Stroth77

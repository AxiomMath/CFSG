module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7Block

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.OddStandard.Seitz77
open CFSG.LieType.Chevalley (SL2 uSL vSL HSL WSL)

section Data

variable {G : Type*} [Group G] {K : Type} [Field K]

structure FrameData (A V : Subgroup G) (K : Type) [Field K] where
  ψ : unipAll K →* G
  rad : Fin 2 → Subgroup G
  leviData : ∀ i, LeviData A (rad i) K
  ψ_injective : Function.Injective ψ
  map_top_ψ : (⊤ : Subgroup (unipAll K)).map ψ = V
  ι_zero_apply : ∀ w, (leviData 0).ι w =
    ψ (uelt (-(Multiplicative.toAdd w) 1) 0 (Multiplicative.toAdd w 0))
  ι_one_apply : ∀ w, (leviData 1).ι w =
    ψ (uelt 0 (Multiplicative.toAdd w 1) (Multiplicative.toAdd w 0))
  lev_zero_uSL : ∀ s, (leviData 0).lev (uSL s) = ψ (uelt 0 s 0)
  lev_one_uSL : ∀ s, (leviData 1).lev (uSL s) = ψ (uelt s 0 0)
  braid : (leviData 0).lev WSL * (leviData 1).lev WSL * (leviData 0).lev WSL =
    (leviData 1).lev WSL * (leviData 0).lev WSL * (leviData 1).lev WSL
  sup_lev_range : (leviData 0).lev.range ⊔ (leviData 1).lev.range = A
  isQuasisimple : CFSG.Open.IsQuasisimple A

namespace FrameData

variable {A V : Subgroup G}

theorem mem_V_iff (F : FrameData A V K) {x : G} : x ∈ V ↔ ∃ u, F.ψ u = x := by
  constructor
  · intro hx
    have h : x ∈ (⊤ : Subgroup (unipAll K)).map F.ψ := by rw [F.map_top_ψ]; exact hx
    obtain ⟨u, -, rfl⟩ := h
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    have h : F.ψ u ∈ (⊤ : Subgroup (unipAll K)).map F.ψ := ⟨u, mem_top u, rfl⟩
    rwa [F.map_top_ψ] at h

theorem ψ_mem_V (F : FrameData A V K) (u : unipAll K) : F.ψ u ∈ V :=
  F.mem_V_iff.2 ⟨u, rfl⟩

theorem map_radOne_ψ (F : FrameData A V K) : (radOne K).map F.ψ = F.rad 0 := by
  rw [← (F.leviData 0).range_ι]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨a, b, c, rfl⟩ := exists_uelt u
    rw [SetLike.mem_coe, mem_radOne, coordB_uelt] at hu
    subst hu
    refine ⟨Multiplicative.ofAdd ![c, -a], ?_⟩
    rw [F.ι_zero_apply]
    congr 1
    rw [uelt_inj]
    refine ⟨?_, ?_, ?_⟩ <;> simp
  · rintro ⟨w, rfl⟩
    refine ⟨uelt (-(Multiplicative.toAdd w) 1) 0 (Multiplicative.toAdd w 0), ?_,
      (F.ι_zero_apply w).symm⟩
    rw [SetLike.mem_coe, mem_radOne, coordB_uelt]

theorem map_radTwo_ψ (F : FrameData A V K) : (radTwo K).map F.ψ = F.rad 1 := by
  rw [← (F.leviData 1).range_ι]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨a, b, c, rfl⟩ := exists_uelt u
    rw [SetLike.mem_coe, mem_radTwo, coordA_uelt] at hu
    subst hu
    refine ⟨Multiplicative.ofAdd ![c, b], ?_⟩
    rw [F.ι_one_apply]
    simp
  · rintro ⟨w, rfl⟩
    refine ⟨uelt 0 (Multiplicative.toAdd w 1) (Multiplicative.toAdd w 0), ?_,
      (F.ι_one_apply w).symm⟩
    rw [SetLike.mem_coe, mem_radTwo, coordA_uelt]

theorem radicals [Finite K] [CharP K 2] (F : FrameData A V K) :
    Radicals V (F.rad 0) (F.rad 1) (Nat.card K) := by
  have h := (radicals_unipAll (K := K)).map F.ψ_injective
  rwa [F.map_top_ψ, F.map_radOne_ψ, F.map_radTwo_ψ] at h

theorem eq_bot_or_eq_bot (F : FrameData A V K) {P Q : Subgroup G}
    (hc : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = V) :
    P = ⊥ ∨ Q = ⊥ := by
  have hPV : P ≤ V := hsup ▸ le_sup_left
  have hQV : Q ≤ V := hsup ▸ le_sup_right
  have hP : P = (P.comap F.ψ).map F.ψ := by
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_map, F.map_top_ψ, inf_eq_right.2 hPV]
  have hQ : Q = (Q.comap F.ψ).map F.ψ := by
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_map, F.map_top_ψ, inf_eq_right.2 hQV]
  rcases unipAll_eq_bot_or_eq_bot (P := P.comap F.ψ) (Q := Q.comap F.ψ)
      (fun x hx y hy => F.ψ_injective (by rw [map_mul, map_mul]; exact hc _ hx _ hy))
      (by rw [← Subgroup.comap_inf, hinf, MonoidHom.comap_bot,
        (MonoidHom.ker_eq_bot_iff _).2 F.ψ_injective])
      (by
        rw [eq_top_iff]
        intro u _
        have hu : F.ψ u ∈ P ⊔ Q := hsup ▸ F.ψ_mem_V u
        rw [hP, hQ, ← Subgroup.map_sup] at hu
        obtain ⟨v, hv, he⟩ := hu
        rwa [← F.ψ_injective he]) with h | h
  · left
    rw [hP, h, Subgroup.map_bot]
  · right
    rw [hQ, h, Subgroup.map_bot]

theorem exists_mul_lev (F : FrameData A V K) (i : Fin 2) {v : G} (hv : v ∈ V) :
    ∃ x ∈ F.rad i, ∃ s : K, v = x * (F.leviData i).lev (uSL s) := by
  match i with
  | 0 =>
    obtain ⟨u, rfl⟩ := F.mem_V_iff.1 hv
    obtain ⟨a, b, c, rfl⟩ := exists_uelt u
    refine ⟨F.ψ (uelt a 0 (c - a * b)), ?_, b, ?_⟩
    · rw [← F.map_radOne_ψ]
      exact ⟨_, (mem_radOne _).2 (coordB_uelt _ _ _), rfl⟩
    · rw [F.lev_zero_uSL, ← map_mul, uelt_mul]
      congr 1
      rw [uelt_inj]
      refine ⟨?_, ?_, ?_⟩ <;> simp
  | 1 =>
    obtain ⟨u, rfl⟩ := F.mem_V_iff.1 hv
    obtain ⟨a, b, c, rfl⟩ := exists_uelt u
    refine ⟨F.ψ (uelt 0 b c), ?_, a, ?_⟩
    · rw [← F.map_radTwo_ψ]
      exact ⟨_, (mem_radTwo _).2 (coordA_uelt _ _ _), rfl⟩
    · rw [F.lev_one_uSL, ← map_mul, uelt_mul]
      congr 1
      rw [uelt_inj]
      refine ⟨?_, ?_, ?_⟩ <;> simp

theorem lev_uSL_mem_V (F : FrameData A V K) (i : Fin 2) (s : K) :
    (F.leviData i).lev (uSL s) ∈ V := by
  match i with
  | 0 => rw [F.lev_zero_uSL]; exact F.ψ_mem_V _
  | 1 => rw [F.lev_one_uSL]; exact F.ψ_mem_V _

theorem lev_zero_HSL_conj (F : FrameData A V K) (l : Kˣ) (a b c : K) :
    (F.leviData 0).lev (HSL l) * F.ψ (uelt a b c) * ((F.leviData 0).lev (HSL l))⁻¹ =
      F.ψ (uelt (((l⁻¹ : Kˣ) : K) * a) ((l : K) ^ 2 * b) ((l : K) * c)) := by
  have hSL : HSL l * uSL b * (HSL l)⁻¹ = uSL ((l : K) ^ 2 * b) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.LieType.Chevalley.coe_HSL, CFSG.LieType.Chevalley.coe_uSL,
        Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring
  have hdecomp : F.ψ (uelt a b c) =
      (F.leviData 0).ι (Multiplicative.ofAdd ![c - a * b, -a]) *
        (F.leviData 0).lev (uSL b) := by
    rw [F.ι_zero_apply, F.lev_zero_uSL, ← map_mul, uelt_mul]
    congr 1
    rw [uelt_inj]
    refine ⟨?_, ?_, ?_⟩ <;> simp
  have hconjlev : (F.leviData 0).lev (HSL l) * (F.leviData 0).lev (uSL b) *
      ((F.leviData 0).lev (HSL l))⁻¹ = (F.leviData 0).lev (uSL ((l : K) ^ 2 * b)) := by
    rw [← map_inv, ← map_mul, ← map_mul, hSL]
  have hmat : ((HSL l : SL2 K) : Matrix (Fin 2) (Fin 2) K) *ᵥ ![c - a * b, -a] =
      ![((l : K) * (c - a * b)), -(((l⁻¹ : Kˣ) : K) * a)] := by
    ext i
    fin_cases i <;>
      simp [CFSG.LieType.Chevalley.coe_HSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hdecomp]
  calc
    (F.leviData 0).lev (HSL l) *
        ((F.leviData 0).ι (Multiplicative.ofAdd ![c - a * b, -a]) *
          (F.leviData 0).lev (uSL b)) *
        ((F.leviData 0).lev (HSL l))⁻¹
        = ((F.leviData 0).lev (HSL l) *
            (F.leviData 0).ι (Multiplicative.ofAdd ![c - a * b, -a]) *
            ((F.leviData 0).lev (HSL l))⁻¹) *
          ((F.leviData 0).lev (HSL l) * (F.leviData 0).lev (uSL b) *
            ((F.leviData 0).lev (HSL l))⁻¹) := by group
    _ = (F.leviData 0).ι (Multiplicative.ofAdd
          (((HSL l : SL2 K) : Matrix (Fin 2) (Fin 2) K) *ᵥ ![c - a * b, -a])) *
          (F.leviData 0).lev (uSL ((l : K) ^ 2 * b)) := by
      rw [(F.leviData 0).lev_conj, hconjlev]
      simp
    _ = (F.leviData 0).ι (Multiplicative.ofAdd
          ![((l : K) * (c - a * b)), -(((l⁻¹ : Kˣ) : K) * a)]) *
          (F.leviData 0).lev (uSL ((l : K) ^ 2 * b)) := by
      rw [hmat]
    _ = F.ψ (uelt (((l⁻¹ : Kˣ) : K) * a) ((l : K) ^ 2 * b) ((l : K) * c)) := by
      rw [F.ι_zero_apply, F.lev_zero_uSL, ← map_mul, uelt_mul]
      congr 1
      rw [uelt_inj]
      refine ⟨by simp, by simp, ?_⟩
      simp
      field_simp
      ring

theorem lev_zero_HSL_conj_mem_V₁ (F : FrameData A V K) (l : Kˣ) {v : G} (hv : v ∈ F.rad 1) :
    (F.leviData 0).lev (HSL l) * v * ((F.leviData 0).lev (HSL l))⁻¹ ∈ F.rad 1 := by
  rw [← F.map_radTwo_ψ] at hv ⊢
  obtain ⟨u, hu, rfl⟩ := hv
  obtain ⟨a, b, c, rfl⟩ := exists_uelt u
  rw [SetLike.mem_coe, mem_radTwo, coordA_uelt] at hu
  subst hu
  rw [F.lev_zero_HSL_conj]
  exact ⟨_, (mem_radTwo _).2 (by rw [coordA_uelt, mul_zero]), rfl⟩

theorem eq_one_of_lev_zero_HSL_conj [CharP K 2] (F : FrameData A V K) {l : Kˣ}
    (hl : (l : K) ≠ 1) {v : G} (hv : v ∈ V)
    (hfix : (F.leviData 0).lev (HSL l) * v * ((F.leviData 0).lev (HSL l))⁻¹ = v) : v = 1 := by
  obtain ⟨u, rfl⟩ := F.mem_V_iff.1 hv
  obtain ⟨a, b, c, rfl⟩ := exists_uelt u
  rw [F.lev_zero_HSL_conj] at hfix
  obtain ⟨ha, hb, hc⟩ := uelt_inj.1 (F.ψ_injective hfix)
  have hl' : ((l⁻¹ : Kˣ) : K) ≠ 1 := fun h => hl (by
    rw [Units.val_inv_eq_inv_val, inv_eq_one] at h; exact h)
  have hl2 : (l : K) ^ 2 ≠ 1 := fun h => hl (by
    have h' : ((l : K) - 1) ^ 2 = 0 := by
      rw [sub_sq, h, mul_one, CharTwo.two_eq_zero, zero_mul, sub_zero, one_pow]
      exact CharTwo.add_self_eq_zero 1
    exact sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h'))
  have ha0 : a = 0 := by
    have : (((l⁻¹ : Kˣ) : K) - 1) * a = 0 := by rw [sub_mul, one_mul, ha, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hl')
  have hb0 : b = 0 := by
    have : ((l : K) ^ 2 - 1) * b = 0 := by rw [sub_mul, one_mul, hb, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hl2)
  have hc0 : c = 0 := by
    have : ((l : K) - 1) * c = 0 := by rw [sub_mul, one_mul, hc, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hl)
  rw [ha0, hb0, hc0, uelt_zero, map_one]

private theorem lev_WSL_conj {W : Subgroup G} (D : LeviData A W K) (x y : K) :
    D.lev WSL * D.ι (Multiplicative.ofAdd ![x, y]) * (D.lev WSL)⁻¹ =
      D.ι (Multiplicative.ofAdd ![y, -x]) := by
  have h : ((WSL : SL2 K) : Matrix (Fin 2) (Fin 2) K) *ᵥ ![x, y] = ![y, -x] := by
    ext i
    fin_cases i <;> simp [CFSG.LieType.Chevalley.coe_WSL, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  simpa [h] using D.lev_conj WSL (Multiplicative.ofAdd ![x, y])

theorem s_zero_conj_one (F : FrameData A V K) (s : K) :
    (F.leviData 0).lev WSL * F.ψ (uelt s 0 0) * ((F.leviData 0).lev WSL)⁻¹ =
      F.ψ (uelt 0 0 (-s)) := by
  have h : F.ψ (uelt s 0 0) =
      (F.leviData 0).ι (Multiplicative.ofAdd ![0, -s]) := by
    rw [F.ι_zero_apply]
    congr 1
    rw [uelt_inj]
    refine ⟨?_, ?_, ?_⟩ <;> simp
  rw [h, lev_WSL_conj (F.leviData 0)]
  rw [F.ι_zero_apply]
  simp

theorem s_zero_conj_three (F : FrameData A V K) (c : K) :
    (F.leviData 0).lev WSL * F.ψ (uelt 0 0 c) * ((F.leviData 0).lev WSL)⁻¹ =
      F.ψ (uelt c 0 0) := by
  have h : F.ψ (uelt 0 0 c) =
      (F.leviData 0).ι (Multiplicative.ofAdd ![c, 0]) := by
    rw [F.ι_zero_apply]
    congr 1
    rw [uelt_inj]
    refine ⟨?_, ?_, ?_⟩ <;> simp
  rw [h, lev_WSL_conj (F.leviData 0)]
  rw [F.ι_zero_apply]
  simp

theorem s_one_conj_three (F : FrameData A V K) (c : K) :
    (F.leviData 1).lev WSL * F.ψ (uelt 0 0 c) * ((F.leviData 1).lev WSL)⁻¹ =
      F.ψ (uelt 0 (-c) 0) := by
  have h : F.ψ (uelt 0 0 c) =
      (F.leviData 1).ι (Multiplicative.ofAdd ![c, 0]) := by
    rw [F.ι_one_apply]
    congr 1
  rw [h, lev_WSL_conj (F.leviData 1)]
  rw [F.ι_one_apply]
  simp

theorem s_one_conj_two (F : FrameData A V K) (b : K) :
    (F.leviData 1).lev WSL * F.ψ (uelt 0 b 0) * ((F.leviData 1).lev WSL)⁻¹ =
      F.ψ (uelt 0 0 b) := by
  have h : F.ψ (uelt 0 b 0) =
      (F.leviData 1).ι (Multiplicative.ofAdd ![0, b]) := by
    rw [F.ι_one_apply]
    congr 1
  rw [h, lev_WSL_conj (F.leviData 1)]
  rw [F.ι_one_apply]
  simp

end FrameData

theorem isQuasisimple_of_range_eq_of_ker_le_center {A : Subgroup G}
    (ρ : SpecialLinearGroup (Fin 3) K →* G) (hρ : ρ.range = A)
    (hker : ρ.ker ≤ center (SpecialLinearGroup (Fin 3) K)) : CFSG.Open.IsQuasisimple A := by
  subst hρ
  have hcent : center (SpecialLinearGroup (Fin 3) K) ≠ ⊤ := by
    intro htop
    refine CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.cyc_not_central (K := K) ?_
    rw [htop]
    exact mem_top _
  have hne : ρ.ker ≠ ⊤ := by
    intro htop
    exact hcent (top_unique (htop ▸ hker))
  exact CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.isQuasisimple_SL3 ρ hne

end Data

section OfFrame

variable {G : Type} [Group G] {A V : Subgroup G} {K : Type} [Field K]

theorem Frame.isQuasisimple (F : Frame A V K) : CFSG.Open.IsQuasisimple A := by
  have hρ : (F.φ.comp (proj 3 K)).range = A := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (proj_surjective 3 K),
      Subgroup.map_top, F.range_eq]
  have hker : (F.φ.comp (proj 3 K)).ker ≤ center (SpecialLinearGroup (Fin 3) K) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [← scalars_eq_center 3 K, ← ker_proj 3 K]
    have hx1 : proj 3 K x = 1 :=
      F.injective (by simpa only [MonoidHom.comp_apply, map_one] using hx)
    exact MonoidHom.mem_ker.2 hx1
  exact isQuasisimple_of_range_eq_of_ker_le_center (F.φ.comp (proj 3 K)) hρ hker

variable [Finite K] [CharP K 2]

@[expose] noncomputable def Frame.toFrameData (F : Frame A V K) : FrameData A V K where
  ψ := F.ψ
  rad i := (projRad K i).map F.φ
  leviData := F.leviData
  ψ_injective := F.ψ_injective
  map_top_ψ := F.map_top_ψ
  ι_zero_apply := F.ι_zero_apply
  ι_one_apply := F.ι_one_apply
  lev_zero_uSL := F.lev_zero_uSL
  lev_one_uSL := F.lev_one_uSL
  braid := F.braid
  sup_lev_range := F.sup_lev_range
  isQuasisimple := F.isQuasisimple

end OfFrame

end CFSG.LocalAnalysis.EvenBN.LinearThree

end

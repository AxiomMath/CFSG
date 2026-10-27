module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Gen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Model
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Comm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Corr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113X0

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint Equiv

theorem Sec113Shape.ne_one {σ : Perm (Fin 6)} (h : Sec113Shape σ) : σ ≠ 1 := by
  obtain ⟨-, a, b, c, -, -, -, hab, -, -, hσa, -⟩ := h
  intro h1
  rw [h1, Equiv.Perm.one_apply] at hσa
  exact hab hσa

theorem asc82Lemma113_of (hp : Asc82Pre11) : Asc82Lemma113 := by
  intro G _ _ t L S z K1 K2 T R hctx
  obtain ⟨Alt, φ, hm⟩ := sec11_model_of hp hctx
  have hTM := sec113_T_le_M hctx
  have htA : t ∈ secA t S L := by
    have h := hm.perm.mem (Pi.single 0 1)
    rwa [← hm.t_eq] at h
  rcases Sec11Model.cent_T_Q hp hctx hm with ⟨hAlt, hC⟩ | ⟨hAlt, r, hr2, hC, -, hract⟩
  ·
    obtain ⟨x0, hx0T, hx02, hx0ty⟩ := sec113_exists_x0_A hp hctx hm hAlt
    obtain ⟨x, hxT, hx2, hρx, h1, h2⟩ := sec113_correct hp hctx hm hx0T hx02 hx0ty.shape
    have hxty : Sec113TypeA (hm.perm.rho x) := by
      rw [hρx]
      exact hx0ty
    have hxne : x ≠ 1 := by
      rintro rfl
      exact hxty.shape.ne_one hm.perm.rho_one
    obtain ⟨hout1, hout2⟩ := sec113_outer hp hctx hm hxT hx2 hxty.shape h1 h2
    have htC : t ∈ secCTQ K1 K2 T := by
      rw [hC]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
    exact ⟨φ (Pi.single 2 1), x,
      { toSec11Ctx := hctx
        a_mem := hm.perm.mem _
        a_not_Q := sec113_a_not_Q hm 2
        swap := sec113_swap hp hctx hm (k := 2) (by decide)
        x_mem := hxT
        x_inv := orderOf_eq_prime (by rw [pow_two]; exact hx2) hxne
        x_out1 := hout1
        x_out2 := hout2
        a_comm := sec113_a_comm hm (k := 2) (by decide) (Or.inl hC)
        x_comm := fun hne => absurd hC hne
        gen := sec113_gen hp hctx hm hxT htC (Or.inl ⟨hAlt, hxty⟩) }⟩
  ·
    have hr2' : r * r = 1 := by
      have h := pow_orderOf_eq_one r
      rwa [hr2, pow_two] at h
    have hrC : r ∈ secCTQ K1 K2 T := by
      rw [hC]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers r)
    have htC : t ∈ secCTQ K1 K2 T := by
      rw [hC]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
    have hrT : r ∈ T := (inf_le_right : secCTQ K1 K2 T ≤ T) hrC
    have hrQ : ∀ q ∈ secQ K1 K2, q * r = r * q := fun q hq =>
      Subgroup.mem_centralizer_iff.mp hrC.1 q hq
    have hρr : hm.perm.rho r = swap 0 1 := hm.perm.rho_eq (hTM hrT) _ hract
    obtain ⟨x0, hx0T, hx02, hx0ty⟩ := sec113_exists_x0_S hp hctx hm hAlt hr2' hrT hract
    obtain ⟨x1, hx1T, hx12, hρx1, h1, h2⟩ := sec113_correct hp hctx hm hx0T hx02 hx0ty.shape
    have hx1ty : Sec113TypeS (hm.perm.rho x1) := by
      rw [hρx1]
      exact hx0ty
    obtain ⟨x, hxT, hx2, hρx, h1', h2', hxt, hxr⟩ :=
      sec113_comm hp hctx hm hr2' hrT hrQ hract hx1T hx12 hx1ty h1 h2
    have hxty : Sec113TypeS (hm.perm.rho x) := by
      rw [hρx]
      exact hx1ty
    have hxne : x ≠ 1 := by
      rintro rfl
      exact hxty.shape.ne_one hm.perm.rho_one
    obtain ⟨hout1, hout2⟩ := sec113_outer hp hctx hm hxT hx2 hxty.shape h1' h2'
    have hle : zpowers t ⊔ zpowers r ≤ centralizer ({x} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_) <;>
        rw [Subgroup.mem_centralizer_singleton_iff]
      · exact hxt.symm
      · exact hxr.symm
    exact ⟨φ (Pi.single 2 1), x,
      { toSec11Ctx := hctx
        a_mem := hm.perm.mem _
        a_not_Q := sec113_a_not_Q hm 2
        swap := sec113_swap hp hctx hm (k := 2) (by decide)
        x_mem := hxT
        x_inv := orderOf_eq_prime (by rw [pow_two]; exact hx2) hxne
        x_out1 := hout1
        x_out2 := hout2
        a_comm := sec113_a_comm hm (k := 2) (by decide) (Or.inr ⟨r, hract, hC⟩)
        x_comm := fun _ c hc => by
          rw [hC] at hc
          exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hc)).symm
        gen := sec113_gen hp hctx hm hxT htC (Or.inr ⟨hAlt, hxty, r, hrC, hρr⟩) }⟩

end CFSG.OddStandard.SmallF3.Omega

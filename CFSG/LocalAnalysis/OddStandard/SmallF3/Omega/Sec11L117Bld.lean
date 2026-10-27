module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Cnt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117CC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Elt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Ent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Ax

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_cnt_of_ax [Finite G] (hp : Asc82Pre11) (r : Asc82Res11a) {t : G} {L S : Subgroup G}
    {z : G} {K1 K2 T R : Subgroup G} {a x : G} (hax : Sec11Ax G t L S z K1 K2 T R a x) :
    Sec11Cnt G z T (secCTQ K1 K2 T) (twoCoreIn K1) (twoCoreIn K2) a x := by
  have hctx : Sec11Ctx G t L S z K1 K2 T R := hax.toSec11Ctx
  have hctx10 : Sec10Ctx G t L S z K1 K2 := hctx.toSec10Ctx
  have hQ : secQ K1 K2 = twoCoreIn K1 ⊔ twoCoreIn K2 := sec11_Q_eq_sup hp hctx10
  have h1 : Sec11Q8 G z (twoCoreIn K1) := sec11_Q8_K1 hp hctx10
  have h2 : Sec11Q8 G z (twoCoreIn K2) := sec11_Q8_K2 hp hctx10
  obtain ⟨-, hzsq, -, -, hzne⟩ := sec11_invols hctx10
  have haT : a ∈ T ∧ a * a = 1 := sec11_a_T hp hax
  have hsw := sec11_a_swap hp hax
  have hx2 : x * x = 1 := sec11_x_sq hax
  have hn1 := sec11_x_normQ1 hp hctx hax.x_mem hax.x_out1
  have hn2 := sec11_x_normQ2 hp hctx hax.x_mem hax.x_out2
  have hnt1 := sec11_x_nt1 hp r hctx hax.x_mem hax.x_out1
  have hnt2 := sec11_x_nt2 hp r hctx hax.x_mem hax.x_out2
  have hTn : ∀ g ∈ T, ∀ q ∈ twoCoreIn K1 ⊔ twoCoreIn K2,
      g * q * g⁻¹ ∈ twoCoreIn K1 ⊔ twoCoreIn K2 := by
    rw [← hQ]
    exact sec11_T_normQ hctx
  have hCQ : ∀ c ∈ secCTQ K1 K2 T, ∀ q ∈ twoCoreIn K1 ⊔ twoCoreIn K2, c * q = q * c := by
    rw [← hQ]
    exact sec11_C_Q
  have hCinf : secCTQ K1 K2 T ⊓ (twoCoreIn K1 ⊔ twoCoreIn K2) = zpowers z := by
    rw [← hQ]
    exact sec11_C_inf hp hctx
  have hWn : ∀ g ∈ T, ∀ w ∈ secCTQ K1 K2 T ⊔ (twoCoreIn K1 ⊔ twoCoreIn K2),
      g * w * g⁻¹ ∈ secCTQ K1 K2 T ⊔ (twoCoreIn K1 ⊔ twoCoreIn K2) := by
    rw [← hQ]
    exact sec11_W_norm hctx
  have hC : ∀ g ∈ T, (∀ q ∈ twoCoreIn K1 ⊔ twoCoreIn K2, g * q = q * g) →
      g ∈ secCTQ K1 K2 T := by
    intro g hg hgq
    rw [← hQ] at hgq
    exact sec11_mem_C_of hg hgq
  have haxW : a * x * a⁻¹ * x⁻¹ ∈ secCTQ K1 K2 T ⊔ (twoCoreIn K1 ⊔ twoCoreIn K2) :=
    sec11_ax_W_abs h1 h2 (sec11_T_isPGroup hctx) (hctx.S_le hctx.mem_S)
      (sec11_T_cent_z hp hctx) (sec11_Q1_le_T hp hctx) (sec11_Q2_le_T hp hctx)
      (sec11_Q12_comm hp hctx10) haT.1 hax.x_mem haT.2 hx2 hsw.1 hsw.2 hn1 hn2 hnt1 hnt2 hC
  have hgen : T = Subgroup.closure ((secCTQ K1 K2 T : Set G) ∪
      ((twoCoreIn K1 ⊔ twoCoreIn K2 : Subgroup G) : Set G) ∪ ({a, x} : Set G)) := by
    have h := hax.gen
    rw [hQ] at h
    exact h
  exact
    { z_sq := hzsq
      z_ne := hzne
      z_cent := sec11_T_cent_z hp hctx
      Q1_le := sec11_Q1_le_T hp hctx
      Q2_le := sec11_Q2_le_T hp hctx
      Q_comm := sec11_Q12_comm hp hctx10
      Q_inf := sec11_Q12_inf hp hctx10
      Q1_card := h1.card
      Q2_card := h2.card
      Q1_el := fun p hp' q hq => (h1.el p hp' q hq).1
      Q2_el := fun p hp' q hq => (h2.el p hp' q hq).1
      T_normQ := hTn
      C_comm := fun c hc c' hc' => (sec11_C_elemAb hp r hctx c hc c' hc').1
      C_Q := hCQ
      C_inf := hCinf
      W_norm := hWn
      a_mem := haT.1
      a_sq := haT.2
      a_C := hax.a_comm
      a_swap := hsw.2
      x_mem := hax.x_mem
      x_sq := hx2
      x_C := sec11_x_C hp r hax
      x_norm1 := hn1
      x_norm2 := hn2
      x_nt1 := hnt1
      x_nt2 := hnt2
      ax_W := haxW
      gen := hgen }

end CFSG.OddStandard.SmallF3.Omega

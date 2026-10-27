module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S117R
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117cDS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117cMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117cR
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117cT

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11c_cnt_of_ax [Finite G] (hp : Asc82Pre11) (r : Asc82Res11a) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G} {a x : G}
    (hax : Sec11Ax G t L S z K1 K2 T R a x) :
    Sec11cCnt G z R T (secCTQ K1 K2 T) (secD K1 K2 R) (twoCoreIn K1) (twoCoreIn K2) a x := by
  have hctx : Sec11Ctx G t L S z K1 K2 T R := hax.toSec11Ctx
  have hQ : secQ K1 K2 = twoCoreIn K1 ⊔ twoCoreIn K2 := sec11_Q_eq_sup hp hctx.toSec10Ctx
  have hel : IsElemAbelianMod z (secQ K1 K2) :=
    sec11_isElemAbelianMod_mono le_sup_right (sec11_W_elemAb hp r hctx)
  have hnQ := sec11c_R_normQ hctx
  have hDQ : ∀ d ∈ secD K1 K2 R, ∀ q ∈ secQ K1 K2, d * q = q * d := sec11c_D_Q
  have hinf := sec11c_D_inf hp hctx
  have hbar := sec11c_bar hp hctx
  rw [hQ] at hel hnQ hDQ hinf hbar
  exact
    { cnt := sec11_cnt_of_ax hp r hax
      T_le := hctx.T_le
      C_le := sec11c_C_le_D hctx
      D_le := inf_le_right
      R_two := sec11c_R_isPGroup hctx
      R_z := sec11c_R_z hp hctx
      R_normD := sec11c_R_normD hctx
      R_normQ := hnQ
      D_Q := hDQ
      D_inf := hinf
      Q_el := hel
      R_bar := hbar }

theorem asc82Step117R_of (hp : Asc82Pre11) (r : Asc82Res11a) : Asc82Step117R := by
  intro G _ _ t L S z K1 K2 T R hctx
  rcases r.l112 G t L S z K1 K2 T R hctx with ⟨hA6, -⟩ | ⟨-, _, -, -, hD8, -⟩
  · rw [r.l115b G t L S z K1 K2 T R hctx hA6]
    exact sec11c_JMod_T hp r hctx
  · obtain ⟨a, x, hax⟩ := r.l113 G t L S z K1 K2 T R hctx
    have hc := sec11c_cnt_of_ax hp r hax
    have hQ : secQ K1 K2 = twoCoreIn K1 ⊔ twoCoreIn K2 := sec11_Q_eq_sup hp hctx.toSec10Ctx
    obtain ⟨Y, hYD, hY, hYi, hY4⟩ := sec11c_isDihSd_cyclic4 (r.l114 G t L S z K1 K2 T R hctx)
    have hnab : ∃ u ∈ secD K1 K2 R, ∃ v ∈ secD K1 K2 R, u * v ≠ v * u := by
      obtain ⟨u, hu, v, hv, huv⟩ := sec11_isD8_nonabelian hD8
      exact ⟨u, sec11c_C_le_D hctx hu, v, sec11c_C_le_D hctx hv, huv⟩
    obtain ⟨ht2, -, -, -, -⟩ := sec11_invols hctx.toSec10Ctx
    have hR : R = T ⊔ secD K1 K2 R ∨
        ∃ t' : G, t' * t' = 1 ∧ secD K1 K2 R = zpowers t ⊔ zpowers t' := by
      rcases r.l115d G t L S z K1 K2 T R hctx with h | ⟨x1, -, -, -, -, -, hD⟩
      · exact Or.inl h
      · refine Or.inr ⟨x1⁻¹ * t * x1, ?_, hD⟩
        calc x1⁻¹ * t * x1 * (x1⁻¹ * t * x1) = x1⁻¹ * (t * t) * x1 := by group
          _ = 1 := by rw [ht2]; group
    rw [hQ]
    exact hc.JMod_eq hY hYD hYi hY4 hnab ht2 (sec11c_t_ne_z hp hctx) (sec11c_cl hp hctx) hR

end CFSG.OddStandard.SmallF3.Omega

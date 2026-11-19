module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SingleXSetup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SingleXPsi
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SingleXCaseA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SingleXCaseB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110Single

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem s11s_core {t z : G} {K1 K2 T R : Subgroup G} {ρ : ↥R →* MulAut ↥(K1 ⊔ K2)} {a x : G}
    (c : S11sCtx t z K1 K2 T R ρ a x) {h : G} (hh : h ∈ centralizer ({z} : Set G))
    (hR : h⁻¹ * t * h ∈ R)
    (hQ1 : ∀ q ∈ twoCoreIn K1, h⁻¹ * t * h * q * (h⁻¹ * t * h)⁻¹ ∈ twoCoreIn K1)
    (hQ2 : ∀ q ∈ twoCoreIn K2, h⁻¹ * t * h * q * (h⁻¹ * t * h)⁻¹ ∈ twoCoreIn K2)
    (h2 : ActsTrivModZ z (h⁻¹ * t * h) (twoCoreIn K2))
    (h1 : ¬ ActsTrivModZ z (h⁻¹ * t * h) (twoCoreIn K1)) : False := by
  obtain ⟨b, hb, hsb⟩ : ∃ b ∈ twoCoreIn K1,
      h⁻¹ * t * h * b * (h⁻¹ * t * h)⁻¹ * b⁻¹ ∉ zpowers z := by
    by_contra hcon
    push Not at hcon
    exact h1 hcon
  have hs2 : h⁻¹ * t * h * (h⁻¹ * t * h) = 1 := by
    calc h⁻¹ * t * h * (h⁻¹ * t * h) = h⁻¹ * (t * t) * h := by group
      _ = 1 := by rw [c.t_sq]; group
  obtain ⟨hA, hsign, q, hq4, hψ⟩ := c.psi_class hR hs2 hQ1 hQ2 h2 hb hsb
  by_cases hq : q = 1 ∨ q = -1
  · have hB : ∀ y ∈ K2.subgroupOf (K1 ⊔ K2), ρ ⟨h⁻¹ * t * h, hR⟩ y = y := by
      intro y hy
      rw [hψ y hy]
      rcases hq with rfl | rfl
      · simp
      · have hzA : c.pair.embB (-1) ∈ K1.subgroupOf (K1 ⊔ K2) := by
          rw [Subgroup.mem_subgroupOf, c.embB_neg_one]
          exact c.z_K1
        have hzc := c.pair.inf_central ⟨hzA, c.pair.embB_mem (-1)⟩ y
        rw [hzc, mul_inv_cancel_right]
    exact c.caseA hh rfl hR hb hsb hA hB hsign
  · push Not at hq
    exact c.caseB hh rfl hR hQ1 hb hsb hq4 hq.1 hq.2 hψ

theorem asc82Step1110Single_of (hp : Asc82Pre11) (hT : Asc82Step1110Type) :
    Asc82Step1110Single := by
  intro G _ _ t L S z K1 K2 T R hctx h hh hR _ hQ1 hQ2
  obtain ⟨ρ, a, x, c⟩ := s11s_ctx_of hp hT hctx
  obtain ⟨ρ', a', x', c'⟩ := s11s_ctx_of hp hT (s11s_ctx_swap hctx)
  constructor
  · intro h1
    by_contra h2
    exact s11s_core c' hh hR hQ2 hQ1 h1 h2
  · intro h2
    by_contra h1
    exact s11s_core c hh hR hQ1 hQ2 h2 h1

end CFSG.OddStandard.SmallF3.Omega

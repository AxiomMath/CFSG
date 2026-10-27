module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Cl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Fb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Cv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Prof

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10 Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau : G} {T₂ : Subgroup G}

theorem fzr_rules [IsSimpleGroup G]
    (D : FzRNum t x₁ x₂ lam rho tau T₂)
    (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    (hT2 : IsFzT2 t x₁ x₂ S T₂) (hT : FzSylow T₂) :
    FzRules (fzrPar D) (fzrTh D) := by
  have hord : orderOf t = 2 := h.hyp.ord_t
  have ht2 : t * t = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord])
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  exact
    { mul := fzrPar_mul D
      tI_lt := (fzrPar_lt D).1
      sI_lt := (fzrPar_lt D).2.1
      gens_lt := (fzrPar_lt D).2.2.1
      rho_lt := (fzrPar_lt D).2.2.2
      th_t := fzr_th_t D
      th_inv := fun x hx => fzr_th_inv D ht2 ht1 hx
      conj := fun g x y hg hx hy hxy => fzr_th_conj D hg hx hy hxy
      rho := fun x hx => fzr_th_rho D hx
      forb := fun x hx hTL hx0 hxx => fzr_th_forb D h hx hTL hx0 hxx
      wrule := fun x hW hθ => fzr_th_wrule D h hK hW hθ
      ktl := fun x hx hTL hx0 hxx => fzr_th_ktl D h hK hx hTL hx0 hxx
      kout := fun sp hsp l hl hTL hinv => fzr_th_kout D h hsp hl hTL hinv
      cover := fun f hadd hf => fzr_th_cover D h hT f hadd hf
      prof := fun u hu hcard => fzr_th_prof D h hK hT2 hu hcard }

end CFSG.OddStandard.SmallF3.FritzII

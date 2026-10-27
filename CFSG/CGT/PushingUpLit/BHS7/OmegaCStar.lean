module

public import CFSG.CGT.PushingUpLit.BHS7.OmegaSL

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

theorem omegaCStar_of (h : MinCex G T) (hprod : OmegaCStarProd G T)
    (halt : OmegaCStarAlt G T) : OmegaCStar G T := by
  refine ⟨hprod, fun E hE => ?_⟩
  rcases (omega_isBTBlock h hE).type with ⟨n, hn2, hn⟩ | ⟨m, hm, hn⟩
  · exact Or.inl ⟨⟨n, hn2, hn⟩, omega_cstar_sl h hE hn2 hn⟩
  · exact Or.inr ⟨m, hm, hn, halt E hE m hm hn⟩

end CFSG.CGT.PushingUpLit.BHS7

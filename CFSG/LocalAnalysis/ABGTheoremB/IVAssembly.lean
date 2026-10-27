module

public import CFSG.LocalAnalysis.ABGTheoremB.IV2
public import CFSG.LocalAnalysis.ABGTheoremB.IV3
public import CFSG.LocalAnalysis.ABGTheoremB.IV6

public section

namespace CFSG.ABGTheoremB

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

theorem lemmaIV32_of (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) : σ.LemmaIV32 :=
  σ.lemmaIV32 hσ hII (fun _ hr hdiv _ hR => σ.constrained_iff_centralizer_le hσ hII hr hdiv hR)
    (fun _ hr hdiv => σ.ordinary_iff hσ hII hr hdiv)

theorem propIV61_of (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) : σ.PropIV61 :=
  σ.propIV61 hσ hII (σ.lemmaIV32_of hσ hII) (σ.lemmaIV33 hσ hII)

theorem corIV61_of (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) : σ.CorIV61 :=
  σ.corIV61 hσ hII (σ.propIV61_of hσ hII) (σ.propIV62 hσ hII)

end Setting

end CFSG.ABGTheoremB

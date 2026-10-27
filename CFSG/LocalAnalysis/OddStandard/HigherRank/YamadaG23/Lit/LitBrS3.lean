module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitS3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitS3B

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1
  CFSG.GH74.GLS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {Gh Zh Ah : Subgroup Γ} {t : Γ}

theorem lit_hO [(Zh.subgroupOf Gh).Normal] (c : LitCtx (Zh.subgroupOf Gh) (Ah.subgroupOf Gh))
    (h : LitGam Gh Zh Ah t)
    (hq : IsQuotIso (normIn Gh Ah) (Gh ⊓ centralizerSection Ah Zh) (Equiv.Perm (Fin 6)))
    (hT : IsQuotIso (Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh)
      (Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh ⊓ (Gh ⊓ centralizerSection Ah Zh))
      ↥blockStab)
    (φ : ↥(normalizer ((Ah.subgroupOf Gh : Subgroup ↥Gh) : Set ↥Gh)) →* Equiv.Perm (Fin 6))
    (hφs : Function.Surjective φ)
    (hφk : ∀ g : ↥(normalizer ((Ah.subgroupOf Gh : Subgroup ↥Gh) : Set ↥Gh)),
      φ g = 1 ↔ ∀ a ∈ Ah.subgroupOf Gh, ⁅a, (g : ↥Gh)⁆ ∈ Zh.subgroupOf Gh) :
    ∀ a ∈ Ah.subgroupOf Gh, ∀ x ∈ CFSG.oddCore ↥Gh, x * a = a * x := by
  classical
  obtain ⟨b, hbA, hbZ, hb_comm⟩ := lit_s3_comm h hq hT
  let b' : ↥Gh := ⟨b, h.A_le_G hbA⟩
  have hb'A : b' ∈ Ah.subgroupOf Gh := by
    rw [Subgroup.mem_subgroupOf]
    exact hbA
  have hb'Z : b' ∉ Zh.subgroupOf Gh := by
    intro hz
    exact hbZ (by rwa [Subgroup.mem_subgroupOf] at hz)
  have hb'' : ∀ x ∈ CFSG.oddCore ↥Gh, x * b' = b' * x := by
    intro x hx
    apply Subtype.ext
    exact hb_comm (x : Γ) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  haveI : (litP (Zh.subgroupOf Gh)).Normal := Subgroup.sup_normal _ _
  exact lit_s3b c (QuotientGroup.mk'_surjective (litP (Zh.subgroupOf Gh)))
    (QuotientGroup.ker_mk' (litP (Zh.subgroupOf Gh))) φ hφs hφk hb'A hb'Z hb''

end CFSG.OddStandard.HigherRank.YamadaG23

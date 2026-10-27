module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Inputs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Thm84K_of (h36 : Asc82Lemma36) (hZ : Asc82ZExists) (h83 : Asc82Lemma83)
    (hM : Asc82Tab6M) (hE : Asc82FinkE) (hK : Asc82Step84GamK) (hEnd : Asc82Step84End) :
    Asc82Thm84K := by
  intro G _ _ hKP t L hS hΩ
  by_contra hneg
  have hnoi3 : ∀ s : G, s ∈ centralizer ({t} : Set G) → orderOf s = 2 →
      ∀ α : ℤˣ, ¬ InducesTypeSome L s 6 (-1) 3 α := by
    intro s hsC hs2 α htype
    exact hneg ⟨s, hs2, hsC, α, htype⟩
  obtain ⟨S, hSsyl, _⟩ :=
    sec68_exists_sylow_ge (G := G) (B := ⊥) (H := centralizer ({t} : Set G))
      IsPGroup.of_bot bot_le
  obtain ⟨z, hz⟩ := hZ G t L hS S hSsyl
  have hconj : IsConj t (t * z) := h83 G t L hS hΩ z hz.pocket.1 hz.pocket.mem
  obtain ⟨g, hg⟩ := isConj_iff_inv_mul.mp hconj
  have hLcent : L ≤ centralizer ({t} : Set G) := hS.component.le
  have hN : ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 hS
  have hP : IsSylow2Of (S ⊓ L) L := sec4_isSylow2Of_inf hLcent hN hSsyl
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hΩ⟩
  obtain ⟨B, _B₂, _hBne, hBnorm, _hB₂norm, _huniq⟩ :=
    hM.sylow_E16 G L hLM (S ⊓ L) hP
  have hsetting : Sec8Setting G t L S z :=
    { toSec3SettingLB := hS, toAsc82Notation := hz, omega6m := hΩ }
  have hbase : Sec8Base G t L S z g B :=
    ⟨hsetting, hg, by rw [inf_comm]; exact hBnorm.1, hBnorm.2.1⟩
  have hctx : Sec8Ctx G t L S z g B := ⟨hbase, hnoi3⟩
  obtain ⟨E, hE'⟩ := hE G t L S z g B hctx
  obtain ⟨γ, K, U, hγ⟩ := hK G hKP t L S z g B E hE'
  exact hEnd G t L S z g B γ K U hγ

end CFSG.OddStandard.SmallF3.Omega

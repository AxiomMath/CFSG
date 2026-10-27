module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23Pair
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiNoBigger

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

@[expose] def Fi24Cfg610Hyp35 : Prop :=
  Sol78Lit → ∀ (H : Type) [Group H] [Finite H], BelowSec (Sol78PredS fiTypes) H →
    ∀ (N L : Subgroup H) (t u : H), CFSG.Assembly.KProper CFSG.Blueprint.Catalog H →
      OddCover .Fi24Prime L → Cfg610_2 H N L t u → ∀ (K : Subgroup H) (u₀ : H), K ≤ L →
        K ≤ centralizer ({u} : Set H) → IsSporadic ↥K .Fi23 → u₀ ∈ K → Fi23Transposition K u₀ →
          K ⊓ centralizer ({u₀} : Set H) = componentProduct (K ⊓ centralizer ({u₀} : Set H)) u₀

section Certificates


theorem fi24_cfg610_false (hin : Sol78Closing [.Fi24Prime] fun _ => fiIn24)
    (h35 : Fi24Cfg610Hyp35) (lit : Sol78Lit) {H : Type} [Group H] [Finite H]
    (ih : BelowSec (Sol78PredS fiTypes) H) {N L : Subgroup H} {t u : H}
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hcov : OddCover .Fi24Prime L)
    (hcfg : Cfg610_2 H N L t u) : False := by
  obtain ⟨K, _, _, hd⟩ := hcfg.exists_data
  have hKL := hd.le_L
  have hKC := hd.le_C
  have hKs := hd.isSporadic
  obtain ⟨K₀, u₀, hu₀K, hT, hK₀, hloc⟩ := exists_fiLoc_pair_of_isSporadic_fi23 hKs hKL
  have hyp35 : K₀ = componentProduct K₀ u₀ := by
    subst hK₀
    exact h35 lit H ih N L t u hKP hcov hcfg K u₀ hKL hKC hKs hu₀K hT
  have hfi : fiIn24 H L K₀ u₀ := fiInBase_iff.2 ⟨hloc, noBiggerFi_fi24Prime H⟩
  have hglob : SolomonGlobalQ H L K₀ t u₀ :=
    { standardL := hcfg.standardL
      cyclicSylow := hcfg.cyclicSylow
      t_order := hcfg.t_order
      t_mem := hcfg.t_mem
      u_comm_t := mem_centralizer_iff.1 hcfg.t_mem u₀ hfi.1
      hyp35 := hyp35 }
  exact hin H N L K₀ t u₀ .Fi24Prime (List.mem_singleton.2 rfl) hcfg.fstar hcfg.index_le_two hKP
    hcov hglob hfi

end Certificates

end CFSG.EvenSporadicStandard.Induction

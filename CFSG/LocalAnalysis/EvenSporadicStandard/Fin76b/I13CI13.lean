module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13CI12

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α) {π : MulAut ↥E →* Equiv.Perm (Fin 5)}

theorem caseI_false (hπ : EPi E π)
    (hI : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔
      π a ∈ alternatingGroup (Fin 5) ∧ π b = π a)
    (hfix : ∀ φ : MulAut ↥E, BInv E π φ → Nat.card {e : ↥E // φ e = e} = 4)
    (hE64 : c.E64Statement) (hrank : RankStatement z) : False := by
  have : IsSimpleGroup G := c.h.conf.std.simple
  obtain ⟨Rs, hRs2, hzRs, -, hRsN, hmax, -⟩ := c.h.exists_Rs c.hα
  have hR : c.IsRs Rs := ⟨hRs2, hzRs, hRsN, hmax⟩
  have hSyl : ¬ 2 ∣ Rs.index := hR.not_two_dvd_index_caseI hπ hI hfix
  obtain ⟨g, hg⟩ := CFSG.EvenSporadicStandard.exists_conj_mem_complement
    c.h.conf.std.nonabelian hRs2 hSyl (inf_le_left : Rs ⊓ c.N1 ≤ Rs) hR.relIndex_R.1 hzRs
    hR.relIndex_R.2 c.h.conf.cfg.z_order
  exact hR.not_conj_z_of_mem_R0 hπ hI hE64 hrank hg ⟨g⁻¹, by group⟩

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b

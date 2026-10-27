module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cover
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5QCStep
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5QCHom
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverPocket
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5PocketOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82FactQCentTwo6_of (hS : Asc82SchurU43) : Asc82FactQCentTwo6 := by
  intro G _ _ L z hL hI K₁ K₂ h₁ h₂ _hne hQ₁ _hQ₂ _hcomm hcard _hcen x hxN hxz hxQ n hn
  obtain ⟨V, _, _, _, Q, hQ, φ, hφ⟩ := t5_exists_cover hS hL
  have hdim := hφ.finrank_eq
  have hsgn := hφ.quadSign_eq
  have hoc : OddCentralCover φ := hφ.oddCentralCover hL
  have hz2 : orderOf z = 2 := hI.1
  have hzL : z ∈ L := (Subgroup.mem_inf.mp (h₁.2.1 h₁.1)).1
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2]; exact pow_orderOf_eq_one z
  let zL : ↥L := ⟨z, hzL⟩
  have hzLord : orderOf zL = 2 := (Subgroup.orderOf_mk z hzL).trans hz2
  have hφzz : φ zL * φ zL = 1 := by
    rw [← map_mul, show zL * zL = 1 from Subtype.ext hzz, map_one]
  have hφz1 : φ zL ≠ 1 := by
    intro h
    have h2 := l34g_x_orderOf_map hoc hzLord
    rw [h, orderOf_one] at h2
    omega
  have hI4 : IsI4PlusIn (⊤ : Subgroup ↥(omegaGroup hQ)) (φ zL) :=
    (t5_isI4PlusIn_iff hL hφ hzL hz2).mp hI
  have hztt : ((φ zL : omegaGroup hQ) : OGroup Q) * ((φ zL : omegaGroup hQ) : OGroup Q) = 1 :=
    congrArg Subtype.val hφzz
  have hzt4 : invType ((φ zL : omegaGroup hQ) : OGroup Q) = (4, 1) :=
    (t5_isI4PlusIn_omega_iff hdim hsgn hztt hφz1).mp hI4
  let D : Om6Par Q (sec5cdPhi φ zL) := Om6Par.mk' hQ hdim hsgn hztt hzt4
  let f := sec5cdPhi φ
  let f' : ↥L →* OGroup Q := f.comp (L.normalizerMonoidHom ⟨x, hxN⟩).toMonoidHom
  have key : ∀ g : ↥L, Odd (orderOf g) → g * ⟨z, hzL⟩ = ⟨z, hzL⟩ * g → f' g = f g :=
    fun g hg hgz =>
      sec5qc_step hoc hφ.ker_eq hzL hz2 D h₁ h₂ hQ₁ hcard hxN hxz hxQ hg hgz
  obtain ⟨l, hln, hl⟩ := sec5qc_twoRes_lift hzL f f' key n hn
  rw [← hln]
  have hl' : sec5cdPhi φ (L.normalizerMonoidHom ⟨x, hxN⟩ l) = sec5cdPhi φ l := hl
  exact sec5qc_comm_mem_oddCoreIn hφ.ker_eq hxN hl'

end CFSG.OddStandard.SmallF3.Omega

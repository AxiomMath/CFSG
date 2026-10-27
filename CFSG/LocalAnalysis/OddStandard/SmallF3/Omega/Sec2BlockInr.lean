module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Block

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def blockInr {s : OGroup Q} (hs : s * s = 1) :
    OGroup (Q.restrict (commSp s)) →* OGroup Q :=
  (blockHom hs).comp (MonoidHom.inr _ _)

theorem blockInr_apply {s : OGroup Q} (hs : s * s = 1) (b : OGroup (Q.restrict (commSp s))) :
    blockInr hs b = blockHom hs (1, b) := rfl

theorem blockInr_injective {s : OGroup Q} (hs : s * s = 1) : Function.Injective (blockInr hs) := by
  intro a b h
  have h' : blockHom hs (1, a) = blockHom hs (1, b) := h
  exact congrArg Prod.snd (blockHom_injective hs h')

theorem blockInr_piOrth {s : OGroup Q} (hs : s * s = 1) :
    blockInr hs (piOrth (Q.restrict (commSp s))) = s :=
  blockHom_one_piOrth hs

theorem blockInr_mem_centralizer (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (b : OGroup (Q.restrict (commSp s))) :
    blockInr hs b ∈ Subgroup.centralizer ({s} : Set (OGroup Q)) := by
  rw [← range_blockHom hQ hs]
  exact ⟨(1, b), rfl⟩

theorem blockInr_conj (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1) {c : OGroup Q}
    (hc : c ∈ Subgroup.centralizer ({s} : Set (OGroup Q))) (b : OGroup (Q.restrict (commSp s))) :
    ∃ c₂ : OGroup (Q.restrict (commSp s)),
      c * blockInr hs b * c⁻¹ = blockInr hs (c₂ * b * c₂⁻¹) := by
  rw [← range_blockHom hQ hs] at hc
  obtain ⟨p, rfl⟩ := hc
  refine ⟨p.2, ?_⟩
  rw [blockInr_apply, blockInr_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  ext <;> simp

theorem blockInr_mem_omegaGroup (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hU : 2 ≤ Module.finrank (ZMod 3) (commSp s)) {b : OGroup (Q.restrict (commSp s))}
    (hb : b ∈ omegaGroup (nondegenerate_restrict_commSp hQ hs)) :
    blockInr hs b ∈ omegaGroup hQ :=
  blockHom_right_mem_omegaGroup hQ hs hU hb

end CFSG.OddStandard.SmallF3.Omega

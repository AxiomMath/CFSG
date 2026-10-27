module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporSevenType

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

open CFSG.RankThree.Native CFSG.HardMathSupport.Solomon.Coordinator CFSG.Monster.B.Fischer


theorem card_centralizer_five_fi22P (k : ↥fi22P) (hk : orderOf k = 5) :
    Nat.card (Subgroup.centralizer ({k} : Set ↥fi22P)) = 600 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, -, -, hQsyl⟩, ⟨hlinesSet, -⟩, -, hrec⟩ :=
    R3E_Fi22_full_five_centralizers_common_outer_involution
  have hQ := card_eq_of_sylow_subgroupOf hQP hQsyl
  have hlines := lines_of_eq hlinesSet
  have hko : orderOf (k : Equiv.Perm (Fin 3510)) = 5 := by rw [Subgroup.orderOf_coe]; exact hk
  obtain ⟨g, hgP, hgQ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.exists_conj_mem_of_full hQP hQ k.2 hko
  set t := g⁻¹ * (k : Equiv.Perm (Fin 3510)) * g with htdef
  have hto : orderOf t = 5 := by
    have := (MulAut.conj g⁻¹ : Equiv.Perm (Fin 3510) ≃* Equiv.Perm (Fin 3510)).orderOf_eq k
    simpa [MulAut.conj_apply, htdef, hko] using this
  obtain ⟨j, hj⟩ := hlines (Subgroup.zpowers t) ((Subgroup.zpowers_le).2 hgQ)
    (by rw [Nat.card_zpowers, hto])
  have htP : t ∈ fi22P := fi22P.mul_mem (fi22P.mul_mem (fi22P.inv_mem hgP) k.2) hgP
  have hlP : fi22FiveLine j ∈ fi22P := by
    have h1 : fi22FiveLine j ∈ Subgroup.zpowers t := hj ▸ Subgroup.mem_zpowers _
    exact (Subgroup.zpowers_le.2 htP) h1
  obtain ⟨-, -, hCP, hCcard, -⟩ := hrec j
  have hline : Nat.card (Subgroup.centralizer ({(⟨fi22FiveLine j, hlP⟩ : ↥fi22P)} : Set ↥fi22P)) =
      600 := by
    rw [← Subgroup.card_map_of_injective fi22P.subtype_injective, map_centralizer_subtype,
      ← hCcard, hCP]
  have ht : Nat.card (Subgroup.centralizer ({(⟨t, htP⟩ : ↥fi22P)} : Set ↥fi22P)) = 600 := by
    rw [centralizer_singleton_eq_of_zpowers (CFSG.LocalAnalysis.GLTheoremA.KDSpor.zpowers_subtype_eq
      (P := fi22P) (a := ⟨t, htP⟩) (b := ⟨fi22FiveLine j, hlP⟩) hj)]
    exact hline
  have hk' : (⟨g, hgP⟩ : ↥fi22P) * (⟨t, htP⟩ : ↥fi22P) * (⟨g, hgP⟩ : ↥fi22P)⁻¹ = k := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, htdef]
    group
  rw [← hk', card_centralizer_conj' (⟨g, hgP⟩ : ↥fi22P) ⟨t, htP⟩]
  exact ht

theorem card_centralizer_five_of_equiv {H : Type} [Group H] (e : H ≃* ↥fi22P) (y : H)
    (hy : orderOf y = 5) : Nat.card (Subgroup.centralizer ({y} : Set H)) = 600 := by
  have hmap : (Subgroup.centralizer ({y} : Set H)).map e.toMonoidHom =
      Subgroup.centralizer ({e y} : Set ↥fi22P) := by
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [← map_mul, hu, map_mul]
    · intro hz
      refine ⟨e.symm z, ?_, by simp⟩
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hz]
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hmap]
  exact card_centralizer_five_fi22P (e y) (by rw [MulEquiv.orderOf_eq, hy])

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows

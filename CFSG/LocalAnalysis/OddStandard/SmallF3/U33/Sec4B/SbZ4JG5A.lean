module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC17
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NA

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z


variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
include hz

theorem z4j_bound_conj (g : G) {R : Subgroup G} (hR : IsPGroup 2 R)
    (hRc : R ≤ centralizer ({g * t * g⁻¹} : Set G)) : Nat.card R ≤ 128 := by
  have h := S4A.card_le_of_isPGroup_le_centralizer_conj (S := S) (t := t)
    hz.toCtx10.le_invCent hz.toCtx10.isPGroup hz.toCtx10.relIndex_odd
    (Ctx4.card_S_seven hz.toCtx10.toCtx4) g hR hRc
  norm_num at h
  exact h

theorem z4j_card_syl_cent (g : G) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPc : P ≤ centralizer ({g * t * g⁻¹} : Set G))
    (hPi : ¬ 2 ∣ P.relIndex (centralizer ({g * t * g⁻¹} : Set G))) : Nat.card P = 128 := by
  have hle := z4j_bound_conj hz g hP hPc
  have hge : 128 ≤ Nat.card P := by
    let H : Subgroup G := centralizer ({g * t * g⁻¹} : Set G)
    let S' : Subgroup G := S.map (MulAut.conj g).toMonoidHom
    have hS'le : S' ≤ H := by
      rintro x hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm : s * t = t * s :=
        Subgroup.mem_centralizer_singleton_iff.mp (hz.toCtx10.le_invCent hs)
      change g * s * g⁻¹ * (g * t * g⁻¹) = (g * t * g⁻¹) * (g * s * g⁻¹)
      calc (g * s * g⁻¹) * (g * t * g⁻¹) = g * (s * t) * g⁻¹ := by group
        _ = g * (t * s) * g⁻¹ := by rw [hcomm]
        _ = (g * t * g⁻¹) * (g * s * g⁻¹) := by group
    have hS'p : IsPGroup 2 S' := hz.toCtx10.isPGroup.map (MulAut.conj g).toMonoidHom
    have hS'card : Nat.card S' = 128 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
        Ctx4.card_S_seven hz.toCtx10.toCtx4]
      norm_num
    obtain ⟨k, -, hk⟩ := S4A.exists_conj_le_of_isPGroup hS'le hS'p hPc hP hPi
    have hmap : S'.map (MulAut.conj k).toMonoidHom ≤ P := by
      rintro _ ⟨q, hq, rfl⟩
      simpa [MulAut.conj_apply] using hk q hq
    have hcard : Nat.card (S'.map (MulAut.conj k).toMonoidHom) = 128 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hS'card]
    have hle' := Subgroup.card_le_of_le hmap
    rw [hcard] at hle'
    exact hle'
  omega

theorem z4j_conj_onto_S (g : G) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPc : P ≤ centralizer ({g * t * g⁻¹} : Set G)) (hP128 : Nat.card P = 128) :
    ∃ k : G, P.map (MulAut.conj k).toMonoidHom = S := by
  obtain ⟨k, hk⟩ := S4B.c17_exists_conj hz.toCtx10 g hP hPc
  refine ⟨k, ?_⟩
  have hmap : P.map (MulAut.conj k).toMonoidHom ≤ S := by
    rintro _ ⟨p, hp, rfl⟩
    simpa [MulAut.conj_apply] using hk p hp
  have hcard : Nat.card (P.map (MulAut.conj k).toMonoidHom) = Nat.card S := by
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hP128,
      Ctx4.card_S_seven hz.toCtx10.toCtx4]
    norm_num
  exact Subgroup.eq_of_le_of_card_ge hmap (le_of_eq hcard.symm)

theorem z4j_nonabelian : ∃ a b : G, a * b ≠ b * a := by
  refine ⟨x₁ ^ 2, lam, fun hcv => ?_⟩
  have hconj : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := by rw [← hcv]; group
  exact hz.y_ne_x₂_sq (hconj.symm.trans hz.nGood.lam_conj_y)

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33

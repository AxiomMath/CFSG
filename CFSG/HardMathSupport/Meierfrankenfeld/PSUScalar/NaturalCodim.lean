module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.UnitaryOrderBound
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.WittTransport

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open Module CFSG.Open CFSG.HardMathSupport.GuralnickMalle CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits

theorem one_le_natCodim_and_mul_le {K : Type} [Field K] [Finite K] [CharP K 2] {m f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) {P : Subgroup (SU (unitaryInvolution K 2 f) m)} (hP : P ≠ ⊥)
    (hPel : IsElemAbelian 2 P) {k : Type} [Field k] (φ₀ : K →+* k) {s e : ℕ}
    (hse : 2 ^ (s * e) ≤ 2 * Nat.card P) :
    1 ≤ m - finrank k (fixSubGen (suNaturalRep φ₀ (unitaryInvolution K 2 f) m) P) ∧
      s * e ≤ 1 + f * ((m - finrank k (fixSubGen (suNaturalRep φ₀ (unitaryInvolution K 2 f) m) P)) *
        (m - (m - finrank k (fixSubGen (suNaturalRep φ₀ (unitaryInvolution K 2 f) m) P)))) := by
  let eS := suToStated hK m
  let P₀ : Subgroup (StatedSU m (2 ^ f) K) := P.map eS.toMonoidHom
  let A : Subgroup (GL (Fin m) K) := P₀.map (StatedSU m (2 ^ f) K).subtype
  have hPP₀ : P₀.comap eS.toMonoidHom = P :=
    Subgroup.comap_map_eq_self_of_injective eS.injective P
  have hd : finrank k (fixSubGen (suNaturalRep φ₀ (unitaryInvolution K 2 f) m) P) =
      finrank K (fixSubGen (glNaturalRep m K) A) := by
    rw [← hPP₀]
    exact finrank_fixSubGen_suNaturalRep hK φ₀ P₀
  rw [hd]
  have hdm : finrank K (fixSubGen (glNaturalRep m K) A) ≤ m := by
    simpa using Submodule.finrank_le (fixSubGen (glNaturalRep m K) A)
  have hcardA : Nat.card A = Nat.card P := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective eS.injective]
  have hAS : A ≤ StatedSU m (2 ^ f) K := Subgroup.map_subtype_le P₀
  have hAel : IsElemAbelian 2 A := (hPel.map eS.toMonoidHom).map _
  have hT1 := card_le_pow_fix_mul_of_le_statedSU hK hAS hAel
  refine ⟨?_, ?_⟩
  ·
    by_contra hlt
    have hdm' : finrank K (fixSubGen (glNaturalRep m K) A) = finrank K (Fin m → K) := by
      rw [Module.finrank_fin_fun]
      omega
    have htop : fixSubGen (glNaturalRep m K) A = ⊤ := Submodule.eq_top_of_finrank_eq hdm'
    apply hP
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    have hgA : ((eS g : StatedSU m (2 ^ f) K) : GL (Fin m) K) ∈ A :=
      ⟨eS g, ⟨g, hg, rfl⟩, rfl⟩
    have hrep : glNaturalRep m K ((eS g : StatedSU m (2 ^ f) K) : GL (Fin m) K) =
        glNaturalRep m K 1 := by
      refine LinearMap.ext fun v => ?_
      have hv : v ∈ fixSubGen (glNaturalRep m K) A := by
        rw [htop]
        exact Submodule.mem_top
      rw [(mem_fixSubGen.mp hv) _ hgA, map_one, Module.End.one_apply]
    have h1 : eS g = 1 := Subtype.ext (glNaturalRep_injective m K hrep)
    exact (map_eq_one_iff eS eS.injective).mp h1
  ·
    have hcm : m - (m - finrank K (fixSubGen (glNaturalRep m K) A)) =
        finrank K (fixSubGen (glNaturalRep m K) A) := by
      omega
    rw [hcm]
    have hpow : 2 ^ (s * e) ≤ 2 ^ (1 + f * ((m - finrank K (fixSubGen (glNaturalRep m K) A)) *
        finrank K (fixSubGen (glNaturalRep m K) A))) := by
      calc 2 ^ (s * e) ≤ 2 * Nat.card P := hse
        _ = 2 * Nat.card A := by rw [hcardA]
        _ ≤ 2 * (2 ^ f) ^ (finrank K (fixSubGen (glNaturalRep m K) A) *
            (m - finrank K (fixSubGen (glNaturalRep m K) A))) :=
          Nat.mul_le_mul_left 2 hT1
        _ = 2 ^ (1 + f * ((m - finrank K (fixSubGen (glNaturalRep m K) A)) *
            finrank K (fixSubGen (glNaturalRep m K) A))) := by
          rw [← pow_mul, pow_add, pow_one, mul_comm (finrank K _)]
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hpow

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKL3Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKAbs

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem examExcludes_evenL3_large : ExamExcludes FamEvenL3Large := by
  rintro G _ _ K B B' P R m h ⟨f, hf3, hmodel⟩
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmodel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcp : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hF
  have hF8 : 8 ≤ Nat.card F := by
    rw [hF]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
  have habs := h.toAbs
  let ψ : (↥K ⧸ Subgroup.center ↥K) ≃* projectiveSL 3 F :=
    e.trans (CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL 3 F)
  let θ : ↥K →* projectiveSL 3 F := ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hθsurj : Function.Surjective θ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hθker : θ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    change ψ (QuotientGroup.mk x) = 1 ↔ _
    rw [map_eq_one_iff ψ ψ.injective, QuotientGroup.eq_one_iff]
  obtain ⟨S, hSU⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf (projUnitriangular 3 F) ⊤ :=
    hSU ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
  obtain ⟨R₀, A₀, hR₀U, hnorm, hcardR, hnea, hA₀R, hA₀e, hcardA, -⟩ :=
    habs.exists_Rprime θ hθsurj hθker.le (projUnitriangular 3 F) hU
  have hReq : R₀ = projUnitriangular 3 F :=
    L3Core.eq_projUnitriangular_of_normalized hF8 hR₀U
      (fun g hg r hr => hnorm g (Subgroup.le_normalizer hg) r hr)
      (fun s hs r hr => hnorm _ (L3Core.torus_mem_normalizer s hs) r hr) hnea
  have h3f : 3 * f = 4 * m := by
    rw [hReq, card_projUnitriangular, hF, ← pow_mul] at hcardR
    have := Nat.pow_right_injective (le_refl 2) hcardR
    norm_num at this
    omega
  have hA₀U : A₀ ≤ projUnitriangular 3 F := hA₀R.trans (hReq ▸ le_rfl)
  have hle := L3Core.card_le_sq_of_isElemAbelian hA₀U hA₀e
  rw [hcardA, hF, ← pow_mul] at hle
  have h3m : 3 * m ≤ f * 2 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  have hm := h.two_le
  omega

end CFSG.QuasithinUnique.Lin2

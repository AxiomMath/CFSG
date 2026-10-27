module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.NoKlein
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X3Aut CFSG.QuasithinUnique.A6Facts
open CFSG.RankThree.PartOne.OutStructure

set_option maxRecDepth 100000 in
theorem rank_two_rep_meets_psl :
    ((List.range repsC.length).all fun j => (rep j).length != 4 ||
      (rep j).any fun e => e != Core.cid && Core.pslLit.contains e) = true := by
  decide +kernel


theorem mem_PslSub_of_cd_mem {x : AutA6} (h : Core.pslLit.contains (cd x) = true) : x ∈ PslSub := by
  obtain ⟨y, hy, hyc⟩ := exists_psl29_of_code (List.contains_iff_mem.mp h)
  have : (x : P10) = y := code_injective hyc.symm
  rw [mem_PslSub, this]
  exact hy

theorem noKlein_alternatingGroup_six : NoKlein (alternatingGroup (Fin 6)) := by
  classical
  intro B hcomm hsq hcard hinn
  let B₁ : Subgroup AutA6 := B.map thetaEquiv.symm.toMonoidHom
  have hB₁c : ∀ a ∈ B₁, ∀ b ∈ B₁, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  have hB₁s : ∀ a ∈ B₁, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hsq a ha, map_one]
  have hel : CFSG.IsElementaryAbelian 2 ↥B₁ := by
    refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
    · exact IsMulCommutative.of_setLike_mul_comm fun a ha b hb => hB₁c a ha b hb
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_
      apply Subtype.ext
      rw [Subgroup.coe_pow, pow_two]
      exact hB₁s x x.2
  have hcard1 : Nat.card B₁ = 2 ^ 2 := by
    rw [Subgroup.card_map_of_injective thetaEquiv.symm.injective, hcard]; norm_num
  obtain ⟨-, j, hj, hlen, n, hn⟩ := rank_lemma 2 B₁ hel hcard1
  obtain ⟨hnd, hcid, -⟩ := rep_spec hj
  have hex : ∃ e ∈ rep j, e ≠ Core.cid ∧ Core.pslLit.contains e = true := by
    have h := rank_two_rep_meets_psl
    rw [List.all_eq_true] at h
    have := h j (List.mem_range.mpr hj)
    rw [Bool.or_eq_true] at this
    rcases this with h4 | h4
    · exfalso
      rw [bne_iff_ne] at h4
      apply h4
      rw [hlen]; norm_num
    · obtain ⟨e, he, hee⟩ := List.any_eq_true.mp h4
      rw [Bool.and_eq_true, bne_iff_ne] at hee
      exact ⟨e, he, hee.1, hee.2⟩
  obtain ⟨e, he, hecid, hepsl⟩ := hex
  obtain ⟨b, hb, hbe⟩ := conjInto_surj hnd (by rw [hcard1, hlen]) hn e he
  have hnb : n * b * n⁻¹ ∈ PslSub := mem_PslSub_of_cd_mem (by rw [hbe]; exact hepsl)
  have hbP : b ∈ PslSub := by
    have := PslSub_normal (g := n⁻¹) hnb
    simpa [mul_assoc] using this
  obtain ⟨b', hb', hb'eq⟩ := hb
  have hbinn : thetaEquiv b ∈ (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range := by
    rw [← map_PslSub_eq_inner]; exact ⟨b, hbP, rfl⟩
  have hbB : thetaEquiv b ∈ B := by
    rw [← hb'eq]
    simpa using hb'
  have h1 : thetaEquiv b ∈ B ⊓ Inn (alternatingGroup (Fin 6)) := ⟨hbB, hbinn⟩
  rw [hinn] at h1
  have hb1 : b = 1 := by
    have : thetaEquiv b = 1 := by simpa using h1
    simpa using thetaEquiv.injective (this.trans (map_one thetaEquiv).symm)
  apply hecid
  rw [← hbe, hb1]
  simp [cd_one]

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

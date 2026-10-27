module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphOmegaBlock
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.OrthMinus
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusHat

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Omega

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus
open CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.U42O8.OmegaMinusEight
open CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus CFSG.RankThree.OrthogonalInvolutions

theorem card_le_two_mul_card_ker_orthLeviHom {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} {s : ℕ} {d : Fin (s + 1) → ℕ} (hd : OrthCuts 3 d)
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (hK : Nat.card K = 2) (hlast : d (Fin.last s) = 3)
    (h3 : ∀ l : Fin s, d l.succ - d l.castSucc ≠ 3)
    {S : Subgroup ↥(orthParab 3 (minusTailForm K b c) d)} (hS : IsPGroup 2 S) :
    Nat.card S ≤ 2 * Nat.card (orthLeviHom b c hd).ker := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) :=
    finite_orthLinearEquiv
  let Tj : ∀ j : Fin s ⊕ Unit, Subgroup (orthLeviGroup K 3 d j) := fun j =>
    match j with
    | .inl _ => ⊤
    | .inr _ => omegaGroup (quadTail (3 - d (Fin.last s)) (minusTailForm K b c))
        (nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr))
  have hmem : ∀ (x : ↥(orthParab 3 (minusTailForm K b c) d)) (j : Fin s ⊕ Unit),
      orthLeviHom b c hd x j ∈ Tj j := by
    intro x j
    rcases j with l | u
    · exact Subgroup.mem_top _
    · obtain rfl : u = () := rfl
      rw [orthLeviHom_inr]
      exact orthResHom_mem_omegaGroup hd le_rfl hirr x
  let γ : ↥S →* ∀ j, ↥(Tj j) := MonoidHom.pi fun j =>
    ((Pi.evalMonoidHom (orthLeviGroup K 3 d) j).comp
      ((orthLeviHom b c hd).comp S.subtype)).codRestrict (Tj j) fun x => hmem x j
  have hker : Nat.card γ.ker ≤ Nat.card (orthLeviHom b c hd).ker := by
    rw [← Subgroup.card_map_of_injective S.subtype_injective (f := S.subtype)]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [MonoidHom.mem_ker]
    funext j
    exact congrArg Subtype.val (congrFun (MonoidHom.mem_ker.1 hx) j)
  have hrange : IsPGroup 2 ↥γ.range := hS.of_surjective γ.rangeRestrict γ.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hrange
  have hdvd : Nat.card ↥γ.range ∣ ∏ j, Nat.card ↥(Tj j) := by
    have := Subgroup.card_subgroup_dvd_card γ.range
    rwa [Nat.card_pi] at this
  have hΩ : Odd (Nat.card ↥(Tj (.inr ()))) :=
    odd_card_omegaGroup_tail_of_eq_zero (by omega) hirr
  have hprod : ∏ j, Nat.card ↥(Tj j) =
      (∏ l : Fin s, Nat.card (GL (Fin (d l.succ - d l.castSucc)) K)) *
        Nat.card ↥(Tj (.inr ())) := by
    rw [Fintype.prod_sum_type]
    simp only [Finset.univ_unique, Finset.prod_singleton]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    show Nat.card ↥(⊤ : Subgroup (GL (Fin (d l.succ - d l.castSucc)) K)) = _
    rw [Subgroup.card_top]
  have h6 := prod_card_GL_dvd_six hK hd hlast h3
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥(Tj (.inr ()))) :=
    (Nat.coprime_two_left.2 hΩ).pow_left k
  rw [hk, hprod] at hdvd
  have h2k : 2 ^ k ∣ 6 := (hcop.dvd_of_dvd_mul_right hdvd).trans h6
  have hle2 : 2 ^ k ≤ 2 := by
    have hk3 : k < 3 := by
      by_contra hcon
      have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hcon)
      have := Nat.le_of_dvd (by norm_num) h2k
      omega
    interval_cases k
    · norm_num
    · norm_num
    · norm_num at h2k
  calc Nat.card S = Nat.card γ.ker * Nat.card γ.range := (Subgroup.card_ker_mul_card_range γ).symm
    _ ≤ Nat.card (orthLeviHom b c hd).ker * 2 := by
        rw [hk]
        exact Nat.mul_le_mul hker hle2
    _ = 2 * Nat.card (orthLeviHom b c hd).ker := mul_comm _ _

theorem card_le_two_mul_pCoreOf_of_solvThree {A : Type} [Group A] [Finite A] {Y P : Subgroup A}
    (h : IsLieOver ↥Y (.twistedD 4) 2 1) (hP : IsParabolicTwo Y P)
    (hperf : ∀ J : Subgroup A, J ≤ P → ⁅J, J⁆ = J → ¬ 3 ∣ Nat.card J) :
    ∀ S : Subgroup A, S ≤ P → IsPGroup 2 S → Nat.card S ≤ 2 * Nat.card (pCoreOf 2 P) := by
  classical
  obtain ⟨K, _, _, _, b, c, hK, hirr, ⟨φ⟩⟩ := exists_model h
  obtain ⟨ρ, s, d, hd, hρ⟩ :=
    LeviBlock.exists_comap_eq_orthParab (by norm_num) hirr hP φ.symm
  let C : OmCover Y P 3 K b c d := ⟨ρ, hρ⟩
  haveI : Finite ↥(orthElementaryGroup (quadTail 3 (minusTailForm K b c))) :=
    Finite.of_equiv _ C.ρ.symm.toEquiv
  have hlast : d (Fin.last s) = 3 := by
    by_contra hne
    obtain ⟨J, hJP, hJperf, hJ3⟩ :=
      exists_perfect_of_residual C hd hirr hK hP.1 (by have := hd.last; omega)
    exact hperf J hJP hJperf hJ3
  have h3 : ∀ l : Fin s, d l.succ - d l.castSucc ≠ 3 := by
    intro l hl
    obtain ⟨J, hJP, hJperf, hJ3⟩ := exists_perfect_of_block C hd hirr hK hl
    exact hperf J hJP hJperf hJ3
  intro S hSP hS
  let τ : ↥(orthParab 3 (minusTailForm K b c) d) ≃* ↥P :=
    MulEquiv.ofBijective C.toP ⟨C.toP_injective, C.toP_surjective hP.1⟩
  let SQ : Subgroup ↥(orthParab 3 (minusTailForm K b c) d) :=
    (S.subgroupOf P).map τ.symm.toMonoidHom
  have hSQp : IsPGroup 2 ↥SQ := (hS.comap_of_injective P.subtype P.subtype_injective).map _
  have hSQcard : Nat.card SQ = Nat.card S := by
    rw [Subgroup.card_map_of_injective τ.symm.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP).toEquiv
  have hbound := card_le_two_mul_card_ker_orthLeviHom hd hirr hK hlast h3 hSQp
  have hkerP : Nat.card (orthLeviHom b c hd).ker ≤ Nat.card (pCoreOf 2 P) := by
    have h1 : (orthLeviHom b c hd).ker ≤ C.toHat.ker := C.ker_orthLeviHom_le_ker_toHat hd hP.1
    rw [C.ker_toHat_eq] at h1
    have h2 : (orthLeviHom b c hd).ker.map C.toP ≤ CFSG.pCore 2 ↥P :=
      Subgroup.map_le_iff_le_comap.2 h1
    calc Nat.card (orthLeviHom b c hd).ker
        = Nat.card ((orthLeviHom b c hd).ker.map C.toP) :=
          (Subgroup.card_map_of_injective C.toP_injective).symm
      _ ≤ Nat.card (CFSG.pCore 2 ↥P) := Subgroup.card_le_of_le h2
      _ = Nat.card (pCoreOf 2 P) := (Subgroup.card_map_of_injective P.subtype_injective).symm
  rw [hSQcard] at hbound
  exact hbound.trans (Nat.mul_le_mul_left 2 hkerP)

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Omega

module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6E26A
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6E26B
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54R

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y6e_M3_comm (c : Ctx5 G L) (hF : c.Facts5) : IsMulCommutative ↥(M3 c.s) := by
  rcases hF.2.2.2.2.2.2 with ⟨-, hE⟩ | ⟨-, hMC, -⟩
  · exact hE.1
  · exact hMC

theorem y6e_card_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : Nat.card ↥(M3 c.s) = 64 := by
  have hFM3 : c.s.fr.F ≤ M3 c.s := le_sup_right
  have h := Subgroup.relIndex_mul_card (H := c.s.fr.F) (K := M3 c.s)
  rw [inf_of_le_left hFM3, y54_M3_relIndex c hH, (y54_F_isE3 hH).2] at h
  omega

theorem y6e_M3_pgroup (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : IsPGroup 2 ↥(M3 c.s) :=
  IsPGroup.of_card (n := 6) (by rw [y6e_card_M3 c hH]; norm_num)

theorem y6e_M3_equiv (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    Nonempty (↥(M3 c.s) ≃* (Fin 3 → Multiplicative (ZMod 4))) := by
  rcases hF.2.2.2.2.2.2 with ⟨-, hE⟩ | ⟨-, -, ⟨r, ⟨e⟩⟩, -⟩
  · exfalso
    have hA : LFactsA c.s := lfactsA_of_setting hH.hS hH.hZ c.s
    have hz2 : orderOf c.s.fr.z = 2 := s3_z_order c.s hA
    obtain ⟨hord, -⟩ := Ctx5pre.u_facts c.toCtx5.toCtx5pre hz2
    have hdt : c.d * c.s.t ∈ V1 c.e := by
      rw [c.hV]
      exact Subgroup.mem_zpowers _
    have hdtM : c.d * c.s.t ∈ M3 c.s := (inf_le_right : V1 c.e ≤ M3 c.s) hdt
    have h2 : (c.d * c.s.t) ^ 2 = 1 := hE.2 _ hdtM
    have hdvd : orderOf (c.d * c.s.t) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at hdvd
    omega
  · have hcard := y6e_card_M3 c.toCtx5 hH
    have hpi : Nat.card (Fin r → Multiplicative (ZMod 4)) = 4 ^ r := by
      rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have h4 : Nat.card (Multiplicative (ZMod 4)) = 4 := by
        rw [Nat.card_eq_fintype_card]
        decide
      rw [h4]
    have h64 : 4 ^ r = 4 ^ 3 := by
      rw [← hpi, ← Nat.card_congr e.toEquiv, hcard]
      norm_num
    have hr : r = 3 := Nat.pow_right_injective (by norm_num : 2 ≤ 4) h64
    subst hr
    exact ⟨e⟩

theorem y6e_NL_le_normalizer_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    normIn L c.s.fr.F ≤ normalizer (M3 c.s : Set G) :=
  Subgroup.le_normalizer_iff.mpr fun n hn m hm =>
    y54_N_norm_M3 c hH n (y54_NL_le_N hH hn) m hm

theorem y6e_NL_inf_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    normIn L c.s.fr.F ⊓ M3 c.s = c.s.fr.F := by
  refine le_antisymm ?_ (le_inf ?_ le_sup_right)
  · intro x hx
    obtain ⟨hxN, hxM⟩ := Subgroup.mem_inf.mp hx
    rw [← y54_H_inf_M3 c hH]
    exact Subgroup.mem_inf.mpr ⟨s3_L_le_H c.s hH.hS (Subgroup.mem_inf.mp hxN).1, hxM⟩
  · exact le_inf (y54_F_le_L c.s) Subgroup.le_normalizer

theorem y6e_card_X (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    Nat.card ↥(normIn L c.s.fr.F ⊔ M3 c.s) = 10752 := by
  have hprod := y6e_card_sup_mul_inf (y6e_NL_le_normalizer_M3 c hH)
  rw [y6e_NL_inf_M3 c hH, y54_card_N hH, y6e_card_M3 c hH, (y54_F_isE3 hH).2] at hprod
  omega

theorem y6e_S3_le_X (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    S3 c.s ≤ normIn L c.s.fr.F ⊔ M3 c.s :=
  sup_le_sup_right (y54_S_le_N hH) _

theorem y6e_S_inf_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : c.s.fr.S ⊓ M3 c.s = c.s.fr.F := by
  refine le_antisymm ?_ (le_inf ((s3_F_le_A c.s).trans (s3_A_le_S c.s)) le_sup_right)
  intro x hx
  have hx' : x ∈ normIn L c.s.fr.F ⊓ M3 c.s :=
    Subgroup.mem_inf.mpr ⟨y54_S_le_N hH (Subgroup.mem_inf.mp hx).1, (Subgroup.mem_inf.mp hx).2⟩
  rw [y6e_NL_inf_M3 c hH] at hx'
  exact hx'

theorem y6e_card_S3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : Nat.card ↥(S3 c.s) = 512 := by
  have hSN : c.s.fr.S ≤ normalizer (M3 c.s : Set G) :=
    (y54_S_le_N hH).trans (y6e_NL_le_normalizer_M3 c hH)
  have hprod := y6e_card_sup_mul_inf hSN
  rw [y6e_S_inf_M3 c hH, y54_card_S hH, y6e_card_M3 c hH, (y54_F_isE3 hH).2] at hprod
  show Nat.card ↥(c.s.fr.S ⊔ M3 c.s) = 512
  omega

theorem y6e_S3_pgroup (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : IsPGroup 2 ↥(S3 c.s) :=
  IsPGroup.of_card (n := 9) (by rw [y6e_card_S3 c hH]; norm_num)

theorem y6e_secProp (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    SecProp (normIn L c.s.fr.F ⊔ M3 c.s) (M3 c.s)
      (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) := by
  have hLE : normIn L c.s.fr.F ≤ normalizer (M3 c.s : Set G) := y6e_NL_le_normalizer_M3 c hH
  obtain ⟨hN, hP⟩ := hH.hLF.fact18.2.2.2.2.1
  obtain ⟨eGL⟩ := hP
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hLE
  haveI hnX := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
  have heq : (M3 c.s).subgroupOf (normIn L c.s.fr.F) =
      (zL L ⊔ c.s.fr.F).subgroupOf (normIn L c.s.fr.F) := by
    rw [f3_zL_eq_bot hH, bot_sup_eq]
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have : (x : G) ∈ normIn L c.s.fr.F ⊓ M3 c.s := ⟨x.2, hx⟩
      rwa [y6e_NL_inf_M3 c hH] at this
    · intro hx
      exact (le_sup_right : c.s.fr.F ≤ M3 c.s) hx
  refine ⟨hnX, ⟨?_⟩⟩
  exact (QuotientGroup.quotientInfEquivProdNormalizerQuotient (normIn L c.s.fr.F) (M3 c.s)
    hLE).symm.trans ((QuotientGroup.quotientMulEquivOfEq heq).trans eGL)

theorem y6e_cent (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5) :
    (normIn L c.s.fr.F ⊔ M3 c.s) ⊓ centralizer (M3 c.s : Set G) = M3 c.s := by
  haveI := y6e_M3_comm c hF
  have hLE : normIn L c.s.fr.F ≤ normalizer (M3 c.s : Set G) := y6e_NL_le_normalizer_M3 c hH
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.mp hx
    have hmem : x ∈ ((normIn L c.s.fr.F ⊔ M3 c.s : Subgroup G) : Set G) := hxX
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (normIn L c.s.fr.F) (M3 c.s) hLE] at hmem
    obtain ⟨n, hn, m, hm, rfl⟩ := hmem
    have hnC : ∀ y ∈ M3 c.s, y * n = n * y := by
      intro y hy
      have h1 : y * (n * m) = (n * m) * y := Subgroup.mem_centralizer_iff.mp hxC y hy
      have h2 : m * y = y * m := Subgroup.mul_comm_of_mem_isMulCommutative _ hm hy
      have h3 : y * n * m = n * y * m := by
        calc y * n * m = y * (n * m) := by rw [mul_assoc]
          _ = (n * m) * y := h1
          _ = n * (m * y) := by rw [mul_assoc]
          _ = n * (y * m) := by rw [h2]
          _ = n * y * m := by rw [mul_assoc]
      exact mul_right_cancel h3
    have hnF : n ∈ centIn L c.s.fr.F := by
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hn).1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      exact hnC f ((le_sup_right : c.s.fr.F ≤ M3 c.s) hf)
    rw [y54_centIn_L_F hH] at hnF
    exact (M3 c.s).mul_mem ((le_sup_right : c.s.fr.F ≤ M3 c.s) hnF) hm
  · intro x hx
    refine Subgroup.mem_inf.mpr
      ⟨(le_sup_right : M3 c.s ≤ normIn L c.s.fr.F ⊔ M3 c.s) hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mul_comm_of_mem_isMulCommutative _ hy hx

theorem y6e_isExt26 (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    Sec2.IsExt26 2 ↥(normIn L c.s.fr.F ⊔ M3 c.s) := by
  obtain ⟨e⟩ := y6e_M3_equiv c hH hF
  exact y6e_isExt26_of_sub (le_sup_right : M3 c.s ≤ normIn L c.s.fr.F ⊔ M3 c.s)
    (y6e_M3_pgroup c.toCtx5 hH) e (y6e_secProp c.toCtx5 hH) (y6e_cent c.toCtx5 hH hF)

theorem y6e_exists_sylow (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∃ P : Sylow 2 ↥(normIn L c.s.fr.F ⊔ M3 c.s),
      (P : Subgroup ↥(normIn L c.s.fr.F ⊔ M3 c.s)) =
        (S3 c.s).subgroupOf (normIn L c.s.fr.F ⊔ M3 c.s) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : S3 c.s ≤ normIn L c.s.fr.F ⊔ M3 c.s := y6e_S3_le_X c hH
  have hp : IsPGroup 2 ↥((S3 c.s).subgroupOf (normIn L c.s.fr.F ⊔ M3 c.s)) :=
    (y6e_S3_pgroup c hH).of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  have hidx : ¬ 2 ∣ ((S3 c.s).subgroupOf (normIn L c.s.fr.F ⊔ M3 c.s)).index := by
    have h := Subgroup.relIndex_mul_card (H := S3 c.s) (K := normIn L c.s.fr.F ⊔ M3 c.s)
    rw [inf_of_le_left hle, y6e_card_S3 c hH, y6e_card_X c hH] at h
    have h21 : (S3 c.s).relIndex (normIn L c.s.fr.F ⊔ M3 c.s) = 21 := by omega
    change ¬ 2 ∣ (S3 c.s).relIndex (normIn L c.s.fr.F ⊔ M3 c.s)
    rw [h21]
    decide
  exact ⟨hp.toSylow hidx, rfl⟩

theorem y6e_sylow_equiv {X S : Subgroup G} (hle : S ≤ X) (P : Sylow 2 ↥X)
    (hP : (P : Subgroup ↥X) = S.subgroupOf X) :
    ∃ φ : ↥P ≃* ↥S, ∀ x : ↥P, ((φ x : ↥S) : G) = (((x : ↥P) : ↥X) : G) :=
  ⟨(MulEquiv.subgroupCongr hP).trans (Subgroup.subgroupOfEquivOfLe hle), fun _ => rfl⟩

end CFSG.OddStandard.HigherRank.YamadaG23

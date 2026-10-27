module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.PGSp45Identification
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxPGStage
public import Certificates.Certificate27230
public import CFSG.Blueprint.Catalog
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG.Blueprint CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.EvenSporadicStandard.TwoHS
  CFSG.EvenSporadicStandard.TwoHS.GH312

theorem normal_of_index_le_two {X : Type*} [Group X] {H : Subgroup X} (h2 : H.index ≤ 2)
    (h0 : H.index ≠ 0) : H.Normal := by
  rcases (by omega : H.index = 1 ∨ H.index = 2) with h | h
  · exact Subgroup.normal_of_index_eq_one h
  · exact Subgroup.normal_of_index_eq_two h

theorem mem_of_pow_eq_one_of_index_le_two {X : Type*} [Group X] {H : Subgroup X}
    (h2 : H.index ≤ 2) (h0 : H.index ≠ 0) {x : X} {m : ℕ} (hm : Odd m) (hx : x ^ m = 1) :
    x ∈ H := by
  haveI := normal_of_index_le_two h2 h0
  rcases (by omega : H.index = 1 ∨ H.index = 2) with h | h
  · rw [Subgroup.index_eq_one] at h
    rw [h]
    exact Subgroup.mem_top x
  · have hx2 : x ^ 2 ∈ H := by
      have := H.pow_index_mem x
      rwa [h] at this
    obtain ⟨k, rfl⟩ := hm
    have e : x = (x ^ 2) ^ (k + 1) := by
      calc x = x ^ (2 * k + 1) * x := by rw [hx, one_mul]
        _ = (x ^ 2) ^ (k + 1) := by rw [← pow_succ, ← pow_mul]; ring_nf
    rw [e]
    exact Subgroup.pow_mem H hx2 _

theorem card_le_two_mul_inf {X : Type*} [Group X] [Finite X] {H : Subgroup X} (h2 : H.index ≤ 2)
    (K : Subgroup X) : Nat.card K ≤ 2 * Nat.card ↥(H ⊓ K) := by
  haveI := normal_of_index_le_two h2 Subgroup.index_ne_zero_of_finite
  have h1 : H.relIndex K ∣ H.index := Subgroup.relIndex_dvd_index_of_normal H K
  have h3 : H.relIndex K ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1).trans h2
  have h4 := Subgroup.relIndex_mul_card (H := H) (K := K)
  calc Nat.card K = H.relIndex K * Nat.card ↥(H ⊓ K) := h4.symm
    _ ≤ 2 * Nat.card ↥(H ⊓ K) := Nat.mul_le_mul_right _ h3

theorem exists_injective_hom_pgsp45 {X : Type} [Group X] [Finite X] (T : Subgroup X) [T.Normal]
    (e : T ≃* StatedProj (StatedSp 2 (ZMod 5)))
    (hC : Subgroup.centralizer (T : Set X) = ⊥) :
    ∃ ψ : X →* PGSp45, Function.Injective ψ := by
  haveI : IsSimpleGroup (StatedProj (StatedSp 2 (ZMod 5))) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 5) 2 (by norm_num)
      (Or.inl (Or.inr (by rw [Nat.card_zmod]; norm_num)))
  haveI : IsSimpleGroup T := e.isSimpleGroup
  let aut : X →* MulAut (StatedProj (StatedSp 2 (ZMod 5))) :=
    (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
  let aut' : X →* (conjAut 2 (ZMod 5)).range :=
    aut.codRestrict _ fun x => range_conjAut_eq_top ▸ Subgroup.mem_top _
  let ψ : X →* soGroup5 := rangeToSoGroup5.comp aut'
  have hφ : ∃ t ∈ T, ψ t ≠ 1 := by
    let s : StatedSp 2 (ZMod 5) := ⟨diagTwoOneThreeOneGsp, by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
      simpa [diagTwoOneThreeOneGsp] using diagTwoOneThreeOne_symplectic⟩
    refine ⟨e.symm (proj 2 (ZMod 5) s), (e.symm (proj 2 (ZMod 5) s)).2, ?_⟩
    have haut : aut (e.symm (proj 2 (ZMod 5) s)) = conjAut 2 (ZMod 5) diagTwoOneThreeOneGsp := by
      have : (⟨s, statedSp_le_gsp s.2⟩ : gsp 2 (ZMod 5)) = diagTwoOneThreeOneGsp := rfl
      rw [← this, ← conj_proj_statedSp_eq_conjAut]
      ext y
      simp [aut, MulAut.congr_apply, MulAut.conjNormal_val]
    have : aut' (e.symm (proj 2 (ZMod 5) s)) =
        ⟨conjAut 2 (ZMod 5) diagTwoOneThreeOneGsp, diagTwoOneThreeOneGsp, rfl⟩ :=
      Subtype.ext haut
    simp only [ψ, MonoidHom.comp_apply, this, rangeToSoGroup5_apply]
    exact gspToSoGroup5_diag_ne_one
  exact ⟨ψ, ψ.injective_of_simple_normal T hC hφ⟩

theorem factorization_two_card_pgsp45 : (9360000 : ℕ).factorization 2 = 7 := by
  have h : (9360000 : ℕ) = 2 ^ 7 * 73125 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

theorem card_pgsp45_arith {nX : ℕ} (h1 : 4680000 ∣ nX) (h3 : nX ≤ 9360000) (hX : 0 < nX)
    (h128 : 128 ∣ nX) : nX = 9360000 := by
  obtain ⟨k, hk⟩ := h1
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0] at hk
      omega
    · exact h0
  have hk2 : k ≤ 2 := by
    by_contra hk3
    replace hk3 := not_le.mp hk3
    clear h128
    omega
  interval_cases k
  · rw [hk] at h128
    norm_num at h128
  · clear h128
    omega

theorem index_arith {nG idx : ℕ} (h1 : 4680000 ≤ nG) (h : nG * idx = 9360000) : idx ≤ 2 := by
  by_contra h3
  replace h3 := not_le.mp h3
  have : nG * 3 ≤ nG * idx := Nat.mul_le_mul_left _ h3
  omega

structure PGSp45Emb {G : Type} [Group G] (ψ : G →* PGSp45) : Prop where
  inj : Function.Injective ψ
  card : Nat.card PGSp45 = 9360000
  index : ψ.range.index ≤ 2

theorem exists_pgsp45Emb {G : Type} [Group G] [Finite G]
    (S : Subgroup G) [S.Normal] (hS : LieModel S .PSp 2 5 1)
    (hcent : centralizer (S : Set G) = ⊥) : ∃ ψ : G →* PGSp45, PGSp45Emb ψ := by
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hS.statedClassicalModel_of_ne_zero (by norm_num)
  have e : S ≃* StatedProj (StatedSp 2 (ZMod 5)) :=
    e0.trans (statedProjStatedSpEquivZModFive (by simpa using hK))
  obtain ⟨ψ, hψ⟩ := exists_injective_hom_pgsp45 S e hcent
  have hc : PGStage1 := Certificates.certificate27230.toMatrix
  have hS4 : Nat.card S = 4680000 := by
    rw [Nat.card_congr e.toEquiv, natCard_statedProj_statedSp_zmod_five]
  have hXle : Nat.card PGSp45 ≤ 9360000 := card_soGroup5_le
  have hGdvd : 4680000 ∣ Nat.card G := hS4 ▸ Subgroup.card_subgroup_dvd_card S
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hGge : 4680000 ≤ Nat.card G := Nat.le_of_dvd hGpos hGdvd
  have hHG : Nat.card ψ.range = Nat.card G :=
    Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm
  have hGX : Nat.card G ∣ Nat.card PGSp45 := hHG ▸ Subgroup.card_subgroup_dvd_card ψ.range
  have h128 : 128 ∣ Nat.card PGSp45 :=
    (card_pgP0 hc) ▸ Subgroup.card_subgroup_dvd_card (pgP0 hc)
  have hXpos : 0 < Nat.card PGSp45 := Nat.card_pos
  have hX : Nat.card PGSp45 = 9360000 :=
    card_pgsp45_arith (hGdvd.trans hGX) hXle hXpos h128
  refine ⟨ψ, hψ, hX, ?_⟩
  have h1 := ψ.range.card_mul_index
  rw [hHG, hX] at h1
  exact index_arith hGge h1

namespace PGSp45Emb

variable {G : Type} [Group G] [Finite G] {ψ : G →* PGSp45} (h : PGSp45Emb ψ)

include h

theorem mem_range_of_pow_eq_one {z : PGSp45} {m : ℕ} (hm : Odd m) (hz : z ^ m = 1) :
    z ∈ ψ.range :=
  mem_of_pow_eq_one_of_index_le_two h.index Subgroup.index_ne_zero_of_finite hm hz

theorem exists_cent_of_odd {u : G} {z : PGSp45} {m : ℕ} (hm : Odd m) (hz : z ^ m = 1)
    (hcomm : z * ψ u = ψ u * z) : ∃ w ∈ centralizer ({u} : Set G), ψ w = z := by
  obtain ⟨w, hw⟩ := h.mem_range_of_pow_eq_one hm hz
  refine ⟨w, mem_centralizer_singleton_iff.2 ?_, hw⟩
  apply h.inj
  rw [map_mul, map_mul, hw]
  exact hcomm

theorem card_le_two_mul (K : Subgroup PGSp45) :
    Nat.card K ≤ 2 * Nat.card ↥(ψ.range ⊓ K) :=
  card_le_two_mul_inf h.index K

theorem card_inf_dvd (u : G) (K : Subgroup PGSp45) (hK : K ≤ centralizer ({ψ u} : Set PGSp45)) :
    Nat.card ↥(ψ.range ⊓ K) ∣ Nat.card ↥(centralizer ({u} : Set G)) := by
  let f : ↥(centralizer ({u} : Set G)) →* PGSp45 := ψ.comp (centralizer ({u} : Set G)).subtype
  have hf : Function.Injective f := h.inj.comp (Subgroup.subtype_injective _)
  have hle : ψ.range ⊓ K ≤ f.range := by
    rintro y ⟨⟨w, hw⟩, hyK⟩
    have hyc := mem_centralizer_singleton_iff.1 (hK hyK)
    have hwu : w * u = u * w := by
      apply h.inj
      rw [map_mul, map_mul, hw]
      exact hyc
    exact ⟨⟨w, mem_centralizer_singleton_iff.2 hwu⟩, hw⟩
  have h1 := Subgroup.card_dvd_of_le hle
  rwa [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm] at h1

end PGSp45Emb

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

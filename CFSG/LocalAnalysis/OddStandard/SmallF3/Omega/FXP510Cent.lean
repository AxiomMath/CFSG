module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Center
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTheta
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTransAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarE16

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem fx_p510_exists_E16 {t : G} (hcore : twoCoreIn L = zpowers t) {B : Subgroup G}
    (hBL : B ≤ L) (hB : IsElemAb2 B 5) (htB : t ∈ B)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) :
    ∃ U : Subgroup ↥(omegaProj hQ), IsElemAb2 U 4 ∧
      ∀ u ∈ U, ∃ b : ↥L, (b : G) ∈ B ∧ ff6mPhi e b = u := by
  let ψ : ↥B →* ↥(omegaProj hQ) := (ff6mPhi e).comp (Subgroup.inclusion hBL)
  have hsq : ∀ b : ↥B, b ^ 2 = 1 := fun b => Subtype.ext (by simpa using hB.1.2 (b : G) b.2)
  have hker : Nat.card ψ.ker ≤ 2 := by
    have hle : ψ.ker.map B.subtype ≤ zpowers t := by
      rintro _ ⟨b, hb, rfl⟩
      have hcen : Subgroup.inclusion hBL b ∈ Subgroup.center ↥L := by
        rw [← ff6mPhi_ker e]
        exact hb
      have hcenIn : (b : G) ∈ centerIn L := Subgroup.mem_map_of_mem L.subtype hcen
      have hb2 : (b : G) ^ 2 = 1 := hB.1.2 (b : G) b.2
      by_cases h1 : (b : G) = 1
      · rw [Subgroup.coe_subtype, h1]
        exact one_mem _
      · have h3 := sec5_zpowers_le_twoCoreIn hcenIn (orderOf_eq_prime hb2 h1)
        rw [hcore] at h3
        exact h3 (Subgroup.mem_zpowers _)
    have h4 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective B.subtype_injective] at h4
    have h5 : Nat.card (zpowers t) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one (hB.1.2 t htB))
    exact h4.trans h5
  have hcard : Nat.card ψ.ker * Nat.card ψ.range = 2 ^ 5 := by
    rw [Subgroup.card_ker_mul_card_range ψ]
    exact hB.2
  have hkpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have h16 : 2 ^ 4 ∣ Nat.card ψ.range := by
    rcases (by omega : Nat.card ψ.ker = 1 ∨ Nat.card ψ.ker = 2) with h | h
    · rw [h] at hcard
      exact ⟨2, by omega⟩
    · rw [h] at hcard
      exact ⟨1, by omega⟩
  haveI : Finite ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  obtain ⟨U, hUcard, -, hUle⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := (⊥ : Subgroup ↥(omegaProj hQ))) (L := ψ.range) (n := 4) (by simp) h16 bot_le
  refine ⟨U, ?_, ?_⟩
  · unfold IsElemAb2 CFSG.Open.IsElemAbelian
    refine ⟨⟨?_, ?_⟩, hUcard⟩
    · haveI : IsMulCommutative ↥B := hB.1.1
      haveI : IsMulCommutative ↥ψ.range := inferInstance
      exact isMulCommutative_anti hUle
    · intro x hx
      obtain ⟨b, rfl⟩ := hUle hx
      rw [← map_pow, hsq b, map_one]
  · intro u hu
    obtain ⟨b, rfl⟩ := hUle hu
    exact ⟨Subgroup.inclusion hBL b, b.2, rfl⟩

theorem asc82FactBCent6_holds : Asc82FactBCent6 := by
  intro G _ _ t L r B hL hcore hBr hB htB _ _ hα c hcN hcB
  obtain ⟨α, V, _, _, _, Q, hQ, e, x, hdim, hsgn, -, -⟩ := hα
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hh : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)) :=
    Or.inr ⟨hdim, Or.inr hsgn⟩
  have hBL : B ≤ L := fun b hb => (Subgroup.mem_inf.mp (hBr hb)).1
  obtain ⟨fr⟩ := exists_nframe_six hQ hdim hsgn
  obtain ⟨U, hU, hUφ⟩ := fx_p510_exists_E16 hcore hBL hB htB e
  obtain ⟨y, hy⟩ := ff_star_E16_conj hQ hdim hsgn h2 fr hU
  let z : ProjSim Q := ffTheta hQ hh e ⟨c, hcN⟩
  have hzI : InducesViaP L (Subgroup.center ↥L) hQ e c z := ffTheta_induces hQ hh e ⟨c, hcN⟩
  have hzU : ∀ u ∈ U, ffSimOmegaAct hQ h2 z u = u := by
    intro u hu
    obtain ⟨l, hlB, rfl⟩ := hUφ u hu
    have hcl : c * (l : G) = (l : G) * c := (Subgroup.mem_centralizer_iff.mp hcB (l : G) hlB).symm
    exact ff6m_phi_conj hQ h2 e hzI l l (by rw [hcl]; group)
  have hz' : ∀ b ∈ ffB1 hQ fr, ffSimOmegaAct hQ h2 (y⁻¹ * z * y) b = b := by
    intro b hb
    have hbU : ffSimOmegaAct hQ h2 y b ∈ U := by
      rw [hy]
      exact Subgroup.mem_map_of_mem (ffSimOmegaAct hQ h2 y).toMonoidHom hb
    apply (ffSimOmegaAct hQ h2 y).injective
    rw [← MulAut.mul_apply, ← map_mul, show y * (y⁻¹ * z * y) = z * y by group, map_mul,
      MulAut.mul_apply, hzU _ hbU]
  obtain ⟨K, hK⟩ := ff_star_cent_sim hQ h2 fr hz'
  have hzz' : (y⁻¹ * z * y) * (y⁻¹ * z * y) = 1 := by
    rw [hK, ← map_mul, ← map_mul, fr.signChange_mul_self, map_one, map_one]
  have hzz : z * z = 1 := by
    have h : z * z = y * ((y⁻¹ * z * y) * (y⁻¹ * z * y)) * y⁻¹ := by group
    rw [h, hzz', mul_one, mul_inv_cancel]
  have hcc : (⟨c, hcN⟩ : ↥(normalizer (L : Set G))) * ⟨c, hcN⟩ = ⟨c * c, mul_mem hcN hcN⟩ := rfl
  have h1 : ffTheta hQ hh e ⟨c * c, mul_mem hcN hcN⟩ = 1 := by
    rw [← hcc, map_mul]
    exact hzz
  exact (ffTheta_eq_one_iff hQ hh e (Group.isPerfect_def.mp hL.1.1)
    ⟨c * c, mul_mem hcN hcN⟩).mp h1

end CFSG.OddStandard.SmallF3.Omega

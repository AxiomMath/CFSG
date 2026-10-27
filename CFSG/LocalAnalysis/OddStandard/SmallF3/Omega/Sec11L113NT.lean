module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Base
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Fin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110Q8

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 T : Subgroup G}
  {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem sec113_comm_mem_Q2 {Q1 Q2 : Subgroup G} (P : Sec11Q8Pair z Q1 Q2) {x p : G}
    (hxQ2 : ∀ q ∈ Q2, x * q * x⁻¹ ∈ Q2) (h1 : ActsTrivModZ z x Q1) (hp : p ∈ Q1 ⊔ Q2) :
    x * p * x⁻¹ * p⁻¹ ∈ Q2 := by
  obtain ⟨p1, hp1, p2, hp2, rfl⟩ := P.exists_mul_of_mem_sup hp
  have he : x * p1 * x⁻¹ * p1⁻¹ ∈ zpowers z := h1 p1 hp1
  have hzQ2 : x * p1 * x⁻¹ * p1⁻¹ ∈ Q2 := (Subgroup.zpowers_le.mpr P.z_mem2) he
  have hp2' : x * p2 * x⁻¹ ∈ Q2 := hxQ2 p2 hp2
  have hw : (x * p2 * x⁻¹) * p2⁻¹ ∈ Q2 := Q2.mul_mem hp2' (Q2.inv_mem hp2)
  have hc : p1 * ((x * p2 * x⁻¹) * p2⁻¹) = ((x * p2 * x⁻¹) * p2⁻¹) * p1 := P.comm p1 hp1 _ hw
  have e : x * (p1 * p2) * x⁻¹ * (p1 * p2)⁻¹ =
      (x * p1 * x⁻¹ * p1⁻¹) * ((x * p2 * x⁻¹) * p2⁻¹) := by
    have e1 : x * (p1 * p2) * x⁻¹ * (p1 * p2)⁻¹ =
        (x * p1 * x⁻¹ * p1⁻¹) * (p1 * ((x * p2 * x⁻¹) * p2⁻¹) * p1⁻¹) := by group
    rw [e1, hc]
    group
  rw [e]
  exact Q2.mul_mem hzQ2 hw

theorem sec113_not_triv (hm : Sec11Model t L S z K1 K2 T Alt φ) {Q1 Q2 : Subgroup G}
    (P : Sec11Q8Pair z Q1 Q2) (hQ : secQ K1 K2 = Q1 ⊔ Q2) {x : G} (hxM : x ∈ secM t S L)
    (hxQ2 : ∀ q ∈ Q2, x * q * x⁻¹ ∈ Q2) (hsh : Sec113Shape (hm.perm.rho x)) :
    ¬ ActsTrivModZ z x Q1 := by
  intro h1
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc, hxa, hxc⟩ := hsh.ex
  have hpQ : φ (Pi.single a 1 + Pi.single c 1) ∈ Q1 ⊔ Q2 := by
    rw [← hQ, hm.mem_Q]
    exact ⟨sec113_single_add_sum a c, sec113_pair_eq a c ha hc⟩
  have hu := sec113_comm_mem_Q2 P hxQ2 h1 hpQ
  have hconj : x * φ (Pi.single a 1 + Pi.single c 1) * x⁻¹ = φ (Pi.single b 1 + Pi.single c 1) := by
    rw [hm.perm.conj_apply hxM, sec11_permVec_add, sec11_permVec_single, sec11_permVec_single,
      hxa, hxc]
  have hval : x * φ (Pi.single a 1 + Pi.single c 1) * x⁻¹ * (φ (Pi.single a 1 + Pi.single c 1))⁻¹ =
      φ (Pi.single a 1 + Pi.single b 1) := by
    rw [hconj, hm.perm.inv_eq, ← hm.perm.mul]
    congr 1
    calc Pi.single b 1 + Pi.single c 1 + (Pi.single a 1 + Pi.single c 1)
        = Pi.single a 1 + Pi.single b 1 + (Pi.single c 1 + Pi.single c 1) := by abel
      _ = Pi.single a 1 + Pi.single b 1 := by rw [sec11_vec_add_self, add_zero]
  rw [hval] at hu
  have hsq := hm.perm.sq (Pi.single a 1 + Pi.single b 1)
  rcases P.mem_zpowers_iff.mp (P.invol2 _ hu hsq) with h | h
  · exact sec113_ab_ne a b ha hb hab ((hm.perm.ker _).1 h)
  · rw [sec113_z_eq hm, hm.perm.eq_iff] at h
    exact sec113_ab_z_ne a b ha hb hab h

end CFSG.OddStandard.SmallF3.Omega

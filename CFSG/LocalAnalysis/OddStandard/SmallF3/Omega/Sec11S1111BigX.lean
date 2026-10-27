module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111Th
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111DI
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111Hcl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111BigT

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_hDI [Finite G] (hp : Asc82Pre11) (h111N : Asc82Lemma111N) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R)
    (hdih : IsDih2 (Subgroup.closure (secTheta t z R)))
    (h8 : 8 ≤ Nat.card ↥(Subgroup.closure (secTheta t z R))) :
    ∀ d ∈ Subgroup.closure (secTheta t z R), orderOf d = 2 → d ≠ z → d ∈ secTheta t z R := by
  obtain ⟨m, hm1, ⟨e⟩⟩ := hdih
  have hcard : Nat.card ↥(Subgroup.closure (secTheta t z R)) = 2 * 2 ^ m := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hm : 2 ≤ m := by
    by_contra h
    have hm_eq : m = 1 := le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_le h)) hm1
    have h4 : Nat.card ↥(Subgroup.closure (secTheta t z R)) = 4 := by
      rw [hcard, hm_eq]
      norm_num
    omega
  have hzc : ∀ u ∈ Subgroup.closure (secTheta t z R), z * u = u * z := by
    intro u hu
    have huH : u ∈ centralizer ({z} : Set G) :=
      (sec11_R_le_H hp hctx) (sec11_closure_Theta_le_R t z R hu)
    exact (Subgroup.mem_centralizer_singleton_iff.mp huH).symm
  intro d hd hd2 hdz
  exact sec11_dihedral_invol_mem (E := G) (D := Subgroup.closure (secTheta t z R)) (m := m) hm e
    (Θ := secTheta t z R) (z := z) Subgroup.subset_closure rfl
    (sec11_Theta_order hctx.toSec10Ctx R)
    (fun s hs u hu => sec11_Theta_conj (sec11_R_le_H hp hctx) s hs u hu)
    (sec11_z_mem_closure_Theta hp h111N hctx) hctx.toSec10Z.pocket.1 hzc
    (sec11_Theta_not_z hp hctx.toSec10Ctx R) hd hd2 hdz

theorem sec11_X_big [Finite G] (hp : Asc82Pre11) (h111N : Asc82Lemma111N)
    (hB4 : Asc82InputDihSd) {t : G} {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) (hR : IsSylow2Of R (centralizer ({z} : Set G)))
    (hdih : IsDih2 (Subgroup.closure (secTheta t z R)))
    (h8 : 8 ≤ Nat.card ↥(Subgroup.closure (secTheta t z R))) :
    ∃ P : Subgroup G, IsSylow2Of P (secXH t z) ∧ IsDihSd P := by
  have htH : t ∈ centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (sec11_invols hctx.toSec10Ctx).2.2.1
  have hDH : Subgroup.closure (secTheta t z R) ≤ centralizer ({z} : Set G) :=
    (sec11_closure_Theta_le_R t z R).trans (sec11_R_le_H hp hctx)
  have hDX : Subgroup.closure (secTheta t z R) ≤ secXH t z := by
    refine (Subgroup.closure_le (secXH t z)).mpr ?_
    rintro s ⟨-, h, hh, heq⟩
    exact Subgroup.subset_closure ⟨h, hh, heq⟩
  have hzH : ∀ h ∈ centralizer ({z} : Set G), h * z = z * h :=
    fun h hh => Subgroup.mem_centralizer_singleton_iff.mp hh
  have hcl := sec11_hcl_core (H := centralizer ({z} : Set G)) (Θ := secTheta t z R) hR
    (fun s => Iff.rfl) hzH (sec11_z_mem_closure_Theta hp h111N hctx)
    (sec11_hDI hp h111N hctx hdih h8)
  exact sec11_dihSd_of_input hB4 (H := centralizer ({z} : Set G)) (R := R)
    (D := Subgroup.closure (secTheta t z R)) (X := secXH t z) (t := t)
    hR htH hDH rfl (Subgroup.subset_closure (sec11_t_mem_Theta hp hctx)) hDX hdih h8 hcl

end CFSG.OddStandard.SmallF3.Omega

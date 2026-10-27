module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UTstar
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UFusion
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UD8

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G} {ι ιd : Perm (Fin 10) →* G}

theorem false_of_odd_index_Tstar [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (F : UFrame z ι ιd) {P : Subgroup (Perm (Fin 8))}
    (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ (Dsub z ιd ⊔ Qsub ι P : Subgroup G).index) : False := by
  obtain ⟨ε, hεz, hεg⟩ := D8Rel.exists_hom F.d8
  refine false_of_thompson_product hnonab (isPGroup_Dsub F) (isPGroup_Qsub F hP)
    (comm_Dsub_Qsub F P) (Dsub_inf_Qsub F P) ε
    (signMap (ι.comp liftS8) (injective_comp_liftS8 F) P)
    F.cent.order (D8Rel.z_mem z (gElt ιd)) hεz hidx ?_
  intro d q h2 hχ a hconj
  obtain ⟨p, hp, hp_eq⟩ := Subgroup.mem_map.mp q.2
  have hq_eq : q = ⟨(ι.comp liftS8) p, Subgroup.mem_map_of_mem (ι.comp liftS8) hp⟩ :=
    Subtype.ext hp_eq.symm
  have hψ : signMap (ι.comp liftS8) (injective_comp_liftS8 F) P q = sign p := by
    rw [hq_eq]
    exact signMap_apply (ι.comp liftS8) (injective_comp_liftS8 F) P hp
  have hε : ε ⟨(d : G), d.2⟩ * sign p = 1 := by
    rw [← hψ]
    exact hχ
  have h2' : ((d : G) * ι (liftS8 p)) * ((d : G) * ι (liftS8 p)) = 1 := by
    rw [← hp_eq] at h2
    exact h2
  obtain ⟨hdd, hpp⟩ := (UFrame.mul_self_eq_one_iff F d.2 p).mp h2'
  rw [← hp_eq] at hconj
  exact not_isConj_of_chi F ε hεz hεg (q := (d : G)) d.2 hdd hpp hε a hconj

theorem two_pow_eleven_dvd_card_centralizer [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (F : UFrame z ι ιd) :
    2 ^ 11 ∣ Nat.card (centralizer ({z * ι τ₀} : Set G)) := by
  by_contra h
  obtain ⟨P, hP2, hPcard, h01, h23, h45, h67, hZ⟩ := exists_sylow_eight_swaps
  have hT : IsPGroup 2 (Dsub z ιd ⊔ Qsub ι P : Subgroup G) :=
    isPGroup_sup_of_commute (isPGroup_Dsub F) (isPGroup_Qsub F hP2) (comm_Dsub_Qsub F P)
  have hTcard : Nat.card (Dsub z ιd ⊔ Qsub ι P : Subgroup G) = 2 ^ 10 :=
    card_Tstar F hP2 hPcard
  have hH : normalizer ((Dsub z ιd ⊔ Qsub ι P : Subgroup G) : Set G) ≤
      centralizer ({z * ι τ₀} : Set G) :=
    normalizer_Tstar_le F h01 h23 h45 h67 hZ
  have hHcard : ¬ 2 ^ (10 + 1) ∣ Nat.card (centralizer ({z * ι τ₀} : Set G)) := by
    simpa using h
  have hidx : ¬ 2 ∣ (Dsub z ιd ⊔ Qsub ι P : Subgroup G).index :=
    not_two_dvd_index_of_normalizer_le hT hH (a := 10) hTcard hHcard
  exact false_of_odd_index_Tstar hnonab F hP2 hidx

end CFSG.OddStandard.AltStdSec.SwapPartner

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8L85
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HSylM
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HP1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HGenL
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTrans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E4SylA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84_gen_proved (hM : Asc82Tab6M) (h36 : Asc82Lemma36) : Asc82Sec8Gen := by
  intro G _ _ t L S z g B hctx
  have hS3 : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hLM : IsOm6M L := ⟨hS3.component.isQuasisimple, hctx.omega6m⟩
  have hnorm : ∀ c ∈ centralizer ({t} : Set G), CFSG.conjugate L c = L :=
    conjugate_eq_self_of_lemma36 h36 hS3
  have hzL : z ∈ L := by
    obtain ⟨K, hK⟩ := hctx.pocket.2
    exact (hK.2.1 hK.1).1
  have hz2 : orderOf z = 2 := hctx.pocket.1
  have hsylL : IsSylow2Of (S ⊓ L) L :=
    sec8t84_sylow_inf_normal hctx.sylow hS3.component.1 (fun h hh n hn => by
      have hnconj : n ∈ CFSG.conjugate L h := by
        rw [hnorm h hh]
        exact hn
      exact mem_conjugate_iff'.mp hnconj)
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hsgn⟩ := ff6m_exists_model hLM
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := ff6m_odd_center hLM
  have hφ : OddCentralCover (ff6mPhi e) := ff6m_phi_cover e hodd
  have hPf : IsSylow2Of (ffImg (ff6mPhi e) (S ⊓ L)) (⊤ : Subgroup ↥(omegaProj hQ)) :=
    ff_cover_isSylow2Of hφ hsylL
  have hP : IsSylow2Of ((ffImg (ff6mPhi e) (S ⊓ L)).map (omegaProj hQ).subtype)
      (omegaProj hQ) :=
    sec8t84h_isSylow2Of_map_subtype (omegaProj hQ) hPf
  have hω : omega1 ((ffImg (ff6mPhi e) (S ⊓ L)).map (omegaProj hQ).subtype) =
      (ffImg (ff6mPhi e) (S ⊓ L)).map (omegaProj hQ).subtype :=
    (sec8t84_modelSylow V Q hQ hdim hsgn _ hP).1
  have hω' : omega1 (ffImg (ff6mPhi e) (S ⊓ L)) = ffImg (ff6mPhi e) (S ⊓ L) :=
    sec8t84h_omega1_of_map_subtype (omegaProj hQ) hω
  have hCS : conjClassIn L z ∩ (S : Set G) ⊆ ((S ⊓ L : Subgroup G) : Set G) := by
    rintro y ⟨⟨l, hl, rfl⟩, hyS⟩
    exact Subgroup.mem_inf.mpr ⟨hyS, L.mul_mem (L.mul_mem hl hzL) (L.inv_mem hl)⟩
  have hC : ∀ u ∈ (S ⊓ L : Subgroup G), u * u = 1 → u ≠ 1 →
      u ∈ conjClassIn L z ∩ (S : Set G) := by
    intro u hu huu hu1
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact huu) hu1
    exact ⟨hM.inv_one_class G L hLM z u hzL (Subgroup.mem_inf.mp hu).2 hz2 hu2,
      (Subgroup.mem_inf.mp hu).1⟩
  exact le_antisymm
    (sec8t84h_cover_le_closure hφ inf_le_right hsylL.2.1 hω' hCS hC)
    ((Subgroup.closure_le (S ⊓ L)).mpr hCS)

end CFSG.OddStandard.SmallF3.Omega
